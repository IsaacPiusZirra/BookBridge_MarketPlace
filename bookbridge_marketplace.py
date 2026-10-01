#!/usr/bin/env python3
"""
BookBridge Marketplace
======================

Single-file reference implementation of the BookBridge books e-commerce
marketplace described in the CSC 720 Electronic Commerce Technologies report.

Technology:
    - Python 3.11+
    - SQLite
    - Flet (desktop/web/mobile UI)

The code intentionally keeps database, security, service and presentation
responsibilities separated into classes/functions even though they are packaged
in one .py file for convenient submission and download.

Install UI dependency:
    pip install flet

Run:
    python bookbridge_marketplace.py

Run service-layer self tests without Flet:
    python bookbridge_marketplace.py --self-test

Demo accounts created automatically:
    Buyer:  buyer@bookbridge.local  / Buyer123!
    Seller: seller@bookbridge.local / Seller123!
    Admin:  admin@bookbridge.local  / Admin123!

SECURITY NOTE:
This is an academic prototype. It uses salted PBKDF2 password hashing,
parameterised SQL and transactional checkout. A production deployment should
use PostgreSQL, HTTPS, a hosted payment gateway, MFA/rate limiting, secret
management, audit logs, backups and other production controls.
"""

from __future__ import annotations

import argparse
import base64
import hashlib
import hmac
import os
import re
import secrets
import sqlite3
import tempfile
import unittest
from contextlib import contextmanager
from dataclasses import dataclass
from decimal import Decimal, InvalidOperation, ROUND_HALF_UP
from pathlib import Path
from typing import Any, Iterable, Optional

try:
    import flet as ft
except ModuleNotFoundError:  # Allows --self-test to work without Flet installed.
    ft = None


APP_TITLE = "BookBridge Marketplace"
DB_FILE = "bookbridge.db"
PBKDF2_ITERATIONS = 240_000

ROLES = {"buyer", "seller", "admin"}
PUBLIC_REGISTRATION_ROLES = {"buyer", "seller"}
PRODUCT_STATUSES = {"active", "inactive"}
PAYMENT_METHODS = {"bank_transfer", "cash_on_delivery", "demo_card"}
PAYMENT_STATUSES = {"pending", "paid", "failed"}
FULFILMENT_STATUSES = {"pending", "processing", "shipped", "delivered", "cancelled"}

EMAIL_RE = re.compile(r"^[^@\s]+@[^@\s]+\.[^@\s]+$")


# ---------------------------------------------------------------------------
# Exceptions and domain model
# ---------------------------------------------------------------------------

class BookBridgeError(Exception):
    """Base class for application-level errors."""


class ValidationError(BookBridgeError):
    """Raised when user supplied data does not satisfy business rules."""


class AuthenticationError(BookBridgeError):
    """Raised when login credentials are invalid."""


class AuthorizationError(BookBridgeError):
    """Raised when a user attempts an operation outside the user's role."""


class NotFoundError(BookBridgeError):
    """Raised when an expected record does not exist."""


@dataclass(frozen=True)
class SessionUser:
    id: int
    full_name: str
    email: str
    role: str


# ---------------------------------------------------------------------------
# Security helpers
# ---------------------------------------------------------------------------

def hash_password(password: str) -> str:
    """Create a salted PBKDF2-SHA256 password representation."""
    if len(password) < 8:
        raise ValueError("Password must contain at least 8 characters")

    salt = os.urandom(16)
    digest = hashlib.pbkdf2_hmac(
        "sha256",
        password.encode("utf-8"),
        salt,
        PBKDF2_ITERATIONS,
    )
    return "pbkdf2_sha256${}${}${}".format(
        PBKDF2_ITERATIONS,
        base64.b64encode(salt).decode("ascii"),
        base64.b64encode(digest).decode("ascii"),
    )


def verify_password(password: str, encoded: str) -> bool:
    """Verify password using a constant-time digest comparison."""
    try:
        algorithm, iterations, salt_b64, digest_b64 = encoded.split("$", 3)
        if algorithm != "pbkdf2_sha256":
            return False

        salt = base64.b64decode(salt_b64)
        expected = base64.b64decode(digest_b64)
        actual = hashlib.pbkdf2_hmac(
            "sha256",
            password.encode("utf-8"),
            salt,
            int(iterations),
        )
        return hmac.compare_digest(actual, expected)
    except (ValueError, TypeError):
        return False


def normalise_email(email: str) -> str:
    return email.strip().lower()


def money_to_kobo(value: Any) -> int:
    """Convert a naira amount to integer kobo without binary floating-point error."""
    try:
        amount = Decimal(str(value).replace(",", "").strip())
    except (InvalidOperation, AttributeError):
        raise ValidationError("Enter a valid price")

    if amount < 0:
        raise ValidationError("Price cannot be negative")

    return int(
        (amount * Decimal("100")).quantize(
            Decimal("1"), rounding=ROUND_HALF_UP
        )
    )


def kobo_to_naira(kobo: int) -> str:
    return f"₦{Decimal(kobo) / Decimal(100):,.2f}"


# ---------------------------------------------------------------------------
# Database
# ---------------------------------------------------------------------------

SCHEMA = """
PRAGMA foreign_keys = ON;

CREATE TABLE IF NOT EXISTS users (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    full_name TEXT NOT NULL,
    email TEXT NOT NULL UNIQUE COLLATE NOCASE,
    password_hash TEXT NOT NULL,
    role TEXT NOT NULL CHECK(role IN ('buyer','seller','admin')),
    is_active INTEGER NOT NULL DEFAULT 1,
    created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP
);

CREATE TABLE IF NOT EXISTS products (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    seller_id INTEGER NOT NULL,
    title TEXT NOT NULL,
    author TEXT NOT NULL,
    isbn TEXT,
    category TEXT NOT NULL,
    description TEXT NOT NULL DEFAULT '',
    price_kobo INTEGER NOT NULL CHECK(price_kobo >= 0),
    stock INTEGER NOT NULL CHECK(stock >= 0),
    status TEXT NOT NULL DEFAULT 'active'
        CHECK(status IN ('active','inactive')),
    created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,
    updated_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,
    FOREIGN KEY(seller_id) REFERENCES users(id)
);

CREATE TABLE IF NOT EXISTS cart_items (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    buyer_id INTEGER NOT NULL,
    product_id INTEGER NOT NULL,
    quantity INTEGER NOT NULL CHECK(quantity > 0),
    UNIQUE(buyer_id, product_id),
    FOREIGN KEY(buyer_id) REFERENCES users(id) ON DELETE CASCADE,
    FOREIGN KEY(product_id) REFERENCES products(id) ON DELETE CASCADE
);

CREATE TABLE IF NOT EXISTS orders (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    buyer_id INTEGER NOT NULL,
    total_kobo INTEGER NOT NULL CHECK(total_kobo >= 0),
    shipping_address TEXT NOT NULL,
    payment_method TEXT NOT NULL,
    payment_status TEXT NOT NULL
        CHECK(payment_status IN ('pending','paid','failed')),
    order_status TEXT NOT NULL
        CHECK(order_status IN ('pending','processing','shipped','delivered','cancelled')),
    created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,
    FOREIGN KEY(buyer_id) REFERENCES users(id)
);

CREATE TABLE IF NOT EXISTS order_items (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    order_id INTEGER NOT NULL,
    product_id INTEGER NOT NULL,
    seller_id INTEGER NOT NULL,
    title_snapshot TEXT NOT NULL,
    quantity INTEGER NOT NULL CHECK(quantity > 0),
    unit_price_kobo INTEGER NOT NULL CHECK(unit_price_kobo >= 0),
    subtotal_kobo INTEGER NOT NULL CHECK(subtotal_kobo >= 0),
    fulfilment_status TEXT NOT NULL DEFAULT 'pending'
        CHECK(fulfilment_status IN ('pending','processing','shipped','delivered','cancelled')),
    FOREIGN KEY(order_id) REFERENCES orders(id) ON DELETE CASCADE,
    FOREIGN KEY(product_id) REFERENCES products(id),
    FOREIGN KEY(seller_id) REFERENCES users(id)
);

CREATE TABLE IF NOT EXISTS payments (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    order_id INTEGER NOT NULL UNIQUE,
    reference TEXT NOT NULL UNIQUE,
    amount_kobo INTEGER NOT NULL CHECK(amount_kobo >= 0),
    method TEXT NOT NULL,
    status TEXT NOT NULL CHECK(status IN ('pending','paid','failed')),
    created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,
    FOREIGN KEY(order_id) REFERENCES orders(id) ON DELETE CASCADE
);

CREATE INDEX IF NOT EXISTS idx_products_search
    ON products(title, author, category);

CREATE INDEX IF NOT EXISTS idx_products_seller
    ON products(seller_id, status);

CREATE INDEX IF NOT EXISTS idx_orders_buyer
    ON orders(buyer_id, created_at);

CREATE INDEX IF NOT EXISTS idx_order_items_seller
    ON order_items(seller_id, fulfilment_status);
"""


class Database:
    def __init__(self, path: str | Path = DB_FILE):
        self.path = str(path)

    def connect(self) -> sqlite3.Connection:
        conn = sqlite3.connect(
            self.path,
            timeout=30,
            isolation_level=None,
        )
        conn.row_factory = sqlite3.Row
        conn.execute("PRAGMA foreign_keys = ON")
        conn.execute("PRAGMA busy_timeout = 5000")
        return conn

    @contextmanager
    def transaction(self):
        conn = self.connect()
        try:
            conn.execute("BEGIN IMMEDIATE")
            yield conn
            conn.commit()
        except Exception:
            conn.rollback()
            raise
        finally:
            conn.close()

    def initialize(self, seed_demo: bool = True) -> None:
        with self.connect() as conn:
            conn.executescript(SCHEMA)

        if seed_demo:
            self.seed_demo_data()

    def _insert_user_if_missing(
        self,
        full_name: str,
        email: str,
        password: str,
        role: str,
    ) -> int:
        email = normalise_email(email)
        with self.transaction() as conn:
            row = conn.execute(
                "SELECT id FROM users WHERE email=?",
                (email,),
            ).fetchone()
            if row:
                return int(row["id"])

            cur = conn.execute(
                """
                INSERT INTO users(full_name,email,password_hash,role)
                VALUES (?,?,?,?)
                """,
                (full_name, email, hash_password(password), role),
            )
            return int(cur.lastrowid)

    def seed_demo_data(self) -> None:
        buyer_id = self._insert_user_if_missing(
            "Demo Buyer",
            "buyer@bookbridge.local",
            "Buyer123!",
            "buyer",
        )
        seller_id = self._insert_user_if_missing(
            "Demo Bookseller",
            "seller@bookbridge.local",
            "Seller123!",
            "seller",
        )
        self._insert_user_if_missing(
            "BookBridge Administrator",
            "admin@bookbridge.local",
            "Admin123!",
            "admin",
        )

        del buyer_id  # buyer account is intentionally seeded even if no cart exists.

        sample_books = [
            (
                "Things Fall Apart",
                "Chinua Achebe",
                "9780385474542",
                "Literature",
                "A landmark African novel examining culture, change and colonial encounter.",
                650000,
                12,
            ),
            (
                "Half of a Yellow Sun",
                "Chimamanda Ngozi Adichie",
                "9780007200283",
                "Literature",
                "A novel set during the Nigerian Civil War.",
                850000,
                9,
            ),
            (
                "Clean Code",
                "Robert C. Martin",
                "9780132350884",
                "Computing",
                "Practical principles for writing maintainable software.",
                2400000,
                5,
            ),
            (
                "Software Engineering",
                "Ian Sommerville",
                "9780137035151",
                "Computing",
                "A comprehensive software engineering textbook.",
                1200000,
                4,
            ),
            (
                "Research Methodology",
                "C. R. Kothari",
                "9788122424881",
                "Academic",
                "Methods and techniques for academic and applied research.",
                1000000,
                8,
            ),
        ]

        with self.transaction() as conn:
            count = conn.execute(
                "SELECT COUNT(*) AS c FROM products WHERE seller_id=?",
                (seller_id,),
            ).fetchone()["c"]

            if count == 0:
                conn.executemany(
                    """
                    INSERT INTO products(
                        seller_id,title,author,isbn,category,description,
                        price_kobo,stock,status
                    )
                    VALUES (?,?,?,?,?,?,?,?, 'active')
                    """,
                    [
                        (seller_id, *book)
                        for book in sample_books
                    ],
                )


# ---------------------------------------------------------------------------
# Application / service layer
# ---------------------------------------------------------------------------

class MarketplaceService:
    def __init__(self, db: Database):
        self.db = db

    # ---------- common helpers ----------

    @staticmethod
    def _require_role(user: SessionUser, *roles: str) -> None:
        if user.role not in roles:
            allowed = ", ".join(roles)
            raise AuthorizationError(f"This action requires role: {allowed}")

    @staticmethod
    def _row_to_dict(row: sqlite3.Row) -> dict[str, Any]:
        return dict(row)

    # ---------- authentication ----------

    def register(
        self,
        full_name: str,
        email: str,
        password: str,
        role: str,
    ) -> int:
        full_name = full_name.strip()
        email = normalise_email(email)
        role = role.strip().lower()

        if len(full_name) < 2:
            raise ValidationError("Enter your full name")
        if not EMAIL_RE.match(email):
            raise ValidationError("Enter a valid email address")
        if role not in PUBLIC_REGISTRATION_ROLES:
            raise ValidationError("Choose buyer or seller")
        if len(password) < 8:
            raise ValidationError("Password must contain at least 8 characters")

        try:
            encoded = hash_password(password)
            with self.db.transaction() as conn:
                cur = conn.execute(
                    """
                    INSERT INTO users(full_name,email,password_hash,role)
                    VALUES (?,?,?,?)
                    """,
                    (full_name, email, encoded, role),
                )
                return int(cur.lastrowid)
        except sqlite3.IntegrityError as exc:
            if "email" in str(exc).lower() or "unique" in str(exc).lower():
                raise ValidationError("An account already exists with this email")
            raise ValidationError("Unable to create account") from exc

    def login(self, email: str, password: str) -> SessionUser:
        email = normalise_email(email)
        with self.db.connect() as conn:
            row = conn.execute(
                """
                SELECT id,full_name,email,password_hash,role,is_active
                FROM users
                WHERE email=?
                """,
                (email,),
            ).fetchone()

        if not row or not row["is_active"]:
            raise AuthenticationError("Invalid email or password")

        if not verify_password(password, row["password_hash"]):
            raise AuthenticationError("Invalid email or password")

        return SessionUser(
            id=int(row["id"]),
            full_name=row["full_name"],
            email=row["email"],
            role=row["role"],
        )

    # ---------- catalogue ----------

    def categories(self) -> list[str]:
        with self.db.connect() as conn:
            rows = conn.execute(
                """
                SELECT DISTINCT category
                FROM products
                WHERE status='active'
                ORDER BY category COLLATE NOCASE
                """
            ).fetchall()
        return [str(r["category"]) for r in rows]

    def list_products(
        self,
        query: str = "",
        category: str = "",
        include_out_of_stock: bool = False,
    ) -> list[dict[str, Any]]:
        query = query.strip()
        category = category.strip()

        clauses = ["p.status='active'"]
        params: list[Any] = []

        if not include_out_of_stock:
            clauses.append("p.stock > 0")

        if query:
            like = f"%{query}%"
            clauses.append(
                """
                (
                    p.title LIKE ? OR p.author LIKE ? OR
                    COALESCE(p.isbn,'') LIKE ? OR
                    p.description LIKE ?
                )
                """
            )
            params.extend([like, like, like, like])

        if category:
            clauses.append("p.category = ?")
            params.append(category)

        sql = f"""
            SELECT
                p.id,p.seller_id,p.title,p.author,p.isbn,p.category,
                p.description,p.price_kobo,p.stock,p.status,p.created_at,
                u.full_name AS seller_name
            FROM products p
            JOIN users u ON u.id=p.seller_id
            WHERE {' AND '.join(clauses)}
            ORDER BY p.created_at DESC, p.title COLLATE NOCASE
        """

        with self.db.connect() as conn:
            rows = conn.execute(sql, params).fetchall()
        return [self._row_to_dict(r) for r in rows]

    def seller_products(self, seller: SessionUser) -> list[dict[str, Any]]:
        self._require_role(seller, "seller", "admin")

        with self.db.connect() as conn:
            if seller.role == "admin":
                rows = conn.execute(
                    """
                    SELECT p.*, u.full_name AS seller_name
                    FROM products p
                    JOIN users u ON u.id=p.seller_id
                    ORDER BY p.created_at DESC
                    """
                ).fetchall()
            else:
                rows = conn.execute(
                    """
                    SELECT p.*, u.full_name AS seller_name
                    FROM products p
                    JOIN users u ON u.id=p.seller_id
                    WHERE p.seller_id=?
                    ORDER BY p.created_at DESC
                    """,
                    (seller.id,),
                ).fetchall()
        return [self._row_to_dict(r) for r in rows]

    def save_product(
        self,
        seller: SessionUser,
        title: str,
        author: str,
        isbn: str,
        category: str,
        description: str,
        price_naira: Any,
        stock: Any,
        *,
        product_id: Optional[int] = None,
        status: str = "active",
    ) -> int:
        self._require_role(seller, "seller", "admin")

        title = title.strip()
        author = author.strip()
        isbn = isbn.strip()
        category = category.strip()
        description = description.strip()
        status = status.strip().lower()

        if not title:
            raise ValidationError("Book title is required")
        if not author:
            raise ValidationError("Author is required")
        if not category:
            raise ValidationError("Category is required")
        if status not in PRODUCT_STATUSES:
            raise ValidationError("Invalid product status")

        try:
            stock_int = int(str(stock).strip())
        except (ValueError, TypeError):
            raise ValidationError("Stock must be a whole number")

        if stock_int < 0:
            raise ValidationError("Stock cannot be negative")

        price_kobo = money_to_kobo(price_naira)

        with self.db.transaction() as conn:
            if product_id is None:
                if seller.role == "admin":
                    raise ValidationError(
                        "Administrator cannot create a listing without a seller account"
                    )
                cur = conn.execute(
                    """
                    INSERT INTO products(
                        seller_id,title,author,isbn,category,description,
                        price_kobo,stock,status
                    )
                    VALUES (?,?,?,?,?,?,?,?,?)
                    """,
                    (
                        seller.id,
                        title,
                        author,
                        isbn or None,
                        category,
                        description,
                        price_kobo,
                        stock_int,
                        status,
                    ),
                )
                return int(cur.lastrowid)

            existing = conn.execute(
                "SELECT seller_id FROM products WHERE id=?",
                (product_id,),
            ).fetchone()
            if not existing:
                raise NotFoundError("Product not found")

            if seller.role != "admin" and int(existing["seller_id"]) != seller.id:
                raise AuthorizationError("You can update only your own listings")

            conn.execute(
                """
                UPDATE products
                SET title=?,author=?,isbn=?,category=?,description=?,
                    price_kobo=?,stock=?,status=?,updated_at=CURRENT_TIMESTAMP
                WHERE id=?
                """,
                (
                    title,
                    author,
                    isbn or None,
                    category,
                    description,
                    price_kobo,
                    stock_int,
                    status,
                    product_id,
                ),
            )
            return int(product_id)

    def set_product_status(
        self,
        user: SessionUser,
        product_id: int,
        status: str,
    ) -> None:
        self._require_role(user, "seller", "admin")
        status = status.lower().strip()
        if status not in PRODUCT_STATUSES:
            raise ValidationError("Invalid product status")

        with self.db.transaction() as conn:
            row = conn.execute(
                "SELECT seller_id FROM products WHERE id=?",
                (product_id,),
            ).fetchone()
            if not row:
                raise NotFoundError("Product not found")

            if user.role != "admin" and int(row["seller_id"]) != user.id:
                raise AuthorizationError("You can update only your own listings")

            conn.execute(
                """
                UPDATE products
                SET status=?,updated_at=CURRENT_TIMESTAMP
                WHERE id=?
                """,
                (status, product_id),
            )

    # ---------- cart ----------

    def add_to_cart(
        self,
        buyer: SessionUser,
        product_id: int,
        quantity: int = 1,
    ) -> None:
        self._require_role(buyer, "buyer")

        try:
            quantity = int(quantity)
        except (ValueError, TypeError):
            raise ValidationError("Quantity must be a whole number")

        if quantity <= 0:
            raise ValidationError("Quantity must be greater than zero")

        with self.db.transaction() as conn:
            product = conn.execute(
                """
                SELECT id,title,stock,status
                FROM products
                WHERE id=?
                """,
                (product_id,),
            ).fetchone()

            if not product or product["status"] != "active":
                raise ValidationError("This book is not available")

            current = conn.execute(
                """
                SELECT quantity
                FROM cart_items
                WHERE buyer_id=? AND product_id=?
                """,
                (buyer.id, product_id),
            ).fetchone()
            current_qty = int(current["quantity"]) if current else 0
            new_qty = current_qty + quantity

            if new_qty > int(product["stock"]):
                raise ValidationError(
                    f"Only {product['stock']} unit(s) of {product['title']} are available"
                )

            conn.execute(
                """
                INSERT INTO cart_items(buyer_id,product_id,quantity)
                VALUES (?,?,?)
                ON CONFLICT(buyer_id,product_id)
                DO UPDATE SET quantity=excluded.quantity
                """,
                (buyer.id, product_id, new_qty),
            )

    def update_cart_quantity(
        self,
        buyer: SessionUser,
        product_id: int,
        quantity: int,
    ) -> None:
        self._require_role(buyer, "buyer")

        try:
            quantity = int(quantity)
        except (ValueError, TypeError):
            raise ValidationError("Quantity must be a whole number")

        if quantity <= 0:
            self.remove_from_cart(buyer, product_id)
            return

        with self.db.transaction() as conn:
            product = conn.execute(
                """
                SELECT title,stock,status
                FROM products
                WHERE id=?
                """,
                (product_id,),
            ).fetchone()

            if not product or product["status"] != "active":
                raise ValidationError("This book is not available")
            if quantity > int(product["stock"]):
                raise ValidationError(
                    f"Only {product['stock']} unit(s) of {product['title']} are available"
                )

            result = conn.execute(
                """
                UPDATE cart_items
                SET quantity=?
                WHERE buyer_id=? AND product_id=?
                """,
                (quantity, buyer.id, product_id),
            )
            if result.rowcount == 0:
                raise NotFoundError("Cart item not found")

    def remove_from_cart(
        self,
        buyer: SessionUser,
        product_id: int,
    ) -> None:
        self._require_role(buyer, "buyer")
        with self.db.transaction() as conn:
            conn.execute(
                "DELETE FROM cart_items WHERE buyer_id=? AND product_id=?",
                (buyer.id, product_id),
            )

    def cart(self, buyer_id: int) -> list[dict[str, Any]]:
        with self.db.connect() as conn:
            rows = conn.execute(
                """
                SELECT
                    c.product_id,c.quantity,
                    p.title,p.author,p.price_kobo,p.stock,p.status,
                    (c.quantity * p.price_kobo) AS subtotal_kobo
                FROM cart_items c
                JOIN products p ON p.id=c.product_id
                WHERE c.buyer_id=?
                ORDER BY c.id
                """,
                (buyer_id,),
            ).fetchall()
        return [self._row_to_dict(r) for r in rows]

    # ---------- checkout / orders ----------

    def checkout(
        self,
        buyer: SessionUser,
        shipping_address: str,
        payment_method: str,
    ) -> int:
        self._require_role(buyer, "buyer")

        shipping_address = shipping_address.strip()
        payment_method = payment_method.strip()

        if len(shipping_address) < 8:
            raise ValidationError("Enter a complete delivery address")
        if payment_method not in PAYMENT_METHODS:
            raise ValidationError("Select a valid payment method")

        with self.db.transaction() as conn:
            rows = conn.execute(
                """
                SELECT
                    c.product_id,c.quantity,p.title,p.seller_id,
                    p.price_kobo,p.stock,p.status
                FROM cart_items c
                JOIN products p ON p.id=c.product_id
                WHERE c.buyer_id=?
                """,
                (buyer.id,),
            ).fetchall()

            if not rows:
                raise ValidationError("Your cart is empty")

            total = 0
            for row in rows:
                if row["status"] != "active":
                    raise ValidationError(
                        f"{row['title']} is no longer available"
                    )
                if int(row["quantity"]) > int(row["stock"]):
                    raise ValidationError(
                        f"Insufficient stock for {row['title']}"
                    )
                total += int(row["quantity"]) * int(row["price_kobo"])

            payment_status = (
                "paid" if payment_method == "demo_card" else "pending"
            )
            order_status = (
                "processing" if payment_status == "paid" else "pending"
            )

            cur = conn.execute(
                """
                INSERT INTO orders(
                    buyer_id,total_kobo,shipping_address,payment_method,
                    payment_status,order_status
                )
                VALUES (?,?,?,?,?,?)
                """,
                (
                    buyer.id,
                    total,
                    shipping_address,
                    payment_method,
                    payment_status,
                    order_status,
                ),
            )
            order_id = int(cur.lastrowid)

            for row in rows:
                quantity = int(row["quantity"])
                price_kobo = int(row["price_kobo"])
                subtotal = quantity * price_kobo

                conn.execute(
                    """
                    INSERT INTO order_items(
                        order_id,product_id,seller_id,title_snapshot,
                        quantity,unit_price_kobo,subtotal_kobo
                    )
                    VALUES (?,?,?,?,?,?,?)
                    """,
                    (
                        order_id,
                        int(row["product_id"]),
                        int(row["seller_id"]),
                        row["title"],
                        quantity,
                        price_kobo,
                        subtotal,
                    ),
                )

                result = conn.execute(
                    """
                    UPDATE products
                    SET stock=stock-?,updated_at=CURRENT_TIMESTAMP
                    WHERE id=? AND status='active' AND stock>=?
                    """,
                    (quantity, int(row["product_id"]), quantity),
                )
                if result.rowcount != 1:
                    raise ValidationError(
                        f"Stock changed while ordering {row['title']}; please try again"
                    )

            reference = "BB-" + secrets.token_hex(6).upper()
            conn.execute(
                """
                INSERT INTO payments(
                    order_id,reference,amount_kobo,method,status
                )
                VALUES (?,?,?,?,?)
                """,
                (
                    order_id,
                    reference,
                    total,
                    payment_method,
                    payment_status,
                ),
            )

            conn.execute(
                "DELETE FROM cart_items WHERE buyer_id=?",
                (buyer.id,),
            )
            return order_id

    def buyer_orders(self, buyer_id: int) -> list[dict[str, Any]]:
        with self.db.connect() as conn:
            rows = conn.execute(
                """
                SELECT
                    o.*,
                    p.reference AS payment_reference,
                    COUNT(oi.id) AS item_count
                FROM orders o
                LEFT JOIN payments p ON p.order_id=o.id
                LEFT JOIN order_items oi ON oi.order_id=o.id
                WHERE o.buyer_id=?
                GROUP BY o.id
                ORDER BY o.created_at DESC,o.id DESC
                """,
                (buyer_id,),
            ).fetchall()
        return [self._row_to_dict(r) for r in rows]

    def order_items(
        self,
        user: SessionUser,
        order_id: int,
    ) -> list[dict[str, Any]]:
        with self.db.connect() as conn:
            order = conn.execute(
                "SELECT buyer_id FROM orders WHERE id=?",
                (order_id,),
            ).fetchone()
            if not order:
                raise NotFoundError("Order not found")

            if user.role == "buyer" and int(order["buyer_id"]) != user.id:
                raise AuthorizationError("This order does not belong to you")

            if user.role == "seller":
                rows = conn.execute(
                    """
                    SELECT oi.*
                    FROM order_items oi
                    WHERE oi.order_id=? AND oi.seller_id=?
                    ORDER BY oi.id
                    """,
                    (order_id, user.id),
                ).fetchall()
            elif user.role in {"buyer", "admin"}:
                rows = conn.execute(
                    """
                    SELECT oi.*
                    FROM order_items oi
                    WHERE oi.order_id=?
                    ORDER BY oi.id
                    """,
                    (order_id,),
                ).fetchall()
            else:
                raise AuthorizationError("Access denied")

        return [self._row_to_dict(r) for r in rows]

    # ---------- seller fulfilment ----------

    def seller_orders(self, seller_id: int) -> list[dict[str, Any]]:
        with self.db.connect() as conn:
            rows = conn.execute(
                """
                SELECT
                    oi.id,oi.order_id,oi.product_id,oi.title_snapshot,
                    oi.quantity,oi.unit_price_kobo,oi.subtotal_kobo,
                    oi.fulfilment_status,
                    o.shipping_address,o.payment_method,o.payment_status,
                    o.order_status,o.created_at,
                    b.full_name AS buyer_name,
                    b.email AS buyer_email
                FROM order_items oi
                JOIN orders o ON o.id=oi.order_id
                JOIN users b ON b.id=o.buyer_id
                WHERE oi.seller_id=?
                ORDER BY o.created_at DESC,oi.id DESC
                """,
                (seller_id,),
            ).fetchall()
        return [self._row_to_dict(r) for r in rows]

    def update_fulfilment(
        self,
        seller: SessionUser,
        order_item_id: int,
        status: str,
    ) -> None:
        self._require_role(seller, "seller", "admin")
        status = status.strip().lower()
        if status not in FULFILMENT_STATUSES:
            raise ValidationError("Invalid fulfilment status")

        with self.db.transaction() as conn:
            item = conn.execute(
                """
                SELECT order_id,seller_id
                FROM order_items
                WHERE id=?
                """,
                (order_item_id,),
            ).fetchone()
            if not item:
                raise NotFoundError("Order item not found")

            if seller.role != "admin" and int(item["seller_id"]) != seller.id:
                raise AuthorizationError(
                    "You can update only order items assigned to you"
                )

            conn.execute(
                """
                UPDATE order_items
                SET fulfilment_status=?
                WHERE id=?
                """,
                (status, order_item_id),
            )

            order_id = int(item["order_id"])
            statuses = [
                r["fulfilment_status"]
                for r in conn.execute(
                    """
                    SELECT fulfilment_status
                    FROM order_items
                    WHERE order_id=?
                    """,
                    (order_id,),
                ).fetchall()
            ]
            payment = conn.execute(
                "SELECT payment_status FROM orders WHERE id=?",
                (order_id,),
            ).fetchone()

            overall = self._derive_order_status(
                statuses,
                payment["payment_status"] if payment else "pending",
            )
            conn.execute(
                "UPDATE orders SET order_status=? WHERE id=?",
                (overall, order_id),
            )

    @staticmethod
    def _derive_order_status(
        statuses: Iterable[str],
        payment_status: str,
    ) -> str:
        statuses = list(statuses)
        if not statuses:
            return "pending"
        if all(s == "cancelled" for s in statuses):
            return "cancelled"
        if all(s in {"delivered", "cancelled"} for s in statuses) and any(
            s == "delivered" for s in statuses
        ):
            return "delivered"
        if any(s == "shipped" for s in statuses):
            return "shipped"
        if any(s == "processing" for s in statuses):
            return "processing"
        if payment_status == "paid":
            return "processing"
        return "pending"

    # ---------- administration ----------

    def admin_metrics(self, admin: SessionUser) -> dict[str, Any]:
        self._require_role(admin, "admin")
        with self.db.connect() as conn:
            metrics = {
                "users": conn.execute(
                    "SELECT COUNT(*) AS c FROM users"
                ).fetchone()["c"],
                "buyers": conn.execute(
                    "SELECT COUNT(*) AS c FROM users WHERE role='buyer'"
                ).fetchone()["c"],
                "sellers": conn.execute(
                    "SELECT COUNT(*) AS c FROM users WHERE role='seller'"
                ).fetchone()["c"],
                "products": conn.execute(
                    "SELECT COUNT(*) AS c FROM products"
                ).fetchone()["c"],
                "active_products": conn.execute(
                    "SELECT COUNT(*) AS c FROM products WHERE status='active'"
                ).fetchone()["c"],
                "orders": conn.execute(
                    "SELECT COUNT(*) AS c FROM orders"
                ).fetchone()["c"],
                "paid_revenue_kobo": conn.execute(
                    """
                    SELECT COALESCE(SUM(total_kobo),0) AS total
                    FROM orders
                    WHERE payment_status='paid'
                    """
                ).fetchone()["total"],
            }
        return metrics

    def list_users(self, admin: SessionUser) -> list[dict[str, Any]]:
        self._require_role(admin, "admin")
        with self.db.connect() as conn:
            rows = conn.execute(
                """
                SELECT id,full_name,email,role,is_active,created_at
                FROM users
                ORDER BY created_at DESC,id DESC
                """
            ).fetchall()
        return [self._row_to_dict(r) for r in rows]

    def set_user_active(
        self,
        admin: SessionUser,
        user_id: int,
        active: bool,
    ) -> None:
        self._require_role(admin, "admin")
        if user_id == admin.id and not active:
            raise ValidationError("You cannot deactivate your own administrator account")

        with self.db.transaction() as conn:
            result = conn.execute(
                "UPDATE users SET is_active=? WHERE id=?",
                (1 if active else 0, user_id),
            )
            if result.rowcount != 1:
                raise NotFoundError("User not found")


# ---------------------------------------------------------------------------
# Flet presentation layer
# ---------------------------------------------------------------------------

class BookBridgeUI:
    def __init__(self, page, service: MarketplaceService):
        if ft is None:
            raise RuntimeError("Flet is not installed")
        self.page = page
        self.service = service
        self.user: Optional[SessionUser] = None

        self.search_box = None
        self.category_filter = None

        self.editing_product_id: Optional[int] = None
        self.product_title = None
        self.product_author = None
        self.product_isbn = None
        self.product_category = None
        self.product_description = None
        self.product_price = None
        self.product_stock = None
        self.product_status = None

    def start(self) -> None:
        self.page.title = APP_TITLE
        self.page.padding = 20
        self.page.scroll = "auto"
        try:
            self.page.theme_mode = ft.ThemeMode.LIGHT
        except Exception:
            pass
        self.show_login()

    # ---------- generic UI helpers ----------

    def _set_view(self, controls: list[Any]) -> None:
        self.page.clean()
        self.page.add(*controls)
        self.page.update()

    def _message(self, text: str, error: bool = False) -> None:
        try:
            bar = ft.SnackBar(
                content=ft.Text(text),
                bgcolor="#B00020" if error else "#1B5E20",
            )
            self.page.overlay.append(bar)
            bar.open = True
            self.page.update()
        except Exception:
            # Fallback for older/newer Flet API differences.
            self.page.add(ft.Text(text))
            self.page.update()

    def _guard(self, action, success: Optional[str] = None):
        try:
            result = action()
            if success:
                self._message(success)
            return result
        except BookBridgeError as exc:
            self._message(str(exc), error=True)
        except ValueError as exc:
            self._message(str(exc), error=True)
        except Exception as exc:
            self._message(f"Unexpected error: {exc}", error=True)
        return None

    def _header(self, title: str) -> Any:
        controls = [
            ft.Text(APP_TITLE, size=28, weight="bold"),
            ft.Text(title, size=18),
        ]

        if self.user:
            nav = [ft.Text(f"Signed in as {self.user.full_name} ({self.user.role})")]

            nav.append(
                ft.TextButton(
                    "Marketplace",
                    on_click=lambda e: self.show_marketplace(),
                )
            )
            if self.user.role == "buyer":
                nav.extend(
                    [
                        ft.TextButton("Cart", on_click=lambda e: self.show_cart()),
                        ft.TextButton("Orders", on_click=lambda e: self.show_orders()),
                    ]
                )
            if self.user.role == "seller":
                nav.append(
                    ft.TextButton(
                        "Seller dashboard",
                        on_click=lambda e: self.show_seller_dashboard(),
                    )
                )
            if self.user.role == "admin":
                nav.append(
                    ft.TextButton(
                        "Admin",
                        on_click=lambda e: self.show_admin_dashboard(),
                    )
                )

            nav.append(
                ft.TextButton(
                    "Logout",
                    on_click=lambda e: self.logout(),
                )
            )
            controls.append(ft.Row(nav, wrap=True, spacing=6))

        controls.append(ft.Divider())
        return ft.Column(controls, spacing=8)

    def logout(self) -> None:
        self.user = None
        self.editing_product_id = None
        self.show_login()

    # ---------- authentication views ----------

    def show_login(self) -> None:
        email = ft.TextField(
            label="Email",
            width=420,
            autofocus=True,
        )
        password = ft.TextField(
            label="Password",
            password=True,
            can_reveal_password=True,
            width=420,
        )

        def do_login(_):
            def action():
                user = self.service.login(email.value or "", password.value or "")
                self.user = user
                self.show_marketplace()
            self._guard(action)

        controls = [
            ft.Text(APP_TITLE, size=34, weight="bold"),
            ft.Text("Marketplace for new and pre-owned books", size=17),
            ft.Container(height=10),
            email,
            password,
            ft.ElevatedButton("Sign in", on_click=do_login),
            ft.TextButton(
                "Create buyer or seller account",
                on_click=lambda e: self.show_register(),
            ),
            ft.Divider(),
            ft.Text("Demo accounts", size=16, weight="bold"),
            ft.Text("Buyer: buyer@bookbridge.local / Buyer123!"),
            ft.Text("Seller: seller@bookbridge.local / Seller123!"),
            ft.Text("Admin: admin@bookbridge.local / Admin123!"),
        ]
        self._set_view(
            [
                ft.Container(
                    content=ft.Column(
                        controls,
                        horizontal_alignment="center",
                    ),
                    alignment=ft.alignment.center,
                    padding=30,
                )
            ]
        )

    def show_register(self) -> None:
        full_name = ft.TextField(label="Full name", width=430)
        email = ft.TextField(label="Email", width=430)
        password = ft.TextField(
            label="Password (minimum 8 characters)",
            password=True,
            can_reveal_password=True,
            width=430,
        )
        role = ft.Dropdown(
            label="Account type",
            value="buyer",
            options=[
                ft.dropdown.Option("buyer", "Buyer"),
                ft.dropdown.Option("seller", "Seller"),
            ],
            width=430,
        )

        def do_register(_):
            def action():
                self.service.register(
                    full_name.value or "",
                    email.value or "",
                    password.value or "",
                    role.value or "",
                )
                self._message("Account created. You can now sign in.")
                self.show_login()
            self._guard(action)

        self._set_view(
            [
                self._header("Create account"),
                full_name,
                email,
                password,
                role,
                ft.Row(
                    [
                        ft.ElevatedButton("Register", on_click=do_register),
                        ft.TextButton(
                            "Back to sign in",
                            on_click=lambda e: self.show_login(),
                        ),
                    ]
                ),
            ]
        )

    # ---------- marketplace ----------

    def show_marketplace(self) -> None:
        self.search_box = ft.TextField(
            label="Search title, author, ISBN or keyword",
            expand=True,
        )
        category_options = [ft.dropdown.Option("", "All categories")]
        category_options.extend(
            ft.dropdown.Option(c, c)
            for c in self.service.categories()
        )
        self.category_filter = ft.Dropdown(
            label="Category",
            value="",
            options=category_options,
            width=220,
        )

        def search(_):
            self._render_marketplace_results()

        controls = [
            self._header("Marketplace"),
            ft.Row(
                [
                    self.search_box,
                    self.category_filter,
                    ft.ElevatedButton("Search", on_click=search),
                ],
                wrap=True,
            ),
            ft.Divider(),
        ]

        self._set_view(controls)
        self._render_marketplace_results()

    def _render_marketplace_results(self) -> None:
        query = self.search_box.value if self.search_box else ""
        category = self.category_filter.value if self.category_filter else ""
        products = self.service.list_products(query or "", category or "")

        result_controls: list[Any] = []
        if not products:
            result_controls.append(ft.Text("No matching books found."))
        else:
            for product in products:
                buttons = []
                if self.user and self.user.role == "buyer":
                    buttons.append(
                        ft.ElevatedButton(
                            "Add to cart",
                            on_click=lambda e, pid=product["id"]: self._add_product_to_cart(pid),
                        )
                    )

                body = [
                    ft.Text(product["title"], size=20, weight="bold"),
                    ft.Text(f"Author: {product['author']}"),
                    ft.Text(f"Category: {product['category']}"),
                    ft.Text(f"Seller: {product['seller_name']}"),
                    ft.Text(f"Stock: {product['stock']}"),
                    ft.Text(kobo_to_naira(product["price_kobo"]), size=18, weight="bold"),
                ]
                if product.get("isbn"):
                    body.append(ft.Text(f"ISBN: {product['isbn']}"))
                if product.get("description"):
                    body.append(ft.Text(product["description"]))
                if buttons:
                    body.append(ft.Row(buttons, wrap=True))

                result_controls.append(
                    ft.Card(
                        content=ft.Container(
                            content=ft.Column(body, spacing=5),
                            padding=15,
                        )
                    )
                )

        # Replace everything below the fixed first three marketplace controls.
        while len(self.page.controls) > 3:
            self.page.controls.pop()
        self.page.add(ft.Column(result_controls, spacing=10))
        self.page.update()

    def _add_product_to_cart(self, product_id: int) -> None:
        if not self.user:
            self._message("Sign in as a buyer to add books to the cart", error=True)
            return

        def action():
            self.service.add_to_cart(self.user, product_id, 1)
        if self._guard(action, "Book added to cart") is not None:
            pass

    # ---------- cart / checkout ----------

    def show_cart(self) -> None:
        if not self.user or self.user.role != "buyer":
            self._message("Buyer access is required", error=True)
            self.show_marketplace()
            return

        items = self.service.cart(self.user.id)
        controls: list[Any] = [self._header("Shopping cart")]

        if not items:
            controls.extend(
                [
                    ft.Text("Your cart is empty."),
                    ft.ElevatedButton(
                        "Browse books",
                        on_click=lambda e: self.show_marketplace(),
                    ),
                ]
            )
            self._set_view(controls)
            return

        total = 0
        for item in items:
            total += int(item["subtotal_kobo"])
            qty = ft.TextField(
                value=str(item["quantity"]),
                width=90,
                label="Qty",
            )

            def update_item(_, pid=item["product_id"], field=qty):
                def action():
                    self.service.update_cart_quantity(
                        self.user,
                        pid,
                        int(field.value or "0"),
                    )
                    self.show_cart()
                self._guard(action)

            def remove_item(_, pid=item["product_id"]):
                def action():
                    self.service.remove_from_cart(self.user, pid)
                    self.show_cart()
                self._guard(action)

            controls.append(
                ft.Card(
                    content=ft.Container(
                        content=ft.Column(
                            [
                                ft.Text(item["title"], size=18, weight="bold"),
                                ft.Text(f"Author: {item['author']}"),
                                ft.Text(f"Unit price: {kobo_to_naira(item['price_kobo'])}"),
                                ft.Text(f"Subtotal: {kobo_to_naira(item['subtotal_kobo'])}"),
                                ft.Text(f"Available stock: {item['stock']}"),
                                ft.Row(
                                    [
                                        qty,
                                        ft.OutlinedButton("Update", on_click=update_item),
                                        ft.TextButton("Remove", on_click=remove_item),
                                    ],
                                    wrap=True,
                                ),
                            ]
                        ),
                        padding=12,
                    )
                )
            )

        address = ft.TextField(
            label="Delivery address",
            multiline=True,
            min_lines=2,
            max_lines=3,
        )
        payment = ft.Dropdown(
            label="Payment method",
            value="bank_transfer",
            options=[
                ft.dropdown.Option("bank_transfer", "Bank transfer"),
                ft.dropdown.Option("cash_on_delivery", "Cash on delivery"),
                ft.dropdown.Option(
                    "demo_card",
                    "Demo card (marks payment as paid; no card data collected)",
                ),
            ],
            width=520,
        )

        def place_order(_):
            def action():
                order_id = self.service.checkout(
                    self.user,
                    address.value or "",
                    payment.value or "",
                )
                self._message(f"Order #{order_id} created successfully.")
                self.show_orders()
            self._guard(action)

        controls.extend(
            [
                ft.Divider(),
                ft.Text(f"Cart total: {kobo_to_naira(total)}", size=22, weight="bold"),
                address,
                payment,
                ft.ElevatedButton("Place order", on_click=place_order),
            ]
        )
        self._set_view(controls)

    # ---------- buyer orders ----------

    def show_orders(self) -> None:
        if not self.user or self.user.role != "buyer":
            self._message("Buyer access is required", error=True)
            self.show_marketplace()
            return

        orders = self.service.buyer_orders(self.user.id)
        controls: list[Any] = [self._header("My orders")]

        if not orders:
            controls.append(ft.Text("No orders have been placed yet."))
            self._set_view(controls)
            return

        for order in orders:
            items = self.service.order_items(self.user, int(order["id"]))
            item_controls = [
                ft.Text(
                    f"{i['title_snapshot']} × {i['quantity']} — "
                    f"{kobo_to_naira(i['subtotal_kobo'])} — "
                    f"{i['fulfilment_status']}"
                )
                for i in items
            ]

            controls.append(
                ft.Card(
                    content=ft.Container(
                        content=ft.Column(
                            [
                                ft.Text(
                                    f"Order #{order['id']}",
                                    size=19,
                                    weight="bold",
                                ),
                                ft.Text(f"Date: {order['created_at']}"),
                                ft.Text(f"Total: {kobo_to_naira(order['total_kobo'])}"),
                                ft.Text(
                                    f"Payment: {order['payment_status']} "
                                    f"({order['payment_method']})"
                                ),
                                ft.Text(f"Payment reference: {order['payment_reference']}"),
                                ft.Text(f"Order status: {order['order_status']}"),
                                ft.Text(f"Delivery address: {order['shipping_address']}"),
                                ft.Divider(),
                                *item_controls,
                            ],
                            spacing=4,
                        ),
                        padding=15,
                    )
                )
            )

        self._set_view(controls)

    # ---------- seller dashboard ----------

    def show_seller_dashboard(self) -> None:
        if not self.user or self.user.role != "seller":
            self._message("Seller access is required", error=True)
            self.show_marketplace()
            return

        self._build_product_form()
        product_controls: list[Any] = []

        for product in self.service.seller_products(self.user):
            def edit_product(_, p=product):
                self.editing_product_id = int(p["id"])
                self.show_seller_dashboard()

            product_controls.append(
                ft.Card(
                    content=ft.Container(
                        content=ft.Row(
                            [
                                ft.Column(
                                    [
                                        ft.Text(
                                            f"#{product['id']} {product['title']}",
                                            weight="bold",
                                        ),
                                        ft.Text(
                                            f"{product['author']} | "
                                            f"{product['category']} | "
                                            f"{kobo_to_naira(product['price_kobo'])}"
                                        ),
                                        ft.Text(
                                            f"Stock: {product['stock']} | "
                                            f"Status: {product['status']}"
                                        ),
                                    ],
                                    expand=True,
                                ),
                                ft.OutlinedButton("Edit", on_click=edit_product),
                            ],
                            wrap=True,
                        ),
                        padding=10,
                    )
                )
            )

        order_controls: list[Any] = []
        for item in self.service.seller_orders(self.user.id):
            status_dropdown = ft.Dropdown(
                value=item["fulfilment_status"],
                options=[
                    ft.dropdown.Option(s, s.title())
                    for s in [
                        "pending",
                        "processing",
                        "shipped",
                        "delivered",
                        "cancelled",
                    ]
                ],
                width=180,
            )

            def update_status(
                _,
                item_id=item["id"],
                field=status_dropdown,
            ):
                def action():
                    self.service.update_fulfilment(
                        self.user,
                        int(item_id),
                        field.value,
                    )
                    self.show_seller_dashboard()
                self._guard(action, "Fulfilment status updated")

            order_controls.append(
                ft.Card(
                    content=ft.Container(
                        content=ft.Column(
                            [
                                ft.Text(
                                    f"Order #{item['order_id']} — {item['title_snapshot']}",
                                    size=17,
                                    weight="bold",
                                ),
                                ft.Text(f"Buyer: {item['buyer_name']} ({item['buyer_email']})"),
                                ft.Text(f"Quantity: {item['quantity']}"),
                                ft.Text(f"Subtotal: {kobo_to_naira(item['subtotal_kobo'])}"),
                                ft.Text(f"Payment: {item['payment_status']}"),
                                ft.Text(f"Delivery address: {item['shipping_address']}"),
                                ft.Row(
                                    [
                                        status_dropdown,
                                        ft.ElevatedButton(
                                            "Update fulfilment",
                                            on_click=update_status,
                                        ),
                                    ],
                                    wrap=True,
                                ),
                            ],
                            spacing=4,
                        ),
                        padding=12,
                    )
                )
            )

        controls = [
            self._header("Seller dashboard"),
            ft.Text(
                "Add / edit book listing",
                size=20,
                weight="bold",
            ),
            self.product_title,
            self.product_author,
            self.product_isbn,
            self.product_category,
            self.product_description,
            ft.Row(
                [self.product_price, self.product_stock, self.product_status],
                wrap=True,
            ),
            ft.Row(
                [
                    ft.ElevatedButton(
                        "Save product",
                        on_click=self._save_product_from_form,
                    ),
                    ft.TextButton(
                        "Clear form",
                        on_click=lambda e: self._clear_product_edit(),
                    ),
                ]
            ),
            ft.Divider(),
            ft.Text("My products", size=20, weight="bold"),
            ft.Column(product_controls or [ft.Text("No products yet.")]),
            ft.Divider(),
            ft.Text("Fulfilment queue", size=20, weight="bold"),
            ft.Column(order_controls or [ft.Text("No orders to fulfil yet.")]),
        ]
        self._set_view(controls)

    def _build_product_form(self) -> None:
        existing = None
        if self.editing_product_id and self.user:
            for p in self.service.seller_products(self.user):
                if int(p["id"]) == int(self.editing_product_id):
                    existing = p
                    break

        self.product_title = ft.TextField(
            label="Title",
            value=existing["title"] if existing else "",
        )
        self.product_author = ft.TextField(
            label="Author",
            value=existing["author"] if existing else "",
        )
        self.product_isbn = ft.TextField(
            label="ISBN",
            value=(existing["isbn"] or "") if existing else "",
        )
        self.product_category = ft.TextField(
            label="Category",
            value=existing["category"] if existing else "",
        )
        self.product_description = ft.TextField(
            label="Description",
            value=existing["description"] if existing else "",
            multiline=True,
            min_lines=2,
        )
        self.product_price = ft.TextField(
            label="Price (₦)",
            value=(
                f"{Decimal(existing['price_kobo']) / Decimal(100):.2f}"
                if existing
                else ""
            ),
            width=180,
        )
        self.product_stock = ft.TextField(
            label="Stock",
            value=str(existing["stock"]) if existing else "",
            width=130,
        )
        self.product_status = ft.Dropdown(
            label="Status",
            value=existing["status"] if existing else "active",
            options=[
                ft.dropdown.Option("active", "Active"),
                ft.dropdown.Option("inactive", "Inactive"),
            ],
            width=150,
        )

    def _save_product_from_form(self, _):
        def action():
            pid = self.service.save_product(
                self.user,
                self.product_title.value or "",
                self.product_author.value or "",
                self.product_isbn.value or "",
                self.product_category.value or "",
                self.product_description.value or "",
                self.product_price.value or "",
                self.product_stock.value or "",
                product_id=self.editing_product_id,
                status=self.product_status.value or "active",
            )
            self.editing_product_id = None
            self._message(f"Product #{pid} saved.")
            self.show_seller_dashboard()

        self._guard(action)

    def _clear_product_edit(self) -> None:
        self.editing_product_id = None
        self.show_seller_dashboard()

    # ---------- administrator dashboard ----------

    def show_admin_dashboard(self) -> None:
        if not self.user or self.user.role != "admin":
            self._message("Administrator access is required", error=True)
            self.show_marketplace()
            return

        metrics = self.service.admin_metrics(self.user)
        metric_cards = [
            ("Users", metrics["users"]),
            ("Buyers", metrics["buyers"]),
            ("Sellers", metrics["sellers"]),
            ("Products", metrics["products"]),
            ("Active products", metrics["active_products"]),
            ("Orders", metrics["orders"]),
            ("Paid revenue", kobo_to_naira(metrics["paid_revenue_kobo"])),
        ]

        metric_controls = [
            ft.Card(
                content=ft.Container(
                    content=ft.Column(
                        [
                            ft.Text(label),
                            ft.Text(str(value), size=24, weight="bold"),
                        ]
                    ),
                    padding=15,
                    width=190,
                )
            )
            for label, value in metric_cards
        ]

        user_controls: list[Any] = []
        for account in self.service.list_users(self.user):
            target_active = not bool(account["is_active"])
            action_label = "Activate" if target_active else "Deactivate"

            def toggle_user(
                _,
                uid=account["id"],
                active=target_active,
            ):
                def action():
                    self.service.set_user_active(self.user, int(uid), active)
                    self.show_admin_dashboard()
                self._guard(action)

            user_controls.append(
                ft.Card(
                    content=ft.Container(
                        content=ft.Row(
                            [
                                ft.Column(
                                    [
                                        ft.Text(account["full_name"], weight="bold"),
                                        ft.Text(
                                            f"{account['email']} | "
                                            f"{account['role']} | "
                                            f"{'active' if account['is_active'] else 'inactive'}"
                                        ),
                                    ],
                                    expand=True,
                                ),
                                ft.OutlinedButton(
                                    action_label,
                                    on_click=toggle_user,
                                    disabled=int(account["id"]) == self.user.id,
                                ),
                            ],
                            wrap=True,
                        ),
                        padding=10,
                    )
                )
            )

        self._set_view(
            [
                self._header("Administrator dashboard"),
                ft.Text("Marketplace metrics", size=20, weight="bold"),
                ft.Row(metric_controls, wrap=True),
                ft.Divider(),
                ft.Text("User accounts", size=20, weight="bold"),
                ft.Column(user_controls),
                ft.Divider(),
                ft.Text(
                    "Prototype note: production administration should also include "
                    "audit logging, moderation queues, incident reports and stronger "
                    "administrator authentication."
                ),
            ]
        )


# ---------------------------------------------------------------------------
# Self-tests
# ---------------------------------------------------------------------------

class MarketplaceServiceTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.db = Database(Path(self.tmp.name) / "test.db")
        self.db.initialize(seed_demo=False)
        self.svc = MarketplaceService(self.db)

        self.buyer_id = self.svc.register(
            "Buyer One",
            "buyer@example.com",
            "Buyer123!",
            "buyer",
        )
        self.seller_id = self.svc.register(
            "Seller One",
            "seller@example.com",
            "Seller123!",
            "seller",
        )
        self.buyer = self.svc.login("buyer@example.com", "Buyer123!")
        self.seller = self.svc.login("seller@example.com", "Seller123!")

        self.product_id = self.svc.save_product(
            self.seller,
            "Software Engineering",
            "Ian Sommerville",
            "9780137035151",
            "Computing",
            "Software engineering text",
            12000.00,
            4,
        )

    def tearDown(self):
        self.tmp.cleanup()

    def test_registration_and_login(self):
        user = self.svc.login("buyer@example.com", "Buyer123!")
        self.assertEqual(user.role, "buyer")

    def test_duplicate_registration_is_rejected(self):
        with self.assertRaises(ValidationError):
            self.svc.register(
                "Another",
                "buyer@example.com",
                "Password1!",
                "buyer",
            )

    def test_search_finds_product(self):
        products = self.svc.list_products("Sommerville")
        self.assertEqual(len(products), 1)
        self.assertEqual(products[0]["id"], self.product_id)

    def test_cart_rejects_quantity_above_stock(self):
        with self.assertRaises(ValidationError):
            self.svc.add_to_cart(self.buyer, self.product_id, 5)

    def test_checkout_creates_order_and_reduces_stock(self):
        self.svc.add_to_cart(self.buyer, self.product_id, 2)
        order_id = self.svc.checkout(
            self.buyer,
            "12 University Road, Yola",
            "demo_card",
        )
        orders = self.svc.buyer_orders(self.buyer.id)
        self.assertEqual(orders[0]["id"], order_id)
        self.assertEqual(orders[0]["payment_status"], "paid")

        products = self.svc.list_products("Software Engineering")
        self.assertEqual(products[0]["stock"], 2)
        self.assertEqual(self.svc.cart(self.buyer.id), [])

    def test_seller_updates_fulfilment(self):
        self.svc.add_to_cart(self.buyer, self.product_id, 1)
        self.svc.checkout(
            self.buyer,
            "12 University Road, Yola",
            "demo_card",
        )
        seller_items = self.svc.seller_orders(self.seller.id)
        self.svc.update_fulfilment(
            self.seller,
            seller_items[0]["id"],
            "shipped",
        )
        seller_items = self.svc.seller_orders(self.seller.id)
        self.assertEqual(
            seller_items[0]["fulfilment_status"],
            "shipped",
        )

    def test_seller_cannot_edit_another_sellers_product(self):
        other_id = self.svc.register(
            "Seller Two",
            "seller2@example.com",
            "Seller234!",
            "seller",
        )
        other = self.svc.login("seller2@example.com", "Seller234!")
        with self.assertRaises(AuthorizationError):
            self.svc.save_product(
                other,
                "Changed title",
                "Author",
                "",
                "Computing",
                "",
                1000,
                1,
                product_id=self.product_id,
            )
        self.assertIsInstance(other_id, int)

    def test_cart_quantity_can_be_updated(self):
        self.svc.add_to_cart(self.buyer, self.product_id, 1)
        self.svc.update_cart_quantity(self.buyer, self.product_id, 3)
        self.assertEqual(self.svc.cart(self.buyer.id)[0]["quantity"], 3)

    def test_checkout_rollback_on_stock_change(self):
        self.svc.add_to_cart(self.buyer, self.product_id, 4)

        # Simulate stock reduction by another transaction before checkout.
        with self.db.transaction() as conn:
            conn.execute(
                "UPDATE products SET stock=2 WHERE id=?",
                (self.product_id,),
            )

        with self.assertRaises(ValidationError):
            self.svc.checkout(
                self.buyer,
                "12 University Road, Yola",
                "demo_card",
            )

        with self.db.connect() as conn:
            count = conn.execute(
                "SELECT COUNT(*) AS c FROM orders"
            ).fetchone()["c"]
        self.assertEqual(count, 0)
        self.assertEqual(self.svc.cart(self.buyer.id)[0]["quantity"], 4)


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

def launch_flet() -> None:
    if ft is None:
        raise SystemExit(
            "Flet is not installed.\n"
            "Install it with: pip install flet\n"
            "Then run this file again."
        )

    def main(page) -> None:
        db = Database(DB_FILE)
        db.initialize(seed_demo=True)
        service = MarketplaceService(db)
        BookBridgeUI(page, service).start()

    ft.app(target=main)


def run_self_tests() -> int:
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(
        MarketplaceServiceTests
    )
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    return 0 if result.wasSuccessful() else 1


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="BookBridge books e-commerce marketplace"
    )
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="Run service-layer tests without starting the Flet UI",
    )
    args = parser.parse_args()

    if args.self_test:
        raise SystemExit(run_self_tests())

    launch_flet()
