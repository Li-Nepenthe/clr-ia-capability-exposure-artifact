#!/usr/bin/env python3
"""NIST P-256 (secp256r1) in the Python standard library only.

The accompanying paper's experiments run the identification protocol over the
standardized P-256 elliptic-curve group. (The analyzed CLR-IA paper also
measures its protocol over an elliptic-curve group, there the curve
y^2 = x^3 - 2x.) This module provides that group: points are exchanged in affine
coordinates, and scalar multiplication works internally in Jacobian
coordinates (one field inversion per multiplication). It performs no key
agreement or signing; it only supplies the group operations the protocol needs.
``check_p256.py`` compares it with OpenSSL.
"""

# secp256r1 domain parameters (NIST FIPS 186-4 / SEC 2 v2).
P = 0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF
A = P - 3
B = 0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B
GX = 0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296
GY = 0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5
N = 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551

# An affine point is a tuple (x, y) of integers, or None for the identity.
# A Jacobian point (X, Y, Z) stands for (X/Z^2, Y/Z^3); Z = 0 is the identity.


def is_on_curve(pt):
    if pt is None:
        return True
    x, y = pt
    return (y * y - (x * x * x + A * x + B)) % P == 0


def add(p1, p2):
    """Affine point addition."""
    if p1 is None:
        return p2
    if p2 is None:
        return p1
    x1, y1 = p1
    x2, y2 = p2
    if x1 == x2 and (y1 + y2) % P == 0:
        return None
    if p1 == p2:
        lam = (3 * x1 * x1 + A) * pow(2 * y1, -1, P) % P
    else:
        lam = (y2 - y1) * pow(x2 - x1, -1, P) % P
    x3 = (lam * lam - x1 - x2) % P
    y3 = (lam * (x1 - x3) - y1) % P
    return (x3, y3)


def _jdouble(pt):
    X1, Y1, Z1 = pt
    if Z1 == 0 or Y1 == 0:
        return (1, 1, 0)
    # a = -3 (dbl-2001-b)
    delta = Z1 * Z1 % P
    gamma = Y1 * Y1 % P
    beta = X1 * gamma % P
    alpha = 3 * (X1 - delta) * (X1 + delta) % P
    X3 = (alpha * alpha - 8 * beta) % P
    Z3 = ((Y1 + Z1) * (Y1 + Z1) - gamma - delta) % P
    Y3 = (alpha * (4 * beta - X3) - 8 * gamma * gamma) % P
    return (X3, Y3, Z3)


def _jadd_affine(pt, q):
    """Jacobian point plus affine point (mixed addition)."""
    X1, Y1, Z1 = pt
    if Z1 == 0:
        return (q[0], q[1], 1)
    x2, y2 = q
    Z1Z1 = Z1 * Z1 % P
    U2 = x2 * Z1Z1 % P
    S2 = y2 * Z1 * Z1Z1 % P
    H = (U2 - X1) % P
    r = (S2 - Y1) % P
    if H == 0:
        if r == 0:
            return _jdouble(pt)
        return (1, 1, 0)
    HH = H * H % P
    HHH = H * HH % P
    V = X1 * HH % P
    X3 = (r * r - HHH - 2 * V) % P
    Y3 = (r * (V - X3) - Y1 * HHH) % P
    Z3 = Z1 * H % P
    return (X3, Y3, Z3)


def _to_affine(pt):
    X, Y, Z = pt
    if Z == 0:
        return None
    zi = pow(Z, -1, P)
    zi2 = zi * zi % P
    return (X * zi2 % P, Y * zi2 * zi % P)


def mul(k, pt):
    """Scalar multiplication k*pt (left-to-right double-and-add)."""
    k %= N
    if k == 0 or pt is None:
        return None
    acc = (1, 1, 0)
    for bit in bin(k)[2:]:
        acc = _jdouble(acc)
        if bit == "1":
            acc = _jadd_affine(acc, pt)
    return _to_affine(acc)


G = (GX, GY)
assert is_on_curve(G)
