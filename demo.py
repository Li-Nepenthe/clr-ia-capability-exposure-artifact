#!/usr/bin/env python3
"""Concrete instantiation of the capability-exposure analysis.

Runs on a stock CPython 3 interpreter using only the standard library. There
are no third-party dependencies and no external cryptographic library.

The script instantiates the analyzed identification protocol over a prime-order
subgroup, performs the leakage query the published interface admits, and drives
the resulting impersonation session to the verifier's accept bit. Every claim it
checks is asserted; the final line reports whether all checks passed.
"""

import argparse
import json
import os
import random
import sys

# --------------------------------------------------------------------------
# check harness
# --------------------------------------------------------------------------

CHECKS = []


def check(ident, description, condition, observed):
    """Record one assertion together with what was observed."""
    CHECKS.append(
        {
            "id": ident,
            "description": description,
            "passed": bool(condition),
            "observed": observed,
        }
    )
    status = "ok  " if condition else "FAIL"
    print("    [{}] {} : {} -- {}".format(status, ident, description, observed))
    return bool(condition)


# --------------------------------------------------------------------------
# prime-order group over a safe prime
# --------------------------------------------------------------------------


def small_primes(limit):
    sieve = [True] * (limit + 1)
    sieve[0] = sieve[1] = False
    for i in range(2, int(limit ** 0.5) + 1):
        if sieve[i]:
            for j in range(i * i, limit + 1, i):
                sieve[j] = False
    return [i for i, ok in enumerate(sieve) if ok]


SMALL_PRIMES = small_primes(2000)


def is_probable_prime(n, rng, rounds=16):
    if n < 2:
        return False
    for p in SMALL_PRIMES:
        if n == p:
            return True
        if n % p == 0:
            return False
    d = n - 1
    s = 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for _ in range(rounds):
        a = rng.randrange(2, n - 1)
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(s - 1):
            x = (x * x) % n
            if x == n - 1:
                break
        else:
            return False
    return True


def find_safe_prime(bits, rng):
    """Return (p, q) with q prime, p = 2q + 1 prime, q of the requested width."""
    while True:
        q = rng.getrandbits(bits) | (1 << (bits - 1)) | 1
        q = q - (q % 6) + 5
        if q.bit_length() != bits:
            continue
        for _ in range(20000):
            p = 2 * q + 1
            sieved = True
            for sp in SMALL_PRIMES:
                if sp == 3:
                    continue
                if q % sp == 0 or p % sp == 0:
                    sieved = False
                    break
            if sieved and is_probable_prime(q, rng) and is_probable_prime(p, rng):
                return p, q
            q += 6
            if q.bit_length() != bits:
                break


def subgroup_generator(p, q, rng):
    """A generator of the order-q subgroup of Z_p^*, i.e. the quadratic residues."""
    while True:
        h = rng.randrange(2, p - 1)
        g = pow(h, 2, p)
        if g != 1 and pow(g, q, p) == 1:
            return g


# --------------------------------------------------------------------------
# linear algebra over Z_q
# --------------------------------------------------------------------------


def mat_vec_row(row, mat, q):
    """Row vector times matrix: (1 x n) . (n x m) -> (1 x m)."""
    m = len(mat[0])
    out = [0] * m
    for j in range(m):
        acc = 0
        for i, a in enumerate(row):
            acc += a * mat[i][j]
        out[j] = acc % q
    return out


def mat_mul(left, right, q):
    rows = len(left)
    inner = len(right)
    cols = len(right[0])
    out = [[0] * cols for _ in range(rows)]
    for i in range(rows):
        li = left[i]
        for j in range(cols):
            acc = 0
            for k in range(inner):
                acc += li[k] * right[k][j]
            out[i][j] = acc % q
    return out


def mat_inverse(mat, q):
    """Gauss-Jordan inverse mod prime q; returns None if singular."""
    n = len(mat)
    aug = [list(mat[i]) + [1 if i == j else 0 for j in range(n)] for i in range(n)]
    for col in range(n):
        pivot = None
        for r in range(col, n):
            if aug[r][col] % q != 0:
                pivot = r
                break
        if pivot is None:
            return None
        aug[col], aug[pivot] = aug[pivot], aug[col]
        inv = pow(aug[col][col], q - 2, q)
        aug[col] = [(v * inv) % q for v in aug[col]]
        for r in range(n):
            if r == col:
                continue
            factor = aug[r][col] % q
            if factor:
                aug[r] = [(aug[r][k] - factor * aug[col][k]) % q for k in range(2 * n)]
    return [row[n:] for row in aug]


def random_invertible(n, q, rng):
    while True:
        mat = [[rng.randrange(q) for _ in range(n)] for _ in range(n)]
        inv = mat_inverse(mat, q)
        if inv is not None:
            return mat, inv


# --------------------------------------------------------------------------
# serialization
# --------------------------------------------------------------------------


def enc(value, w):
    """Unsigned big-endian w-bit encoding, leading zeroes included."""
    return format(value, "0{}b".format(w))


def dec(bits):
    return int(bits, 2)


def serialize_state(A, B, w):
    """A_1..A_n then B_11..B_n2, each a fixed-width w-bit big-endian word."""
    parts = [enc(a, w) for a in A]
    for row in B:
        for entry in row:
            parts.append(enc(entry, w))
    return "".join(parts)


# --------------------------------------------------------------------------
# leakage functions
# --------------------------------------------------------------------------


def f_AB(bitstring, n, w, q):
    """The R1 query: parse the serialized state and return enc(x1) || enc(x2)."""
    if len(bitstring) != 3 * n * w:
        return "0" * (2 * w)
    words = [dec(bitstring[i * w:(i + 1) * w]) for i in range(3 * n)]
    if any(word >= q for word in words):
        return "0" * (2 * w)
    A = words[:n]
    if all(a == 0 for a in A):
        return "0" * (2 * w)
    flat = words[n:]
    B = [[flat[2 * i], flat[2 * i + 1]] for i in range(n)]
    X = mat_vec_row(A, B, q)
    return enc(X[0], w) + enc(X[1], w)


def f_A_component(A, w):
    """R2 first query, A-side: return the whole A component."""
    return "".join(enc(a, w) for a in A)


def f_B_with_hardwired_A(B, A_known, w, q):
    """R2 second query, B-side: A is hardwired into the function, return A.B."""
    X = mat_vec_row(A_known, B, q)
    return enc(X[0], w) + enc(X[1], w)


# --------------------------------------------------------------------------
# protocol
# --------------------------------------------------------------------------


class Verifier(object):
    """Honest verifier. Counts every honest-prover oracle call it serves."""

    def __init__(self, p, q, g1, g2, pk, rng):
        self.p = p
        self.q = q
        self.g1 = g1
        self.g2 = g2
        self.pk = pk
        self.rng = rng
        self.prover_oracle_calls = 0

    def fresh_challenge(self):
        return self.rng.randrange(1, self.q)

    def accepts(self, U, c, v1, v2):
        lhs = (pow(self.g1, v1, self.p) * pow(self.g2, v2, self.p)) % self.p
        rhs = (U * pow(self.pk, c, self.p)) % self.p
        return lhs == rhs


def impersonate(verifier, X, rng, p, q, g1, g2):
    """Run one session using only the retained pair X. No prover oracle is used."""
    r1 = rng.randrange(1, q)
    r2 = rng.randrange(1, q)
    U = (pow(g1, r1, p) * pow(g2, r2, p)) % p
    c = verifier.fresh_challenge()
    v1 = (r1 + c * X[0]) % q
    v2 = (r2 + c * X[1]) % q
    return verifier.accepts(U, c, v1, v2), c


def refresh(A, B, q, rng):
    """A product-preserving refresh, not the source's exact Update.

    Draws a non-singular T, sets E = A.T, draws F with E.F = (0,0), and returns
    A' = E, B' = T^-1.B + F. Then A'.B' = A.B, so the decoded pair and the
    public key are both unchanged while both stored components are rerandomized.
    """
    n = len(A)
    T, T_inv = random_invertible(n, q, rng)
    E = mat_vec_row(A, T, q)
    nonzero = next(i for i, e in enumerate(E) if e % q != 0)
    e_inv = pow(E[nonzero], q - 2, q)
    F = [[0, 0] for _ in range(n)]
    for col in range(2):
        vec = [rng.randrange(q) for _ in range(n)]
        vec[nonzero] = 0
        acc = sum(E[i] * vec[i] for i in range(n)) % q
        vec[nonzero] = (-acc * e_inv) % q
        for i in range(n):
            F[i][col] = vec[i]
    B_new = mat_mul(T_inv, B, q)
    B_new = [[(B_new[i][j] + F[i][j]) % q for j in range(2)] for i in range(n)]
    return E, B_new


# --------------------------------------------------------------------------
# main
# --------------------------------------------------------------------------


def main():
    parser = argparse.ArgumentParser(
        description="Concrete instantiation of the capability-exposure analysis."
    )
    parser.add_argument("--n", type=int, default=16, help="matrix dimension (default 16)")
    parser.add_argument("--bits", type=int, default=256, help="bit length of q (default 256)")
    parser.add_argument("--seed", type=int, default=20260813, help="PRNG seed (default fixed)")
    args = parser.parse_args()

    n = args.n
    rng = random.Random(args.seed)

    print("=" * 72)
    print("Concrete instantiation: capability exposure in the published interface")
    print("=" * 72)
    print("parameters: n = {}, |q| = {} bits, seed = {}".format(n, args.bits, args.seed))
    print()

    # -- 1. Setup / KeyGen --------------------------------------------------
    print("[1] Setup and KeyGen")
    p, q = find_safe_prime(args.bits, rng)
    g1 = subgroup_generator(p, q, rng)
    g2 = subgroup_generator(p, q, rng)
    w = q.bit_length()
    print("    safe prime p = 2q + 1, subgroup of prime order q")
    print("    |q| = {} bits, w = ceil(log2 q) = {}".format(q.bit_length(), w))
    check("G1", "g1, g2 lie in the order-q subgroup",
          pow(g1, q, p) == 1 and pow(g2, q, p) == 1 and g1 != 1 and g2 != 1,
          "g1^q = g2^q = 1 mod p")

    # A is drawn from Z_q^n \ {0^n} and B from Z_q^{n x 2}, matching KeyGen.
    while True:
        A = [rng.randrange(q) for _ in range(n)]
        if any(a != 0 for a in A):
            break
    B = [[rng.randrange(q), rng.randrange(q)] for _ in range(n)]
    X = mat_vec_row(A, B, q)
    pk = (pow(g1, X[0], p) * pow(g2, X[1], p)) % p
    print("    sk = (A, B) with A in Z_q^{}, B in Z_q^{}x2".format(n, n))
    print("    X = (x1, x2) = A.B ; pk = g1^x1 . g2^x2")
    print()

    # -- 2. Serialization ---------------------------------------------------
    print("[2] Serialization of the stored state")
    state_bits = serialize_state(A, B, w)
    check("A1", "serialized state occupies exactly 3nw bits",
          len(state_bits) == 3 * n * w,
          "{} bits = 3 * {} * {}".format(len(state_bits), n, w))
    print()

    # -- 3. R1 leakage query ------------------------------------------------
    print("[3] The admissible leakage query of the published interface (R1)")
    leaked = f_AB(state_bits, n, w, q)
    recovered = (dec(leaked[:w]), dec(leaked[w:]))
    check("A2a", "query output width is exactly 2w bits",
          len(leaked) == 2 * w, "{} bits = 2 * {}".format(len(leaked), w))
    check("A2b", "decoded output equals the true decoded pair X",
          list(recovered) == list(X), "recovered X matches A.B")
    print()

    # -- 4. Budget comparison ----------------------------------------------
    print("[4] Budget comparison (nominal leading term only)")
    floor_log2_q = q.bit_length() - 1
    nominal = (3 * n - 2) * floor_log2_q
    query_bits = 2 * w
    print("    serialized state              : {} bits".format(3 * n * w))
    print("    nominal leading term (3n-2)a  : {} bits".format(nominal))
    print("    leakage query                 : {} bits".format(query_bits))
    print("    NOTE: the nominal leading term ignores the subtracted omega(log kappa)")
    print("          slack, so it is NOT the theorem's exact allowance. It is an")
    print("          upper estimate of that allowance, used only for orientation.")
    check("A3", "leakage query is strictly shorter than the nominal leading term",
          query_bits < nominal,
          "{} bits < {} bits (ratio > {:.1f})".format(
              query_bits, nominal, float(nominal) / query_bits))
    print()

    # -- 5. Impersonation session -------------------------------------------
    print("[5] Impersonation session driven from the retained pair")
    verifier = Verifier(p, q, g1, g2, pk, rng)
    accepted, c = impersonate(verifier, recovered, rng, p, q, g1, g2)
    print("    fresh challenge c drawn by the verifier from Z_q^*")
    check("A4", "verification equation g1^v1 . g2^v2 = U . pk^c holds, accept bit",
          accepted, "accept = {}".format(1 if accepted else 0))
    print()

    # -- 6. No honest-prover query ------------------------------------------
    print("[6] Honest-prover oracle usage")
    check("A5", "no honest-prover oracle call was made",
          verifier.prover_oracle_calls == 0,
          "prover oracle calls = {}".format(verifier.prover_oracle_calls))
    print()

    # -- 7. Validity across a refresh ---------------------------------------
    print("[7] The same retained pair after a key refresh")
    A2, B2 = refresh(A, B, q, rng)
    X2 = mat_vec_row(A2, B2, q)
    pk2 = (pow(g1, X2[0], p) * pow(g2, X2[1], p)) % p
    print("    product-preserving refresh, not the source's exact Update")
    check("A6a", "refresh preserves the decoded pair and the public key",
          list(X2) == list(X) and pk2 == pk,
          "A'.B' = A.B and pk unchanged")
    check("A6b", "both stored components actually changed",
          list(A2) != list(A) and B2 != B, "A' != A and B' != B")
    verifier2 = Verifier(p, q, g1, g2, pk2, rng)
    accepted2, _ = impersonate(verifier2, recovered, rng, p, q, g1, g2)
    check("A6c", "the pair retained before the refresh still authenticates",
          accepted2, "accept = {}".format(1 if accepted2 else 0))
    print()

    # -- 8. Component-local reading (R2) ------------------------------------
    print("[8] Two component-local queries (R2)")
    q1_a = f_A_component(A, w)
    q1_b = "0"                       # 1-bit constant on the B side
    q1_len = len(q1_a) + len(q1_b)
    q2_a = "0"                       # 1-bit constant on the A side
    q2_b = f_B_with_hardwired_A(B, [dec(q1_a[i * w:(i + 1) * w]) for i in range(n)], w, q)
    q2_len = len(q2_a) + len(q2_b)
    total = q1_len + q2_len
    recovered_r2 = (dec(q2_b[:w]), dec(q2_b[w:]))
    print("    query 1 (f_A, z_B) returns A  : {} bits = nw + 1".format(q1_len))
    print("    query 2 (z_A, f_B) returns X  : {} bits = 1 + 2w".format(q2_len))
    check("A7a", "two queries total exactly (n+2)w + 2 bits",
          total == (n + 2) * w + 2,
          "{} bits = ({}+2)*{} + 2".format(total, n, w))
    check("A7b", "the pair recovered by the two queries equals the R1 result",
          list(recovered_r2) == list(recovered), "same X as step 3")
    print()

    # -- 9. Negative control -------------------------------------------------
    print("[9] Negative control")
    wrong = ((X[0] + 1) % q, X[1])
    verifier3 = Verifier(p, q, g1, g2, pk, rng)
    accepted3, _ = impersonate(verifier3, wrong, rng, p, q, g1, g2)
    check("A8", "a session driven from an incorrect pair is rejected",
          not accepted3, "accept = {}".format(1 if accepted3 else 0))
    print()

    # -- 10. Source binding --------------------------------------------------
    print("[10] Analyzed source")
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "sources.json"), "r") as handle:
        sources = json.load(handle)
    for entry in sources["analyzed"]:
        print("    title  : {}".format(entry["title"]))
        print("    venue  : {} vol. {}, no. {}, pp. {}".format(
            entry["venue"], entry["volume"], entry["issue"], entry["pages"]))
        print("    doi    : {}".format(entry["doi"]))
        print("    sha256 : {}".format(entry["sha256"]))
        if entry["sha256"] == "FILL-SHA256":
            print("    WARNING: the source hash is a placeholder and was not verified.")
        for key, value in entry["locators"].items():
            print("    locator: {:<28} {}".format(key, value))
    print("    The analyzed article is not redistributed here; it is identified")
    print("    by hash and locator only.")
    print()

    # -- summary -------------------------------------------------------------
    failed = [c["id"] for c in CHECKS if not c["passed"]]
    print("=" * 72)
    if failed:
        print("RESULT: {} of {} checks FAILED: {}".format(
            len(failed), len(CHECKS), ", ".join(failed)))
        return 1
    print("RESULT: all {} checks passed.".format(len(CHECKS)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
