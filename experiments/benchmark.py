#!/usr/bin/env python3
"""Measured evaluation of the key-product leakage attack over a standard curve.

This benchmark accompanies the paper's experimental-validation subsection. It
reuses the correctness logic of ``demo.py`` (matrix algebra, encodings, the
leakage functions and the key update) and runs it over the NIST P-256 group
(``p256.py``, checked against OpenSSL by ``check_p256.py``). The analyzed
CLR-IA paper also measures its protocol over an elliptic-curve group, there
the curve y^2 = x^3 - 2x. For dimensions n = 16, 32, 64 it records, over many
trials:

  * the success rate of impersonation from the leaked key product, for each of
    the three legal acquisition paths (joint query, split queries on one key,
    split queries across a refresh), and a negative control in which a random
    pair is submitted instead;
  * the number of leaked bits and its fraction of the stored key, against the
    advertised leakage allowance;
  * the wall-clock cost of the leakage query, an impersonation session, an
    honest session and one key update (median and 5th/95th percentiles over
    interleaved repetitions).

It then runs the two MEC session attacks under the corrected checks and records
their success and cost. The algebraic facts are proved in the paper and checked
for all parameters in the Lean development; the runs here are execution
witnesses that also supply concrete success rates and timings. Only the Python
standard library and the two local modules are used.

Usage:
  python3 benchmark.py [--trials N] [--timing-reps R] [--refresh-trials M]
                       [--dims n ...] [--seed S] [--out FILE]
"""

import argparse
import gc
import hashlib
import json
import math
import os
import platform
import random
import sys
import time

_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
for _p in (_HERE, _ROOT):
    if _p not in sys.path:
        sys.path.insert(0, _p)

import p256
from demo import (
    dec,
    f_AB,
    f_A_component,
    f_B_with_hardwired_A,
    mat_vec_row,
    serialize_state,
    update,
    UpdateFailed,
)

Q = p256.N
W = Q.bit_length()  # 256


# --------------------------------------------------------------------------
# group: X = (x1, x2) is encoded as the point x1*G1 + x2*G2
# --------------------------------------------------------------------------


class Group(object):
    def __init__(self, rng):
        self.G1 = p256.G
        # a second generator with unknown discrete log; the attack never uses s
        self.G2 = p256.mul(rng.randrange(2, Q), self.G1)

    def combine(self, x1, x2):
        return p256.add(p256.mul(x1, self.G1), p256.mul(x2, self.G2))


def keygen(dim, rng):
    A = [rng.randrange(0, Q) for _ in range(dim)]
    while all(a == 0 for a in A):
        A = [rng.randrange(0, Q) for _ in range(dim)]
    B = [[rng.randrange(0, Q) for _ in range(2)] for _ in range(dim)]
    X = tuple(mat_vec_row(A, B, Q))  # the key product (x1, x2)
    return A, B, X


def verifier_accepts(grp, pk, U, c, v):
    lhs = grp.combine(v[0], v[1])
    rhs = p256.add(U, p256.mul(c, pk))
    return lhs == rhs


def prove_from_X(grp, X, c, rng):
    r1 = rng.randrange(1, Q)
    r2 = rng.randrange(1, Q)
    U = grp.combine(r1, r2)
    v = ((r1 + c * X[0]) % Q, (r2 + c * X[1]) % Q)
    return U, v


# --------------------------------------------------------------------------
# the three legal ways to obtain X, reusing the demo leakage functions
# --------------------------------------------------------------------------


def leak_joint(A, B):
    """One joint query on the whole key; returns decoded X and the output width."""
    bits = f_AB(serialize_state(A, B, W), len(A), W, Q)
    X = (dec(bits[:W]), dec(bits[W:]))
    return X, len(bits)


def leak_split(A, B):
    """Two component-local queries on one key."""
    a_bits = f_A_component(A, W)
    x_bits = f_B_with_hardwired_A(B, A, W, Q)
    X = (dec(x_bits[:W]), dec(x_bits[W:]))
    return X, len(a_bits) + len(x_bits)


def leak_cross_refresh(A, B, rng):
    """Read A in round i, refresh, then read only the refreshed B in round i+1."""
    a_bits = f_A_component(A, W)          # round i: returns A_i
    A2, B2, _ = update(A, B, Q, rng)      # the original update; keeps A_i*B' = X
    x_bits = f_B_with_hardwired_A(B2, A, W, Q)  # round i+1: returns A_i*B_{i+1} = X
    X = (dec(x_bits[:W]), dec(x_bits[W:]))
    return X, len(a_bits) + len(x_bits)


# --------------------------------------------------------------------------
# MEC procedure under the corrected checks (second base g2)
# --------------------------------------------------------------------------


def mec_commit(grp, rng):
    r1 = rng.randrange(1, Q)
    r2 = rng.randrange(1, Q)
    R1 = p256.mul(r1, grp.G1)
    R2 = p256.mul(r2, grp.G2)
    return (r1, r2), (R1, R2)


def mec_session_key(id_u, id_s, R_peer, r_self):
    """K = H(id_u, id_s, D1, D2) with D_k = r_self^k * R_peer^k."""
    D1 = p256.mul(r_self[0], R_peer[0])
    D2 = p256.mul(r_self[1], R_peer[1])
    data = json.dumps([id_u, id_s, D1, D2], separators=(",", ":")).encode()
    return hashlib.sha256(data).hexdigest()


def mec_new_session_impersonation(grp, rng):
    """Adversary holds the registered X_U and is accepted as U by honest S;
    it also computes S's session key."""
    _, _, X_U = keygen(16, rng)
    pk_U = grp.combine(X_U[0], X_U[1])
    id_u, id_s = "U", "S"
    # adversary (as U) and honest S exchange commitments
    r_adv, R_adv = mec_commit(grp, rng)
    r_s, R_s = mec_commit(grp, rng)
    c_s = rng.randrange(1, Q)
    # adversary's response uses the actual X_U
    v = ((r_adv[0] + c_s * X_U[0]) % Q, (r_adv[1] + c_s * X_U[1]) % Q)
    # S's corrected check: v1*G1 + v2*G2 == R_adv1 + R_adv2 + c_s*pk_U
    lhs = grp.combine(v[0], v[1])
    rhs = p256.add(p256.add(R_adv[0], R_adv[1]), p256.mul(c_s, pk_U))
    accepted = (lhs == rhs)
    # adversary computes the same session key S derives
    k_adv = mec_session_key(id_u, id_s, R_s, r_adv)
    k_s = mec_session_key(id_u, id_s, R_adv, r_s)
    return accepted and (k_adv == k_s)


def mec_past_session_recovery(grp, rng):
    """From a recorded honest transcript of a user session and the user's later
    complete key, recover the old nonce and recompute the past session key. The
    original update runs between the recorded session and the compromise.
    Returns (recovered, refresh_succeeded)."""
    A_U, B_U, X_U = keygen(16, rng)
    id_u, id_s = "U", "S"
    r_u, R_u = mec_commit(grp, rng)
    r_s, R_s = mec_commit(grp, rng)
    c_s = rng.randrange(1, Q)
    v_u = ((r_u[0] + c_s * X_U[0]) % Q, (r_u[1] + c_s * X_U[1]) % Q)
    k_true = mec_session_key(id_u, id_s, R_s, r_u)
    # the user's key is refreshed after the session; by invariance the product
    # is unchanged whether or not a given refresh returns a key
    refreshed = True
    try:
        A_U, B_U, _ = update(A_U, B_U, Q, rng)
    except UpdateFailed:
        refreshed = False
    # later: the adversary obtains the complete key (A', B') and computes its
    # product; the transcript (R_u, R_s, c_s, v_u) is public.
    X_later = mat_vec_row(A_U, B_U, Q)
    r_rec = ((v_u[0] - c_s * X_later[0]) % Q, (v_u[1] - c_s * X_later[1]) % Q)
    k_rec = mec_session_key(id_u, id_s, R_s, r_rec)
    return (k_rec == k_true), refreshed


# --------------------------------------------------------------------------
# measurement helpers
# --------------------------------------------------------------------------


def lower_bound_all_success(trials, alpha=0.05):
    """Two-sided Clopper-Pearson lower bound when every trial succeeded."""
    return (alpha / 2) ** (1.0 / trials)


def summarize(samples):
    s = sorted(samples)
    n = len(s)

    def pct(p):
        k = (n - 1) * p
        lo, hi = int(math.floor(k)), int(math.ceil(k))
        return s[lo] + (s[hi] - s[lo]) * (k - lo)

    return {"median_ms": 1e3 * pct(0.5), "p5_ms": 1e3 * pct(0.05),
            "p95_ms": 1e3 * pct(0.95), "mean_ms": 1e3 * sum(s) / n, "runs": n}


def time_interleaved(fns, reps, warmup=5):
    """Time each function `reps` times, interleaving them and rotating their
    order every repetition so that drift affects all of them alike."""
    names = list(fns)
    out = {k: [] for k in names}
    for _ in range(warmup):
        for k in names:
            fns[k]()
    gc_was_enabled = gc.isenabled()
    gc.disable()
    try:
        for i in range(reps):
            order = names[i % len(names):] + names[:i % len(names)]
            for k in order:
                t0 = time.perf_counter()
                fns[k]()
                out[k].append(time.perf_counter() - t0)
    finally:
        if gc_was_enabled:
            gc.enable()
    return {k: summarize(v) for k, v in out.items()}


def log(msg):
    print(msg, flush=True)


# --------------------------------------------------------------------------
# experiment
# --------------------------------------------------------------------------


def run(dims, trials, timing_reps, refresh_trials, seed):
    rng = random.Random(seed)
    grp = Group(rng)
    results = {"group": "NIST P-256 (secp256r1)", "field_bits": W,
               "trials": trials, "timing_reps": timing_reps,
               "refresh_trials": refresh_trials, "seed": seed,
               "success_lower_bound_95": lower_bound_all_success(trials),
               "dims": {}}
    for dim in dims:
        t_start = time.perf_counter()
        stored_bits = 3 * dim * W
        advertised_fraction = (3 * dim - 2) / (3 * dim)
        succ = {"joint": 0, "split": 0, "cross_refresh": 0}
        control_accepted = 0
        update_failures = 0
        leaked = {}
        for t in range(trials):
            A, B, X = keygen(dim, rng)
            pk = grp.combine(X[0], X[1])
            for name, fn in (("joint", leak_joint), ("split", leak_split)):
                Xl, nbits = fn(A, B)
                leaked[name] = nbits
                c = rng.randrange(1, Q)
                U, v = prove_from_X(grp, Xl, c, rng)
                if Xl == X and verifier_accepts(grp, pk, U, c, v):
                    succ[name] += 1
            try:
                Xc, nbits = leak_cross_refresh(A, B, rng)
            except UpdateFailed:
                update_failures += 1
            else:
                leaked["cross_refresh"] = nbits
                c = rng.randrange(1, Q)
                U, v = prove_from_X(grp, Xc, c, rng)
                if Xc == X and verifier_accepts(grp, pk, U, c, v):
                    succ["cross_refresh"] += 1
            # negative control: a random pair in place of the leaked one
            Xr = (rng.randrange(0, Q), rng.randrange(0, Q))
            c = rng.randrange(1, Q)
            U, v = prove_from_X(grp, Xr, c, rng)
            if verifier_accepts(grp, pk, U, c, v):
                control_accepted += 1
            if (t + 1) % 100 == 0:
                log("  n={}: {}/{} trials".format(dim, t + 1, trials))

        # timing on one fresh key
        A, B, X = keygen(dim, rng)
        pk = grp.combine(X[0], X[1])
        state_bits = serialize_state(A, B, W)
        leaked_bits = f_AB(state_bits, dim, W, Q)

        def leakage_query():
            # the device-side evaluation of the one joint query
            f_AB(state_bits, dim, W, Q)

        def impersonation_session():
            # the adversary decodes the leaked bits and answers a fresh
            # challenge; the verifier checks the response
            Xl = (dec(leaked_bits[:W]), dec(leaked_bits[W:]))
            c = rng.randrange(1, Q)
            U, v = prove_from_X(grp, Xl, c, rng)
            assert verifier_accepts(grp, pk, U, c, v)

        def honest_session():
            # the honest prover computes A*B in every execution (source
            # behaviour), then commits and responds; the verifier checks
            Xh = mat_vec_row(A, B, Q)
            c = rng.randrange(1, Q)
            U, v = prove_from_X(grp, Xh, c, rng)
            assert verifier_accepts(grp, pk, U, c, v)

        timing = time_interleaved(
            {"leakage_query": leakage_query,
             "impersonation_session": impersonation_session,
             "honest_session": honest_session}, timing_reps)

        def key_update():
            try:
                update(A, B, Q, rng)
            except UpdateFailed:
                pass

        timing.update(time_interleaved({"key_update": key_update},
                                       refresh_trials, warmup=2))
        results["dims"][str(dim)] = {
            "stored_key_bits": stored_bits,
            "leaked_bits": leaked,
            "leaked_fraction_joint": leaked["joint"] / stored_bits,
            "advertised_fraction": advertised_fraction,
            "success": succ,
            "control_random_pair_accepted": control_accepted,
            "update_failures": update_failures,
            "timing": timing,
            "ratio_impersonation_to_honest": (
                timing["impersonation_session"]["median_ms"]
                / timing["honest_session"]["median_ms"]),
            "elapsed_s": time.perf_counter() - t_start,
        }
        log("n={} done in {:.0f} s".format(dim, time.perf_counter() - t_start))

    # MEC, at the paper's dim = 16, user-side session
    rng2 = random.Random(seed + 1)
    grp2 = Group(rng2)
    mec_imp = sum(mec_new_session_impersonation(grp2, rng2) for _ in range(trials))
    log("  MEC impersonation done")
    mec_rec = mec_refresh_fail = 0
    for _ in range(trials):
        ok, refreshed = mec_past_session_recovery(grp2, rng2)
        mec_rec += ok
        mec_refresh_fail += (not refreshed)
    log("  MEC recovery done")
    mec_timing = time_interleaved(
        {"impersonation": lambda: mec_new_session_impersonation(grp2, rng2),
         "recovery": lambda: mec_past_session_recovery(grp2, rng2)},
        timing_reps)
    results["mec"] = {
        "dim": 16,
        "role": "user-side session",
        "impersonation_success": mec_imp,
        "recovery_success": mec_rec,
        "recovery_refresh_failures": mec_refresh_fail,
        "timing": mec_timing,
    }
    results["environment"] = {
        "python": platform.python_version(),
        "implementation": platform.python_implementation(),
        "platform": platform.platform(),
        "processor": platform.processor(),
    }
    return results


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--trials", type=int, default=1000)
    ap.add_argument("--timing-reps", type=int, default=200)
    ap.add_argument("--refresh-trials", type=int, default=100)
    ap.add_argument("--seed", type=int, default=20261119)
    ap.add_argument("--dims", type=int, nargs="+", default=[16, 32, 64])
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    res = run(args.dims, args.trials, args.timing_reps, args.refresh_trials,
              args.seed)
    text = json.dumps(res, indent=2)
    if args.out:
        with open(args.out, "w") as fh:
            fh.write(text + "\n")
    # human summary
    for dim, d in res["dims"].items():
        tm = d["timing"]
        log("n = {}: stored {} bits; joint leak {} bits = {:.2f}% "
            "vs advertised {:.1f}%".format(
                dim, d["stored_key_bits"], d["leaked_bits"]["joint"],
                100 * d["leaked_fraction_joint"], 100 * d["advertised_fraction"]))
        log("        success {}/{} (joint), {}/{} (split), {}/{} (cross-refresh); "
            "random pair accepted {}/{}; update failures {}".format(
                d["success"]["joint"], args.trials,
                d["success"]["split"], args.trials,
                d["success"]["cross_refresh"], args.trials,
                d["control_random_pair_accepted"], args.trials,
                d["update_failures"]))
        log("        median ms: leakage query {:.3f}, impersonation {:.3f}, "
            "honest {:.3f}, key update {:.3f}; ratio {:.3f}".format(
                tm["leakage_query"]["median_ms"],
                tm["impersonation_session"]["median_ms"],
                tm["honest_session"]["median_ms"],
                tm["key_update"]["median_ms"],
                d["ratio_impersonation_to_honest"]))
    m = res["mec"]
    log("MEC (n=16): impersonation {}/{}, recovery {}/{}; median {:.3f} ms, "
        "{:.3f} ms".format(
            m["impersonation_success"], args.trials,
            m["recovery_success"], args.trials,
            m["timing"]["impersonation"]["median_ms"],
            m["timing"]["recovery"]["median_ms"]))
    log("all-success 95% lower bound: {:.4f}".format(res["success_lower_bound_95"]))
    return 0


if __name__ == "__main__":
    sys.exit(main())
