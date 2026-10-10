#!/usr/bin/env python3
"""Separate-process adversary; stdin is the only protocol/secret input.

No repository module is imported. The hook covers Python open audit events
after script start, not startup or all native accesses. Runtime inputs include
OS entropy and the recorded environment. This is instrumentation, not a sandbox.
"""
import sys

OPEN_EVENTS = []


def audit(event, args):
    if event == "open":
        OPEN_EVENTS.append({"path": str(args[0]), "mode": str(args[1]),
                            "flags": args[2]})


sys.addaudithook(audit)
import hashlib
import json
import os
import random


def exact(obj, keys):
    if not isinstance(obj, dict) or set(obj) != set(keys):
        raise ValueError("input field whitelist mismatch: " + str(keys))
    return obj


def emit(obj):
    print(json.dumps(obj, separators=(",", ":")), flush=True)


class PeerAbort(Exception):
    pass


def receive():
    raw = sys.stdin.readline()
    if not raw:
        raise EOFError("world closed stdin")
    obj = json.loads(raw)
    if obj.get("type") == "abort":
        exact(obj, ["type", "reason"])
        raise PeerAbort(obj["reason"])
    return obj


MESSAGE_KEYS = {
    "M1": ["idU", "Ru1", "Ru2", "Ti"],
    "M2": ["idS", "Rs1", "Rs2", "cS", "Tj"],
    "M3": ["idU", "vu1", "vu2", "cU", "Ti_prime"],
    "M4": ["idS", "vs1", "vs2", "Tj_prime"],
}


def recv_message(name):
    envelope = exact(receive(), ["type", "message"])
    if envelope["type"] != "message":
        raise ValueError("expected message")
    return exact(envelope["message"], MESSAGE_KEYS[name])


def send_message(message):
    emit({"type": "message", "message": message})


def session_key(public, dh):
    # Test hash convention: JSON array gives unambiguous types and boundaries.
    data = [public["idU"], public["idS"], dh[0], dh[1]]
    encoded = json.dumps(data, ensure_ascii=True, separators=(",", ":")).encode("ascii")
    return hashlib.sha256(encoded).hexdigest()


def accepts(public, role, commitments, challenge, response):
    p, g1, g2 = public["p"], public["g1"], public["g2"]
    return (pow(g1, response[0], p) * pow(g2, response[1], p)) % p == (
        commitments[0] * commitments[1] * pow(public["pk" + role], challenge, p)) % p


def fresh(timestamp, now, window):
    return 0 <= now - timestamp <= window


def h1(start):
    exact(start, ["scenario", "role", "public", "X", "timestamp", "now", "window"])
    p = start["public"]
    q, modulus = p["q"], p["p"]
    role, x = start["role"], start["X"]
    # No seed comes from the world. Only this process samples its ephemerals.
    rng = random.SystemRandom()
    r = [rng.randrange(1, q), rng.randrange(1, q)]
    own_r = [pow(p["g1"], r[0], modulus), pow(p["g2"], r[1], modulus)]
    timestamp = start["timestamp"]
    emit({"type": "ready"})
    if role == "U":
        send_message(dict(idU=p["idU"], Ru1=own_r[0], Ru2=own_r[1], Ti=timestamp))
        m2 = recv_message("M2")
        if m2["idS"] != p["idS"] or not fresh(m2["Tj"], start["now"], start["window"]):
            raise ValueError("invalid server identity or timestamp")
        c_u = rng.randrange(1, q)
        v = [(r[i] + m2["cS"] * x[i]) % q for i in range(2)]
        send_message(dict(idU=p["idU"], vu1=v[0], vu2=v[1], cU=c_u, Ti_prime=timestamp))
        m4 = recv_message("M4")
        peer_ok = m4["idS"] == p["idS"] and fresh(m4["Tj_prime"], start["now"], start["window"]) and accepts(
            p, "S", [m2["Rs1"], m2["Rs2"]], c_u, [m4["vs1"], m4["vs2"]])
        dh = [pow(m2["Rs1"], r[0], modulus), pow(m2["Rs2"], r[1], modulus)]
    elif role == "S":
        m1 = recv_message("M1")
        if m1["idU"] != p["idU"] or not fresh(m1["Ti"], start["now"], start["window"]):
            raise ValueError("invalid user identity or timestamp")
        c_s = rng.randrange(1, q)
        send_message(dict(idS=p["idS"], Rs1=own_r[0], Rs2=own_r[1], cS=c_s, Tj=timestamp))
        m3 = recv_message("M3")
        peer_ok = m3["idU"] == p["idU"] and fresh(m3["Ti_prime"], start["now"], start["window"]) and accepts(
            p, "U", [m1["Ru1"], m1["Ru2"]], c_s, [m3["vu1"], m3["vu2"]])
        if not peer_ok:
            raise ValueError("honest user response invalid")
        v = [(r[i] + m3["cU"] * x[i]) % q for i in range(2)]
        send_message(dict(idS=p["idS"], vs1=v[0], vs2=v[1], Tj_prime=timestamp))
        dh = [pow(m1["Ru1"], r[0], modulus), pow(m1["Ru2"], r[1], modulus)]
    else:
        raise ValueError("role must be U or S")
    return {"own_ephemeral": r, "peer_accepted_by_adversary": peer_ok,
            "dh": dh, "key": session_key(p, dh), "aborted": False}


def h2(start):
    exact(start, ["scenario", "role", "public", "transcript", "secret"])
    p, role = start["public"], start["role"]
    q, modulus = p["q"], p["p"]
    tr = exact(start["transcript"], ["M1", "M2", "M3", "M4"])
    for name, fields in MESSAGE_KEYS.items():
        exact(tr[name], fields)
    secret = start["secret"]
    if secret["kind"] == "current_sk":
        exact(secret, ["kind", "A", "B"])
        a, b = secret["A"], secret["B"]
        if not isinstance(a, list) or len(a) < 16 or not isinstance(b, list) or len(b) != len(a):
            raise ValueError("current_sk dimensions")
        if any(not isinstance(row, list) or len(row) != 2 for row in b):
            raise ValueError("current_sk matrix width")
        if any(type(v) is not int or not 0 <= v < q for v in a + [v for row in b for v in row]) or not any(a):
            raise ValueError("current_sk field range or zero A")
        x = [sum(a * row[j] for a, row in zip(secret["A"], secret["B"])) % q for j in range(2)]
    elif secret["kind"] == "product_bits":
        exact(secret, ["kind", "bits"])
        bits, w = secret["bits"], p["w"]
        if len(bits) != 2 * w or set(bits) - {"0", "1"}:
            raise ValueError("noncanonical product encoding")
        x = [int(bits[:w], 2), int(bits[w:], 2)]
        if any(v >= q for v in x):
            raise ValueError("product coordinate outside Zq")
    elif secret["kind"] == "control_vector":
        exact(secret, ["kind", "X"])
        x = secret["X"]
    else:
        raise ValueError("secret interface kind")
    if role == "U":
        v = [tr["M3"]["vu1"], tr["M3"]["vu2"]]
        c = tr["M2"]["cS"]
        own = [tr["M1"]["Ru1"], tr["M1"]["Ru2"]]
        peer = [tr["M2"]["Rs1"], tr["M2"]["Rs2"]]
    elif role == "S":
        v = [tr["M4"]["vs1"], tr["M4"]["vs2"]]
        c = tr["M3"]["cU"]
        own = [tr["M2"]["Rs1"], tr["M2"]["Rs2"]]
        peer = [tr["M1"]["Ru1"], tr["M1"]["Ru2"]]
    else:
        raise ValueError("role must be U or S")
    recovered = [(v[i] - c * x[i]) % q for i in range(2)]
    commitment = [pow(p["g1"], recovered[0], modulus) == own[0],
                  pow(p["g2"], recovered[1], modulus) == own[1]]
    dh = [pow(peer[i], recovered[i], modulus) for i in range(2)]
    return {"recovered_ephemeral": recovered, "commitment_consistency": commitment,
            "dh": dh, "key": session_key(p, dh), "aborted": False}


def main():
    try:
        start = receive()
        exact(start["public"], ["p", "q", "g1", "g2", "w", "idU", "idS", "pkU", "pkS"])
        if start["scenario"] not in ("H1", "H2"):
            raise ValueError("scenario must be H1 or H2")
        result = h1(start) if start["scenario"] == "H1" else h2(start)
    except PeerAbort as exc:
        result = {"aborted": True, "reason": str(exc)}
    except Exception as exc:
        result = {"aborted": True, "error": type(exc).__name__ + ": " + str(exc)}
    result["audit"] = {"open_events_after_script_start": OPEN_EVENTS,
                       "cwd": os.getcwd(), "environment": dict(os.environ),
                       "argv": sys.argv, "sys_path": sys.path,
                       "isolation_flag": sys.flags.isolated,
                       "no_bytecode_flag": sys.flags.dont_write_bytecode,
                       "no_site_flag": sys.flags.no_site,
                       "python": sys.version,
                       "coverage": "Python open audit events after script start; not interpreter startup, all native accesses, or an OS file audit; not a sandbox"}
    emit({"type": "result", "result": result})


if __name__ == "__main__":
    main()
