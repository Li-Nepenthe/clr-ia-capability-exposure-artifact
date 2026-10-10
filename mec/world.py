#!/usr/bin/env python3
"""Offline honest world and checks for the MEC session attacks. Standard library only.

Public artifact version: only file locations, provenance fields and the redaction
of local paths in the written record differ from the version that produced the
private records; the protocol, oracle, checks and adversary are unchanged.
"""
import argparse
import datetime
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import platform
import queue
import random
import re
import subprocess
import sys
import tempfile
import threading
import traceback

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
spec = importlib.util.spec_from_file_location("mec_reused_demo", ROOT / "demo.py")
demo = importlib.util.module_from_spec(spec)
spec.loader.exec_module(demo)
# The analyzed article is not redistributed (copyright). sources.json gives its
# SHA-256; a local copy placed at the repository root is hashed if present.
SOURCE = ROOT / "CLR-IA_An_Efficient_Identity_Authentication_Protocol_With_Continuous_Leakage_Resilience_for_Mobile_Edge_Computing.pdf"
TASK_ID = "artifact-mec"
RECORDS = ROOT / "mec/records"


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def key(public, dh):
    data = [public["idU"], public["idS"], dh[0], dh[1]]
    return hashlib.sha256(json.dumps(data, ensure_ascii=True, separators=(",", ":")).encode("ascii")).hexdigest()


def fields(value, prefix=""):
    result = []
    if isinstance(value, dict):
        for name, child in value.items():
            item = prefix + "." + name if prefix else name
            result.append(item)
            result.extend(fields(child, item))
    elif isinstance(value, list) and value:
        result.extend(fields(value[0], prefix + "[]"))
    return result


class Child:
    """No world data is written to its temporary cwd or command/environment."""
    def __init__(self, world, initial):
        self.world = world
        self.temp = tempfile.TemporaryDirectory(prefix="mec-adversary-")
        # Windows normalizes environment names to uppercase in os.environ.
        self.env = {name.upper(): os.environ[name] for name in ("SystemRoot", "WINDIR") if name in os.environ}
        self.env.update(TEMP=self.temp.name, TMP=self.temp.name)
        self.command = [sys.executable, "-I", "-S", "-B", "-u", str(HERE / "adversary.py")]
        self.record = {"id": len(world.out["processes"]), "command": self.command,
                       "cwd": self.temp.name, "passed_environment": self.env,
                       "events": [], "timeout_seconds": 20, "exit_code": None}
        world.out["processes"].append(self.record)
        self.proc = subprocess.Popen(self.command, cwd=self.temp.name, env=self.env,
                                     stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                     stderr=subprocess.PIPE, text=True, encoding="utf-8")
        self.lines = queue.Queue()
        self.thread = threading.Thread(target=self._read_stdout, daemon=True)
        self.thread.start()
        self.send(initial)

    def _read_stdout(self):
        for line in self.proc.stdout:
            self.lines.put(line)
        self.lines.put(None)

    def send(self, obj):
        # Make the log a value snapshot rather than a reference to mutable keys.
        copied = json.loads(json.dumps(obj))
        self.record["events"].append({"direction": "world_to_adversary", "fields": fields(copied), "data": copied})
        self.proc.stdin.write(json.dumps(copied, separators=(",", ":")) + "\n")
        self.proc.stdin.flush()

    def receive(self, expected):
        try:
            line = self.lines.get(timeout=20)
        except queue.Empty:
            self.record["timeout"] = True
            self.proc.kill()
            raise TimeoutError("adversary output timeout")
        if line is None:
            raise RuntimeError("adversary closed stdout")
        obj = json.loads(line)
        self.record["events"].append({"direction": "adversary_to_world", "data": obj})
        if obj.get("type") != expected:
            raise ValueError("expected " + expected + ", received " + str(obj))
        return obj

    def send_message(self, message):
        self.send({"type": "message", "message": message})

    def message(self):
        return self.receive("message")["message"]

    def result(self):
        result = self.receive("result")["result"]
        self.proc.stdin.close()
        try:
            self.record["exit_code"] = self.proc.wait(timeout=20)
        except subprocess.TimeoutExpired:
            self.proc.kill()
            self.record["exit_code"] = self.proc.wait()
            self.record["timeout"] = True
        self.record["stderr"] = self.proc.stderr.read()
        self.record["temporary_cwd_files_after_run"] = [p.name for p in Path(self.temp.name).iterdir()]
        self.record["result"] = result
        self.world.audit_child(self.record)
        self.temp.cleanup()
        return result


class Oracle:
    def __init__(self, world, role, iota, budget, initial_usage):
        self.world, self.role, self.iota = world, role, iota
        self.budget, self.used = budget, initial_usage
        self.record = {"role": role, "iota": iota, "lambda": budget, "b0": initial_usage,
                       "epoch": world.states[role]["epoch"], "queries": []}
        world.out["oracles"].append(self.record)

    def query(self):
        length = 2 * self.world.public["w"]
        allowed = self.used + length + self.iota <= self.budget
        item = {"requested_bits": length, "used_before": self.used,
                "inequality_lhs": self.used + length + self.iota,
                "allowed": allowed, "f_AB_called": False}
        self.record["queries"].append(item)
        if not allowed:
            item["used_after"] = self.used
            item["output"] = None
            return None
        state = self.world.states[self.role]
        p = self.world.public
        bits = demo.f_AB(demo.serialize_state(state["A"], state["B"], p["w"]), self.world.n, p["w"], p["q"])
        item.update(f_AB_called=True, output=bits)
        self.used += len(bits)
        item["used_after"] = self.used
        return bits


class World:
    def __init__(self, args, out):
        self.args, self.out, self.n = args, out, args.n
        self.rng = random.Random(args.seed)
        self.now, self.window = 1000000, 30
        self.states = {}

    def check(self, ident, condition, observed, expected=None):
        self.out["checks"].append({"id": ident, "status": "PASS" if condition else "FAIL",
                                   "expected": expected, "observed": observed})
        if not condition:
            print("FAIL " + ident, flush=True)
        return bool(condition)

    def setup(self):
        p, q = demo.find_safe_prime(self.args.bits, self.rng)
        g1 = demo.subgroup_generator(p, q, self.rng)
        self.alpha = self.rng.randrange(1, q)
        g2 = pow(g1, self.alpha, p)
        self.public = dict(p=p, q=q, g1=g1, g2=g2, w=q.bit_length(), idU="test-user", idS="test-edge")
        for role in ("U", "S"):
            a = [0] * self.n
            while not any(a):
                a = [self.rng.randrange(q) for _ in range(self.n)]
            b = [[self.rng.randrange(q), self.rng.randrange(q)] for _ in range(self.n)]
            x = demo.mat_vec_row(a, b, q)
            self.states[role] = dict(A=a, B=b, X=x, epoch=0)
            self.public["pk" + role] = self.pk(x)
        self.out["public"] = self.public
        self.out["world_initial_states"] = json.loads(json.dumps(self.states))
        self.out["test_control_alpha_world_only"] = self.alpha
        self.check("group", all(g != 1 and pow(g, q, p) == 1 for g in (g1, g2)), {"distinct": g1 != g2})
        for role in ("U", "S"):
            x = self.states[role]["X"]
            self.check("keygen." + role, self.pk(x) == self.public["pk" + role], {"zero_X_coordinates": [v == 0 for v in x]})

    def pk(self, x):
        p = self.public
        return pow(p["g1"], x[0], p["p"]) * pow(p["g2"], x[1], p["p"]) % p["p"]

    def ephemeral(self):
        p = self.public
        r = [self.rng.randrange(1, p["q"]) for _ in range(2)]
        return r, [pow(p["g1"], r[0], p["p"]), pow(p["g2"], r[1], p["p"])]

    def response(self, r, c, role):
        return [(r[i] + c * self.states[role]["X"][i]) % self.public["q"] for i in range(2)]

    def accepts(self, role, commitments, c, v, literal=False):
        p = self.public
        base2 = p["g1"] if literal else p["g2"]
        lhs = pow(p["g1"], v[0], p["p"]) * pow(base2, v[1], p["p"]) % p["p"]
        rhs = commitments[0] * commitments[1] * pow(p["pk" + role], c, p["p"]) % p["p"]
        return lhs == rhs

    def fresh(self, timestamp):
        return 0 <= self.now - timestamp <= self.window

    def update(self, role, reason):
        s, q = self.states[role], self.public["q"]
        old_a, old_b, old_x = s["A"], s["B"], s["X"]
        rec = {"role": role, "reason": reason, "epoch_before": s["epoch"], "status": "NOT RUN"}
        self.out["updates"].append(rec)
        try:
            a, b, wit = demo.update(old_a, old_b, q, self.rng)
        except demo.UpdateFailed as exc:
            rec.update(status="FAIL", abort=str(exc))
            raise
        x = demo.mat_vec_row(a, b, q)
        tf = demo.mat_mul(wit["T"], wit["F"], q)
        shift = demo.mat_vec_row(wit["E2"], wit["T2"], q)
        constraints = {
            "E_nonzero": any(wit["E"]), "E2_nonzero": any(wit["E2"]),
            "EF_zero": demo.mat_vec_row(wit["E"], wit["F"], q) == [0, 0],
            "E2F2_zero": demo.mat_vec_row(wit["E2"], wit["F2"], q) == [0, 0],
            "T_invertible": demo.mat_inverse(wit["T"], q) is not None,
            "T2_invertible": demo.mat_inverse(wit["T2"], q) is not None,
            "AT_E": demo.mat_vec_row(old_a, wit["T"], q) == wit["E"],
            "T2Bnew_F2": demo.mat_mul(wit["T2"], b, q) == wit["F2"],
            "Bnew_B_plus_TF": b == [[(old_b[i][j] + tf[i][j]) % q for j in range(2)] for i in range(self.n)],
            "Anew_A_plus_E2T2": a == [(old_a[i] + shift[i]) % q for i in range(self.n)],
            "product_preserved": x == old_x, "pk_preserved": self.pk(x) == self.public["pk" + role],
            "new_A_nonzero": any(a), "state_changed": a != old_a or b != old_b,
            "fixed_width": len(demo.serialize_state(a, b, self.public["w"])) == 3 * self.n * self.public["w"],
        }
        ok = all(constraints.values())
        rec.update(status="PASS" if ok else "FAIL", constraints=constraints, witnesses=wit,
                   A_before=old_a, B_before=old_b, A_after=a, B_after=b,
                   X_before=old_x, X_after=x, epoch_after=s["epoch"] + 1)
        self.check("update." + str(len(self.out["updates"])) + "." + role, ok, constraints)
        if not ok:
            raise ValueError("Update constraints failed")
        self.states[role] = dict(A=a, B=b, X=x, epoch=s["epoch"] + 1)

    def literal_probe(self):
        # Both equations evaluated; server rejection halts actual printed flow.
        for trial in range(3):
            ru, ru_pub = self.ephemeral()
            rs, rs_pub = self.ephemeral()
            cs, cu = [self.rng.randrange(1, self.public["q"]) for _ in range(2)]
            vu, vs = self.response(ru, cs, "U"), self.response(rs, cu, "S")
            observed = [self.accepts("U", ru_pub, cs, vu, True), self.accepts("S", rs_pub, cu, vs, True)]
            predicted = [self.public["g1"] == self.public["g2"] or v[1] == 0 for v in (vu, vs)]
            rec = dict(trial=trial, ru=ru, rs=rs, Ru=ru_pub, Rs=rs_pub, cS=cs, cU=cu,
                       vu=vu, vs=vs, observed_checks=observed, predicted_checks=predicted,
                       honest_completed=all(observed),
                       user_check_executed_in_flow=observed[0],
                       user_check_diagnostic_only=not observed[0])
            self.out["literal"].append(rec)
            self.check("literal.exact_failure_condition." + str(trial), observed == predicted, rec,
                       "accept iff g1==g2 or corresponding v2==0")
        self.check("literal.general_incompleteness_witness", any(not all(r["observed_checks"]) for r in self.out["literal"]),
                   {"completed": sum(r["honest_completed"] for r in self.out["literal"]), "trials": 3},
                   "at least one sampled nonexceptional failure; never a universal no-success claim")

    def honest(self, label):
        p = self.public
        ru, ru_pub = self.ephemeral()
        m1 = dict(idU=p["idU"], Ru1=ru_pub[0], Ru2=ru_pub[1], Ti=self.now)
        validation = {"M1": m1["idU"] == p["idU"] and self.fresh(m1["Ti"])}
        if not validation["M1"]:
            raise ValueError("honest M1 identity/timestamp invalid")
        rs, rs_pub = self.ephemeral()
        cs = self.rng.randrange(1, p["q"])
        m2 = dict(idS=p["idS"], Rs1=rs_pub[0], Rs2=rs_pub[1], cS=cs, Tj=self.now)
        validation["M2"] = m2["idS"] == p["idS"] and self.fresh(m2["Tj"])
        if not validation["M2"]:
            raise ValueError("honest M2 identity/timestamp invalid")
        cu = self.rng.randrange(1, p["q"])
        vu = self.response(ru, cs, "U")
        m3 = dict(idU=p["idU"], vu1=vu[0], vu2=vu[1], cU=cu, Ti_prime=self.now)
        validation["M3"] = m3["idU"] == p["idU"] and self.fresh(m3["Ti_prime"])
        server_ok = validation["M3"] and self.accepts("U", ru_pub, cs, vu)
        if not server_ok:
            raise ValueError("corrected honest server rejection")
        vs = self.response(rs, cu, "S")
        m4 = dict(idS=p["idS"], vs1=vs[0], vs2=vs[1], Tj_prime=self.now)
        epochs = {role: self.states[role]["epoch"] for role in ("U", "S")}
        validation["M4"] = m4["idS"] == p["idS"] and self.fresh(m4["Tj_prime"])
        user_ok = validation["M4"] and self.accepts("S", rs_pub, cu, vs)
        if not user_ok:
            raise ValueError("corrected honest user rejection")
        # Printed step (6): both checks have succeeded; U derives K and updates,
        # then S derives K and updates. No Update is assigned to step (5).
        dhu = [pow(rs_pub[i], ru[i], p["p"]) for i in range(2)]
        ku = key(p, dhu)
        self.update("U", label + ": VI-A.3 step (6), user derives K then Update")
        dhs = [pow(ru_pub[i], rs[i], p["p"]) for i in range(2)]
        ks = key(p, dhs)
        self.update("S", label + ": VI-A.3 step (6), server derives K then Update")
        rec = dict(label=label, transcript=dict(M1=m1, M2=m2, M3=m3, M4=m4),
                   world_ephemeral=dict(U=ru, S=rs), world_dh=dict(U=dhu, S=dhs),
                   world_key=dict(U=ku, S=ks), epochs_at_start=epochs,
                   epochs_after_session={role: self.states[role]["epoch"] for role in ("U", "S")},
                   accepted=dict(U=user_ok, S=server_ok), identity_timestamp_valid=validation,
                   local_step6_order=["U derives K", "U Update", "S derives K", "S Update"])
        self.out["honest_sessions"].append(rec)
        self.check("honest." + label, user_ok and server_ok and dhu == dhs and ku == ks, rec)
        self.now += 1
        return rec

    def h1(self, role, x, label, expect_accept=True, expired=False):
        p = self.public
        start = dict(scenario="H1", role=role, public=p, X=x,
                     timestamp=self.now - self.window - 1 if expired else self.now,
                     now=self.now, window=self.window)
        child = Child(self, start)
        child.receive("ready")
        rec = dict(label=label, role=role, process_id=child.record["id"], epochs={r: self.states[r]["epoch"] for r in ("U", "S")},
                   capability=x, pk_matches=self.pk(x) == p["pk" + role], transcript={}, accepted=False)
        self.out["h1"].append(rec)
        if role == "U":
            m1 = child.message()
            rec["transcript"]["M1"] = m1
            if m1["idU"] != p["idU"] or not self.fresh(m1["Ti"]):
                return self.h1_abort(child, rec, "identity_or_expired_M1", expect_accept)
            rs, rs_pub = self.ephemeral()
            cs = self.rng.randrange(1, p["q"])
            m2 = dict(idS=p["idS"], Rs1=rs_pub[0], Rs2=rs_pub[1], cS=cs, Tj=self.now)
            rec["transcript"]["M2"] = m2
            child.send_message(m2)
            m3 = child.message()
            rec["transcript"]["M3"] = m3
            ok = m3["idU"] == p["idU"] and self.fresh(m3["Ti_prime"]) and self.accepts("U", [m1["Ru1"], m1["Ru2"]], cs, [m3["vu1"], m3["vu2"]])
            if not ok:
                return self.h1_abort(child, rec, "invalid_user_response", expect_accept)
            vs = self.response(rs, m3["cU"], "S")
            m4 = dict(idS=p["idS"], vs1=vs[0], vs2=vs[1], Tj_prime=self.now)
            rec["transcript"]["M4"] = m4
            child.send_message(m4)
            dh = [pow(m1["Ru1"], rs[0], p["p"]), pow(m1["Ru2"], rs[1], p["p"])]
            honest_role = "S"
        else:
            ru, ru_pub = self.ephemeral()
            m1 = dict(idU=p["idU"], Ru1=ru_pub[0], Ru2=ru_pub[1], Ti=self.now)
            rec["transcript"]["M1"] = m1
            child.send_message(m1)
            m2 = child.message()
            rec["transcript"]["M2"] = m2
            if m2["idS"] != p["idS"] or not self.fresh(m2["Tj"]):
                return self.h1_abort(child, rec, "identity_or_expired_M2", expect_accept)
            cu = self.rng.randrange(1, p["q"])
            vu = self.response(ru, m2["cS"], "U")
            m3 = dict(idU=p["idU"], vu1=vu[0], vu2=vu[1], cU=cu, Ti_prime=self.now)
            rec["transcript"]["M3"] = m3
            child.send_message(m3)
            m4 = child.message()
            rec["transcript"]["M4"] = m4
            ok = m4["idS"] == p["idS"] and self.fresh(m4["Tj_prime"]) and self.accepts("S", [m2["Rs1"], m2["Rs2"]], cu, [m4["vs1"], m4["vs2"]])
            dh = [pow(m2["Rs1"], ru[0], p["p"]), pow(m2["Rs2"], ru[1], p["p"])] if ok else None
            honest_role = "U"
        result = child.result()
        rec.update(accepted=ok, result=result, world_peer_dh=dh, world_peer_key=key(p, dh) if ok else None,
                   identity_accepted=p["id" + role] if ok else None)
        matches = ok and not result["aborted"] and result["dh"] == dh and result["key"] == key(p, dh)
        self.check("h1." + label + "." + role, ok == expect_accept and (not expect_accept or matches and result["peer_accepted_by_adversary"]),
                   {"accepted": ok, "key_equal": matches, "identity": rec["identity_accepted"]},
                   {"accepted": expect_accept, "matching_key_if_accepted": True})
        if ok:
            self.update(honest_role, "H1 " + label + " honest peer after K")
        return rec

    def h1_abort(self, child, rec, reason, expect_accept):
        child.send({"type": "abort", "reason": reason})
        result = child.result()
        rec.update(accepted=False, abort_reason=reason, result=result)
        self.check("h1." + rec["label"] + "." + rec["role"], not expect_accept and result["aborted"],
                   {"accepted": False, "reason": reason}, {"accepted": expect_accept})
        return rec

    def h2(self, role, session, secret, label, expect_success=True):
        p = self.public
        later = self.states[role]["epoch"] - session["epochs_after_session"][role]
        self.check("h2.later_updates." + label + "." + role + "." + session["label"], later >= 2,
                   {"additional_successful_updates": later}, ">=2 after recorded session")
        initial = dict(scenario="H2", role=role, public=p, transcript=session["transcript"], secret=secret)
        child = Child(self, initial)
        result = child.result()
        if result["aborted"]:
            raise ValueError("H2 subprocess abort: " + str(result))
        r = session["world_ephemeral"][role]
        rh = result["recovered_ephemeral"]
        tr = session["transcript"]
        own = [tr["M1"]["Ru1"], tr["M1"]["Ru2"]] if role == "U" else [tr["M2"]["Rs1"], tr["M2"]["Rs2"]]
        commitment = [pow(p["g1"], rh[0], p["p"]) == own[0], pow(p["g2"], rh[1], p["p"]) == own[1]]
        ephemeral = [rh[i] == r[i] for i in range(2)]
        dh = [result["dh"][i] == session["world_dh"][role][i] for i in range(2)]
        key_equal = result["key"] == session["world_key"][role]
        ordered = [{"stage": "commitment", "equal": commitment}, {"stage": "ephemeral", "equal": ephemeral},
                   {"stage": "dh", "equal": dh}, {"stage": "key", "equal": key_equal}]
        rec = dict(label=label, role=role, session=session["label"], process_id=child.record["id"],
                   additional_successful_updates=later, compromise_epoch=self.states[role]["epoch"],
                   validation_in_order=ordered, result=result, final_hash_difference_observed=not key_equal)
        self.out["h2"].append(rec)
        ident = "h2." + label + "." + role + "." + session["label"]
        self.check(ident + ".worker_commitment_agreement", result["commitment_consistency"] == commitment, commitment)
        if expect_success:
            for item in ordered:
                value = item["equal"]
                self.check(ident + "." + item["stage"], all(value) if isinstance(value, list) else value, value, True)
        else:
            c = tr["M2"]["cS"] if role == "U" else tr["M3"]["cU"]
            x, w = self.states[role]["X"], secret["X"]
            delta = [(rh[i] - r[i]) % p["q"] for i in range(2)]
            predicted = [(c * (x[i] - w[i])) % p["q"] for i in range(2)]
            rec.update(ephemeral_error=delta, predicted_error=predicted)
            self.check(ident + ".error_identity", delta == predicted and any(delta), {"delta": delta, "predicted": predicted})
            self.check(ident + ".commitment_failure", not all(commitment), commitment, "at least one False")
            self.check(ident + ".corresponding_dh_failure", all(not dh[i] for i in range(2) if delta[i]), dh, "False for every nonzero error coordinate")
            # Deliberately no assertion that distinct hash inputs imply distinct hashes.
        return rec

    def audit_child(self, rec):
        result = rec["result"]
        audit = result["audit"]
        opens = audit["open_events_after_script_start"]
        library_roots = [Path(sys.base_prefix).resolve(), Path(sys.prefix).resolve()]
        bad_reads = []
        for event in opens:
            path = Path(event["path"])
            allowed = path.is_absolute() and any(path.resolve().is_relative_to(root) for root in library_roots)
            if not allowed:
                bad_reads.append(event)
        inputs = [e["data"] for e in rec["events"] if e["direction"] == "world_to_adversary"]
        forbidden = {"seed", "world_state", "world_ephemeral", "own_ephemeral", "world_key", "key", "alpha", "rU", "rS"}
        leaf_fields = {f.split(".")[-1].replace("[]", "") for obj in inputs for f in fields(obj)}
        rec["data_flow_review"] = {"unexpected_open_events": bad_reads,
                                   "forbidden_input_fields": sorted(forbidden & leaf_fields),
                                   "startup_before_hook_unobserved": True,
                                   "standard_library_roots": [str(p) for p in library_roots]}
        ok = not bad_reads and not forbidden & leaf_fields and audit["isolation_flag"] == 1 and audit["no_bytecode_flag"] == 1 and audit["no_site_flag"] == 1
        ok = ok and audit["cwd"] == rec["cwd"] and audit["environment"] == rec["passed_environment"]
        ok = ok and rec["exit_code"] == 0 and not rec["stderr"] and not rec["temporary_cwd_files_after_run"]
        self.check("process.data_flow." + str(rec["id"]), ok, rec["data_flow_review"],
                   "declared input only; observed reads limited to standard library; source review also required")

    def run(self):
        self.setup()
        self.literal_probe()
        retained = {role: list(self.states[role]["X"]) for role in ("U", "S")}
        for role in ("U", "S"):
            self.h1(role, retained[role], "actual_X_initial")
        for round_id in range(2):
            self.honest("before_H1_repetition_" + str(round_id + 1))
        for role in ("U", "S"):
            self.h1(role, retained[role], "actual_X_after_updates")
        for role in ("U", "S"):
            x, q = self.states[role]["X"], self.public["q"]
            w = [(x[0] + self.alpha) % q, (x[1] - 1) % q]
            bad = [(x[0] + 1) % q, x[1]]
            self.check("controls." + role, w != x and self.pk(w) == self.pk(x) and self.pk(bad) != self.pk(x), {"X": x, "W": w, "X_bad": bad})
            self.h1(role, w, "alternative_W")
            self.h1(role, bad, "X_bad", expect_accept=False)
            self.h1(role, x, "expired", expect_accept=False, expired=True)
        sessions = [self.honest("history_1"), self.honest("history_2")]
        for round_id in range(2):
            self.honest("post_history_" + str(round_id + 1))
        self.out["world_current_states_at_compromise"] = json.loads(json.dumps(self.states))
        for role in ("U", "S"):
            s, q = self.states[role], self.public["q"]
            for session in sessions:
                self.h2(role, session, dict(kind="current_sk", A=s["A"], B=s["B"]), "main_full_key")
            for iota in (0, 1):
                b0, length = self.args.b0, 2 * self.public["w"]
                oracle = Oracle(self, role, iota, b0 + length + iota, b0)
                leaked = oracle.query()
                self.check("oracle.allowed." + role + "." + str(iota), leaked is not None and len(leaked) == length,
                           oracle.record, "b0+2w+iota=lambda")
                for session in sessions:
                    self.h2(role, session, dict(kind="product_bits", bits=leaked), "strengthened_iota" + str(iota))
                denied = oracle.query()
                self.check("oracle.cumulative_refusal." + role + "." + str(iota), denied is None and oracle.used == b0 + length,
                           oracle.record["queries"][-1])
                under = Oracle(self, role, iota, b0 + length + iota - 1, b0)
                refused = under.query()
                self.check("oracle.one_bit_short_refusal." + role + "." + str(iota), refused is None and under.used == b0 and not under.record["queries"][0]["f_AB_called"], under.record)
            x = s["X"]
            for label, control in (("alternative_W", [(x[0] + self.alpha) % q, (x[1] - 1) % q]), ("X_bad", [(x[0] + 1) % q, x[1]])):
                for session in sessions:
                    self.h2(role, session, dict(kind="control_vector", X=control), label, expect_success=False)


def git(*args):
    try:
        return subprocess.check_output(["git", *args], cwd=ROOT, text=True, encoding="utf-8",
                                       stderr=subprocess.DEVNULL).strip()
    except (OSError, subprocess.CalledProcessError):
        return "unavailable (not a git checkout or git not found)"


PLACEHOLDERS = {"<artifact>": "repository root", "<tmp>": "system temporary directory",
                "<python>": "Python installation", "<home>": "user home directory"}


def path_pattern(path):
    parts = [p for p in re.split(r"[\\/]+", str(path)) if p]
    return re.compile(r"[\\/]+".join(re.escape(p) for p in parts), re.IGNORECASE)


def redactions():
    """Local path prefixes replaced in the written record, longest first."""
    pairs = [(ROOT, "<artifact>"), (Path(tempfile.gettempdir()), "<tmp>"),
             (Path(sys.base_prefix), "<python>"), (Path(sys.prefix), "<python>"),
             (Path(sys.executable).parent, "<python>"), (Path.home(), "<home>")]
    unique = {}
    for path, label in pairs:
        for variant in {str(path), str(path.resolve())}:
            unique.setdefault(variant, label)
    ordered = sorted(unique.items(), key=lambda item: -len(item[0]))
    return [(path_pattern(path), label) for path, label in ordered]


def redact(value, rules):
    """Applied once to the finished record, after every check has been evaluated."""
    if isinstance(value, dict):
        return {name: redact(child, rules) for name, child in value.items()}
    if isinstance(value, list):
        return [redact(child, rules) for child in value]
    if isinstance(value, str):
        for pattern, label in rules:
            value = pattern.sub(lambda _match, label=label: label, value)
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bits", type=int, default=256)
    parser.add_argument("--n", type=int, default=16)
    parser.add_argument("--seed", type=int, default=20261009)
    parser.add_argument("--b0", type=int, default=7)
    parser.add_argument("--output", default="mec/records/mec_h1h2_public.json")
    args = parser.parse_args()
    if args.bits < 16 or args.n < 16 or args.b0 <= 0:
        parser.error("require bits>=16, n>=16, b0>0")
    output = (ROOT / args.output).resolve()
    if output.exists():
        parser.error("refusing to overwrite existing raw evidence: " + str(output))
    if output.parent != RECORDS.resolve() or not output.name.startswith("mec_h1h2") or output.suffix != ".json":
        parser.error("output must be mec/records/mec_h1h2*.json")
    tracked = [HERE / "world.py", HERE / "adversary.py", HERE / "README.md", ROOT / "demo.py"]
    if SOURCE.exists():
        tracked.append(SOURCE)
    out = {"task": TASK_ID,
           "role": "execution witness for main-paper Propositions 15 and 16 (Supplement S6); not a proof",
           "config": vars(args),
           "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
           "environment": {"python": sys.version, "executable": sys.executable, "platform": platform.platform()},
           "provenance": {"base_commit": git("rev-parse", "HEAD"), "branch": git("branch", "--show-current"),
                          "working_tree_status_before": git("status", "--short"),
                          "sha256": {str(path.relative_to(ROOT)).replace("\\", "/"): sha(path) for path in tracked},
                          "analyzed_article": ("hashed above" if SOURCE.exists() else
                                               "not included (copyright); identified by SHA-256 in sources.json")},
           "conventions": {"world_prng": "random.Random(seed)", "adversary_prng": "SystemRandom; no seed passed",
                           "hash": "SHA256(canonical ASCII JSON [idU,idS,DH1,DH2])",
                           "freshness": "0 <= now - timestamp <= 30 synthetic seconds",
                           "update_sampler": "demo.py: printed constraints, not source sampling distribution",
                           "separation": "separate process and reviewed input/data flow; not a sandbox"},
           "checks": [], "literal": [], "honest_sessions": [], "updates": [],
           "h1": [], "h2": [], "oracles": [], "processes": []}
    try:
        World(args, out).run()
    except Exception as exc:
        out["abort"] = {"type": type(exc).__name__, "message": str(exc), "traceback": traceback.format_exc()}
        out["checks"].append({"id": "run.completed", "status": "FAIL", "observed": out["abort"]})
        out["checks"].append({"id": "remaining_work_after_abort", "status": "NOT RUN", "observed": "see completed arrays; no fabricated result"})
    failed = [c["id"] for c in out["checks"] if c["status"] == "FAIL"]
    out["finished_utc"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    out["summary"] = {"status": "FAIL" if failed else "PASS", "checks": len(out["checks"]),
                      "failed": failed, "processes": len(out["processes"]),
                      "successful_updates": sum(u["status"] == "PASS" for u in out["updates"]),
                      "h1_cases": len(out["h1"]), "h2_cases": len(out["h2"])}
    out["redaction"] = {"placeholders": PLACEHOLDERS,
                        "applied": "to the finished record after all checks; values are unchanged otherwise"}
    out = redact(out, redactions())
    output.parent.mkdir(parents=True, exist_ok=True)
    with output.open("x", encoding="utf-8", newline="\n") as handle:
        json.dump(out, handle, indent=2, ensure_ascii=False)
        handle.write("\n")
    print(json.dumps(out["summary"], ensure_ascii=False), flush=True)
    print(output.relative_to(ROOT).as_posix(), flush=True)
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
