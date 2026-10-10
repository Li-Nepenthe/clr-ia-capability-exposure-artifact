"""Hypothesis audit of the 90 checked theorems; writes COVERAGE.md.

    python coverage_audit.py

For every theorem named in CheckAxioms.lean, the script finds its statement, lists the
explicit hypotheses (binders whose name starts with `h`) and joins the hand-written note
on what each hypothesis is and where the paper provides it. A theorem without a note
fails the run, so new theorems cannot enter the table unreviewed.
"""
import re
import sys
from pathlib import Path

sys.stdout.reconfigure(encoding='utf-8')
HERE = Path(__file__).resolve().parent
SRC = HERE / 'ClriaLean'
MODULES = ('Params', 'IBKEM', 'IBE', 'Fiber', 'Projection', 'RefreshLimit', 'ProofWitness',
           'Repairs')

# Categories of hypotheses.
#   P  premise of the paper statement itself (the paper states the same "if")
#   S  setting or well-formedness (nonzero generator, nonzero A, q > 1, probabilities)
#   F  source fact or printed constraint (update equations, symmetric pairing, ...)
#   N  stated assumption of a numerical claim (S4-E values, slack and dimension windows)
#   E  established elsewhere on paper; named in the note
NOTES = {
    'row_apply': 'none',
    'capability_accepts': 'none. Proves the verification identity of eq. (6) only; that X is a 1-capability for both published games, and the legality of the query, are argued on paper (Proposition 5, Table I).',
    'honest_accepts': 'none',
    'theta_of_two_reps': 'S: g1 is not the identity (generator). P: X ≠ X\' with g^X = g^X\' (the premise of eq. (2)).',
    'rewind_extracts_X': 'P: distinct challenges.',
    'trapdoor_witness': 'none',
    'bridge': 'F: the printed first-stage constraints AT = E, EF = 0.',
    'stages_preserve_product': 'F: the printed constraints of both stages.',
    'IsUpdate.bridge': 'F: one non-aborting execution of the printed update (definition IsUpdate).',
    'IsUpdate.product': 'F: one non-aborting execution of the printed update.',
    'update_chain_product': 'F: every refresh in the sequence returns a key (Section VI: "whenever the refreshes return keys").',
    'update_chain_bridge': 'F: every refresh in the sequence returns a key.',
    'bridge_one_direction': 'S: n ≥ 2 (the source fixes n ≥ 16).',
    'L_split': 'none',
    'joint_margins': 'none',
    'split_margins': 'none',
    'cross_i_margins': 'none',
    'cross_next_margins': 'none',
    'margins_at_16': 'S: δ < 1 (definition of δ).',
    'margin_growth': 'S: a, δ ≥ 0.',
    'margins_pos': 'S: n ≥ 16, δ < 1, ι ≤ 1. N: a ≥ 5, weaker than the paper\'s a > 255.',
    'copy_excess': 'none',
    'widths_16_256': 'none (numerals)',
    'rounded_percentages': 'none (numerals)',
    's4e_percentages_not_implied': 'none (numerals). Records that the R23.28 wording of S4-E did not follow; no current statement relies on it.',
    's4e_percentages_valid': 'N: log q − σ < 256, (log q − σ)/2 < 128, log q < 256 (the 256-bit setting). Superseded in the text by s4e_exact.',
    's4e_exact': 'N: as s4e_percentages_valid.',
    's4e_bound': 'N: q > 2^255, Q ≤ 2^30, λ\' ≤ 173 and DLadv ≤ 2^−81, the values S4-E fixes with "let". The bound DLadv ≤ 2^−81 is an assumption, not a result; eq. (14) itself is a paper proof.',
    'any_value': 'none (numerals)',
    'secure_fraction': 'S: n, w > 0, a ≤ w, slack s > 0.',
    'attack_fraction': 'S: n, w ≠ 0.',
    'ibkem_cap_exceeded': 'N: full-group encoding ℓ_G ≥ log q; l_m + σ_K > 0; S: j ≥ 1, b ≥ 0.',
    'ibe_window': 'N: n ≥ ⌈(2ℓ_G + ℓ_p + 1 + σ_B)/log p⌉ (the dimension threshold n0 of S7-C). S: log p > 0, ι ≤ 1.',
    'ibe_copy_exceeds': 'N: full-field encodings ℓ_G, ℓ_p ≥ log p. S: n, σ_B ≥ 0.',
    'zhouyang_window': 'N: slack σ ≤ log p − 2 (S7-C). S: p > 1, ι ≤ 1.',
    'capability': 'none (every α, β, s, r, μ and every h_i, including 0).',
    'recovers_key': 'P: μ ≠ −1 (the case of Proposition 17; π = Pr[μ ≠ −1] is bounded on paper from target-collision resistance).',
    'mu_neg_one': 'none',
    'update_keeps_R': 'none',
    'hybrid_identity': 'F: the pairing is symmetric (the source uses symmetric pairing groups).',
    'normalization': 'F: a public index j with k_pub,j ≠ 0, as Section VIII-B selects.',
    'recovery': 'F: symmetric pairing; public j with k_pub,j ≠ 0. The vector reading is built into the model (pairings with vector components taken coordinatewise); it is an interpretation stated in the paper, not proved.',
    'update_persistence': 'F: symmetric pairing; k_pub,j ≠ 0; the printed update constraint ⟨k_pub, t\'⟩ = 0.',
    'zhouyang_invalid_accept': 'none',
    'zhouyang_header_invalid': 'F: id ≠ α, g ≠ 0, e(g,g) ≠ 0 (nondegenerate pairing). P: c1 = 1_G for the candidate r.',
    'card_dot_fiber': 'S: a ≠ 0.',
    'card_fiber_fixed_A': 'S: A ≠ 0 (KeyGen draws A nonzero).',
    'card_key_fiber': 'none',
    'card_line': 'none',
    'card_keys_given_pk': 'none',
    'fiber_charge': 'S: q > 1, n ≥ 1.',
    'printed_charge_exceeds': 'S: q > 1, n ≥ 1.',
    'mul_Bp': 'S: A_i ≠ 0 for the chosen index.',
    'Bp_add_smul': 'none',
    'res_correct': 'S: A_i ≠ 0.',
    'res_uniform': 'S: A_i ≠ 0. P: AB = X for the target B. The distributional statement (pk, X, Res(X)) ≡ (pk, X, (A, B)) and Lemma 3 are paper arguments built on these counts.',
    'fiber_weight_le': 'P: every weight ≤ M and the fiber has ≤ F points (the core of Lemma 2(b)).',
    'exists_weight_ge': 'P: ≤ N values carry total weight 1 (the core of Lemma 2(a)).',
    'lemma2a': 'S: nonnegative weights of total mass 1. P: ≤ N positive values per view (Lemma 2(a)).',
    'lemma2b': 'S: nonnegative weights of total mass 1. P: ≤ F positive states per view and value (Lemma 2(b)).',
    'witness_of_responses': 'E: perfect correctness of the m-generator Okamoto verifier for every state, coin and challenge. S5-A assumes this; the theorem does not prove it for a given scheme (for CLR-IA it is eq. (3), honest_accepts).',
    'nontrivial_relation': 'P: two different witnesses of one public key.',
    'clria_witness_is_product': 'none',
    'splice_chunks': 'S: b ≥ 1 (Lemma 4: b = λ − ι ≥ 1).',
    'periods_bound': 'S: w ≥ 1, b ≥ 1.',
    'one_period': 'S: w ≥ 1. P: b ≥ 2w.',
    'claim2_fiber': 'none',
    'claim2_ratio': 'S: q ≥ 2.',
    'one_tag_per_state': 'none',
    'fresh_tags': 'none',
    'fresh_tags_prob': 'S: q > 0.',
    'interpolation_count': 'P: three distinct points.',
    'sd_determined': 'S: view distribution nonnegative with mass 1. The premise that the proof\'s view determines Z is argued on paper (S7-B).',
    'sd_upper': 'S: a joint distribution with the given view marginal.',
    'event_le_sd': 'S: both distributions have mass 1.',
    'predictor_bound': 'E: a predictor recovers the extractor output with probability ≥ 1 − ρ. S8-B argues this from correctness with error ρ; Lean takes it as a hypothesis.',
    'collSeeds_card': 'none',
    'collide_at_one': 'none',
    'collide_prob': 'S: q ≥ 2.',
    'collision_identity': 'S: mass 1.',
    'family_bound': 'S: mass 1, q ≥ 2. Seed independence and the min-entropy premise of S9-B are conditions of the stated repair, outside this count.',
    'cp_ge': 'S: mass 1 (Cauchy–Schwarz: collision probability ≥ 1/N).',
    'sum_abs_le_sqrt': 'S: mass 1.',
    'final_bound': 'N: x ≤ 1/p, i.e. log p ≤ k. S: p > 1.',
    'df_fiber': 'S: L ≠ 0.',
    'df_bad_event': 'S: N > 1.',
    'df_conditional': 'S: q, N > 1.',
    'df_deficit': 'S: q, N > 1.',
    'df_thresholds': 'N: N > 17.',
    'df_conversion': 'E: bad-event mass β ≤ 2γ. With γ = 1/8 this is 2/N ≤ 1/4, which follows from df_bad_event and N ≥ 8 by arithmetic not carried out in Lean. S: M, a, γ ≥ 0, m ≥ 1.',
}


def short(name):
    s = name.removeprefix('Clria.')
    for m in MODULES:
        if s.startswith(m + '.'):
            return m, s[len(m) + 1:]
    return None, s


def binders(stmt):
    """Top-level binder groups before the first top-level colon."""
    out, depth, cur = [], 0, ''
    for ch in stmt:
        if ch in '([{⦃':
            if depth == 0:
                cur = ''
            depth += 1
            cur += ch
            continue
        if ch in ')]}⦄':
            depth -= 1
            cur += ch
            if depth == 0:
                out.append(cur)
            continue
        if depth == 0 and ch == ':':
            break
        if depth > 0:
            cur += ch
    return out


def main():
    names = re.findall(r'#print axioms (\S+)', (HERE / 'CheckAxioms.lean').read_text(encoding='utf-8'))
    files = {p.stem: p.read_text(encoding='utf-8') for p in SRC.glob('*.lean')}
    rows, missing = [], []
    for full in names:
        mod, sname = short(full)
        cands = [mod] if mod else ['Basic', 'Update']
        found = None
        for f in cands:
            m = re.search(r'^(?:theorem|lemma) ' + re.escape(sname) + r'\b(.*?)(?=:= by|:=\s*$)', files[f], re.S | re.M)
            if m:
                found = (f, re.sub(r'\s+', ' ', m.group(1)))
                break
        if not found:
            missing.append(full)
            continue
        f, stmt = found
        hyps = [b for b in binders(stmt) if re.match(r'\((h\S*) :', b)]
        if sname not in NOTES:
            missing.append(full + ' (no note)')
            continue
        rows.append((full, f, hyps, NOTES[sname]))
    if missing:
        print('MISSING:', missing)
        sys.exit(1)
    lines = ['# Hypothesis audit of the checked theorems', '',
             'Generated by `coverage_audit.py` from `CheckAxioms.lean` and the sources. Columns: the theorem, its file,',
             'the explicit hypotheses as written (binders named `h…`), and what each hypothesis is and where the paper',
             'provides it. Categories: **P** premise of the paper statement itself; **S** setting or well-formedness;',
             '**F** source fact or printed constraint; **N** stated assumption of a numerical claim; **E** established',
             'elsewhere on paper (named in the note). Implicit typing assumptions (a field `K`, a `K`-module `G`, finiteness',
             'where counts are taken) are the modeling conventions of `README.md` and are not repeated.', '',
             f'{len(rows)} theorems; {sum(1 for r in rows if r[2])} have explicit hypotheses; '
             f'{sum(1 for r in rows if "E:" in r[3])} have a hypothesis of category E.', '',
             '| # | Theorem | File | Explicit hypotheses | Note |', '|---|---|---|---|---|']
    for i, (full, f, hyps, note) in enumerate(rows, 1):
        hs = '<br>'.join('`' + h.replace('|', '\\|') + '`' for h in hyps) or '—'
        lines.append(f'| {i} | `{full}` | `{f}` | {hs} | {note} |')
    (HERE / 'COVERAGE.md').write_bytes(('\n'.join(lines) + '\n').encode('utf-8'))
    print(f'{len(rows)} theorems written to COVERAGE.md')


if __name__ == '__main__':
    main()
