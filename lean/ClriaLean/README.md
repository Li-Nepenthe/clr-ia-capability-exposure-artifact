# ClriaLean — machine-checked algebra for the CLR-IA paper

Lean 4 (v4.34.1) with Mathlib (tag v4.34.1).
This development checks the algebraic identities, budget arithmetic, concrete values, fiber
counts, Lemma 2, the refresh-limit algebra, the counterexamples to two proof steps and the
exact counts behind the two local repairs of the accompanying paper (main paper and
supplement; locators below). It does not check the
DL/DBDH/TCR reductions, the rewinding analysis behind Corollary 10, the leakage games,
negligibility, extractor properties, or the interpretation choices made when restating the
source schemes; those are argued on paper.

## Modeling

- `K` is a field. Groups are written additively as `K`-modules: `g₁^{x₁} g₂^{x₂}` is
  `x₁ • g₁ + x₂ • g₂`. A pairing is a `K`-bilinear map `e : G →ₗ[K] G →ₗ[K] G_T`,
  assumed symmetric where the source pairing is symmetric. A cyclic group of prime order
  `q` with `K = ZMod q` is the one-dimensional case, so every identity holds there.
- CLR-IA keys are Mathlib matrices `A : K^{1×n}`, `B : K^{n×2}`; `X = AB`.
- Budgets use real arithmetic with `a = log q`, `w = a + δ`, `0 ≤ δ < 1`.

## Paper statements and Lean theorems

| Paper | Statement | Lean theorem | File |
|---|---|---|---|
| eq. (3), S2-A | honest responses `v = r + c·AB` verify | `Clria.honest_accepts`, `Clria.row_apply` | `Basic.lean` |
| eq. (6), §V-A | responses from `X` alone verify for every nonce and challenge | `Clria.capability_accepts` | `Basic.lean` |
| eq. (2) | two representations of `pk` give `θ`, and `x₂ ≠ x₂'` | `Clria.theta_of_two_reps` | `Basic.lean` |
| eq. (12), §VI-A | rewinding with a fixed nonce extracts exactly `X` | `Clria.rewind_extracts_X` | `Basic.lean` |
| Remark 14 | `(x₁ + θx₂, 0)` is a witness of `pk` | `Clria.trapdoor_witness` | `Basic.lean` |
| Lemma 7, eq. (10) | `A(B + TF) = AB` | `Clria.bridge`, `Clria.IsUpdate.bridge` | `Update.lean` |
| eq. (4) | both update stages keep `A'B' = AB` | `Clria.stages_preserve_product`, `Clria.IsUpdate.product` | `Update.lean` |
| §VII, Prop. 8 | `A_iB_i = X` and `A_iB_{i+1} = X` along any run | `Clria.update_chain_product`, `Clria.update_chain_bridge` | `Update.lean` |
| after Lemma 7 | for every `n ≥ 2` some run has `A_{i+1}B_i ≠ X` | `Clria.bridge_one_direction` | `Update.lean` |
| eq. (9) | `(nw+1) + (2w+1) = (n+2)w + 2` | `Clria.Params.L_split` | `Params.lean` |
| Table S2 | eight margin formulas | `joint_margins`, `split_margins`, `cross_i_margins`, `cross_next_margins` | `Params.lean` |
| Table S2 | four rows at `n = 16` | `margins_at_16` | `Params.lean` |
| S3-C | growth `≥ 2a − δ` and `≥ a/2 − δ` per unit of `n`; positivity for `n ≥ 16` | `margin_growth`, `margins_pos` | `Params.lean` |
| S3-C | copying both factors exceeds the allowance by `2a + 3nδ` | `copy_excess` | `Params.lean` |
| Figs. 1, 4; S4-E; S9 | widths 12,288 / 512 / 4,610 / 4,097 / 513; 11,730; 11,776; 5,888; rounded percentages | `widths_16_256`, `rounded_percentages` | `Params.lean` |
| S4-E | `(1+2^{λ'})/q ≤ 2^{-81}`, root `≤ 2^{-40}`, `(2Q+3)/q < 2^{-223}`; 86 for `ANY` | `s4e_bound`, `any_value` | `Params.lean` |
| S4-E | the earlier wording "below 2.08%, 1.04%, 95.83%" does not follow; the revised wording "below 1/48 ≈ 2.083%, 1/96 ≈ 1.042%, 23/24 ≈ 95.833%" does | `s4e_percentages_not_implied`, `s4e_percentages_valid`, `s4e_exact` | `Params.lean` |
| Corollary 11 | endpoints below `1/(3n)` and about `2/(3n)` of the key | `secure_fraction`, `attack_fraction` | `Params.lean` |
| S6-A | group-element outputs exceed the IB-KEM target cap | `ibkem_cap_exceeded` | `Params.lean` |
| S6-C | IBE window nonempty for `n ≥ n₀`; full copying exceeds the cap | `ibe_window`, `ibe_copy_exceeds` | `Params.lean` |
| S7-C | Zhou–Yang window nonempty for `σ ≤ log p − 2`; `2^λ/p^3 < 4/p^2` | `zhouyang_window` | `Params.lean` |
| eq. (15), Prop. 15 | `R = (α−β)g`, `D = X − Y`, `V + D = (μ+1)X`, key recovered for `μ ≠ −1` | `Clria.IBKEM.capability`, `Clria.IBKEM.recovers_key` | `IBKEM.lean` |
| §VIII-A | nothing recovered at `μ = −1`; the update keeps `R` | `Clria.IBKEM.mu_neg_one`, `Clria.IBKEM.update_keeps_R` | `IBKEM.lean` |
| S6-A | hybrid identity `e(R,c₁*)V* = (T e(c₁*,g)^{α̂})^{1+μ*}` for every `T` | `Clria.IBKEM.hybrid_identity` | `IBKEM.lean` |
| S6-B | public normalization `W = g^{1/γ}`, `g₃^𝐭 = W^{a_B}`, `∏ c_{3,k}^{t_k} = E₁^{a_B}` | `Clria.IBE.normalization` | `IBE.lean` |
| eq. (16), Prop. 16 | `X, Y, M` recovered from `(d₁, d₃, a_B)` for all `μ, η` | `Clria.IBE.recovery` | `IBE.lean` |
| S6-D | the update keeps `R`, `a_B`, `g₃^𝐭`, `e(d₁,g)e(d₃,F) = e(d/W^{a_B}, g₁)`; `d₃` changes | `Clria.IBE.update_persistence` | `IBE.lean` |
| S7-A, S7-C | the header `(1_G, e(g,g))` is invalid, yet the leaked `μt₁ + t₂` passes the tag check | `Clria.IBE.zhouyang_header_invalid`, `Clria.IBE.zhouyang_invalid_accept` | `IBE.lean` |
| §VI-A, S4-A | for `A ≠ 0`, exactly `q^{2n-2}` matrices `B` give `AB = X`; each `X` has `F = (q^n-1)q^{2n-2}` keys; the public-key line has `q` points, so `q(q^n-1)q^{2n-2}` keys | `Clria.Fiber.card_fiber_fixed_A`, `card_key_fiber`, `card_line`, `card_keys_given_pk` | `Fiber.lean` |
| S4-A | the fiber charge leaves `log q`; charging the printed `(3n-1) log q` exceeds `log q` at `λ = 0` | `Clria.Fiber.fiber_charge`, `printed_charge_exceeds` | `Fiber.lean` |
| S4-B, Theorem 9 | `A·B_p(A,Y) = Y`, `B_p` linear, `A·Res = X`; each target `B` is hit by exactly `q²` inputs, so `Res` is uniform | `Clria.Fiber.mul_Bp`, `Bp_add_smul`, `res_correct`, `res_uniform` | `Fiber.lean` |
| Lemma 2 | (a) `H̃∞(φ(S)|V) ≤ log N`; (b) `H̃∞(φ(S)|V) ≥ H̃∞(S|V) − log F`, on finite distributions | `Clria.Projection.lemma2a`, `lemma2b` | `Projection.lean` |
| S5-A, Prop. 12(a) | with `m` generators, `Rsp(st,ρ₀,2) − Rsp(st,ρ₀,1)` is a witness; two witnesses give a nontrivial relation; for CLR-IA the witness is `X` | `Clria.RefreshLimit.witness_of_responses`, `nontrivial_relation`, `clria_witness_is_product` | `RefreshLimit.lean` |
| Lemma 4, Cor. 13 | the `⌈ℓ/b⌉` pieces concatenate to `enc(φ)`; `⌈2w/b⌉ ≤ 2w`; one period when `b ≥ 2w` | `Clria.RefreshLimit.splice_chunks`, `periods_bound`, `one_period` | `RefreshLimit.lean` |
| §VIII-C, S7-A | `q` keys accept the invalid header (probability `1/q`, not `1/q³`); one tag per state; `d` fresh tags succeed with `1 − (1 − 1/q)^d` | `Clria.ProofWitness.claim2_fiber`, `claim2_ratio`, `one_tag_per_state`, `fresh_tags`, `fresh_tags_prob` | `ProofWitness.lean` |
| S7-A | three distinct points: `q` interpolants of degree ≤ 3, `q − 1` of degree exactly 3 | `Clria.ProofWitness.interpolation_count` | `ProofWitness.lean` |
| S7-B, eqs. (h2perfect), (h2error) | a view-determined `W` is at distance exactly `1 − 1/N`; every joint distribution is within `1 − 1/N`; a predictor with success `1 − ρ` forces distance `≥ 1 − ρ − 1/N` | `Clria.ProofWitness.sd_determined`, `sd_upper`, `event_le_sd`, `predictor_bound` | `ProofWitness.lean` |
| S8-B | collision counts per pair; `(h², h)` and `(h, h²)` collide only at `η = 1`; eq. (S5) `Σ_{η≠0} CP = qC_Z + 1 − C_A − C_B` | `Clria.Repairs.collSeeds_card`, `collide_at_one`, `collide_prob`, `collision_identity` | `Repairs.lean` |
| S8-B | `SD ≤ ½√(N·CP − 1)`; averaged over seeds `SD ≤ ½√((q²C_Z − 1)/(q − 1))`; `≤ ½√(p 2^{-k})` for `k ≥ log p` | `Clria.Repairs.sum_abs_le_sqrt`, `cp_ge`, `family_bound`, `final_bound` | `Repairs.lean` |
| S8-A | nonzero `R` with `⟨L,R⟩ = t`: `N/q − 1` or `N/q`; `Pr[Ḡ] = 2/N`; conditional law and `d_G = (q−1)/(q(N−1))`; deficit `log₂[N/(N−1)]`; thresholds for `N > 17`; the corrected conversion chain | `Clria.Repairs.df_fiber`, `df_bad_event`, `df_conditional`, `df_deficit`, `df_thresholds`, `df_conversion` | `Repairs.lean` |

Several theorems are slightly more general than the paper: nonces and challenges range over
all of `K`, `hᵢ`, `d`, `F` may be zero, the update identities do not use nonsingularity, the
bridge counterexample holds for every `n ≥ 2`, and the S8-B bound holds for any real weights
summing to `1`.

## Reproduce

```
lake exe cache get      # prebuilt Mathlib (about 5 GB unpacked, kept in .lake/, not committed)
lake build              # expected: "Build completed successfully", no warnings
lake env lean CheckAxioms.lean
```

All 90 listed theorems depend only on `propext`, `Classical.choice` and `Quot.sound` (some on
fewer). No `sorry` and no `native_decide` are used.
