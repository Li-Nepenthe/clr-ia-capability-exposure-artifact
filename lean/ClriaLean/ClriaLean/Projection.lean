import Mathlib

/-!
# Lemma 2 (projection) on finite distributions

Main paper, Lemma 2. A joint distribution of a state `S` and a view `V` on finite types is
given by weights `P s v ≥ 0` with total mass `1`. The average conditional min-entropy is
`H̃∞(S | V) = -log₂ Σ_v max_s P(s, v)`, and for a function `φ` of the state
`H̃∞(φ(S) | V) = -log₂ Σ_v max_z Σ_{s : φ s = z} P(s, v)`.

(a) If for every view at most `N` values of `φ(S)` have positive probability, then
`H̃∞(φ(S) | V) ≤ log₂ N`.
(b) If for every view and value at most `F` states of positive probability map to that value,
then `H̃∞(φ(S) | V) ≥ H̃∞(S | V) - log₂ F`.
-/

namespace Clria.Projection

open Finset

variable {S V Z : Type*} [Fintype S] [Fintype V] [Fintype Z] [Nonempty S] [Nonempty Z]
  [DecidableEq Z]

/-- Mass of the value `z` of `φ` jointly with the view `v`. -/
def mass (P : S → V → ℝ) (φ : S → Z) (z : Z) (v : V) : ℝ :=
  ∑ s ∈ univ.filter (fun s => φ s = z), P s v

/-- `Σ_v max_s P(s, v)`, the best guessing probability for `S` given `V`. -/
noncomputable def predS (P : S → V → ℝ) : ℝ :=
  ∑ v, univ.sup' univ_nonempty (fun s => P s v)

/-- `Σ_v max_z Pr[φ(S) = z, V = v]`, the best guessing probability for `φ(S)` given `V`. -/
noncomputable def predPhi (P : S → V → ℝ) (φ : S → Z) : ℝ :=
  ∑ v, univ.sup' univ_nonempty (fun z => mass P φ z v)

/-- Average conditional min-entropy `-log₂` of a guessing probability. -/
noncomputable def Hinf (pred : ℝ) : ℝ := -Real.logb 2 pred

omit [Fintype V] [Fintype Z] [Nonempty S] [Nonempty Z] in
lemma mass_nonneg {P : S → V → ℝ} (hP : ∀ s v, 0 ≤ P s v) (φ : S → Z) (z : Z) (v : V) :
    0 ≤ mass P φ z v :=
  sum_nonneg fun s _ => hP s v

omit [Fintype V] [Nonempty S] [Nonempty Z] in
lemma sum_mass (P : S → V → ℝ) (φ : S → Z) (v : V) :
    ∑ z, mass P φ z v = ∑ s, P s v := by
  simp only [mass]
  exact sum_fiberwise univ φ (fun s => P s v)

omit [Nonempty S] in
/-- Lemma 2(a), probability form: at most `N` positive values per view give
`predPhi ≥ 1/N`. -/
theorem predPhi_ge {P : S → V → ℝ} (hP : ∀ s v, 0 ≤ P s v) (hsum : ∑ s, ∑ v, P s v = 1)
    (φ : S → Z) (N : ℕ) (hN : 0 < N)
    (hcard : ∀ v, (univ.filter fun z => 0 < mass P φ z v).card ≤ N) :
    1 / (N : ℝ) ≤ predPhi P φ := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hv : ∀ v, (∑ s, P s v) / N ≤ univ.sup' univ_nonempty (fun z => mass P φ z v) := by
    intro v
    set M := univ.sup' univ_nonempty (fun z => mass P φ z v)
    have hM0 : 0 ≤ M := le_trans (mass_nonneg hP φ (Classical.arbitrary Z) v)
      (le_sup' (fun z => mass P φ z v) (mem_univ _))
    have hsplit : ∑ z, mass P φ z v = ∑ z ∈ univ.filter (fun z => 0 < mass P φ z v),
        mass P φ z v := by
      rw [sum_filter_of_ne]
      intro z _ hz
      exact lt_of_le_of_ne (mass_nonneg hP φ z v) (Ne.symm hz)
    have hle : ∑ z ∈ univ.filter (fun z => 0 < mass P φ z v), mass P φ z v ≤ N * M := by
      calc ∑ z ∈ univ.filter (fun z => 0 < mass P φ z v), mass P φ z v
          ≤ ∑ _z ∈ univ.filter (fun z => 0 < mass P φ z v), M :=
            sum_le_sum fun z _ => le_sup' (fun z => mass P φ z v) (mem_univ z)
        _ = (univ.filter fun z => 0 < mass P φ z v).card * M := by simp
        _ ≤ N * M := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard v) hM0
    rw [div_le_iff₀ hN', ← sum_mass P φ v, hsplit]
    linarith
  calc 1 / (N : ℝ) = (∑ v, ∑ s, P s v) / N := by rw [sum_comm, hsum]
    _ = ∑ v, (∑ s, P s v) / N := by rw [sum_div]
    _ ≤ predPhi P φ := sum_le_sum fun v _ => hv v

omit [Nonempty S] in
/-- Main paper, Lemma 2(a): `H̃∞(φ(S) | V) ≤ log₂ N`. -/
theorem lemma2a {P : S → V → ℝ} (hP : ∀ s v, 0 ≤ P s v) (hsum : ∑ s, ∑ v, P s v = 1)
    (φ : S → Z) (N : ℕ) (hN : 0 < N)
    (hcard : ∀ v, (univ.filter fun z => 0 < mass P φ z v).card ≤ N) :
    Hinf (predPhi P φ) ≤ Real.logb 2 N := by
  have h := predPhi_ge hP hsum φ N hN hcard
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  unfold Hinf
  have : Real.logb 2 (1 / (N : ℝ)) ≤ Real.logb 2 (predPhi P φ) :=
    Real.logb_le_logb_of_le (by norm_num) (by positivity) h
  rw [one_div, Real.logb_inv] at this
  linarith

/-- Lemma 2(b), probability form: at most `F` positive states per view and value give
`predPhi ≤ F · predS`. -/
theorem predPhi_le {P : S → V → ℝ} (hP : ∀ s v, 0 ≤ P s v) (φ : S → Z) (F : ℕ)
    (hcard : ∀ v z, (univ.filter fun s => φ s = z ∧ 0 < P s v).card ≤ F) :
    predPhi P φ ≤ F * predS P := by
  unfold predPhi predS
  rw [mul_sum]
  refine sum_le_sum fun v _ => ?_
  set M := univ.sup' univ_nonempty (fun s => P s v)
  have hM0 : 0 ≤ M := le_trans (hP (Classical.arbitrary S) v)
    (le_sup' (fun s => P s v) (mem_univ _))
  refine sup'_le _ _ fun z _ => ?_
  have hsplit : mass P φ z v = ∑ s ∈ univ.filter (fun s => φ s = z ∧ 0 < P s v), P s v := by
    simp only [mass]
    rw [← filter_filter]
    symm
    apply sum_filter_of_ne
    intro s _ hs
    exact lt_of_le_of_ne (hP s v) (Ne.symm hs)
  rw [hsplit]
  calc ∑ s ∈ univ.filter (fun s => φ s = z ∧ 0 < P s v), P s v
      ≤ ∑ _s ∈ univ.filter (fun s => φ s = z ∧ 0 < P s v), M :=
        sum_le_sum fun s _ => le_sup' (fun s => P s v) (mem_univ s)
    _ = (univ.filter fun s => φ s = z ∧ 0 < P s v).card * M := by simp
    _ ≤ F * M := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard v z) hM0

/-- Main paper, Lemma 2(b): `H̃∞(φ(S) | V) ≥ H̃∞(S | V) - log₂ F`. -/
theorem lemma2b {P : S → V → ℝ} (hP : ∀ s v, 0 ≤ P s v) (hsum : ∑ s, ∑ v, P s v = 1)
    (φ : S → Z) (F : ℕ) (hF : 0 < F)
    (hcard : ∀ v z, (univ.filter fun s => φ s = z ∧ 0 < P s v).card ≤ F) :
    Hinf (predS P) - Real.logb 2 F ≤ Hinf (predPhi P φ) := by
  have hle := predPhi_le hP φ F hcard
  have hpos : 0 < predPhi P φ := by
    have hN := predPhi_ge hP hsum φ (Fintype.card Z) Fintype.card_pos (fun v => by
      exact le_trans (card_le_univ _) le_rfl)
    exact lt_of_lt_of_le (by positivity) hN
  have hF' : (0 : ℝ) < F := by exact_mod_cast hF
  have hS : 0 < predS P := by
    have : 0 < (F : ℝ) * predS P := lt_of_lt_of_le hpos hle
    exact pos_of_mul_pos_right this hF'.le
  unfold Hinf
  have h := Real.logb_le_logb_of_le (b := 2) (by norm_num) hpos hle
  rw [Real.logb_mul hF'.ne' hS.ne'] at h
  linarith

end Clria.Projection
