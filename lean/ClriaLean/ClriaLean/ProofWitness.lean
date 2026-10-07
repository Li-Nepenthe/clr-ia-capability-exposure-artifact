import Mathlib

/-!
# Witnesses against two proof steps

Main paper, Section VIII-C; Supplement S7-A (Zhou and Yang, Claim 2) and S7-B
(Zhou et al., the extraction step). `K` is a finite field with `q = |K|`; uniform choices
are stated as counts, and statistical distance is `½ Σ |P - Q|` on finite types.
-/

namespace Clria.ProofWitness

open Finset

section Claim2

variable {K : Type*} [Field K] [Fintype K]

/-- Main paper, Section VIII-C, and Supplement S7-A: for uniform key coordinates
`(t₁, t₂)`, an invalid header is accepted exactly when `μ t₁ + t₂` takes one value, an event
on a fiber of `q` keys, i.e. probability `q/q² = 1/q`. -/
theorem claim2_fiber (μ z : K) :
    Nat.card {t : K × K // μ * t.1 + t.2 = z} = Fintype.card K := by
  let e : {t : K × K // μ * t.1 + t.2 = z} ≃ K :=
    { toFun := fun t => t.1.1
      invFun := fun u => ⟨(u, z - μ * u), by simp⟩
      left_inv := fun t => by
        obtain ⟨⟨a, b⟩, h⟩ := t
        simp only at h
        subst h
        apply Subtype.ext
        simp
      right_inv := fun u => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]

/-- The fiber probability `q/q² = 1/q` exceeds the single-query bound `1/q³` of Claim 2. -/
theorem claim2_ratio (q : ℚ) (hq : 2 ≤ q) : q / q ^ 2 = 1 / q ∧ 1 / q ^ 3 < 1 / q := by
  have hq0 : 0 < q := by linarith
  constructor
  · field_simp
  · rw [div_lt_div_iff₀ (by positivity) hq0]
    have h4 : (1 : ℚ) < q ^ 2 := by nlinarith
    have : q * 1 < q * q ^ 2 := mul_lt_mul_of_pos_left h4 hq0
    nlinarith

omit [Fintype K] in
/-- Supplement S7-A: every fixed state accepts exactly one tag. -/
theorem one_tag_per_state (μ t₁ t₂ : K) : Nat.card {z : K // μ * t₁ + t₂ = z} = 1 := by
  let e : {z : K // μ * t₁ + t₂ = z} ≃ Unit :=
    { toFun := fun _ => ()
      invFun := fun _ => ⟨μ * t₁ + t₂, rfl⟩
      left_inv := fun z => Subtype.ext z.2
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_unique]

omit [Field K] in
/-- Supplement S7-A: `d` fresh uniform tags hit the accepted one with probability
`1 - (1 - 1/q)^d`; as a count, `q^d - (q - 1)^d` tag tuples contain it. -/
theorem fresh_tags (z₀ : K) (d : ℕ) :
    Nat.card {zs : Fin d → K // ∃ i, zs i = z₀} =
      Fintype.card K ^ d - (Fintype.card K - 1) ^ d := by
  classical
  have hne : Nat.card {z : K // z ≠ z₀} = Fintype.card K - 1 := by
    have h := Nat.card_congr (Equiv.optionSubtypeNe z₀)
    rw [Finite.card_option, Nat.card_eq_fintype_card (α := K)] at h
    omega
  have hall : Nat.card {zs : Fin d → K // ∀ i, zs i ≠ z₀} = (Fintype.card K - 1) ^ d := by
    rw [Nat.card_congr (Equiv.subtypePiEquivPi (p := fun _ z => z ≠ z₀)), Nat.card_pi]
    simp only [hne, prod_const, card_univ, Fintype.card_fin]
  have hsplit : Nat.card {zs : Fin d → K // ∃ i, zs i = z₀} +
      Nat.card {zs : Fin d → K // ∀ i, zs i ≠ z₀} = Fintype.card K ^ d := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    have := Fintype.card_subtype_compl (fun zs : Fin d → K => ∃ i, zs i = z₀)
    have h2 : Fintype.card {zs : Fin d → K // ∀ i, zs i ≠ z₀} =
        Fintype.card {zs : Fin d → K // ¬∃ i, zs i = z₀} :=
      Fintype.card_congr (Equiv.subtypeEquivRight fun zs => by simp)
    have h3 := Fintype.card_subtype_le (fun zs : Fin d → K => ∃ i, zs i = z₀)
    simp only [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this h3
    omega
  omega

/-- The count of `fresh_tags` as a probability: `1 - (1 - 1/q)^d`. -/
theorem fresh_tags_prob (q : ℚ) (hq : 0 < q) (d : ℕ) :
    (q ^ d - (q - 1) ^ d) / q ^ d = 1 - (1 - 1 / q) ^ d := by
  rw [show 1 - 1 / q = (q - 1) / q by field_simp, div_pow]
  field_simp

end Claim2

/-! ## Interpolation counts (Supplement S7-A) -/

section Interpolation

variable {K : Type*} [Field K] [Fintype K]

omit [Fintype K] in
/-- Value at `t` of the polynomial `Σ_{k ≤ 3} c_k X^k` given by its coefficients. -/
def ev (c : Fin 4 → K) (t : K) : K := ∑ k, c k * t ^ (k : ℕ)

omit [Fintype K] in
/-- Coefficients of `(X - x₀)(X - x₁)(X - x₂)`. -/
def cubic (x : Fin 3 → K) : Fin 4 → K :=
  ![-(x 0 * x 1 * x 2), x 0 * x 1 + x 0 * x 2 + x 1 * x 2, -(x 0 + x 1 + x 2), 1]

omit [Fintype K] in
lemma ev_cubic (x : Fin 3 → K) (t : K) : ev (cubic x) t = (t - x 0) * (t - x 1) * (t - x 2) := by
  simp only [ev, cubic, Fin.sum_univ_four]
  simp
  ring

omit [Fintype K] in
lemma ev_cubic_root (x : Fin 3 → K) (i : Fin 3) : ev (cubic x) (x i) = 0 := by
  rw [ev_cubic]
  fin_cases i <;> simp

omit [Fintype K] in
lemma ev_add_smul (c c' : Fin 4 → K) (a t : K) : ev (c + a • c') t = ev c t + a * ev c' t := by
  simp only [ev, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

omit [Fintype K] in
lemma ev_sub (c c' : Fin 4 → K) (t : K) : ev (c - c') t = ev c t - ev c' t := by
  simp only [ev, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

omit [Fintype K] in
lemma ev_four (c : Fin 4 → K) (t : K) :
    ev c t = c 0 + c 1 * t + c 2 * t ^ 2 + c 3 * t ^ 3 := by
  simp [ev, Fin.sum_univ_four]

omit [Fintype K] in
/-- For three distinct points, the system `Σ_{k<3} c_k x_i^k = y_i` has exactly one solution
(the Vandermonde matrix is invertible). -/
lemma low_unique {x : Fin 3 → K} (hx : Function.Injective x) (y : Fin 3 → K) :
    ∃ c₀ : Fin 3 → K, (∀ i, ∑ k, c₀ k * x i ^ (k : ℕ) = y i) ∧
      ∀ c : Fin 3 → K, (∀ i, ∑ k, c k * x i ^ (k : ℕ) = y i) → c = c₀ := by
  set M := Matrix.vandermonde x
  have hdet : IsUnit M.det := (Matrix.det_vandermonde_ne_zero_iff.mpr hx).isUnit
  have hM : ∀ c : Fin 3 → K, (∀ i, ∑ k, c k * x i ^ (k : ℕ) = y i) ↔ M.mulVec c = y := by
    intro c
    constructor
    · intro h
      funext i
      rw [← h i]
      simp only [M, Matrix.mulVec, dotProduct, Matrix.vandermonde_apply]
      exact Finset.sum_congr rfl fun k _ => by ring
    · intro h i
      rw [← h]
      simp only [M, Matrix.mulVec, dotProduct, Matrix.vandermonde_apply]
      exact Finset.sum_congr rfl fun k _ => by ring
  refine ⟨M⁻¹.mulVec y, (hM _).mpr ?_, fun c hc => ?_⟩
  · rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  · rw [← (hM c).mp hc, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]

/-- Supplement S7-A: for three distinct points, every triple of values has exactly `q`
interpolating polynomials of degree at most three, and `q - 1` of degree exactly three. -/
theorem interpolation_count {x : Fin 3 → K} (hx : Function.Injective x) (y : Fin 3 → K) :
    Nat.card {c : Fin 4 → K // ∀ i, ev c (x i) = y i} = Fintype.card K ∧
    Nat.card {c : Fin 4 → K // (∀ i, ev c (x i) = y i) ∧ c 3 ≠ 0} = Fintype.card K - 1 := by
  classical
  obtain ⟨c₀', hc₀', huniq⟩ := low_unique hx y
  let c₀ : Fin 4 → K := ![c₀' 0, c₀' 1, c₀' 2, 0]
  have hcub3 : cubic x 3 = 1 := rfl
  have hc₀ : ∀ i, ev c₀ (x i) = y i := by
    intro i
    have h := hc₀' i
    simp only [Fin.sum_univ_three] at h
    rw [ev_four, ← h]
    simp [c₀]
  -- every solution is c₀ + c_3 · cubic
  have hform : ∀ c : Fin 4 → K, (∀ i, ev c (x i) = y i) → c₀ + c 3 • cubic x = c := by
    intro c hc
    set d := c - c 3 • cubic x with hd_def
    have hd3 : d 3 = 0 := by simp [d, hcub3]
    have hdlow : ∀ i, ∑ k, (![d 0, d 1, d 2] : Fin 3 → K) k * x i ^ (k : ℕ) = y i := by
      intro i
      have h1 : ev d (x i) = y i := by
        rw [show d = c + (-c 3) • cubic x by simp [d, sub_eq_add_neg],
          ev_add_smul, ev_cubic_root, hc i]
        ring
      rw [ev_four, hd3] at h1
      simp only [Fin.sum_univ_three]
      simpa using h1
    have hlow := huniq _ hdlow
    have hdc₀ : d = c₀ := by
      funext k
      fin_cases k
      · simpa [c₀] using congrFun hlow 0
      · simpa [c₀] using congrFun hlow 1
      · simpa [c₀] using congrFun hlow 2
      · simpa [c₀] using hd3
    rw [← hdc₀]
    simp [d]
  have hlast : ∀ a : K, (c₀ + a • cubic x) 3 = a := fun a => by simp [c₀, hcub3]
  let e : {c : Fin 4 → K // ∀ i, ev c (x i) = y i} ≃ K :=
    { toFun := fun c => c.1 3
      invFun := fun a => ⟨c₀ + a • cubic x, fun i => by
        rw [ev_add_smul, ev_cubic_root, hc₀ i, mul_zero, add_zero]⟩
      left_inv := fun c => Subtype.ext (hform c.1 c.2)
      right_inv := fun a => hlast a }
  refine ⟨by rw [Nat.card_congr e, Nat.card_eq_fintype_card], ?_⟩
  let e' : {c : Fin 4 → K // (∀ i, ev c (x i) = y i) ∧ c 3 ≠ 0} ≃ {a : K // a ≠ 0} :=
    { toFun := fun c => ⟨c.1 3, c.2.2⟩
      invFun := fun a => ⟨c₀ + a.1 • cubic x, fun i => by
        rw [ev_add_smul, ev_cubic_root, hc₀ i, mul_zero, add_zero], by rw [hlast]; exact a.2⟩
      left_inv := fun c => Subtype.ext (hform c.1 c.2.1)
      right_inv := fun a => Subtype.ext (hlast a.1) }
  rw [Nat.card_congr e']
  have h := Nat.card_congr (Equiv.optionSubtypeNe (0 : K))
  rw [Finite.card_option, Nat.card_eq_fintype_card (α := K)] at h
  omega

end Interpolation

/-! ## Statistical distance (Supplement S7-B) -/

section Distance

variable {W V : Type*} [Fintype W] [Fintype V] [Nonempty W]

/-- Statistical distance `½ Σ |P - Q|`. -/
noncomputable def sd {α : Type*} [Fintype α] (P Q : α → ℝ) : ℝ := (1 / 2) * ∑ a, |P a - Q a|

/-- A nonnegative weight `r` of total mass `m` on `N` points satisfies
`Σ |r w - m/N| ≤ 2m(1 - 1/N)`. -/
lemma sum_abs_le (r : W → ℝ) (hr : ∀ w, 0 ≤ r w) :
    ∑ w, |r w - (∑ u, r u) / Fintype.card W| ≤
      2 * (∑ u, r u) * (1 - 1 / Fintype.card W) := by
  set m := ∑ u, r u
  set N : ℝ := (Fintype.card W : ℝ)
  have hN : 0 < N := by simp [N, Fintype.card_pos]
  have hm : 0 ≤ m := sum_nonneg fun w _ => hr w
  -- some point carries at least the average mass
  obtain ⟨w₀, hw₀⟩ : ∃ w₀, m / N ≤ r w₀ := by
    by_contra h
    simp only [not_exists, not_le] at h
    have : ∑ w, r w < ∑ _w : W, m / N := sum_lt_sum_of_nonempty univ_nonempty fun w _ => h w
    simp only [sum_const, card_univ, nsmul_eq_mul] at this
    rw [show (Fintype.card W : ℝ) * (m / N) = m by simp [N]; field_simp] at this
    linarith
  have habs : ∀ w, |r w - m / N| = r w + m / N - 2 * min (r w) (m / N) := by
    intro w
    rcases le_total (r w) (m / N) with h | h
    · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
    · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring
  have hmin : m / N ≤ ∑ w, min (r w) (m / N) := by
    have := single_le_sum (f := fun w => min (r w) (m / N))
      (fun w _ => le_min (hr w) (div_nonneg hm hN.le)) (mem_univ w₀)
    simp only [min_eq_right hw₀] at this
    exact this
  simp only [habs, sum_sub_distrib, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul,
    ← mul_sum]
  rw [show (Fintype.card W : ℝ) * (m / N) = m by simp [N]; field_simp]
  have : 2 * m * (1 - 1 / N) = 2 * m - 2 * (m / N) := by field_simp
  rw [this]
  linarith

/-- Supplement S7-B, eq. (h2perfect): if the view determines `W`, the joint distribution of
(view, `W`) is at distance exactly `1 - 1/N` from (view, uniform), `N = 2^{l_k}`. -/
theorem sd_determined [DecidableEq W] (PV : V → ℝ) (hPV : ∀ v, 0 ≤ PV v) (hsum : ∑ v, PV v = 1)
    (f : V → W) :
    sd (fun p : V × W => if p.2 = f p.1 then PV p.1 else 0)
      (fun p : V × W => PV p.1 / Fintype.card W) = 1 - 1 / Fintype.card W := by
  set N : ℝ := (Fintype.card W : ℝ)
  have hN : 0 < N := by simp [N, Fintype.card_pos]
  have hrow : ∀ v, ∑ w : W, |(if w = f v then PV v else 0) - PV v / N| =
      2 * PV v * (1 - 1 / N) := by
    intro v
    rw [← add_sum_erase _ _ (mem_univ (f v))]
    simp only [↓reduceIte]
    have hrest : ∑ w ∈ univ.erase (f v), |(if w = f v then PV v else 0) - PV v / N| =
        ((Fintype.card W : ℝ) - 1) * (PV v / N) := by
      rw [sum_congr rfl fun w hw => by
        simp only [ne_of_mem_erase hw, ↓reduceIte, zero_sub, abs_neg]
        rw [abs_of_nonneg (div_nonneg (hPV v) hN.le)]]
      rw [sum_const, card_erase_of_mem (mem_univ _), card_univ, nsmul_eq_mul,
        Nat.cast_sub Fintype.card_pos]
      simp
    rw [hrest, abs_of_nonneg (by
      have : PV v / N ≤ PV v := div_le_self (hPV v) (by
        have : (1 : ℝ) ≤ Fintype.card W := by exact_mod_cast Fintype.card_pos
        simpa [N] using this)
      linarith)]
    field_simp
    ring
  unfold sd
  rw [Fintype.sum_prod_type]
  simp only [hrow, ← sum_mul, ← mul_sum, hsum]
  ring

/-- Supplement S7-B, upper bounds in eqs. (h2perfect) and (h2error): every joint distribution
of (view, `W`) with view marginal `PV` is within `1 - 1/N` of (view, uniform). -/
theorem sd_upper (R : V × W → ℝ) (hR : ∀ p, 0 ≤ R p) (PV : V → ℝ)
    (hrow : ∀ v, ∑ w, R (v, w) = PV v) (hPV : ∑ v, PV v = 1) :
    sd R (fun p : V × W => PV p.1 / Fintype.card W) ≤ 1 - 1 / Fintype.card W := by
  unfold sd
  rw [Fintype.sum_prod_type]
  have h : ∀ v, ∑ w, |R (v, w) - PV v / Fintype.card W| ≤
      2 * PV v * (1 - 1 / Fintype.card W) := by
    intro v
    have := sum_abs_le (fun w => R (v, w)) (fun w => hR (v, w))
    rw [hrow v] at this
    exact this
  calc (1 / 2) * ∑ v, ∑ w, |R (v, w) - PV v / Fintype.card W|
      ≤ (1 / 2) * ∑ v, 2 * PV v * (1 - 1 / Fintype.card W) :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun v _ => h v) (by norm_num)
    _ = 1 - 1 / Fintype.card W := by
        rw [← sum_mul, ← mul_sum, hPV]
        ring

/-- For any event `E`, `P(E) - Q(E) ≤ SD(P, Q)` when both have total mass `1`. -/
theorem event_le_sd {α : Type*} [Fintype α] (P Q : α → ℝ) (hP : ∑ a, P a = 1) (hQ : ∑ a, Q a = 1)
    (E : Finset α) : ∑ a ∈ E, P a - ∑ a ∈ E, Q a ≤ sd P Q := by
  classical
  have h1 : ∑ a ∈ E, (P a - Q a) ≤ ∑ a ∈ E, |P a - Q a| := sum_le_sum fun a _ => le_abs_self _
  have h2 : ∑ a ∈ Eᶜ, (Q a - P a) ≤ ∑ a ∈ Eᶜ, |P a - Q a| :=
    sum_le_sum fun a _ => by rw [abs_sub_comm]; exact le_abs_self _
  have hc : ∑ a ∈ E, (P a - Q a) = ∑ a ∈ Eᶜ, (Q a - P a) := by
    have hP' := sum_add_sum_compl E P
    have hQ' := sum_add_sum_compl E Q
    simp only [sum_sub_distrib]
    linarith
  have htot : ∑ a ∈ E, |P a - Q a| + ∑ a ∈ Eᶜ, |P a - Q a| = ∑ a, |P a - Q a| :=
    sum_add_sum_compl E _
  unfold sd
  rw [← sum_sub_distrib]
  linarith

/-- Supplement S7-B, eq. (h2error): if a predictor from the view recovers the extractor
output with probability at least `1 - ρ`, the joint distance is at least `1 - ρ - 1/N`;
under the uniform side the test `w = g(v)` has probability exactly `1/N`. -/
theorem predictor_bound [DecidableEq W] (R : V × W → ℝ) (PV : V → ℝ) (hR : ∑ p, R p = 1)
    (hPV : ∑ v, PV v = 1) (g : V → W) (ρ : ℝ)
    (hpred : 1 - ρ ≤ ∑ p ∈ univ.filter (fun p : V × W => p.2 = g p.1), R p) :
    1 - ρ - 1 / Fintype.card W ≤ sd R (fun p : V × W => PV p.1 / Fintype.card W) := by
  have hN : (0 : ℝ) < Fintype.card W := by exact_mod_cast Fintype.card_pos
  have hU : ∑ p : V × W, PV p.1 / Fintype.card W = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [sum_const, card_univ, nsmul_eq_mul]
    calc ∑ x, (Fintype.card W : ℝ) * (PV x / Fintype.card W) = ∑ x, PV x :=
          sum_congr rfl fun x _ => by field_simp
      _ = 1 := hPV
  have hUT : ∑ p ∈ univ.filter (fun p : V × W => p.2 = g p.1), PV p.1 / Fintype.card W =
      1 / Fintype.card W := by
    rw [sum_filter, Fintype.sum_prod_type]
    simp only [sum_ite_eq', mem_univ, ite_true]
    rw [← sum_div, hPV]
  have := event_le_sd R _ hR hU (univ.filter fun p : V × W => p.2 = g p.1)
  linarith

end Distance

end Clria.ProofWitness
