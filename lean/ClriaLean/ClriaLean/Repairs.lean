import Mathlib
import ClriaLean.Fiber

/-!
# Local repairs: exact counts

Supplement S8. Part S8-B: the seeded family `H_η(X, Y) = X Y^η`, written on exponents as
`A + η B` with `η ∈ K^*`. Part S8-A: the Dziembowski–Faust scalar witness and the corrected
probability conversion. `K` is a finite field with `q = |K|`.
-/

namespace Clria.Repairs

open Finset

/-! ## S8-B: collisions of `A + ηB` -/

section Family

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- `η` makes `H_η` collide on the pairs `z = (A, B)` and `z' = (A', B')`. -/
def Coll (η : K) (z z' : K × K) : Prop := z.1 + η * z.2 = z'.1 + η * z'.2

instance (η : K) (z z' : K × K) : Decidable (Coll η z z') := by unfold Coll; infer_instance

/-- Nonzero seeds on which `z` and `z'` collide. -/
def collSeeds (z z' : K × K) : Finset K := univ.filter fun η => η ≠ 0 ∧ Coll η z z'

/-- Supplement S8-B: when both coordinates agree every nonzero seed collides, when exactly
one agrees none does, and otherwise exactly one does. As a single count:
`#{η ≠ 0 : collide} = q·[z = z'] + 1 - [A = A'] - [B = B']`. -/
theorem collSeeds_card (z z' : K × K) :
    ((collSeeds z z').card : ℝ) = Fintype.card K * (if z = z' then 1 else 0) + 1
      - (if z.1 = z'.1 then 1 else 0) - (if z.2 = z'.2 then 1 else 0) := by
  obtain ⟨A, B⟩ := z
  obtain ⟨A', B'⟩ := z'
  simp only [Prod.mk.injEq]
  by_cases hA : A = A' <;> by_cases hB : B = B'
  · -- both agree: all q - 1 nonzero seeds
    subst hA hB
    have : collSeeds (A, B) (A, B) = univ.erase 0 := by
      ext η
      simp [collSeeds, Coll]
    rw [this, card_erase_of_mem (mem_univ _), card_univ, Nat.cast_sub Fintype.card_pos]
    simp
  · -- only A agrees: η (B - B') = 0 forces η = 0
    subst hA
    have : collSeeds (A, B) (A, B') = ∅ := by
      ext η
      simp only [collSeeds, Coll, mem_filter, mem_univ, true_and, add_right_inj,
        Finset.notMem_empty, iff_false, not_and]
      intro hη h
      exact hB (mul_left_cancel₀ hη h)
    simp [this, hB]
  · -- only B agrees: never
    subst hB
    have : collSeeds (A, B) (A', B) = ∅ := by
      ext η
      simp only [collSeeds, Coll, mem_filter, mem_univ, true_and, add_left_inj,
        Finset.notMem_empty, iff_false, not_and]
      intro _ h
      exact hA h
    simp [this, hA]
  · -- both differ: exactly η = (A' - A)/(B - B')
    have hBB : B - B' ≠ 0 := sub_ne_zero.mpr hB
    have : collSeeds (A, B) (A', B') = {(A' - A) / (B - B')} := by
      ext η
      rw [collSeeds, mem_filter, mem_singleton]
      simp only [mem_univ, true_and, Coll]
      constructor
      · rintro ⟨_, h⟩
        field_simp
        linear_combination h
      · rintro rfl
        refine ⟨div_ne_zero (sub_ne_zero.mpr (Ne.symm hA)) hBB, ?_⟩
        field_simp
        ring
    simp [this, hA, hB]

omit [Fintype K] [DecidableEq K] in
/-- Supplement S8-B: the distinct pairs `(h², h)` and `(h, h²)`, i.e. `(2, 1)` and `(1, 2)`
on exponents, collide exactly at `η = 1`. -/
theorem collide_at_one (η : K) : Coll η ((2 : K), (1 : K)) ((1 : K), (2 : K)) ↔ η = 1 := by
  simp only [Coll]
  constructor
  · intro h
    linear_combination -h
  · rintro rfl
    ring

/-- One collision among the `q - 1` seeds, i.e. probability `1/(q - 1) > 1/q`. -/
theorem collide_prob (q : ℚ) (hq : 2 ≤ q) : 1 / q < 1 / (q - 1) := by
  apply one_div_lt_one_div_of_lt (by linarith) (by linarith)

variable (P : K × K → ℝ)

/-- `C_Z = Pr[Z = Z']`, `C_A = Pr[A = A']`, `C_B = Pr[B = B']` for independent copies. -/
def CZ : ℝ := ∑ z, ∑ z', P z * P z' * (if z = z' then 1 else 0)
def CA : ℝ := ∑ z, ∑ z', P z * P z' * (if z.1 = z'.1 then 1 else 0)
def CB : ℝ := ∑ z, ∑ z', P z * P z' * (if z.2 = z'.2 then 1 else 0)

/-- `CP(A + ηB) = Pr[A + ηB = A' + ηB']`. -/
def CPeta (η : K) : ℝ := ∑ z, ∑ z', P z * P z' * (if Coll η z z' then 1 else 0)

/-- Supplement S8-B, eq. (S5): `Σ_{η ≠ 0} CP(A + ηB) = q C_Z + 1 - C_A - C_B`, so the
average over the `q - 1` nonzero seeds is `(q C_Z + 1 - C_A - C_B)/(q - 1)`. -/
theorem collision_identity (hP : ∑ z, P z = 1) :
    ∑ η ∈ univ.filter (fun η : K => η ≠ 0), CPeta P η =
      Fintype.card K * CZ P + 1 - CA P - CB P := by
  have hswap : ∑ η ∈ univ.filter (fun η : K => η ≠ 0), CPeta P η =
      ∑ z, ∑ z', P z * P z' * ((collSeeds z z').card : ℝ) := by
    simp only [CPeta]
    rw [sum_comm]
    refine sum_congr rfl fun z _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun z' _ => ?_
    rw [← mul_sum, collSeeds, card_filter, Nat.cast_sum, sum_filter]
    congr 1
    refine sum_congr rfl fun η _ => ?_
    by_cases hη : η = 0 <;> simp [hη]
  rw [hswap]
  have hexp : ∀ z z' : K × K, P z * P z' * ((collSeeds z z').card : ℝ) =
      Fintype.card K * (P z * P z' * (if z = z' then 1 else 0)) + P z * P z'
        - P z * P z' * (if z.1 = z'.1 then 1 else 0)
        - P z * P z' * (if z.2 = z'.2 then 1 else 0) := by
    intro z z'
    rw [collSeeds_card]
    ring
  simp only [hexp, sum_add_distrib, sum_sub_distrib, ← mul_sum]
  rw [← sum_mul, hP, one_mul]
  rfl

/-! ### Collision probability and statistical distance -/

/-- The collision probability of the image of `P` under `f` is
`Σ_t (Σ_{x : f x = t} P x)² = Σ_{x, x'} P x P x' [f x = f x']`. -/
lemma sq_sum_fiber {X T : Type*} [Fintype X] [Fintype T] [DecidableEq T] (p : X → ℝ) (f : X → T) :
    ∑ t, (∑ x, if f x = t then p x else 0) ^ 2 =
      ∑ x, ∑ x', p x * p x' * (if f x = f x' then 1 else 0) := by
  simp only [sq, sum_mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun x' _ => ?_
  by_cases h : f x = f x'
  · simp only [h, ↓reduceIte, mul_one]
    rw [sum_eq_single (f x')]
    · simp
    · intro t _ ht
      simp [Ne.symm ht]
    · simp
  · simp only [h, ↓reduceIte, mul_zero]
    have h' : f x' ≠ f x := fun e => h e.symm
    refine sum_eq_zero fun t _ => ?_
    by_cases ht : f x = t
    · subst ht
      simp [h']
    · simp [ht]

/-- Cauchy–Schwarz: a distribution on `N` points has collision probability at least `1/N`. -/
lemma cp_ge {X : Type*} [Fintype X] [Nonempty X] (p : X → ℝ) (hp : ∑ x, p x = 1) :
    1 / (Fintype.card X : ℝ) ≤ ∑ x, p x ^ 2 := by
  have hN : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have h := sum_mul_sq_le_sq_mul_sq univ p (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, sum_const, card_univ, nsmul_eq_mul, hp] at h
  rw [div_le_iff₀ hN]
  linarith

/-- Supplement S8-B: `SD(V, U) ≤ ½ √(N·CP(V) - 1)`, written as
`Σ |p - 1/N| ≤ √(N Σ p² - 1)`. -/
lemma sum_abs_le_sqrt {X : Type*} [Fintype X] [Nonempty X] (p : X → ℝ) (hp : ∑ x, p x = 1) :
    ∑ x, |p x - 1 / Fintype.card X| ≤ Real.sqrt (Fintype.card X * ∑ x, p x ^ 2 - 1) := by
  set N : ℝ := (Fintype.card X : ℝ)
  have hN : 0 < N := by simp [N, Fintype.card_pos]
  have hcs := sum_mul_sq_le_sq_mul_sq univ (fun x => |p x - 1 / N|) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, sum_const, card_univ, nsmul_eq_mul, sq_abs] at hcs
  have hsq : ∑ x, (p x - 1 / N) ^ 2 = ∑ x, p x ^ 2 - 1 / N := by
    simp only [sub_sq, sum_add_distrib, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul,
      ← mul_sum, ← sum_mul, hp]
    field_simp
    ring
  rw [hsq] at hcs
  have hnn : 0 ≤ ∑ x, |p x - 1 / N| := sum_nonneg fun x _ => abs_nonneg _
  calc ∑ x, |p x - 1 / N| = Real.sqrt ((∑ x, |p x - 1 / N|) ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt (N * ∑ x, p x ^ 2 - 1) := by
      apply Real.sqrt_le_sqrt
      have : (∑ x, p x ^ 2 - 1 / N) * N = N * ∑ x, p x ^ 2 - 1 := by field_simp
      linarith

/-- Concavity of the square root, by Cauchy–Schwarz: `Σ_{i ∈ s} √aᵢ ≤ √(|s| Σ aᵢ)`. -/
lemma sum_sqrt_le {ι : Type*} (s : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) :
    ∑ i ∈ s, Real.sqrt (a i) ≤ Real.sqrt (s.card * ∑ i ∈ s, a i) := by
  have hcs := sum_mul_sq_le_sq_mul_sq s (fun i => Real.sqrt (a i)) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, sum_const, nsmul_eq_mul] at hcs
  rw [sum_congr rfl fun i hi => Real.sq_sqrt (ha i hi)] at hcs
  have hnn : 0 ≤ ∑ i ∈ s, Real.sqrt (a i) := sum_nonneg fun i _ => Real.sqrt_nonneg _
  calc ∑ i ∈ s, Real.sqrt (a i) = Real.sqrt ((∑ i ∈ s, Real.sqrt (a i)) ^ 2) :=
        (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt (s.card * ∑ i ∈ s, a i) := Real.sqrt_le_sqrt (by linarith)

/-- Distribution of `A + ηB`. -/
def dist (η : K) (t : K) : ℝ := ∑ z, if z.1 + η * z.2 = t then P z else 0

/-- Supplement S8-B, unconditional bound: averaged over the `q - 1` nonzero seeds,
`SD((A + ηB, η), (U, η)) ≤ ½ √((q² C_Z - 1)/(q - 1))`. -/
theorem family_bound (hP : ∑ z, P z = 1) (hq : 2 ≤ Fintype.card K) :
    (1 / ((Fintype.card K : ℝ) - 1)) * ∑ η ∈ univ.filter (fun η : K => η ≠ 0),
        (1 / 2) * ∑ t, |dist P η t - 1 / Fintype.card K| ≤
      (1 / 2) * Real.sqrt (((Fintype.card K : ℝ) ^ 2 * CZ P - 1) / ((Fintype.card K : ℝ) - 1)) := by
  have hq' : (2 : ℝ) ≤ (Fintype.card K : ℝ) := by exact_mod_cast hq
  set q : ℝ := (Fintype.card K : ℝ)
  have hq1 : 0 < q - 1 := by linarith
  set S := univ.filter (fun η : K => η ≠ 0)
  have hS : (S.card : ℝ) = q - 1 := by
    have : S = univ.erase 0 := by ext η; simp [S]
    rw [this, card_erase_of_mem (mem_univ _), card_univ, Nat.cast_sub Fintype.card_pos]
    simp [q]
  have hdist1 : ∀ η, ∑ t, dist P η t = 1 := by
    intro η
    simp only [dist]
    rw [sum_comm]
    simp [sum_ite_eq, hP]
  have hcp : ∀ η, ∑ t, dist P η t ^ 2 = CPeta P η := by
    intro η
    simp only [dist, CPeta, Coll]
    exact sq_sum_fiber P (fun z => z.1 + η * z.2)
  -- per seed: SD ≤ ½ √(q CP - 1)
  have hseed : ∀ η, ∑ t, |dist P η t - 1 / q| ≤ Real.sqrt (q * CPeta P η - 1) := by
    intro η
    rw [← hcp η]
    exact sum_abs_le_sqrt (dist P η) (hdist1 η)
  have hnonneg : ∀ η, 0 ≤ q * CPeta P η - 1 := by
    intro η
    have := cp_ge (dist P η) (hdist1 η)
    rw [hcp η] at this
    have hq0 : 0 < q := by linarith
    rw [div_le_iff₀ hq0] at this
    linarith
  -- marginal collision probabilities are at least 1/q
  have hCA : 1 / q ≤ CA P := by
    have h := sq_sum_fiber P (fun z : K × K => z.1)
    have hm : ∑ a : K, (∑ z : K × K, if z.1 = a then P z else 0) = 1 := by
      rw [sum_comm]; simp [sum_ite_eq, hP]
    have := cp_ge (fun a : K => ∑ z : K × K, if z.1 = a then P z else 0) hm
    simp only [CA]
    rw [← h]
    exact this
  have hCB : 1 / q ≤ CB P := by
    have h := sq_sum_fiber P (fun z : K × K => z.2)
    have hm : ∑ a : K, (∑ z : K × K, if z.2 = a then P z else 0) = 1 := by
      rw [sum_comm]; simp [sum_ite_eq, hP]
    have := cp_ge (fun a : K => ∑ z : K × K, if z.2 = a then P z else 0) hm
    simp only [CB]
    rw [← h]
    exact this
  have hid := collision_identity P hP
  -- sum over seeds of (q CP - 1) ≤ q² C_Z - 1
  have hsum : ∑ η ∈ S, (q * CPeta P η - 1) ≤ q ^ 2 * CZ P - 1 := by
    rw [sum_sub_distrib, ← mul_sum, hid, sum_const, nsmul_eq_mul, hS]
    have hq0 : 0 < q := by linarith
    have h2 : q * (1 / q) = 1 := by field_simp
    nlinarith
  calc (1 / (q - 1)) * ∑ η ∈ S, (1 / 2) * ∑ t, |dist P η t - 1 / q|
      ≤ (1 / (q - 1)) * ∑ η ∈ S, (1 / 2) * Real.sqrt (q * CPeta P η - 1) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact sum_le_sum fun η _ => mul_le_mul_of_nonneg_left (hseed η) (by norm_num)
    _ = (1 / 2) * ((1 / (q - 1)) * ∑ η ∈ S, Real.sqrt (q * CPeta P η - 1)) := by
        rw [← mul_sum]; ring
    _ ≤ (1 / 2) * ((1 / (q - 1)) * Real.sqrt ((q - 1) * (q ^ 2 * CZ P - 1))) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc ∑ η ∈ S, Real.sqrt (q * CPeta P η - 1)
            ≤ Real.sqrt (S.card * ∑ η ∈ S, (q * CPeta P η - 1)) :=
              sum_sqrt_le S _ fun η _ => hnonneg η
          _ ≤ Real.sqrt ((q - 1) * (q ^ 2 * CZ P - 1)) := by
              rw [hS]
              exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hsum hq1.le)
    _ = (1 / 2) * Real.sqrt ((q ^ 2 * CZ P - 1) / (q - 1)) := by
        congr 1
        rw [Real.sqrt_mul hq1.le, show (q ^ 2 * CZ P - 1) / (q - 1) =
          (q ^ 2 * CZ P - 1) * (1 / (q - 1)) by ring]
        have hnn : 0 ≤ q ^ 2 * CZ P - 1 := by
          have := sum_nonneg fun η (_ : η ∈ S) => hnonneg η
          linarith
        rw [Real.sqrt_mul hnn, Real.sqrt_div' 1 hq1.le]
        have hsq : Real.sqrt (q - 1) ^ 2 = q - 1 := Real.sq_sqrt hq1.le
        have hpos : 0 < Real.sqrt (q - 1) := Real.sqrt_pos.mpr hq1
        field_simp
        rw [hsq]
        ring

/-- Supplement S8-B, eq. (familyrepair-detail), last step: for `log p ≤ k`, i.e.
`x = 2^{-k} ≤ 1/p`, `½ √((p² x - 1)/(p - 1)) ≤ ½ √(p x)`. -/
theorem final_bound (p x : ℝ) (hp : 1 < p) (hx : x ≤ 1 / p) :
    (1 / 2) * Real.sqrt ((p ^ 2 * x - 1) / (p - 1)) ≤ (1 / 2) * Real.sqrt (p * x) := by
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.sqrt_le_sqrt
  have hp1 : 0 < p - 1 := by linarith
  rw [div_le_iff₀ hp1]
  have hp0 : 0 < p := by linarith
  have : p * x ≤ 1 := by rw [le_div_iff₀ hp0] at hx; linarith
  nlinarith

end Family

/-! ## S8-A: the Dziembowski–Faust scalar witness -/

section DF

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {n : ℕ}

/-- Supplement S8-A: for `L ≠ 0`, the nonzero right vectors with `⟨L, R⟩ = t` number
`N/q - 1` for `t = 0` and `N/q` otherwise (`N = q^n`). -/
theorem df_fiber {L : Fin n → K} (hL : L ≠ 0) (t : K) :
    Nat.card {R : Fin n → K // R ≠ 0 ∧ L ⬝ᵥ R = t} =
      Fintype.card K ^ (n - 1) - (if t = 0 then 1 else 0) := by
  classical
  have hfib := Clria.Fiber.card_dot_fiber hL t
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hfib ⊢
  by_cases ht : t = 0
  · subst ht
    have : (univ.filter fun R : Fin n → K => R ≠ 0 ∧ L ⬝ᵥ R = 0) =
        (univ.filter fun R : Fin n → K => L ⬝ᵥ R = 0).erase 0 := by
      ext R
      simp [and_comm]
    rw [this, card_erase_of_mem (by simp), hfib]
    simp
  · have : (univ.filter fun R : Fin n → K => R ≠ 0 ∧ L ⬝ᵥ R = t) =
        (univ.filter fun R : Fin n → K => L ⬝ᵥ R = t) := by
      ext R
      simp only [mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
      rintro h rfl
      simp at h
      exact ht h.symm
    rw [this, hfib]
    simp [ht]

/-- Supplement S8-A: `Pr[Ḡ] = Pr[L = l₀ ∨ R = 0] = 2/N` for independent uniform `L ≠ 0` and
`R`, since `1/(N - 1) + 1/N - 1/(N(N - 1)) = 2/N`. -/
theorem df_bad_event (N : ℝ) (hN : 1 < N) : 1 / (N - 1) + 1 / N - 1 / (N * (N - 1)) = 2 / N := by
  have h1 : N - 1 ≠ 0 := by linarith
  have h0 : N ≠ 0 := by linarith
  field_simp
  ring

/-- Supplement S8-A: given `G`, `Pr[T = 0 | G] = (N/q - 1)/(N - 1)` and
`Pr[T = t | G] = N/(q(N - 1))` for `t ≠ 0`; these sum to `1` and have distance
`d_G = (q - 1)/(q(N - 1))` from uniform on `q` values. -/
theorem df_conditional (q N : ℝ) (hq : 1 < q) (hN : 1 < N) :
    (N / q - 1) / (N - 1) + (q - 1) * (N / (q * (N - 1))) = 1 ∧
    (1 / 2) * (|(N / q - 1) / (N - 1) - 1 / q| + (q - 1) * |N / (q * (N - 1)) - 1 / q|) =
      (q - 1) / (q * (N - 1)) := by
  have hq0 : 0 < q := by linarith
  have hN1 : 0 < N - 1 := by linarith
  have e0 : (N / q - 1) / (N - 1) - 1 / q = -((q - 1) / (q * (N - 1))) := by
    field_simp; ring
  have e1 : N / (q * (N - 1)) - 1 / q = 1 / (q * (N - 1)) := by
    field_simp; ring
  refine ⟨by field_simp; ring, ?_⟩
  rw [e0, e1, abs_neg, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  field_simp
  ring

/-- Supplement S8-A: the entropy deficit of `T | G` is `log₂[N/(N - 1)]`. -/
theorem df_deficit (q N : ℝ) (hq : 1 < q) (hN : 1 < N) :
    -Real.logb 2 (N / (q * (N - 1))) = Real.logb 2 q - Real.logb 2 (N / (N - 1)) := by
  have hq0 : 0 < q := by linarith
  have hN0 : 0 < N := by linarith
  have hN1 : 0 < N - 1 := by linarith
  rw [show N / (q * (N - 1)) = (N / (N - 1)) / q by field_simp,
    Real.logb_div (by positivity) hq0.ne']
  ring

/-- Supplement S8-A: with `γ = 1/8` and `N > 17`, the thresholds `k_L = log₂(N - 1) - 4` and
`k_R = log₂ N - 4` are positive, and the predicate-zero branches stay above them:
`log₂(N - 2) > k_L` and `log₂(N - 1) > k_R`. -/
theorem df_thresholds (N : ℝ) (hN : 17 < N) :
    0 < Real.logb 2 (N - 1) - 4 ∧ 0 < Real.logb 2 N - 4 ∧
    Real.logb 2 (N - 1) - 4 < Real.logb 2 (N - 2) ∧ Real.logb 2 N - 4 < Real.logb 2 (N - 1) := by
  have h16 : Real.logb 2 16 = 4 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one] <;> norm_num
  have key : ∀ a b : ℝ, 0 < a → 0 < b → a < 16 * b → Real.logb 2 a - 4 < Real.logb 2 b := by
    intro a b ha hb hab
    have := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) ha hab
    rw [Real.logb_mul (by norm_num) hb.ne', h16] at this
    linarith
  have hpos : ∀ a : ℝ, 16 < a → 0 < Real.logb 2 a - 4 := by
    intro a ha
    have := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) (by norm_num) ha
    rw [h16] at this
    linarith
  refine ⟨hpos _ (by linarith), hpos _ (by linarith), key _ _ (by linarith) (by linarith)
    (by linarith), key _ _ (by linarith) (by linarith) (by linarith)⟩

/-- Supplement S8-A, corrected conversion: with bad-event mass `β ≤ 2γ`,
`η = m(a + γ)` and `m ≥ 1`, `M(1 - β)η + Mβ/2 ≤ Mη + Mγ ≤ 2Mm(a + γ) = ε_LRS`. -/
theorem df_conversion (M β γ a m : ℝ) (hM : 0 ≤ M) (hβ0 : 0 ≤ β) (hβ : β ≤ 2 * γ)
    (ha : 0 ≤ a) (hγ : 0 ≤ γ) (hm : 1 ≤ m) :
    M * (1 - β) * (m * (a + γ)) + M * β / 2 ≤ M * (m * (a + γ)) + M * γ ∧
    M * (m * (a + γ)) + M * γ ≤ 2 * M * m * (a + γ) := by
  have hη : 0 ≤ m * (a + γ) := by nlinarith
  constructor
  · nlinarith [mul_nonneg hM hβ0, mul_nonneg (mul_nonneg hM hβ0) hη]
  · have hm1 : 0 ≤ m - 1 := by linarith
    nlinarith [mul_nonneg hM ha, mul_nonneg hM hγ, mul_nonneg (mul_nonneg hM ha) hm1,
      mul_nonneg (mul_nonneg hM hγ) hm1]

end DF

end Clria.Repairs
