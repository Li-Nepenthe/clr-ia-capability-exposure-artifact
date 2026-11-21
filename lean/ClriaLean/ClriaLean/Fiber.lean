import Mathlib

/-!
# Fiber counts and the resampler

Main paper, Section VI-A and Lemma 2; Supplement S4-A and S4-B. `K` is a finite field
with `q = |K|`. Uniform distributions are stated as counts of finite sets.
-/

namespace Clria.Fiber

open Module

variable {K : Type*} [Field K] {n : ℕ}

/-- The functional `b ↦ a ⬝ b`. -/
def dotL (a : Fin n → K) : (Fin n → K) →ₗ[K] K where
  toFun b := a ⬝ᵥ b
  map_add' x y := dotProduct_add a x y
  map_smul' c x := by simp [dotProduct_smul]

lemma dotL_apply (a b : Fin n → K) : dotL a b = a ⬝ᵥ b := rfl

lemma dotL_surjective {a : Fin n → K} (ha : a ≠ 0) : Function.Surjective (dotL a) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  have hi' : a i ≠ 0 := by simpa using hi
  intro x
  refine ⟨Pi.single i (x / a i), ?_⟩
  rw [dotL_apply, dotProduct_single]
  field_simp

lemma finrank_ker_dotL {a : Fin n → K} (ha : a ≠ 0) :
    finrank K (LinearMap.ker (dotL a)) = n - 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker (dotL a)
  rw [LinearMap.range_eq_top.mpr (dotL_surjective ha), finrank_top, Module.finrank_self,
    Module.finrank_fin_fun] at h
  omega

/-- For `a ≠ 0`, each value of `b ↦ a ⬝ b` is taken by exactly `q^{n-1}` vectors. -/
theorem card_dot_fiber [Fintype K] {a : Fin n → K} (ha : a ≠ 0) (x : K) :
    Nat.card {b : Fin n → K // a ⬝ᵥ b = x} = Fintype.card K ^ (n - 1) := by
  obtain ⟨b₀, hb₀⟩ := dotL_surjective ha x
  rw [dotL_apply] at hb₀
  let e : {b : Fin n → K // a ⬝ᵥ b = x} ≃ LinearMap.ker (dotL a) :=
    { toFun := fun b => ⟨b.1 - b₀, by simp [LinearMap.mem_ker, dotL_apply, dotProduct_sub,
        b.2, hb₀]⟩
      invFun := fun k => ⟨k.1 + b₀, by
        have hk := k.2
        rw [LinearMap.mem_ker, dotL_apply] at hk
        rw [dotProduct_add, hk, hb₀, zero_add]⟩
      left_inv := fun b => by ext; simp
      right_inv := fun k => by ext; simp }
  rw [Nat.card_congr e, Module.natCard_eq_pow_finrank (K := K), finrank_ker_dotL ha,
    Nat.card_eq_fintype_card]

/-- Supplement S4-A: for a fixed nonzero `A ∈ K^{1×n}` and any `X ∈ K^{1×2}`,
exactly `q^{2n-2}` matrices `B` satisfy `AB = X`. -/
theorem card_fiber_fixed_A [Fintype K] {A : Matrix (Fin 1) (Fin n) K} (hA : A ≠ 0)
    (X : Matrix (Fin 1) (Fin 2) K) :
    Nat.card {B : Matrix (Fin n) (Fin 2) K // A * B = X} =
      Fintype.card K ^ (2 * (n - 1)) := by
  have hA0 : A 0 ≠ 0 := by
    intro h
    apply hA
    ext i j
    fin_cases i
    simp [h]
  have hcond : ∀ B : Matrix (Fin n) (Fin 2) K,
      A * B = X ↔ ∀ k, A 0 ⬝ᵥ (fun j => B.transpose k j) = X 0 k := by
    intro B
    constructor
    · intro h k
      have := congrFun (congrFun h 0) k
      simpa [Matrix.mul_apply, dotProduct] using this
    · intro h
      ext i k
      fin_cases i
      simpa [Matrix.mul_apply, dotProduct] using h k
  let e : {B : Matrix (Fin n) (Fin 2) K // A * B = X} ≃
      ((k : Fin 2) → {b : Fin n → K // A 0 ⬝ᵥ b = X 0 k}) :=
    (Equiv.subtypeEquiv (Matrix.transposeAddEquiv (Fin n) (Fin 2) K).toEquiv
      (fun B => by rw [hcond]; rfl)).trans Equiv.subtypePiEquivPi
  rw [Nat.card_congr e, Nat.card_pi]
  simp only [card_dot_fiber hA0, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

lemma card_ne_zero_mat [Fintype K] :
    Nat.card {A : Matrix (Fin 1) (Fin n) K // A ≠ 0} = Fintype.card K ^ n - 1 := by
  classical
  have h := Nat.card_congr (Equiv.optionSubtypeNe (0 : Matrix (Fin 1) (Fin n) K))
  rw [Finite.card_option, Matrix.card_matrix, Nat.card_eq_fintype_card (α := K),
    Nat.card_eq_fintype_card (α := Fin n), Nat.card_eq_fintype_card (α := Fin 1),
    Fintype.card_fin, Fintype.card_fin, mul_one] at h
  omega

/-- Main paper, Section VI-A, and Supplement S4-A: each `X` has exactly
`F = (q^n - 1) q^{2n-2}` keys `(A, B)` with `A ≠ 0` and `AB = X`. -/
theorem card_key_fiber [Fintype K] (X : Matrix (Fin 1) (Fin 2) K) :
    Nat.card {p : Matrix (Fin 1) (Fin n) K × Matrix (Fin n) (Fin 2) K //
      p.1 ≠ 0 ∧ p.1 * p.2 = X} = (Fintype.card K ^ n - 1) * Fintype.card K ^ (2 * (n - 1)) := by
  classical
  let e : {p : Matrix (Fin 1) (Fin n) K × Matrix (Fin n) (Fin 2) K // p.1 ≠ 0 ∧ p.1 * p.2 = X} ≃
      (Σ A : {A : Matrix (Fin 1) (Fin n) K // A ≠ 0}, {B : Matrix (Fin n) (Fin 2) K //
        A.1 * B = X}) :=
    { toFun := fun p => ⟨⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩⟩
      invFun := fun s => ⟨(s.1.1, s.2.1), s.1.2, s.2.2⟩
      left_inv := fun p => rfl
      right_inv := fun s => rfl }
  rw [Nat.card_congr e, Nat.card_sigma]
  have : ∀ A : {A : Matrix (Fin 1) (Fin n) K // A ≠ 0},
      Nat.card {B : Matrix (Fin n) (Fin 2) K // A.1 * B = X} =
        Fintype.card K ^ (2 * (n - 1)) := fun A => card_fiber_fixed_A A.2 X
  simp only [this, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← Nat.card_eq_fintype_card, card_ne_zero_mat]

/-- Supplement S4-A: for fixed `θ` and `t`, the line `x₁ + θ x₂ = t` has exactly `q` points. -/
theorem card_line [Fintype K] (θ t : K) :
    Nat.card {X : Fin 2 → K // X 0 + θ * X 1 = t} = Fintype.card K := by
  let e : {X : Fin 2 → K // X 0 + θ * X 1 = t} ≃ K :=
    { toFun := fun X => X.1 1
      invFun := fun y => ⟨![t - θ * y, y], by simp⟩
      left_inv := fun X => by
        ext i
        fin_cases i
        · simp [← X.2]
        · simp
      right_inv := fun y => by simp }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]

/-- Supplement S4-A: given the public key, i.e. the line `x₁ + θ x₂ = t`, there are exactly
`q (q^n - 1) q^{2n-2}` keys, so the key is uniform on a set of that size. -/
theorem card_keys_given_pk [Fintype K] (θ t : K) :
    Nat.card {p : Matrix (Fin 1) (Fin n) K × Matrix (Fin n) (Fin 2) K //
      p.1 ≠ 0 ∧ (p.1 * p.2) 0 0 + θ * (p.1 * p.2) 0 1 = t} =
      Fintype.card K * ((Fintype.card K ^ n - 1) * Fintype.card K ^ (2 * (n - 1))) := by
  classical
  let e : {p : Matrix (Fin 1) (Fin n) K × Matrix (Fin n) (Fin 2) K //
      p.1 ≠ 0 ∧ (p.1 * p.2) 0 0 + θ * (p.1 * p.2) 0 1 = t} ≃
      (Σ X : {X : Fin 2 → K // X 0 + θ * X 1 = t},
        {p : Matrix (Fin 1) (Fin n) K × Matrix (Fin n) (Fin 2) K //
          p.1 ≠ 0 ∧ p.1 * p.2 = Matrix.of fun _ => X.1}) :=
    { toFun := fun p => ⟨⟨(p.1.1 * p.1.2) 0, p.2.2⟩, ⟨p.1, p.2.1, by
        ext i k
        fin_cases i
        rfl⟩⟩
      invFun := fun s => ⟨s.2.1, s.2.2.1, by
        have h := s.2.2.2
        have h0 := congrFun (congrFun h 0) 0
        have h1 := congrFun (congrFun h 0) 1
        simp only [Matrix.of_apply] at h0 h1
        rw [h0, h1]
        exact s.1.2⟩
      left_inv := fun p => rfl
      right_inv := fun s => by
        obtain ⟨⟨X, hX⟩, ⟨p, hp, hpX⟩⟩ := s
        apply Sigma.subtype_ext
        · apply Subtype.ext
          funext k
          simpa using congrFun (congrFun hpX 0) k
        · rfl }
  rw [Nat.card_congr e, Nat.card_sigma]
  simp only [card_key_fiber, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← Nat.card_eq_fintype_card, card_line]

/-- Supplement S4-A, the fiber charge: subtracting `log F` from the exact whole-key entropy
`log[(q^n - 1) q^{2n-1}]` leaves `log q`. -/
theorem fiber_charge (q : ℝ) (n : ℕ) (hq : 1 < q) (hn : 1 ≤ n) :
    Real.log ((q ^ n - 1) * q ^ (2 * n - 1)) - Real.log ((q ^ n - 1) * q ^ (2 * n - 2)) =
      Real.log q := by
  have hq0 : 0 < q := by linarith
  have hqn : 0 < q ^ n - 1 := by
    have : 1 < q ^ n := one_lt_pow₀ hq (by omega)
    linarith
  rw [← Real.log_div (by positivity) (by positivity)]
  congr 1
  have h : 2 * n - 1 = (2 * n - 2) + 1 := by omega
  rw [h, pow_succ]
  field_simp

/-- Supplement S4-A: charging `log F` to the printed `(3n - 1) log q` instead exceeds the
ceiling `log q` already at `λ = 0`. -/
theorem printed_charge_exceeds (q : ℝ) (n : ℕ) (hq : 1 < q) (hn : 1 ≤ n) :
    (3 * n - 1) * Real.log q - Real.log ((q ^ n - 1) * q ^ (2 * n - 2)) > Real.log q := by
  have hq0 : 0 < q := by linarith
  have hqn : 0 < q ^ n - 1 := by
    have : 1 < q ^ n := one_lt_pow₀ hq (by omega)
    linarith
  rw [Real.log_mul hqn.ne' (by positivity), Real.log_pow]
  have hlt : Real.log (q ^ n - 1) < n * Real.log q := by
    rw [← Real.log_pow]
    exact Real.log_lt_log hqn (by linarith)
  have hcast : ((2 * n - 2 : ℕ) : ℝ) = 2 * n - 2 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hcast]
  nlinarith [Real.log_pos hq]

/-! ## The resampler (Supplement S4-B) -/

section Resampler

variable {i : Fin n}

/-- `B_p(A, Y)`: row `i` equals `Y / A_i`, all other rows are zero. -/
def Bp (A : Matrix (Fin 1) (Fin n) K) (i : Fin n) (Y : Matrix (Fin 1) (Fin 2) K) :
    Matrix (Fin n) (Fin 2) K :=
  Matrix.of fun j k => if j = i then Y 0 k / A 0 i else 0

/-- Supplement S4-B: `A B_p(A, Y) = Y` when `A_i ≠ 0`. -/
theorem mul_Bp {A : Matrix (Fin 1) (Fin n) K} (hi : A 0 i ≠ 0) (Y : Matrix (Fin 1) (Fin 2) K) :
    A * Bp A i Y = Y := by
  ext r k
  fin_cases r
  simp [Bp, Matrix.mul_apply]
  field_simp

lemma Bp_sub (A : Matrix (Fin 1) (Fin n) K) (Y Y' : Matrix (Fin 1) (Fin 2) K) :
    Bp A i (Y - Y') = Bp A i Y - Bp A i Y' := by
  ext j k
  simp only [Bp, Matrix.of_apply, Matrix.sub_apply]
  split_ifs <;> ring

/-- Supplement S4-B: `B_p(A, ·)` is linear. -/
theorem Bp_add_smul (A : Matrix (Fin 1) (Fin n) K) (Y Y' : Matrix (Fin 1) (Fin 2) K) (c : K) :
    Bp A i (Y + Y') = Bp A i Y + Bp A i Y' ∧ Bp A i (c • Y) = c • Bp A i Y := by
  constructor
  · ext j k
    simp only [Bp, Matrix.of_apply, Matrix.add_apply]
    split_ifs <;> ring
  · ext j k
    simp only [Bp, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> ring

/-- `Res(X; A, B') = (A, B' + B_p(A, X - AB'))`. -/
def res (A : Matrix (Fin 1) (Fin n) K) (i : Fin n) (X : Matrix (Fin 1) (Fin 2) K)
    (B' : Matrix (Fin n) (Fin 2) K) : Matrix (Fin n) (Fin 2) K :=
  B' + Bp A i (X - A * B')

/-- Supplement S4-B: the resampler's output satisfies `A · Res = X`. -/
theorem res_correct {A : Matrix (Fin 1) (Fin n) K} (hi : A 0 i ≠ 0)
    (X : Matrix (Fin 1) (Fin 2) K) (B' : Matrix (Fin n) (Fin 2) K) :
    A * res A i X B' = X := by
  rw [res, Matrix.mul_add, mul_Bp hi]
  abel

/-- Supplement S4-B: for fixed `A` and `X`, every `B` with `AB = X` is the output of
exactly `q^2` inputs `B'`, so a uniform `B'` gives a uniform output on `{B : AB = X}`. -/
theorem res_uniform [Fintype K] {A : Matrix (Fin 1) (Fin n) K} (hi : A 0 i ≠ 0)
    (X : Matrix (Fin 1) (Fin 2) K) (B : Matrix (Fin n) (Fin 2) K) (hB : A * B = X) :
    Nat.card {B' : Matrix (Fin n) (Fin 2) K // res A i X B' = B} = Fintype.card K ^ 2 := by
  have key : ∀ Y, A * (B - Bp A i X + Bp A i Y) = Y := fun Y => by
    rw [Matrix.mul_add, Matrix.mul_sub, mul_Bp hi, mul_Bp hi, hB]
    abel
  let e : {B' : Matrix (Fin n) (Fin 2) K // res A i X B' = B} ≃ Matrix (Fin 1) (Fin 2) K :=
    { toFun := fun B' => A * B'.1
      invFun := fun Y => ⟨B - Bp A i X + Bp A i Y, by
        rw [res, key, Bp_sub]
        abel⟩
      left_inv := fun B' => by
        obtain ⟨B', hB'⟩ := B'
        apply Subtype.ext
        simp only
        rw [← hB', res, Bp_sub]
        abel
      right_inv := fun Y => key Y }
  rw [Nat.card_congr e, Matrix.card_matrix, Nat.card_eq_fintype_card (α := K)]
  simp

end Resampler

/-! ## Lemma 2: counting cores -/

/-- Main paper, Lemma 2(b), core: if a fiber of `φ` has at most `F` points and every point
has weight at most `M`, then the fiber has total weight at most `F M`. -/
theorem fiber_weight_le {S Z : Type*} [Fintype S] [DecidableEq Z] (φ : S → Z) (p : S → ℝ)
    (M : ℝ) (F : ℕ) (hM : ∀ s, p s ≤ M) (z : Z)
    (hF : (Finset.univ.filter fun s => φ s = z).card ≤ F) (hM0 : 0 ≤ M) :
    ∑ s ∈ Finset.univ.filter (fun s => φ s = z), p s ≤ F * M := by
  calc ∑ s ∈ Finset.univ.filter (fun s => φ s = z), p s
      ≤ ∑ _s ∈ Finset.univ.filter (fun s => φ s = z), M := Finset.sum_le_sum fun s _ => hM s
    _ = (Finset.univ.filter fun s => φ s = z).card * M := by simp
    _ ≤ F * M := by
      apply mul_le_mul_of_nonneg_right _ hM0
      exact_mod_cast hF

/-- Main paper, Lemma 2(a), core: if at most `N` values carry all the weight `1`, one of them
has weight at least `1/N`. -/
theorem exists_weight_ge {Z : Type*} (T : Finset Z) (p : Z → ℝ) (N : ℕ)
    (hT : T.card ≤ N) (hN : 0 < N) (hsum : ∑ z ∈ T, p z = 1) :
    ∃ z ∈ T, 1 / (N : ℝ) ≤ p z := by
  by_contra h
  simp only [not_exists, not_and, not_le] at h
  have hlt : ∑ z ∈ T, p z < ∑ _z ∈ T, 1 / (N : ℝ) := by
    apply Finset.sum_lt_sum_of_nonempty
    · rcases Finset.eq_empty_or_nonempty T with hT0 | hT0
      · simp [hT0] at hsum
      · exact hT0
    · exact h
  rw [hsum, Finset.sum_const, nsmul_eq_mul] at hlt
  have : (T.card : ℝ) * (1 / N) ≤ 1 := by
    rw [mul_one_div, div_le_one (by exact_mod_cast hN)]
    exact_mod_cast hT
  linarith

end Clria.Fiber
