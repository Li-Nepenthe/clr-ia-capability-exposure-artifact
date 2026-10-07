import Mathlib

/-!
# CLR-IA: the printed key update

Main paper, Section IV and Lemma 7; Supplement S2-A. A key is
`A : K^{1×n}` (nonzero) and `B : K^{n×2}`; the update has two stages:

* first stage: `E ≠ 0`, `E F = 0`, nonsingular `T` with `A T = E`, and `B' = B + T F`;
* second stage: `Ẽ ≠ 0`, `Ẽ F̃ = 0`, nonsingular `T̃` with `T̃ B' = F̃`, and `A' = A + Ẽ T̃`;
* the output differs from the input.

`IsUpdate A B A' B'` states that `(A', B')` is an output of one execution that does
not abort. Nonsingularity and `E, Ẽ ≠ 0` are recorded for fidelity; the algebraic
statements below do not need them.
-/

namespace Clria

variable {K : Type*} [Field K] {n : ℕ}

/-- One non-aborting execution of the printed update (Supplement S2-A). -/
def IsUpdate (A : Matrix (Fin 1) (Fin n) K) (B : Matrix (Fin n) (Fin 2) K)
    (A' : Matrix (Fin 1) (Fin n) K) (B' : Matrix (Fin n) (Fin 2) K) : Prop :=
  ∃ (E Et : Matrix (Fin 1) (Fin n) K) (F Ft : Matrix (Fin n) (Fin 2) K)
    (T Tt : Matrix (Fin n) (Fin n) K),
    E ≠ 0 ∧ E * F = 0 ∧ IsUnit T.det ∧ A * T = E ∧ B' = B + T * F ∧
    Et ≠ 0 ∧ Et * Ft = 0 ∧ IsUnit Tt.det ∧ Tt * B' = Ft ∧ A' = A + Et * Tt ∧
    (A', B') ≠ (A, B)

/-- Main paper, Lemma 7 and eq. (10): `A (B + T F) = A B` whenever `A T = E` and
`E F = 0`. -/
theorem bridge (A E : Matrix (Fin 1) (Fin n) K) (B F : Matrix (Fin n) (Fin 2) K)
    (T : Matrix (Fin n) (Fin n) K) (hT : A * T = E) (hEF : E * F = 0) :
    A * (B + T * F) = A * B := by
  rw [Matrix.mul_add, ← Matrix.mul_assoc, hT, hEF, add_zero]

/-- Main paper, eq. (4): both stages together keep the product, `A' B' = A B`. -/
theorem stages_preserve_product (A E Et : Matrix (Fin 1) (Fin n) K)
    (B F Ft : Matrix (Fin n) (Fin 2) K) (T Tt : Matrix (Fin n) (Fin n) K)
    (hT : A * T = E) (hEF : E * F = 0) (hTt : Tt * (B + T * F) = Ft)
    (hEFt : Et * Ft = 0) :
    (A + Et * Tt) * (B + T * F) = A * B := by
  rw [Matrix.add_mul, bridge A E B F T hT hEF, Matrix.mul_assoc, hTt, hEFt, add_zero]

/-- Lemma 7 for an execution: the old first factor with the new second factor. -/
theorem IsUpdate.bridge {A A' : Matrix (Fin 1) (Fin n) K} {B B' : Matrix (Fin n) (Fin 2) K}
    (h : IsUpdate A B A' B') : A * B' = A * B := by
  obtain ⟨E, _, F, _, T, _, _, hEF, _, hT, hB', -⟩ := h
  rw [hB']
  exact Clria.bridge A E B F T hT hEF

/-- Eq. (4) for an execution: `A' B' = A B`. -/
theorem IsUpdate.product {A A' : Matrix (Fin 1) (Fin n) K} {B B' : Matrix (Fin n) (Fin 2) K}
    (h : IsUpdate A B A' B') : A' * B' = A * B := by
  obtain ⟨E, Et, F, Ft, T, Tt, _, hEF, _, hT, hB', _, hEFt, _, hTt, hA', -⟩ := h
  subst hA' hB'
  exact stages_preserve_product A E Et B F Ft T Tt hT hEF hTt hEFt

/-- The product is unchanged along any sequence of executions (main paper, Section VII:
the printed update keeps `AB` on every execution that returns a key). -/
theorem update_chain_product (As : ℕ → Matrix (Fin 1) (Fin n) K)
    (Bs : ℕ → Matrix (Fin n) (Fin 2) K)
    (h : ∀ i, IsUpdate (As i) (Bs i) (As (i + 1)) (Bs (i + 1))) :
    ∀ i, As i * Bs i = As 0 * Bs 0 := by
  intro i
  induction i with
  | zero => rfl
  | succ k ih => rw [(h k).product, ih]

/-- Main paper, eq. (10) along a sequence: `A_i B_{i+1} = A_i B_i = X` for every round,
which is what the cross-refresh acquisition (Proposition 8) uses. -/
theorem update_chain_bridge (As : ℕ → Matrix (Fin 1) (Fin n) K)
    (Bs : ℕ → Matrix (Fin n) (Fin 2) K)
    (h : ∀ i, IsUpdate (As i) (Bs i) (As (i + 1)) (Bs (i + 1))) (i : ℕ) :
    As i * Bs (i + 1) = As 0 * Bs 0 := by
  rw [(h i).bridge, update_chain_product As Bs h i]

/-- Main paper, after Lemma 7: the bridge works in one direction only. For every
dimension `n ≥ 2` (in particular `n = 16`) and every field, some execution of the
printed update has `A' B ≠ A B`, i.e. the new first factor with the old second factor
does not return `X`.

Witness: `A = E = e₀`, `T = T̃ = 1`, `F` with a single `1` at `(1, 0)`, `B = -F`,
so `B' = 0`, `F̃ = 0`, and `Ẽ = e₁`. -/
theorem bridge_one_direction (hn : 2 ≤ n) :
    ∃ (A A' : Matrix (Fin 1) (Fin n) K) (B B' : Matrix (Fin n) (Fin 2) K),
      IsUpdate A B A' B' ∧ A' * B ≠ A * B := by
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  have h10 : i1 ≠ i0 := by simp [i0, i1, Fin.ext_iff]
  let A : Matrix (Fin 1) (Fin n) K := Matrix.of fun _ j => if j = i0 then 1 else 0
  let Et : Matrix (Fin 1) (Fin n) K := Matrix.of fun _ j => if j = i1 then 1 else 0
  let F : Matrix (Fin n) (Fin 2) K := Matrix.of fun i k => if i = i1 ∧ k = 0 then 1 else 0
  have hAF : A * F = 0 := by
    ext a k
    simp only [A, F, Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
    apply Finset.sum_eq_zero
    intro j _
    split_ifs with h h' <;> first | exact absurd (h'.1.symm.trans h) h10 | rfl | simp
  have hEtF : (Et * F) 0 0 = 1 := by
    simp [Et, F, Matrix.mul_apply]
  have hA0 : A ≠ 0 := fun h => by simpa [A] using congrArg (fun M => M 0 i0) h
  have hEt0 : Et ≠ 0 := fun h => by simpa [Et] using congrArg (fun M => M 0 i1) h
  refine ⟨A, A + Et * 1, -F, -F + 1 * F,
    ⟨A, Et, F, 0, 1, 1, hA0, hAF, by simp, by simp, rfl, hEt0, by simp, by simp,
      by simp, rfl, ?_⟩, ?_⟩
  · intro h
    have hA := congrArg Prod.fst h
    simp only [Matrix.mul_one, add_eq_left] at hA
    exact hEt0 hA
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    simp only [Matrix.mul_one, Matrix.add_mul, Matrix.mul_neg, hAF, neg_zero, zero_add,
      Matrix.neg_apply, Matrix.zero_apply, neg_eq_zero] at h00
    rw [hEtF] at h00
    exact one_ne_zero h00

end Clria
