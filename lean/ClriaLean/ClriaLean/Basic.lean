import Mathlib

/-!
# CLR-IA: authentication algebra and the two-representation step

Main paper, Sections II, IV–VII. The group of prime order `q` is written
additively as a `K`-module `G`, so `g₁^{x₁} g₂^{x₂}` becomes `x₁ • g₁ + x₂ • g₂`.
A cyclic group of prime order `q` with `K = ZMod q` is the one-dimensional case;
every statement below holds for an arbitrary `K`-module.

Index convention: `X 0, X 1` are the paper's `x₁, x₂`.
-/

namespace Clria

variable {K : Type*} [Field K] {G : Type*} [AddCommGroup G] [Module K G]

/-- `g^X = g₁^{x₁} g₂^{x₂}` (main paper, Section II), written additively. -/
def gpow (g₁ g₂ : G) (X : Fin 2 → K) : G := X 0 • g₁ + X 1 • g₂

/-- The pair `X = AB` as a vector, for `A ∈ K^{1×n}` and `B ∈ K^{n×2}`. -/
def row {n : ℕ} (A : Matrix (Fin 1) (Fin n) K) (B : Matrix (Fin n) (Fin 2) K) : Fin 2 → K :=
  (A * B) 0

/-- Supplement S2-A: the prover's `j`-th response uses `Σ_l A_l B_{l,j}`. -/
theorem row_apply {n : ℕ} (A : Matrix (Fin 1) (Fin n) K) (B : Matrix (Fin n) (Fin 2) K)
    (j : Fin 2) : row A B j = ∑ l, A 0 l * B l j := by
  simp [row, Matrix.mul_apply]

/-- Main paper, eq. (6): responses `v = r + cX` computed from `X` alone satisfy
`g^v = U · pk^c` with `U = g^r` and `pk = g^X`, for every nonce `r` and challenge `c`.
Hence `X` is a `1`-capability for both published games. -/
theorem capability_accepts (g₁ g₂ : G) (X r : Fin 2 → K) (c : K) :
    gpow g₁ g₂ (r + c • X) = gpow g₁ g₂ r + c • gpow g₁ g₂ X := by
  simp only [gpow, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, mul_smul, smul_add]
  abel

/-- Main paper, eq. (3): the honest prover with key `(A, B)` answers `v = r + c·AB`,
which passes verification against `pk = g^{AB}`. -/
theorem honest_accepts (g₁ g₂ : G) {n : ℕ} (A : Matrix (Fin 1) (Fin n) K)
    (B : Matrix (Fin n) (Fin 2) K) (r : Fin 2 → K) (c : K) :
    gpow g₁ g₂ (r + c • row A B) = gpow g₁ g₂ r + c • gpow g₁ g₂ (row A B) :=
  capability_accepts g₁ g₂ (row A B) r c

/-- Main paper, eq. (2): two different representations of one public key give
`θ = log_{g₁} g₂ = -(x₁' - x₁)/(x₂' - x₂)`, and `x₂ ≠ x₂'`. -/
theorem theta_of_two_reps (g₁ g₂ : G) (hg₁ : g₁ ≠ 0) {X X' : Fin 2 → K} (hne : X ≠ X')
    (h : gpow g₁ g₂ X = gpow g₁ g₂ X') :
    X 1 ≠ X' 1 ∧ g₂ = (-(X' 0 - X 0) / (X' 1 - X 1)) • g₁ := by
  have key : (X 1 - X' 1) • g₂ = (X' 0 - X 0) • g₁ := by
    simp only [gpow] at h
    rw [sub_smul, sub_smul, sub_eq_sub_iff_add_eq_add, add_comm, h]
  have h1 : X 1 ≠ X' 1 := by
    intro h11
    rw [h11, sub_self, zero_smul] at key
    have h0 : X' 0 - X 0 = 0 := by
      rcases smul_eq_zero.mp key.symm with h0 | h0
      · exact h0
      · exact absurd h0 hg₁
    apply hne
    funext i
    fin_cases i
    · exact (sub_eq_zero.mp h0).symm
    · exact h11
  refine ⟨h1, ?_⟩
  have hd : X 1 - X' 1 ≠ 0 := sub_ne_zero.mpr h1
  have hd' : X' 1 - X 1 ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  calc g₂ = (X 1 - X' 1)⁻¹ • ((X 1 - X' 1) • g₂) := (inv_smul_smul₀ hd g₂).symm
    _ = (X 1 - X' 1)⁻¹ • ((X' 0 - X 0) • g₁) := by rw [key]
    _ = (-(X' 0 - X 0) / (X' 1 - X 1)) • g₁ := by
      rw [smul_smul]
      congr 1
      rw [show X' 1 - X 1 = -(X 1 - X' 1) by ring, div_neg, neg_div, neg_neg, div_eq_inv_mul]

/-- Main paper, eq. (12) and Section VI-A: rewinding with a fixed nonce `r` on two
distinct challenges extracts `(v - v')/(c - c') = X`, so the extracted key always
equals the attacker's `X` (the source's event `E₂`). -/
theorem rewind_extracts_X (X r : Fin 2 → K) {c c' : K} (hc : c ≠ c') :
    (c - c')⁻¹ • ((r + c • X) - (r + c' • X)) = X := by
  have h : (r + c • X) - (r + c' • X) = (c - c') • X := by
    rw [sub_smul]
    abel
  rw [h, inv_smul_smul₀ (sub_ne_zero.mpr hc)]

/-- Main paper, Remark 14: if `g₂ = g₁^θ`, then `t = x₁ + θ x₂` gives the witness
`(t, 0)` of the same public key. -/
theorem trapdoor_witness (g₁ : G) (θ : K) (X : Fin 2 → K) :
    gpow g₁ (θ • g₁) ![X 0 + θ * X 1, 0] = gpow g₁ (θ • g₁) X := by
  simp only [gpow, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [zero_smul, add_zero, add_smul, smul_smul, mul_comm θ]

end Clria
