import Mathlib

/-!
# IBE of Zhou et al. and IBE of Zhou and Yang

Main paper, Sections VIII-B and VIII-C, Proposition 18; Supplement S7-B, S7-D and S8-C.
Groups are `K`-modules and the symmetric pairing is a `K`-bilinear map
`e : G →ₗ[K] G →ₗ[K] G_T` with `e x y = e y x`.

Zhou et al. (vector reading): `g₁ = α g`, `g₂ = β g`, `g_{3,j} = ρ_j g`,
`𝐤_pub = γ ρ`. A key for `id` has `d₁ = α (d - g₃^𝐭) + r F`, `d₂ = β (d - g₃^𝐭) + r F`,
`d₃ = -r g`, `d₄ = 𝐭`, with `a_B = ⟨𝐤_pub, 𝐭⟩`. An honest ciphertext has
`c₁ = s g`, `c₂ = s F`, `c_{3,j} = s e(g₁, g_{3,j})`, `X = s e(d, g₁)`,
`Y = s e(d, g₂)`, `c₅ = X + η Y + M` and `c₆ = μ X + Y`. The statements hold for
all `μ, η`, and also when `d = 0`, `F = 0` or `α = β`.
-/

namespace Clria.IBE

variable {K : Type*} [Field K] {G GT : Type*} [AddCommGroup G] [Module K G]
  [AddCommGroup GT] [Module K GT] {n : ℕ}

/-- `g₃^𝐭 = ∏_j g_{3,j}^{t_j}` with `g_{3,j} = ρ_j g`. -/
def g3pow (g : G) (ρ t : Fin n → K) : G := ∑ i, t i • (ρ i • g)

/-- `a_B = ⟨𝐤_pub, 𝐭⟩` with `𝐤_pub = γ ρ`. -/
def aB (γ : K) (ρ t : Fin n → K) : K := ∑ i, (γ * ρ i) * t i

lemma g3pow_eq (g : G) (ρ t : Fin n → K) : g3pow g ρ t = (∑ i, t i * ρ i) • g := by
  simp only [g3pow, smul_smul, Finset.sum_smul]

lemma aB_eq (γ : K) (ρ t : Fin n → K) : aB γ ρ t = γ * ∑ i, t i * ρ i := by
  simp only [aB, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Supplement S7-B, public normalization: for a public `j` with `k_{pub,j} ≠ 0`,
`W = g_{3,j}^{1/k_{pub,j}} = g^{1/γ}`, `g₃^𝐭 = W^{a_B}` and
`∏_k c_{3,k}^{t_k} = E₁^{a_B}` with `E₁ = c_{3,j}^{1/k_{pub,j}}`. The secret exponents
justify these identities; the algorithm uses only public values. -/
theorem normalization (e : G →ₗ[K] G →ₗ[K] GT) (g g₁ : G) (γ s : K) (ρ t : Fin n → K)
    (j : Fin n) (hk : γ * ρ j ≠ 0) :
    (γ * ρ j)⁻¹ • (ρ j • g) = γ⁻¹ • g ∧
    g3pow g ρ t = aB γ ρ t • ((γ * ρ j)⁻¹ • (ρ j • g)) ∧
    (∑ i, t i • (s • e g₁ (ρ i • g))) = aB γ ρ t • ((γ * ρ j)⁻¹ • (s • e g₁ (ρ j • g))) := by
  have hγ : γ ≠ 0 := left_ne_zero_of_mul hk
  have hρ : ρ j ≠ 0 := right_ne_zero_of_mul hk
  have hW : (γ * ρ j)⁻¹ • (ρ j • g) = γ⁻¹ • g := by
    rw [smul_smul]
    congr 1
    field_simp
  refine ⟨hW, ?_, ?_⟩
  · rw [hW, g3pow_eq, aB_eq, smul_smul]
    congr 1
    field_simp
  · have hE : (γ * ρ j)⁻¹ • (s • e g₁ (ρ j • g)) = (s * γ⁻¹) • e g₁ g := by
      rw [map_smul, smul_smul, smul_smul]
      congr 1
      field_simp
    rw [hE, aB_eq, smul_smul]
    simp only [map_smul, smul_smul]
    rw [← Finset.sum_smul]
    congr 1
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by field_simp

/-- Main paper, eq. (17) and Proposition 18: the leaked `C_all = (d₁, d₃, a_B)` and
public values give `X = e(c₁, d₁) e(c₂, d₃) E₁^{a_B}`, then `Y = c₆ X^{-μ}` and
`M = c₅/(X Y^η)`, written additively. -/
theorem recovery (e : G →ₗ[K] G →ₗ[K] GT) (he : ∀ x y, e x y = e y x)
    (g d F : G) (α β γ r s μ η : K) (ρ t : Fin n → K) (M : GT) (j : Fin n)
    (hk : γ * ρ j ≠ 0) :
    let X := s • e d (α • g)
    let Y := s • e d (β • g)
    let Xhat := e (s • g) (α • (d - g3pow g ρ t) + r • F) + e (s • F) (-(r • g)) +
      aB γ ρ t • ((γ * ρ j)⁻¹ • (s • e (α • g) (ρ j • g)))
    Xhat = X ∧ (μ • X + Y) - μ • Xhat = Y ∧
      (X + η • Y + M) - (Xhat + η • ((μ • X + Y) - μ • Xhat)) = M := by
  intro X Y Xhat
  have hX : Xhat = X := by
    simp only [Xhat, X]
    rw [← (normalization e g (α • g) γ s ρ t j hk).2.2, g3pow_eq]
    simp only [map_add, map_sub, map_neg, map_smul, LinearMap.smul_apply, he g d, he F g,
      smul_smul]
    have hs : ∑ i, t i * (s * (ρ i * α)) = (∑ i, t i * ρ i) * (s * α) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [← Finset.sum_smul, hs]
    module
  refine ⟨hX, ?_, ?_⟩
  · rw [hX]; module
  · rw [hX]; module

/-- Supplement S7-D, persistence. On a successful update with `r'` and
`⟨𝐤_pub, 𝐭'⟩ = 0`, the printed rules `d₁ ↦ d₁ + r' F`, `d₂ ↦ d₂ + r' F`,
`d₃ ↦ d₃ - r' g`, `𝐭 ↦ 𝐭 + 𝐭'` keep `R = d₁ - d₂`, `a_B`, `g₃^𝐭` and
`e(d₁, g) e(d₃, F)`, while `d₃` changes when `r' ≠ 0`. The kept value equals
`e(d / W^{a_B}, g₁)`, so the old `C_all` still recovers later honest challenges. -/
theorem update_persistence (e : G →ₗ[K] G →ₗ[K] GT) (he : ∀ x y, e x y = e y x)
    (g d F : G) (α β γ r r' : K) (ρ t t' : Fin n → K) (j : Fin n) (hk : γ * ρ j ≠ 0)
    (ht' : aB γ ρ t' = 0) :
    let d₁ := α • (d - g3pow g ρ t) + r • F
    let d₂ := β • (d - g3pow g ρ t) + r • F
    let d₃ := -(r • g)
    (d₁ + r' • F) - (d₂ + r' • F) = d₁ - d₂ ∧
    aB γ ρ (t + t') = aB γ ρ t ∧
    g3pow g ρ (t + t') = g3pow g ρ t ∧
    e (d₁ + r' • F) g + e (d₃ - r' • g) F = e d₁ g + e d₃ F ∧
    e d₁ g + e d₃ F = e (d - aB γ ρ t • ((γ * ρ j)⁻¹ • (ρ j • g))) (α • g) ∧
    (r' ≠ 0 → g ≠ 0 → d₃ - r' • g ≠ d₃) := by
  intro d₁ d₂ d₃
  have hγ : γ ≠ 0 := left_ne_zero_of_mul hk
  have hsum : ∑ i, t' i * ρ i = 0 := by
    rw [aB_eq] at ht'
    exact (mul_eq_zero.mp ht').resolve_left hγ
  refine ⟨by abel, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [aB, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    rw [show ∑ i, γ * ρ i * t' i = aB γ ρ t' from rfl, ht', add_zero]
  · simp only [g3pow_eq, Pi.add_apply, add_mul, Finset.sum_add_distrib, hsum, add_zero]
  · simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, he g F]
    abel
  · rw [← (normalization e g g γ 1 ρ t j hk).2.1]
    simp only [d₁, d₃, map_add, map_neg, map_smul, LinearMap.add_apply, LinearMap.neg_apply,
      LinearMap.smul_apply, he g F]
    module
  · intro hr hg h
    have : r' • g = 0 := by
      have h' := congrArg (fun z => d₃ - z) h
      simpa using h'
    rcases smul_eq_zero.mp this with h0 | h0
    · exact hr h0
    · exact hg h0

/-- Main paper, Section VIII-C, and Supplement S8-C (Zhou and Yang): decryption computes
`ω_j = e(c₁, sk_j) c₂^{t_j}`; for `c₁ = 1_G` and `c₂ = h` this is `h^{t_j}`, so the tag
`c₄ = h^{z}` with the leaked `z = μ t₁ + t₂` satisfies `c₄ = ω₁^μ ω₂` and is accepted. -/
theorem zhouyang_invalid_accept (e : G →ₗ[K] G →ₗ[K] GT) (sk₁ sk₂ : G) (t₁ t₂ μ : K)
    (h : GT) :
    (μ * t₁ + t₂) • h = μ • (e 0 sk₁ + t₁ • h) + (e 0 sk₂ + t₂ • h) := by
  simp only [map_zero, LinearMap.zero_apply, zero_add]
  module

/-- Supplement S8-A: the header `(c₁, c₂) = (1_G, e(g, g))` is invalid. Honest headers are
`c₁ = (g₁ g^{-id})^r = r (α - id) g` and `c₂ = e(g, g)^r`; for `id ≠ α`, `g ≠ 0` and
`e(g, g) ≠ 0`, no `r` gives `c₁ = 0` and `c₂ = e(g, g)`. -/
theorem zhouyang_header_invalid (e : G →ₗ[K] G →ₗ[K] GT) (g : G) (α id r : K)
    (hα : α ≠ id) (hg : g ≠ 0) (hgg : e g g ≠ 0) (hc₁ : r • ((α - id) • g) = 0) :
    r • e g g ≠ e g g := by
  rw [smul_smul] at hc₁
  rcases smul_eq_zero.mp hc₁ with h0 | h0
  · have hr : r = 0 := (mul_eq_zero.mp h0).resolve_right (sub_ne_zero.mpr hα)
    rw [hr, zero_smul]
    exact fun h => hgg h.symm
  · exact absurd h0 hg

end Clria.IBE
