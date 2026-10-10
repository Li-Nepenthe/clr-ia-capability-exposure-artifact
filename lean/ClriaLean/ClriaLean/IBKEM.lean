import Mathlib

/-!
# IB-KEM of Qiao et al.: the identity-independent capability

Main paper, Section VIII-A and Proposition 17; Supplement S7-A. The pairing groups
are written additively as `K`-modules `G` and `G_T`, and the pairing is a `K`-bilinear
map `e : G →ₗ[K] G →ₗ[K] G_T`; `E = e(g, g)`. A key of identity `i` is
`(d₁, d₂, d₃) = (α g + s hᵢ, β g + s hᵢ, -s g)`. An honest encapsulation has
`c₁ = r g`, `X = (αr) E`, `Y = (βr) E` and `V = μ X + Y`.
The statements hold for every `hᵢ` (including `0`) and every `α, β`.
-/

namespace Clria.IBKEM

variable {K : Type*} [Field K] {G GT : Type*} [AddCommGroup G] [Module K G]
  [AddCommGroup GT] [Module K GT]

/-- Main paper, eq. (16): any non-target key gives `R = d₁ - d₂ = (α - β) g`, which
does not depend on the identity; `D = e(R, c₁) = X - Y` and `V + D = (μ + 1) X`. -/
theorem capability (e : G →ₗ[K] G →ₗ[K] GT) (g h : G) (α β s r μ : K) :
    (α • g + s • h) - (β • g + s • h) = (α - β) • g ∧
    e ((α - β) • g) (r • g) = (α * r) • e g g - (β * r) • e g g ∧
    (μ • ((α * r) • e g g) + (β * r) • e g g) + e ((α - β) • g) (r • g) =
      (μ + 1) • ((α * r) • e g g) := by
  refine ⟨by module, ?_, ?_⟩
  · simp only [map_smul, LinearMap.smul_apply, smul_smul]
    rw [← sub_smul]
    ring_nf
  · simp only [map_smul, LinearMap.smul_apply, smul_smul]
    module

/-- Main paper, eq. (16): for `μ ≠ -1`, `X̂ = (μ + 1)⁻¹ (V + D) = X`, so the extracted
key `Ext(X̂, S)` equals the real key `Ext(X, S)` for every extractor and seed. -/
theorem recovers_key (e : G →ₗ[K] G →ₗ[K] GT) (g : G) (α β r μ : K) (hμ : μ ≠ -1)
    {Seed Key : Type*} (Ext : GT → Seed → Key) (S : Seed) :
    (μ + 1)⁻¹ • ((μ • ((α * r) • e g g) + (β * r) • e g g) + e ((α - β) • g) (r • g)) =
      (α * r) • e g g ∧
    Ext ((μ + 1)⁻¹ • ((μ • ((α * r) • e g g) + (β * r) • e g g) +
      e ((α - β) • g) (r • g))) S = Ext ((α * r) • e g g) S := by
  have hμ' : μ + 1 ≠ 0 := fun h => hμ (eq_neg_of_add_eq_zero_left h)
  have key := (capability e g g α β 0 r μ).2.2
  rw [key, inv_smul_smul₀ hμ']
  exact ⟨rfl, rfl⟩

/-- Main paper, Section VIII-A: for `μ = -1`, `V + D = 0`, so the recovery formula
gives nothing. -/
theorem mu_neg_one (e : G →ₗ[K] G →ₗ[K] GT) (g : G) (α β r : K) :
    ((-1 : K) • ((α * r) • e g g) + (β * r) • e g g) + e ((α - β) • g) (r • g) = 0 := by
  rw [(capability e g g α β 0 r (-1)).2.2]
  simp

/-- Main paper, Section VIII-A: the update multiplies `d₁` and `d₂` by the same
`hᵢ^{s'}`, so `R` is unchanged. -/
theorem update_keeps_R (d₁ d₂ h : G) (s' : K) :
    (d₁ + s' • h) - (d₂ + s' • h) = d₁ - d₂ := by
  abel

/-- Supplement S7-A, "Where the proof fails": in the hybrid with DBDH exponents
`α = ab + α̂`, `β = ab + β̂` and challenge value `V* = (1 + μ*) T + (α̂ μ* + β̂) e(c₁*, g)`,
every non-target key gives `e(R, c₁*) + V* = (1 + μ*)(T + α̂ e(c₁*, g))` for every
`T ∈ G_T`, uniform or not. For `μ* ≠ -1`, the extractor input `T + α̂ e(c₁*, g)` of the
challenge key is therefore determined by `R`, `c₁*` and `V*`. -/
theorem hybrid_identity (e : G →ₗ[K] G →ₗ[K] GT) (he : ∀ x y, e x y = e y x)
    (g c : G) (a b α' β' μ : K) (T : GT) :
    e (((a * b + α') - (a * b + β')) • g) c + ((1 + μ) • T + (α' * μ + β') • e c g) =
      (1 + μ) • (T + α' • e c g) ∧
    (μ ≠ -1 →
      (1 + μ)⁻¹ • (e (((a * b + α') - (a * b + β')) • g) c +
        ((1 + μ) • T + (α' * μ + β') • e c g)) = T + α' • e c g) := by
  have h1 : e (((a * b + α') - (a * b + β')) • g) c + ((1 + μ) • T + (α' * μ + β') • e c g) =
      (1 + μ) • (T + α' • e c g) := by
    simp only [map_smul, LinearMap.smul_apply, he g c]
    module
  refine ⟨h1, fun hμ => ?_⟩
  have hμ' : (1 : K) + μ ≠ 0 := by
    intro h
    exact hμ (eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact h))
  rw [h1, inv_smul_smul₀ hμ']

end Clria.IBKEM
