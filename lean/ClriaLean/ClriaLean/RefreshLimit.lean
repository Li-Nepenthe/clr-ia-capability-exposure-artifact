import Mathlib

/-!
# Refresh limits: the invariant witness and the period-by-period splice

Main paper, Lemma 4, Proposition 12 and Corollary 13; Supplement S5-A. The group is
written additively as a `K`-module with generators `g : Fin m → G`, so
`∏ g_i^{w_i}` is `Σ w_i • g_i`.
-/

namespace Clria.RefreshLimit

variable {K : Type*} [Field K] {G : Type*} [AddCommGroup G] [Module K G] {m : ℕ}

/-- `∏ g_i^{w_i}`, written additively. -/
def rep (g : Fin m → G) (w : Fin m → K) : G := ∑ i, w i • g i

lemma rep_sub (g : Fin m → G) (w w' : Fin m → K) : rep g (w - w') = rep g w - rep g w' := by
  simp only [rep, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]

/-- Supplement S5-A: if an honest prover's responses satisfy the `m`-generator Okamoto
verification `∏ g_i^{Rsp_i(st, ρ, c)} = Com(st, ρ) · pk^c` for all coins and challenges,
then `W(st) = Rsp(st, ρ₀, 2) - Rsp(st, ρ₀, 1)` is a witness of the public key. -/
theorem witness_of_responses {St R : Type*} (g : Fin m → G) (pk : G) (Com : St → R → G)
    (Rsp : St → R → K → Fin m → K)
    (hcorr : ∀ st ρ c, rep g (Rsp st ρ c) = Com st ρ + c • pk) (st : St) (ρ₀ : R) :
    rep g (Rsp st ρ₀ 2 - Rsp st ρ₀ 1) = pk := by
  rw [rep_sub, hcorr, hcorr]
  rw [show (2 : K) = 1 + 1 by norm_num, add_smul, one_smul]
  abel

/-- Supplement S5-A and Proposition 12(a), core: two different witnesses of one public key
differ by a nontrivial representation of the identity, from which DL is solved. -/
theorem nontrivial_relation (g : Fin m → G) (pk : G) {w w' : Fin m → K} (hne : w ≠ w')
    (hw : rep g w = pk) (hw' : rep g w' = pk) :
    w - w' ≠ 0 ∧ rep g (w - w') = 0 := by
  refine ⟨sub_ne_zero.mpr hne, ?_⟩
  rw [rep_sub, hw, hw', sub_self]

/-- Supplement S5-A: for CLR-IA the prover answers `v = r + c X` with `X = AB`, so the
witness `W(st)` is exactly `X`. -/
theorem clria_witness_is_product (X r : Fin 2 → K) :
    (r + (2 : K) • X) - (r + (1 : K) • X) = X := by
  rw [show (2 : K) = 1 + 1 by norm_num, add_smul, one_smul]
  abel

/-! ## Lemma 4: leaking `enc(φ)` in pieces across periods -/

/-- The piece leaked in period `j`: bits `jb + 1` through `min((j + 1) b, ℓ)`. -/
def piece {α : Type*} (s : List α) (b j : ℕ) : List α := (s.drop (j * b)).take b

lemma flatMap_pieces {α : Type*} (b : ℕ) :
    ∀ (k : ℕ) (s : List α), s.length ≤ k * b →
      (List.range k).flatMap (piece s b) = s := by
  intro k
  induction k with
  | zero =>
    intro s hs
    simp only [zero_mul, Nat.le_zero, List.length_eq_zero_iff] at hs
    simp [hs]
  | succ k ih =>
    intro s hs
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    have hrest : (List.range k).flatMap (fun j => piece s b (j + 1)) =
        (List.range k).flatMap (piece (s.drop b) b) := by
      congr 1
      funext j
      simp only [piece, List.drop_drop]
      congr 2
      ring
    rw [hrest, ih (s.drop b) (by simp; rw [Nat.succ_mul] at hs; omega)]
    simp [piece]

/-- Main paper, Lemma 4: with `b ≥ 1` bits per period and `k = ⌈ℓ/b⌉` periods, the pieces
`bits jb + 1 … min((j + 1) b, ℓ)` for `j < k` concatenate to the whole encoding, and each
piece fits in one period's `b` bits. -/
theorem splice_chunks {α : Type*} (s : List α) (b : ℕ) (hb : 1 ≤ b) :
    (List.range ((s.length + b - 1) / b)).flatMap (piece s b) = s ∧
    ∀ j, (piece s b j).length ≤ b := by
  refine ⟨flatMap_pieces b _ s ?_, fun j => by simp [piece]⟩
  have h := Nat.lt_div_mul_add (a := s.length + b - 1) (b := b) (by omega)
  omega

/-- Corollary 13: with at least one bit per period, `⌈2w/b⌉ ≤ 2w` periods suffice. -/
theorem periods_bound (w b : ℕ) (hw : 1 ≤ w) (hb : 1 ≤ b) : (2 * w + b - 1) / b ≤ 2 * w := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  apply Nat.div_le_of_le_mul
  have : 2 * w + (b' + 1) - 1 = 2 * w + b' := by omega
  rw [this]
  nlinarith

/-- Proposition 12(b): for `b ≥ 2w` a single period suffices, which is the attack of
Proposition 5. -/
theorem one_period (w b : ℕ) (hw : 1 ≤ w) (hb : 2 * w ≤ b) : (2 * w + b - 1) / b = 1 := by
  apply le_antisymm
  · have h := (Nat.div_lt_iff_lt_mul (by omega : 0 < b)).mpr
      (by omega : 2 * w + b - 1 < 2 * b)
    omega
  · exact Nat.div_pos (by omega) (by omega)

end Clria.RefreshLimit
