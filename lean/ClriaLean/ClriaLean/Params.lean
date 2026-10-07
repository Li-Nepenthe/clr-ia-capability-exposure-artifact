import Mathlib

/-!
# Budget arithmetic and concrete values

Main paper, Sections V–VI and Corollary 11; Supplement S3-C (Table S2), S4-E,
S6-A, S6-C and S7-C. Throughout, `a = log q`, `w = ⌈log q⌉ = a + δ` with
`0 ≤ δ < 1`, and `ι ∈ {0, 1}` covers the strict and non-strict conventions.
Margins are stated before subtracting the slack, as in Table S2.
-/

namespace Clria.Params

/-! ## Costs and margins (main paper, eqs. (9), (11); Table S2) -/

/-- Main paper, eq. (9): `L_split = (nw + 1) + (2w + 1) = (n + 2)w + 2`. -/
theorem L_split (n w : ℕ) : (n * w + 1) + (2 * w + 1) = (n + 2) * w + 2 := by ring

/-- Full margin `(3n - 2)a - L - ι` of Table S2. -/
noncomputable def full (n a L ι : ℝ) : ℝ := (3 * n - 2) * a - L - ι

/-- Half margin `(3n - 2)a/2 - L - ι` of Table S2. -/
noncomputable def half (n a L ι : ℝ) : ℝ := (3 * n - 2) * a / 2 - L - ι

section Table
variable (n a δ ι : ℝ)

/-- Table S2, joint query, cost `2w`. -/
theorem joint_margins :
    full n a (2 * (a + δ)) ι = (3 * n - 4) * a - 2 * δ - ι ∧
    half n a (2 * (a + δ)) ι = (3 * n - 6) * a / 2 - 2 * δ - ι := by
  constructor
  · unfold full; ring
  · unfold half; ring

/-- Table S2, split queries on one key, cost `(n + 2)w + 2`. -/
theorem split_margins :
    full n a ((n + 2) * (a + δ) + 2) ι = (2 * n - 4) * a - (n + 2) * δ - 2 - ι ∧
    half n a ((n + 2) * (a + δ) + 2) ι = (n / 2 - 3) * a - (n + 2) * δ - 2 - ι := by
  constructor
  · unfold full; ring
  · unfold half; ring

/-- Table S2, cross-refresh round `i`, cost `nw + 1`. -/
theorem cross_i_margins :
    full n a (n * (a + δ) + 1) ι = (2 * n - 2) * a - n * δ - 1 - ι ∧
    half n a (n * (a + δ) + 1) ι = (n / 2 - 1) * a - n * δ - 1 - ι := by
  constructor
  · unfold full; ring
  · unfold half; ring

/-- Table S2, cross-refresh round `i + 1`, cost `2w + 1`. -/
theorem cross_next_margins :
    full n a (2 * (a + δ) + 1) ι = (3 * n - 4) * a - 2 * δ - 1 - ι ∧
    half n a (2 * (a + δ) + 1) ι = (3 * n - 6) * a / 2 - 2 * δ - 1 - ι := by
  constructor
  · unfold full; ring
  · unfold half; ring

end Table

section Sixteen
variable {a δ ι : ℝ}

/-- Table S2, the four rows at `n = 16` (using `δ < 1`). -/
theorem margins_at_16 (hδ1 : δ < 1) :
    full 16 a (2 * (a + δ)) ι > 44 * a - 2 - ι ∧
    half 16 a (2 * (a + δ)) ι > 21 * a - 2 - ι ∧
    full 16 a ((16 + 2) * (a + δ) + 2) ι > 28 * a - 20 - ι ∧
    half 16 a ((16 + 2) * (a + δ) + 2) ι > 5 * a - 20 - ι ∧
    full 16 a (16 * (a + δ) + 1) ι > 30 * a - 17 - ι ∧
    half 16 a (16 * (a + δ) + 1) ι > 7 * a - 17 - ι ∧
    full 16 a (2 * (a + δ) + 1) ι > 44 * a - 3 - ι ∧
    half 16 a (2 * (a + δ) + 1) ι > 21 * a - 3 - ι := by
  unfold full half
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

end Sixteen

/-- Supplement S3-C: raising `n` by one raises each full margin by at least
`2a - δ` and each half margin by at least `a/2 - δ`. -/
theorem margin_growth (n a δ ι : ℝ) (ha : 0 ≤ a) (hδ : 0 ≤ δ) :
    -- joint
    full (n + 1) a (2 * (a + δ)) ι - full n a (2 * (a + δ)) ι ≥ 2 * a - δ ∧
    half (n + 1) a (2 * (a + δ)) ι - half n a (2 * (a + δ)) ι ≥ a / 2 - δ ∧
    -- split
    full (n + 1) a ((n + 1 + 2) * (a + δ) + 2) ι
      - full n a ((n + 2) * (a + δ) + 2) ι ≥ 2 * a - δ ∧
    half (n + 1) a ((n + 1 + 2) * (a + δ) + 2) ι
      - half n a ((n + 2) * (a + δ) + 2) ι ≥ a / 2 - δ ∧
    -- cross, round i
    full (n + 1) a ((n + 1) * (a + δ) + 1) ι - full n a (n * (a + δ) + 1) ι ≥ 2 * a - δ ∧
    half (n + 1) a ((n + 1) * (a + δ) + 1) ι - half n a (n * (a + δ) + 1) ι ≥ a / 2 - δ ∧
    -- cross, round i + 1
    full (n + 1) a (2 * (a + δ) + 1) ι - full n a (2 * (a + δ) + 1) ι ≥ 2 * a - δ ∧
    half (n + 1) a (2 * (a + δ) + 1) ι - half n a (2 * (a + δ) + 1) ι ≥ a / 2 - δ := by
  unfold full half
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- All eight margins of Table S2 are positive for every `n ≥ 16` once `a ≥ 5`
(the paper's `a > 255`), so a positive slack fits below each of them. -/
theorem margins_pos (n a δ ι : ℝ) (hn : 16 ≤ n) (ha : 5 ≤ a) (hδ1 : δ < 1) (hι1 : ι ≤ 1) :
    0 < full n a (2 * (a + δ)) ι ∧ 0 < half n a (2 * (a + δ)) ι ∧
    0 < full n a ((n + 2) * (a + δ) + 2) ι ∧ 0 < half n a ((n + 2) * (a + δ) + 2) ι ∧
    0 < full n a (n * (a + δ) + 1) ι ∧ 0 < half n a (n * (a + δ) + 1) ι ∧
    0 < full n a (2 * (a + δ) + 1) ι ∧ 0 < half n a (2 * (a + δ) + 1) ι := by
  unfold full half
  have h1 : 0 ≤ (n - 16) * (a / 2 - δ) := mul_nonneg (by linarith) (by linarith)
  have h2 : 0 ≤ (n - 16) * (2 * a - δ) := mul_nonneg (by linarith) (by linarith)
  have h3 : 0 ≤ (n - 16) * a := mul_nonneg (by linarith) (by linarith)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- Supplement S3-C: copying both factors costs `3nw`, which exceeds the full leading
allowance `(3n - 2)a` by `2a + 3nδ`. -/
theorem copy_excess (n a δ : ℝ) : 3 * n * (a + δ) - (3 * n - 2) * a = 2 * a + 3 * n * δ := by
  ring

/-! ## Concrete widths at `n = 16`, `w = 256` (main paper, Figs. 1 and 4; S4-E; S9) -/

/-- Key, joint, split and cross-refresh widths, and the advertised range. -/
theorem widths_16_256 :
    3 * 16 * 256 = 12288 ∧ 2 * 256 = 512 ∧ (16 + 2) * 256 + 2 = 4610 ∧
    16 * 256 + 1 = 4097 ∧ 2 * 256 + 1 = 513 ∧ (3 * 16 - 2) * 255 = 11730 ∧
    (3 * 16 - 2) * 256 = 11776 ∧ 11776 / 2 = 5888 := by
  norm_num

/-- Rounded percentages that the text states as approximations: 512 bits are 4.17%,
173 bits 1.41%, 86 bits 0.70%, and 11,776 bits about 95.8% of the 12,288-bit key;
5,888 bits are below 47.92%. Each value lies in the rounding interval. -/
theorem rounded_percentages :
    (0.04165 : ℚ) ≤ 512 / 12288 ∧ (512 : ℚ) / 12288 < 0.04175 ∧
    (0.01405 : ℚ) ≤ 173 / 12288 ∧ (173 : ℚ) / 12288 < 0.01415 ∧
    (0.00695 : ℚ) ≤ 86 / 12288 ∧ (86 : ℚ) / 12288 < 0.00705 ∧
    (0.9575 : ℚ) ≤ 11776 / 12288 ∧ (11776 : ℚ) / 12288 < 0.9585 ∧
    (5888 : ℚ) / 12288 < 0.4792 := by
  norm_num

/-- Supplement S4-E states that the endpoints `log q - σ < 256` and
`(log q - σ)/2 < 128` are below 2.08% and 1.04% of the key, and that the advertised
allowance `46 log q - σ_C`, with `log q < 256`, is below 95.83%. The stated bounds
only give 256/12288 > 2.083%, 128/12288 > 1.041% and 11776/12288 > 95.833%; values
admitted by those bounds exceed the printed percentages. -/
theorem s4e_percentages_not_implied :
    (255.9 : ℚ) < 256 ∧ (255.9 : ℚ) / 12288 > 0.0208 ∧
    (127.95 : ℚ) < 128 ∧ (127.95 : ℚ) / 12288 > 0.0104 ∧
    (255.999 : ℚ) < 256 ∧ 46 * (255.999 : ℚ) / 12288 > 0.9583 := by
  norm_num

/-- The bounds that do follow: below 2.09%, 1.05% and 95.84%. -/
theorem s4e_percentages_valid (e e' lq : ℝ) (he : e < 256) (he' : e' < 128) (hlq : lq < 256) :
    e / 12288 < 0.0209 ∧ e' / 12288 < 0.0105 ∧ 46 * lq / 12288 < 0.9584 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [div_lt_iff₀ (by norm_num)] <;> linarith

/-- Supplement S4-E as revised in R23.29: the endpoints are below `1/48 ≈ 2.083%` and
`1/96 ≈ 1.042%` of the 12,288-bit key, and `46 log q` is below `23/24 ≈ 95.833%`; the three
fractions are exactly `256/12288`, `128/12288` and `11776/12288`. -/
theorem s4e_exact (e e' lq : ℝ) (he : e < 256) (he' : e' < 128) (hlq : lq < 256) :
    e / 12288 < 1 / 48 ∧ e' / 12288 < 1 / 96 ∧ 46 * lq / 12288 < 23 / 24 ∧
    (256 : ℚ) / 12288 = 1 / 48 ∧ (128 : ℚ) / 12288 = 1 / 96 ∧ (11776 : ℚ) / 12288 = 23 / 24 ∧
    (0.020825 : ℚ) < 1 / 48 ∧ (1 : ℚ) / 48 < 0.020835 ∧
    (0.010415 : ℚ) < 1 / 96 ∧ (1 : ℚ) / 96 < 0.010425 ∧
    (0.958325 : ℚ) < 23 / 24 ∧ (23 : ℚ) / 24 < 0.958335 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [div_lt_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith
  · norm_num

/-! ## The concrete guarantee of Supplement S4-E -/

/-- Supplement S4-E: with `q > 2^255`, `Q ≤ 2^30`, `DLadv ≤ 2^{-81}` and `λ' ≤ 173`,
`(1 + 2^{λ'})/q ≤ 2^{-81}`, the square root of main-paper eq. (14) is at most `2^{-40}`,
`(2Q + 3)/q < 2^{-223}`, and the impersonation probability bound of eq. (14) is below
`2^{-40} + 2^{-223}`. -/
theorem s4e_bound (q Q adv : ℝ) (lam : ℕ) (hq : (2 : ℝ) ^ 255 < q)
    (hQ : Q ≤ 2 ^ 30) (hadv : adv ≤ 1 / 2 ^ 81) (hlam : lam ≤ 173) :
    (1 + 2 ^ lam) / q ≤ 1 / 2 ^ 81 ∧
    Real.sqrt (adv + (1 + 2 ^ lam) / q) ≤ 1 / 2 ^ 40 ∧
    (2 * Q + 3) / q < 1 / 2 ^ 223 ∧
    (2 * Q + 3) / q + Real.sqrt (adv + (1 + 2 ^ lam) / q) < 1 / 2 ^ 40 + 1 / 2 ^ 223 := by
  have hq0 : 0 < q := lt_trans (by positivity) hq
  have hpow : (2 : ℝ) ^ lam ≤ 2 ^ 173 := pow_le_pow_right₀ (by norm_num) hlam
  have h1 : (1 + 2 ^ lam) / q ≤ 1 / 2 ^ 81 := by
    rw [div_le_div_iff₀ hq0 (by positivity)]
    have : (1 + (2 : ℝ) ^ lam) * 2 ^ 81 ≤ 2 ^ 255 := by
      have : (1 + (2 : ℝ) ^ 173) * 2 ^ 81 ≤ 2 ^ 255 := by norm_num
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) 81]
    nlinarith
  have h2 : Real.sqrt (adv + (1 + 2 ^ lam) / q) ≤ 1 / 2 ^ 40 := by
    rw [show (1 : ℝ) / 2 ^ 40 = Real.sqrt ((1 / 2 ^ 40) ^ 2) by
      rw [Real.sqrt_sq (by positivity)]]
    apply Real.sqrt_le_sqrt
    have : (1 : ℝ) / 2 ^ 81 + 1 / 2 ^ 81 = (1 / 2 ^ 40) ^ 2 := by norm_num
    linarith
  have h3 : (2 * Q + 3) / q < 1 / 2 ^ 223 := by
    rw [div_lt_div_iff₀ hq0 (by positivity)]
    have : (2 * Q + 3) * 2 ^ 223 < (2 : ℝ) ^ 255 := by
      have : (2 * 2 ^ 30 + 3) * (2 : ℝ) ^ 223 < 2 ^ 255 := by norm_num
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) 223]
    nlinarith
  exact ⟨h1, h2, h3, by linarith⟩

/-- The `ANY` value 86: there `λ' = 2λ`, and `2 · 86 = 172 ≤ 173`. -/
theorem any_value : 2 * 86 ≤ 173 := by norm_num

/-! ## Corollary 11: the endpoints as fractions of the key -/

/-- The secure endpoint `log q - s` with `s > 0` is below `1/(3n)` of the `3nw`-bit key. -/
theorem secure_fraction (n a w s : ℝ) (hn : 0 < n) (hw : 0 < w) (haw : a ≤ w) (hs : 0 < s) :
    (a - s) / (3 * n * w) < 1 / (3 * n) := by
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- The broken endpoint `2w + ι` is `2/(3n)` of the key plus `ι/(3nw)`. -/
theorem attack_fraction (n w ι : ℝ) (hn : n ≠ 0) (hw : w ≠ 0) :
    (2 * w + ι) / (3 * n * w) = 2 / (3 * n) + ι / (3 * n * w) := by
  field_simp

/-! ## Identity-based budgets (Supplement S6-A, S6-C, S7-C) -/

/-- Supplement S6-A: under a full-group encoding `ℓ_G ≥ log q`, every output of
`j ≥ 1` group elements after prior target leakage `b ≥ 0` exceeds the cap
`log q - l_m - σ_K` whenever `l_m + σ_K > 0`. -/
theorem ibkem_cap_exceeded (lq ℓG lm σ b : ℝ) (j : ℕ) (hj : 1 ≤ j) (hlq : 0 ≤ lq)
    (hℓ : lq ≤ ℓG) (hb : 0 ≤ b) (hpos : 0 < lm + σ) :
    b + j * ℓG > lq - lm - σ := by
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  nlinarith

/-- Supplement S6-C: for `n ≥ ⌈(2ℓ_G + ℓ_p + 1 + σ_B)/log p⌉`, the leakage parameter
`λ = 2ℓ_G + ℓ_p + 1` with `b₀ = 0` satisfies `b₀ + L_all + ι ≤ λ ≤ ⌊(n + 1) log p - σ_B⌋`
under both conventions. -/
theorem ibe_window (lp σB : ℝ) (ℓG ℓp n : ℕ) (ι : ℝ) (hlp : 0 < lp) (hι : ι ≤ 1)
    (hn : ⌈(2 * ℓG + ℓp + 1 + σB) / lp⌉₊ ≤ n) :
    (0 : ℝ) + (2 * ℓG + ℓp) + ι ≤ ((2 * ℓG + ℓp + 1 : ℕ) : ℝ) ∧
    ((2 * ℓG + ℓp + 1 : ℕ) : ℤ) ≤ ⌊(n + 1) * lp - σB⌋ := by
  refine ⟨by push_cast; linarith, ?_⟩
  rw [Int.le_floor]
  have h1 : (2 * ℓG + ℓp + 1 + σB) / lp ≤ n :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
  rw [div_le_iff₀ hlp] at h1
  push_cast
  nlinarith

/-- Supplement S6-C: with ordinary full-field encodings `ℓ_G, ℓ_p ≥ log p`, copying the
whole key costs `3ℓ_G + nℓ_p ≥ (n + 3) log p`, above the cap `(n + 1) log p - σ_B`. -/
theorem ibe_copy_exceeds (lp ℓG ℓp σB n : ℝ) (hlp : 0 < lp) (hG : lp ≤ ℓG) (hp : lp ≤ ℓp)
    (hn : 0 ≤ n) (hσ : 0 ≤ σB) :
    (n + 3) * lp ≤ 3 * ℓG + n * ℓp ∧ (n + 1) * lp - σB < (n + 3) * lp := by
  constructor <;> nlinarith

/-- Supplement S7-C: the window `⌈log p⌉ + ι ≤ λ ≤ 2 log p - σ` contains
`λ = ⌈log p⌉ + ι` for every slack `σ ≤ log p - 2`, and at this smallest `λ`
the Claim 2 bound `2^λ/p^3` is below `4/p^2`. -/
theorem zhouyang_window (p σ ι : ℝ) (hp : 1 < p) (hσ : σ ≤ Real.logb 2 p - 2) (hι1 : ι ≤ 1) :
    (⌈Real.logb 2 p⌉ : ℝ) + ι ≤ 2 * Real.logb 2 p - σ ∧
    (2 : ℝ) ^ ((⌈Real.logb 2 p⌉ : ℝ) + ι) / p ^ 3 < 4 / p ^ 2 := by
  have hp0 : 0 < p := by linarith
  have hceil : (⌈Real.logb 2 p⌉ : ℝ) < Real.logb 2 p + 1 := Int.ceil_lt_add_one _
  refine ⟨by linarith, ?_⟩
  have hpow : (2 : ℝ) ^ ((⌈Real.logb 2 p⌉ : ℝ) + ι) < 2 ^ (Real.logb 2 p + 2) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  have hval : (2 : ℝ) ^ (Real.logb 2 p + 2) = 4 * p := by
    rw [Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hp0]
    norm_num
    ring
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  rw [hval] at hpow
  have : (4 * p) * p ^ 2 = 4 * p ^ 3 := by ring
  nlinarith [pow_pos hp0 2]

end Clria.Params
