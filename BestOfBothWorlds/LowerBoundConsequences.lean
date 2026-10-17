module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

/-!
Quantitative consequences used in Appendices D and E. These are scalar helper
lemmas: the information and concentration inputs are explicit hypotheses, not
claims that the constructed bandit laws already satisfy them.
-/

@[expose] public section

namespace BestOfBothWorlds.LowerBounds

/-- Either manuscript horizon restriction forces a genuinely long horizon.
The stronger `1/128` restriction can be weakened to this `1/32` input. -/
theorem horizon_gap_square_ge_one {K n : ℕ} (hK : 2 ≤ K) (d : ℝ)
    (horizon : (K : ℝ) * Real.exp (-(n : ℝ) * d ^ 2 / 128) ≤ 1 / 32) :
    1 ≤ (n : ℝ) * d ^ 2 := by
  have hKr : (2 : ℝ) ≤ (K : ℝ) := Nat.cast_le.mpr hK
  have hexp := Real.add_one_le_exp (-(n : ℝ) * d ^ 2 / 128)
  have hmul := mul_le_mul_of_nonneg_right hKr
    (Real.exp_pos (-(n : ℝ) * d ^ 2 / 128)).le
  linarith

/-- Deterministic arithmetic consequences used in both lower-bound appendices. -/
theorem horizon_arithmetic {n : ℕ} (d D : ℝ)
    (hd : 0 < d) (hdsmall : d ≤ 1 / 8) (hD : 0 < D) (hDsmall : D ≤ 1 / 8)
    (hlarge : 1 ≤ (n : ℝ) * d ^ 2) :
    64 ≤ n ∧ 1 ≤ (n : ℝ) * d / D ∧ D / (n : ℝ) ≤ d / 8 := by
  have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hdsq : d ^ 2 ≤ 1 / 64 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_left hdsq hnnonneg
  have hn64 : (64 : ℝ) ≤ (n : ℝ) := by linarith
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hpair : d * D ≤ 1 / 64 := by
    calc
      d * D ≤ (1 / 8 : ℝ) * (1 / 8) := mul_le_mul hdsmall hDsmall hD.le (by norm_num)
      _ = _ := by norm_num
  have hr : D ≤ (n : ℝ) * d := by
    by_contra h
    have hlt := mul_lt_mul_of_pos_right (lt_of_not_ge h) hd
    nlinarith
  have hround : 8 * D ≤ (n : ℝ) * d := by
    by_contra h
    have hlt := mul_lt_mul_of_pos_right (lt_of_not_ge h) hd
    nlinarith
  refine ⟨Nat.cast_le.mp hn64, ?_, ?_⟩
  · exact (le_div_iff₀ hD).2 (by simpa only [one_mul] using hr)
  · apply (div_le_iff₀ hnpos).2
    linarith

/-- Appendix E's event estimate, with the exact stochastic-error and
information constants. The zero-probability case uses common support. -/
theorem bob_recommendation_bound {p q x D : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hx : 0 ≤ x)
    (herror : q ≤ Real.exp (-2048 * x) / 64)
    (hzero : q = 0 → p = 0)
    (hinfo : 0 < q → p * Real.log (1 / q) ≤ D + Real.log 2)
    (hD : D ≤ 768 * x) : p ≤ 3 / 8 := by
  by_cases hqzero : q = 0
  · rw [hzero hqzero]
    norm_num
  have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hqzero)
  have hlog : 2048 * x + 6 * Real.log 2 ≤ Real.log (1 / q) := by
    have h := Real.log_le_log hqpos herror
    have h64 : Real.log (64 : ℝ) = 6 * Real.log 2 := by
      have heq : (64 : ℝ) = 2 ^ (6 : ℕ) := by norm_num
      rw [heq, Real.log_pow]
      norm_num
    rw [Real.log_div (Real.exp_ne_zero _) (by norm_num), Real.log_exp, h64] at h
    rw [one_div, Real.log_inv]
    linarith
  have htwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hden : 0 < 2048 * x + 6 * Real.log 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hlog hp
  have hi := hinfo hqpos
  have hc : p * (2048 * x + 6 * Real.log 2) ≤
      (3 / 8 : ℝ) * (2048 * x + 6 * Real.log 2) := by
    nlinarith
  exact (mul_le_mul_iff_left₀ hden).mp hc

/-- Appendix D's comparison of bad-table mass with the testing exponential.
Here x=n/H_UNIF and K*x=n*Delta_1^2. -/
theorem adversarial_bad_mass_relative {K x b : ℝ} (hK : 4096 ≤ K) (hx : 0 ≤ x)
    (horizon : K * Real.exp (-K * x / 128) ≤ 1 / 128)
    (hbad : b ≤ 2 * K * Real.exp (-K * x / 64)) :
    b ≤ Real.exp (-32 * x) / 64 := by
  have heq : Real.exp (-K * x / 64) =
      Real.exp (-K * x / 128) * Real.exp (-K * x / 128) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hmul := mul_le_mul_of_nonneg_right horizon (Real.exp_pos (-K * x / 128)).le
  have hcompare : Real.exp (-K * x / 128) ≤ Real.exp (-32 * x) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hK) hx]
  rw [heq] at hbad
  nlinarith

/-- Good-table error mass after removing bad tables from a testing bound.
This calculation does not condition a transcript law on the good event. -/
theorem adversarial_good_error_sum {R₁ R₂ test₁ test₂ b₁ b₂ ε : ℝ}
    (htesting : ε / 2 ≤ test₁ + test₂)
    (hremove₁ : test₁ - b₁ ≤ R₁)
    (hremove₂ : test₂ - b₂ ≤ R₂)
    (hbad₁ : b₁ ≤ ε / 64) (hbad₂ : b₂ ≤ ε / 64) :
    15 * ε / 32 ≤ R₁ + R₂ := by linarith

/-- The two deterministic maximizing witnesses give the exact reported
Theorem 2 conclusion once the preceding probability bounds are discharged. -/
theorem adversarial_two_witness_errors {R₁ R₂ e₁ e₂ ε : ℝ}
    (hε : 0 ≤ ε) (hR : 15 * ε / 32 ≤ R₁ + R₂)
    (he₁ : R₁ ≤ e₁) (he₂ : R₂ ≤ e₂) :
    min (ε / 128) (1 / 32) ≤ max e₁ e₂ := by
  have h₁ : e₁ ≤ max e₁ e₂ := le_max_left _ _
  have h₂ : e₂ ≤ max e₁ e₂ := le_max_right _ _
  have hbound : ε / 128 ≤ max e₁ e₂ := by linarith
  exact (min_le_left _ _).trans hbound

/-- Appendix E's quantitative removal of bad tables, without an independence
hypothesis between the recommendation and full-table goodness. -/
theorem bob_good_error_lower {p bad goodError : ℝ}
    (hp : p ≤ 3 / 8) (hbad : bad ≤ 1 / 16)
    (hremove : 1 - p - bad ≤ goodError) :
    (9 : ℝ) / 16 ≤ goodError := by linarith

end BestOfBothWorlds.LowerBounds
