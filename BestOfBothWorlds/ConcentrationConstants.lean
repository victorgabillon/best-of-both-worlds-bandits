module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
Exact deterministic reductions of the Bernstein–Freedman exponent.
The variables are real parameters; no sampling schedule is defined here.
-/

@[expose] public section

namespace BestOfBothWorlds.ConcentrationConstants

/-- Substituting the stochastic threshold preserves the manuscript's factor 128. -/
theorem stochastic_exponent (H K Q t delta : ℝ)
    (hH : 0 < H) (hQ : 0 < Q + (K / 24) * t * delta) :
    -(t * delta / 8) ^ 2 /
        (2 * (H * Q + (K * H) * (t * delta / 8) / 3)) =
      -(t * delta) ^ 2 / (128 * H * (Q + (K / 24) * t * delta)) := by
  have hd : 2 * (H * Q + (K * H) * (t * delta / 8) / 3) =
      2 * H * (Q + (K / 24) * t * delta) := by ring
  rw [hd]
  apply (div_eq_div_iff (by positivity) (by positivity)).2
  ring

/-- The same identity exposes the comparison-time and accumulated-rank parameters. -/
theorem stochastic_schedule_exponent (H K S r t comparisonTime delta : ℝ)
    (hH : 0 < H)
    (hD : 0 < S + r * (t - comparisonTime) + (K / 24) * t * delta) :
    -(t * delta / 8) ^ 2 /
        (2 * (H * (S + r * (t - comparisonTime)) +
          (K * H) * (t * delta / 8) / 3)) =
      -(t * delta) ^ 2 /
        (128 * H * (S + r * (t - comparisonTime) + (K / 24) * t * delta)) :=
  stochastic_exponent H K (S + r * (t - comparisonTime)) t delta hH hD

/-- Positive stochastic variance budget gives the positive Freedman denominator. -/
theorem stochastic_denominator_pos (H K Q t delta : ℝ)
    (hH : 0 < H) (hK : 0 ≤ K) (hQ : 0 < Q) (ht : 0 ≤ t) (hdelta : 0 ≤ delta) :
    0 < H * Q + (K * H) * (t * delta / 8) / 3 := by
  exact add_pos_of_pos_of_nonneg (mul_pos hH hQ) (by positivity)

/-- Fixed-table threshold and variance substitutions simplify without changing 1/3. -/
theorem adversarial_exponent (n b delta : ℝ)
    (hn : 0 < n) (hb : 0 < b) (hdelta : 0 ≤ delta) :
    -(n * delta / 2) ^ 2 / (2 * (n * b + b * (n * delta / 2) / 3)) =
      -(n * delta ^ 2) / (8 * b * (1 + delta / 6)) := by
  have hfactor : 0 < 1 + delta / 6 := by positivity
  have hd : n * b + b * (n * delta / 2) / 3 = n * b * (1 + delta / 6) := by ring
  rw [hd]
  apply (div_eq_div_iff (by positivity) (by positivity)).2
  ring

/-- For gaps at most 1, the exact exponent implies the sharper 3/28 coefficient. -/
theorem adversarial_exp_le (n b delta : ℝ)
    (hn : 0 ≤ n) (hb : 0 < b) (hdelta : 0 ≤ delta) (hdelta_one : delta ≤ 1) :
    Real.exp (-(n * delta ^ 2) / (8 * b * (1 + delta / 6))) ≤
      Real.exp (-(3 * n * delta ^ 2) / (28 * b)) := by
  apply Real.exp_le_exp.mpr
  have hfactor : 0 < 1 + delta / 6 := by positivity
  have hleft : 0 < 28 * b := by positivity
  have hright : 0 < 8 * b * (1 + delta / 6) := by positivity
  have hratio : (3 * n * delta ^ 2) / (28 * b) ≤
      (n * delta ^ 2) / (8 * b * (1 + delta / 6)) := by
    apply (div_le_div_iff₀ hleft hright).2
    have hprod := mul_nonneg (mul_nonneg (mul_nonneg hn (sq_nonneg delta)) hb.le)
      (sub_nonneg.mpr hdelta_one)
    nlinarith
  simpa only [neg_div] using neg_le_neg hratio

end BestOfBothWorlds.ConcentrationConstants
