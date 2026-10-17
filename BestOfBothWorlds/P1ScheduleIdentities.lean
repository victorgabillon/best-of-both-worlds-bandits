module

public import BestOfBothWorlds.P1Complexity
public import Mathlib.Algebra.BigOperators.Intervals

/-!
Exact conversion between the manuscript's weighted phase differences and the
positive telescoped schedule expression. The final extended time is the zero
sentinel, not an additional comparison or sampling round.
-/

@[expose] public section

namespace BestOfBothWorlds.P1Schedule

variable {K : ℕ}

/-- Finite summation by parts for the coefficients 1,2,... . -/
theorem weighted_telescope (T : ℕ → ℝ) (a b : ℕ) (hab : a < b) :
    (∑ j ∈ Finset.Ico a b, ((j + 1 : ℕ) : ℝ) * (T j - T (j + 1))) =
      ((a + 1 : ℕ) : ℝ) * T a + (∑ j ∈ Finset.Ico (a + 1) b, T j) - (b : ℝ) * T b := by
  have hle : a + 1 ≤ b := hab
  induction b, hle using Nat.le_induction with
  | base =>
      simp only [Nat.Ico_succ_singleton, Finset.sum_singleton, Finset.Ico_self, Finset.sum_empty,
        add_zero]
      ring
  | succ b hle ih =>
      rw [Finset.sum_Ico_succ_top (Nat.le_trans (Nat.le_succ a) hle),
        Finset.sum_Ico_succ_top hle, ih (by omega)]
      simp only [Nat.cast_add, Nat.cast_one]
      ring

/-- Natural and finite rank indices enumerate exactly the same strict tail. -/
theorem tail_nat_sum (f : ℕ → ℝ) (r : Fin K) :
    (∑ j ∈ later r, f j.val) = ∑ j ∈ Finset.Ico (r.val + 1) K, f j := by
  classical
  refine Finset.sum_bij (fun j _ => j.val) ?_ ?_ ?_ ?_
  · intro j hj
    exact Finset.mem_Ico.mpr ⟨Nat.succ_le_of_lt ((mem_later r j).1 hj), j.isLt⟩
  · intro i _ j _ hij
    exact Fin.ext hij
  · intro j hj
    obtain ⟨hrj, hjK⟩ := Finset.mem_Ico.mp hj
    exact ⟨⟨j, hjK⟩, (mem_later r _).2 (Nat.lt_of_succ_le hrj), rfl⟩
  · intro j _
    rfl

/-- The comparison vector extended by the manuscript's final zero sentinel. -/
noncomputable def extendedTime {hK : 2 ≤ K} {n : ℕ} (s : Schedule hK n) (j : ℕ) : ℝ :=
  if hj : j < K then (s.time ⟨j, hj⟩ : ℝ) else 0

@[simp]
theorem extendedTime_val {hK : 2 ≤ K} {n : ℕ} (s : Schedule hK n) (r : Fin K) :
    extendedTime s r.val = (s.time r : ℝ) := by
  simp only [extendedTime, dite_eq_left r.isLt]

@[simp]
theorem extendedTime_last {hK : 2 ≤ K} {n : ℕ} (s : Schedule hK n) : extendedTime s K = 0 := by
  simp [extendedTime]

/-- The original weighted phase sum, with real subtraction and its explicit zero sentinel. -/
noncomputable def weightedAccumulated {hK : 2 ≤ K} {n : ℕ} (s : Schedule hK n) (r : Fin K) : ℝ :=
  ∑ j ∈ Finset.Ico r.val K, ((j + 1 : ℕ) : ℝ) * (extendedTime s j - extendedTime s (j + 1))

/-- The actual weighted schedule numerator equals the telescoped positive form used in the proofs. -/
theorem weightedAccumulated_eq_accumulated {hK : 2 ≤ K} {n : ℕ}
    (s : Schedule hK n) (r : Fin K) : weightedAccumulated s r = accumulated s r := by
  unfold weightedAccumulated
  rw [weighted_telescope (extendedTime s) r.val K r.isLt, extendedTime_last, mul_zero, sub_zero,
    ← tail_nat_sum (extendedTime s) r]
  simp only [extendedTime_val, accumulated, rank]

/-- The comparison fractions, extended by the same zero sentinel. -/
noncomputable def extendedFraction {hK : 2 ≤ K} {n : ℕ} (s : Schedule hK n) (j : ℕ) : ℝ :=
  extendedTime s j / (n : ℝ)

/-- The phase-weighted numerator appearing literally in the manuscript's
comparison-fraction definition of H_P1. -/
noncomputable def weightedFractionAccumulated {hK : 2 ≤ K} {n : ℕ}
    (s : Schedule hK n) (r : Fin K) : ℝ :=
  ∑ j ∈ Finset.Ico r.val K, ((j + 1 : ℕ) : ℝ) *
    (extendedFraction s j - extendedFraction s (j + 1))

theorem weightedFractionAccumulated_eq {hK : 2 ≤ K} {n : ℕ}
    (s : Schedule hK n) (r : Fin K) :
    weightedFractionAccumulated s r =
      P1Complexity.algebraicAccumulated (fraction s) r := by
  rw [P1Complexity.algebraicAccumulated_fraction]
  unfold weightedFractionAccumulated extendedFraction
  have hterm (j : ℕ) : ((j + 1 : ℕ) : ℝ) *
      (extendedTime s j / (n : ℝ) - extendedTime s (j + 1) / (n : ℝ)) =
      (((j + 1 : ℕ) : ℝ) * (extendedTime s j - extendedTime s (j + 1))) / (n : ℝ) := by
    ring
  simp_rw [hterm]
  rw [← Finset.sum_div]
  change weightedAccumulated s r / (n : ℝ) = accumulated s r / (n : ℝ)
  rw [weightedAccumulated_eq_accumulated]

/-- The literal weighted-fraction formula, evaluated at an admissible schedule. -/
noncomputable def weightedProfileComplexity {hK : 2 ≤ K} {n : ℕ}
    (gap : Fin K → ℝ) (s : Schedule hK n) : ℝ :=
  P1Ranking.harmonicK K * (Finset.univ : Finset (Fin K)).sup'
    ⟨firstRank hK, Finset.mem_univ _⟩
    (fun r => (weightedFractionAccumulated s r + ((K : ℝ) / 24) * fraction s r * gap r) /
      ((fraction s r) ^ 2 * (gap r) ^ 2))

/-- The fixed-schedule complexity used by the stochastic proof is exactly the
paper's weighted comparison-fraction expression, including its zero sentinel. -/
theorem fixedComplexity_eq_weightedProfileComplexity (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    {n : ℕ} (s : Schedule hK n) :
    P1Complexity.fixedComplexity gap s = weightedProfileComplexity gap s := by
  rw [P1Complexity.fixedComplexity_eq_profileComplexity hK gap hpos hsorted]
  unfold P1Complexity.profileComplexity weightedProfileComplexity P1Complexity.profileCost
  simp_rw [weightedFractionAccumulated_eq]

end BestOfBothWorlds.P1Schedule
