module

public import BestOfBothWorlds.UniformAdversarialBound
public import Mathlib.Tactic.FinCases

/-!
Explicit admissible tables for the complete uniform-sampling theorem. The first
changes with time; the second has tied suboptimal arms and permits tied estimated
scores. In both cases the true best arm has index one, rather than index zero.
-/

@[expose] public section

namespace BestOfBothWorlds.UniformExamples

open RealizedGaps UniformAdversarialBound

/-- At horizon two, arm one has gains 3/4 and 1; arm zero has gains 1/4 and 0. -/
noncomputable def changingTwo (t : ℕ) (k : Fin 2) : ℝ :=
  if t = 0 then (if k = 0 then 1 / 4 else 3 / 4)
  else (if k = 0 then 0 else 1)

theorem changingTwo_bounds (t : ℕ) (k : Fin 2) :
    0 ≤ changingTwo t k ∧ changingTwo t k ≤ 1 := by
  unfold changingTwo
  split_ifs <;> norm_num

/-- At horizon one the two suboptimal arms tie at zero; arm one gains 1/2. -/
noncomputable def tiedThree (_t : ℕ) (k : Fin 3) : ℝ :=
  if k = 1 then 1 / 2 else 0

theorem tiedThree_bounds (t : ℕ) (k : Fin 3) :
    0 ≤ tiedThree t k ∧ tiedThree t k ≤ 1 := by
  unfold tiedThree
  split_ifs <;> norm_num

theorem changingTwo_strict (k : Fin 2) (hk : k ≠ 1) :
    cumulative changingTwo 2 k < cumulative changingTwo 2 1 := by
  fin_cases k <;> norm_num [cumulative, changingTwo, Finset.sum_range_succ] at *

theorem changingTwo_best : best (by decide : 0 < 2) changingTwo 2 = 1 :=
  best_eq_of_strict (by decide) changingTwo 2 1 changingTwo_strict

theorem changingTwo_unique : UniqueBest (by decide : 0 < 2) changingTwo 2 :=
  uniqueBest_of_strict (by decide) changingTwo 2 1 changingTwo_strict

theorem changingTwo_gap : minGap (by decide : 2 ≤ 2) changingTwo 2 = 3 / 4 := by
  apply minGap_eq_of_constant_competitors
  intro k hk
  have hk' : k ≠ 1 := by simpa only [changingTwo_best] using hk
  fin_cases k <;>
    norm_num [competitorGap, changingTwo_best, cumulative, changingTwo,
      Finset.sum_range_succ] at *

theorem changingTwo_complexity : complexity (by decide : 2 ≤ 2) changingTwo 2 = 32 / 9 := by
  rw [complexity_eq, changingTwo_gap]
  norm_num

/-- The complete theorem is instantiated at a changing table with a nonzero best index. -/
theorem changingTwo_error_bound :
    errorProbability (by decide : 0 < 2) changingTwo 2 ≤
      2 * Real.exp (-(27 : ℝ) / 448) := by
  have h := unif_adversarial_error_bound (by decide : 2 ≤ 2) changingTwo 2
    (fun t _ k => changingTwo_bounds t k) changingTwo_unique
  norm_num [changingTwo_complexity] at h ⊢
  exact h

theorem tiedThree_strict (k : Fin 3) (hk : k ≠ 1) :
    cumulative tiedThree 1 k < cumulative tiedThree 1 1 := by
  fin_cases k <;> norm_num [cumulative, tiedThree] at *

theorem tiedThree_best : best (by decide : 0 < 3) tiedThree 1 = 1 :=
  best_eq_of_strict (by decide) tiedThree 1 1 tiedThree_strict

theorem tiedThree_unique : UniqueBest (by decide : 0 < 3) tiedThree 1 :=
  uniqueBest_of_strict (by decide) tiedThree 1 1 tiedThree_strict

theorem tiedThree_gap : minGap (by decide : 2 ≤ 3) tiedThree 1 = 1 / 2 := by
  apply minGap_eq_of_constant_competitors
  intro k hk
  have hk' : k ≠ 1 := by simpa only [tiedThree_best] using hk
  fin_cases k <;> norm_num [competitorGap, tiedThree_best, cumulative, tiedThree] at *

theorem tiedThree_complexity : complexity (by decide : 2 ≤ 3) tiedThree 1 = 12 := by
  rw [complexity_eq, tiedThree_gap]
  norm_num

/-- The complete theorem also handles tied suboptimal arms at horizon one. -/
theorem tiedThree_error_bound :
    errorProbability (by decide : 0 < 3) tiedThree 1 ≤
      3 * Real.exp (-(1 : ℝ) / 112) := by
  have h := unif_adversarial_error_bound (by decide : 2 ≤ 3) tiedThree 1
    (fun t _ k => tiedThree_bounds t k) tiedThree_unique
  norm_num [tiedThree_complexity] at h ⊢
  exact h

/-- An admissible one-round trajectory that pulls a zero-reward arm. -/
noncomputable def tiedObservation : AdaptiveBanditProcess.Trajectory 3 1 :=
  (((), (0 : Fin 3)), tiedThree 0)

/-- All estimated scores tie at zero on this concrete trajectory. -/
theorem tiedObservation_estimates (k : Fin 3) :
    UniformSampling.estimatedCumulative (by decide : 0 < 3) 1 k tiedObservation = 0 := by
  rw [UniformSampling.estimatedCumulative_eq_sum]
  simp only [Finset.sum_range_one]
  rw [UniformSampling.estimatedGain_formula (by decide) (by decide : 0 < 1)]
  norm_num [tiedObservation, AdaptiveBanditProcess.roundAction,
    AdaptiveBanditProcess.roundObservedReward, AdaptiveBanditProcess.roundRewardVector,
    AdaptiveBanditProcess.roundOutcome, AdaptiveBanditProcess.prefix_self, id, tiedThree]

/-- The tie rule chooses index zero, although the true best index is one. -/
theorem tiedObservation_recommendation :
    UniformSampling.recommendation (by decide : 0 < 3) 1 tiedObservation = 0 := by
  apply le_antisymm
  · apply UniformSampling.recommendation_smallest_tie
    rw [tiedObservation_estimates, tiedObservation_estimates]
  · exact Fin.zero_le _

/-- The actual error definition includes this estimated-score tie. -/
theorem tiedObservation_error :
    tiedObservation ∈ errorEvent (by decide : 0 < 3) tiedThree 1 := by
  change UniformSampling.recommendation (by decide : 0 < 3) 1 tiedObservation ≠
    best (by decide : 0 < 3) tiedThree 1
  rw [tiedObservation_recommendation, tiedThree_best]
  decide

end BestOfBothWorlds.UniformExamples
