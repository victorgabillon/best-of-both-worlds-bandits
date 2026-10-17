module

public import BestOfBothWorlds.P1Algorithm
public import BestOfBothWorlds.P1StochasticModel
public import BestOfBothWorlds.P1AdversarialBound
public import BestOfBothWorlds.P1StochasticBound
public import BestOfBothWorlds.P1Corollary
public import BestOfBothWorlds.ArchitectureExamples
public import BestOfBothWorlds.UniformExamples
public import Mathlib.Tactic.FinCases

/-!
Symbolic witnesses for actual P1. With two arms, the initial probabilities are
2/3 and 1/3; observing reward 1/2 from arm one reverses the ranks and these
probabilities. The stochastic witness has correlated nonbinary rewards and
unique best arm one. No numerical simulation is used.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open BestOfBothWorlds.AdaptiveBanditProcess

namespace BestOfBothWorlds.P1Examples

theorem harmonic_two : P1Ranking.harmonicK 2 = 3 / 2 := by
  norm_num [P1Ranking.harmonicK, Fin.sum_univ_two]

theorem order_zero : P1Ranking.order (fun _ : Fin 2 => (0 : ℝ)) = Equiv.refl _ := by
  exact Tuple.sort_eq_refl_iff_monotone.mpr monotone_const

/-- Unobserved tied scores use the fixed smallest-index tie rule. -/
theorem initial_probability (k : Fin 2) :
    (P1Algorithm.policy (by decide : 0 < 2)).prob 0 () k =
      if k = 0 then 2 / 3 else 1 / 3 := by
  change P1Ranking.probability (by decide : 0 < 2) (fun _ => 0) k = _
  simp only [P1Ranking.probability, P1Ranking.rank, P1Ranking.position, order_zero]
  fin_cases k <;> norm_num [harmonic_two]

noncomputable def observedHistory : ObservedHistory 2 1 := ((), (1, 1 / 2))

/-- One observed nonbinary reward changes the actual recursive importance-weighted score. -/
theorem observed_score (k : Fin 2) :
    P1Algorithm.score (by decide : 0 < 2) observedHistory k =
      if k = 1 then 3 / 2 else 0 := by
  have hp : P1Ranking.probability (by decide : 0 < 2)
      (P1Algorithm.score (by decide : 0 < 2) (t := 0) ()) (1 : Fin 2) = 1 / 3 := by
    have hh := initial_probability (1 : Fin 2)
    change P1Ranking.probability (by decide : 0 < 2)
      (P1Algorithm.score (by decide : 0 < 2) (t := 0) ()) 1 = _ at hh
    norm_num at hh
    exact hh
  change (0 : ℝ) + (if (1 : Fin 2) = k then (1 / 2) /
    P1Ranking.probability (by decide : 0 < 2)
      (P1Algorithm.score (by decide : 0 < 2) (t := 0) ()) k else 0) = _
  fin_cases k <;> norm_num [hp]

/-- The estimated order genuinely reverses after the observation. -/
theorem observed_order :
    P1Ranking.order (P1Algorithm.score (by decide : 0 < 2) observedHistory) = Equiv.swap 0 1 := by
  symm
  apply Tuple.eq_sort_iff.mpr
  constructor
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      norm_num [Function.comp_def, Equiv.swap_apply_def, observed_score] at *
  · intro i j hij heq
    fin_cases i <;> fin_cases j <;>
      norm_num [Function.comp_def, Equiv.swap_apply_def, observed_score] at *

/-- P1 increases the formerly second-ranked arm's actual next sampling probability. -/
theorem observed_probability (k : Fin 2) :
    (P1Algorithm.policy (by decide : 0 < 2)).prob 1 observedHistory k =
      if k = 1 then 2 / 3 else 1 / 3 := by
  change P1Ranking.probability (by decide : 0 < 2)
    (P1Algorithm.score (by decide : 0 < 2) observedHistory) k = _
  simp only [P1Ranking.probability, P1Ranking.rank, P1Ranking.position, observed_order]
  fin_cases k <;> norm_num [harmonic_two]

theorem probability_changes_with_observation :
    (P1Algorithm.policy (by decide : 0 < 2)).prob 0 () 1 = 1 / 3 ∧
    (P1Algorithm.policy (by decide : 0 < 2)).prob 1 observedHistory 1 = 2 / 3 ∧
    (P1Algorithm.policy (by decide : 0 < 2)).prob 0 () 1 ≠
      (P1Algorithm.policy (by decide : 0 < 2)).prob 1 observedHistory 1 := by
  have h0 : (P1Algorithm.policy (by decide : 0 < 2)).prob 0 () 1 = 1 / 3 := by
    simpa only [show (1 : Fin 2) ≠ 0 by decide, ite_false] using
      initial_probability (1 : Fin 2)
  have h1 : (P1Algorithm.policy (by decide : 0 < 2)).prob 1 observedHistory 1 = 2 / 3 := by
    simpa only [ite_eq_left] using observed_probability (1 : Fin 2)
  exact ⟨h0, h1, by
    intro heq
    have hh : (1 / 3 : ℝ) = 2 / 3 := h0.symm.trans (heq.trans h1)
    norm_num at hh⟩

/-- The probabilities normalize before and after the adaptive update. -/
theorem probability_normalization :
    (∑ k : Fin 2, (P1Algorithm.policy (by decide : 0 < 2)).prob 0 () k) = 1 ∧
    (∑ k : Fin 2, (P1Algorithm.policy (by decide : 0 < 2)).prob 1 observedHistory k) = 1 :=
  ⟨(P1Algorithm.policy (by decide : 0 < 2)).normalized 0 (),
    (P1Algorithm.policy (by decide : 0 < 2)).normalized 1 observedHistory⟩

noncomputable def observedTrajectory : Trajectory 2 1 :=
  (((), (1 : Fin 2)), fun k => if k = 1 then 1 / 2 else 0)

/-- The virtual terminal rank uses the last observed score and takes no extra sample. -/
theorem observed_terminal_recommendation :
    P1Algorithm.recommendation (by decide : 0 < 2) 1 observedTrajectory = 1 := by
  have hs := P1Algorithm.score_observe_eq (by decide : 0 < 2) 1 observedTrajectory
  have hobs : observe observedTrajectory = observedHistory := rfl
  rw [hobs] at hs
  have ht := P1Algorithm.terminal_first (by decide : 0 < 2) 1 observedTrajectory
  change P1Ranking.order (fun k => P1Algorithm.estimatedCumulative (by decide : 0 < 2)
    1 k observedTrajectory) ⟨0, by decide⟩ = _ at ht
  rw [← hs, observed_order] at ht
  simpa using ht.symm

/-- Distinct bounded reward vectors, with common randomness across arms. -/
noncomputable def lowVector : Fin 2 → ℝ := fun k => if k = 0 then 1 / 8 else 1 / 4
noncomputable def highVector : Fin 2 → ℝ := fun k => if k = 0 then 3 / 8 else 3 / 4
noncomputable def rewardLaw : Measure (Fin 2 → ℝ) :=
  bernoulliMeasure lowVector highVector ArchitectureExamples.half

instance rewardLaw_isProbabilityMeasure : IsProbabilityMeasure rewardLaw := by
  unfold rewardLaw
  infer_instance

theorem rewardLaw_bounds : ∀ᵐ y ∂rewardLaw, ∀ k, 0 ≤ y k ∧ y k ≤ 1 := by
  rw [rewardLaw, bernoulliMeasure_def, ae_add_measure_iff]
  constructor
  · exact Measure.ae_smul_measure
      (StochasticImportanceWeighting.dirac_reward_bounds lowVector (by
        intro k
        fin_cases k <;> norm_num [lowVector])) _
  · exact Measure.ae_smul_measure
      (StochasticImportanceWeighting.dirac_reward_bounds highVector (by
        intro k
        fin_cases k <;> norm_num [highVector])) _

/-- Every arm reward is strictly between zero and one almost surely. -/
theorem rewardLaw_nonbinary : ∀ᵐ y ∂rewardLaw, ∀ k, 0 < y k ∧ y k < 1 := by
  rw [rewardLaw, bernoulliMeasure_def, ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    simpa using (show ∀ k : Fin 2, 0 < lowVector k ∧ lowVector k < 1 by
      intro k
      fin_cases k <;> norm_num [lowVector])
  · apply Measure.ae_smul_measure
    simpa using (show ∀ k : Fin 2, 0 < highVector k ∧ highVector k < 1 by
      intro k
      fin_cases k <;> norm_num [highVector])

theorem rewardLaw_mean (k : Fin 2) :
    StochasticImportanceWeighting.mean rewardLaw k = if k = 0 then 1 / 4 else 1 / 2 := by
  unfold StochasticImportanceWeighting.mean rewardLaw
  rw [integral_bernoulliMeasure]
  fin_cases k <;> norm_num [ArchitectureExamples.half, lowVector, highVector, smul_eq_mul]

/-- This nonbinary stochastic problem has best arm one, not zero. -/
theorem rewardLaw_best : P1StochasticModel.best (by decide : 2 ≤ 2) rewardLaw = 1 := by
  change P1Ranking.order (StochasticImportanceWeighting.mean rewardLaw) ⟨0, by decide⟩ = 1
  rw [P1Ranking.order_first_eq_select]
  apply FiniteMaximizer.select_eq_of_strict
  intro k hk
  fin_cases k <;> norm_num [rewardLaw_mean] at *

theorem rewardLaw_unique : P1StochasticModel.UniqueBest (by decide : 2 ≤ 2) rewardLaw := by
  intro k hk
  rw [rewardLaw_best] at hk ⊢
  fin_cases k <;> norm_num [rewardLaw_mean] at *

/-- The actual P1 theorem holds on the changing table whose best arm is one. -/
theorem changingTwo_adversarial_error_bound :
    P1AdversarialBound.errorProbability (by decide : 0 < 2) UniformExamples.changingTwo 2 ≤
      2 * Real.exp (-(9 : ℝ) / 320) := by
  have h := P1AdversarialBound.p1_adversarial_error_bound (by decide : 2 ≤ 2)
    UniformExamples.changingTwo 2 (fun t _ k => UniformExamples.changingTwo_bounds t k)
    UniformExamples.changingTwo_unique
  norm_num [UniformExamples.changingTwo_complexity, harmonic_two] at h ⊢
  exact h

/-- The actual stochastic P1 theorem admits this correlated nonbinary reward law. -/
theorem nonbinary_stochastic_error_bound (n : ℕ) (hn : 0 < n) :
    P1StochasticEvents.errorProbability (by decide : 2 ≤ 2) rewardLaw n ≤
      2 * (2 : ℝ) ^ 3 * (n : ℝ) * Real.exp (-(n : ℝ) /
        (128 * P1Complexity.optimizedComplexity (by decide : 2 ≤ 2)
          (P1StochasticModel.gap (by decide : 2 ≤ 2) rewardLaw) n hn)) :=
  P1StochasticBound.p1_stochastic_error_bound (by decide : 2 ≤ 2) rewardLaw
    rewardLaw_bounds rewardLaw_unique n hn

/-- The all-positive-horizon corollary also applies to the actual nonbinary example. -/
theorem nonbinary_bob_error_bound (n : ℕ) (hn : 0 < n) :
    P1StochasticEvents.errorProbability (by decide : 2 ≤ 2) rewardLaw n ≤
      2 * (2 : ℝ) ^ 3 * (n : ℝ) * Real.exp (-(n : ℝ) /
        (256 * H_BOB (by decide : 2 ≤ 2)
          (P1StochasticModel.gap (by decide : 2 ≤ 2) rewardLaw) *
            (P1Ranking.harmonicK 2) ^ 2)) :=
  P1Corollary.p1_stochastic_bob_error_bound (by decide : 2 ≤ 2) rewardLaw
    rewardLaw_bounds rewardLaw_unique n hn

end BestOfBothWorlds.P1Examples
