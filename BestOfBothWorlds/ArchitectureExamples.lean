module

public import BestOfBothWorlds.BanditSpecializations
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Tactic.NormNum

/-!
Concrete witnesses that the observed-history policy interface is inhabited and adaptive.
The two arms receive a common fresh reward of either 1/4 or 3/4, each with probability
1/2. The next action probabilities change with the last observed reward. Correlation
between reward coordinates is intentional and permitted by the general model.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open BestOfBothWorlds.AdaptiveBanditProcess

namespace BestOfBothWorlds.ArchitectureExamples

/-- A nonuniform policy switches its preference according to the last observed reward. -/
noncomputable def adaptiveProb : (t : ℕ) → ObservedHistory 2 t → Fin 2 → ℝ
  | 0, _, k => if k = 0 then 3 / 4 else 1 / 4
  | _t + 1, h, k => if h.2.2 ≤ 1 / 2 then
      (if k = 0 then 1 / 4 else 3 / 4)
    else (if k = 0 then 3 / 4 else 1 / 4)

noncomputable def adaptivePolicy : Policy 2 where
  prob := adaptiveProb
  measurable_prob := by
    intro t k
    cases t with
    | zero => exact measurable_const
    | succ t =>
      exact Measurable.ite
        (measurableSet_le (measurable_snd.comp measurable_snd) measurable_const)
        measurable_const measurable_const
  positive := by
    intro t h k
    cases t <;> simp only [adaptiveProb] <;> split_ifs <;> norm_num
  normalized := by
    intro t h
    cases t with
    | zero => norm_num [adaptiveProb, Fin.sum_univ_two]
    | succ t =>
      by_cases hr : h.2.2 ≤ 1 / 2 <;>
        norm_num [adaptiveProb, Fin.sum_univ_two, hr]

/-- This explicit policy has the deterministic floor used by the upper-bound model. -/
theorem adaptivePolicy_floor (t : ℕ) (h : ObservedHistory 2 t) (k : Fin 2) :
    (1 / 4 : ℝ) ≤ adaptivePolicy.prob t h k := by
  change (1 / 4 : ℝ) ≤ adaptiveProb t h k
  cases t <;> simp only [adaptiveProb] <;> split_ifs <;> norm_num

noncomputable def lowHistory : ObservedHistory 2 1 := ((), (0, 1 / 4))
noncomputable def highHistory : ObservedHistory 2 1 := ((), (0, 3 / 4))

/-- The probabilities genuinely change with observed rewards, and are not uniform. -/
theorem adaptivePolicy_changes_with_reward :
    adaptivePolicy.prob 1 lowHistory 0 = 1 / 4 ∧
    adaptivePolicy.prob 1 highHistory 0 = 3 / 4 ∧
    adaptivePolicy.prob 1 lowHistory 0 ≠ adaptivePolicy.prob 1 highHistory 0 := by
  norm_num [adaptivePolicy, adaptiveProb, lowHistory, highHistory]

noncomputable def lowVector : Fin 2 → ℝ := fun _ => 1 / 4
noncomputable def highVector : Fin 2 → ℝ := fun _ => 3 / 4

noncomputable def half : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩

/-- A nondegenerate bounded law; its coordinates are dependent and are not 0/1-valued. -/
noncomputable def rewardLaw : Measure (Fin 2 → ℝ) :=
  bernoulliMeasure lowVector highVector half

instance rewardLaw_isProbabilityMeasure : IsProbabilityMeasure rewardLaw := by
  unfold rewardLaw
  infer_instance

theorem lowVector_ne_highVector : lowVector ≠ highVector := by
  intro h
  have he := congrFun h (0 : Fin 2)
  norm_num [lowVector, highVector] at he

theorem rewardLaw_low_mass : rewardLaw.real {lowVector} = 1 / 2 := by
  unfold rewardLaw
  have h := bernoulliMeasure_real_apply_of_mem_of_notMem
    (x := lowVector) (y := highVector) half (measurableSet_singleton lowVector)
    (by simp) (by simpa using lowVector_ne_highVector.symm)
  norm_num [half] at h ⊢
  exact h

theorem rewardLaw_high_mass : rewardLaw.real {highVector} = 1 / 2 := by
  unfold rewardLaw
  have h := bernoulliMeasure_real_apply_of_notMem_of_mem
    (x := lowVector) (y := highVector) half (measurableSet_singleton highVector)
    (by simpa using lowVector_ne_highVector) (by simp)
  norm_num [half] at h ⊢
  exact h

theorem rewardLaw_bounds : ∀ᵐ y ∂rewardLaw, ∀ k, 0 ≤ y k ∧ y k ≤ 1 := by
  rw [rewardLaw, bernoulliMeasure_def, ae_add_measure_iff]
  constructor
  · exact Measure.ae_smul_measure
      (StochasticImportanceWeighting.dirac_reward_bounds lowVector
        (by intro k; norm_num [lowVector])) _
  · exact Measure.ae_smul_measure
      (StochasticImportanceWeighting.dirac_reward_bounds highVector
        (by intro k; norm_num [highVector])) _

theorem rewardLaw_mean (k : Fin 2) : StochasticImportanceWeighting.mean rewardLaw k = 1 / 2 := by
  unfold StochasticImportanceWeighting.mean rewardLaw
  rw [integral_bernoulliMeasure]
  norm_num [half, lowVector, highVector, smul_eq_mul]

theorem rewardLaw_secondMoment (k : Fin 2) :
    StochasticImportanceWeighting.secondMoment rewardLaw k = 5 / 16 := by
  unfold StochasticImportanceWeighting.secondMoment rewardLaw
  rw [integral_bernoulliMeasure]
  norm_num [half, lowVector, highVector, smul_eq_mul]

/-- For every finite horizon this explicit adaptive model is a probability space. -/
theorem adaptiveLaw_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (trajectoryLaw adaptivePolicy (fun _ => rewardLaw) n) :=
  inferInstance

/-- Both reward atoms really occur under the constructed trajectory law. -/
theorem adaptiveLaw_reward_atom (n t : ℕ) (ht : t < n) (y : Fin 2 → ℝ) :
    (trajectoryLaw adaptivePolicy (fun _ => rewardLaw) n).real
      {z | roundRewardVector t n ht z = y} = rewardLaw.real {y} := by
  have hmp := round_reward_measurePreserving adaptivePolicy (fun _ => rewardLaw) ht
  have hm : (trajectoryLaw adaptivePolicy (fun _ => rewardLaw) n)
      {z | roundRewardVector t n ht z = y} = rewardLaw {y} := by
    calc
      _ = ((trajectoryLaw adaptivePolicy (fun _ => rewardLaw) n).map
          (roundRewardVector t n ht)) {y} :=
        (Measure.map_apply hmp.measurable (measurableSet_singleton y)).symm
      _ = _ := congrArg (fun μ => μ {y}) hmp.map_eq
  simp only [measureReal_def, hm]

/-- A genuine cumulative martingale for a concrete nonuniform adaptive learner. -/
theorem adaptive_stochastic_martingale (n : ℕ) (k : Fin 2) :
    Martingale (BanditMartingales.cumulativeMartingale adaptivePolicy (fun _ => rewardLaw) n k)
      (historyFiltration n) (trajectoryLaw adaptivePolicy (fun _ => rewardLaw) n) :=
  BanditSpecializations.stochastic_martingale adaptivePolicy rewardLaw n rewardLaw_bounds
    (1 / 4) (by norm_num) (fun t _ h k => adaptivePolicy_floor t h k) k

/-- A deterministic, time-varying oblivious reward table for the same adaptive learner. -/
noncomputable def fixedTable (t : ℕ) (k : Fin 2) : ℝ :=
  if t % 2 = 0 then (if k = 0 then 1 / 4 else 3 / 4)
  else (if k = 0 then 3 / 4 else 1 / 4)

theorem fixedTable_bounds (t : ℕ) (k : Fin 2) :
    0 ≤ fixedTable t k ∧ fixedTable t k ≤ 1 := by
  unfold fixedTable
  split_ifs <;> norm_num

/-- The same concrete learner also has a martingale under fixed oblivious rewards. -/
theorem adaptive_fixedTable_martingale (n : ℕ) (k : Fin 2) :
    Martingale (BanditMartingales.cumulativeMartingale adaptivePolicy
      (fun t => Measure.dirac (fixedTable t)) n k) (historyFiltration n)
      (trajectoryLaw adaptivePolicy (fun t => Measure.dirac (fixedTable t)) n) :=
  BanditSpecializations.fixedTable_martingale adaptivePolicy fixedTable n
    (fun t _ k => fixedTable_bounds t k) (1 / 4) (by norm_num)
    (fun t _ h k => adaptivePolicy_floor t h k) k

end BestOfBothWorlds.ArchitectureExamples
