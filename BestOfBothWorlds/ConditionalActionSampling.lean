module

public import BestOfBothWorlds.ConditionalImportanceWeighting

/-! The conditional action probabilities of the one-round kernel, without a sampling floor. -/

@[expose] public section

open MeasureTheory

namespace BestOfBothWorlds.ConditionalActionSampling

variable {K : ℕ}

/-- A finite-action indicator is bounded and integrable under every finite measure. -/
theorem indicator_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (A : Ω → Fin K) (hA : Measurable A) (k : Fin K) :
    Integrable (fun ω => if A ω = k then (1 : ℝ) else 0) μ := by
  apply Integrable.of_bound
    (Measurable.ite (measurableSet_eq_fun hA measurable_const)
      measurable_const measurable_const).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun ω => by
    by_cases h : A ω = k <;> simp [h])

variable {History : Type*} [MeasurableSpace History]
variable (p : History → Fin K → ℝ)
variable (hpos : ∀ h k, 0 < p h k) (hnorm : ∀ h, ∑ k, p h k = 1)
variable (hp : ∀ k, Measurable (fun h => p h k))
variable (μ : Measure History) [IsProbabilityMeasure μ]
variable (ν : Measure (Fin K → ℝ)) [IsProbabilityMeasure ν]

/-- The actual action kernel has the prescribed conditional mass at each arm. -/
theorem conditional_indicator (k : Fin K) :
    (ConditionalImportanceWeighting.jointMeasure p hpos hnorm hp μ ν)[
        (fun z => if ConditionalImportanceWeighting.action z = k then (1 : ℝ) else 0) |
        ConditionalImportanceWeighting.historySigma]
      =ᵐ[ConditionalImportanceWeighting.jointMeasure p hpos hnorm hp μ ν]
        (fun z => p (ConditionalImportanceWeighting.history z) k) := by
  have hpint : Integrable (fun z : ConditionalImportanceWeighting.Outcome History K =>
      p (ConditionalImportanceWeighting.history z) k)
      (ConditionalImportanceWeighting.jointMeasure p hpos hnorm hp μ ν) := by
    apply Integrable.of_bound
      ((hp k).comp ConditionalImportanceWeighting.history_measurable).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall (fun z => by
      simp only [Function.comp_apply]
      rw [Real.norm_eq_abs, abs_of_nonneg (hpos _ k).le]
      exact ImportanceWeighting.probability_le_one p hpos hnorm _ k)
  apply ConditionalImportanceWeighting.condExp_of_fixed_history p hpos hnorm hp μ ν
    (fun z => if ConditionalImportanceWeighting.action z = k then (1 : ℝ) else 0)
    (fun h => p h k)
    (indicator_integrable _ _ ConditionalImportanceWeighting.action_measurable k)
    (fun h => indicator_integrable _ Prod.fst measurable_fst k) (hp k) hpint
  intro h
  change (∫ ay : Fin K × (Fin K → ℝ), (if ay.1 = k then (1 : ℝ) else 0)
    ∂StochasticImportanceWeighting.jointLaw p hpos hnorm ν h) = p h k
  rw [StochasticImportanceWeighting.joint_integral p hpos hnorm ν h _
    (indicator_integrable _ Prod.fst measurable_fst k)]
  simp [ImportanceWeighting.expectation, mul_ite]

end BestOfBothWorlds.ConditionalActionSampling
