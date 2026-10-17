module

public import BestOfBothWorlds.Freedman
public import BestOfBothWorlds.BanditSpecializations
public import BestOfBothWorlds.MathlibInterop

/-!
Bernstein–Freedman bounds for the existing stopped adaptive importance-weighted
process. Future events are restricted under the original law, without conditioning.
Identities that subtract means or table rewards through time `t` require `t ≤ n`.
-/

@[expose] public section

open MeasureTheory
open BestOfBothWorlds.AdaptiveBanditProcess
open BestOfBothWorlds.AdaptiveBanditMoments
open BestOfBothWorlds.BanditMartingales

namespace BestOfBothWorlds.BanditConcentration

section EventUnion

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]

/-- An absolute deviation event is contained in the union of its two signed tails. -/
theorem abs_event_measure_le (M : Ω → ℝ) (E : Set Ω) (x : ℝ) :
    μ.real {ω | ω ∈ E ∧ x ≤ |M ω|} ≤
      μ.real {ω | ω ∈ E ∧ x ≤ M ω} + μ.real {ω | ω ∈ E ∧ M ω ≤ -x} := by
  have hsub : {ω | ω ∈ E ∧ x ≤ |M ω|} ⊆
      {ω | ω ∈ E ∧ x ≤ M ω} ∪ {ω | ω ∈ E ∧ M ω ≤ -x} := by
    intro ω hω
    by_cases hsign : 0 ≤ M ω
    · exact Or.inl ⟨hω.1, by simpa only [abs_of_nonneg hsign] using hω.2⟩
    · exact Or.inr ⟨hω.1, by
        have h := hω.2
        rw [abs_of_neg (lt_of_not_ge hsign)] at h
        linarith⟩
  exact (measureReal_mono hsub).trans (measureReal_union_le _ _)

end EventUnion

section GenericFutureEvent

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {F : Filtration ℕ mΩ} {X v : ℕ → Ω → ℝ} {b : ℝ}

/-- Arbitrary ambient future events have a two-sided bound from AE variance inclusion. -/
theorem difference_two_sided_on_event (h : Freedman.DifferenceSequence μ F X v b)
    (t : ℕ) (x a : ℝ) (hx : 0 ≤ x) (ha : 0 ≤ a) (hden : 0 < a + b * x / 3)
    (E : Set Ω) (hE : MeasurableSet E)
    (hEV : ∀ᵐ ω ∂μ, ω ∈ E → Freedman.partialSum v t ω ≤ a) :
    μ.real {ω | ω ∈ E ∧ x ≤ |Freedman.partialSum X t ω|} ≤
      2 * Real.exp (-x ^ 2 / (2 * (a + b * x / 3))) := by
  calc
    _ ≤ μ.real {ω | ω ∈ E ∧ x ≤ Freedman.partialSum X t ω} +
        μ.real {ω | ω ∈ E ∧ Freedman.partialSum X t ω ≤ -x} :=
      abs_event_measure_le μ _ E x
    _ ≤ Real.exp (-x ^ 2 / (2 * (a + b * x / 3))) +
        Real.exp (-x ^ 2 / (2 * (a + b * x / 3))) :=
      add_le_add (Freedman.upper_tail_on_event h t x a hx ha hden E hE hEV)
        (Freedman.lower_tail_on_event h t x a hx ha hden E hE hEV)
    _ = _ := by ring

end GenericFutureEvent

/-- The adaptive estimation errors explicitly vanish after the fixed horizon. -/
theorem increment_stopped {K : ℕ} (π : Policy K) (ν : ℕ → Measure (Fin K → ℝ))
    (n : ℕ) (k : Fin K) (t : ℕ) (ht : n ≤ t) : increment π ν n k t = 0 := by
  funext z
  simp [increment, importanceWeighted, not_lt_of_ge ht]

/-- The explicit conditional-variance increments also vanish after the horizon. -/
theorem varianceIncrement_stopped {K : ℕ} (π : Policy K)
    (ν : ℕ → Measure (Fin K → ℝ)) (n : ℕ) (k : Fin K) (t : ℕ) (ht : n ≤ t) :
    varianceIncrement π ν n k t = 0 := by
  funext z
  simp [varianceIncrement, not_lt_of_ge ht]

section Adaptive

variable {K : ℕ} (π : Policy K) (ν : ℕ → Measure (Fin K → ℝ))
variable [∀ s, IsProbabilityMeasure (ν s)] (n : ℕ)
variable (hbound : ∀ s < n, ∀ᵐ y ∂ν s, ∀ k, 0 ≤ y k ∧ y k ≤ 1)
variable (ε : ℝ) (hε : 0 < ε) (hfloor : ∀ s < n, ∀ h k, ε ≤ π.prob s h k)

include hbound hε hfloor in
/-- Existing conditional moments instantiate the generic difference-sequence interface. -/
theorem importanceDifferenceSequence (k : Fin K) :
    Freedman.DifferenceSequence (trajectoryLaw π ν n) (historyFiltration n)
      (increment π ν n k) (varianceIncrement π ν n k) (1 / ε) where
  b_nonneg := (one_div_pos.mpr hε).le
  adapted := fun s => increment_stronglyMeasurable π ν n k s
  variance_adapted := fun s => varianceIncrement_stronglyMeasurable π ν n k s
  abs_le := fun s => increment_uniform_bound π ν n hbound ε hε hfloor k s
  mean_zero := fun s => conditional_increment_zero π ν n hbound ε hε hfloor k s
  second_moment := fun s => conditional_increment_square π ν n hbound ε hε hfloor k s

include hbound hε hfloor in
/-- The adaptive upper tail retains the random predictable variance in the joint event. -/
theorem upper_tail (k : Fin K) (t : ℕ) (x a : ℝ)
    (hx : 0 ≤ x) (ha : 0 ≤ a) (hden : 0 < a + (1 / ε) * x / 3) :
    (trajectoryLaw π ν n).real {z | x ≤ cumulativeMartingale π ν n k t z ∧
      predictableVariance π ν n k t z ≤ a} ≤
      Real.exp (-x ^ 2 / (2 * (a + (1 / ε) * x / 3))) := by
  simpa [Freedman.partialSum, cumulativeMartingale, predictableVariance, partialSum] using
    Freedman.upper_tail (importanceDifferenceSequence π ν n hbound ε hε hfloor k) t x a hx ha hden

include hbound hε hfloor in
/-- The lower tail uses the same variance process and Bernstein coefficient. -/
theorem lower_tail (k : Fin K) (t : ℕ) (x a : ℝ)
    (hx : 0 ≤ x) (ha : 0 ≤ a) (hden : 0 < a + (1 / ε) * x / 3) :
    (trajectoryLaw π ν n).real {z | cumulativeMartingale π ν n k t z ≤ -x ∧
      predictableVariance π ν n k t z ≤ a} ≤
      Real.exp (-x ^ 2 / (2 * (a + (1 / ε) * x / 3))) := by
  simpa [Freedman.partialSum, cumulativeMartingale, predictableVariance, partialSum] using
    Freedman.lower_tail (importanceDifferenceSequence π ν n hbound ε hε hfloor k) t x a hx ha hden

include hbound hε hfloor in
/-- An event may depend on the entire trajectory, including observations after `t`. -/
theorem upper_tail_on_event (k : Fin K) (t : ℕ) (x a : ℝ)
    (hx : 0 ≤ x) (ha : 0 ≤ a) (hden : 0 < a + (1 / ε) * x / 3)
    (E : Set (Trajectory K n)) (hE : MeasurableSet E)
    (hEV : ∀ᵐ z ∂trajectoryLaw π ν n, z ∈ E → predictableVariance π ν n k t z ≤ a) :
    (trajectoryLaw π ν n).real {z | z ∈ E ∧ x ≤ cumulativeMartingale π ν n k t z} ≤
      Real.exp (-x ^ 2 / (2 * (a + (1 / ε) * x / 3))) := by
  simpa [Freedman.partialSum, cumulativeMartingale, predictableVariance, partialSum,
    Set.inter_def] using
    Freedman.upper_tail_on_event (importanceDifferenceSequence π ν n hbound ε hε hfloor k)
      t x a hx ha hden E hE hEV

include hbound hε hfloor in
theorem lower_tail_on_event (k : Fin K) (t : ℕ) (x a : ℝ)
    (hx : 0 ≤ x) (ha : 0 ≤ a) (hden : 0 < a + (1 / ε) * x / 3)
    (E : Set (Trajectory K n)) (hE : MeasurableSet E)
    (hEV : ∀ᵐ z ∂trajectoryLaw π ν n, z ∈ E → predictableVariance π ν n k t z ≤ a) :
    (trajectoryLaw π ν n).real {z | z ∈ E ∧ cumulativeMartingale π ν n k t z ≤ -x} ≤
      Real.exp (-x ^ 2 / (2 * (a + (1 / ε) * x / 3))) := by
  simpa [Freedman.partialSum, cumulativeMartingale, predictableVariance, partialSum,
    Set.inter_def] using
    Freedman.lower_tail_on_event (importanceDifferenceSequence π ν n hbound ε hε hfloor k)
      t x a hx ha hden E hE hEV

include hbound hε hfloor in
/-- The two-sided event interface requires only ambient measurability and AE inclusion. -/
theorem two_sided_on_event (k : Fin K) (t : ℕ) (x a : ℝ)
    (hx : 0 ≤ x) (ha : 0 ≤ a) (hden : 0 < a + (1 / ε) * x / 3)
    (E : Set (Trajectory K n)) (hE : MeasurableSet E)
    (hEV : ∀ᵐ z ∂trajectoryLaw π ν n, z ∈ E → predictableVariance π ν n k t z ≤ a) :
    (trajectoryLaw π ν n).real {z | z ∈ E ∧ x ≤ |cumulativeMartingale π ν n k t z|} ≤
      2 * Real.exp (-x ^ 2 / (2 * (a + (1 / ε) * x / 3))) := by
  simpa [Freedman.partialSum, cumulativeMartingale, predictableVariance, partialSum] using
    difference_two_sided_on_event (importanceDifferenceSequence π ν n hbound ε hε hfloor k)
      t x a hx ha hden E hE hEV

include hbound hε hfloor in
/-- The same event interface can consume Mathlib conditional variances of the raw estimates. -/
theorem two_sided_on_condVar_event (k : Fin K) (t : ℕ) (x a : ℝ)
    (hx : 0 ≤ x) (ha : 0 ≤ a) (hden : 0 < a + (1 / ε) * x / 3)
    (E : Set (Trajectory K n)) (hE : MeasurableSet E)
    (hEV : ∀ᵐ z ∂trajectoryLaw π ν n, z ∈ E →
      (∑ s ∈ Finset.range t,
        ProbabilityTheory.condVar (historyFiltration n s) (importanceWeighted π n k s)
          (trajectoryLaw π ν n)) z ≤ a) :
    (trajectoryLaw π ν n).real {z | z ∈ E ∧ x ≤ |cumulativeMartingale π ν n k t z|} ≤
      2 * Real.exp (-x ^ 2 / (2 * (a + (1 / ε) * x / 3))) := by
  apply two_sided_on_event π ν n hbound ε hε hfloor k t x a hx ha hden E hE
  filter_upwards [hEV,
    MathlibInterop.predictableVariance_eq_sum_condVar_estimator π ν n hbound ε hε hfloor k t]
    with z hz heq
  intro hzE
  rw [heq]
  exact hz hzE

end Adaptive

section Stochastic

variable {K : ℕ} (π : Policy K) (ν : Measure (Fin K → ℝ)) [IsProbabilityMeasure ν]
variable (n : ℕ) (hbound : ∀ᵐ y ∂ν, ∀ k, 0 ≤ y k ∧ y k ≤ 1)
variable (ε : ℝ) (hε : 0 < ε) (hfloor : ∀ s < n, ∀ h k, ε ≤ π.prob s h k)

include hbound hε hfloor in
/-- Stationary bounded reward vectors give the estimate-minus-time-times-mean upper tail. -/
theorem stochastic_upper_tail (k : Fin K) (t : ℕ) (ht : t ≤ n) (x a : ℝ)
    (hx : 0 ≤ x) (ha : 0 ≤ a) (hden : 0 < a + (1 / ε) * x / 3) :
    (trajectoryLaw π (fun _ => ν) n).real {z |
      x ≤ cumulativeEstimate π n k t z - (t : ℝ) * StochasticImportanceWeighting.mean ν k ∧
      predictableVariance π (fun _ => ν) n k t z ≤ a} ≤
      Real.exp (-x ^ 2 / (2 * (a + (1 / ε) * x / 3))) := by
  let : ∀ _s : ℕ, IsProbabilityMeasure ν := fun _ => inferInstance
  simpa only [BanditSpecializations.stochastic_cumulative_identity π ν n k t ht] using
    upper_tail π (fun _ => ν) n (fun _ _ => hbound) ε hε hfloor k t x a hx ha hden

include hbound hε hfloor in
theorem stochastic_lower_tail (k : Fin K) (t : ℕ) (ht : t ≤ n) (x a : ℝ)
    (hx : 0 ≤ x) (ha : 0 ≤ a) (hden : 0 < a + (1 / ε) * x / 3) :
    (trajectoryLaw π (fun _ => ν) n).real {z |
      cumulativeEstimate π n k t z - (t : ℝ) * StochasticImportanceWeighting.mean ν k ≤ -x ∧
      predictableVariance π (fun _ => ν) n k t z ≤ a} ≤
      Real.exp (-x ^ 2 / (2 * (a + (1 / ε) * x / 3))) := by
  let : ∀ _s : ℕ, IsProbabilityMeasure ν := fun _ => inferInstance
  simpa only [BanditSpecializations.stochastic_cumulative_identity π ν n k t ht] using
    lower_tail π (fun _ => ν) n (fun _ _ => hbound) ε hε hfloor k t x a hx ha hden

include hbound hε hfloor in
theorem stochastic_two_sided_on_event (k : Fin K) (t : ℕ) (ht : t ≤ n) (x a : ℝ)
    (hx : 0 ≤ x) (ha : 0 ≤ a) (hden : 0 < a + (1 / ε) * x / 3)
    (E : Set (Trajectory K n)) (hE : MeasurableSet E)
    (hEV : ∀ᵐ z ∂trajectoryLaw π (fun _ => ν) n, z ∈ E →
      predictableVariance π (fun _ => ν) n k t z ≤ a) :
    (trajectoryLaw π (fun _ => ν) n).real {z | z ∈ E ∧
      x ≤ |cumulativeEstimate π n k t z - (t : ℝ) * StochasticImportanceWeighting.mean ν k|} ≤
      2 * Real.exp (-x ^ 2 / (2 * (a + (1 / ε) * x / 3))) := by
  let : ∀ _s : ℕ, IsProbabilityMeasure ν := fun _ => inferInstance
  simpa only [BanditSpecializations.stochastic_cumulative_identity π ν n k t ht] using
    two_sided_on_event π (fun _ => ν) n (fun _ _ => hbound) ε hε hfloor
      k t x a hx ha hden E hE hEV

end Stochastic

section FixedTable

variable {K : ℕ} (π : Policy K) (g : ℕ → Fin K → ℝ) (n : ℕ)
variable (hg : ∀ s < n, ∀ k, 0 ≤ g s k ∧ g s k ≤ 1)
variable (ε : ℝ) (hε : 0 < ε) (hfloor : ∀ s < n, ∀ h k, ε ≤ π.prob s h k)

include hg hε hfloor in
/-- Fixed oblivious reward tables use the already constructed Dirac environment. -/
theorem fixedTable_upper_tail (k : Fin K) (t : ℕ) (ht : t ≤ n) (x a : ℝ)
    (hx : 0 ≤ x) (ha : 0 ≤ a) (hden : 0 < a + (1 / ε) * x / 3) :
    (trajectoryLaw π (fun s => Measure.dirac (g s)) n).real {z |
      x ≤ cumulativeEstimate π n k t z - ∑ s ∈ Finset.range t, g s k ∧
      predictableVariance π (fun s => Measure.dirac (g s)) n k t z ≤ a} ≤
      Real.exp (-x ^ 2 / (2 * (a + (1 / ε) * x / 3))) := by
  let : ∀ s, IsProbabilityMeasure (Measure.dirac (g s)) := fun _ => inferInstance
  simpa only [BanditSpecializations.fixedTable_cumulative_identity π g n k t ht] using
    upper_tail π (fun s => Measure.dirac (g s)) n
      (fun s hs => StochasticImportanceWeighting.dirac_reward_bounds (g s) (hg s hs))
      ε hε hfloor k t x a hx ha hden

include hg hε hfloor in
theorem fixedTable_lower_tail (k : Fin K) (t : ℕ) (ht : t ≤ n) (x a : ℝ)
    (hx : 0 ≤ x) (ha : 0 ≤ a) (hden : 0 < a + (1 / ε) * x / 3) :
    (trajectoryLaw π (fun s => Measure.dirac (g s)) n).real {z |
      cumulativeEstimate π n k t z - ∑ s ∈ Finset.range t, g s k ≤ -x ∧
      predictableVariance π (fun s => Measure.dirac (g s)) n k t z ≤ a} ≤
      Real.exp (-x ^ 2 / (2 * (a + (1 / ε) * x / 3))) := by
  let : ∀ s, IsProbabilityMeasure (Measure.dirac (g s)) := fun _ => inferInstance
  simpa only [BanditSpecializations.fixedTable_cumulative_identity π g n k t ht] using
    lower_tail π (fun s => Measure.dirac (g s)) n
      (fun s hs => StochasticImportanceWeighting.dirac_reward_bounds (g s) (hg s hs))
      ε hε hfloor k t x a hx ha hden

include hg hε hfloor in
theorem fixedTable_two_sided_on_event (k : Fin K) (t : ℕ) (ht : t ≤ n) (x a : ℝ)
    (hx : 0 ≤ x) (ha : 0 ≤ a) (hden : 0 < a + (1 / ε) * x / 3)
    (E : Set (Trajectory K n)) (hE : MeasurableSet E)
    (hEV : ∀ᵐ z ∂trajectoryLaw π (fun s => Measure.dirac (g s)) n, z ∈ E →
      predictableVariance π (fun s => Measure.dirac (g s)) n k t z ≤ a) :
    (trajectoryLaw π (fun s => Measure.dirac (g s)) n).real {z | z ∈ E ∧
      x ≤ |cumulativeEstimate π n k t z - ∑ s ∈ Finset.range t, g s k|} ≤
      2 * Real.exp (-x ^ 2 / (2 * (a + (1 / ε) * x / 3))) := by
  let : ∀ s, IsProbabilityMeasure (Measure.dirac (g s)) := fun _ => inferInstance
  simpa only [BanditSpecializations.fixedTable_cumulative_identity π g n k t ht] using
    two_sided_on_event π (fun s => Measure.dirac (g s)) n
      (fun s hs => StochasticImportanceWeighting.dirac_reward_bounds (g s) (hg s hs))
      ε hε hfloor k t x a hx ha hden E hE hEV

end FixedTable

end BestOfBothWorlds.BanditConcentration
