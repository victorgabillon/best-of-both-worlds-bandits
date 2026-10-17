module

public import BestOfBothWorlds.AdaptiveBanditMoments
public import Mathlib.Probability.Martingale.Basic

/-!
Finite cumulative sums turn the adaptive process's proved one-step moments into
martingales, predictable variance processes, and compensated pull counts.
The concrete process applications below use its natural observed-history filtration.
-/

@[expose] public section

open MeasureTheory

namespace BestOfBothWorlds.BanditMartingales

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {ℱ : Filtration ℕ mΩ}

/-- Sum the increments from rounds `0` through `t - 1`. -/
noncomputable def partialSum (d : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  ∑ s ∈ Finset.range t, d s

@[simp] theorem partialSum_zero (d : ℕ → Ω → ℝ) : partialSum d 0 = 0 := by
  simp [partialSum]

@[simp] theorem partialSum_succ_sub (d : ℕ → Ω → ℝ) (t : ℕ) :
    partialSum d (t + 1) - partialSum d t = d t := by
  simp [partialSum, Finset.sum_range_succ]

theorem partialSum_integrable (d : ℕ → Ω → ℝ) (hd : ∀ s, Integrable (d s) μ) (t : ℕ) :
    Integrable (partialSum d t) μ :=
  integrable_finsetSum' _ (fun s _ => hd s)

theorem partialSum_stronglyAdapted (d : ℕ → Ω → ℝ)
    (hd : ∀ s, StronglyMeasurable[ℱ (s + 1)] (d s)) : StronglyAdapted ℱ (partialSum d) := by
  intro t
  apply Finset.stronglyMeasurable_sum
  intro s hs
  exact (hd s).mono (ℱ.mono (Nat.succ_le_of_lt (Finset.mem_range.mp hs)))

/-- Next-round observable, integrable, conditionally centered increments give a martingale. -/
theorem partialSum_martingale [IsFiniteMeasure μ] (d : ℕ → Ω → ℝ)
    (hd : ∀ s, StronglyMeasurable[ℱ (s + 1)] (d s))
    (hi : ∀ s, Integrable (d s) μ)
    (hc : ∀ s, μ[d s | ℱ s] =ᵐ[μ] (0 : Ω → ℝ)) :
    Martingale (partialSum d) ℱ μ := by
  apply martingale_of_condExp_sub_eq_zero_nat (partialSum_stronglyAdapted d hd)
    (partialSum_integrable d hi)
  intro s
  rw [partialSum_succ_sub]
  exact hc s

theorem partialSum_integral_zero [IsFiniteMeasure μ] (d : ℕ → Ω → ℝ)
    (hm : Martingale (partialSum d) ℱ μ) (t : ℕ) : ∫ ω, partialSum d t ω ∂μ = 0 := by
  have h := hm.setIntegral_eq (i := 0) (j := t) (Nat.zero_le t) MeasurableSet.univ
  simpa using h.symm

/-- The sum through round `t` is known at time `t`, as required for predictability. -/
theorem predictable_partialSum (v : ℕ → Ω → ℝ)
    (hv : ∀ s, StronglyMeasurable[ℱ s] (v s)) :
    IsStronglyPredictable ℱ (partialSum v) := by
  apply IsStronglyPredictable.of_measurable_add_one
  · rw [partialSum_zero]
    exact stronglyMeasurable_zero
  · intro t
    apply Finset.stronglyMeasurable_sum
    intro s hs
    exact (hv s).mono (ℱ.mono (Nat.le_of_lt_succ (Finset.mem_range.mp hs)))

theorem partialSum_sub (f g : ℕ → Ω → ℝ) (t : ℕ) :
    partialSum (fun s => f s - g s) t = partialSum f t - partialSum g t := by
  simp [partialSum, Finset.sum_sub_distrib]

/-- Subtracting the predictable sampling probabilities compensates the pull indicators. -/
theorem compensated_partialSum_martingale [IsFiniteMeasure μ] (I p : ℕ → Ω → ℝ)
    (hI : ∀ s, StronglyMeasurable[ℱ (s + 1)] (I s))
    (hp : ∀ s, StronglyMeasurable[ℱ s] (p s))
    (hIi : ∀ s, Integrable (I s) μ) (hpi : ∀ s, Integrable (p s) μ)
    (hce : ∀ s, μ[I s | ℱ s] =ᵐ[μ] p s) :
    Martingale (partialSum (fun s => I s - p s)) ℱ μ := by
  apply partialSum_martingale
  · intro s
    exact (hI s).sub ((hp s).mono (ℱ.mono (Nat.le_succ s)))
  · exact fun s => (hIi s).sub (hpi s)
  · intro s
    have hsub := condExp_sub (hIi s) (hpi s) (ℱ s)
    rw [condExp_of_stronglyMeasurable (ℱ.le s) (hp s) (hpi s)] at hsub
    filter_upwards [hsub, hce s] with ω hω hmean
    simpa only [Pi.sub_apply, Pi.zero_apply, hmean, sub_self] using hω

theorem compensated_expected_counts [IsFiniteMeasure μ] (I p : ℕ → Ω → ℝ)
    (hI : ∀ s, StronglyMeasurable[ℱ (s + 1)] (I s))
    (hp : ∀ s, StronglyMeasurable[ℱ s] (p s))
    (hIi : ∀ s, Integrable (I s) μ) (hpi : ∀ s, Integrable (p s) μ)
    (hce : ∀ s, μ[I s | ℱ s] =ᵐ[μ] p s) (t : ℕ) :
    (∫ ω, partialSum I t ω ∂μ) = ∫ ω, partialSum p t ω ∂μ := by
  have hzero := partialSum_integral_zero (fun s => I s - p s)
    (compensated_partialSum_martingale I p hI hp hIi hpi hce) t
  rw [partialSum_sub] at hzero
  simp only [Pi.sub_apply] at hzero
  rw [integral_sub (partialSum_integrable I hIi t) (partialSum_integrable p hpi t)] at hzero
  exact sub_eq_zero.mp hzero

theorem partialSum_conditional_square (d v : ℕ → Ω → ℝ)
    (hce : ∀ s, μ[(fun ω => (d s ω)^2) | ℱ s] =ᵐ[μ] v s) (t : ℕ) :
    partialSum v t =ᵐ[μ] ∑ s ∈ Finset.range t, μ[(fun ω => (d s ω)^2) | ℱ s] := by
  exact eventuallyEq_sum (fun s _ => (hce s).symm)

theorem partialSum_stopped_eq (d : ℕ → Ω → ℝ) (n t : ℕ) (ht : t ≤ n) :
    partialSum (fun s => if s < n then d s else 0) t = partialSum d t := by
  unfold partialSum
  apply Finset.sum_congr rfl
  intro s hs
  exact ite_eq_left (lt_of_lt_of_le (Finset.mem_range.mp hs) ht)

theorem partialSum_const (c : ℝ) (t : ℕ) :
    partialSum (fun (_ : ℕ) (_ : Ω) => c) t = fun _ => (t : ℝ) * c := by
  ext ω
  simp [partialSum]

theorem partialSum_stopped_const (c : ℝ) (n t : ℕ) (ht : t ≤ n) :
    partialSum (fun s => if s < n then (fun _ : Ω => c) else 0) t =
      fun _ => (t : ℝ) * c := by
  rw [partialSum_stopped_eq _ n t ht, partialSum_const]


section AdaptiveProcess

open AdaptiveBanditProcess AdaptiveBanditMoments

variable {K : ℕ}

/-- The importance-weighted reward accumulated before time `t`. -/
noncomputable def cumulativeEstimate (π : Policy K) (n : ℕ) (k : Fin K) :
    ℕ → Trajectory K n → ℝ := partialSum (importanceWeighted π n k)

/-- The accumulated centered estimation error, stopped after the horizon. -/
noncomputable def cumulativeMartingale (π : Policy K)
    (ν : ℕ → Measure (Fin K → ℝ)) (n : ℕ) (k : Fin K) :
    ℕ → Trajectory K n → ℝ := partialSum (increment π ν n k)

/-- The accumulated conditional second moments of the centered increments. -/
noncomputable def predictableVariance (π : Policy K)
    (ν : ℕ → Measure (Fin K → ℝ)) (n : ℕ) (k : Fin K) :
    ℕ → Trajectory K n → ℝ := partialSum (varianceIncrement π ν n k)

/-- A real-valued count of the actual pulls before time `t`. -/
noncomputable def pullCount (n : ℕ) (k : Fin K) : ℕ → Trajectory K n → ℝ :=
  partialSum (pullIndicator n k)

/-- The sum of the history-dependent probabilities of pulling the arm. -/
noncomputable def expectedPullCount (π : Policy K) (n : ℕ) (k : Fin K) :
    ℕ → Trajectory K n → ℝ := partialSum (samplingProbability π n k)

/-- Actual pulls minus their predictable compensator. -/
noncomputable def compensatedPullCount (π : Policy K) (n : ℕ) (k : Fin K) (t : ℕ) :
    Trajectory K n → ℝ := pullCount n k t - expectedPullCount π n k t

@[simp] theorem cumulativeMartingale_zero (π : Policy K)
    (ν : ℕ → Measure (Fin K → ℝ)) (n : ℕ) (k : Fin K) :
    cumulativeMartingale π ν n k 0 = 0 := partialSum_zero _

theorem cumulativeMartingale_succ_sub (π : Policy K)
    (ν : ℕ → Measure (Fin K → ℝ)) (n : ℕ) (k : Fin K) (t : ℕ) :
    cumulativeMartingale π ν n k (t+1) - cumulativeMartingale π ν n k t =
      increment π ν n k t := partialSum_succ_sub _ _

@[simp] theorem predictableVariance_zero (π : Policy K)
    (ν : ℕ → Measure (Fin K → ℝ)) (n : ℕ) (k : Fin K) :
    predictableVariance π ν n k 0 = 0 := partialSum_zero _

theorem predictableVariance_succ_sub (π : Policy K)
    (ν : ℕ → Measure (Fin K → ℝ)) (n : ℕ) (k : Fin K) (t : ℕ) :
    predictableVariance π ν n k (t+1) - predictableVariance π ν n k t =
      varianceIncrement π ν n k t := partialSum_succ_sub _ _

/-- Cumulative estimation error equals estimated gain minus the sum of true means. -/
theorem cumulativeMartingale_eq_estimate_sub_means (π : Policy K)
    (ν : ℕ → Measure (Fin K → ℝ)) (n : ℕ) (k : Fin K) (t : ℕ) (ht : t ≤ n)
    (z : Trajectory K n) :
    cumulativeMartingale π ν n k t z = cumulativeEstimate π n k t z -
      ∑ s ∈ Finset.range t, StochasticImportanceWeighting.mean (ν s) k := by
  simp only [cumulativeMartingale, cumulativeEstimate, partialSum, Finset.sum_apply, increment]
  rw [Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  exact ite_eq_left (lt_of_lt_of_le (Finset.mem_range.mp hs) ht)

theorem pullCount_stronglyAdapted (n : ℕ) (k : Fin K) :
    StronglyAdapted (historyFiltration n) (pullCount n k) :=
  partialSum_stronglyAdapted _ (fun s => pullIndicator_stronglyMeasurable n k s)

/-- The count compensator through round `t` is already known at time `t`. -/
theorem expectedPullCount_predictable (π : Policy K) (n : ℕ) (k : Fin K) :
    IsStronglyPredictable (historyFiltration n) (expectedPullCount π n k) :=
  predictable_partialSum _ (fun s => samplingProbability_stronglyMeasurable π n k s)

variable (π : Policy K) (ν : ℕ → Measure (Fin K → ℝ))
variable [∀ s, IsProbabilityMeasure (ν s)] (n : ℕ)
variable (hbound : ∀ s < n, ∀ᵐ y ∂ν s, ∀ k, 0 ≤ y k ∧ y k ≤ 1)
variable (ε : ℝ) (hε : 0 < ε) (hfloor : ∀ s < n, ∀ h k, ε ≤ π.prob s h k)

include hbound hε hfloor in
/-- The cumulative importance-weighted estimation error is an actual martingale. -/
theorem cumulativeMartingale_martingale (k : Fin K) :
    Martingale (cumulativeMartingale π ν n k) (historyFiltration n) (trajectoryLaw π ν n) := by
  apply partialSum_martingale
  · exact fun s => increment_stronglyMeasurable π ν n k s
  · exact fun s => increment_integrable π ν n hbound ε hε hfloor k s
  · exact fun s => conditional_increment_zero π ν n hbound ε hε hfloor k s

include hbound hε hfloor in
theorem cumulativeMartingale_integrable (k : Fin K) (t : ℕ) :
    Integrable (cumulativeMartingale π ν n k t) (trajectoryLaw π ν n) :=
  (cumulativeMartingale_martingale π ν n hbound ε hε hfloor k).integrable t

omit [∀ s, IsProbabilityMeasure (ν s)] in
theorem cumulativeMartingale_stronglyMeasurable (k : Fin K) (t : ℕ) :
    StronglyMeasurable[historyFiltration n t] (cumulativeMartingale π ν n k t) :=
  partialSum_stronglyAdapted _ (fun s => increment_stronglyMeasurable π ν n k s) t

include hbound hε hfloor in
/-- The full martingale identity holds for all earlier and later stopped times. -/
theorem cumulativeMartingale_condExp (k : Fin K) {t u : ℕ} (htu : t ≤ u) :
    (trajectoryLaw π ν n)[cumulativeMartingale π ν n k u | historyFiltration n t]
      =ᵐ[trajectoryLaw π ν n] cumulativeMartingale π ν n k t :=
  (cumulativeMartingale_martingale π ν n hbound ε hε hfloor k).condExp_ae_eq htu

omit [∀ s, IsProbabilityMeasure (ν s)] in
/-- In discrete time, `V (t+1)` is measurable before drawing round `t`. -/
theorem predictableVariance_predictable (k : Fin K) :
    IsStronglyPredictable (historyFiltration n) (predictableVariance π ν n k) :=
  predictable_partialSum _ (fun s => varianceIncrement_stronglyMeasurable π ν n k s)

include hbound in
theorem predictableVariance_nonneg (k : Fin K) (t : ℕ) (z : Trajectory K n) :
    0 ≤ predictableVariance π ν n k t z := by
  unfold predictableVariance partialSum
  rw [Finset.sum_apply]
  exact Finset.sum_nonneg (fun s _ => (varianceIncrement_bounds π ν n hbound k s z).1)

include hbound in
theorem predictableVariance_le_reciprocalSum (k : Fin K) (t : ℕ) (z : Trajectory K n) :
    predictableVariance π ν n k t z ≤ partialSum (reciprocalProbability π n k) t z := by
  unfold predictableVariance partialSum
  rw [Finset.sum_apply, Finset.sum_apply]
  exact Finset.sum_le_sum (fun s _ => (varianceIncrement_bounds π ν n hbound k s z).2)

include hbound hε hfloor in
theorem predictableVariance_uniform_bound (k : Fin K) (t : ℕ) (z : Trajectory K n) :
    predictableVariance π ν n k t z ≤ (t : ℝ) / ε := by
  calc
    predictableVariance π ν n k t z ≤ partialSum (reciprocalProbability π n k) t z :=
      predictableVariance_le_reciprocalSum π ν n hbound k t z
    _ ≤ ∑ _s ∈ Finset.range t, 1 / ε := by
      unfold partialSum
      rw [Finset.sum_apply]
      exact Finset.sum_le_sum (fun s _ => reciprocalProbability_uniform_bound π n ε hε hfloor k s z)
    _ = (t : ℝ) / ε := by simp [div_eq_mul_inv]

include hbound hε hfloor in
/-- The explicit predictable variance is the sum of the proved conditional moments. -/
theorem predictableVariance_eq_sum_condExp (k : Fin K) (t : ℕ) :
    predictableVariance π ν n k t =ᵐ[trajectoryLaw π ν n]
      ∑ s ∈ Finset.range t, (trajectoryLaw π ν n)[(fun z => (increment π ν n k s z)^2) |
        historyFiltration n s] :=
  partialSum_conditional_square _ _
    (fun s => conditional_increment_square π ν n hbound ε hε hfloor k s) t

theorem pullCount_integrable (k : Fin K) (t : ℕ) :
    Integrable (pullCount n k t) (trajectoryLaw π ν n) :=
  partialSum_integrable _ (fun s => pullIndicator_integrable π ν n k s) t

theorem expectedPullCount_integrable (k : Fin K) (t : ℕ) :
    Integrable (expectedPullCount π n k t) (trajectoryLaw π ν n) :=
  partialSum_integrable _ (fun s => samplingProbability_integrable π ν n k s) t

/-- Compensated pull counts need no reward support or inverse-probability floor. -/
theorem compensatedPullCount_martingale (k : Fin K) :
    Martingale (compensatedPullCount π n k) (historyFiltration n) (trajectoryLaw π ν n) := by
  have hm := compensated_partialSum_martingale (pullIndicator n k) (samplingProbability π n k)
    (fun s => pullIndicator_stronglyMeasurable n k s)
    (fun s => samplingProbability_stronglyMeasurable π n k s)
    (fun s => pullIndicator_integrable π ν n k s)
    (fun s => samplingProbability_integrable π ν n k s)
    (fun s => conditional_pullIndicator π ν n k s)
  have heq : partialSum (fun s => pullIndicator n k s - samplingProbability π n k s) =
      compensatedPullCount π n k := by
    funext t
    exact partialSum_sub _ _ t
  rw [heq] at hm
  exact hm

/-- The expected actual number of pulls equals its predictable expected count. -/
theorem pullCount_integral_eq (k : Fin K) (t : ℕ) :
    (∫ z, pullCount n k t z ∂trajectoryLaw π ν n) =
      ∫ z, expectedPullCount π n k t z ∂trajectoryLaw π ν n :=
  compensated_expected_counts (pullIndicator n k) (samplingProbability π n k)
    (fun s => pullIndicator_stronglyMeasurable n k s)
    (fun s => samplingProbability_stronglyMeasurable π n k s)
    (fun s => pullIndicator_integrable π ν n k s)
    (fun s => samplingProbability_integrable π ν n k s)
    (fun s => conditional_pullIndicator π ν n k s) t

end AdaptiveProcess

end BestOfBothWorlds.BanditMartingales
