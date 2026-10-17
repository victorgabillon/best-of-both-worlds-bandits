module

public import BestOfBothWorlds.BanditMartingales
public import Mathlib.Probability.CondVar
public import Mathlib.Probability.Martingale.Centering

/-!
Bridges from the finite bandit process to Mathlib's conditional variance and
Doob centering. These preserve the Step 18D definitions and proofs. Equalities
with conditional expectations are almost-everywhere equalities, as in Mathlib.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open BestOfBothWorlds.AdaptiveBanditProcess
open BestOfBothWorlds.AdaptiveBanditMoments
open BestOfBothWorlds.BanditMartingales

namespace BestOfBothWorlds.MathlibInterop

variable {K : ℕ} (π : Policy K) (ν : ℕ → Measure (Fin K → ℝ))
variable [∀ s, IsProbabilityMeasure (ν s)] (n : ℕ)
variable (hbound : ∀ s < n, ∀ᵐ y ∂ν s, ∀ k, 0 ≤ y k ∧ y k ≤ 1)
variable (ε : ℝ) (hε : 0 < ε) (hfloor : ∀ s < n, ∀ h k, ε ≤ π.prob s h k)

include hbound hε hfloor in
/-- The explicit centered variance is Mathlib's conditional variance. -/
theorem increment_condVar (k : Fin K) (t : ℕ) :
    condVar (historyFiltration n t) (increment π ν n k t) (trajectoryLaw π ν n)
      =ᵐ[trajectoryLaw π ν n] varianceIncrement π ν n k t := by
  unfold condVar
  have hz := conditional_increment_zero π ν n hbound ε hε hfloor k t
  have heq :
      (increment π ν n k t -
        (trajectoryLaw π ν n)[increment π ν n k t | historyFiltration n t]) ^ 2
      =ᵐ[trajectoryLaw π ν n] (fun z => (increment π ν n k t z) ^ 2) := by
    filter_upwards [hz] with z hzero
    simp [hzero]
  exact (condExp_congr_ae heq).trans
    (conditional_increment_square π ν n hbound ε hε hfloor k t)

include hbound hε hfloor in
/-- Conditional variance can also be taken before subtracting the known mean. -/
theorem importanceWeighted_condVar (k : Fin K) (t : ℕ) :
    condVar (historyFiltration n t) (importanceWeighted π n k t) (trajectoryLaw π ν n)
      =ᵐ[trajectoryLaw π ν n] varianceIncrement π ν n k t := by
  unfold condVar
  have hm := conditional_unbiased π ν n hbound ε hε hfloor k t
  have heq :
      (importanceWeighted π n k t -
        (trajectoryLaw π ν n)[importanceWeighted π n k t | historyFiltration n t]) ^ 2
      =ᵐ[trajectoryLaw π ν n] (fun z => (increment π ν n k t z) ^ 2) := by
    filter_upwards [hm] with z hmean
    simp [hmean, increment_eq_weighted_sub_mean]
  exact (condExp_congr_ae heq).trans
    (conditional_increment_square π ν n hbound ε hε hfloor k t)

include hbound hε hfloor in
/-- The predictable variance is the sum of Mathlib conditional variances of the errors. -/
theorem predictableVariance_eq_sum_condVar_increment (k : Fin K) (t : ℕ) :
    predictableVariance π ν n k t =ᵐ[trajectoryLaw π ν n]
      ∑ s ∈ Finset.range t,
        condVar (historyFiltration n s) (increment π ν n k s) (trajectoryLaw π ν n) := by
  change (∑ s ∈ Finset.range t, varianceIncrement π ν n k s) =ᵐ[trajectoryLaw π ν n] _
  exact eventuallyEq_sum (fun s _ => (increment_condVar π ν n hbound ε hε hfloor k s).symm)

include hbound hε hfloor in
/-- The same accumulated variance can be consumed directly by estimator-based APIs. -/
theorem predictableVariance_eq_sum_condVar_estimator (k : Fin K) (t : ℕ) :
    predictableVariance π ν n k t =ᵐ[trajectoryLaw π ν n]
      ∑ s ∈ Finset.range t,
        condVar (historyFiltration n s) (importanceWeighted π n k s) (trajectoryLaw π ν n) := by
  change (∑ s ∈ Finset.range t, varianceIncrement π ν n k s) =ᵐ[trajectoryLaw π ν n] _
  exact eventuallyEq_sum
    (fun s _ => (importanceWeighted_condVar π ν n hbound ε hε hfloor k s).symm)

include hbound hε hfloor in
/-- Mathlib's Doob martingale part of cumulative IW rewards is the existing error process. -/
theorem cumulativeEstimate_martingalePart (k : Fin K) (t : ℕ) :
    martingalePart (cumulativeEstimate π n k) (historyFiltration n) (trajectoryLaw π ν n) t
      =ᵐ[trajectoryLaw π ν n] cumulativeMartingale π ν n k t := by
  unfold martingalePart predictablePart
  simp only [cumulativeEstimate, partialSum_succ_sub]
  have hs :
      (∑ s ∈ Finset.range t,
        (trajectoryLaw π ν n)[importanceWeighted π n k s | historyFiltration n s])
      =ᵐ[trajectoryLaw π ν n]
        ∑ s ∈ Finset.range t,
          (fun _ : Trajectory K n => if s < n then StochasticImportanceWeighting.mean (ν s) k else 0) :=
    eventuallyEq_sum (fun s _ => conditional_unbiased π ν n hbound ε hε hfloor k s)
  have h := (EventuallyEq.rfl : partialSum (importanceWeighted π n k) t
      =ᵐ[trajectoryLaw π ν n] partialSum (importanceWeighted π n k) t).sub hs
  have hi (s : ℕ) : increment π ν n k s = importanceWeighted π n k s -
      (fun _ => if s < n then StochasticImportanceWeighting.mean (ν s) k else 0) := by
    funext z
    exact increment_eq_weighted_sub_mean π ν n k s z
  simpa only [cumulativeMartingale, partialSum, hi,
    Finset.sum_sub_distrib] using h

/-- Mathlib's Doob martingale part of actual pull counts is their existing compensation. -/
theorem pullCount_martingalePart (k : Fin K) (t : ℕ) :
    martingalePart (pullCount n k) (historyFiltration n) (trajectoryLaw π ν n) t
      =ᵐ[trajectoryLaw π ν n] compensatedPullCount π n k t := by
  unfold martingalePart predictablePart
  simp only [pullCount, partialSum_succ_sub]
  have hs :
      (∑ s ∈ Finset.range t,
        (trajectoryLaw π ν n)[pullIndicator n k s | historyFiltration n s])
      =ᵐ[trajectoryLaw π ν n] ∑ s ∈ Finset.range t, samplingProbability π n k s :=
    eventuallyEq_sum (fun s _ => conditional_pullIndicator π ν n k s)
  have h := (EventuallyEq.rfl : partialSum (pullIndicator n k) t
      =ᵐ[trajectoryLaw π ν n] partialSum (pullIndicator n k) t).sub hs
  simpa [compensatedPullCount, pullCount, expectedPullCount, partialSum] using h

end BestOfBothWorlds.MathlibInterop
