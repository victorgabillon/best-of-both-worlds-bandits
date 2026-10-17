module

public import BestOfBothWorlds.P1StochasticBound
public import BestOfBothWorlds.P1AdversarialBound
public import BestOfBothWorlds.P1Corollary
public import BestOfBothWorlds.P1ScheduleIdentities

/-!
The complete pair of guarantees in frozen Theorem 6, for the same concrete P1
policy. Corollary 7 and the exact weighted-schedule identities are imported with
the endpoints so that this module is the entry point for the P1 certificate.
-/

@[expose] public section

open MeasureTheory

namespace BestOfBothWorlds.P1UpperBounds

/-- Theorem 6: stochastic and adversarial guarantees for the actual same learner. -/
theorem p1_upper_bounds {K : ℕ} (hK : 2 ≤ K)
    (ν : Measure (Fin K → ℝ)) [IsProbabilityMeasure ν]
    (hbound : ∀ᵐ y ∂ν, ∀ k, 0 ≤ y k ∧ y k ≤ 1)
    (hUnique : P1StochasticModel.UniqueBest hK ν)
    (g : ℕ → Fin K → ℝ) (n : ℕ) (hn : 0 < n)
    (hg : ∀ t < n, ∀ k, 0 ≤ g t k ∧ g t k ≤ 1)
    (hgUnique : RealizedGaps.UniqueBest (RealizedGaps.arms_pos hK) g n) :
    P1StochasticEvents.errorProbability hK ν n ≤
        2 * (K : ℝ) ^ 3 * (n : ℝ) * Real.exp (-(n : ℝ) /
          (128 * P1Complexity.optimizedComplexity hK (P1StochasticModel.gap hK ν) n hn)) ∧
      P1AdversarialBound.errorProbability (RealizedGaps.arms_pos hK) g n ≤
        (K : ℝ) * Real.exp (-(3 * (n : ℝ)) /
          (40 * P1Ranking.harmonicK K * RealizedGaps.complexity hK g n)) := by
  exact ⟨P1StochasticBound.p1_stochastic_error_bound hK ν hbound hUnique n hn,
    P1AdversarialBound.p1_adversarial_error_bound hK g n hg hgUnique⟩

end BestOfBothWorlds.P1UpperBounds
