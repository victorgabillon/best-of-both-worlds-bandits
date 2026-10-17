module

public import BestOfBothWorlds.SeededLearnerCounts
public import BestOfBothWorlds.SeededLearnerFreshness
public import Mathlib.Tactic.Linarith
public import Lean.Elab.Tactic.Omega

/-! Agreement of actual expected pull counts under fixed-prefix environment agreement. -/

@[expose] public section

open MeasureTheory

namespace BestOfBothWorlds.SeededLearner.Learner

variable {Seed Reward : Type*} [MeasurableSpace Seed] [MeasurableSpace Reward]
  [Fintype Reward] [MeasurableSingletonClass Reward] {K n : ℕ}
  (L : Learner Seed Reward K n)

/-- Earlier-row equality gives equality of each actual prefix expected count.
This statement uses the original independent seed/table laws, not laws
conditioned on a table event or a learner's realized choices. -/
theorem expectedPullCount_eq_of_prefix (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (ν η : Fin n → Fin K → Measure Reward)
    [∀ t k, IsProbabilityMeasure (ν t k)] [∀ t k, IsProbabilityMeasure (η t k)]
    (N : ℕ) (k : Fin K)
    (hprefix : ∀ t : Fin n, t.val < N → ∀ a, ν t a = η t a) :
    L.expectedPullCount ρ ν (prefixRounds n N) k =
      L.expectedPullCount ρ η (prefixRounds n N) k := by
  classical
  rw [L.expectedPullCount_eq_sum_action_mass, L.expectedPullCount_eq_sum_action_mass]
  apply Finset.sum_congr rfl
  intro t ht
  have htN := (mem_prefixRounds n N t).mp ht
  simpa only [measureReal_def] using congrArg ENNReal.toReal
    (L.action_mass_eq_of_prefix ρ ν η t k (fun u hu a => hprefix u (by omega) a))

/-- Theorem 2's complete arm-selection bound for the actual BASE interaction. -/
theorem exists_halfHorizon_light_actual (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (ν : Fin n → Fin K → Measure Reward) [∀ t k, IsProbabilityMeasure (ν t k)]
    (hK : 2 ≤ K) :
    ∃ k : Fin K, k ≠ firstRank hK ∧
      L.expectedPullCount ρ ν (prefixRounds n (n / 2)) k ≤ (n : ℝ) / (K : ℝ) := by
  apply LowerBoundSelection.exists_halfHorizon_light hK n
    (L.expectedPullCount ρ ν (prefixRounds n (n / 2)))
    (L.expectedPullCount_nonneg ρ ν _)
  rw [L.sum_expectedPullCount, prefixRounds_card n (n / 2) (by omega)]
  exact le_rfl

end BestOfBothWorlds.SeededLearner.Learner
