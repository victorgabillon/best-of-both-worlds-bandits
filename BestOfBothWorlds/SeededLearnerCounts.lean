module

public import BestOfBothWorlds.SeededLearner
public import BestOfBothWorlds.LowerBoundSelection
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-! Actual finite pull counts for the general private-seed learner. -/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace BestOfBothWorlds.SeededLearner.Learner

/-- The fixed informative prefix, with zero-based Lean rounds. -/
def prefixRounds (n N : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun t => t.val < N)

theorem mem_prefixRounds (n N : ℕ) (t : Fin n) :
    t ∈ prefixRounds n N ↔ t.val < N := by simp [prefixRounds]

theorem prefixRounds_card (n N : ℕ) (hN : N ≤ n) :
    (prefixRounds n N).card = N := by
  classical
  calc
    _ = (Finset.univ : Finset (Fin N)).card := by
      apply Finset.card_bij (fun t ht => (⟨t.val, (mem_prefixRounds n N t).mp ht⟩ : Fin N))
      · intro t ht
        exact Finset.mem_univ _
      · intro i hi j hj heq
        apply Fin.ext
        exact congrArg (fun x : Fin N => x.val) heq
      · intro j _
        refine ⟨Fin.castLE hN j, ?_, ?_⟩
        · exact (mem_prefixRounds n N _).mpr j.isLt
        · rfl
    _ = N := Finset.card_fin N

theorem prefixRounds_full (n : ℕ) : prefixRounds n n = Finset.univ := by
  ext t
  simp [mem_prefixRounds, t.isLt]

variable {Seed Reward : Type*} [MeasurableSpace Seed] [MeasurableSpace Reward]
  [Fintype Reward] [MeasurableSingletonClass Reward] {K n : ℕ}
  (L : Learner Seed Reward K n)

/-- Number of actual selections of k during the fixed informative round set. -/
noncomputable def pullCount (T : Finset (Fin n)) (k : Fin K)
    (z : Seed × Table K Reward n) : ℝ :=
  ∑ t ∈ T, if (L.play z.1 z.2 t).1 = k then (1 : ℝ) else 0

omit [Fintype Reward] [MeasurableSingletonClass Reward] in
theorem pullCount_nonneg (T : Finset (Fin n)) (k : Fin K)
    (z : Seed × Table K Reward n) : 0 ≤ L.pullCount T k z := by
  unfold pullCount
  exact Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity

omit [Fintype Reward] [MeasurableSingletonClass Reward] in
theorem pullCount_le_card (T : Finset (Fin n)) (k : Fin K)
    (z : Seed × Table K Reward n) : L.pullCount T k z ≤ T.card := by
  classical
  unfold pullCount
  calc
    _ ≤ ∑ _t ∈ T, (1 : ℝ) := Finset.sum_le_sum fun _ _ => by split_ifs <;> norm_num
    _ = T.card := by simp

theorem pullCount_measurable (T : Finset (Fin n)) (k : Fin K) :
    Measurable (L.pullCount T k) := by
  classical
  unfold pullCount
  exact Finset.measurable_sum T fun t _ =>
    Measurable.ite (measurableSet_eq_fun (L.play_measurable t).fst measurable_const)
      measurable_const measurable_const

omit [Fintype Reward] [MeasurableSingletonClass Reward] in
/-- Exactly one arm is selected at every informative round; zero action
probabilities do not change this pathwise count identity. -/
theorem sum_pullCount (T : Finset (Fin n)) (z : Seed × Table K Reward n) :
    ∑ k, L.pullCount T k z = T.card := by
  classical
  unfold pullCount
  rw [Finset.sum_comm]
  simp

/-- Pull counts are integrable even when the private seed has infinite support. -/
theorem pullCount_integrable (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (ν : Fin n → Fin K → Measure Reward) [∀ t k, IsProbabilityMeasure (ν t k)]
    (T : Finset (Fin n)) (k : Fin K) :
    Integrable (L.pullCount T k) (ρ.prod (tableLaw ν)) :=
  Integrable.of_mem_Icc 0 T.card (L.pullCount_measurable T k).aemeasurable
    (Filter.Eventually.of_forall fun z =>
      ⟨L.pullCount_nonneg T k z, L.pullCount_le_card T k z⟩)

/-- Expectation under the actual independent seed and full-table law. -/
noncomputable def expectedPullCount (ρ : Measure Seed)
    (ν : Fin n → Fin K → Measure Reward) (T : Finset (Fin n)) (k : Fin K) : ℝ :=
  ∫ z, L.pullCount T k z ∂(ρ.prod (tableLaw ν))

omit [Fintype Reward] [MeasurableSingletonClass Reward] in
theorem expectedPullCount_nonneg (ρ : Measure Seed)
    (ν : Fin n → Fin K → Measure Reward) (T : Finset (Fin n)) (k : Fin K) :
    0 ≤ L.expectedPullCount ρ ν T k :=
  integral_nonneg fun z => L.pullCount_nonneg T k z

theorem sum_expectedPullCount (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (ν : Fin n → Fin K → Measure Reward) [∀ t k, IsProbabilityMeasure (ν t k)]
    (T : Finset (Fin n)) : ∑ k, L.expectedPullCount ρ ν T k = T.card := by
  unfold expectedPullCount
  rw [← integral_finsetSum _ (fun k _ => L.pullCount_integrable ρ ν T k)]
  simp only [L.sum_pullCount]
  simp

/-- Observing the selected arm is a genuine transcript event. -/
theorem transcript_action_mass (ρ : Measure Seed)
    (ν : Fin n → Fin K → Measure Reward) (t : Fin n) (k : Fin K) :
    L.transcriptLaw ρ ν {z | (z.1 t).1 = k} =
      (ρ.prod (tableLaw ν)) {z | (L.play z.1 z.2 t).1 = k} := by
  rw [transcriptLaw, Measure.map_apply L.transcript_measurable
    (Set.Finite.measurableSet (Set.toFinite _))]
  rfl

/-- The expected actual pull count is the sum of its observed action masses. -/
theorem expectedPullCount_eq_sum_action_mass
    (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (ν : Fin n → Fin K → Measure Reward) [∀ t k, IsProbabilityMeasure (ν t k)]
    (T : Finset (Fin n)) (k : Fin K) :
    L.expectedPullCount ρ ν T k =
      ∑ t ∈ T, (L.transcriptLaw ρ ν).real {z | (z.1 t).1 = k} := by
  classical
  unfold expectedPullCount pullCount
  have hind : ∀ t : Fin n, Integrable
      (fun z : Seed × Table K Reward n =>
        if (L.play z.1 z.2 t).1 = k then (1 : ℝ) else 0)
      (ρ.prod (tableLaw ν)) := by
    intro t
    have heq : (fun z : Seed × Table K Reward n =>
        if (L.play z.1 z.2 t).1 = k then (1 : ℝ) else 0) =
        ({z | (L.play z.1 z.2 t).1 = k} : Set (Seed × Table K Reward n)).indicator
          (fun _ => (1 : ℝ)) := by
      funext z
      simp only [Set.indicator, Set.mem_ofPred_eq]
    rw [heq]
    exact (integrable_const (μ := ρ.prod (tableLaw ν)) (1 : ℝ)).indicator
      (measurableSet_eq_fun (L.play_measurable t).fst (measurable_const (a := k)))
  rw [integral_finsetSum _ (fun t _ => hind t)]
  apply Finset.sum_congr rfl
  intro t _
  have hset := measurableSet_eq_fun (L.play_measurable t).fst (measurable_const (a := k))
  have heq : (fun z : Seed × Table K Reward n =>
      if (L.play z.1 z.2 t).1 = k then (1 : ℝ) else 0) =
      ({z | (L.play z.1 z.2 t).1 = k} : Set (Seed × Table K Reward n)).indicator
        (fun _ => (1 : ℝ)) := by
    funext z
    simp only [Set.indicator, Set.mem_ofPred_eq]
  rw [heq, integral_indicator hset]
  simp only [integral_const, smul_eq_mul, mul_one, measureReal_def,
    L.transcript_action_mass]
  simp

/-- A suboptimal label with a small actual expected informative pull count.
The witness depends on the probability law, not a sampled seed or table. -/
theorem exists_suboptimal_light_actual (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (ν : Fin n → Fin K → Measure Reward) [∀ t k, IsProbabilityMeasure (ν t k)]
    (hK : 2 ≤ K) (T : Finset (Fin n)) :
    ∃ k : Fin K, k ≠ firstRank hK ∧
      L.expectedPullCount ρ ν T k ≤ (T.card : ℝ) / ((K : ℝ) - 1) :=
  LowerBoundSelection.exists_suboptimal_light hK (L.expectedPullCount ρ ν T) T.card
    (L.expectedPullCount_nonneg ρ ν T) (L.sum_expectedPullCount ρ ν T).le

/-- Theorem 4's informative label for the actual BASE interaction after its
maximizing reference rank has been selected. -/
theorem exists_informative_actual (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (ν : Fin n → Fin K → Measure Reward) [∀ t k, IsProbabilityMeasure (ν t k)]
    (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    (i : Fin K) (hi : 1 ≤ i.val)
    (hmax : ∀ r, LowerBoundSelection.rank r / gap r ≤ LowerBoundSelection.rank i / gap i)
    (T : Finset (Fin n)) :
    ∃ k : Fin K, 1 ≤ k.val ∧ k ≤ i ∧
      LowerBoundSelection.rank i / 2 ≤ LowerBoundSelection.rank k ∧
      gap i / 2 ≤ gap k ∧ gap k ≤ gap i ∧
      L.expectedPullCount ρ ν T k ≤ 2 * (T.card : ℝ) / LowerBoundSelection.rank i :=
  LowerBoundSelection.exists_informative_arm hK gap hpos hsorted i hi hmax
    (L.expectedPullCount ρ ν T) T.card (L.expectedPullCount_nonneg ρ ν T)
    (L.sum_expectedPullCount ρ ν T).le

end BestOfBothWorlds.SeededLearner.Learner
