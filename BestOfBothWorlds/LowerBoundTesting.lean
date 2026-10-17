module

public import BestOfBothWorlds.LowerBoundExtraction
public import BestOfBothWorlds.SeededLearner
public import BestOfBothWorlds.SeededLearnerRestriction
public import BestOfBothWorlds.FullTableConcentration

/-!
Removing full-table bad events from observed-transcript tests, under the
original independent seed/table laws. Goodness may depend on every table entry
and may be dependent on the learner's recommendation. No conditioning occurs.
-/

@[expose] public section

open MeasureTheory

namespace BestOfBothWorlds.LowerBounds

variable {Table Seed Arm : Type*} [Fintype Table] [MeasurableSpace Table]
  [MeasurableSingletonClass Table] [MeasurableSpace Seed]

/-- Error mass on good deterministic tables, averaged under the original law. -/
noncomputable def goodErrorMass (ρ : Measure Seed) (μ : Measure Table)
    (recommend : Seed × Table → Arm) (best : Table → Arm) (good : Set Table) : ℝ :=
  ∫ g, good.indicator (deterministicError ρ recommend best) g ∂μ

omit [Fintype Table] [MeasurableSingletonClass Table] in
theorem goodErrorMass_nonneg (ρ : Measure Seed) (μ : Measure Table)
    (recommend : Seed × Table → Arm) (best : Table → Arm) (good : Set Table) :
    0 ≤ goodErrorMass ρ μ recommend best good := by
  classical
  apply integral_nonneg
  intro g
  by_cases hg : g ∈ good
  · simp only [Set.indicator_of_mem hg, deterministicError]
    exact measureReal_nonneg
  · simp only [Set.indicator_of_notMem hg]
    exact le_rfl

/-- Any reference error whose target agrees with the actual best arm on good
tables is at most the actual good error mass plus the bad-table probability. -/
theorem randomizedError_agreement_le_goodErrorMass_add_bad
    [MeasurableSpace Arm] [MeasurableSingletonClass Arm] [Countable Arm]
    (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (μ : Measure Table) [IsProbabilityMeasure μ]
    (recommend : Seed × Table → Arm) (hrec : Measurable recommend)
    (best target : Table → Arm) (good : Set Table)
    (hagrees : ∀ g ∈ good, target g = best g) :
    randomizedError ρ μ recommend target ≤
      goodErrorMass ρ μ recommend best good + μ.real goodᶜ := by
  classical
  have hgood : MeasurableSet good := good.toFinite.measurableSet
  rw [randomizedError_eq_average ρ μ recommend hrec target]
  calc
    _ ≤ ∫ g, good.indicator (deterministicError ρ recommend best) g +
        goodᶜ.indicator (fun _ => (1 : ℝ)) g ∂μ := by
      apply integral_mono Integrable.of_finite Integrable.of_finite
      intro g
      by_cases hg : g ∈ good
      · simp only [Set.indicator_of_mem hg, Set.indicator_of_notMem
          (show g ∉ goodᶜ from fun h => h hg), add_zero]
        unfold deterministicError
        rw [hagrees g hg]
      · simp only [Set.indicator_of_notMem hg, Set.indicator_of_mem (show g ∈ goodᶜ from hg), zero_add,
          deterministicError]
        exact measureReal_le_one
    _ = _ := by
      rw [integral_add Integrable.of_finite Integrable.of_finite,
        integral_indicator hgood.compl]
      simp only [goodErrorMass, integral_const, smul_eq_mul, mul_one]
      rw [measureReal_def, Measure.restrict_apply MeasurableSet.univ]
      simp only [Set.univ_inter, measureReal_def]

theorem goodErrorMass_le_randomizedError
    [MeasurableSpace Arm] [MeasurableSingletonClass Arm] [Countable Arm]
    (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (μ : Measure Table) [IsProbabilityMeasure μ]
    (recommend : Seed × Table → Arm) (hrec : Measurable recommend)
    (best : Table → Arm) (good : Set Table) :
    goodErrorMass ρ μ recommend best good ≤ randomizedError ρ μ recommend best := by
  classical
  rw [randomizedError_eq_average ρ μ recommend hrec best]
  apply integral_mono Integrable.of_finite Integrable.of_finite
  intro g
  by_cases hg : g ∈ good
  · simp only [Set.indicator_of_mem hg]
    exact le_rfl
  · simp only [Set.indicator_of_notMem hg, deterministicError]
    exact measureReal_nonneg

omit [Fintype Table] [MeasurableSingletonClass Table] in
/-- A probability of bad tables strictly below one guarantees a deterministic
good table exists; no conditional probability or support division is used. -/
theorem good_nonempty_of_bad_lt_one (μ : Measure Table) [IsProbabilityMeasure μ]
    (good : Set Table) (hbad : μ.real goodᶜ < 1) : good.Nonempty := by
  by_contra h
  have hg : good = ∅ := Set.not_nonempty_iff_eq_empty.mp h
  simp only [hg, Set.compl_empty, probReal_univ, lt_self_iff_false] at hbad

section Transcript

variable {Reward : Type*} [MeasurableSpace Reward] [Fintype Reward]
  [MeasurableSingletonClass Reward] {K n : ℕ}

/-- Tests of the final recommendation use the actual observed transcript law. -/
theorem transcript_error_eq_randomizedError
    (L : SeededLearner.Learner Seed Reward K n) (ρ : Measure Seed)
    (ν : Fin n → Fin K → Measure Reward) (b : Fin K) :
    (L.transcriptLaw ρ ν).real {z | z.2 ≠ b} =
      randomizedError ρ (SeededLearner.Learner.tableLaw ν)
        (fun z => (L.transcript z).2) (fun _ => b) := by
  unfold SeededLearner.Learner.transcriptLaw randomizedError
  simp only [measureReal_def]
  rw [Measure.map_apply L.transcript_measurable (Set.toFinite _).measurableSet]
  rfl

end Transcript

section RealLearner

variable {K n : ℕ}

/-- Actual fixed-table error of an arbitrary learner observing real rewards.
The finite horizon is taken from the learner's type; all randomness is its seed. -/
noncomputable def realLearnerError (hK : 2 ≤ K)
    (L : SeededLearner.Learner Seed ℝ K n) (ρ : Measure Seed)
    (g : ℕ → Fin K → ℝ) : ℝ :=
  ρ.real {r | (L.transcript (r, fun t : Fin n => g t.val)).2 ≠
    RealizedGaps.best (RealizedGaps.arms_pos hK) g n}

theorem realLearnerError_event_measurable (hK : 2 ≤ K)
    (L : SeededLearner.Learner Seed ℝ K n) (g : ℕ → Fin K → ℝ) :
    MeasurableSet {r | (L.transcript (r, fun t : Fin n => g t.val)).2 ≠
      RealizedGaps.best (RealizedGaps.arms_pos hK) g n} :=
  (measurableSet_eq_fun (L.recommendation_fixedRealTable_measurable _) measurable_const).compl

theorem realLearnerError_nonneg (hK : 2 ≤ K)
    (L : SeededLearner.Learner Seed ℝ K n) (ρ : Measure Seed) (g : ℕ → Fin K → ℝ) :
    0 ≤ realLearnerError hK L ρ g := measureReal_nonneg

theorem realLearnerError_le_one (hK : 2 ≤ K)
    (L : SeededLearner.Learner Seed ℝ K n) (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (g : ℕ → Fin K → ℝ) : realLearnerError hK L ρ g ≤ 1 := measureReal_le_one

/-- Restricting a real-history learner to the finite actual reward alphabet
does not change its deterministic-table error or reveal extra observations. -/
theorem deterministicError_restrictReward {Reward : Type*} [MeasurableSpace Reward]
    [Fintype Reward] [MeasurableSingletonClass Reward]
    (hK : 2 ≤ K) (L : SeededLearner.Learner Seed ℝ K n) (ρ : Measure Seed)
    (value : Reward → ℝ) (g : SeededLearner.Table K Reward n) :
    deterministicError ρ (fun z => ((L.restrictReward value).transcript z).2)
        (fun h => RealizedGaps.best (RealizedGaps.arms_pos hK) (realTable value h) n) g =
      realLearnerError hK L ρ (realTable value g) := by
  have htable : (fun t : Fin n => realTable value g t.val) = SeededLearner.mapTable value g := by
    funext t j
    simp only [realTable, dite_eq_left t.isLt, SeededLearner.mapTable]
  unfold deterministicError realLearnerError
  apply congrArg (fun W : Set Seed => ρ.real W)
  ext r
  change ((L.restrictReward value).transcript (r, g)).2 ≠ _ ↔ _
  rw [L.recommendation_restrictReward, htable]
  rfl

end RealLearner

end BestOfBothWorlds.LowerBounds
