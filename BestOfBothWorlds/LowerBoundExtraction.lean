module

public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
Finite-table averaging and deterministic witness extraction for the lower bounds.
The hypotheses in this helper are explicitly the quantitative inputs that must
later be proved for the actual constructed table laws. This module does not
claim either principal lower-bound theorem.
-/

@[expose] public section

open MeasureTheory

namespace BestOfBothWorlds.LowerBounds

variable {Table : Type*} [Fintype Table] [MeasurableSpace Table]
  [MeasurableSingletonClass Table]

/-- Error averaged over finitely many complete tables is the weighted sum of
its deterministic-table errors. -/
theorem finite_table_average (μ : Measure Table) [IsFiniteMeasure μ]
    (error : Table → ℝ) :
    (∫ g, error g ∂μ) = ∑ g, μ.real {g} * error g := by
  simpa only [smul_eq_mul] using integral_fintype (μ := μ)
    (f := error) Integrable.of_finite

/-- A bound on each good table yields the corresponding expectation bound.
No independence between a table's goodness and its error is assumed. -/
theorem average_le_good_bound (μ : Measure Table) [IsProbabilityMeasure μ]
    (error : Table → ℝ) (good : Set Table) (c : ℝ)
    (hgood : ∀ g ∈ good, error g ≤ c)
    (hupper : ∀ g, error g ≤ 1) :
    (∫ g, error g ∂μ) ≤ c * μ.real good + μ.real goodᶜ := by
  classical
  have hmeas : MeasurableSet good := Set.Finite.measurableSet good.toFinite
  calc
    (∫ g, error g ∂μ) ≤ ∫ g,
        good.indicator (fun _ => c) g + goodᶜ.indicator (fun _ => (1 : ℝ)) g ∂μ := by
      apply integral_mono Integrable.of_finite Integrable.of_finite
      intro g
      by_cases hg : g ∈ good
      · simpa [hg] using hgood g hg
      · simpa [hg] using hupper g
    _ = c * μ.real good + μ.real goodᶜ := by
      rw [integral_add Integrable.of_finite Integrable.of_finite,
        integral_indicator hmeas, integral_indicator hmeas.compl]
      simp [mul_comm]

/-- The final finite-support extraction used in Appendix E, with its exact
`1/8`, `1/16` thresholds. The conclusion is a deterministic table. -/
theorem exists_good_table_error_ge_one_sixteenth
    (μ : Measure Table) [IsProbabilityMeasure μ]
    (error : Table → ℝ) (good : Set Table)
    (hupper : ∀ g, error g ≤ 1)
    (haverage : (1 : ℝ) / 8 ≤ ∫ g, error g ∂μ)
    (hbad : μ.real goodᶜ ≤ (1 : ℝ) / 16) :
    ∃ g ∈ good, (1 : ℝ) / 16 ≤ error g := by
  classical
  by_contra h
  push Not at h
  have hbound := average_le_good_bound μ error good ((1 : ℝ) / 16)
    (fun g hg => (h g hg).le) hupper
  have hmass : μ.real good + μ.real goodᶜ = 1 := by
    rw [measureReal_add_measureReal_compl (Set.Finite.measurableSet good.toFinite)]
    simp
  linarith

/-- Maximizing the deterministic error over a nonempty finite good set bounds
its entire good-table error mass, as used in Appendix D. -/
theorem exists_good_table_dominating_good_mass
    (μ : Measure Table) [IsProbabilityMeasure μ]
    (error : Table → ℝ) (good : Set Table)
    (herror : ∀ g, 0 ≤ error g)
    (hgood : good.Nonempty) :
    ∃ g ∈ good, (∫ x, good.indicator error x ∂μ) ≤ error g := by
  classical
  obtain ⟨g, hg, hmax⟩ := good.toFinite.toFinset.exists_max_image error (by simpa using hgood)
  have hg' : g ∈ good := by simpa using hg
  refine ⟨g, hg', ?_⟩
  calc
    (∫ x, good.indicator error x ∂μ) ≤ ∫ _, error g ∂μ := by
      apply integral_mono Integrable.of_finite (integrable_const _)
      intro x
      by_cases hx : x ∈ good
      · simpa [hx] using hmax x (by simpa using hx)
      · simpa [hx] using herror g
    _ = error g := by simp

/-- Error on a deterministic table, with probability over private randomness. -/
noncomputable def deterministicError {Seed Arm : Type*} [MeasurableSpace Seed]
    (ρ : Measure Seed) (recommend : Seed × Table → Arm) (best : Table → Arm)
    (g : Table) : ℝ :=
  ρ.real {r | recommend (r, g) ≠ best g}

/-- Error under the actual product of the seed and table distributions. -/
noncomputable def randomizedError {Seed Arm : Type*} [MeasurableSpace Seed]
    (ρ : Measure Seed) (μ : Measure Table) (recommend : Seed × Table → Arm)
    (best : Table → Arm) : ℝ :=
  (ρ.prod μ).real {z | recommend z ≠ best z.2}

/-- The finite-table averaging identity for an arbitrary measurable private
seed. The recommendation may depend on that seed and all observed history. -/
theorem randomizedError_eq_average {Seed Arm : Type*} [MeasurableSpace Seed]
    [MeasurableSpace Arm] [MeasurableSingletonClass Arm] [Countable Arm]
    (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (μ : Measure Table) [IsProbabilityMeasure μ]
    (recommend : Seed × Table → Arm) (hrec : Measurable recommend)
    (best : Table → Arm) :
    randomizedError ρ μ recommend best =
      ∫ g, deterministicError ρ recommend best g ∂μ := by
  classical
  let bad : Set (Seed × Table) := {z | recommend z ≠ best z.2}
  have hbest : Measurable best := measurable_of_countable best
  have hbad : MeasurableSet bad :=
    (measurableSet_eq_fun hrec (hbest.comp measurable_snd)).compl
  have hint : Integrable (bad.indicator (fun _ => (1 : ℝ))) (ρ.prod μ) :=
    (integrable_const (1 : ℝ)).indicator hbad
  have hprob : (∫ z, bad.indicator (fun _ => (1 : ℝ)) z ∂(ρ.prod μ)) =
      randomizedError ρ μ recommend best := by
    rw [integral_indicator hbad]
    simp [randomizedError, bad]
  rw [← hprob, integral_prod_symm _ hint]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun g => by
    have hs : MeasurableSet {r | recommend (r, g) ≠ best g} :=
      (measurableSet_eq_fun
        (hrec.comp (measurable_id.prodMk measurable_const)) measurable_const).compl
    change (∫ r, ({r | recommend (r, g) ≠ best g} : Set Seed).indicator
      (fun _ => (1 : ℝ)) r ∂ρ) = _
    rw [integral_indicator hs]
    simp [deterministicError]

/-- Extraction from an actual independent seed/table law. All information and
concentration estimates remain visible quantitative inputs of this helper. -/
theorem exists_deterministic_good_error {Seed Arm : Type*} [MeasurableSpace Seed]
    [MeasurableSpace Arm] [MeasurableSingletonClass Arm] [Countable Arm]
    (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (μ : Measure Table) [IsProbabilityMeasure μ]
    (recommend : Seed × Table → Arm) (hrec : Measurable recommend)
    (best : Table → Arm) (good : Set Table)
    (haverage : (1 : ℝ) / 8 ≤ randomizedError ρ μ recommend best)
    (hbad : μ.real goodᶜ ≤ (1 : ℝ) / 16) :
    ∃ g ∈ good, (1 : ℝ) / 16 ≤ deterministicError ρ recommend best g := by
  apply exists_good_table_error_ge_one_sixteenth μ
    (deterministicError ρ recommend best) good
  · intro g
    exact (measureReal_mono (Set.subset_univ _)).trans_eq (by simp)
  · simpa only [randomizedError_eq_average ρ μ recommend hrec best] using haverage
  · exact hbad

end BestOfBothWorlds.LowerBounds
