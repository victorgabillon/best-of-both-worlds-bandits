module

public import BestOfBothWorlds.FiniteInformation
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
Binary relative entropy with the manuscript's convention: parameter p is the
mass at true (and, under the standard real encoding, the reward one). The
first parameter may be an endpoint; the second parameter is interior in all
finite formulas below.
-/

@[expose] public section

open MeasureTheory

namespace BestOfBothWorlds.BernoulliInformation

/-- Binary relative entropy; zero-weight endpoint terms are zero. -/
noncomputable def binaryKL (p q : ℝ) : ℝ :=
  p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))

/-- Mathlib's Bernoulli law with mass p at true, not at false. -/
noncomputable def law (p : unitInterval) : Measure Bool :=
  ProbabilityTheory.bernoulliMeasure true false p

instance law_isProbabilityMeasure (p : unitInterval) : IsProbabilityMeasure (law p) := by
  unfold law
  infer_instance

@[simp]
theorem law_true (p : unitInterval) : (law p).real {true} = (p : ℝ) := by
  exact ProbabilityTheory.bernoulliMeasure_real_apply_of_mem_of_notMem p
    (measurableSet_singleton true) (by simp) (by simp)

@[simp]
theorem law_false (p : unitInterval) : (law p).real {false} = 1 - (p : ℝ) := by
  exact ProbabilityTheory.bernoulliMeasure_real_apply_of_notMem_of_mem p
    (measurableSet_singleton false) (by simp) (by simp)

theorem law_absolutelyContinuous (p q : unitInterval) (hq0 : 0 < (q : ℝ))
    (hq1 : (q : ℝ) < 1) : law p ≪ law q := by
  apply FiniteInformation.absolutelyContinuous_of_atom_support
  intro b hb
  have hm : (law q).real {b} = 0 := by simp [measureReal_def, hb]
  cases b
  · rw [law_false] at hm
    linarith
  · rw [law_true] at hm
    linarith

theorem finiteKL_law (p q : unitInterval) :
    FiniteInformation.finiteKL (law p) (law q) = binaryKL p q := by
  simp [FiniteInformation.finiteKL, binaryKL]

theorem klDiv_ne_top (p q : unitInterval) (hq0 : 0 < (q : ℝ)) (hq1 : (q : ℝ) < 1) :
    InformationTheory.klDiv (law p) (law q) ≠ ⊤ :=
  FiniteInformation.klDiv_ne_top _ _ (law_absolutelyContinuous p q hq0 hq1)

/-- Exact Bernoulli formula for Mathlib KL, including endpoints of p. -/
theorem klDiv_law_eq (p q : unitInterval) (hq0 : 0 < (q : ℝ)) (hq1 : (q : ℝ) < 1) :
    InformationTheory.klDiv (law p) (law q) = ENNReal.ofReal (binaryKL p q) := by
  rw [FiniteInformation.klDiv_eq_ofReal_finiteKL _ _ (law_absolutelyContinuous p q hq0 hq1),
    finiteKL_law]

theorem toReal_klDiv_law (p q : unitInterval) (hq0 : 0 < (q : ℝ)) (hq1 : (q : ℝ) < 1) :
    (InformationTheory.klDiv (law p) (law q)).toReal = binaryKL p q := by
  rw [FiniteInformation.toReal_klDiv_eq_finiteKL _ _ (law_absolutelyContinuous p q hq0 hq1),
    finiteKL_law]

/-- The same formula for Mathlib Bernoulli laws on any two distinct atoms.
The first atom receives the parameter mass, so x=1,y=0 is the reward convention. -/
theorem klDiv_bernoulliMeasure {β : Type*} [MeasurableSpace β] [MeasurableSingletonClass β]
    (x y : β) (hxy : x ≠ y) (p q : unitInterval)
    (hq0 : 0 < (q : ℝ)) (hq1 : (q : ℝ) < 1) :
    InformationTheory.klDiv (ProbabilityTheory.bernoulliMeasure x y p)
      (ProbabilityTheory.bernoulliMeasure x y q) = ENNReal.ofReal (binaryKL p q) := by
  classical
  let f : Bool → β := fun b => if b then x else y
  let g : β → Bool := fun b => if b = x then true else false
  have hf : Measurable f := measurable_of_finite f
  have hg : Measurable g :=
    Measurable.ite (measurableSet_singleton x) measurable_const measurable_const
  have hgf : Function.LeftInverse g f := by
    intro b
    cases b <;> simp [f, g, hxy.symm]
  have hmap (r : unitInterval) : (law r).map f =
      ProbabilityTheory.bernoulliMeasure x y r := by
    simp only [law, ProbabilityTheory.map_bernoulliMeasure, f, Bool.false_eq_true, ite_false, ite_true]
  rw [← hmap p, ← hmap q, FiniteInformation.klDiv_map_eq_of_leftInverse
    (law p) (law q) f g hf hg hgf, klDiv_law_eq p q hq0 hq1]

theorem klDiv_bernoulliMeasure_ne_top {β : Type*} [MeasurableSpace β]
    [MeasurableSingletonClass β] (x y : β) (hxy : x ≠ y) (p q : unitInterval)
    (hq0 : 0 < (q : ℝ)) (hq1 : (q : ℝ) < 1) :
    InformationTheory.klDiv (ProbabilityTheory.bernoulliMeasure x y p)
      (ProbabilityTheory.bernoulliMeasure x y q) ≠ ⊤ := by
  rw [klDiv_bernoulliMeasure x y hxy p q hq0 hq1]
  exact ENNReal.ofReal_ne_top

theorem binaryKL_nonneg {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 < q) (hq1 : q < 1) : 0 ≤ binaryKL p q := by
  let pp : unitInterval := ⟨p, hp0, hp1⟩
  let qq : unitInterval := ⟨q, hq0.le, hq1.le⟩
  exact (finiteKL_law pp qq) ▸ FiniteInformation.finiteKL_nonneg (law pp) (law qq)
    (law_absolutelyContinuous pp qq hq0 hq1)

/-- A weighted log inequality which remains valid when its numerator is zero. -/
theorem mul_log_ratio_le {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    p * Real.log (p / q) ≤ p * (p / q - 1) := by
  rcases hp.eq_or_lt with rfl | hp
  · simp
  · exact mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hp hq)) hp.le

/-- The elementary Bernoulli chi-square upper estimate used in both lower bounds. -/
theorem binaryKL_le_chiSquare {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 < q) (hq1 : q < 1) :
    binaryKL p q ≤ (p - q) ^ 2 / (q * (1 - q)) := by
  calc
    _ ≤ p * (p / q - 1) + (1 - p) * ((1 - p) / (1 - q) - 1) :=
      add_le_add (mul_log_ratio_le hp0 hq0)
        (mul_log_ratio_le (sub_nonneg.mpr hp1) (sub_pos.mpr hq1))
    _ = _ := by
      field_simp [hq0.ne', (sub_pos.mpr hq1).ne']
      ring

/-- The logarithmic entropy decomposition also respects zero-weight endpoints. -/
theorem binaryKL_entropy {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 < q) (hq1 : q < 1) :
    binaryKL p q = p * Real.log (1 / q) +
      (1 - p) * Real.log (1 / (1 - q)) - Real.binEntropy p := by
  have hterm {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
      a * Real.log (a / b) = a * Real.log a - a * Real.log b := by
    rcases ha.eq_or_lt with rfl | ha
    · simp
    · rw [Real.log_div ha.ne' hb.ne']
      ring
  unfold binaryKL
  rw [hterm hp0 hq0, hterm (sub_nonneg.mpr hp1) (sub_pos.mpr hq1)]
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp only [Real.negMulLog_def, one_div, Real.log_inv]
  ring

/-- The paper's event-information consequence before data processing is applied. -/
theorem event_log_le_binaryKL_add_log_two {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 < q) (hq1 : q < 1) :
    p * Real.log (1 / q) ≤ binaryKL p q + Real.log 2 := by
  rw [binaryKL_entropy hp0 hp1 hq0 hq1]
  have hn : 0 ≤ (1 - p) * Real.log (1 / (1 - q)) := by
    apply mul_nonneg (sub_nonneg.mpr hp1)
    apply Real.log_nonneg
    apply (one_le_div (sub_pos.mpr hq1)).2
    linarith
  linarith [Real.binEntropy_le_log_two (p := p)]

section Event

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- Event data processing for actual finite probability laws, with no independence premise. -/
theorem event_binaryKL_le (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) (W : Set α) (hq0 : 0 < ν.real W) (hq1 : ν.real W < 1) :
    binaryKL (μ.real W) (ν.real W) ≤ FiniteInformation.finiteKL μ ν := by
  classical
  let f : α → ℝ := W.indicator (1 : α → ℝ)
  have hW : MeasurableSet W := (Set.to_countable W).measurableSet
  have hf : Measurable f := measurable_const.indicator hW
  have hμ := ProbabilityTheory.hasLaw_indicator_one_bernoulliMeasure
    (P := μ) (M := ℝ) hW.nullMeasurableSet
  have hν := ProbabilityTheory.hasLaw_indicator_one_bernoulliMeasure
    (P := ν) (M := ℝ) hW.nullMeasurableSet
  have hdp := InformationTheory.klDiv_map_le μ ν hf
  change InformationTheory.klDiv (μ.map (W.indicator (1 : α → ℝ)))
    (ν.map (W.indicator (1 : α → ℝ))) ≤ InformationTheory.klDiv μ ν at hdp
  rw [hμ.map_eq, hν.map_eq, klDiv_bernoulliMeasure (1 : ℝ) 0 one_ne_zero
    _ _ hq0 hq1, FiniteInformation.klDiv_eq_ofReal_finiteKL μ ν hac] at hdp
  exact (ENNReal.ofReal_le_ofReal_iff
    (FiniteInformation.finiteKL_nonneg μ ν hac)).1 hdp

/-- Lemma 10's event logarithm consequence, still for arbitrary transcript events. -/
theorem event_log_le (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) (W : Set α) (hq0 : 0 < ν.real W) (hq1 : ν.real W < 1) :
    μ.real W * Real.log (1 / ν.real W) ≤ FiniteInformation.finiteKL μ ν + Real.log 2 := by
  exact (event_log_le_binaryKL_add_log_two measureReal_nonneg measureReal_le_one hq0 hq1).trans
    (add_le_add (event_binaryKL_le μ ν hac W hq0 hq1) le_rfl)

omit [Fintype α] [MeasurableSingletonClass α] in
/-- Null endpoint events are handled by absolute continuity, without logarithms at zero. -/
theorem event_zero_of_ac (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) (W : Set α) (hq : ν.real W = 0) : μ.real W = 0 := by
  have hz : ν W = 0 := (measureReal_eq_zero_iff (measure_ne_top ν W)).1 hq
  simp only [measureReal_def, hac hz, ENNReal.toReal_zero]

/-- The full endpoint follows by applying absolute continuity to the complement. -/
theorem event_one_of_ac (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) (W : Set α) (hq : ν.real W = 1) : μ.real W = 1 := by
  have hW : MeasurableSet W := (Set.to_countable W).measurableSet
  have hz : ν.real Wᶜ = 0 := by rw [measureReal_compl hW, probReal_univ, hq]; ring
  have hp := event_zero_of_ac μ ν hac Wᶜ hz
  rw [measureReal_compl hW, probReal_univ] at hp
  linarith

end Event

end BestOfBothWorlds.BernoulliInformation
