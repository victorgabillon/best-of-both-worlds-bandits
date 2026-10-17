module

public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
Finite probability KL formulas, as an explicit bridge to Mathlib's actual
ENNReal-valued Kullback--Leibler divergence. Finiteness is proved before its
real value is used. Zero-mass atoms contribute zero to the finite sum.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace BestOfBothWorlds.FiniteInformation

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The manuscript's finite KL sum, including zero-weight atoms harmlessly. -/
noncomputable def finiteKL (μ ν : Measure α) : ℝ :=
  ∑ a, μ.real {a} * Real.log (μ.real {a} / ν.real {a})

omit [MeasurableSingletonClass α] in
/-- The support premise only excludes a positive numerator at a zero denominator. -/
theorem absolutelyContinuous_of_atom_support (μ ν : Measure α)
    (hsupport : ∀ a, ν {a} = 0 → μ {a} = 0) : μ ≪ ν := by
  intro s hs
  apply (measure_null_iff_singleton (Set.to_countable s)).2
  intro a ha
  exact hsupport a (measure_mono_null (Set.singleton_subset_iff.mpr ha) hs)

omit [MeasurableSingletonClass α] in
theorem absolutelyContinuous_iff_atom_support (μ ν : Measure α) :
    μ ≪ ν ↔ ∀ a, ν {a} = 0 → μ {a} = 0 :=
  ⟨fun h _a ha => h ha, absolutelyContinuous_of_atom_support μ ν⟩

/-- At an atom with positive denominator mass, the RN derivative is the atom ratio. -/
theorem rnDeriv_atom_toReal (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hac : μ ≪ ν) (a : α) (hν : ν {a} ≠ 0) :
    (μ.rnDeriv ν a).toReal = μ.real {a} / ν.real {a} := by
  have heq := Measure.setLIntegral_rnDeriv hac ({a} : Set α)
  rw [lintegral_singleton] at heq
  have hr := congrArg ENNReal.toReal heq
  simp only [ENNReal.toReal_mul] at hr
  have hn : ν.real {a} ≠ 0 :=
    (ENNReal.toReal_pos hν (measure_ne_top ν {a})).ne'
  exact (eq_div_iff hn).2 hr

/-- On a finite probability space, absolute continuity suffices for finite KL. -/
theorem klDiv_ne_top (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) : InformationTheory.klDiv μ ν ≠ ⊤ :=
  InformationTheory.klDiv_ne_top hac Integrable.of_finite

/-- Exact finite-support formula for the real value of Mathlib KL. -/
theorem toReal_klDiv_eq_finiteKL (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hac : μ ≪ ν) :
    (InformationTheory.klDiv μ ν).toReal = finiteKL μ ν := by
  rw [InformationTheory.toReal_klDiv hac Integrable.of_finite]
  simp only [probReal_univ, add_sub_cancel_right]
  rw [integral_fintype Integrable.of_finite]
  unfold finiteKL
  apply Finset.sum_congr rfl
  intro a _
  by_cases hμ : μ {a} = 0
  · simp [measureReal_def, hμ]
  · have hν : ν {a} ≠ 0 := fun h => hμ (hac h)
    rw [llr, rnDeriv_atom_toReal μ ν hac a hν]
    rfl

theorem finiteKL_nonneg (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hac : μ ≪ ν) :
    0 ≤ finiteKL μ ν := by
  rw [← toReal_klDiv_eq_finiteKL μ ν hac]
  exact ENNReal.toReal_nonneg

/-- Agreement with Mathlib in ENNReal, after a genuine finiteness proof. -/
theorem klDiv_eq_ofReal_finiteKL (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hac : μ ≪ ν) :
    InformationTheory.klDiv μ ν = ENNReal.ofReal (finiteKL μ ν) := by
  rw [← toReal_klDiv_eq_finiteKL μ ν hac, ENNReal.ofReal_toReal (klDiv_ne_top μ ν hac)]

theorem finiteKL_self (μ : Measure α) [IsProbabilityMeasure μ] : finiteKL μ μ = 0 := by
  rw [← toReal_klDiv_eq_finiteKL μ μ Measure.AbsolutelyContinuous.rfl]
  simp

theorem atom_sum_one (μ : Measure α) [IsProbabilityMeasure μ] :
    (∑ a, μ.real {a}) = 1 := by
  simp

open scoped Classical in
theorem real_event_eq_sum (μ : Measure α) [IsProbabilityMeasure μ] (W : Set α) :
    μ.real W = ∑ a, if a ∈ W then μ.real {a} else 0 := by
  classical
  rw [← Finset.sum_filter]
  have hset : ((Finset.univ : Finset α).filter (· ∈ W) : Set α) = W := by
    ext a
    simp
  rw [sum_measureReal_singleton, hset]

omit [Fintype α] [MeasurableSingletonClass α] in
theorem atom_real_pos_of_ac (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) (a : α) (hμ : 0 < μ.real {a}) : 0 < ν.real {a} := by
  apply ENNReal.toReal_pos _ (measure_ne_top ν {a})
  intro hν
  have hz := hac hν
  simp only [measureReal_def, hz, ENNReal.toReal_zero] at hμ
  exact (lt_irrefl _ hμ)

omit [Fintype α] [MeasurableSingletonClass α] in
/-- A measurable encoding with a measurable left inverse preserves actual KL. -/
theorem klDiv_map_eq_of_leftInverse {β : Type*} [MeasurableSpace β]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : α → β) (g : β → α) (hf : Measurable f) (hg : Measurable g)
    (hgf : Function.LeftInverse g f) :
    InformationTheory.klDiv (μ.map f) (ν.map f) = InformationTheory.klDiv μ ν := by
  apply le_antisymm (InformationTheory.klDiv_map_le μ ν hf)
  have h := InformationTheory.klDiv_map_le (μ.map f) (ν.map f) hg
  have hcomp : g ∘ f = id := funext hgf
  simpa only [Measure.map_map hg hf, hcomp, Measure.map_id] using h

/-- Hellinger affinity of the two finite observed laws. -/
noncomputable def affinity (μ ν : Measure α) : ℝ :=
  ∑ a, Real.sqrt (μ.real {a} * ν.real {a})

/-- Total common mass of the two finite observed laws. -/
noncomputable def overlap (μ ν : Measure α) : ℝ :=
  ∑ a, min (μ.real {a}) (ν.real {a})

omit [MeasurableSingletonClass α] in
theorem affinity_nonneg (μ ν : Measure α) : 0 ≤ affinity μ ν :=
  Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)

omit [MeasurableSingletonClass α] in
theorem overlap_nonneg (μ ν : Measure α) : 0 ≤ overlap μ ν :=
  Finset.sum_nonneg (fun _ _ => le_min measureReal_nonneg measureReal_nonneg)

/-- Jensen's inequality for logarithms gives the lower affinity estimate. -/
theorem exp_neg_finiteKL_le_affinity_sq (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hac : μ ≪ ν) :
    Real.exp (-finiteKL μ ν) ≤ (affinity μ ν) ^ 2 := by
  classical
  let R : α → ℝ := fun a => if μ.real {a} = 0 then 1 else Real.sqrt (ν.real {a} / μ.real {a})
  have hR (a : α) : 0 < R a := by
    by_cases hp : μ.real {a} = 0
    · simp [R, hp]
    · have hp' : 0 < μ.real {a} := lt_of_le_of_ne measureReal_nonneg (Ne.symm hp)
      have hq := atom_real_pos_of_ac μ ν hac a hp'
      simpa only [R, ite_eq_right hp] using Real.sqrt_pos.mpr (div_pos hq hp')
  have hroot (a : α) : μ.real {a} * R a = Real.sqrt (μ.real {a} * ν.real {a}) := by
    by_cases hp : μ.real {a} = 0
    · simp [R, hp]
    · have hp' : 0 < μ.real {a} := lt_of_le_of_ne measureReal_nonneg (Ne.symm hp)
      have hq : 0 ≤ ν.real {a} := measureReal_nonneg
      simp only [R, ite_eq_right hp]
      apply (sq_eq_sq₀ (mul_nonneg hp'.le (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)).1
      rw [mul_pow, Real.sq_sqrt (div_nonneg hq hp'.le), Real.sq_sqrt (mul_nonneg hp'.le hq)]
      field_simp [hp]
  have hlog (a : α) : μ.real {a} * Real.log (R a) =
      -(μ.real {a} * Real.log (μ.real {a} / ν.real {a})) / 2 := by
    by_cases hp : μ.real {a} = 0
    · simp [hp]
    · have hp' : 0 < μ.real {a} := lt_of_le_of_ne measureReal_nonneg (Ne.symm hp)
      have hq := atom_real_pos_of_ac μ ν hac a hp'
      rw [show R a = Real.sqrt (ν.real {a} / μ.real {a}) by simp only [R, ite_eq_right hp],
        Real.log_sqrt (div_nonneg hq.le hp'.le), Real.log_div hq.ne' hp'.ne',
        Real.log_div hp'.ne' hq.ne']
      ring
  have hConc : ConcaveOn ℝ (Set.Ioi 0) Real.log := StrictConcaveOn.concaveOn strictConcaveOn_log_Ioi
  have hJ := hConc.le_map_sum
    (t := Finset.univ) (w := fun a : α => μ.real {a}) (p := R)
    (fun _ _ => measureReal_nonneg) (atom_sum_one μ) (fun a _ => hR a)
  simp only [smul_eq_mul] at hJ
  have hsumR : (∑ a, μ.real {a} * R a) = affinity μ ν := by
    exact Finset.sum_congr rfl (fun a _ => hroot a)
  have hsumlog : (∑ a, μ.real {a} * Real.log (R a)) = -finiteKL μ ν / 2 := by
    simp_rw [hlog]
    rw [← Finset.sum_div, Finset.sum_neg_distrib]
    rfl
  rw [hsumR, hsumlog] at hJ
  have hsumpos : 0 < affinity μ ν := by
    have hex : ∃ a, 0 < μ.real {a} := by
      by_contra hn
      push Not at hn
      have hz : (∑ a, μ.real {a}) = 0 :=
        Finset.sum_eq_zero (fun a _ => le_antisymm (hn a) measureReal_nonneg)
      rw [atom_sum_one μ] at hz
      norm_num at hz
    obtain ⟨a, ha⟩ := hex
    have hterm : 0 < μ.real {a} * R a := mul_pos ha (hR a)
    rw [← hsumR]
    exact hterm.trans_le (Finset.single_le_sum
      (fun b _ => mul_nonneg measureReal_nonneg (hR b).le) (Finset.mem_univ a))
  have he := Real.exp_le_exp.mpr hJ
  rw [Real.exp_log hsumpos] at he
  have hsquare := mul_self_le_mul_self (Real.exp_pos _).le he
  have hexp : Real.exp (-finiteKL μ ν) = Real.exp (-finiteKL μ ν / 2) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  simpa only [pow_two] using hsquare

/-- Cauchy--Schwarz compares affinity with overlap without positive atom assumptions. -/
theorem affinity_sq_le_two_overlap (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (affinity μ ν) ^ 2 ≤ 2 * overlap μ ν := by
  have hCS := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (s := (Finset.univ : Finset α))
    (r := fun a => Real.sqrt (μ.real {a} * ν.real {a}))
    (f := fun a => min (μ.real {a}) (ν.real {a}))
    (g := fun a => max (μ.real {a}) (ν.real {a}))
    (fun _ _ => le_min measureReal_nonneg measureReal_nonneg)
    (fun _ _ => le_max_of_le_left measureReal_nonneg)
    (fun a _ => by rw [Real.sq_sqrt (mul_nonneg measureReal_nonneg measureReal_nonneg), min_mul_max])
  have hmass : (∑ a, min (μ.real {a}) (ν.real {a})) +
      (∑ a, max (μ.real {a}) (ν.real {a})) = 2 := by
    rw [← Finset.sum_add_distrib]
    simp_rw [min_add_max]
    rw [Finset.sum_add_distrib, atom_sum_one μ, atom_sum_one ν]
    norm_num
  change affinity μ ν ^ 2 ≤ overlap μ ν * (∑ a, max (μ.real {a}) (ν.real {a})) at hCS
  change overlap μ ν + (∑ a, max (μ.real {a}) (ν.real {a})) = 2 at hmass
  have hmax : (∑ a, max (μ.real {a}) (ν.real {a})) = 2 - overlap μ ν := by linarith
  rw [hmax] at hCS
  nlinarith [sq_nonneg (overlap μ ν)]

theorem overlap_le_testing_error (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (W : Set α) :
    overlap μ ν ≤ μ.real Wᶜ + ν.real W := by
  classical
  rw [real_event_eq_sum μ Wᶜ, real_event_eq_sum ν W, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : a ∈ W
  · simp only [Set.mem_compl_iff, ha, not_true_eq_false, ite_false, ite_true, zero_add]
    exact min_le_right _ _
  · simp only [Set.mem_compl_iff, ha, not_false_eq_true, ite_true, ite_false, add_zero]
    exact min_le_left _ _

/-- Bretagnolle--Huber for finite actual laws, including empty/full events and null atoms. -/
theorem bretagnolle_huber (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hac : μ ≪ ν) (W : Set α) :
    (1 / 2 : ℝ) * Real.exp (-finiteKL μ ν) ≤ μ.real Wᶜ + ν.real W := by
  have ha := exp_neg_finiteKL_le_affinity_sq μ ν hac
  have hb := affinity_sq_le_two_overlap μ ν
  have hc := overlap_le_testing_error μ ν W
  linarith

end BestOfBothWorlds.FiniteInformation
