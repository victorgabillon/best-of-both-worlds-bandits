module

public import BestOfBothWorlds.SeededLearner
public import BestOfBothWorlds.RealizedGaps
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
Hoeffding bounds for full-table events. These events retain every table entry,
including rewards the learner never observes; no transcript conditioning occurs.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace BestOfBothWorlds.LowerBounds

/-- Two-sided Hoeffding for a finite independent family in [0,1], proved from
Mathlib's bounded-variable sub-Gaussian and independent-sum infrastructure. -/
theorem finite_bounded_sum_deviation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m : ℕ} (_hm : 0 < m)
    (X : Fin m → Ω → ℝ) (hX : ∀ t, Measurable (X t))
    (hind : iIndepFun X μ) (hbound : ∀ t ω, X t ω ∈ Set.Icc (0 : ℝ) 1)
    (ε : ℝ) (hε : 0 ≤ ε) :
    μ.real {ω | ε < |(∑ t, X t ω) - ∑ t, ∫ w, X t w ∂μ|} ≤
      2 * Real.exp (-2 * ε ^ 2 / (m : ℝ)) := by
  classical
  let Y := fun t ω => X t ω - ∫ w, X t w ∂μ
  have hYind : iIndepFun Y μ :=
    hind.comp (fun t x => x - ∫ w, X t w ∂μ) (fun _ => measurable_id.sub_const _)
  have hsub : ∀ t, HasSubgaussianMGF (Y t) (1 / 4 : ℝ≥0) μ := by
    intro t
    have h := hasSubgaussianMGF_of_mem_Icc (μ := μ) (hX t).aemeasurable
      (Filter.Eventually.of_forall (hbound t))
    convert h using 1
    norm_num
  have hs := HasSubgaussianMGF.sum_of_iIndepFun hYind
    (s := Finset.univ) (c := fun _ => (1 / 4 : ℝ≥0)) (fun t _ => hsub t)
  have hplus := hs.measure_ge_le hε
  have hminus := hs.neg.measure_ge_le hε
  have heq : ∀ ω, (∑ t, X t ω) - ∑ t, ∫ w, X t w ∂μ = ∑ t, Y t ω := by
    intro ω
    simp [Y, Finset.sum_sub_distrib]
  have hsubset : {ω | ε < |(∑ t, X t ω) - ∑ t, ∫ w, X t w ∂μ|} ⊆
      {ω | ε ≤ ∑ t, Y t ω} ∪ {ω | ε ≤ -(∑ t, Y t ω)} := by
    intro ω hω
    rw [Set.mem_ofPred_eq, heq] at hω
    change ε ≤ ∑ t, Y t ω ∨ ε ≤ -(∑ t, Y t ω)
    rcases (lt_abs.mp hω) with h | h
    · exact Or.inl h.le
    · exact Or.inr (by linarith)
  have hvar : (2 : ℝ) * ((∑ _t : Fin m, (1 / 4 : ℝ≥0) : ℝ≥0) : ℝ) = (m : ℝ) / 2 := by simp; ring
  calc
    _ ≤ μ.real ({ω | ε ≤ ∑ t, Y t ω} ∪ {ω | ε ≤ -(∑ t, Y t ω)}) := measureReal_mono hsubset
    _ ≤ μ.real {ω | ε ≤ ∑ t, Y t ω} + μ.real {ω | ε ≤ -(∑ t, Y t ω)} := measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-ε ^ 2 / ((m : ℝ) / 2)) := by
      rw [hvar] at hplus hminus
      exact (add_le_add hplus hminus).trans_eq (by ring)
    _ = _ := by congr 2; ring

variable {Reward : Type*} [MeasurableSpace Reward] [Fintype Reward]
  [MeasurableSingletonClass Reward] {K n : ℕ}

/-- Complete cumulative table reward, regardless of which arms were pulled. -/
noncomputable def tableTotal (value : Reward → ℝ) (g : SeededLearner.Table K Reward n)
    (j : Fin K) : ℝ := ∑ t, value (g t j)

/-- Centering by the actual expectation under the complete independent table law. -/
noncomputable def tableExpectedTotal (value : Reward → ℝ)
    (ν : Fin n → Fin K → Measure Reward) (j : Fin K) : ℝ :=
  ∑ t, ∫ g, value (g t j) ∂SeededLearner.Learner.tableLaw ν

/-- The complete-table good event from Appendices D and E. -/
def goodTable (value : Reward → ℝ) (ν : Fin n → Fin K → Measure Reward)
    (ε : ℝ) : Set (SeededLearner.Table K Reward n) :=
  {g | ∀ j, |tableTotal value g j - tableExpectedTotal value ν j| ≤ ε}

/-- A finite actual table is extended by zeros beyond the fixed horizon, for
interoperation with the established realized-gap definitions. -/
noncomputable def realTable (value : Reward → ℝ) (g : SeededLearner.Table K Reward n) :
    ℕ → Fin K → ℝ :=
  fun t j => if ht : t < n then value (g ⟨t, ht⟩ j) else 0

omit [MeasurableSpace Reward] [Fintype Reward] [MeasurableSingletonClass Reward] in
theorem realTable_cumulative (value : Reward → ℝ)
    (g : SeededLearner.Table K Reward n) (j : Fin K) :
    RealizedGaps.cumulative (realTable value g) n j = tableTotal value g j := by
  exact (Finset.sum_fin_eq_sum_range (fun t => value (g t j))).symm

omit [MeasurableSpace Reward] [Fintype Reward] [MeasurableSingletonClass Reward] in
theorem realTable_bounded (value : Reward → ℝ)
    (hvalue : ∀ x, value x ∈ Set.Icc (0 : ℝ) 1)
    (g : SeededLearner.Table K Reward n) :
    ∀ t < n, ∀ j, realTable value g t j ∈ Set.Icc (0 : ℝ) 1 := by
  intro t ht j
  simpa only [realTable, dite_eq_left ht] using hvalue (g ⟨t, ht⟩ j)

omit [Fintype Reward] [MeasurableSingletonClass Reward] in
/-- Every coordinate marginal of the actual independent table is its specified
entry distribution. This also justifies computing the complete expected gains. -/
theorem table_entry_law (ν : Fin n → Fin K → Measure Reward)
    [∀ t j, IsProbabilityMeasure (ν t j)] (t : Fin n) (j : Fin K) :
    (SeededLearner.Learner.tableLaw ν).map (fun g => g t j) = ν t j := by
  classical
  have hrow : (SeededLearner.Learner.tableLaw ν).map (Function.eval t) = Measure.pi (ν t) := by
    simp [SeededLearner.Learner.tableLaw, Measure.pi_map_eval]
  calc
    _ = ((SeededLearner.Learner.tableLaw ν).map (Function.eval t)).map (Function.eval j) :=
      (Measure.map_map (measurable_pi_apply j) (measurable_pi_apply t)).symm
    _ = ν t j := by rw [hrow]; simp [Measure.pi_map_eval]

theorem table_entry_integral (ν : Fin n → Fin K → Measure Reward)
    [∀ t j, IsProbabilityMeasure (ν t j)] (value : Reward → ℝ) (t : Fin n) (j : Fin K) :
    (∫ g, value (g t j) ∂SeededLearner.Learner.tableLaw ν) = ∫ x, value x ∂ν t j := by
  have hvalue : Measurable value := measurable_of_countable value
  have heval : Measurable (fun g : SeededLearner.Table K Reward n => g t j) :=
    (measurable_pi_apply j).comp (measurable_pi_apply t)
  calc
    _ = ∫ x, value x ∂(SeededLearner.Learner.tableLaw ν).map (fun g => g t j) :=
      (integral_map heval.aemeasurable hvalue.aestronglyMeasurable).symm
    _ = _ := by rw [table_entry_law]

theorem tableExpectedTotal_eq_sum_entry_integrals (ν : Fin n → Fin K → Measure Reward)
    [∀ t j, IsProbabilityMeasure (ν t j)] (value : Reward → ℝ) (j : Fin K) :
    tableExpectedTotal value ν j = ∑ t, ∫ x, value x ∂ν t j := by
  unfold tableExpectedTotal
  apply Finset.sum_congr rfl
  intro t _
  exact table_entry_integral ν value t j

/-- The Appendix E full-table concentration bound with its exact exponent. -/
theorem goodTable_compl_bound (ν : Fin n → Fin K → Measure Reward)
    [∀ t j, IsProbabilityMeasure (ν t j)] (hn : 0 < n)
    (value : Reward → ℝ) (hvalue : ∀ x, value x ∈ Set.Icc (0 : ℝ) 1)
    (d : ℝ) (hd : 0 ≤ d) :
    (SeededLearner.Learner.tableLaw ν).real (goodTable value ν ((n : ℝ) * d / 16))ᶜ ≤
      2 * (K : ℝ) * Real.exp (-(n : ℝ) * d ^ 2 / 128) := by
  classical
  let μ := SeededLearner.Learner.tableLaw ν
  have hsingle : ∀ j : Fin K,
      μ.real {g | (n : ℝ) * d / 16 <
        |tableTotal value g j - tableExpectedTotal value ν j|} ≤
        2 * Real.exp (-(n : ℝ) * d ^ 2 / 128) := by
    intro j
    have hfun : Measurable value := measurable_of_countable value
    have hind : iIndepFun (fun t g => value (g t j)) μ := by
      exact iIndepFun_pi (μ := fun t => Measure.pi (ν t))
        (X := fun _ row => value (row j))
        (fun _ => (hfun.comp (measurable_pi_apply j)).aemeasurable)
    have h := finite_bounded_sum_deviation μ hn (fun t g => value (g t j))
      (fun t => hfun.comp ((measurable_pi_apply j).comp (measurable_pi_apply t)))
      hind (fun _ g => hvalue _) ((n : ℝ) * d / 16) (by positivity)
    have heq : -2 * ((n : ℝ) * d / 16) ^ 2 / (n : ℝ) =
        -(n : ℝ) * d ^ 2 / 128 := by
      have hnne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      field_simp
      ring
    simpa only [tableTotal, tableExpectedTotal, heq] using h
  have hset : (goodTable value ν ((n : ℝ) * d / 16))ᶜ =
      ⋃ j : Fin K, {g | (n : ℝ) * d / 16 <
        |tableTotal value g j - tableExpectedTotal value ν j|} := by
    ext g
    simp only [goodTable, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall,
      not_le, Set.mem_iUnion]
  rw [hset]
  calc
    _ ≤ ∑ j : Fin K, μ.real {g | (n : ℝ) * d / 16 <
      |tableTotal value g j - tableExpectedTotal value ν j|} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : Fin K, 2 * Real.exp (-(n : ℝ) * d ^ 2 / 128) :=
      Finset.sum_le_sum fun j _ => hsingle j
    _ = _ := by simp; ring

end BestOfBothWorlds.LowerBounds
