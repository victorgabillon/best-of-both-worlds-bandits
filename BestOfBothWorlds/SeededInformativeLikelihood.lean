module

public import BestOfBothWorlds.SeededChangeOfMeasure

/-! The pointwise observed log likelihood contains only informative pulls. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

namespace BestOfBothWorlds.SeededChangeOfMeasure

open SeededLearner

variable {Seed Reward : Type*} [MeasurableSpace Seed] [MeasurableSpace Reward]
  [Fintype Reward] [MeasurableSingletonClass Reward] {K n : ℕ}

omit [Fintype Reward] in
/-- A positive Bernoulli atom is one of the two prescribed rewards. Its log
ratio is consequently the corresponding genuine positive-mass Bernoulli term. -/
theorem bernoulli_log_ratio_on_support (one zero : Reward) (hneq : one ≠ zero)
    (u v : unitInterval) (hu0 : 0 < (u : ℝ)) (hu1 : (u : ℝ) < 1)
    (_hv0 : 0 < (v : ℝ)) (_hv1 : (v : ℝ) < 1)
    (x : Reward) (hx : 0 < (bernoulliMeasure one zero u).real {x}) :
    Real.log ((bernoulliMeasure one zero u).real {x} /
      (bernoulliMeasure one zero v).real {x}) =
      if x = one then Real.log ((u : ℝ) / (v : ℝ))
      else Real.log ((1 - (u : ℝ)) / (1 - (v : ℝ))) := by
  classical
  by_cases ho : x = one
  · subst x
    rw [bernoulliMeasure_real_apply_of_mem_of_notMem u (measurableSet_singleton one)
        (by simp) (by simpa only [Set.mem_singleton_iff] using hneq.symm),
      bernoulliMeasure_real_apply_of_mem_of_notMem v (measurableSet_singleton one)
        (by simp) (by simpa only [Set.mem_singleton_iff] using hneq.symm)]
    simp
  · have hz : x = zero := by
      by_contra hz
      have he := (bernoulli_atom_eq_zero_iff one zero hneq u hu0 hu1 x).mpr ⟨ho, hz⟩
      have hr : (bernoulliMeasure one zero u).real {x} = 0 := by
        simp only [measureReal_def, he, ENNReal.toReal_zero]
      exact hx.ne' hr
    subst x
    rw [bernoulliMeasure_real_apply_of_notMem_of_mem u (measurableSet_singleton zero)
        (by simpa only [Set.mem_singleton_iff] using hneq) (by simp),
      bernoulliMeasure_real_apply_of_notMem_of_mem v (measurableSet_singleton zero)
        (by simpa only [Set.mem_singleton_iff] using hneq) (by simp)]
    simp only [ho, ite_false]

/-- Lemma 10's exact pointwise log likelihood, after cancelling the learner
factor and all common reward factors on proved positive transcript support.
Only fixed informative rounds and actual pulls of k remain. -/
theorem lemma10_log_likelihood (L : Learner Seed Reward K n)
    (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (common : Fin n → Fin K → Measure Reward) [∀ t j, IsProbabilityMeasure (common t j)]
    (k : Fin K) (T : Finset (Fin n)) (one zero : Reward) (hneq : one ≠ zero)
    (u v : unitInterval) (hu0 : 0 < (u : ℝ)) (hu1 : (u : ℝ) < 1)
    (hv0 : 0 < (v : ℝ)) (hv1 : (v : ℝ) < 1)
    (z : Transcript K Reward n)
    (hz : 0 < (observedLaw L ρ common k T one zero u).real {z}) :
    Real.log ((observedLaw L ρ common k T one zero u).real {z} /
        (observedLaw L ρ common k T one zero v).real {z}) =
      ∑ t ∈ T, if (z.1 t).1 = k then
        (if (z.1 t).2 = one then Real.log ((u : ℝ) / (v : ℝ))
          else Real.log ((1 - (u : ℝ)) / (1 - (v : ℝ)))) else 0 := by
  classical
  change Real.log ((L.transcriptLaw ρ (environment common k T one zero u)).real {z} /
    (L.transcriptLaw ρ (environment common k T one zero v)).real {z}) = _
  rw [L.log_likelihood_eq ρ _ _
    (environment_support common k T one zero hneq u v hu0 hu1 hv0 hv1) z hz]
  have ht (t : Fin n) :
      Real.log ((environment common k T one zero u t (z.1 t).1).real {(z.1 t).2} /
        (environment common k T one zero v t (z.1 t).1).real {(z.1 t).2}) =
      if t ∈ T then (if (z.1 t).1 = k then
        (if (z.1 t).2 = one then Real.log ((u : ℝ) / (v : ℝ))
          else Real.log ((1 - (u : ℝ)) / (1 - (v : ℝ)))) else 0) else 0 := by
    have hp := L.observed_atom_pos ρ (environment common k T one zero u) z hz t
    by_cases htime : t ∈ T
    · by_cases harm : (z.1 t).1 = k
      · have hBern : 0 < (bernoulliMeasure one zero u).real {(z.1 t).2} := by
          simpa [environment, htime, harm] using hp
        simpa [environment, htime, harm] using
          bernoulli_log_ratio_on_support one zero hneq u v hu0 hu1 hv0 hv1 (z.1 t).2 hBern
      · have hc : 0 < (common t (z.1 t).1).real {(z.1 t).2} := by
          simpa [environment, harm] using hp
        simp [environment, htime, harm, div_self hc.ne']
    · have hc : 0 < (common t (z.1 t).1).real {(z.1 t).2} := by
        simpa [environment, htime] using hp
      simp [environment, htime, div_self hc.ne']
  calc
    _ = ∑ t, if t ∈ T then (if (z.1 t).1 = k then
        (if (z.1 t).2 = one then Real.log ((u : ℝ) / (v : ℝ))
          else Real.log ((1 - (u : ℝ)) / (1 - (v : ℝ)))) else 0) else 0 :=
      Finset.sum_congr rfl fun t _ => ht t
    _ = _ := Finset.sum_ite_mem_eq _ _

end BestOfBothWorlds.SeededChangeOfMeasure
