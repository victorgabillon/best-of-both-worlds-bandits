module

public import BestOfBothWorlds.SeededLikelihood
public import BestOfBothWorlds.SeededLearnerRestriction
public import BestOfBothWorlds.BernoulliInformation

/-!
Observed-transcript change of measure for one deterministic arm and round set.
The two environments are constructed from common finite reward laws and changed
Bernoulli entries. The learner seed is arbitrary and may persist through the
final recommendation. All probabilities below are actual transcript laws.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BestOfBothWorlds.SeededChangeOfMeasure

open SeededLearner

variable {Seed Reward : Type*} [MeasurableSpace Seed] [MeasurableSpace Reward]
  [Fintype Reward] [MeasurableSingletonClass Reward] {K n : ℕ}

/-- The only environment difference is the prescribed arm-round rectangle. -/
noncomputable def environment (common : Fin n → Fin K → Measure Reward)
    (k : Fin K) (T : Finset (Fin n)) (one zero : Reward) (p : unitInterval)
    (t : Fin n) (j : Fin K) : Measure Reward :=
  if t ∈ T ∧ j = k then bernoulliMeasure one zero p else common t j

instance environment_isProbabilityMeasure (common : Fin n → Fin K → Measure Reward)
    [∀ t j, IsProbabilityMeasure (common t j)]
    (k : Fin K) (T : Finset (Fin n)) (one zero : Reward) (p : unitInterval)
    (t : Fin n) (j : Fin K) :
    IsProbabilityMeasure (environment common k T one zero p t j) := by
  unfold environment
  split_ifs <;> infer_instance

omit [Fintype Reward] in
/-- An interior Bernoulli law has exactly its two prescribed atoms as support. -/
theorem bernoulli_atom_eq_zero_iff (one zero : Reward) (hneq : one ≠ zero)
    (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (x : Reward) :
    bernoulliMeasure one zero p {x} = 0 ↔ x ≠ one ∧ x ≠ zero := by
  classical
  rw [← measureReal_eq_zero_iff (measure_ne_top (bernoulliMeasure one zero p) {x})]
  by_cases ho : x = one
  · subst x
    rw [bernoulliMeasure_real_apply_of_mem_of_notMem p (measurableSet_singleton one)
      (by simp) (by simpa only [Set.mem_singleton_iff] using hneq.symm)]
    simp [hp0.ne']
  · by_cases hz : x = zero
    · subst x
      rw [bernoulliMeasure_real_apply_of_notMem_of_mem p (measurableSet_singleton zero)
        (by simpa only [Set.mem_singleton_iff] using hneq) (by simp)]
      simp [(sub_pos.mpr hp1).ne', hneq.symm]
    · rw [bernoulliMeasure_real_apply_of_notMem_of_notMem p (measurableSet_singleton x)
        (by simpa only [Set.mem_singleton_iff] using Ne.symm ho)
        (by simpa only [Set.mem_singleton_iff] using Ne.symm hz)]
      simp [ho, hz]

omit [Fintype Reward] in
theorem environment_support (common : Fin n → Fin K → Measure Reward)
    (k : Fin K) (T : Finset (Fin n)) (one zero : Reward) (hneq : one ≠ zero)
    (u v : unitInterval) (hu0 : 0 < (u : ℝ)) (hu1 : (u : ℝ) < 1)
    (hv0 : 0 < (v : ℝ)) (hv1 : (v : ℝ) < 1) :
    ∀ t j x, environment common k T one zero u t j {x} = 0 ↔
      environment common k T one zero v t j {x} = 0 := by
  intro t j x
  by_cases h : t ∈ T ∧ j = k
  · simp only [environment, h]
    exact (bernoulli_atom_eq_zero_iff one zero hneq u hu0 hu1 x).trans
      (bernoulli_atom_eq_zero_iff one zero hneq v hv0 hv1 x).symm
  · simp only [environment, h, ite_false]

theorem finiteKL_bernoulli (one zero : Reward) (hneq : one ≠ zero)
    (u v : unitInterval) (hu0 : 0 < (u : ℝ)) (hu1 : (u : ℝ) < 1)
    (hv0 : 0 < (v : ℝ)) (hv1 : (v : ℝ) < 1) :
    FiniteInformation.finiteKL (bernoulliMeasure one zero u) (bernoulliMeasure one zero v) =
      BernoulliInformation.binaryKL u v := by
  have hac : bernoulliMeasure one zero u ≪ bernoulliMeasure one zero v :=
    FiniteInformation.absolutelyContinuous_of_atom_support _ _ fun x hx =>
      (bernoulli_atom_eq_zero_iff one zero hneq u hu0 hu1 x).mpr
        ((bernoulli_atom_eq_zero_iff one zero hneq v hv0 hv1 x).mp hx)
  rw [← FiniteInformation.toReal_klDiv_eq_finiteKL _ _ hac,
    BernoulliInformation.klDiv_bernoulliMeasure one zero hneq u v hv0 hv1,
    ENNReal.toReal_ofReal (BernoulliInformation.binaryKL_nonneg u.2.1 u.2.2 hv0 hv1)]

/-- Each environment is the same seeded learner applied to an independent
complete table; its transcript already contains the final recommendation. -/
noncomputable def observedLaw (L : Learner Seed Reward K n) (ρ : Measure Seed)
    (common : Fin n → Fin K → Measure Reward) (k : Fin K) (T : Finset (Fin n))
    (one zero : Reward) (p : unitInterval) : Measure (Transcript K Reward n) :=
  L.transcriptLaw ρ (environment common k T one zero p)

instance observedLaw_isProbabilityMeasure (L : Learner Seed Reward K n)
    (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (common : Fin n → Fin K → Measure Reward) [∀ t j, IsProbabilityMeasure (common t j)]
    (k : Fin K) (T : Finset (Fin n)) (one zero : Reward) (p : unitInterval) :
    IsProbabilityMeasure (observedLaw L ρ common k T one zero p) := by
  unfold observedLaw
  infer_instance

variable (L : Learner Seed Reward K n) (ρ : Measure Seed) [IsProbabilityMeasure ρ]
  (common : Fin n → Fin K → Measure Reward) [∀ t j, IsProbabilityMeasure (common t j)]
  (k : Fin K) (T : Finset (Fin n)) (one zero : Reward) (hneq : one ≠ zero)
  (u v : unitInterval) (hu0 : 0 < (u : ℝ)) (hu1 : (u : ℝ) < 1)
  (hv0 : 0 < (v : ℝ)) (hv1 : (v : ℝ) < 1)

include hneq hu0 hu1 hv0 hv1

/-- Lemma 10(i), without positive action probabilities or positive atom weights. -/
theorem lemma10_common_support (z : Transcript K Reward n) :
    observedLaw L ρ common k T one zero u {z} = 0 ↔
      observedLaw L ρ common k T one zero v {z} = 0 :=
  L.transcript_atom_eq_zero_iff ρ _ _
    (environment_support common k T one zero hneq u v hu0 hu1 hv0 hv1) z

theorem observed_absolutelyContinuous :
    observedLaw L ρ common k T one zero u ≪ observedLaw L ρ common k T one zero v :=
  L.transcript_absolutelyContinuous ρ _ _
    (environment_support common k T one zero hneq u v hu0 hu1 hv0 hv1)

/-- Lemma 10(i) in the manuscript's explicit positive-support form. -/
theorem lemma10_positive_support (z : Transcript K Reward n) :
    0 < (observedLaw L ρ common k T one zero u).real {z} ↔
      0 < (observedLaw L ρ common k T one zero v).real {z} := by
  constructor
  · exact FiniteInformation.atom_real_pos_of_ac _ _
      (observed_absolutelyContinuous L ρ common k T one zero hneq u v hu0 hu1 hv0 hv1) z
  · exact FiniteInformation.atom_real_pos_of_ac _ _
      (observed_absolutelyContinuous L ρ common k T one zero hneq v u hv0 hv1 hu0 hu1) z

/-- Lemma 10(ii): the expected count is under environment A and is the count
of actual selected arms at the deterministic informative rounds. -/
theorem lemma10_kl_identity :
    FiniteInformation.finiteKL (observedLaw L ρ common k T one zero u)
        (observedLaw L ρ common k T one zero v) =
      L.expectedPullCount ρ (environment common k T one zero u) T k *
        BernoulliInformation.binaryKL u v := by
  classical
  unfold observedLaw
  rw [L.finiteKL_eq_sum_action_entryKL ρ _ _
    (environment_support common k T one zero hneq u v hu0 hu1 hv0 hv1)]
  have hentry (t : Fin n) (j : Fin K) :
      FiniteInformation.finiteKL (environment common k T one zero u t j)
          (environment common k T one zero v t j) =
        if t ∈ T ∧ j = k then BernoulliInformation.binaryKL u v else 0 := by
    by_cases h : t ∈ T ∧ j = k
    · simpa [environment, h] using
        finiteKL_bernoulli one zero hneq u v hu0 hu1 hv0 hv1
    · simp only [environment, h, ite_false, FiniteInformation.finiteKL_self]
  rw [L.expectedPullCount_eq_sum_action_mass, Finset.sum_mul]
  calc
    _ = ∑ t, if t ∈ T then
        (L.transcriptLaw ρ (environment common k T one zero u)).real {z | (z.1 t).1 = k} *
          BernoulliInformation.binaryKL u v else 0 := by
      apply Finset.sum_congr rfl
      intro t _
      by_cases ht : t ∈ T <;> simp [hentry, ht]
    _ = _ := Finset.sum_ite_mem_eq _ _

/-- Actual Mathlib divergence is proved finite before taking its real value. -/
theorem lemma10_kl_ne_top :
    InformationTheory.klDiv (observedLaw L ρ common k T one zero u)
      (observedLaw L ρ common k T one zero v) ≠ ⊤ :=
  FiniteInformation.klDiv_ne_top _ _
    (observed_absolutelyContinuous L ρ common k T one zero hneq u v hu0 hu1 hv0 hv1)

/-- ENNReal-valued Mathlib KL also equals the finite expected information. -/
theorem lemma10_kl_eq_ofReal :
    InformationTheory.klDiv (observedLaw L ρ common k T one zero u)
      (observedLaw L ρ common k T one zero v) =
      ENNReal.ofReal (L.expectedPullCount ρ (environment common k T one zero u) T k *
        BernoulliInformation.binaryKL u v) := by
  rw [FiniteInformation.klDiv_eq_ofReal_finiteKL _ _
      (observed_absolutelyContinuous L ρ common k T one zero hneq u v hu0 hu1 hv0 hv1),
    lemma10_kl_identity L ρ common k T one zero hneq u v hu0 hu1 hv0 hv1]

/-- The equality also holds for the real value of Mathlib's divergence. -/
theorem lemma10_toReal_kl_identity :
    (InformationTheory.klDiv (observedLaw L ρ common k T one zero u)
        (observedLaw L ρ common k T one zero v)).toReal =
      L.expectedPullCount ρ (environment common k T one zero u) T k *
        BernoulliInformation.binaryKL u v := by
  rw [FiniteInformation.toReal_klDiv_eq_finiteKL _ _
      (observed_absolutelyContinuous L ρ common k T one zero hneq u v hu0 hu1 hv0 hv1),
    lemma10_kl_identity L ρ common k T one zero hneq u v hu0 hu1 hv0 hv1]

/-- Lemma 10(iii), event data processing for any observed-transcript event. -/
theorem lemma10_event_binaryKL (W : Set (Transcript K Reward n))
    (hq0 : 0 < (observedLaw L ρ common k T one zero v).real W)
    (hq1 : (observedLaw L ρ common k T one zero v).real W < 1) :
    BernoulliInformation.binaryKL ((observedLaw L ρ common k T one zero u).real W)
        ((observedLaw L ρ common k T one zero v).real W) ≤
      L.expectedPullCount ρ (environment common k T one zero u) T k *
        BernoulliInformation.binaryKL u v := by
  rw [← lemma10_kl_identity L ρ common k T one zero hneq u v hu0 hu1 hv0 hv1]
  exact BernoulliInformation.event_binaryKL_le _ _
    (observed_absolutelyContinuous L ρ common k T one zero hneq u v hu0 hu1 hv0 hv1) W hq0 hq1

/-- Lemma 10(iii), with logarithms evaluated only at an interior event probability. -/
theorem lemma10_event_log (W : Set (Transcript K Reward n))
    (hq0 : 0 < (observedLaw L ρ common k T one zero v).real W)
    (hq1 : (observedLaw L ρ common k T one zero v).real W < 1) :
    (observedLaw L ρ common k T one zero u).real W *
        Real.log (1 / (observedLaw L ρ common k T one zero v).real W) ≤
      L.expectedPullCount ρ (environment common k T one zero u) T k *
        BernoulliInformation.binaryKL u v + Real.log 2 := by
  rw [← lemma10_kl_identity L ρ common k T one zero hneq u v hu0 hu1 hv0 hv1]
  exact BernoulliInformation.event_log_le _ _
    (observed_absolutelyContinuous L ρ common k T one zero hneq u v hu0 hu1 hv0 hv1) W hq0 hq1

theorem lemma10_event_zero (W : Set (Transcript K Reward n))
    (hq : (observedLaw L ρ common k T one zero v).real W = 0) :
    (observedLaw L ρ common k T one zero u).real W = 0 :=
  BernoulliInformation.event_zero_of_ac _ _
    (observed_absolutelyContinuous L ρ common k T one zero hneq u v hu0 hu1 hv0 hv1) W hq

theorem lemma10_event_one (W : Set (Transcript K Reward n))
    (hq : (observedLaw L ρ common k T one zero v).real W = 1) :
    (observedLaw L ρ common k T one zero u).real W = 1 :=
  BernoulliInformation.event_one_of_ac _ _
    (observed_absolutelyContinuous L ρ common k T one zero hneq u v hu0 hu1 hv0 hv1) W hq

/-- Lemma 10(iv), including empty/full events and zero-mass transcript atoms. -/
theorem lemma10_testing (W : Set (Transcript K Reward n)) :
    (1 / 2 : ℝ) * Real.exp (-
      (L.expectedPullCount ρ (environment common k T one zero u) T k *
        BernoulliInformation.binaryKL u v)) ≤
      (observedLaw L ρ common k T one zero u).real Wᶜ +
        (observedLaw L ρ common k T one zero v).real W := by
  rw [← lemma10_kl_identity L ρ common k T one zero hneq u v hu0 hu1 hv0 hv1]
  exact FiniteInformation.bretagnolle_huber _ _
    (observed_absolutelyContinuous L ρ common k T one zero hneq u v hu0 hu1 hv0 hv1) W

end BestOfBothWorlds.SeededChangeOfMeasure
