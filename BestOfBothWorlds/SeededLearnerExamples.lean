module

public import BestOfBothWorlds.SeededLearnerRestriction
public import BestOfBothWorlds.SeededChangeOfMeasure
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Tactic.NormNum

/-!
Symbolic nonvacuity witnesses for the lower-bound learner model: deterministic
choices, positive pre-sampled randomization, a persistent private arm, and a
zero conditional action probability. A finite alphabet of actual real rewards
contains the nonbinary value 1/2.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators

namespace BestOfBothWorlds.SeededLearnerExamples

open SeededLearner

/-- Normalized counting measure, constructed with the existing finite PMF API. -/
noncomputable def uniformMeasure (α : Type*) [Fintype α] [Nonempty α] [MeasurableSpace α] :
    Measure α :=
  (PMF.ofFintype (fun _ : α => (Fintype.card α : ℝ≥0∞)⁻¹) (by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (by simp))).toMeasure

instance uniformMeasure_isProbabilityMeasure (α : Type*) [Fintype α] [Nonempty α]
    [MeasurableSpace α] : IsProbabilityMeasure (uniformMeasure α) := by
  unfold uniformMeasure
  infer_instance

theorem uniformMeasure_atom (α : Type*) [Fintype α] [Nonempty α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (a : α) :
    uniformMeasure α {a} = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  unfold uniformMeasure
  rw [PMF.toMeasure_apply_singleton _ a (measurableSet_singleton a)]
  rfl

theorem uniformMeasure_atom_pos (α : Type*) [Fintype α] [Nonempty α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (a : α) : 0 < uniformMeasure α {a} := by
  rw [uniformMeasure_atom]
  exact ENNReal.inv_pos.mpr (by simp)

variable {Seed Reward : Type*} [MeasurableSpace Seed] [MeasurableSpace Reward] {K n : ℕ}

/-- A deterministic learner is admissible for every measurable private seed type. -/
def deterministic : Learner Seed Reward 2 n where
  action _ _ _ := 0
  action_measurable _ _ := measurable_const
  recommendation _ _ := 0
  recommendation_measurable _ := measurable_const

theorem deterministic_play_action (r : Seed) (g : Table 2 Reward n) (t : Fin n) :
    ((deterministic : Learner Seed Reward 2 n).play r g t).1 = 0 := by
  rw [Learner.play_eq]
  rfl

/-- In particular, positive sampling probabilities are not required. -/
theorem deterministic_zero_probability (ρ : Measure Seed) (g : Table 2 Reward n) (t : Fin n) :
    ρ {r | ((deterministic : Learner Seed Reward 2 n).play r g t).1 = 1} = 0 := by
  have he : {r | ((deterministic : Learner Seed Reward 2 n).play r g t).1 = 1} =
      (∅ : Set Seed) := by
    ext r
    simp only [Set.mem_ofPred_eq, deterministic_play_action, Fin.zero_ne_one, Set.mem_empty_iff_false]
  rw [he, measure_empty]

/-- Every action and the final recommendation are pre-sampled into one seed. -/
def randomized : Learner ((Fin n → Fin K) × Fin K) Reward K n where
  action t r _ := r.1 t
  action_measurable t _ := (measurable_pi_apply t).comp measurable_fst
  recommendation r _ := r.2
  recommendation_measurable _ := measurable_snd

theorem randomized_play_action (r : (Fin n → Fin K) × Fin K)
    (g : Table K Reward n) (t : Fin n) :
    ((randomized : Learner ((Fin n → Fin K) × Fin K) Reward K n).play r g t).1 = r.1 t := by
  rw [Learner.play_eq]
  rfl

/-- Each action has positive probability even after an arbitrary fixed table is chosen. -/
theorem randomized_action_positive [NeZero K] (g : Table K Reward n) (t : Fin n) (k : Fin K) :
    0 < uniformMeasure ((Fin n → Fin K) × Fin K)
      {r | ((randomized : Learner ((Fin n → Fin K) × Fin K) Reward K n).play r g t).1 = k} := by
  let r : (Fin n → Fin K) × Fin K := (fun _ => k, k)
  apply (uniformMeasure_atom_pos _ r).trans_le
  apply measure_mono
  intro q hq
  have hqr : q = r := Set.mem_singleton_iff.mp hq
  subst q
  exact randomized_play_action r g t

/-- One private arm is retained and reused through all rounds and recommendation. -/
def persistent : Learner (Fin 2) Reward 2 n where
  action _ r _ := r
  action_measurable _ _ := measurable_id
  recommendation r _ := r
  recommendation_measurable _ := measurable_id

theorem persistent_play_action (r : Fin 2) (g : Table 2 Reward n) (t : Fin n) :
    ((persistent : Learner (Fin 2) Reward 2 n).play r g t).1 = r := by
  rw [Learner.play_eq]
  rfl

theorem persistent_same_action (r : Fin 2) (g : Table 2 Reward n) (s t : Fin n) :
    ((persistent : Learner (Fin 2) Reward 2 n).play r g s).1 =
      ((persistent : Learner (Fin 2) Reward 2 n).play r g t).1 := by
  rw [persistent_play_action, persistent_play_action]

theorem persistent_first_probability (g : Table 2 Reward 2) :
    uniformMeasure (Fin 2)
      {r | ((persistent : Learner (Fin 2) Reward 2 2).play r g 0).1 = 0} = 1 / 2 := by
  have he : {r | ((persistent : Learner (Fin 2) Reward 2 2).play r g 0).1 = 0} =
      ({0} : Set (Fin 2)) := by
    ext r
    simp only [Set.mem_ofPred_eq, persistent_play_action, Set.mem_singleton_iff]
  rw [he, uniformMeasure_atom]
  norm_num

/-- The conditioning event has mass 1/2, but switching arms has joint mass zero. -/
theorem persistent_zero_joint_probability (g : Table 2 Reward 2) :
    uniformMeasure (Fin 2)
      {r | ((persistent : Learner (Fin 2) Reward 2 2).play r g 0).1 = 0 ∧
        ((persistent : Learner (Fin 2) Reward 2 2).play r g 1).1 = 1} = 0 := by
  have he : {r | ((persistent : Learner (Fin 2) Reward 2 2).play r g 0).1 = 0 ∧
        ((persistent : Learner (Fin 2) Reward 2 2).play r g 1).1 = 1} =
      (∅ : Set (Fin 2)) := by
    ext r
    simp only [Set.mem_ofPred_eq, persistent_play_action, Set.mem_empty_iff_false]
    exact ⟨fun h => Fin.zero_ne_one (h.1.symm.trans h.2), False.elim⟩
  rw [he, measure_empty]

/-- This is literally a finite alphabet of real values, rather than hidden labels. -/
noncomputable def realAlphabet : Finset ℝ := {0, 1 / 2, 1}
abbrev RealReward := ↥realAlphabet

noncomputable def halfReward : RealReward := ⟨1 / 2, by simp [realAlphabet]⟩

theorem realAlphabet_bounds (x : RealReward) : 0 ≤ (x : ℝ) ∧ (x : ℝ) ≤ 1 := by
  have hx := x.property
  simp only [realAlphabet, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with hx | hx | hx <;> rw [hx] <;> norm_num

theorem halfReward_nonbinary : (halfReward : ℝ) ≠ 0 ∧ (halfReward : ℝ) ≠ 1 := by
  norm_num [halfReward]

noncomputable def commonLaw (n : ℕ) : Fin n → Fin 2 → Measure RealReward :=
  fun _ _ => Measure.dirac halfReward

instance commonLaw_isProbabilityMeasure (n : ℕ) (t : Fin n) (k : Fin 2) :
    IsProbabilityMeasure (commonLaw n t k) := by
  unfold commonLaw
  infer_instance

/-- Instantiate the genuine atom factorization with persistent randomness and a
nonbinary deterministic reward common to the two environments. -/
theorem persistent_atom_factorization (z : Transcript 2 RealReward n) :
    (persistent : Learner (Fin 2) RealReward 2 n).transcriptLaw
        (uniformMeasure (Fin 2)) (commonLaw n) {z} =
      uniformMeasure (Fin 2)
          ((persistent : Learner (Fin 2) RealReward 2 n).seedConsistency z) *
        ∏ t, commonLaw n t (z.1 t).1 {(z.1 t).2} :=
  Learner.transcript_atom_factorization persistent (uniformMeasure (Fin 2)) (commonLaw n) z


noncomputable def zeroReward : RealReward := ⟨0, by simp [realAlphabet]⟩
noncomputable def oneReward : RealReward := ⟨1, by simp [realAlphabet]⟩

theorem oneReward_ne_zeroReward : oneReward ≠ zeroReward := by
  intro h
  have hh := congrArg Subtype.val h
  norm_num [oneReward, zeroReward] at hh

noncomputable def quarter : unitInterval := ⟨1 / 4, by norm_num⟩
noncomputable def threeQuarters : unitInterval := ⟨3 / 4, by norm_num⟩

/-- A persistent learner and a genuinely nonbinary common law instantiate
Lemma 10's exact KL equality for any deterministic informative-round set. -/
theorem persistent_lemma10_kl (T : Finset (Fin n)) :
    FiniteInformation.finiteKL
        (SeededChangeOfMeasure.observedLaw (persistent : Learner (Fin 2) RealReward 2 n)
          (uniformMeasure (Fin 2)) (commonLaw n) 1 T oneReward zeroReward quarter)
        (SeededChangeOfMeasure.observedLaw (persistent : Learner (Fin 2) RealReward 2 n)
          (uniformMeasure (Fin 2)) (commonLaw n) 1 T oneReward zeroReward threeQuarters) =
      (persistent : Learner (Fin 2) RealReward 2 n).expectedPullCount (uniformMeasure (Fin 2))
        (SeededChangeOfMeasure.environment (commonLaw n) 1 T oneReward zeroReward quarter) T 1 *
        BernoulliInformation.binaryKL quarter threeQuarters :=
  SeededChangeOfMeasure.lemma10_kl_identity persistent (uniformMeasure (Fin 2))
    (commonLaw n) 1 T oneReward zeroReward oneReward_ne_zeroReward quarter threeQuarters
    (by norm_num [quarter]) (by norm_num [quarter])
    (by norm_num [threeQuarters]) (by norm_num [threeQuarters])

/-- Zero sampling probability genuinely removes the changed arm's information. -/
theorem deterministic_lemma10_zero_information (T : Finset (Fin n)) :
    FiniteInformation.finiteKL
        (SeededChangeOfMeasure.observedLaw (deterministic : Learner (Fin 2) RealReward 2 n)
          (uniformMeasure (Fin 2)) (commonLaw n) 1 T oneReward zeroReward quarter)
        (SeededChangeOfMeasure.observedLaw (deterministic : Learner (Fin 2) RealReward 2 n)
          (uniformMeasure (Fin 2)) (commonLaw n) 1 T oneReward zeroReward threeQuarters) = 0 := by
  rw [SeededChangeOfMeasure.lemma10_kl_identity deterministic (uniformMeasure (Fin 2))
    (commonLaw n) 1 T oneReward zeroReward oneReward_ne_zeroReward quarter threeQuarters
    (by norm_num [quarter]) (by norm_num [quarter])
    (by norm_num [threeQuarters]) (by norm_num [threeQuarters])]
  simp [Learner.expectedPullCount, Learner.pullCount, deterministic_play_action]

/-- The actual persistent-randomness laws also satisfy the testing conclusion. -/
theorem persistent_lemma10_testing (T : Finset (Fin n))
    (W : Set (Transcript 2 RealReward n)) :
    (1 / 2 : ℝ) * Real.exp (-
      ((persistent : Learner (Fin 2) RealReward 2 n).expectedPullCount (uniformMeasure (Fin 2))
        (SeededChangeOfMeasure.environment (commonLaw n) 1 T oneReward zeroReward quarter) T 1 *
          BernoulliInformation.binaryKL quarter threeQuarters)) ≤
      (SeededChangeOfMeasure.observedLaw (persistent : Learner (Fin 2) RealReward 2 n)
        (uniformMeasure (Fin 2)) (commonLaw n) 1 T oneReward zeroReward quarter).real Wᶜ +
      (SeededChangeOfMeasure.observedLaw (persistent : Learner (Fin 2) RealReward 2 n)
        (uniformMeasure (Fin 2)) (commonLaw n) 1 T oneReward zeroReward threeQuarters).real W :=
  SeededChangeOfMeasure.lemma10_testing persistent (uniformMeasure (Fin 2))
    (commonLaw n) 1 T oneReward zeroReward oneReward_ne_zeroReward quarter threeQuarters
    (by norm_num [quarter]) (by norm_num [quarter])
    (by norm_num [threeQuarters]) (by norm_num [threeQuarters]) W

end BestOfBothWorlds.SeededLearnerExamples
