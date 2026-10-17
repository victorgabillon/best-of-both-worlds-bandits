module

public import BestOfBothWorlds.LowerBoundEnvironments
public import BestOfBothWorlds.LowerBoundGapClasses
public import BestOfBothWorlds.LowerBoundConsequences
public import BestOfBothWorlds.LowerBoundExtraction
public import BestOfBothWorlds.FullTableConcentration
public import BestOfBothWorlds.SeededLearnerCounts
public import BestOfBothWorlds.SeededLearnerFreshness
public import BestOfBothWorlds.BernoulliInformation
public import BestOfBothWorlds.SeededChangeOfMeasure
public import BestOfBothWorlds.LowerBoundTesting
public import BestOfBothWorlds.SeededRealTranscript

/-!
The actual stochastic and oblivious-adversarial constructions of Theorem 4.
All probability expressions refer to the same private-seed learner. The selected
arm and rounded initial phase are chosen from the fixed BASE law before any
table or private seed is sampled.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators
open BestOfBothWorlds.SeededLearner

namespace BestOfBothWorlds.LowerBounds.BOBLowerBound

variable {K : ℕ}

/-- A finite two-phase sum, including a full prefix and empty suffix. -/
theorem sum_two_phase (n N : ℕ) (hN : N ≤ n) (a b : ℝ) :
    (∑ t : Fin n, if t.val < N then a else b) =
      (N : ℝ) * a + ((n - N : ℕ) : ℝ) * b := by
  classical
  have hones : (∑ t : Fin n, if t.val < N then (1 : ℝ) else 0) = (N : ℝ) := by
    calc
      _ = ((Learner.prefixRounds n N).card : ℝ) := by
        rw [← Finset.sum_filter]
        simp only [Learner.prefixRounds, Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = _ := congrArg (fun m : ℕ => (m : ℝ)) (Learner.prefixRounds_card n N hN)
  calc
    _ = ∑ t : Fin n, (b + (if t.val < N then (1 : ℝ) else 0) * (a - b)) := by
      apply Finset.sum_congr rfl
      intro t _
      split_ifs <;> ring
    _ = (n : ℝ) * b + (N : ℝ) * (a - b) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hones]
      simp
    _ = _ := by rw [Nat.cast_sub hN]; ring

variable (hK : 2 ≤ K) (gap : Fin K → ℝ)
  (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
  (hsmall : ∀ j, gap j ≤ 1 / 8)

/-- The actual stationary arm laws of the constructed stochastic witness. -/
noncomputable def stochasticArmLaw (k j : Fin K) : Measure (Alphabet hK gap) :=
  alphabetBernoulli hK gap (stoParameter hK gap hpos hsorted hsmall k j)

instance stochasticArmLaw_probability (k j : Fin K) :
    IsProbabilityMeasure (stochasticArmLaw hK gap hpos hsorted hsmall k j) := by
  unfold stochasticArmLaw
  infer_instance

theorem stochasticArmLaw_mean (k j : Fin K) :
    (∫ x, x.val ∂stochasticArmLaw hK gap hpos hsorted hsmall k j) =
      stoMean hK gap k j := integral_alphabetBernoulli hK gap _

theorem stochastic_entries_stationary (n : ℕ) (k : Fin K) (t s : Fin n) (j : Fin K) :
    stoEntries hK gap hpos hsorted hsmall n k t j =
      stoEntries hK gap hpos hsorted hsmall n k s j := rfl

theorem stochastic_actual_unique_best (k : Fin K) :
    ∀ j, j ≠ k →
      (∫ x, x.val ∂stochasticArmLaw hK gap hpos hsorted hsmall k j) <
        ∫ x, x.val ∂stochasticArmLaw hK gap hpos hsorted hsmall k k := by
  intro j hj
  rw [stochasticArmLaw_mean, stochasticArmLaw_mean]
  exact stoMean_strict_best hK gap hpos hsorted k j hj

theorem stochastic_actual_class_four (k : Fin K) (hk : k ≠ firstRank hK) :
    LabelledGapClass hK gap (RealizedGaps.armGap hK
      (fun _ j => ∫ x, x.val ∂stochasticArmLaw hK gap hpos hsorted hsmall k j) 1) 4 := by
  simp only [stochasticArmLaw_mean]
  exact sto_actual_class_four hK gap hpos hsorted k hk

/-- Complexity of the constructed STO's actual sorted mean gaps. -/
noncomputable def stoComplexity (k : Fin K) : ℝ :=
  H_BOB hK (RealizedGaps.sortedProfile hK (fun _ => stoMean hK gap k) 1)

/-- The displayed STO complexity is exactly the complexity of the actual
stationary arm-law means, rather than the reference profile. -/
theorem stoComplexity_eq_actual (k : Fin K) :
    stoComplexity hK gap k = H_BOB hK (RealizedGaps.sortedProfile hK
      (fun _ j => ∫ x, x.val ∂stochasticArmLaw hK gap hpos hsorted hsmall k j) 1) := by
  simp only [stochasticArmLaw_mean]
  rfl

include hpos hsorted in
theorem stoComplexity_pos (k : Fin K) (hk : k ≠ firstRank hK) :
    0 < stoComplexity hK gap k := by
  have hfirst : 0 < RealizedGaps.sortedProfile hK (fun _ => stoMean hK gap k) 1
      (firstRank hK) := by
    simp only [RealizedGaps.sortedProfile, RealizedGaps.gapOrder,
      ← stoGap_eq_actual_mean_gaps hK gap hpos hsorted k hk]
    exact (div_pos hpos (by norm_num : (0 : ℝ) < 4)).trans_le
      (stoGap_min_le hK gap hpos hsorted k _)
  exact (gap_complexities_pos hK _ hfirst).2.1

/-- The complete expected gain of every arm under the actual switched table law. -/
theorem bob_expected_total (n N : ℕ) (hN : N ≤ n) (k j : Fin K) :
    tableExpectedTotal Subtype.val (bobEntries hK gap hpos hsorted hsmall n N k) j =
      (N : ℝ) * baseMean hK gap j + ((n - N : ℕ) : ℝ) * stoMean hK gap k j := by
  rw [tableExpectedTotal_eq_sum_entry_integrals]
  have hentry (t : Fin n) :
      (∫ x, x.val ∂bobEntries hK gap hpos hsorted hsmall n N k t j) =
        if t.val < N then baseMean hK gap j else stoMean hK gap k j := by
    by_cases ht : t.val < N
    · simp only [bobEntries, ht, ite_true]
      exact baseEntries_integral hK gap hpos hsorted hsmall n t j
    · simp only [bobEntries, ht, ite_false]
      exact stoEntries_integral hK gap hpos hsorted hsmall n k t j
  simp_rw [hentry]
  exact sum_two_phase n N hN _ _

theorem bob_expected_first (n N : ℕ) (hN : N ≤ n) (k : Fin K)
    (hk : k ≠ firstRank hK) :
    tableExpectedTotal Subtype.val (bobEntries hK gap hpos hsorted hsmall n N k)
      (firstRank hK) = (n : ℝ) / 2 := by
  rw [bob_expected_total hK gap hpos hsorted hsmall n N hN]
  simp only [stoMean, Ne.symm hk, ite_false, baseMean, ite_true]
  rw [Nat.cast_sub hN]
  ring

theorem bob_expected_selected (n N : ℕ) (hN : N ≤ n) (k : Fin K)
    (hk : k ≠ firstRank hK) :
    tableExpectedTotal Subtype.val (bobEntries hK gap hpos hsorted hsmall n N k) k =
      (N : ℝ) * (1 / 2 - gap k) +
        ((n - N : ℕ) : ℝ) * (1 / 2 + gap (firstRank hK) / 4) := by
  rw [bob_expected_total hK gap hpos hsorted hsmall n N hN]
  simp only [stoMean, ite_true, baseMean, hk, ite_false]

theorem bob_expected_other (n N : ℕ) (hN : N ≤ n) (k j : Fin K)
    (hjfirst : j ≠ firstRank hK) (hjk : j ≠ k) :
    tableExpectedTotal Subtype.val (bobEntries hK gap hpos hsorted hsmall n N k) j =
      (n : ℝ) * (1 / 2 - gap j) := by
  rw [bob_expected_total hK gap hpos hsorted hsmall n N hN]
  simp only [stoMean, hjk, ite_false, baseMean, hjfirst]
  rw [Nat.cast_sub hN]
  ring

/-- Expected selected-arm gap for the exact rounded initial phase. -/
theorem bob_expected_selected_gap (n : ℕ) (hn : 0 < n) (i k : Fin K)
    (hk : k ≠ firstRank hK) :
    let N := LowerBoundSelection.phaseLength n (gap (firstRank hK)) (gap i)
    let M := tableExpectedTotal Subtype.val (bobEntries hK gap hpos hsorted hsmall n N k)
    M (firstRank hK) - M k = (n : ℝ) *
      LowerBoundSelection.expectedSelectedGap n (gap (firstRank hK)) (gap i) (gap k) := by
  dsimp only
  have hN := LowerBoundSelection.phaseLength_le_horizon n (gap (firstRank hK)) (gap i)
  rw [bob_expected_first hK gap hpos hsorted hsmall n _ hN k hk,
    bob_expected_selected hK gap hpos hsorted hsmall n _ hN k hk, Nat.cast_sub hN]
  unfold LowerBoundSelection.expectedSelectedGap
  have hnne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp [hnne]
  ring

/-- The two laws differ exactly at the fixed informative arm and prefix. -/
theorem bob_entries_changed_prefix (n N : ℕ) (k : Fin K) :
    bobEntries hK gap hpos hsorted hsmall n N k =
      fun t j => if t ∈ Learner.prefixRounds n N ∧ j = k then
        alphabetBernoulli hK gap (baseParameter hK gap hpos hsorted hsmall k)
      else stoEntries hK gap hpos hsorted hsmall n k t j := by
  classical
  funext t j
  by_cases ht : t.val < N
  · by_cases hj : j = k
    · subst j
      simp only [bobEntries, ht, ite_true, Learner.mem_prefixRounds, and_self,
        baseEntries]
    · simp only [bobEntries, ht, ite_true, Learner.mem_prefixRounds, hj, and_false, ite_false]
      exact (stoEntries_eq_base_of_ne hK gap hpos hsorted hsmall n k t j hj).symm
  · simp only [bobEntries, ht, ite_false, Learner.mem_prefixRounds, false_and]

theorem sto_entries_changed_prefix (n N : ℕ) (k : Fin K) :
    stoEntries hK gap hpos hsorted hsmall n k =
      fun t j => if t ∈ Learner.prefixRounds n N ∧ j = k then
        alphabetBernoulli hK gap (stoParameter hK gap hpos hsorted hsmall k k)
      else stoEntries hK gap hpos hsorted hsmall n k t j := by
  classical
  funext t j
  by_cases h : t ∈ Learner.prefixRounds n N ∧ j = k
  · rw [ite_eq_left h, h.2]
    rfl
  · rw [ite_eq_right h]

/-- The actual switched ADV and BASE interactions agree throughout the fixed
informative prefix, even for deterministic actions or persistent seeds. -/
theorem bob_expected_count_eq_base {Seed : Type*} [MeasurableSpace Seed]
    (n N : ℕ) (k : Fin K) (L : Learner Seed (Alphabet hK gap) K n)
    (ρ : Measure Seed) [IsProbabilityMeasure ρ] :
    L.expectedPullCount ρ (bobEntries hK gap hpos hsorted hsmall n N k)
        (Learner.prefixRounds n N) k =
      L.expectedPullCount ρ (baseEntries hK gap hpos hsorted hsmall n)
        (Learner.prefixRounds n N) k := by
  rw [L.expectedPullCount_eq_sum_action_mass, L.expectedPullCount_eq_sum_action_mass]
  apply Finset.sum_congr rfl
  intro t ht
  have htprefix := (Learner.mem_prefixRounds n N t).mp ht
  apply congrArg ENNReal.toReal
  apply L.action_mass_eq_of_prefix
  intro u hut j
  simp only [bobEntries, ite_eq_left (hut.trans htprefix)]

/-- Exact observed information for the actual switched ADV and stationary STO,
with the expected informative count replaced by its actual BASE value. -/
theorem bob_kl_identity {Seed : Type*} [MeasurableSpace Seed]
    (n N : ℕ) (k : Fin K) (hk : k ≠ firstRank hK)
    (L : Learner Seed (Alphabet hK gap) K n) (ρ : Measure Seed) [IsProbabilityMeasure ρ] :
    FiniteInformation.finiteKL
        (L.transcriptLaw ρ (bobEntries hK gap hpos hsorted hsmall n N k))
        (L.transcriptLaw ρ (stoEntries hK gap hpos hsorted hsmall n k)) =
      L.expectedPullCount ρ (baseEntries hK gap hpos hsorted hsmall n)
        (Learner.prefixRounds n N) k *
          BernoulliInformation.binaryKL (1 / 2 - gap k) (1 / 2 + gap (firstRank hK) / 4) := by
  let u := baseParameter hK gap hpos hsorted hsmall k
  let v := stoParameter hK gap hpos hsorted hsmall k k
  let common := stoEntries hK gap hpos hsorted hsmall n k
  let T := Learner.prefixRounds n N
  have hu : 0 < (u : ℝ) ∧ (u : ℝ) < 1 := baseMean_mem_Ioo hK gap hpos hsorted hsmall k
  have hv : 0 < (v : ℝ) ∧ (v : ℝ) < 1 := stoMean_mem_Ioo hK gap hpos hsorted hsmall k k
  have hA : SeededChangeOfMeasure.environment common k T
      (oneReward hK gap) (zeroReward hK gap) u =
        bobEntries hK gap hpos hsorted hsmall n N k := by
    exact (bob_entries_changed_prefix hK gap hpos hsorted hsmall n N k).symm
  have hB : SeededChangeOfMeasure.environment common k T
      (oneReward hK gap) (zeroReward hK gap) v = common := by
    exact (sto_entries_changed_prefix hK gap hpos hsorted hsmall n N k).symm
  have hI := SeededChangeOfMeasure.lemma10_kl_identity L ρ common k T
    (oneReward hK gap) (zeroReward hK gap) (oneReward_ne_zeroReward hK gap)
    u v hu.1 hu.2 hv.1 hv.2
  simp only [SeededChangeOfMeasure.observedLaw, hA, hB] at hI
  rw [bob_expected_count_eq_base hK gap hpos hsorted hsmall n N k L ρ] at hI
  have hueq : (u : ℝ) = 1 / 2 - gap k := by simp [u, baseParameter, baseMean, hk]
  have hveq : (v : ℝ) = 1 / 2 + gap (firstRank hK) / 4 := by simp [v, stoParameter, stoMean]
  rw [hueq, hveq] at hI
  exact hI

/-- Common observed support gives absolute continuity without any positivity
assumption on action probabilities or seed-consistency masses. -/
theorem bob_transcript_absolutelyContinuous {Seed : Type*} [MeasurableSpace Seed]
    (n N : ℕ) (k : Fin K)
    (L : Learner Seed (Alphabet hK gap) K n) (ρ : Measure Seed) [IsProbabilityMeasure ρ] :
    L.transcriptLaw ρ (bobEntries hK gap hpos hsorted hsmall n N k) ≪
      L.transcriptLaw ρ (stoEntries hK gap hpos hsorted hsmall n k) := by
  let u := baseParameter hK gap hpos hsorted hsmall k
  let v := stoParameter hK gap hpos hsorted hsmall k k
  let common := stoEntries hK gap hpos hsorted hsmall n k
  let T := Learner.prefixRounds n N
  have hu : 0 < (u : ℝ) ∧ (u : ℝ) < 1 := baseMean_mem_Ioo hK gap hpos hsorted hsmall k
  have hv : 0 < (v : ℝ) ∧ (v : ℝ) < 1 := stoMean_mem_Ioo hK gap hpos hsorted hsmall k k
  have hA : SeededChangeOfMeasure.environment common k T
      (oneReward hK gap) (zeroReward hK gap) u =
        bobEntries hK gap hpos hsorted hsmall n N k :=
    (bob_entries_changed_prefix hK gap hpos hsorted hsmall n N k).symm
  have hB : SeededChangeOfMeasure.environment common k T
      (oneReward hK gap) (zeroReward hK gap) v = common :=
    (sto_entries_changed_prefix hK gap hpos hsorted hsmall n N k).symm
  simpa only [SeededChangeOfMeasure.observedLaw, hA, hB] using
    SeededChangeOfMeasure.observed_absolutelyContinuous L ρ common k T
      (oneReward hK gap) (zeroReward hK gap) (oneReward_ne_zeroReward hK gap)
      u v hu.1 hu.2 hv.1 hv.2

/-- The per-observation Bernoulli information bound of Appendix E. -/
theorem binaryKL_bob_le {d δ : ℝ} (hd : 0 < d) (hδ : d ≤ δ) (hδsmall : δ ≤ 1 / 8) :
    BernoulliInformation.binaryKL (1 / 2 - δ) (1 / 2 + d / 4) ≤ 8 * δ ^ 2 := by
  have hdsmall : d ≤ 1 / 8 := hδ.trans hδsmall
  have hδpos : 0 < δ := hd.trans_le hδ
  have hvpos : 0 < (1 / 2 + d / 4 : ℝ) := by linarith
  have hvone : (1 / 2 + d / 4 : ℝ) < 1 := by linarith
  have hden : 0 < (1 / 2 + d / 4) * (1 - (1 / 2 + d / 4)) :=
    mul_pos hvpos (sub_pos.mpr hvone)
  have hchi := BernoulliInformation.binaryKL_le_chiSquare
    (show (0 : ℝ) ≤ 1 / 2 - δ by linarith)
    (show (1 / 2 - δ : ℝ) ≤ 1 by linarith) hvpos hvone
  apply hchi.trans
  apply (div_le_iff₀ hden).2
  have hdiff : ((1 / 2 - δ) - (1 / 2 + d / 4)) ^ 2 ≤ (25 / 16 : ℝ) * δ ^ 2 := by
    nlinarith [sq_nonneg (δ - d)]
  have hprod : (255 : ℝ) / 1024 ≤ (1 / 2 + d / 4) * (1 - (1 / 2 + d / 4)) := by
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hprod (sq_nonneg δ)
  nlinarith

/-- Every actual full table in the actual Hoeffding event belongs to Delta_4. -/
theorem bob_good_table (n : ℕ) (hn : 0 < n) (i k : Fin K)
    (hk : k ≠ firstRank hK) (hhalf : gap i / 2 ≤ gap k) (hupper : gap k ≤ gap i)
    (hslack : gap i / (n : ℝ) ≤ gap (firstRank hK) / 8)
    (g : Table K (Alphabet hK gap) n)
    (hgood : g ∈ goodTable Subtype.val
      (bobEntries hK gap hpos hsorted hsmall n
        (LowerBoundSelection.phaseLength n (gap (firstRank hK)) (gap i)) k)
      ((n : ℝ) * gap (firstRank hK) / 16)) :
    RealizedGaps.best (RealizedGaps.arms_pos hK) (realTable Subtype.val g) n = firstRank hK ∧
      AdversarialGapClass hK gap 4 (realTable Subtype.val g) n := by
  simp only [goodTable, Set.mem_ofPred_eq] at hgood
  let N := LowerBoundSelection.phaseLength n (gap (firstRank hK)) (gap i)
  let ν := bobEntries hK gap hpos hsorted hsmall n N k
  let M := tableExpectedTotal Subtype.val ν
  let b := LowerBoundSelection.expectedSelectedGap n (gap (firstRank hK)) (gap i) (gap k)
  have hN : N ≤ n := LowerBoundSelection.phaseLength_le_horizon n _ _
  have hb : 3 * gap (firstRank hK) / 4 ≤ b ∧ b ≤ 17 * gap (firstRank hK) / 8 :=
    LowerBoundSelection.expectedSelectedGap_bounds n hn hpos
      (gap_pos_of_sorted hK gap hpos hsorted i)
      (hsorted (Nat.zero_le k.val)) hhalf hupper hslack
  apply bob_good_table_class_four hK gap hpos hsorted (realTable Subtype.val g) n hn
    (realTable_bounded Subtype.val (alphabet_value_mem_Icc hK gap hpos hsorted hsmall) g)
    k hk M b hb
  · exact bob_expected_selected_gap hK gap hpos hsorted hsmall n hn i k hk
  · intro j hj hjk
    dsimp only [M, ν]
    rw [bob_expected_first hK gap hpos hsorted hsmall n N hN k hk,
      bob_expected_other hK gap hpos hsorted hsmall n N hN k j hj hjk]
    ring
  · intro j
    simpa only [realTable_cumulative] using hgood j

include hpos hsorted in
/-- Count selection, gap comparison and capped ceiling give the exact reference
information allowance. Every premise here is deterministic construction algebra. -/
theorem information_cost_le_ref (n : ℕ) (i k : Fin K)
    (hupper : gap k ≤ gap i)
    (hH : H_BOB hK gap = LowerBoundSelection.rank i /
      (gap (firstRank hK) * gap i))
    (hone : 1 ≤ (n : ℝ) * gap (firstRank hK) / gap i)
    (count : ℝ) (_hcount0 : 0 ≤ count)
    (hcount : count ≤ 2 * (LowerBoundSelection.phaseLength n
      (gap (firstRank hK)) (gap i) : ℝ) / LowerBoundSelection.rank i) :
    count * (8 * gap k ^ 2) ≤ 48 * (n : ℝ) / H_BOB hK gap := by
  have hi := LowerBoundSelection.rank_pos i
  have hgi := gap_pos_of_sorted hK gap hpos hsorted i
  have hgk := gap_pos_of_sorted hK gap hpos hsorted k
  have hsq : gap k ^ 2 ≤ gap i ^ 2 := pow_le_pow_left₀ hgk.le hupper 2
  have hphase := LowerBoundSelection.phaseLength_le_three n hpos hgi hone
  have hNnonneg : (0 : ℝ) ≤ (LowerBoundSelection.phaseLength n
      (gap (firstRank hK)) (gap i) : ℝ) := Nat.cast_nonneg _
  calc
    _ ≤ (2 * (LowerBoundSelection.phaseLength n (gap (firstRank hK)) (gap i) : ℝ) /
        LowerBoundSelection.rank i) * (8 * gap i ^ 2) :=
      mul_le_mul hcount (mul_le_mul_of_nonneg_left hsq (by norm_num))
        (by positivity) (by positivity)
    _ = (16 * gap i ^ 2) *
        (LowerBoundSelection.phaseLength n (gap (firstRank hK)) (gap i) : ℝ) /
          LowerBoundSelection.rank i := by ring
    _ ≤ (16 * gap i ^ 2) * (3 * (n : ℝ) * gap (firstRank hK) / gap i) /
          LowerBoundSelection.rank i :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hphase (by positivity)) hi.le
    _ = 48 * (n : ℝ) / H_BOB hK gap := by
      rw [hH]
      field_simp [hpos.ne', hgi.ne', hi.ne']
      ring

/-- The information bound is computed under the actual observed laws and
expressed using the actual STO complexity. -/
theorem bob_kl_le_actual {Seed : Type*} [MeasurableSpace Seed]
    (hduplicate : gap (firstRank hK) = gap (secondRank hK))
    (n : ℕ) (i k : Fin K) (hk : k ≠ firstRank hK) (hupper : gap k ≤ gap i)
    (hH : H_BOB hK gap = LowerBoundSelection.rank i /
      (gap (firstRank hK) * gap i))
    (hone : 1 ≤ (n : ℝ) * gap (firstRank hK) / gap i)
    (L : Learner Seed (Alphabet hK gap) K n) (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (hcount : L.expectedPullCount ρ (baseEntries hK gap hpos hsorted hsmall n)
        (Learner.prefixRounds n (LowerBoundSelection.phaseLength n (gap (firstRank hK)) (gap i))) k ≤
      2 * (LowerBoundSelection.phaseLength n (gap (firstRank hK)) (gap i) : ℝ) /
        LowerBoundSelection.rank i) :
    let N := LowerBoundSelection.phaseLength n (gap (firstRank hK)) (gap i)
    FiniteInformation.finiteKL
      (L.transcriptLaw ρ (bobEntries hK gap hpos hsorted hsmall n N k))
      (L.transcriptLaw ρ (stoEntries hK gap hpos hsorted hsmall n k)) ≤
        768 * (n : ℝ) / stoComplexity hK gap k := by
  dsimp only
  rw [bob_kl_identity hK gap hpos hsorted hsmall n _ k hk L ρ]
  have hc0 := L.expectedPullCount_nonneg ρ (baseEntries hK gap hpos hsorted hsmall n)
    (Learner.prefixRounds n (LowerBoundSelection.phaseLength n (gap (firstRank hK)) (gap i))) k
  have hinfo := information_cost_le_ref hK gap hpos hsorted n i k hupper hH hone
    _ hc0 hcount
  have hbasepos : 0 < H_BOB hK gap := (gap_complexities_pos hK gap hpos).2.1
  have hstopos := stoComplexity_pos hK gap hpos hsorted k hk
  have hcomparison : stoComplexity hK gap k ≤ 16 * H_BOB hK gap :=
    H_BOB_actual_sto_le_sixteen hK gap hpos hsorted hduplicate k hk
  calc
    _ ≤ L.expectedPullCount ρ (baseEntries hK gap hpos hsorted hsmall n)
        (Learner.prefixRounds n (LowerBoundSelection.phaseLength n (gap (firstRank hK)) (gap i))) k *
          (8 * gap k ^ 2) :=
      mul_le_mul_of_nonneg_left
        (binaryKL_bob_le hpos (hsorted (Nat.zero_le k.val)) (hsmall k)) hc0
    _ ≤ 48 * (n : ℝ) / H_BOB hK gap := hinfo
    _ ≤ 768 * (n : ℝ) / stoComplexity hK gap k := by
      apply (div_le_div_iff₀ hbasepos hstopos).2
      have hm := mul_le_mul_of_nonneg_left hcomparison
        (show (0 : ℝ) ≤ 48 * (n : ℝ) by positivity)
      nlinarith

/-- Actual mean-best identification error in the stationary STO witness. -/
noncomputable def stochasticError {Seed : Type*} [MeasurableSpace Seed]
    (n : ℕ) (k : Fin K) (L : Learner Seed (Alphabet hK gap) K n) (ρ : Measure Seed) : ℝ :=
  (L.transcriptLaw ρ (stoEntries hK gap hpos hsorted hsmall n k)).real {z | z.2 ≠ k}

/-- Identification error on a deterministic actual-valued table, over the seed. -/
noncomputable def tableError {Seed : Type*} [MeasurableSpace Seed]
    (n : ℕ) (L : Learner Seed (Alphabet hK gap) K n) (ρ : Measure Seed)
    (g : Table K (Alphabet hK gap) n) : ℝ :=
  deterministicError ρ (fun z => (L.transcript z).2)
    (fun a => RealizedGaps.best (RealizedGaps.arms_pos hK) (realTable Subtype.val a) n) g

/-- Theorem 4's complete testing and deterministic extraction step, after the
fixed maximizing rank and informative arm have been constructed. -/
theorem bob_error_implication {Seed : Type*} [MeasurableSpace Seed]
    (hduplicate : gap (firstRank hK) = gap (secondRank hK))
    (n : ℕ) (hn : 0 < n)
    (horizon : (K : ℝ) * Real.exp (-(n : ℝ) * gap (firstRank hK) ^ 2 / 128) ≤ 1 / 32)
    (i k : Fin K) (hk : k ≠ firstRank hK) (hhalf : gap i / 2 ≤ gap k) (hupper : gap k ≤ gap i)
    (hH : H_BOB hK gap = LowerBoundSelection.rank i /
      (gap (firstRank hK) * gap i))
    (hone : 1 ≤ (n : ℝ) * gap (firstRank hK) / gap i)
    (hslack : gap i / (n : ℝ) ≤ gap (firstRank hK) / 8)
    (L : Learner Seed (Alphabet hK gap) K n) (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (hcount : L.expectedPullCount ρ (baseEntries hK gap hpos hsorted hsmall n)
        (Learner.prefixRounds n (LowerBoundSelection.phaseLength n (gap (firstRank hK)) (gap i))) k ≤
      2 * (LowerBoundSelection.phaseLength n (gap (firstRank hK)) (gap i) : ℝ) /
        LowerBoundSelection.rank i)
    (herror : stochasticError hK gap hpos hsorted hsmall n k L ρ ≤
      (1 / 64 : ℝ) * Real.exp (-(2048 * (n : ℝ)) / stoComplexity hK gap k)) :
    ∃ g : Table K (Alphabet hK gap) n,
      AdversarialGapClass hK gap 4 (realTable Subtype.val g) n ∧
        (1 : ℝ) / 16 ≤ tableError hK gap n L ρ g := by
  classical
  let N := LowerBoundSelection.phaseLength n (gap (firstRank hK)) (gap i)
  let νA := bobEntries hK gap hpos hsorted hsmall n N k
  let νS := stoEntries hK gap hpos hsorted hsmall n k
  let PA := L.transcriptLaw ρ νA
  let PS := L.transcriptLaw ρ νS
  let μ := Learner.tableLaw νA
  let good := goodTable Subtype.val νA ((n : ℝ) * gap (firstRank hK) / 16)
  let recommend : Seed × Table K (Alphabet hK gap) n → Fin K := fun z => (L.transcript z).2
  let best : Table K (Alphabet hK gap) n → Fin K := fun g =>
    RealizedGaps.best (RealizedGaps.arms_pos hK) (realTable Subtype.val g) n
  let W : Set (Transcript K (Alphabet hK gap) n) := {z | z.2 = firstRank hK}
  let p := PA.real W
  let q := PS.real W
  let x := (n : ℝ) / stoComplexity hK gap k
  have hx : 0 ≤ x := div_nonneg (Nat.cast_nonneg n) (stoComplexity_pos hK gap hpos hsorted k hk).le
  have hAC : PA ≪ PS := bob_transcript_absolutelyContinuous hK gap hpos hsorted hsmall n N k L ρ
  have hD : FiniteInformation.finiteKL PA PS ≤ 768 * x := by
    have h := bob_kl_le_actual hK gap hpos hsorted hsmall hduplicate n i k hk hupper hH hone L ρ hcount
    have heq : 768 * (n : ℝ) / stoComplexity hK gap k = 768 * x := by dsimp [x]; ring
    simpa only [heq] using h
  have hqerror : q ≤ Real.exp (-2048 * x) / 64 := by
    have hsubset : W ⊆ {z | z.2 ≠ k} := by
      intro z hz
      simp only [W, Set.mem_ofPred_eq] at hz ⊢
      intro hz'
      exact hk (hz'.symm.trans hz)
    have hqle : q ≤ stochasticError hK gap hpos hsorted hsmall n k L ρ :=
      measureReal_mono hsubset
    have heq : -(2048 * (n : ℝ)) / stoComplexity hK gap k = -2048 * x := by dsimp [x]; ring
    exact hqle.trans (by simpa only [heq, one_div_mul_eq_div] using herror)
  have hqone : q < 1 := by
    have he : Real.exp (-2048 * x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  have hp : p ≤ 3 / 8 := by
    apply bob_recommendation_bound (p := p) (q := q) (x := x)
      (D := FiniteInformation.finiteKL PA PS) measureReal_nonneg measureReal_nonneg hx hqerror
    · intro hqzero
      exact BernoulliInformation.event_zero_of_ac PA PS hAC W hqzero
    · intro hqpos
      exact BernoulliInformation.event_log_le PA PS hAC W hqpos hqone
    · exact hD
  have hbad : μ.real goodᶜ ≤ (1 : ℝ) / 16 := by
    have h := goodTable_compl_bound νA hn Subtype.val
      (alphabet_value_mem_Icc hK gap hpos hsorted hsmall) (gap (firstRank hK)) hpos.le
    exact h.trans (by nlinarith [horizon])
  have hrec : Measurable recommend := L.transcript_measurable.snd
  have hagrees : ∀ g ∈ good, (firstRank hK) = best g := by
    intro g hg
    exact (bob_good_table hK gap hpos hsorted hsmall n hn i k hk hhalf hupper hslack g hg).1.symm
  have hremove := randomizedError_agreement_le_goodErrorMass_add_bad ρ μ
    recommend hrec best (fun _ => firstRank hK) good hagrees
  have hmass := goodErrorMass_le_randomizedError ρ μ recommend hrec best good
  have hcomplement : PA.real {z | z.2 ≠ firstRank hK} = 1 - p := by
    have hs : {z : Transcript K (Alphabet hK gap) n | z.2 ≠ firstRank hK} = Wᶜ := by
      ext z
      simp [W]
    rw [hs]
    exact probReal_compl_eq_one_sub (Set.toFinite W).measurableSet
  have htest : randomizedError ρ μ recommend (fun _ => firstRank hK) = 1 - p := by
    rw [← transcript_error_eq_randomizedError L ρ νA (firstRank hK)]
    exact hcomplement
  have haverage : (1 : ℝ) / 8 ≤ randomizedError ρ μ recommend best := by
    rw [htest] at hremove
    linarith
  obtain ⟨g, hg, herr⟩ := exists_deterministic_good_error ρ μ recommend hrec best good haverage hbad
  exact ⟨g, (bob_good_table hK gap hpos hsorted hsmall n hn i k hk hhalf hupper hslack g hg).2, herr⟩

/-- The complete Theorem 4 construction on the common actual reward alphabet.
The existential arm names the explicitly defined stationary stochastic law;
its best arm, actual class and error implication are all included. -/
theorem theorem4_finite {Seed : Type*} [MeasurableSpace Seed]
    (hduplicate : gap (firstRank hK) = gap (secondRank hK))
    (n : ℕ) (hn : 0 < n)
    (horizon : (K : ℝ) * Real.exp (-(n : ℝ) * gap (firstRank hK) ^ 2 / 128) ≤ 1 / 32)
    (L : Learner Seed (Alphabet hK gap) K n) (ρ : Measure Seed) [IsProbabilityMeasure ρ] :
    ∃ k : Fin K, k ≠ firstRank hK ∧
      (∀ t s : Fin n, ∀ j,
        stoEntries hK gap hpos hsorted hsmall n k t j =
          stoEntries hK gap hpos hsorted hsmall n k s j) ∧
      (∀ j, j ≠ k →
        (∫ x, x.val ∂stochasticArmLaw hK gap hpos hsorted hsmall k j) <
          ∫ x, x.val ∂stochasticArmLaw hK gap hpos hsorted hsmall k k) ∧
      LabelledGapClass hK gap (RealizedGaps.armGap hK
        (fun _ j => ∫ x, x.val ∂stochasticArmLaw hK gap hpos hsorted hsmall k j) 1) 4 ∧
      (stochasticError hK gap hpos hsorted hsmall n k L ρ ≤
          (1 / 64 : ℝ) * Real.exp (-(2048 * (n : ℝ)) / stoComplexity hK gap k) →
        ∃ g : Table K (Alphabet hK gap) n,
          AdversarialGapClass hK gap 4 (realTable Subtype.val g) n ∧
            (1 : ℝ) / 16 ≤ tableError hK gap n L ρ g) := by
  obtain ⟨i, hi, hmax, hH⟩ := LowerBoundSelection.exists_maximizing_rank
    hK gap hpos hsorted hduplicate
  let N := LowerBoundSelection.phaseLength n (gap (firstRank hK)) (gap i)
  let T := Learner.prefixRounds n N
  have hN : N ≤ n := LowerBoundSelection.phaseLength_le_horizon n _ _
  obtain ⟨k, hkpos, _hki, _hrank, hhalf, hupper, hcount⟩ := L.exists_informative_actual
    ρ (baseEntries hK gap hpos hsorted hsmall n) hK gap hpos hsorted i hi hmax T
  have hk : k ≠ firstRank hK := by
    intro heq
    have hv := congrArg Fin.val heq
    change k.val = 0 at hv
    omega
  have hcount' : L.expectedPullCount ρ (baseEntries hK gap hpos hsorted hsmall n)
      (Learner.prefixRounds n N) k ≤ 2 * (N : ℝ) / LowerBoundSelection.rank i := by
    simpa only [T, Learner.prefixRounds_card n N hN] using hcount
  have hlarge := horizon_gap_square_ge_one hK (gap (firstRank hK)) horizon
  obtain ⟨_hn64, hone, hslack⟩ := horizon_arithmetic (gap (firstRank hK)) (gap i)
    hpos (hsmall _) (gap_pos_of_sorted hK gap hpos hsorted i) (hsmall i) hlarge
  refine ⟨k, hk, stochastic_entries_stationary hK gap hpos hsorted hsmall n k,
    stochastic_actual_unique_best hK gap hpos hsorted hsmall k,
    stochastic_actual_class_four hK gap hpos hsorted hsmall k hk, ?_⟩
  intro herror
  exact bob_error_implication hK gap hpos hsorted hsmall hduplicate n hn horizon
    i k hk hhalf hupper hH hone hslack L ρ hcount' herror

/-- The constructed stochastic arm laws on actual real reward values. -/
noncomputable def realStochasticArmLaw (k j : Fin K) : Measure ℝ :=
  (stochasticArmLaw hK gap hpos hsorted hsmall k j).map Subtype.val

theorem realStochasticArmLaw_eq_bernoulli (k j : Fin K) :
    realStochasticArmLaw hK gap hpos hsorted hsmall k j =
      ProbabilityTheory.bernoulliMeasure (1 : ℝ) 0
        (stoParameter hK gap hpos hsorted hsmall k j) := by
  simp only [realStochasticArmLaw, stochasticArmLaw, alphabetBernoulli,
    ProbabilityTheory.map_bernoulliMeasure, oneReward, zeroReward]

instance realStochasticArmLaw_probability (k j : Fin K) :
    IsProbabilityMeasure (realStochasticArmLaw hK gap hpos hsorted hsmall k j) := by
  rw [realStochasticArmLaw_eq_bernoulli]
  infer_instance

theorem realStochasticArmLaw_mean (k j : Fin K) :
    (∫ x, x ∂realStochasticArmLaw hK gap hpos hsorted hsmall k j) = stoMean hK gap k j := by
  rw [realStochasticArmLaw_eq_bernoulli, ProbabilityTheory.integral_bernoulliMeasure]
  simp [stoParameter]

theorem stoComplexity_eq_actual_real (k : Fin K) :
    stoComplexity hK gap k = H_BOB hK (RealizedGaps.sortedProfile hK
      (fun _ j => ∫ x, x ∂realStochasticArmLaw hK gap hpos hsorted hsmall k j) 1) := by
  simp only [realStochasticArmLaw_mean]
  rfl

/-- Actual real-history observed law, constructed from the independent seed
and complete finite Bernoulli table before interaction. -/
noncomputable def realStochasticLaw {Seed : Type*} [MeasurableSpace Seed]
    (n : ℕ) (k : Fin K) (L : Learner Seed ℝ K n) (ρ : Measure Seed) :
    Measure (Transcript K ℝ n) :=
  L.realObservedLaw ρ (stoEntries hK gap hpos hsorted hsmall n k) Subtype.val

theorem realStochasticTranscript_measurable {Seed : Type*} [MeasurableSpace Seed]
    (n : ℕ) (L : Learner Seed ℝ K n) :
    Measurable (fun z : Seed × Table K (Alphabet hK gap) n =>
      L.transcript (z.1, mapTable Subtype.val z.2)) := L.realTranscript_measurable _

theorem realStochasticLaw_eq_actual {Seed : Type*} [MeasurableSpace Seed]
    (n : ℕ) (k : Fin K) (L : Learner Seed ℝ K n) (ρ : Measure Seed) :
    realStochasticLaw hK gap hpos hsorted hsmall n k L ρ =
      (ρ.prod (Learner.tableLaw (stoEntries hK gap hpos hsorted hsmall n k))).map
        (fun z => L.transcript (z.1, mapTable Subtype.val z.2)) :=
  L.realObservedLaw_eq_actual _ _ _

instance realStochasticLaw_probability {Seed : Type*} [MeasurableSpace Seed]
    (n : ℕ) (k : Fin K) (L : Learner Seed ℝ K n) (ρ : Measure Seed) [IsProbabilityMeasure ρ] :
    IsProbabilityMeasure (realStochasticLaw hK gap hpos hsorted hsmall n k L ρ) := by
  unfold realStochasticLaw
  infer_instance

/-- The real-history learner's stochastic error, with its actual mean-best arm. -/
noncomputable def realStochasticError {Seed : Type*} [MeasurableSpace Seed]
    (n : ℕ) (k : Fin K) (L : Learner Seed ℝ K n) (ρ : Measure Seed) : ℝ :=
  (realStochasticLaw hK gap hpos hsorted hsmall n k L ρ).real {z | z.2 ≠ k}

theorem realStochasticError_eq_restrict {Seed : Type*} [MeasurableSpace Seed]
    (n : ℕ) (k : Fin K) (L : Learner Seed ℝ K n) (ρ : Measure Seed) :
    realStochasticError hK gap hpos hsorted hsmall n k L ρ =
      stochasticError hK gap hpos hsorted hsmall n k
        (L.restrictReward (Subtype.val : Alphabet hK gap → ℝ)) ρ := by
  unfold realStochasticError realStochasticLaw Learner.realObservedLaw stochasticError
  have hreal : MeasurableSet {z : Transcript K ℝ n | z.2 ≠ k} :=
    (measurableSet_eq_fun measurable_snd measurable_const).compl
  rw [measureReal_def, Measure.map_apply (mapTranscript_measurable Subtype.val) hreal]
  apply congrArg (fun W => ((L.restrictReward (Subtype.val : Alphabet hK gap → ℝ)).transcriptLaw
    ρ (stoEntries hK gap hpos hsorted hsmall n k)) W |>.toReal)
  ext z
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, mapTranscript]

/-- Theorem 4 for every real-reward learner with an arbitrary measurable private
seed. The witness and its actual STO complexity may depend on that learner and n. -/
theorem theorem4 {Seed : Type*} [MeasurableSpace Seed]
    (hduplicate : gap (firstRank hK) = gap (secondRank hK))
    (n : ℕ) (hn : 0 < n)
    (horizon : (K : ℝ) * Real.exp (-(n : ℝ) * gap (firstRank hK) ^ 2 / 128) ≤ 1 / 32)
    (L : Learner Seed ℝ K n) (ρ : Measure Seed) [IsProbabilityMeasure ρ] :
    ∃ k : Fin K, k ≠ firstRank hK ∧
      (∀ t : Fin n, ∀ j,
        (stoEntries hK gap hpos hsorted hsmall n k t j).map Subtype.val =
          realStochasticArmLaw hK gap hpos hsorted hsmall k j) ∧
      (∀ j, j ≠ k →
        (∫ x, x ∂realStochasticArmLaw hK gap hpos hsorted hsmall k j) <
          ∫ x, x ∂realStochasticArmLaw hK gap hpos hsorted hsmall k k) ∧
      LabelledGapClass hK gap (RealizedGaps.armGap hK
        (fun _ j => ∫ x, x ∂realStochasticArmLaw hK gap hpos hsorted hsmall k j) 1) 4 ∧
      (realStochasticError hK gap hpos hsorted hsmall n k L ρ ≤
          (1 / 64 : ℝ) * Real.exp (-(2048 * (n : ℝ)) / stoComplexity hK gap k) →
        ∃ g : ℕ → Fin K → ℝ,
          AdversarialGapClass hK gap 4 g n ∧ (1 : ℝ) / 16 ≤ realLearnerError hK L ρ g) := by
  obtain ⟨k, hk, _hstationary, _hbest, _hclass, himp⟩ := theorem4_finite
    hK gap hpos hsorted hsmall hduplicate n hn horizon
      (L.restrictReward (Subtype.val : Alphabet hK gap → ℝ)) ρ
  refine ⟨k, hk, ?_, ?_, ?_, ?_⟩
  · intro t j
    rfl
  · intro j hj
    simp only [realStochasticArmLaw_mean]
    exact stoMean_strict_best hK gap hpos hsorted k j hj
  · simp only [realStochasticArmLaw_mean]
    exact sto_actual_class_four hK gap hpos hsorted k hk
  · intro herror
    rw [realStochasticError_eq_restrict] at herror
    obtain ⟨g, hg, herr⟩ := himp herror
    refine ⟨realTable Subtype.val g, hg, ?_⟩
    rw [← deterministicError_restrictReward hK L ρ Subtype.val g]
    exact herr

end BestOfBothWorlds.LowerBounds.BOBLowerBound
