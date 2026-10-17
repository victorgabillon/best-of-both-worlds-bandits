module

public import BestOfBothWorlds.LowerBoundStochasticGaps
public import BestOfBothWorlds.LowerBoundSelection
public import BestOfBothWorlds.SeededLearner
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
Explicit finite-alphabet reward laws for the lower-bound constructions. The
alphabet consists of actual real values and includes every possible deterministic
suffix reward before the lightly sampled arm is chosen. It has no extra symbols
that could reveal more than the real reward supplied to the learner.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace BestOfBothWorlds.LowerBounds

variable {K : ℕ}

/-- One common finite alphabet for every candidate informative arm. -/
noncomputable def rewardAlphabet (hK : 2 ≤ K) (gap : Fin K → ℝ) : Finset ℝ := by
  classical
  exact {0, 1} ∪ Finset.univ.image (fun j => gap j - gap (firstRank hK))

abbrev Alphabet (hK : 2 ≤ K) (gap : Fin K → ℝ) := {x : ℝ // x ∈ rewardAlphabet hK gap}

noncomputable def zeroReward (hK : 2 ≤ K) (gap : Fin K → ℝ) : Alphabet hK gap :=
  ⟨0, by classical simp [rewardAlphabet]⟩

noncomputable def oneReward (hK : 2 ≤ K) (gap : Fin K → ℝ) : Alphabet hK gap :=
  ⟨1, by classical simp [rewardAlphabet]⟩

noncomputable def suffixReward (hK : 2 ≤ K) (gap : Fin K → ℝ) (k : Fin K) : Alphabet hK gap :=
  ⟨gap k - gap (firstRank hK), by classical simp [rewardAlphabet]⟩

theorem oneReward_ne_zeroReward (hK : 2 ≤ K) (gap : Fin K → ℝ) :
    oneReward hK gap ≠ zeroReward hK gap := by
  intro h
  have hv := congrArg Subtype.val h
  norm_num [oneReward, zeroReward] at hv

/-- All alphabet values lie in [0,1], including deterministic nonbinary rewards. -/
theorem alphabet_value_mem_Icc (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    (hsmall : ∀ j, gap j ≤ 1 / 8) (x : Alphabet hK gap) :
    x.val ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  have hx := x.property
  simp only [rewardAlphabet, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton, Finset.mem_image, Finset.mem_univ, true_and] at hx
  rcases hx with (hx | hx) | ⟨j, hj⟩
  · simp [hx]
  · simp [hx]
  · have hle : gap (firstRank hK) ≤ gap j := hsorted (Nat.zero_le j.val)
    rw [← hj]
    constructor <;> linarith [hsmall j]

theorem baseMean_mem_Ioo (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    (hsmall : ∀ j, gap j ≤ 1 / 8) (j : Fin K) :
    baseMean hK gap j ∈ Set.Ioo (0 : ℝ) 1 := by
  have hj := gap_pos_of_sorted hK gap hpos hsorted j
  unfold baseMean
  split_ifs <;> constructor <;> linarith [hsmall j]

noncomputable def baseParameter (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    (hsmall : ∀ j, gap j ≤ 1 / 8) (j : Fin K) : unitInterval :=
  ⟨baseMean hK gap j, (baseMean_mem_Ioo hK gap hpos hsorted hsmall j).1.le,
    (baseMean_mem_Ioo hK gap hpos hsorted hsmall j).2.le⟩

noncomputable def stoParameter (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    (hsmall : ∀ j, gap j ≤ 1 / 8) (k j : Fin K) : unitInterval :=
  ⟨stoMean hK gap k j, (stoMean_mem_Ioo hK gap hpos hsorted hsmall k j).1.le,
    (stoMean_mem_Ioo hK gap hpos hsorted hsmall k j).2.le⟩

/-- Bernoulli(p) has mass p at reward1 and mass 1-p at reward0. -/
noncomputable def alphabetBernoulli (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (p : unitInterval) : Measure (Alphabet hK gap) :=
  bernoulliMeasure (oneReward hK gap) (zeroReward hK gap) p

instance alphabetBernoulli_probability (hK : 2 ≤ K) (gap : Fin K → ℝ) (p : unitInterval) :
    IsProbabilityMeasure (alphabetBernoulli hK gap p) := by
  unfold alphabetBernoulli
  infer_instance

/-- The reward-value expectation uses the correct Bernoulli convention. -/
theorem integral_alphabetBernoulli (hK : 2 ≤ K) (gap : Fin K → ℝ) (p : unitInterval) :
    (∫ x, x.val ∂alphabetBernoulli hK gap p) = p.val := by
  rw [alphabetBernoulli, integral_bernoulliMeasure]
  simp [oneReward, zeroReward]

variable (hK : 2 ≤ K) (gap : Fin K → ℝ)
  (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
  (hsmall : ∀ j, gap j ≤ 1 / 8)

/-- BASE is stationary with the manuscript's exact reference means. -/
noncomputable def baseEntries (n : ℕ) : Fin n → Fin K → Measure (Alphabet hK gap) :=
  fun _ j => alphabetBernoulli hK gap (baseParameter hK gap hpos hsorted hsmall j)

/-- STO is stationary, changing only the selected label. -/
noncomputable def stoEntries (n : ℕ) (k : Fin K) : Fin n → Fin K → Measure (Alphabet hK gap) :=
  fun _ j => alphabetBernoulli hK gap (stoParameter hK gap hpos hsorted hsmall k j)

/-- BOB ADV is an oblivious independent table law. Its selected arm switches
from BASE to STO only after the fixed initial prefix; a full prefix is allowed. -/
noncomputable def bobEntries (n N : ℕ) (k : Fin K) : Fin n → Fin K → Measure (Alphabet hK gap) :=
  fun t j => if t.val < N then baseEntries hK gap hpos hsorted hsmall n t j
    else stoEntries hK gap hpos hsorted hsmall n k t j

instance baseEntries_probability (n : ℕ) (t : Fin n) (j : Fin K) :
    IsProbabilityMeasure (baseEntries hK gap hpos hsorted hsmall n t j) := by
  unfold baseEntries
  infer_instance

instance stoEntries_probability (n : ℕ) (k : Fin K) (t : Fin n) (j : Fin K) :
    IsProbabilityMeasure (stoEntries hK gap hpos hsorted hsmall n k t j) := by
  unfold stoEntries
  infer_instance

instance bobEntries_probability (n N : ℕ) (k : Fin K) (t : Fin n) (j : Fin K) :
    IsProbabilityMeasure (bobEntries hK gap hpos hsorted hsmall n N k t j) := by
  unfold bobEntries
  split_ifs <;> infer_instance

/-- ADV2's first-phase Bernoulli parameter. -/
noncomputable def perturbedParameter (k : Fin K) : unitInterval := by
  have hd := hsmall (firstRank hK)
  have hk := hsmall k
  have hle : gap (firstRank hK) ≤ gap k := hsorted (Nat.zero_le k.val)
  refine ⟨1 / 2 - gap k + 2 * gap (firstRank hK), ?_, ?_⟩ <;> linarith

/-- ADV1/ADV2 differ only on the selected arm in the first floor(n/2) rounds.
Both have the same deterministic second phase and optional final zero padding. -/
noncomputable def adversarialEntries (n : ℕ) (k : Fin K) (modified : Bool) :
    Fin n → Fin K → Measure (Alphabet hK gap) :=
  fun t j => if t.val < n / 2 then
    if modified = true ∧ j = k then
      alphabetBernoulli hK gap (perturbedParameter hK gap hpos hsorted hsmall k)
    else baseEntries hK gap hpos hsorted hsmall n t j
  else if t.val < 2 * (n / 2) ∧ j = k then Measure.dirac (suffixReward hK gap k)
  else Measure.dirac (zeroReward hK gap)

instance adversarialEntries_probability (n : ℕ) (k : Fin K) (modified : Bool)
    (t : Fin n) (j : Fin K) :
    IsProbabilityMeasure (adversarialEntries hK gap hpos hsorted hsmall n k modified t j) := by
  unfold adversarialEntries
  split_ifs <;> infer_instance

theorem baseEntries_integral (n : ℕ) (t : Fin n) (j : Fin K) :
    (∫ x, x.val ∂baseEntries hK gap hpos hsorted hsmall n t j) = baseMean hK gap j :=
  integral_alphabetBernoulli hK gap _

theorem stoEntries_integral (n : ℕ) (k : Fin K) (t : Fin n) (j : Fin K) :
    (∫ x, x.val ∂stoEntries hK gap hpos hsorted hsmall n k t j) = stoMean hK gap k j :=
  integral_alphabetBernoulli hK gap _

theorem stoEntries_eq_base_of_ne (n : ℕ) (k : Fin K) (t : Fin n) (j : Fin K)
    (hj : j ≠ k) :
    stoEntries hK gap hpos hsorted hsmall n k t j =
      baseEntries hK gap hpos hsorted hsmall n t j := by
  unfold stoEntries baseEntries
  congr 1
  apply Subtype.ext
  simp [stoParameter, baseParameter, stoMean, hj]

theorem perturbedParameter_mem_Ioo (k : Fin K) :
    (perturbedParameter hK gap hpos hsorted hsmall k).val ∈ Set.Ioo (0 : ℝ) 1 := by
  have hd := hsmall (firstRank hK)
  have hk := hsmall k
  have hle : gap (firstRank hK) ≤ gap k := hsorted (Nat.zero_le k.val)
  change (1 / 2 - gap k + 2 * gap (firstRank hK)) ∈ Set.Ioo (0 : ℝ) 1
  constructor <;> linarith

end BestOfBothWorlds.LowerBounds
