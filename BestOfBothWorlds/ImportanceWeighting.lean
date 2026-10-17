module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Tactic.Ring

/-!
One deterministic reward vector and one history-dependent action distribution.

The history is an arbitrary parameter. Only the current action is averaged
over; these finite identities do not construct a history law or a conditional
expectation on a filtered probability space.
-/

@[expose] public section

namespace BestOfBothWorlds.ImportanceWeighting

variable {K : ℕ} {History : Type*}
variable (p : History → Fin K → ℝ) (g : Fin K → ℝ)

/-- The selected action `a` and the arm being estimated `k` have distinct roles. -/
noncomputable def estimator (h : History) (a k : Fin K) : ℝ :=
  if a = k then g k / p h k else 0

/-- Finite expectation over the current action, with the history held fixed. -/
noncomputable def expectation (h : History) (f : Fin K → ℝ) : ℝ :=
  ∑ a, p h a * f a

/-- Centered second moment about `g k`; unbiasedness makes this the variance. -/
noncomputable def variance (h : History) (k : Fin K) : ℝ :=
  expectation p h (fun a => (estimator p g h a k - g k) ^ 2)

/-- Positive normalized weights are at most one, at every history. -/
theorem probability_le_one
    (hpos : ∀ h k, 0 < p h k) (hnorm : ∀ h, ∑ k, p h k = 1)
    (h : History) (k : Fin K) : p h k ≤ 1 := by
  calc
    p h k ≤ ∑ a, p h a :=
      Finset.single_le_sum (fun a _ => (hpos h a).le) (Finset.mem_univ k)
    _ = 1 := hnorm h

/-- Importance weighting is unbiased for any history-dependent positive policy. -/
theorem unbiased
    (hpos : ∀ h k, 0 < p h k) (h : History) (k : Fin K) :
    expectation p h (fun a => estimator p g h a k) = g k := by
  simp [expectation, estimator, mul_ite]
  exact mul_div_cancel₀ (g k) (hpos h k).ne'

/-- The exact second moment needs positivity, without reward-range assumptions. -/
theorem second_moment
    (hpos : ∀ h k, 0 < p h k) (h : History) (k : Fin K) :
    expectation p h (fun a => (estimator p g h a k) ^ 2) = (g k) ^ 2 / p h k := by
  have hnonzero : p h k ≠ 0 := (hpos h k).ne'
  have hsingle : expectation p h (fun a => (estimator p g h a k) ^ 2) =
      p h k * (g k / p h k) ^ 2 := by
    simp [expectation, estimator, mul_ite]
  rw [hsingle, div_pow, pow_two (p h k), ← mul_div_assoc,
    mul_div_mul_left _ _ hnonzero]

/-- The variance identity uses normalization, unbiasedness and the second moment. -/
theorem variance_eq
    (hpos : ∀ h k, 0 < p h k) (hnorm : ∀ h, ∑ k, p h k = 1)
    (h : History) (k : Fin K) :
    variance p g h k = (g k) ^ 2 * (1 / p h k - 1) := by
  have hexpand : variance p g h k =
      expectation p h (fun a => (estimator p g h a k) ^ 2) -
        (2 * g k) * expectation p h (fun a => estimator p g h a k) +
        (g k) ^ 2 * (∑ a, p h a) := by
    unfold variance expectation
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hexpand, second_moment p g hpos h k, unbiased p g hpos h k, hnorm h]
  ring

/-- A centered second moment with positive weights is nonnegative. -/
theorem variance_nonneg
    (hpos : ∀ h k, 0 < p h k) (h : History) (k : Fin K) :
    0 ≤ variance p g h k := by
  unfold variance expectation
  exact Finset.sum_nonneg (fun a _ => mul_nonneg (hpos h a).le (sq_nonneg _))

/-- Bounded rewards give the reciprocal-probability variance bound. -/
theorem variance_le_inv_probability
    (hpos : ∀ h k, 0 < p h k) (hnorm : ∀ h, ∑ k, p h k = 1)
    (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) (h : History) (k : Fin K) :
    variance p g h k ≤ 1 / p h k := by
  rw [variance_eq p g hpos hnorm h k]
  have hfactor : 0 ≤ 1 / p h k - 1 :=
    sub_nonneg.mpr (one_le_one_div (hpos h k) (probability_le_one p hpos hnorm h k))
  have hgsq : (g k) ^ 2 ≤ 1 := by
    simpa only [pow_two, one_mul] using
      mul_le_mul (hg k).2 (hg k).2 (hg k).1 (zero_le_one : (0 : ℝ) ≤ 1)
  calc
    (g k) ^ 2 * (1 / p h k - 1) ≤ 1 / p h k - 1 :=
      mul_le_of_le_one_left hfactor hgsq
    _ ≤ 1 / p h k := sub_le_self _ (zero_le_one : (0 : ℝ) ≤ 1)

/-- The centered increment is bounded for every possible selected action. -/
theorem increment_abs_le_inv_probability
    (hpos : ∀ h k, 0 < p h k) (hnorm : ∀ h, ∑ k, p h k = 1)
    (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) (h : History) (a k : Fin K) :
    |estimator p g h a k - g k| ≤ 1 / p h k := by
  have hrecip : 1 ≤ 1 / p h k :=
    one_le_one_div (hpos h k) (probability_le_one p hpos hnorm h k)
  have hgrecip : g k ≤ 1 / p h k := (hg k).2.trans hrecip
  by_cases hak : a = k
  · simp only [estimator, ite_eq_left hak]
    apply abs_sub_le_iff.mpr
    constructor
    · exact (sub_le_self _ (hg k).1).trans
        (div_le_div_of_nonneg_right (hg k).2 (hpos h k).le)
    · exact (sub_le_self _ (div_nonneg (hg k).1 (hpos h k).le)).trans hgrecip
  · simp only [estimator, ite_eq_right hak, zero_sub, abs_neg, abs_of_nonneg (hg k).1]
    exact hgrecip

/-- The policy at a fixed history, as a genuine probability mass function. -/
noncomputable def toPMF
    (hpos : ∀ h k, 0 < p h k) (hnorm : ∀ h, ∑ k, p h k = 1)
    (h : History) : PMF (Fin K) :=
  PMF.ofFintype (fun a => ENNReal.ofReal (p h a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => (hpos h a).le), hnorm h,
      ENNReal.ofReal_one])

/-- Converting a PMF mass back to a real number recovers the policy weight. -/
theorem toPMF_toReal
    (hpos : ∀ h k, 0 < p h k) (hnorm : ∀ h, ∑ k, p h k = 1)
    (h : History) (a : Fin K) :
    (toPMF p hpos hnorm h a).toReal = p h a :=
  ENNReal.toReal_ofReal (hpos h a).le

/-- All finite expectations above are real-mass weighted sums for this PMF. -/
theorem pmf_expectation
    (hpos : ∀ h k, 0 < p h k) (hnorm : ∀ h, ∑ k, p h k = 1)
    (h : History) (f : Fin K → ℝ) :
    (∑ a, (toPMF p hpos hnorm h a).toReal * f a) = expectation p h f := by
  unfold expectation
  apply Finset.sum_congr rfl
  intro a _
  rw [toPMF_toReal]

end BestOfBothWorlds.ImportanceWeighting
