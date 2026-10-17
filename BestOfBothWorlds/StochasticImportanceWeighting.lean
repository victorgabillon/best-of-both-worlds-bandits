module

public import BestOfBothWorlds.ImportanceWeighting
public import Mathlib.MeasureTheory.Integral.Prod

/-!
One round with a fixed history and an arbitrary bounded reward-vector law.
The product law makes the fresh action independent of the reward vector;
reward coordinates need not be independent. All reward bounds are almost sure.
These are ordinary real integrals, not conditional-expectation statements.
-/

@[expose] public section

open MeasureTheory

namespace BestOfBothWorlds.StochasticImportanceWeighting

variable {K : ℕ} {History : Type*}

/-- Only the selected coordinate is observed. -/
def observedReward (z : Fin K × (Fin K → ℝ)) : ℝ := z.2 z.1

/-- Step 18A's estimator applied to the single observed reward. -/
noncomputable def estimator (p : History → Fin K → ℝ) (h : History) (k : Fin K)
    (z : Fin K × (Fin K → ℝ)) : ℝ :=
  ImportanceWeighting.estimator p (fun _ => observedReward z) h z.1 k

/-- Fixing the reward vector recovers exactly the Step 18A estimator. -/
theorem estimator_eq_deterministic (p : History → Fin K → ℝ)
    (h : History) (a k : Fin K) (y : Fin K → ℝ) :
    estimator p h k (a, y) = ImportanceWeighting.estimator p y h a k := by
  by_cases hak : a = k
  · subst a
    simp [estimator, ImportanceWeighting.estimator, observedReward]
  · simp [estimator, ImportanceWeighting.estimator, hak]

/-- The current action law from Step 18A. -/
noncomputable def actionMeasure (p : History → Fin K → ℝ)
    (hpos : ∀ h k, 0 < p h k) (hnorm : ∀ h, ∑ k, p h k = 1)
    (h : History) : Measure (Fin K) :=
  (ImportanceWeighting.toPMF p hpos hnorm h).toMeasure

instance actionMeasure_isProbabilityMeasure (p : History → Fin K → ℝ)
    (hpos : ∀ h k, 0 < p h k) (hnorm : ∀ h, ∑ k, p h k = 1) (h : History) :
    IsProbabilityMeasure (actionMeasure p hpos hnorm h) := by
  unfold actionMeasure
  infer_instance

/-- The one-round law at a fixed history; no random history is constructed. -/
noncomputable def jointLaw (p : History → Fin K → ℝ)
    (hpos : ∀ h k, 0 < p h k) (hnorm : ∀ h, ∑ k, p h k = 1)
    (ν : Measure (Fin K → ℝ)) (h : History) : Measure (Fin K × (Fin K → ℝ)) :=
  (actionMeasure p hpos hnorm h).prod ν

instance jointLaw_isProbabilityMeasure (p : History → Fin K → ℝ)
    (hpos : ∀ h k, 0 < p h k) (hnorm : ∀ h, ∑ k, p h k = 1)
    (ν : Measure (Fin K → ℝ)) [IsProbabilityMeasure ν] (h : History) :
    IsProbabilityMeasure (jointLaw p hpos hnorm ν h) := by
  unfold jointLaw
  infer_instance

/-- The reward mean is an actual Bochner integral. -/
noncomputable def mean (ν : Measure (Fin K → ℝ)) (k : Fin K) : ℝ := ∫ y, y k ∂ν

/-- The reward second moment is not in general the square of its mean. -/
noncomputable def secondMoment (ν : Measure (Fin K → ℝ)) (k : Fin K) : ℝ :=
  ∫ y, (y k) ^ 2 ∂ν

noncomputable def centered (p : History → Fin K → ℝ) (ν : Measure (Fin K → ℝ))
    (h : History) (k : Fin K) (z : Fin K × (Fin K → ℝ)) : ℝ :=
  estimator p h k z - mean ν k

section RewardMoments

variable (ν : Measure (Fin K → ℝ)) [IsProbabilityMeasure ν]
variable (hbound : ∀ᵐ y ∂ν, ∀ k, 0 ≤ y k ∧ y k ≤ 1)
include hbound

theorem coordinate_integrable (k : Fin K) : Integrable (fun y => y k) ν := by
  apply Integrable.of_bound (measurable_pi_apply k).aestronglyMeasurable 1
  filter_upwards [hbound] with y hy
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hy k).1] using (hy k).2

omit [IsProbabilityMeasure ν] in
theorem coordinate_sq_le (k : Fin K) : ∀ᵐ y ∂ν, (y k) ^ 2 ≤ y k := by
  filter_upwards [hbound] with y hy
  simpa only [pow_two] using mul_le_of_le_one_right (hy k).1 (hy k).2

theorem coordinate_square_integrable (k : Fin K) :
    Integrable (fun y => (y k) ^ 2) ν := by
  apply Integrable.of_bound ((measurable_pi_apply k).pow_const 2).aestronglyMeasurable 1
  filter_upwards [hbound, coordinate_sq_le ν hbound k] with y hy hsq
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (y k))] using hsq.trans (hy k).2

theorem mean_bounds (k : Fin K) : 0 ≤ mean ν k ∧ mean ν k ≤ 1 := by
  refine ⟨integral_nonneg_of_ae (hbound.mono (fun y hy => (hy k).1)), ?_⟩
  calc
    mean ν k ≤ ∫ _ : Fin K → ℝ, (1 : ℝ) ∂ν :=
      integral_mono_ae (coordinate_integrable ν hbound k) (integrable_const 1)
        (hbound.mono (fun y hy => (hy k).2))
    _ = 1 := by simp

theorem secondMoment_le_mean (k : Fin K) : secondMoment ν k ≤ mean ν k :=
  integral_mono_ae (coordinate_square_integrable ν hbound k)
    (coordinate_integrable ν hbound k) (coordinate_sq_le ν hbound k)

theorem secondMoment_bounds (k : Fin K) : 0 ≤ secondMoment ν k ∧ secondMoment ν k ≤ 1 :=
  ⟨integral_nonneg (fun y => sq_nonneg (y k)),
    (secondMoment_le_mean ν hbound k).trans (mean_bounds ν hbound k).2⟩

end RewardMoments

theorem observedReward_measurable : Measurable (observedReward (K := K)) :=
  measurable_from_prod_countable_right (fun a => measurable_pi_apply a)

theorem estimator_measurable (p : History → Fin K → ℝ) (h : History) (k : Fin K) :
    Measurable (estimator p h k) := by
  apply measurable_from_prod_countable_right
  intro a
  by_cases hak : a = k
  · subst a
    simpa [estimator, ImportanceWeighting.estimator, observedReward, Function.comp_def] using
      ((measurable_div_const (p h k)).comp (measurable_pi_apply k))
  · simp [estimator, ImportanceWeighting.estimator, hak]

theorem centered_measurable (p : History → Fin K → ℝ) (ν : Measure (Fin K → ℝ))
    (h : History) (k : Fin K) : Measurable (centered p ν h k) :=
  (estimator_measurable p h k).sub measurable_const

section OneRound

variable (p : History → Fin K → ℝ)
variable (hpos : ∀ h k, 0 < p h k) (hnorm : ∀ h, ∑ k, p h k = 1)
variable (ν : Measure (Fin K → ℝ)) [IsProbabilityMeasure ν]
variable (hbound : ∀ᵐ y ∂ν, ∀ k, 0 ≤ y k ∧ y k ≤ 1)

/-- Convert an actual action integral to the already verified finite expectation. -/
theorem action_integral (h : History) (f : Fin K → ℝ) :
    (∫ a, f a ∂actionMeasure p hpos hnorm h) = ImportanceWeighting.expectation p h f := by
  rw [integral_fintype .of_finite]
  unfold ImportanceWeighting.expectation actionMeasure
  apply Finset.sum_congr rfl
  intro a _
  rw [measureReal_def, PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _),
    ImportanceWeighting.toPMF_toReal]
  rfl

/-- Fubini, with actions integrated first, under a proved integrability hypothesis. -/
theorem joint_integral (h : History) (F : Fin K × (Fin K → ℝ) → ℝ)
    (hF : Integrable F (jointLaw p hpos hnorm ν h)) :
    (∫ z, F z ∂jointLaw p hpos hnorm ν h) =
      ∫ y, ImportanceWeighting.expectation p h (fun a => F (a, y)) ∂ν := by
  rw [jointLaw, integral_prod_symm F hF]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => action_integral p hpos hnorm h (fun a => F (a, y)))

include hbound in
/-- The reward assumption transfers through the second marginal of the product. -/
theorem joint_reward_bounds (h : History) :
    ∀ᵐ z ∂jointLaw p hpos hnorm ν h, ∀ k, 0 ≤ z.2 k ∧ z.2 k ≤ 1 := by
  exact (measurePreserving_snd (μ := actionMeasure p hpos hnorm h)
    (ν := ν)).quasiMeasurePreserving.ae hbound

include hbound in
theorem estimator_bounds (h : History) (k : Fin K) :
    ∀ᵐ z ∂jointLaw p hpos hnorm ν h,
      0 ≤ estimator p h k z ∧ estimator p h k z ≤ 1 / p h k := by
  filter_upwards [joint_reward_bounds p hpos hnorm ν hbound h] with z hz
  rcases z with ⟨a, y⟩
  rw [estimator_eq_deterministic]
  by_cases hak : a = k
  · simp only [ImportanceWeighting.estimator, ite_eq_left hak]
    exact ⟨div_nonneg (hz k).1 (hpos h k).le,
      div_le_div_of_nonneg_right (hz k).2 (hpos h k).le⟩
  · simp only [ImportanceWeighting.estimator, ite_eq_right hak]
    exact ⟨le_rfl, (one_div_pos.mpr (hpos h k)).le⟩

include hbound in
theorem estimator_integrable (h : History) (k : Fin K) :
    Integrable (estimator p h k) (jointLaw p hpos hnorm ν h) := by
  apply Integrable.of_bound (estimator_measurable p h k).aestronglyMeasurable (1 / p h k)
  filter_upwards [estimator_bounds p hpos hnorm ν hbound h k] with z hz
  simpa only [Real.norm_eq_abs, abs_of_nonneg hz.1] using hz.2

include hbound in
theorem estimator_square_integrable (h : History) (k : Fin K) :
    Integrable (fun z => (estimator p h k z) ^ 2) (jointLaw p hpos hnorm ν h) := by
  apply Integrable.of_bound ((estimator_measurable p h k).pow_const 2).aestronglyMeasurable
    ((1 / p h k) ^ 2)
  filter_upwards [estimator_bounds p hpos hnorm ν hbound h k] with z hz
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (estimator p h k z))] using
    pow_le_pow_left₀ hz.1 hz.2 2

include hbound in
theorem centered_integrable (h : History) (k : Fin K) :
    Integrable (centered p ν h k) (jointLaw p hpos hnorm ν h) :=
  (estimator_integrable p hpos hnorm ν hbound h k).sub (integrable_const _)

include hbound in
/-- Centering at the stochastic mean still gives the sharp reciprocal bound. -/
theorem increment_bound (h : History) (k : Fin K) :
    ∀ᵐ z ∂jointLaw p hpos hnorm ν h, |centered p ν h k z| ≤ 1 / p h k := by
  have hm := mean_bounds ν hbound k
  have hrecip : 1 ≤ 1 / p h k :=
    one_le_one_div (hpos h k) (ImportanceWeighting.probability_le_one p hpos hnorm h k)
  filter_upwards [estimator_bounds p hpos hnorm ν hbound h k] with z hz
  exact abs_sub_le_iff.mpr ⟨(sub_le_self _ hm.1).trans hz.2,
    (sub_le_self _ hz.1).trans (hm.2.trans hrecip)⟩

include hbound in
theorem centered_square_integrable (h : History) (k : Fin K) :
    Integrable (fun z => (centered p ν h k z) ^ 2) (jointLaw p hpos hnorm ν h) := by
  apply Integrable.of_bound ((centered_measurable p ν h k).pow_const 2).aestronglyMeasurable
    ((1 / p h k) ^ 2)
  filter_upwards [increment_bound p hpos hnorm ν hbound h k] with z hz
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (centered p ν h k z)), sq_abs] using
    pow_le_pow_left₀ (abs_nonneg (centered p ν h k z)) hz 2

include hbound in
/-- Integrating the Step 18A identity over the arbitrary reward-vector law. -/
theorem unbiased (h : History) (k : Fin K) :
    (∫ z, estimator p h k z ∂jointLaw p hpos hnorm ν h) = mean ν k := by
  rw [joint_integral p hpos hnorm ν h _ (estimator_integrable p hpos hnorm ν hbound h k)]
  unfold mean
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => by
    simp_rw [estimator_eq_deterministic]
    exact ImportanceWeighting.unbiased p y hpos h k)

include hbound in
theorem second_moment (h : History) (k : Fin K) :
    (∫ z, (estimator p h k z) ^ 2 ∂jointLaw p hpos hnorm ν h) =
      secondMoment ν k / p h k := by
  rw [joint_integral p hpos hnorm ν h _
    (estimator_square_integrable p hpos hnorm ν hbound h k)]
  calc
    (∫ y, ImportanceWeighting.expectation p h (fun a => (estimator p h k (a, y)) ^ 2) ∂ν) =
        ∫ y, (y k) ^ 2 / p h k ∂ν := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => by
        simp_rw [estimator_eq_deterministic]
        exact ImportanceWeighting.second_moment p y hpos h k)
    _ = secondMoment ν k / p h k := integral_div _ _

include hbound in
theorem centered_mean_zero (h : History) (k : Fin K) :
    (∫ z, centered p ν h k z ∂jointLaw p hpos hnorm ν h) = 0 := by
  unfold centered
  rw [integral_sub (estimator_integrable p hpos hnorm ν hbound h k) (integrable_const _),
    unbiased p hpos hnorm ν hbound h k]
  simp

include hbound in
theorem centered_second_moment (h : History) (k : Fin K) :
    (∫ z, (centered p ν h k z)^2 ∂jointLaw p hpos hnorm ν h) =
      secondMoment ν k / p h k - (mean ν k)^2 := by
  have hi := estimator_integrable p hpos hnorm ν hbound h k
  have hi2 := estimator_square_integrable p hpos hnorm ν hbound h k
  have hlinear : Integrable (fun z => (2 * mean ν k) * estimator p h k z)
      (jointLaw p hpos hnorm ν h) := hi.const_mul _
  have hsub : Integrable (fun z => (estimator p h k z)^2 -
      (2 * mean ν k) * estimator p h k z) (jointLaw p hpos hnorm ν h) := hi2.sub hlinear
  calc
    (∫ z, (centered p ν h k z)^2 ∂jointLaw p hpos hnorm ν h) =
        ∫ z, (estimator p h k z)^2 - (2 * mean ν k) * estimator p h k z + (mean ν k)^2
          ∂jointLaw p hpos hnorm ν h := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => by unfold centered; ring)
    _ = (∫ z, (estimator p h k z)^2 ∂jointLaw p hpos hnorm ν h) -
        (2 * mean ν k) * (∫ z, estimator p h k z ∂jointLaw p hpos hnorm ν h) +
        (mean ν k)^2 := by
      rw [integral_add hsub (integrable_const _), integral_sub hi2 hlinear,
        integral_const_mul]
      simp
    _ = secondMoment ν k / p h k - (mean ν k)^2 := by
      rw [second_moment p hpos hnorm ν hbound h k, unbiased p hpos hnorm ν hbound h k]
      ring

omit [IsProbabilityMeasure ν] in
theorem variance_nonneg (h : History) (k : Fin K) :
    0 ≤ ∫ z, (centered p ν h k z)^2 ∂jointLaw p hpos hnorm ν h :=
  integral_nonneg (fun z => sq_nonneg (centered p ν h k z))

include hbound in
theorem variance_bound (h : History) (k : Fin K) :
    (∫ z, (centered p ν h k z)^2 ∂jointLaw p hpos hnorm ν h) ≤ 1 / p h k := by
  rw [centered_second_moment p hpos hnorm ν hbound h k]
  exact (sub_le_self _ (sq_nonneg (mean ν k))).trans
    (div_le_div_of_nonneg_right (secondMoment_bounds ν hbound k).2 (hpos h k).le)

end OneRound

/-- A bounded deterministic reward vector is an admissible stochastic law. -/
theorem dirac_reward_bounds (g : Fin K → ℝ) (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) :
    ∀ᵐ y ∂Measure.dirac g, ∀ k, 0 ≤ y k ∧ y k ≤ 1 := by
  simpa using hg

@[simp] theorem mean_dirac (g : Fin K → ℝ) (k : Fin K) : mean (Measure.dirac g) k = g k := by
  simp [mean]

@[simp] theorem secondMoment_dirac (g : Fin K → ℝ) (k : Fin K) :
    secondMoment (Measure.dirac g) k = (g k) ^ 2 := by
  simp [secondMoment]

/-- The stochastic centered moment agrees with the old finite variance for a Dirac law. -/
theorem centered_second_moment_dirac (p : History → Fin K → ℝ)
    (hpos : ∀ h k, 0 < p h k) (hnorm : ∀ h, ∑ k, p h k = 1)
    (g : Fin K → ℝ) (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) (h : History) (k : Fin K) :
    (∫ z, (centered p (Measure.dirac g) h k z) ^ 2
      ∂jointLaw p hpos hnorm (Measure.dirac g) h) = ImportanceWeighting.variance p g h k := by
  rw [centered_second_moment p hpos hnorm (Measure.dirac g) (dirac_reward_bounds g hg) h k,
    mean_dirac, secondMoment_dirac, ImportanceWeighting.variance_eq p g hpos hnorm h k]
  ring

end BestOfBothWorlds.StochasticImportanceWeighting
