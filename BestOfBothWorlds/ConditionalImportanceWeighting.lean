module

public import BestOfBothWorlds.StochasticImportanceWeighting
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Probability.Independence.Basic

/-!
One random measurable history and one fresh action/reward round.
The history sigma-algebra is a pullback through the history projection only.
A deterministic positive sampling floor makes the squared estimators integrable.
Conditional expectations below use Mathlib's actual `MeasureTheory.condExp`.
No multi-round process or concentration inequality is constructed here.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace BestOfBothWorlds.ConditionalImportanceWeighting

variable {K : ℕ} {History : Type*} [MeasurableSpace History]

/-- A past history, its next action, and the fresh vector of potential rewards. -/
abbrev Outcome (History : Type*) (K : ℕ) := (History × Fin K) × (Fin K → ℝ)

def history (z : Outcome History K) : History := z.1.1

def action (z : Outcome History K) : Fin K := z.1.2

def rewardVector (z : Outcome History K) : Fin K → ℝ := z.2

theorem history_measurable : Measurable (history (History := History) (K := K)) :=
  measurable_fst.comp measurable_fst

theorem action_measurable : Measurable (action (History := History) (K := K)) :=
  measurable_snd.comp measurable_fst

theorem rewardVector_measurable :
    Measurable (rewardVector (History := History) (K := K)) := measurable_snd

/-- The Step 18A action law, now proved measurable in an arbitrary history. -/
noncomputable def actionKernel (p : History → Fin K → ℝ)
    (hpos : ∀ h k, 0 < p h k) (hnorm : ∀ h, ∑ k, p h k = 1)
    (hp : ∀ k, Measurable (fun h => p h k)) : Kernel History (Fin K) where
  toFun := StochasticImportanceWeighting.actionMeasure p hpos hnorm
  measurable' := by
    classical
    apply Measure.measurable_of_measurable_coe
    intro s hs
    change Measurable (fun h => (ImportanceWeighting.toPMF p hpos hnorm h).toMeasure s)
    simp_rw [PMF.toMeasure_apply_eq_toOuterMeasure_apply _ hs,
      PMF.toOuterMeasure_apply_fintype]
    apply Finset.measurable_sum
    intro a _
    by_cases ha : a ∈ s
    · simp only [Set.indicator_of_mem ha]
      change Measurable (fun h => ENNReal.ofReal (p h a))
      exact ENNReal.measurable_ofReal.comp (hp a)
    · simp only [Set.indicator_of_notMem ha]
      exact measurable_const

instance actionKernel_isMarkovKernel (p : History → Fin K → ℝ)
    (hpos : ∀ h k, 0 < p h k) (hnorm : ∀ h, ∑ k, p h k = 1)
    (hp : ∀ k, Measurable (fun h => p h k)) :
    IsMarkovKernel (actionKernel p hpos hnorm hp) where
  isProbabilityMeasure h := by
    change IsProbabilityMeasure (StochasticImportanceWeighting.actionMeasure p hpos hnorm h)
    infer_instance

theorem actionKernel_apply (p : History → Fin K → ℝ)
    (hpos : ∀ h k, 0 < p h k) (hnorm : ∀ h, ∑ k, p h k = 1)
    (hp : ∀ k, Measurable (fun h => p h k)) (h : History) :
    actionKernel p hpos hnorm hp h =
      StochasticImportanceWeighting.actionMeasure p hpos hnorm h := rfl

/-- First sample history and its action, then sample the independent fresh rewards. -/
noncomputable def jointMeasure (p : History → Fin K → ℝ)
    (hpos : ∀ h k, 0 < p h k) (hnorm : ∀ h, ∑ k, p h k = 1)
    (hp : ∀ k, Measurable (fun h => p h k))
    (μ : Measure History) (ν : Measure (Fin K → ℝ)) : Measure (Outcome History K) :=
  (μ.compProd (actionKernel p hpos hnorm hp)).prod ν

instance jointMeasure_isProbabilityMeasure (p : History → Fin K → ℝ)
    (hpos : ∀ h k, 0 < p h k) (hnorm : ∀ h, ∑ k, p h k = 1)
    (hp : ∀ k, Measurable (fun h => p h k))
    (μ : Measure History) [IsProbabilityMeasure μ]
    (ν : Measure (Fin K → ℝ)) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (jointMeasure p hpos hnorm hp μ ν) := by
  unfold jointMeasure
  infer_instance

theorem observedReward_measurable :
    Measurable (fun z : Outcome History K => rewardVector z (action z)) := by
  exact StochasticImportanceWeighting.observedReward_measurable.comp
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd)

/-- Reuse Step 18B's estimator with the realized history and the observed reward. -/
noncomputable def estimator (p : History → Fin K → ℝ) (k : Fin K)
    (z : Outcome History K) : ℝ :=
  StochasticImportanceWeighting.estimator p (history z) k (action z, rewardVector z)

theorem estimator_measurable (p : History → Fin K → ℝ)
    (hp : ∀ k, Measurable (fun h => p h k)) (k : Fin K) :
    Measurable (estimator p k) := by
  unfold estimator StochasticImportanceWeighting.estimator ImportanceWeighting.estimator
  apply Measurable.ite
  · exact measurableSet_eq_fun (measurable_snd.comp measurable_fst) measurable_const
  · exact observedReward_measurable.div ((hp k).comp (measurable_fst.comp measurable_fst))
  · exact measurable_const



/-- Exactly the information carried by the history projection. -/
abbrev historySigma : MeasurableSpace (Outcome History K) :=
  (inferInstance : MeasurableSpace History).comap history

theorem historySigma_le : historySigma (History := History) (K := K) ≤
    (inferInstance : MeasurableSpace (Outcome History K)) :=
  history_measurable.comap_le

theorem history_function_measurable (G : History → ℝ) (hG : Measurable G) :
    Measurable[historySigma] (fun z : Outcome History K => G (history z)) :=
  hG.comp (comap_measurable history)

/-- Centering reuses the mean and estimator convention of Step 18B. -/
noncomputable def centered (p : History → Fin K → ℝ) (ν : Measure (Fin K → ℝ))
    (k : Fin K) (z : Outcome History K) : ℝ :=
  StochasticImportanceWeighting.centered p ν (history z) k (action z, rewardVector z)

theorem centered_measurable (p : History → Fin K → ℝ)
    (hp : ∀ k, Measurable (fun h => p h k)) (ν : Measure (Fin K → ℝ)) (k : Fin K) :
    Measurable (centered p ν k) :=
  (estimator_measurable p hp k).sub measurable_const

section OneRound

variable (p : History → Fin K → ℝ)
variable (hpos : ∀ h k, 0 < p h k) (hnorm : ∀ h, ∑ k, p h k = 1)
variable (hp : ∀ k, Measurable (fun h => p h k))
variable (μ : Measure History) [IsProbabilityMeasure μ]
variable (ν : Measure (Fin K → ℝ)) [IsProbabilityMeasure ν]
variable (hbound : ∀ᵐ y ∂ν, ∀ k, 0 ≤ y k ∧ y k ≤ 1)

theorem historySigma_sigmaFinite :
    SigmaFinite ((jointMeasure p hpos hnorm hp μ ν).trim historySigma_le) := inferInstance

/-- Fresh rewards are independent of the entire history/action pair. -/
theorem rewardVector_independent_history_action :
    IndepFun (fun z : Outcome History K => z.1) rewardVector
      (jointMeasure p hpos hnorm hp μ ν) := by
  exact indepFun_prod (μ := μ.compProd (actionKernel p hpos hnorm hp))
    (ν := ν) measurable_id measurable_id

/-- The history projection has exactly the specified law, even for nondiscrete histories. -/
theorem history_measurePreserving :
    MeasurePreserving (history (History := History) (K := K))
      (jointMeasure p hpos hnorm hp μ ν) μ := by
  have hfst : MeasurePreserving (Prod.fst : History × Fin K → History)
      (μ.compProd (actionKernel p hpos hnorm hp)) μ :=
    ⟨measurable_fst, Measure.fst_compProd μ (actionKernel p hpos hnorm hp)⟩
  exact hfst.comp (measurePreserving_fst (μ := μ.compProd (actionKernel p hpos hnorm hp)) (ν := ν))

include hbound in
/-- Reward support is lifted through the second projection of the outer product. -/
theorem reward_bounds :
    ∀ᵐ z ∂jointMeasure p hpos hnorm hp μ ν, ∀ k, 0 ≤ rewardVector z k ∧ rewardVector z k ≤ 1 := by
  exact measurePreserving_snd.quasiMeasurePreserving.ae hbound

include hbound in
theorem estimator_bounds (k : Fin K) :
    ∀ᵐ z ∂jointMeasure p hpos hnorm hp μ ν,
      0 ≤ estimator p k z ∧ estimator p k z ≤ 1 / p (history z) k := by
  filter_upwards [reward_bounds p hpos hnorm hp μ ν hbound] with z hz
  unfold estimator StochasticImportanceWeighting.estimator ImportanceWeighting.estimator
  split_ifs
  · exact ⟨div_nonneg (hz (action z)).1 (hpos (history z) k).le,
      div_le_div_of_nonneg_right (hz (action z)).2 (hpos (history z) k).le⟩
  · exact ⟨le_rfl, (one_div_pos.mpr (hpos (history z) k)).le⟩

include hbound in
theorem increment_bound (k : Fin K) :
    ∀ᵐ z ∂jointMeasure p hpos hnorm hp μ ν,
      |centered p ν k z| ≤ 1 / p (history z) k := by
  have hm := StochasticImportanceWeighting.mean_bounds ν hbound k
  filter_upwards [estimator_bounds p hpos hnorm hp μ ν hbound k] with z hz
  have hrecip : 1 ≤ 1 / p (history z) k :=
    one_le_one_div (hpos (history z) k)
      (ImportanceWeighting.probability_le_one p hpos hnorm (history z) k)
  exact abs_sub_le_iff.mpr ⟨(sub_le_self _ hm.1).trans hz.2,
    (sub_le_self _ hz.1).trans (hm.2.trans hrecip)⟩

section SamplingFloor

variable (ε : ℝ) (hε : 0 < ε) (hfloor : ∀ h k, ε ≤ p h k)

omit [MeasurableSpace History] in
include hε hfloor in
/-- The explicit floor implies the positivity used by the earlier PMF interface. -/
theorem probability_pos_of_floor (h : History) (k : Fin K) : 0 < p h k :=
  hε.trans_le (hfloor h k)

omit [MeasurableSpace History] in
include hε hfloor in
theorem reciprocal_le (h : History) (k : Fin K) : 1 / p h k ≤ 1 / ε :=
  one_div_le_one_div_of_le hε (hfloor h k)

include hbound hε hfloor in
theorem estimator_uniform_bound (k : Fin K) :
    ∀ᵐ z ∂jointMeasure p hpos hnorm hp μ ν, |estimator p k z| ≤ 1 / ε := by
  filter_upwards [estimator_bounds p hpos hnorm hp μ ν hbound k] with z hz
  rw [abs_of_nonneg hz.1]
  exact hz.2.trans (reciprocal_le p ε hε hfloor (history z) k)

include hbound hε hfloor in
theorem increment_uniform_bound (k : Fin K) :
    ∀ᵐ z ∂jointMeasure p hpos hnorm hp μ ν, |centered p ν k z| ≤ 1 / ε := by
  filter_upwards [increment_bound p hpos hnorm hp μ ν hbound k] with z hz
  exact hz.trans (reciprocal_le p ε hε hfloor (history z) k)

include hbound hε hfloor in
theorem estimator_integrable (k : Fin K) :
    Integrable (estimator p k) (jointMeasure p hpos hnorm hp μ ν) := by
  apply Integrable.of_bound (estimator_measurable p hp k).aestronglyMeasurable (1 / ε)
  simpa only [Real.norm_eq_abs] using estimator_uniform_bound p hpos hnorm hp μ ν hbound ε hε hfloor k

include hbound hε hfloor in
theorem estimator_square_integrable (k : Fin K) :
    Integrable (fun z => (estimator p k z) ^ 2) (jointMeasure p hpos hnorm hp μ ν) := by
  apply Integrable.of_bound ((estimator_measurable p hp k).pow_const 2).aestronglyMeasurable
    ((1 / ε) ^ 2)
  filter_upwards [estimator_uniform_bound p hpos hnorm hp μ ν hbound ε hε hfloor k] with z hz
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (estimator p k z)), sq_abs] using
    pow_le_pow_left₀ (abs_nonneg (estimator p k z)) hz 2

include hbound hε hfloor in
theorem centered_integrable (k : Fin K) :
    Integrable (centered p ν k) (jointMeasure p hpos hnorm hp μ ν) :=
  (estimator_integrable p hpos hnorm hp μ ν hbound ε hε hfloor k).sub (integrable_const _)

include hbound hε hfloor in
theorem centered_square_integrable (k : Fin K) :
    Integrable (fun z => (centered p ν k z) ^ 2) (jointMeasure p hpos hnorm hp μ ν) := by
  apply Integrable.of_bound ((centered_measurable p hp ν k).pow_const 2).aestronglyMeasurable
    ((1 / ε) ^ 2)
  filter_upwards [increment_uniform_bound p hpos hnorm hp μ ν hbound ε hε hfloor k] with z hz
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (centered p ν k z)), sq_abs] using
    pow_le_pow_left₀ (abs_nonneg (centered p ν k z)) hz 2

end SamplingFloor

/-- Product Fubini and kernel integration recover the fixed-history law of Step 18B. -/
theorem integral_by_history (F : Outcome History K → ℝ)
    (hF : Integrable F (jointMeasure p hpos hnorm hp μ ν))
    (hsection : ∀ h, Integrable (fun ay => F ((h, ay.1), ay.2))
      (StochasticImportanceWeighting.jointLaw p hpos hnorm ν h)) :
    (∫ z, F z ∂jointMeasure p hpos hnorm hp μ ν) =
      ∫ h, ∫ ay, F ((h, ay.1), ay.2)
        ∂StochasticImportanceWeighting.jointLaw p hpos hnorm ν h ∂μ := by
  rw [jointMeasure, integral_prod F hF, Measure.integral_compProd hF.integral_prod_left]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun h => (integral_prod _ (hsection h)).symm)

/-- The same bridge on every event specified solely by a measurable set of histories. -/
theorem setIntegral_by_history (F : Outcome History K → ℝ)
    (hF : Integrable F (jointMeasure p hpos hnorm hp μ ν))
    (hsection : ∀ h, Integrable (fun ay => F ((h, ay.1), ay.2))
      (StochasticImportanceWeighting.jointLaw p hpos hnorm ν h))
    (B : Set History) (hB : MeasurableSet B) :
    (∫ z in history ⁻¹' B, F z ∂jointMeasure p hpos hnorm hp μ ν) =
      ∫ h in B, ∫ ay, F ((h, ay.1), ay.2)
        ∂StochasticImportanceWeighting.jointLaw p hpos hnorm ν h ∂μ := by
  have hevent : (history (History := History) (K := K)) ⁻¹' B =
      (B ×ˢ Set.univ) ×ˢ Set.univ := by
    ext z
    simp [history]
  rw [jointMeasure, hevent, setIntegral_prod F hF.integrableOn]
  simp only [Measure.restrict_univ]
  rw [Measure.setIntegral_compProd hB MeasurableSet.univ hF.integral_prod_left.integrableOn]
  simp only [Measure.restrict_univ]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun h => (integral_prod _ (hsection h)).symm)

/-- Integrating a history-only function over a history event recovers its original law. -/
theorem setIntegral_history (G : History → ℝ)
    (hGint : Integrable (fun z : Outcome History K => G (history z))
      (jointMeasure p hpos hnorm hp μ ν)) (B : Set History) (hB : MeasurableSet B) :
    (∫ z in history ⁻¹' B, G (history z) ∂jointMeasure p hpos hnorm hp μ ν) = ∫ h in B, G h ∂μ := by
  rw [setIntegral_by_history p hpos hnorm hp μ ν _ hGint (fun h => integrable_const (G h)) B hB]
  simp [history]

/-- Characterize actual conditional expectation by all history-event integrals. -/
theorem condExp_of_history_integrals (F : Outcome History K → ℝ) (G : History → ℝ)
    (hF : Integrable F (jointMeasure p hpos hnorm hp μ ν)) (hG : Measurable G)
    (hGint : Integrable (fun z : Outcome History K => G (history z))
      (jointMeasure p hpos hnorm hp μ ν))
    (hsets : ∀ B : Set History, MeasurableSet B →
      (∫ z in history ⁻¹' B, F z ∂jointMeasure p hpos hnorm hp μ ν) =
        ∫ h in B, G h ∂μ) :
    (jointMeasure p hpos hnorm hp μ ν)[F | historySigma] =ᵐ[jointMeasure p hpos hnorm hp μ ν]
      (fun z => G (history z)) := by
  have hGm := history_function_measurable G hG (K := K)
  refine (ae_eq_condExp_of_forall_setIntegral_eq historySigma_le hF
    (fun _ _ _ => hGint.integrableOn) ?_
    hGm.stronglyMeasurable.aestronglyMeasurable).symm
  intro s hs _
  rcases (MeasurableSpace.measurableSet_comap (f := history)).mp hs with ⟨B, hB, rfl⟩
  rw [hsets B hB, setIntegral_history p hpos hnorm hp μ ν G hGint B hB]

/-- Fixed-history integral identities determine genuine conditional expectations. -/
theorem condExp_of_fixed_history (F : Outcome History K → ℝ) (G : History → ℝ)
    (hF : Integrable F (jointMeasure p hpos hnorm hp μ ν))
    (hsection : ∀ h, Integrable (fun ay => F ((h, ay.1), ay.2))
      (StochasticImportanceWeighting.jointLaw p hpos hnorm ν h))
    (hG : Measurable G)
    (hGint : Integrable (fun z : Outcome History K => G (history z))
      (jointMeasure p hpos hnorm hp μ ν))
    (hfixed : ∀ h, (∫ ay, F ((h, ay.1), ay.2)
      ∂StochasticImportanceWeighting.jointLaw p hpos hnorm ν h) = G h) :
    (jointMeasure p hpos hnorm hp μ ν)[F | historySigma] =ᵐ[jointMeasure p hpos hnorm hp μ ν]
      (fun z => G (history z)) := by
  apply condExp_of_history_integrals p hpos hnorm hp μ ν F G hF hG hGint
  intro B hB
  rw [setIntegral_by_history p hpos hnorm hp μ ν F hF hsection B hB]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall hfixed

section ConditionalMoments
variable (ε : ℝ) (hε : 0 < ε) (hfloor : ∀ h k, ε ≤ p h k)

include hbound hε hfloor in
theorem conditional_unbiased (k : Fin K) :
    (jointMeasure p hpos hnorm hp μ ν)[estimator p k | historySigma]
      =ᵐ[jointMeasure p hpos hnorm hp μ ν] (fun _ => StochasticImportanceWeighting.mean ν k) := by
  apply condExp_of_fixed_history p hpos hnorm hp μ ν (estimator p k)
    (fun _ => StochasticImportanceWeighting.mean ν k)
    (estimator_integrable p hpos hnorm hp μ ν hbound ε hε hfloor k)
    (fun h => StochasticImportanceWeighting.estimator_integrable p hpos hnorm ν hbound h k)
    measurable_const (integrable_const _)
    (fun h => StochasticImportanceWeighting.unbiased p hpos hnorm ν hbound h k)

include hbound hε hfloor in
theorem conditional_centered_mean_zero (k : Fin K) :
    (jointMeasure p hpos hnorm hp μ ν)[centered p ν k | historySigma]
      =ᵐ[jointMeasure p hpos hnorm hp μ ν] (fun _ => 0) := by
  have hsub := condExp_sub
    (estimator_integrable p hpos hnorm hp μ ν hbound ε hε hfloor k)
    (integrable_const (StochasticImportanceWeighting.mean ν k))
    (historySigma (History := History) (K := K))
  rw [condExp_const (μ := jointMeasure p hpos hnorm hp μ ν) historySigma_le
    (StochasticImportanceWeighting.mean ν k)] at hsub
  simp only [Pi.sub_def] at hsub
  change (jointMeasure p hpos hnorm hp μ ν)[(fun z => estimator p k z -
    StochasticImportanceWeighting.mean ν k) | historySigma]
      =ᵐ[jointMeasure p hpos hnorm hp μ ν] (fun _ => 0)
  filter_upwards [hsub, conditional_unbiased p hpos hnorm hp μ ν hbound ε hε hfloor k]
    with z hz hmean
  simpa only [Pi.sub_apply, hmean, sub_self] using hz

include hbound hε hfloor in
theorem secondMoment_ratio_integrable (k : Fin K) :
    Integrable (fun z : Outcome History K => StochasticImportanceWeighting.secondMoment ν k /
      p (history z) k) (jointMeasure p hpos hnorm hp μ ν) := by
  have hm2 := StochasticImportanceWeighting.secondMoment_bounds ν hbound k
  apply Integrable.of_bound
    (measurable_const.div ((hp k).comp history_measurable)).aestronglyMeasurable (1 / ε)
  exact Filter.Eventually.of_forall (fun z => by
    simp only [Real.norm_eq_abs, Pi.div_apply, Function.comp_apply]
    rw [abs_of_nonneg (div_nonneg hm2.1 (hpos (history z) k).le)]
    exact (div_le_div_of_nonneg_right hm2.2 (hpos (history z) k).le).trans
      (reciprocal_le p ε hε hfloor (history z) k))

include hbound hε hfloor in
theorem conditional_second_moment (k : Fin K) :
    (jointMeasure p hpos hnorm hp μ ν)[(fun z => (estimator p k z)^2) | historySigma]
      =ᵐ[jointMeasure p hpos hnorm hp μ ν]
      (fun z => StochasticImportanceWeighting.secondMoment ν k / p (history z) k) := by
  apply condExp_of_fixed_history p hpos hnorm hp μ ν (fun z => (estimator p k z)^2)
    (fun h => StochasticImportanceWeighting.secondMoment ν k / p h k)
    (estimator_square_integrable p hpos hnorm hp μ ν hbound ε hε hfloor k)
    (fun h => StochasticImportanceWeighting.estimator_square_integrable p hpos hnorm ν hbound h k)
    (measurable_const.div (hp k))
    (secondMoment_ratio_integrable p hpos hnorm hp μ ν hbound ε hε hfloor k)
    (fun h => StochasticImportanceWeighting.second_moment p hpos hnorm ν hbound h k)

include hbound hε hfloor in
theorem conditional_centered_second_moment (k : Fin K) :
    (jointMeasure p hpos hnorm hp μ ν)[(fun z => (centered p ν k z)^2) | historySigma]
      =ᵐ[jointMeasure p hpos hnorm hp μ ν]
      (fun z => StochasticImportanceWeighting.secondMoment ν k / p (history z) k -
        (StochasticImportanceWeighting.mean ν k)^2) := by
  have hGint : Integrable (fun z : Outcome History K =>
      StochasticImportanceWeighting.secondMoment ν k / p (history z) k -
        (StochasticImportanceWeighting.mean ν k)^2) (jointMeasure p hpos hnorm hp μ ν) :=
    (secondMoment_ratio_integrable p hpos hnorm hp μ ν hbound ε hε hfloor k).sub (integrable_const _)
  apply condExp_of_fixed_history p hpos hnorm hp μ ν (fun z => (centered p ν k z)^2)
    (fun h => StochasticImportanceWeighting.secondMoment ν k / p h k -
      (StochasticImportanceWeighting.mean ν k)^2)
    (centered_square_integrable p hpos hnorm hp μ ν hbound ε hε hfloor k)
    (fun h => StochasticImportanceWeighting.centered_square_integrable p hpos hnorm ν hbound h k)
    ((measurable_const.div (hp k)).sub measurable_const) hGint
    (fun h => StochasticImportanceWeighting.centered_second_moment p hpos hnorm ν hbound h k)

include hbound hε hfloor in
/-- The conditional centered second moment is nonnegative almost surely. -/
theorem conditional_variance_nonneg (k : Fin K) :
    ∀ᵐ z ∂jointMeasure p hpos hnorm hp μ ν,
      0 ≤ ((jointMeasure p hpos hnorm hp μ ν)[(fun z => (centered p ν k z) ^ 2) | historySigma]) z := by
  filter_upwards [conditional_centered_second_moment p hpos hnorm hp μ ν hbound ε hε hfloor k]
    with z hz
  rw [hz]
  rw [← StochasticImportanceWeighting.centered_second_moment p hpos hnorm ν hbound (history z) k]
  exact StochasticImportanceWeighting.variance_nonneg p hpos hnorm ν (history z) k

include hbound hε hfloor in
/-- The exact conditional moment has the history-dependent reciprocal upper bound. -/
theorem conditional_variance_bound (k : Fin K) :
    ∀ᵐ z ∂jointMeasure p hpos hnorm hp μ ν,
      ((jointMeasure p hpos hnorm hp μ ν)[(fun z => (centered p ν k z) ^ 2) | historySigma]) z ≤ 1 / p (history z) k := by
  filter_upwards [conditional_centered_second_moment p hpos hnorm hp μ ν hbound ε hε hfloor k]
    with z hz
  rw [hz]
  rw [← StochasticImportanceWeighting.centered_second_moment p hpos hnorm ν hbound (history z) k]
  exact StochasticImportanceWeighting.variance_bound p hpos hnorm ν hbound (history z) k

include hbound hε hfloor in
/-- The deterministic floor also bounds the conditional variance uniformly. -/
theorem conditional_variance_uniform_bound (k : Fin K) :
    ∀ᵐ z ∂jointMeasure p hpos hnorm hp μ ν,
      ((jointMeasure p hpos hnorm hp μ ν)[(fun z => (centered p ν k z) ^ 2) | historySigma]) z ≤ 1 / ε := by
  filter_upwards [conditional_variance_bound p hpos hnorm hp μ ν hbound ε hε hfloor k] with z hz
  exact hz.trans (reciprocal_le p ε hε hfloor (history z) k)

end ConditionalMoments

end OneRound

end BestOfBothWorlds.ConditionalImportanceWeighting
