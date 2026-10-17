module

public import BestOfBothWorlds.FiniteMaximizer
public import BestOfBothWorlds.BanditMartingales
public import BestOfBothWorlds.BanditSpecializations

/-!
The manuscript's UNIF algorithm in the existing finite trajectory model.
Every action uses the constant uniform probability vector. The terminal
recommendation maximizes the actual accumulated importance-weighted estimates,
with the smallest index resolving estimated-score ties.
-/

@[expose] public section

open MeasureTheory
open BestOfBothWorlds.AdaptiveBanditProcess
open BestOfBothWorlds.AdaptiveBanditMoments
open BestOfBothWorlds.BanditMartingales

namespace BestOfBothWorlds.UniformSampling

variable {K : ℕ}

/-- A concrete policy, constant in time, observed history, and arm. -/
noncomputable def policy (hK : 0 < K) : Policy K where
  prob _ _ _ := 1 / (K : ℝ)
  measurable_prob := fun _ _ => measurable_const
  positive := fun _ _ _ => one_div_pos.mpr (Nat.cast_pos.mpr hK)
  normalized := by
    intro t h
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_one_div_cancel (Nat.cast_ne_zero.mpr hK.ne')

@[simp] theorem policy_prob (hK : 0 < K) (t : ℕ) (h : ObservedHistory K t) (k : Fin K) :
    (policy hK).prob t h k = 1 / (K : ℝ) := rfl

theorem sampling_floor_pos (hK : 0 < K) : 0 < 1 / (K : ℝ) :=
  one_div_pos.mpr (Nat.cast_pos.mpr hK)

theorem policy_floor (hK : 0 < K) (n : ℕ) :
    ∀ t < n, ∀ h k, 1 / (K : ℝ) ≤ (policy hK).prob t h k :=
  fun _ _ _ _ => le_rfl

/-- The original importance-weighted estimator, specialized to UNIF. -/
noncomputable def estimatedGain (hK : 0 < K) (n : ℕ) (k : Fin K) (t : ℕ) :
    Trajectory K n → ℝ := importanceWeighted (policy hK) n k t

/-- The actual cumulative estimated score after all n rounds. -/
noncomputable def estimatedCumulative (hK : 0 < K) (n : ℕ) (k : Fin K) :
    Trajectory K n → ℝ := cumulativeEstimate (policy hK) n k n

theorem estimatedCumulative_eq_sum (hK : 0 < K) (n : ℕ) (k : Fin K)
    (z : Trajectory K n) :
    estimatedCumulative hK n k z = ∑ t ∈ Finset.range n, estimatedGain hK n k t z := by
  simp only [estimatedCumulative, cumulativeEstimate, partialSum, Finset.sum_apply, estimatedGain]

/-- The estimator depends only on the selected arm and the observed reward. -/
theorem estimatedGain_formula (hK : 0 < K) {n t : ℕ} (ht : t < n) (k : Fin K)
    (z : Trajectory K n) :
    estimatedGain hK n k t z =
      if roundAction t n ht z = k then (K : ℝ) * roundObservedReward t n ht z else 0 := by
  rw [estimatedGain, importanceWeighted_formula (policy hK) ht k z, policy_prob]
  simp only [one_div, div_inv_eq_mul, mul_comm]

/-- The estimated cumulative score is measurable from the final observed history. -/
theorem estimatedCumulative_stronglyMeasurable (hK : 0 < K) (n : ℕ) (k : Fin K) :
    StronglyMeasurable[historyFiltration n n] (estimatedCumulative hK n k) :=
  partialSum_stronglyAdapted _
    (fun t => importanceWeighted_stronglyMeasurable (policy hK) n k t) n

/-- UNIF recommends the smallest arm attaining its largest estimated score. -/
noncomputable def recommendation (hK : 0 < K) (n : ℕ) (z : Trajectory K n) : Fin K :=
  FiniteMaximizer.select hK (fun k => estimatedCumulative hK n k z)

theorem recommendation_max (hK : 0 < K) (n : ℕ) (z : Trajectory K n) (k : Fin K) :
    estimatedCumulative hK n k z ≤ estimatedCumulative hK n (recommendation hK n z) z :=
  FiniteMaximizer.le_select hK (fun j => estimatedCumulative hK n j z) k

theorem recommendation_smallest_tie (hK : 0 < K) (n : ℕ) (z : Trajectory K n) (k : Fin K)
    (heq : estimatedCumulative hK n k z =
      estimatedCumulative hK n (recommendation hK n z) z) :
    recommendation hK n z ≤ k :=
  FiniteMaximizer.select_le_of_eq hK _ k heq

/-- Recommendation measurability is with respect to observations, not latent rewards. -/
theorem recommendation_observable (hK : 0 < K) (n : ℕ) :
    Measurable[historyFiltration n n] (recommendation hK n) :=
  @FiniteMaximizer.select_measurable K hK (Trajectory K n) (historyFiltration n n)
    (fun z k => estimatedCumulative hK n k z)
    (fun k => (estimatedCumulative_stronglyMeasurable hK n k).measurable)

theorem recommendation_measurable (hK : 0 < K) (n : ℕ) :
    Measurable (recommendation hK n) :=
  (recommendation_observable hK n).mono ((historyFiltration n).le n) le_rfl

/-- Equal observed histories give exactly the same recommendation. -/
theorem recommendation_eq_of_observe_eq (hK : 0 < K) (n : ℕ)
    (z z' : Trajectory K n) (heq : observe z = observe z') :
    recommendation hK n z = recommendation hK n z' := by
  have hm := (recommendation_observable hK n) (measurableSet_singleton (recommendation hK n z))
  rw [historyFiltration_of_le (le_refl n)] at hm
  rcases (MeasurableSpace.measurableSet_comap (f := historyAt n n (le_refl n))).mp hm with
    ⟨S, _, hS⟩
  have hh : historyAt n n (le_refl n) z = historyAt n n (le_refl n) z' := by
    simpa [historyAt] using heq
  have hz : z ∈ historyAt n n (le_refl n) ⁻¹' S := by
    rw [hS]
    rfl
  have hz' : z' ∈ historyAt n n (le_refl n) ⁻¹' S := by
    change historyAt n n (le_refl n) z' ∈ S
    rwa [← hh]
  rw [hS] at hz'
  exact (Set.mem_singleton_iff.mp hz').symm

/-- Fixed oblivious rewards use the existing sequential law and Dirac environments. -/
noncomputable def law (hK : 0 < K) (g : ℕ → Fin K → ℝ) (n : ℕ) :
    Measure (Trajectory K n) :=
  trajectoryLaw (policy hK) (fun t => Measure.dirac (g t)) n

instance law_isProbabilityMeasure (hK : 0 < K) (g : ℕ → Fin K → ℝ) (n : ℕ) :
    IsProbabilityMeasure (law hK g n) := by
  let : ∀ t, IsProbabilityMeasure (Measure.dirac (g t)) := fun _ => inferInstance
  exact trajectoryLaw_isProbabilityMeasure (policy hK) (fun t => Measure.dirac (g t)) n

/-- Every current action has conditional probability 1/K given its observed past. -/
theorem conditional_pullIndicator_uniform (hK : 0 < K) (g : ℕ → Fin K → ℝ)
    {n t : ℕ} (ht : t < n) (k : Fin K) :
    (law hK g n)[pullIndicator n k t | historyFiltration n t] =ᵐ[law hK g n]
      (fun _ => 1 / (K : ℝ)) := by
  let : ∀ s, IsProbabilityMeasure (Measure.dirac (g s)) := fun _ => inferInstance
  have h := conditional_pullIndicator (policy hK) (fun s => Measure.dirac (g s)) n k t
  have hp : samplingProbability (policy hK) n k t =
      (fun _ : Trajectory K n => 1 / (K : ℝ)) := by
    funext z
    simp only [samplingProbability, dite_eq_left ht, policy_prob]
  rw [hp] at h
  exact h

/-- In the fixed-table law, UNIF's estimator is exactly K times the observed entry. -/
theorem estimatedGain_fixedTable (hK : 0 < K) (g : ℕ → Fin K → ℝ)
    {n t : ℕ} (ht : t < n) (k : Fin K) :
    ∀ᵐ z ∂law hK g n, estimatedGain hK n k t z =
      if roundAction t n ht z = k then (K : ℝ) * g t k else 0 := by
  filter_upwards [BanditSpecializations.fixedTable_observed_reward (policy hK) g n t ht]
    with z hz
  rw [estimatedGain_formula hK ht k z, hz]
  by_cases hk : roundAction t n ht z = k
  · simp only [hk]
  · simp only [ite_eq_right hk]

/-- Cumulative estimates in the fixed-table law sum precisely the prescribed UNIF gains. -/
theorem estimatedCumulative_fixedTable (hK : 0 < K) (g : ℕ → Fin K → ℝ) (n : ℕ) (k : Fin K) :
    ∀ᵐ z ∂law hK g n, estimatedCumulative hK n k z =
      ∑ t : Fin n, if roundAction t.val n t.isLt z = k then (K : ℝ) * g t.val k else 0 := by
  filter_upwards [ae_all_iff.2 (fun t : Fin n => estimatedGain_fixedTable hK g t.isLt k)]
    with z hz
  rw [estimatedCumulative_eq_sum]
  rw [← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl (fun t _ => hz t)

end BestOfBothWorlds.UniformSampling
