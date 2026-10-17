module

public import BestOfBothWorlds.BanditMartingales

/-! Finite-policy inputs and the stochastic and fixed-table instances of the bandit model. -/

@[expose] public section

open MeasureTheory
open BestOfBothWorlds.AdaptiveBanditProcess

namespace BestOfBothWorlds.BanditSpecializations

/-- Extend an arbitrary finite-horizon policy by uniform sampling afterwards. -/
noncomputable def finitePolicy {K n : ℕ} (hK : 0 < K)
    (p : (t : Fin n) → ObservedHistory K t.val → Fin K → ℝ)
    (hp : ∀ t k, Measurable (fun h => p t h k))
    (hpos : ∀ t h k, 0 < p t h k)
    (hnorm : ∀ t h, ∑ k, p t h k = 1) : Policy K where
  prob t h k := if ht : t < n then p ⟨t, ht⟩ h k else 1 / (K : ℝ)
  measurable_prob := by
    intro t k
    by_cases ht : t < n
    · simpa only [dite_eq_left ht] using hp ⟨t, ht⟩ k
    · simp only [dite_eq_right ht]
      exact measurable_const
  positive := by
    intro t h k
    by_cases ht : t < n
    · simpa only [dite_eq_left ht] using hpos ⟨t, ht⟩ h k
    · simp only [dite_eq_right ht]
      exact one_div_pos.mpr (Nat.cast_pos.mpr hK)
  normalized := by
    intro t h
    by_cases ht : t < n
    · simpa only [dite_eq_left ht] using hnorm ⟨t, ht⟩ h
    · simp only [dite_eq_right ht, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      exact mul_one_div_cancel (Nat.cast_ne_zero.mpr hK.ne')

theorem finitePolicy_agrees {K n : ℕ} (hK : 0 < K)
    (p : (t : Fin n) → ObservedHistory K t.val → Fin K → ℝ)
    (hp : ∀ t k, Measurable (fun h => p t h k))
    (hpos : ∀ t h k, 0 < p t h k)
    (hnorm : ∀ t h, ∑ k, p t h k = 1) (t : Fin n) (h : ObservedHistory K t.val) (k : Fin K) :
    (finitePolicy hK p hp hpos hnorm).prob t.val h k = p t h k := by
  simp [finitePolicy, t.isLt]

/-- A floor assumed only within the finite horizon is preserved by the extension. -/
theorem finitePolicy_floor {K n : ℕ} (hK : 0 < K)
    (p : (t : Fin n) → ObservedHistory K t.val → Fin K → ℝ)
    (hp : ∀ t k, Measurable (fun h => p t h k))
    (hpos : ∀ t h k, 0 < p t h k)
    (hnorm : ∀ t h, ∑ k, p t h k = 1) (ε : ℝ)
    (hfloor : ∀ t h k, ε ≤ p t h k) :
    ∀ t < n, ∀ h k, ε ≤ (finitePolicy hK p hp hpos hnorm).prob t h k := by
  intro t ht h k
  simpa only [finitePolicy, dite_eq_left ht] using hfloor ⟨t, ht⟩ h k


/-- Under the Dirac environment, the actual fresh vector equals the fixed table row. -/
theorem fixedTable_reward_vector {K : ℕ} (π : Policy K) (g : ℕ → Fin K → ℝ)
    (n t : ℕ) (ht : t < n) :
    ∀ᵐ z ∂trajectoryLaw π (fun s => Measure.dirac (g s)) n,
      roundRewardVector t n ht z = g t := by
  let : ∀ s, IsProbabilityMeasure (Measure.dirac (g s)) := fun _ => inferInstance
  have he : ∀ᵐ y ∂Measure.dirac (g t), y = g t := by simp
  exact (round_reward_measurePreserving π (fun s => Measure.dirac (g s)) ht).quasiMeasurePreserving.ae he

/-- The learner observes precisely the selected table entry. -/
theorem fixedTable_observed_reward {K : ℕ} (π : Policy K) (g : ℕ → Fin K → ℝ)
    (n t : ℕ) (ht : t < n) :
    ∀ᵐ z ∂trajectoryLaw π (fun s => Measure.dirac (g s)) n,
      roundObservedReward t n ht z = g t (roundAction t n ht z) := by
  filter_upwards [fixedTable_reward_vector π g n t ht] with z hz
  exact congrFun hz (roundAction t n ht z)


/-- Constant reward laws give the familiar estimate-minus-time-times-mean identity. -/
theorem stochastic_cumulative_identity {K : ℕ} (π : Policy K)
    (ν : Measure (Fin K → ℝ)) (n : ℕ) (k : Fin K) (t : ℕ) (ht : t ≤ n)
    (z : Trajectory K n) :
    BanditMartingales.cumulativeMartingale π (fun _ => ν) n k t z =
      BanditMartingales.cumulativeEstimate π n k t z -
        (t : ℝ) * StochasticImportanceWeighting.mean ν k := by
  rw [BanditMartingales.cumulativeMartingale_eq_estimate_sub_means π (fun _ => ν) n k t ht z]
  simp

/-- A general bounded stochastic reward law gives a genuine cumulative martingale. -/
theorem stochastic_martingale {K : ℕ} (π : Policy K)
    (ν : Measure (Fin K → ℝ)) [IsProbabilityMeasure ν] (n : ℕ)
    (hbound : ∀ᵐ y ∂ν, ∀ k, 0 ≤ y k ∧ y k ≤ 1)
    (ε : ℝ) (hε : 0 < ε) (hfloor : ∀ s < n, ∀ h k, ε ≤ π.prob s h k) (k : Fin K) :
    Martingale (BanditMartingales.cumulativeMartingale π (fun _ => ν) n k)
      (historyFiltration n) (trajectoryLaw π (fun _ => ν) n) := by
  let : ∀ _s : ℕ, IsProbabilityMeasure ν := fun _ => inferInstance
  exact BanditMartingales.cumulativeMartingale_martingale π (fun _ => ν) n
    (fun _ _ => hbound) ε hε hfloor k

/-- A fixed oblivious table is represented by Dirac laws, with no new process convention. -/
theorem fixedTable_conditional_unbiased {K : ℕ} (π : Policy K)
    (g : ℕ → Fin K → ℝ) (n : ℕ)
    (hg : ∀ s < n, ∀ k, 0 ≤ g s k ∧ g s k ≤ 1)
    (ε : ℝ) (hε : 0 < ε) (hfloor : ∀ s < n, ∀ h k, ε ≤ π.prob s h k)
    (k : Fin K) (t : ℕ) (ht : t < n) :
    (trajectoryLaw π (fun s => Measure.dirac (g s)) n)[
      AdaptiveBanditMoments.importanceWeighted π n k t | historyFiltration n t]
      =ᵐ[trajectoryLaw π (fun s => Measure.dirac (g s)) n] (fun _ => g t k) := by
  let : ∀ s, IsProbabilityMeasure (Measure.dirac (g s)) := fun _ => inferInstance
  have hb : ∀ s < n, ∀ᵐ y ∂Measure.dirac (g s), ∀ k, 0 ≤ y k ∧ y k ≤ 1 :=
    fun s hs => StochasticImportanceWeighting.dirac_reward_bounds (g s) (hg s hs)
  simpa only [ite_eq_left ht, StochasticImportanceWeighting.mean_dirac] using
    AdaptiveBanditMoments.conditional_unbiased π (fun s => Measure.dirac (g s)) n hb ε hε hfloor k t

/-- The deterministic-table conditional variance is exactly g²(1/p-1). -/
theorem fixedTable_conditional_variance {K : ℕ} (π : Policy K)
    (g : ℕ → Fin K → ℝ) (n : ℕ)
    (hg : ∀ s < n, ∀ k, 0 ≤ g s k ∧ g s k ≤ 1)
    (ε : ℝ) (hε : 0 < ε) (hfloor : ∀ s < n, ∀ h k, ε ≤ π.prob s h k)
    (k : Fin K) (t : ℕ) (ht : t < n) :
    (trajectoryLaw π (fun s => Measure.dirac (g s)) n)[
      (fun z => (AdaptiveBanditMoments.importanceWeighted π n k t z - g t k) ^ 2) |
        historyFiltration n t]
      =ᵐ[trajectoryLaw π (fun s => Measure.dirac (g s)) n]
        (fun z => (g t k) ^ 2 *
          (1 / π.prob t (historyAt n t (Nat.le_of_lt ht) z) k - 1)) := by
  let : ∀ s, IsProbabilityMeasure (Measure.dirac (g s)) := fun _ => inferInstance
  have hb : ∀ s < n, ∀ᵐ y ∂Measure.dirac (g s), ∀ k, 0 ≤ y k ∧ y k ≤ 1 :=
    fun s hs => StochasticImportanceWeighting.dirac_reward_bounds (g s) (hg s hs)
  have heq : (fun z : Trajectory K n =>
      (AdaptiveBanditMoments.importanceWeighted π n k t z - g t k) ^ 2) =
      fun z => (AdaptiveBanditMoments.increment π (fun s => Measure.dirac (g s)) n k t z) ^ 2 := by
    funext z
    simp only [AdaptiveBanditMoments.increment, ite_eq_left ht, StochasticImportanceWeighting.mean_dirac]
  rw [heq]
  filter_upwards [AdaptiveBanditMoments.conditional_increment_square π
    (fun s => Measure.dirac (g s)) n hb ε hε hfloor k t] with z hz
  rw [hz]
  simp only [AdaptiveBanditMoments.varianceIncrement, dite_eq_left ht,
    StochasticImportanceWeighting.mean_dirac, StochasticImportanceWeighting.secondMoment_dirac]
  ring

/-- For fixed rewards, centering subtracts exactly the cumulative table reward. -/
theorem fixedTable_cumulative_identity {K : ℕ} (π : Policy K)
    (g : ℕ → Fin K → ℝ) (n : ℕ) (k : Fin K) (t : ℕ) (ht : t ≤ n)
    (z : Trajectory K n) :
    BanditMartingales.cumulativeMartingale π (fun s => Measure.dirac (g s)) n k t z =
      BanditMartingales.cumulativeEstimate π n k t z - ∑ s ∈ Finset.range t, g s k := by
  rw [BanditMartingales.cumulativeMartingale_eq_estimate_sub_means π
    (fun s => Measure.dirac (g s)) n k t ht z]
  simp only [StochasticImportanceWeighting.mean_dirac]

/-- Oblivious time-varying reward tables give a genuine cumulative martingale. -/
theorem fixedTable_martingale {K : ℕ} (π : Policy K)
    (g : ℕ → Fin K → ℝ) (n : ℕ)
    (hg : ∀ s < n, ∀ k, 0 ≤ g s k ∧ g s k ≤ 1)
    (ε : ℝ) (hε : 0 < ε) (hfloor : ∀ s < n, ∀ h k, ε ≤ π.prob s h k) (k : Fin K) :
    Martingale (BanditMartingales.cumulativeMartingale π (fun s => Measure.dirac (g s)) n k)
      (historyFiltration n) (trajectoryLaw π (fun s => Measure.dirac (g s)) n) := by
  let : ∀ s, IsProbabilityMeasure (Measure.dirac (g s)) := fun _ => inferInstance
  exact BanditMartingales.cumulativeMartingale_martingale π (fun s => Measure.dirac (g s)) n
    (fun s hs => StochasticImportanceWeighting.dirac_reward_bounds (g s) (hg s hs)) ε hε hfloor k

end BestOfBothWorlds.BanditSpecializations
