module

public import BestOfBothWorlds.P1Algorithm
public import BestOfBothWorlds.RealizedGaps
public import BestOfBothWorlds.BanditConcentration
public import BestOfBothWorlds.ConcentrationConstants

/-!
The adversarial error probability of the concrete P1 learner. A wrong
recommendation is covered by exactly one best-arm lower-tail event and one
upper-tail event for each other arm. The existing fixed-table concentration
theorem gives the stronger coefficient `3/28`, followed by the frozen `3/40` bound.
-/

@[expose] public section

open MeasureTheory
open BestOfBothWorlds.AdaptiveBanditProcess
open BestOfBothWorlds.BanditMartingales

namespace BestOfBothWorlds.P1AdversarialBound

variable {K : ℕ}

/-- The universal P1 reciprocal-probability allowance is strictly positive. -/
theorem samplingBudget_pos (hK : 0 < K) :
    0 < (K : ℝ) * P1Ranking.harmonicK K :=
  mul_pos (Nat.cast_pos.mpr hK) (P1Ranking.harmonicK_pos hK)

/-- The estimation error uses the actual P1 estimator and the fixed table's gain. -/
noncomputable def estimationError (hK : 0 < K) (g : ℕ → Fin K → ℝ) (n : ℕ)
    (k : Fin K) (z : Trajectory K n) : ℝ :=
  P1Algorithm.estimatedCumulative hK n k z - RealizedGaps.cumulative g n k

/-- Identification error of the actual recommendation, with no prescribed best-arm index. -/
def errorEvent (hK : 0 < K) (g : ℕ → Fin K → ℝ) (n : ℕ) : Set (Trajectory K n) :=
  {z | P1Algorithm.recommendation hK n z ≠ RealizedGaps.best hK g n}

/-- The error event is measurable under the existing trajectory space. -/
theorem errorEvent_measurable (hK : 0 < K) (g : ℕ → Fin K → ℝ) (n : ℕ) :
    MeasurableSet (errorEvent hK g n) := by
  exact (measurableSet_eq_fun (P1Algorithm.recommendation_measurable hK n)
    measurable_const).compl

/-- The adversarial error probability is taken under the concrete P1 learner's law. -/
noncomputable def errorProbability (hK : 0 < K) (g : ℕ → Fin K → ℝ) (n : ℕ) : ℝ :=
  (P1Algorithm.law hK g n).real (errorEvent hK g n)

/-- The actual P1 policy gives the deterministic variance allowance `n*K*harmonicK`. -/
theorem predictableVariance_le (hK : 0 < K) (g : ℕ → Fin K → ℝ) (n : ℕ)
    (hg : ∀ s < n, ∀ k, 0 ≤ g s k ∧ g s k ≤ 1) (k : Fin K) (z : Trajectory K n) :
    predictableVariance (P1Algorithm.policy hK) (fun s => Measure.dirac (g s))
      n k n z ≤ (n : ℝ) * ((K : ℝ) * P1Ranking.harmonicK K) := by
  let : ∀ s, IsProbabilityMeasure (Measure.dirac (g s)) := fun _ => inferInstance
  have hv := predictableVariance_uniform_bound (P1Algorithm.policy hK)
    (fun s => Measure.dirac (g s)) n
    (fun s hs => StochasticImportanceWeighting.dirac_reward_bounds (g s) (hg s hs))
    (1 / ((K : ℝ) * P1Ranking.harmonicK K)) (one_div_pos.mpr (samplingBudget_pos hK))
    (P1Algorithm.policy_floor hK n) k n z
  simpa only [div_div_eq_mul_div, div_one] using hv

/-- A P1 upper estimation tail, with its actual predictable-variance bound discharged. -/
theorem estimation_upper_tail (hK : 0 < K) (g : ℕ → Fin K → ℝ) (n : ℕ)
    (hg : ∀ s < n, ∀ k, 0 ≤ g s k ∧ g s k ≤ 1) (hn : 0 < n)
    (k : Fin K) (x : ℝ) (hx : 0 ≤ x) :
    (P1Algorithm.law hK g n).real {z | x ≤ estimationError hK g n k z} ≤
      Real.exp (-x ^ 2 / (2 * ((n : ℝ) * ((K : ℝ) * P1Ranking.harmonicK K) + ((K : ℝ) * P1Ranking.harmonicK K) * x / 3))) := by
  have hd : 0 < (n : ℝ) * ((K : ℝ) * P1Ranking.harmonicK K) + ((K : ℝ) * P1Ranking.harmonicK K) * x / 3 :=
    add_pos_of_pos_of_nonneg (mul_pos (Nat.cast_pos.mpr hn) (samplingBudget_pos hK))
      (div_nonneg (mul_nonneg (samplingBudget_pos hK).le hx) (by norm_num))
  have ht := BanditConcentration.fixedTable_upper_tail (P1Algorithm.policy hK)
    g n hg (1 / ((K : ℝ) * P1Ranking.harmonicK K)) (one_div_pos.mpr (samplingBudget_pos hK))
    (P1Algorithm.policy_floor hK n) k n le_rfl x ((n : ℝ) * ((K : ℝ) * P1Ranking.harmonicK K)) hx
    (mul_nonneg (Nat.cast_nonneg n) (samplingBudget_pos hK).le)
    (by simpa only [one_div, inv_inv] using hd)
  have hsub : {z | x ≤ estimationError hK g n k z} ⊆
      {z | x ≤ cumulativeEstimate (P1Algorithm.policy hK) n k n z -
          ∑ s ∈ Finset.range n, g s k ∧
        predictableVariance (P1Algorithm.policy hK) (fun s => Measure.dirac (g s))
          n k n z ≤ (n : ℝ) * ((K : ℝ) * P1Ranking.harmonicK K)} := by
    intro z hz
    exact ⟨hz, predictableVariance_le hK g n hg k z⟩
  exact (measureReal_mono hsub).trans (by
    simpa only [P1Algorithm.law, one_div, inv_inv] using ht)

/-- The corresponding lower tail uses the same concrete law and variance allowance. -/
theorem estimation_lower_tail (hK : 0 < K) (g : ℕ → Fin K → ℝ) (n : ℕ)
    (hg : ∀ s < n, ∀ k, 0 ≤ g s k ∧ g s k ≤ 1) (hn : 0 < n)
    (k : Fin K) (x : ℝ) (hx : 0 ≤ x) :
    (P1Algorithm.law hK g n).real {z | estimationError hK g n k z ≤ -x} ≤
      Real.exp (-x ^ 2 / (2 * ((n : ℝ) * ((K : ℝ) * P1Ranking.harmonicK K) + ((K : ℝ) * P1Ranking.harmonicK K) * x / 3))) := by
  have hd : 0 < (n : ℝ) * ((K : ℝ) * P1Ranking.harmonicK K) + ((K : ℝ) * P1Ranking.harmonicK K) * x / 3 :=
    add_pos_of_pos_of_nonneg (mul_pos (Nat.cast_pos.mpr hn) (samplingBudget_pos hK))
      (div_nonneg (mul_nonneg (samplingBudget_pos hK).le hx) (by norm_num))
  have ht := BanditConcentration.fixedTable_lower_tail (P1Algorithm.policy hK)
    g n hg (1 / ((K : ℝ) * P1Ranking.harmonicK K)) (one_div_pos.mpr (samplingBudget_pos hK))
    (P1Algorithm.policy_floor hK n) k n le_rfl x ((n : ℝ) * ((K : ℝ) * P1Ranking.harmonicK K)) hx
    (mul_nonneg (Nat.cast_nonneg n) (samplingBudget_pos hK).le)
    (by simpa only [one_div, inv_inv] using hd)
  have hsub : {z | estimationError hK g n k z ≤ -x} ⊆
      {z | cumulativeEstimate (P1Algorithm.policy hK) n k n z -
          ∑ s ∈ Finset.range n, g s k ≤ -x ∧
        predictableVariance (P1Algorithm.policy hK) (fun s => Measure.dirac (g s))
          n k n z ≤ (n : ℝ) * ((K : ℝ) * P1Ranking.harmonicK K)} := by
    intro z hz
    exact ⟨hz, predictableVariance_le hK g n hg k z⟩
  exact (measureReal_mono hsub).trans (by
    simpa only [P1Algorithm.law, one_div, inv_inv] using ht)

/-- Exactly one signed event per arm: a lower tail for the best arm, upper otherwise. -/
noncomputable def signedTailEvent (hK : 0 < K) (g : ℕ → Fin K → ℝ) (n : ℕ)
    (x : ℝ) (k : Fin K) : Set (Trajectory K n) :=
  if k = RealizedGaps.best hK g n then {z | estimationError hK g n k z ≤ -x}
  else {z | x ≤ estimationError hK g n k z}

/-- Estimated-score ties are covered by the nonstrict signed deviations. -/
theorem errorEvent_subset_signedTails (hK : 2 ≤ K) (g : ℕ → Fin K → ℝ) (n : ℕ)
    (hUnique : RealizedGaps.UniqueBest (RealizedGaps.arms_pos hK) g n) :
    errorEvent (RealizedGaps.arms_pos hK) g n ⊆
      ⋃ k, signedTailEvent (RealizedGaps.arms_pos hK) g n
        ((n : ℝ) * RealizedGaps.minGap hK g n / 2) k := by
  intro z hz
  let hKpos := RealizedGaps.arms_pos hK
  let j := P1Algorithm.recommendation hKpos n z
  let kstar := RealizedGaps.best hKpos g n
  let x := (n : ℝ) * RealizedGaps.minGap hK g n / 2
  have hj : j ≠ kstar := hz
  by_cases hbest : estimationError hKpos g n kstar z ≤ -x
  · apply Set.mem_iUnion.mpr
    refine ⟨kstar, ?_⟩
    change z ∈ signedTailEvent hKpos g n x kstar
    rw [signedTailEvent, ite_eq_left rfl]
    exact hbest
  · have hsep : (n : ℝ) * RealizedGaps.minGap hK g n ≤
        RealizedGaps.cumulative g n kstar - RealizedGaps.cumulative g n j :=
      RealizedGaps.gap_separation hK g n hUnique j hj
    have hmax : P1Algorithm.estimatedCumulative hKpos n kstar z ≤
        P1Algorithm.estimatedCumulative hKpos n j z :=
      P1Algorithm.recommendation_max hKpos n z kstar
    have hjupper : x ≤ estimationError hKpos g n j z := by
      dsimp [estimationError] at hbest ⊢
      dsimp [x] at *
      linarith
    apply Set.mem_iUnion.mpr
    refine ⟨j, ?_⟩
    change z ∈ signedTailEvent hKpos g n x j
    rw [signedTailEvent, ite_eq_right hj]
    exact hjupper

/-- Each member of the `K`-event cover has the same exact Bernstein upper bound. -/
theorem signedTailEvent_bound (hK : 2 ≤ K) (g : ℕ → Fin K → ℝ) (n : ℕ)
    (hg : ∀ s < n, ∀ k, 0 ≤ g s k ∧ g s k ≤ 1)
    (hUnique : RealizedGaps.UniqueBest (RealizedGaps.arms_pos hK) g n) (k : Fin K) :
    (P1Algorithm.law (RealizedGaps.arms_pos hK) g n).real
      (signedTailEvent (RealizedGaps.arms_pos hK) g n
        ((n : ℝ) * RealizedGaps.minGap hK g n / 2) k) ≤
      Real.exp (-((n : ℝ) * (RealizedGaps.minGap hK g n) ^ 2) /
        (8 * ((K : ℝ) * P1Ranking.harmonicK K) * (1 + RealizedGaps.minGap hK g n / 6))) := by
  have hn := RealizedGaps.horizon_pos hK g n hUnique
  have hdelta := RealizedGaps.minGap_pos hK g n hUnique
  have hx : 0 ≤ (n : ℝ) * RealizedGaps.minGap hK g n / 2 := by positivity
  have he := ConcentrationConstants.adversarial_exponent (n : ℝ) ((K : ℝ) * P1Ranking.harmonicK K)
    (RealizedGaps.minGap hK g n) (Nat.cast_pos.mpr hn)
    (samplingBudget_pos (RealizedGaps.arms_pos hK)) hdelta.le
  by_cases hk : k = RealizedGaps.best (RealizedGaps.arms_pos hK) g n
  · have ht := estimation_lower_tail (RealizedGaps.arms_pos hK) g n hg hn k
      ((n : ℝ) * RealizedGaps.minGap hK g n / 2) hx
    rw [he] at ht
    simpa only [signedTailEvent, ite_eq_left hk] using ht
  · have ht := estimation_upper_tail (RealizedGaps.arms_pos hK) g n hg hn k
      ((n : ℝ) * RealizedGaps.minGap hK g n / 2) hx
    rw [he] at ht
    simpa only [signedTailEvent, ite_eq_right hk] using ht

/-- The concrete P1 algorithm satisfies the stronger, unsimplified Bernstein bound. -/
theorem p1_adversarial_error_bound_bernstein (hK : 2 ≤ K)
    (g : ℕ → Fin K → ℝ) (n : ℕ)
    (hg : ∀ s < n, ∀ k, 0 ≤ g s k ∧ g s k ≤ 1)
    (hUnique : RealizedGaps.UniqueBest (RealizedGaps.arms_pos hK) g n) :
    errorProbability (RealizedGaps.arms_pos hK) g n ≤
      (K : ℝ) * Real.exp (-((n : ℝ) * (RealizedGaps.minGap hK g n) ^ 2) /
        (8 * ((K : ℝ) * P1Ranking.harmonicK K) * (1 + RealizedGaps.minGap hK g n / 6))) := by
  unfold errorProbability
  calc
    _ ≤ (P1Algorithm.law (RealizedGaps.arms_pos hK) g n).real
        (⋃ k, signedTailEvent (RealizedGaps.arms_pos hK) g n
          ((n : ℝ) * RealizedGaps.minGap hK g n / 2) k) :=
      measureReal_mono (errorEvent_subset_signedTails hK g n hUnique)
    _ ≤ ∑ k, (P1Algorithm.law (RealizedGaps.arms_pos hK) g n).real
        (signedTailEvent (RealizedGaps.arms_pos hK) g n
          ((n : ℝ) * RealizedGaps.minGap hK g n / 2) k) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _k : Fin K, Real.exp (-((n : ℝ) * (RealizedGaps.minGap hK g n) ^ 2) /
        (8 * ((K : ℝ) * P1Ranking.harmonicK K) * (1 + RealizedGaps.minGap hK g n / 6))) :=
      Finset.sum_le_sum (fun k _ => signedTailEvent_bound hK g n hg hUnique k)
    _ = _ := by simp

/-- The stronger adversarial bound for the actual P1 learner before the stated 3/40 relaxation. -/
theorem p1_adversarial_error_bound_strong (hK : 2 ≤ K) (g : ℕ → Fin K → ℝ) (n : ℕ)
    (hg : ∀ s < n, ∀ k, 0 ≤ g s k ∧ g s k ≤ 1)
    (hUnique : RealizedGaps.UniqueBest (RealizedGaps.arms_pos hK) g n) :
    errorProbability (RealizedGaps.arms_pos hK) g n ≤
      (K : ℝ) * Real.exp (-(3 * (n : ℝ)) / (28 * P1Ranking.harmonicK K * RealizedGaps.complexity hK g n)) := by
  have hdelta := RealizedGaps.minGap_pos hK g n hUnique
  have hdelta_one := RealizedGaps.minGap_le_one hK g n hUnique hg
  have hKpos : (0 : ℝ) < K := Nat.cast_pos.mpr (RealizedGaps.arms_pos hK)
  calc
    _ ≤ (K : ℝ) * Real.exp (-((n : ℝ) * (RealizedGaps.minGap hK g n) ^ 2) /
        (8 * ((K : ℝ) * P1Ranking.harmonicK K) * (1 + RealizedGaps.minGap hK g n / 6))) :=
      p1_adversarial_error_bound_bernstein hK g n hg hUnique
    _ ≤ (K : ℝ) * Real.exp (-(3 * (n : ℝ) * (RealizedGaps.minGap hK g n) ^ 2) /
        (28 * ((K : ℝ) * P1Ranking.harmonicK K))) :=
      mul_le_mul_of_nonneg_left
        (ConcentrationConstants.adversarial_exp_le (n : ℝ) ((K : ℝ) * P1Ranking.harmonicK K)
          (RealizedGaps.minGap hK g n) (Nat.cast_nonneg n) (samplingBudget_pos (RealizedGaps.arms_pos hK)) hdelta.le hdelta_one)
        (Nat.cast_nonneg K)
    _ = _ := by
      rw [RealizedGaps.complexity_eq]
      congr 1
      congr 1
      field_simp [ne_of_gt hKpos, ne_of_gt hdelta,
        ne_of_gt (P1Ranking.harmonicK_pos (RealizedGaps.arms_pos hK))]

/-- The adversarial assertion of frozen Theorem 6, with its exact coefficient 3/40. -/
theorem p1_adversarial_error_bound (hK : 2 ≤ K) (g : ℕ → Fin K → ℝ) (n : ℕ)
    (hg : ∀ s < n, ∀ k, 0 ≤ g s k ∧ g s k ≤ 1)
    (hUnique : RealizedGaps.UniqueBest (RealizedGaps.arms_pos hK) g n) :
    errorProbability (RealizedGaps.arms_pos hK) g n ≤
      (K : ℝ) * Real.exp (-(3 * (n : ℝ)) /
        (40 * P1Ranking.harmonicK K * RealizedGaps.complexity hK g n)) := by
  have hL := P1Ranking.harmonicK_pos (RealizedGaps.arms_pos hK)
  have hH := RealizedGaps.complexity_pos hK g n hUnique
  have hc : 0 < P1Ranking.harmonicK K * RealizedGaps.complexity hK g n :=
    mul_pos (P1Ranking.harmonicK_pos (RealizedGaps.arms_pos hK))
      (RealizedGaps.complexity_pos hK g n hUnique)
  refine (p1_adversarial_error_bound_strong hK g n hg hUnique).trans ?_
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg K)
  apply Real.exp_le_exp.mpr
  apply (div_le_div_iff₀ (by positivity : 0 < 28 * P1Ranking.harmonicK K *
    RealizedGaps.complexity hK g n) (by positivity : 0 < 40 * P1Ranking.harmonicK K *
    RealizedGaps.complexity hK g n)).2
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

end BestOfBothWorlds.P1AdversarialBound
