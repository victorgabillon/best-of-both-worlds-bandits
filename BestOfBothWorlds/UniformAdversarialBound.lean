module

public import BestOfBothWorlds.UniformSampling
public import BestOfBothWorlds.RealizedGaps
public import BestOfBothWorlds.BanditConcentration
public import BestOfBothWorlds.ConcentrationConstants

/-!
The adversarial error probability of the concrete uniform learner. A wrong
recommendation is covered by exactly one best-arm lower-tail event and one
upper-tail event for each other arm. The existing fixed-table concentration
theorem then proves the manuscript's coefficient `3/28` and leading factor `K`.
-/

@[expose] public section

open MeasureTheory
open BestOfBothWorlds.AdaptiveBanditProcess
open BestOfBothWorlds.BanditMartingales

namespace BestOfBothWorlds.UniformAdversarialBound

variable {K : ℕ}

/-- The estimation error uses the actual uniform estimator and the fixed table's gain. -/
noncomputable def estimationError (hK : 0 < K) (g : ℕ → Fin K → ℝ) (n : ℕ)
    (k : Fin K) (z : Trajectory K n) : ℝ :=
  UniformSampling.estimatedCumulative hK n k z - RealizedGaps.cumulative g n k

/-- Identification error of the actual recommendation, with no prescribed best-arm index. -/
def errorEvent (hK : 0 < K) (g : ℕ → Fin K → ℝ) (n : ℕ) : Set (Trajectory K n) :=
  {z | UniformSampling.recommendation hK n z ≠ RealizedGaps.best hK g n}

/-- The error event is measurable under the existing trajectory space. -/
theorem errorEvent_measurable (hK : 0 < K) (g : ℕ → Fin K → ℝ) (n : ℕ) :
    MeasurableSet (errorEvent hK g n) := by
  exact (measurableSet_eq_fun (UniformSampling.recommendation_measurable hK n)
    measurable_const).compl

/-- The adversarial error probability is taken under the concrete uniform learner's law. -/
noncomputable def errorProbability (hK : 0 < K) (g : ℕ → Fin K → ℝ) (n : ℕ) : ℝ :=
  (UniformSampling.law hK g n).real (errorEvent hK g n)

/-- The actual uniform policy gives the deterministic variance allowance `n*K`. -/
theorem predictableVariance_le (hK : 0 < K) (g : ℕ → Fin K → ℝ) (n : ℕ)
    (hg : ∀ s < n, ∀ k, 0 ≤ g s k ∧ g s k ≤ 1) (k : Fin K) (z : Trajectory K n) :
    predictableVariance (UniformSampling.policy hK) (fun s => Measure.dirac (g s))
      n k n z ≤ (n : ℝ) * (K : ℝ) := by
  let : ∀ s, IsProbabilityMeasure (Measure.dirac (g s)) := fun _ => inferInstance
  have hv := predictableVariance_uniform_bound (UniformSampling.policy hK)
    (fun s => Measure.dirac (g s)) n
    (fun s hs => StochasticImportanceWeighting.dirac_reward_bounds (g s) (hg s hs))
    (1 / (K : ℝ)) (one_div_pos.mpr (Nat.cast_pos.mpr hK))
    (UniformSampling.policy_floor hK n) k n z
  simpa only [div_div_eq_mul_div, div_one] using hv

/-- A uniform upper estimation tail, with its actual predictable-variance bound discharged. -/
theorem estimation_upper_tail (hK : 0 < K) (g : ℕ → Fin K → ℝ) (n : ℕ)
    (hg : ∀ s < n, ∀ k, 0 ≤ g s k ∧ g s k ≤ 1) (hn : 0 < n)
    (k : Fin K) (x : ℝ) (hx : 0 ≤ x) :
    (UniformSampling.law hK g n).real {z | x ≤ estimationError hK g n k z} ≤
      Real.exp (-x ^ 2 / (2 * ((n : ℝ) * (K : ℝ) + (K : ℝ) * x / 3))) := by
  have hd : 0 < (n : ℝ) * (K : ℝ) + (K : ℝ) * x / 3 :=
    add_pos_of_pos_of_nonneg (mul_pos (Nat.cast_pos.mpr hn) (Nat.cast_pos.mpr hK))
      (by positivity)
  have ht := BanditConcentration.fixedTable_upper_tail (UniformSampling.policy hK)
    g n hg (1 / (K : ℝ)) (one_div_pos.mpr (Nat.cast_pos.mpr hK))
    (UniformSampling.policy_floor hK n) k n le_rfl x ((n : ℝ) * (K : ℝ)) hx
    (mul_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg K))
    (by simpa only [one_div, inv_inv] using hd)
  have hsub : {z | x ≤ estimationError hK g n k z} ⊆
      {z | x ≤ cumulativeEstimate (UniformSampling.policy hK) n k n z -
          ∑ s ∈ Finset.range n, g s k ∧
        predictableVariance (UniformSampling.policy hK) (fun s => Measure.dirac (g s))
          n k n z ≤ (n : ℝ) * (K : ℝ)} := by
    intro z hz
    exact ⟨hz, predictableVariance_le hK g n hg k z⟩
  exact (measureReal_mono hsub).trans (by
    simpa only [UniformSampling.law, one_div, inv_inv] using ht)

/-- The corresponding lower tail uses the same concrete law and variance allowance. -/
theorem estimation_lower_tail (hK : 0 < K) (g : ℕ → Fin K → ℝ) (n : ℕ)
    (hg : ∀ s < n, ∀ k, 0 ≤ g s k ∧ g s k ≤ 1) (hn : 0 < n)
    (k : Fin K) (x : ℝ) (hx : 0 ≤ x) :
    (UniformSampling.law hK g n).real {z | estimationError hK g n k z ≤ -x} ≤
      Real.exp (-x ^ 2 / (2 * ((n : ℝ) * (K : ℝ) + (K : ℝ) * x / 3))) := by
  have hd : 0 < (n : ℝ) * (K : ℝ) + (K : ℝ) * x / 3 :=
    add_pos_of_pos_of_nonneg (mul_pos (Nat.cast_pos.mpr hn) (Nat.cast_pos.mpr hK))
      (by positivity)
  have ht := BanditConcentration.fixedTable_lower_tail (UniformSampling.policy hK)
    g n hg (1 / (K : ℝ)) (one_div_pos.mpr (Nat.cast_pos.mpr hK))
    (UniformSampling.policy_floor hK n) k n le_rfl x ((n : ℝ) * (K : ℝ)) hx
    (mul_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg K))
    (by simpa only [one_div, inv_inv] using hd)
  have hsub : {z | estimationError hK g n k z ≤ -x} ⊆
      {z | cumulativeEstimate (UniformSampling.policy hK) n k n z -
          ∑ s ∈ Finset.range n, g s k ≤ -x ∧
        predictableVariance (UniformSampling.policy hK) (fun s => Measure.dirac (g s))
          n k n z ≤ (n : ℝ) * (K : ℝ)} := by
    intro z hz
    exact ⟨hz, predictableVariance_le hK g n hg k z⟩
  exact (measureReal_mono hsub).trans (by
    simpa only [UniformSampling.law, one_div, inv_inv] using ht)

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
  let j := UniformSampling.recommendation hKpos n z
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
    have hmax : UniformSampling.estimatedCumulative hKpos n kstar z ≤
        UniformSampling.estimatedCumulative hKpos n j z :=
      UniformSampling.recommendation_max hKpos n z kstar
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
    (UniformSampling.law (RealizedGaps.arms_pos hK) g n).real
      (signedTailEvent (RealizedGaps.arms_pos hK) g n
        ((n : ℝ) * RealizedGaps.minGap hK g n / 2) k) ≤
      Real.exp (-((n : ℝ) * (RealizedGaps.minGap hK g n) ^ 2) /
        (8 * (K : ℝ) * (1 + RealizedGaps.minGap hK g n / 6))) := by
  have hn := RealizedGaps.horizon_pos hK g n hUnique
  have hdelta := RealizedGaps.minGap_pos hK g n hUnique
  have hx : 0 ≤ (n : ℝ) * RealizedGaps.minGap hK g n / 2 := by positivity
  have he := ConcentrationConstants.adversarial_exponent (n : ℝ) (K : ℝ)
    (RealizedGaps.minGap hK g n) (Nat.cast_pos.mpr hn)
    (Nat.cast_pos.mpr (RealizedGaps.arms_pos hK)) hdelta.le
  by_cases hk : k = RealizedGaps.best (RealizedGaps.arms_pos hK) g n
  · have ht := estimation_lower_tail (RealizedGaps.arms_pos hK) g n hg hn k
      ((n : ℝ) * RealizedGaps.minGap hK g n / 2) hx
    rw [he] at ht
    simpa only [signedTailEvent, ite_eq_left hk] using ht
  · have ht := estimation_upper_tail (RealizedGaps.arms_pos hK) g n hg hn k
      ((n : ℝ) * RealizedGaps.minGap hK g n / 2) hx
    rw [he] at ht
    simpa only [signedTailEvent, ite_eq_right hk] using ht

/-- The concrete uniform algorithm satisfies the stronger, unsimplified Bernstein bound. -/
theorem unif_adversarial_error_bound_bernstein (hK : 2 ≤ K)
    (g : ℕ → Fin K → ℝ) (n : ℕ)
    (hg : ∀ s < n, ∀ k, 0 ≤ g s k ∧ g s k ≤ 1)
    (hUnique : RealizedGaps.UniqueBest (RealizedGaps.arms_pos hK) g n) :
    errorProbability (RealizedGaps.arms_pos hK) g n ≤
      (K : ℝ) * Real.exp (-((n : ℝ) * (RealizedGaps.minGap hK g n) ^ 2) /
        (8 * (K : ℝ) * (1 + RealizedGaps.minGap hK g n / 6))) := by
  unfold errorProbability
  calc
    _ ≤ (UniformSampling.law (RealizedGaps.arms_pos hK) g n).real
        (⋃ k, signedTailEvent (RealizedGaps.arms_pos hK) g n
          ((n : ℝ) * RealizedGaps.minGap hK g n / 2) k) :=
      measureReal_mono (errorEvent_subset_signedTails hK g n hUnique)
    _ ≤ ∑ k, (UniformSampling.law (RealizedGaps.arms_pos hK) g n).real
        (signedTailEvent (RealizedGaps.arms_pos hK) g n
          ((n : ℝ) * RealizedGaps.minGap hK g n / 2) k) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _k : Fin K, Real.exp (-((n : ℝ) * (RealizedGaps.minGap hK g n) ^ 2) /
        (8 * (K : ℝ) * (1 + RealizedGaps.minGap hK g n / 6))) :=
      Finset.sum_le_sum (fun k _ => signedTailEvent_bound hK g n hg hUnique k)
    _ = _ := by simp

/-- Theorem 1: end-to-end adversarial error bound for the actual uniform learner. -/
theorem unif_adversarial_error_bound (hK : 2 ≤ K) (g : ℕ → Fin K → ℝ) (n : ℕ)
    (hg : ∀ s < n, ∀ k, 0 ≤ g s k ∧ g s k ≤ 1)
    (hUnique : RealizedGaps.UniqueBest (RealizedGaps.arms_pos hK) g n) :
    errorProbability (RealizedGaps.arms_pos hK) g n ≤
      (K : ℝ) * Real.exp (-(3 * (n : ℝ)) / (28 * RealizedGaps.complexity hK g n)) := by
  have hdelta := RealizedGaps.minGap_pos hK g n hUnique
  have hdelta_one := RealizedGaps.minGap_le_one hK g n hUnique hg
  have hKpos : (0 : ℝ) < K := Nat.cast_pos.mpr (RealizedGaps.arms_pos hK)
  calc
    _ ≤ (K : ℝ) * Real.exp (-((n : ℝ) * (RealizedGaps.minGap hK g n) ^ 2) /
        (8 * (K : ℝ) * (1 + RealizedGaps.minGap hK g n / 6))) :=
      unif_adversarial_error_bound_bernstein hK g n hg hUnique
    _ ≤ (K : ℝ) * Real.exp (-(3 * (n : ℝ) * (RealizedGaps.minGap hK g n) ^ 2) /
        (28 * (K : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (ConcentrationConstants.adversarial_exp_le (n : ℝ) (K : ℝ)
          (RealizedGaps.minGap hK g n) (Nat.cast_nonneg n) hKpos hdelta.le hdelta_one)
        (Nat.cast_nonneg K)
    _ = _ := by
      rw [RealizedGaps.complexity_eq]
      congr 1
      congr 1
      field_simp [ne_of_gt hKpos, ne_of_gt hdelta]

end BestOfBothWorlds.UniformAdversarialBound
