module

public import BestOfBothWorlds.P1StochasticEvents
public import BestOfBothWorlds.P1Complexity
public import BestOfBothWorlds.BanditConcentration
public import BestOfBothWorlds.ConcentrationConstants

/-!
The stochastic guarantee for the actual P1 recommendation. A fixed admissible
schedule is held throughout the comparison and ranking arguments. The future
good-ranking event supplies the predictable-variance allowance under the
original law. Only the final error bound is minimized over schedules.
-/

@[expose] public section

open MeasureTheory Filter
open BestOfBothWorlds.AdaptiveBanditProcess
open BestOfBothWorlds.AdaptiveBanditMoments
open BestOfBothWorlds.BanditMartingales
open BestOfBothWorlds.P1StochasticEvents

namespace BestOfBothWorlds.P1StochasticBound

variable {K : ℕ}

/-- Candidate doubled-gap ranks, including exact doubled-gap equality. -/
noncomputable def doubledCandidates (hK : 2 ≤ K) (ν : Measure (Fin K → ℝ))
    (j : Fin K) : Finset (Fin K) := by
  classical
  exact Finset.univ.filter (fun r => j ≤ r ∧
    P1StochasticModel.gap hK ν r ≤ 2 * P1StochasticModel.gap hK ν j)

theorem doubledCandidates_nonempty (hK : 2 ≤ K) (ν : Measure (Fin K → ℝ)) (j : Fin K) :
    (doubledCandidates hK ν j).Nonempty := by
  classical
  have hg : 0 ≤ P1StochasticModel.gap hK ν j := P1StochasticModel.trueGap_nonneg hK ν _
  exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, by linarith⟩⟩

/-- The sentinel-free maximum used for the worse arm's variance calculation. -/
noncomputable def doubledRank (hK : 2 ≤ K) (ν : Measure (Fin K → ℝ)) (j : Fin K) : Fin K :=
  (doubledCandidates hK ν j).max' (doubledCandidates_nonempty hK ν j)

theorem le_doubledRank (hK : 2 ≤ K) (ν : Measure (Fin K → ℝ)) (j : Fin K) :
    j ≤ doubledRank hK ν j := by
  classical
  exact (Finset.mem_filter.mp ((doubledCandidates hK ν j).max'_mem
    (doubledCandidates_nonempty hK ν j))).2.1

theorem gap_doubledRank_le (hK : 2 ≤ K) (ν : Measure (Fin K → ℝ)) (j : Fin K) :
    P1StochasticModel.gap hK ν (doubledRank hK ν j) ≤ 2 * P1StochasticModel.gap hK ν j := by
  classical
  exact (Finset.mem_filter.mp ((doubledCandidates hK ν j).max'_mem
    (doubledCandidates_nonempty hK ν j))).2.2

theorem gap_lt_half_later (hK : 2 ≤ K) (ν : Measure (Fin K → ℝ)) (j p : Fin K)
    (hp : doubledRank hK ν j < p) :
    P1StochasticModel.gap hK ν j < P1StochasticModel.gap hK ν p / 2 := by
  classical
  by_contra hnot
  have hmem : p ∈ doubledCandidates hK ν j :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (le_doubledRank hK ν j).trans hp.le, by linarith⟩
  exact (not_lt_of_ge (Finset.le_max' _ _ hmem)) hp

section Stochastic

variable (hK : 2 ≤ K) (ν : Measure (Fin K → ℝ)) [IsProbabilityMeasure ν]
variable (hbound : ∀ᵐ y ∂ν, ∀ k, 0 ≤ y k ∧ y k ≤ 1)
variable (hUnique : P1StochasticModel.UniqueBest hK ν)

include hUnique in
omit [IsProbabilityMeasure ν] in
/-- The fixed-schedule complexity comparison applies after every comparison time. -/
theorem exponent_le {n : ℕ} (s : P1Schedule.Schedule hK n) (r : Fin K)
    (t : ℕ) (ht : s.time r ≤ t) :
    -((t : ℝ) * P1StochasticModel.gap hK ν r / 8) ^ 2 /
        (2 * (P1Ranking.harmonicK K * (P1Schedule.accumulated s r +
          P1Schedule.rank r * ((t : ℝ) - (s.time r : ℝ))) +
          ((K : ℝ) * P1Ranking.harmonicK K) * ((t : ℝ) * P1StochasticModel.gap hK ν r / 8) / 3)) ≤
      -(n : ℝ) / (128 * P1Complexity.fixedComplexity (P1StochasticModel.gap hK ν) s) := by
  have hH := P1Ranking.harmonicK_pos (arms_pos hK)
  have hgap := P1StochasticModel.gap_pos hK ν hUnique r
  have hD : 0 < P1Schedule.accumulated s r +
      P1Schedule.rank r * ((t : ℝ) - (s.time r : ℝ)) +
      ((K : ℝ) / 24) * (t : ℝ) * P1StochasticModel.gap hK ν r :=
    add_pos_of_pos_of_nonneg (P1Schedule.continuation_pos s r t ht) (by positivity)
  rw [ConcentrationConstants.stochastic_schedule_exponent _ _ _ _ _ _ _ hH hD]
  have hc := P1Complexity.exponent_comparison hK (P1StochasticModel.gap hK ν)
    (P1StochasticModel.gap_pos hK ν hUnique _) (P1StochasticModel.gap_monotone hK ν) s r t ht
  simpa only [neg_div] using neg_le_neg hc

include hbound hUnique in
/-- One upper martingale tail together with the future good-ranking event. -/
theorem upper_on_earlierGood {n : ℕ} (s : P1Schedule.Schedule hK n)
    (i r h : Fin K) (hir : i ≤ r)
    (hgap : ∀ p : Fin K, r < p → P1StochasticModel.trueGap hK ν h < P1StochasticModel.gap hK ν p / 2)
    (t : ℕ) (ht : s.time r ≤ t) (htn : t ≤ n) :
    (law hK ν n).real {z | z ∈ earlierGood hK ν s i ∧
      (t : ℝ) * P1StochasticModel.gap hK ν r / 8 ≤
        cumulativeMartingale (P1Algorithm.policy (arms_pos hK)) (fun _ => ν) n h t z} ≤
      Real.exp (-(n : ℝ) / (128 * P1Complexity.fixedComplexity (P1StochasticModel.gap hK ν) s)) := by
  let : ∀ _s : ℕ, IsProbabilityMeasure ν := fun _ => inferInstance
  have hH := P1Ranking.harmonicK_pos (arms_pos hK)
  have hgapr := P1StochasticModel.gap_pos hK ν hUnique r
  have hQ := P1Schedule.continuation_pos s r t ht
  have hx : 0 ≤ (t : ℝ) * P1StochasticModel.gap hK ν r / 8 := by positivity
  have hv : 0 ≤ P1Ranking.harmonicK K * (P1Schedule.accumulated s r +
      P1Schedule.rank r * ((t : ℝ) - (s.time r : ℝ))) := (mul_pos hH hQ).le
  have hd := ConcentrationConstants.stochastic_denominator_pos (P1Ranking.harmonicK K)
    (K : ℝ) (P1Schedule.accumulated s r + P1Schedule.rank r * ((t : ℝ) - (s.time r : ℝ)))
    (t : ℝ) (P1StochasticModel.gap hK ν r) hH (Nat.cast_nonneg K) hQ
    (Nat.cast_nonneg t) hgapr.le
  have htbound := BanditConcentration.upper_tail_on_event (P1Algorithm.policy (arms_pos hK))
    (fun _ => ν) n (fun _ _ => hbound)
    (1 / ((K : ℝ) * P1Ranking.harmonicK K)) (P1Algorithm.sampling_floor_pos (arms_pos hK))
    (P1Algorithm.policy_floor (arms_pos hK) n) h t
    ((t : ℝ) * P1StochasticModel.gap hK ν r / 8)
    (P1Ranking.harmonicK K * (P1Schedule.accumulated s r +
      P1Schedule.rank r * ((t : ℝ) - (s.time r : ℝ)))) hx hv
    (by simpa only [one_div, inv_inv] using hd)
    (earlierGood hK ν s i) (earlierGood_measurable hK ν s i)
    (Eventually.of_forall (fun z hz => variance_on_earlierGood hK ν hbound s i r h hir hgap t ht htn z hz))
  have htail : (law hK ν n).real {z | z ∈ earlierGood hK ν s i ∧
      (t : ℝ) * P1StochasticModel.gap hK ν r / 8 ≤
        cumulativeMartingale (P1Algorithm.policy (arms_pos hK)) (fun _ => ν) n h t z} ≤
      Real.exp (-((t : ℝ) * P1StochasticModel.gap hK ν r / 8) ^ 2 /
        (2 * (P1Ranking.harmonicK K * (P1Schedule.accumulated s r +
          P1Schedule.rank r * ((t : ℝ) - (s.time r : ℝ))) +
          ((K : ℝ) * P1Ranking.harmonicK K) * ((t : ℝ) * P1StochasticModel.gap hK ν r / 8) / 3))) := by
    simpa only [law, one_div, inv_inv] using htbound
  exact htail.trans (Real.exp_le_exp.mpr (exponent_le hK ν hUnique s r t ht))

include hbound hUnique in
/-- The lower martingale tail uses the same original law and variance event. -/
theorem lower_on_earlierGood {n : ℕ} (s : P1Schedule.Schedule hK n)
    (i r h : Fin K) (hir : i ≤ r)
    (hgap : ∀ p : Fin K, r < p → P1StochasticModel.trueGap hK ν h < P1StochasticModel.gap hK ν p / 2)
    (t : ℕ) (ht : s.time r ≤ t) (htn : t ≤ n) :
    (law hK ν n).real {z | z ∈ earlierGood hK ν s i ∧
      cumulativeMartingale (P1Algorithm.policy (arms_pos hK)) (fun _ => ν) n h t z ≤
        -((t : ℝ) * P1StochasticModel.gap hK ν r / 8)} ≤
      Real.exp (-(n : ℝ) / (128 * P1Complexity.fixedComplexity (P1StochasticModel.gap hK ν) s)) := by
  let : ∀ _s : ℕ, IsProbabilityMeasure ν := fun _ => inferInstance
  have hH := P1Ranking.harmonicK_pos (arms_pos hK)
  have hgapr := P1StochasticModel.gap_pos hK ν hUnique r
  have hQ := P1Schedule.continuation_pos s r t ht
  have hx : 0 ≤ (t : ℝ) * P1StochasticModel.gap hK ν r / 8 := by positivity
  have hv : 0 ≤ P1Ranking.harmonicK K * (P1Schedule.accumulated s r +
      P1Schedule.rank r * ((t : ℝ) - (s.time r : ℝ))) := (mul_pos hH hQ).le
  have hd := ConcentrationConstants.stochastic_denominator_pos (P1Ranking.harmonicK K)
    (K : ℝ) (P1Schedule.accumulated s r + P1Schedule.rank r * ((t : ℝ) - (s.time r : ℝ)))
    (t : ℝ) (P1StochasticModel.gap hK ν r) hH (Nat.cast_nonneg K) hQ
    (Nat.cast_nonneg t) hgapr.le
  have htbound := BanditConcentration.lower_tail_on_event (P1Algorithm.policy (arms_pos hK))
    (fun _ => ν) n (fun _ _ => hbound)
    (1 / ((K : ℝ) * P1Ranking.harmonicK K)) (P1Algorithm.sampling_floor_pos (arms_pos hK))
    (P1Algorithm.policy_floor (arms_pos hK) n) h t
    ((t : ℝ) * P1StochasticModel.gap hK ν r / 8)
    (P1Ranking.harmonicK K * (P1Schedule.accumulated s r +
      P1Schedule.rank r * ((t : ℝ) - (s.time r : ℝ)))) hx hv
    (by simpa only [one_div, inv_inv] using hd)
    (earlierGood hK ν s i) (earlierGood_measurable hK ν s i)
    (Eventually.of_forall (fun z hz => variance_on_earlierGood hK ν hbound s i r h hir hgap t ht htn z hz))
  have htail : (law hK ν n).real {z | z ∈ earlierGood hK ν s i ∧
      cumulativeMartingale (P1Algorithm.policy (arms_pos hK)) (fun _ => ν) n h t z ≤
        -((t : ℝ) * P1StochasticModel.gap hK ν r / 8)} ≤
      Real.exp (-((t : ℝ) * P1StochasticModel.gap hK ν r / 8) ^ 2 /
        (2 * (P1Ranking.harmonicK K * (P1Schedule.accumulated s r +
          P1Schedule.rank r * ((t : ℝ) - (s.time r : ℝ))) +
          ((K : ℝ) * P1Ranking.harmonicK K) * ((t : ℝ) * P1StochasticModel.gap hK ν r / 8) / 3))) := by
    simpa only [law, one_div, inv_inv] using htbound
  exact htail.trans (Real.exp_le_exp.mpr (exponent_le hK ν hUnique s r t ht))

/-- A concrete comparison error, intersected with the earlier good rankings. -/
def comparisonOnGood {n : ℕ} (s : P1Schedule.Schedule hK n) (i j k : Fin K) (t : ℕ) :
    Set (Trajectory K n) := {z | z ∈ earlierGood hK ν s i ∧
      P1Algorithm.estimatedScore (arms_pos hK) n t z k ≤
        P1Algorithm.estimatedScore (arms_pos hK) n t z (P1StochasticModel.meanOrder ν j)}

omit [IsProbabilityMeasure ν] in
theorem comparisonOnGood_measurable {n : ℕ} (s : P1Schedule.Schedule hK n)
    (i j k : Fin K) (t : ℕ) : MeasurableSet (comparisonOnGood hK ν s i j k t) := by
  exact (earlierGood_measurable hK ν s i).inter (measurableSet_le
    ((P1Algorithm.estimatedScore_stronglyMeasurable (arms_pos hK) n t k).mono
      ((historyFiltration n).le t)).measurable
    ((P1Algorithm.estimatedScore_stronglyMeasurable (arms_pos hK) n t
      (P1StochasticModel.meanOrder ν j)).mono ((historyFiltration n).le t)).measurable)

include hbound hUnique in
/-- Lemma errTwoArms for the fixed schedule, with the doubled-gap endpoint handled. -/
theorem comparison_bound {n : ℕ} (s : P1Schedule.Schedule hK n) (i j k : Fin K)
    (hi : 1 ≤ i.val) (hij : i ≤ j)
    (heligible : P1StochasticModel.trueGap hK ν k < P1StochasticModel.gap hK ν i / 2)
    (t : ℕ) (ht : s.time i ≤ t) (htn : t ≤ n) :
    (law hK ν n).real (comparisonOnGood hK ν s i j k t) ≤
      2 * Real.exp (-(n : ℝ) / (128 * P1Complexity.fixedComplexity (P1StochasticModel.gap hK ν) s)) := by
  let r := doubledRank hK ν j
  let badLower := {z | z ∈ earlierGood hK ν s i ∧
    cumulativeMartingale (P1Algorithm.policy (arms_pos hK)) (fun _ => ν) n k t z ≤
      -((t : ℝ) * P1StochasticModel.gap hK ν i / 8)}
  let badUpper := {z | z ∈ earlierGood hK ν s i ∧
    (t : ℝ) * P1StochasticModel.gap hK ν r / 8 ≤
      cumulativeMartingale (P1Algorithm.policy (arms_pos hK)) (fun _ => ν) n
        (P1StochasticModel.meanOrder ν j) t z}
  have hbetter : ∀ p : Fin K, i < p → P1StochasticModel.trueGap hK ν k <
      P1StochasticModel.gap hK ν p / 2 := by
    intro p hip
    exact heligible.trans_le (div_le_div_of_nonneg_right (P1StochasticModel.gap_monotone hK ν hip.le) (by norm_num))
  have hworse : ∀ p : Fin K, r < p →
      P1StochasticModel.trueGap hK ν (P1StochasticModel.meanOrder ν j) < P1StochasticModel.gap hK ν p / 2 := by
    intro p hrp
    rw [P1StochasticModel.trueGap_at_rank hK ν j (hi.trans hij)]
    exact gap_lt_half_later hK ν j p hrp
  have hir : i ≤ r := hij.trans (le_doubledRank hK ν j)
  have htr : s.time r ≤ t := (s.antitone hir).trans ht
  have hsub : comparisonOnGood hK ν s i j k t ⊆ badLower ∪ badUpper := by
    intro z hz
    by_cases hlow : cumulativeMartingale (P1Algorithm.policy (arms_pos hK)) (fun _ => ν) n k t z ≤
        -((t : ℝ) * P1StochasticModel.gap hK ν i / 8)
    · exact Or.inl ⟨hz.1, hlow⟩
    · apply Or.inr
      refine ⟨hz.1, ?_⟩
      have hmk := BanditSpecializations.stochastic_cumulative_identity
        (P1Algorithm.policy (arms_pos hK)) ν n k t htn z
      have hmj := BanditSpecializations.stochastic_cumulative_identity
        (P1Algorithm.policy (arms_pos hK)) ν n (P1StochasticModel.meanOrder ν j) t htn z
      have htpos : (0 : ℝ) < t := Nat.cast_pos.mpr ((s.positive i).trans_le ht)
      have hmargin := mul_lt_mul_of_pos_left
        (P1StochasticModel.comparison_margin hK ν hUnique i j k hi hij heligible) htpos
      have hmono := mul_le_mul_of_nonneg_left (P1StochasticModel.gap_monotone hK ν hij) htpos.le
      have hdoubled := mul_le_mul_of_nonneg_left (gap_doubledRank_le hK ν j) htpos.le
      have hnonneg := mul_nonneg htpos.le (P1StochasticModel.gap_pos hK ν hUnique j).le
      change cumulativeMartingale (P1Algorithm.policy (arms_pos hK)) (fun _ => ν) n k t z =
        P1Algorithm.estimatedScore (arms_pos hK) n t z k - (t : ℝ) * StochasticImportanceWeighting.mean ν k at hmk
      change cumulativeMartingale (P1Algorithm.policy (arms_pos hK)) (fun _ => ν) n
        (P1StochasticModel.meanOrder ν j) t z =
        P1Algorithm.estimatedScore (arms_pos hK) n t z (P1StochasticModel.meanOrder ν j) -
        (t : ℝ) * StochasticImportanceWeighting.mean ν (P1StochasticModel.meanOrder ν j) at hmj
      dsimp [r] at *
      nlinarith [hz.2]
  have hl := lower_on_earlierGood hK ν hbound hUnique s i i k le_rfl hbetter t ht htn
  have hu := upper_on_earlierGood hK ν hbound hUnique s i r
    (P1StochasticModel.meanOrder ν j) hir hworse t htr htn
  calc
    _ ≤ (law hK ν n).real (badLower ∪ badUpper) := measureReal_mono hsub
    _ ≤ (law hK ν n).real badLower + (law hK ν n).real badUpper := measureReal_union_le _ _
    _ ≤ _ := add_le_add hl hu
    _ = _ := by ring

/-- Invalid rank/arm/time tuples contribute empty events rather than extra counts. -/
noncomputable def comparisonBad {n : ℕ} (s : P1Schedule.Schedule hK n)
    (i j k : Fin K) (τ : Fin n) : Set (Trajectory K n) := by
  classical
  exact if 1 ≤ i.val ∧ i ≤ j ∧
      P1StochasticModel.trueGap hK ν k < P1StochasticModel.gap hK ν i / 2 ∧ s.time i ≤ τ.val + 1
    then comparisonOnGood hK ν s i j k (τ.val + 1) else ∅

omit [IsProbabilityMeasure ν] in
theorem comparisonBad_measurable {n : ℕ} (s : P1Schedule.Schedule hK n)
    (i j k : Fin K) (τ : Fin n) : MeasurableSet (comparisonBad hK ν s i j k τ) := by
  classical
  unfold comparisonBad
  split_ifs
  · exact comparisonOnGood_measurable hK ν s i j k _
  · exact MeasurableSet.empty

include hUnique in
omit [IsProbabilityMeasure ν] in
/-- The actual error is covered by rank/arm/time comparison errors under earlier good events. -/
theorem error_subset_comparisons {n : ℕ} (s : P1Schedule.Schedule hK n) :
    errorEvent hK ν n ⊆ ⋃ a : Fin K × Fin K × Fin K × Fin n,
      comparisonBad hK ν s a.1 a.2.1 a.2.2.1 a.2.2.2 := by
  classical
  intro z hz
  obtain ⟨i, hi, hfail, hgood⟩ := error_has_largest_failure hK ν hUnique s z hz
  obtain ⟨t, ht, j, k, hij, heligible, hscore⟩ := failure_witness hK ν hUnique s i hi z hfail
  have htpos : 0 < t.val := (s.positive i).trans_le ht
  let τ : Fin n := ⟨t.val - 1, by have := t.isLt; omega⟩
  have hτ : τ.val + 1 = t.val := by dsimp [τ]; omega
  apply Set.mem_iUnion.mpr
  refine ⟨(i, j, k, τ), ?_⟩
  change z ∈ comparisonBad hK ν s i j k τ
  rw [comparisonBad, ite_eq_left ⟨hi, hij, heligible, by rw [hτ]; exact ht⟩]
  exact ⟨hgood, by rw [hτ]; exact hscore⟩

include hbound hUnique in
theorem comparisonBad_bound {n : ℕ} (s : P1Schedule.Schedule hK n)
    (i j k : Fin K) (τ : Fin n) :
    (law hK ν n).real (comparisonBad hK ν s i j k τ) ≤
      2 * Real.exp (-(n : ℝ) / (128 * P1Complexity.fixedComplexity (P1StochasticModel.gap hK ν) s)) := by
  classical
  by_cases hc : 1 ≤ i.val ∧ i ≤ j ∧
      P1StochasticModel.trueGap hK ν k < P1StochasticModel.gap hK ν i / 2 ∧ s.time i ≤ τ.val + 1
  · rw [comparisonBad, ite_eq_left hc]
    exact comparison_bound hK ν hbound hUnique s i j k hc.1 hc.2.1 hc.2.2.1
      (τ.val + 1) hc.2.2.2 (Nat.succ_le_of_lt τ.isLt)
  · rw [comparisonBad, ite_eq_right hc]
    simp only [measureReal_empty]
    positivity

include hbound hUnique in
/-- The fixed schedule is optimized only after the actual error event has been bounded. -/
theorem error_bound_fixed {n : ℕ} (s : P1Schedule.Schedule hK n) :
    errorProbability hK ν n ≤ 2 * (K : ℝ) ^ 3 * (n : ℝ) *
      Real.exp (-(n : ℝ) / (128 * P1Complexity.fixedComplexity (P1StochasticModel.gap hK ν) s)) := by
  unfold errorProbability
  calc
    _ ≤ (law hK ν n).real (⋃ a : Fin K × Fin K × Fin K × Fin n,
        comparisonBad hK ν s a.1 a.2.1 a.2.2.1 a.2.2.2) :=
      measureReal_mono (error_subset_comparisons hK ν hUnique s)
    _ ≤ ∑ a : Fin K × Fin K × Fin K × Fin n,
        (law hK ν n).real (comparisonBad hK ν s a.1 a.2.1 a.2.2.1 a.2.2.2) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _a : Fin K × Fin K × Fin K × Fin n,
        2 * Real.exp (-(n : ℝ) / (128 * P1Complexity.fixedComplexity (P1StochasticModel.gap hK ν) s)) :=
      Finset.sum_le_sum (fun a _ => comparisonBad_bound hK ν hbound hUnique s a.1 a.2.1 a.2.2.1 a.2.2.2)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_mul]
      ring

include hbound hUnique in
/-- Theorem 6, stochastic guarantee for the actual P1 policy and recommendation. -/
theorem p1_stochastic_error_bound (n : ℕ) (hn : 0 < n) :
    errorProbability hK ν n ≤ 2 * (K : ℝ) ^ 3 * (n : ℝ) *
      Real.exp (-(n : ℝ) / (128 * P1Complexity.optimizedComplexity hK
        (P1StochasticModel.gap hK ν) n hn)) := by
  obtain ⟨s, hs⟩ := P1Complexity.exists_minimizer hK (P1StochasticModel.gap hK ν) n hn
  have hb := error_bound_fixed hK ν hbound hUnique s
  rw [← hs] at hb
  exact hb

end Stochastic

end BestOfBothWorlds.P1StochasticBound
