module

public import BestOfBothWorlds.P1Algorithm
public import BestOfBothWorlds.P1StochasticModel
public import BestOfBothWorlds.P1Schedule
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Tactic.Linarith
public import Lean.Elab.Tactic.Omega

/-!
The repaired P1 stochastic events. Good rankings may involve observations
after a comparison time. Their deterministic consequences bound the actual
predictable variance on those events; no probability law is conditioned on them.
Positions are zero-based and scores at time t use exactly t observed rewards.
-/

@[expose] public section

open MeasureTheory
open BestOfBothWorlds.AdaptiveBanditProcess
open BestOfBothWorlds.AdaptiveBanditMoments
open BestOfBothWorlds.BanditMartingales

namespace BestOfBothWorlds.P1StochasticEvents

variable {K : ℕ}

theorem arms_pos (hK : 2 ≤ K) : 0 < K := lt_of_lt_of_le (by decide : 0 < 2) hK

/-- Actual stationary stochastic law of the same P1 policy used against fixed tables. -/
noncomputable def law (hK : 2 ≤ K) (ν : Measure (Fin K → ℝ)) (n : ℕ) :
    Measure (Trajectory K n) := trajectoryLaw (P1Algorithm.policy (arms_pos hK)) (fun _ => ν) n

instance law_isProbabilityMeasure (hK : 2 ≤ K) (ν : Measure (Fin K → ℝ))
    [IsProbabilityMeasure ν] (n : ℕ) : IsProbabilityMeasure (law hK ν n) := by
  let : ∀ _s : ℕ, IsProbabilityMeasure ν := fun _ => inferInstance
  exact trajectoryLaw_isProbabilityMeasure (P1Algorithm.policy (arms_pos hK)) (fun _ => ν) n

/-- The actual stochastic identification error, with the best arm defined by actual means. -/
def errorEvent (hK : 2 ≤ K) (ν : Measure (Fin K → ℝ)) (n : ℕ) : Set (Trajectory K n) :=
  {z | P1Algorithm.recommendation (arms_pos hK) n z ≠ P1StochasticModel.best hK ν}

theorem errorEvent_measurable (hK : 2 ≤ K) (ν : Measure (Fin K → ℝ)) (n : ℕ) :
    MeasurableSet (errorEvent hK ν n) :=
  (measurableSet_eq_fun (P1Algorithm.recommendation_measurable (arms_pos hK) n)
    measurable_const).compl

noncomputable def errorProbability (hK : 2 ≤ K) (ν : Measure (Fin K → ℝ)) (n : ℕ) : ℝ :=
  (law hK ν n).real (errorEvent hK ν n)

/-- `Q_i` in the manuscript, including the unplayed terminal ranking through time n. -/
def goodRanking (hK : 2 ≤ K) (ν : Measure (Fin K → ℝ)) {n : ℕ}
    (s : P1Schedule.Schedule hK n) (i : Fin K) : Set (Trajectory K n) :=
  {z | ∀ t : Fin (n + 1), s.time i ≤ t.val → ∀ k : Fin K,
    P1StochasticModel.trueGap hK ν k < P1StochasticModel.gap hK ν i / 2 →
      (P1Algorithm.positionAt (arms_pos hK) n t.val z k).val < i.val}

/-- The larger-index good rankings needed for the phase-i comparison. -/
def earlierGood (hK : 2 ≤ K) (ν : Measure (Fin K → ℝ)) {n : ℕ}
    (s : P1Schedule.Schedule hK n) (i : Fin K) : Set (Trajectory K n) :=
  {z | ∀ p : Fin K, i < p → z ∈ goodRanking hK ν s p}

theorem goodRanking_measurable (hK : 2 ≤ K) (ν : Measure (Fin K → ℝ)) {n : ℕ}
    (s : P1Schedule.Schedule hK n) (i : Fin K) : MeasurableSet (goodRanking hK ν s i) := by
  simp only [goodRanking, Set.ofPred_forall]
  refine MeasurableSet.iInter (fun t => MeasurableSet.iInter (fun _ =>
    MeasurableSet.iInter (fun k => MeasurableSet.iInter (fun _ => ?_))))
  have hp := (P1Algorithm.positionAt_observable (arms_pos hK) n t.val k).mono
    ((historyFiltration n).le t.val) le_rfl
  exact measurableSet_lt ((measurable_of_finite (fun p : Fin K => p.val)).comp hp) measurable_const

theorem earlierGood_measurable (hK : 2 ≤ K) (ν : Measure (Fin K → ℝ)) {n : ℕ}
    (s : P1Schedule.Schedule hK n) (i : Fin K) : MeasurableSet (earlierGood hK ν s i) := by
  simp only [earlierGood, Set.ofPred_forall]
  exact MeasurableSet.iInter (fun p => MeasurableSet.iInter (fun _ =>
    goodRanking_measurable hK ν s p))

/-- The final rank-two event is exactly correctness of the actual recommendation. -/
theorem goodRanking_second_iff (hK : 2 ≤ K) (ν : Measure (Fin K → ℝ))
    (hUnique : P1StochasticModel.UniqueBest hK ν) {n : ℕ}
    (s : P1Schedule.Schedule hK n) (z : Trajectory K n) :
    z ∈ goodRanking hK ν s (secondRank hK) ↔
      P1Algorithm.recommendation (arms_pos hK) n z = P1StochasticModel.best hK ν := by
  constructor
  · intro hz
    have hp := hz (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) (by rw [s.second_time])
      (P1StochasticModel.best hK ν)
      ((P1StochasticModel.eligible_second_iff hK ν hUnique _).2 rfl)
    have hr : P1Algorithm.rankAt (arms_pos hK) n n z (P1StochasticModel.best hK ν) = 1 := by
      change (P1Algorithm.positionAt (arms_pos hK) n n z (P1StochasticModel.best hK ν)).val + 1 = 1
      change (P1Algorithm.positionAt (arms_pos hK) n n z (P1StochasticModel.best hK ν)).val < 1 at hp
      omega
    exact ((P1Algorithm.terminal_rank_one_iff (arms_pos hK) n z _).1 hr).symm
  · intro hz t ht k hk
    have htn : t.val = n := Nat.le_antisymm (Nat.le_of_lt_succ t.isLt)
      (by simpa only [s.second_time] using ht)
    have hkb := (P1StochasticModel.eligible_second_iff hK ν hUnique k).1 hk
    have hr := (P1Algorithm.terminal_rank_one_iff (arms_pos hK) n z k).2 (hkb.trans hz.symm)
    change (P1Algorithm.positionAt (arms_pos hK) n n z k).val + 1 = 1 at hr
    change (P1Algorithm.positionAt (arms_pos hK) n t.val z k).val < 1
    rw [htn]
    omega

/-- A failed good-ranking event produces a concrete arm/rank/time comparison witness. -/
theorem failure_witness (hK : 2 ≤ K) (ν : Measure (Fin K → ℝ))
    (hUnique : P1StochasticModel.UniqueBest hK ν) {n : ℕ}
    (s : P1Schedule.Schedule hK n) (i : Fin K) (hi : 1 ≤ i.val)
    (z : Trajectory K n) (hz : z ∉ goodRanking hK ν s i) :
    ∃ t : Fin (n + 1), s.time i ≤ t.val ∧ ∃ j k : Fin K,
      i ≤ j ∧ P1StochasticModel.trueGap hK ν k < P1StochasticModel.gap hK ν i / 2 ∧
      P1Algorithm.estimatedScore (arms_pos hK) n t.val z k ≤
        P1Algorithm.estimatedScore (arms_pos hK) n t.val z (P1StochasticModel.meanOrder ν j) := by
  classical
  change ¬∀ t : Fin (n + 1), s.time i ≤ t.val → ∀ k : Fin K,
    P1StochasticModel.trueGap hK ν k < P1StochasticModel.gap hK ν i / 2 →
      (P1Algorithm.positionAt (arms_pos hK) n t.val z k).val < i.val at hz
  push Not at hz
  obtain ⟨t, ht, k, hk, hr⟩ := hz
  have htrue := P1StochasticModel.eligible_truePosition_lt hK ν hUnique i k hi hk
  obtain ⟨j, hj, _, hscore⟩ := P1Ranking.exists_outside_prefix_precedes
    (P1Algorithm.estimatedScore (arms_pos hK) n t.val z) (P1StochasticModel.meanOrder ν)
    i.val k htrue hr
  refine ⟨t, ht, P1StochasticModel.truePosition ν j, k, hj, hk, ?_⟩
  simpa only [P1StochasticModel.order_truePosition] using hscore

/-- Select the largest failed index, so every larger-index ranking event holds. -/
theorem error_has_largest_failure (hK : 2 ≤ K) (ν : Measure (Fin K → ℝ))
    (hUnique : P1StochasticModel.UniqueBest hK ν) {n : ℕ}
    (s : P1Schedule.Schedule hK n) (z : Trajectory K n) (hz : z ∈ errorEvent hK ν n) :
    ∃ i : Fin K, 1 ≤ i.val ∧ z ∉ goodRanking hK ν s i ∧ z ∈ earlierGood hK ν s i := by
  classical
  let failed := Finset.univ.filter (fun i : Fin K => 1 ≤ i.val ∧ z ∉ goodRanking hK ν s i)
  have hsecond : z ∉ goodRanking hK ν s (secondRank hK) := by
    intro hgood
    exact hz ((goodRanking_second_iff hK ν hUnique s z).1 hgood)
  have hnonempty : failed.Nonempty :=
    ⟨secondRank hK, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by exact ⟨le_rfl, hsecond⟩⟩⟩
  let i := failed.max' hnonempty
  have hi := (Finset.mem_filter.mp (failed.max'_mem hnonempty)).2
  refine ⟨i, hi.1, hi.2, ?_⟩
  intro p hip
  by_contra hp
  have hpmem : p ∈ failed := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, le_trans hi.1 (Nat.le_of_lt hip), hp⟩
  exact (not_lt_of_ge (Finset.le_max' failed p hpmem)) hip

/-- The rank allowance follows from all later good rankings, including empty blocks. -/
theorem position_le_envelope {hK : 2 ≤ K} {n : ℕ} (s : P1Schedule.Schedule hK n)
    (r m : Fin K) (q : ℕ)
    (hgood : ∀ p : Fin K, r < p → s.time p ≤ q → m < p) :
    (((m.val + 1 : ℕ) : ℝ)) ≤ P1Schedule.envelope s r q := by
  classical
  by_cases hmr : m ≤ r
  · have hsum : 0 ≤ ∑ j ∈ P1Schedule.later r, if q < s.time j then (1 : ℝ) else 0 :=
      Finset.sum_nonneg (fun j _ => by split_ifs <;> norm_num)
    exact (Nat.cast_le.mpr (Nat.succ_le_succ hmr)).trans (le_add_of_nonneg_right hsum)
  · have hrm : r ≤ m := (lt_of_not_ge hmr).le
    have hactive : ∀ p ∈ Finset.Ioc r m, q < s.time p := by
      intro p hp
      have hp' := Finset.mem_Ioc.mp hp
      by_contra hnot
      exact (not_lt_of_ge hp'.2) (hgood p hp'.1 (Nat.le_of_not_gt hnot))
    have hsum : (((m.val - r.val : ℕ) : ℝ)) ≤
        ∑ j ∈ P1Schedule.later r, if q < s.time j then (1 : ℝ) else 0 := by
      calc
        _ = ∑ _p ∈ Finset.Ioc r m, (1 : ℝ) := by simp only [Finset.sum_const, nsmul_one, Fin.card_Ioc]
        _ = ∑ p ∈ Finset.Ioc r m, if q < s.time p then (1 : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [ite_eq_left (hactive p hp)]
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
          (fun p hp => (P1Schedule.mem_later r p).2 (Finset.mem_Ioc.mp hp).1)
          (fun _ _ _ => by split_ifs <;> norm_num)
    have heq : (((m.val + 1 : ℕ) : ℝ)) = P1Schedule.rank r + (((m.val - r.val : ℕ) : ℝ)) := by
      change (((m.val + 1 : ℕ) : ℝ)) = (((r.val + 1 : ℕ) : ℝ)) + (((m.val - r.val : ℕ) : ℝ))
      norm_cast
      omega
    rw [heq]
    exact add_le_add le_rfl hsum

/-- Earlier good rankings bound each actual sampling rank by the schedule envelope. -/
theorem rank_le_envelope (hK : 2 ≤ K) (ν : Measure (Fin K → ℝ)) {n : ℕ}
    (s : P1Schedule.Schedule hK n) (i r h : Fin K) (hir : i ≤ r)
    (hgap : ∀ p : Fin K, r < p → P1StochasticModel.trueGap hK ν h < P1StochasticModel.gap hK ν p / 2)
    (q : ℕ) (hq : q < n) (z : Trajectory K n) (hz : z ∈ earlierGood hK ν s i) :
    (P1Algorithm.rankAt (arms_pos hK) n q z h : ℝ) ≤ P1Schedule.envelope s r q := by
  apply position_le_envelope s r (P1Algorithm.positionAt (arms_pos hK) n q z h) q
  intro p hrp hpq
  have hgood := hz p (lt_of_le_of_lt hir hrp)
  exact hgood ⟨q, Nat.lt_succ_of_lt hq⟩ hpq h (hgap p hrp)

/-- The actual predictable variance is bounded on the future good-ranking event. -/
theorem variance_on_earlierGood (hK : 2 ≤ K) (ν : Measure (Fin K → ℝ))
    [IsProbabilityMeasure ν] (hbound : ∀ᵐ y ∂ν, ∀ k, 0 ≤ y k ∧ y k ≤ 1) {n : ℕ}
    (s : P1Schedule.Schedule hK n) (i r h : Fin K) (hir : i ≤ r)
    (hgap : ∀ p : Fin K, r < p → P1StochasticModel.trueGap hK ν h < P1StochasticModel.gap hK ν p / 2)
    (t : ℕ) (ht : s.time r ≤ t) (htn : t ≤ n) (z : Trajectory K n)
    (hz : z ∈ earlierGood hK ν s i) :
    predictableVariance (P1Algorithm.policy (arms_pos hK)) (fun _ => ν) n h t z ≤
      P1Ranking.harmonicK K * (P1Schedule.accumulated s r +
        P1Schedule.rank r * ((t : ℝ) - (s.time r : ℝ))) := by
  let : ∀ _s : ℕ, IsProbabilityMeasure ν := fun _ => inferInstance
  calc
    _ ≤ partialSum (reciprocalProbability (P1Algorithm.policy (arms_pos hK)) n h) t z :=
      predictableVariance_le_reciprocalSum (P1Algorithm.policy (arms_pos hK)) (fun _ => ν) n
        (fun _ _ => hbound) h t z
    _ ≤ ∑ q ∈ Finset.range t, P1Schedule.envelope s r q * P1Ranking.harmonicK K := by
      unfold partialSum
      rw [Finset.sum_apply]
      apply Finset.sum_le_sum
      intro q hqt
      have hqn : q < n := lt_of_lt_of_le (Finset.mem_range.mp hqt) htn
      rw [P1Algorithm.reciprocalProbability_eq_rankAt (arms_pos hK) hqn h z]
      exact mul_le_mul_of_nonneg_right (rank_le_envelope hK ν s i r h hir hgap q hqn z hz)
        (P1Ranking.harmonicK_pos (arms_pos hK)).le
    _ = _ := by
      rw [← Finset.sum_mul, P1Schedule.sum_envelope s r t ht]
      exact mul_comm _ _

end BestOfBothWorlds.P1StochasticEvents
