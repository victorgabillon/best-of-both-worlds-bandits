module

public import BestOfBothWorlds.P1Ranking
public import BestOfBothWorlds.BanditMartingales
public import BestOfBothWorlds.BanditSpecializations

/-!
P1 is an anytime observable learner. Its score recursion is defined on observed
histories before the policy, so each update uses the probability computed from
the preceding score without circularly referring to an already-defined policy.
The trajectory identities below identify these scores with the existing
importance-weighted estimates. The ranking at time n is the manuscript's
unplayed virtual ranking n+1, with no additional observation or action.
-/

@[expose] public section

open MeasureTheory
open BestOfBothWorlds.AdaptiveBanditProcess
open BestOfBothWorlds.AdaptiveBanditMoments
open BestOfBothWorlds.BanditMartingales

namespace BestOfBothWorlds.P1Algorithm

variable {K : ℕ}

/-- Cumulative importance-weighted scores computed solely from observed history. -/
noncomputable def score (hK : 0 < K) : {t : ℕ} → ObservedHistory K t → Fin K → ℝ
  | 0, _, _ => 0
  | _t+1, h, k => score hK h.1 k +
      if h.2.1 = k then h.2.2 / P1Ranking.probability hK (score hK h.1) k else 0

theorem score_measurable (hK : 0 < K) (t : ℕ) (k : Fin K) :
    Measurable (fun h : ObservedHistory K t => score hK h k) := by
  induction t generalizing k with
  | zero => exact measurable_const
  | succ t ih =>
      have hprior : ∀ j, Measurable (fun h : ObservedHistory K (t+1) => score hK h.1 j) :=
        fun j => (ih j).comp measurable_fst
      exact (hprior k).add (Measurable.ite
        (measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const)
        ((measurable_snd.comp measurable_snd).div
          (P1Ranking.probability_measurable hK _ hprior k)) measurable_const)

/-- P1's actual policy uses rank-dependent harmonic probabilities at every history. -/
noncomputable def policy (hK : 0 < K) : Policy K where
  prob _t h k := P1Ranking.probability hK (score hK h) k
  measurable_prob := fun t k => P1Ranking.probability_measurable hK _
    (fun j => score_measurable hK t j) k
  positive := fun _ h k => P1Ranking.probability_pos hK (score hK h) k
  normalized := fun _ h => P1Ranking.probability_normalized hK (score hK h)

@[simp] theorem policy_prob (hK : 0 < K) (t : ℕ) (h : ObservedHistory K t) (k : Fin K) :
    (policy hK).prob t h k = P1Ranking.probability hK (score hK h) k := rfl

theorem sampling_floor_pos (hK : 0 < K) :
    0 < 1 / ((K : ℝ) * P1Ranking.harmonicK K) :=
  one_div_pos.mpr (mul_pos (Nat.cast_pos.mpr hK) (P1Ranking.harmonicK_pos hK))

theorem policy_floor (hK : 0 < K) (n : ℕ) :
    ∀ t < n, ∀ h k, 1 / ((K : ℝ) * P1Ranking.harmonicK K) ≤ (policy hK).prob t h k :=
  fun _ _ h k => P1Ranking.probability_floor hK (score hK h) k

/-- The recursive observed score equals the existing estimator through each valid time. -/
theorem score_history_eq (hK : 0 < K) (n t : ℕ) (ht : t ≤ n) (z : Trajectory K n) :
    score hK (historyAt n t ht z) = fun k => cumulativeEstimate (policy hK) n k t z := by
  induction t with
  | zero =>
      funext k
      simp [score, cumulativeEstimate, partialSum]
  | succ t ih =>
      have htn : t < n := Nat.lt_of_succ_le ht
      have hpast := ih (Nat.le_of_lt htn)
      funext k
      calc
        _ = score hK (historyAt n t (Nat.le_of_lt htn) z) k +
            (if roundAction t n htn z = k then roundObservedReward t n htn z /
              (policy hK).prob t (historyAt n t (Nat.le_of_lt htn) z) k else 0) := by
          rw [congrFun (observed_history_extension htn) z]
          rfl
        _ = cumulativeEstimate (policy hK) n k t z + importanceWeighted (policy hK) n k t z := by
          rw [hpast, importanceWeighted_formula (policy hK) htn k z]
        _ = cumulativeEstimate (policy hK) n k (t+1) z := by
          simp [cumulativeEstimate, partialSum, Finset.sum_range_succ]

/-- Score array on the fixed horizon, stopped after its last observation. -/
noncomputable def estimatedScore (hK : 0 < K) (n t : ℕ) (z : Trajectory K n) (k : Fin K) : ℝ :=
  cumulativeEstimate (policy hK) n k t z

/-- Terminal cumulative estimated gain, reusing the established estimator exactly. -/
noncomputable def estimatedCumulative (hK : 0 < K) (n : ℕ) (k : Fin K) :
    Trajectory K n → ℝ := cumulativeEstimate (policy hK) n k n

noncomputable def positionAt (hK : 0 < K) (n t : ℕ) (z : Trajectory K n) (k : Fin K) : Fin K :=
  P1Ranking.position (estimatedScore hK n t z) k

/-- Rank after t observations; at t=n this is the virtual terminal ranking. -/
noncomputable def rankAt (hK : 0 < K) (n t : ℕ) (z : Trajectory K n) (k : Fin K) : ℕ :=
  P1Ranking.rank (estimatedScore hK n t z) k

theorem estimatedScore_stronglyMeasurable (hK : 0 < K) (n t : ℕ) (k : Fin K) :
    StronglyMeasurable[historyFiltration n t] (fun z => estimatedScore hK n t z k) :=
  partialSum_stronglyAdapted _ (fun s => importanceWeighted_stronglyMeasurable (policy hK) n k s) t

theorem positionAt_observable (hK : 0 < K) (n t : ℕ) (k : Fin K) :
    Measurable[historyFiltration n t] (fun z => positionAt hK n t z k) :=
  @P1Ranking.position_measurable K (Trajectory K n) (historyFiltration n t)
    (estimatedScore hK n t) (fun j => (estimatedScore_stronglyMeasurable hK n t j).measurable) k

theorem rankAt_observable (hK : 0 < K) (n t : ℕ) (k : Fin K) :
    Measurable[historyFiltration n t] (fun z => rankAt hK n t z k) :=
  (measurable_of_finite (fun i : Fin K => i.val + 1)).comp (positionAt_observable hK n t k)

theorem rankAt_pos (hK : 0 < K) (n t : ℕ) (z : Trajectory K n) (k : Fin K) :
    0 < rankAt hK n t z k := P1Ranking.rank_pos _ k

theorem rankAt_le (hK : 0 < K) (n t : ℕ) (z : Trajectory K n) (k : Fin K) :
    rankAt hK n t z k ≤ K := P1Ranking.rank_le _ k

/-- The actual current sampling probability is the reciprocal of its observed rank. -/
theorem policy_prob_rankAt (hK : 0 < K) {n t : ℕ} (ht : t < n) (k : Fin K)
    (z : Trajectory K n) :
    (policy hK).prob t (historyAt n t (Nat.le_of_lt ht) z) k =
      1 / ((rankAt hK n t z k : ℝ) * P1Ranking.harmonicK K) := by
  rw [policy_prob, score_history_eq]
  rfl

theorem reciprocalProbability_eq_rankAt (hK : 0 < K) {n t : ℕ} (ht : t < n)
    (k : Fin K) (z : Trajectory K n) :
    reciprocalProbability (policy hK) n k t z =
      (rankAt hK n t z k : ℝ) * P1Ranking.harmonicK K := by
  simp only [reciprocalProbability, dite_eq_left ht, policy_prob_rankAt hK ht k z,
    one_div, inv_inv]

/-- The actual recommendation is the smallest maximizing terminal estimated gain. -/
noncomputable def recommendation (hK : 0 < K) (n : ℕ) (z : Trajectory K n) : Fin K :=
  FiniteMaximizer.select hK (fun k => estimatedCumulative hK n k z)

theorem recommendation_max (hK : 0 < K) (n : ℕ) (z : Trajectory K n) (k : Fin K) :
    estimatedCumulative hK n k z ≤ estimatedCumulative hK n (recommendation hK n z) z :=
  FiniteMaximizer.le_select hK (fun j => estimatedCumulative hK n j z) k

theorem recommendation_observable (hK : 0 < K) (n : ℕ) :
    Measurable[historyFiltration n n] (recommendation hK n) :=
  @FiniteMaximizer.select_measurable K hK (Trajectory K n) (historyFiltration n n)
    (fun z k => estimatedCumulative hK n k z)
    (fun k => (estimatedScore_stronglyMeasurable hK n n k).measurable)

theorem recommendation_measurable (hK : 0 < K) (n : ℕ) :
    Measurable (recommendation hK n) :=
  (recommendation_observable hK n).mono ((historyFiltration n).le n) le_rfl

/-- The recursive observation score, with no final action, is the terminal score. -/
theorem score_observe_eq (hK : 0 < K) (n : ℕ) (z : Trajectory K n) :
    score hK (observe z) = fun k => estimatedCumulative hK n k z := by
  simpa [historyAt, estimatedCumulative] using score_history_eq hK n n le_rfl z

/-- The unplayed next ranking puts the actual recommendation first. -/
theorem terminal_first (hK : 0 < K) (n : ℕ) (z : Trajectory K n) :
    P1Ranking.order (estimatedScore hK n n z) ⟨0, hK⟩ = recommendation hK n z :=
  P1Ranking.order_first_eq_select hK _

theorem terminal_rank_one_iff (hK : 0 < K) (n : ℕ) (z : Trajectory K n) (k : Fin K) :
    rankAt hK n n z k = 1 ↔ k = recommendation hK n z := by
  change (P1Ranking.position (estimatedScore hK n n z) k).val + 1 = 1 ↔ _
  constructor
  · intro h
    have hp : P1Ranking.position (estimatedScore hK n n z) k = (⟨0, hK⟩ : Fin K) :=
      Fin.ext (by
        change (P1Ranking.position (estimatedScore hK n n z) k).val = 0
        omega)
    have he := congrArg (P1Ranking.order (estimatedScore hK n n z)) hp
    simpa only [P1Ranking.order_position, terminal_first] using he
  · intro hk
    rw [hk, ← terminal_first hK n z, P1Ranking.position_order]

/-- Equal observed histories give exactly the same terminal recommendation. -/
theorem recommendation_eq_of_observe_eq (hK : 0 < K) (n : ℕ)
    (z z' : Trajectory K n) (heq : observe z = observe z') :
    recommendation hK n z = recommendation hK n z' := by
  have hs : (fun k => estimatedCumulative hK n k z) =
      (fun k => estimatedCumulative hK n k z') := by
    rw [← score_observe_eq, ← score_observe_eq, heq]
  exact congrArg (FiniteMaximizer.select hK) hs

/-- The same concrete P1 policy is run on a fixed oblivious reward table. -/
noncomputable def law (hK : 0 < K) (g : ℕ → Fin K → ℝ) (n : ℕ) :
    Measure (Trajectory K n) := trajectoryLaw (policy hK) (fun t => Measure.dirac (g t)) n

instance law_isProbabilityMeasure (hK : 0 < K) (g : ℕ → Fin K → ℝ) (n : ℕ) :
    IsProbabilityMeasure (law hK g n) := by
  let : ∀ t, IsProbabilityMeasure (Measure.dirac (g t)) := fun _ => inferInstance
  exact trajectoryLaw_isProbabilityMeasure (policy hK) (fun t => Measure.dirac (g t)) n

end BestOfBothWorlds.P1Algorithm
