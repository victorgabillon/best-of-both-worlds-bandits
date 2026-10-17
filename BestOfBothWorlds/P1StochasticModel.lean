module

public import BestOfBothWorlds.P1Ranking
public import BestOfBothWorlds.GapComplexity
public import BestOfBothWorlds.StochasticImportanceWeighting
public import Mathlib.Tactic.Linarith
public import Lean.Elab.Tactic.Omega

/-!
The actual stationary reward means and their analysis ordering for P1.
Sorting these unknown means is used only in the proof; the learner's policy
does not receive the reward law, means, true order, or gaps as inputs.
-/

@[expose] public section

open MeasureTheory

namespace BestOfBothWorlds.P1StochasticModel

variable {K : ℕ}

/-- The true decreasing mean order, solely an analysis permutation. -/
noncomputable def meanOrder (ν : Measure (Fin K → ℝ)) : Equiv.Perm (Fin K) :=
  P1Ranking.order (StochasticImportanceWeighting.mean ν)

/-- Position in the true mean order, starting at zero. -/
noncomputable def truePosition (ν : Measure (Fin K → ℝ)) (k : Fin K) : Fin K :=
  (meanOrder ν).symm k

/-- The best arm is chosen from its actual mean, without fixing an arm label. -/
noncomputable def best (hK : 2 ≤ K) (ν : Measure (Fin K → ℝ)) : Fin K :=
  meanOrder ν (firstRank hK)

/-- The stochastic problem's unique-best assumption, applied to its actual means. -/
def UniqueBest (hK : 2 ≤ K) (ν : Measure (Fin K → ℝ)) : Prop :=
  ∀ k, k ≠ best hK ν → StochasticImportanceWeighting.mean ν k <
    StochasticImportanceWeighting.mean ν (best hK ν)

/-- A mean difference before duplicating the best arm's smallest positive gap. -/
noncomputable def trueGap (hK : 2 ≤ K) (ν : Measure (Fin K → ℝ)) (k : Fin K) : ℝ :=
  StochasticImportanceWeighting.mean ν (best hK ν) - StochasticImportanceWeighting.mean ν k

/-- The sorted paper gap profile, with the first two entries equal. -/
noncomputable def gap (hK : 2 ≤ K) (ν : Measure (Fin K → ℝ)) (r : Fin K) : ℝ :=
  trueGap hK ν (meanOrder ν (if r = firstRank hK then secondRank hK else r))

theorem second_ne_first (hK : 2 ≤ K) : secondRank hK ≠ firstRank hK := by
  intro heq
  have hv := congrArg Fin.val heq
  simp only [secondRank, firstRank] at hv
  contradiction

@[simp] theorem truePosition_order (ν : Measure (Fin K → ℝ)) (r : Fin K) :
    truePosition ν (meanOrder ν r) = r := (meanOrder ν).symm_apply_apply r

@[simp] theorem order_truePosition (ν : Measure (Fin K → ℝ)) (k : Fin K) :
    meanOrder ν (truePosition ν k) = k := (meanOrder ν).apply_symm_apply k

theorem meanOrder_antitone (ν : Measure (Fin K → ℝ)) :
    Antitone (fun r => StochasticImportanceWeighting.mean ν (meanOrder ν r)) :=
  P1Ranking.score_order_antitone (StochasticImportanceWeighting.mean ν)

theorem mean_le_best (hK : 2 ≤ K) (ν : Measure (Fin K → ℝ)) (k : Fin K) :
    StochasticImportanceWeighting.mean ν k ≤ StochasticImportanceWeighting.mean ν (best hK ν) := by
  have hm := meanOrder_antitone ν (show firstRank hK ≤ truePosition ν k from Nat.zero_le _)
  simpa only [order_truePosition, best] using hm

theorem trueGap_nonneg (hK : 2 ≤ K) (ν : Measure (Fin K → ℝ)) (k : Fin K) :
    0 ≤ trueGap hK ν k := sub_nonneg.mpr (mean_le_best hK ν k)

@[simp] theorem trueGap_best (hK : 2 ≤ K) (ν : Measure (Fin K → ℝ)) :
    trueGap hK ν (best hK ν) = 0 := sub_self _

theorem gap_eq_of_ne_first (hK : 2 ≤ K) (ν : Measure (Fin K → ℝ)) (r : Fin K)
    (hr : r ≠ firstRank hK) : gap hK ν r = trueGap hK ν (meanOrder ν r) := by
  simp only [gap, ite_eq_right hr]

@[simp] theorem gap_first (hK : 2 ≤ K) (ν : Measure (Fin K → ℝ)) :
    gap hK ν (firstRank hK) = trueGap hK ν (meanOrder ν (secondRank hK)) := by
  simp [gap]

theorem gap_duplicate (hK : 2 ≤ K) (ν : Measure (Fin K → ℝ)) :
    gap hK ν (firstRank hK) = gap hK ν (secondRank hK) := by
  rw [gap_first, gap_eq_of_ne_first hK ν _ (second_ne_first hK)]

theorem gap_monotone (hK : 2 ≤ K) (ν : Measure (Fin K → ℝ)) :
    Monotone (gap hK ν) := by
  intro r s hrs
  by_cases hr : r = firstRank hK
  · subst r
    by_cases hs : s = firstRank hK
    · rw [hs]
    · rw [gap_first, gap_eq_of_ne_first hK ν s hs]
      apply sub_le_sub_left
      apply meanOrder_antitone ν
      change 1 ≤ s.val
      have hs0 : s.val ≠ 0 := by
        intro heq
        exact hs (Fin.ext heq)
      omega
  · have hs : s ≠ firstRank hK := by
      intro hs
      apply hr
      apply Fin.ext
      change r.val = 0
      have : r.val ≤ 0 := by
        change r.val ≤ s.val at hrs
        simpa only [hs, firstRank] using hrs
      omega
    rw [gap_eq_of_ne_first hK ν r hr, gap_eq_of_ne_first hK ν s hs]
    exact sub_le_sub_left (meanOrder_antitone ν hrs) _

theorem gap_pos (hK : 2 ≤ K) (ν : Measure (Fin K → ℝ))
    (hUnique : UniqueBest hK ν) (r : Fin K) : 0 < gap hK ν r := by
  let q := if r = firstRank hK then secondRank hK else r
  have hq : q ≠ firstRank hK := by
    by_cases hr : r = firstRank hK
    · simpa only [q, ite_eq_left hr] using second_ne_first hK
    · simpa only [q, ite_eq_right hr] using hr
  have hne : meanOrder ν q ≠ best hK ν := by
    intro heq
    exact hq ((meanOrder ν).injective heq)
  exact sub_pos.mpr (hUnique _ hne)

theorem gap_le_one (hK : 2 ≤ K) (ν : Measure (Fin K → ℝ)) [IsProbabilityMeasure ν]
    (hbound : ∀ᵐ y ∂ν, ∀ k, 0 ≤ y k ∧ y k ≤ 1) (r : Fin K) : gap hK ν r ≤ 1 := by
  have hb := (StochasticImportanceWeighting.mean_bounds ν hbound (best hK ν)).2
  have hr := (StochasticImportanceWeighting.mean_bounds ν hbound
    (meanOrder ν (if r = firstRank hK then secondRank hK else r))).1
  change StochasticImportanceWeighting.mean ν (best hK ν) - _ ≤ 1
  linarith

theorem trueGap_at_rank (hK : 2 ≤ K) (ν : Measure (Fin K → ℝ)) (r : Fin K)
    (hr : 1 ≤ r.val) : trueGap hK ν (meanOrder ν r) = gap hK ν r := by
  apply (gap_eq_of_ne_first hK ν r ?_).symm
  intro heq
  have : r.val = 0 := congrArg Fin.val heq
  omega

/-- Eligibility forces a true position strictly before the comparison rank. -/
theorem eligible_truePosition_lt (hK : 2 ≤ K) (ν : Measure (Fin K → ℝ))
    (hUnique : UniqueBest hK ν) (i k : Fin K) (hi : 1 ≤ i.val)
    (heligible : trueGap hK ν k < gap hK ν i / 2) : (truePosition ν k).val < i.val := by
  by_contra hnot
  have horder : i ≤ truePosition ν k := Nat.le_of_not_gt hnot
  have hmean := meanOrder_antitone ν horder
  dsimp only at hmean
  rw [order_truePosition] at hmean
  have hgap : gap hK ν i ≤ trueGap hK ν k := by
    rw [← trueGap_at_rank hK ν i hi]
    exact sub_le_sub_left hmean _
  have hpos := gap_pos hK ν hUnique i
  linarith

/-- Exactly the best arm is eligible for the final rank-two comparison. -/
theorem eligible_second_iff (hK : 2 ≤ K) (ν : Measure (Fin K → ℝ))
    (hUnique : UniqueBest hK ν) (k : Fin K) :
    trueGap hK ν k < gap hK ν (secondRank hK) / 2 ↔ k = best hK ν := by
  constructor
  · intro hk
    have hp := eligible_truePosition_lt hK ν hUnique (secondRank hK) k (by rfl) hk
    have heq : truePosition ν k = firstRank hK := by
      apply Fin.ext
      change (truePosition ν k).val = 0
      change (truePosition ν k).val < 1 at hp
      omega
    rw [← order_truePosition ν k, heq]
    rfl
  · intro hk
    rw [hk, trueGap_best]
    exact half_pos (gap_pos hK ν hUnique _)

/-- A comparison against a truly later arm has a strictly positive half-gap margin. -/
theorem comparison_margin (hK : 2 ≤ K) (ν : Measure (Fin K → ℝ))
    (_hUnique : UniqueBest hK ν) (i j k : Fin K) (hi : 1 ≤ i.val) (hij : i ≤ j)
    (heligible : trueGap hK ν k < gap hK ν i / 2) :
    gap hK ν j / 2 < StochasticImportanceWeighting.mean ν k -
      StochasticImportanceWeighting.mean ν (meanOrder ν j) := by
  have hj : 1 ≤ j.val := hi.trans hij
  have hgj := trueGap_at_rank hK ν j hj
  have hmono := gap_monotone hK ν hij
  change StochasticImportanceWeighting.mean ν (best hK ν) -
    StochasticImportanceWeighting.mean ν (meanOrder ν j) = gap hK ν j at hgj
  change StochasticImportanceWeighting.mean ν (best hK ν) -
    StochasticImportanceWeighting.mean ν k < gap hK ν i / 2 at heligible
  linarith

end BestOfBothWorlds.P1StochasticModel
