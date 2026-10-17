module

public import BestOfBothWorlds.P1Complexity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Lean.Elab.Tactic.Omega

/-!
The algebraic comparison at the ideal (possibly nonintegral) analysis fractions.
These fractions never enter P1's policy. Integer rounding and schedule admissibility
are handled separately before the corollary uses this comparison.
-/

@[expose] public section

namespace BestOfBothWorlds.P1IdealComplexity

open P1Ranking P1Schedule P1Complexity

variable {K : ℕ}

/-- The linear-gap maximum already appearing inside the paper's H_BOB. -/
noncomputable def linearMaximum (hK : 2 ≤ K) (gap : Fin K → ℝ) : ℝ :=
  (Finset.univ : Finset (Fin K)).sup' ⟨firstRank hK, Finset.mem_univ _⟩
    (fun r => P1Schedule.rank r / gap r)

theorem rank_div_gap_le_linearMaximum (hK : 2 ≤ K) (gap : Fin K → ℝ) (r : Fin K) :
    P1Schedule.rank r / gap r ≤ linearMaximum hK gap := by
  unfold linearMaximum
  exact Finset.le_sup' (fun j : Fin K => P1Schedule.rank j / gap j) (Finset.mem_univ r)

theorem linearMaximum_pos (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) : 0 < linearMaximum hK gap := by
  have h := rank_div_gap_le_linearMaximum hK gap (firstRank hK)
  have hf : P1Schedule.rank (firstRank hK) = 1 := by
    simp [P1Schedule.rank, firstRank]
  rw [hf] at h
  exact (one_div_pos.mpr hpos).trans_le h

/-- The reciprocal-rank tail omits the first two harmonic terms. -/
theorem harmonic_tail_le (hK : 2 ≤ K) (r : Fin K) (hr : 1 ≤ r.val) :
    (∑ j ∈ P1Schedule.later r, 1 / P1Schedule.rank j) ≤ harmonicK K - 3 / 2 := by
  classical
  let f : Fin K → ℝ := fun j => 1 / P1Schedule.rank j
  let T := ((Finset.univ : Finset (Fin K)).erase (firstRank hK)).erase (secondRank hK)
  have hsecond : secondRank hK ≠ firstRank hK := by
    intro heq
    have hv := congrArg Fin.val heq
    simp only [secondRank, firstRank] at hv
    contradiction
  have hs : secondRank hK ∈ (Finset.univ : Finset (Fin K)).erase (firstRank hK) :=
    Finset.mem_erase.mpr ⟨hsecond, Finset.mem_univ _⟩
  have hsub : P1Schedule.later r ⊆ T := by
    intro j hj
    have hjr : r.val < j.val := (Finset.mem_filter.mp hj).2
    have hjf : j ≠ firstRank hK := by
      intro heq
      have : j.val = 0 := congrArg Fin.val heq
      omega
    have hjs : j ≠ secondRank hK := by
      intro heq
      have : j.val = 1 := congrArg Fin.val heq
      omega
    exact Finset.mem_erase.mpr ⟨hjs, Finset.mem_erase.mpr ⟨hjf, Finset.mem_univ _⟩⟩
  have hsum : (∑ j ∈ P1Schedule.later r, f j) ≤ ∑ j ∈ T, f j :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => by
      dsimp [f, P1Schedule.rank]
      positivity)
  have h1 := Finset.sum_erase_add (Finset.univ : Finset (Fin K)) f
    (Finset.mem_univ (firstRank hK))
  have h2 := Finset.sum_erase_add
    ((Finset.univ : Finset (Fin K)).erase (firstRank hK)) f hs
  have hf : f (firstRank hK) = 1 := by norm_num [f, P1Schedule.rank, firstRank]
  have hs' : f (secondRank hK) = 1 / 2 := by
    norm_num [f, P1Schedule.rank, secondRank]
  have htotal : (∑ j : Fin K, f j) = harmonicK K := rfl
  change (∑ j ∈ P1Schedule.later r, f j) ≤ _
  dsimp [T] at hsum
  linarith

/-- Each reciprocal gap is bounded by the linear maximum divided by its rank. -/
theorem reciprocal_gap_le (hK : 2 ≤ K) (gap : Fin K → ℝ) (j : Fin K) :
    1 / gap j ≤ linearMaximum hK gap / P1Schedule.rank j := by
  have hr : 0 < P1Schedule.rank j := by dsimp [P1Schedule.rank]; positivity
  apply (le_div_iff₀ hr).2
  simpa only [one_div_mul_eq_div] using rank_div_gap_le_linearMaximum hK gap j

/-- From the second rank onward the ideal weighted term saves half a harmonic unit. -/
theorem ideal_linear_term_le (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK))
    (r : Fin K) (hr : 1 ≤ r.val) :
    P1Schedule.rank r / gap r + (∑ j ∈ P1Schedule.later r, 1 / gap j) ≤
      linearMaximum hK gap * (harmonicK K - 1 / 2) := by
  have hq := linearMaximum_pos hK gap hpos
  calc
    _ ≤ linearMaximum hK gap +
        ∑ j ∈ P1Schedule.later r, linearMaximum hK gap / P1Schedule.rank j :=
      add_le_add (rank_div_gap_le_linearMaximum hK gap r)
        (Finset.sum_le_sum (fun j _ => reciprocal_gap_le hK gap j))
    _ = linearMaximum hK gap *
        (1 + ∑ j ∈ P1Schedule.later r, 1 / P1Schedule.rank j) := by
      rw [mul_add, Finset.mul_sum]
      simp only [mul_one_div]
      ring
    _ ≤ linearMaximum hK gap * (harmonicK K - 1 / 2) := by
      apply mul_le_mul_of_nonneg_left _ hq.le
      have ht := harmonic_tail_le hK r hr
      linarith

/-- The final rank term implies Q>=K when all gaps are at most one. -/
theorem arms_le_linearMaximum (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    (hcap : ∀ r, gap r ≤ 1) : (K : ℝ) ≤ linearMaximum hK gap := by
  have hg := gap_pos_of_sorted hK gap hpos hsorted (lastRank hK)
  have hq := rank_div_gap_le_linearMaximum hK gap (lastRank hK)
  have hr : P1Schedule.rank (lastRank hK) = (K : ℝ) := by
    simp only [P1Schedule.rank, lastRank_rank]
  rw [hr] at hq
  apply le_trans _ hq
  apply (le_div_iff₀ hg).2
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (hcap (lastRank hK)) (Nat.cast_nonneg K)

/-- Ideal fractions give a common denominator, the squared smallest gap. -/
theorem ideal_profileCost_eq (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap) (r : Fin K) :
    profileCost gap (idealFractions hK gap) r =
      (P1Schedule.rank r / gap r + (∑ j ∈ P1Schedule.later r, 1 / gap j) +
        (K : ℝ) / 24) / gap (firstRank hK) := by
  let d := gap (firstRank hK)
  have hg : gap r ≠ 0 := (gap_pos_of_sorted hK gap hpos hsorted r).ne'
  have ha : idealFractions hK gap r * gap r = d := div_mul_cancel₀ _ hg
  have hw : algebraicAccumulated (idealFractions hK gap) r =
      d * (P1Schedule.rank r / gap r + ∑ j ∈ P1Schedule.later r, 1 / gap j) := by
    unfold algebraicAccumulated
    rw [mul_add, Finset.mul_sum]
    apply congrArg₂ (· + ·)
    · dsimp [idealFractions, d]
      ring
    · apply Finset.sum_congr rfl
      intro j _
      dsimp [idealFractions, d]
      ring
  have hd : (idealFractions hK gap r) ^ 2 * gap r ^ 2 = d ^ 2 := by
    rw [← mul_pow, ha]
  rw [profileCost, hw, hd]
  have hn : ((K : ℝ) / 24) * idealFractions hK gap r * gap r = ((K : ℝ) / 24) * d := by
    rw [mul_assoc, ha]
  rw [hn]
  dsimp [d]
  field_simp [hpos.ne']

/-- Duplicated first fractions make the first two telescoped numerators equal. -/
theorem accumulated_first_eq_second (hK : 2 ≤ K) (b : Fin K → ℝ)
    (hb : b (firstRank hK) = b (secondRank hK)) :
    algebraicAccumulated b (firstRank hK) = algebraicAccumulated b (secondRank hK) := by
  classical
  have hl : P1Schedule.later (firstRank hK) =
      insert (secondRank hK) (P1Schedule.later (secondRank hK)) := by
    ext j
    simp only [P1Schedule.later, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    change 0 < j.val ↔ j = secondRank hK ∨ 1 < j.val
    constructor
    · intro hj
      by_cases heq : j.val = 1
      · exact Or.inl (Fin.ext heq)
      · exact Or.inr (by omega)
    · rintro (hj | hj)
      · subst j
        change 0 < 1
        decide
      · omega
  have hn : secondRank hK ∉ P1Schedule.later (secondRank hK) := by
    simp [P1Schedule.later]
  rw [algebraicAccumulated, algebraicAccumulated, hl, Finset.sum_insert hn, hb]
  norm_num [P1Schedule.rank, firstRank, secondRank]
  ring

/-- Duplicating the minimum gap makes the first two complete ideal costs equal. -/
theorem ideal_profileCost_first (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hduplicate : gap (firstRank hK) = gap (secondRank hK)) :
    profileCost gap (idealFractions hK gap) (firstRank hK) =
      profileCost gap (idealFractions hK gap) (secondRank hK) := by
  have hb : idealFractions hK gap (firstRank hK) = idealFractions hK gap (secondRank hK) := by
    simp only [idealFractions, hduplicate]
  unfold profileCost
  rw [accumulated_first_eq_second hK _ hb, hb, hduplicate]

/-- Each ideal cost is at most H_BOB times the harmonic normalizer. -/
theorem ideal_profileCost_le (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    (hduplicate : gap (firstRank hK) = gap (secondRank hK))
    (hcap : ∀ r, gap r ≤ 1) (r : Fin K) :
    profileCost gap (idealFractions hK gap) r ≤ H_BOB hK gap * harmonicK K := by
  have hrow (q : Fin K) (hq : 1 ≤ q.val) :
      profileCost gap (idealFractions hK gap) q ≤ H_BOB hK gap * harmonicK K := by
    rw [ideal_profileCost_eq hK gap hpos hsorted]
    have ht := ideal_linear_term_le hK gap hpos q hq
    have hk := arms_le_linearMaximum hK gap hpos hsorted hcap
    have hbob := (gap_complexities_pos hK gap hpos).2.1
    calc
      _ ≤ (linearMaximum hK gap * (harmonicK K - 1 / 2) +
          linearMaximum hK gap / 24) / gap (firstRank hK) := by
        apply div_le_div_of_nonneg_right _ hpos.le
        exact add_le_add ht (div_le_div_of_nonneg_right hk (by norm_num))
      _ = H_BOB hK gap * (harmonicK K - 1 / 2 + 1 / 24) := by
        unfold H_BOB linearMaximum
        simp only [P1Schedule.rank]
        ring
      _ ≤ H_BOB hK gap * harmonicK K := by
        apply mul_le_mul_of_nonneg_left _ hbob.le
        linarith
  by_cases hr : r = firstRank hK
  · rw [hr, ideal_profileCost_first hK gap hduplicate]
    exact hrow (secondRank hK) (by rfl)
  · apply hrow r
    have hr0 : r.val ≠ 0 := by
      intro heq
      exact hr (Fin.ext heq)
    omega

/-- The ideal algebraic comparison used before rounding the analysis schedule. -/
theorem ideal_profileComplexity_le (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    (hduplicate : gap (firstRank hK) = gap (secondRank hK))
    (hcap : ∀ r, gap r ≤ 1) :
    profileComplexity hK gap (idealFractions hK gap) ≤
      H_BOB hK gap * (harmonicK K) ^ 2 := by
  unfold profileComplexity
  calc
    _ ≤ harmonicK K * (H_BOB hK gap * harmonicK K) := by
      apply mul_le_mul_of_nonneg_left _ (harmonicK_pos (by omega : 0 < K)).le
      apply Finset.sup'_le
      intro r _
      exact ideal_profileCost_le hK gap hpos hsorted hduplicate hcap r
    _ = _ := by ring

end BestOfBothWorlds.P1IdealComplexity
