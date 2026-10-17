module

public import BestOfBothWorlds.P1Schedule
public import BestOfBothWorlds.P1Ranking
public import Mathlib.Tactic.FieldSimp

/-!
The manuscript's P1 complexity, first for a fixed integer schedule and then
minimized over the finite nonempty set of admissible schedules. The algebraic
fraction expression is also exposed for the corollary's rounding comparison.
-/

@[expose] public section

open BestOfBothWorlds.P1Schedule

namespace BestOfBothWorlds.P1Complexity

variable {K : ℕ}

/-- The telescoped numerator for an arbitrary real comparison-fraction vector. -/
noncomputable def algebraicAccumulated (b : Fin K → ℝ) (r : Fin K) : ℝ :=
  P1Schedule.rank r * b r + ∑ j ∈ P1Schedule.later r, b j

/-- One rank's contribution to the algebraic complexity expression Phi. -/
noncomputable def profileCost (gap b : Fin K → ℝ) (r : Fin K) : ℝ :=
  (algebraicAccumulated b r + ((K : ℝ) / 24) * b r * gap r) /
    ((b r) ^ 2 * (gap r) ^ 2)

/-- The algebraic expression Phi; real fractions here need not be admissible schedules. -/
noncomputable def profileComplexity (hK : 2 ≤ K) (gap b : Fin K → ℝ) : ℝ :=
  P1Ranking.harmonicK K *
    (Finset.univ : Finset (Fin K)).sup' ⟨firstRank hK, Finset.mem_univ _⟩ (profileCost gap b)

/-- The ideal, generally nonintegral fractions used only in the corollary's algebra. -/
noncomputable def idealFractions (hK : 2 ≤ K) (gap : Fin K → ℝ) (r : Fin K) : ℝ :=
  gap (firstRank hK) / gap r

/-- One rank's exact time-based complexity contribution. -/
noncomputable def rankCost {hK : 2 ≤ K} {n : ℕ} (gap : Fin K → ℝ)
    (s : P1Schedule.Schedule hK n) (r : Fin K) : ℝ :=
  (P1Schedule.accumulated s r + ((K : ℝ) / 24) * (s.time r : ℝ) * gap r) /
    ((s.time r : ℝ) ^ 2 * (gap r) ^ 2)

/-- H_P1 for one fixed admissible integer comparison schedule. -/
noncomputable def fixedComplexity {hK : 2 ≤ K} {n : ℕ} (gap : Fin K → ℝ)
    (s : P1Schedule.Schedule hK n) : ℝ :=
  (n : ℝ) * P1Ranking.harmonicK K *
    (Finset.univ : Finset (Fin K)).sup' ⟨firstRank hK, Finset.mem_univ _⟩ (rankCost gap s)

theorem rankCost_pos {hK : 2 ≤ K} {n : ℕ} (gap : Fin K → ℝ)
    (s : P1Schedule.Schedule hK n) (r : Fin K) (hgap : 0 < gap r) :
    0 < rankCost gap s r := by
  apply div_pos
  · exact add_pos_of_pos_of_nonneg (P1Schedule.accumulated_pos s r) (by positivity)
  · exact mul_pos (pow_pos (Nat.cast_pos.mpr (s.positive r)) 2) (pow_pos hgap 2)

theorem fixedComplexity_pos (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    {n : ℕ} (s : P1Schedule.Schedule hK n) : 0 < fixedComplexity gap s := by
  have hmax : 0 < (Finset.univ : Finset (Fin K)).sup'
      ⟨firstRank hK, Finset.mem_univ _⟩ (rankCost gap s) :=
    (rankCost_pos gap s (firstRank hK) (gap_pos_of_sorted hK gap hpos hsorted _)).trans_le
      (Finset.le_sup' _ (Finset.mem_univ _))
  exact mul_pos (mul_pos (Nat.cast_pos.mpr s.horizon_pos)
    (P1Ranking.harmonicK_pos (lt_of_lt_of_le (by decide : 0 < 2) hK))) hmax

theorem rankCost_le_fixedComplexity {hK : 2 ≤ K} {n : ℕ} (gap : Fin K → ℝ)
    (s : P1Schedule.Schedule hK n) (r : Fin K) :
    (n : ℝ) * P1Ranking.harmonicK K * rankCost gap s r ≤ fixedComplexity gap s := by
  exact mul_le_mul_of_nonneg_left (Finset.le_sup' _ (Finset.mem_univ r))
    (mul_nonneg (Nat.cast_nonneg n)
      (P1Ranking.harmonicK_pos (lt_of_lt_of_le (by decide : 0 < 2) hK)).le)

theorem schedules_nonempty (hK : 2 ≤ K) (n : ℕ) (hn : 0 < n) :
    (Finset.univ : Finset (P1Schedule.Schedule hK n)).Nonempty :=
  ⟨P1Schedule.Schedule.allOnes hK n hn, Finset.mem_univ _⟩

/-- The exact finite optimization over admissible integer schedules, for n>0. -/
noncomputable def optimizedComplexity (hK : 2 ≤ K) (gap : Fin K → ℝ) (n : ℕ) (hn : 0 < n) : ℝ :=
  (Finset.univ : Finset (P1Schedule.Schedule hK n)).inf' (schedules_nonempty hK n hn)
    (fixedComplexity gap)

theorem optimizedComplexity_le (hK : 2 ≤ K) (gap : Fin K → ℝ) (n : ℕ) (hn : 0 < n)
    (s : P1Schedule.Schedule hK n) : optimizedComplexity hK gap n hn ≤ fixedComplexity gap s :=
  Finset.inf'_le _ (Finset.mem_univ s)

theorem exists_minimizer (hK : 2 ≤ K) (gap : Fin K → ℝ) (n : ℕ) (hn : 0 < n) :
    ∃ s : P1Schedule.Schedule hK n, optimizedComplexity hK gap n hn = fixedComplexity gap s := by
  obtain ⟨s, _, hs⟩ := Finset.exists_mem_eq_inf' (schedules_nonempty hK n hn) (fixedComplexity gap)
  exact ⟨s, hs⟩

theorem optimizedComplexity_pos (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap) (n : ℕ) (hn : 0 < n) :
    0 < optimizedComplexity hK gap n hn := by
  obtain ⟨s, hs⟩ := exists_minimizer hK gap n hn
  rw [hs]
  exact fixedComplexity_pos hK gap hpos hsorted s

theorem algebraicAccumulated_fraction {hK : 2 ≤ K} {n : ℕ}
    (s : P1Schedule.Schedule hK n) (r : Fin K) :
    algebraicAccumulated (P1Schedule.fraction s) r = P1Schedule.accumulated s r / (n : ℝ) := by
  simp only [algebraicAccumulated, P1Schedule.fraction, P1Schedule.accumulated,
    add_div, mul_div_assoc, Finset.sum_div]

/-- The time expression defining fixedComplexity is exactly the manuscript's fraction expression. -/
theorem fixedComplexity_eq_profileComplexity (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    {n : ℕ} (s : P1Schedule.Schedule hK n) :
    fixedComplexity gap s = profileComplexity hK gap (P1Schedule.fraction s) := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr s.horizon_pos.ne'
  have hc (r : Fin K) : profileCost gap (P1Schedule.fraction s) r = (n : ℝ) * rankCost gap s r := by
    rw [profileCost, algebraicAccumulated_fraction]
    unfold P1Schedule.fraction rankCost
    have hg : gap r ≠ 0 := (gap_pos_of_sorted hK gap hpos hsorted r).ne'
    have ht : (s.time r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (s.positive r).ne'
    field_simp [hn, hg, ht]
  have hsup : (Finset.univ : Finset (Fin K)).sup'
      ⟨firstRank hK, Finset.mem_univ _⟩ (profileCost gap (P1Schedule.fraction s)) =
      (n : ℝ) * (Finset.univ : Finset (Fin K)).sup'
        ⟨firstRank hK, Finset.mem_univ _⟩ (rankCost gap s) := by
    calc
      _ = (Finset.univ : Finset (Fin K)).sup'
          ⟨firstRank hK, Finset.mem_univ _⟩ (fun r => (n : ℝ) * rankCost gap s r) := by
        apply Finset.sup'_congr _ rfl
        intro r _
        exact hc r
      _ = _ := (map_finset_sup' (OrderIso.mulLeft₀ (n : ℝ) (Nat.cast_pos.mpr s.horizon_pos)) _ _).symm
  unfold fixedComplexity profileComplexity
  rw [hsup]
  ring

/-- The later variance allowance grows at most linearly from a comparison time. -/
theorem varianceBudget_le_scaled {hK : 2 ≤ K} {n : ℕ}
    (s : P1Schedule.Schedule hK n) (r : Fin K) (t : ℕ) (ht : s.time r ≤ t) (delta : ℝ) :
    P1Schedule.accumulated s r + P1Schedule.rank r * ((t : ℝ) - (s.time r : ℝ)) +
        ((K : ℝ) / 24) * (t : ℝ) * delta ≤
      ((t : ℝ) / (s.time r : ℝ)) *
        (P1Schedule.accumulated s r + ((K : ℝ) / 24) * (s.time r : ℝ) * delta) := by
  have hm : (0 : ℝ) < s.time r := Nat.cast_pos.mpr (s.positive r)
  have htime : (s.time r : ℝ) ≤ t := Nat.cast_le.mpr ht
  have hprod := mul_nonneg (sub_nonneg.mpr htime)
    (sub_nonneg.mpr (P1Schedule.accumulated_ge_rank_time s r))
  conv_rhs => rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hm).2
  nlinarith only [hprod]

/-- A fixed schedule's complexity controls the comparison-time exponent at every rank. -/
theorem comparison_time_exponent (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    {n : ℕ} (s : P1Schedule.Schedule hK n) (r : Fin K) :
    (n : ℝ) / (128 * fixedComplexity gap s) ≤
      ((s.time r : ℝ) * gap r) ^ 2 /
        (128 * P1Ranking.harmonicK K *
          (P1Schedule.accumulated s r + ((K : ℝ) / 24) * (s.time r : ℝ) * gap r)) := by
  have hg := gap_pos_of_sorted hK gap hpos hsorted r
  have hm : (0 : ℝ) < s.time r := Nat.cast_pos.mpr (s.positive r)
  have hL := P1Ranking.harmonicK_pos (lt_of_lt_of_le (by decide : 0 < 2) hK)
  have hH := fixedComplexity_pos hK gap hpos hsorted s
  have hD : 0 < P1Schedule.accumulated s r + ((K : ℝ) / 24) * (s.time r : ℝ) * gap r :=
    add_pos_of_pos_of_nonneg (P1Schedule.accumulated_pos s r) (by positivity)
  have hcost := rankCost_le_fixedComplexity gap s r
  have hscaled : (n : ℝ) * P1Ranking.harmonicK K *
      (P1Schedule.accumulated s r + ((K : ℝ) / 24) * (s.time r : ℝ) * gap r) ≤
      fixedComplexity gap s * ((s.time r : ℝ) ^ 2 * (gap r) ^ 2) := by
    apply (div_le_iff₀ (mul_pos (pow_pos hm 2) (pow_pos hg 2))).1
    simpa only [rankCost, mul_div_assoc] using hcost
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith only [hscaled]

/-- The exact schedule exponent can only improve after the rank's comparison time. -/
theorem exponent_monotone (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    {n : ℕ} (s : P1Schedule.Schedule hK n) (r : Fin K) (t : ℕ) (ht : s.time r ≤ t) :
    ((s.time r : ℝ) * gap r) ^ 2 /
        (128 * P1Ranking.harmonicK K *
          (P1Schedule.accumulated s r + ((K : ℝ) / 24) * (s.time r : ℝ) * gap r)) ≤
      ((t : ℝ) * gap r) ^ 2 /
        (128 * P1Ranking.harmonicK K *
          (P1Schedule.accumulated s r + P1Schedule.rank r * ((t : ℝ) - (s.time r : ℝ)) +
            ((K : ℝ) / 24) * (t : ℝ) * gap r)) := by
  let m : ℝ := s.time r
  let D : ℝ := P1Schedule.accumulated s r + ((K : ℝ) / 24) * m * gap r
  let T : ℝ := P1Schedule.accumulated s r + P1Schedule.rank r * ((t : ℝ) - m) +
    ((K : ℝ) / 24) * (t : ℝ) * gap r
  have hm : 0 < m := Nat.cast_pos.mpr (s.positive r)
  have htime : m ≤ (t : ℝ) := Nat.cast_le.mpr ht
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hg := gap_pos_of_sorted hK gap hpos hsorted r
  have hL := P1Ranking.harmonicK_pos (lt_of_lt_of_le (by decide : 0 < 2) hK)
  have hD : 0 < D := add_pos_of_pos_of_nonneg (P1Schedule.accumulated_pos s r) (by positivity)
  have hT : 0 < T := add_pos_of_pos_of_nonneg (P1Schedule.continuation_pos s r t ht) (by positivity)
  have hscaled : T ≤ ((t : ℝ) * D) / m := by
    simpa only [D, T, m, div_mul_eq_mul_div] using varianceBudget_le_scaled s r t ht (gap r)
  have hlinear : T * m ≤ (t : ℝ) * D := (le_div_iff₀ hm).1 hscaled
  have hsquare : m ^ 2 * T ≤ (t : ℝ) ^ 2 * D := by
    calc
      m ^ 2 * T = (T * m) * m := by ring
      _ ≤ ((t : ℝ) * D) * m := mul_le_mul_of_nonneg_right hlinear hm.le
      _ = ((t : ℝ) * m) * D := by ring
      _ ≤ ((t : ℝ) * (t : ℝ)) * D :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htime ht0) hD.le
      _ = _ := by ring
  change (m * gap r) ^ 2 / (128 * P1Ranking.harmonicK K * D) ≤
    ((t : ℝ) * gap r) ^ 2 / (128 * P1Ranking.harmonicK K * T)
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  have hmult := mul_le_mul_of_nonneg_left hsquare
    (show 0 ≤ 128 * P1Ranking.harmonicK K * (gap r) ^ 2 by positivity)
  nlinarith only [hmult]

/-- The final schedule-dependent exponent, before any optimization over schedules. -/
theorem exponent_comparison (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    {n : ℕ} (s : P1Schedule.Schedule hK n) (r : Fin K) (t : ℕ) (ht : s.time r ≤ t) :
    (n : ℝ) / (128 * fixedComplexity gap s) ≤
      ((t : ℝ) * gap r) ^ 2 /
        (128 * P1Ranking.harmonicK K *
          (P1Schedule.accumulated s r + P1Schedule.rank r * ((t : ℝ) - (s.time r : ℝ)) +
            ((K : ℝ) / 24) * (t : ℝ) * gap r)) :=
  (comparison_time_exponent hK gap hpos hsorted s r).trans
    (exponent_monotone hK gap hpos hsorted s r t ht)

/-- Increasing every positive fraction by at most two multiplies each cost by at most two. -/
theorem profileCost_le_two (gap b c : Fin K → ℝ) (r : Fin K) (hgap : 0 < gap r)
    (hb : ∀ j, 0 < b j) (hlower : ∀ j, b j ≤ c j) (hupper : ∀ j, c j ≤ 2 * b j) :
    profileCost gap c r ≤ 2 * profileCost gap b r := by
  have hsum : (∑ j ∈ P1Schedule.later r, c j) ≤ 2 * ∑ j ∈ P1Schedule.later r, b j := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => hupper j)
  have hnum : algebraicAccumulated c r + ((K : ℝ) / 24) * c r * gap r ≤
      2 * (algebraicAccumulated b r + ((K : ℝ) / 24) * b r * gap r) := by
    calc
      _ ≤ P1Schedule.rank r * (2 * b r) + 2 * (∑ j ∈ P1Schedule.later r, b j) +
          ((K : ℝ) / 24) * (2 * b r) * gap r :=
        add_le_add (add_le_add
          (mul_le_mul_of_nonneg_left (hupper r) (P1Schedule.rank_pos r).le) hsum)
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hupper r) (by positivity)) hgap.le)
      _ = _ := by unfold algebraicAccumulated; ring
  have hnum0 : 0 ≤ 2 * (algebraicAccumulated b r + ((K : ℝ) / 24) * b r * gap r) := by
    unfold algebraicAccumulated
    have hsum0 : 0 ≤ ∑ j ∈ P1Schedule.later r, b j :=
      Finset.sum_nonneg (fun j _ => (hb j).le)
    have hr0 := (P1Schedule.rank_pos r).le
    have hb0 := (hb r).le
    positivity
  have hden : (b r) ^ 2 * (gap r) ^ 2 ≤ (c r) ^ 2 * (gap r) ^ 2 :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hb r).le (hlower r) 2) (sq_nonneg _)
  calc
    _ ≤ (2 * (algebraicAccumulated b r + ((K : ℝ) / 24) * b r * gap r)) /
        ((b r) ^ 2 * (gap r) ^ 2) :=
      div_le_div₀ hnum0 hnum (mul_pos (pow_pos (hb r) 2) (pow_pos hgap 2)) hden
    _ = _ := by unfold profileCost; ring

theorem profileComplexity_le_two (hK : 2 ≤ K) (gap b c : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    (hb : ∀ j, 0 < b j) (hlower : ∀ j, b j ≤ c j) (hupper : ∀ j, c j ≤ 2 * b j) :
    profileComplexity hK gap c ≤ 2 * profileComplexity hK gap b := by
  have hsup : (Finset.univ : Finset (Fin K)).sup'
      ⟨firstRank hK, Finset.mem_univ _⟩ (profileCost gap c) ≤
      2 * (Finset.univ : Finset (Fin K)).sup'
        ⟨firstRank hK, Finset.mem_univ _⟩ (profileCost gap b) := by
    apply Finset.sup'_le
    intro r _
    exact (profileCost_le_two gap b c r (gap_pos_of_sorted hK gap hpos hsorted r)
      hb hlower hupper).trans
      (mul_le_mul_of_nonneg_left (Finset.le_sup' _ (Finset.mem_univ r)) (by positivity))
  have h := mul_le_mul_of_nonneg_left hsup
    (P1Ranking.harmonicK_pos (lt_of_lt_of_le (by decide : 0 < 2) hK)).le
  simpa only [profileComplexity, mul_left_comm] using h

theorem rounded_fraction_lower (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    (hduplicate : gap (firstRank hK) = gap (secondRank hK))
    (n : ℕ) (hn : 0 < n) (r : Fin K) :
    idealFractions hK gap r ≤
      P1Schedule.fraction (P1Schedule.rounded hK gap hpos hsorted hduplicate n hn) r := by
  apply (le_div_iff₀ (Nat.cast_pos.mpr hn)).2
  have heq : idealFractions hK gap r * (n : ℝ) = (n : ℝ) * gap (firstRank hK) / gap r := by
    unfold idealFractions
    ring
  rw [heq]
  exact P1Schedule.rounded_lower hK gap hpos hsorted hduplicate n hn r

theorem rounded_fraction_upper (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    (hduplicate : gap (firstRank hK) = gap (secondRank hK)) (n : ℕ) (hn : 0 < n)
    (hbudget : gap (lastRank hK) / gap (firstRank hK) ≤ (n : ℝ)) (r : Fin K) :
    P1Schedule.fraction (P1Schedule.rounded hK gap hpos hsorted hduplicate n hn) r ≤
      2 * idealFractions hK gap r := by
  apply (div_le_iff₀ (Nat.cast_pos.mpr hn)).2
  have heq : (2 * idealFractions hK gap r) * (n : ℝ) =
      2 * ((n : ℝ) * gap (firstRank hK) / gap r) := by
    unfold idealFractions
    ring
  rw [heq]
  exact (P1Schedule.rounded_upper hK gap hpos hsorted hduplicate n hn hbudget r).le

/-- The corollary's rounded admissible schedule loses at most a factor two. -/
theorem rounded_fixedComplexity_le (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    (hduplicate : gap (firstRank hK) = gap (secondRank hK)) (n : ℕ) (hn : 0 < n)
    (hbudget : gap (lastRank hK) / gap (firstRank hK) ≤ (n : ℝ)) :
    fixedComplexity gap (P1Schedule.rounded hK gap hpos hsorted hduplicate n hn) ≤
      2 * profileComplexity hK gap (idealFractions hK gap) := by
  rw [fixedComplexity_eq_profileComplexity hK gap hpos hsorted]
  exact profileComplexity_le_two hK gap _ _ hpos hsorted
    (fun r => div_pos hpos (gap_pos_of_sorted hK gap hpos hsorted r))
    (rounded_fraction_lower hK gap hpos hsorted hduplicate n hn)
    (rounded_fraction_upper hK gap hpos hsorted hduplicate n hn hbudget)

end BestOfBothWorlds.P1Complexity
