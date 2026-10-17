module

public import BestOfBothWorlds.GapComplexity
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

/-!
Finite expected-count selection and deterministic phase arithmetic for the two
lower-bound constructions. Counts are real expectations under one fixed learner
and BASE law. No choice in this file depends on a realized trajectory, and no
positivity assumption is made about the learner's action probabilities.
-/

@[expose] public section

open scoped BigOperators

namespace BestOfBothWorlds.LowerBoundSelection

variable {K : ℕ}

/-- Manuscript ranks are one-based; finite indices are zero-based. -/
def rank (i : Fin K) : ℝ := ((i.val + 1 : ℕ) : ℝ)

theorem rank_pos (i : Fin K) : 0 < rank i := Nat.cast_pos.mpr (Nat.succ_pos _)

/-- The finite averaging step, with no probabilistic assumptions. -/
theorem exists_mem_le_average {α : Type*} [DecidableEq α] (s : Finset α)
    (hs : s.Nonempty) (count : α → ℝ) (m : ℝ)
    (hbudget : ∑ k ∈ s, count k ≤ m) :
    ∃ k ∈ s, count k ≤ m / (s.card : ℝ) := by
  have hcard : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hs.card_pos.ne'
  apply Finset.exists_le_of_sum_le hs
  calc
    ∑ k ∈ s, count k ≤ m := hbudget
    _ = ∑ _k ∈ s, m / (s.card : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      field_simp [hcard]

/-- Theorem 2's informative arm is fixed by the vector of BASE expectations. -/
theorem exists_suboptimal_light (hK : 2 ≤ K) (count : Fin K → ℝ) (m : ℝ)
    (hnonneg : ∀ k, 0 ≤ count k) (hbudget : ∑ k, count k ≤ m) :
    ∃ k : Fin K, k ≠ firstRank hK ∧ count k ≤ m / ((K : ℝ) - 1) := by
  classical
  let s : Finset (Fin K) := Finset.univ.erase (firstRank hK)
  have hs : s.Nonempty := by
    refine ⟨secondRank hK, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩⟩
    intro heq
    have hv := congrArg Fin.val heq
    change 1 = 0 at hv
    omega
  have hsub : ∑ k ∈ s, count k ≤ m :=
    (Finset.sum_le_univ_sum_of_nonneg hnonneg).trans hbudget
  obtain ⟨k, hk, hcount⟩ := exists_mem_le_average s hs count m hsub
  refine ⟨k, (Finset.mem_erase.mp hk).1, ?_⟩
  have hcard : s.card = K - 1 := by simp [s]
  rw [hcard, Nat.cast_sub (by omega : 1 ≤ K), Nat.cast_one] at hcount
  exact hcount

/-- Half-horizon sampling gives the manuscript's weaker n/K allowance. -/
theorem suboptimal_average_le (hK : 2 ≤ K) {m n : ℝ}
    (hm : 0 ≤ m) (hhalf : 2 * m ≤ n) :
    m / ((K : ℝ) - 1) ≤ n / (K : ℝ) := by
  have hKr : (2 : ℝ) ≤ (K : ℝ) := Nat.cast_le.mpr hK
  have hKpos : (0 : ℝ) < (K : ℝ) := lt_of_lt_of_le (by norm_num) hKr
  have hKm : 0 < (K : ℝ) - 1 := by linarith
  apply (div_le_div_iff₀ hKm hKpos).2
  have hmul := mul_le_mul_of_nonneg_right hhalf
    (show 0 ≤ (K : ℝ) - 1 by linarith)
  nlinarith [mul_nonneg hm (sub_nonneg.mpr hKr)]

/-- Theorem 2's two equal phases use floor(n/2) rounds apiece. -/
def halfHorizon (n : ℕ) : ℕ := n / 2

theorem halfHorizon_twice_le (n : ℕ) : 2 * halfHorizon n ≤ n := by
  unfold halfHorizon
  omega

/-- The optional remainder is exactly zero or one round. -/
theorem halfHorizon_padding (n : ℕ) : n - 2 * halfHorizon n ≤ 1 := by
  unfold halfHorizon
  omega

theorem halfHorizon_pos {n : ℕ} (hn : 2 ≤ n) : 0 < halfHorizon n := by
  unfold halfHorizon
  omega

theorem halfHorizon_lt {n : ℕ} (hn : 0 < n) : halfHorizon n < n := by
  unfold halfHorizon
  omega

/-- The exact beta interval used for odd as well as even horizons. -/
theorem halfHorizon_ratio_bounds {n : ℕ} (hn : 12 ≤ n) :
    (11 : ℝ) / 24 ≤ (halfHorizon n : ℝ) / (n : ℝ) ∧
      (halfHorizon n : ℝ) / (n : ℝ) ≤ 1 / 2 := by
  have hnr : (12 : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hupper : (2 : ℝ) * (halfHorizon n : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast halfHorizon_twice_le n
  have hlowerNat : n ≤ 2 * halfHorizon n + 1 := by unfold halfHorizon; omega
  have hlower : (n : ℝ) ≤ 2 * (halfHorizon n : ℝ) + 1 := by
    exact_mod_cast hlowerNat
  constructor
  · apply (le_div_iff₀ hnpos).2
    nlinarith
  · apply (div_le_iff₀ hnpos).2
    linarith

/-- The complete deterministic count-selection inequality in Appendix D. -/
theorem exists_halfHorizon_light (hK : 2 ≤ K) (n : ℕ) (count : Fin K → ℝ)
    (hnonneg : ∀ k, 0 ≤ count k) (hbudget : ∑ k, count k ≤ (halfHorizon n : ℝ)) :
    ∃ k : Fin K, k ≠ firstRank hK ∧ count k ≤ (n : ℝ) / (K : ℝ) := by
  obtain ⟨k, hk, hc⟩ := exists_suboptimal_light hK count (halfHorizon n : ℝ) hnonneg hbudget
  refine ⟨k, hk, hc.trans ?_⟩
  apply suboptimal_average_le hK (Nat.cast_nonneg _)
  exact_mod_cast halfHorizon_twice_le n

/-- An attained maximizing rank and its exact reference H_BOB expression. -/
theorem exists_maximizing_rank (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (_hsorted : Monotone gap)
    (hduplicate : gap (firstRank hK) = gap (secondRank hK)) :
    ∃ i : Fin K, 1 ≤ i.val ∧
      (∀ r, rank r / gap r ≤ rank i / gap i) ∧
      H_BOB hK gap = rank i / (gap (firstRank hK) * gap i) := by
  classical
  obtain ⟨i, _hi, hmax⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (Fin K)))
    ⟨firstRank hK, Finset.mem_univ _⟩ (fun r => rank r / gap r)
  have hmaximal : ∀ r, rank r / gap r ≤ rank i / gap i := by
    intro r
    rw [← hmax]
    exact Finset.le_sup' (fun j : Fin K => rank j / gap j) (Finset.mem_univ r)
  have hi : 1 ≤ i.val := by
    by_contra hnot
    have heq : i = firstRank hK := Fin.ext (by change i.val = 0; omega)
    have hc := hmaximal (secondRank hK)
    rw [heq, ← hduplicate] at hc
    have hr1 : rank (firstRank hK) = (1 : ℝ) := by norm_num [rank, firstRank]
    have hr2 : rank (secondRank hK) = (2 : ℝ) := by norm_num [rank, secondRank]
    rw [hr1, hr2] at hc
    have hc' := (div_le_div_iff₀ hpos hpos).1 hc
    linarith
  refine ⟨i, hi, hmaximal, ?_⟩
  change (1 / gap (firstRank hK)) *
    (Finset.univ : Finset (Fin K)).sup' _ (fun r => rank r / gap r) = _
  rw [hmax, div_mul_div_comm, one_mul]

/-- The upper half of manuscript ranks through i, including both endpoints. -/
def upperHalf (i : Fin K) : Finset (Fin K) :=
  Finset.Icc ⟨i.val / 2, lt_of_le_of_lt (Nat.div_le_self _ _) i.isLt⟩ i

theorem upperHalf_nonempty (i : Fin K) : (upperHalf i).Nonempty := by
  refine ⟨i, Finset.mem_Icc.mpr ⟨?_, le_rfl⟩⟩
  exact Nat.div_le_self _ _

theorem upperHalf_card (i : Fin K) : (upperHalf i).card = i.val + 1 - i.val / 2 := by
  simp only [upperHalf, Fin.card_Icc]

theorem upperHalf_card_large (i : Fin K) : rank i ≤ 2 * ((upperHalf i).card : ℝ) := by
  have hn : i.val + 1 ≤ 2 * (upperHalf i).card := by rw [upperHalf_card]; omega
  have hc : ((i.val + 1 : ℕ) : ℝ) ≤ ((2 * (upperHalf i).card : ℕ) : ℝ) :=
    Nat.cast_le.mpr hn
  simpa only [rank, Nat.cast_mul, Nat.cast_ofNat] using hc

theorem upperHalf_rank_bounds (i k : Fin K) (hk : k ∈ upperHalf i) :
    k ≤ i ∧ rank i / 2 ≤ rank k := by
  obtain ⟨hlower, hupper⟩ := Finset.mem_Icc.mp hk
  refine ⟨hupper, ?_⟩
  have hn : i.val + 1 ≤ 2 * (k.val + 1) := by
    change i.val / 2 ≤ k.val at hlower
    omega
  have hc : ((i.val + 1 : ℕ) : ℝ) ≤ ((2 * (k.val + 1) : ℕ) : ℝ) :=
    Nat.cast_le.mpr hn
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hc
  change (((i.val + 1 : ℕ) : ℝ) / 2) ≤ ((k.val + 1 : ℕ) : ℝ)
  linarith

/-- Theorem 4's upper-half selection, including the separate i=2 case. -/
theorem exists_informative_arm (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    (i : Fin K) (hi : 1 ≤ i.val)
    (hmax : ∀ r, rank r / gap r ≤ rank i / gap i)
    (count : Fin K → ℝ) (m : ℝ)
    (hnonneg : ∀ k, 0 ≤ count k) (hbudget : ∑ k, count k ≤ m) :
    ∃ k : Fin K, 1 ≤ k.val ∧ k ≤ i ∧ rank i / 2 ≤ rank k ∧
      gap i / 2 ≤ gap k ∧ gap k ≤ gap i ∧ count k ≤ 2 * m / rank i := by
  classical
  have hm : 0 ≤ m := (Finset.sum_nonneg (fun k _ => hnonneg k)).trans hbudget
  have hselect : ∃ k : Fin K, 1 ≤ k.val ∧ k ≤ i ∧
      rank i / 2 ≤ rank k ∧ count k ≤ 2 * m / rank i := by
    by_cases hsecond : i = secondRank hK
    · refine ⟨secondRank hK, by simp [secondRank], hsecond.ge, ?_, ?_⟩
      · simp [hsecond, rank, secondRank]
      · have hc : count (secondRank hK) ≤ m :=
          (Finset.single_le_sum (fun k _ => hnonneg k) (Finset.mem_univ _)).trans hbudget
        simpa [hsecond, rank, secondRank] using hc
    · have hi3 : 2 ≤ i.val := by
        have hne : i.val ≠ 1 := by
          intro heq
          apply hsecond
          exact Fin.ext heq
        omega
      obtain ⟨k, hk, hc⟩ := exists_mem_le_average (upperHalf i)
        (upperHalf_nonempty i) count m
        ((Finset.sum_le_univ_sum_of_nonneg hnonneg).trans hbudget)
      obtain ⟨hki, hrank⟩ := upperHalf_rank_bounds i k hk
      have hkpos : 1 ≤ k.val := by
        have hlower := (Finset.mem_Icc.mp hk).1
        change i.val / 2 ≤ k.val at hlower
        omega
      refine ⟨k, hkpos, hki, hrank, hc.trans ?_⟩
      have hcardpos : (0 : ℝ) < ((upperHalf i).card : ℝ) :=
        Nat.cast_pos.mpr (upperHalf_nonempty i).card_pos
      apply (div_le_div_iff₀ hcardpos (rank_pos i)).2
      nlinarith [mul_nonneg hm (sub_nonneg.mpr (upperHalf_card_large i))]
  obtain ⟨k, hkpos, hki, hrank, hcount⟩ := hselect
  refine ⟨k, hkpos, hki, hrank, ?_, hsorted hki, hcount⟩
  have hgapi := gap_pos_of_sorted hK gap hpos hsorted i
  have hgapk := gap_pos_of_sorted hK gap hpos hsorted k
  have hproduct := (div_le_div_iff₀ hgapk hgapi).1 (hmax k)
  have hmul := mul_le_mul_of_nonneg_right hrank hgapi.le
  have hri := rank_pos i
  apply le_of_mul_le_mul_left (a := rank i) ?_ hri
  nlinarith

/-- Capped initial-phase fraction from Appendix E. -/
noncomputable def phaseFraction (d D : ℝ) : ℝ := min 1 (2 * d / D)

/-- The actual integer phase length; this construction includes an empty suffix. -/
noncomputable def phaseLength (n : ℕ) (d D : ℝ) : ℕ :=
  ⌈(n : ℝ) * phaseFraction d D⌉₊

theorem phaseFraction_pos {d D : ℝ} (hd : 0 < d) (hD : 0 < D) :
    0 < phaseFraction d D := lt_min (by norm_num) (div_pos (by positivity) hD)

theorem phaseLength_pos (n : ℕ) (hn : 0 < n) {d D : ℝ}
    (hd : 0 < d) (hD : 0 < D) : 0 < phaseLength n d D :=
  Nat.ceil_pos.mpr (mul_pos (Nat.cast_pos.mpr hn) (phaseFraction_pos hd hD))

theorem phaseLength_le_horizon (n : ℕ) (d D : ℝ) : phaseLength n d D ≤ n := by
  apply Nat.ceil_le.mpr
  exact (mul_le_mul_of_nonneg_left (min_le_left _ _) (Nat.cast_nonneg n)).trans_eq (mul_one _)

theorem phaseLength_eq_capped_ceiling (n : ℕ) {d D : ℝ}
    (_hd : 0 < d) (_hD : 0 < D) :
    phaseLength n d D = min n ⌈2 * (n : ℝ) * d / D⌉₊ := by
  by_cases hcap : 1 ≤ 2 * d / D
  · have heq : phaseFraction d D = 1 := min_eq_left hcap
    rw [phaseLength, heq, mul_one, Nat.ceil_natCast]
    apply (min_eq_left ?_).symm
    have hc : (n : ℝ) ≤ 2 * (n : ℝ) * d / D := by
      have hm := mul_le_mul_of_nonneg_left hcap (Nat.cast_nonneg n)
      have halg : (n : ℝ) * (2 * d / D) = 2 * (n : ℝ) * d / D := by ring
      simpa only [mul_one, halg] using hm
    exact_mod_cast hc.trans (Nat.le_ceil _)
  · have hratio : 2 * d / D ≤ 1 := (lt_of_not_ge hcap).le
    have heq : phaseFraction d D = 2 * d / D := min_eq_right hratio
    have halg : (n : ℝ) * (2 * d / D) = 2 * (n : ℝ) * d / D := by ring
    rw [phaseLength, heq, halg]
    apply (min_eq_right ?_).symm
    apply Nat.ceil_le.mpr
    have hm := mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg n)
    simpa only [mul_one, ← halg] using hm

theorem phaseLength_of_equal (n : ℕ) {d : ℝ} (hd : 0 < d) :
    phaseLength n d d = n := by
  have hratio : 2 * d / d = (2 : ℝ) := mul_div_cancel_right₀ _ hd.ne'
  simp [phaseLength, phaseFraction, hratio]

theorem phaseLength_le_two_add_one (n : ℕ) {d D : ℝ}
    (hd : 0 < d) (hD : 0 < D) :
    (phaseLength n d D : ℝ) ≤ 2 * (n : ℝ) * d / D + 1 := by
  have hc := Nat.ceil_lt_add_one
    (mul_nonneg (Nat.cast_nonneg n) (phaseFraction_pos hd hD).le)
  have hf := mul_le_mul_of_nonneg_left (min_le_right (1 : ℝ) (2 * d / D))
    (Nat.cast_nonneg n)
  change (phaseLength n d D : ℝ) < (n : ℝ) * phaseFraction d D + 1 at hc
  change (n : ℝ) * phaseFraction d D ≤ (n : ℝ) * (2 * d / D) at hf
  have halg : (n : ℝ) * (2 * d / D) = 2 * (n : ℝ) * d / D := by ring
  rw [halg] at hf
  linarith

theorem phaseLength_le_three (n : ℕ) {d D : ℝ}
    (hd : 0 < d) (hD : 0 < D) (hone : 1 ≤ (n : ℝ) * d / D) :
    (phaseLength n d D : ℝ) ≤ 3 * (n : ℝ) * d / D := by
  have hc := phaseLength_le_two_add_one n hd hD
  have htwo : 2 * (n : ℝ) * d / D = 2 * ((n : ℝ) * d / D) := by ring
  have hthree : 3 * (n : ℝ) * d / D = 3 * ((n : ℝ) * d / D) := by ring
  rw [htwo] at hc
  rw [hthree]
  linarith

/-- If the cap did not fill the horizon, its uncapped ratio is rounded upward. -/
theorem phaseLength_lower_of_lt (n : ℕ) {d D : ℝ}
    (_hd : 0 < d) (_hD : 0 < D) (hshort : phaseLength n d D < n) :
    2 * (n : ℝ) * d / D ≤ (phaseLength n d D : ℝ) := by
  have hnotcap : ¬ 1 ≤ 2 * d / D := by
    intro hcap
    have heq : phaseLength n d D = n := by
      simp only [phaseLength, phaseFraction, min_eq_left hcap, mul_one, Nat.ceil_natCast]
    omega
  have heq : phaseFraction d D = 2 * d / D := min_eq_right (lt_of_not_ge hnotcap).le
  have hc : (n : ℝ) * phaseFraction d D ≤ (phaseLength n d D : ℝ) := Nat.le_ceil _
  rw [heq] at hc
  convert hc using 1; ring

/-- Expected average gap of selected arm k in the randomized ADV construction. -/
noncomputable def expectedSelectedGap (n : ℕ) (d D δ : ℝ) : ℝ :=
  ((phaseLength n d D : ℝ) / (n : ℝ)) * δ -
    (1 - (phaseLength n d D : ℝ) / (n : ℝ)) * d / 4

/-- Both full and nonfull phases preserve the manuscript's expected-gap margin. -/
theorem expectedSelectedGap_bounds (n : ℕ) (hn : 0 < n) {d D δ : ℝ}
    (hd : 0 < d) (hD : 0 < D) (hδmin : d ≤ δ)
    (hδhalf : D / 2 ≤ δ) (hδmax : δ ≤ D)
    (hslack : D / (n : ℝ) ≤ d / 8) :
    3 * d / 4 ≤ expectedSelectedGap n d D δ ∧
      expectedSelectedGap n d D δ ≤ 17 * d / 8 := by
  have hnreal : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hNnonneg : (0 : ℝ) ≤ (phaseLength n d D : ℝ) := Nat.cast_nonneg _
  have hNle : (phaseLength n d D : ℝ) ≤ (n : ℝ) :=
    Nat.cast_le.mpr (phaseLength_le_horizon n d D)
  have hid : expectedSelectedGap n d D δ * (n : ℝ) =
      (phaseLength n d D : ℝ) * δ - ((n : ℝ) - (phaseLength n d D : ℝ)) * d / 4 := by
    unfold expectedSelectedGap
    field_simp [hnreal.ne']
  constructor
  · by_cases hfull : phaseLength n d D = n
    · simp only [expectedSelectedGap, hfull, div_self hnreal.ne', one_mul, sub_self,
        zero_mul, zero_div, sub_zero]
      linarith
    · have hshort : phaseLength n d D < n := lt_of_le_of_ne
        (phaseLength_le_horizon n d D) hfull
      have hNlower := phaseLength_lower_of_lt n hd hD hshort
      have hND : 2 * (n : ℝ) * d ≤ (phaseLength n d D : ℝ) * D :=
        (div_le_iff₀ hD).1 hNlower
      have hNδ := mul_le_mul_of_nonneg_left hδhalf hNnonneg
      apply (le_of_mul_le_mul_right ?_ hnreal)
      nlinarith [mul_nonneg hNnonneg hd.le]
  · have hNupper := phaseLength_le_two_add_one n hd hD
    have hND : (phaseLength n d D : ℝ) * D ≤ 2 * (n : ℝ) * d + D := by
      have hm := (le_div_iff₀ hD).1
        (show (phaseLength n d D : ℝ) ≤ (2 * (n : ℝ) * d + D) / D by
          convert hNupper using 1; field_simp)
      exact hm
    have hslack' : D ≤ (d / 8) * (n : ℝ) := (div_le_iff₀ hnreal).1 hslack
    have hNδ := mul_le_mul_of_nonneg_left hδmax hNnonneg
    have hsub := mul_nonneg (sub_nonneg.mpr hNle) hd.le
    apply (le_of_mul_le_mul_right ?_ hnreal)
    nlinarith

end BestOfBothWorlds.LowerBoundSelection
