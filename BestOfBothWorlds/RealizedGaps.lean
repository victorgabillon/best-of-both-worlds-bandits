module

public import BestOfBothWorlds.FiniteMaximizer
public import BestOfBothWorlds.GapComplexity
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Tactic.Linarith
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Positivity

/-!
Realized rewards and gaps of a fixed oblivious table. The best arm is the
smallest cumulative maximizer. Its gap duplicates the smallest competitor gap.
The ranked profile is a permutation of these actual arm gaps, sorted using
Mathlib's tuple sorting; it is not an artificial constant profile.
-/

@[expose] public section

namespace BestOfBothWorlds.RealizedGaps

variable {K : ℕ}

theorem arms_pos (hK : 2 ≤ K) : 0 < K :=
  lt_of_lt_of_le (by decide : 0 < 2) hK

/-- The true cumulative reward of an arm in the first `n` rounds. -/
def cumulative (g : ℕ → Fin K → ℝ) (n : ℕ) (k : Fin K) : ℝ :=
  ∑ t ∈ Finset.range n, g t k

/-- The realized average reward; the unique-best case will imply `n > 0`. -/
noncomputable def average (g : ℕ → Fin K → ℝ) (n : ℕ) (k : Fin K) : ℝ :=
  cumulative g n k / (n : ℝ)

/-- The smallest arm index attaining the largest realized cumulative reward. -/
noncomputable def best (hK : 0 < K) (g : ℕ → Fin K → ℝ) (n : ℕ) : Fin K :=
  FiniteMaximizer.select hK (cumulative g n)

theorem cumulative_le_best (hK : 0 < K) (g : ℕ → Fin K → ℝ) (n : ℕ) (k : Fin K) :
    cumulative g n k ≤ cumulative g n (best hK g n) :=
  FiniteMaximizer.le_select hK (cumulative g n) k

theorem best_le_of_eq (hK : 0 < K) (g : ℕ → Fin K → ℝ) (n : ℕ) (k : Fin K)
    (heq : cumulative g n k = cumulative g n (best hK g n)) : best hK g n ≤ k :=
  FiniteMaximizer.select_le_of_eq hK (cumulative g n) k heq

/-- The manuscript assumes that the realized best arm is unique. -/
def UniqueBest (hK : 0 < K) (g : ℕ → Fin K → ℝ) (n : ℕ) : Prop :=
  ∀ k, k ≠ best hK g n → cumulative g n k < cumulative g n (best hK g n)

theorem best_eq_of_strict (hK : 0 < K) (g : ℕ → Fin K → ℝ) (n : ℕ) (a : Fin K)
    (hstrict : ∀ k, k ≠ a → cumulative g n k < cumulative g n a) :
    best hK g n = a :=
  FiniteMaximizer.select_eq_of_strict hK (cumulative g n) a hstrict

theorem uniqueBest_of_strict (hK : 0 < K) (g : ℕ → Fin K → ℝ) (n : ℕ) (a : Fin K)
    (hstrict : ∀ k, k ≠ a → cumulative g n k < cumulative g n a) :
    UniqueBest hK g n := by
  unfold UniqueBest
  rw [best_eq_of_strict hK g n a hstrict]
  exact hstrict

/-- All arms other than the actual best arm. -/
noncomputable def competitors (hK : 0 < K) (g : ℕ → Fin K → ℝ) (n : ℕ) : Finset (Fin K) :=
  Finset.univ.erase (best hK g n)

theorem mem_competitors (hK : 0 < K) (g : ℕ → Fin K → ℝ) (n : ℕ) (k : Fin K) :
    k ∈ competitors hK g n ↔ k ≠ best hK g n := by
  simp [competitors]

/-- At least one competitor exists, even when the best arm has an arbitrary index. -/
theorem competitors_nonempty (hK : 2 ≤ K) (g : ℕ → Fin K → ℝ) (n : ℕ) :
    (competitors (arms_pos hK) g n).Nonempty := by
  by_cases hb : best (arms_pos hK) g n = firstRank hK
  · refine ⟨secondRank hK, (mem_competitors _ _ _ _).2 ?_⟩
    intro heq
    have hv := congrArg Fin.val (heq.trans hb)
    simp [firstRank, secondRank] at hv
  · exact ⟨firstRank hK, (mem_competitors _ _ _ _).2 (Ne.symm hb)⟩

/-- Unique best arms with at least two arms cannot occur at the zero horizon. -/
theorem horizon_pos (hK : 2 ≤ K) (g : ℕ → Fin K → ℝ) (n : ℕ)
    (hUnique : UniqueBest (arms_pos hK) g n) : 0 < n := by
  by_contra hn
  have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
  obtain ⟨k, hk⟩ := competitors_nonempty hK g n
  have hlt := hUnique k ((mem_competitors _ _ _ _).1 hk)
  simp [cumulative, hn0] at hlt

theorem not_uniqueBest_zero (hK : 2 ≤ K) (g : ℕ → Fin K → ℝ) :
    ¬UniqueBest (arms_pos hK) g 0 := by
  intro hUnique
  exact (Nat.not_lt_zero 0) (horizon_pos hK g 0 hUnique)

theorem cumulative_nonneg (g : ℕ → Fin K → ℝ) (n : ℕ)
    (hg : ∀ t < n, ∀ k, 0 ≤ g t k ∧ g t k ≤ 1) (k : Fin K) :
    0 ≤ cumulative g n k := by
  exact Finset.sum_nonneg (fun t ht => (hg t (Finset.mem_range.mp ht) k).1)

theorem cumulative_le_horizon (g : ℕ → Fin K → ℝ) (n : ℕ)
    (hg : ∀ t < n, ∀ k, 0 ≤ g t k ∧ g t k ≤ 1) (k : Fin K) :
    cumulative g n k ≤ (n : ℝ) := by
  calc
    _ ≤ ∑ t ∈ Finset.range n, (1 : ℝ) :=
      Finset.sum_le_sum (fun t ht => (hg t (Finset.mem_range.mp ht) k).2)
    _ = _ := by simp

/-- The average reward difference from the best arm, before duplicating its own gap. -/
noncomputable def competitorGap (hK : 0 < K) (g : ℕ → Fin K → ℝ) (n : ℕ) (k : Fin K) : ℝ :=
  (cumulative g n (best hK g n) - cumulative g n k) / (n : ℝ)

theorem competitorGap_eq_average (hK : 0 < K) (g : ℕ → Fin K → ℝ) (n : ℕ) (k : Fin K) :
    competitorGap hK g n k = average g n (best hK g n) - average g n k := by
  simp only [competitorGap, average, sub_div]

/-- The actual smallest competitor gap, over a proved nonempty finite set. -/
noncomputable def minGap (hK : 2 ≤ K) (g : ℕ → Fin K → ℝ) (n : ℕ) : ℝ :=
  (competitors (arms_pos hK) g n).inf' (competitors_nonempty hK g n)
    (competitorGap (arms_pos hK) g n)

theorem minGap_le_gap (hK : 2 ≤ K) (g : ℕ → Fin K → ℝ) (n : ℕ)
    (k : Fin K) (hk : k ≠ best (arms_pos hK) g n) :
    minGap hK g n ≤ competitorGap (arms_pos hK) g n k :=
  Finset.inf'_le _ ((mem_competitors _ _ _ _).2 hk)

theorem minGap_attained (hK : 2 ≤ K) (g : ℕ → Fin K → ℝ) (n : ℕ) :
    ∃ k, k ≠ best (arms_pos hK) g n ∧
      minGap hK g n = competitorGap (arms_pos hK) g n k := by
  obtain ⟨k, hk, heq⟩ := Finset.exists_mem_eq_inf' (competitors_nonempty hK g n)
    (competitorGap (arms_pos hK) g n)
  exact ⟨k, (mem_competitors _ _ _ _).1 hk, heq⟩

theorem minGap_eq_of_constant_competitors (hK : 2 ≤ K) (g : ℕ → Fin K → ℝ) (n : ℕ)
    (delta : ℝ)
    (hgap : ∀ k, k ≠ best (arms_pos hK) g n → competitorGap (arms_pos hK) g n k = delta) :
    minGap hK g n = delta := by
  obtain ⟨k, hk, heq⟩ := minGap_attained hK g n
  exact heq.trans (hgap k hk)

theorem minGap_pos (hK : 2 ≤ K) (g : ℕ → Fin K → ℝ) (n : ℕ)
    (hUnique : UniqueBest (arms_pos hK) g n) : 0 < minGap hK g n := by
  obtain ⟨k, hk, heq⟩ := minGap_attained hK g n
  rw [heq]
  exact div_pos (sub_pos.mpr (hUnique k hk)) (Nat.cast_pos.mpr (horizon_pos hK g n hUnique))

theorem competitorGap_le_one (hK : 0 < K) (g : ℕ → Fin K → ℝ) (n : ℕ)
    (hn : 0 < n) (hg : ∀ t < n, ∀ k, 0 ≤ g t k ∧ g t k ≤ 1) (k : Fin K) :
    competitorGap hK g n k ≤ 1 := by
  apply (div_le_one (Nat.cast_pos.mpr hn)).2
  have hbest := cumulative_le_horizon g n hg (best hK g n)
  have hk := cumulative_nonneg g n hg k
  linarith

theorem minGap_le_one (hK : 2 ≤ K) (g : ℕ → Fin K → ℝ) (n : ℕ)
    (hUnique : UniqueBest (arms_pos hK) g n)
    (hg : ∀ t < n, ∀ k, 0 ≤ g t k ∧ g t k ≤ 1) : minGap hK g n ≤ 1 := by
  obtain ⟨k, _, heq⟩ := minGap_attained hK g n
  rw [heq]
  exact competitorGap_le_one (arms_pos hK) g n (horizon_pos hK g n hUnique) hg k

/-- Every competitor is separated in cumulative reward by at least `n * minGap`. -/
theorem gap_separation (hK : 2 ≤ K) (g : ℕ → Fin K → ℝ) (n : ℕ)
    (hUnique : UniqueBest (arms_pos hK) g n) (k : Fin K)
    (hk : k ≠ best (arms_pos hK) g n) :
    (n : ℝ) * minGap hK g n ≤
      cumulative g n (best (arms_pos hK) g n) - cumulative g n k := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (horizon_pos hK g n hUnique).ne'
  calc
    _ ≤ (n : ℝ) * competitorGap (arms_pos hK) g n k :=
      mul_le_mul_of_nonneg_left (minGap_le_gap hK g n k hk) (Nat.cast_nonneg n)
    _ = _ := mul_div_cancel₀ _ hn

/-- The manuscript assigns the best arm the same gap as its closest competitor. -/
noncomputable def armGap (hK : 2 ≤ K) (g : ℕ → Fin K → ℝ) (n : ℕ) (k : Fin K) : ℝ :=
  if k = best (arms_pos hK) g n then minGap hK g n
  else competitorGap (arms_pos hK) g n k

@[simp]
theorem armGap_best (hK : 2 ≤ K) (g : ℕ → Fin K → ℝ) (n : ℕ) :
    armGap hK g n (best (arms_pos hK) g n) = minGap hK g n := by
  simp [armGap]

theorem armGap_of_ne (hK : 2 ≤ K) (g : ℕ → Fin K → ℝ) (n : ℕ)
    (k : Fin K) (hk : k ≠ best (arms_pos hK) g n) :
    armGap hK g n k = competitorGap (arms_pos hK) g n k := by
  simp [armGap, hk]

theorem minGap_le_armGap (hK : 2 ≤ K) (g : ℕ → Fin K → ℝ) (n : ℕ) (k : Fin K) :
    minGap hK g n ≤ armGap hK g n k := by
  by_cases hk : k = best (arms_pos hK) g n
  · simp [hk]
  · rw [armGap_of_ne hK g n k hk]
    exact minGap_le_gap hK g n k hk

/-- Mathlib's actual permutation sorting the duplicated arm gaps. -/
noncomputable def gapOrder (hK : 2 ≤ K) (g : ℕ → Fin K → ℝ) (n : ℕ) : Equiv.Perm (Fin K) :=
  Tuple.sort (armGap hK g n)

/-- Sorted realized gaps, with manuscript rank `i.val + 1`. -/
noncomputable def sortedProfile (hK : 2 ≤ K) (g : ℕ → Fin K → ℝ) (n : ℕ) : Fin K → ℝ :=
  armGap hK g n ∘ gapOrder hK g n

theorem sortedProfile_permutation (hK : 2 ≤ K) (g : ℕ → Fin K → ℝ) (n : ℕ) :
    ∃ sigma : Equiv.Perm (Fin K), sortedProfile hK g n = armGap hK g n ∘ sigma :=
  ⟨gapOrder hK g n, rfl⟩

theorem sortedProfile_monotone (hK : 2 ≤ K) (g : ℕ → Fin K → ℝ) (n : ℕ) :
    Monotone (sortedProfile hK g n) :=
  Tuple.monotone_sort (armGap hK g n)

theorem sortedProfile_first (hK : 2 ≤ K) (g : ℕ → Fin K → ℝ) (n : ℕ) :
    sortedProfile hK g n (firstRank hK) = minGap hK g n := by
  let sigma := gapOrder hK g n
  apply le_antisymm
  · calc
      _ ≤ sortedProfile hK g n (sigma.symm (best (arms_pos hK) g n)) :=
        sortedProfile_monotone hK g n (Nat.zero_le _)
      _ = _ := by simp [sortedProfile, sigma]
  · exact minGap_le_armGap hK g n (sigma (firstRank hK))

theorem sortedProfile_second (hK : 2 ≤ K) (g : ℕ → Fin K → ℝ) (n : ℕ) :
    sortedProfile hK g n (secondRank hK) = minGap hK g n := by
  obtain ⟨k, hk, hgap⟩ := minGap_attained hK g n
  let sigma := gapOrder hK g n
  let i := sigma.symm (best (arms_pos hK) g n)
  let j := sigma.symm k
  have hij : i ≠ j := by
    intro heq
    have hb := congrArg sigma heq
    simp only [i, j, Equiv.apply_symm_apply] at hb
    exact hk hb.symm
  have hi : sortedProfile hK g n i = minGap hK g n := by
    simp [sortedProfile, i, sigma]
  have hj : sortedProfile hK g n j = minGap hK g n := by
    simp only [sortedProfile, Function.comp_apply, j, sigma, Equiv.apply_symm_apply,
      armGap_of_ne hK g n k hk, hgap]
  have hlarge : secondRank hK ≤ i ∨ secondRank hK ≤ j := by
    by_cases hsi : secondRank hK ≤ i
    · exact Or.inl hsi
    · apply Or.inr
      have hi0 : i.val = 0 := by
        change ¬1 ≤ i.val at hsi
        omega
      have hj0 : j.val ≠ 0 := by
        intro hj0
        apply hij
        exact Fin.ext (by omega)
      change 1 ≤ j.val
      omega
  apply le_antisymm
  · rcases hlarge with hlarge | hlarge
    · exact (sortedProfile_monotone hK g n hlarge).trans_eq hi
    · exact (sortedProfile_monotone hK g n hlarge).trans_eq hj
  · exact minGap_le_armGap hK g n (sigma (secondRank hK))

theorem sortedProfile_duplicate (hK : 2 ≤ K) (g : ℕ → Fin K → ℝ) (n : ℕ) :
    sortedProfile hK g n (firstRank hK) = sortedProfile hK g n (secondRank hK) := by
  rw [sortedProfile_first, sortedProfile_second]

/-- The existing uniform complexity, evaluated on the actual sorted gap profile. -/
noncomputable def complexity (hK : 2 ≤ K) (g : ℕ → Fin K → ℝ) (n : ℕ) : ℝ :=
  BestOfBothWorlds.H_UNIF hK (sortedProfile hK g n)

theorem complexity_eq (hK : 2 ≤ K) (g : ℕ → Fin K → ℝ) (n : ℕ) :
    complexity hK g n = (K : ℝ) / (minGap hK g n) ^ 2 := by
  simp only [complexity, H_UNIF, sortedProfile_first]

theorem complexity_pos (hK : 2 ≤ K) (g : ℕ → Fin K → ℝ) (n : ℕ)
    (hUnique : UniqueBest (arms_pos hK) g n) : 0 < complexity hK g n := by
  rw [complexity_eq]
  exact div_pos (Nat.cast_pos.mpr (arms_pos hK)) (pow_pos (minGap_pos hK g n hUnique) 2)

end BestOfBothWorlds.RealizedGaps
