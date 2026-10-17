module

public import BestOfBothWorlds.GapComplexity
public import BestOfBothWorlds.RealizedGaps
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Lean.Elab.Tactic.Omega

/-!
The actual labelled and sorted gaps of Appendix E's stochastic construction.
An explicit permutation moves the selected arm in front of the original best
arm and preserves the order of every other label. Thus ties require no strict
ordering assumption.
-/

@[expose] public section

namespace BestOfBothWorlds.LowerBounds

variable {K : ℕ}

/-- Appendix E's BASE means, indexed by the original labels. -/
noncomputable def baseMean (hK : 2 ≤ K) (gap : Fin K → ℝ) (j : Fin K) : ℝ :=
  if j = firstRank hK then 1 / 2 else 1 / 2 - gap j

/-- Only the selected label changes in the stationary STO instance. -/
noncomputable def stoMean (hK : 2 ≤ K) (gap : Fin K → ℝ) (k j : Fin K) : ℝ :=
  if j = k then 1 / 2 + gap (firstRank hK) / 4 else baseMean hK gap j

/-- The STO gap profile, with the best arm's duplicated minimum encoded. -/
noncomputable def stoGap (hK : 2 ≤ K) (gap : Fin K → ℝ) (k j : Fin K) : ℝ :=
  if j = firstRank hK ∨ j = k then gap (firstRank hK) / 4
  else gap j + gap (firstRank hK) / 4

/-- The constructed means are valid Bernoulli parameters. -/
theorem stoMean_mem_Ioo (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    (hsmall : ∀ j, gap j ≤ 1 / 8) (k j : Fin K) :
    stoMean hK gap k j ∈ Set.Ioo (0 : ℝ) 1 := by
  have hj := gap_pos_of_sorted hK gap hpos hsorted j
  have hfirst := hsmall (firstRank hK)
  unfold stoMean baseMean
  split_ifs <;> constructor <;> linarith [hsmall j]

/-- The selected label is uniquely best, including K=2 and tied other gaps. -/
theorem stoMean_strict_best (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    (k j : Fin K) (hj : j ≠ k) :
    stoMean hK gap k j < stoMean hK gap k k := by
  have hgap := gap_pos_of_sorted hK gap hpos hsorted j
  simp only [stoMean, hj, ↓reduceIte]
  unfold baseMean
  split_ifs <;> linarith

/-- Every non-best STO gap is the actual difference of its constructed means. -/
theorem stoGap_eq_mean_difference (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (k j : Fin K) (hk : k ≠ firstRank hK) (hj : j ≠ k) :
    stoGap hK gap k j = stoMean hK gap k k - stoMean hK gap k j := by
  unfold stoGap stoMean baseMean
  split_ifs <;> simp_all
  all_goals ring

/-- The reference best label attains the new duplicated minimum. -/
theorem stoGap_first_and_selected (hK : 2 ≤ K) (gap : Fin K → ℝ) (k : Fin K) :
    stoGap hK gap k (firstRank hK) = gap (firstRank hK) / 4 ∧
    stoGap hK gap k k = gap (firstRank hK) / 4 := by simp [stoGap]

/-- All competitor gaps are at least the attained minimum. -/
theorem stoGap_min_le (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    (k j : Fin K) : gap (firstRank hK) / 4 ≤ stoGap hK gap k j := by
  have hj := gap_pos_of_sorted hK gap hpos hsorted j
  unfold stoGap
  split_ifs <;> linarith

/-- The finite problem-class inequalities for the actual STO labelled gaps.
The selected arm is the exceptional label in Delta_4. -/
theorem stoGap_class_four (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    (k : Fin K) :
    gap (firstRank hK) / 4 ≤ stoGap hK gap k k ∧
    stoGap hK gap k k ≤ 4 * gap (firstRank hK) ∧
    ∀ j, j ≠ k → gap j / 4 ≤ stoGap hK gap k j ∧
      stoGap hK gap k j ≤ 4 * gap j := by
  have hgp := gap_pos_of_sorted hK gap hpos hsorted
  refine ⟨?_, ?_, ?_⟩
  · simp [stoGap]
  · simp only [stoGap, or_true, ite_true]; linarith
  · intro j hj
    have hle : gap (firstRank hK) ≤ gap j := hsorted (Nat.zero_le j.val)
    unfold stoGap
    by_cases hfirst : j = firstRank hK
    · subst j
      simp only [true_or, ite_true]
      constructor <;> linarith
    · simp only [hfirst, hj, or_self, ite_false]
      constructor <;> linarith [hgp j]

/-- A permutation sending rank1 to the selected label, rank2 to the original
best, and leaving all remaining labels in their original increasing order. -/
def stoOrderFun (k r : Fin K) : Fin K :=
  if hr : r.val = 0 then k
  else if r.val ≤ k.val then ⟨r.val - 1, by omega⟩ else r

theorem stoOrderFun_injective (k : Fin K) : Function.Injective (stoOrderFun k) := by
  intro a b hab
  have heq := congrArg Fin.val hab
  simp only [stoOrderFun] at heq
  split_ifs at heq <;> apply Fin.ext <;> simp_all <;> omega

/-- The explicit STO gap-order permutation. -/
noncomputable def stoOrder (k : Fin K) : Equiv.Perm (Fin K) :=
  Equiv.ofBijective (stoOrderFun k)
    ((Finite.injective_iff_bijective).1 (stoOrderFun_injective k))

private theorem selected_val_pos (hK : 2 ≤ K) (k : Fin K)
    (hk : k ≠ firstRank hK) : 0 < k.val := by
  have hn : k.val ≠ 0 := by
    intro heq
    apply hk
    exact Fin.ext heq
  omega

/-- The first two permuted entries are precisely the duplicated new minimum. -/
theorem stoGap_order_small (hK : 2 ≤ K) (gap : Fin K → ℝ) (k r : Fin K)
    (hk : k ≠ firstRank hK) (hr : r.val ≤ 1) :
    stoGap hK gap k (stoOrder k r) = gap (firstRank hK) / 4 := by
  have hkpos := selected_val_pos hK k hk
  change stoGap hK gap k (stoOrderFun k r) = _
  by_cases hz : r.val = 0
  · simp [stoOrderFun, hz, stoGap]
  · have hrv : r.val = 1 := by omega
    have hle : r.val ≤ k.val := by omega
    have heq : (⟨r.val - 1, by omega⟩ : Fin K) = firstRank hK := by
      apply Fin.ext
      simp [hrv, firstRank]
    simp [stoOrderFun, hz, hle, heq, stoGap]

/-- Beyond the first two positions, the original nonexceptional gap appears
with the additive mean shift. -/
theorem stoGap_order_large (hK : 2 ≤ K) (gap : Fin K → ℝ) (k r : Fin K)
    (hr : 2 ≤ r.val) :
    stoGap hK gap k (stoOrder k r) =
      gap (stoOrderFun k r) + gap (firstRank hK) / 4 := by
  change stoGap hK gap k (stoOrderFun k r) = _
  have hf : stoOrderFun k r ≠ firstRank hK := by
    intro h
    have hval := congrArg Fin.val h
    simp only [stoOrderFun, firstRank] at hval
    split_ifs at hval <;> (try dsimp only at hval) <;> omega
  have hk : stoOrderFun k r ≠ k := by
    intro h
    have hval := congrArg Fin.val h
    simp only [stoOrderFun] at hval
    split_ifs at hval <;> (try dsimp only at hval) <;> omega
  simp [stoGap, hf, hk]

private theorem stoOrderFun_monotone_positive (k : Fin K) {r s : Fin K}
    (hr : 0 < r.val) (hrs : r ≤ s) : stoOrderFun k r ≤ stoOrderFun k s := by
  change (stoOrderFun k r).val ≤ (stoOrderFun k s).val
  have hrv : r.val ≤ s.val := hrs
  simp only [stoOrderFun]
  split_ifs <;> (try dsimp only) <;> omega

/-- The explicit permutation really sorts the constructed actual gaps. -/
theorem stoGap_order_monotone (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    (k : Fin K) (hk : k ≠ firstRank hK) :
    Monotone (stoGap hK gap k ∘ stoOrder k) := by
  intro r s hrs
  dsimp only [Function.comp_apply]
  by_cases hr : r.val ≤ 1
  · rw [stoGap_order_small hK gap k r hk hr]
    exact stoGap_min_le hK gap hpos hsorted k _
  · have hrlarge : 2 ≤ r.val := by omega
    have hslarge : 2 ≤ s.val := by have h := hrs; change r.val ≤ s.val at h; omega
    rw [stoGap_order_large hK gap k r hrlarge, stoGap_order_large hK gap k s hslarge]
    exact add_le_add (hsorted (stoOrderFun_monotone_positive k (by omega) hrs)) le_rfl

/-- Identification with Mathlib's sorted actual-gap tuple. -/
theorem stoGap_order_eq_sort (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    (k : Fin K) (hk : k ≠ firstRank hK) :
    stoGap hK gap k ∘ stoOrder k =
      stoGap hK gap k ∘ Tuple.sort (stoGap hK gap k) :=
  Tuple.comp_sort_eq_comp_iff_monotone.mpr
    (stoGap_order_monotone hK gap hpos hsorted k hk)

/-- The actual sorted STO complexity is controlled by the reference complexity.
This statement uses the constructed gaps after sorting, not the reference gaps
in place of the actual stochastic problem. -/
theorem H_BOB_stoGap_le_sixteen (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    (hduplicate : gap (firstRank hK) = gap (secondRank hK))
    (k : Fin K) (hk : k ≠ firstRank hK) :
    H_BOB hK (stoGap hK gap k ∘ Tuple.sort (stoGap hK gap k)) ≤
      16 * H_BOB hK gap := by
  classical
  rw [← stoGap_order_eq_sort hK gap hpos hsorted k hk]
  let d := gap (firstRank hK)
  let Q := (Finset.univ : Finset (Fin K)).sup'
    ⟨firstRank hK, Finset.mem_univ _⟩
    (fun i => ((i.val + 1 : ℕ) : ℝ) / gap i)
  let h := stoGap hK gap k ∘ stoOrder k
  have hd : 0 < d := hpos
  have hgp := gap_pos_of_sorted hK gap hpos hsorted
  have hQ : ∀ i : Fin K, ((i.val + 1 : ℕ) : ℝ) / gap i ≤ Q :=
    fun i => Finset.le_sup' (fun j : Fin K => ((j.val + 1 : ℕ) : ℝ) / gap j) (Finset.mem_univ i)
  have htwo : 2 / d ≤ Q := by
    have ht := hQ (secondRank hK)
    change (2 : ℝ) / gap (secondRank hK) ≤ Q at ht
    simpa only [← hduplicate] using ht
  have hQpos : 0 < Q := lt_of_lt_of_le (div_pos (by norm_num) hd) htwo
  have hfirst : h (firstRank hK) = d / 4 :=
    stoGap_order_small hK gap k _ hk (by simp [firstRank])
  have hbound : ∀ r : Fin K, ((r.val + 1 : ℕ) : ℝ) / h r ≤ 4 * Q := by
    intro r
    by_cases hr : r.val ≤ 1
    · have heq : h r = d / 4 := stoGap_order_small hK gap k r hk hr
      have hnum : ((r.val + 1 : ℕ) : ℝ) ≤ 2 := by exact_mod_cast (show r.val + 1 ≤ 2 by omega)
      rw [heq]
      calc
        _ ≤ 2 / (d / 4) := div_le_div_of_nonneg_right hnum (by positivity)
        _ = 4 * (2 / d) := by ring
        _ ≤ 4 * Q := mul_le_mul_of_nonneg_left htwo (by norm_num)
    · have hrl : 2 ≤ r.val := by omega
      let f := stoOrderFun k r
      have hf : r.val ≤ 2 * (f.val + 1) - 1 := by
        dsimp [f, stoOrderFun]
        split_ifs <;> (try dsimp only) <;> omega
      have hnum : ((r.val + 1 : ℕ) : ℝ) ≤ 2 * ((f.val + 1 : ℕ) : ℝ) := by
        exact_mod_cast (show r.val + 1 ≤ 2 * (f.val + 1) by omega)
      have hh : h r = gap f + d / 4 := stoGap_order_large hK gap k r hrl
      have hden : gap f ≤ h r := by rw [hh]; linarith
      calc
        _ ≤ ((r.val + 1 : ℕ) : ℝ) / gap f :=
          div_le_div_of_nonneg_left (Nat.cast_nonneg _) (hgp f) hden
        _ ≤ (2 * ((f.val + 1 : ℕ) : ℝ)) / gap f :=
          div_le_div_of_nonneg_right hnum (hgp f).le
        _ = 2 * (((f.val + 1 : ℕ) : ℝ) / gap f) := by ring
        _ ≤ 2 * Q := mul_le_mul_of_nonneg_left (hQ f) (by norm_num)
        _ ≤ 4 * Q := by linarith
  have hsup : (Finset.univ : Finset (Fin K)).sup'
      ⟨firstRank hK, Finset.mem_univ _⟩
      (fun r => ((r.val + 1 : ℕ) : ℝ) / h r) ≤ 4 * Q :=
    Finset.sup'_le _ _ (fun r _ => hbound r)
  change (1 / h (firstRank hK)) * _ ≤ 16 * ((1 / d) * Q)
  rw [hfirst]
  calc
    _ ≤ (1 / (d / 4)) * (4 * Q) := mul_le_mul_of_nonneg_left hsup (by positivity)
    _ = 16 * ((1 / d) * Q) := by ring

/-- The explicit profile is exactly the established arm-gap definition applied
to the constructed vector of stochastic means. The one-round constant table
has the same gaps as that mean vector. -/
theorem stoGap_eq_actual_mean_gaps (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    (k : Fin K) (hk : k ≠ firstRank hK) :
    stoGap hK gap k = RealizedGaps.armGap hK (fun _ => stoMean hK gap k) 1 := by
  let g : ℕ → Fin K → ℝ := fun _ => stoMean hK gap k
  have hbest : RealizedGaps.best (RealizedGaps.arms_pos hK) g 1 = k := by
    apply RealizedGaps.best_eq_of_strict
    intro j hj
    simpa [g, RealizedGaps.cumulative] using stoMean_strict_best hK gap hpos hsorted k j hj
  have hcomp : ∀ j, j ≠ k →
      RealizedGaps.competitorGap (RealizedGaps.arms_pos hK) g 1 j = stoGap hK gap k j := by
    intro j hj
    rw [stoGap_eq_mean_difference hK gap k j hk hj]
    simp [RealizedGaps.competitorGap, RealizedGaps.cumulative, hbest, g]
  have hmin : RealizedGaps.minGap hK g 1 = gap (firstRank hK) / 4 := by
    apply le_antisymm
    · have hb : firstRank hK ≠ RealizedGaps.best (RealizedGaps.arms_pos hK) g 1 := by
        simpa only [hbest] using hk.symm
      have hh := RealizedGaps.minGap_le_gap hK g 1 (firstRank hK) hb
      simpa only [hcomp _ hk.symm, (stoGap_first_and_selected hK gap k).1] using hh
    · obtain ⟨j, hj, heq⟩ := RealizedGaps.minGap_attained hK g 1
      have hjk : j ≠ k := by simpa only [hbest] using hj
      rw [heq, hcomp j hjk]
      exact stoGap_min_le hK gap hpos hsorted k j
  funext j
  change stoGap hK gap k j = RealizedGaps.armGap hK g 1 j
  by_cases hj : j = k
  · subst j
    simp only [RealizedGaps.armGap, hbest, ↓reduceIte, hmin]
    exact (stoGap_first_and_selected hK gap k).2
  · have hjb : j ≠ RealizedGaps.best (RealizedGaps.arms_pos hK) g 1 := by
      simpa only [hbest] using hj
    rw [RealizedGaps.armGap_of_ne hK g 1 j hjb, hcomp j hj]

/-- The complexity comparison for the constructed STO's actual sorted mean
gaps, reusing the same arm-gap and sorting definitions as the upper bounds. -/
theorem H_BOB_actual_sto_le_sixteen (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    (hduplicate : gap (firstRank hK) = gap (secondRank hK))
    (k : Fin K) (hk : k ≠ firstRank hK) :
    H_BOB hK (RealizedGaps.sortedProfile hK (fun _ => stoMean hK gap k) 1) ≤
      16 * H_BOB hK gap := by
  simpa only [RealizedGaps.sortedProfile, RealizedGaps.gapOrder,
    ← stoGap_eq_actual_mean_gaps hK gap hpos hsorted k hk] using
    H_BOB_stoGap_le_sixteen hK gap hpos hsorted hduplicate k hk

end BestOfBothWorlds.LowerBounds
