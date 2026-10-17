module

public import BestOfBothWorlds.RealizedGaps
public import BestOfBothWorlds.LowerBoundStochasticGaps
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-! Labelled problem classes and deterministic good-table gap certificates. -/

@[expose] public section

namespace BestOfBothWorlds.LowerBounds

variable {K : ℕ}

/-- The manuscript's labelled class: one exceptional label uses the smallest
reference gap, while every other label retains its own reference gap. -/
def LabelledGapClass (hK : 2 ≤ K) (gap actual : Fin K → ℝ) (c : ℝ) : Prop :=
  ∃ exceptional : Fin K,
    gap (firstRank hK) / c ≤ actual exceptional ∧
    actual exceptional ≤ c * gap (firstRank hK) ∧
    ∀ j, j ≠ exceptional → gap j / c ≤ actual j ∧ actual j ≤ c * gap j

/-- Deterministic adversarial tables use the already verified realized gaps
and the same smallest-index best-arm convention as the upper bounds. -/
def AdversarialGapClass (hK : 2 ≤ K) (gap : Fin K → ℝ) (c : ℝ)
    (g : ℕ → Fin K → ℝ) (n : ℕ) : Prop :=
  (∀ t < n, ∀ j, g t j ∈ Set.Icc (0 : ℝ) 1) ∧
  RealizedGaps.UniqueBest (RealizedGaps.arms_pos hK) g n ∧
  LabelledGapClass hK gap (RealizedGaps.armGap hK g n) c

/-- The actual constructed stochastic mean gaps belong to Delta_4. -/
theorem sto_actual_class_four (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    (k : Fin K) (hk : k ≠ firstRank hK) :
    LabelledGapClass hK gap
      (RealizedGaps.armGap hK (fun _ => stoMean hK gap k) 1) 4 := by
  rw [← stoGap_eq_actual_mean_gaps hK gap hpos hsorted k hk]
  exact ⟨k, stoGap_class_four hK gap hpos hsorted k⟩

/-- A table with positive normalized differences from b has actual unique
best arm b. This bridges deterministic margin calculations to realized gaps. -/
theorem best_and_unique_of_positive_average_differences
    (hK : 2 ≤ K) (g : ℕ → Fin K → ℝ) (n : ℕ) (hn : 0 < n)
    (b : Fin K)
    (hmargin : ∀ j, j ≠ b → 0 <
      (RealizedGaps.cumulative g n b - RealizedGaps.cumulative g n j) / (n : ℝ)) :
    RealizedGaps.best (RealizedGaps.arms_pos hK) g n = b ∧
      RealizedGaps.UniqueBest (RealizedGaps.arms_pos hK) g n := by
  have hstrict : ∀ j, j ≠ b → RealizedGaps.cumulative g n j < RealizedGaps.cumulative g n b := by
    intro j hj
    exact sub_pos.mp ((div_pos_iff_of_pos_right (Nat.cast_pos.mpr hn)).mp (hmargin j hj))
  exact ⟨RealizedGaps.best_eq_of_strict _ g n b hstrict,
    RealizedGaps.uniqueBest_of_strict _ g n b hstrict⟩

/-- A generic deterministic labelled-class certificate. Its pairwise premises
are discharged by the concrete good-table calculations in the two appendices. -/
theorem labelled_class_of_pairwise_bounds
    (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    (c : ℝ) (hc : 0 < c) (g : ℕ → Fin K → ℝ) (n : ℕ) (hn : 0 < n)
    (b a : Fin K) (hba : b = firstRank hK ∨ b = a)
    (hpair : ∀ j, j ≠ b →
      (if j = a then gap (firstRank hK) else gap j) / c ≤
        (RealizedGaps.cumulative g n b - RealizedGaps.cumulative g n j) / (n : ℝ) ∧
      (RealizedGaps.cumulative g n b - RealizedGaps.cumulative g n j) / (n : ℝ) ≤
        c * (if j = a then gap (firstRank hK) else gap j))
    (hnear : ∃ j, j ≠ b ∧
      (RealizedGaps.cumulative g n b - RealizedGaps.cumulative g n j) / (n : ℝ) ≤
        c * gap (firstRank hK)) :
    RealizedGaps.best (RealizedGaps.arms_pos hK) g n = b ∧
    RealizedGaps.UniqueBest (RealizedGaps.arms_pos hK) g n ∧
    LabelledGapClass hK gap (RealizedGaps.armGap hK g n) c := by
  classical
  have hreference : ∀ j, gap (firstRank hK) ≤ if j = a then gap (firstRank hK) else gap j := by
    intro j
    split_ifs
    · exact le_rfl
    · exact hsorted (Nat.zero_le j.val)
  have hmargin : ∀ j, j ≠ b → 0 <
      (RealizedGaps.cumulative g n b - RealizedGaps.cumulative g n j) / (n : ℝ) := by
    intro j hj
    exact lt_of_lt_of_le (div_pos (hpos.trans_le (hreference j)) hc) (hpair j hj).1
  obtain ⟨hbest, hunique⟩ := best_and_unique_of_positive_average_differences hK g n hn b hmargin
  have hcomp : ∀ j, RealizedGaps.competitorGap (RealizedGaps.arms_pos hK) g n j =
      (RealizedGaps.cumulative g n b - RealizedGaps.cumulative g n j) / (n : ℝ) := by
    intro j
    simp only [RealizedGaps.competitorGap, hbest]
  have hmin : gap (firstRank hK) / c ≤ RealizedGaps.minGap hK g n ∧
      RealizedGaps.minGap hK g n ≤ c * gap (firstRank hK) := by
    constructor
    · obtain ⟨j, hj, heq⟩ := RealizedGaps.minGap_attained hK g n
      have hjb : j ≠ b := by simpa only [hbest] using hj
      rw [heq, hcomp]
      exact (div_le_div_of_nonneg_right (hreference j) hc.le).trans (hpair j hjb).1
    · obtain ⟨j, hj, hjnear⟩ := hnear
      have hjbest : j ≠ RealizedGaps.best (RealizedGaps.arms_pos hK) g n := by
        simpa only [hbest] using hj
      exact (RealizedGaps.minGap_le_gap hK g n j hjbest).trans (by rwa [hcomp])
  have hactual : ∀ j, j ≠ b →
      RealizedGaps.armGap hK g n j =
      (RealizedGaps.cumulative g n b - RealizedGaps.cumulative g n j) / (n : ℝ) := by
    intro j hj
    rw [RealizedGaps.armGap_of_ne hK g n j (by simpa only [hbest] using hj), hcomp]
  have hbestgap : RealizedGaps.armGap hK g n b = RealizedGaps.minGap hK g n := by
    simpa only [hbest] using RealizedGaps.armGap_best hK g n
  refine ⟨hbest, hunique, a, ?_, ?_, ?_⟩
  · by_cases ha : a = b
    · simpa only [ha, hbestgap] using hmin.1
    · rw [hactual a ha]
      simpa only [ite_true] using (hpair a ha).1
  · by_cases ha : a = b
    · simpa only [ha, hbestgap] using hmin.2
    · rw [hactual a ha]
      simpa only [ite_true] using (hpair a ha).2
  · intro j hja
    by_cases hjb : j = b
    · subst j
      have hbfirst : b = firstRank hK := hba.resolve_right hja
      rw [hbestgap, hbfirst]
      exact hmin
    · rw [hactual j hjb]
      simpa only [hja, ite_false] using hpair j hjb

/-- Deviations of two complete arm sums give deviations of their normalized
difference. This concerns unobserved full-table rewards as well. -/
theorem normalized_pair_bounds {g : ℕ → Fin K → ℝ} {n : ℕ} (hn : 0 < n)
    (M : Fin K → ℝ) (d : ℝ) (b j : Fin K) (δ : ℝ)
    (hb : |RealizedGaps.cumulative g n b - M b| ≤ (n : ℝ) * d / 16)
    (hj : |RealizedGaps.cumulative g n j - M j| ≤ (n : ℝ) * d / 16)
    (hmean : M b - M j = (n : ℝ) * δ) :
    δ - d / 8 ≤
      (RealizedGaps.cumulative g n b - RealizedGaps.cumulative g n j) / (n : ℝ) ∧
    (RealizedGaps.cumulative g n b - RealizedGaps.cumulative g n j) / (n : ℝ) ≤
      δ + d / 8 := by
  obtain ⟨hbl, hbu⟩ := abs_le.mp hb
  obtain ⟨hjl, hju⟩ := abs_le.mp hj
  constructor
  · apply (le_div_iff₀ (Nat.cast_pos.mpr hn)).2
    nlinarith
  · apply (div_le_iff₀ (Nat.cast_pos.mpr hn)).2
    nlinarith

/-- The good-table margin calculation of Appendix E implies unique best arm1
and actual membership in Delta_4. The probability of this good event is handled
separately by full-table Hoeffding. -/
theorem bob_good_table_class_four (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    (g : ℕ → Fin K → ℝ) (n : ℕ) (hn : 0 < n)
    (hg : ∀ t < n, ∀ j, g t j ∈ Set.Icc (0 : ℝ) 1)
    (a : Fin K) (ha : a ≠ firstRank hK) (M : Fin K → ℝ) (b : ℝ)
    (hb : 3 * gap (firstRank hK) / 4 ≤ b ∧ b ≤ 17 * gap (firstRank hK) / 8)
    (hmean_a : M (firstRank hK) - M a = (n : ℝ) * b)
    (hmean_other : ∀ j, j ≠ firstRank hK → j ≠ a →
      M (firstRank hK) - M j = (n : ℝ) * gap j)
    (hgood : ∀ j, |RealizedGaps.cumulative g n j - M j| ≤
      (n : ℝ) * gap (firstRank hK) / 16) :
    RealizedGaps.best (RealizedGaps.arms_pos hK) g n = firstRank hK ∧
      AdversarialGapClass hK gap 4 g n := by
  have hselected := normalized_pair_bounds hn M (gap (firstRank hK))
    (firstRank hK) a b (hgood _) (hgood _) hmean_a
  have hpair : ∀ j, j ≠ firstRank hK →
      (if j = a then gap (firstRank hK) else gap j) / 4 ≤
        (RealizedGaps.cumulative g n (firstRank hK) - RealizedGaps.cumulative g n j) / (n : ℝ) ∧
      (RealizedGaps.cumulative g n (firstRank hK) - RealizedGaps.cumulative g n j) / (n : ℝ) ≤
        4 * (if j = a then gap (firstRank hK) else gap j) := by
    intro j hj
    by_cases hja : j = a
    · subst j
      simp only [↓reduceIte]
      constructor <;> linarith [hb.1, hb.2, hselected.1, hselected.2]
    · simp only [hja, ite_false]
      have hdiff := normalized_pair_bounds hn M (gap (firstRank hK))
        (firstRank hK) j (gap j) (hgood _) (hgood _) (hmean_other j hj hja)
      have hle : gap (firstRank hK) ≤ gap j := hsorted (Nat.zero_le j.val)
      constructor <;> linarith [hdiff.1, hdiff.2]
  have hnear : ∃ j, j ≠ firstRank hK ∧
      (RealizedGaps.cumulative g n (firstRank hK) - RealizedGaps.cumulative g n j) / (n : ℝ) ≤
        4 * gap (firstRank hK) := by
    refine ⟨a, ha, ?_⟩
    linarith [hb.2, hselected.2]
  obtain ⟨hbest, hunique, hclass⟩ := labelled_class_of_pairwise_bounds hK gap hpos hsorted
    4 (by norm_num) g n hn (firstRank hK) a (Or.inl rfl) hpair hnear
  exact ⟨hbest, hg, hunique, hclass⟩

end BestOfBothWorlds.LowerBounds
