module

public import BestOfBothWorlds.LowerBoundEnvironments
public import BestOfBothWorlds.LowerBoundGapClasses
public import BestOfBothWorlds.LowerBoundConsequences
public import BestOfBothWorlds.LowerBoundTesting
public import BestOfBothWorlds.FullTableConcentration
public import BestOfBothWorlds.SeededLearnerCounts
public import BestOfBothWorlds.BernoulliInformation
public import BestOfBothWorlds.SeededLearnerPrefix
public import BestOfBothWorlds.SeededChangeOfMeasure

/-!
The Appendix D construction for the adversarial lower bound. Both equal phases
have floor(n/2) rounds, and an odd final round is retained with zero rewards.
All table laws are chosen before interaction and independently of the private
learner seed. Full-table good events are never used to condition a transcript.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open BestOfBothWorlds.SeededLearner
open BestOfBothWorlds.SeededLearner.Learner
open scoped BigOperators NNReal

namespace BestOfBothWorlds.LowerBounds

variable {K : ℕ}

/-- The Bernoulli information cost of the Appendix D perturbation. -/
theorem adversarial_binaryKL_bound {d D : ℝ} (hd : 0 < d) (hle : d ≤ D)
    (hD : D ≤ 1 / 8) :
    BernoulliInformation.binaryKL (1 / 2 - D) (1 / 2 - D + 2 * d) ≤ 32 * d ^ 2 := by
  let p := 1 / 2 - D
  let q := 1 / 2 - D + 2 * d
  have hdsmall : d ≤ 1 / 8 := hle.trans hD
  have hp : (3 : ℝ) / 8 ≤ p ∧ p ≤ 5 / 8 := by dsimp [p]; constructor <;> linarith
  have hq : (3 : ℝ) / 8 ≤ q ∧ q ≤ 5 / 8 := by dsimp [q]; constructor <;> linarith
  have hden : 0 < q * (1 - q) := mul_pos (by linarith [hq.1]) (by linarith [hq.2])
  have hprod : (1 : ℝ) / 8 ≤ q * (1 - q) := by
    have hh := mul_nonneg (sub_nonneg.mpr hq.1) (sub_nonneg.mpr hq.2)
    nlinarith
  have hchi := BernoulliInformation.binaryKL_le_chiSquare
    (by linarith [hp.1] : 0 ≤ p) (by linarith [hp.2] : p ≤ 1)
    (by linarith [hq.1] : 0 < q) (by linarith [hq.2] : q < 1)
  apply hchi.trans
  apply (div_le_iff₀ hden).2
  have hnum : (p - q) ^ 2 = 4 * d ^ 2 := by dsimp [p, q]; ring
  rw [hnum]
  have hm := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 32 * d ^ 2 by positivity)
  nlinarith

open scoped Classical in
theorem prefix_sum_const (n m : ℕ) (hm : m ≤ n) (a : ℝ) :
    (∑ t : Fin n, if t.val < m then a else 0) = (m : ℝ) * a := by
  rw [← Finset.sum_filter]
  change (∑ _t ∈ prefixRounds n m, a) = _
  simp only [Finset.sum_const, nsmul_eq_mul, prefixRounds_card n m hm]

/-- Exact finite two-phase summation, with the optional zero padding retained. -/
theorem two_phase_sum (n : ℕ) (a b : ℝ) :
    (∑ t : Fin n, if t.val < n / 2 then a else if t.val < 2 * (n / 2) then b else 0) =
      ((n / 2 : ℕ) : ℝ) * a + ((n / 2 : ℕ) : ℝ) * b := by
  classical
  have ht : ∀ t : Fin n,
      (if t.val < n / 2 then a else if t.val < 2 * (n / 2) then b else 0) =
      (if t.val < n / 2 then a - b else 0) +
        (if t.val < 2 * (n / 2) then b else 0) := by
    intro t
    by_cases h₁ : t.val < n / 2
    · have h₂ : t.val < 2 * (n / 2) := by omega
      simp only [h₁, h₂, ↓reduceIte]
      ring
    · by_cases h₂ : t.val < 2 * (n / 2) <;> simp [h₁, h₂]
  rw [Finset.sum_congr rfl (fun t _ => ht t), Finset.sum_add_distrib,
    prefix_sum_const n (n / 2) (Nat.div_le_self n 2),
    prefix_sum_const n (2 * (n / 2)) (by omega)]
  push_cast
  ring

/-- The exact deterministic expected total in ADV1 or ADV2. -/
noncomputable def adversarialExpected (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (n : ℕ) (k : Fin K) (modified : Bool) (j : Fin K) : ℝ :=
  ((n / 2 : ℕ) : ℝ) *
      (if modified = true ∧ j = k then 1 / 2 - gap k + 2 * gap (firstRank hK)
       else baseMean hK gap j) +
    ((n / 2 : ℕ) : ℝ) * (if j = k then gap k - gap (firstRank hK) else 0)

theorem adversarialEntries_integral (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    (hsmall : ∀ j, gap j ≤ 1 / 8) (n : ℕ) (k : Fin K) (modified : Bool)
    (t : Fin n) (j : Fin K) :
    (∫ x, x.val ∂adversarialEntries hK gap hpos hsorted hsmall n k modified t j) =
      if t.val < n / 2 then
        (if modified = true ∧ j = k then 1 / 2 - gap k + 2 * gap (firstRank hK)
         else baseMean hK gap j)
      else if t.val < 2 * (n / 2) then
        (if j = k then gap k - gap (firstRank hK) else 0) else 0 := by
  classical
  by_cases ht : t.val < n / 2
  · by_cases hc : modified = true ∧ j = k
    · simp only [adversarialEntries, ht, hc, and_self, ↓reduceIte]
      rw [integral_alphabetBernoulli]
      rfl
    · simp only [adversarialEntries, ht, hc, ↓reduceIte]
      exact baseEntries_integral hK gap hpos hsorted hsmall n t j
  · by_cases hphase : t.val < 2 * (n / 2)
    · by_cases hj : j = k
      · simp [adversarialEntries, ht, hphase, hj, suffixReward]
      · simp [adversarialEntries, ht, hphase, hj, zeroReward]
    · simp [adversarialEntries, ht, hphase, zeroReward]

/-- Expected cumulative rewards are computed under the actual complete table law. -/
theorem adversarial_tableExpectedTotal (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    (hsmall : ∀ j, gap j ≤ 1 / 8) (n : ℕ) (k : Fin K) (modified : Bool) (j : Fin K) :
    tableExpectedTotal Subtype.val
      (adversarialEntries hK gap hpos hsorted hsmall n k modified) j =
      adversarialExpected hK gap n k modified j := by
  rw [tableExpectedTotal_eq_sum_entry_integrals]
  simp_rw [adversarialEntries_integral]
  exact two_phase_sum n _ _

/-- The original best arm's expected total is unchanged in both environments. -/
theorem adversarialExpected_first (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (n : ℕ) (k : Fin K) (hk : k ≠ firstRank hK) (modified : Bool) :
    adversarialExpected hK gap n k modified (firstRank hK) = ((n / 2 : ℕ) : ℝ) / 2 := by
  simp [adversarialExpected, baseMean, hk.symm]
  ring

theorem adversarialExpected_selected (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (n : ℕ) (k : Fin K) (hk : k ≠ firstRank hK) (modified : Bool) :
    adversarialExpected hK gap n k modified k =
      ((n / 2 : ℕ) : ℝ) * (1 / 2 + if modified then gap (firstRank hK) else -gap (firstRank hK)) := by
  cases modified <;> simp [adversarialExpected, baseMean, hk] <;> ring

theorem adversarialExpected_other (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (n : ℕ) (k j : Fin K) (hj : j ≠ firstRank hK) (hjk : j ≠ k) (modified : Bool) :
    adversarialExpected hK gap n k modified j = ((n / 2 : ℕ) : ℝ) * (1 / 2 - gap j) := by
  simp [adversarialExpected, baseMean, hj, hjk]

/-- Only the first floor(n/2) entries of an arm contribute Hoeffding variance;
the common deterministic suffix and the optional zero padding contribute zero. -/
theorem adversarial_centeredTotal_subGaussian (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    (hsmall : ∀ j, gap j ≤ 1 / 8) (n : ℕ) (k : Fin K) (modified : Bool) (j : Fin K) :
    HasSubgaussianMGF
      (fun g => tableTotal Subtype.val g j -
        tableExpectedTotal Subtype.val
          (adversarialEntries hK gap hpos hsorted hsmall n k modified) j)
      ((((n / 2 : ℕ) : ℝ≥0) / 4) : ℝ≥0)
      (SeededLearner.Learner.tableLaw
        (adversarialEntries hK gap hpos hsorted hsmall n k modified)) := by
  classical
  let ν := adversarialEntries hK gap hpos hsorted hsmall n k modified
  let μ := SeededLearner.Learner.tableLaw ν
  let X : Fin n → Table K (Alphabet hK gap) n → ℝ := fun t g => (g t j).val
  let Y := fun t g => X t g - ∫ w, X t w ∂μ
  let c : Fin n → ℝ≥0 := fun t => if t.val < n / 2 then 1 / 4 else 0
  have hX : ∀ t, Measurable (X t) := fun _ => measurable_of_finite _
  have hind : iIndepFun X μ := by
    exact iIndepFun_pi (μ := fun t => Measure.pi (ν t))
      (X := fun _ row => (row j).val)
      (fun _ => (measurable_subtype_coe.comp (measurable_pi_apply j)).aemeasurable)
  have hYind : iIndepFun Y μ :=
    hind.comp (fun t x => x - ∫ w, X t w ∂μ) (fun _ => measurable_id.sub_const _)
  have hsub : ∀ t, HasSubgaussianMGF (Y t) (c t) μ := by
    intro t
    by_cases ht : t.val < n / 2
    · have hb : ∀ᵐ g ∂μ, X t g ∈ Set.Icc (0 : ℝ) 1 :=
        Filter.Eventually.of_forall fun g => alphabet_value_mem_Icc hK gap hpos hsorted hsmall (g t j)
      have h := hasSubgaussianMGF_of_mem_Icc (hX t).aemeasurable hb
      convert h using 1; norm_num [c, ht]
    · let a : Alphabet hK gap :=
        if t.val < 2 * (n / 2) ∧ j = k then suffixReward hK gap k else zeroReward hK gap
      have hν : ν t j = Measure.dirac a := by
        by_cases hc : t.val < 2 * (n / 2) ∧ j = k <;>
          simp only [ν, adversarialEntries, ht, ↓reduceIte, a, hc, and_self]
      have heval : Measurable (fun g : Table K (Alphabet hK gap) n => g t j) :=
        (measurable_pi_apply j).comp (measurable_pi_apply t)
      have hmap : μ.map (fun g => g t j) = Measure.dirac a :=
        (table_entry_law ν t j).trans hν
      have ha : ∀ᵐ x ∂μ.map (fun g => g t j), x = a := by
        rw [hmap]
        simp
      have hag := ae_of_ae_map heval.aemeasurable ha
      have hb : ∀ᵐ g ∂μ, X t g ∈ Set.Icc a.val a.val := by
        filter_upwards [hag] with g hg
        simp only [X, hg, Set.mem_Icc, le_refl, and_self]
      have h := hasSubgaussianMGF_of_mem_Icc (hX t).aemeasurable hb
      convert h using 1; simp [c, ht]
  have hs := HasSubgaussianMGF.sum_of_iIndepFun hYind
    (s := Finset.univ) (c := c) (fun t _ => hsub t)
  have hc : (∑ t, c t) = ((n / 2 : ℕ) : ℝ≥0) / 4 := by
    unfold c
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    change ((prefixRounds n (n / 2)).card : ℝ≥0) * (1 / 4) = _
    rw [prefixRounds_card n (n / 2) (Nat.div_le_self n 2)]
    ring
  rw [hc] at hs
  convert hs using 1
  funext g
  simp only [Y, X, tableTotal, tableExpectedTotal, Finset.sum_sub_distrib]
  rfl

/-- The sharper Appendix D full-table probability bound uses m random rounds,
including for odd horizons; deterministic continuation never costs variance. -/
theorem adversarial_goodTable_compl_bound (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    (hsmall : ∀ j, gap j ≤ 1 / 8) (n : ℕ) (hn : 2 ≤ n)
    (k : Fin K) (modified : Bool) :
    (SeededLearner.Learner.tableLaw
      (adversarialEntries hK gap hpos hsorted hsmall n k modified)).real
      (goodTable Subtype.val (adversarialEntries hK gap hpos hsorted hsmall n k modified)
        ((n : ℝ) * gap (firstRank hK) / 16))ᶜ ≤
      2 * (K : ℝ) * Real.exp (-(n : ℝ) * gap (firstRank hK) ^ 2 / 64) := by
  classical
  let ν := adversarialEntries hK gap hpos hsorted hsmall n k modified
  let μ := SeededLearner.Learner.tableLaw ν
  let ε := (n : ℝ) * gap (firstRank hK) / 16
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hm : (0 : ℝ) < ((n / 2 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_pos hn (by decide : 0 < 2))
  have hhalf : (2 : ℝ) * ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (LowerBoundSelection.halfHorizon_twice_le n)
  have hvar : (2 : ℝ) * (((((n / 2 : ℕ) : ℝ≥0) / 4) : ℝ≥0) : ℝ) =
      ((n / 2 : ℕ) : ℝ) / 2 := by
    simp
    ring
  have hexponent : -ε ^ 2 / (((n / 2 : ℕ) : ℝ) / 2) ≤
      -(n : ℝ) * gap (firstRank hK) ^ 2 / 64 := by
    apply (div_le_iff₀ (div_pos hm zero_lt_two)).2
    have hp := mul_nonneg (sub_nonneg.mpr hhalf)
      (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg (gap (firstRank hK))))
    dsimp [ε]
    nlinarith
  have hsingle : ∀ j : Fin K,
      μ.real {g | ε < |tableTotal Subtype.val g j - tableExpectedTotal Subtype.val ν j|} ≤
        2 * Real.exp (-(n : ℝ) * gap (firstRank hK) ^ 2 / 64) := by
    intro j
    have hs := adversarial_centeredTotal_subGaussian hK gap hpos hsorted hsmall n k modified j
    have hu := hs.measure_ge_le hε
    have hl := hs.neg.measure_ge_le hε
    rw [hvar] at hu hl
    have hsubset : {g : Table K (Alphabet hK gap) n | ε < |tableTotal Subtype.val g j - tableExpectedTotal Subtype.val ν j|} ⊆
        {g | ε ≤ tableTotal Subtype.val g j - tableExpectedTotal Subtype.val ν j} ∪
        {g | ε ≤ -(tableTotal Subtype.val g j - tableExpectedTotal Subtype.val ν j)} := by
      intro g hg
      change ε ≤ tableTotal Subtype.val g j - tableExpectedTotal Subtype.val ν j ∨
        ε ≤ -(tableTotal Subtype.val g j - tableExpectedTotal Subtype.val ν j)
      change ε < |tableTotal Subtype.val g j - tableExpectedTotal Subtype.val ν j| at hg
      rcases lt_abs.mp hg with h | h
      · exact Or.inl h.le
      · exact Or.inr (by linarith)
    calc
      _ ≤ μ.real ({g | ε ≤ tableTotal Subtype.val g j - tableExpectedTotal Subtype.val ν j} ∪
          {g | ε ≤ -(tableTotal Subtype.val g j - tableExpectedTotal Subtype.val ν j)}) :=
        measureReal_mono hsubset
      _ ≤ μ.real {g | ε ≤ tableTotal Subtype.val g j - tableExpectedTotal Subtype.val ν j} +
          μ.real {g | ε ≤ -(tableTotal Subtype.val g j - tableExpectedTotal Subtype.val ν j)} :=
        measureReal_union_le _ _
      _ ≤ 2 * Real.exp (-ε ^ 2 / (((n / 2 : ℕ) : ℝ) / 2)) :=
        (add_le_add hu hl).trans_eq (by ring)
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (by positivity)
  have hset : (goodTable Subtype.val ν ε)ᶜ =
      ⋃ j : Fin K, {g | ε < |tableTotal Subtype.val g j - tableExpectedTotal Subtype.val ν j|} := by
    ext g
    simp only [goodTable, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le, Set.mem_iUnion]
  change μ.real (goodTable Subtype.val ν ε)ᶜ ≤ _
  rw [hset]
  calc
    _ ≤ ∑ j : Fin K, μ.real {g | ε <
        |tableTotal Subtype.val g j - tableExpectedTotal Subtype.val ν j|} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : Fin K, 2 * Real.exp (-(n : ℝ) * gap (firstRank hK) ^ 2 / 64) :=
      Finset.sum_le_sum (fun j _ => hsingle j)
    _ = _ := by simp; ring

/-- ADV1's full-table good event gives the first unique best arm and Delta3
membership, with the selected label as the exceptional coordinate. -/
theorem adversarial_one_good_class_three (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    (g : ℕ → Fin K → ℝ) (n : ℕ) (hn : 0 < n)
    (hg : ∀ t < n, ∀ j, g t j ∈ Set.Icc (0 : ℝ) 1)
    (k : Fin K) (hk : k ≠ firstRank hK) (M : Fin K → ℝ) (β : ℝ)
    (hβ : 11 / 24 ≤ β ∧ β ≤ 1 / 2)
    (hselected : M (firstRank hK) - M k = (n : ℝ) * (β * gap (firstRank hK)))
    (hother : ∀ j, j ≠ firstRank hK → j ≠ k →
      M (firstRank hK) - M j = (n : ℝ) * (β * gap j))
    (hgood : ∀ j, |RealizedGaps.cumulative g n j - M j| ≤
      (n : ℝ) * gap (firstRank hK) / 16) :
    RealizedGaps.best (RealizedGaps.arms_pos hK) g n = firstRank hK ∧
      AdversarialGapClass hK gap 3 g n := by
  have hs := normalized_pair_bounds hn M (gap (firstRank hK)) (firstRank hK) k
    (β * gap (firstRank hK)) (hgood _) (hgood _) hselected
  have hβd₁ := mul_le_mul_of_nonneg_right hβ.1 hpos.le
  have hβd₂ := mul_le_mul_of_nonneg_right hβ.2 hpos.le
  have hpair : ∀ j, j ≠ firstRank hK →
      (if j = k then gap (firstRank hK) else gap j) / 3 ≤
        (RealizedGaps.cumulative g n (firstRank hK) - RealizedGaps.cumulative g n j) / (n : ℝ) ∧
      (RealizedGaps.cumulative g n (firstRank hK) - RealizedGaps.cumulative g n j) / (n : ℝ) ≤
        3 * (if j = k then gap (firstRank hK) else gap j) := by
    intro j hj
    by_cases hjk : j = k
    · subst j
      simp only [↓reduceIte]
      constructor <;> linarith [hs.1, hs.2]
    · simp only [hjk, ↓reduceIte]
      have hd := normalized_pair_bounds hn M (gap (firstRank hK)) (firstRank hK) j
        (β * gap j) (hgood _) (hgood _) (hother j hj hjk)
      have hgap := gap_pos_of_sorted hK gap hpos hsorted j
      have hle : gap (firstRank hK) ≤ gap j := hsorted (Nat.zero_le j.val)
      have hl := mul_le_mul_of_nonneg_right hβ.1 hgap.le
      have hu := mul_le_mul_of_nonneg_right hβ.2 hgap.le
      constructor <;> linarith [hd.1, hd.2]
  obtain ⟨hbest, hunique, hclass⟩ := labelled_class_of_pairwise_bounds hK gap hpos hsorted
    3 (by norm_num) g n hn (firstRank hK) k (Or.inl rfl) hpair
    ⟨k, hk, by linarith [hs.2]⟩
  exact ⟨hbest, hg, hunique, hclass⟩

/-- ADV2's good event has a different unique best arm while retaining the
same labelled Delta3 reference class. -/
theorem adversarial_two_good_class_three (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    (g : ℕ → Fin K → ℝ) (n : ℕ) (hn : 0 < n)
    (hg : ∀ t < n, ∀ j, g t j ∈ Set.Icc (0 : ℝ) 1)
    (k : Fin K) (hk : k ≠ firstRank hK) (M : Fin K → ℝ) (β : ℝ)
    (hβ : 11 / 24 ≤ β ∧ β ≤ 1 / 2)
    (hfirst : M k - M (firstRank hK) = (n : ℝ) * (β * gap (firstRank hK)))
    (hother : ∀ j, j ≠ firstRank hK → j ≠ k →
      M k - M j = (n : ℝ) * (β * (gap j + gap (firstRank hK))))
    (hgood : ∀ j, |RealizedGaps.cumulative g n j - M j| ≤
      (n : ℝ) * gap (firstRank hK) / 16) :
    RealizedGaps.best (RealizedGaps.arms_pos hK) g n = k ∧
      AdversarialGapClass hK gap 3 g n := by
  have hs := normalized_pair_bounds hn M (gap (firstRank hK)) k (firstRank hK)
    (β * gap (firstRank hK)) (hgood _) (hgood _) hfirst
  have hβd₁ := mul_le_mul_of_nonneg_right hβ.1 hpos.le
  have hβd₂ := mul_le_mul_of_nonneg_right hβ.2 hpos.le
  have hβnonneg : 0 ≤ β := by linarith [hβ.1]
  have hpair : ∀ j, j ≠ k →
      (if j = k then gap (firstRank hK) else gap j) / 3 ≤
        (RealizedGaps.cumulative g n k - RealizedGaps.cumulative g n j) / (n : ℝ) ∧
      (RealizedGaps.cumulative g n k - RealizedGaps.cumulative g n j) / (n : ℝ) ≤
        3 * (if j = k then gap (firstRank hK) else gap j) := by
    intro j hjk
    simp only [hjk, ↓reduceIte]
    by_cases hj : j = firstRank hK
    · subst j
      constructor <;> linarith [hs.1, hs.2]
    · have hd := normalized_pair_bounds hn M (gap (firstRank hK)) k j
        (β * (gap j + gap (firstRank hK))) (hgood _) (hgood _) (hother j hj hjk)
      have hgap := gap_pos_of_sorted hK gap hpos hsorted j
      have hle : gap (firstRank hK) ≤ gap j := hsorted (Nat.zero_le j.val)
      have hl := mul_le_mul_of_nonneg_right hβ.1 hgap.le
      have hu := mul_le_mul_of_nonneg_right hβ.2 hgap.le
      have hprod : 0 ≤ β * gap (firstRank hK) := mul_nonneg hβnonneg hpos.le
      constructor <;> nlinarith [hd.1, hd.2]
  obtain ⟨hbest, hunique, hclass⟩ := labelled_class_of_pairwise_bounds hK gap hpos hsorted
    3 (by norm_num) g n hn k k (Or.inr rfl) hpair
    ⟨firstRank hK, hk.symm, by linarith [hs.2]⟩
  exact ⟨hbest, hg, hunique, hclass⟩

/-- Actual good tables of the two constructed laws satisfy all deterministic
class and unique-best conclusions needed for witness extraction. -/
theorem adversarial_good_table_class (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    (hsmall : ∀ j, gap j ≤ 1 / 8) (n : ℕ) (hn : 12 ≤ n)
    (k : Fin K) (hk : k ≠ firstRank hK) (modified : Bool)
    (g : Table K (Alphabet hK gap) n)
    (hgood : g ∈ goodTable Subtype.val
      (adversarialEntries hK gap hpos hsorted hsmall n k modified)
      ((n : ℝ) * gap (firstRank hK) / 16)) :
    RealizedGaps.best (RealizedGaps.arms_pos hK) (realTable Subtype.val g) n =
        (if modified then k else firstRank hK) ∧
      AdversarialGapClass hK gap 3 (realTable Subtype.val g) n := by
  have hnpos : 0 < n := by omega
  have hnreal : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hnpos.ne'
  let β : ℝ := ((n / 2 : ℕ) : ℝ) / (n : ℝ)
  have hβ : 11 / 24 ≤ β ∧ β ≤ 1 / 2 := by
    simpa only [β, LowerBoundSelection.halfHorizon] using
      (LowerBoundSelection.halfHorizon_ratio_bounds hn)
  have hscale (a : ℝ) : (n : ℝ) * (β * a) = ((n / 2 : ℕ) : ℝ) * a := by
    dsimp [β]
    field_simp [hnreal]
  have hg := realTable_bounded Subtype.val
    (alphabet_value_mem_Icc hK gap hpos hsorted hsmall) g
  have hgood' : ∀ j,
      |RealizedGaps.cumulative (realTable Subtype.val g) n j -
        adversarialExpected hK gap n k modified j| ≤ (n : ℝ) * gap (firstRank hK) / 16 := by
    intro j
    have hh := hgood j
    rw [adversarial_tableExpectedTotal hK gap hpos hsorted hsmall n k modified j] at hh
    simpa only [realTable_cumulative] using hh
  cases modified
  · apply adversarial_one_good_class_three hK gap hpos hsorted _ n hnpos hg k hk
      (adversarialExpected hK gap n k false) β hβ _ _ hgood'
    · rw [adversarialExpected_first hK gap n k hk false,
        adversarialExpected_selected hK gap n k hk false, hscale]
      simp
      ring
    · intro j hj hjk
      rw [adversarialExpected_first hK gap n k hk false,
        adversarialExpected_other hK gap n k j hj hjk false, hscale]
      ring
  · apply adversarial_two_good_class_three hK gap hpos hsorted _ n hnpos hg k hk
      (adversarialExpected hK gap n k true) β hβ _ _ hgood'
    · rw [adversarialExpected_selected hK gap n k hk true,
        adversarialExpected_first hK gap n k hk true, hscale]
      simp
      ring
    · intro j hj hjk
      rw [adversarialExpected_selected hK gap n k hk true,
        adversarialExpected_other hK gap n k j hj hjk true, hscale]
      simp
      ring


/-- ADV1 agrees with BASE at every earlier row of the informative prefix. -/
theorem adversarial_one_prefix (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    (hsmall : ∀ j, gap j ≤ 1 / 8) (n : ℕ) (k : Fin K)
    (t : Fin n) (ht : t.val < n / 2) (j : Fin K) :
    adversarialEntries hK gap hpos hsorted hsmall n k false t j =
      baseEntries hK gap hpos hsorted hsmall n t j := by
  simp [adversarialEntries, ht]

/-- The two actual adversarial laws are precisely the environments used in
Lemma 10, with only the selected arm and deterministic prefix changed. -/
theorem adversarial_environment_base (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    (hsmall : ∀ j, gap j ≤ 1 / 8) (n : ℕ) (k : Fin K) :
    SeededChangeOfMeasure.environment
        (adversarialEntries hK gap hpos hsorted hsmall n k false)
        k (prefixRounds n (n / 2)) (oneReward hK gap) (zeroReward hK gap)
        (baseParameter hK gap hpos hsorted hsmall k) =
      adversarialEntries hK gap hpos hsorted hsmall n k false := by
  classical
  funext t j
  by_cases h : t ∈ prefixRounds n (n / 2) ∧ j = k
  · obtain ⟨ht, rfl⟩ := h
    have ht' := (mem_prefixRounds n (n / 2) t).mp ht
    simp only [SeededChangeOfMeasure.environment, ht, and_self, ↓reduceIte,
      adversarialEntries, ht', Bool.false_eq_true, false_and, baseEntries,
      alphabetBernoulli]
  · simp only [SeededChangeOfMeasure.environment, h, ↓reduceIte]

theorem adversarial_environment_perturbed (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    (hsmall : ∀ j, gap j ≤ 1 / 8) (n : ℕ) (k : Fin K) :
    SeededChangeOfMeasure.environment
        (adversarialEntries hK gap hpos hsorted hsmall n k false)
        k (prefixRounds n (n / 2)) (oneReward hK gap) (zeroReward hK gap)
        (perturbedParameter hK gap hpos hsorted hsmall k) =
      adversarialEntries hK gap hpos hsorted hsmall n k true := by
  classical
  funext t j
  by_cases ht : t.val < n / 2
  · have ht' := (mem_prefixRounds n (n / 2) t).mpr ht
    by_cases hj : j = k
    · simp [SeededChangeOfMeasure.environment, ht', hj, adversarialEntries, ht,
        alphabetBernoulli]
    · simp [SeededChangeOfMeasure.environment, ht', hj, adversarialEntries, ht]
  · have ht' : t ∉ prefixRounds n (n / 2) := by
      simpa only [mem_prefixRounds] using ht
    simp [SeededChangeOfMeasure.environment, ht', adversarialEntries, ht]

section ActualLearner

variable {Seed : Type*} [MeasurableSpace Seed]

/-- Theorem 2 for the finite actual reward alphabet. The selected arm, both
independent table laws, and both good deterministic witnesses are constructed
inside the proof. In particular, the conclusion has no information, support,
selection, concentration, or extraction hypothesis. -/
theorem adversarial_lower_bound_finite
    (hK : 2 ≤ K) (hKlarge : 4096 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    (hsmall : ∀ j, gap j ≤ 1 / 8) (n : ℕ)
    (L : Learner Seed (Alphabet hK gap) K n)
    (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (horizon : (K : ℝ) * Real.exp (-(n : ℝ) * gap (firstRank hK) ^ 2 / 128) ≤ 1 / 128) :
    ∃ g₁ g₂ : Table K (Alphabet hK gap) n,
      AdversarialGapClass hK gap 3 (realTable Subtype.val g₁) n ∧
      AdversarialGapClass hK gap 3 (realTable Subtype.val g₂) n ∧
      RealizedGaps.best (RealizedGaps.arms_pos hK) (realTable Subtype.val g₁) n ≠
        RealizedGaps.best (RealizedGaps.arms_pos hK) (realTable Subtype.val g₂) n ∧
      min (Real.exp (-32 * (n : ℝ) / H_UNIF hK gap) / 128) (1 / 32) ≤
        max
          (deterministicError ρ (fun z => (L.transcript z).2)
            (fun g => RealizedGaps.best (RealizedGaps.arms_pos hK) (realTable Subtype.val g) n) g₁)
          (deterministicError ρ (fun z => (L.transcript z).2)
            (fun g => RealizedGaps.best (RealizedGaps.arms_pos hK) (realTable Subtype.val g) n) g₂) := by
  classical
  let δ := gap (firstRank hK)
  let x := (n : ℝ) * δ ^ 2 / (K : ℝ)
  let ε := Real.exp (-32 * x)
  have hKpos : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr (by omega)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hεpos : 0 < ε := Real.exp_pos _
  have hεle : ε ≤ 1 := by
    change Real.exp (-32 * x) ≤ 1
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hlarge := horizon_gap_square_ge_one (n := n) hK δ (by dsimp [δ]; linarith [horizon])
  have hn64 := (horizon_arithmetic δ δ hpos (hsmall _) hpos (hsmall _) hlarge).1
  let ν₀ := baseEntries hK gap hpos hsorted hsmall n
  obtain ⟨k, hk, hlight⟩ := L.exists_halfHorizon_light_actual ρ ν₀ hK
  let ν₁ := adversarialEntries hK gap hpos hsorted hsmall n k false
  let ν₂ := adversarialEntries hK gap hpos hsorted hsmall n k true
  let μ₁ := SeededLearner.Learner.tableLaw ν₁
  let μ₂ := SeededLearner.Learner.tableLaw ν₂
  let G₁ := goodTable Subtype.val ν₁ ((n : ℝ) * δ / 16)
  let G₂ := goodTable Subtype.val ν₂ ((n : ℝ) * δ / 16)
  let recommendTable : Seed × Table K (Alphabet hK gap) n → Fin K := fun z => (L.transcript z).2
  let bestTable := fun g : Table K (Alphabet hK gap) n =>
    RealizedGaps.best (RealizedGaps.arms_pos hK) (realTable Subtype.val g) n
  let R₁ := goodErrorMass ρ μ₁ recommendTable bestTable G₁
  let R₂ := goodErrorMass ρ μ₂ recommendTable bestTable G₂
  have hrec : Measurable recommendTable := measurable_snd.comp L.transcript_measurable
  have hfirst := baseMean_mem_Ioo hK gap hpos hsorted hsmall k
  have hpert := perturbedParameter_mem_Ioo hK gap hpos hsorted hsmall k
  have hcount : L.expectedPullCount ρ ν₁ (prefixRounds n (n / 2)) k ≤ (n : ℝ) / (K : ℝ) := by
    have heq := L.expectedPullCount_eq_of_prefix ρ ν₁ ν₀ (n / 2) k
      (fun t ht j => adversarial_one_prefix hK gap hpos hsorted hsmall n k t ht j)
    rw [heq]
    exact hlight
  have hinfo : L.expectedPullCount ρ ν₁ (prefixRounds n (n / 2)) k *
      BernoulliInformation.binaryKL
        (baseParameter hK gap hpos hsorted hsmall k)
        (perturbedParameter hK gap hpos hsorted hsmall k) ≤ 32 * x := by
    have hcost : BernoulliInformation.binaryKL
        (baseParameter hK gap hpos hsorted hsmall k)
        (perturbedParameter hK gap hpos hsorted hsmall k) ≤ 32 * δ ^ 2 := by
      change BernoulliInformation.binaryKL (baseMean hK gap k)
        (1 / 2 - gap k + 2 * δ) ≤ _
      rw [baseMean, ite_eq_right hk]
      exact adversarial_binaryKL_bound hpos (hsorted (Nat.zero_le k.val)) (hsmall k)
    calc
      _ ≤ L.expectedPullCount ρ ν₁ (prefixRounds n (n / 2)) k * (32 * δ ^ 2) :=
        mul_le_mul_of_nonneg_left hcost (L.expectedPullCount_nonneg ρ ν₁ _ k)
      _ ≤ ((n : ℝ) / (K : ℝ)) * (32 * δ ^ 2) :=
        mul_le_mul_of_nonneg_right hcount (by positivity)
      _ = 32 * x := by dsimp [x]; ring
  let W : Set (Transcript K (Alphabet hK gap) n) := {z | z.2 = firstRank hK}
  have htest : ε / 2 ≤ (L.transcriptLaw ρ ν₁).real Wᶜ + (L.transcriptLaw ρ ν₂).real W := by
    have h := SeededChangeOfMeasure.lemma10_testing L ρ ν₁ k (prefixRounds n (n / 2))
      (oneReward hK gap) (zeroReward hK gap) (oneReward_ne_zeroReward hK gap)
      (baseParameter hK gap hpos hsorted hsmall k)
      (perturbedParameter hK gap hpos hsorted hsmall k)
      hfirst.1 hfirst.2 hpert.1 hpert.2 W
    have henv₁ : SeededChangeOfMeasure.environment ν₁ k (prefixRounds n (n / 2))
        (oneReward hK gap) (zeroReward hK gap)
        (baseParameter hK gap hpos hsorted hsmall k) = ν₁ :=
      adversarial_environment_base hK gap hpos hsorted hsmall n k
    have henv₂ : SeededChangeOfMeasure.environment ν₁ k (prefixRounds n (n / 2))
        (oneReward hK gap) (zeroReward hK gap)
        (perturbedParameter hK gap hpos hsorted hsmall k) = ν₂ :=
      adversarial_environment_perturbed hK gap hpos hsorted hsmall n k
    simp only [SeededChangeOfMeasure.observedLaw] at h
    rw [henv₁, henv₂] at h
    have he : ε ≤ Real.exp (-(L.expectedPullCount ρ ν₁ (prefixRounds n (n / 2)) k *
        BernoulliInformation.binaryKL
          (baseParameter hK gap hpos hsorted hsmall k)
          (perturbedParameter hK gap hpos hsorted hsmall k))) := by
      apply Real.exp_le_exp.mpr
      linarith [hinfo]
    calc
      ε / 2 ≤ (1 / 2 : ℝ) * Real.exp (-
          (L.expectedPullCount ρ ν₁ (prefixRounds n (n / 2)) k *
            BernoulliInformation.binaryKL
              (baseParameter hK gap hpos hsorted hsmall k)
              (perturbedParameter hK gap hpos hsorted hsmall k))) := by
        linarith [he]
      _ ≤ _ := h
  have hKx : (K : ℝ) * x = (n : ℝ) * δ ^ 2 := by
    dsimp [x]
    field_simp [hKpos.ne']
  have hnegKx : -(K : ℝ) * x = -(n : ℝ) * δ ^ 2 := by nlinarith [hKx]
  have hbad₁ : μ₁.real G₁ᶜ ≤ ε / 64 := by
    apply adversarial_bad_mass_relative (Nat.cast_le.mpr hKlarge) hx
    · rw [hnegKx]
      exact horizon
    · rw [hnegKx]
      exact adversarial_goodTable_compl_bound hK gap hpos hsorted hsmall n (by omega) k false
  have hbad₂ : μ₂.real G₂ᶜ ≤ ε / 64 := by
    apply adversarial_bad_mass_relative (Nat.cast_le.mpr hKlarge) hx
    · rw [hnegKx]
      exact horizon
    · rw [hnegKx]
      exact adversarial_goodTable_compl_bound hK gap hpos hsorted hsmall n (by omega) k true
  have hclass₁ : ∀ g ∈ G₁, bestTable g = firstRank hK ∧
      AdversarialGapClass hK gap 3 (realTable Subtype.val g) n := by
    intro g hg
    exact adversarial_good_table_class hK gap hpos hsorted hsmall n (by omega) k hk false g hg
  have hclass₂ : ∀ g ∈ G₂, bestTable g = k ∧
      AdversarialGapClass hK gap 3 (realTable Subtype.val g) n := by
    intro g hg
    exact adversarial_good_table_class hK gap hpos hsorted hsmall n (by omega) k hk true g hg
  have hremove₁ : (L.transcriptLaw ρ ν₁).real Wᶜ - μ₁.real G₁ᶜ ≤ R₁ := by
    have h := randomizedError_agreement_le_goodErrorMass_add_bad ρ μ₁ recommendTable hrec
      bestTable (fun _ => firstRank hK) G₁ (fun g hg => (hclass₁ g hg).1.symm)
    rw [← transcript_error_eq_randomizedError L ρ ν₁ (firstRank hK)] at h
    change (L.transcriptLaw ρ ν₁).real {z | z.2 ≠ firstRank hK} ≤ _ at h
    have heq : Wᶜ = {z | z.2 ≠ firstRank hK} := rfl
    rw [heq]
    linarith
  have hremove₂ : (L.transcriptLaw ρ ν₂).real W - μ₂.real G₂ᶜ ≤ R₂ := by
    have h := randomizedError_agreement_le_goodErrorMass_add_bad ρ μ₂ recommendTable hrec
      bestTable (fun _ => k) G₂ (fun g hg => (hclass₂ g hg).1.symm)
    rw [← transcript_error_eq_randomizedError L ρ ν₂ k] at h
    have hw : W ⊆ {z | z.2 ≠ k} := by
      intro z hz heq
      exact hk (heq.symm.trans hz)
    have hmono := measureReal_mono (μ := L.transcriptLaw ρ ν₂) hw
    linarith
  have hR := adversarial_good_error_sum htest hremove₁ hremove₂ hbad₁ hbad₂
  have hG₁ : G₁.Nonempty := good_nonempty_of_bad_lt_one μ₁ G₁ (by linarith)
  have hG₂ : G₂.Nonempty := good_nonempty_of_bad_lt_one μ₂ G₂ (by linarith)
  obtain ⟨g₁, hg₁, he₁⟩ := exists_good_table_dominating_good_mass μ₁
    (deterministicError ρ recommendTable bestTable) G₁ (fun _ => measureReal_nonneg) hG₁
  obtain ⟨g₂, hg₂, he₂⟩ := exists_good_table_dominating_good_mass μ₂
    (deterministicError ρ recommendTable bestTable) G₂ (fun _ => measureReal_nonneg) hG₂
  refine ⟨g₁, g₂, (hclass₁ g₁ hg₁).2, (hclass₂ g₂ hg₂).2, ?_, ?_⟩
  · change bestTable g₁ ≠ bestTable g₂
    rw [(hclass₁ g₁ hg₁).1, (hclass₂ g₂ hg₂).1]
    exact hk.symm
  · have heq : Real.exp (-32 * (n : ℝ) / H_UNIF hK gap) = ε := by
      congr 1
      dsimp [H_UNIF, ε, x, δ]
      field_simp [hpos.ne', hKpos.ne']
    rw [heq]
    exact adversarial_two_witness_errors hεpos.le hR he₁ he₂

/-- Theorem 2 for an arbitrary real-history learner and arbitrary measurable
private seed. The witnesses are actual oblivious real reward tables, chosen
before the seed is sampled, with the exact manuscript error lower bound. -/
theorem adversarial_lower_bound
    (hK : 2 ≤ K) (hKlarge : 4096 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    (_hduplicate : gap (firstRank hK) = gap (secondRank hK))
    (hsmall : ∀ j, gap j ≤ 1 / 8) (n : ℕ)
    (L : Learner Seed ℝ K n) (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (horizon : (K : ℝ) * Real.exp (-(n : ℝ) * gap (firstRank hK) ^ 2 / 128) ≤ 1 / 128) :
    ∃ g₁ g₂ : ℕ → Fin K → ℝ,
      AdversarialGapClass hK gap 3 g₁ n ∧ AdversarialGapClass hK gap 3 g₂ n ∧
      RealizedGaps.best (RealizedGaps.arms_pos hK) g₁ n ≠
        RealizedGaps.best (RealizedGaps.arms_pos hK) g₂ n ∧
      min (Real.exp (-32 * (n : ℝ) / H_UNIF hK gap) / 128) (1 / 32) ≤
        max (realLearnerError hK L ρ g₁) (realLearnerError hK L ρ g₂) := by
  obtain ⟨g₁, g₂, hc₁, hc₂, hbest, herr⟩ := adversarial_lower_bound_finite hK hKlarge gap
    hpos hsorted hsmall n (L.restrictReward Subtype.val) ρ horizon
  refine ⟨realTable Subtype.val g₁, realTable Subtype.val g₂, hc₁, hc₂, hbest, ?_⟩
  rw [deterministicError_restrictReward hK L ρ Subtype.val g₁,
    deterministicError_restrictReward hK L ρ Subtype.val g₂] at herr
  exact herr

end ActualLearner

end BestOfBothWorlds.LowerBounds
