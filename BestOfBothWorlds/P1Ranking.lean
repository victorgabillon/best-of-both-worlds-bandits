module

public import BestOfBothWorlds.FiniteMaximizer
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Lean.Elab.Tactic.Omega

/-!
P1 ranks larger estimated cumulative gains first. Mathlib's tuple sort resolves
score ties by the original arm index. This deterministic tie rule is one of the
arbitrary rules allowed by the manuscript and agrees with FiniteMaximizer at
rank one. Ranks are one-based, while positions are elements of Fin K.
-/

@[expose] public section

open MeasureTheory

namespace BestOfBothWorlds.P1Ranking

variable {K : ℕ}

/-- The harmonic normalizer, with indices one through K. -/
noncomputable def harmonicK (K : ℕ) : ℝ :=
  ∑ i : Fin K, 1 / (((i.val + 1 : ℕ) : ℝ))

theorem one_le_harmonicK (hK : 0 < K) : 1 ≤ harmonicK K := by
  have h := Finset.single_le_sum
    (s := (Finset.univ : Finset (Fin K)))
    (f := fun i : Fin K => (1 : ℝ) / (((i.val + 1 : ℕ) : ℝ)))
    (fun i _ => (one_div_pos.mpr (Nat.cast_pos.mpr (Nat.succ_pos i.val))).le)
    (Finset.mem_univ (⟨0, hK⟩ : Fin K))
  simpa only [harmonicK, Nat.zero_add, Nat.cast_one, one_div_one] using h

theorem harmonicK_pos (hK : 0 < K) : 0 < harmonicK K :=
  lt_of_lt_of_le zero_lt_one (one_le_harmonicK hK)

/-- Arm at each estimated position, in decreasing score order and increasing index ties. -/
noncomputable def order (score : Fin K → ℝ) : Equiv.Perm (Fin K) :=
  Tuple.sort (fun k => -score k)

/-- The inverse permutation gives each arm its zero-based estimated position. -/
noncomputable def position (score : Fin K → ℝ) (k : Fin K) : Fin K :=
  (order score).symm k

/-- Manuscript rank is one more than the zero-based position. -/
noncomputable def rank (score : Fin K → ℝ) (k : Fin K) : ℕ :=
  (position score k).val + 1

theorem rank_pos (score : Fin K → ℝ) (k : Fin K) : 0 < rank score k :=
  Nat.succ_pos _

theorem rank_le (score : Fin K → ℝ) (k : Fin K) : rank score k ≤ K :=
  Nat.succ_le_of_lt (position score k).isLt

@[simp] theorem order_position (score : Fin K → ℝ) (k : Fin K) :
    order score (position score k) = k := (order score).apply_symm_apply k

@[simp] theorem position_order (score : Fin K → ℝ) (r : Fin K) :
    position score (order score r) = r := (order score).symm_apply_apply r

theorem score_order_antitone (score : Fin K → ℝ) :
    Antitone (fun r => score (order score r)) := by
  intro i j hij
  have h := Tuple.monotone_sort (fun k => -score k) hij
  exact neg_le_neg_iff.mp h

theorem order_tie (score : Fin K → ℝ) (i j : Fin K) (hij : i < j)
    (heq : score (order score i) = score (order score j)) :
    order score i < order score j := by
  exact (Tuple.eq_sort_iff.mp (rfl : order score = Tuple.sort (fun k => -score k))).2
    i j hij (by simp only [heq])

theorem score_le_of_position_le (score : Fin K → ℝ) (j k : Fin K)
    (h : position score j ≤ position score k) : score k ≤ score j := by
  simpa only [order_position] using score_order_antitone score h

/-- Rank one is the same smallest maximizing arm used by the actual recommendation. -/
theorem order_first_eq_select (hK : 0 < K) (score : Fin K → ℝ) :
    order score ⟨0, hK⟩ = FiniteMaximizer.select hK score := by
  symm
  apply (FiniteMaximizer.select_eq_iff hK score _).2
  constructor
  · intro k
    exact score_le_of_position_le score _ k (by
      rw [position_order]
      exact Nat.zero_le _)
  · intro k hk
    by_cases heq : k = order score ⟨0, hK⟩
    · exact heq.symm.le
    · have hpos : (⟨0, hK⟩ : Fin K) < position score k := by
        have hn : position score k ≠ (⟨0, hK⟩ : Fin K) := by
          intro h
          apply heq
          simpa only [order_position] using congrArg (order score) h
        exact lt_of_le_of_ne (Nat.zero_le _) (Ne.symm hn)
      have h := order_tie score ⟨0, hK⟩ (position score k) hpos (by
        simpa only [order_position] using hk.symm)
      simpa only [order_position] using h.le

/-- A poorly ranked eligible arm has a preceding arm outside the true leading prefix. -/
theorem exists_outside_prefix_precedes (score : Fin K → ℝ) (truth : Equiv.Perm (Fin K))
    (i : ℕ) (k : Fin K) (hk : (truth.symm k).val < i)
    (hr : i ≤ (position score k).val) :
    ∃ j, i ≤ (truth.symm j).val ∧ position score j < position score k ∧ score k ≤ score j := by
  classical
  by_contra hnone
  have hiK : i < K := lt_of_le_of_lt hr (position score k).isLt
  have hsmall : ∀ a : Fin i, (truth.symm (order score ⟨a.val, a.isLt.trans hiK⟩)).val < i := by
    intro a
    by_contra ha
    apply hnone
    refine ⟨order score ⟨a.val, a.isLt.trans hiK⟩, Nat.le_of_not_gt ha, ?_, ?_⟩
    · rw [position_order]
      change a.val < (position score k).val
      exact a.isLt.trans_le hr
    · exact score_le_of_position_le score _ k (by
        rw [position_order]
        exact (a.isLt.trans_le hr).le)
  let f : Fin i → Fin i := fun a =>
    ⟨(truth.symm (order score ⟨a.val, a.isLt.trans hiK⟩)).val, hsmall a⟩
  have hfinj : Function.Injective f := by
    intro a b hab
    have hv := congrArg Fin.val hab
    have he := truth.symm.injective (Fin.ext hv)
    have he' := (order score).injective he
    exact Fin.ext (congrArg (fun x : Fin K => x.val) he')
  obtain ⟨a, ha⟩ := (Finite.surjective_of_injective hfinj) (⟨(truth.symm k).val, hk⟩ : Fin i)
  have hva := congrArg (fun x : Fin i => x.val) ha
  have htrue : truth.symm (order score ⟨a.val, a.isLt.trans hiK⟩) = truth.symm k :=
    Fin.ext hva
  have horder : order score ⟨a.val, a.isLt.trans hiK⟩ = k := truth.symm.injective htrue
  have hp := congrArg (position score) horder
  rw [position_order] at hp
  have hv := congrArg (fun x : Fin K => x.val) hp
  change a.val = (position score k).val at hv
  omega

/-- Sorting fibers are finite measurable combinations of coordinate comparisons. -/
theorem measurableSet_order_eq {Ω : Type*} [MeasurableSpace Ω]
    (score : Ω → Fin K → ℝ) (hscore : ∀ k, Measurable (fun ω => score ω k))
    (σ : Equiv.Perm (Fin K)) : MeasurableSet {ω | order (score ω) = σ} := by
  have hm : MeasurableSet {ω | Monotone ((fun k => -score ω k) ∘ σ)} := by
    change MeasurableSet {ω | ∀ i j : Fin K, i ≤ j → -score ω (σ i) ≤ -score ω (σ j)}
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun j =>
      MeasurableSet.iInter (fun _ => measurableSet_le (hscore (σ i)).neg (hscore (σ j)).neg)))
  have ht : MeasurableSet {ω | ∀ i j : Fin K, i < j →
      -score ω (σ i) = -score ω (σ j) → σ i < σ j} := by
    simp only [Set.ofPred_forall]
    refine MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun j =>
      MeasurableSet.iInter (fun _ => ?_)))
    by_cases hij : σ i < σ j
    · simpa only [hij, implies_true, Set.ofPred_true] using
        (MeasurableSet.univ : MeasurableSet (Set.univ : Set Ω))
    · have he : {ω | -score ω (σ i) = -score ω (σ j) → σ i < σ j} =
          {ω | -score ω (σ i) = -score ω (σ j)}ᶜ := by
        ext ω
        simp [hij]
      rw [he]
      exact (measurableSet_eq_fun (hscore (σ i)).neg (hscore (σ j)).neg).compl
  have he : {ω | order (score ω) = σ} =
      {ω | Monotone ((fun k => -score ω k) ∘ σ)} ∩
        {ω | ∀ i j : Fin K, i < j → -score ω (σ i) = -score ω (σ j) → σ i < σ j} := by
    ext ω
    change order (score ω) = σ ↔ _
    rw [eq_comm]
    exact Tuple.eq_sort_iff
  rw [he]
  exact hm.inter ht

theorem position_measurable {Ω : Type*} [MeasurableSpace Ω]
    (score : Ω → Fin K → ℝ) (hscore : ∀ k, Measurable (fun ω => score ω k)) (k : Fin K) :
    Measurable (fun ω => position (score ω) k) := by
  classical
  apply measurable_to_countable'
  intro i
  have he : (fun ω => position (score ω) k) ⁻¹' {i} =
      ⋃ σ : Equiv.Perm (Fin K), {ω | order (score ω) = σ} ∩ {ω | σ.symm k = i} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion,
      Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro hi
      exact ⟨order (score ω), rfl, hi⟩
    · rintro ⟨σ, hσ, hi⟩
      change (order (score ω)).symm k = i
      rwa [hσ]
  rw [he]
  exact MeasurableSet.iUnion (fun σ =>
    (measurableSet_order_eq score hscore σ).inter (MeasurableSet.const _))

/-- Reciprocal ranks sum to the harmonic normalizer because ranks are a permutation. -/
theorem sum_reciprocal_rank (score : Fin K → ℝ) :
    (∑ k : Fin K, 1 / ((rank score k : ℕ) : ℝ)) = harmonicK K := by
  exact Equiv.sum_comp (order score).symm (fun i : Fin K => 1 / (((i.val + 1 : ℕ) : ℝ)))

/-- P1's concrete rank-dependent probability vector. -/
noncomputable def probability (_hK : 0 < K) (score : Fin K → ℝ) (k : Fin K) : ℝ :=
  1 / (((rank score k : ℕ) : ℝ) * harmonicK K)

theorem probability_pos (hK : 0 < K) (score : Fin K → ℝ) (k : Fin K) :
    0 < probability hK score k :=
  one_div_pos.mpr (mul_pos (Nat.cast_pos.mpr (rank_pos score k)) (harmonicK_pos hK))

theorem probability_normalized (hK : 0 < K) (score : Fin K → ℝ) :
    ∑ k, probability hK score k = 1 := by
  calc
    _ = (∑ k : Fin K, 1 / ((rank score k : ℕ) : ℝ)) / harmonicK K := by
      simp only [probability, div_div, Finset.sum_div]
    _ = harmonicK K / harmonicK K := by rw [sum_reciprocal_rank]
    _ = 1 := div_self (ne_of_gt (harmonicK_pos hK))

theorem probability_floor (hK : 0 < K) (score : Fin K → ℝ) (k : Fin K) :
    1 / ((K : ℝ) * harmonicK K) ≤ probability hK score k := by
  exact one_div_le_one_div_of_le
    (mul_pos (Nat.cast_pos.mpr (rank_pos score k)) (harmonicK_pos hK))
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (rank_le score k)) (harmonicK_pos hK).le)

theorem probability_measurable (hK : 0 < K) {Ω : Type*} [MeasurableSpace Ω]
    (score : Ω → Fin K → ℝ) (hscore : ∀ k, Measurable (fun ω => score ω k)) (k : Fin K) :
    Measurable (fun ω => probability hK (score ω) k) := by
  exact (measurable_of_finite (fun i : Fin K =>
    (1 : ℝ) / (((i.val + 1 : ℕ) : ℝ) * harmonicK K))).comp
      (position_measurable score hscore k)

end BestOfBothWorlds.P1Ranking
