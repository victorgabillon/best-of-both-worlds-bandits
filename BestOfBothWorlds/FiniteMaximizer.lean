module

public import Mathlib.Data.Finset.Max
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.MeasurableSpace.Instances

/-!
A finite real score vector has an actual maximizer, with ties resolved by the
smallest arm index. Its measurable fibers are finite combinations of score
comparisons; no assumption that score ties have probability zero is used.
-/

@[expose] public section

open MeasureTheory

namespace BestOfBothWorlds.FiniteMaximizer

variable {K : ℕ}

/-- The finite set of all score maximizers. -/
noncomputable def maximizers (score : Fin K → ℝ) : Finset (Fin K) := by
  classical
  exact Finset.univ.filter (fun k => ∀ j, score j ≤ score k)

theorem maximizers_nonempty (hK : 0 < K) (score : Fin K → ℝ) :
    (maximizers score).Nonempty := by
  classical
  obtain ⟨k, _, hk⟩ := (Finset.univ : Finset (Fin K)).exists_max_image score
    ⟨⟨0, hK⟩, Finset.mem_univ _⟩
  exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j => hk j (Finset.mem_univ _)⟩⟩

/-- The smallest index attaining the maximum score. -/
noncomputable def select (hK : 0 < K) (score : Fin K → ℝ) : Fin K :=
  (maximizers score).min' (maximizers_nonempty hK score)

/-- The selected score is at least every arm's score. -/
theorem le_select (hK : 0 < K) (score : Fin K → ℝ) (k : Fin K) :
    score k ≤ score (select hK score) := by
  classical
  exact (Finset.mem_filter.mp ((maximizers score).min'_mem (maximizers_nonempty hK score))).2 k

/-- An equal-scoring maximizer cannot have a smaller index than the selection. -/
theorem select_le_of_eq (hK : 0 < K) (score : Fin K → ℝ) (k : Fin K)
    (heq : score k = score (select hK score)) : select hK score ≤ k := by
  classical
  apply Finset.min'_le
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j => by
    rw [heq]
    exact le_select hK score j⟩

/-- Score maximality and smallest-index ties characterize the selected arm. -/
theorem select_eq_iff (hK : 0 < K) (score : Fin K → ℝ) (k : Fin K) :
    select hK score = k ↔
      (∀ j, score j ≤ score k) ∧ (∀ j, score j = score k → k ≤ j) := by
  constructor
  · intro h
    subst k
    exact ⟨le_select hK score, select_le_of_eq hK score⟩
  · rintro ⟨hmax, hsmall⟩
    have heq : score k = score (select hK score) :=
      le_antisymm (le_select hK score k) (hmax (select hK score))
    exact le_antisymm (select_le_of_eq hK score k heq) (hsmall _ heq.symm)

/-- In particular, a unique strict score maximizer is selected. -/
theorem select_eq_of_strict (hK : 0 < K) (score : Fin K → ℝ) (k : Fin K)
    (hstrict : ∀ j, j ≠ k → score j < score k) : select hK score = k := by
  by_contra hne
  exact (not_lt_of_ge (le_select hK score k)) (hstrict _ hne)

/-- Coordinatewise measurable real scores give a measurable smallest maximizer. -/
theorem select_measurable (hK : 0 < K) {Ω : Type*} [MeasurableSpace Ω]
    (score : Ω → Fin K → ℝ) (hscore : ∀ k, Measurable (fun ω => score ω k)) :
    Measurable (fun ω => select hK (score ω)) := by
  apply measurable_to_countable'
  intro k
  have he : (fun ω => select hK (score ω)) ⁻¹' {k} =
      (⋂ j : Fin K, {ω | score ω j ≤ score ω k}) ∩
        (⋂ j : Fin K, {ω | score ω j = score ω k → k ≤ j}) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, select_eq_iff,
      Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [he]
  refine (MeasurableSet.iInter (fun j => measurableSet_le (hscore j) (hscore k))).inter
    (MeasurableSet.iInter (fun j => ?_))
  by_cases hkj : k ≤ j
  · simpa only [hkj, implies_true, Set.ofPred_true] using
      (MeasurableSet.univ : MeasurableSet (Set.univ : Set Ω))
  · have hneq : {ω | score ω j = score ω k → k ≤ j} =
        {ω | score ω j = score ω k}ᶜ := by
      ext ω
      simp [hkj]
    rw [hneq]
    exact (measurableSet_eq_fun (hscore j) (hscore k)).compl

end BestOfBothWorlds.FiniteMaximizer
