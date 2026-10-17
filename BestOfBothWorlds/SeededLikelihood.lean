module

public import BestOfBothWorlds.SeededLearner
public import BestOfBothWorlds.SeededLearnerFreshness
public import BestOfBothWorlds.SeededLearnerCounts
public import BestOfBothWorlds.FiniteInformation

/-!
The actual observed-transcript likelihood ratio for a private-seed learner. All
cancellation is restricted to positive transcript support. Null atoms contribute
zero to the finite KL sum. No latent-table KL is substituted for observed KL.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace BestOfBothWorlds.SeededLearner.Learner

variable {Seed Reward : Type*} [MeasurableSpace Seed] [MeasurableSpace Reward]
  [Fintype Reward] [MeasurableSingletonClass Reward] {K n : ℕ}
  (L : Learner Seed Reward K n)

/-- Real-valued form of the exact factorization, with no positivity assumption. -/
theorem transcript_atom_factorization_real (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (ν : Fin n → Fin K → Measure Reward) [∀ t k, IsProbabilityMeasure (ν t k)]
    (z : Transcript K Reward n) :
    (L.transcriptLaw ρ ν).real {z} =
      ρ.real (L.seedConsistency z) * ∏ t, (ν t (z.1 t).1).real {(z.1 t).2} := by
  simp only [measureReal_def, L.transcript_atom_factorization,
    ENNReal.toReal_mul, ENNReal.toReal_prod]

/-- Actual transcript absolute continuity follows from common entry supports. -/
theorem transcript_absolutelyContinuous (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (ν η : Fin n → Fin K → Measure Reward)
    [∀ t k, IsProbabilityMeasure (ν t k)] [∀ t k, IsProbabilityMeasure (η t k)]
    (hsupport : ∀ t k x, ν t k {x} = 0 ↔ η t k {x} = 0) :
    L.transcriptLaw ρ ν ≪ L.transcriptLaw ρ η :=
  FiniteInformation.absolutelyContinuous_of_atom_support _ _ fun z hz =>
    (L.transcript_atom_eq_zero_iff ρ ν η hsupport z).mpr hz

/-- Every observed factor is strictly positive on positive transcript support. -/
theorem observed_atom_pos (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (ν : Fin n → Fin K → Measure Reward) [∀ t k, IsProbabilityMeasure (ν t k)]
    (z : Transcript K Reward n) (hz : 0 < (L.transcriptLaw ρ ν).real {z}) (t : Fin n) :
    0 < (ν t (z.1 t).1).real {(z.1 t).2} := by
  have heq := L.transcript_atom_factorization_real ρ ν z
  have hmul : ρ.real (L.seedConsistency z) *
      (∏ s, (ν s (z.1 s).1).real {(z.1 s).2}) ≠ 0 := by
    rw [← heq]
    exact hz.ne'
  have hp := (mul_ne_zero_iff.mp hmul).2
  have ht := (Finset.prod_ne_zero_iff.mp hp) t (Finset.mem_univ t)
  exact lt_of_le_of_ne measureReal_nonneg (Ne.symm ht)

/-- Positive transcript mass forces a positive learner-consistency factor. -/
theorem seedConsistency_mass_pos (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (ν : Fin n → Fin K → Measure Reward) [∀ t k, IsProbabilityMeasure (ν t k)]
    (z : Transcript K Reward n) (hz : 0 < (L.transcriptLaw ρ ν).real {z}) :
    0 < ρ.real (L.seedConsistency z) := by
  have heq := L.transcript_atom_factorization_real ρ ν z
  have hmul : ρ.real (L.seedConsistency z) *
      (∏ s, (ν s (z.1 s).1).real {(z.1 s).2}) ≠ 0 := by
    rw [← heq]
    exact hz.ne'
  exact lt_of_le_of_ne measureReal_nonneg (Ne.symm (mul_ne_zero_iff.mp hmul).1)

/-- The private-seed factor cancels, leaving only actually observed reward terms. -/
theorem log_likelihood_eq (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (ν η : Fin n → Fin K → Measure Reward)
    [∀ t k, IsProbabilityMeasure (ν t k)] [∀ t k, IsProbabilityMeasure (η t k)]
    (hsupport : ∀ t k x, ν t k {x} = 0 ↔ η t k {x} = 0)
    (z : Transcript K Reward n) (hz : 0 < (L.transcriptLaw ρ ν).real {z}) :
    Real.log ((L.transcriptLaw ρ ν).real {z} / (L.transcriptLaw ρ η).real {z}) =
      ∑ t, Real.log ((ν t (z.1 t).1).real {(z.1 t).2} /
        (η t (z.1 t).1).real {(z.1 t).2}) := by
  have hη := FiniteInformation.atom_real_pos_of_ac _ _
    (L.transcript_absolutelyContinuous ρ ν η hsupport) z hz
  have hw := L.seedConsistency_mass_pos ρ ν z hz
  have hνf := L.observed_atom_pos ρ ν z hz
  have hηf := L.observed_atom_pos ρ η z hη
  have hνp : 0 < ∏ t, (ν t (z.1 t).1).real {(z.1 t).2} :=
    Finset.prod_pos fun t _ => hνf t
  have hηp : 0 < ∏ t, (η t (z.1 t).1).real {(z.1 t).2} :=
    Finset.prod_pos fun t _ => hηf t
  rw [Real.log_div hz.ne' hη.ne', L.transcript_atom_factorization_real,
    L.transcript_atom_factorization_real, Real.log_mul hw.ne' hνp.ne',
    Real.log_mul hw.ne' hηp.ne', Real.log_prod (fun t _ => (hνf t).ne'),
    Real.log_prod (fun t _ => (hηf t).ne')]
  have ht (t : Fin n) : Real.log ((ν t (z.1 t).1).real {(z.1 t).2} /
      (η t (z.1 t).1).real {(z.1 t).2}) =
      Real.log ((ν t (z.1 t).1).real {(z.1 t).2}) -
        Real.log ((η t (z.1 t).1).real {(z.1 t).2}) :=
    Real.log_div (hνf t).ne' (hηf t).ne'
  simp_rw [ht]
  rw [Finset.sum_sub_distrib]
  ring

/-- Finite observed KL is the expected sum of observed log factors. At null
transcripts both weighted sides are zero, so no null denominator is cancelled. -/
theorem finiteKL_eq_expected_observed_log (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (ν η : Fin n → Fin K → Measure Reward)
    [∀ t k, IsProbabilityMeasure (ν t k)] [∀ t k, IsProbabilityMeasure (η t k)]
    (hsupport : ∀ t k x, ν t k {x} = 0 ↔ η t k {x} = 0) :
    FiniteInformation.finiteKL (L.transcriptLaw ρ ν) (L.transcriptLaw ρ η) =
      ∑ z, (L.transcriptLaw ρ ν).real {z} *
        ∑ t, Real.log ((ν t (z.1 t).1).real {(z.1 t).2} /
          (η t (z.1 t).1).real {(z.1 t).2}) := by
  classical
  unfold FiniteInformation.finiteKL
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : (L.transcriptLaw ρ ν).real {z} = 0
  · simp only [hz, zero_mul]
  · rw [L.log_likelihood_eq ρ ν η hsupport z
      (lt_of_le_of_ne measureReal_nonneg (Ne.symm hz))]

/-- The same exact identity with the finite time sum outside the expectation. -/
theorem finiteKL_eq_sum_expected_observed_log (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (ν η : Fin n → Fin K → Measure Reward)
    [∀ t k, IsProbabilityMeasure (ν t k)] [∀ t k, IsProbabilityMeasure (η t k)]
    (hsupport : ∀ t k x, ν t k {x} = 0 ↔ η t k {x} = 0) :
    FiniteInformation.finiteKL (L.transcriptLaw ρ ν) (L.transcriptLaw ρ η) =
      ∑ t, ∑ z, (L.transcriptLaw ρ ν).real {z} *
        Real.log ((ν t (z.1 t).1).real {(z.1 t).2} /
          (η t (z.1 t).1).real {(z.1 t).2}) := by
  rw [L.finiteKL_eq_expected_observed_log ρ ν η hsupport]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]


/-- Regroup a finite weighted expectation by its actually observed value. -/
theorem sum_weighted_fibers {α β : Type*} [Fintype α] [Fintype β]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) [IsProbabilityMeasure μ] (obs : α → β) (f : β → ℝ) :
    (∑ a, μ.real {a} * f (obs a)) =
      ∑ b, μ.real {a | obs a = b} * f b := by
  classical
  have hevent (b : β) : μ.real {a | obs a = b} =
      ∑ a, if obs a = b then μ.real {a} else 0 := by
    simpa only [Set.mem_ofPred_eq] using
      FiniteInformation.real_event_eq_sum μ {a | obs a = b}
  symm
  simp_rw [hevent, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [ite_mul]

/-- The exact observed KL written using actual action/reward observation atoms. -/
theorem finiteKL_eq_sum_observation_atoms (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (ν η : Fin n → Fin K → Measure Reward)
    [∀ t k, IsProbabilityMeasure (ν t k)] [∀ t k, IsProbabilityMeasure (η t k)]
    (hsupport : ∀ t k x, ν t k {x} = 0 ↔ η t k {x} = 0) :
    FiniteInformation.finiteKL (L.transcriptLaw ρ ν) (L.transcriptLaw ρ η) =
      ∑ t, ∑ k, ∑ x, (L.transcriptLaw ρ ν).real {z | z.1 t = (k, x)} *
        Real.log ((ν t k).real {x} / (η t k).real {x}) := by
  rw [L.finiteKL_eq_sum_expected_observed_log ρ ν η hsupport]
  apply Finset.sum_congr rfl
  intro t _
  have h := sum_weighted_fibers (L.transcriptLaw ρ ν) (fun z => z.1 t)
    (fun o : Fin K × Reward => Real.log ((ν t o.1).real {o.2} / (η t o.1).real {o.2}))
  simpa only [Fintype.sum_prod_type] using h

/-- Finiteness precedes every use of the real value of Mathlib KL. -/
theorem transcript_klDiv_ne_top (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (ν η : Fin n → Fin K → Measure Reward)
    [∀ t k, IsProbabilityMeasure (ν t k)] [∀ t k, IsProbabilityMeasure (η t k)]
    (hsupport : ∀ t k x, ν t k {x} = 0 ↔ η t k {x} = 0) :
    InformationTheory.klDiv (L.transcriptLaw ρ ν) (L.transcriptLaw ρ η) ≠ ⊤ :=
  FiniteInformation.klDiv_ne_top _ _ (L.transcript_absolutelyContinuous ρ ν η hsupport)

/-- Mathlib KL agrees with the actual expected observed log-likelihood sum. -/
theorem toReal_klDiv_eq_sum_observation_atoms (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (ν η : Fin n → Fin K → Measure Reward)
    [∀ t k, IsProbabilityMeasure (ν t k)] [∀ t k, IsProbabilityMeasure (η t k)]
    (hsupport : ∀ t k x, ν t k {x} = 0 ↔ η t k {x} = 0) :
    (InformationTheory.klDiv (L.transcriptLaw ρ ν) (L.transcriptLaw ρ η)).toReal =
      ∑ t, ∑ k, ∑ x, (L.transcriptLaw ρ ν).real {z | z.1 t = (k, x)} *
        Real.log ((ν t k).real {x} / (η t k).real {x}) := by
  rw [FiniteInformation.toReal_klDiv_eq_finiteKL _ _
      (L.transcript_absolutelyContinuous ρ ν η hsupport),
    L.finiteKL_eq_sum_observation_atoms ρ ν η hsupport]


/-- The genuine finite adaptive chain rule, obtained from the constructed
transcript factorization and actual current-coordinate freshness. -/
theorem finiteKL_eq_sum_action_entryKL (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (ν η : Fin n → Fin K → Measure Reward)
    [∀ t k, IsProbabilityMeasure (ν t k)] [∀ t k, IsProbabilityMeasure (η t k)]
    (hsupport : ∀ t k x, ν t k {x} = 0 ↔ η t k {x} = 0) :
    FiniteInformation.finiteKL (L.transcriptLaw ρ ν) (L.transcriptLaw ρ η) =
      ∑ t, ∑ k, (L.transcriptLaw ρ ν).real {z | (z.1 t).1 = k} *
        FiniteInformation.finiteKL (ν t k) (η t k) := by
  rw [L.finiteKL_eq_sum_observation_atoms ρ ν η hsupport]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro k _
  exact L.expected_observation_factor ρ ν t k
    (fun x => Real.log ((ν t k).real {x} / (η t k).real {x}))

end BestOfBothWorlds.SeededLearner.Learner
