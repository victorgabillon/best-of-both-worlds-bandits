module

public import BestOfBothWorlds.SeededLearnerRestriction
public import BestOfBothWorlds.FiniteInformation

/-!
The finite actual-value transcript encoding preserves the law and all KL
information of the real observations. Thus the finite-alphabet certificates
apply to a learner observing real rewards without supplying extra symbols.
-/

@[expose] public section

open MeasureTheory

namespace BestOfBothWorlds.SeededLearner

variable {Seed Reward : Type*} [MeasurableSpace Seed] [MeasurableSpace Reward]
  [Fintype Reward] [MeasurableSingletonClass Reward] {K n : ℕ}

namespace Learner

variable (L : Learner Seed ℝ K n)

/-- Actual observed law on real-valued transcripts from the finite reward law. -/
noncomputable def realObservedLaw (ρ : Measure Seed)
    (ν : Fin n → Fin K → Measure Reward) (value : Reward → ℝ) :
    Measure (Transcript K ℝ n) :=
  ((L.restrictReward value).transcriptLaw ρ ν).map (mapTranscript value)

/-- The real observed transcript is an actual measurable function of the
original private seed and independently generated complete finite table. -/
theorem realTranscript_measurable (value : Reward → ℝ) :
    Measurable (fun z : Seed × Table K Reward n =>
      L.transcript (z.1, mapTable value z.2)) := by
  have hm := (mapTranscript_measurable (K := K) (n := n) value).comp
    (L.restrictReward value).transcript_measurable
  convert hm using 1
  funext z
  exact (L.transcript_restrictReward value z.1 z.2).symm

/-- This law is exactly the pushforward of the independent seed/table law
through the original real-reward learner's actual interaction. -/
theorem realObservedLaw_eq_actual (ρ : Measure Seed)
    (ν : Fin n → Fin K → Measure Reward) (value : Reward → ℝ) :
    L.realObservedLaw ρ ν value =
      (ρ.prod (Learner.tableLaw ν)).map
        (fun z => L.transcript (z.1, mapTable value z.2)) := by
  unfold realObservedLaw Learner.transcriptLaw
  rw [Measure.map_map (mapTranscript_measurable value)
    (L.restrictReward value).transcript_measurable]
  congr 1
  funext z
  exact L.transcript_restrictReward value z.1 z.2

instance realObservedLaw_probability (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (ν : Fin n → Fin K → Measure Reward) [∀ t k, IsProbabilityMeasure (ν t k)]
    (value : Reward → ℝ) : IsProbabilityMeasure (L.realObservedLaw ρ ν value) :=
  by
  unfold realObservedLaw
  infer_instance

/-- Recording actual real values preserves the exact divergence when the
alphabet contains actual distinct real values, as in the paper's finite support. -/
theorem realObservedLaw_kl_eq (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (ν η : Fin n → Fin K → Measure Reward)
    [∀ t k, IsProbabilityMeasure (ν t k)] [∀ t k, IsProbabilityMeasure (η t k)]
    (value : Reward → ℝ) (hvalue : Function.Injective value)
    (a : Fin K) (x : Reward) :
    InformationTheory.klDiv (L.realObservedLaw ρ ν value) (L.realObservedLaw ρ η value) =
      InformationTheory.klDiv ((L.restrictReward value).transcriptLaw ρ ν)
        ((L.restrictReward value).transcriptLaw ρ η) := by
  let z₀ : Transcript K Reward n := (fun _ => (a, x), a)
  obtain ⟨inverse, hinverse, hleft⟩ := (mapTranscript_measurableEmbedding
    (K := K) (n := n) value hvalue).exists_measurable_extend
      (measurable_id : Measurable (id : Transcript K Reward n → Transcript K Reward n))
      (fun _ => ⟨z₀⟩)
  unfold realObservedLaw
  exact FiniteInformation.klDiv_map_eq_of_leftInverse _ _ _ inverse
    (mapTranscript_measurable value) hinverse (fun z => congrFun hleft z)

end Learner

end BestOfBothWorlds.SeededLearner
