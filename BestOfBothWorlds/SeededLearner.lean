module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Data.Fin.Tuple.Basic

/-!
A finite-horizon learner with an arbitrary measurable private seed. Actions and
recommendations use only that seed and recorded observations. The reward alphabet
is any finite measurable type with measurable singletons; a finite subset of
[0,1] can be used directly, without restricting common rewards to Bernoulli laws.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace BestOfBothWorlds.SeededLearner

abbrev History (K : ℕ) (Reward : Type*) (t : ℕ) := Fin t → Fin K × Reward
abbrev Table (K : ℕ) (Reward : Type*) (n : ℕ) := Fin n → Fin K → Reward
abbrev Transcript (K : ℕ) (Reward : Type*) (n : ℕ) := History K Reward n × Fin K

/-- The strictly earlier portion of a recorded interaction. -/
def before {K n : ℕ} {Reward : Type*} (h : History K Reward n) (t : Fin n) :
    History K Reward t.val := fun s => h ⟨s.val, s.isLt.trans t.isLt⟩

variable {Seed Reward : Type*} [MeasurableSpace Seed] [MeasurableSpace Reward]
  [Fintype Reward] [MeasurableSingletonClass Reward] {K n : ℕ}

/-- Fixing one seed makes the whole adaptive learner deterministic. Its seed may
contain persistent state and all final recommendation randomness. -/
structure Learner (Seed Reward : Type*) [MeasurableSpace Seed] [MeasurableSpace Reward]
    (K n : ℕ) where
  action : (t : Fin n) → Seed → History K Reward t.val → Fin K
  action_measurable : ∀ t h, Measurable fun r => action t r h
  recommendation : Seed → History K Reward n → Fin K
  recommendation_measurable : ∀ h, Measurable fun r => recommendation r h

namespace Learner

variable (L : Learner Seed Reward K n)

theorem action_joint_measurable (t : Fin n) :
    Measurable fun z : Seed × History K Reward t.val => L.action t z.1 z.2 :=
  measurable_from_prod_countable_left (L.action_measurable t)

theorem recommendation_joint_measurable :
    Measurable fun z : Seed × History K Reward n => L.recommendation z.1 z.2 :=
  measurable_from_prod_countable_left L.recommendation_measurable

/-- Actual interaction with a complete table, revealing only the chosen entry. -/
def play (L : Learner Seed Reward K n) (r : Seed) (g : Table K Reward n) (t : Fin n) : Fin K × Reward :=
  let h : History K Reward t.val := fun s => play L r g ⟨s.val, s.isLt.trans t.isLt⟩
  let a := L.action t r h
  (a, g t a)
termination_by t.val

omit [Fintype Reward] [MeasurableSingletonClass Reward] in
theorem play_eq (r : Seed) (g : Table K Reward n) (t : Fin n) :
    L.play r g t = (L.action t r (before (L.play r g) t),
      g t (L.action t r (before (L.play r g) t))) := by
  rw [play]
  rfl

/-- The observed transcript includes the final (possibly randomized) recommendation. -/
def transcript (z : Seed × Table K Reward n) : Transcript K Reward n :=
  (L.play z.1 z.2, L.recommendation z.1 (L.play z.1 z.2))

theorem play_measurable (t : Fin n) :
    Measurable fun z : Seed × Table K Reward n => L.play z.1 z.2 t := by
  induction t using (measure (fun t : Fin n => t.val)).wf.induction with
  | h t ih =>
    have hp : Measurable fun z : Seed × Table K Reward n =>
        before (L.play z.1 z.2) t :=
      Measurable.of_eval fun s => ih ⟨s.val, s.isLt.trans t.isLt⟩ s.isLt
    have ha := (L.action_joint_measurable t).comp (measurable_fst.prodMk hp)
    have heval : Measurable fun z : Fin K × (Fin K → Reward) => z.2 z.1 :=
      measurable_from_prod_countable_right fun k => measurable_pi_apply k
    have hr := heval.comp (ha.prodMk ((measurable_pi_apply t).comp measurable_snd))
    convert ha.prodMk hr using 1
    funext z
    exact L.play_eq z.1 z.2 t

theorem interaction_measurable :
    Measurable fun z : Seed × Table K Reward n => L.play z.1 z.2 :=
  Measurable.of_eval L.play_measurable

theorem transcript_measurable : Measurable L.transcript :=
  L.interaction_measurable.prodMk
    (L.recommendation_joint_measurable.comp (measurable_fst.prodMk L.interaction_measurable))

theorem recommendation_fixedTable_measurable (g : Table K Reward n) :
    Measurable fun r => (L.transcript (r, g)).2 :=
  L.transcript_measurable.snd.comp (measurable_id.prodMk measurable_const)

/-- Seeds that would choose the recorded actions and recommendation when supplied
exactly the recorded observations. This set does not involve an environment. -/
def seedConsistency (z : Transcript K Reward n) : Set Seed :=
  {r | (∀ t, L.action t r (before z.1 t) = (z.1 t).1) ∧ L.recommendation r z.1 = z.2}

/-- Only the selected coordinate at each round is constrained. -/
def tableConsistency (h : History K Reward n) : Set (Table K Reward n) :=
  {g | ∀ t, g t (h t).1 = (h t).2}

omit [Fintype Reward] [MeasurableSingletonClass Reward] in
theorem seedConsistency_measurable (z : Transcript K Reward n) :
    MeasurableSet (L.seedConsistency z) := by
  apply MeasurableSet.inter
  · have hm := MeasurableSet.iInter fun t =>
      measurableSet_eq_fun (L.action_measurable t (before z.1 t))
        (measurable_const : Measurable fun _ : Seed => (z.1 t).1)
    rw [Set.iInter_ofPred] at hm
    simpa only [Set.ofPred] using hm
  · exact measurableSet_eq_fun (L.recommendation_measurable z.1) measurable_const

theorem tableConsistency_measurable (h : History K Reward n) :
    MeasurableSet (tableConsistency h) := by
  have hm := MeasurableSet.iInter fun t => measurableSet_eq_fun
    ((measurable_pi_apply (h t).1).comp (measurable_pi_apply t))
    (measurable_const : Measurable fun _ : Table K Reward n => (h t).2)
  convert hm using 1
  ext g
  simp [tableConsistency]

omit [Fintype Reward] [MeasurableSingletonClass Reward] in
theorem play_eq_iff (r : Seed) (g : Table K Reward n) (h : History K Reward n) :
    L.play r g = h ↔
      (∀ t, L.action t r (before h t) = (h t).1) ∧ g ∈ tableConsistency h := by
  constructor
  · intro hh
    constructor
    · intro t
      have he := congrArg Prod.fst (congrFun hh t)
      rw [L.play_eq] at he
      simpa only [hh] using he
    · intro t
      have he := congrArg Prod.snd (congrFun hh t)
      have ha := congrArg Prod.fst (congrFun hh t)
      rw [L.play_eq] at he ha
      change L.action t r (before (L.play r g) t) = (h t).1 at ha
      simpa only [ha] using he
  · rintro ⟨ha, hg⟩
    funext t
    induction t using (measure (fun t : Fin n => t.val)).wf.induction with
    | h t ih =>
      have hp : before (L.play r g) t = before h t := by
        funext s
        exact ih ⟨s.val, s.isLt.trans t.isLt⟩ s.isLt
      rw [L.play_eq, hp, ha t, hg t]

omit [Fintype Reward] [MeasurableSingletonClass Reward] in
/-- The transcript atom is an actual rectangle in independent seed/table space. -/
theorem transcript_preimage_singleton (z : Transcript K Reward n) :
    L.transcript ⁻¹' {z} = L.seedConsistency z ×ˢ tableConsistency z.1 := by
  ext rg
  change L.transcript rg = z ↔
    ((∀ t, L.action t rg.1 (before z.1 t) = (z.1 t).1) ∧
      L.recommendation rg.1 z.1 = z.2) ∧ rg.2 ∈ tableConsistency z.1
  constructor
  · intro hz
    have hh : L.play rg.1 rg.2 = z.1 := congrArg Prod.fst hz
    have hj := congrArg Prod.snd hz
    change L.recommendation rg.1 (L.play rg.1 rg.2) = z.2 at hj
    rw [hh] at hj
    obtain ⟨ha, hg⟩ := (L.play_eq_iff rg.1 rg.2 z.1).mp hh
    exact ⟨⟨ha, hj⟩, hg⟩
  · rintro ⟨⟨ha, hj⟩, hg⟩
    have hh := (L.play_eq_iff rg.1 rg.2 z.1).mpr ⟨ha, hg⟩
    exact Prod.ext hh (by simpa only [transcript, hh] using hj)

/-- A full table generated before interaction with independent arm-round entries. -/
noncomputable def tableLaw (ν : Fin n → Fin K → Measure Reward) : Measure (Table K Reward n) :=
  Measure.pi fun t => Measure.pi (ν t)

instance tableLaw_isProbabilityMeasure (ν : Fin n → Fin K → Measure Reward)
    [∀ t k, IsProbabilityMeasure (ν t k)] : IsProbabilityMeasure (tableLaw ν) := by
  unfold tableLaw
  infer_instance

/-- The same private-seed learner is pushed forward from an independent seed/table law. -/
noncomputable def transcriptLaw (ρ : Measure Seed) (ν : Fin n → Fin K → Measure Reward) :
    Measure (Transcript K Reward n) :=
  (ρ.prod (tableLaw ν)).map L.transcript

instance transcriptLaw_isProbabilityMeasure (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (ν : Fin n → Fin K → Measure Reward) [∀ t k, IsProbabilityMeasure (ν t k)] :
    IsProbabilityMeasure (L.transcriptLaw ρ ν) :=
by
  unfold transcriptLaw
  infer_instance

omit [MeasurableSpace Reward] [Fintype Reward] [MeasurableSingletonClass Reward] in
theorem tableConsistency_eq_pi (h : History K Reward n) :
    tableConsistency h = Set.pi Set.univ (fun t =>
      Set.pi Set.univ (fun k => if k = (h t).1 then {(h t).2} else Set.univ)) := by
  classical
  ext g
  simp only [tableConsistency, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_const]
  constructor
  · intro hg t k
    by_cases hk : k = (h t).1
    · simpa only [hk, ite_true, Set.mem_singleton_iff] using hg t
    · simp only [hk, ite_false, Set.mem_univ]
  · intro hg t
    simpa only [ite_true, Set.mem_singleton_iff] using hg t (h t).1

omit [Fintype Reward] [MeasurableSingletonClass Reward] in
/-- Unobserved coordinates integrate to one, including deterministic common laws. -/
theorem tableConsistency_mass (ν : Fin n → Fin K → Measure Reward)
    [∀ t k, IsProbabilityMeasure (ν t k)] (h : History K Reward n) :
    tableLaw ν (tableConsistency h) = ∏ t, ν t (h t).1 {(h t).2} := by
  classical
  rw [tableConsistency_eq_pi, tableLaw, Measure.pi_pi]
  congr 1
  funext t
  rw [Measure.pi_pi]
  simp only [apply_ite, measure_univ]
  simp

/-- The exact observed-transcript likelihood factorization. The learner factor
may vanish and is not asserted to be normalized over possible transcripts. -/
theorem transcript_atom_factorization (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (ν : Fin n → Fin K → Measure Reward) [∀ t k, IsProbabilityMeasure (ν t k)]
    (z : Transcript K Reward n) :
    L.transcriptLaw ρ ν {z} =
      ρ (L.seedConsistency z) * ∏ t, ν t (z.1 t).1 {(z.1 t).2} := by
  rw [transcriptLaw, Measure.map_apply L.transcript_measurable (measurableSet_singleton z),
    L.transcript_preimage_singleton, Measure.prod_prod, tableConsistency_mass]

/-- Common entrywise support gives common observed support even for deterministic
or zero-probability action choices and zero learner-consistency factors. -/
theorem transcript_atom_eq_zero_iff (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (ν η : Fin n → Fin K → Measure Reward)
    [∀ t k, IsProbabilityMeasure (ν t k)] [∀ t k, IsProbabilityMeasure (η t k)]
    (hsupport : ∀ t k x, ν t k {x} = 0 ↔ η t k {x} = 0)
    (z : Transcript K Reward n) :
    L.transcriptLaw ρ ν {z} = 0 ↔ L.transcriptLaw ρ η {z} = 0 := by
  classical
  rw [L.transcript_atom_factorization, L.transcript_atom_factorization]
  simp only [mul_eq_zero, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and]
  exact or_congr Iff.rfl (exists_congr fun t => hsupport t (z.1 t).1 (z.1 t).2)

end Learner

end BestOfBothWorlds.SeededLearner
