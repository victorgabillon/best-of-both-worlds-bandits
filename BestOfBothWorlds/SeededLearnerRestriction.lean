module

public import BestOfBothWorlds.SeededLearner

/-!
Restriction of an arbitrary learner observing real rewards to a finite actual
reward alphabet. The learner, seed, actions, and recommendation are unchanged;
finite labels are supplied to the learner through their actual real values.
-/

@[expose] public section

open MeasureTheory

namespace BestOfBothWorlds.SeededLearner

variable {Seed Reward : Type*} [MeasurableSpace Seed] [MeasurableSpace Reward] {K n : ℕ}

/-- Encode the recorded rewards, preserving their recorded actions. -/
def mapHistory (value : Reward → ℝ) {t : ℕ} (h : History K Reward t) : History K ℝ t :=
  fun s => ((h s).1, value (h s).2)

def mapTable (value : Reward → ℝ) (g : Table K Reward n) : Table K ℝ n :=
  fun t k => value (g t k)

def mapTranscript (value : Reward → ℝ) (z : Transcript K Reward n) : Transcript K ℝ n :=
  (mapHistory value z.1, z.2)

omit [MeasurableSpace Seed] [MeasurableSpace Reward] in
@[simp] theorem before_mapHistory (value : Reward → ℝ) (h : History K Reward n) (t : Fin n) :
    before (mapHistory value h) t = mapHistory value (before h t) := rfl

namespace Learner

variable (L : Learner Seed ℝ K n)

/-- Run the same real-reward learner on values of the chosen finite alphabet.
This construction has no finiteness assumption on its private seed. -/
def restrictReward (value : Reward → ℝ) : Learner Seed Reward K n where
  action t r h := L.action t r (mapHistory value h)
  action_measurable t h := L.action_measurable t (mapHistory value h)
  recommendation r h := L.recommendation r (mapHistory value h)
  recommendation_measurable h := L.recommendation_measurable (mapHistory value h)

/-- The actual interaction commutes pointwise with the reward-value encoding. -/
theorem play_restrictReward (value : Reward → ℝ) (r : Seed) (g : Table K Reward n) :
    mapHistory value ((L.restrictReward value).play r g) = L.play r (mapTable value g) := by
  funext t
  induction t using (measure (fun t : Fin n => t.val)).wf.induction with
  | h t ih =>
    have hp : mapHistory value (before ((L.restrictReward value).play r g) t) =
        before (L.play r (mapTable value g)) t := by
      funext s
      exact ih ⟨s.val, s.isLt.trans t.isLt⟩ s.isLt
    calc
      mapHistory value ((L.restrictReward value).play r g) t =
          (L.action t r (mapHistory value (before ((L.restrictReward value).play r g) t)),
            value (g t (L.action t r
              (mapHistory value (before ((L.restrictReward value).play r g) t))))) :=
        congrArg (fun q : Fin K × Reward => (q.1, value q.2))
          ((L.restrictReward value).play_eq r g t)
      _ = (L.action t r (before (L.play r (mapTable value g)) t),
          value (g t (L.action t r (before (L.play r (mapTable value g)) t)))) := by rw [hp]
      _ = L.play r (mapTable value g) t := (L.play_eq r (mapTable value g) t).symm

/-- The final recommendation is part of the commuting observed transcript. -/
theorem transcript_restrictReward (value : Reward → ℝ) (r : Seed) (g : Table K Reward n) :
    mapTranscript value ((L.restrictReward value).transcript (r, g)) =
      L.transcript (r, mapTable value g) := by
  apply Prod.ext
  · exact L.play_restrictReward value r g
  · change L.recommendation r (mapHistory value ((L.restrictReward value).play r g)) =
      L.recommendation r (L.play r (mapTable value g))
    rw [L.play_restrictReward]

theorem recommendation_restrictReward (value : Reward → ℝ) (r : Seed) (g : Table K Reward n) :
    ((L.restrictReward value).transcript (r, g)).2 =
      (L.transcript (r, mapTable value g)).2 :=
  congrArg Prod.snd (L.transcript_restrictReward value r g)

end Learner

variable [Fintype Reward] [MeasurableSingletonClass Reward]

theorem mapHistory_measurable (value : Reward → ℝ) (t : ℕ) :
    Measurable (mapHistory (K := K) (t := t) value) := measurable_of_finite _

theorem mapTable_measurable (value : Reward → ℝ) :
    Measurable (mapTable (K := K) (n := n) value) := measurable_of_finite _

theorem mapTranscript_measurable (value : Reward → ℝ) :
    Measurable (mapTranscript (K := K) (n := n) value) := measurable_of_finite _

omit [MeasurableSpace Seed] [MeasurableSpace Reward] [Fintype Reward] [MeasurableSingletonClass Reward] in
theorem mapHistory_injective (value : Reward → ℝ) (hvalue : Function.Injective value) (t : ℕ) :
    Function.Injective (mapHistory (K := K) (t := t) value) := by
  intro h h' hh
  funext s
  have he := congrFun hh s
  exact Prod.ext (congrArg (fun p : Fin K × ℝ => p.1) he)
    (hvalue (congrArg (fun p : Fin K × ℝ => p.2) he))

omit [MeasurableSpace Seed] [MeasurableSpace Reward] [Fintype Reward] [MeasurableSingletonClass Reward] in
theorem mapTranscript_injective (value : Reward → ℝ) (hvalue : Function.Injective value) :
    Function.Injective (mapTranscript (K := K) (n := n) value) := by
  intro z z' hz
  exact Prod.ext (mapHistory_injective value hvalue n
      (congrArg (fun p : Transcript K ℝ n => p.1) hz))
    (congrArg (fun p : Transcript K ℝ n => p.2) hz)


/-- Injective finite-alphabet encoding preserves exactly the observed information. -/
theorem mapTranscript_measurableEmbedding (value : Reward → ℝ)
    (hvalue : Function.Injective value) :
    MeasurableEmbedding (mapTranscript (K := K) (n := n) value) where
  injective := mapTranscript_injective value hvalue
  measurable := mapTranscript_measurable value
  measurableSet_image' := fun s _ => ((Set.toFinite s).image _).measurableSet


namespace Learner

/-- For any real table the set of its entries is finite. Thus the actual real
transcript is measurable in an arbitrary seed, without restricting the learner
to an alphabet chosen in advance. -/
theorem transcript_fixedRealTable_measurable (L : Learner Seed ℝ K n) (g : Table K ℝ n) :
    Measurable fun r => L.transcript (r, g) := by
  classical
  let A : Finset ℝ := Finset.univ.image (fun p : Fin n × Fin K => g p.1 p.2)
  let gA : Table K ↥A n := fun t k => ⟨g t k,
    Finset.mem_image.mpr ⟨(t, k), Finset.mem_univ _, rfl⟩⟩
  let value : ↥A → ℝ := Subtype.val
  have hm := (mapTranscript_measurable (K := K) (n := n) value).comp
    ((L.restrictReward value).transcript_measurable.comp
      (measurable_id.prodMk (measurable_const : Measurable fun _ : Seed => gA)))
  convert hm using 1
  funext r
  exact (L.transcript_restrictReward value r gA).symm

/-- Actual deterministic-table learner error probabilities are therefore based
on a measurable final recommendation, even for real reward learners. -/
theorem recommendation_fixedRealTable_measurable (L : Learner Seed ℝ K n) (g : Table K ℝ n) :
    Measurable fun r => (L.transcript (r, g)).2 :=
  (L.transcript_fixedRealTable_measurable g).snd

end Learner

end BestOfBothWorlds.SeededLearner
