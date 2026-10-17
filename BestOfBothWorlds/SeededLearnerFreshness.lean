module

public import BestOfBothWorlds.SeededLearner
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Lean.Elab.Tactic.Omega

/-!
Fresh reward and prefix-law identities for arbitrary measurable private seeds.
Only the actually observed past constrains the learner; the current table row
is independent of that past. The argument is a finite atom calculation under
the original independent seed/table law, with no conditional law assumption.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace BestOfBothWorlds.SeededLearner

variable {Seed Reward : Type*} [MeasurableSpace Seed] [MeasurableSpace Reward]
  [Fintype Reward] [MeasurableSingletonClass Reward] {K n : ℕ}

/-- Include a strictly earlier round in the full horizon. -/
def liftTime (t : Fin n) (s : Fin t.val) : Fin n :=
  ⟨s.val, s.isLt.trans t.isLt⟩

namespace Learner

variable (L : Learner Seed Reward K n)

omit [Fintype Reward] [MeasurableSingletonClass Reward] in
/-- The learner sees identical interaction prefixes on equal table prefixes. -/
theorem play_eq_of_prefix_eq (r : Seed) (g g' : Table K Reward n) (m : ℕ)
    (hprefix : ∀ t : Fin n, t.val < m → g t = g' t)
    (t : Fin n) (ht : t.val < m) : L.play r g t = L.play r g' t := by
  revert ht
  induction t using (measure (fun t : Fin n => t.val)).wf.induction with
  | h t ih =>
    intro ht
    have hp : before (L.play r g) t = before (L.play r g') t := by
      funext s
      exact ih ⟨s.val, s.isLt.trans t.isLt⟩ s.isLt (s.isLt.trans ht)
    rw [L.play_eq, L.play_eq, hp, hprefix t ht]

omit [Fintype Reward] [MeasurableSingletonClass Reward] in
/-- The selected action depends only on rows strictly before its round. -/
theorem action_eq_of_before_eq (r : Seed) (g g' : Table K Reward n) (t : Fin n)
    (hprefix : ∀ s : Fin n, s.val < t.val → g s = g' s) :
    (L.play r g t).1 = (L.play r g' t).1 := by
  have hp : before (L.play r g) t = before (L.play r g') t := by
    funext s
    exact L.play_eq_of_prefix_eq r g g' t.val hprefix
      ⟨s.val, s.isLt.trans t.isLt⟩ s.isLt
  simp only [L.play_eq, hp]

/-- Seed choices consistent with a recorded prefix and its next action. -/
def prefixSeedConsistency (t : Fin n) (h : History K Reward t.val) (k : Fin K) : Set Seed :=
  {r | (∀ s : Fin t.val, L.action (liftTime t s) r (before h s) = (h s).1) ∧
    L.action t r h = k}

omit [Fintype Reward] [MeasurableSingletonClass Reward] in
theorem prefixSeedConsistency_measurable (t : Fin n) (h : History K Reward t.val)
    (k : Fin K) : MeasurableSet (L.prefixSeedConsistency t h k) := by
  apply MeasurableSet.inter
  · have hm := MeasurableSet.iInter fun s =>
      measurableSet_eq_fun (L.action_measurable (liftTime t s) (before h s))
        (measurable_const : Measurable fun _ : Seed => (h s).1)
    rw [Set.iInter_ofPred] at hm
    simpa only [Set.ofPred] using hm
  · exact measurableSet_eq_fun (L.action_measurable t h) measurable_const

end Learner

/-- Past selected-coordinate constraints in one complete table row. -/
def prefixRowConstraint (t : Fin n) (h : History K Reward t.val) (u : Fin n) :
    Set (Fin K → Reward) :=
  if hu : u.val < t.val then {y | y (h ⟨u.val, hu⟩).1 = (h ⟨u.val, hu⟩).2}
  else Set.univ

/-- The prefix constraints involve no entry in the current or future rows. -/
def prefixTableConsistency (t : Fin n) (h : History K Reward t.val) : Set (Table K Reward n) :=
  Set.pi Set.univ (prefixRowConstraint t h)

omit [MeasurableSpace Reward] [Fintype Reward] [MeasurableSingletonClass Reward] in
theorem prefixTableConsistency_iff (t : Fin n) (h : History K Reward t.val)
    (g : Table K Reward n) :
    g ∈ prefixTableConsistency t h ↔
      ∀ s : Fin t.val, g (liftTime t s) (h s).1 = (h s).2 := by
  simp only [prefixTableConsistency, Set.mem_pi, Set.mem_univ, forall_const]
  constructor
  · intro hg s
    have hs := hg (liftTime t s)
    have hst : (liftTime t s).val < t.val := s.isLt
    rw [prefixRowConstraint, dite_eq_left hst] at hs
    simpa only [liftTime, Set.mem_ofPred_eq] using hs
  · intro hg u
    by_cases hu : u.val < t.val
    · simpa only [prefixRowConstraint, hu, dite_true, Set.mem_ofPred_eq, liftTime]
        using hg ⟨u.val, hu⟩
    · simp only [prefixRowConstraint, hu, dite_false, Set.mem_univ]

omit [MeasurableSpace Reward] [Fintype Reward] [MeasurableSingletonClass Reward] in
theorem prefixRowConstraint_current (t : Fin n) (h : History K Reward t.val) :
    prefixRowConstraint t h t = Set.univ := by simp [prefixRowConstraint]

theorem prefixTableConsistency_measurable (t : Fin n) (h : History K Reward t.val) :
    MeasurableSet (prefixTableConsistency t h) := by
  apply MeasurableSet.pi Set.countable_univ
  intro u _
  unfold prefixRowConstraint
  split_ifs
  · exact measurableSet_eq_fun (measurable_pi_apply _) measurable_const
  · exact MeasurableSet.univ

namespace Learner

variable (L : Learner Seed Reward K n)

omit [Fintype Reward] [MeasurableSingletonClass Reward] in
/-- Exact consistency characterization before the current reward is revealed. -/
theorem before_play_eq_iff (r : Seed) (g : Table K Reward n) (t : Fin n)
    (h : History K Reward t.val) :
    before (L.play r g) t = h ↔
      (∀ s : Fin t.val, L.action (liftTime t s) r (before h s) = (h s).1) ∧
        g ∈ prefixTableConsistency t h := by
  constructor
  · intro hh
    have hp (s : Fin t.val) : before (L.play r g) (liftTime t s) = before h s := by
      funext q
      exact congrFun hh ⟨q.val, q.isLt.trans s.isLt⟩
    constructor
    · intro s
      have he := congrArg Prod.fst (congrFun hh s)
      change (L.play r g (liftTime t s)).1 = (h s).1 at he
      simpa only [L.play_eq, hp s] using he
    · apply (prefixTableConsistency_iff t h g).mpr
      intro s
      have he := congrArg Prod.snd (congrFun hh s)
      have ha := congrArg Prod.fst (congrFun hh s)
      change (L.play r g (liftTime t s)).2 = (h s).2 at he
      change (L.play r g (liftTime t s)).1 = (h s).1 at ha
      rw [L.play_eq, hp s] at he ha
      change L.action (liftTime t s) r (before h s) = (h s).1 at ha
      simpa only [ha] using he
  · rintro ⟨ha, hg⟩
    have htable := (prefixTableConsistency_iff t h g).mp hg
    funext s
    induction s using (measure (fun s : Fin t.val => s.val)).wf.induction with
    | h s ih =>
      have hp : before (L.play r g) (liftTime t s) = before h s := by
        funext q
        exact ih ⟨q.val, q.isLt.trans s.isLt⟩ q.isLt
      change L.play r g (liftTime t s) = h s
      rw [L.play_eq, hp, ha s, htable s]

omit [Fintype Reward] [MeasurableSingletonClass Reward] in
/-- A recorded prefix and next action define an actual seed/table rectangle. -/
theorem prefix_action_event_eq (t : Fin n) (h : History K Reward t.val) (k : Fin K) :
    {z : Seed × Table K Reward n |
      before (L.play z.1 z.2) t = h ∧ (L.play z.1 z.2 t).1 = k} =
      L.prefixSeedConsistency t h k ×ˢ prefixTableConsistency t h := by
  ext z
  change (before (L.play z.1 z.2) t = h ∧ (L.play z.1 z.2 t).1 = k) ↔
    ((∀ s : Fin t.val, L.action (liftTime t s) z.1 (before h s) = (h s).1) ∧
      L.action t z.1 h = k) ∧ z.2 ∈ prefixTableConsistency t h
  constructor
  · rintro ⟨hh, hk⟩
    obtain ⟨ha, hg⟩ := (L.before_play_eq_iff z.1 z.2 t h).mp hh
    exact ⟨⟨ha, by simpa only [L.play_eq, hh] using hk⟩, hg⟩
  · rintro ⟨⟨ha, hk⟩, hg⟩
    have hh := (L.before_play_eq_iff z.1 z.2 t h).mpr ⟨ha, hg⟩
    exact ⟨hh, by simpa only [L.play_eq, hh] using hk⟩

omit [Fintype Reward] [MeasurableSingletonClass Reward] in
/-- Adding the current observation constrains exactly one additional coordinate. -/
theorem prefix_observation_event_eq (t : Fin n) (h : History K Reward t.val)
    (k : Fin K) (x : Reward) :
    {z : Seed × Table K Reward n |
      before (L.play z.1 z.2) t = h ∧ L.play z.1 z.2 t = (k, x)} =
      L.prefixSeedConsistency t h k ×ˢ
        (prefixTableConsistency t h ∩ {g | g t k = x}) := by
  ext z
  constructor
  · rintro ⟨hh, hx⟩
    have hk := congrArg Prod.fst hx
    have he := congrArg Prod.snd hx
    have hc := Set.ext_iff.mp (L.prefix_action_event_eq t h k) z
    have hz := hc.mp ⟨hh, hk⟩
    have hact : L.action t z.1 (before (L.play z.1 z.2) t) = k := by
      simpa only [L.play_eq] using hk
    refine ⟨hz.1, hz.2, ?_⟩
    simpa only [Set.mem_ofPred_eq, L.play_eq, hact] using he
  · rintro ⟨hr, hg, hx⟩
    have hc := Set.ext_iff.mp (L.prefix_action_event_eq t h k) z
    obtain ⟨hh, hk⟩ := hc.mpr ⟨hr, hg⟩
    have hact : L.action t z.1 (before (L.play z.1 z.2) t) = k := by
      simpa only [L.play_eq] using hk
    refine ⟨hh, Prod.ext hk ?_⟩
    simpa only [Set.mem_ofPred_eq, L.play_eq, hact] using hx

end Learner

/-- A finite product rectangle places no restriction at one fresh coordinate. -/
theorem pi_inter_fresh_coordinate {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace α] (μ : ι → Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    (A : ι → Set α) (i : ι) (hi : A i = Set.univ) (B : Set α) :
    Measure.pi μ (Set.pi Set.univ A ∩ {g | g i ∈ B}) =
      Measure.pi μ (Set.pi Set.univ A) * μ i B := by
  have hs : Set.pi Set.univ A ∩ {g | g i ∈ B} =
      Set.pi Set.univ (Function.update A i B) := by
    ext g
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_const]
    constructor
    · rintro ⟨hg, hgi⟩ j
      by_cases hj : j = i
      · simpa only [hj, Function.update_self] using hgi
      · simpa only [Function.update_of_ne hj] using hg j
    · intro hg
      refine ⟨?_, ?_⟩
      · intro j
        by_cases hj : j = i
        · simp only [hj, hi, Set.mem_univ]
        · simpa only [Function.update_of_ne hj] using hg j
      · simpa only [Function.update_self] using hg i
  rw [hs, Measure.pi_pi, Measure.pi_pi]
  have hp : (fun j => μ j (Function.update A i B j)) =
      fun j => μ j (A j) * (if j = i then μ i B else 1) := by
    funext j
    by_cases hj : j = i
    · simp only [hj, Function.update_self, hi, measure_univ, ite_true, one_mul]
    · simp only [Function.update_of_ne hj, hj, ite_false, mul_one]
  rw [hp, Finset.prod_mul_distrib]
  simp

omit [Fintype Reward] [MeasurableSingletonClass Reward] in
/-- The unobserved current row integrates independently of all prefix constraints. -/
theorem prefixTableConsistency_fresh_mass (ν : Fin n → Fin K → Measure Reward)
    [∀ t k, IsProbabilityMeasure (ν t k)] (t : Fin n)
    (h : History K Reward t.val) (k : Fin K) (x : Reward) :
    Learner.tableLaw ν (prefixTableConsistency t h ∩ {g | g t k = x}) =
      Learner.tableLaw ν (prefixTableConsistency t h) * ν t k {x} := by
  have hrow : (Measure.pi (ν t)) {y : Fin K → Reward | y k = x} = ν t k {x} := by
    have heq : {y : Fin K → Reward | y k = x} =
        Set.pi Set.univ (fun a => if a = k then {x} else Set.univ) := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_const]
      constructor
      · intro hy a
        by_cases ha : a = k
        · simpa only [ha, ite_true, Set.mem_singleton_iff] using hy
        · simp only [ha, ite_false, Set.mem_univ]
      · intro hy
        simpa only [ite_true, Set.mem_singleton_iff] using hy k
    rw [heq, Measure.pi_pi]
    simp only [apply_ite, measure_univ]
    simp
  change (Measure.pi fun u => Measure.pi (ν u))
    (Set.pi Set.univ (prefixRowConstraint t h) ∩
      {g | g t ∈ {y : Fin K → Reward | y k = x}}) = _
  rw [pi_inter_fresh_coordinate _ _ t (prefixRowConstraint_current t h), hrow]
  rfl

namespace Learner

variable (L : Learner Seed Reward K n)

theorem before_play_measurable (t : Fin n) :
    Measurable fun z : Seed × Table K Reward n => before (L.play z.1 z.2) t :=
  Measurable.of_eval fun s => L.play_measurable (liftTime t s)

/-- An elementary finite measurable partition, used without conditioning. -/
theorem measure_partition_by {Ω H : Type*} [MeasurableSpace Ω]
    [MeasurableSpace H] [Fintype H] [MeasurableSingletonClass H]
    (μ : Measure Ω) (f : Ω → H) (hf : Measurable f)
    (s : Set Ω) (hs : MeasurableSet s) :
    μ s = ∑ h : H, μ {z | f z = h ∧ z ∈ s} := by
  classical
  have heq : s = ⋃ h : H, {z | f z = h ∧ z ∈ s} := by
    ext z
    simp
  have hdisjoint : Pairwise (fun h h' : H =>
      Disjoint {z | f z = h ∧ z ∈ s} {z | f z = h' ∧ z ∈ s}) := by
    intro h h' hne
    apply Set.disjoint_left.mpr
    intro z hz hz'
    exact hne (hz.1.symm.trans hz'.1)
  calc
    μ s = μ (⋃ h : H, {z | f z = h ∧ z ∈ s}) := congrArg μ heq
    _ = _ := by
      rw [measure_iUnion hdisjoint (fun h =>
        (measurableSet_eq_fun hf measurable_const).inter hs), tsum_fintype]

omit [Fintype Reward] [MeasurableSingletonClass Reward] in
/-- The fresh coordinate multiplies an actual prefix-and-action atom. -/
theorem prefix_observation_factorization (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (ν : Fin n → Fin K → Measure Reward) [∀ t k, IsProbabilityMeasure (ν t k)]
    (t : Fin n) (h : History K Reward t.val) (k : Fin K) (x : Reward) :
    (ρ.prod (tableLaw ν))
        {z | before (L.play z.1 z.2) t = h ∧ L.play z.1 z.2 t = (k, x)} =
      (ρ.prod (tableLaw ν))
        {z | before (L.play z.1 z.2) t = h ∧ (L.play z.1 z.2 t).1 = k} * ν t k {x} := by
  rw [L.prefix_observation_event_eq, L.prefix_action_event_eq, Measure.prod_prod,
    Measure.prod_prod, prefixTableConsistency_fresh_mass]
  exact (mul_assoc _ _ _).symm

/-- Current selected rewards are fresh under the actual seed/table law. -/
theorem play_observation_factorization (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (ν : Fin n → Fin K → Measure Reward) [∀ t k, IsProbabilityMeasure (ν t k)]
    (t : Fin n) (k : Fin K) (x : Reward) :
    (ρ.prod (tableLaw ν)) {z | L.play z.1 z.2 t = (k, x)} =
      (ρ.prod (tableLaw ν)) {z | (L.play z.1 z.2 t).1 = k} * ν t k {x} := by
  rw [measure_partition_by (ρ.prod (tableLaw ν)) _ (L.before_play_measurable t)
    _ (measurableSet_eq_fun (L.play_measurable t) measurable_const)]
  rw [measure_partition_by (ρ.prod (tableLaw ν)) _ (L.before_play_measurable t)
    _ (measurableSet_eq_fun (L.play_measurable t).fst measurable_const)]
  simp only [Set.mem_ofPred_eq]
  simp_rw [L.prefix_observation_factorization]
  rw [Finset.sum_mul]

/-- The same fresh-observation factorization stated on the observed transcript. -/
theorem observation_atom_factorization (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (ν : Fin n → Fin K → Measure Reward) [∀ t k, IsProbabilityMeasure (ν t k)]
    (t : Fin n) (k : Fin K) (x : Reward) :
    L.transcriptLaw ρ ν {z | z.1 t = (k, x)} =
      L.transcriptLaw ρ ν {z | (z.1 t).1 = k} * ν t k {x} := by
  have hj : MeasurableSet {z : Transcript K Reward n | z.1 t = (k, x)} :=
    measurableSet_eq_fun ((measurable_pi_apply t).comp measurable_fst) measurable_const
  have ha : MeasurableSet {z : Transcript K Reward n | (z.1 t).1 = k} :=
    measurableSet_eq_fun (((measurable_pi_apply t).comp measurable_fst).fst) measurable_const
  rw [transcriptLaw, Measure.map_apply L.transcript_measurable hj,
    Measure.map_apply L.transcript_measurable ha]
  exact L.play_observation_factorization ρ ν t k x

theorem observation_real_factorization (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (ν : Fin n → Fin K → Measure Reward) [∀ t k, IsProbabilityMeasure (ν t k)]
    (t : Fin n) (k : Fin K) (x : Reward) :
    (L.transcriptLaw ρ ν).real {z | z.1 t = (k, x)} =
      (L.transcriptLaw ρ ν).real {z | (z.1 t).1 = k} * (ν t k).real {x} := by
  simpa only [measureReal_def, ENNReal.toReal_mul] using
    congrArg ENNReal.toReal (L.observation_atom_factorization ρ ν t k x)

/-- Finite expected reward/log factor, ready to be summed over informative pulls. -/
theorem expected_observation_factor (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (ν : Fin n → Fin K → Measure Reward) [∀ t k, IsProbabilityMeasure (ν t k)]
    (t : Fin n) (k : Fin K) (f : Reward → ℝ) :
    (∑ x, (L.transcriptLaw ρ ν).real {z | z.1 t = (k, x)} * f x) =
      (L.transcriptLaw ρ ν).real {z | (z.1 t).1 = k} *
        ∑ x, (ν t k).real {x} * f x := by
  simp_rw [L.observation_real_factorization, mul_assoc]
  rw [Finset.mul_sum]

omit [Fintype Reward] [MeasurableSingletonClass Reward] in
/-- Prefix-action atom masses use only reward laws at strictly earlier rounds. -/
theorem prefix_action_mass_eq (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (ν η : Fin n → Fin K → Measure Reward)
    [∀ t k, IsProbabilityMeasure (ν t k)] [∀ t k, IsProbabilityMeasure (η t k)]
    (t : Fin n) (h : History K Reward t.val) (k : Fin K)
    (hprefix : ∀ u : Fin n, u.val < t.val → ∀ a, ν u a = η u a) :
    (ρ.prod (tableLaw ν))
      {z | before (L.play z.1 z.2) t = h ∧ (L.play z.1 z.2 t).1 = k} =
    (ρ.prod (tableLaw η))
      {z | before (L.play z.1 z.2) t = h ∧ (L.play z.1 z.2 t).1 = k} := by
  rw [L.prefix_action_event_eq, Measure.prod_prod, Measure.prod_prod]
  congr 1
  change (Measure.pi fun u => Measure.pi (ν u)) (Set.pi Set.univ (prefixRowConstraint t h)) =
    (Measure.pi fun u => Measure.pi (η u)) (Set.pi Set.univ (prefixRowConstraint t h))
  rw [Measure.pi_pi, Measure.pi_pi]
  apply Finset.prod_congr rfl
  intro u _
  by_cases hu : u.val < t.val
  · have hrow : ν u = η u := funext (hprefix u hu)
    rw [hrow]
  · simp only [prefixRowConstraint, hu, dite_false, measure_univ]

/-- Actual selected-action probabilities agree when the earlier environment agrees. -/
theorem action_mass_eq_of_prefix (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (ν η : Fin n → Fin K → Measure Reward)
    [∀ t k, IsProbabilityMeasure (ν t k)] [∀ t k, IsProbabilityMeasure (η t k)]
    (t : Fin n) (k : Fin K)
    (hprefix : ∀ u : Fin n, u.val < t.val → ∀ a, ν u a = η u a) :
    L.transcriptLaw ρ ν {z | (z.1 t).1 = k} =
      L.transcriptLaw ρ η {z | (z.1 t).1 = k} := by
  have ha : MeasurableSet {z : Transcript K Reward n | (z.1 t).1 = k} :=
    measurableSet_eq_fun (((measurable_pi_apply t).comp measurable_fst).fst) measurable_const
  simp only [transcriptLaw, Measure.map_apply L.transcript_measurable ha]
  change (ρ.prod (tableLaw ν)) {z | (L.play z.1 z.2 t).1 = k} =
    (ρ.prod (tableLaw η)) {z | (L.play z.1 z.2 t).1 = k}
  rw [measure_partition_by (ρ.prod (tableLaw ν)) _ (L.before_play_measurable t)
      _ (measurableSet_eq_fun (L.play_measurable t).fst measurable_const),
    measure_partition_by (ρ.prod (tableLaw η)) _ (L.before_play_measurable t)
      _ (measurableSet_eq_fun (L.play_measurable t).fst measurable_const)]
  simp only [Set.mem_ofPred_eq]
  apply Finset.sum_congr rfl
  intro h _
  exact L.prefix_action_mass_eq ρ ν η t h k hprefix

end Learner

end BestOfBothWorlds.SeededLearner
