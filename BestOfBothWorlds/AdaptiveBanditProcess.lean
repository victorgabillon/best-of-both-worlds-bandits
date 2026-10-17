module
public import BestOfBothWorlds.ConditionalImportanceWeighting
public import Mathlib.Probability.Process.Filtration

/-!
A finite adaptive trajectory is built by adjoining one Step 18C outcome to
the previous trajectory. Its observed history retains only selected arms
and their observed rewards. Prefixes have exactly their recursively defined
laws, including when later actions depend on earlier observations.

Round indices start at zero: the history at time `t` precedes action `t`.
The natural filtration stops at the horizon and never adds latent reward
coordinates. Policies use observed histories; persistent private learner
state and separate randomized tie resolution are not encoded here.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory
namespace BestOfBothWorlds.AdaptiveBanditProcess

/-- The learner sees only past selected arms and their observed rewards. -/
def ObservedHistory (K : ℕ) : ℕ → Type
  | 0 => Unit
  | t + 1 => ObservedHistory K t × (Fin K × ℝ)

instance observedHistoryMeasurableSpace (K : ℕ) : (t : ℕ) → MeasurableSpace (ObservedHistory K t)
  | 0 => inferInstanceAs (MeasurableSpace Unit)
  | t + 1 => letI := observedHistoryMeasurableSpace K t
             inferInstanceAs (MeasurableSpace (ObservedHistory K t × (Fin K × ℝ)))

/-- Latent potential rewards are stored in the sample space, outside observed histories. -/
def Trajectory (K : ℕ) : ℕ → Type
  | 0 => Unit
  | t + 1 => ConditionalImportanceWeighting.Outcome (Trajectory K t) K

instance trajectoryMeasurableSpace (K : ℕ) : (t : ℕ) → MeasurableSpace (Trajectory K t)
  | 0 => inferInstanceAs (MeasurableSpace Unit)
  | t + 1 => letI := trajectoryMeasurableSpace K t
             inferInstanceAs (MeasurableSpace (ConditionalImportanceWeighting.Outcome (Trajectory K t) K))

/-- Observation discards every unselected reward coordinate. -/
def observe {K : ℕ} : {t : ℕ} → Trajectory K t → ObservedHistory K t
  | 0, _ => ()
  | _t + 1, z => (observe z.1.1, (z.1.2, z.2 z.1.2))

lemma observe_measurable (K t : ℕ) : Measurable (@observe K t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
      exact (ih.comp ConditionalImportanceWeighting.history_measurable).prodMk
        (ConditionalImportanceWeighting.action_measurable.prodMk ConditionalImportanceWeighting.observedReward_measurable)

/-- Restrict a latent trajectory to its first `t` rounds. -/
def trajectoryPrefix {K : ℕ} (t n : ℕ) (ht : t ≤ n) : Trajectory K n → Trajectory K t :=
  @Nat.leRec t (fun n _ => Trajectory K n → Trajectory K t) id
    (fun _ _ f z => f z.1.1) n ht

@[simp] lemma prefix_self {K : ℕ} (t : ℕ) : trajectoryPrefix (K := K) t t le_rfl = id := by
  simp [trajectoryPrefix]

lemma prefix_succ {K : ℕ} (t n : ℕ) (ht : t ≤ n) :
    trajectoryPrefix (K := K) t (n+1) (ht.trans (Nat.le_succ n)) =
      fun z => trajectoryPrefix t n ht z.1.1 := by
  unfold trajectoryPrefix
  rw [Nat.leRec_succ _ _ ht]

lemma prefix_measurable {K t n : ℕ} (ht : t ≤ n) :
    Measurable (trajectoryPrefix (K := K) t n ht) := by
  induction n, ht using Nat.le_induction with
  | base => simpa using (measurable_id : Measurable (id : Trajectory K t → Trajectory K t))
  | succ n ht ih =>
      rw [prefix_succ t n ht]
      exact ih.comp ConditionalImportanceWeighting.history_measurable

lemma prefix_comp {K s t n : ℕ} (hst : s ≤ t) (htn : t ≤ n) :
    (fun z => trajectoryPrefix (K := K) s t hst (trajectoryPrefix t n htn z)) =
      trajectoryPrefix s n (hst.trans htn) := by
  induction n, htn using Nat.le_induction with
  | base => simp
  | succ n htn ih =>
      rw [prefix_succ t n htn, prefix_succ s n (hst.trans htn)]
      exact congrArg (fun f (z : Trajectory K (n+1)) => f z.1.1) ih

/-- Restriction of an observed history drops its latest observations. -/
def historyPrefix {K : ℕ} (t n : ℕ) (ht : t ≤ n) :
    ObservedHistory K n → ObservedHistory K t :=
  @Nat.leRec t (fun n _ => ObservedHistory K n → ObservedHistory K t) id
    (fun _ _ f z => f z.1) n ht

@[simp] lemma historyPrefix_self {K : ℕ} (t : ℕ) :
    historyPrefix (K := K) t t le_rfl = id := by simp [historyPrefix]

lemma historyPrefix_succ {K : ℕ} (t n : ℕ) (ht : t ≤ n) :
    historyPrefix (K := K) t (n+1) (ht.trans (Nat.le_succ n)) =
      fun z => historyPrefix t n ht z.1 := by
  unfold historyPrefix
  rw [Nat.leRec_succ _ _ ht]

lemma historyPrefix_measurable {K t n : ℕ} (ht : t ≤ n) :
    Measurable (historyPrefix (K := K) t n ht) := by
  induction n, ht using Nat.le_induction with
  | base => simpa using (measurable_id : Measurable (id : ObservedHistory K t → ObservedHistory K t))
  | succ n ht ih =>
      rw [historyPrefix_succ t n ht]
      exact ih.comp measurable_fst

lemma observe_prefix {K t n : ℕ} (ht : t ≤ n) :
    (fun z => observe (trajectoryPrefix (K := K) t n ht z)) =
      fun z => historyPrefix t n ht (observe z) := by
  induction n, ht using Nat.le_induction with
  | base => simp
  | succ n ht ih =>
      rw [prefix_succ t n ht, historyPrefix_succ t n ht]
      exact congrArg (fun f (z : Trajectory K (n+1)) => f z.1.1) ih

/-- Measurable adaptive policies on observed histories; no persistent private state is encoded. -/
structure Policy (K : ℕ) where
  prob : (t : ℕ) → ObservedHistory K t → Fin K → ℝ
  measurable_prob : ∀ t k, Measurable (fun h => prob t h k)
  positive : ∀ t h k, 0 < prob t h k
  normalized : ∀ t h, ∑ k, prob t h k = 1

/-- A raw past influences the policy only through its observed history. -/
def rawPolicy {K : ℕ} (π : Policy K) (t : ℕ) (z : Trajectory K t) (k : Fin K) : ℝ :=
  π.prob t (observe z) k

lemma rawPolicy_pos {K : ℕ} (π : Policy K) (t : ℕ) : ∀ z k, 0 < rawPolicy π t z k :=
  fun z k => π.positive t (observe z) k
lemma rawPolicy_norm {K : ℕ} (π : Policy K) (t : ℕ) : ∀ z, ∑ k, rawPolicy π t z k = 1 :=
  fun z => π.normalized t (observe z)
lemma rawPolicy_measurable {K : ℕ} (π : Policy K) (t : ℕ) :
    ∀ k, Measurable (fun z => rawPolicy π t z k) :=
  fun k => (π.measurable_prob t k).comp (observe_measurable K t)

/-- Finite sequential law, adjoining one fresh action and reward vector at each step. -/
noncomputable def trajectoryLaw {K : ℕ} (π : Policy K)
    (ν : ℕ → Measure (Fin K → ℝ)) : (n : ℕ) → Measure (Trajectory K n)
  | 0 => Measure.dirac ()
  | t+1 => ConditionalImportanceWeighting.jointMeasure (rawPolicy π t) (rawPolicy_pos π t) (rawPolicy_norm π t)
      (rawPolicy_measurable π t) (trajectoryLaw π ν t) (ν t)

instance trajectoryLaw_isProbabilityMeasure {K : ℕ} (π : Policy K)
    (ν : ℕ → Measure (Fin K → ℝ)) [∀ t, IsProbabilityMeasure (ν t)] :
    (n : ℕ) → IsProbabilityMeasure (trajectoryLaw π ν n)
  | 0 => inferInstanceAs (IsProbabilityMeasure (Measure.dirac ()))
  | t+1 => by
      have := trajectoryLaw_isProbabilityMeasure π ν t
      change IsProbabilityMeasure (ConditionalImportanceWeighting.jointMeasure _ _ _ _ _ _)
      infer_instance

lemma prefix_measurePreserving {K t n : ℕ} (π : Policy K)
    (ν : ℕ → Measure (Fin K → ℝ)) [∀ t, IsProbabilityMeasure (ν t)] (ht : t ≤ n) :
    MeasurePreserving (trajectoryPrefix (K := K) t n ht) (trajectoryLaw π ν n) (trajectoryLaw π ν t) := by
  induction n, ht using Nat.le_induction with
  | base => simpa using (MeasurePreserving.id (trajectoryLaw π ν t))
  | succ n ht ih =>
      rw [prefix_succ t n ht]
      exact ih.comp (ConditionalImportanceWeighting.history_measurePreserving (rawPolicy π n) (rawPolicy_pos π n)
        (rawPolicy_norm π n) (rawPolicy_measurable π n) (trajectoryLaw π ν n) (ν n))


/-- Actual observed past at a specified valid time. -/
def historyAt {K : ℕ} (n t : ℕ) (ht : t ≤ n) : Trajectory K n → ObservedHistory K t :=
  fun z => observe (trajectoryPrefix t n ht z)

lemma historyAt_measurable {K n t : ℕ} (ht : t ≤ n) :
    Measurable (historyAt (K := K) n t ht) :=
  (observe_measurable K t).comp (prefix_measurable ht)

/-- Stop the observed history after the fixed horizon. -/
def historyProjection {K : ℕ} (n t : ℕ) :
    Trajectory K n → ObservedHistory K (min t n) :=
  historyAt n (min t n) (Nat.min_le_right t n)

lemma historyProjection_measurable {K n t : ℕ} :
    Measurable (historyProjection (K := K) n t) := historyAt_measurable _

lemma historyProjection_factor {K n s t : ℕ} (hst : s ≤ t) :
    historyProjection (K := K) n s =
      fun z => historyPrefix (min s n) (min t n) (min_le_min_right n hst)
        (historyProjection n t z) := by
  funext z
  unfold historyProjection historyAt
  rw [← congrFun (observe_prefix (K := K) (min_le_min_right n hst))
    (trajectoryPrefix (min t n) n (Nat.min_le_right t n) z)]
  exact (congrArg observe (congrFun (prefix_comp (K := K)
    (min_le_min_right n hst) (Nat.min_le_right t n)) z)).symm

/-- Information generated by the observed arms and observed rewards only. -/
abbrev historySigma {K : ℕ} (n t : ℕ) : MeasurableSpace (Trajectory K n) :=
  (inferInstance : MeasurableSpace (ObservedHistory K (min t n))).comap (historyProjection n t)

lemma historySigma_mono {K n : ℕ} : Monotone (historySigma (K := K) n) := by
  intro s t hst
  have hm : Measurable[historySigma n t] (historyProjection (K := K) n s) := by
    rw [historyProjection_factor hst]
    exact (historyPrefix_measurable (min_le_min_right n hst)).comp
      (comap_measurable (historyProjection n t))
  exact hm.comap_le

/-- The natural observed-history filtration, frozen after the horizon. -/
def historyFiltration {K : ℕ} (n : ℕ) : Filtration ℕ (trajectoryMeasurableSpace K n) where
  seq := historySigma n
  mono' := historySigma_mono
  le' := fun _ => historyProjection_measurable.comap_le

lemma historyFiltration_of_le {K n t : ℕ} (ht : t ≤ n) :
    historyFiltration (K := K) n t =
      (inferInstance : MeasurableSpace (ObservedHistory K t)).comap (historyAt n t ht) := by
  have he : (⟨min t n, Nat.min_le_right t n⟩ : {s : ℕ // s ≤ n}) = ⟨t, ht⟩ :=
    Subtype.ext (min_eq_left ht)
  exact congrArg (fun q : {s : ℕ // s ≤ n} =>
    (inferInstance : MeasurableSpace (ObservedHistory K q.1)).comap (historyAt n q.1 q.2)) he

lemma historyAt_observable {K n t : ℕ} (ht : t ≤ n) :
    Measurable[historyFiltration n t] (historyAt (K := K) n t ht) := by
  rw [historyFiltration_of_le ht]
  exact comap_measurable _

lemma policy_observable {K n t : ℕ} (π : Policy K) (ht : t ≤ n) (k : Fin K) :
    Measurable[historyFiltration n t]
      (fun z => π.prob t (historyAt (K := K) n t ht z) k) :=
  (π.measurable_prob t k).comp (historyAt_observable ht)

/-- The complete data of round `t`, including the raw past for applying Step 18C. -/
def roundOutcome {K : ℕ} (t n : ℕ) (ht : t < n) :
    Trajectory K n → ConditionalImportanceWeighting.Outcome (Trajectory K t) K :=
  trajectoryPrefix (t+1) n (Nat.succ_le_of_lt ht)

lemma roundOutcome_measurable {K n t : ℕ} (ht : t < n) :
    Measurable (roundOutcome (K := K) t n ht) := prefix_measurable _

def roundAction {K : ℕ} (t n : ℕ) (ht : t < n) (z : Trajectory K n) : Fin K :=
  (roundOutcome t n ht z).1.2

def roundRewardVector {K : ℕ} (t n : ℕ) (ht : t < n) (z : Trajectory K n) : Fin K → ℝ :=
  (roundOutcome t n ht z).2

def roundObservedReward {K : ℕ} (t n : ℕ) (ht : t < n) (z : Trajectory K n) : ℝ :=
  roundRewardVector t n ht z (roundAction t n ht z)

lemma roundOutcome_history {K n t : ℕ} (ht : t < n) :
    (fun z => (roundOutcome (K := K) t n ht z).1.1) =
      trajectoryPrefix t n (Nat.le_of_lt ht) := by
  have hh := prefix_comp (K := K) (Nat.le_succ t) (Nat.succ_le_of_lt ht)
  simpa [prefix_succ, roundOutcome] using hh

lemma observed_history_extension {K n t : ℕ} (ht : t < n) :
    historyAt (K := K) n (t+1) (Nat.succ_le_of_lt ht) =
      fun z => (historyAt n t (Nat.le_of_lt ht) z,
        (roundAction t n ht z, roundObservedReward t n ht z)) := by
  funext z
  change (observe ((roundOutcome t n ht z).1.1),
    ((roundOutcome t n ht z).1.2, (roundOutcome t n ht z).2 (roundOutcome t n ht z).1.2)) = _
  rw [congrFun (roundOutcome_history ht) z]
  rfl

lemma roundAction_observable {K n t : ℕ} (ht : t < n) :
    Measurable[historyFiltration n (t+1)] (roundAction (K := K) t n ht) := by
  have hm := (measurable_fst.comp measurable_snd).comp
    (historyAt_observable (K := K) (Nat.succ_le_of_lt ht))
  change Measurable[historyFiltration n (t+1)] (fun z =>
    (historyAt n (t+1) (Nat.succ_le_of_lt ht) z).2.1) at hm
  exact hm

lemma roundObservedReward_observable {K n t : ℕ} (ht : t < n) :
    Measurable[historyFiltration n (t+1)] (roundObservedReward (K := K) t n ht) := by
  exact (measurable_snd.comp measurable_snd).comp
    (historyAt_observable (K := K) (Nat.succ_le_of_lt ht))

lemma roundOutcome_measurePreserving {K n t : ℕ} (π : Policy K)
    (ν : ℕ → Measure (Fin K → ℝ)) [∀ t, IsProbabilityMeasure (ν t)] (ht : t < n) :
    MeasurePreserving (roundOutcome (K := K) t n ht) (trajectoryLaw π ν n)
      (ConditionalImportanceWeighting.jointMeasure (rawPolicy π t) (rawPolicy_pos π t)
        (rawPolicy_norm π t) (rawPolicy_measurable π t) (trajectoryLaw π ν t) (ν t)) :=
  prefix_measurePreserving π ν (Nat.succ_le_of_lt ht)

lemma round_reward_measurePreserving {K n t : ℕ} (π : Policy K)
    (ν : ℕ → Measure (Fin K → ℝ)) [∀ t, IsProbabilityMeasure (ν t)] (ht : t < n) :
    MeasurePreserving (roundRewardVector (K := K) t n ht) (trajectoryLaw π ν n) (ν t) := by
  exact (measurePreserving_snd (μ := (trajectoryLaw π ν t).compProd
    (ConditionalImportanceWeighting.actionKernel (rawPolicy π t) (rawPolicy_pos π t)
      (rawPolicy_norm π t) (rawPolicy_measurable π t))) (ν := ν t)).comp
        (roundOutcome_measurePreserving π ν ht)

lemma observed_le_raw_round {K n t : ℕ} (ht : t < n) :
    historyFiltration (K := K) n t ≤
      (ConditionalImportanceWeighting.historySigma (History := Trajectory K t) (K := K)).comap
        (roundOutcome t n ht) := by
  rw [historyFiltration_of_le (Nat.le_of_lt ht)]
  have he : historyAt (K := K) n t (Nat.le_of_lt ht) =
      fun z => observe (ConditionalImportanceWeighting.history (roundOutcome t n ht z)) := by
    funext z
    rw [ConditionalImportanceWeighting.history, congrFun (roundOutcome_history ht) z]
    rfl
  rw [he]
  exact ((observe_measurable K t).comp
    ((comap_measurable ConditionalImportanceWeighting.history).comp
      (comap_measurable (roundOutcome t n ht)))).comap_le

/-- Independence is preserved when the underlying probability space is pulled back. -/
lemma indepFun_comp_measurePreserving {Ω Ω' α β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure Ω) (ν : Measure Ω') (q : Ω → Ω') (hq : MeasurePreserving q μ ν)
    (F : Ω' → α) (G : Ω' → β) (hF : Measurable F) (hG : Measurable G)
    (h : IndepFun F G ν) :
    IndepFun (fun ω => F (q ω)) (fun ω => G (q ω)) μ := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  have hm (s : Set Ω') (hs : MeasurableSet s) : μ (q ⁻¹' s) = ν s := by
    rw [← Measure.map_apply hq.measurable hs, hq.map_eq]
  intro s t hs ht
  change μ (q ⁻¹' (F ⁻¹' s ∩ G ⁻¹' t)) = μ (q ⁻¹' (F ⁻¹' s)) * μ (q ⁻¹' (G ⁻¹' t))
  rw [hm _ ((hF hs).inter (hG ht)), hm _ (hF hs), hm _ (hG ht)]
  exact h s t hs ht

lemma round_reward_independent_rawpast_action {K n t : ℕ} (π : Policy K)
    (ν : ℕ → Measure (Fin K → ℝ)) [∀ t, IsProbabilityMeasure (ν t)] (ht : t < n) :
    IndepFun (fun z => (roundOutcome (K := K) t n ht z).1)
      (roundRewardVector t n ht) (trajectoryLaw π ν n) := by
  exact indepFun_comp_measurePreserving _ _ _ (roundOutcome_measurePreserving π ν ht)
    (fun z => z.1) ConditionalImportanceWeighting.rewardVector measurable_fst measurable_snd
    (ConditionalImportanceWeighting.rewardVector_independent_history_action
      (rawPolicy π t) (rawPolicy_pos π t) (rawPolicy_norm π t)
      (rawPolicy_measurable π t) (trajectoryLaw π ν t) (ν t))

/-- The current fresh reward vector is independent of the observed past and current action. -/
lemma round_reward_independent_past_action {K n t : ℕ} (π : Policy K)
    (ν : ℕ → Measure (Fin K → ℝ)) [∀ t, IsProbabilityMeasure (ν t)] (ht : t < n) :
    IndepFun (fun z => (historyAt (K := K) n t (Nat.le_of_lt ht) z, roundAction t n ht z))
      (roundRewardVector t n ht) (trajectoryLaw π ν n) := by
  have he : (fun z => (historyAt (K := K) n t (Nat.le_of_lt ht) z, roundAction t n ht z)) =
      fun z => (observe (roundOutcome t n ht z).1.1, roundAction t n ht z) := by
    funext z
    rw [congrFun (roundOutcome_history ht) z]
    rfl
  rw [he]
  exact (round_reward_independent_rawpast_action π ν ht).comp
    (((observe_measurable K t).comp measurable_fst).prodMk measurable_snd) measurable_id


end BestOfBothWorlds.AdaptiveBanditProcess
