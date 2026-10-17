module

public import BestOfBothWorlds.ConditionalBernstein
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
Bernstein–Freedman concentration on the original probability space. The variance
allowance enters through a joint event; no future event is used to condition the
law. Round t is observed at F_(t+1), and v_t is known at F_t. The generic sequence
is indexed by Nat; finite-horizon applications use zero increments after their
horizon, as supported by `stopped` below.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter

namespace BestOfBothWorlds.Freedman

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {F : Filtration ℕ mΩ} {X v : ℕ → Ω → ℝ} {b : ℝ}

/-- Bounded martingale differences and their exact predictable conditional squares. -/
structure DifferenceSequence (μ : Measure Ω) (F : Filtration ℕ mΩ)
    (X v : ℕ → Ω → ℝ) (b : ℝ) : Prop where
  b_nonneg : 0 ≤ b
  adapted : ∀ t, StronglyMeasurable[F (t+1)] (X t)
  variance_adapted : ∀ t, StronglyMeasurable[F t] (v t)
  abs_le : ∀ t, ∀ᵐ ω ∂μ, |X t ω| ≤ b
  mean_zero : ∀ t, μ[X t | F t] =ᵐ[μ] (0 : Ω → ℝ)
  second_moment : ∀ t, μ[(fun ω => (X t ω)^2) | F t] =ᵐ[μ] v t

/-- Sum rounds zero through n-1. -/
noncomputable def partialSum (f : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  ∑ t ∈ Finset.range n, f t

@[simp] theorem partialSum_zero (f : ℕ → Ω → ℝ) : partialSum f 0 = 0 := by
  simp [partialSum]

@[simp] theorem partialSum_succ (f : ℕ → Ω → ℝ) (n : ℕ) :
    partialSum f (n+1) = partialSum f n + f n := by
  simp [partialSum, Finset.sum_range_succ]

@[simp] theorem partialSum_neg (f : ℕ → Ω → ℝ) (n : ℕ) :
    partialSum (fun t ω => -f t ω) n = -partialSum f n := by
  funext ω
  simp [partialSum, Finset.sum_apply]

/-- The variance-compensated exponential process. -/
noncomputable def exponentialProcess (X v : ℕ → Ω → ℝ) (b lambda : ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  Real.exp (lambda * partialSum X n ω - Bernstein.psi b lambda * partialSum v n ω)

/-- Stop a sequence after its finite horizon. -/
def stopped (f : ℕ → Ω → ℝ) (N t : ℕ) : Ω → ℝ := if t < N then f t else 0

@[simp] theorem stopped_after (f : ℕ → Ω → ℝ) (N t : ℕ) (ht : N ≤ t) :
    stopped f N t = 0 := by simp [BestOfBothWorlds.Freedman.stopped, Nat.not_lt.mpr ht]

/-- Stopping preserves every difference-sequence hypothesis without changing the filtration. -/
theorem DifferenceSequence.stopped (h : DifferenceSequence μ F X v b) (N : ℕ) :
    DifferenceSequence μ F (stopped X N) (stopped v N) b := by
  refine ⟨h.b_nonneg, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    by_cases ht : t < N
    · simpa [BestOfBothWorlds.Freedman.stopped, ht] using h.adapted t
    · simp only [BestOfBothWorlds.Freedman.stopped, ite_eq_right ht]
      exact stronglyMeasurable_zero
  · intro t
    by_cases ht : t < N
    · simpa [BestOfBothWorlds.Freedman.stopped, ht] using h.variance_adapted t
    · simp only [BestOfBothWorlds.Freedman.stopped, ite_eq_right ht]
      exact stronglyMeasurable_zero
  · intro t
    by_cases ht : t < N
    · simpa [BestOfBothWorlds.Freedman.stopped, ht] using h.abs_le t
    · exact Eventually.of_forall (fun ω => by simpa [BestOfBothWorlds.Freedman.stopped, ht] using h.b_nonneg)
  · intro t
    by_cases ht : t < N
    · simpa [BestOfBothWorlds.Freedman.stopped, ht] using h.mean_zero t
    · simp [BestOfBothWorlds.Freedman.stopped, ht]
  · intro t
    by_cases ht : t < N
    · simpa [BestOfBothWorlds.Freedman.stopped, ht] using h.second_moment t
    · simp [BestOfBothWorlds.Freedman.stopped, ht]
      exact Eventually.of_forall (fun _ => rfl)

variable [IsProbabilityMeasure μ]

namespace DifferenceSequence

variable (h : DifferenceSequence μ F X v b)
include h

theorem increment_integrable (t : ℕ) : Integrable (X t) μ :=
  Bernstein.bounded_integrable ((h.adapted t).mono (F.le (t+1))).aestronglyMeasurable (h.abs_le t)

theorem square_integrable (t : ℕ) : Integrable (fun ω => (X t ω)^2) μ :=
  Bernstein.bounded_square_integrable h.b_nonneg
    ((h.adapted t).mono (F.le (t+1))).aestronglyMeasurable (h.abs_le t)

/-- The conditional second moments are nonnegative and bounded by b squared. -/
theorem variance_bounds (t : ℕ) : ∀ᵐ ω ∂μ, 0 ≤ v t ω ∧ v t ω ≤ b^2 := by
  have hlo : 0 ≤ᵐ[μ] μ[(fun ω => (X t ω)^2) | F t] :=
    condExp_nonneg (Eventually.of_forall (fun ω => sq_nonneg (X t ω)))
  have hsq : (fun ω => (X t ω)^2) ≤ᵐ[μ] (fun _ => b^2) := by
    filter_upwards [h.abs_le t] with ω hω
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) h.b_nonneg).2 hω
  have hhi := condExp_mono (m := F t) (h.square_integrable t) (integrable_const (b^2)) hsq
  rw [condExp_const (μ := μ) (F.le t) (b^2)] at hhi
  filter_upwards [hlo, hhi, h.second_moment t] with ω hlo hhi heq
  exact ⟨by simpa [heq] using hlo, by simpa [heq] using hhi⟩

theorem variance_nonneg (t : ℕ) : ∀ᵐ ω ∂μ, 0 ≤ v t ω :=
  (h.variance_bounds t).mono (fun _ hω => hω.1)

omit [IsProbabilityMeasure μ] in
theorem partialSum_stronglyMeasurable (n : ℕ) : StronglyMeasurable[F n] (partialSum X n) := by
  apply Finset.stronglyMeasurable_sum
  intro t ht
  exact (h.adapted t).mono (F.mono (Nat.succ_le_of_lt (Finset.mem_range.mp ht)))

omit [IsProbabilityMeasure μ] in
theorem varianceSum_stronglyMeasurable (n : ℕ) : StronglyMeasurable[F n] (partialSum v n) := by
  apply Finset.stronglyMeasurable_sum
  intro t ht
  exact (h.variance_adapted t).mono (F.mono (Nat.le_of_lt (Finset.mem_range.mp ht)))

omit [IsProbabilityMeasure μ] in
theorem partialSum_le (n : ℕ) : ∀ᵐ ω ∂μ, partialSum X n ω ≤ (n : ℝ)*b := by
  filter_upwards [ae_all_iff.2 h.abs_le] with ω hω
  simp only [partialSum, Finset.sum_apply]
  calc
    _ ≤ ∑ _t ∈ Finset.range n, b :=
      Finset.sum_le_sum (fun t _ => (le_abs_self _).trans (hω t))
    _ = _ := by simp

theorem varianceSum_nonneg (n : ℕ) : ∀ᵐ ω ∂μ, 0 ≤ partialSum v n ω := by
  filter_upwards [ae_all_iff.2 h.variance_nonneg] with ω hω
  simp only [partialSum, Finset.sum_apply]
  exact Finset.sum_nonneg (fun t _ => hω t)

omit [IsProbabilityMeasure μ] in
theorem exponential_stronglyAdapted (lambda : ℝ) :
    StronglyAdapted F (exponentialProcess X v b lambda) := by
  intro n
  exact ((measurable_const.mul (h.partialSum_stronglyMeasurable n).measurable).sub
    (measurable_const.mul (h.varianceSum_stronglyMeasurable n).measurable)).exp.stronglyMeasurable

omit h [IsProbabilityMeasure μ] in
theorem exponential_nonneg (lambda : ℝ) (n : ℕ) (ω : Ω) :
    0 ≤ exponentialProcess X v b lambda n ω := (Real.exp_pos _).le

/-- Integrability is derived from an actual deterministic bound for every finite time. -/
theorem exponential_integrable (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (hbl : b*lambda < 3) (n : ℕ) : Integrable (exponentialProcess X v b lambda n) μ := by
  apply Integrable.of_bound
    (((h.exponential_stronglyAdapted lambda) n).mono (F.le n)).aestronglyMeasurable
    (Real.exp (lambda * ((n : ℝ)*b)))
  filter_upwards [h.partialSum_le n, h.varianceSum_nonneg n] with ω hM hV
  rw [Real.norm_eq_abs, abs_of_nonneg (exponential_nonneg (X := X) (v := v) (b := b) lambda n ω)]
  apply Real.exp_le_exp.mpr
  have hp : 0 ≤ Bernstein.psi b lambda := Bernstein.psi_nonneg hbl
  exact (sub_le_self _ (mul_nonneg hp hV)).trans (mul_le_mul_of_nonneg_left hM hlambda)

/-- The variance-sensitive exponential is a genuine Mathlib supermartingale. -/
theorem exponential_supermartingale (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (hbl : b*lambda < 3) : Supermartingale (exponentialProcess X v b lambda) F μ := by
  apply supermartingale_nat (h.exponential_stronglyAdapted lambda)
    (h.exponential_integrable lambda hlambda hbl)
  intro n
  let A : Ω → ℝ := fun ω => Real.exp
    (lambda * partialSum X n ω - Bernstein.psi b lambda * partialSum v n ω -
      Bernstein.psi b lambda * v n ω)
  let B : Ω → ℝ := fun ω => Real.exp (lambda * X n ω)
  have hA : StronglyMeasurable[F n] A :=
    (((measurable_const.mul (h.partialSum_stronglyMeasurable n).measurable).sub
      (measurable_const.mul (h.varianceSum_stronglyMeasurable n).measurable)).sub
      (measurable_const.mul (h.variance_adapted n).measurable)).exp.stronglyMeasurable
  have hB : Integrable B μ :=
    integrable_exp_mul_of_mem_Icc
      (((h.adapted n).mono (F.le (n+1))).aestronglyMeasurable.aemeasurable)
      ((h.abs_le n).mono (fun _ hω => _root_.abs_le.mp hω))
  have hfactor : A * B = exponentialProcess X v b lambda (n+1) := by
    funext ω
    rw [Pi.mul_apply, ← Real.exp_add]
    simp only [exponentialProcess, partialSum_succ, Pi.add_apply]
    congr 1
    ring
  have hAB : Integrable (A*B) μ := by
    rw [hfactor]
    exact h.exponential_integrable lambda hlambda hbl (n+1)
  have hpull := condExp_mul_of_stronglyMeasurable_left (m := F n) hA hAB hB
  rw [hfactor] at hpull
  have hmgf := Bernstein.conditional_mgf (F.le n) h.b_nonneg hlambda hbl
    (((h.adapted n).mono (F.le (n+1))).aestronglyMeasurable) (h.abs_le n)
    (h.mean_zero n) (h.second_moment n)
  filter_upwards [hpull, hmgf] with ω hpull hmgf
  calc
    _ = A ω * μ[B | F n] ω := hpull
    _ ≤ A ω * Real.exp (Bernstein.psi b lambda * v n ω) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = exponentialProcess X v b lambda n ω := by
      rw [← Real.exp_add]
      congr 1
      ring

omit h [IsProbabilityMeasure μ] in
@[simp] theorem exponential_zero (lambda : ℝ) :
    exponentialProcess X v b lambda 0 = (fun _ => 1) := by
  funext ω
  simp [exponentialProcess]

/-- Supermartingale expectation comparison yields the normalized expectation bound. -/
theorem exponential_integral_le_one (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (hbl : b*lambda < 3) (n : ℕ) :
    (∫ ω, exponentialProcess X v b lambda n ω ∂μ) ≤ 1 := by
  have hi := (h.exponential_supermartingale lambda hlambda hbl).setIntegral_le
    (i := 0) (j := n) (Nat.zero_le n) MeasurableSet.univ
  simpa only [Measure.restrict_univ, exponential_zero, integral_const, probReal_univ,
    one_smul] using hi

omit [IsProbabilityMeasure μ] in
/-- Changing sign leaves the exact predictable variance unchanged. -/
theorem neg : DifferenceSequence μ F (fun t ω => -X t ω) v b := by
  refine ⟨h.b_nonneg, (fun t => (h.adapted t).neg), h.variance_adapted, ?_, ?_, ?_⟩
  · intro t
    simpa only [abs_neg] using h.abs_le t
  · intro t
    change μ[-(X t) | F t] =ᵐ[μ] (0 : Ω → ℝ)
    filter_upwards [condExp_neg (μ := μ) (X t) (F t), h.mean_zero t] with ω hn hz
    simpa only [Pi.neg_apply, hz, Pi.zero_apply, neg_zero] using hn
  · intro t
    simpa only [neg_sq] using h.second_moment t

/-- A zero increment bound forces both cumulative error and variance to vanish a.e. -/
theorem sums_eq_zero_of_bound_zero (hb : b = 0) (n : ℕ) :
    partialSum X n =ᵐ[μ] 0 ∧ partialSum v n =ᵐ[μ] 0 := by
  have hX : ∀ t, X t =ᵐ[μ] 0 := by
    intro t
    filter_upwards [h.abs_le t] with ω hω
    exact abs_eq_zero.mp (le_antisymm (by simpa only [hb] using hω) (abs_nonneg _))
  have hv : ∀ t, v t =ᵐ[μ] 0 := by
    intro t
    filter_upwards [h.variance_bounds t] with ω hω
    exact le_antisymm (by simpa only [hb, zero_pow (by decide : 2 ≠ 0), Pi.zero_apply] using hω.2) hω.1
  constructor
  · have hs : (∑ t ∈ Finset.range n, X t) =ᵐ[μ] ∑ _t ∈ Finset.range n, (0 : Ω → ℝ) :=
      eventuallyEq_sum (fun t _ => hX t)
    simpa only [partialSum, Finset.sum_const_zero] using hs
  · have hs : (∑ t ∈ Finset.range n, v t) =ᵐ[μ] ∑ _t ∈ Finset.range n, (0 : Ω → ℝ) :=
      eventuallyEq_sum (fun t _ => hv t)
    simpa only [partialSum, Finset.sum_const_zero] using hs

end DifferenceSequence

/-- AE event inclusion suffices for real probability comparison under a finite measure. -/
theorem measureReal_mono_ae {s t : Set Ω} (hst : s ≤ᵐ[μ] t) : μ.real s ≤ μ.real t :=
  ENNReal.toReal_mono (measure_ne_top μ t) (measure_mono_ae hst)

/-- The unoptimized upper-tail bound uses the original law on a joint event. -/
theorem upper_tail_unoptimized (h : DifferenceSequence μ F X v b) (n : ℕ)
    (x a lambda : ℝ) (hlambda : 0 ≤ lambda) (hbl : b*lambda < 3) :
    μ.real {ω | x ≤ partialSum X n ω ∧ partialSum v n ω ≤ a} ≤
      Real.exp (-lambda*x + Bernstein.psi b lambda*a) := by
  let c := Real.exp (lambda*x - Bernstein.psi b lambda*a)
  have hc : 0 < c := Real.exp_pos _
  have hinc : {ω | x ≤ partialSum X n ω ∧ partialSum v n ω ≤ a} ⊆
      {ω | c ≤ exponentialProcess X v b lambda n ω} := by
    intro ω hω
    apply Real.exp_le_exp.mpr
    exact sub_le_sub (mul_le_mul_of_nonneg_left hω.1 hlambda)
      (mul_le_mul_of_nonneg_left hω.2 (Bernstein.psi_nonneg hbl))
  have hMarkov := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (DifferenceSequence.exponential_nonneg (X := X) (v := v) (b := b) lambda n))
    (h.exponential_integrable lambda hlambda hbl n) c
  have hproduct : c * μ.real {ω | x ≤ partialSum X n ω ∧ partialSum v n ω ≤ a} ≤ 1 :=
    (mul_le_mul_of_nonneg_left (measureReal_mono hinc) hc.le).trans
      (hMarkov.trans (h.exponential_integral_le_one lambda hlambda hbl n))
  have hdiv : μ.real {ω | x ≤ partialSum X n ω ∧ partialSum v n ω ≤ a} ≤ 1/c :=
    (le_div_iff₀ hc).2 (by rwa [mul_comm])
  have hc_inv : 1/c = Real.exp (-lambda*x + Bernstein.psi b lambda*a) := by
    dsimp [c]
    rw [one_div, ← Real.exp_neg]
    congr 1
    ring
  rwa [hc_inv] at hdiv

/-- The optimized upper tail, with an explicitly positive Bernstein denominator. -/
theorem upper_tail (h : DifferenceSequence μ F X v b) (n : ℕ) (x a : ℝ)
    (hx : 0 ≤ x) (ha : 0 ≤ a) (hden : 0 < a+b*x/3) :
    μ.real {ω | x ≤ partialSum X n ω ∧ partialSum v n ω ≤ a} ≤
      Real.exp (-x^2/(2*(a+b*x/3))) := by
  by_cases hx0 : x = 0
  · subst x
    simpa only [zero_pow (by decide : 2 ≠ 0), neg_zero, zero_div, Real.exp_zero] using
      (measureReal_le_one (μ := μ) (s := {ω | 0 ≤ partialSum X n ω ∧ partialSum v n ω ≤ a}))
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  by_cases ha0 : a = 0
  · subst a
    have hbpos : 0 < b := by
      by_contra hnot
      have hb0 : b = 0 := le_antisymm (le_of_not_gt hnot) h.b_nonneg
      simp [hb0] at hden
    have hp := Bernstein.zero_variance_parameter hbpos
    have hu := upper_tail_unoptimized h n x 0 (3/(2*b)) hp.1 hp.2
    rw [Bernstein.zero_variance_exponent hbpos hxpos] at hu
    exact hu
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hp := Bernstein.optimizer_admissible h.b_nonneg hx hapos
    have hu := upper_tail_unoptimized h n x a (x/(a+b*x/3)) hp.1 hp.2
    rw [Bernstein.optimizer_exponent h.b_nonneg hx hapos] at hu
    exact hu

/-- Lower-tail concentration follows by sign reversal, with the same variance process. -/
theorem lower_tail (h : DifferenceSequence μ F X v b) (n : ℕ) (x a : ℝ)
    (hx : 0 ≤ x) (ha : 0 ≤ a) (hden : 0 < a+b*x/3) :
    μ.real {ω | partialSum X n ω ≤ -x ∧ partialSum v n ω ≤ a} ≤
      Real.exp (-x^2/(2*(a+b*x/3))) := by
  have hu := upper_tail h.neg n x a hx ha hden
  have he : {ω | x ≤ partialSum (fun t ω => -X t ω) n ω ∧ partialSum v n ω ≤ a} =
      {ω | partialSum X n ω ≤ -x ∧ partialSum v n ω ≤ a} := by
    ext ω
    simp only [Set.mem_ofPred_eq, partialSum_neg, Pi.neg_apply]
    constructor <;> rintro ⟨hω, hv⟩ <;> exact ⟨by linarith, hv⟩
  rw [he] at hu
  exact hu

/-- Any ambient future event may supply the variance allowance by AE inclusion. -/
theorem upper_tail_on_event (h : DifferenceSequence μ F X v b) (n : ℕ) (x a : ℝ)
    (hx : 0 ≤ x) (ha : 0 ≤ a) (hden : 0 < a+b*x/3)
    (E : Set Ω) (_hE : MeasurableSet E)
    (hEV : ∀ᵐ ω ∂μ, ω ∈ E → partialSum v n ω ≤ a) :
    μ.real (E ∩ {ω | x ≤ partialSum X n ω}) ≤ Real.exp (-x^2/(2*(a+b*x/3))) := by
  apply (measureReal_mono_ae (μ := μ) ?_).trans (upper_tail h n x a hx ha hden)
  filter_upwards [hEV] with ω hω
  exact fun hmem => ⟨hmem.2, hω hmem.1⟩

/-- Lower-tail restriction likewise imposes no independence or positive-probability condition on E. -/
theorem lower_tail_on_event (h : DifferenceSequence μ F X v b) (n : ℕ) (x a : ℝ)
    (hx : 0 ≤ x) (ha : 0 ≤ a) (hden : 0 < a+b*x/3)
    (E : Set Ω) (_hE : MeasurableSet E)
    (hEV : ∀ᵐ ω ∂μ, ω ∈ E → partialSum v n ω ≤ a) :
    μ.real (E ∩ {ω | partialSum X n ω ≤ -x}) ≤ Real.exp (-x^2/(2*(a+b*x/3))) := by
  apply (measureReal_mono_ae (μ := μ) ?_).trans (lower_tail h n x a hx ha hden)
  filter_upwards [hEV] with ω hω
  exact fun hmem => ⟨hmem.2, hω hmem.1⟩

/-- At zero threshold a probability bound of one covers every variance boundary. -/
theorem zero_threshold (n : ℕ) (a : ℝ) :
    μ.real {ω | 0 ≤ partialSum X n ω ∧ partialSum v n ω ≤ a} ≤ 1 :=
  measureReal_le_one

/-- A zero increment bound makes every strictly positive upper deviation a null event. -/
theorem upper_tail_null_of_bound_zero (h : DifferenceSequence μ F X v b) (hb : b = 0)
    (n : ℕ) (x : ℝ) (hx : 0 < x) : μ.real {ω | x ≤ partialSum X n ω} = 0 := by
  apply le_antisymm ?_ ENNReal.toReal_nonneg
  calc
    _ ≤ μ.real ∅ := measureReal_mono_ae (by
      filter_upwards [(h.sums_eq_zero_of_bound_zero hb n).1] with ω hω
      intro hmem
      have : x ≤ 0 := by simpa only [Set.mem_ofPred_eq, hω, Pi.zero_apply] using hmem
      exact False.elim ((not_le_of_gt hx) this))
    _ = 0 := by simp

/-- The corresponding strictly negative deviation is null for the same zero bound. -/
theorem lower_tail_null_of_bound_zero (h : DifferenceSequence μ F X v b) (hb : b = 0)
    (n : ℕ) (x : ℝ) (hx : 0 < x) : μ.real {ω | partialSum X n ω ≤ -x} = 0 := by
  have hu := upper_tail_null_of_bound_zero h.neg hb n x hx
  have he : {ω | x ≤ partialSum (fun t ω => -X t ω) n ω} =
      {ω | partialSum X n ω ≤ -x} := by
    ext ω
    simp only [Set.mem_ofPred_eq, partialSum_neg, Pi.neg_apply]
    constructor <;> intro hω <;> linarith
  rwa [he] at hu

omit [IsProbabilityMeasure μ] in
/-- Empty sums have no strictly positive deviation, without dividing by any denominator. -/
theorem upper_tail_null_at_zero (x : ℝ) (hx : 0 < x) :
    μ.real {ω | x ≤ partialSum X 0 ω} = 0 := by
  have he : {ω | x ≤ partialSum X 0 ω} = ∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq, partialSum_zero, Pi.zero_apply, Set.mem_empty_iff_false,
      iff_false, not_le]
    exact hx
  rw [he]
  simp


/-- The lower zero-threshold probability also needs no division or variance assumption. -/
theorem zero_threshold_lower (n : ℕ) (a : ℝ) :
    μ.real {ω | partialSum X n ω ≤ 0 ∧ partialSum v n ω ≤ a} ≤ 1 :=
  measureReal_le_one

/-- Explicit upper-tail coverage when the Bernstein denominator vanishes. -/
theorem upper_tail_zero_denominator (h : DifferenceSequence μ F X v b) (n : ℕ) (x a : ℝ)
    (hx : 0 ≤ x) (ha : 0 ≤ a) (hden : a+b*x/3 = 0) :
    μ.real {ω | x ≤ partialSum X n ω ∧ partialSum v n ω ≤ a} ≤
      if x = 0 then 1 else 0 := by
  by_cases hx0 : x = 0
  · simp only [ite_eq_left hx0]
    exact measureReal_le_one
  · simp only [ite_eq_right hx0]
    have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    have hprod : b*x = 0 := by nlinarith [hden, mul_nonneg h.b_nonneg hx]
    have hb0 : b = 0 := (mul_eq_zero.mp hprod).resolve_right hxpos.ne'
    have hi : {ω | x ≤ partialSum X n ω ∧ partialSum v n ω ≤ a} ⊆
        {ω | x ≤ partialSum X n ω} := fun _ hω => hω.1
    exact (measureReal_mono hi).trans_eq (upper_tail_null_of_bound_zero h hb0 n x hxpos)

/-- Explicit lower-tail coverage at a zero denominator, without totalized division. -/
theorem lower_tail_zero_denominator (h : DifferenceSequence μ F X v b) (n : ℕ) (x a : ℝ)
    (hx : 0 ≤ x) (ha : 0 ≤ a) (hden : a+b*x/3 = 0) :
    μ.real {ω | partialSum X n ω ≤ -x ∧ partialSum v n ω ≤ a} ≤
      if x = 0 then 1 else 0 := by
  by_cases hx0 : x = 0
  · simp only [ite_eq_left hx0]
    exact measureReal_le_one
  · simp only [ite_eq_right hx0]
    have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    have hprod : b*x = 0 := by nlinarith [hden, mul_nonneg h.b_nonneg hx]
    have hb0 : b = 0 := (mul_eq_zero.mp hprod).resolve_right hxpos.ne'
    have hi : {ω | partialSum X n ω ≤ -x ∧ partialSum v n ω ≤ a} ⊆
        {ω | partialSum X n ω ≤ -x} := fun _ hω => hω.1
    exact (measureReal_mono hi).trans_eq (lower_tail_null_of_bound_zero h hb0 n x hxpos)

omit [IsProbabilityMeasure μ] in
/-- Empty sums also have no strictly negative deviation. -/
theorem lower_tail_null_at_zero (x : ℝ) (hx : 0 < x) :
    μ.real {ω | partialSum X 0 ω ≤ -x} = 0 := by
  have hn : ¬(0 : ℝ) ≤ -x := by linarith
  simp only [partialSum_zero, Pi.zero_apply]
  simp [hn]

end BestOfBothWorlds.Freedman
