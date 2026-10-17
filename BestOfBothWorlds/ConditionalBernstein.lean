module

public import BestOfBothWorlds.BernsteinEnvelope
public import Mathlib.Probability.Moments.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
The conditional Bernstein estimate keeps the conditional second moment as a
random function. All integrability is derived from the increment bound before
conditional expectation monotonicity is used. No independence is required.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter

namespace BestOfBothWorlds.Bernstein

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
variable {X v : Ω → ℝ} {b lambda : ℝ}

/-- A bounded real random variable is genuinely integrable. -/
theorem bounded_integrable [IsFiniteMeasure μ]
    (hX : AEStronglyMeasurable[mΩ] X μ) (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ b) :
    Integrable X μ := by
  exact Integrable.of_bound hX b (by simpa only [Real.norm_eq_abs] using hbound)

/-- The squared increment is integrable under the same absolute bound. -/
theorem bounded_square_integrable [IsFiniteMeasure μ] (hb : 0 ≤ b)
    (hX : AEStronglyMeasurable[mΩ] X μ) (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ b) :
    Integrable (fun ω => (X ω) ^ 2) μ := by
  apply Integrable.of_bound (hX.pow 2) (b ^ 2)
  filter_upwards [hbound] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simpa only [Pi.pow_apply, sq_abs] using (sq_le_sq₀ (abs_nonneg _) hb).2 hω

/-- Genuine conditional MGF control with a possibly random conditional variance. -/
theorem conditional_mgf [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) (hb : 0 ≤ b) (hlambda : 0 ≤ lambda) (hbl : b * lambda < 3)
    (hX : AEStronglyMeasurable[mΩ] X μ) (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ b)
    (hzero : μ[X | m] =ᵐ[μ] (0 : Ω → ℝ))
    (hsquare : μ[(fun ω => (X ω) ^ 2) | m] =ᵐ[μ] v) :
    μ[(fun ω => Real.exp (lambda * X ω)) | m]
      ≤ᵐ[μ] fun ω => Real.exp (psi b lambda * v ω) := by
  have hi := bounded_integrable (mΩ := mΩ) hX hbound
  have hsq := bounded_square_integrable (mΩ := mΩ) hb hX hbound
  have hexp : Integrable (fun ω => Real.exp (lambda * X ω)) μ :=
    integrable_exp_mul_of_mem_Icc hX.aemeasurable (by
      filter_upwards [hbound] with ω hω
      exact abs_le.mp hω)
  have hpoly : Integrable (fun ω => 1 + lambda * X ω + psi b lambda * (X ω) ^ 2) μ :=
    ((integrable_const (1 : ℝ)).add (hi.const_mul lambda)).add
      (hsq.const_mul (psi b lambda))
  have hle : (fun ω => Real.exp (lambda * X ω)) ≤ᵐ[μ]
      (fun ω => 1 + lambda * X ω + psi b lambda * (X ω) ^ 2) := by
    filter_upwards [hbound] with ω hω
    exact exp_mul_le_quadratic hb hlambda hbl hω
  have hc := condExp_mono (m := m) hexp hpoly hle
  have ha := condExp_add (integrable_const (1 : ℝ)) (hi.const_mul lambda) m
  have hp := condExp_add ((integrable_const (1 : ℝ)).add (hi.const_mul lambda))
    (hsq.const_mul (psi b lambda)) m
  have hs := condExp_smul (μ := μ) lambda X m
  have hss := condExp_smul (μ := μ) (psi b lambda) (fun ω => (X ω) ^ 2) m
  filter_upwards [hc, ha, hp, hs, hss, hzero, hsquare] with ω hc ha hp hs hss hz hv
  simp only [Pi.add_def, Pi.smul_def, smul_eq_mul] at ha hp hs hss
  have hconst := congrFun (condExp_const (μ := μ) hm (1 : ℝ)) ω
  calc
    _ ≤ _ := hc
    _ = 1 + psi b lambda * v ω := by rw [hp, ha, hs, hss, hconst, hz, hv]; simp
    _ ≤ _ := by simpa [add_comm] using Real.add_one_le_exp (psi b lambda * v ω)

/-- The positive-variance optimizer has a positive denominator. -/
theorem optimizer_denominator_pos {b x a : ℝ} (hb : 0 ≤ b) (hx : 0 ≤ x) (ha : 0 < a) :
    0 < a + b * x / 3 := by positivity

/-- The optimizer lies strictly inside the Bernstein parameter range. -/
theorem optimizer_admissible {b x a : ℝ} (hb : 0 ≤ b) (hx : 0 ≤ x) (ha : 0 < a) :
    0 ≤ x / (a + b * x / 3) ∧ b * (x / (a + b * x / 3)) < 3 := by
  have hd := optimizer_denominator_pos hb hx ha
  constructor
  · exact div_nonneg hx hd.le
  · rw [← mul_div_assoc, div_lt_iff₀ hd]
    nlinarith

/-- Exact optimizer algebra; the coefficient is the manuscript's `1/3`. -/
theorem optimizer_exponent {b x a : ℝ} (hb : 0 ≤ b) (hx : 0 ≤ x) (ha : 0 < a) :
    -(x / (a + b * x / 3)) * x + psi b (x / (a + b * x / 3)) * a =
      -x ^ 2 / (2 * (a + b * x / 3)) := by
  have hd := optimizer_denominator_pos hb hx ha
  have hq : 1 - b * (x / (a + b * x / 3)) / 3 = a / (a + b * x / 3) := by
    field_simp [ne_of_gt hd]
    ring
  unfold psi
  rw [hq]
  field_simp [ne_of_gt hd, ne_of_gt ha]
  ring

/-- At zero variance this interior parameter avoids the forbidden endpoint. -/
theorem zero_variance_parameter {b : ℝ} (hb : 0 < b) :
    0 ≤ (3 : ℝ) / (2 * b) ∧ b * ((3 : ℝ) / (2 * b)) < 3 := by
  constructor
  · positivity
  · have he : b * ((3 : ℝ) / (2 * b)) = 3 / 2 := by field_simp [ne_of_gt hb]
    rw [he]
    norm_num

/-- The interior zero-variance parameter gives exactly the required exponent. -/
theorem zero_variance_exponent {b x : ℝ} (hb : 0 < b) (hx : 0 < x) :
    -((3 : ℝ) / (2 * b)) * x + psi b ((3 : ℝ) / (2 * b)) * 0 =
      -x ^ 2 / (2 * (0 + b * x / 3)) := by
  simp only [mul_zero, add_zero, zero_add]
  field_simp [ne_of_gt hb, ne_of_gt hx]

end BestOfBothWorlds.Bernstein
