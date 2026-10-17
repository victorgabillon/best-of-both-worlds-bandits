module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
The exact scalar exponential estimate for Bernstein--Freedman concentration.

Mathlib's finite Taylor remainder gives a polynomial of degree four and an
absolute fifth-order remainder. A polynomial factorization then supplies the
coefficient `1 / (2 * (1 - b * lambda / 3))` on the full strict parameter range.
The finite Taylor strategy is also used in the Apache-2.0 StatsMLlib reference
`Probability/Concentration/Bernstein.lean`; no external dependency is imported.
-/

@[expose] public section

open scoped BigOperators

namespace BestOfBothWorlds.Bernstein

/-- The exact variance coefficient in the Bernstein exponential bound. -/
noncomputable def psi (b lambda : ℝ) : ℝ :=
  lambda ^ 2 / (2 * (1 - b * lambda / 3))

/-- The strict Bernstein parameter range makes the denominator positive. -/
theorem denominator_pos {b lambda : ℝ} (hbl : b * lambda < 3) :
    0 < 1 - b * lambda / 3 := by
  linarith

/-- The variance coefficient is nonnegative on the strict parameter range. -/
theorem psi_nonneg {b lambda : ℝ} (hbl : b * lambda < 3) :
    0 ≤ psi b lambda := by
  exact div_nonneg (sq_nonneg lambda)
    (mul_pos (by norm_num : (0 : ℝ) < 2) (denominator_pos hbl)).le

@[simp] theorem psi_zero (b : ℝ) : psi b 0 = 0 := by
  simp [psi]

private theorem exp_le_taylor_four {u : ℝ} (hu : |u| ≤ 3) :
    Real.exp u ≤ 1 + u + u ^ 2 / 2 + u ^ 3 / 6 + u ^ 4 / 24 + |u| ^ 5 / 60 := by
  have hcomplex :
      ‖Complex.exp (u : ℂ) -
        ∑ m ∈ Finset.range 5, (u : ℂ) ^ m / (m.factorial : ℂ)‖ ≤
        ‖(u : ℂ)‖ ^ 5 / (Nat.factorial 5 : ℝ) * 2 := by
    apply Complex.exp_bound'
    have hnorm : ‖(u : ℂ)‖ ≤ 3 := by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using hu
    norm_num
    linarith
  have hcast :
      ((Real.exp u - (1 + u + u ^ 2 / 2 + u ^ 3 / 6 + u ^ 4 / 24) : ℝ) : ℂ) =
        Complex.exp (u : ℂ) -
          ∑ m ∈ Finset.range 5, (u : ℂ) ^ m / (m.factorial : ℂ) := by
    push_cast
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hreal :
      |Real.exp u - (1 + u + u ^ 2 / 2 + u ^ 3 / 6 + u ^ 4 / 24)| ≤ |u| ^ 5 / 60 := by
    calc
      _ = ‖((Real.exp u - (1 + u + u ^ 2 / 2 + u ^ 3 / 6 + u ^ 4 / 24) : ℝ) : ℂ)‖ := by
        simp only [Complex.norm_real, Real.norm_eq_abs]
      _ = _ := congrArg norm hcast
      _ ≤ _ := hcomplex
      _ = _ := by
        norm_num [Complex.norm_real, Real.norm_eq_abs, Nat.factorial]
        ring
  exact (sub_le_iff_le_add.mp ((abs_le.mp hreal).2)).trans_eq (by ring)

private theorem taylor_tail_le_quadratic {w : ℝ} (hw : 0 ≤ w) (hw3 : w < 3) :
    w ^ 2 / 2 + w ^ 3 / 6 + w ^ 4 / 24 + w ^ 5 / 60 ≤
      (w ^ 2 / 2) / (1 - w / 3) := by
  have hden : 0 < 1 - w / 3 := by linarith
  apply (le_div_iff₀ hden).2
  apply sub_nonneg.mp
  have hfactor : 0 ≤ w ^ 4 * (5 - w + 2 * w ^ 2) := by
    exact mul_nonneg (pow_nonneg hw 4) (by linarith [sq_nonneg w])
  have hidentity :
      w ^ 2 / 2 -
        (w ^ 2 / 2 + w ^ 3 / 6 + w ^ 4 / 24 + w ^ 5 / 60) * (1 - w / 3) =
        w ^ 4 * (5 - w + 2 * w ^ 2) / 360 := by
    ring
  rw [hidentity]
  exact div_nonneg hfactor (by norm_num)

private theorem exp_le_quadratic_abs {u : ℝ} (hu : |u| < 3) :
    Real.exp u ≤ 1 + u + (u ^ 2 / 2) / (1 - |u| / 3) := by
  have hthird : u ^ 3 ≤ |u| ^ 3 := by
    calc
      u ^ 3 ≤ |u ^ 3| := le_abs_self _
      _ = |u| ^ 3 := abs_pow u 3
  have hfourth : |u| ^ 4 = u ^ 4 := by
    calc
      |u| ^ 4 = (|u| ^ 2) ^ 2 := by ring
      _ = (u ^ 2) ^ 2 := by rw [sq_abs]
      _ = u ^ 4 := by ring
  have htaylor := exp_le_taylor_four hu.le
  calc
    Real.exp u ≤ 1 + u + (|u| ^ 2 / 2 + |u| ^ 3 / 6 + |u| ^ 4 / 24 + |u| ^ 5 / 60) := by
      rw [sq_abs, hfourth]
      linarith
    _ ≤ 1 + u + (|u| ^ 2 / 2) / (1 - |u| / 3) :=
      by simpa only [add_comm] using
        add_le_add_left (taylor_tail_le_quadratic (abs_nonneg u) hu) (1 + u)
    _ = _ := by rw [sq_abs]

/-- The exact bounded-increment Bernstein envelope, retaining the factor `1/3`.
It includes zero increments, zero range, and zero exponential parameter. -/
theorem exp_mul_le_quadratic {b lambda u : ℝ}
    (hb : 0 ≤ b) (hlambda : 0 ≤ lambda) (hbl : b * lambda < 3) (hu : |u| ≤ b) :
    Real.exp (lambda * u) ≤ 1 + lambda * u + psi b lambda * u ^ 2 := by
  have habs : |lambda * u| ≤ b * lambda := by
    calc
      |lambda * u| = |u| * lambda := by rw [abs_mul, abs_of_nonneg hlambda, mul_comm]
      _ ≤ b * lambda := mul_le_mul hu le_rfl hlambda hb
  have hlocal : |lambda * u| < 3 := habs.trans_lt hbl
  have hden : 0 < 1 - b * lambda / 3 := denominator_pos hbl
  have hden_le : 1 - b * lambda / 3 ≤ 1 - |lambda * u| / 3 := by linarith
  calc
    Real.exp (lambda * u) ≤
        1 + lambda * u + ((lambda * u) ^ 2 / 2) / (1 - |lambda * u| / 3) :=
      exp_le_quadratic_abs hlocal
    _ ≤ 1 + lambda * u + ((lambda * u) ^ 2 / 2) / (1 - b * lambda / 3) :=
      by simpa only [add_comm] using
        add_le_add_left
          (div_le_div_of_nonneg_left
            (div_nonneg (sq_nonneg (lambda * u)) (by norm_num : (0 : ℝ) ≤ 2))
            hden hden_le)
          (1 + lambda * u)
    _ = _ := by
      unfold psi
      rw [div_div, mul_pow]
      ring

end BestOfBothWorlds.Bernstein
