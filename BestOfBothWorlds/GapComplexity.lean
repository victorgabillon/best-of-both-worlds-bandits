module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.Fin.Basic
public import Mathlib.Analysis.Real.Sqrt

/-!
The finite gap complexities in `problemFormulation.tex`.

An index `i : Fin K` has manuscript rank `i.val + 1`. In particular,
`firstRank` and `secondRank` have manuscript ranks 1 and 2.
-/

@[expose] public section

namespace BestOfBothWorlds

/-- The index of the smallest gap (manuscript rank 1). -/
def firstRank {K : ℕ} (hK : 2 ≤ K) : Fin K :=
  ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hK⟩

/-- The index of the duplicated smallest gap (manuscript rank 2). -/
def secondRank {K : ℕ} (hK : 2 ≤ K) : Fin K :=
  ⟨1, lt_of_lt_of_le (by decide : 1 < 2) hK⟩

/-- `H_SR = max_{1 ≤ r ≤ K} r / Δ_r²`, using a nonempty finite maximum. -/
noncomputable def H_SR {K : ℕ} (hK : 2 ≤ K) (gap : Fin K → ℝ) : ℝ :=
  (Finset.univ : Finset (Fin K)).sup'
    ⟨firstRank hK, Finset.mem_univ _⟩
    (fun i => ((i.val + 1 : ℕ) : ℝ) / (gap i) ^ 2)

/-- `H_UNIF = K / Δ_1²`. -/
noncomputable def H_UNIF {K : ℕ} (hK : 2 ≤ K) (gap : Fin K → ℝ) : ℝ :=
  (K : ℝ) / (gap (firstRank hK)) ^ 2

/-- `H_BOB = (1 / Δ_1) * max_{1 ≤ r ≤ K} r / Δ_r`. -/
noncomputable def H_BOB {K : ℕ} (hK : 2 ≤ K) (gap : Fin K → ℝ) : ℝ :=
  (1 / gap (firstRank hK)) *
    (Finset.univ : Finset (Fin K)).sup'
      ⟨firstRank hK, Finset.mem_univ _⟩
      (fun i => ((i.val + 1 : ℕ) : ℝ) / gap i)

/-- For `0 < Δ_1 = Δ_2 ≤ ⋯ ≤ Δ_K`, the paper's complexities satisfy
`(2 / K) * H_UNIF ≤ H_SR ≤ H_UNIF`.
Positivity of the first gap and monotonicity imply positivity of every gap. -/
theorem gap_complexity_bounds
    {K : ℕ} (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK))
    (hsorted : Monotone gap)
    (hduplicate : gap (firstRank hK) = gap (secondRank hK)) :
    (2 / (K : ℝ)) * H_UNIF hK gap ≤ H_SR hK gap ∧
      H_SR hK gap ≤ H_UNIF hK gap := by
  have hKpos : 0 < K := lt_of_lt_of_le (by decide : 0 < 2) hK
  have hKreal : (K : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hKpos)
  constructor
  · -- Rank 2 contributes `2 / Δ_2²` to the maximum.
    have hsecond : (2 : ℝ) / (gap (secondRank hK)) ^ 2 ≤ H_SR hK gap := by
      exact Finset.le_sup'
        (fun i : Fin K => ((i.val + 1 : ℕ) : ℝ) / (gap i) ^ 2)
        (Finset.mem_univ (secondRank hK))
    calc
      (2 / (K : ℝ)) * H_UNIF hK gap =
          (2 : ℝ) / (gap (firstRank hK)) ^ 2 :=
        div_mul_div_cancel₀ hKreal
      _ = (2 : ℝ) / (gap (secondRank hK)) ^ 2 := by rw [hduplicate]
      _ ≤ H_SR hK gap := hsecond
  · -- Every numerator is at most `K`; every denominator is at least `Δ_1²`.
    apply Finset.sup'_le
    intro i _
    have hfirst : firstRank hK ≤ i := Nat.zero_le i.val
    have hgap : gap (firstRank hK) ≤ gap i := hsorted hfirst
    have hsquare : (gap (firstRank hK)) ^ 2 ≤ (gap i) ^ 2 :=
      pow_le_pow_left₀ hpos.le hgap 2
    have hrank : ((i.val + 1 : ℕ) : ℝ) ≤ (K : ℝ) :=
      Nat.cast_le.mpr (Nat.succ_le_of_lt i.isLt)
    exact div_le_div₀ (Nat.cast_nonneg K) hrank (pow_pos hpos 2) hsquare

/-- The paper's complexity comparison `H_SR ≤ H_BOB ≤ H_UNIF`.
The duplicate-gap hypothesis keeps the interface shared with Step 17A;
these two inequalities use only positivity and sortedness. -/
theorem gap_complexity_sandwich
    {K : ℕ} (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK))
    (hsorted : Monotone gap)
    (_hduplicate : gap (firstRank hK) = gap (secondRank hK)) :
    H_SR hK gap ≤ H_BOB hK gap ∧ H_BOB hK gap ≤ H_UNIF hK gap := by
  have hfactor : 0 ≤ 1 / gap (firstRank hK) := (one_div_pos.mpr hpos).le
  constructor
  · -- Compare each squared-gap term with the corresponding scaled linear-gap term.
    apply Finset.sup'_le
    intro i _
    have hgap : gap (firstRank hK) ≤ gap i := hsorted (Nat.zero_le i.val)
    have hipos : 0 < gap i := lt_of_lt_of_le hpos hgap
    have hdenom : gap (firstRank hK) * gap i ≤ (gap i) ^ 2 := by
      simpa only [pow_two] using mul_le_mul_of_nonneg_right hgap hipos.le
    calc
      ((i.val + 1 : ℕ) : ℝ) / (gap i) ^ 2 ≤
          ((i.val + 1 : ℕ) : ℝ) / (gap (firstRank hK) * gap i) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg _) (mul_pos hpos hipos) hdenom
      _ = (1 / gap (firstRank hK)) * (((i.val + 1 : ℕ) : ℝ) / gap i) := by
        rw [div_mul_div_comm, one_mul]
      _ ≤ H_BOB hK gap :=
        mul_le_mul_of_nonneg_left
          (Finset.le_sup' (fun j : Fin K => ((j.val + 1 : ℕ) : ℝ) / gap j)
            (Finset.mem_univ i)) hfactor
  · -- Bound the inner maximum by `K / Δ_1`, then multiply by `1 / Δ_1`.
    have hmax :
        (Finset.univ : Finset (Fin K)).sup'
          ⟨firstRank hK, Finset.mem_univ _⟩
          (fun i => ((i.val + 1 : ℕ) : ℝ) / gap i) ≤
            (K : ℝ) / gap (firstRank hK) := by
      apply Finset.sup'_le
      intro i _
      have hgap : gap (firstRank hK) ≤ gap i := hsorted (Nat.zero_le i.val)
      have hrank : ((i.val + 1 : ℕ) : ℝ) ≤ (K : ℝ) :=
        Nat.cast_le.mpr (Nat.succ_le_of_lt i.isLt)
      exact div_le_div₀ (Nat.cast_nonneg K) hrank hpos hgap
    calc
      H_BOB hK gap ≤ (1 / gap (firstRank hK)) * ((K : ℝ) / gap (firstRank hK)) :=
        mul_le_mul_of_nonneg_left hmax hfactor
      _ = H_UNIF hK gap := by
        change (1 / gap (firstRank hK)) * ((K : ℝ) / gap (firstRank hK)) =
          (K : ℝ) / (gap (firstRank hK)) ^ 2
        rw [div_mul_div_comm, one_mul, pow_two]

/-- The full complexity chain, combining Steps 17A and 17B. -/
theorem gap_complexity_chain
    {K : ℕ} (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK))
    (hsorted : Monotone gap)
    (hduplicate : gap (firstRank hK) = gap (secondRank hK)) :
    (2 / (K : ℝ)) * H_UNIF hK gap ≤ H_SR hK gap ∧
      H_SR hK gap ≤ H_BOB hK gap ∧ H_BOB hK gap ≤ H_UNIF hK gap :=
  ⟨(gap_complexity_bounds hK gap hpos hsorted hduplicate).1,
    gap_complexity_sandwich hK gap hpos hsorted hduplicate⟩

section Scaling

/-- Multiply every gap by the same real scalar, keeping the existing ranks. -/
def scaleGap {K : ℕ} (c : ℝ) (gap : Fin K → ℝ) : Fin K → ℝ :=
  fun i => c * gap i

/-- Sorted gaps with a positive first gap are positive at every rank. -/
theorem gap_pos_of_sorted
    {K : ℕ} (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap) :
    ∀ i, 0 < gap i := by
  intro i
  exact lt_of_lt_of_le hpos (hsorted (Nat.zero_le i.val))

/-- Positive scaling preserves the paper's positive, sorted, duplicated minimum. -/
theorem scaleGap_admissible
    {K : ℕ} (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    (hduplicate : gap (firstRank hK) = gap (secondRank hK))
    {c : ℝ} (hc : 0 < c) :
    0 < scaleGap c gap (firstRank hK) ∧ Monotone (scaleGap c gap) ∧
      scaleGap c gap (firstRank hK) = scaleGap c gap (secondRank hK) := by
  refine ⟨mul_pos hc hpos, ?_, ?_⟩
  · intro i j hij
    exact mul_le_mul_of_nonneg_left (hsorted hij) hc.le
  · change c * gap (firstRank hK) = c * gap (secondRank hK)
    rw [hduplicate]

/-- All three complexities are positive when the first gap is positive.
The rank-1 terms witness positivity of both finite maxima. -/
theorem gap_complexities_pos
    {K : ℕ} (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) :
    0 < H_SR hK gap ∧ 0 < H_BOB hK gap ∧ 0 < H_UNIF hK gap := by
  have hfirst : (1 : ℝ) / (gap (firstRank hK)) ^ 2 ≤ H_SR hK gap := by
    simpa only [H_SR, firstRank, Nat.zero_add, Nat.cast_one] using
      (Finset.le_sup'
        (fun i : Fin K => ((i.val + 1 : ℕ) : ℝ) / (gap i) ^ 2)
        (Finset.mem_univ (firstRank hK)))
  have hlinear : 0 <
      (Finset.univ : Finset (Fin K)).sup'
        ⟨firstRank hK, Finset.mem_univ _⟩
        (fun i => ((i.val + 1 : ℕ) : ℝ) / gap i) := by
    apply lt_of_lt_of_le (one_div_pos.mpr hpos)
    simpa only [firstRank, Nat.zero_add, Nat.cast_one] using
      (Finset.le_sup'
        (fun i : Fin K => ((i.val + 1 : ℕ) : ℝ) / gap i)
        (Finset.mem_univ (firstRank hK)))
  exact ⟨lt_of_lt_of_le (div_pos zero_lt_one (pow_pos hpos 2)) hfirst,
    mul_pos (one_div_pos.mpr hpos) hlinear,
    div_pos (Nat.cast_pos.mpr (lt_of_lt_of_le (by decide : 0 < 2) hK))
      (pow_pos hpos 2)⟩

/-- Multiplying every gap by `c > 0` divides `H_SR` by `c²`. -/
theorem H_SR_scale
    {K : ℕ} (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    {c : ℝ} (hc : 0 < c) :
    H_SR hK (scaleGap c gap) = H_SR hK gap / c ^ 2 := by
  have hcne : c ≠ 0 := ne_of_gt hc
  unfold H_SR
  calc
    _ = (Finset.univ : Finset (Fin K)).sup'
        ⟨firstRank hK, Finset.mem_univ _⟩
        (fun i => (((i.val + 1 : ℕ) : ℝ) / (gap i) ^ 2) / c ^ 2) := by
      apply Finset.sup'_congr _ rfl
      intro i _
      have hgapne : gap i ≠ 0 := ne_of_gt (gap_pos_of_sorted hK gap hpos hsorted i)
      change ((i.val + 1 : ℕ) : ℝ) / (c * gap i) ^ 2 =
        (((i.val + 1 : ℕ) : ℝ) / (gap i) ^ 2) / c ^ 2
      rw [div_div]
      apply (div_eq_div_iff (pow_ne_zero 2 (mul_ne_zero hcne hgapne))
        (mul_ne_zero (pow_ne_zero 2 hgapne) (pow_ne_zero 2 hcne))).2
      rw [mul_pow, mul_comm (c ^ 2)]
    _ = _ :=
      (map_finset_sup' (OrderIso.divRight₀ (c ^ 2) (pow_pos hc 2)) _ _).symm

/-- Both the prefactor and the inner maximum in `H_BOB` acquire `1 / c`. -/
theorem H_BOB_scale
    {K : ℕ} (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    {c : ℝ} (hc : 0 < c) :
    H_BOB hK (scaleGap c gap) = H_BOB hK gap / c ^ 2 := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have hmax :
      (Finset.univ : Finset (Fin K)).sup'
        ⟨firstRank hK, Finset.mem_univ _⟩
        (fun i => ((i.val + 1 : ℕ) : ℝ) / scaleGap c gap i) =
      (Finset.univ : Finset (Fin K)).sup'
        ⟨firstRank hK, Finset.mem_univ _⟩
        (fun i => ((i.val + 1 : ℕ) : ℝ) / gap i) / c := by
    calc
      _ = (Finset.univ : Finset (Fin K)).sup'
          ⟨firstRank hK, Finset.mem_univ _⟩
          (fun i => (((i.val + 1 : ℕ) : ℝ) / gap i) / c) := by
        apply Finset.sup'_congr _ rfl
        intro i _
        have hgapne : gap i ≠ 0 := ne_of_gt (gap_pos_of_sorted hK gap hpos hsorted i)
        change ((i.val + 1 : ℕ) : ℝ) / (c * gap i) =
          (((i.val + 1 : ℕ) : ℝ) / gap i) / c
        rw [div_div]
        apply (div_eq_div_iff (mul_ne_zero hcne hgapne) (mul_ne_zero hgapne hcne)).2
        rw [mul_comm c]
      _ = _ := (map_finset_sup' (OrderIso.divRight₀ c hc) _ _).symm
  unfold H_BOB
  dsimp only [scaleGap] at hmax ⊢
  rw [hmax, mul_comm c (gap (firstRank hK)), div_mul_eq_div_div,
    div_mul_div_comm, ← pow_two]

/-- The uniform complexity has the same inverse-square scaling law. -/
theorem H_UNIF_scale
    {K : ℕ} (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) {c : ℝ} (hc : 0 < c) :
    H_UNIF hK (scaleGap c gap) = H_UNIF hK gap / c ^ 2 := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have hgapne : gap (firstRank hK) ≠ 0 := ne_of_gt hpos
  change (K : ℝ) / (c * gap (firstRank hK)) ^ 2 =
    ((K : ℝ) / (gap (firstRank hK)) ^ 2) / c ^ 2
  rw [div_div]
  apply (div_eq_div_iff (pow_ne_zero 2 (mul_ne_zero hcne hgapne))
    (mul_ne_zero (pow_ne_zero 2 hgapne) (pow_ne_zero 2 hcne))).2
  rw [mul_pow, mul_comm (c ^ 2)]

/-- Positive scaling leaves all three complexity ratios in Remark 5 unchanged. -/
theorem gap_complexity_ratios_scale
    {K : ℕ} (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    {c : ℝ} (hc : 0 < c) :
    H_BOB hK (scaleGap c gap) / H_SR hK (scaleGap c gap) =
        H_BOB hK gap / H_SR hK gap ∧
      H_SR hK (scaleGap c gap) / H_UNIF hK (scaleGap c gap) =
        H_SR hK gap / H_UNIF hK gap ∧
      H_BOB hK (scaleGap c gap) / H_UNIF hK (scaleGap c gap) =
        H_BOB hK gap / H_UNIF hK gap := by
  have hpositive := gap_complexities_pos hK gap hpos
  have hratio (a b : ℝ) (hb : 0 < b) :
      (a / c ^ 2) / (b / c ^ 2) = a / b := by
    have hscaledpos : 0 < b / c ^ 2 := div_pos hb (pow_pos hc 2)
    apply (div_eq_div_iff (ne_of_gt hscaledpos) (ne_of_gt hb)).2
    rw [div_mul_eq_mul_div, mul_div_assoc]
  rw [H_BOB_scale hK gap hpos hsorted hc, H_SR_scale hK gap hpos hsorted hc,
    H_UNIF_scale hK gap hpos hc]
  exact ⟨hratio _ _ hpositive.1, hratio _ _ hpositive.2.2,
    hratio _ _ hpositive.2.2⟩

end Scaling

section FlatGaps

/-- In Remark 5's flat regime, all three complexities equal `K / delta²`. -/
theorem flat_gap_complexities
    {K : ℕ} (hK : 2 ≤ K) (delta : ℝ) (hdelta : 0 < delta) :
    H_SR hK (fun _ => delta) = (K : ℝ) / delta ^ 2 ∧
      H_BOB hK (fun _ => delta) = (K : ℝ) / delta ^ 2 ∧
      H_UNIF hK (fun _ => delta) = (K : ℝ) / delta ^ 2 := by
  have hKpos : 0 < K := lt_of_lt_of_le (by decide : 0 < 2) hK
  let last : Fin K := ⟨K - 1, Nat.sub_lt hKpos Nat.one_pos⟩
  have hrank : last.val + 1 = K := by
    change K - 1 + 1 = K
    exact Nat.sub_add_cancel (Nat.succ_le_of_lt hKpos)
  have hchain := gap_complexity_chain hK (fun _ => delta) hdelta
    (fun _ _ _ => le_rfl) rfl
  -- The last rank contributes `K / delta²` to the squared-gap maximum.
  have hsr_lower : (K : ℝ) / delta ^ 2 ≤ H_SR hK (fun _ => delta) := by
    simpa only [H_SR, hrank] using
      (Finset.le_sup' (fun i : Fin K => ((i.val + 1 : ℕ) : ℝ) / delta ^ 2)
        (Finset.mem_univ last))
  -- It also contributes `K / delta` to the linear-gap maximum in `H_BOB`.
  have hlinear : (K : ℝ) / delta ≤
      (Finset.univ : Finset (Fin K)).sup'
        ⟨firstRank hK, Finset.mem_univ _⟩
        (fun i => ((i.val + 1 : ℕ) : ℝ) / delta) := by
    simpa only [hrank] using
      (Finset.le_sup' (fun i : Fin K => ((i.val + 1 : ℕ) : ℝ) / delta)
        (Finset.mem_univ last))
  have hbob_lower : (K : ℝ) / delta ^ 2 ≤ H_BOB hK (fun _ => delta) := by
    calc
      (K : ℝ) / delta ^ 2 = (1 / delta) * ((K : ℝ) / delta) := by
        rw [div_mul_div_comm, one_mul, pow_two]
      _ ≤ H_BOB hK (fun _ => delta) :=
        mul_le_mul_of_nonneg_left hlinear (one_div_pos.mpr hdelta).le
  -- The existing chain bounds both complexities by the defining uniform value.
  exact ⟨le_antisymm (le_trans hchain.2.1 hchain.2.2) hsr_lower,
    le_antisymm hchain.2.2 hbob_lower, rfl⟩

/-- The flat-regime complexity ratios are one, using the checked flat values. -/
theorem flat_gap_ratios
    {K : ℕ} (hK : 2 ≤ K) (delta : ℝ) (hdelta : 0 < delta) :
    H_BOB hK (fun _ => delta) / H_SR hK (fun _ => delta) = 1 ∧
      H_SR hK (fun _ => delta) / H_UNIF hK (fun _ => delta) = 1 := by
  obtain ⟨hsr, hbob, hunif⟩ := flat_gap_complexities hK delta hdelta
  have hnonzero : (K : ℝ) / delta ^ 2 ≠ 0 :=
    ne_of_gt (gap_complexities_pos hK (fun _ => delta) hdelta).2.2
  constructor
  · rw [hbob, hsr]
    exact div_self hnonzero
  · rw [hsr, hunif]
    exact div_self hnonzero

end FlatGaps

section SuperlinearGaps

/-- Remark 5's super-linear regime: rank 2 minimizes `Δ_r / r`.
With `Δ_2 = Δ_1`, the visible hypothesis is equivalently `r * Δ_1 ≤ 2 * Δ_r`.
No equality profile or upper gap cap is assumed. -/
theorem superlinear_gap_complexities
    {K : ℕ} (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    (hduplicate : gap (firstRank hK) = gap (secondRank hK))
    (hsuper : ∀ i : Fin K,
      ((i.val + 1 : ℕ) : ℝ) * gap (firstRank hK) ≤ 2 * gap i) :
    H_SR hK gap = 2 / (gap (firstRank hK)) ^ 2 ∧
      H_BOB hK gap = 2 / (gap (firstRank hK)) ^ 2 ∧
      H_UNIF hK gap = (K : ℝ) / (gap (firstRank hK)) ^ 2 := by
  have hchain := gap_complexity_chain hK gap hpos hsorted hduplicate
  have hKreal : (K : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (lt_of_lt_of_le (by decide : 0 < 2) hK))
  -- Step 17A already supplies the rank-2 lower bound.
  have hsr_lower : 2 / (gap (firstRank hK)) ^ 2 ≤ H_SR hK gap := by
    simpa only [H_UNIF, div_mul_div_cancel₀ hKreal] using hchain.1
  -- Positive denominators turn the super-linear hypothesis into a ratio bound.
  have hmax :
      (Finset.univ : Finset (Fin K)).sup'
        ⟨firstRank hK, Finset.mem_univ _⟩
        (fun i => ((i.val + 1 : ℕ) : ℝ) / gap i) ≤
          2 / gap (firstRank hK) := by
    apply Finset.sup'_le
    intro i _
    exact (div_le_div_iff₀ (gap_pos_of_sorted hK gap hpos hsorted i) hpos).2 (hsuper i)
  have hbob_upper : H_BOB hK gap ≤ 2 / (gap (firstRank hK)) ^ 2 := by
    calc
      H_BOB hK gap ≤ (1 / gap (firstRank hK)) * (2 / gap (firstRank hK)) :=
        mul_le_mul_of_nonneg_left hmax (one_div_pos.mpr hpos).le
      _ = 2 / (gap (firstRank hK)) ^ 2 := by
        rw [div_mul_div_comm, one_mul, pow_two]
  -- Both ends of the verified chain now equal `2 / Δ_1²`.
  exact ⟨le_antisymm (hchain.2.1.trans hbob_upper) hsr_lower,
    le_antisymm hbob_upper (hsr_lower.trans hchain.2.1), rfl⟩

/-- The super-linear identities in the manuscript's relative-complexity form. -/
theorem superlinear_gap_ratio
    {K : ℕ} (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    (hduplicate : gap (firstRank hK) = gap (secondRank hK))
    (hsuper : ∀ i : Fin K,
      ((i.val + 1 : ℕ) : ℝ) * gap (firstRank hK) ≤ 2 * gap i) :
    H_SR hK gap = H_BOB hK gap ∧ H_BOB hK gap = (2 / (K : ℝ)) * H_UNIF hK gap := by
  obtain ⟨hsr, hbob, hunif⟩ :=
    superlinear_gap_complexities hK gap hpos hsorted hduplicate hsuper
  have hKreal : (K : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (lt_of_lt_of_le (by decide : 0 < 2) hK))
  constructor
  · exact hsr.trans hbob.symm
  · rw [hbob, hunif]
    exact (div_mul_div_cancel₀ hKreal).symm

end SuperlinearGaps

section SquareRootGaps

/-- The last index has manuscript rank `K`, using the same construction as Step 17D. -/
def lastRank {K : ℕ} (hK : 2 ≤ K) : Fin K :=
  ⟨K - 1, Nat.sub_lt (lt_of_lt_of_le (by decide : 0 < 2) hK) Nat.one_pos⟩

/-- The zero-based last index corresponds exactly to manuscript rank `K`. -/
theorem lastRank_rank {K : ℕ} (hK : 2 ≤ K) : (lastRank hK).val + 1 = K := by
  exact Nat.sub_add_cancel
    (Nat.succ_le_of_lt (lt_of_lt_of_le (by decide : 0 < 2) hK))

/-- The linear-gap term at a positive square-root envelope has this exact value. -/
theorem rank_div_square_root_gap {r a : ℝ} (hr : 0 < r) (ha : 0 < a) :
    r / (a * Real.sqrt (r / 2)) = (2 / a) * Real.sqrt (r / 2) := by
  have hs : 0 < Real.sqrt (r / 2) := Real.sqrt_pos.mpr (div_pos hr zero_lt_two)
  have hsquare : (Real.sqrt (r / 2)) ^ 2 = r / 2 :=
    Real.sq_sqrt (div_nonneg hr.le zero_le_two)
  have hrwrite : r = 2 * (Real.sqrt (r / 2)) ^ 2 := by
    calc
      r = (r / 2) * 2 := (div_mul_cancel₀ r two_ne_zero).symm
      _ = (Real.sqrt (r / 2)) ^ 2 * 2 := by rw [hsquare]
      _ = 2 * (Real.sqrt (r / 2)) ^ 2 := mul_comm _ _
  apply (div_eq_iff (mul_ne_zero ha.ne' hs.ne')).2
  calc
    r = 2 * (Real.sqrt (r / 2)) ^ 2 := hrwrite
    _ = ((2 / a) * a) * (Real.sqrt (r / 2) * Real.sqrt (r / 2)) := by
      rw [div_mul_cancel₀ _ ha.ne', pow_two]
    _ = ((2 / a) * Real.sqrt (r / 2)) * (a * Real.sqrt (r / 2)) :=
      mul_mul_mul_comm _ _ _ _

/-- The squared-gap condition bounds a linear-gap term by its square-root envelope. -/
theorem rank_div_gap_le_square_root
    {r a d : ℝ} (hr : 0 < r) (ha : 0 < a) (hd : 0 < d)
    (hsquared : r * a ^ 2 ≤ 2 * d ^ 2) :
    r / d ≤ (2 / a) * Real.sqrt (r / 2) := by
  have hroot : Real.sqrt (r / 2) ≤ d / a := by
    apply (Real.sqrt_le_left (div_nonneg hd.le ha.le)).2
    rw [div_pow]
    apply (div_le_div_iff₀ zero_lt_two (pow_pos ha 2)).2
    simpa only [mul_comm] using hsquared
  have henvelope : a * Real.sqrt (r / 2) ≤ d := by
    simpa only [mul_comm] using (le_div_iff₀ ha).mp hroot
  calc
    r / d ≤ r / (a * Real.sqrt (r / 2)) :=
      div_le_div_of_nonneg_left hr.le
        (mul_pos ha (Real.sqrt_pos.mpr (div_pos hr zero_lt_two))) henvelope
    _ = (2 / a) * Real.sqrt (r / 2) := rank_div_square_root_gap hr ha

/-- Remark 5's squared-gap minimum and endpoint equality suffice for the exact
square-root complexities. Intermediate gaps need not equal their envelopes. -/
theorem square_root_gap_complexities
    {K : ℕ} (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    (hduplicate : gap (firstRank hK) = gap (secondRank hK))
    (hsquared : ∀ i : Fin K,
      ((i.val + 1 : ℕ) : ℝ) * (gap (firstRank hK)) ^ 2 ≤ 2 * (gap i) ^ 2)
    (hendpoint : gap (lastRank hK) =
      gap (firstRank hK) * Real.sqrt ((K : ℝ) / 2)) :
    H_SR hK gap = 2 / (gap (firstRank hK)) ^ 2 ∧
      H_BOB hK gap = 2 * Real.sqrt ((K : ℝ) / 2) / (gap (firstRank hK)) ^ 2 ∧
      H_UNIF hK gap = (K : ℝ) / (gap (firstRank hK)) ^ 2 := by
  have hKpos : (0 : ℝ) < K :=
    Nat.cast_pos.mpr (lt_of_lt_of_le (by decide : 0 < 2) hK)
  have hchain := gap_complexity_chain hK gap hpos hsorted hduplicate
  have hsr : H_SR hK gap = 2 / (gap (firstRank hK)) ^ 2 := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro i _
      exact (div_le_div_iff₀ (pow_pos (gap_pos_of_sorted hK gap hpos hsorted i) 2)
        (pow_pos hpos 2)).2 (hsquared i)
    · simpa only [H_UNIF, div_mul_div_cancel₀ hKpos.ne'] using hchain.1
  let innerMax : ℝ := (Finset.univ : Finset (Fin K)).sup'
    ⟨firstRank hK, Finset.mem_univ _⟩
    (fun i => ((i.val + 1 : ℕ) : ℝ) / gap i)
  have hupper : innerMax ≤ (2 / gap (firstRank hK)) * Real.sqrt ((K : ℝ) / 2) := by
    apply Finset.sup'_le
    intro i _
    have hrpos : (0 : ℝ) < ((i.val + 1 : ℕ) : ℝ) :=
      Nat.cast_pos.mpr (Nat.succ_pos i.val)
    have hrank : ((i.val + 1 : ℕ) : ℝ) ≤ (K : ℝ) :=
      Nat.cast_le.mpr (Nat.succ_le_of_lt i.isLt)
    exact (rank_div_gap_le_square_root hrpos hpos
      (gap_pos_of_sorted hK gap hpos hsorted i) (hsquared i)).trans
      (mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hrank zero_le_two))
        (div_nonneg zero_le_two hpos.le))
  have hlower : (2 / gap (firstRank hK)) * Real.sqrt ((K : ℝ) / 2) ≤ innerMax := by
    have hlast : (K : ℝ) / gap (lastRank hK) ≤ innerMax := by
      simpa only [lastRank_rank] using
        (Finset.le_sup' (fun i : Fin K => ((i.val + 1 : ℕ) : ℝ) / gap i)
          (Finset.mem_univ (lastRank hK)))
    calc
      (2 / gap (firstRank hK)) * Real.sqrt ((K : ℝ) / 2) =
          (K : ℝ) / gap (lastRank hK) := by
        rw [hendpoint]
        exact (rank_div_square_root_gap hKpos hpos).symm
      _ ≤ innerMax := hlast
  have hmax := le_antisymm hupper hlower
  have hbob : H_BOB hK gap =
      2 * Real.sqrt ((K : ℝ) / 2) / (gap (firstRank hK)) ^ 2 := by
    change (1 / gap (firstRank hK)) * innerMax = _
    rw [hmax]
    rw [← mul_assoc, div_mul_div_comm, one_mul, ← pow_two, div_mul_eq_mul_div]
  exact ⟨hsr, hbob, rfl⟩

/-- The square-root regime's exact multiplicative separation, reusing its values. -/
theorem square_root_gap_separation
    {K : ℕ} (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    (hduplicate : gap (firstRank hK) = gap (secondRank hK))
    (hsquared : ∀ i : Fin K,
      ((i.val + 1 : ℕ) : ℝ) * (gap (firstRank hK)) ^ 2 ≤ 2 * (gap i) ^ 2)
    (hendpoint : gap (lastRank hK) =
      gap (firstRank hK) * Real.sqrt ((K : ℝ) / 2)) :
    H_BOB hK gap = Real.sqrt ((K : ℝ) / 2) * H_SR hK gap := by
  obtain ⟨hsr, hbob, _⟩ :=
    square_root_gap_complexities hK gap hpos hsorted hduplicate hsquared hendpoint
  rw [hsr, hbob, mul_comm (2 : ℝ) (Real.sqrt ((K : ℝ) / 2)), mul_div_assoc]

/-- The corresponding quotient is defined with a positive `H_SR` denominator. -/
theorem square_root_gap_ratio
    {K : ℕ} (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    (hduplicate : gap (firstRank hK) = gap (secondRank hK))
    (hsquared : ∀ i : Fin K,
      ((i.val + 1 : ℕ) : ℝ) * (gap (firstRank hK)) ^ 2 ≤ 2 * (gap i) ^ 2)
    (hendpoint : gap (lastRank hK) =
      gap (firstRank hK) * Real.sqrt ((K : ℝ) / 2)) :
    H_BOB hK gap / H_SR hK gap = Real.sqrt ((K : ℝ) / 2) := by
  rw [square_root_gap_separation hK gap hpos hsorted hduplicate hsquared hendpoint,
    mul_div_cancel_right₀ _ (gap_complexities_pos hK gap hpos).1.ne']

end SquareRootGaps

end BestOfBothWorlds
