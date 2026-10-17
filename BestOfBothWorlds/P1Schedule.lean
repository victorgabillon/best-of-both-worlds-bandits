module

public import BestOfBothWorlds.GapComplexity
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

/-!
P1's deterministic analysis schedules. Comparison times are positive integers,
the best two ranks are compared at the horizon, and later ranks may have equal
comparison times. These schedules are not inputs to the learner.
-/

@[expose] public section

namespace BestOfBothWorlds.P1Schedule

variable {K : ℕ}

/-- The real manuscript rank of a zero-based finite index. -/
def rank (r : Fin K) : ℝ := ((r.val + 1 : ℕ) : ℝ)

theorem rank_pos (r : Fin K) : 0 < rank r := Nat.cast_pos.mpr (Nat.succ_pos r.val)

theorem rank_le (r : Fin K) : rank r ≤ (K : ℝ) :=
  Nat.cast_le.mpr (Nat.succ_le_of_lt r.isLt)

/-- The ranks strictly after `r`. -/
def later (r : Fin K) : Finset (Fin K) := Finset.univ.filter (r < ·)

@[simp] theorem mem_later (r j : Fin K) : j ∈ later r ↔ r < j := by simp [later]

/-- Exactly the integer comparison schedules in the manuscript. -/
structure Schedule (hK : 2 ≤ K) (n : ℕ) where
  time : Fin K → ℕ
  positive : ∀ r, 0 < time r
  le_horizon : ∀ r, time r ≤ n
  antitone : Antitone time
  first_time : time (firstRank hK) = n
  second_time : time (secondRank hK) = n

namespace Schedule

variable {hK : 2 ≤ K} {n : ℕ}

theorem ext {s t : Schedule hK n} (h : ∀ r, s.time r = t.time r) : s = t := by
  cases s
  cases t
  dsimp only at h
  have ht := funext h
  cases ht
  rfl

/-- A bounded integer function encodes the schedule, so the optimization set is finite. -/
def encode (s : Schedule hK n) : Fin K → Fin (n + 1) :=
  fun r => ⟨s.time r, Nat.lt_succ_of_le (s.le_horizon r)⟩

theorem encode_injective : Function.Injective (encode (hK := hK) (n := n)) := by
  intro s t h
  apply ext
  intro r
  exact congrArg Fin.val (congrFun h r)

instance : Finite (Schedule hK n) := Finite.of_injective encode encode_injective

noncomputable instance : Fintype (Schedule hK n) := Fintype.ofFinite _

theorem horizon_pos (s : Schedule hK n) : 0 < n := by
  rw [← s.first_time]
  exact s.positive _

/-- The all-ones fraction vector is an admissible schedule at every positive horizon. -/
def allOnes (hK : 2 ≤ K) (n : ℕ) (hn : 0 < n) : Schedule hK n where
  time _ := n
  positive _ := hn
  le_horizon _ := le_rfl
  antitone _ _ _ := le_rfl
  first_time := rfl
  second_time := rfl

theorem nonempty (hK : 2 ≤ K) (n : ℕ) (hn : 0 < n) : Nonempty (Schedule hK n) :=
  ⟨allOnes hK n hn⟩

end Schedule

/-- The positive telescoped form of the accumulated phase variance allowance. -/
noncomputable def accumulated {hK : 2 ≤ K} {n : ℕ} (s : Schedule hK n) (r : Fin K) : ℝ :=
  rank r * (s.time r : ℝ) + ∑ j ∈ later r, (s.time j : ℝ)

theorem accumulated_ge_rank_time {hK : 2 ≤ K} {n : ℕ} (s : Schedule hK n) (r : Fin K) :
    rank r * (s.time r : ℝ) ≤ accumulated s r := by
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => Nat.cast_nonneg (s.time j)))

theorem accumulated_pos {hK : 2 ≤ K} {n : ℕ} (s : Schedule hK n) (r : Fin K) :
    0 < accumulated s r :=
  (mul_pos (rank_pos r) (Nat.cast_pos.mpr (s.positive r))).trans_le
    (accumulated_ge_rank_time s r)

theorem continuation_pos {hK : 2 ≤ K} {n : ℕ} (s : Schedule hK n) (r : Fin K)
    (t : ℕ) (ht : s.time r ≤ t) :
    0 < accumulated s r + rank r * ((t : ℝ) - (s.time r : ℝ)) := by
  exact add_pos_of_pos_of_nonneg (accumulated_pos s r)
    (mul_nonneg (rank_pos r).le (sub_nonneg.mpr (Nat.cast_le.mpr ht)))

/-- A rank allowance for each zero-based sampling round. -/
noncomputable def envelope {hK : 2 ≤ K} {n : ℕ} (s : Schedule hK n) (r : Fin K) (q : ℕ) : ℝ :=
  rank r + ∑ j ∈ later r, if q < s.time j then (1 : ℝ) else 0

theorem envelope_nonneg {hK : 2 ≤ K} {n : ℕ} (s : Schedule hK n) (r : Fin K) (q : ℕ) :
    0 ≤ envelope s r q := by
  exact add_nonneg (rank_pos r).le
    (Finset.sum_nonneg (fun j _ => by split_ifs <;> positivity))

theorem sum_indicator (m t : ℕ) (hm : m ≤ t) :
    (∑ q ∈ Finset.range t, if q < m then (1 : ℝ) else 0) = (m : ℝ) := by
  classical
  rw [← Finset.sum_filter]
  have hs : (Finset.range t).filter (fun q => q < m) = Finset.range m := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hs]
  simp

/-- Exact summation of the per-round rank envelope, including coincident comparison times. -/
theorem sum_envelope {hK : 2 ≤ K} {n : ℕ} (s : Schedule hK n) (r : Fin K)
    (t : ℕ) (ht : s.time r ≤ t) :
    (∑ q ∈ Finset.range t, envelope s r q) =
      accumulated s r + rank r * ((t : ℝ) - (s.time r : ℝ)) := by
  classical
  simp only [envelope, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  rw [Finset.sum_comm]
  have hinner (j : Fin K) (hj : j ∈ later r) :
      (∑ q ∈ Finset.range t, if q < s.time j then (1 : ℝ) else 0) = (s.time j : ℝ) :=
    sum_indicator _ _ ((s.antitone (le_of_lt ((mem_later r j).1 hj))).trans ht)
  rw [Finset.sum_congr rfl hinner]
  unfold accumulated
  ring

/-- Comparison fractions are obtained from integer times, not independently chosen real rounds. -/
noncomputable def fraction {hK : 2 ≤ K} {n : ℕ} (s : Schedule hK n) (r : Fin K) : ℝ :=
  (s.time r : ℝ) / (n : ℝ)

theorem fraction_pos {hK : 2 ≤ K} {n : ℕ} (s : Schedule hK n) (r : Fin K) :
    0 < fraction s r :=
  div_pos (Nat.cast_pos.mpr (s.positive r)) (Nat.cast_pos.mpr s.horizon_pos)

theorem fraction_le_one {hK : 2 ≤ K} {n : ℕ} (s : Schedule hK n) (r : Fin K) :
    fraction s r ≤ 1 :=
  (div_le_one (Nat.cast_pos.mpr s.horizon_pos)).2 (Nat.cast_le.mpr (s.le_horizon r))

theorem fraction_antitone {hK : 2 ≤ K} {n : ℕ} (s : Schedule hK n) : Antitone (fraction s) := by
  intro r j hrj
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (s.antitone hrj)) (Nat.cast_nonneg n)

theorem fraction_first {hK : 2 ≤ K} {n : ℕ} (s : Schedule hK n) : fraction s (firstRank hK) = 1 := by
  rw [fraction, s.first_time]
  exact div_self (Nat.cast_ne_zero.mpr s.horizon_pos.ne')

theorem fraction_second {hK : 2 ≤ K} {n : ℕ} (s : Schedule hK n) : fraction s (secondRank hK) = 1 := by
  rw [fraction, s.second_time]
  exact div_self (Nat.cast_ne_zero.mpr s.horizon_pos.ne')

/-- Ceilings of the ideal gap ratios give the precise rounded integer schedule. -/
noncomputable def rounded (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    (hduplicate : gap (firstRank hK) = gap (secondRank hK))
    (n : ℕ) (hn : 0 < n) : Schedule hK n where
  time r := ⌈(n : ℝ) * gap (firstRank hK) / gap r⌉₊
  positive r := Nat.ceil_pos.mpr
    (div_pos (mul_pos (Nat.cast_pos.mpr hn) hpos) (gap_pos_of_sorted hK gap hpos hsorted r))
  le_horizon r := Nat.ceil_le.mpr ((div_le_iff₀ (gap_pos_of_sorted hK gap hpos hsorted r)).2
    (mul_le_mul_of_nonneg_left (hsorted (Nat.zero_le r.val)) (Nat.cast_nonneg n)))
  antitone r j hrj := Nat.ceil_mono
    (div_le_div_of_nonneg_left (mul_nonneg (Nat.cast_nonneg n) hpos.le)
      (gap_pos_of_sorted hK gap hpos hsorted r) (hsorted hrj))
  first_time := by rw [mul_div_cancel_right₀ _ hpos.ne']; simp
  second_time := by rw [← hduplicate, mul_div_cancel_right₀ _ hpos.ne']; simp

/-- Upward rounding never moves a comparison earlier. -/
theorem rounded_lower (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    (hduplicate : gap (firstRank hK) = gap (secondRank hK)) (n : ℕ) (hn : 0 < n) (r : Fin K) :
    (n : ℝ) * gap (firstRank hK) / gap r ≤
      ((rounded hK gap hpos hsorted hduplicate n hn).time r : ℝ) :=
  Nat.le_ceil _

/-- In the corollary's budget range, upward rounding costs less than a factor two. -/
theorem rounded_upper (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    (hduplicate : gap (firstRank hK) = gap (secondRank hK)) (n : ℕ) (hn : 0 < n)
    (hbudget : gap (lastRank hK) / gap (firstRank hK) ≤ (n : ℝ)) (r : Fin K) :
    ((rounded hK gap hpos hsorted hduplicate n hn).time r : ℝ) <
      2 * ((n : ℝ) * gap (firstRank hK) / gap r) := by
  have hgapr := gap_pos_of_sorted hK gap hpos hsorted r
  have hlast : gap (lastRank hK) ≤ (n : ℝ) * gap (firstRank hK) :=
    (div_le_iff₀ hpos).1 hbudget
  have hrle : r ≤ lastRank hK := by
    change r.val ≤ K - 1
    omega
  have hone : (1 : ℝ) ≤ (n : ℝ) * gap (firstRank hK) / gap r :=
    (one_le_div hgapr).2 ((hsorted hrle).trans hlast)
  have hc := Nat.ceil_lt_add_one (le_trans zero_le_one hone)
  exact hc.trans_le (by linarith)

end BestOfBothWorlds.P1Schedule
