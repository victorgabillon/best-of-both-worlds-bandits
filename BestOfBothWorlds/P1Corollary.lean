module

public import BestOfBothWorlds.P1ScheduleIdentities
public import BestOfBothWorlds.P1IdealComplexity
public import BestOfBothWorlds.P1StochasticBound

/-!
Corollary 7 for the actual P1 learner. The complexity comparison uses a rounded
admissible integer schedule. The probability statement covers every positive
horizon: when the rounding budget condition fails, its stated right-hand side
is at least one.
-/

@[expose] public section

open MeasureTheory

namespace BestOfBothWorlds.P1Corollary

variable {K : ℕ}

/-- The exact integer-schedule optimum satisfies the manuscript's factor-two
comparison whenever the horizon is at least the largest-to-smallest gap ratio. -/
theorem optimizedComplexity_le_bob (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    (hduplicate : gap (firstRank hK) = gap (secondRank hK))
    (hcap : ∀ r, gap r ≤ 1) (n : ℕ) (hn : 0 < n)
    (hbudget : gap (lastRank hK) / gap (firstRank hK) ≤ (n : ℝ)) :
    P1Complexity.optimizedComplexity hK gap n hn ≤
      2 * H_BOB hK gap * (P1Ranking.harmonicK K) ^ 2 := by
  calc
    _ ≤ P1Complexity.fixedComplexity gap
        (P1Schedule.rounded hK gap hpos hsorted hduplicate n hn) :=
      P1Complexity.optimizedComplexity_le hK gap n hn _
    _ ≤ 2 * P1Complexity.profileComplexity hK gap
        (P1Complexity.idealFractions hK gap) :=
      P1Complexity.rounded_fixedComplexity_le hK gap hpos hsorted hduplicate n hn hbudget
    _ ≤ 2 * (H_BOB hK gap * (P1Ranking.harmonicK K) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (P1IdealComplexity.ideal_profileComplexity_le hK gap hpos hsorted hduplicate hcap)
        (by positivity)
    _ = _ := by ring

/-- The complexity part of Corollary 7 for the actual stochastic mean-gap
profile, with the manuscript's horizon condition. -/
theorem p1_complexity_le_bob (hK : 2 ≤ K) (ν : Measure (Fin K → ℝ))
    [IsProbabilityMeasure ν] (hbound : ∀ᵐ y ∂ν, ∀ k, 0 ≤ y k ∧ y k ≤ 1)
    (hUnique : P1StochasticModel.UniqueBest hK ν) (n : ℕ) (hn : 0 < n)
    (hbudget : P1StochasticModel.gap hK ν (lastRank hK) /
      P1StochasticModel.gap hK ν (firstRank hK) ≤ (n : ℝ)) :
    P1Complexity.optimizedComplexity hK (P1StochasticModel.gap hK ν) n hn ≤
      2 * H_BOB hK (P1StochasticModel.gap hK ν) * (P1Ranking.harmonicK K) ^ 2 :=
  optimizedComplexity_le_bob hK (P1StochasticModel.gap hK ν)
    (P1StochasticModel.gap_pos hK ν hUnique _)
    (P1StochasticModel.gap_monotone hK ν)
    (P1StochasticModel.gap_duplicate hK ν)
    (P1StochasticModel.gap_le_one hK ν hbound) n hn hbudget

/-- The duplicated smallest gap supplies the second-rank lower bound. -/
theorem two_le_bob_mul_gap_sq (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK))
    (hduplicate : gap (firstRank hK) = gap (secondRank hK)) :
    2 ≤ H_BOB hK gap * (gap (firstRank hK)) ^ 2 := by
  have hterm : (2 : ℝ) / gap (firstRank hK) ≤
      (Finset.univ : Finset (Fin K)).sup'
        ⟨firstRank hK, Finset.mem_univ _⟩
        (fun i => ((i.val + 1 : ℕ) : ℝ) / gap i) := by
    have h := Finset.le_sup'
      (fun i : Fin K => ((i.val + 1 : ℕ) : ℝ) / gap i)
      (Finset.mem_univ (secondRank hK))
    change (2 : ℝ) / gap (secondRank hK) ≤ _ at h
    rw [← hduplicate] at h
    exact h
  have hmul := mul_le_mul_of_nonneg_left hterm (one_div_pos.mpr hpos).le
  have heq : (1 / gap (firstRank hK)) * (2 / gap (firstRank hK)) =
      2 / (gap (firstRank hK)) ^ 2 := by ring
  rw [heq] at hmul
  exact (div_le_iff₀ (pow_pos hpos 2)).1 hmul

/-- For the short horizons omitted by the rounding comparison, the exact
Corollary 7 probability expression is already at least one. -/
theorem short_horizon_rhs_ge_one (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK))
    (hduplicate : gap (firstRank hK) = gap (secondRank hK))
    (hcap : ∀ r, gap r ≤ 1) (n : ℕ) (hn : 0 < n)
    (hshort : (n : ℝ) < gap (lastRank hK) / gap (firstRank hK)) :
    1 ≤ 2 * (K : ℝ) ^ 3 * (n : ℝ) *
      Real.exp (-(n : ℝ) /
        (256 * H_BOB hK gap * (P1Ranking.harmonicK K) ^ 2)) := by
  have hKpos : 0 < K := by omega
  have hKreal : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hn)
  have hH := P1Ranking.one_le_harmonicK hKpos
  have hbob := (gap_complexities_pos hK gap hpos).2.1
  have hsmall := two_le_bob_mul_gap_sq hK gap hpos hduplicate
  have hgapcap := hcap (firstRank hK)
  have hlastcap := hcap (lastRank hK)
  have hnd : (n : ℝ) * gap (firstRank hK) < gap (lastRank hK) :=
    (lt_div_iff₀ hpos).1 hshort
  have hndsq : (n : ℝ) * (gap (firstRank hK)) ^ 2 < 1 := by
    have hm := mul_lt_mul_of_pos_right hnd hpos
    have hc : gap (lastRank hK) * gap (firstRank hK) ≤ 1 :=
      (mul_le_mul_of_nonneg_right hlastcap hpos.le).trans (by simpa using hgapcap)
    nlinarith
  have hn_bob : (n : ℝ) < H_BOB hK gap / 2 := by
    by_contra hnot
    have hm := mul_le_mul_of_nonneg_right (le_of_not_gt hnot)
      (sq_nonneg (gap (firstRank hK)))
    nlinarith
  have hHsq : (1 : ℝ) ≤ (P1Ranking.harmonicK K) ^ 2 := by nlinarith
  have hden : 0 < 256 * H_BOB hK gap * (P1Ranking.harmonicK K) ^ 2 := by positivity
  have hratio : (n : ℝ) /
      (256 * H_BOB hK gap * (P1Ranking.harmonicK K) ^ 2) < 1 / 512 := by
    apply (div_lt_iff₀ hden).2
    nlinarith [mul_le_mul_of_nonneg_left hHsq hbob.le]
  have hexp : (1 / 2 : ℝ) ≤ Real.exp (-(n : ℝ) /
      (256 * H_BOB hK gap * (P1Ranking.harmonicK K) ^ 2)) := by
    have he := Real.add_one_le_exp (-(n : ℝ) /
      (256 * H_BOB hK gap * (P1Ranking.harmonicK K) ^ 2))
    rw [neg_div] at he
    rw [neg_div]
    linarith
  have hpre : (2 : ℝ) ≤ 2 * (K : ℝ) ^ 3 * (n : ℝ) := by
    have hKsq : (1 : ℝ) ≤ (K : ℝ) ^ 2 := by nlinarith
    have hKcube : (1 : ℝ) ≤ (K : ℝ) ^ 3 := by
      have hm := mul_le_mul hKsq (by linarith : (1 : ℝ) ≤ (K : ℝ))
        (by positivity : (0 : ℝ) ≤ 1) (sq_nonneg (K : ℝ))
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hnreal (le_trans zero_le_one hKcube)]
  nlinarith [mul_le_mul hpre hexp (by positivity : (0 : ℝ) ≤ 1 / 2)
    (by positivity : (0 : ℝ) ≤ 2 * (K : ℝ) ^ 3 * (n : ℝ))]

/-- Monotonicity of the final exponential after the integer-schedule comparison. -/
theorem optimized_exponent_le_bob (hK : 2 ≤ K) (gap : Fin K → ℝ)
    (hpos : 0 < gap (firstRank hK)) (hsorted : Monotone gap)
    (hduplicate : gap (firstRank hK) = gap (secondRank hK))
    (hcap : ∀ r, gap r ≤ 1) (n : ℕ) (hn : 0 < n)
    (hbudget : gap (lastRank hK) / gap (firstRank hK) ≤ (n : ℝ)) :
    -(n : ℝ) / (128 * P1Complexity.optimizedComplexity hK gap n hn) ≤
      -(n : ℝ) / (256 * H_BOB hK gap * (P1Ranking.harmonicK K) ^ 2) := by
  have hopt := P1Complexity.optimizedComplexity_pos hK gap hpos hsorted n hn
  have hbob := (gap_complexities_pos hK gap hpos).2.1
  have hH := P1Ranking.harmonicK_pos (by omega : 0 < K)
  have hc := optimizedComplexity_le_bob hK gap hpos hsorted hduplicate hcap n hn hbudget
  apply (div_le_div_iff₀ (by positivity :
    0 < 128 * P1Complexity.optimizedComplexity hK gap n hn)
    (by positivity : 0 < 256 * H_BOB hK gap * (P1Ranking.harmonicK K) ^ 2)).2
  have hm := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg n)
  nlinarith

/-- Corollary 7 for the observable P1 process, at every positive horizon. -/
theorem p1_stochastic_bob_error_bound (hK : 2 ≤ K) (ν : Measure (Fin K → ℝ))
    [IsProbabilityMeasure ν] (hbound : ∀ᵐ y ∂ν, ∀ k, 0 ≤ y k ∧ y k ≤ 1)
    (hUnique : P1StochasticModel.UniqueBest hK ν) (n : ℕ) (hn : 0 < n) :
    P1StochasticEvents.errorProbability hK ν n ≤
      2 * (K : ℝ) ^ 3 * (n : ℝ) *
        Real.exp (-(n : ℝ) / (256 * H_BOB hK (P1StochasticModel.gap hK ν) *
          (P1Ranking.harmonicK K) ^ 2)) := by
  let gap := P1StochasticModel.gap hK ν
  have hpos : 0 < gap (firstRank hK) := P1StochasticModel.gap_pos hK ν hUnique _
  have hsorted : Monotone gap := P1StochasticModel.gap_monotone hK ν
  have hduplicate : gap (firstRank hK) = gap (secondRank hK) :=
    P1StochasticModel.gap_duplicate hK ν
  have hcap : ∀ r, gap r ≤ 1 := P1StochasticModel.gap_le_one hK ν hbound
  by_cases hbudget : gap (lastRank hK) / gap (firstRank hK) ≤ (n : ℝ)
  · exact (P1StochasticBound.p1_stochastic_error_bound hK ν hbound hUnique n hn).trans
      (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr
          (optimized_exponent_le_bob hK gap hpos hsorted hduplicate hcap n hn hbudget))
        (by positivity))
  · have hp : P1StochasticEvents.errorProbability hK ν n ≤ 1 := by
      unfold P1StochasticEvents.errorProbability
      exact measureReal_le_one
    exact hp.trans (short_horizon_rhs_ge_one hK gap hpos hduplicate hcap n hn
      (lt_of_not_ge hbudget))

end BestOfBothWorlds.P1Corollary
