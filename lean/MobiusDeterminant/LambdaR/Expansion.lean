import MobiusDeterminant.Basic

/-!
# Expansion of the truncated pair-correlation sum

We expand `∑_{n ≤ N} Λ_R(n) Λ_R(n+2)` as `N · M(R)` plus the remainder sum
`∑_{d,e ≤ R} μ(d) μ(e) log(R/d) log(R/e) r_N(d,e)`.
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace MobiusDeterminant

/-- For `m ≠ 0`, the divisors `d ∣ m` with `d ≤ R` are exactly the `d ∈ [1, ⌊R⌋₊]`
dividing `m`. -/
lemma divisors_filter_le_eq (R : ℝ) {m : ℕ} (hm : m ≠ 0) :
    m.divisors.filter (fun d : ℕ => (d : ℝ) ≤ R) =
      (Finset.Icc 1 ⌊R⌋₊).filter (fun d => d ∣ m) := by
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hd, -⟩, hdR⟩
    have hd0 : d ≠ 0 := by
      rintro rfl
      exact hm (Nat.eq_zero_of_zero_dvd hd)
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr hd0, (Nat.le_floor_iff' hd0).mpr hdR⟩, hd⟩
  · rintro ⟨⟨h1, hdK⟩, hd⟩
    exact ⟨⟨hd, hm⟩, (Nat.le_floor_iff' (by omega)).mp hdK⟩

/-- `Λ_R(m)` as a sum over `d ∈ [1, ⌊R⌋₊]` with a divisibility indicator. -/
lemma LambdaR_eq_sum_ite (R : ℝ) {m : ℕ} (hm : m ≠ 0) :
    LambdaR R m = ∑ d ∈ Finset.Icc 1 ⌊R⌋₊,
      if d ∣ m then (μ d : ℝ) * Real.log (R / d) else 0 := by
  unfold LambdaR
  rw [divisors_filter_le_eq R hm, Finset.sum_filter]

/-- The sum over `n` of the indicator of `d ∣ n ∧ e ∣ n + 2` is `pairCount`. -/
lemma sum_ite_pair_eq (N d e : ℕ) (x : ℝ) :
    ∑ n ∈ Finset.Icc 1 N, (if d ∣ n ∧ e ∣ n + 2 then x else 0) = (pairCount N d e : ℝ) * x := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rfl

theorem sum_LambdaR_mul_eq (N : ℕ) (R : ℝ) :
    ∑ n ∈ Finset.Icc 1 N, LambdaR R n * LambdaR R (n + 2)
      = (N : ℝ) * mainSum R + ∑ d ∈ Finset.Icc 1 ⌊R⌋₊, ∑ e ∈ Finset.Icc 1 ⌊R⌋₊,
          (μ d : ℝ) * (μ e : ℝ) * Real.log (R / d) * Real.log (R / e) * rem N d e := by
  have h1 : ∀ n ∈ Finset.Icc 1 N, LambdaR R n * LambdaR R (n + 2) =
      ∑ d ∈ Finset.Icc 1 ⌊R⌋₊, ∑ e ∈ Finset.Icc 1 ⌊R⌋₊,
        (if d ∣ n ∧ e ∣ n + 2 then
          (μ d : ℝ) * (μ e : ℝ) * Real.log (R / d) * Real.log (R / e) else 0) := by
    intro n hn
    have hn0 : n ≠ 0 := by
      simp only [Finset.mem_Icc] at hn
      omega
    rw [LambdaR_eq_sum_ite R hn0, LambdaR_eq_sum_ite R (by omega : n + 2 ≠ 0),
      Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => ?_
    by_cases hd : d ∣ n <;> by_cases he : e ∣ n + 2 <;> simp [hd, he]
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  have h2 : ∀ d ∈ Finset.Icc 1 ⌊R⌋₊,
      ∑ n ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 ⌊R⌋₊,
        (if d ∣ n ∧ e ∣ n + 2 then
          (μ d : ℝ) * (μ e : ℝ) * Real.log (R / d) * Real.log (R / e) else 0) =
      ∑ e ∈ Finset.Icc 1 ⌊R⌋₊,
        ((N : ℝ) * ((μ d : ℝ) * (μ e : ℝ) * Real.log (R / d) * Real.log (R / e) * dens d e) +
          (μ d : ℝ) * (μ e : ℝ) * Real.log (R / d) * Real.log (R / e) * rem N d e) := by
    intro d _
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [sum_ite_pair_eq]
    unfold rem
    ring
  rw [Finset.sum_congr rfl h2, mainSum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]

#print axioms sum_LambdaR_mul_eq

end MobiusDeterminant
