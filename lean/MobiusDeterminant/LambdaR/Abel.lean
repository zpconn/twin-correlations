import MobiusDeterminant.Basic

/-!
# Double Abel summation against `log(R/d) log(R/e)`

With `K = ⌊R⌋₊`, the weights `w_k = g(k) - g(k+1)`, where `g(k) = log(R/k)` for `k ≤ K`
and `g(k) = 0` otherwise, are nonnegative on `[1, K]`, telescope to
`log(R/d) = ∑_{k=d}^{K} w_k`, and sum to `log R`.  This gives
`|∑_{d,e ≤ K} a(d,e) log(R/d) log(R/e)| ≤ (log R)^2 · max_{k,l} |A(k,l)|`.
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace MobiusDeterminant

/-- `g(k) = log(R/k)` for `k ≤ ⌊R⌋₊`, and `0` beyond. -/
noncomputable def abelG (R : ℝ) (k : ℕ) : ℝ :=
  if k ≤ ⌊R⌋₊ then Real.log (R / k) else 0

/-- Abel weights `w_k = g(k) - g(k+1)`. -/
noncomputable def abelW (R : ℝ) (k : ℕ) : ℝ :=
  abelG R k - abelG R (k + 1)

lemma sum_Icc_abelW {R : ℝ} {d : ℕ} (hd : d ≤ ⌊R⌋₊) :
    ∑ k ∈ Finset.Icc d ⌊R⌋₊, abelW R k = abelG R d := by
  have h := Finset.sum_Icc_sub (f := abelG R) hd
  have h0 : abelG R (⌊R⌋₊ + 1) = 0 := by simp [abelG]
  unfold abelW
  rw [Finset.sum_sub_distrib] at h ⊢
  linarith

lemma log_div_eq_sum_abelW {R : ℝ} {d : ℕ} (hd : d ∈ Finset.Icc 1 ⌊R⌋₊) :
    Real.log (R / d) = ∑ k ∈ Finset.Icc 1 ⌊R⌋₊, if d ≤ k then abelW R k else 0 := by
  simp only [Finset.mem_Icc] at hd
  rw [← Finset.sum_filter]
  have hf : (Finset.Icc 1 ⌊R⌋₊).filter (fun k => d ≤ k) = Finset.Icc d ⌊R⌋₊ := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [hf, sum_Icc_abelW hd.2]
  simp [abelG, hd.2]

lemma abelW_nonneg {R : ℝ} {k : ℕ} (hk : k ∈ Finset.Icc 1 ⌊R⌋₊) : 0 ≤ abelW R k := by
  simp only [Finset.mem_Icc] at hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk.1
  have hkR : (k : ℝ) ≤ R := (Nat.le_floor_iff' (by omega)).mp hk.2
  have hR : 0 < R := lt_of_lt_of_le hk0 hkR
  unfold abelW abelG
  simp only [hk.2, ↓reduceIte]
  by_cases hk1 : k + 1 ≤ ⌊R⌋₊
  · simp only [hk1, ↓reduceIte, sub_nonneg]
    apply Real.log_le_log
    · positivity
    · apply div_le_div_of_nonneg_left hR.le hk0
      push_cast
      linarith
  · simp only [hk1, ↓reduceIte, sub_zero]
    apply Real.log_nonneg
    rw [le_div_iff₀ hk0]
    linarith

lemma sum_abelW_eq_log {R : ℝ} (hR : 1 ≤ R) :
    ∑ k ∈ Finset.Icc 1 ⌊R⌋₊, abelW R k = Real.log R := by
  have h : 1 ≤ ⌊R⌋₊ := (Nat.one_le_floor_iff R).mpr hR
  rw [sum_Icc_abelW h]
  simp [abelG, h]

/-- For `l ≤ ⌊R⌋₊`, truncating a sum over `[1, ⌊R⌋₊]` at `l`. -/
lemma sum_ite_le_eq {R : ℝ} {l : ℕ} (hl : l ∈ Finset.Icc 1 ⌊R⌋₊) (f : ℕ → ℝ) :
    ∑ e ∈ Finset.Icc 1 ⌊R⌋₊, (if e ≤ l then f e else 0) = ∑ e ∈ Finset.Icc 1 l, f e := by
  simp only [Finset.mem_Icc] at hl
  rw [← Finset.sum_filter]
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_Icc]
  omega

/-- Single Abel summation:
`∑_{e ≤ K} f(e) log(R/e) = ∑_{l ≤ K} w_l ∑_{e ≤ l} f(e)`. -/
lemma sum_mul_log_eq_abel (R : ℝ) (f : ℕ → ℝ) :
    ∑ e ∈ Finset.Icc 1 ⌊R⌋₊, f e * Real.log (R / e) =
      ∑ l ∈ Finset.Icc 1 ⌊R⌋₊, abelW R l * ∑ e ∈ Finset.Icc 1 l, f e := by
  calc ∑ e ∈ Finset.Icc 1 ⌊R⌋₊, f e * Real.log (R / e)
      = ∑ e ∈ Finset.Icc 1 ⌊R⌋₊, ∑ l ∈ Finset.Icc 1 ⌊R⌋₊,
          (if e ≤ l then abelW R l * f e else 0) := by
        refine Finset.sum_congr rfl fun e he => ?_
        rw [log_div_eq_sum_abelW he, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        split_ifs <;> ring
    _ = ∑ l ∈ Finset.Icc 1 ⌊R⌋₊, ∑ e ∈ Finset.Icc 1 ⌊R⌋₊,
          (if e ≤ l then abelW R l * f e else 0) := Finset.sum_comm
    _ = ∑ l ∈ Finset.Icc 1 ⌊R⌋₊, abelW R l * ∑ e ∈ Finset.Icc 1 l, f e := by
        refine Finset.sum_congr rfl fun l hl => ?_
        rw [← sum_ite_le_eq hl, Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        split_ifs <;> ring

theorem abs_sum_mul_log_log_le (R : ℝ) (hR : 1 ≤ R) (a : ℕ → ℕ → ℝ) (B : ℝ)
    (hB : ∀ k ∈ Finset.Icc 1 ⌊R⌋₊, ∀ l ∈ Finset.Icc 1 ⌊R⌋₊,
      |∑ d ∈ Finset.Icc 1 k, ∑ e ∈ Finset.Icc 1 l, a d e| ≤ B) :
    |∑ d ∈ Finset.Icc 1 ⌊R⌋₊, ∑ e ∈ Finset.Icc 1 ⌊R⌋₊,
        a d e * Real.log (R / d) * Real.log (R / e)|
      ≤ Real.log R ^ 2 * B := by
  have key : ∑ d ∈ Finset.Icc 1 ⌊R⌋₊, ∑ e ∈ Finset.Icc 1 ⌊R⌋₊,
        a d e * Real.log (R / d) * Real.log (R / e) =
      ∑ l ∈ Finset.Icc 1 ⌊R⌋₊, ∑ k ∈ Finset.Icc 1 ⌊R⌋₊, abelW R l * abelW R k *
        ∑ d ∈ Finset.Icc 1 k, ∑ e ∈ Finset.Icc 1 l, a d e := by
    calc ∑ d ∈ Finset.Icc 1 ⌊R⌋₊, ∑ e ∈ Finset.Icc 1 ⌊R⌋₊,
          a d e * Real.log (R / d) * Real.log (R / e)
        = ∑ d ∈ Finset.Icc 1 ⌊R⌋₊, ∑ l ∈ Finset.Icc 1 ⌊R⌋₊,
            abelW R l * ∑ e ∈ Finset.Icc 1 l, a d e * Real.log (R / d) :=
          Finset.sum_congr rfl fun d _ =>
            sum_mul_log_eq_abel R (fun e => a d e * Real.log (R / d))
      _ = ∑ l ∈ Finset.Icc 1 ⌊R⌋₊, ∑ d ∈ Finset.Icc 1 ⌊R⌋₊,
            abelW R l * ∑ e ∈ Finset.Icc 1 l, a d e * Real.log (R / d) := Finset.sum_comm
      _ = ∑ l ∈ Finset.Icc 1 ⌊R⌋₊, abelW R l * ∑ d ∈ Finset.Icc 1 ⌊R⌋₊,
            (∑ e ∈ Finset.Icc 1 l, a d e) * Real.log (R / d) := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [Finset.sum_mul]
      _ = ∑ l ∈ Finset.Icc 1 ⌊R⌋₊, abelW R l * ∑ k ∈ Finset.Icc 1 ⌊R⌋₊,
            abelW R k * ∑ d ∈ Finset.Icc 1 k, ∑ e ∈ Finset.Icc 1 l, a d e := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [sum_mul_log_eq_abel R (fun d => ∑ e ∈ Finset.Icc 1 l, a d e)]
      _ = _ := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
  rw [key]
  calc |∑ l ∈ Finset.Icc 1 ⌊R⌋₊, ∑ k ∈ Finset.Icc 1 ⌊R⌋₊, abelW R l * abelW R k *
          ∑ d ∈ Finset.Icc 1 k, ∑ e ∈ Finset.Icc 1 l, a d e|
      ≤ ∑ l ∈ Finset.Icc 1 ⌊R⌋₊, |∑ k ∈ Finset.Icc 1 ⌊R⌋₊, abelW R l * abelW R k *
          ∑ d ∈ Finset.Icc 1 k, ∑ e ∈ Finset.Icc 1 l, a d e| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l ∈ Finset.Icc 1 ⌊R⌋₊, ∑ k ∈ Finset.Icc 1 ⌊R⌋₊, |abelW R l * abelW R k *
          ∑ d ∈ Finset.Icc 1 k, ∑ e ∈ Finset.Icc 1 l, a d e| :=
        Finset.sum_le_sum fun l _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l ∈ Finset.Icc 1 ⌊R⌋₊, ∑ k ∈ Finset.Icc 1 ⌊R⌋₊, abelW R l * abelW R k * B := by
        refine Finset.sum_le_sum fun l hl => Finset.sum_le_sum fun k hk => ?_
        have hwl := abelW_nonneg hl
        have hwk := abelW_nonneg hk
        rw [abs_mul, abs_of_nonneg (mul_nonneg hwl hwk)]
        exact mul_le_mul_of_nonneg_left (hB k hk l hl) (mul_nonneg hwl hwk)
    _ = (∑ l ∈ Finset.Icc 1 ⌊R⌋₊, abelW R l) * (∑ k ∈ Finset.Icc 1 ⌊R⌋₊, abelW R k) * B := by
        rw [Finset.sum_mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.sum_mul]
    _ = Real.log R ^ 2 * B := by
        rw [sum_abelW_eq_log hR]
        ring

#print axioms abs_sum_mul_log_log_le

end MobiusDeterminant
