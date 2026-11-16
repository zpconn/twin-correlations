import MobiusDeterminant.Unconditional.PNTMobius
import MobiusDeterminant.MainTerm.MobiusSumsSmooth
import MobiusDeterminant.Unconditional.LevelArith

/-!
# Möbius sums coprime to a modulus

`M_q(n) = ∑_{d ≤ n, (d,q)=1} μ(d)` satisfies `M_q(n) ≪ D exp(-c √log D)` for
`D/4 ≤ n ≤ 2D` and `q ≤ 4 D²`, uniformly in `q` (`Mq_bound`).

Via `μ · 1[(·,q)=1] = 1_{q^∞} * μ`, `M_q(n) = ∑_{k ∣ q^∞, k ≤ n} M(n/k)`.  For `k ≤ √D` the PNT
for `μ` applies to `M(n/k)` (with `∑_{k ≤ √D} 1/k ≤ 1 + log √D`); for `k > √D` the trivial bound
`|M(n/k)| ≤ n/k` and Rankin's trick `∑_{k ∣ q^∞, k > y} 1/k ≤ y^{-1/2} ∏_{p ∣ q} (1 - p^{-1/2})^{-1}`,
with `∏_{p ∣ q} (1 - p^{-1/2})^{-1} ≤ τ(q)² ≪ q^{1/16}`.
-/

open Finset Real
open scoped ArithmeticFunction.Moebius

namespace MobiusDeterminant
namespace Determinant
namespace OddMain

open MobiusSums

/-! ## Elementary bounds for `ep c x = exp(-c √log x)` -/

lemma sqrt_log_le {x a : ℝ} (hx : 0 < x) (ha : 1 ≤ a) :
    Real.sqrt (Real.log x) ≤ Real.sqrt (Real.log (x / a)) + Real.sqrt (Real.log a) := by
  have ha0 : 0 < a := by linarith
  have hla : 0 ≤ Real.log a := Real.log_nonneg ha
  have hsplit : Real.log x = Real.log (x / a) + Real.log a := by
    rw [Real.log_div hx.ne' ha0.ne']; ring
  rcases le_or_gt (Real.log (x / a)) 0 with h | h
  · rw [Real.sqrt_eq_zero'.mpr h, zero_add]
    exact Real.sqrt_le_sqrt (by linarith)
  · rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [add_sq, Real.sq_sqrt h.le, Real.sq_sqrt hla, hsplit]
    have := mul_nonneg (Real.sqrt_nonneg (Real.log (x / a))) (Real.sqrt_nonneg (Real.log a))
    nlinarith

lemma ep_div_le {c x a : ℝ} (hc : 0 ≤ c) (hx : 0 < x) (ha : 1 ≤ a) :
    ep c (x / a) ≤ Real.exp (c * Real.sqrt (Real.log a)) * ep c x := by
  unfold ep
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have := mul_le_mul_of_nonneg_left (sqrt_log_le hx ha) hc
  linarith

lemma ep_rpow_half {c D : ℝ} (hc : 0 ≤ c) (hD : 1 ≤ D) :
    ep c (D ^ (1 / 2 : ℝ)) ≤ ep (c / 2) D := by
  unfold ep
  apply Real.exp_le_exp.mpr
  have hD0 : 0 < D := by linarith
  rw [Real.log_rpow hD0]
  have hL : 0 ≤ Real.log D := Real.log_nonneg hD
  have h1 : Real.sqrt (Real.log D) / 2 ≤ Real.sqrt (1 / 2 * Real.log D) := by
    rw [Real.le_sqrt (by positivity) (by positivity), div_pow, Real.sq_sqrt hL]
    linarith
  have := mul_le_mul_of_nonneg_left h1 hc
  linarith

lemma log_mul_ep_le {b D : ℝ} (hb : 0 < b) (hD : 1 ≤ D) :
    (1 + Real.log D) * ep b D ≤ (1 + 8 / b ^ 2) * ep (b / 2) D := by
  unfold ep
  have hL : 0 ≤ Real.log D := Real.log_nonneg hD
  set u := Real.sqrt (Real.log D) with hu
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hLu : Real.log D = u ^ 2 := (Real.sq_sqrt hL).symm
  rw [hLu]
  set E := Real.exp (-(b / 2) * u) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hsplit : Real.exp (-b * u) = E * E := by
    rw [hE, ← Real.exp_add]; ring_nf
  have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ b / 2 * u by positivity)
  have hEF : E * Real.exp (b / 2 * u) = 1 := by
    rw [hE, ← Real.exp_add]; ring_nf; exact Real.exp_zero
  have h1 : u ^ 2 * E ≤ 8 / b ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have h2 := mul_le_mul_of_nonneg_left hq hEpos.le
    rw [hEF] at h2
    have h3 : 0 ≤ E * (b / 2 * u) := by positivity
    nlinarith
  have h2 : E ≤ 1 := by
    rw [hE, Real.exp_le_one_iff]; nlinarith
  rw [hsplit]
  have h4 := mul_le_mul_of_nonneg_right h1 hEpos.le
  have h5 := mul_le_mul_of_nonneg_right h2 hEpos.le
  nlinarith

lemma rpow_neg_le_ep (c : ℝ) {D : ℝ} (hD : 1 ≤ D) :
    1 / D ^ (1 / 8 : ℝ) ≤ Real.exp (2 * c ^ 2) * ep c D := by
  have hD0 : 0 < D := by linarith
  have hL : 0 ≤ Real.log D := Real.log_nonneg hD
  unfold ep
  rw [← Real.exp_add, Real.rpow_def_of_pos hD0, one_div, ← Real.exp_neg]
  apply Real.exp_le_exp.mpr
  set u := Real.sqrt (Real.log D)
  have hLu : Real.log D = u ^ 2 := (Real.sq_sqrt hL).symm
  rw [hLu]
  nlinarith [sq_nonneg (u - 4 * c)]

/-! ## `∏_{p ∣ q} (1 - p^{-1/2})^{-1} ≪ q^{1/16}` -/

/-- `B(q) = ∏_{p ∣ q} (1 - p^{-1/2})^{-1} = ∑_{k ∣ q^∞} k^{-1/2}`. -/
noncomputable def Bq (q : ℕ) : ℝ := ∏ p ∈ q.primeFactors, (1 - 1 / (p : ℝ) ^ (1 / 2 : ℝ))⁻¹

lemma two_pow_card_primeFactors_le (q : ℕ) (hq : q ≠ 0) :
    2 ^ q.primeFactors.card ≤ q.divisors.card := by
  rw [Nat.card_divisors hq]
  apply Finset.pow_card_le_prod
  intro p hp
  have : q.factorization p ≠ 0 := by
    rw [← Finsupp.mem_support_iff, Nat.support_factorization]; exact hp
  omega

lemma factor_le_four {p : ℕ} (hp : p.Prime) : (1 - 1 / (p : ℝ) ^ (1 / 2 : ℝ))⁻¹ ≤ 4 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hsq : (4 / 3 : ℝ) ≤ (p : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow, Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith
  have hpos : 0 < (p : ℝ) ^ (1 / 2 : ℝ) := by positivity
  have h3 : 1 / (p : ℝ) ^ (1 / 2 : ℝ) ≤ 3 / 4 := by
    rw [div_le_iff₀ hpos]; linarith
  have h4 : 0 < 1 - 1 / (p : ℝ) ^ (1 / 2 : ℝ) := by linarith
  rw [inv_le_comm₀ h4 (by norm_num)]
  linarith

lemma factor_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ (1 - 1 / (p : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have : 1 / (p : ℝ) ^ (1 / 2 : ℝ) < 1 := by
    rw [div_lt_one (by positivity)]
    exact Real.one_lt_rpow hp1 (by norm_num)
  have : 0 < 1 - 1 / (p : ℝ) ^ (1 / 2 : ℝ) := by linarith
  positivity

lemma Bq_le : ∃ C > (0 : ℝ), ∀ q : ℕ, 1 ≤ q → Bq q ≤ C * (q : ℝ) ^ (1 / 16 : ℝ) := by
  obtain ⟨Cτ, hCτ, hτ⟩ := Level.card_divisors_le_rpow (ε := 1 / 32) (by norm_num)
  refine ⟨Cτ ^ 2, by positivity, fun q hq => ?_⟩
  have h4 : Bq q ≤ ((2 : ℝ) ^ q.primeFactors.card) ^ 2 := by
    unfold Bq
    calc ∏ p ∈ q.primeFactors, (1 - 1 / (p : ℝ) ^ (1 / 2 : ℝ))⁻¹
        ≤ ∏ p ∈ q.primeFactors, (4 : ℝ) :=
          Finset.prod_le_prod₀ (fun p hp => factor_nonneg (Nat.prime_of_mem_primeFactors hp))
            (fun p hp => factor_le_four (Nat.prime_of_mem_primeFactors hp))
      _ = ((2 : ℝ) ^ q.primeFactors.card) ^ 2 := by
          rw [Finset.prod_const, ← pow_mul, mul_comm, pow_mul]; norm_num
  have h2 : (2 : ℝ) ^ q.primeFactors.card ≤ q.divisors.card := by
    exact_mod_cast two_pow_card_primeFactors_le q (by omega)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  calc Bq q ≤ ((2 : ℝ) ^ q.primeFactors.card) ^ 2 := h4
    _ ≤ (q.divisors.card : ℝ) ^ 2 := by gcongr
    _ ≤ (Cτ * (q : ℝ) ^ (1 / 32 : ℝ)) ^ 2 := by gcongr; exact hτ q hq
    _ = Cτ ^ 2 * (q : ℝ) ^ (1 / 16 : ℝ) := by
        rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg _)]; norm_num

/-! ## `M_q(n) = ∑_{k ∣ q^∞, k ≤ n} M(n/k)` -/

/-- `M_q(n) = ∑_{d ≤ n, (d,q)=1} μ(d)`. -/
noncomputable def Mq (q n : ℕ) : ℝ := ∑ d ∈ Icc 1 n, ((psiC q d : ℤ) : ℝ)

lemma chiF_real_nonneg (q k : ℕ) : 0 ≤ ((chiF q k : ℤ) : ℝ) := by
  rw [chiF_apply]; split_ifs <;> norm_num

lemma chiF_real_le_one (q k : ℕ) : ((chiF q k : ℤ) : ℝ) ≤ 1 := by
  rw [chiF_apply]; split_ifs <;> norm_num

lemma Mq_eq (q : ℕ) (hq : q ≠ 0) (n : ℕ) :
    Mq q n = ∑ k ∈ Icc 1 n, ((chiF q k : ℤ) : ℝ) * Mf (n / k) := by
  unfold Mq
  have e1 : ∀ d ∈ Icc 1 n, ((psiC q d : ℤ) : ℝ) =
      ∑ x ∈ d.divisorsAntidiagonal, ((chiF q x.1 : ℤ) : ℝ) * ((μ x.2 : ℤ) : ℝ) := by
    intro d _
    rw [← chiF_mul_moebius q hq, ArithmeticFunction.mul_apply]
    push_cast; rfl
  have key := sum_conv_weighted (fun a => ((chiF q a : ℤ) : ℝ)) (fun b => ((μ b : ℤ) : ℝ))
    (fun _ => (1 : ℝ)) n
  simp only [mul_one] at key
  rw [sum_congr rfl e1, key]
  apply sum_congr rfl
  intro k _
  unfold Mf
  rw [Finset.mul_sum]

lemma abs_Mq_le (q : ℕ) (hq : q ≠ 0) (n : ℕ) :
    |Mq q n| ≤ ∑ k ∈ Icc 1 n, ((chiF q k : ℤ) : ℝ) * |Mf (n / k)| := by
  rw [Mq_eq q hq]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  apply sum_congr rfl
  intro k _
  rw [abs_mul, abs_of_nonneg (chiF_real_nonneg q k)]

/-! ## The bound -/

theorem Mq_bound : ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ (D : ℝ) (q n : ℕ), 2 ≤ D → 1 ≤ q →
    (q : ℝ) ≤ 4 * D ^ 2 → 1 ≤ n → D / 4 ≤ n → (n : ℝ) ≤ 2 * D →
      |Mq q n| ≤ C * D * ep c D := by
  obtain ⟨c, hc, C, hC, hM⟩ := Mf_bound pntMobius
  obtain ⟨CB, hCB, hB⟩ := Bq_le
  set K₁ := 2 * C * Real.exp (c * Real.sqrt (Real.log 8)) * (1 + 8 / (c / 2) ^ 2) with hK₁
  set K₂ := 2 * CB * (4 : ℝ) ^ (1 / 16 : ℝ) * Real.exp (2 * (c / 4) ^ 2) with hK₂
  refine ⟨c / 4, by positivity, K₁ + K₂, by positivity, ?_⟩
  intro D q n hD hq1 hqD hn1 hnD hn2
  have hD0 : 0 < D := by linarith
  have hD1 : 1 ≤ D := by linarith
  set y : ℝ := D ^ (1 / 2 : ℝ) with hy
  have hyy : y * y = D := by
    rw [hy, ← Real.rpow_add hD0]; norm_num
  have hy1 : 1 ≤ y := Real.one_le_rpow hD1 (by norm_num)
  have hy0 : 0 < y := by linarith
  have hq0 : q ≠ 0 := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  set E := ep (c / 4) D with hE
  have hEpos : 0 < E := ep_pos _ _
  -- split the sum at `k ≤ y`
  refine (abs_Mq_le q hq0 n).trans ?_
  rw [← Finset.sum_filter_add_sum_filter_not (Icc 1 n) (fun k : ℕ => (k : ℝ) ≤ y)]
  have hS1 : ∑ k ∈ (Icc 1 n).filter (fun k : ℕ => (k : ℝ) ≤ y),
      ((chiF q k : ℤ) : ℝ) * |Mf (n / k)| ≤ K₁ * D * E := by
    have hpt : ∀ k ∈ (Icc 1 n).filter (fun k : ℕ => (k : ℝ) ≤ y),
        ((chiF q k : ℤ) : ℝ) * |Mf (n / k)| ≤ C * n * ep c (y / 8) * (1 / (k : ℝ)) := by
      intro k hk
      simp only [mem_filter, mem_Icc] at hk
      obtain ⟨⟨hk1, hkn⟩, hky⟩ := hk
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
      have hm1 : 1 ≤ n / k := Nat.div_pos hkn hk1
      have hm1R : (1 : ℝ) ≤ ((n / k : ℕ) : ℝ) := by exact_mod_cast hm1
      have hmle : ((n / k : ℕ) : ℝ) ≤ (n : ℝ) / k := Nat.cast_div_le
      have hmgt : (n : ℝ) / k < ((n / k : ℕ) : ℝ) + 1 := by
        have := Nat.lt_floor_add_one ((n : ℝ) / k)
        rwa [Nat.floor_div_eq_div] at this
      have hnk : y / 4 ≤ (n : ℝ) / k := by
        have h1 : (n : ℝ) / y ≤ (n : ℝ) / k := div_le_div_of_nonneg_left hn0.le hk0 hky
        have h2 : y / 4 ≤ (n : ℝ) / y := by
          rw [le_div_iff₀ hy0]; nlinarith
        linarith
      have hm8 : y / 8 ≤ ((n / k : ℕ) : ℝ) := by linarith
      have hep : ep c ((n / k : ℕ) : ℝ) ≤ ep c (y / 8) := ep_anti hc.le (by positivity) hm8
      calc ((chiF q k : ℤ) : ℝ) * |Mf (n / k)| ≤ 1 * |Mf (n / k)| :=
            mul_le_mul_of_nonneg_right (chiF_real_le_one q k) (abs_nonneg _)
        _ ≤ C * ((n / k : ℕ) : ℝ) * ep c ((n / k : ℕ) : ℝ) := by rw [one_mul]; exact hM _ hm1
        _ ≤ C * ((n : ℝ) / k) * ep c (y / 8) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hmle hC.le) hep (ep_pos _ _).le (by positivity)
        _ = C * n * ep c (y / 8) * (1 / (k : ℝ)) := by ring
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [← Finset.mul_sum]
    have hsub : (Icc 1 n).filter (fun k : ℕ => (k : ℝ) ≤ y) ⊆ Icc 1 ⌊y⌋₊ := by
      intro k hk
      simp only [mem_filter, mem_Icc] at hk ⊢
      exact ⟨hk.1.1, Nat.le_floor hk.2⟩
    have hharm : ∑ k ∈ (Icc 1 n).filter (fun k : ℕ => (k : ℝ) ≤ y), 1 / (k : ℝ) ≤
        1 + Real.log D := by
      refine (Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun k _ _ => by positivity)).trans ?_
      have hfl1 : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast hy1)
      have hfl : (0 : ℝ) < ⌊y⌋₊ := by exact_mod_cast hfl1
      have h1 : ∑ k ∈ Icc 1 ⌊y⌋₊, 1 / (k : ℝ) = (harmonic ⌊y⌋₊ : ℝ) := by
        rw [harmonic_eq_sum_Icc]; push_cast; simp [one_div]
      rw [h1]
      refine (harmonic_le_one_add_log _).trans ?_
      have h2 : Real.log ⌊y⌋₊ ≤ Real.log y := Real.log_le_log hfl (Nat.floor_le hy0.le)
      have h3 : Real.log y = 1 / 2 * Real.log D := by rw [hy, Real.log_rpow hD0]
      have h4 : 0 ≤ Real.log D := Real.log_nonneg hD1
      linarith
    have hep8 : ep c (y / 8) ≤ Real.exp (c * Real.sqrt (Real.log 8)) * ep (c / 2) D :=
      (ep_div_le hc.le hy0 (by norm_num)).trans
        (mul_le_mul_of_nonneg_left (ep_rpow_half hc.le hD1) (Real.exp_pos _).le)
    have hlog : (1 + Real.log D) * ep (c / 2) D ≤ (1 + 8 / (c / 2) ^ 2) * E := by
      have := log_mul_ep_le (b := c / 2) (by positivity) hD1
      rwa [show c / 2 / 2 = c / 4 by ring] at this
    have hep0 : 0 ≤ ep c (y / 8) := (ep_pos _ _).le
    calc C * n * ep c (y / 8) * ∑ k ∈ (Icc 1 n).filter (fun k : ℕ => (k : ℝ) ≤ y), 1 / (k : ℝ)
        ≤ C * (2 * D) * (Real.exp (c * Real.sqrt (Real.log 8)) * ep (c / 2) D) *
            (1 + Real.log D) := by
          have h0 : 0 ≤ ∑ k ∈ (Icc 1 n).filter (fun k : ℕ => (k : ℝ) ≤ y), 1 / (k : ℝ) :=
            Finset.sum_nonneg (fun k _ => by positivity)
          gcongr
          exact mul_nonneg (by positivity) (mul_nonneg (Real.exp_pos _).le (ep_pos _ _).le)
      _ = 2 * C * Real.exp (c * Real.sqrt (Real.log 8)) * D *
            ((1 + Real.log D) * ep (c / 2) D) := by ring
      _ ≤ 2 * C * Real.exp (c * Real.sqrt (Real.log 8)) * D *
            ((1 + 8 / (c / 2) ^ 2) * E) := by gcongr
      _ = K₁ * D * E := by rw [hK₁]; ring
  have hS2 : ∑ k ∈ (Icc 1 n).filter (fun k : ℕ => ¬ (k : ℝ) ≤ y),
      ((chiF q k : ℤ) : ℝ) * |Mf (n / k)| ≤ K₂ * D * E := by
    have hpt : ∀ k ∈ (Icc 1 n).filter (fun k : ℕ => ¬ (k : ℝ) ≤ y),
        ((chiF q k : ℤ) : ℝ) * |Mf (n / k)| ≤
          n * (1 / y ^ (1 / 2 : ℝ)) * (((chiF q k : ℤ) : ℝ) * (1 / (k : ℝ) ^ (1 / 2 : ℝ))) := by
      intro k hk
      simp only [mem_filter, mem_Icc, not_le] at hk
      obtain ⟨⟨hk1, hkn⟩, hky⟩ := hk
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
      have hχ := chiF_real_nonneg q k
      have h1 : |Mf (n / k)| ≤ (n : ℝ) / k := (abs_Mf_le _).trans Nat.cast_div_le
      have h2 : (n : ℝ) / k ≤ n * (1 / y ^ (1 / 2 : ℝ)) * (1 / (k : ℝ) ^ (1 / 2 : ℝ)) := by
        have hyk : y ^ (1 / 2 : ℝ) ≤ (k : ℝ) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow hy0.le hky.le (by norm_num)
        have hkk : (k : ℝ) ^ (1 / 2 : ℝ) * (k : ℝ) ^ (1 / 2 : ℝ) = k := by
          rw [← Real.rpow_add hk0]; norm_num
        have hyp : 0 < y ^ (1 / 2 : ℝ) := by positivity
        have hkp : 0 < (k : ℝ) ^ (1 / 2 : ℝ) := by positivity
        rw [mul_assoc, div_eq_mul_one_div (n : ℝ) (k : ℝ)]
        apply mul_le_mul_of_nonneg_left _ hn0.le
        rw [one_div_mul_one_div, one_div_le_one_div hk0 (by positivity)]
        nlinarith
      calc ((chiF q k : ℤ) : ℝ) * |Mf (n / k)| ≤ ((chiF q k : ℤ) : ℝ) *
            (n * (1 / y ^ (1 / 2 : ℝ)) * (1 / (k : ℝ) ^ (1 / 2 : ℝ))) := by
            gcongr; exact h1.trans h2
        _ = _ := by ring
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [← Finset.mul_sum]
    have hsum : ∑ k ∈ (Icc 1 n).filter (fun k : ℕ => ¬ (k : ℝ) ≤ y),
        ((chiF q k : ℤ) : ℝ) * (1 / (k : ℝ) ^ (1 / 2 : ℝ)) ≤ Bq q := by
      exact sum_le_hasSum _ (fun k _ => mul_nonneg (chiF_real_nonneg q k) (by positivity))
        (hasSum_Fg q (by norm_num : (0 : ℝ) < 1 / 2))
    have hBq : Bq q ≤ CB * ((4 : ℝ) ^ (1 / 16 : ℝ) * D ^ (1 / 8 : ℝ)) := by
      refine (hB q hq1).trans ?_
      gcongr
      have hqR : (0 : ℝ) ≤ q := Nat.cast_nonneg _
      calc (q : ℝ) ^ (1 / 16 : ℝ) ≤ (4 * D ^ 2) ^ (1 / 16 : ℝ) :=
            Real.rpow_le_rpow hqR hqD (by norm_num)
        _ = (4 : ℝ) ^ (1 / 16 : ℝ) * D ^ (1 / 8 : ℝ) := by
            rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast,
              ← Real.rpow_mul hD0.le]
            norm_num
    have hy4 : y ^ (1 / 2 : ℝ) = D ^ (1 / 8 : ℝ) * D ^ (1 / 8 : ℝ) := by
      rw [hy, ← Real.rpow_mul hD0.le, ← Real.rpow_add hD0]; norm_num
    have hD8 : 0 < D ^ (1 / 8 : ℝ) := by positivity
    have hrp := rpow_neg_le_ep (c / 4) hD1
    rw [← hE] at hrp
    have h4 : (0 : ℝ) ≤ (4 : ℝ) ^ (1 / 16 : ℝ) := by positivity
    calc (n : ℝ) * (1 / y ^ (1 / 2 : ℝ)) * ∑ k ∈ (Icc 1 n).filter (fun k : ℕ => ¬ (k : ℝ) ≤ y),
          ((chiF q k : ℤ) : ℝ) * (1 / (k : ℝ) ^ (1 / 2 : ℝ))
        ≤ (2 * D) * (1 / y ^ (1 / 2 : ℝ)) *
            (CB * ((4 : ℝ) ^ (1 / 16 : ℝ) * D ^ (1 / 8 : ℝ))) := by
          have h0 : 0 ≤ ∑ k ∈ (Icc 1 n).filter (fun k : ℕ => ¬ (k : ℝ) ≤ y),
              ((chiF q k : ℤ) : ℝ) * (1 / (k : ℝ) ^ (1 / 2 : ℝ)) :=
            Finset.sum_nonneg (fun k _ => mul_nonneg (chiF_real_nonneg q k) (by positivity))
          gcongr
          exact hsum.trans hBq
      _ = 2 * CB * (4 : ℝ) ^ (1 / 16 : ℝ) * D * (1 / D ^ (1 / 8 : ℝ)) := by
          rw [hy4]; field_simp
      _ ≤ 2 * CB * (4 : ℝ) ^ (1 / 16 : ℝ) * D * (Real.exp (2 * (c / 4) ^ 2) * E) := by
          gcongr
      _ = K₂ * D * E := by rw [hK₂]; ring
  calc _ ≤ K₁ * D * E + K₂ * D * E := add_le_add hS1 hS2
    _ = (K₁ + K₂) * D * E := by ring

end OddMain
end Determinant
end MobiusDeterminant
