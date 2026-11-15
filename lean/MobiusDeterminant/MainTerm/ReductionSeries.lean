import MobiusDeterminant.MainTerm.ReductionIdentity

/-!
# The singular series as a sum over squarefree `g`

`sfun g = μ(g)^2 h(g) / φ(g)^2` is multiplicative and `∑' g, sfun g = twinConstant`.
We also prove `φ(n)^4 ≥ n^3 / 64` for squarefree `n`, which gives summability of
`wfun g = μ(g)^2 / φ(g)^2 = |sfun g|` and of the Rankin majorant `g^{1/4} wfun g`.
-/

open Finset Real
open scoped ArithmeticFunction.Moebius

namespace MobiusDeterminant

namespace Reduction

/-- Coefficients of the singular series: `μ(g)^2 h(g) / φ(g)^2`. -/
noncomputable def sfun (g : ℕ) : ℝ := (μ g : ℝ) ^ 2 * hfun g / (Nat.totient g : ℝ) ^ 2

/-- Absolute values of the coefficients: `μ(g)^2 / φ(g)^2`. -/
noncomputable def wfun (g : ℕ) : ℝ := (μ g : ℝ) ^ 2 / (Nat.totient g : ℝ) ^ 2

lemma wfun_nonneg (g : ℕ) : 0 ≤ wfun g := by
  unfold wfun; positivity

lemma abs_sfun (g : ℕ) : |sfun g| = wfun g := by
  unfold sfun wfun
  rw [abs_div, abs_mul, abs_hfun, mul_one, abs_of_nonneg (sq_nonneg _),
    abs_of_nonneg (sq_nonneg _)]

lemma sfun_zero : sfun 0 = 0 := by simp [sfun]

lemma sfun_one : sfun 1 = 1 := by simp [sfun, hfun]

lemma sfun_mul {m n : ℕ} (h : Nat.Coprime m n) : sfun (m * n) = sfun m * sfun n := by
  unfold sfun
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h, hfun_mul_of_coprime h,
    Nat.totient_mul h]
  push_cast
  ring

lemma sfun_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) : sfun (p ^ k) = 0 := by
  simp [sfun, ArithmeticFunction.moebius_apply_prime_pow hp (by omega : k ≠ 0),
    show k ≠ 1 by omega]

lemma sfun_prime {p : ℕ} (hp : p.Prime) :
    sfun p = if p = 2 then 1 else -1 / ((p : ℝ) - 1) ^ 2 := by
  unfold sfun hfun
  rw [ArithmeticFunction.moebius_apply_prime hp, hp.primeFactors, prod_singleton,
    Nat.totient_prime hp]
  unfold hsign
  split_ifs with h2
  · subst h2; norm_num
  · rw [Nat.cast_sub hp.one_le]
    push_cast
    ring

lemma tsum_sfun_prime_pow {p : ℕ} (hp : p.Prime) : ∑' e, sfun (p ^ e) = twinLocal p := by
  rw [tsum_eq_sum (s := range 2)]
  · rw [sum_range_succ, sum_range_one, pow_zero, pow_one, sfun_one, sfun_prime hp, twinLocal]
    split_ifs <;> ring
  · intro b hb
    simp only [mem_range, not_lt] at hb
    exact sfun_prime_pow hp hb

/-! ### Lower bound for `φ` on squarefree numbers -/

lemma totient_eq_prod_of_squarefree {n : ℕ} (hn : Squarefree n) :
    Nat.totient n = ∏ p ∈ n.primeFactors, (p - 1) := by
  have h := Nat.totient_mul_prod_primeFactors n
  rw [Nat.prod_primeFactors_of_squarefree hn, mul_comm] at h
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn.ne_zero) h

lemma prime_cube_le_eight_mul {p : ℕ} (hp : p.Prime) : p ^ 3 ≤ 8 * (p - 1) ^ 4 := by
  have h2 := hp.two_le
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hq : 1 ≤ q := by omega
  calc (q + 1) ^ 3 ≤ (2 * q) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    _ = 8 * q ^ 3 := by ring
    _ ≤ 8 * q ^ 4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hq (by norm_num))

lemma cube_le_pow_four {p : ℕ} (hp : 5 ≤ p) : p ^ 3 ≤ (p - 1) ^ 4 := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hq : 4 ≤ q := by omega
  have h1 : 4 * q ^ 3 ≤ q ^ 4 := by
    calc 4 * q ^ 3 ≤ q * q ^ 3 := Nat.mul_le_mul_right _ hq
      _ = q ^ 4 := by ring
  have h2 : 4 * q ^ 2 ≤ q ^ 3 := by
    calc 4 * q ^ 2 ≤ q * q ^ 2 := Nat.mul_le_mul_right _ hq
      _ = q ^ 3 := by ring
  have h3 : 4 * q ≤ q ^ 2 := by
    calc 4 * q ≤ q * q := Nat.mul_le_mul_right _ hq
      _ = q ^ 2 := by ring
  nlinarith [h1, h2, h3]

lemma cube_le_totient_pow_four {n : ℕ} (hn : Squarefree n) :
    n ^ 3 ≤ 64 * (Nat.totient n) ^ 4 := by
  rw [totient_eq_prod_of_squarefree hn]
  conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hn]
  rw [← prod_pow, ← prod_pow]
  set s := n.primeFactors with hs
  rw [← prod_filter_mul_prod_filter_not s (fun p => p < 5),
    ← prod_filter_mul_prod_filter_not s (fun p => p < 5) (f := fun p => (p - 1) ^ 4)]
  have h1 : ∏ p ∈ s.filter (fun p => p < 5), p ^ 3 ≤
      ∏ p ∈ s.filter (fun p => p < 5), (8 * (p - 1) ^ 4) := by
    apply prod_le_prod
    intro p hp
    exact prime_cube_le_eight_mul (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1)
  have h2 : ∏ p ∈ s.filter (fun p => ¬ p < 5), p ^ 3 ≤
      ∏ p ∈ s.filter (fun p => ¬ p < 5), (p - 1) ^ 4 := by
    apply prod_le_prod
    intro p hp
    exact cube_le_pow_four (by have := (mem_filter.mp hp).2; omega)
  have hcard : (s.filter (fun p => p < 5)).card ≤ 2 := by
    have hsub : s.filter (fun p => p < 5) ⊆ {2, 3} := by
      intro p hp
      rw [mem_filter] at hp
      have hpp := Nat.prime_of_mem_primeFactors hp.1
      have h2 := hpp.two_le
      have h5 := hp.2
      have : p = 2 ∨ p = 3 := by
        interval_cases p
        · left; rfl
        · right; rfl
        · exact absurd hpp (by norm_num)
      rcases this with rfl | rfl <;> simp
    exact (card_le_card hsub).trans (card_le_two)
  have h3 : ∏ p ∈ s.filter (fun p => p < 5), (8 * (p - 1) ^ 4) ≤
      64 * ∏ p ∈ s.filter (fun p => p < 5), (p - 1) ^ 4 := by
    rw [prod_mul_distrib, prod_const]
    apply Nat.mul_le_mul_right
    calc 8 ^ (s.filter (fun p => p < 5)).card ≤ 8 ^ 2 :=
          Nat.pow_le_pow_right (by norm_num) hcard
      _ = 64 := by norm_num
  calc (∏ p ∈ s.filter (fun p => p < 5), p ^ 3) * ∏ p ∈ s.filter (fun p => ¬ p < 5), p ^ 3
      ≤ (64 * ∏ p ∈ s.filter (fun p => p < 5), (p - 1) ^ 4) *
          ∏ p ∈ s.filter (fun p => ¬ p < 5), (p - 1) ^ 4 :=
        Nat.mul_le_mul (h1.trans h3) h2
    _ = _ := by ring

lemma rpow_three_halves_le_totient_sq {n : ℕ} (hn : Squarefree n) :
    (n : ℝ) ^ ((3 : ℝ) / 2) ≤ 8 * (Nat.totient n : ℝ) ^ 2 := by
  have h := cube_le_totient_pow_four hn
  have hR : ((n : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 ≤ (8 * (Nat.totient n : ℝ) ^ 2) ^ 2 := by
    have e1 : ((n : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 = (n : ℝ) ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]; norm_num
    rw [e1]
    have h' : ((n ^ 3 : ℕ) : ℝ) ≤ ((64 * (Nat.totient n) ^ 4 : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    nlinarith [h']
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp hR

lemma wfun_le (n : ℕ) : wfun n ≤ 8 * ((n : ℝ) ^ ((3 : ℝ) / 2))⁻¹ := by
  by_cases hsq : Squarefree n
  · have hn : n ≠ 0 := hsq.ne_zero
    have hφ : (0 : ℝ) < Nat.totient n := by
      exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn)
    have hpos : (0 : ℝ) < (n : ℝ) ^ ((3 : ℝ) / 2) := by
      apply Real.rpow_pos_of_pos; exact_mod_cast Nat.pos_of_ne_zero hn
    have hμ : (μ n : ℝ) ^ 2 = 1 := by
      rw [ArithmeticFunction.moebius_apply_of_squarefree hsq]
      push_cast
      rw [← pow_mul, mul_comm, pow_mul]
      simp
    unfold wfun
    rw [hμ, div_le_iff₀ (by positivity)]
    have := rpow_three_halves_le_totient_sq hsq
    calc (1 : ℝ) = ((n : ℝ) ^ ((3 : ℝ) / 2))⁻¹ * (n : ℝ) ^ ((3 : ℝ) / 2) := by
          field_simp
      _ ≤ ((n : ℝ) ^ ((3 : ℝ) / 2))⁻¹ * (8 * (Nat.totient n : ℝ) ^ 2) := by
          gcongr
      _ = _ := by ring
  · have : wfun n = 0 := by
      simp [wfun, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
    rw [this]
    positivity

lemma summable_wfun : Summable wfun :=
  Summable.of_nonneg_of_le wfun_nonneg wfun_le
    ((Real.summable_nat_rpow_inv.mpr (by norm_num)).mul_left 8)

lemma rankin_wfun_le (n : ℕ) :
    (n : ℝ) ^ ((1 : ℝ) / 4) * wfun n ≤ 8 * ((n : ℝ) ^ ((5 : ℝ) / 4))⁻¹ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsplit : (n : ℝ) ^ ((3 : ℝ) / 2) = (n : ℝ) ^ ((1 : ℝ) / 4) * (n : ℝ) ^ ((5 : ℝ) / 4) := by
    rw [← Real.rpow_add hn']; norm_num
  have h1 := wfun_le n
  have hpos : 0 < (n : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hn' _
  have hpos' : 0 < (n : ℝ) ^ ((5 : ℝ) / 4) := Real.rpow_pos_of_pos hn' _
  calc (n : ℝ) ^ ((1 : ℝ) / 4) * wfun n
      ≤ (n : ℝ) ^ ((1 : ℝ) / 4) * (8 * ((n : ℝ) ^ ((3 : ℝ) / 2))⁻¹) := by gcongr
    _ = 8 * ((n : ℝ) ^ ((5 : ℝ) / 4))⁻¹ := by
      rw [hsplit]; field_simp

lemma summable_rankin_wfun : Summable (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / 4) * wfun n) :=
  Summable.of_nonneg_of_le (fun n => mul_nonneg (by positivity) (wfun_nonneg n))
    rankin_wfun_le ((Real.summable_nat_rpow_inv.mpr (by norm_num)).mul_left 8)

lemma summable_norm_sfun : Summable (fun n => ‖sfun n‖) := by
  simp_rw [Real.norm_eq_abs, abs_sfun]
  exact summable_wfun

lemma summable_sfun : Summable sfun := summable_norm_sfun.of_norm

/-- The singular series: `twinConstant = ∑' g, μ(g)^2 h(g) / φ(g)^2`. -/
theorem twinConstant_eq_tsum_sfun : twinConstant = ∑' n, sfun n := by
  rw [← EulerProduct.eulerProduct_tprod sfun_one (fun h => sfun_mul h) summable_norm_sfun
    sfun_zero]
  unfold twinConstant
  congr 1
  funext p
  exact (tsum_sfun_prime_pow p.prop).symm

end Reduction

end MobiusDeterminant
