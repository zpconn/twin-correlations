import Mathlib

/-!
# Real-number bookkeeping for the mean-value theorem (paper, Theorem 6.1, Steps 3–4)

* `phi_bound`: `Φ(U) ≪ D^{11/12} E^{1/2} H^{3/4}` for the balanced boxes, in the form needed
  for the normalization of `BalancedBoxBound` (sizes `U₀ ≤ W₀`, `U₀ W₀ ≤ 2D`,
  `U₀ ≥ 2^{-13} D^{1/3}`);
* `long_target`: `D H^{3/2} ≤ D^{11/12} E^{1/2} H^{3/4}` when `E ≥ D^{2/3} H^2`
  (absorbing the gcd loss of the long boxes);
* elementary facts about `D ≥ 2^{78}` and about `D^ε` losses.
-/

open Real

namespace MobiusDeterminant
namespace MeanValue

lemma rpow_pow_nat {D : ℝ} (hD : 0 ≤ D) (a : ℝ) (n : ℕ) : (D ^ a) ^ n = D ^ (a * n) :=
  (Real.rpow_mul_natCast hD a n).symm

lemma le_of_pow_le_pow {a b : ℝ} (n : ℕ) (hn : n ≠ 0) (hb : 0 ≤ b) (h : a ^ n ≤ b ^ n) :
    a ≤ b :=
  le_of_pow_le_pow_left₀ hn hb h

/-- **Step 3 of Theorem 6.1**: the bound of `BalancedBoxBound` at balanced sizes is
`≪ D^{11/12} E^{1/2} H^{3/4}`. -/
theorem phi_bound {D E H U W : ℝ} (hD : 1 ≤ D) (hE1 : 1 ≤ E) (hED : E ≤ D) (hH : 1 ≤ H)
    (hHD : H ≤ D ^ ((1 : ℝ) / 6)) (hEH : D ^ ((2 : ℝ) / 3) * H ^ 2 ≤ E)
    (hU : D ^ ((1 : ℝ) / 3) / 2 ^ 13 ≤ U) (hUW : U ≤ W) (hprod : U * W ≤ 2 * D) :
    (U * W * H) ^ ((3 : ℝ) / 4) * E ^ ((3 : ℝ) / 8) *
        ((E + (U * H) ^ 2) * (E + W ^ 2)) ^ ((1 : ℝ) / 8)
      ≤ 2 ^ 5 * (D ^ ((11 : ℝ) / 12) * E ^ ((1 : ℝ) / 2) * H ^ ((3 : ℝ) / 4)) := by
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < E := by linarith
  have hH0 : 0 < H := by linarith
  have hU0 : 0 < U := lt_of_lt_of_le (by positivity) hU
  have hW0 : 0 < W := lt_of_lt_of_le hU0 hUW
  -- polynomial forms of the hypotheses
  have p1 : H ^ 6 ≤ D := by
    have := pow_le_pow_left₀ hH0.le hHD 6
    rwa [rpow_pow_nat hD0.le, show (1 : ℝ) / 6 * ((6 : ℕ) : ℝ) = 1 by norm_num,
      Real.rpow_one] at this
  have p2 : D ^ 2 * H ^ 6 ≤ E ^ 3 := by
    have := pow_le_pow_left₀ (by positivity) hEH 3
    rwa [mul_pow, rpow_pow_nat hD0.le, show (2 : ℝ) / 3 * ((3 : ℕ) : ℝ) = (2 : ℕ) by norm_num,
      Real.rpow_natCast, ← pow_mul] at this
  have p3 : D ≤ 2 ^ 39 * U ^ 3 := by
    have := pow_le_pow_left₀ (by positivity) hU 3
    rw [div_pow, rpow_pow_nat hD0.le, show (1 : ℝ) / 3 * ((3 : ℕ) : ℝ) = 1 by norm_num,
      Real.rpow_one] at this
    have h2 : ((2 : ℝ) ^ 13) ^ 3 = 2 ^ 39 := by norm_num
    rw [h2, div_le_iff₀ (by positivity)] at this
    linarith
  have pU2 : U ^ 2 ≤ 2 * D := by nlinarith
  set L := D ^ ((4 : ℝ) / 3) with hLdef
  have hL : 0 < L := by positivity
  have hL3 : L ^ 3 = D ^ 4 := by
    rw [hLdef, rpow_pow_nat hD0.le, show (4 : ℝ) / 3 * ((3 : ℕ) : ℝ) = (4 : ℕ) by norm_num,
      Real.rpow_natCast]
  -- the four comparisons
  have c1 : E ≤ L := by
    apply le_of_pow_le_pow 3 (by norm_num) hL.le
    rw [hL3]
    calc E ^ 3 ≤ D ^ 3 := pow_le_pow_left₀ hE0.le hED 3
      _ ≤ D ^ 4 := pow_le_pow_right₀ hD (by norm_num)
  have c2 : W ^ 2 ≤ 2 ^ 28 * L := by
    apply le_of_pow_le_pow 3 (by norm_num) (by positivity)
    rw [mul_pow, hL3]
    have hUW6 : (U * W) ^ 6 ≤ (2 * D) ^ 6 := pow_le_pow_left₀ (by positivity) hprod 6
    have hD2 : D ^ 2 ≤ 2 ^ 78 * U ^ 6 := by
      have := pow_le_pow_left₀ hD0.le p3 2
      calc D ^ 2 ≤ (2 ^ 39 * U ^ 3) ^ 2 := this
        _ = 2 ^ 78 * U ^ 6 := by ring
    have h1 : W ^ 6 * D ^ 2 ≤ 2 ^ 84 * D ^ 4 * D ^ 2 := by
      calc W ^ 6 * D ^ 2 ≤ W ^ 6 * (2 ^ 78 * U ^ 6) :=
            mul_le_mul_of_nonneg_left hD2 (by positivity)
        _ = 2 ^ 78 * (U * W) ^ 6 := by ring
        _ ≤ 2 ^ 78 * (2 * D) ^ 6 := mul_le_mul_of_nonneg_left hUW6 (by positivity)
        _ = 2 ^ 84 * D ^ 4 * D ^ 2 := by ring
    have h2 : W ^ 6 ≤ 2 ^ 84 * D ^ 4 := le_of_mul_le_mul_right h1 (by positivity)
    calc (W ^ 2) ^ 3 = W ^ 6 := by ring
      _ ≤ 2 ^ 84 * D ^ 4 := h2
      _ = (2 ^ 28) ^ 3 * D ^ 4 := by norm_num
  have c3 : (U * H) ^ 2 ≤ 2 * L := by
    apply le_of_pow_le_pow 3 (by norm_num) (by positivity)
    rw [show (2 * L) ^ 3 = 2 ^ 3 * L ^ 3 by ring, hL3]
    have hU6 : U ^ 6 ≤ 8 * D ^ 3 := by
      have := pow_le_pow_left₀ (by positivity) pU2 3
      calc U ^ 6 = (U ^ 2) ^ 3 := by ring
        _ ≤ (2 * D) ^ 3 := this
        _ = 8 * D ^ 3 := by ring
    calc ((U * H) ^ 2) ^ 3 = U ^ 6 * H ^ 6 := by ring
      _ ≤ (8 * D ^ 3) * D := mul_le_mul hU6 p1 (by positivity) (by positivity)
      _ = 2 ^ 3 * D ^ 4 := by ring
  have c4 : (U * H) ^ 2 * W ^ 2 ≤ 4 * L * E := by
    apply le_of_pow_le_pow 3 (by norm_num) (by positivity)
    have hUW6 : (U * W) ^ 6 ≤ (2 * D) ^ 6 := pow_le_pow_left₀ (by positivity) hprod 6
    calc ((U * H) ^ 2 * W ^ 2) ^ 3 = (U * W) ^ 6 * H ^ 6 := by ring
      _ ≤ (2 * D) ^ 6 * H ^ 6 := mul_le_mul_of_nonneg_right hUW6 (by positivity)
      _ = 64 * D ^ 4 * (D ^ 2 * H ^ 6) := by ring
      _ ≤ 64 * D ^ 4 * E ^ 3 := mul_le_mul_of_nonneg_left p2 (by positivity)
      _ = (4 * L * E) ^ 3 := by rw [mul_pow, mul_pow, hL3]; ring
  have key : (E + (U * H) ^ 2) * (E + W ^ 2) ≤ 2 ^ 29 * L * E := by
    have e1 : E * E ≤ L * E := mul_le_mul_of_nonneg_right c1 hE0.le
    have e2 : E * W ^ 2 ≤ 2 ^ 28 * L * E := by nlinarith
    have e3 : (U * H) ^ 2 * E ≤ 2 * L * E := mul_le_mul_of_nonneg_right c3 hE0.le
    nlinarith
  have hY : 0 ≤ (E + (U * H) ^ 2) * (E + W ^ 2) := by positivity
  have step1 : ((E + (U * H) ^ 2) * (E + W ^ 2)) ^ ((1 : ℝ) / 8)
      ≤ (2 : ℝ) ^ ((29 : ℝ) / 8) * D ^ ((1 : ℝ) / 6) * E ^ ((1 : ℝ) / 8) := by
    refine (Real.rpow_le_rpow hY key (by norm_num)).trans (le_of_eq ?_)
    rw [Real.mul_rpow (by positivity) hE0.le, Real.mul_rpow (by positivity) hL.le, hLdef,
      ← Real.rpow_mul hD0.le, show (2 : ℝ) ^ 29 = (2 : ℝ) ^ (29 : ℝ) by norm_num,
      ← Real.rpow_mul (by norm_num)]
    norm_num
  have step2 : (U * W * H) ^ ((3 : ℝ) / 4) ≤
      (2 : ℝ) ^ ((3 : ℝ) / 4) * D ^ ((3 : ℝ) / 4) * H ^ ((3 : ℝ) / 4) := by
    have h1 : U * W * H ≤ 2 * D * H := mul_le_mul_of_nonneg_right hprod hH0.le
    refine (Real.rpow_le_rpow (by positivity) h1 (by norm_num)).trans (le_of_eq ?_)
    rw [Real.mul_rpow (by positivity) hH0.le, Real.mul_rpow (by norm_num) hD0.le]
  have h2pow : (2 : ℝ) ^ ((3 : ℝ) / 4) * (2 : ℝ) ^ ((29 : ℝ) / 8) ≤ 2 ^ 5 := by
    rw [← Real.rpow_add (by norm_num)]
    calc (2 : ℝ) ^ ((3 : ℝ) / 4 + 29 / 8) ≤ (2 : ℝ) ^ (5 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 ^ 5 := by norm_num
  have hDexp : D ^ ((3 : ℝ) / 4) * D ^ ((1 : ℝ) / 6) = D ^ ((11 : ℝ) / 12) := by
    rw [← Real.rpow_add hD0]; norm_num
  have hEexp : E ^ ((3 : ℝ) / 8) * E ^ ((1 : ℝ) / 8) = E ^ ((1 : ℝ) / 2) := by
    rw [← Real.rpow_add hE0]; norm_num
  calc (U * W * H) ^ ((3 : ℝ) / 4) * E ^ ((3 : ℝ) / 8) *
        ((E + (U * H) ^ 2) * (E + W ^ 2)) ^ ((1 : ℝ) / 8)
      ≤ ((2 : ℝ) ^ ((3 : ℝ) / 4) * D ^ ((3 : ℝ) / 4) * H ^ ((3 : ℝ) / 4)) * E ^ ((3 : ℝ) / 8) *
          ((2 : ℝ) ^ ((29 : ℝ) / 8) * D ^ ((1 : ℝ) / 6) * E ^ ((1 : ℝ) / 8)) := by
        gcongr
    _ = ((2 : ℝ) ^ ((3 : ℝ) / 4) * (2 : ℝ) ^ ((29 : ℝ) / 8)) *
          ((D ^ ((3 : ℝ) / 4) * D ^ ((1 : ℝ) / 6)) *
            (E ^ ((3 : ℝ) / 8) * E ^ ((1 : ℝ) / 8)) * H ^ ((3 : ℝ) / 4)) := by ring
    _ ≤ 2 ^ 5 * (D ^ ((11 : ℝ) / 12) * E ^ ((1 : ℝ) / 2) * H ^ ((3 : ℝ) / 4)) := by
        rw [hDexp, hEexp]
        gcongr

/-- **Step 4 of Theorem 6.1**: `D H^{3/2} ≤ D^{11/12} E^{1/2} H^{3/4}` when `E ≥ D^{2/3} H^2`. -/
theorem long_target {D E H : ℝ} (hD : 1 ≤ D) (hH : 1 ≤ H)
    (hEH : D ^ ((2 : ℝ) / 3) * H ^ 2 ≤ E) :
    D * (H * Real.sqrt H) ≤ D ^ ((11 : ℝ) / 12) * E ^ ((1 : ℝ) / 2) * H ^ ((3 : ℝ) / 4) := by
  have hD0 : 0 < D := by linarith
  have hH0 : 0 < H := by linarith
  have hE0 : 0 < E := lt_of_lt_of_le (by positivity) hEH
  apply le_of_pow_le_pow 12 (by norm_num) (by positivity)
  have hE6 : D ^ 4 * H ^ 12 ≤ E ^ 6 := by
    have := pow_le_pow_left₀ (by positivity) hEH 6
    rwa [mul_pow, rpow_pow_nat hD0.le, show (2 : ℝ) / 3 * ((6 : ℕ) : ℝ) = (4 : ℕ) by norm_num,
      Real.rpow_natCast, ← pow_mul] at this
  have hsq : Real.sqrt H ^ 12 = H ^ 6 := by
    rw [show (12 : ℕ) = 2 * 6 by norm_num, pow_mul, Real.sq_sqrt hH0.le]
  have hl : (D * (H * Real.sqrt H)) ^ 12 = D ^ 12 * (H ^ 12 * H ^ 6) := by
    rw [mul_pow, mul_pow, hsq]
  have hr : (D ^ ((11 : ℝ) / 12) * E ^ ((1 : ℝ) / 2) * H ^ ((3 : ℝ) / 4)) ^ 12 =
      D ^ 11 * E ^ 6 * H ^ 9 := by
    rw [mul_pow, mul_pow, rpow_pow_nat hD0.le, rpow_pow_nat hE0.le, rpow_pow_nat hH0.le,
      show (11 : ℝ) / 12 * ((12 : ℕ) : ℝ) = ((11 : ℕ) : ℝ) by norm_num,
      show (1 : ℝ) / 2 * ((12 : ℕ) : ℝ) = ((6 : ℕ) : ℝ) by norm_num,
      show (3 : ℝ) / 4 * ((12 : ℕ) : ℝ) = ((9 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, Real.rpow_natCast, Real.rpow_natCast]
  rw [hl, hr]
  have hD1 : D ^ 12 ≤ D ^ 11 * D ^ 4 := by
    rw [← pow_add]; exact pow_le_pow_right₀ hD (by norm_num)
  have hH1 : H ^ 18 ≤ H ^ 12 * H ^ 9 := by
    rw [← pow_add]; exact pow_le_pow_right₀ hH (by norm_num)
  calc D ^ 12 * (H ^ 12 * H ^ 6) = D ^ 12 * H ^ 18 := by ring
    _ ≤ (D ^ 11 * D ^ 4) * (H ^ 12 * H ^ 9) := mul_le_mul hD1 hH1 (by positivity) (by positivity)
    _ = D ^ 11 * (D ^ 4 * H ^ 12) * H ^ 9 := by ring
    _ ≤ D ^ 11 * E ^ 6 * H ^ 9 := by gcongr

/-! ## Facts about `D ≥ 2^{78}` -/

section large
variable {D : ℝ}

lemma D_sixth_ge (hD : (2 : ℝ) ^ 78 ≤ D) : (2 : ℝ) ^ 13 ≤ D ^ ((1 : ℝ) / 6) := by
  have h : ((2 : ℝ) ^ 78) ^ ((1 : ℝ) / 6) = 2 ^ 13 := by
    rw [show (2 : ℝ) ^ 78 = (2 : ℝ) ^ ((78 : ℕ) : ℝ) by norm_cast, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [← h]
  exact Real.rpow_le_rpow (by positivity) hD (by norm_num)

lemma D_third_eq (hD0 : 0 < D) : D ^ ((1 : ℝ) / 3) = D ^ ((1 : ℝ) / 6) * D ^ ((1 : ℝ) / 6) := by
  rw [← Real.rpow_add hD0]; norm_num

lemma D_twothirds_eq (hD0 : 0 < D) : D ^ ((2 : ℝ) / 3) = (D ^ ((1 : ℝ) / 3)) ^ 2 := by
  rw [rpow_pow_nat hD0.le]; norm_num

lemma D_eq_third_mul (hD0 : 0 < D) : D = D ^ ((1 : ℝ) / 3) * D ^ ((2 : ℝ) / 3) := by
  rw [← Real.rpow_add hD0]; norm_num

/-- `H ≤ D^{1/6} ≤ 2^{-13} D^{1/3}`. -/
lemma D_sixth_le (hD : (2 : ℝ) ^ 78 ≤ D) : D ^ ((1 : ℝ) / 6) ≤ D ^ ((1 : ℝ) / 3) / 2 ^ 13 := by
  have hD0 : 0 < D := lt_of_lt_of_le (by positivity) hD
  have h6 := D_sixth_ge hD
  rw [D_third_eq hD0, le_div_iff₀ (by positivity)]
  exact mul_le_mul_of_nonneg_left h6 (by positivity)

lemma one_le_D_third_div (hD : (2 : ℝ) ^ 78 ≤ D) : 2 ≤ D ^ ((1 : ℝ) / 3) / 2 ^ 12 := by
  have h1 := D_sixth_le hD
  have h6 := D_sixth_ge hD
  have : D ^ ((1 : ℝ) / 3) / 2 ^ 12 = 2 * (D ^ ((1 : ℝ) / 3) / 2 ^ 13) := by ring
  rw [this]
  have : (1 : ℝ) ≤ 2 ^ 13 := by norm_num
  linarith

lemma D_third_le_div (hD : (2 : ℝ) ^ 78 ≤ D) : D ^ ((1 : ℝ) / 3) ≤ D / 2 ^ 12 := by
  have hD0 : 0 < D := lt_of_lt_of_le (by positivity) hD
  have h := one_le_D_third_div hD
  have h23 : (2 : ℝ) ^ 12 ≤ D ^ ((2 : ℝ) / 3) := by
    rw [D_twothirds_eq hD0]
    have : (2 : ℝ) ^ 12 ≤ D ^ ((1 : ℝ) / 3) := by
      have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ 12)).1 h; linarith
    nlinarith
  rw [le_div_iff₀ (by positivity)]
  conv_rhs => rw [D_eq_third_mul hD0]
  exact mul_le_mul_of_nonneg_left h23 (by positivity)

lemma le_twothirds_of_pow_five (hD : (2 : ℝ) ^ 78 ≤ D) {x : ℝ}
    (h : x ^ 5 ≤ 256 * D) : x ≤ D ^ ((2 : ℝ) / 3) := by
  have hD0 : 0 < D := lt_of_lt_of_le (by positivity) hD
  have hD1 : (1 : ℝ) ≤ D := le_trans (by norm_num) hD
  apply le_of_pow_le_pow 5 (by norm_num) (by positivity)
  refine h.trans ?_
  rw [rpow_pow_nat hD0.le]
  have : D ^ ((2 : ℝ) / 3 * ((5 : ℕ) : ℝ)) = D * D ^ ((7 : ℝ) / 3) := by
    rw [← Real.rpow_one_add' hD0.le (by norm_num)]; norm_num
  rw [this]
  have h7 : D ≤ D ^ ((7 : ℝ) / 3) := by
    calc D = D ^ (1 : ℝ) := (Real.rpow_one D).symm
      _ ≤ D ^ ((7 : ℝ) / 3) := Real.rpow_le_rpow_of_exponent_le hD1 (by norm_num)
  have : (256 : ℝ) ≤ D := le_trans (by norm_num) hD
  nlinarith

end large

/-! ## `D^ε` losses -/

lemma rpow_mul_le_mul {c D ε : ℝ} (hc : 1 ≤ c) (hD : 0 ≤ D) (hε1 : ε ≤ 1) :
    (c * D) ^ ε ≤ c * D ^ ε := by
  rw [Real.mul_rpow (by linarith) hD]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hD _)
  calc c ^ ε ≤ c ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hc hε1
    _ = c := Real.rpow_one c

lemma one_add_log_le {x D ε : ℝ} (hx : 1 ≤ x) (hxD : x ≤ 8 * D) (hD : 1 ≤ D) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) : 1 + Real.log x ≤ 9 * D ^ ε / ε := by
  have hD0 : 0 ≤ D := by linarith
  have h1 : Real.log x ≤ Real.log (8 * D) := Real.log_le_log (by linarith) hxD
  have h2 : Real.log (8 * D) ≤ (8 * D) ^ ε / ε := Real.log_le_rpow_div (by linarith) hε0
  have h3 : (8 * D) ^ ε ≤ 8 * D ^ ε := rpow_mul_le_mul (by norm_num) hD0 hε1
  have hDe : 1 ≤ D ^ ε := Real.one_le_rpow hD hε0.le
  have h4 : 1 ≤ D ^ ε / ε := by
    rw [le_div_iff₀ hε0]; linarith
  have h5 : (8 * D) ^ ε / ε ≤ 8 * D ^ ε / ε := div_le_div_of_nonneg_right h3 hε0.le
  have : 9 * D ^ ε / ε = 8 * D ^ ε / ε + D ^ ε / ε := by ring
  linarith

end MeanValue
end MobiusDeterminant
