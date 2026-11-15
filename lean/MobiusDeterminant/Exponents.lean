import Mathlib

/-!
# Machine-checked exponent bookkeeping

Every numerical / exponent claim of the paper
`paper/main.tex` ("Möbius cancellation on the determinant equation `be - ad = 2`
beyond the Bettin–Chandee range") is restated here as a statement about real
numbers and proved by `linarith` / `nlinarith` / `norm_num` (with case splits
on `max`).

Conventions (paper, Section 7.1): `A = X^x`, `B = X^y`, `D = X/A = X^{1-x}`,
`E = X/B = X^{1-y}`, `T = E/A = X^{1-x-y}`, and, in base `D`,
`λ = log E / log D = (1-y)/(1-x)`, `ϑ = log T / log D = (1-x-y)/(1-x)`.
In Section 6 (Theorem 6.1) exponents are taken in base `D`:
`U = D^a`, `W = D/U = D^{1-a}`, `E = D^λ`, `H = D^η`.  Since `λ` is a Lean
keyword we write `lam`.

The section names `E1`–`E7` follow the formalization plan.
-/

namespace MobiusDeterminant

namespace Exponents

/-! ## E1. The condition `8x + 9y > 8` is `ϑ < 1/9` -/

/-- **(E1)** Paper, Section 7.1 ("The condition `8x+9y>8` is equivalent to
`ϑ<1/9`") and Section 1.3 ("`8m+9M>8` is exactly the condition `T<D^{1/9}`"):
for `0 < x ≤ y ≤ 1/2`, `(1-x-y)/(1-x) < 1/9 ↔ 8x + 9y > 8`. -/
theorem theta_lt_ninth_iff {x y : ℝ} (_hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ 1 / 2) :
    (1 - x - y) / (1 - x) < 1 / 9 ↔ 8 * x + 9 * y > 8 := by
  have h1 : 0 < 1 - x := by linarith
  rw [div_lt_iff₀ h1]
  constructor <;> intro h <;> linarith

/-- Paper, Section 7.1: "Since `y ≤ 1/2`, we have `λ + ϑ ≥ 1`", where
`λ = (1-y)/(1-x)` and `ϑ = (1-x-y)/(1-x)`. -/
theorem lambda_add_theta_ge_one {x y : ℝ} (hx : x < 1) (hy : y ≤ 1 / 2) :
    1 ≤ (1 - y) / (1 - x) + (1 - x - y) / (1 - x) := by
  have h1 : 0 < 1 - x := by linarith
  rw [← add_div, le_div_iff₀ h1]
  linarith

/-- Paper, Section 7.1: `λ = log E / log D` and `ϑ = log T / log D` are
`(1-y)/(1-x)` and `(1-x-y)/(1-x)` when `D = X^{1-x}`, `E = X^{1-y}`,
`T = X^{1-x-y}` (here `logX = log X > 0`). -/
theorem lambda_theta_eq {x y logX : ℝ} (hX : 0 < logX) (hx : x < 1) :
    ((1 - y) * logX) / ((1 - x) * logX) = (1 - y) / (1 - x) ∧
    ((1 - x - y) * logX) / ((1 - x) * logX) = (1 - x - y) / (1 - x) := by
  have h1 : (1 - x) ≠ 0 := by linarith
  constructor <;> field_simp

/-! ## E2. The balanced-box case analysis (Theorem 6.1, Step 3) -/

/-- Base-`D` exponent of
`Φ(U) = (DH)^{3/4} E^{3/8} {(E+(UH)^2)(E+W^2)}^{1/8}` (paper, Theorem 6.1,
Step 3), with `U = D^a`, `W = D^{1-a}`, `E = D^λ`, `H = D^η`, where a sum
`D^s + D^t` is replaced by `D^{max s t}` (up to the factor `2`). -/
noncomputable def phiExp (a η lam : ℝ) : ℝ :=
  3 / 4 * (1 + η) + 3 / 8 * lam + (max lam (2 * a + 2 * η) + max lam (2 - 2 * a)) / 8

/-- Base-`D` exponent of the target `D^{11/12} E^{1/2} H^{3/4}` of Theorem 6.1. -/
noncomputable def targetExp (η lam : ℝ) : ℝ :=
  11 / 12 + lam / 2 + 3 * η / 4

/-- **(E2)** Paper, Theorem 6.1, Step 3, the claim
"`Φ(U) ≪ D^{11/12}E^{1/2}H^{3/4}` for `2^{-9}D^{1/3} ≤ U ≤ 2D^{1/2}`", in exponent
form: for `1/3 ≤ a ≤ 1/2`, `0 ≤ η ≤ 1/6` (`H ≤ D^{1/6}`), `λ ≤ 1` (`E ≤ D`) and
`λ ≥ 2/3 + 2η` (`E ≥ D^{2/3}H^2`),
`(3/4)(1+η) + (3/8)λ + (max(λ,2a+2η) + max(λ,2-2a))/8 ≤ 11/12 + λ/2 + 3η/4`. -/
theorem phiExp_le_targetExp {a η lam : ℝ} (ha1 : 1 / 3 ≤ a) (ha2 : a ≤ 1 / 2)
    (_hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 6) (hl1 : lam ≤ 1) (hl2 : 2 / 3 + 2 * η ≤ lam) :
    phiExp a η lam ≤ targetExp η lam := by
  unfold phiExp targetExp
  rcases le_total lam (2 * a + 2 * η) with h1 | h1 <;>
    rcases le_total lam (2 - 2 * a) with h2 | h2 <;>
    simp only [max_eq_left, max_eq_right, h1, h2] <;> linarith

/-- The same inequality with the four constraints made explicit: the claim of
Step 3 holds iff all four linear inequalities below hold (this is the
"four cases" of the paper). -/
theorem phiExp_le_targetExp_iff (a η lam : ℝ) :
    phiExp a η lam ≤ targetExp η lam ↔
      (lam ≤ 4 / 3 ∧ 1 / 3 ≤ a ∧ a + η ≤ 2 / 3 ∧ 2 / 3 + 2 * η ≤ lam) := by
  unfold phiExp targetExp
  constructor
  · intro h
    have e1 := le_max_left lam (2 * a + 2 * η)
    have e2 := le_max_right lam (2 * a + 2 * η)
    have e3 := le_max_left lam (2 - 2 * a)
    have e4 := le_max_right lam (2 - 2 * a)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨h1, h2, h3, h4⟩
    rcases le_total lam (2 * a + 2 * η) with k1 | k1 <;>
      rcases le_total lam (2 - 2 * a) with k2 | k2 <;>
      simp only [max_eq_left, max_eq_right, k1, k2] <;> linarith

/-- **(E2), case 1** (paper, Step 3, item 1): if `(UH)^2 ≤ E ≤ W^2`, i.e.
`2a+2η ≤ λ ≤ 2-2a`, then `Φ ≍ (DH)^{3/4} E^{1/2} W^{1/4}`, and this is
`≤ D^{11/12}E^{1/2}H^{3/4}` because `W ≪ D^{2/3}` (`1-a ≤ 2/3`). -/
theorem case1 {a η lam : ℝ} (h1 : 2 * a + 2 * η ≤ lam) (h2 : lam ≤ 2 - 2 * a) :
    phiExp a η lam = 3 / 4 * (1 + η) + lam / 2 + (1 - a) / 4 ∧
    (1 - a ≤ 2 / 3 → 3 / 4 * (1 + η) + lam / 2 + (1 - a) / 4 ≤ targetExp η lam) := by
  refine ⟨?_, fun hW => ?_⟩
  · unfold phiExp
    rw [max_eq_left h1, max_eq_right h2]
    ring
  · unfold targetExp
    linarith

/-- **(E2), case 2** (paper, Step 3, item 2): if `E < (UH)^2` and `E ≤ W^2`, then
`Φ ≍ (DH)^{3/4}E^{3/8}(DH)^{1/4} = DHE^{3/8}`, and this is
`≤ D^{11/12}E^{1/2}H^{3/4}` *exactly when* `E ≥ D^{2/3}H^2`. -/
theorem case2 {a η lam : ℝ} (h1 : lam < 2 * a + 2 * η) (h2 : lam ≤ 2 - 2 * a) :
    phiExp a η lam = 1 + η + 3 / 8 * lam ∧
    (1 + η + 3 / 8 * lam ≤ targetExp η lam ↔ 2 / 3 + 2 * η ≤ lam) := by
  refine ⟨?_, ?_⟩
  · unfold phiExp
    rw [max_eq_right h1.le, max_eq_right h2]
    ring
  · unfold targetExp
    constructor <;> intro h <;> linarith

/-- **(E2), case 3** (paper, Step 3, item 3): if `E < (UH)^2` and `E > W^2`, then
`Φ ≍ (DH)^{3/4}E^{1/2}(UH)^{1/4} ≪ D^{7/8}HE^{1/2}` (using `U ≪ D^{1/2}`), and
`D^{7/8}HE^{1/2} ≤ D^{11/12}E^{1/2}H^{3/4}` iff `H ≤ D^{1/6}`. -/
theorem case3 {a η lam : ℝ} (h1 : lam < 2 * a + 2 * η) (h2 : 2 - 2 * a < lam) :
    phiExp a η lam = 3 / 4 * (1 + η) + lam / 2 + (a + η) / 4 ∧
    (a ≤ 1 / 2 → 3 / 4 * (1 + η) + lam / 2 + (a + η) / 4 ≤ 7 / 8 + η + lam / 2) ∧
    (7 / 8 + η + lam / 2 ≤ targetExp η lam ↔ η ≤ 1 / 6) := by
  refine ⟨?_, fun ha => by linarith, ?_⟩
  · unfold phiExp
    rw [max_eq_right h1.le, max_eq_left h2.le]
    ring
  · unfold targetExp
    constructor <;> intro h <;> linarith

/-- **(E2), case 4** (paper, Step 3, item 4): if `(UH)^2 ≤ E` and `E > W^2`, then
`Φ ≍ (DH)^{3/4}E^{5/8}`, and this is `≤ D^{11/12}E^{1/2}H^{3/4}` iff
`E ≤ D^{4/3}`; in particular it holds since `E ≤ D`. -/
theorem case4 {a η lam : ℝ} (h1 : 2 * a + 2 * η ≤ lam) (h2 : 2 - 2 * a < lam) :
    phiExp a η lam = 3 / 4 * (1 + η) + 5 / 8 * lam ∧
    (3 / 4 * (1 + η) + 5 / 8 * lam ≤ targetExp η lam ↔ lam ≤ 4 / 3) := by
  refine ⟨?_, ?_⟩
  · unfold phiExp
    rw [max_eq_left h1, max_eq_left h2.le]
    ring
  · unfold targetExp
    constructor <;> intro h <;> linarith

/-- Remark on Step 3: in exponent form cases 3 and 4 (`E > W^2`) cannot occur
when `U ≤ D^{1/2}` and `E ≤ D`, since then `W^2 ≥ D ≥ E`.  (In the paper they
are treated anyway because of the constants `2^{±9}`; harmless.) -/
theorem cases34_vacuous {a lam : ℝ} (ha : a ≤ 1 / 2) (hl : lam ≤ 1) :
    ¬ (2 - 2 * a < lam) := by
  intro h; linarith

/-- Paper, Theorem 6.1, Step 3: "`M' ≤ U'` because `H ≤ D^{1/6} < 2^{-9}D^{1/3} ≤ U`"
(exponent form, the constant `2^{-9}` being absorbed for large `D`): `1/6 < 1/3`,
and `η ≤ 1/6 < 1/3 ≤ a`. -/
theorem freq_lt_short_factor {a η : ℝ} (hη : η ≤ 1 / 6) (ha : 1 / 3 ≤ a) : η < a := by
  linarith

/-- Paper, Theorem 6.1, Step 3: the gcd powers.  With `U'M' = UH/(g g'^2)` and
`Q = E/g`, the factor `(U'M')^{3/4} Q^{3/8} (Q+(U'M')^2)^{1/8}` carries
`g^{-3/4} g^{-3/8} g^{-1/8} = g^{-5/4}` and `g'^{-3/2}` (exponent bookkeeping). -/
theorem gcd_powers : (-(3 : ℝ) / 4 - 3 / 8 - 1 / 8 = -5 / 4) ∧ ((3 : ℝ) / 4 * (-2) = -3 / 2) := by
  norm_num

/-- Paper, Proposition 5.1 (Hölder step) and Theorem 6.1, Step 3: the norms
`Γ ≪ (U'M')^{1/2}`, `B ≪ W^{1/2}` combine with `(U'M')^{1/4}W^{1/4}` to the power
`(U'M'W)^{3/4}`, and Hölder with exponents `(4,4,2)` is admissible
(`1/4 + 1/4 + 1/2 = 1`); `(2Q)^{1/4} Q^{1/2}` comes from `q ≤ 2Q` and `#q ≤ Q`. -/
theorem holder_bookkeeping :
    ((1 : ℝ) / 2 + 1 / 4 = 3 / 4) ∧ ((1 : ℝ) / 4 + 1 / 4 + 1 / 2 = 1) ∧
    ((1 : ℝ) / 4 + 1 / 2 = 3 / 4) ∧ ((3 : ℝ) / 4 / 2 = 3 / 8) := by
  norm_num

/-- Genuine (multiplicative) form of the key estimate in Step 3, avoiding `rpow`:
put `L = D^{4/3}` (so `L^3 = D^4`).  If `1 ≤ H`, `H^6 ≤ D` (`H ≤ D^{1/6}`),
`D^2 H^6 ≤ E^3` (`E ≥ D^{2/3}H^2`), `0 < E ≤ D`, `D ≤ U^3` (`U ≥ D^{1/3}`),
`U^2 ≤ D` (`U ≤ D^{1/2}`) and `UW = D`, then
`(E + (UH)^2)(E + W^2) ≤ 4 D^{4/3} E`, whence
`Φ(U) ≤ 4^{1/8} D^{11/12} E^{1/2} H^{3/4}`. -/
theorem balanced_product_bound {D E H U W L : ℝ} (hH : 1 ≤ H) (hE : 0 < E) (hU : 0 < U)
    (hW : 0 < W) (hL : 0 < L) (hL3 : L ^ 3 = D ^ 4)
    (hHD : H ^ 6 ≤ D) (hEl : D ^ 2 * H ^ 6 ≤ E ^ 3) (hEu : E ≤ D) (hUl : D ≤ U ^ 3)
    (hUu : U ^ 2 ≤ D) (hUW : U * W = D) :
    (E + (U * H) ^ 2) * (E + W ^ 2) ≤ 4 * L * E := by
  have hD1 : 1 ≤ D := le_trans (one_le_pow₀ hH) hHD
  have hD0 : 0 < D := by linarith
  -- cube comparison: for nonnegative a, b, a^3 ≤ b^3 → a ≤ b
  have cube : ∀ {s t : ℝ}, 0 ≤ s → 0 ≤ t → s ^ 3 ≤ t ^ 3 → s ≤ t := fun hs ht h =>
    le_of_pow_le_pow_left₀ (by norm_num) ht h
  -- E ≤ L
  have h1 : E ≤ L := by
    apply cube hE.le hL.le
    rw [hL3]
    calc E ^ 3 ≤ D ^ 3 := pow_le_pow_left₀ hE.le hEu 3
      _ ≤ D ^ 4 := pow_le_pow_right₀ hD1 (by norm_num)
  -- W^2 ≤ L
  have h2 : W ^ 2 ≤ L := by
    apply cube (by positivity) hL.le
    rw [hL3]
    have : (W ^ 2) ^ 3 * D ^ 2 ≤ D ^ 4 * (U ^ 6) * 0 + D ^ 4 * D ^ 2 := by
      have e : (W ^ 2) ^ 3 * U ^ 6 = D ^ 6 := by rw [← hUW]; ring
      have hU6 : D ^ 2 ≤ U ^ 6 := by
        have := pow_le_pow_left₀ hD0.le hUl 2
        calc D ^ 2 ≤ (U ^ 3) ^ 2 := this
          _ = U ^ 6 := by ring
      have hw : 0 ≤ (W ^ 2) ^ 3 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hU6 hw]
    have hD2 : 0 < D ^ 2 := by positivity
    nlinarith
  -- (U H)^2 ≤ L
  have h3 : (U * H) ^ 2 ≤ L := by
    apply cube (by positivity) hL.le
    rw [hL3]
    have hU6 : U ^ 6 ≤ D ^ 3 := by
      have := pow_le_pow_left₀ (by positivity) hUu 3
      calc U ^ 6 = (U ^ 2) ^ 3 := by ring
        _ ≤ D ^ 3 := this
    calc ((U * H) ^ 2) ^ 3 = U ^ 6 * H ^ 6 := by ring
      _ ≤ D ^ 3 * D := mul_le_mul hU6 hHD (by positivity) (by positivity)
      _ = D ^ 4 := by ring
  -- (UH)^2 W^2 = (DH)^2 ≤ L E
  have h4 : (U * H) ^ 2 * W ^ 2 ≤ L * E := by
    have e : (U * H) ^ 2 * W ^ 2 = D ^ 2 * H ^ 2 := by rw [← hUW]; ring
    rw [e]
    apply cube (by positivity) (by positivity)
    calc (D ^ 2 * H ^ 2) ^ 3 = D ^ 4 * (D ^ 2 * H ^ 6) := by ring
      _ ≤ D ^ 4 * E ^ 3 := mul_le_mul_of_nonneg_left hEl (by positivity)
      _ = (L * E) ^ 3 := by rw [mul_pow, hL3]
  have hE2 : E * E ≤ L * E := mul_le_mul_of_nonneg_right h1 hE.le
  have hEW : E * W ^ 2 ≤ L * E := by nlinarith
  have hUE : (U * H) ^ 2 * E ≤ L * E := mul_le_mul_of_nonneg_right h3 hE.le
  nlinarith

/-- **(E2)**, genuine real-power form of the claim of Theorem 6.1, Step 3:
if `1 ≤ H ≤ D^{1/6}`, `D^{2/3}H^2 ≤ E ≤ D`, `E > 0`, and `D^{1/3} ≤ U ≤ D^{1/2}`,
then with `W = D/U`,
`Φ(U) = (DH)^{3/4}E^{3/8}{(E+(UH)^2)(E+W^2)}^{1/8} ≤ 4^{1/8} D^{11/12}E^{1/2}H^{3/4}`. -/
theorem phi_le_target_rpow {D E H U : ℝ} (hH : 1 ≤ H) (hE : 0 < E) (hU : 0 < U)
    (hHD : H ≤ D ^ ((1 : ℝ) / 6)) (hEl : D ^ ((2 : ℝ) / 3) * H ^ 2 ≤ E) (hEu : E ≤ D)
    (hUl : D ^ ((1 : ℝ) / 3) ≤ U) (hUu : U ≤ D ^ ((1 : ℝ) / 2)) :
    (D * H) ^ ((3 : ℝ) / 4) * E ^ ((3 : ℝ) / 8) *
        ((E + (U * H) ^ 2) * (E + (D / U) ^ 2)) ^ ((1 : ℝ) / 8)
      ≤ (4 : ℝ) ^ ((1 : ℝ) / 8) * D ^ ((11 : ℝ) / 12) * E ^ ((1 : ℝ) / 2) *
          H ^ ((3 : ℝ) / 4) := by
  have hD : 0 < D := lt_of_lt_of_le hE hEu
  have hH0 : 0 < H := by linarith
  have pw : ∀ (a : ℝ) (n : ℕ), (D ^ a) ^ n = D ^ (a * n) := fun a n =>
    (Real.rpow_mul_natCast hD.le a n).symm
  -- polynomial forms of the hypotheses
  have p1 : H ^ 6 ≤ D := by
    have := pow_le_pow_left₀ hH0.le hHD 6
    rwa [pw, show (1 : ℝ) / 6 * ((6 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one] at this
  have p2 : D ^ 2 * H ^ 6 ≤ E ^ 3 := by
    have := pow_le_pow_left₀ (by positivity) hEl 3
    rwa [mul_pow, pw, show (2 : ℝ) / 3 * ((3 : ℕ) : ℝ) = (2 : ℕ) by norm_num,
      Real.rpow_natCast, ← pow_mul] at this
  have p3 : D ≤ U ^ 3 := by
    have := pow_le_pow_left₀ (by positivity) hUl 3
    rwa [pw, show (1 : ℝ) / 3 * ((3 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one] at this
  have p4 : U ^ 2 ≤ D := by
    have := pow_le_pow_left₀ hU.le hUu 2
    rwa [pw, show (1 : ℝ) / 2 * ((2 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one] at this
  set L := D ^ ((4 : ℝ) / 3) with hLdef
  have hL : 0 < L := by positivity
  have hL3 : L ^ 3 = D ^ 4 := by
    rw [hLdef, pw, show (4 : ℝ) / 3 * ((3 : ℕ) : ℝ) = (4 : ℕ) by norm_num, Real.rpow_natCast]
  have hW : 0 < D / U := by positivity
  have hUW : U * (D / U) = D := by field_simp
  have key := balanced_product_bound hH hE hU hW hL hL3 p1 p2 hEu p3 p4 hUW
  have hY : 0 ≤ (E + (U * H) ^ 2) * (E + (D / U) ^ 2) := by positivity
  have step : ((E + (U * H) ^ 2) * (E + (D / U) ^ 2)) ^ ((1 : ℝ) / 8)
      ≤ (4 * L * E) ^ ((1 : ℝ) / 8) := Real.rpow_le_rpow hY key (by norm_num)
  have e1 : (4 * L * E) ^ ((1 : ℝ) / 8)
      = (4 : ℝ) ^ ((1 : ℝ) / 8) * D ^ ((1 : ℝ) / 6) * E ^ ((1 : ℝ) / 8) := by
    rw [Real.mul_rpow (by positivity) hE.le, Real.mul_rpow (by norm_num) hL.le, hLdef,
      ← Real.rpow_mul hD.le]
    norm_num
  have e2 : (D * H) ^ ((3 : ℝ) / 4) = D ^ ((3 : ℝ) / 4) * H ^ ((3 : ℝ) / 4) :=
    Real.mul_rpow hD.le hH0.le
  have hA : 0 ≤ (D * H) ^ ((3 : ℝ) / 4) * E ^ ((3 : ℝ) / 8) := by positivity
  calc (D * H) ^ ((3 : ℝ) / 4) * E ^ ((3 : ℝ) / 8) *
        ((E + (U * H) ^ 2) * (E + (D / U) ^ 2)) ^ ((1 : ℝ) / 8)
      ≤ (D * H) ^ ((3 : ℝ) / 4) * E ^ ((3 : ℝ) / 8) * (4 * L * E) ^ ((1 : ℝ) / 8) :=
        mul_le_mul_of_nonneg_left step hA
    _ = (4 : ℝ) ^ ((1 : ℝ) / 8) * (D ^ ((3 : ℝ) / 4) * D ^ ((1 : ℝ) / 6)) *
          (E ^ ((3 : ℝ) / 8) * E ^ ((1 : ℝ) / 8)) * H ^ ((3 : ℝ) / 4) := by
        rw [e1, e2]; ring
    _ = (4 : ℝ) ^ ((1 : ℝ) / 8) * D ^ ((11 : ℝ) / 12) * E ^ ((1 : ℝ) / 2) *
          H ^ ((3 : ℝ) / 4) := by
        rw [← Real.rpow_add hD, ← Real.rpow_add hE]
        norm_num

/-! ## E3. Long boxes and the boundary of the method -/

/-- **(E3)** Paper, Theorem 6.1 Step 4 / Section 7.5: the long-box term
`D^{1/3}EH` beats the Cauchy–Schwarz target `DE^{1/2}` (in base `D`:
`1/3 + λ + η < 1 + λ/2`, i.e. `λ/2 + η < 2/3`) whenever `λ ≤ 1` and `η < 1/9`. -/
theorem long_box {lam η : ℝ} (hl : lam ≤ 1) (hη : η < 1 / 9) : lam / 2 + η < 2 / 3 := by
  linarith

/-- **(E3)**, exponent-comparison form: `1/3 + λ + η < 1 + λ/2` (the term
`D^{1/3}EH`) and `1 + η < 1 + λ/2` (the term `DH`, using `λ ≥ 2/3 + 2η`). -/
theorem long_box_terms {lam η : ℝ} (hl : lam ≤ 1) (hη : η < 1 / 9)
    (hl2 : 2 / 3 + 2 * η ≤ lam) :
    1 / 3 + lam + η < 1 + lam / 2 ∧ 1 + η < 1 + lam / 2 := by
  constructor <;> linarith

/-- Paper, Section 8.1 ("The boundary of the method"): the balanced bound
`D^{11/12}E^{1/2}H^{3/4}` beats the target `DE^{1/2}` precisely when
`H < D^{1/9}`. -/
theorem balanced_beats_target_iff (lam η : ℝ) :
    targetExp η lam < 1 + lam / 2 ↔ η < 1 / 9 := by
  unfold targetExp
  constructor <;> intro h <;> linarith

/-- Paper, Section 8.1: the bottleneck is case 1 at `U ≍ D^{1/3}`: the case-1
exponent `(3/4)(1+η) + λ/2 + (1-a)/4` is decreasing in `a`, maximal at `a = 1/3`,
where it equals the target. -/
theorem case1_bottleneck (η lam : ℝ) {a : ℝ} (ha : 1 / 3 ≤ a) :
    3 / 4 * (1 + η) + lam / 2 + (1 - a) / 4 ≤ 3 / 4 * (1 + η) + lam / 2 + (1 - 1 / 3) / 4 ∧
    3 / 4 * (1 + η) + lam / 2 + (1 - 1 / 3) / 4 = targetExp η lam := by
  unfold targetExp
  constructor
  · linarith
  · ring

/-- Paper, Section 7.5: "On `K` we have `ϑ ≤ 1/9 - η` and `λ ≥ 1 - ϑ`.  Hence
`4X^ε T ≤ D^{1/6}`, and `E ≥ D^{2/3}(4X^εT)^2`, because
`λ - 2/3 - 2ϑ ≥ 1/3 - 3ϑ ≥ 3η`."  Here `η > 0` is the margin; the first
conclusion has margin `1/6 - ϑ ≥ 1/18 + η`. -/
theorem meanvalue_hypotheses {lam ϑ η : ℝ} (hϑ : ϑ ≤ 1 / 9 - η) (hl : 1 - ϑ ≤ lam) :
    ϑ + (1 / 18 + η) ≤ 1 / 6 ∧ lam - 2 / 3 - 2 * ϑ ≥ 1 / 3 - 3 * ϑ ∧
      1 / 3 - 3 * ϑ ≥ 3 * η := by
  refine ⟨?_, ?_, ?_⟩ <;> linarith

/-! ## E4. Savings in powers of `X` (Section 7.5) -/

/-- **(E4)**, first saving (paper, Section 7.5): with `D = X^{1-x}` and
`T = X^{1-x-y}`, the `X`-exponent of `D^{-1/12}T^{3/4}` is `-(8x+9y-8)/12 = -σ`. -/
theorem saving1_exp (x y : ℝ) :
    -(1 - x) / 12 + 3 / 4 * (1 - x - y) = -(8 * x + 9 * y - 8) / 12 := by ring

/-- **(E4)**, second saving: the `X`-exponent of `D^{-2/3}E^{1/2}T` is
`-(2x+9y-5)/6`. -/
theorem saving2_exp (x y : ℝ) :
    -(2 / 3) * (1 - x) + (1 - y) / 2 + (1 - x - y) = -(2 * x + 9 * y - 5) / 6 := by ring

/-- **(E4)**, third saving: the `X`-exponent of `E^{-1/2}T` is `-(2x+y-1)/2`. -/
theorem saving3_exp (x y : ℝ) :
    -(1 - y) / 2 + (1 - x - y) = -(2 * x + y - 1) / 2 := by ring

/-- **(E4)**, the three products (paper, Section 7.5: "Indeed,
`AE^{-1/2}·D^{11/12}E^{1/2}T^{3/4} = X·D^{-1/12}T^{3/4}`, and similarly for the
other two terms"), in `X`-exponents with `A = X^x`: the prefactor `AE^{-1/2}`
times the three terms of Theorem 6.1 (at `H = T`) gives `X^{1-σ}`,
`X^{1-(2x+9y-5)/6}`, `X^{1-(2x+y-1)/2}`. -/
theorem savings_products (x y : ℝ) :
    x - (1 - y) / 2 + (11 / 12 * (1 - x) + (1 - y) / 2 + 3 / 4 * (1 - x - y))
      = 1 - (8 * x + 9 * y - 8) / 12 ∧
    x - (1 - y) / 2 + ((1 - x) / 3 + (1 - y) + (1 - x - y))
      = 1 - (2 * x + 9 * y - 5) / 6 ∧
    x - (1 - y) / 2 + ((1 - x) + (1 - x - y))
      = 1 - (2 * x + y - 1) / 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> ring

/-- **(E4)**, the same in genuine powers: for `X > 0`, with `A = X^x`,
`D = X^{1-x}`, `E = X^{1-y}`, `T = X^{1-x-y}`,
`A·E^{-1/2}·D^{11/12}E^{1/2}T^{3/4} = X·X^{-(8x+9y-8)/12}` and
`D^{-1/12}T^{3/4} = X^{-(8x+9y-8)/12}`. -/
theorem savings_rpow {X : ℝ} (hX : 0 < X) (x y : ℝ) :
    (X ^ (1 - x)) ^ (-(1 : ℝ) / 12) * (X ^ (1 - x - y)) ^ ((3 : ℝ) / 4)
        = X ^ (-(8 * x + 9 * y - 8) / 12) ∧
    (X ^ (1 - x)) ^ (-(2 : ℝ) / 3) * (X ^ (1 - y)) ^ ((1 : ℝ) / 2) * X ^ (1 - x - y)
        = X ^ (-(2 * x + 9 * y - 5) / 6) ∧
    (X ^ (1 - y)) ^ (-(1 : ℝ) / 2) * X ^ (1 - x - y) = X ^ (-(2 * x + y - 1) / 2) ∧
    X ^ x * (X ^ (1 - y)) ^ (-(1 : ℝ) / 2) *
        ((X ^ (1 - x)) ^ ((11 : ℝ) / 12) * (X ^ (1 - y)) ^ ((1 : ℝ) / 2) *
          (X ^ (1 - x - y)) ^ ((3 : ℝ) / 4))
        = X * X ^ (-(8 * x + 9 * y - 8) / 12) := by
  simp only [← Real.rpow_mul hX.le, ← Real.rpow_add hX]
  refine ⟨?_, ?_, ?_, ?_⟩
  · congr 1; ring
  · congr 1; ring
  · congr 1; ring
  · rw [show X * X ^ (-(8 * x + 9 * y - 8) / 12)
        = X ^ ((1 : ℝ) + -(8 * x + 9 * y - 8) / 12) by rw [Real.rpow_add hX, Real.rpow_one]]
    congr 1; ring

/-- **(E4)**, comparison of savings (paper, Section 7.5): for `7/16 < x ≤ y ≤ 1/2`
the second and third savings are at least `σ = (8x+9y-8)/12`; indeed the
differences are `(9y-4x-2)/12 ≥ (5x-2)/12 > 0` and `(4x-3y+2)/12 > 0`. -/
theorem savings_compare {x y : ℝ} (hx : 7 / 16 < x) (hxy : x ≤ y) (hy : y ≤ 1 / 2) :
    (2 * x + 9 * y - 5) / 6 - (8 * x + 9 * y - 8) / 12 = (9 * y - 4 * x - 2) / 12 ∧
    (9 * y - 4 * x - 2) / 12 ≥ (5 * x - 2) / 12 ∧ (5 * x - 2) / 12 > 0 ∧
    (2 * x + y - 1) / 2 - (8 * x + 9 * y - 8) / 12 = (4 * x - 3 * y + 2) / 12 ∧
    (4 * x - 3 * y + 2) / 12 > 0 ∧
    (2 * x + 9 * y - 5) / 6 ≥ (8 * x + 9 * y - 8) / 12 ∧
    (2 * x + y - 1) / 2 ≥ (8 * x + 9 * y - 8) / 12 := by
  refine ⟨by ring, by linarith, by linarith, by ring, by linarith, by linarith, by linarith⟩

/-- Paper, Section 7.4: the frequency truncation.  `hA/(2e) ≥ X^εTA/(4E) = X^ε/4`
for `|h| > X^εT`, `e ≤ 2E`, because `TA = E` (`X`-exponents:
`(1-x-y) + x = 1-y`); and `T/(DE) = X^{-1}`. -/
theorem truncation_exps (x y : ℝ) :
    (1 - x - y) + x = 1 - y ∧ (1 - x - y) - (1 - x) - (1 - y) = -1 := by
  constructor <;> ring

/-- Paper, Section 7.3: `AD = X` and `D ≥ √X` (as `x ≤ 1/2`), so
`AD exp(-c√log D) ≤ X exp(-c √(log X / 2))`: exponent form `x + (1-x) = 1`,
`1 - x ≥ 1/2`. -/
theorem zero_freq_exps {x : ℝ} (hx : x ≤ 1 / 2) : x + (1 - x) = 1 ∧ 1 / 2 ≤ 1 - x := by
  constructor
  · ring
  · linarith

/-! ## E5. The region `Ω` -/

/-- **(E5)** Paper, Section 1.1: "Since `M ≤ 1/2`, every point of `Ω` has
`m > 7/16`." -/
theorem omega_min_gt {m M : ℝ} (hM : M ≤ 1 / 2) (h : 8 * m + 9 * M > 8) : m > 7 / 16 := by
  linarith

/-- **(E5)** Paper, Remark 1.3: the endpoints `(7/16, 1/2)` and `(8/17, 8/17)` lie on
the line `8m + 9M = 8`. -/
theorem boundary_endpoints :
    8 * (7 / 16 : ℝ) + 9 * (1 / 2) = 8 ∧ 8 * (8 / 17 : ℝ) + 9 * (8 / 17) = 8 := by
  norm_num

/-- **(E5)** Paper, Remark 1.3: "The boundary of `Ω` inside the ordered
half-square is the segment from `(7/16,1/2)` to `(8/17,8/17)`": a point with
`m ≤ M ≤ 1/2` lies on `8m+9M = 8` iff it is `(m, (8-8m)/9)` with
`7/16 ≤ m ≤ 8/17`. -/
theorem boundary_segment (m M : ℝ) :
    (m ≤ M ∧ M ≤ 1 / 2 ∧ 8 * m + 9 * M = 8) ↔
      (7 / 16 ≤ m ∧ m ≤ 8 / 17 ∧ M = (8 - 8 * m) / 9) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3⟩
    subst h3
    refine ⟨by linarith, by linarith, by linarith⟩

/-- **(E5)** The largest value of `m + M` on the complement of `Ω` within
`0 < m ≤ M ≤ 1/2` is `16/17`, attained at `(8/17, 8/17)`.  (Proof:
`m + M = (8m+9M)/9 + m/9 ≤ 8/9 + (8/17)/9`, as `17m ≤ 8m+9M ≤ 8`.)  Equivalently
the shortest Poisson dual length outside `Ω` is `T = X^{1/17}`. -/
theorem complement_max_sum :
    IsGreatest {s : ℝ | ∃ m M : ℝ, 0 < m ∧ m ≤ M ∧ M ≤ 1 / 2 ∧ 8 * m + 9 * M ≤ 8 ∧ s = m + M}
      (16 / 17) := by
  constructor
  · exact ⟨8 / 17, 8 / 17, by norm_num, le_rfl, by norm_num, by norm_num, by norm_num⟩
  · rintro s ⟨m, M, _h0, h1, _h2, h3, rfl⟩
    linarith

/-! ## E6. Comparison with Bettin–Chandee (Remark 1.3) -/

/-- `X`-exponent, minus `1`, of the contribution of one dyadic frequency block
`H = T` when a term `A₀^α M^β N^γ` of the Bettin–Chandee bound is inserted into
the Poisson reduction: prefactor `A/E`, coefficient norms
`‖ν‖‖α‖‖β‖ = (HDE)^{1/2}`, and `(A₀, M, N) = (H, D, E) = (T, D, E)`. -/
noncomputable def bcExp (α β γ x y : ℝ) : ℝ :=
  (x - (1 - y)) + ((1 - x - y) + (1 - x) + (1 - y)) / 2 +
    (α * (1 - x - y) + β * (1 - x) + γ * (1 - y)) - 1

/-- The Poisson prefactor and the coefficient norms combine to exactly `X^{1/2}`:
`(A/E)(TDE)^{1/2} = X^{1/2}`. -/
theorem bc_prefactor (x y : ℝ) :
    (x - (1 - y)) + ((1 - x - y) + (1 - x) + (1 - y)) / 2 = 1 / 2 := by ring

/-- **(E6a)** The term `A₀^{1/2}M^{1/2}N^{3/8}` gives the power `X·H·E^{-1/8}`,
with exponent `t - e₀/8 = (7-8x-7y)/8`; it is negative iff `8x+7y > 7`. -/
theorem bc_term_a (x y : ℝ) :
    bcExp (1 / 2) (1 / 2) (3 / 8) x y = (1 - x - y) - (1 - y) / 8 ∧
    bcExp (1 / 2) (1 / 2) (3 / 8) x y = (7 - 8 * x - 7 * y) / 8 ∧
    (bcExp (1 / 2) (1 / 2) (3 / 8) x y < 0 ↔ 8 * x + 7 * y > 7) := by
  unfold bcExp
  refine ⟨by ring, by ring, ?_⟩
  constructor <;> intro h <;> linarith

/-- **(E6b)** The term `A₀^{1/2}N^{7/8}` gives `X·H·D^{-1/2}E^{3/8}`, with exponent
`t + 3e₀/8 - d₀/2 = (7-4x-11y)/8`; negative iff `4x+11y > 7`. -/
theorem bc_term_b (x y : ℝ) :
    bcExp (1 / 2) 0 (7 / 8) x y = (1 - x - y) + 3 * (1 - y) / 8 - (1 - x) / 2 ∧
    bcExp (1 / 2) 0 (7 / 8) x y = (7 - 4 * x - 11 * y) / 8 ∧
    (bcExp (1 / 2) 0 (7 / 8) x y < 0 ↔ 4 * x + 11 * y > 7) := by
  unfold bcExp
  refine ⟨by ring, by ring, ?_⟩
  constructor <;> intro h <;> linarith

/-- **(E6c)** The term `A₀^{1/5}M^{3/5}N^{7/20}` gives `X·H^{7/10}D^{1/10}E^{-3/20}`,
with exponent `7t/10 + d₀/10 - 3e₀/20 = (13-16x-11y)/20`; negative iff
`16x+11y > 13`. -/
theorem bc_term_c (x y : ℝ) :
    bcExp (1 / 5) (3 / 5) (7 / 20) x y
      = 7 * (1 - x - y) / 10 + (1 - x) / 10 - 3 * (1 - y) / 20 ∧
    bcExp (1 / 5) (3 / 5) (7 / 20) x y = (13 - 16 * x - 11 * y) / 20 ∧
    (bcExp (1 / 5) (3 / 5) (7 / 20) x y < 0 ↔ 16 * x + 11 * y > 13) := by
  unfold bcExp
  refine ⟨by ring, by ring, ?_⟩
  constructor <;> intro h <;> linarith

/-- **(E6d)** The term `A₀^{7/20}M^{3/10}N^{13/20}` gives
`X·H^{17/20}D^{-1/5}E^{3/20}`, with exponent
`17t/20 - d₀/5 + 3e₀/20 = (16-13x-20y)/20`; negative iff `13x+20y > 16`. -/
theorem bc_term_d (x y : ℝ) :
    bcExp (7 / 20) (3 / 10) (13 / 20) x y
      = 17 * (1 - x - y) / 20 - (1 - x) / 5 + 3 * (1 - y) / 20 ∧
    bcExp (7 / 20) (3 / 10) (13 / 20) x y = (16 - 13 * x - 20 * y) / 20 ∧
    (bcExp (7 / 20) (3 / 10) (13 / 20) x y < 0 ↔ 13 * x + 20 * y > 16) := by
  unfold bcExp
  refine ⟨by ring, by ring, ?_⟩
  constructor <;> intro h <;> linarith

/-- Side conditions of the Bettin–Chandee bound in the hard square: the factor
`(1 + |ϑ|A₀/(MN))` is harmless because `T/(DE) = X^{-1}`, and `M ≪ N^2`
(`D ≪ E^2`, i.e. `2y - x ≤ 1`) holds for `0 ≤ x ≤ y ≤ 1/2`. -/
theorem bc_side_conditions {x y : ℝ} (hx : 0 ≤ x) (hy : y ≤ 1 / 2) :
    (1 - x - y) - (1 - x) - (1 - y) = -1 ∧ 1 - x ≤ 2 * (1 - y) := by
  constructor
  · ring
  · linarith

/-- **(E6)** Within `x ≤ 1/2` (in particular within `0 < x ≤ y ≤ 1/2`) the first two
Bettin–Chandee conditions follow from the third: `16x+11y > 13` forces `y > 5/11`,
and then `8x+7y = (16x+11y)/2 + 3y/2 > 7`, `4x+11y = (16x+11y)/4 + 33y/4 > 7`. -/
theorem bc_ab_of_c {x y : ℝ} (hx : x ≤ 1 / 2) (hc : 16 * x + 11 * y > 13) :
    y > 5 / 11 ∧ 8 * x + 7 * y > 7 ∧ 4 * x + 11 * y > 7 := by
  refine ⟨by linarith, by linarith, by linarith⟩

/-- **(E6)** Paper, Remark 1.3: the identity
`8m + 9M = (43/177)(16m+11M) + (56/177)(13m+20M)`. -/
theorem bc_combination (m M : ℝ) :
    8 * m + 9 * M = 43 / 177 * (16 * m + 11 * M) + 56 / 177 * (13 * m + 20 * M) := by ring

/-- **(E6)** Paper, Remark 1.3: `43·13 + 56·16 = 1455`, `8·177 = 1416 < 1455`, and
`(43/177)·13 + (56/177)·16 = 1455/177 > 8`. -/
theorem bc_combination_numbers :
    43 * 13 + 56 * 16 = (1455 : ℕ) ∧ 8 * 177 = (1416 : ℕ) ∧ 1416 < (1455 : ℕ) ∧
    (43 / 177 : ℝ) * 13 + 56 / 177 * 16 = 1455 / 177 ∧ (1455 / 177 : ℝ) > 8 := by
  norm_num

/-- **(E6)** Paper, Remark 1.3: the Bettin–Chandee region is contained in `Ω`:
`16m+11M > 13` and `13m+20M > 16` imply `8m+9M > 1455/177 > 8`. -/
theorem bc_region_subset {m M : ℝ} (h1 : 16 * m + 11 * M > 13) (h2 : 13 * m + 20 * M > 16) :
    8 * m + 9 * M > 1455 / 177 ∧ 8 * m + 9 * M > 8 := by
  have := bc_combination m M
  constructor <;> linarith

/-- **(E6)** The containment is strict: `(12/25, 12/25)` lies in `Ω` but not in the
Bettin–Chandee region. -/
theorem bc_region_strict :
    (8 * (12 / 25 : ℝ) + 9 * (12 / 25) > 8) ∧ (12 / 25 : ℝ) ≤ 1 / 2 ∧
    ¬ (13 * (12 / 25 : ℝ) + 20 * (12 / 25) > 16) := by
  norm_num

/-- **(E6)** Diagonal (paper, Remark 1.3 and Corollary 1.2): on `x = y` the
Bettin–Chandee conditions are equivalent to `x > 16/33` and `Ω` to `x > 8/17`. -/
theorem diagonal_thresholds (x : ℝ) :
    ((16 * x + 11 * x > 13 ∧ 13 * x + 20 * x > 16) ↔ x > 16 / 33) ∧
    (8 * x + 9 * x > 8 ↔ x > 8 / 17) := by
  refine ⟨⟨fun h => by linarith [h.2], fun h => ⟨by linarith, by linarith⟩⟩,
    ⟨fun h => by linarith, fun h => by linarith⟩⟩

/-- **(E6)** Numerology of the "dial" (paper, Sections 1.1–1.2):
`1 - 16/33 = 17/33`, `1 - 8/17 = 9/17`, `9/17 - 1/2 = 1/34`,
`17/33 - 1/2 = 1/66`, `48/95 - 1/2 = 1/190`, `1/34 > 1/66` with ratio `33/17`,
and `8/17 < 16/33` (our diagonal threshold is lower). -/
theorem dial_numbers :
    (1 : ℝ) - 16 / 33 = 17 / 33 ∧ (1 : ℝ) - 8 / 17 = 9 / 17 ∧
    (9 : ℝ) / 17 - 1 / 2 = 1 / 34 ∧ (17 : ℝ) / 33 - 1 / 2 = 1 / 66 ∧
    (48 : ℝ) / 95 - 1 / 2 = 1 / 190 ∧ (1 : ℝ) / 34 > 1 / 66 ∧
    ((1 : ℝ) / 34) / (1 / 66) = 33 / 17 ∧ (8 : ℝ) / 17 < 16 / 33 ∧
    (16 : ℝ) / 33 > 13 / 27 := by
  norm_num

/-! ## E7. Level-of-distribution exponent checks -/

/-- **(E7)** Level-of-distribution exponent checks (paper, Theorem 1.1 /
Corollary 1.2, used as `MobiusPairLevel θ` for `θ < 9/17` in `Basic.lean`): if
`8/17 + η ≤ x ≤ y` and `η > 0`, then
* `5x + 6y > 5`  (`H = T ≤ D^{1/6}`),
* `8x + 3y > 5`  (`E ≥ D^{2/3}H^2` at `H = T`),
* `8x + 9y - 8 ≥ 17η` (first saving `σ ≥ 17η/12 > 0`),
* `2x + 9y > 5`, `2x + y > 1` (positivity of the second and third savings). -/
theorem level_exponents {x y η : ℝ} (hη : 0 < η) (hx : 8 / 17 + η ≤ x) (hxy : x ≤ y) :
    5 * x + 6 * y > 5 ∧ 8 * x + 3 * y > 5 ∧ 8 * x + 9 * y - 8 ≥ 17 * η ∧
      2 * x + 9 * y > 5 ∧ 2 * x + y > 1 := by
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- **(E7)**, translation of the two hypotheses of Theorem 6.1 at `H = T`:
`T ≤ D^{1/6}` is `1-x-y ≤ (1-x)/6`, i.e. `5x+6y ≥ 5`, and `E ≥ D^{2/3}T^2` is
`1-y ≥ 2(1-x)/3 + 2(1-x-y)`, i.e. `8x+3y ≥ 5`. -/
theorem level_hypotheses_translation (x y : ℝ) :
    ((1 - x - y) ≤ (1 - x) / 6 ↔ 5 * x + 6 * y ≥ 5) ∧
    ((1 - y) ≥ 2 / 3 * (1 - x) + 2 * (1 - x - y) ↔ 8 * x + 3 * y ≥ 5) := by
  constructor <;> constructor <;> intro h <;> linarith

/-! ## Miscellaneous numerical facts -/

/-- Paper, proof of Lemma 2.5: `(1 - p^{-1/2})^{-1} ≤ exp(4 p^{-1/2})`; it suffices
that `1/(1-t) ≤ exp(4t)` for `0 ≤ t ≤ 3/4`, and `p^{-1/2} ≤ 2^{-1/2} < 3/4`. -/
theorem inv_one_sub_le_exp {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 3 / 4) :
    1 / (1 - t) ≤ Real.exp (4 * t) := by
  have hpos : 0 < 1 - t := by linarith
  rw [div_le_iff₀ hpos]
  have := Real.add_one_le_exp (4 * t)
  nlinarith

/-- `2^{-1/2} < 3/4` (so `p^{-1/2} ≤ 3/4` for all primes `p`). -/
theorem inv_sqrt_two_lt : 1 / Real.sqrt 2 < 3 / 4 := by
  have h : (4 : ℝ) / 3 < Real.sqrt 2 := by
    rw [show (4 : ℝ) / 3 = Real.sqrt ((4 / 3) ^ 2) by
      rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h2 : 0 < Real.sqrt 2 := by positivity
  rw [div_lt_iff₀ h2]
  linarith

/-- Paper, proof of Lemma 2.5 (Rankin's trick): for `k > √x`,
`x/k ≤ x^{3/4} k^{-1/2}`.  Written with `x = r^4`, `k = s^2` (`r, s > 0`), the
hypothesis `k ≥ √x` is `r ≤ s` and the claim is `r^4/s^2 ≤ r^3/s`. -/
theorem rankin_step {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (h : r ≤ s) :
    r ^ 4 / s ^ 2 ≤ r ^ 3 / s := by
  rw [div_le_div_iff₀ (by positivity) hs]
  have h3 : 0 ≤ r ^ 3 * s := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h h3]

/-- Paper, Theorem 6.1, Step 2: the dichotomy (B)/(L).  "If every atom size is
below `D^{1/3}`, the first partial product exceeding `D^{1/3}` is below
`D^{2/3}`": if finitely many atom log-sizes (base `D`), each `< 1/3`, have total
`≥ 1/3`, then some initial partial sum lies in `[1/3, 2/3)`. -/
theorem dichotomy_prefix (l : List ℝ) (hsmall : ∀ t ∈ l, t < 1 / 3)
    (htot : 1 / 3 ≤ l.sum) :
    ∃ k, 1 / 3 ≤ (l.take k).sum ∧ (l.take k).sum < 2 / 3 := by
  induction l using List.reverseRecOn with
  | nil => simp at htot; linarith
  | append_singleton l t ih =>
    have hsmall' : ∀ s ∈ l, s < 1 / 3 := fun s hs => hsmall s (List.mem_append_left _ hs)
    have ht : t < 1 / 3 := hsmall t (by simp)
    by_cases hl : 1 / 3 ≤ l.sum
    · obtain ⟨k, hk1, hk2⟩ := ih hsmall' hl
      refine ⟨min k l.length, ?_⟩
      rw [List.take_append_of_le_length (min_le_right _ _), ← List.take_take,
        List.take_length]
      exact ⟨hk1, hk2⟩
    · rw [not_le] at hl
      refine ⟨l.length + 1, ?_⟩
      simp only [List.sum_append, List.sum_singleton] at htot
      rw [List.take_of_length_le (by simp)]
      simp only [List.sum_append, List.sum_singleton]
      constructor <;> linarith

end Exponents

end MobiusDeterminant
