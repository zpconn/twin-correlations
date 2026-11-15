import Mathlib

/-!
# The CRT phase after Poisson summation (paper, Section 7.2)

For odd coprime `d, e` and `κ ∈ {2, -2}`, let `a₀` be the residue class modulo
`2e` with `a₀ ≡ -κ d̄ (mod e)` and `a₀ ≡ 1 (mod 2)`.  The paper uses

* (Section 7.2) the solutions of `be - ad = κ` in odd integers with given
  `d, e` are exactly `a ≡ a₀ (mod 2e)`, `b = (ad+κ)/e`, and `b` is then odd;
* (Section 7.2) `a₀/(2e) ≡ -(κ/2) d̄/e + 1/2 (mod 1)`, hence
  `e(h a₀/(2e)) = (-1)^h e_e(-(κ/2) h d̄)`;
* (Section 1.1) a common divisor of odd `d, e` with `be - ad = κ` divides `κ`,
  so `(d, e) = 1`.

Here `d'` is an integer inverse of `d` modulo `e` (`e ∣ d d' - 1`).  We also
record the "shift-1" (no parity) version: for any shift `κ` and modulus `e`,
`a₀ ≡ -κ d' (mod e)` gives `e(h a₀/e) = e(-κ h d'/e)`.
-/

namespace MobiusDeterminant

namespace CRT

open Complex

/-- Paper, Section 7.2, the CRT congruence `a₀/(2e) ≡ -(κ/2) d̄/e + 1/2 (mod 1)`,
multiplied by an arbitrary frequency `h`: for odd `e`, `κ ∈ {2,-2}`, `a₀` odd with
`a₀ ≡ -κ d' (mod e)`,
`h a₀/(2e) - (h/2 - (κ/2) h d'/e) ∈ ℤ`. -/
theorem phase_sub_mem_int {e d' a₀ κ : ℤ} (h : ℤ) (hκ : κ = 2 ∨ κ = -2) (he : Odd e)
    (ha : e ∣ a₀ + κ * d') (hodd : Odd a₀) :
    ∃ n : ℤ, ((h : ℝ) * a₀) / (2 * e) - ((h : ℝ) / 2 - ((κ : ℝ) / 2) * h * d' / e) = n := by
  obtain ⟨k, hk⟩ := ha
  have he0 : (e : ℝ) ≠ 0 := by
    have : e ≠ 0 := by rintro rfl; simp at he
    exact_mod_cast this
  -- `k` is odd: `a₀ = e k - κ d'` with `κ` even and `e` odd
  have hk_odd : Odd k := by
    have hκe : Even κ := by rcases hκ with rfl | rfl <;> decide
    have h1 : a₀ = e * k - κ * d' := by linarith
    by_contra hk
    rw [Int.not_odd_iff_even] at hk
    have : Even a₀ := by
      rw [h1]
      exact (Even.mul_left hk e).sub (Even.mul_right hκe d')
    exact (Int.not_even_iff_odd.mpr hodd) this
  obtain ⟨j, hj⟩ := hk_odd
  refine ⟨h * j, ?_⟩
  have hA : (a₀ : ℝ) = e * k - κ * d' := by
    have : a₀ = e * k - κ * d' := by linarith
    exact_mod_cast this
  have hK : (k : ℝ) = 2 * j + 1 := by exact_mod_cast hj
  rw [hA, hK]
  push_cast
  field_simp
  ring

/-- Paper, Section 7.2, exponential form:
`e(h a₀/(2e)) = (-1)^h · e(-(κ/2) h d'/e)`, where `e(t) = exp(2πi t)`. -/
theorem phase_exp {e d' a₀ κ : ℤ} (h : ℤ) (hκ : κ = 2 ∨ κ = -2) (he : Odd e)
    (ha : e ∣ a₀ + κ * d') (hodd : Odd a₀) :
    Complex.exp (2 * Real.pi * I * (((h : ℝ) * a₀) / (2 * e) : ℝ))
      = (-1 : ℂ) ^ h * Complex.exp (2 * Real.pi * I * ((-((κ : ℝ) / 2) * h * d' / e) : ℝ)) := by
  obtain ⟨n, hn⟩ := phase_sub_mem_int h hκ he ha hodd
  have hr : ((h : ℝ) * a₀) / (2 * e) = (h : ℝ) / 2 + (-((κ : ℝ) / 2) * h * d' / e) + n := by
    rw [← hn]; ring
  rw [hr]
  push_cast
  have e1 : 2 * (Real.pi : ℂ) * I * ((h : ℂ) / 2 + -((κ : ℂ) / 2) * h * d' / e + n)
      = (h : ℂ) * ((Real.pi : ℂ) * I) + 2 * (Real.pi : ℂ) * I * (-((κ : ℂ) / 2) * h * d' / e)
        + n * (2 * (Real.pi : ℂ) * I) := by ring
  rw [e1, Complex.exp_add, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I,
    Complex.exp_int_mul, Complex.exp_pi_mul_I, mul_one]

/-- Paper, Section 7.2, the case `h = 1`: `a₀/(2e) ≡ -(κ/2) d'/e + 1/2 (mod 1)`. -/
theorem a0_div_two_e_mod_one {e d' a₀ κ : ℤ} (hκ : κ = 2 ∨ κ = -2) (he : Odd e)
    (ha : e ∣ a₀ + κ * d') (hodd : Odd a₀) :
    ∃ n : ℤ, (a₀ : ℝ) / (2 * e) = -((κ : ℝ) / 2) * d' / e + 1 / 2 + n := by
  obtain ⟨n, hn⟩ := phase_sub_mem_int 1 hκ he ha hodd
  refine ⟨n, ?_⟩
  rw [← hn]
  push_cast
  ring

/-- Paper, Section 1.1: if `d, e` are odd and `be - ad = κ` with `κ ∈ {2,-2}`, then
`(d, e) = 1`. -/
theorem coprime_of_det {a b d e κ : ℤ} (hκ : κ = 2 ∨ κ = -2) (hd : Odd d)
    (hdet : b * e - a * d = κ) : IsCoprime d e := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  set g := Int.gcd d e
  have hg2 : (g : ℤ) ∣ 2 := by
    have h1 : (g : ℤ) ∣ b * e - a * d :=
      dvd_sub (dvd_mul_of_dvd_right (Int.gcd_dvd_right d e) b)
        (dvd_mul_of_dvd_right (Int.gcd_dvd_left d e) a)
    rw [hdet] at h1
    rcases hκ with rfl | rfl
    · exact h1
    · exact (dvd_neg).mp h1
  have hgd : (g : ℤ) ∣ d := Int.gcd_dvd_left d e
  have hgpos : (0 : ℤ) < g := by
    have : g ≠ 0 := by
      intro h0
      rw [h0, Nat.cast_zero, zero_dvd_iff] at hgd
      rw [hgd] at hd
      simp at hd
    omega
  have hle : (g : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) hg2
  have hne2 : (g : ℤ) ≠ 2 := by
    intro h2
    rw [h2] at hgd
    exact (Int.not_even_iff_odd.mpr hd) (even_iff_two_dvd.mpr hgd)
  omega

/-- Paper, Section 7.2: for odd `e`, `d` with `e ∣ d d' - 1`, `κ ∈ {2,-2}`, and `a₀`
odd with `a₀ ≡ -κ d' (mod e)`, an integer `a` admits an odd `b` with
`be - ad = κ` and `a` odd if and only if `a ≡ a₀ (mod 2e)`; moreover then `b` is
determined by `be = ad + κ`. -/
theorem solutions_iff {e d d' a₀ κ : ℤ} (hκ : κ = 2 ∨ κ = -2) (he : Odd e) (hd : Odd d)
    (hdd' : e ∣ d * d' - 1) (ha₀ : e ∣ a₀ + κ * d') (hodd : Odd a₀) (a : ℤ) :
    (Odd a ∧ ∃ b : ℤ, Odd b ∧ b * e - a * d = κ) ↔ 2 * e ∣ a - a₀ := by
  have hκe : Even κ := by rcases hκ with rfl | rfl <;> decide
  have hcop2 : IsCoprime (2 : ℤ) e :=
    (Prime.coprime_iff_not_dvd Int.prime_two).mpr
      (by rw [← even_iff_two_dvd, Int.not_even_iff_odd]; exact he)
  constructor
  · rintro ⟨hao, b, _hbo, hb⟩
    -- `a ≡ -κ d' (mod e)`: from `a d ≡ -κ` multiply by `d'`
    have h1 : e ∣ a - a₀ := by
      have h2 : a - a₀ = (a * d + κ) * d' - a * (d * d' - 1) - (a₀ + κ * d') := by ring
      rw [h2]
      have h3 : e ∣ a * d + κ := ⟨b, by linarith⟩
      exact dvd_sub (dvd_sub (dvd_mul_of_dvd_left h3 _) (dvd_mul_of_dvd_right hdd' _)) ha₀
    have h2 : (2 : ℤ) ∣ a - a₀ := by
      rcases hao with ⟨i, rfl⟩; rcases hodd with ⟨j, rfl⟩
      exact ⟨i - j, by ring⟩
    exact IsCoprime.mul_dvd hcop2 h2 h1
  · rintro ⟨k, hk⟩
    have ha : a = a₀ + 2 * e * k := by linarith
    have hao : Odd a := by
      rw [ha]; exact hodd.add_even (by exact ⟨e * k, by ring⟩)
    refine ⟨hao, ?_⟩
    have hdiv : e ∣ a * d + κ := by
      have h2 : a * d + κ = (a₀ + κ * d') * d - κ * (d * d' - 1) + 2 * e * k * d := by
        rw [ha]; ring
      rw [h2]
      exact dvd_add (dvd_sub (dvd_mul_of_dvd_left ha₀ _) (dvd_mul_of_dvd_right hdd' _))
        ⟨2 * k * d, by ring⟩
    obtain ⟨b, hb⟩ := hdiv
    refine ⟨b, ?_, by linarith⟩
    -- `b e = a d + κ` is odd, hence `b` is odd
    have hodd' : Odd (a * d + κ) := (hao.mul hd).add_even hκe
    rw [hb] at hodd'
    exact (Int.odd_mul.mp hodd').2

/-- "Shift-1" version (no parity condition, any shift `κ`, any modulus `e ≠ 0`):
if `a₀ ≡ -κ d' (mod e)` then `h a₀/e + κ h d'/e ∈ ℤ`. -/
theorem phase_sub_mem_int_shift {e d' a₀ κ : ℤ} (h : ℤ) (he : e ≠ 0)
    (ha : e ∣ a₀ + κ * d') :
    ∃ n : ℤ, ((h : ℝ) * a₀) / e - (-(κ : ℝ) * h * d' / e) = n := by
  obtain ⟨k, hk⟩ := ha
  refine ⟨h * k, ?_⟩
  have he0 : (e : ℝ) ≠ 0 := by exact_mod_cast he
  have hA : (a₀ : ℝ) = e * k - κ * d' := by
    have : a₀ = e * k - κ * d' := by linarith
    exact_mod_cast this
  rw [hA]
  push_cast
  field_simp
  ring

/-- "Shift-1" version, exponential form: `e(h a₀/e) = e(-κ h d'/e)`.  For
`κ = ±1` this is the phase for the determinant equation `be - ad = ±1`. -/
theorem phase_exp_shift {e d' a₀ κ : ℤ} (h : ℤ) (he : e ≠ 0) (ha : e ∣ a₀ + κ * d') :
    Complex.exp (2 * Real.pi * I * (((h : ℝ) * a₀) / e : ℝ))
      = Complex.exp (2 * Real.pi * I * ((-(κ : ℝ) * h * d' / e) : ℝ)) := by
  obtain ⟨n, hn⟩ := phase_sub_mem_int_shift h he ha
  have hr : ((h : ℝ) * a₀) / e = (-(κ : ℝ) * h * d' / e) + n := by rw [← hn]; ring
  rw [hr]
  push_cast
  rw [mul_add, Complex.exp_add,
    show 2 * (Real.pi : ℂ) * I * (n : ℂ) = n * (2 * Real.pi * I) by ring,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

end CRT

end MobiusDeterminant
