import MobiusDeterminant.Unconditional.LevelDefs
import LeanPool.MarkoffModP.BGS.NumberTheory.DivisorBound

/-!
# Level of distribution (paper §8): arithmetic lemmas

CRT description of the pairs `(d,e)` with `d ∣ n`, `e ∣ n + 2`, the Poisson phase,
reciprocity for Kloosterman fractions, the parity split of Möbius sums, `|r_N(d,e)| ≤ 1`,
the divisor bound and elementary bounds for the density `ϱ(d,e)`.
-/

open Finset Real
open scoped ArithmeticFunction.Moebius

namespace MobiusDeterminant

namespace Level

namespace Arith

/-- `exp(2πi x) = exp(2πi y)` when `x - y` is an integer. -/
lemma exp_two_pi_I_eq {x y : ℂ} (k : ℤ) (h : x = y + k) :
    Complex.exp (2 * π * Complex.I * x) = Complex.exp (2 * π * Complex.I * y) := by
  rw [h, mul_add, Complex.exp_add,
    show 2 * (π : ℂ) * Complex.I * (k : ℂ) = k * (2 * π * Complex.I) by ring,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- `exp(2πi X/q) = exp(2πi Y/q)` for integers `X ≡ Y (mod q)`. -/
lemma exp_div_eq_of_dvd {q : ℕ} (hq : 0 < q) {X Y : ℤ} (h : (q : ℤ) ∣ X - Y) :
    Complex.exp (2 * π * Complex.I * (X : ℂ) / (q : ℂ)) =
      Complex.exp (2 * π * Complex.I * (Y : ℂ) / (q : ℂ)) := by
  obtain ⟨k, hk⟩ := h
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hX : (X : ℂ) = Y + q * k := by
    have : X = Y + q * k := by linarith
    exact_mod_cast this
  rw [mul_div_assoc, mul_div_assoc]
  apply exp_two_pi_I_eq k
  rw [hX]
  field_simp

lemma moebius_two_mul_odd {d : ℕ} (hd : Odd d) : μ (2 * d) = -μ d := by
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
    (Nat.coprime_two_left.mpr hd), ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  ring

lemma moebius_two_mul_even {d : ℕ} (hd : ¬ Odd d) : μ (2 * d) = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  intro hsq
  rw [Nat.not_odd_iff_even] at hd
  obtain ⟨m, rfl⟩ := hd
  have h := hsq 2 ⟨m, by ring⟩
  simp at h

lemma ellOf_cases (i j : ℕ) : ellOf i j = 1 ∨ ellOf i j = 2 := by
  unfold ellOf; split_ifs <;> simp

lemma kfrac_eq_int (e : ℕ) (m : ℤ) (d : ℕ) :
    kfrac e m d = Complex.exp (2 * π * Complex.I *
      (((((m : ZMod e) * (d : ZMod e)⁻¹).val : ℕ) : ℤ) : ℂ) / (e : ℂ)) := by
  simp [kfrac]


lemma isCoprime_two_of_odd {d : ℕ} (hd : Odd d) : IsCoprime (2 : ℤ) d := by
  have := Nat.isCoprime_iff_coprime.mpr (Nat.coprime_two_left.mpr hd)
  simpa using this

lemma parity_facts {i j d' e' : ℕ} (hi : i ≤ 1) (hj : j ≤ 1) (hd : Odd d') (he : Odd e')
    (hcop : Nat.Coprime d' e') :
    (ellOf i j : ℤ) * kapOf i j = 2 ∧ (2 : ℤ) ^ i ∣ ellOf i j ∧ (2 : ℤ) ^ j ∣ ellOf i j ∧
    (∀ n : ℤ, (2 : ℤ) ^ i * d' ∣ n → (2 : ℤ) ^ j * e' ∣ n + 2 → (ellOf i j : ℤ) * d' ∣ n) ∧
    IsCoprime (ellOf i j : ℤ) e' ∧ Nat.gcd (2 ^ i * d') (2 ^ j * e') ∣ 2 ∧
    Nat.lcm (2 ^ i * d') (2 ^ j * e') = ellOf i j * d' * e' := by
  have h2e : IsCoprime (2 : ℤ) e' := isCoprime_two_of_odd he
  have h2d : IsCoprime (2 : ℤ) d' := isCoprime_two_of_odd hd
  have c2e : Nat.Coprime 2 e' := Nat.coprime_two_left.mpr he
  have c2d : Nat.Coprime 2 d' := Nat.coprime_two_left.mpr hd
  interval_cases i <;> interval_cases j
  · rw [show ellOf 0 0 = 1 from rfl, show kapOf 0 0 = 2 from rfl]
    refine ⟨by norm_num, by norm_num, by norm_num, fun n h1 _ => by simpa using h1,
      by simpa using (isCoprime_one_left : IsCoprime (1 : ℤ) (e' : ℤ)), ?_, ?_⟩
    · simp [hcop]
    · simp [hcop.lcm_eq_mul]
  · rw [show ellOf 0 1 = 2 from rfl, show kapOf 0 1 = 1 from rfl]
    refine ⟨by norm_num, by norm_num, by norm_num, fun n h1 h2 => ?_, by simpa using h2e, ?_, ?_⟩
    · have h3 : (2 : ℤ) ∣ n + 2 := (Dvd.intro _ rfl).trans h2
      have h4 : (2 : ℤ) ∣ n := (dvd_add_left (dvd_refl 2)).mp h3
      have h1' : (d' : ℤ) ∣ n := by simpa using h1
      push_cast
      exact h2d.mul_dvd h4 h1'
    · simp only [pow_zero, pow_one, one_mul]
      rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.mul_right c2d.symm (by simpa using hcop))]
      norm_num
    · simp only [pow_zero, pow_one, one_mul]
      rw [Nat.Coprime.lcm_eq_mul (Nat.Coprime.mul_right c2d.symm (by simpa using hcop))]
      ring
  · rw [show ellOf 1 0 = 2 from rfl, show kapOf 1 0 = 1 from rfl]
    refine ⟨by norm_num, by norm_num, by norm_num, fun n h1 _ => by simpa using h1,
      by simpa using h2e, ?_, ?_⟩
    · simp only [pow_zero, pow_one, one_mul]
      rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.mul_left c2e (by simpa using hcop))]
      norm_num
    · simp only [pow_zero, pow_one, one_mul]
      rw [Nat.Coprime.lcm_eq_mul (Nat.Coprime.mul_left c2e (by simpa using hcop))]
  · rw [show ellOf 1 1 = 2 from rfl, show kapOf 1 1 = 1 from rfl]
    refine ⟨by norm_num, by norm_num, by norm_num, fun n h1 _ => by simpa using h1,
      by simpa using h2e, ?_, ?_⟩
    · simp only [pow_one]
      rw [Nat.gcd_mul_left, hcop]
    · simp only [pow_one]
      rw [Nat.lcm_mul_left, hcop.lcm_eq_mul]; ring


/-- Uniform CRT description of the class. -/
lemma class_iff {i j d' e' ℓ : ℕ} {κ t : ℤ} (hℓκ : (ℓ : ℤ) * κ = 2)
    (hi : (2 : ℤ) ^ i ∣ ℓ) (hj : (2 : ℤ) ^ j ∣ ℓ)
    (hdiv : ∀ n : ℤ, (2 : ℤ) ^ i * d' ∣ n → (2 : ℤ) ^ j * e' ∣ n + 2 → (ℓ : ℤ) * d' ∣ n)
    (hℓe : IsCoprime (ℓ : ℤ) e') (hde : IsCoprime (d' : ℤ) e')
    (ht : (e' : ℤ) ∣ d' * t + κ) (n : ℤ) :
    ((2 : ℤ) ^ i * d' ∣ n ∧ (2 : ℤ) ^ j * e' ∣ n + 2) ↔
      (ℓ : ℤ) * d' * e' ∣ ℓ * d' * t - n := by
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨s, hs⟩ := hdiv n h1 h2
    have he2 : (e' : ℤ) ∣ n + 2 := (Dvd.intro_left _ rfl).trans h2
    have he3 : (e' : ℤ) ∣ ℓ * (d' * s + κ) := by
      have : n + 2 = ℓ * (d' * s + κ) := by rw [hs]; linear_combination -hℓκ
      rwa [this] at he2
    have he4 : (e' : ℤ) ∣ d' * s + κ := hℓe.symm.dvd_of_dvd_mul_left he3
    have he5 : (e' : ℤ) ∣ d' * (t - s) := by
      have := dvd_sub ht he4
      rw [show (d' : ℤ) * t + κ - (d' * s + κ) = d' * (t - s) by ring] at this
      exact this
    have he6 : (e' : ℤ) ∣ t - s := hde.symm.dvd_of_dvd_mul_left he5
    obtain ⟨r, hr⟩ := he6
    exact ⟨r, by rw [hs]; linear_combination (ℓ : ℤ) * d' * hr⟩
  · rintro ⟨m, hm⟩
    have hn : n = ℓ * d' * (t - e' * m) := by linear_combination -hm
    obtain ⟨r, hr⟩ := ht
    refine ⟨?_, ?_⟩
    · rw [hn]
      exact (mul_dvd_mul_right hi _).trans (Dvd.intro _ rfl)
    · have : n + 2 = ℓ * e' * (r - d' * m) := by
        rw [hn]; linear_combination (ℓ : ℤ) * hr - hℓκ
      rw [this]
      exact (mul_dvd_mul_right hj _).trans (Dvd.intro _ rfl)

/-- CRT: if `(d,e) ∣ 2` the solutions of `d ∣ n`, `e ∣ n+2` are one class modulo `[d,e]`. -/
lemma exists_class {d e : ℕ} (_hd : 0 < d) (he : 0 < e) (hg : Nat.gcd d e ∣ 2) :
    ∃ k : ℕ, ∀ n : ℕ, (d ∣ n ∧ e ∣ n + 2) ↔ n ≡ k [MOD Nat.lcm d e] := by
  have hgc : 0 ≡ 2 * e - 2 [MOD Nat.gcd d e] := by
    apply Nat.ModEq.symm
    rw [Nat.modEq_zero_iff_dvd]
    rw [show 2 * e - 2 = 2 * (e - 1) by omega]
    exact hg.trans (Dvd.intro _ rfl)
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder' hgc
  have hdk : (d : ℤ) ∣ k := by
    have := (Nat.modEq_zero_iff_dvd).mp hk1
    exact_mod_cast this
  have hek : (e : ℤ) ∣ (k : ℤ) + 2 := by
    have h := (Nat.modEq_iff_dvd).mp hk2.symm
    have hc : ((2 * e - 2 : ℕ) : ℤ) = 2 * e - 2 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hc] at h
    have : (k : ℤ) + 2 = (k - (2 * e - 2)) + e * 2 := by ring
    rw [this]
    exact dvd_add h (Dvd.intro _ rfl)
  refine ⟨k, fun n => ?_⟩
  rw [Nat.modEq_iff_dvd]
  constructor
  · rintro ⟨h1, h2⟩
    have h1' : (d : ℤ) ∣ n := by exact_mod_cast h1
    have h2' : (e : ℤ) ∣ (n : ℤ) + 2 := by exact_mod_cast h2
    have h3 : (e : ℤ) ∣ (k : ℤ) - n := by
      have := dvd_sub hek h2'
      rwa [show (k : ℤ) + 2 - (n + 2) = k - n by ring] at this
    have := Int.coe_lcm_dvd (dvd_sub hdk h1') h3
    simpa [Int.lcm] using this
  · intro h
    have hdq : (d : ℤ) ∣ (Nat.lcm d e : ℤ) := by exact_mod_cast Nat.dvd_lcm_left d e
    have heq : (e : ℤ) ∣ (Nat.lcm d e : ℤ) := by exact_mod_cast Nat.dvd_lcm_right d e
    have h1 : (d : ℤ) ∣ (n : ℤ) := by
      have := dvd_sub hdk (hdq.trans h)
      rwa [show (k : ℤ) - (k - n) = n by ring] at this
    have h2 : (e : ℤ) ∣ (n : ℤ) + 2 := by
      have := dvd_sub hek (heq.trans h)
      rwa [show (k : ℤ) + 2 - (k - n) = n + 2 by ring] at this
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

/-- A residue class modulo `q` has `N/q + O(1)` elements in `[1, N]`. -/
lemma card_class_bound (N q k : ℕ) (hq : 0 < q) :
    |(((Finset.Icc 1 N).filter (fun n => n ≡ k [MOD q])).card : ℝ) - N / q| ≤ 1 := by
  have hIcc : (Finset.Icc 1 N).filter (fun n => n ≡ k [MOD q]) =
      (Finset.Ioc 0 N).filter (fun n => n ≡ k [MOD q]) := by
    have : Finset.Icc 1 N = Finset.Ioc 0 N := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    rw [this]
  rw [hIcc]
  have hc := Nat.Ioc_filter_modEq_card 0 N hq k
  set c := ((Finset.Ioc 0 N).filter (fun n => n ≡ k [MOD q])).card
  set x : ℚ := ((N : ℚ) - k) / q
  set y : ℚ := ((0 : ℕ) - (k : ℚ)) / q
  have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
  have hxy : x - y = (N : ℚ) / q := by
    simp only [x, y]; field_simp; push_cast; ring
  have hz1 : ((⌊x⌋ - ⌊y⌋ : ℤ) : ℚ) < x - y + 1 := by
    have := Int.floor_le x
    have := Int.lt_floor_add_one y
    push_cast; linarith
  have hz2 : x - y - 1 < ((⌊x⌋ - ⌊y⌋ : ℤ) : ℚ) := by
    have := Int.lt_floor_add_one x
    have := Int.floor_le y
    push_cast; linarith
  have hs0 : (0 : ℚ) ≤ (N : ℚ) / q := by positivity
  have hcQ : (N : ℚ) / q - 1 ≤ (c : ℚ) ∧ (c : ℚ) ≤ (N : ℚ) / q + 1 := by
    have hcz : ((c : ℤ) : ℚ) = ((max (⌊x⌋ - ⌊y⌋) 0 : ℤ) : ℚ) := by
      rw [hc]
    rw [Int.cast_natCast] at hcz
    rw [hcz]
    rcases le_total (⌊x⌋ - ⌊y⌋) 0 with h | h
    · rw [max_eq_right h]
      have : ((⌊x⌋ - ⌊y⌋ : ℤ) : ℚ) ≤ 0 := by exact_mod_cast h
      push_cast
      constructor <;> linarith
    · rw [max_eq_left h]
      constructor <;> linarith
  have h1 : (N : ℝ) / q - 1 ≤ (c : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).mpr hcQ.1
    push_cast at this
    exact this
  have h2 : (c : ℝ) ≤ (N : ℝ) / q + 1 := by
    have := (Rat.cast_le (K := ℝ)).mpr hcQ.2
    push_cast at this
    exact this
  rw [abs_le]
  constructor <;> linarith

end Arith

open Arith

theorem dens_nonneg (d e : ℕ) : 0 ≤ dens d e := by
  unfold dens
  split_ifs
  · positivity
  · exact le_rfl

theorem dens_le_one (d e : ℕ) : dens d e ≤ 1 := by
  unfold dens
  split_ifs
  · rcases Nat.eq_zero_or_pos (Nat.lcm d e) with h | h
    · simp [h]
    · rw [div_le_one (by exact_mod_cast h)]
      exact_mod_cast h
  · norm_num

/-- `ϱ(d,e) ≤ 2/(de)`. -/
theorem dens_le (d e : ℕ) (hd : 0 < d) (he : 0 < e) : dens d e ≤ 2 / ((d : ℝ) * e) := by
  unfold dens
  split_ifs with hg
  · have hgl := Nat.gcd_mul_lcm d e
    have hg2 : Nat.gcd d e ≤ 2 := Nat.le_of_dvd (by norm_num) hg
    have hl : 0 < Nat.lcm d e := Nat.lcm_pos hd he
    have hlR : (0 : ℝ) < Nat.lcm d e := by exact_mod_cast hl
    have hdeR : (0 : ℝ) < (d : ℝ) * e := by positivity
    rw [div_le_div_iff₀ hlR hdeR, one_mul]
    have h1 : ((Nat.gcd d e : ℕ) : ℝ) * (Nat.lcm d e : ℕ) = (d : ℝ) * e := by
      exact_mod_cast hgl
    have h2 : ((Nat.gcd d e : ℕ) : ℝ) ≤ 2 := by exact_mod_cast hg2
    nlinarith
  · positivity

/-- Harmonic sum `∑_{d ≤ K} 1/d ≤ 1 + log K`. -/
theorem sum_inv_le_log (K : ℕ) : ∑ d ∈ Finset.Icc 1 K, (1 : ℝ) / d ≤ 1 + Real.log K := by
  have h := harmonic_le_one_add_log K
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  simpa [one_div] using h

/-- Divisor bound `τ(n) ≤ C n^ε`. -/
theorem card_divisors_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  obtain ⟨N₁, hN₁⟩ := BGS.NumberTheory.exists_threshold_card_divisors_le_rpow hε
  refine ⟨N₁ + 1, by linarith [(Nat.cast_nonneg N₁ : (0 : ℝ) ≤ N₁)], fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : 1 ≤ (n : ℝ) ^ ε := Real.one_le_rpow hn1 hε.le
  rcases le_or_gt N₁ n with h | h
  · have := hN₁ n h
    have h0 : (0 : ℝ) ≤ (n : ℝ) ^ ε := by positivity
    nlinarith [(Nat.cast_nonneg N₁ : (0 : ℝ) ≤ N₁)]
  · have h1 : (n.divisors.card : ℝ) ≤ n := by exact_mod_cast Nat.card_divisors_le_self n
    have h2 : (n : ℝ) ≤ N₁ + 1 := by
      have : (n : ℝ) < N₁ := by exact_mod_cast h
      linarith
    calc (n.divisors.card : ℝ) ≤ N₁ + 1 := h1.trans h2
      _ = (N₁ + 1) * 1 := by ring
      _ ≤ (N₁ + 1) * (n : ℝ) ^ ε := by
        apply mul_le_mul_of_nonneg_left hpow
        positivity

theorem ellOf_kapOf {i j : ℕ} :
    ((ellOf i j = 1 ∧ kapOf i j = 2) ∨ (ellOf i j = 2 ∧ kapOf i j = 1)) := by
  unfold ellOf kapOf
  split_ifs <;> simp

/-- If `(d,e) ∤ 2` there is no `n` with `d ∣ n`, `e ∣ n + 2`, and `ϱ(d,e) = 0`. -/
theorem bracket_eq_zero_of_not_dvd {d e : ℕ} (N₀ : ℝ) (ψ : ℝ → ℂ)
    (h : ¬ Nat.gcd d e ∣ 2) : bracket N₀ ψ d e = 0 := by
  unfold bracket dens
  simp only [h, ↓reduceIte]
  have hempty : (Finset.Icc 1 ⌊2 * N₀⌋₊).filter (fun n => d ∣ n ∧ e ∣ n + 2) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    rintro n - ⟨hdn, hen⟩
    apply h
    have h1 : Nat.gcd d e ∣ n := (Nat.gcd_dvd_left d e).trans hdn
    have h2 : Nat.gcd d e ∣ n + 2 := (Nat.gcd_dvd_right d e).trans hen
    exact (Nat.dvd_add_right h1).mp h2
  rw [hempty]
  simp

/-- Exchange of the roles of the two variables over odd coprime pairs. -/
theorem sum_odd_coprime_comm (X Y : Finset ℕ) (f : ℕ → ℕ → ℂ) :
    ∑ b ∈ X.filter Odd, ∑ a ∈ Y.filter (fun a => Nat.Coprime a (2 * b)), f a b =
      ∑ a ∈ Y.filter Odd, ∑ b ∈ X.filter (fun b => Nat.Coprime b (2 * a)), f a b := by
  have key : ∀ a b : ℕ, (Odd b ∧ Nat.Coprime a (2 * b)) ↔ (Odd a ∧ Nat.Coprime b (2 * a)) := by
    intro a b
    rw [Nat.coprime_mul_iff_right, Nat.coprime_mul_iff_right, Nat.coprime_two_right,
      Nat.coprime_two_right, Nat.coprime_comm (m := a)]
    tauto
  calc ∑ b ∈ X.filter Odd, ∑ a ∈ Y.filter (fun a => Nat.Coprime a (2 * b)), f a b
      = ∑ b ∈ X, ∑ a ∈ Y, if (Odd b ∧ Nat.Coprime a (2 * b)) then f a b else 0 := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_filter]
        split_ifs with hb
        · exact Finset.sum_congr rfl fun a _ => by simp [hb]
        · simp [hb]
    _ = ∑ a ∈ Y, ∑ b ∈ X, if (Odd a ∧ Nat.Coprime b (2 * a)) then f a b else 0 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [if_congr (key a b) rfl rfl]
    _ = ∑ a ∈ Y.filter Odd, ∑ b ∈ X.filter (fun b => Nat.Coprime b (2 * a)), f a b := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_filter]
        split_ifs with ha
        · exact Finset.sum_congr rfl fun b _ => by simp [ha]
        · simp [ha]

/-- CRT description of the pairs (Proposition 8.1, Step 2).  For odd coprime `d', e'` and
`i, j ≤ 1`, the `n` with `2^i d' ∣ n`, `2^j e' ∣ n + 2` form the class `c0Of i j d' e'`
modulo `ℓ d' e'` (`ℓ = ellOf i j`), the density is `1/(ℓ d' e')`, and the Poisson phase is
`e(h c₀/(ℓ d' e')) = e_{e'}(-κ h d̄')`, `κ = kapOf i j`. -/
theorem pair_class {i j d' e' : ℕ} (hi : i ≤ 1) (hj : j ≤ 1) (hd : Odd d') (he : Odd e')
    (hcop : Nat.Coprime d' e') :
    (∀ n : ℕ, (2 ^ i * d' ∣ n ∧ 2 ^ j * e' ∣ n + 2) ↔
        (n : ℤ) ≡ c0Of i j d' e' [ZMOD ((ellOf i j * d' * e' : ℕ) : ℤ)]) ∧
    dens (2 ^ i * d') (2 ^ j * e') = 1 / ((ellOf i j * d' * e' : ℕ) : ℝ) ∧
    ∀ h : ℤ, Complex.exp (2 * π * Complex.I * ((h * c0Of i j d' e' : ℤ) : ℂ) /
        ((ellOf i j * d' * e' : ℕ) : ℂ)) = kfrac e' (-kapOf i j * h) d' := by
  obtain ⟨hℓκ, h2i, h2j, hdiv, hℓe, hg, hl⟩ := parity_facts hi hj hd he hcop
  have he0 : 0 < e' := he.pos
  have hd0 : 0 < d' := hd.pos
  have : NeZero e' := ⟨he0.ne'⟩
  set t : ℤ := ((((-kapOf i j : ℤ) : ZMod e') * ((d' : ZMod e'))⁻¹).val : ℤ) with ht
  have hc0 : c0Of i j d' e' = (ellOf i j : ℤ) * d' * t := rfl
  have htZ : ((t : ℤ) : ZMod e') = ((-kapOf i j : ℤ) : ZMod e') * ((d' : ZMod e'))⁻¹ := by
    rw [ht, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hdt : (e' : ℤ) ∣ d' * t + kapOf i j := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [htZ, ← mul_assoc, mul_comm (d' : ZMod e'), mul_assoc,
      ZMod.coe_mul_inv_eq_one d' hcop]
    push_cast
    ring
  refine ⟨?_, ?_, ?_⟩
  · intro n
    have key := class_iff hℓκ h2i h2j hdiv hℓe (Nat.isCoprime_iff_coprime.mpr hcop) hdt (n : ℤ)
    rw [Int.modEq_iff_dvd, hc0]
    push_cast
    rw [← key]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  · unfold dens
    simp only [hg, ↓reduceIte, hl]
  · intro h
    rw [kfrac_eq_int]
    have hq : ((h * c0Of i j d' e' : ℤ) : ℂ) / ((ellOf i j * d' * e' : ℕ) : ℂ) =
        ((h * t : ℤ) : ℂ) / (e' : ℂ) := by
      have hℓ0 : (ellOf i j : ℂ) ≠ 0 := by
        rcases ellOf_cases i j with h1 | h1 <;> rw [h1] <;> norm_num
      have hd0' : (d' : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
      have he0' : (e' : ℂ) ≠ 0 := by exact_mod_cast he0.ne'
      rw [hc0]
      push_cast
      field_simp
    rw [mul_div_assoc, hq, ← mul_div_assoc]
    apply exp_div_eq_of_dvd he0
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [htZ, ZMod.natCast_zmod_val]
    push_cast
    ring

/-- Reciprocity: `e_b(m ā) = e(m/(ab)) e_a(-m b̄)` for coprime `a, b ≥ 1`. -/
theorem kfrac_reciprocity {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (m : ℤ) :
    kfrac b m a = Complex.exp (2 * π * Complex.I * (m : ℂ) / ((a * b : ℕ) : ℂ)) *
      kfrac a (-m) b := by
  have : NeZero a := ⟨ha.ne'⟩
  have : NeZero b := ⟨hb.ne'⟩
  unfold kfrac
  set v1 := ((m : ZMod b) * (a : ZMod b)⁻¹).val with hv1
  set v2 := (((-m : ℤ) : ZMod a) * (b : ZMod a)⁻¹).val with hv2
  set X : ℤ := (a : ℤ) * v1 - m - (b : ℤ) * v2 with hX
  have hbX : (b : ℤ) ∣ X := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    rw [hX]
    push_cast
    rw [hv1, ZMod.natCast_zmod_val, ZMod.natCast_self, zero_mul, sub_zero,
      ← mul_assoc, mul_comm (a : ZMod b), mul_assoc, ZMod.coe_mul_inv_eq_one a hab]
    ring
  have haX : (a : ℤ) ∣ X := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    rw [hX]
    push_cast
    rw [hv2, ZMod.natCast_zmod_val, ZMod.natCast_self, zero_mul, zero_sub,
      ← mul_assoc, mul_comm (b : ZMod a), mul_assoc, ZMod.coe_mul_inv_eq_one b hab.symm]
    push_cast
    ring
  have habX : (a : ℤ) * b ∣ X :=
    IsCoprime.mul_dvd (Nat.isCoprime_iff_coprime.mpr hab) haX hbX
  obtain ⟨k, hk⟩ := habX
  rw [← Complex.exp_add]
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hXC : (a : ℂ) * (v1 : ℂ) = m + b * v2 + a * b * k := by
    have : (a : ℤ) * v1 = m + b * v2 + a * b * k := by linarith
    exact_mod_cast this
  rw [mul_div_assoc, mul_div_assoc, mul_div_assoc, ← mul_add]
  apply exp_two_pi_I_eq k
  push_cast
  field_simp
  linear_combination hXC

/-- Parity split of a Möbius-weighted sum: `μ(2d) = -μ(d)` for odd `d`, `μ(4m) = 0`. -/
theorem sum_mobius_parity (M : ℕ) (f : ℕ → ℂ) :
    ∑ d ∈ Finset.Icc 1 M, (μ d : ℂ) * f d =
      ∑ d ∈ (Finset.Icc 1 M).filter Odd, (μ d : ℂ) * f d
        - ∑ d ∈ (Finset.Icc 1 (M / 2)).filter Odd, (μ d : ℂ) * f (2 * d) := by
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 M) Odd]
  have heven : ∑ d ∈ (Finset.Icc 1 M).filter (fun d => ¬ Odd d), (μ d : ℂ) * f d =
      ∑ d ∈ Finset.Icc 1 (M / 2), (μ (2 * d) : ℂ) * f (2 * d) := by
    apply Finset.sum_nbij' (fun d => d / 2) (fun d => 2 * d)
    · intro d hd
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.not_odd_iff_even] at hd
      obtain ⟨⟨h1, h2⟩, ⟨m, rfl⟩⟩ := hd
      simp only [Finset.mem_Icc]
      omega
    · intro d hd
      simp only [Finset.mem_Icc] at hd
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.not_odd_iff_even]
      refine ⟨⟨by omega, by omega⟩, ⟨d, by ring⟩⟩
    · intro d hd
      simp only [Finset.mem_filter, Nat.not_odd_iff_even] at hd
      obtain ⟨-, ⟨m, rfl⟩⟩ := hd
      omega
    · intro d _
      omega
    · intro d hd
      simp only [Finset.mem_filter, Nat.not_odd_iff_even] at hd
      obtain ⟨-, ⟨m, rfl⟩⟩ := hd
      congr 3 <;> omega
  rw [heven, ← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 (M / 2)) Odd]
  have h2 : ∑ d ∈ (Finset.Icc 1 (M / 2)).filter (fun d => ¬ Odd d),
      (μ (2 * d) : ℂ) * f (2 * d) = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    rw [Finset.mem_filter] at hd
    rw [moebius_two_mul_even hd.2]
    simp
  rw [h2, add_zero]
  have h3 : ∑ d ∈ (Finset.Icc 1 (M / 2)).filter Odd, (μ (2 * d) : ℂ) * f (2 * d) =
      -∑ d ∈ (Finset.Icc 1 (M / 2)).filter Odd, (μ d : ℂ) * f (2 * d) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mem_filter] at hd
    rw [moebius_two_mul_odd hd.2]
    push_cast
    ring
  rw [h3]
  ring

/-- `|r_N(d,e)| ≤ 1` (CRT: the `n ≤ N` counted form one residue class modulo `[d,e]`). -/
theorem abs_rem_le_one (N d e : ℕ) (hd : 0 < d) (he : 0 < e) : |rem N d e| ≤ 1 := by
  unfold rem pairCount dens
  by_cases hg : Nat.gcd d e ∣ 2
  · obtain ⟨k, hk⟩ := exists_class hd he hg
    simp only [hg, ↓reduceIte]
    have hset : (Finset.Icc 1 N).filter (fun n => d ∣ n ∧ e ∣ n + 2) =
        (Finset.Icc 1 N).filter (fun n => n ≡ k [MOD Nat.lcm d e]) :=
      Finset.filter_congr fun n _ => hk n
    rw [hset, mul_one_div]
    exact card_class_bound N _ k (Nat.lcm_pos hd he)
  · simp only [hg, ↓reduceIte, mul_zero, sub_zero]
    have hempty : (Finset.Icc 1 N).filter (fun n => d ∣ n ∧ e ∣ n + 2) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      rintro n - ⟨hdn, hen⟩
      apply hg
      have h1 : Nat.gcd d e ∣ n := (Nat.gcd_dvd_left d e).trans hdn
      have h2 : Nat.gcd d e ∣ n + 2 := (Nat.gcd_dvd_right d e).trans hen
      exact (Nat.dvd_add_right h1).mp h2
    rw [hempty]
    simp

end Level

end MobiusDeterminant
