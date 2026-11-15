import MobiusDeterminant.MainTerm.MobiusSumsMobius

/-!
# Arithmetic part: reduction of `S_g` to `S₁`, and sums over `g`-smooth numbers

* `μ(d) 1[(d,g)=1] = ∑_{k m = d, k ∣ g^∞} μ(m)` (`chiF_mul_moebius`);
* `S_g(y) = ∑_{k ≤ y, k ∣ g^∞} S₁(y/k)/k` (`Sg_eq`);
* `∑_{k ∣ g^∞} k^{-σ} = ∏_{p ∣ g} (1 - p^{-σ})^{-1}` (`hasSum_Fg`);
* `∏_{p ∣ g} (1 - 1/p)^{-1} = g/φ(g)` and `∏_{p ∣ g} (1 - p^{-1/2})^{-1} ≤ g²`.
-/

open Finset Real Filter Topology
open scoped ArithmeticFunction.Moebius

namespace MobiusDeterminant
namespace MobiusSums

open ArithmeticFunction

/-- The `g`-smooth numbers `k ∣ g^∞`: `k ≠ 0` with all prime factors dividing `g`. -/
abbrev Fg (g : ℕ) : Set ℕ := Nat.factoredNumbers g.primeFactors

open Classical in
/-- Indicator of `Fg g` as an arithmetic function. -/
noncomputable def chiF (g : ℕ) : ArithmeticFunction ℤ :=
  ⟨fun k => if k ∈ Fg g then 1 else 0, by simp [Fg, Nat.mem_factoredNumbers]⟩

open Classical in
lemma chiF_apply (g k : ℕ) : chiF g k = if k ∈ Fg g then 1 else 0 := rfl

lemma one_mem_Fg (g : ℕ) : 1 ∈ Fg g := by simp [Fg, Nat.mem_factoredNumbers]

lemma zero_not_mem_Fg (g : ℕ) : 0 ∉ Fg g := by simp [Fg, Nat.mem_factoredNumbers]

lemma chiF_mult (g : ℕ) : (chiF g).IsMultiplicative := by
  refine ⟨?_, ?_⟩
  · simp [chiF_apply, one_mem_Fg]
  · intro m n _
    simp only [chiF_apply]
    by_cases hm : m = 0
    · subst hm; simp [zero_not_mem_Fg]
    by_cases hn : n = 0
    · subst hn; simp [zero_not_mem_Fg]
    have key : m * n ∈ Fg g ↔ m ∈ Fg g ∧ n ∈ Fg g :=
      ⟨fun h => ⟨Nat.mem_factoredNumbers_of_dvd h (dvd_mul_right m n),
        Nat.mem_factoredNumbers_of_dvd h (dvd_mul_left n m)⟩,
        fun h => Nat.mul_mem_factoredNumbers h.1 h.2⟩
    by_cases h1 : m ∈ Fg g <;> by_cases h2 : n ∈ Fg g <;> simp [h1, h2, key]

/-- `ψ(d) = μ(d) 1[(d,g) = 1]`. -/
noncomputable def psiC (g : ℕ) : ArithmeticFunction ℤ :=
  ⟨fun d => if Nat.Coprime d g then μ d else 0, by split_ifs <;> simp⟩

lemma psiC_apply (g d : ℕ) : psiC g d = if Nat.Coprime d g then μ d else 0 := rfl

lemma psiC_mult (g : ℕ) : (psiC g).IsMultiplicative := by
  refine ⟨by simp [psiC_apply], ?_⟩
  intro m n hmn
  simp only [psiC_apply, Nat.coprime_mul_iff_left]
  by_cases h1 : Nat.Coprime m g
  · by_cases h2 : Nat.Coprime n g
    · rw [ite_eq_left ⟨h1, h2⟩, ite_eq_left h1, ite_eq_left h2, isMultiplicative_moebius.map_mul_of_coprime hmn]
    · rw [ite_eq_right (fun h => h2 h.2), ite_eq_right h2, mul_zero]
  · rw [ite_eq_right (fun h => h1 h.1), ite_eq_right h1, zero_mul]

/-- `1_{g^∞} * μ = μ · 1[(·, g) = 1]`. -/
lemma chiF_mul_moebius (g : ℕ) (hg : g ≠ 0) : chiF g * μ = psiC g := by
  rw [IsMultiplicative.eq_iff_eq_on_prime_powers _ ((chiF_mult g).mul isMultiplicative_moebius)
    _ (psiC_mult g)]
  intro p i hp
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp only [pow_zero]
    rw [((chiF_mult g).mul isMultiplicative_moebius).map_one, (psiC_mult g).map_one]
  have hpi0 : p ^ i ≠ 0 := pow_ne_zero _ hp.ne_zero
  by_cases hpg : p ∣ g
  · have hps : psiC g (p ^ i) = 0 := by
      rw [psiC_apply, ite_eq_right]
      intro hc
      have h1 : p ∣ Nat.gcd (p ^ i) g := Nat.dvd_gcd (dvd_pow_self p hi.ne') hpg
      rw [hc] at h1
      exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
    rw [hps]
    have hz : (chiF g * μ) (p ^ i) = (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℤ) * μ) (p ^ i) := by
      simp only [mul_apply]
      refine sum_congr rfl (fun x hx => ?_)
      have hx' := Nat.mem_divisorsAntidiagonal.mp hx
      have hx1 : x.1 ∣ p ^ i := Dvd.intro _ hx'.1
      have hx10 : x.1 ≠ 0 := by
        rintro h0; rw [h0, zero_mul] at hx'; exact hpi0 hx'.1.symm
      have hmem : x.1 ∈ Fg g := by
        rw [Fg, Nat.mem_factoredNumbers_iff_primeFactors_subset]
        refine ⟨hx10, ?_⟩
        refine (Nat.primeFactors_mono hx1 hpi0).trans ?_
        rw [Nat.primeFactors_prime_pow hi.ne' hp]
        intro q hq
        rw [Finset.mem_singleton] at hq
        subst hq
        exact Nat.mem_primeFactors.mpr ⟨hp, hpg, hg⟩
      rw [chiF_apply, ite_eq_left hmem, natCoe_apply, zeta_apply, ite_eq_right hx10]
      simp
    rw [hz, coe_zeta_mul_moebius, one_apply_ne]
    exact (Nat.one_lt_pow hi.ne' hp.one_lt).ne'
  · have hps : psiC g (p ^ i) = μ (p ^ i) := by
      rw [psiC_apply, ite_eq_left]
      exact Nat.Coprime.pow_left i ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpg)
    rw [hps, mul_apply, Finset.sum_eq_single (1, p ^ i)]
    · simp [chiF_apply, one_mem_Fg]
    · intro x hx hne
      have hx' := Nat.mem_divisorsAntidiagonal.mp hx
      have hx1 : x.1 ≠ 1 := by
        intro h1
        apply hne
        have h2 : x.2 = p ^ i := by rw [h1, one_mul] at hx'; exact hx'.1
        exact Prod.ext h1 h2
      have hnot : x.1 ∉ Fg g := by
        intro hmem
        obtain ⟨k, _, hk'⟩ := (Nat.dvd_prime_pow hp).mp (Dvd.intro _ hx'.1)
        have hk0 : k ≠ 0 := by rintro rfl; rw [pow_zero] at hk'; exact hx1 hk'
        have hpx : p ∈ x.1.primeFactors := by
          rw [hk', Nat.primeFactors_prime_pow hk0 hp]; simp
        have := (Nat.mem_factoredNumbers_iff_primeFactors_subset.mp hmem).2 hpx
        exact hpg (Nat.dvd_of_mem_primeFactors this)
      simp [chiF_apply, hnot]
    · intro h
      exfalso
      apply h
      simp [Nat.mem_divisorsAntidiagonal, hp.ne_zero]

/-- Weighted version of the Dirichlet-convolution summation identity. -/
lemma sum_conv_weighted (f h w : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, (∑ x ∈ n.divisorsAntidiagonal, f x.1 * h x.2) * w n =
      ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 (N / a), f a * h b * w (a * b) := by
  have step1 : ∀ n ∈ Icc 1 N, (∑ x ∈ n.divisorsAntidiagonal, f x.1 * h x.2) * w n =
      ∑ a ∈ n.divisors, f a * h (n / a) * w n := by
    intro n _
    rw [Finset.sum_mul]
    exact Nat.sum_divisorsAntidiagonal (fun a b => f a * h b * w n)
  rw [sum_congr rfl step1]
  rw [Finset.sum_comm' (t' := Icc 1 N) (s' := fun a => (Icc 1 N).filter (a ∣ ·))]
  · apply sum_congr rfl
    intro a ha
    have ha1 : 1 ≤ a := (mem_Icc.mp ha).1
    have ha0 : 0 < a := ha1
    apply Finset.sum_nbij' (fun n => n / a) (fun b => a * b)
    · intro n hn
      simp only [mem_filter, mem_Icc] at hn
      obtain ⟨⟨hn1, hnN⟩, hdvd⟩ := hn
      simp only [mem_Icc]
      obtain ⟨k, rfl⟩ := hdvd
      rw [Nat.mul_div_cancel_left k ha0]
      refine ⟨?_, ?_⟩
      · rcases Nat.eq_zero_or_pos k with rfl | hk
        · omega
        · exact hk
      · rw [Nat.le_div_iff_mul_le ha0]; linarith [mul_comm a k]
    · intro b hb
      simp only [mem_Icc] at hb
      simp only [mem_filter, mem_Icc]
      refine ⟨⟨?_, ?_⟩, dvd_mul_right a b⟩
      · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      · have := (Nat.le_div_iff_mul_le ha0).mp hb.2
        linarith [mul_comm a b]
    · intro n hn
      simp only [mem_filter] at hn
      exact Nat.mul_div_cancel' hn.2
    · intro b _
      exact Nat.mul_div_cancel_left b ha0
    · intro n hn
      simp only [mem_filter] at hn
      rw [Nat.mul_div_cancel' hn.2]
  · intro n a
    simp only [mem_Icc, Nat.mem_divisors, mem_filter]
    constructor
    · rintro ⟨⟨hn1, hnN⟩, hdvd, hn0⟩
      refine ⟨⟨⟨hn1, hnN⟩, hdvd⟩, ?_, ?_⟩
      · exact Nat.pos_of_dvd_of_pos hdvd (by omega)
      · exact (Nat.le_of_dvd (by omega) hdvd).trans hnN
    · rintro ⟨⟨⟨hn1, hnN⟩, hdvd⟩, _, _⟩
      exact ⟨⟨hn1, hnN⟩, hdvd, by omega⟩

/-- `S_g(y) = ∑_{k ≤ y, k ∣ g^∞} S₁(y/k)/k`. -/
lemma Sg_eq (g : ℕ) (hg : g ≠ 0) (y : ℝ) :
    Sg g y = ∑ a ∈ Icc 1 ⌊y⌋₊, (chiF g a : ℝ) * (S1 (y / a) / a) := by
  unfold Sg
  rw [Finset.sum_filter]
  have e1 : ∀ d ∈ Icc 1 ⌊y⌋₊, (if Nat.Coprime d g then (μ d : ℝ) * Real.log (y / d) / d else 0) =
      (((chiF g * μ) d : ℤ) : ℝ) * (Real.log (y / d) / d) := by
    intro d _
    rw [chiF_mul_moebius g hg, psiC_apply]
    split_ifs <;> push_cast <;> ring
  rw [sum_congr rfl e1]
  simp only [ArithmeticFunction.mul_apply, Int.cast_sum, Int.cast_mul]
  rw [sum_conv_weighted (fun a => (chiF g a : ℝ)) (fun b => (μ b : ℝ))
    (fun n => Real.log (y / n) / n) ⌊y⌋₊]
  apply sum_congr rfl
  intro a ha
  have ha1 : 1 ≤ a := (mem_Icc.mp ha).1
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha1
  unfold S1
  rw [Nat.floor_div_natCast, Finset.sum_div, Finset.mul_sum]
  apply sum_congr rfl
  intro b hb
  have hb1 : 1 ≤ b := (mem_Icc.mp hb).1
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb1
  push_cast
  rw [div_div]
  field_simp

/-! ## Sums over `g`-smooth numbers -/

lemma hasSum_Fg (g : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    HasSum (fun k : ℕ => (chiF g k : ℝ) * (1 / (k : ℝ) ^ σ))
      (∏ p ∈ g.primeFactors, (1 - 1 / (p : ℝ) ^ σ)⁻¹) := by
  set f : ℕ → ℝ := fun n => 1 / (n : ℝ) ^ σ with hf
  have hf1 : f 1 = 1 := by simp [f]
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n := by
    intro m n _
    simp only [f]
    push_cast
    rw [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _), one_div_mul_one_div]
  have hgeom : ∀ {p : ℕ}, p.Prime → ∀ n : ℕ, f (p ^ n) = (1 / (p : ℝ) ^ σ) ^ n := by
    intro p _ n
    simp only [f]
    push_cast
    rw [one_div_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _), mul_comm,
      Real.rpow_mul (Nat.cast_nonneg _), Real.rpow_natCast]
  have hr : ∀ {p : ℕ}, p.Prime → 0 ≤ 1 / (p : ℝ) ^ σ ∧ 1 / (p : ℝ) ^ σ < 1 := by
    intro p hp
    refine ⟨by positivity, ?_⟩
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    rw [div_lt_one (by positivity)]
    exact Real.one_lt_rpow hp1 hσ
  have hsum : ∀ {p : ℕ}, p.Prime → Summable (fun n : ℕ => ‖f (p ^ n)‖) := by
    intro p hp
    simp_rw [hgeom hp, norm_pow, Real.norm_eq_abs, abs_of_nonneg (hr hp).1]
    exact summable_geometric_of_lt_one (hr hp).1 (hr hp).2
  obtain ⟨_, hH⟩ :=
    EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum hf1 hmul hsum
      g.primeFactors
  have hfilt : g.primeFactors.filter Nat.Prime = g.primeFactors :=
    Finset.filter_true_of_mem (fun p hp => Nat.prime_of_mem_primeFactors hp)
  rw [hfilt] at hH
  have hprod : ∏ p ∈ g.primeFactors, ∑' n : ℕ, f (p ^ n) =
      ∏ p ∈ g.primeFactors, (1 - 1 / (p : ℝ) ^ σ)⁻¹ := by
    apply prod_congr rfl
    intro p hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    simp_rw [hgeom hp']
    exact tsum_geometric_of_lt_one (hr hp').1 (hr hp').2
  rw [hprod] at hH
  have := (hasSum_subtype_iff_indicator (s := Fg g) (f := f)).mp hH
  convert this using 1
  funext k
  by_cases hk : k ∈ Fg g
  · simp [chiF_apply, hk, f]
  · simp [chiF_apply, hk]

lemma prod_eq_div_totient (g : ℕ) (hg : g ≠ 0) :
    ∏ p ∈ g.primeFactors, (1 - 1 / (p : ℝ) ^ (1 : ℝ))⁻¹ = (g : ℝ) / (Nat.totient g : ℝ) := by
  have hq := Nat.totient_eq_mul_prod_factors g
  have hr : (Nat.totient g : ℝ) = g * ∏ p ∈ g.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have := congrArg (fun q : ℚ => (q : ℝ)) hq
    push_cast at this
    exact this
  rw [hr]
  simp only [Real.rpow_one, one_div]
  rw [Finset.prod_inv_distrib]
  have hg' : (g : ℝ) ≠ 0 := by exact_mod_cast hg
  exact (div_mul_cancel_left₀ hg' _).symm

lemma prod_half_le (g : ℕ) (hg : g ≠ 0) :
    ∏ p ∈ g.primeFactors, (1 - 1 / (p : ℝ) ^ (1 / 2 : ℝ))⁻¹ ≤ (g : ℝ) ^ 2 := by
  have h1 : ∀ p ∈ g.primeFactors, (1 - 1 / (p : ℝ) ^ (1 / 2 : ℝ))⁻¹ ≤ 4 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hsq : (4 / 3 : ℝ) ≤ (p : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow, Real.le_sqrt (by norm_num) (by positivity)]
      nlinarith
    have hpos : 0 < (p : ℝ) ^ (1 / 2 : ℝ) := by positivity
    have h3 : 1 / (p : ℝ) ^ (1 / 2 : ℝ) ≤ 3 / 4 := by
      rw [div_le_iff₀ hpos]; linarith
    have h4 : 0 < 1 - 1 / (p : ℝ) ^ (1 / 2 : ℝ) := by linarith
    rw [inv_le_comm₀ h4 (by norm_num)]
    linarith
  have hnn : ∀ p ∈ g.primeFactors, 0 ≤ (1 - 1 / (p : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hp1 : (1 : ℝ) < p := by linarith
    have : 1 / (p : ℝ) ^ (1 / 2 : ℝ) < 1 := by
      rw [div_lt_one (by positivity)]
      exact Real.one_lt_rpow hp1 (by norm_num)
    have : 0 < 1 - 1 / (p : ℝ) ^ (1 / 2 : ℝ) := by linarith
    positivity
  have hdvd : (∏ p ∈ g.primeFactors, p) ≤ g :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hg) (Nat.prod_primeFactors_dvd g)
  have h2pow' : 2 ^ g.primeFactors.card ≤ ∏ p ∈ g.primeFactors, p :=
    Finset.pow_card_le_prod _ _ _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  have h2pow : (2 : ℝ) ^ g.primeFactors.card ≤ ∏ p ∈ g.primeFactors, (p : ℝ) := by
    rw [← Nat.cast_prod]; exact_mod_cast h2pow'
  have hprodg : ∏ p ∈ g.primeFactors, (p : ℝ) ≤ g := by
    rw [← Nat.cast_prod]; exact_mod_cast hdvd
  calc ∏ p ∈ g.primeFactors, (1 - 1 / (p : ℝ) ^ (1 / 2 : ℝ))⁻¹
      ≤ ∏ p ∈ g.primeFactors, (4 : ℝ) := Finset.prod_le_prod₀ hnn h1
    _ = ((2 : ℝ) ^ g.primeFactors.card) ^ 2 := by
        rw [Finset.prod_const, ← pow_mul, mul_comm, pow_mul]; norm_num
    _ ≤ (g : ℝ) ^ 2 := by
        have : 0 ≤ (2 : ℝ) ^ g.primeFactors.card := by positivity
        gcongr
        exact h2pow.trans hprodg

end MobiusSums
end MobiusDeterminant
