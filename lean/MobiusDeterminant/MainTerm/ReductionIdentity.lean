import MobiusDeterminant.Basic

/-!
# Exact reduction of the main-term sum

We prove the exact identity

  `mainSum R = ∑_{g ≤ R} μ(g)^2 h(g) / g^2 · S_g(R/g)^2`,

where `h(g) = ∏_{p ∣ g} (if p = 2 then 1 else -1)`.
-/

open Finset Real
open scoped ArithmeticFunction.Moebius

namespace MobiusDeterminant

namespace Reduction

/-- `hsign p = 1` if `p = 2`, and `-1` otherwise. -/
noncomputable def hsign (p : ℕ) : ℝ := if p = 2 then 1 else -1

/-- `hfun g = ∏_{p ∣ g} hsign p`. -/
noncomputable def hfun (g : ℕ) : ℝ := ∏ p ∈ g.primeFactors, hsign p

lemma hfun_mul_of_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    hfun (m * n) = hfun m * hfun n := by
  unfold hfun
  rw [h.primeFactors_mul, prod_union h.disjoint_primeFactors]

lemma abs_hfun (g : ℕ) : |hfun g| = 1 := by
  unfold hfun
  rw [abs_prod]
  apply prod_eq_one
  intro p _
  unfold hsign
  split_ifs <;> simp

/-- For squarefree `m`, `∑_{g ∣ m} h(g) = m` if `m ∣ 2` and `0` otherwise. -/
lemma sum_divisors_hfun {m : ℕ} (hm : Squarefree m) :
    ∑ g ∈ m.divisors, hfun g = if m ∣ 2 then (m : ℝ) else 0 := by
  have hmult := ArithmeticFunction.IsMultiplicative.prodPrimeFactors (R := ℝ) hsign
  have key := hmult.prodPrimeFactors_one_add_of_squarefree hm
  have h1 : ∑ g ∈ m.divisors, hfun g =
      ∑ d ∈ m.divisors, ArithmeticFunction.prodPrimeFactors hsign d := by
    apply sum_congr rfl
    intro d hd
    rw [ArithmeticFunction.prodPrimeFactors_apply (Nat.pos_of_mem_divisors hd).ne']
    rfl
  rw [h1, ← key]
  have h2 : ∀ p ∈ m.primeFactors,
      (1 + ArithmeticFunction.prodPrimeFactors hsign p) = 1 + hsign p := by
    intro p hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    rw [ArithmeticFunction.prodPrimeFactors_apply hp'.ne_zero, hp'.primeFactors,
      prod_singleton]
  rw [prod_congr rfl h2]
  by_cases hex : ∃ p ∈ m.primeFactors, p ≠ 2
  · obtain ⟨p, hp, hp2⟩ := hex
    rw [prod_eq_zero hp (by simp [hsign, hp2])]
    have : ¬ m ∣ 2 := by
      intro hdvd
      rcases (Nat.dvd_prime Nat.prime_two).mp ((Nat.dvd_of_mem_primeFactors hp).trans hdvd)
        with h | h
      · exact (Nat.prime_of_mem_primeFactors hp).one_lt.ne' h
      · exact hp2 h
    simp [this]
  · push Not at hex
    have hsub : m.primeFactors ⊆ {2} := fun p hp => mem_singleton.mpr (hex p hp)
    rcases Finset.subset_singleton_iff.mp hsub with h | h
    · have : m = 1 := by
        rcases Nat.primeFactors_eq_empty.mp h with h0 | h1
        · exact absurd h0 hm.ne_zero
        · exact h1
      subst this
      simp
    · have hm2 : m = 2 := by
        rw [← Nat.prod_primeFactors_of_squarefree hm, h, prod_singleton]
      rw [h]
      subst hm2
      simp [hsign]
      norm_num

/-- For squarefree `d, e`: `dens d e = (∑_{g ∣ gcd(d,e)} h(g)) / (d e)`. -/
lemma dens_eq_of_squarefree {d e : ℕ} (hd : Squarefree d) (he : Squarefree e) :
    dens d e = (∑ g ∈ (Nat.gcd d e).divisors, hfun g) / ((d : ℝ) * e) := by
  have hm : Squarefree (Nat.gcd d e) := hd.squarefree_of_dvd (Nat.gcd_dvd_left d e)
  rw [sum_divisors_hfun hm, dens]
  split_ifs with h
  · have hgl : (Nat.gcd d e : ℝ) * (Nat.lcm d e) = d * e := by
      exact_mod_cast Nat.gcd_mul_lcm d e
    have hl : (Nat.lcm d e : ℝ) ≠ 0 := by
      exact_mod_cast Nat.lcm_ne_zero hd.ne_zero he.ne_zero
    have hg : (Nat.gcd d e : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.gcd_pos_of_pos_left e (Nat.pos_of_ne_zero hd.ne_zero)).ne'
    rw [← hgl]
    field_simp
  · simp

lemma moebius_mul_dens (d e : ℕ) :
    (μ d : ℝ) * (μ e : ℝ) * dens d e =
      (μ d : ℝ) * (μ e : ℝ) * ((∑ g ∈ (Nat.gcd d e).divisors, hfun g) / ((d : ℝ) * e)) := by
  by_cases hd : Squarefree d
  · by_cases he : Squarefree e
    · rw [dens_eq_of_squarefree hd he]
    · simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree he]
  · simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd]

/-- The basic term `A_R(d) = μ(d) log(R/d) / d`. -/
noncomputable def Aterm (R : ℝ) (d : ℕ) : ℝ := (μ d : ℝ) * Real.log (R / d) / d

lemma divisors_gcd_eq_filter {K d e : ℕ} (hd : d ∈ Icc 1 K) (_he : e ∈ Icc 1 K) :
    (Icc 1 K).filter (fun g => g ∣ d ∧ g ∣ e) = (Nat.gcd d e).divisors := by
  rw [mem_Icc] at hd
  ext g
  simp only [mem_filter, mem_Icc, Nat.mem_divisors, Nat.dvd_gcd_iff]
  constructor
  · rintro ⟨_, h1, h2⟩
    exact ⟨⟨h1, h2⟩, (Nat.gcd_pos_of_pos_left e (by omega)).ne'⟩
  · rintro ⟨⟨h1, h2⟩, _⟩
    refine ⟨⟨Nat.pos_of_dvd_of_pos h1 (by omega), ?_⟩, h1, h2⟩
    exact (Nat.le_of_dvd (by omega) h1).trans hd.2

lemma mainSum_term_eq (R : ℝ) {K d e : ℕ} (hd : d ∈ Icc 1 K) (he : e ∈ Icc 1 K) :
    (μ d : ℝ) * (μ e : ℝ) * Real.log (R / d) * Real.log (R / e) * dens d e =
      ∑ g ∈ Icc 1 K, hfun g * ((if g ∣ d then Aterm R d else 0) *
        (if g ∣ e then Aterm R e else 0)) := by
  have h1 : ∀ g ∈ Icc 1 K, hfun g * ((if g ∣ d then Aterm R d else 0) *
        (if g ∣ e then Aterm R e else 0)) =
        if (g ∣ d ∧ g ∣ e) then hfun g * (Aterm R d * Aterm R e) else 0 := by
    intro g _
    by_cases h1 : g ∣ d <;> by_cases h2 : g ∣ e <;> simp [h1, h2]
  rw [sum_congr rfl h1, ← sum_filter, divisors_gcd_eq_filter hd he, ← sum_mul]
  have hm := moebius_mul_dens d e
  have hd0 : (d : ℝ) ≠ 0 := by
    have := (mem_Icc.mp hd).1
    exact_mod_cast (show d ≠ 0 by omega)
  have he0 : (e : ℝ) ≠ 0 := by
    have := (mem_Icc.mp he).1
    exact_mod_cast (show e ≠ 0 by omega)
  calc (μ d : ℝ) * (μ e : ℝ) * Real.log (R / d) * Real.log (R / e) * dens d e
      = ((μ d : ℝ) * (μ e : ℝ) * dens d e) * Real.log (R / d) * Real.log (R / e) := by ring
    _ = _ := by
      rw [hm, Aterm, Aterm]
      field_simp

/-- `T_R(g) = ∑_{d ≤ K, g ∣ d} A_R(d)`. -/
lemma mainSum_eq_sum_T (R : ℝ) :
    mainSum R = ∑ g ∈ Icc 1 ⌊R⌋₊, hfun g *
      (∑ d ∈ Icc 1 ⌊R⌋₊, if g ∣ d then Aterm R d else 0) ^ 2 := by
  unfold mainSum
  rw [sum_congr rfl (fun d hd => sum_congr rfl (fun e he => mainSum_term_eq R hd he))]
  rw [sum_congr rfl (fun d _ => sum_comm), sum_comm]
  apply sum_congr rfl
  intro g _
  rw [sq, sum_mul_sum, mul_sum]
  apply sum_congr rfl
  intro d _
  rw [mul_sum]

lemma filter_dvd_Icc_eq_image (K g : ℕ) (hg : 1 ≤ g) :
    (Icc 1 K).filter (fun d => g ∣ d) = (Icc 1 (K / g)).image (fun d' => g * d') := by
  ext d
  simp only [mem_filter, mem_Icc, mem_image]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨k, rfl⟩⟩
    refine ⟨k, ⟨?_, ?_⟩, rfl⟩
    · rcases Nat.eq_zero_or_pos k with h | h
      · subst h; simp at h1
      · exact h
    · rw [Nat.le_div_iff_mul_le hg, mul_comm]; exact h2
  · rintro ⟨k, ⟨h1, h2⟩, rfl⟩
    refine ⟨⟨?_, ?_⟩, dvd_mul_right g k⟩
    · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    · rw [Nat.le_div_iff_mul_le hg, mul_comm] at h2; exact h2

lemma Aterm_mul (R : ℝ) {g k : ℕ} (hg : 1 ≤ g) (hk : 1 ≤ k) :
    Aterm R (g * k) = if Nat.Coprime k g then
      (μ g : ℝ) / g * ((μ k : ℝ) * Real.log (R / g / k) / k) else 0 := by
  have hg0 : (g : ℝ) ≠ 0 := by exact_mod_cast (show g ≠ 0 by omega)
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  split_ifs with h
  · rw [Aterm, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h.symm]
    push_cast
    rw [div_div]
    field_simp
  · have : ¬ Squarefree (g * k) := by
      rw [Nat.squarefree_mul_iff]
      rintro ⟨hc, _, _⟩
      exact h hc.symm
    simp [Aterm, ArithmeticFunction.moebius_eq_zero_of_not_squarefree this]

lemma T_eq_Sg (R : ℝ) {g : ℕ} (hg : 1 ≤ g) :
    (∑ d ∈ Icc 1 ⌊R⌋₊, if g ∣ d then Aterm R d else 0) =
      (μ g : ℝ) / g * Sg g (R / g) := by
  rw [← sum_filter, filter_dvd_Icc_eq_image _ _ hg,
    sum_image (fun x _ y _ hxy => Nat.eq_of_mul_eq_mul_left (by omega) hxy)]
  rw [Sg, Nat.floor_div_natCast, mul_sum, sum_filter]
  apply sum_congr rfl
  intro k hk
  rw [Aterm_mul R hg (mem_Icc.mp hk).1]

/-- **Exact reduction**: `mainSum R = ∑_{g ≤ R} μ(g)^2 h(g)/g^2 · S_g(R/g)^2`. -/
theorem mainSum_eq_sum_Sg (R : ℝ) :
    mainSum R = ∑ g ∈ Icc 1 ⌊R⌋₊,
      (μ g : ℝ) ^ 2 * hfun g / (g : ℝ) ^ 2 * (Sg g (R / g)) ^ 2 := by
  rw [mainSum_eq_sum_T]
  apply sum_congr rfl
  intro g hg
  rw [T_eq_Sg R (mem_Icc.mp hg).1]
  ring

end Reduction

end MobiusDeterminant
