import MobiusDeterminant.Basic
import MobiusDeterminant.MainTerm.ReductionIdentity
import MobiusDeterminant.MainTerm.ReductionSeries

/-!
# From `SgAsymp` to `MainTermAsymp`

Using the exact identity `mainSum R = ∑_{g ≤ R} μ(g)^2 h(g)/g^2 · S_g(R/g)^2`
(`mainSum_eq_sum_Sg`) and the singular series `twinConstant = ∑' g, μ(g)^2 h(g)/φ(g)^2`
(`twinConstant_eq_tsum_sfun`), we deduce the main-term asymptotic from the uniform
asymptotic for `S_g`.
-/

open Finset Real
open scoped ArithmeticFunction.Moebius

namespace MobiusDeterminant

namespace Reduction

/-- The coefficient `μ(g)^2 h(g) / g^2`. -/
noncomputable def acoef (g : ℕ) : ℝ := (μ g : ℝ) ^ 2 * hfun g / (g : ℝ) ^ 2

lemma mainSum_eq_sum_acoef (R : ℝ) :
    mainSum R = ∑ g ∈ Icc 1 ⌊R⌋₊, acoef g * (Sg g (R / g)) ^ 2 :=
  mainSum_eq_sum_Sg R

lemma moebius_sq_le_one (n : ℕ) : (μ n : ℝ) ^ 2 ≤ 1 := by
  have h : |(μ n : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  nlinarith [abs_nonneg (μ n : ℝ), sq_abs (μ n : ℝ)]

lemma abs_acoef_le_inv_sq (g : ℕ) : |acoef g| ≤ 1 / (g : ℝ) ^ 2 := by
  unfold acoef
  rw [abs_div, abs_mul, abs_hfun, mul_one, abs_of_nonneg (sq_nonneg _),
    abs_of_nonneg (sq_nonneg _)]
  exact div_le_div_of_nonneg_right (moebius_sq_le_one g) (sq_nonneg _)

lemma abs_acoef_le_wfun {g : ℕ} (hg : 1 ≤ g) : |acoef g| ≤ wfun g := by
  unfold acoef wfun
  rw [abs_div, abs_mul, abs_hfun, mul_one, abs_of_nonneg (sq_nonneg _),
    abs_of_nonneg (sq_nonneg _)]
  have hφ : (0 : ℝ) < Nat.totient g := by exact_mod_cast Nat.totient_pos.mpr hg
  have hφg : (Nat.totient g : ℝ) ≤ g := by exact_mod_cast Nat.totient_le g
  exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (pow_le_pow_left₀ hφ.le hφg 2)

lemma sfun_eq_acoef_mul {g : ℕ} (hg : 1 ≤ g) :
    sfun g = acoef g * ((g : ℝ) / Nat.totient g) ^ 2 := by
  have hφ : (Nat.totient g : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hg).ne'
  have hg0 : (g : ℝ) ≠ 0 := by exact_mod_cast (show g ≠ 0 by omega)
  unfold sfun acoef
  field_simp

/-! ### Trivial bound for `S_g` -/

lemma sum_inv_Icc_le (n : ℕ) : ∑ d ∈ Icc 1 n, (d : ℝ)⁻¹ ≤ 1 + Real.log n := by
  have := harmonic_le_one_add_log n
  rw [harmonic_eq_sum_Icc] at this
  push_cast at this
  exact this

lemma abs_Sg_le (g : ℕ) {y : ℝ} (hy : 1 ≤ y) : |Sg g y| ≤ (1 + Real.log y) ^ 2 := by
  unfold Sg
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg hy
  calc |∑ d ∈ (Icc 1 ⌊y⌋₊).filter (fun d => Nat.Coprime d g),
          (μ d : ℝ) * Real.log (y / d) / d|
      ≤ ∑ d ∈ (Icc 1 ⌊y⌋₊).filter (fun d => Nat.Coprime d g),
          |(μ d : ℝ) * Real.log (y / d) / d| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Icc 1 ⌊y⌋₊, |(μ d : ℝ) * Real.log (y / d) / d| :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => abs_nonneg _)
    _ ≤ ∑ d ∈ Icc 1 ⌊y⌋₊, Real.log y * (d : ℝ)⁻¹ := by
        apply sum_le_sum
        intro d hd
        have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (mem_Icc.mp hd).1
        have hdy : (d : ℝ) ≤ y :=
          (Nat.cast_le.mpr (mem_Icc.mp hd).2).trans (Nat.floor_le (by linarith))
        have hd0 : (0 : ℝ) < d := by linarith
        have hμ : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        have hl0 : 0 ≤ Real.log (y / d) :=
          Real.log_nonneg (by rw [le_div_iff₀ hd0]; linarith)
        have hl1 : Real.log (y / d) ≤ Real.log y := by
          rw [Real.log_div (by linarith) hd0.ne']; linarith [Real.log_nonneg hd1]
        rw [abs_div, abs_mul, abs_of_nonneg hl0, abs_of_pos hd0, div_eq_mul_inv]
        gcongr
        calc |(μ d : ℝ)| * Real.log (y / d) ≤ 1 * Real.log y :=
              mul_le_mul hμ hl1 hl0 zero_le_one
          _ = Real.log y := one_mul _
    _ = Real.log y * ∑ d ∈ Icc 1 ⌊y⌋₊, (d : ℝ)⁻¹ := by rw [mul_sum]
    _ ≤ Real.log y * (1 + Real.log y) := by
        gcongr
        refine (sum_inv_Icc_le _).trans ?_
        have h1 : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast hy)
        have h1' : (0 : ℝ) < ⌊y⌋₊ := by exact_mod_cast h1
        gcongr
        exact Nat.floor_le (by linarith)
    _ ≤ (1 + Real.log y) ^ 2 := by nlinarith

lemma Sg_sq_le {g : ℕ} (hg : 1 ≤ g) {R : ℝ} (hgR : (g : ℝ) ≤ R) :
    (Sg g (R / g)) ^ 2 ≤ (1 + Real.log R) ^ 4 := by
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hy : 1 ≤ R / g := by rw [le_div_iff₀ (by linarith)]; linarith
  have hlog : Real.log (R / g) ≤ Real.log R := by
    rw [Real.log_div (by linarith) (by linarith)]; linarith [Real.log_nonneg hg1]
  have hlog0 : 0 ≤ Real.log (R / g) := Real.log_nonneg hy
  have hSb := abs_Sg_le g hy
  calc (Sg g (R / g)) ^ 2 = |Sg g (R / g)| ^ 2 := (sq_abs _).symm
    _ ≤ ((1 + Real.log (R / g)) ^ 2) ^ 2 := by gcongr
    _ ≤ ((1 + Real.log R) ^ 2) ^ 2 := by gcongr
    _ = (1 + Real.log R) ^ 4 := by ring

/-! ### Pointwise error bounds -/

lemma small_term_bound {c C : ℝ} (hC : 0 < C)
    (hS : ∀ g : ℕ, 1 ≤ g → ∀ y : ℝ, 2 ≤ y →
      |Sg g y - (g : ℝ) / (Nat.totient g : ℝ)|
        ≤ C * (g : ℝ) ^ 3 * Real.exp (-c * Real.sqrt (Real.log y)))
    (hc : 0 < c) {g : ℕ} (hg : 1 ≤ g) {y : ℝ} (hy : 2 ≤ y) :
    |acoef g * (Sg g y) ^ 2 - sfun g|
      ≤ C * (C + 2) * (g : ℝ) ^ 4 * Real.exp (-c * Real.sqrt (Real.log y)) := by
  set S := Sg g y
  set t := (g : ℝ) / Nat.totient g with ht
  set ε := Real.exp (-c * Real.sqrt (Real.log y)) with hε
  have hε0 : 0 < ε := Real.exp_pos _
  have hε1 : ε ≤ 1 := by
    rw [hε, Real.exp_le_one_iff]
    nlinarith [Real.sqrt_nonneg (Real.log y)]
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hφ : (1 : ℝ) ≤ Nat.totient g := by exact_mod_cast Nat.totient_pos.mpr hg
  have ht0 : 0 ≤ t := by positivity
  have htg : t ≤ g := by
    rw [ht, div_le_iff₀ (by linarith)]; nlinarith
  have hdiff : |S - t| ≤ C * (g : ℝ) ^ 3 * ε := hS g hg y hy
  have hg3 : (g : ℝ) ≤ (g : ℝ) ^ 3 := le_self_pow₀ hg1 (by norm_num)
  have hsum : |S + t| ≤ (C + 2) * (g : ℝ) ^ 3 := by
    have h1 : |S + t| ≤ |S - t| + |2 * t| := by
      have : S + t = (S - t) + 2 * t := by ring
      rw [this]; exact abs_add_le _ _
    rw [abs_of_nonneg (by positivity : 0 ≤ 2 * t)] at h1
    have h2 : C * (g : ℝ) ^ 3 * ε ≤ C * (g : ℝ) ^ 3 :=
      mul_le_of_le_one_right (by positivity) hε1
    nlinarith
  rw [sfun_eq_acoef_mul hg]
  have : acoef g * S ^ 2 - acoef g * t ^ 2 = acoef g * ((S - t) * (S + t)) := by ring
  rw [this, abs_mul, abs_mul]
  have ha := abs_acoef_le_inv_sq g
  have hg0 : (0 : ℝ) < g := by linarith
  calc |acoef g| * (|S - t| * |S + t|)
      ≤ (1 / (g : ℝ) ^ 2) * ((C * (g : ℝ) ^ 3 * ε) * ((C + 2) * (g : ℝ) ^ 3)) := by
        gcongr
    _ = C * (C + 2) * (g : ℝ) ^ 4 * ε := by field_simp

lemma large_term_bound {g : ℕ} (hg : 1 ≤ g) {R : ℝ} (hgR : (g : ℝ) ≤ R) :
    |acoef g * (Sg g (R / g)) ^ 2 - sfun g| ≤ wfun g * ((1 + Real.log R) ^ 4 + 1) := by
  calc |acoef g * (Sg g (R / g)) ^ 2 - sfun g|
      ≤ |acoef g * (Sg g (R / g)) ^ 2| + |sfun g| := abs_sub _ _
    _ = |acoef g| * (Sg g (R / g)) ^ 2 + wfun g := by
        rw [abs_mul, abs_of_nonneg (sq_nonneg (Sg g (R / g))), abs_sfun]
    _ ≤ wfun g * (1 + Real.log R) ^ 4 + wfun g :=
        add_le_add_left (mul_le_mul (abs_acoef_le_wfun hg) (Sg_sq_le hg hgR) (sq_nonneg _)
          (wfun_nonneg g)) _
    _ = wfun g * ((1 + Real.log R) ^ 4 + 1) := by ring

/-! ### Rankin bounds for the tails -/

/-- `M = ∑' n, n^{1/4} μ(n)^2/φ(n)^2`. -/
noncomputable def rankinConst : ℝ := ∑' n : ℕ, (n : ℝ) ^ ((1 : ℝ) / 4) * wfun n

lemma rankinConst_nonneg : 0 ≤ rankinConst :=
  tsum_nonneg (fun n => mul_nonneg (by positivity) (wfun_nonneg n))

lemma wfun_le_rankin {G : ℝ} (hG : 0 < G) {g : ℕ} (hgG : G < g) :
    wfun g ≤ (G ^ ((1 : ℝ) / 4))⁻¹ * ((g : ℝ) ^ ((1 : ℝ) / 4) * wfun g) := by
  have hGp : 0 < G ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hG _
  have hle : G ^ ((1 : ℝ) / 4) ≤ (g : ℝ) ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow hG.le hgG.le (by norm_num)
  rw [← div_eq_inv_mul, le_div_iff₀ hGp]
  nlinarith [mul_le_mul_of_nonneg_right hle (wfun_nonneg g)]

lemma sum_wfun_le_rankin {G : ℝ} (hG : 0 < G) (t : Finset ℕ) (ht : ∀ g ∈ t, G < g) :
    ∑ g ∈ t, wfun g ≤ (G ^ ((1 : ℝ) / 4))⁻¹ * rankinConst := by
  calc ∑ g ∈ t, wfun g
      ≤ ∑ g ∈ t, (G ^ ((1 : ℝ) / 4))⁻¹ * ((g : ℝ) ^ ((1 : ℝ) / 4) * wfun g) :=
        sum_le_sum (fun g hg => wfun_le_rankin hG (ht g hg))
    _ = (G ^ ((1 : ℝ) / 4))⁻¹ * ∑ g ∈ t, ((g : ℝ) ^ ((1 : ℝ) / 4) * wfun g) := by
        rw [mul_sum]
    _ ≤ (G ^ ((1 : ℝ) / 4))⁻¹ * rankinConst := by
        gcongr
        exact summable_rankin_wfun.sum_le_tsum t
          (fun i _ => mul_nonneg (by positivity) (wfun_nonneg i))

lemma tail_bound {G : ℝ} (hG : 0 < G) (s : Finset ℕ) (hs : ∀ g ∉ s, g ≠ 0 → G < g) :
    |∑' n, sfun n - ∑ g ∈ s, sfun g| ≤ (G ^ ((1 : ℝ) / 4))⁻¹ * rankinConst := by
  set u : ℕ → ℝ := fun g => if g ∈ s then 0 else sfun g with hu
  have h1 : HasSum (fun g => if g ∈ s then sfun g else 0) (∑ g ∈ s, sfun g) := by
    rw [show ∑ g ∈ s, sfun g = ∑ g ∈ s, (if g ∈ s then sfun g else 0) from
      sum_congr rfl (fun g hg => by simp [hg])]
    exact hasSum_sum_of_ne_finset_zero (fun b hb => by simp [hb])
  have h2 : HasSum u (∑' n, sfun n - ∑ g ∈ s, sfun g) := by
    have := summable_sfun.hasSum.sub h1
    convert this using 1
    funext g
    simp only [u]
    split_ifs <;> simp
  rw [← h2.tsum_eq, ← Real.norm_eq_abs]
  have hB : HasSum (fun n : ℕ => (G ^ ((1 : ℝ) / 4))⁻¹ * ((n : ℝ) ^ ((1 : ℝ) / 4) * wfun n))
      ((G ^ ((1 : ℝ) / 4))⁻¹ * rankinConst) :=
    summable_rankin_wfun.hasSum.mul_left _
  refine tsum_of_norm_bounded hB (fun i => ?_)
  simp only [u, Real.norm_eq_abs]
  split_ifs with hi
  · rw [abs_zero]
    exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (wfun_nonneg i))
  · by_cases h0 : i = 0
    · subst h0
      rw [sfun_zero, abs_zero]
      exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (wfun_nonneg 0))
    · rw [abs_sfun]
      exact wfun_le_rankin hG (hs i hi h0)

/-! ### Decomposition of the error -/

lemma mainSum_sub_twinConstant (R G : ℝ) :
    mainSum R - twinConstant =
      ∑ g ∈ (Icc 1 ⌊R⌋₊).filter (fun g : ℕ => (g : ℝ) ≤ G), (acoef g * (Sg g (R / g)) ^ 2 - sfun g)
      + ∑ g ∈ (Icc 1 ⌊R⌋₊).filter (fun g : ℕ => ¬ (g : ℝ) ≤ G),
          (acoef g * (Sg g (R / g)) ^ 2 - sfun g)
      - (∑' n, sfun n - ∑ g ∈ Icc 1 ⌊R⌋₊, sfun g) := by
  rw [sum_filter_add_sum_filter_not, sum_sub_distrib, mainSum_eq_sum_acoef,
    twinConstant_eq_tsum_sfun]
  ring

lemma small_sum_bound {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hS : ∀ g : ℕ, 1 ≤ g → ∀ y : ℝ, 2 ≤ y →
      |Sg g y - (g : ℝ) / (Nat.totient g : ℝ)|
        ≤ C * (g : ℝ) ^ 3 * Real.exp (-c * Real.sqrt (Real.log y)))
    {R G X : ℝ} (hG : 1 ≤ G) (hX : 0 ≤ X)
    (hRG : ∀ g : ℕ, 1 ≤ g → (g : ℝ) ≤ G →
      2 ≤ R / g ∧ Real.exp (-c * Real.sqrt (Real.log (R / g))) ≤ X) :
    |∑ g ∈ (Icc 1 ⌊R⌋₊).filter (fun g : ℕ => (g : ℝ) ≤ G), (acoef g * (Sg g (R / g)) ^ 2 - sfun g)|
      ≤ G * (C * (C + 2) * G ^ 4 * X) := by
  set s := (Icc 1 ⌊R⌋₊).filter (fun g : ℕ => (g : ℝ) ≤ G) with hs
  have hcard : (s.card : ℝ) ≤ G := by
    have hsub : s ⊆ Icc 1 ⌊G⌋₊ := by
      intro g hg
      rw [hs, mem_filter, mem_Icc] at hg
      rw [mem_Icc]
      exact ⟨hg.1.1, Nat.le_floor hg.2⟩
    have := card_le_card hsub
    rw [Nat.card_Icc] at this
    calc (s.card : ℝ) ≤ (⌊G⌋₊ : ℝ) := by exact_mod_cast (by omega : s.card ≤ ⌊G⌋₊)
      _ ≤ G := Nat.floor_le (by linarith)
  calc |∑ g ∈ s, (acoef g * (Sg g (R / g)) ^ 2 - sfun g)|
      ≤ ∑ g ∈ s, |acoef g * (Sg g (R / g)) ^ 2 - sfun g| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ g ∈ s, C * (C + 2) * G ^ 4 * X := by
        apply sum_le_sum
        intro g hg
        rw [hs, mem_filter, mem_Icc] at hg
        have hg1 := hg.1.1
        obtain ⟨h2, hX'⟩ := hRG g hg1 hg.2
        refine (small_term_bound hC hS hc hg1 h2).trans ?_
        have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg g
        have hgG : (g : ℝ) ≤ G := hg.2
        gcongr
    _ = s.card * (C * (C + 2) * G ^ 4 * X) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ G * (C * (C + 2) * G ^ 4 * X) := by
        gcongr

lemma large_sum_bound {R G : ℝ} (hR : 1 ≤ R) (hG : 0 < G) :
    |∑ g ∈ (Icc 1 ⌊R⌋₊).filter (fun g : ℕ => ¬ (g : ℝ) ≤ G),
        (acoef g * (Sg g (R / g)) ^ 2 - sfun g)|
      ≤ ((1 + Real.log R) ^ 4 + 1) * ((G ^ ((1 : ℝ) / 4))⁻¹ * rankinConst) := by
  set s := (Icc 1 ⌊R⌋₊).filter (fun g : ℕ => ¬ (g : ℝ) ≤ G) with hs
  calc |∑ g ∈ s, (acoef g * (Sg g (R / g)) ^ 2 - sfun g)|
      ≤ ∑ g ∈ s, |acoef g * (Sg g (R / g)) ^ 2 - sfun g| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ g ∈ s, wfun g * ((1 + Real.log R) ^ 4 + 1) := by
        apply sum_le_sum
        intro g hg
        rw [hs, mem_filter, mem_Icc] at hg
        have hgR : (g : ℝ) ≤ R :=
          (Nat.cast_le.mpr hg.1.2).trans (Nat.floor_le (by linarith))
        exact large_term_bound hg.1.1 hgR
    _ = (∑ g ∈ s, wfun g) * ((1 + Real.log R) ^ 4 + 1) := by rw [sum_mul]
    _ ≤ ((G ^ ((1 : ℝ) / 4))⁻¹ * rankinConst) * ((1 + Real.log R) ^ 4 + 1) := by
        gcongr
        exact sum_wfun_le_rankin hG _ (fun g hg => lt_of_not_ge (mem_filter.mp hg).2)
    _ = _ := mul_comm _ _

lemma abs_mainSum_le {R : ℝ} (hR : 1 ≤ R) :
    |mainSum R| ≤ (1 + Real.log R) ^ 4 * ∑' n, wfun n := by
  rw [mainSum_eq_sum_acoef]
  calc |∑ g ∈ Icc 1 ⌊R⌋₊, acoef g * (Sg g (R / g)) ^ 2|
      ≤ ∑ g ∈ Icc 1 ⌊R⌋₊, |acoef g * (Sg g (R / g)) ^ 2| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ g ∈ Icc 1 ⌊R⌋₊, wfun g * (1 + Real.log R) ^ 4 := by
        apply sum_le_sum
        intro g hg
        have hg1 := (mem_Icc.mp hg).1
        have hgR : (g : ℝ) ≤ R :=
          (Nat.cast_le.mpr (mem_Icc.mp hg).2).trans (Nat.floor_le (by linarith))
        rw [abs_mul, abs_of_nonneg (sq_nonneg (Sg g (R / g)))]
        exact mul_le_mul (abs_acoef_le_wfun hg1) (Sg_sq_le hg1 hgR) (sq_nonneg _)
          (wfun_nonneg _)
    _ = (∑ g ∈ Icc 1 ⌊R⌋₊, wfun g) * (1 + Real.log R) ^ 4 := by rw [sum_mul]
    _ ≤ (∑' n, wfun n) * (1 + Real.log R) ^ 4 := by
        gcongr
        exact summable_wfun.sum_le_tsum _ (fun i _ => wfun_nonneg i)
    _ = _ := mul_comm _ _

/-! ### Polynomial versus exponential -/

lemma poly_le_exp {γ : ℝ} (hγ : 0 < γ) {v : ℝ} (hv : 0 ≤ v) :
    (1 + v ^ 2) ^ 4 + 2 ≤
      3 * (Nat.factorial 8 : ℝ) * Real.exp γ / γ ^ 8 * Real.exp (γ * v) := by
  have h1 := Real.pow_div_factorial_le_exp (γ * (1 + v)) (by positivity) 8
  have h2 : Real.exp (γ * (1 + v)) = Real.exp γ * Real.exp (γ * v) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : (1 + v ^ 2) ^ 4 ≤ (1 + v) ^ 8 := by
    have : 1 + v ^ 2 ≤ (1 + v) ^ 2 := by nlinarith
    calc (1 + v ^ 2) ^ 4 ≤ ((1 + v) ^ 2) ^ 4 := by gcongr
      _ = (1 + v) ^ 8 := by ring
  have h4 : (1 : ℝ) ≤ (1 + v) ^ 8 := one_le_pow₀ (by linarith)
  have hf : (0 : ℝ) < Nat.factorial 8 := by positivity
  have hγ8 : (0 : ℝ) < γ ^ 8 := by positivity
  have h5 : (1 + v) ^ 8 ≤ (Nat.factorial 8 : ℝ) / γ ^ 8 * (Real.exp γ * Real.exp (γ * v)) := by
    rw [← h2, div_mul_eq_mul_div, le_div_iff₀ hγ8]
    rw [div_le_iff₀ hf, mul_pow] at h1
    linarith
  calc (1 + v ^ 2) ^ 4 + 2 ≤ 3 * (1 + v) ^ 8 := by linarith
    _ ≤ 3 * ((Nat.factorial 8 : ℝ) / γ ^ 8 * (Real.exp γ * Real.exp (γ * v))) := by gcongr
    _ = 3 * (Nat.factorial 8 : ℝ) * Real.exp γ / γ ^ 8 * Real.exp (γ * v) := by ring

/-! ### The main deduction -/

/-- For `β + 1 ≤ √(log R)` and `g ≤ exp(β √(log R))`: `R/g ≥ 2` and
`exp(-c √(log(R/g))) ≤ exp(cβ) exp(-c √(log R))`. -/
lemma small_range_hyp {c β R : ℝ} (hc : 0 < c) (hβ : 0 < β) (hR : 2 ≤ R)
    (hcase : β + 1 ≤ Real.sqrt (Real.log R)) (g : ℕ) (hg : 1 ≤ g)
    (hgG : (g : ℝ) ≤ Real.exp (β * Real.sqrt (Real.log R))) :
    2 ≤ R / g ∧ Real.exp (-c * Real.sqrt (Real.log (R / g)))
      ≤ Real.exp (c * β) * Real.exp (-c * Real.sqrt (Real.log R)) := by
  have hu0 : 0 < Real.log R := Real.log_pos (by linarith)
  have hvu : Real.sqrt (Real.log R) ^ 2 = Real.log R := Real.sq_sqrt hu0.le
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hlogg : Real.log g ≤ β * Real.sqrt (Real.log R) := by
    calc Real.log g ≤ Real.log (Real.exp (β * Real.sqrt (Real.log R))) :=
          Real.log_le_log (by linarith) hgG
      _ = β * Real.sqrt (Real.log R) := Real.log_exp _
  have hlogRg : Real.log R - β * Real.sqrt (Real.log R) ≤ Real.log (R / g) := by
    rw [Real.log_div (by linarith) (by linarith)]; linarith
  have hkey : 1 ≤ Real.log R - β * Real.sqrt (Real.log R) := by nlinarith
  constructor
  · have : Real.exp 1 ≤ R / g := by
      calc Real.exp 1 ≤ Real.exp (Real.log (R / g)) := Real.exp_le_exp.mpr (by linarith)
        _ = R / g := Real.exp_log (by positivity)
    linarith [Real.add_one_le_exp (1 : ℝ)]
  · have hsq : Real.sqrt (Real.log R) - β ≤ Real.sqrt (Real.log (R / g)) := by
      apply Real.le_sqrt_of_sq_le
      nlinarith
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith

lemma exp_algebra_one {c v C : ℝ} :
    Real.exp ((c / 10) * v) * (C * (C + 2) * Real.exp ((c / 10) * v) ^ 4 *
        (Real.exp (c * (c / 10)) * Real.exp (-c * v)))
      = C * (C + 2) * Real.exp (c * (c / 10)) * Real.exp (-(c / 2) * v) := by
  rw [← Real.exp_nat_mul]
  have : Real.exp ((c / 10) * v) * Real.exp (↑(4 : ℕ) * ((c / 10) * v)) * Real.exp (-c * v)
      = Real.exp (-(c / 2) * v) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    push_cast; ring
  rw [← this]; ring

lemma exp_algebra_two {c v : ℝ} :
    (Real.exp ((c / 10) * v) ^ ((1 : ℝ) / 4))⁻¹ = Real.exp (-(2 * (c / 80)) * v) := by
  rw [← Real.exp_mul, ← Real.exp_neg]
  congr 1
  ring

/-- The bound for large `R`. -/
lemma main_range_bound {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hS : ∀ g : ℕ, 1 ≤ g → ∀ y : ℝ, 2 ≤ y →
      |Sg g y - (g : ℝ) / (Nat.totient g : ℝ)|
        ≤ C * (g : ℝ) ^ 3 * Real.exp (-c * Real.sqrt (Real.log y)))
    {R : ℝ} (hR : 2 ≤ R) (hcase : c / 10 + 1 ≤ Real.sqrt (Real.log R)) :
    |mainSum R - twinConstant| ≤
      (C * (C + 2) * Real.exp (c * (c / 10)) +
        3 * (Nat.factorial 8 : ℝ) * Real.exp (c / 80) / (c / 80) ^ 8 * rankinConst) *
        Real.exp (-(c / 80) * Real.sqrt (Real.log R)) := by
  have hβ0 : 0 < c / 10 := by positivity
  have hγ0 : 0 < c / 80 := by positivity
  have hR1 : 1 ≤ R := by linarith
  have hR0 : 0 < R := by linarith
  have hu0 : 0 < Real.log R := Real.log_pos (by linarith)
  have hv0 : 0 ≤ Real.sqrt (Real.log R) := Real.sqrt_nonneg _
  have hvu : Real.sqrt (Real.log R) ^ 2 = Real.log R := Real.sq_sqrt hu0.le
  have hM0 : 0 ≤ rankinConst := rankinConst_nonneg
  generalize hv : Real.sqrt (Real.log R) = v at hcase hv0 hvu ⊢
  generalize hG : Real.exp ((c / 10) * v) = G
  have hG1 : 1 ≤ G := by rw [← hG]; exact Real.one_le_exp (by positivity)
  have hG0 : 0 < G := by linarith
  have hGR : G ≤ R := by
    rw [← hG, ← Real.exp_log hR0]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hRG : ∀ g : ℕ, 1 ≤ g → (g : ℝ) ≤ G →
      2 ≤ R / g ∧ Real.exp (-c * Real.sqrt (Real.log (R / g)))
        ≤ Real.exp (c * (c / 10)) * Real.exp (-c * v) := by
    intro g hg hgG
    rw [← hv]
    rw [← hG, ← hv] at hgG
    exact small_range_hyp hc hβ0 hR (by rw [hv]; exact hcase) g hg hgG
  have hsmall := small_sum_bound hc hC hS hG1 (by positivity) hRG
  have hlarge := large_sum_bound hR1 hG0
  have htail := tail_bound hG0 (Icc 1 ⌊R⌋₊) (by
    intro g hg hg0
    have hKg : ⌊R⌋₊ < g := by
      by_contra hcon
      exact hg (mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hg0, by omega⟩)
    exact lt_of_le_of_lt hGR (Nat.lt_of_floor_lt hKg))
  have hG4 : (G ^ ((1 : ℝ) / 4))⁻¹ = Real.exp (-(2 * (c / 80)) * v) := by
    rw [← hG]; exact exp_algebra_two
  have hG5 : G * (C * (C + 2) * G ^ 4 * (Real.exp (c * (c / 10)) * Real.exp (-c * v)))
      = C * (C + 2) * Real.exp (c * (c / 10)) * Real.exp (-(c / 2) * v) := by
    rw [← hG]; exact exp_algebra_one
  have hA' : C * (C + 2) * Real.exp (c * (c / 10)) * Real.exp (-(c / 2) * v)
      ≤ C * (C + 2) * Real.exp (c * (c / 10)) * Real.exp (-(c / 80) * v) := by
    gcongr
    nlinarith
  have hPexp := poly_le_exp hγ0 hv0
  have hlog4 : (1 + Real.log R) ^ 4 = (1 + v ^ 2) ^ 4 := by rw [hvu]
  have hrest : ((1 + Real.log R) ^ 4 + 1) * ((G ^ ((1 : ℝ) / 4))⁻¹ * rankinConst)
      + (G ^ ((1 : ℝ) / 4))⁻¹ * rankinConst
      ≤ 3 * (Nat.factorial 8 : ℝ) * Real.exp (c / 80) / (c / 80) ^ 8 * rankinConst *
          Real.exp (-(c / 80) * v) := by
    rw [hG4]
    have e1 : ((1 + Real.log R) ^ 4 + 1) * (Real.exp (-(2 * (c / 80)) * v) * rankinConst)
        + Real.exp (-(2 * (c / 80)) * v) * rankinConst
        = ((1 + v ^ 2) ^ 4 + 2) * rankinConst * Real.exp (-(2 * (c / 80)) * v) := by
      rw [hlog4]; ring
    rw [e1]
    have e2 : Real.exp (-(c / 80) * v)
        = Real.exp ((c / 80) * v) * Real.exp (-(2 * (c / 80)) * v) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e2]
    calc ((1 + v ^ 2) ^ 4 + 2) * rankinConst * Real.exp (-(2 * (c / 80)) * v)
        ≤ (3 * (Nat.factorial 8 : ℝ) * Real.exp (c / 80) / (c / 80) ^ 8 *
            Real.exp ((c / 80) * v)) * rankinConst * Real.exp (-(2 * (c / 80)) * v) := by
          gcongr
      _ = _ := by ring
  have h1 : |∑ g ∈ (Icc 1 ⌊R⌋₊).filter (fun g : ℕ => (g : ℝ) ≤ G),
      (acoef g * (Sg g (R / g)) ^ 2 - sfun g)|
        ≤ C * (C + 2) * Real.exp (c * (c / 10)) * Real.exp (-(c / 80) * v) :=
    (hsmall.trans_eq hG5).trans hA'
  have h2 : |∑ g ∈ (Icc 1 ⌊R⌋₊).filter (fun g : ℕ => ¬ (g : ℝ) ≤ G),
      (acoef g * (Sg g (R / g)) ^ 2 - sfun g)|
      + |∑' n, sfun n - ∑ g ∈ Icc 1 ⌊R⌋₊, sfun g|
        ≤ 3 * (Nat.factorial 8 : ℝ) * Real.exp (c / 80) / (c / 80) ^ 8 * rankinConst *
          Real.exp (-(c / 80) * v) :=
    (add_le_add hlarge htail).trans hrest
  rw [mainSum_sub_twinConstant R G]
  refine (abs_sub _ _).trans ?_
  refine (add_le_add_left (abs_add_le _ _) _).trans ?_
  rw [add_mul]
  linarith only [h1, h2]

/-- The bound for bounded `R`. -/
lemma bounded_range_bound {B R : ℝ} (hR : 2 ≤ R) (hcase : Real.sqrt (Real.log R) < B) :
    |mainSum R - twinConstant| ≤ (1 + B ^ 2) ^ 4 * (∑' n, wfun n) + |twinConstant| := by
  have hu0 : 0 < Real.log R := Real.log_pos (by linarith)
  have hvu : Real.sqrt (Real.log R) ^ 2 = Real.log R := Real.sq_sqrt hu0.le
  have hv0 : 0 ≤ Real.sqrt (Real.log R) := Real.sqrt_nonneg _
  have hub : Real.log R ≤ B ^ 2 := by rw [← hvu]; nlinarith
  have hM₀0 : 0 ≤ ∑' n, wfun n := tsum_nonneg wfun_nonneg
  calc |mainSum R - twinConstant| ≤ |mainSum R| + |twinConstant| := abs_sub _ _
    _ ≤ (1 + Real.log R) ^ 4 * (∑' n, wfun n) + |twinConstant| := by
        gcongr
        exact abs_mainSum_le (by linarith)
    _ ≤ (1 + B ^ 2) ^ 4 * (∑' n, wfun n) + |twinConstant| := by
        gcongr

end Reduction

open Reduction in
/-- **Main-term asymptotic from the `S_g` asymptotic.** -/
theorem mainTermAsymp_of_sgAsymp (h : SgAsymp) : MainTermAsymp := by
  obtain ⟨c, hc, C, hC, hS⟩ := h
  have hγ0 : 0 < c / 80 := by positivity
  have hM0 : 0 ≤ rankinConst := rankinConst_nonneg
  have hM₀0 : 0 ≤ ∑' n, wfun n := tsum_nonneg wfun_nonneg
  obtain ⟨A, hA0, hA⟩ : ∃ A : ℝ, 0 ≤ A ∧ A = C * (C + 2) * Real.exp (c * (c / 10)) +
      3 * (Nat.factorial 8 : ℝ) * Real.exp (c / 80) / (c / 80) ^ 8 * rankinConst :=
    ⟨_, by positivity, rfl⟩
  obtain ⟨D, hD0, hD⟩ : ∃ D : ℝ, 0 ≤ D ∧
      D = (1 + (c / 10 + 1) ^ 2) ^ 4 * (∑' n, wfun n) + |twinConstant| :=
    ⟨_, by positivity, rfl⟩
  refine ⟨c / 80, hγ0, A + D * Real.exp (c / 80 * (c / 10 + 1)) + 1, by positivity, ?_⟩
  intro R hR
  have hv0 : 0 ≤ Real.sqrt (Real.log R) := Real.sqrt_nonneg _
  have hEpos : 0 < Real.exp (-(c / 80) * Real.sqrt (Real.log R)) := Real.exp_pos _
  have hsplit : (A + D * Real.exp (c / 80 * (c / 10 + 1)) + 1) *
      Real.exp (-(c / 80) * Real.sqrt (Real.log R))
      = A * Real.exp (-(c / 80) * Real.sqrt (Real.log R))
        + D * (Real.exp (c / 80 * (c / 10 + 1)) *
            Real.exp (-(c / 80) * Real.sqrt (Real.log R)))
        + Real.exp (-(c / 80) * Real.sqrt (Real.log R)) := by ring
  rw [hsplit]
  have hDE : 0 ≤ D * (Real.exp (c / 80 * (c / 10 + 1)) *
      Real.exp (-(c / 80) * Real.sqrt (Real.log R))) := by positivity
  have hAE : 0 ≤ A * Real.exp (-(c / 80) * Real.sqrt (Real.log R)) := by positivity
  by_cases hcase : c / 10 + 1 ≤ Real.sqrt (Real.log R)
  · have := main_range_bound hc hC hS hR hcase
    rw [← hA] at this
    linarith only [this, hDE, hEpos]
  · push Not at hcase
    have hb := bounded_range_bound hR hcase
    rw [← hD] at hb
    have hexp : 1 ≤ Real.exp (c / 80 * (c / 10 + 1)) *
        Real.exp (-(c / 80) * Real.sqrt (Real.log R)) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      nlinarith
    have : D ≤ D * (Real.exp (c / 80 * (c / 10 + 1)) *
        Real.exp (-(c / 80) * Real.sqrt (Real.log R))) := le_mul_of_one_le_right hD0 hexp
    linarith only [this, hb, hAE, hEpos]

end MobiusDeterminant
