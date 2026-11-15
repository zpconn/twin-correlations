import MobiusDeterminant.Basic
import MobiusDeterminant.Unconditional.PNTMobiusContour

/-!
# The prime number theorem for `μ` with classical error term

`pntMobius : PNTMobius`, i.e. `|∑_{n ≤ x} μ(n)| ≤ C x exp(-c √(log x))` for `x ≥ 2`.

The proof adapts PNT+'s proof of `StrongPNT` (smoothed Chebyshev function, Mellin inversion,
contour shift into the de la Vallée Poussin zero-free region, unsmoothing) to the Dirichlet
series `1/ζ(s) = ∑ μ(n) n^{-s}`:

* `PNTMobiusInvZeta`: `1/ζ(σ+it) ≪ (1+|t|)^{1/2}` for `σ ≥ 1 - δ/log|t|`, from PNT+'s
  zero-free region `ZetaZeroFree1` and log-derivative bound
  `LogDerivZetaUniformLogSquaredBound` (Grönwall along horizontal segments);
* `PNTMobiusSmoothed`: `∑ μ(n) ν_ε(n/X) = (1/2π) ∫_{(σ₀)} (1/ζ) 𝓜(ν_ε) X^s`;
* `PNTMobiusContour`: the contour shift and the bound on the shifted contour;
* this file: unsmoothing (`|μ| ≤ 1`, so the error is the number of integers in a window of
  length `≍ εX`) and the choice `T = exp √log X`, `σ₁ = 1 - δ/√log X`,
  `σ₀ = 1 + 1/log X`, `ε = exp(-(δ/2)√log X)`.
-/

open Complex Real Set Filter Topology MeasureTheory
open scoped ArithmeticFunction.Moebius

namespace MobiusDeterminant
namespace PNTMobiusAux

/-! ## Unsmoothing -/

lemma card_filter_window (N : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (((Finset.range N).filter (fun n : ℕ => a < n ∧ (n : ℝ) < b)).card : ℝ) ≤ b - a + 2 := by
  have hsub : (Finset.range N).filter (fun n : ℕ => a < n ∧ (n : ℝ) < b) ⊆
      Finset.Ioo ⌊a⌋₊ ⌈b⌉₊ := by
    intro n hn
    simp only [Finset.mem_filter] at hn
    simp only [Finset.mem_Ioo]
    constructor
    · exact_mod_cast (Nat.floor_le ha).trans_lt hn.2.1
    · exact_mod_cast hn.2.2.trans_le (Nat.le_ceil b)
  have h1 := Finset.card_le_card hsub
  rw [Nat.card_Ioo] at h1
  have h2 : ⌊a⌋₊ ≤ ⌈b⌉₊ := (Nat.floor_le_floor hab).trans (Nat.floor_le_ceil b)
  have h3 : ((Finset.range N).filter (fun n : ℕ => a < n ∧ (n : ℝ) < b)).card + ⌊a⌋₊ ≤
      ⌈b⌉₊ := by omega
  have h4 : (((Finset.range N).filter (fun n : ℕ => a < n ∧ (n : ℝ) < b)).card : ℝ) +
      ⌊a⌋₊ ≤ ⌈b⌉₊ := by exact_mod_cast h3
  have h5 := Nat.ceil_lt_add_one (ha.trans hab)
  have h6 := Nat.lt_floor_add_one a
  linarith

lemma unsmooth_bound {ν : ℝ → ℝ} (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : Function.support ν ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), ν x / x = 1) {ε X : ℝ} (εpos : 0 < ε) (ε1 : ε < 1)
    (X_pos : 0 < X) :
    |∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (μ n : ℝ) - ∑' n : ℕ, (μ n : ℝ) * Smooth1 ν ε (n / X)| ≤
      3 * ε * X + 2 := by
  obtain ⟨c₁, c₁pos, c₁eq, hc₁⟩ := Smooth1Properties_below suppν mass_one
  obtain ⟨c₂, c₂pos, c₂eq, hc₂⟩ := Smooth1Properties_above suppν
  have hlog2 := Real.log_two_lt_d9
  have c₁le : c₁ ≤ 1 := by rw [c₁eq]; linarith
  have c₂le : c₂ ≤ 2 := by rw [c₂eq]; linarith
  set S : ℕ → ℝ := fun n => Smooth1 ν ε (n / X) with hS
  set N : ℕ := ⌊3 * X⌋₊ + 1 with hN
  set a : ℝ := (1 - c₁ * ε) * X with ha
  set b : ℝ := (1 + c₂ * ε) * X with hb
  have ha0 : 0 ≤ a := by
    have : c₁ * ε ≤ 1 := by nlinarith
    rw [ha]; nlinarith
  have hab : a ≤ b := by rw [ha, hb]; nlinarith [mul_pos c₁pos εpos, mul_pos c₂pos εpos]
  have haX : a ≤ X := by rw [ha]; nlinarith [mul_pos c₁pos εpos]
  have hbX : X < b := by rw [hb]; nlinarith [mul_pos c₂pos εpos]
  have hb3 : b < 3 * X := by
    have : c₂ * ε < 2 := by nlinarith
    rw [hb]; nlinarith [mul_lt_mul_of_pos_right this X_pos]
  -- the tsum is a finite sum over `range N`
  have hzero : ∀ n ∉ Finset.range N, (μ n : ℝ) * S n = 0 := by
    intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    have hn' : (3 * X : ℝ) < n := by
      have := Nat.lt_floor_add_one (3 * X)
      have h : ((⌊3 * X⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
      push_cast at h
      linarith
    have : S n = 0 := by
      apply hc₂ ε _ ⟨εpos, ε1⟩
      rw [le_div_iff₀ X_pos]
      linarith
    rw [this, mul_zero]
  rw [tsum_eq_sum hzero]
  have hsubset : Finset.Icc 1 ⌊X⌋₊ ⊆ Finset.range N := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    simp only [Finset.mem_range, hN]
    have : ⌊X⌋₊ ≤ ⌊3 * X⌋₊ := Nat.floor_le_floor (by linarith)
    omega
  have hsum1 : ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (μ n : ℝ) =
      ∑ n ∈ Finset.range N, (if n ∈ Finset.Icc 1 ⌊X⌋₊ then (μ n : ℝ) else 0) := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsubset]
  rw [hsum1, ← Finset.sum_sub_distrib]
  -- termwise bound by the indicator of the window `(a, b)`
  have hterm : ∀ n ∈ Finset.range N,
      |(if n ∈ Finset.Icc 1 ⌊X⌋₊ then (μ n : ℝ) else 0) - (μ n : ℝ) * S n| ≤
        if a < n ∧ (n : ℝ) < b then 1 else 0 := by
    intro n _
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · simp only [Finset.mem_Icc, ArithmeticFunction.map_zero, Int.cast_zero, zero_mul, sub_zero]
      split_ifs <;> norm_num
    have hnX : (0 : ℝ) < n / X := div_pos (by exact_mod_cast hnpos) X_pos
    have hS0 : 0 ≤ S n := Smooth1Nonneg νpos hnX εpos
    have hS1 : S n ≤ 1 := Smooth1LeOne νpos mass_one εpos hnX
    have hμ : |(μ n : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    by_cases hlo : (n : ℝ) ≤ a
    · have hmem : n ∈ Finset.Icc 1 ⌊X⌋₊ := by
        simp only [Finset.mem_Icc]
        exact ⟨hnpos, Nat.le_floor (by linarith)⟩
      have : S n = 1 := by
        apply hc₁ ε _ εpos hnX
        rw [div_le_iff₀ X_pos]; linarith
      simp only [hmem, ↓reduceIte, this, mul_one, sub_self, abs_zero]
      split_ifs <;> norm_num
    by_cases hhi : b ≤ (n : ℝ)
    · have hmem : n ∉ Finset.Icc 1 ⌊X⌋₊ := by
        simp only [Finset.mem_Icc, not_and, not_le]
        intro _
        have : (⌊X⌋₊ : ℝ) < n := (Nat.floor_le X_pos.le).trans_lt (by linarith)
        exact_mod_cast this
      have : S n = 0 := by
        apply hc₂ ε _ ⟨εpos, ε1⟩
        rw [le_div_iff₀ X_pos]; linarith
      simp only [hmem, ↓reduceIte, this, mul_zero, sub_self, abs_zero]
      split_ifs <;> norm_num
    · replace hlo := not_le.mp hlo
      replace hhi := not_le.mp hhi
      have hw : (if a < n ∧ (n : ℝ) < b then (1 : ℝ) else 0) = 1 := by simp [hlo, hhi]
      rw [hw]
      split_ifs
      · rw [← mul_one_sub, abs_mul]
        have : |1 - S n| ≤ 1 := by rw [abs_le]; constructor <;> linarith
        nlinarith [abs_nonneg (μ n : ℝ), abs_nonneg (1 - S n)]
      · rw [zero_sub, abs_neg, abs_mul, abs_of_nonneg hS0]
        nlinarith [abs_nonneg (μ n : ℝ)]
  calc |∑ n ∈ Finset.range N,
          ((if n ∈ Finset.Icc 1 ⌊X⌋₊ then (μ n : ℝ) else 0) - (μ n : ℝ) * S n)|
      ≤ ∑ n ∈ Finset.range N,
          |(if n ∈ Finset.Icc 1 ⌊X⌋₊ then (μ n : ℝ) else 0) - (μ n : ℝ) * S n| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.range N, (if a < n ∧ (n : ℝ) < b then (1 : ℝ) else 0) :=
        Finset.sum_le_sum hterm
    _ = (((Finset.range N).filter (fun n : ℕ => a < n ∧ (n : ℝ) < b)).card : ℝ) := by
        rw [Finset.card_filter]; push_cast; rfl
    _ ≤ b - a + 2 := card_filter_window N ha0 hab
    _ ≤ 3 * ε * X + 2 := by
        rw [ha, hb]; nlinarith [mul_pos εpos X_pos]

/-! ## Assembly -/

lemma smoothed_sum_bound {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν) (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : Function.support ν ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), ν x / x = 1) {X ε σ₀ : ℝ} (X_pos : 0 < X)
    (εpos : 0 < ε) (ε1 : ε < 1) (σ₀1 : 1 < σ₀) (σ₀2 : σ₀ ≤ 2) :
    |∑' n : ℕ, (μ n : ℝ) * Smooth1 ν ε (n / X)| ≤
      ‖∫ t : ℝ, mobIntegrand ν ε X (σ₀ + t * I)‖ := by
  have h := smoothedMobius_eq_integral diffν νpos suppν mass_one X_pos εpos ε1 σ₀1 σ₀2
  have hc : ((∑' n : ℕ, (μ n : ℝ) * Smooth1 ν ε (n / X) : ℝ) : ℂ) =
      ∑' n : ℕ, (μ n : ℂ) * Smooth1 ν ε (n / X) := by
    rw [ofReal_tsum]; push_cast; rfl
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hc, ← h, norm_mul]
  have hπ : ‖(1 : ℂ) / (2 * π)‖ ≤ 1 := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
    rw [div_le_one (by positivity)]
    linarith [Real.pi_gt_three]
  calc ‖(1 : ℂ) / (2 * π)‖ * ‖∫ t : ℝ, mobIntegrand ν ε X (σ₀ + t * I)‖
      ≤ 1 * ‖∫ t : ℝ, mobIntegrand ν ε X (σ₀ + t * I)‖ := by gcongr
    _ = _ := one_mul _

/-- Elementary exponential inequalities used in the final balancing. -/
lemma exp_estimates {L dl c : ℝ} (L2 : 2 ≤ L) (_dlpos : 0 < dl) (dlle : dl ≤ 1 / 2)
    (cpos : 0 < c) (c8 : c ≤ 1 / 8) (cdl : c ≤ dl / 2) :
    Real.exp (dl / 2 * L) * Real.exp (-L / 2) ≤ Real.exp (-L / 4) ∧
    L ^ 2 * Real.exp (-L / 4) ≤ 128 * Real.exp (-c * L) ∧
    Real.exp (-L / 4) ≤ Real.exp (-c * L) ∧
    Real.exp (dl / 2 * L) * Real.exp (-dl * L) ≤ Real.exp (-c * L) ∧
    Real.exp (-(dl / 2) * L) ≤ Real.exp (-c * L) ∧
    1 ≤ Real.exp (L ^ 2) * Real.exp (-c * L) := by
  have Lnn : 0 ≤ L := by linarith
  have h1 := mul_le_mul_of_nonneg_right dlle Lnn
  have h2 := mul_le_mul_of_nonneg_right c8 Lnn
  have h3 := mul_le_mul_of_nonneg_right cdl Lnn
  have h4 : 2 * L ≤ L * L := mul_le_mul_of_nonneg_right L2 Lnn
  have hcL : -L / 4 ≤ -c * L := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; linarith
  · have h := Real.pow_div_factorial_le_exp (L / 8) (by positivity) 2
    simp only [Nat.factorial_two, Nat.cast_ofNat] at h
    have h' : L ^ 2 ≤ 128 * Real.exp (L / 8) := by
      have : L ^ 2 = 128 * ((L / 8) ^ 2 / 2) := by ring
      linarith
    calc L ^ 2 * Real.exp (-L / 4) ≤ 128 * Real.exp (L / 8) * Real.exp (-L / 4) := by
          gcongr
      _ = 128 * Real.exp (-L / 8) := by rw [mul_assoc, ← Real.exp_add]; ring_nf
      _ ≤ 128 * Real.exp (-c * L) := by
          gcongr; linarith
  · exact Real.exp_le_exp.mpr hcL
  · rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; linarith
  · apply Real.exp_le_exp.mpr; linarith
  · rw [← Real.exp_add]; apply Real.one_le_exp; nlinarith

/-- The PNT for `μ` for `√(log X) ≥ L₀`. -/
theorem mertens_bound_large :
    ∃ c > 0, ∃ C > 0, ∃ L₀ > 0, ∀ X : ℝ, 2 ≤ X → L₀ ≤ √(Real.log X) →
      |∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (μ n : ℝ)| ≤ C * X * Real.exp (-c * √(Real.log X)) := by
  obtain ⟨ν, hν, hν0, hνsupp, hνmass⟩ := SmoothExistence
  have diffν : ContDiff ℝ 1 ν := hν.of_le (by simp)
  have νpos : ∀ x > 0, 0 ≤ ν x := fun x _ => hν0 x
  have mass_one : ∫ x in Ioi (0 : ℝ), ν x / x = 1 := by rwa [← integral_Ici_eq_integral_Ioi]
  obtain ⟨dl, dlpos, dlle, σ₂, hσ₂, K, Kpos, hK⟩ :=
    mobius_integral_bound diffν νpos hνsupp mass_one
  set c : ℝ := min (1 / 8) (dl / 2) with hc
  have cpos : 0 < c := by positivity
  have c8 : c ≤ 1 / 8 := min_le_left _ _
  have cdl : c ≤ dl / 2 := min_le_right _ _
  have h1σ₂ : 0 < 1 - σ₂ := by linarith
  set L₀ : ℝ := max 2 (dl / (1 - σ₂)) with hL₀
  refine ⟨c, cpos, K * (129 * Real.exp 1 + 1) + 5, by positivity, L₀, by positivity, ?_⟩
  intro X hX hL
  have X_pos : 0 < X := by linarith
  set L : ℝ := √(Real.log X) with hLdef
  have L2 : 2 ≤ L := (le_max_left _ _).trans hL
  have Lpos : 0 < L := by linarith
  have hLdl : dl / (1 - σ₂) ≤ L := (le_max_right _ _).trans hL
  have hlogX : Real.log X = L ^ 2 := (Real.sq_sqrt (Real.log_nonneg (by linarith))).symm
  have hXexp : X = Real.exp (L ^ 2) := by rw [← hlogX, Real.exp_log X_pos]
  -- parameters
  set T : ℝ := Real.exp L with hT
  set σ₁ : ℝ := 1 - dl / L with hσ₁
  set σ₀ : ℝ := 1 + 1 / L ^ 2 with hσ₀
  set ε : ℝ := Real.exp (-(dl / 2) * L) with hε
  have εpos : 0 < ε := Real.exp_pos _
  have ε1 : ε < 1 := by
    rw [hε, Real.exp_lt_one_iff]
    have : 0 < dl / 2 * L := by positivity
    linarith
  have hT3 : 3 ≤ T := by
    have := Real.add_one_le_exp L
    rw [hT]; linarith
  have hdlL : dl / L ≤ dl / 2 := div_le_div_of_nonneg_left dlpos.le (by norm_num) L2
  have hσ₁h : 1 / 2 ≤ σ₁ := by
    rw [hσ₁]
    have : dl / 2 ≤ 1 / 4 := by linarith
    linarith
  have hσ₂σ₁ : σ₂ ≤ σ₁ := by
    rw [hσ₁]
    have : dl / L ≤ 1 - σ₂ := by
      rw [div_le_iff₀ Lpos]
      have := (div_le_iff₀ h1σ₂).mp hLdl
      linarith
    linarith
  have hσ₁1 : σ₁ < 1 := by
    rw [hσ₁]; have : 0 < dl / L := by positivity
    linarith
  have hσ₁T : 1 - dl / Real.log T ≤ σ₁ := by rw [hT, Real.log_exp]
  have hL2 : 1 ≤ L ^ 2 := by nlinarith
  have hσ₀1 : 1 < σ₀ := by rw [hσ₀]; have : 0 < 1 / L ^ 2 := by positivity
                           linarith
  have hσ₀2 : σ₀ ≤ 2 := by
    rw [hσ₀]; have : 1 / L ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; exact hL2
    linarith
  have hint := hK X ε T σ₁ σ₀ (by linarith) εpos ε1 hT3 hσ₁h hσ₂σ₁ hσ₁1 hσ₁T hσ₀1 hσ₀2
  have hsm := smoothed_sum_bound diffν νpos hνsupp mass_one X_pos εpos ε1 hσ₀1 hσ₀2
  have hus := unsmooth_bound νpos hνsupp mass_one εpos ε1 X_pos
  -- evaluate the parameters
  have hXσ₀ : X ^ σ₀ = Real.exp 1 * X := by
    rw [Real.rpow_def_of_pos X_pos, hlogX, hσ₀, hXexp, ← Real.exp_add]
    congr 1; field_simp; ring
  have hXσ₁ : X ^ σ₁ = X * Real.exp (-dl * L) := by
    rw [Real.rpow_def_of_pos X_pos, hlogX, hσ₁, hXexp, ← Real.exp_add]
    congr 1; field_simp; ring
  have hσ₀' : 1 / (σ₀ - 1) = L ^ 2 := by rw [hσ₀]; field_simp; ring
  have hW : (1 + T) ^ (-(1 / 2) : ℝ) ≤ Real.exp (-L / 2) := by
    calc (1 + T) ^ (-(1 / 2) : ℝ) ≤ T ^ (-(1 / 2) : ℝ) :=
          Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) (by linarith) (by norm_num)
      _ = Real.exp (-L / 2) := by
          rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]; ring_nf
  have hWnn : 0 ≤ (1 + T) ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg (by positivity) _
  have hKε : K / ε = K * Real.exp (dl / 2 * L) := by
    rw [hε, div_eq_mul_inv, ← Real.exp_neg]; ring_nf
  -- elementary exponential inequalities
  set E : ℝ := Real.exp (-c * L) with hE
  have Epos : 0 < E := Real.exp_pos _
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := exp_estimates L2 dlpos dlle cpos c8 cdl
  rw [← hE] at e2 e3 e4 e5 e6
  rw [← hε] at e5
  rw [← hXexp] at e6
  -- the smoothed sum
  have hS : |∑' n : ℕ, (μ n : ℝ) * Smooth1 ν ε (n / X)| ≤ K * (129 * Real.exp 1 + 1) * X * E := by
    refine hsm.trans (hint.trans ?_)
    rw [hKε, hXσ₀, hXσ₁, div_eq_mul_one_div _ (σ₀ - 1), hσ₀']
    set W := (1 + T) ^ (-(1 / 2) : ℝ)
    set A := Real.exp (dl / 2 * L)
    have Apos : 0 < A := Real.exp_pos _
    have hexp1 : 0 < Real.exp 1 := Real.exp_pos _
    calc K * A * (Real.exp 1 * X * W * L ^ 2 + Real.exp 1 * X * W + X * Real.exp (-dl * L))
        ≤ K * A * (Real.exp 1 * X * Real.exp (-L / 2) * L ^ 2 +
            Real.exp 1 * X * Real.exp (-L / 2) + X * Real.exp (-dl * L)) := by
          gcongr
      _ = K * X * (Real.exp 1 * (L ^ 2 * (A * Real.exp (-L / 2))) +
            Real.exp 1 * (A * Real.exp (-L / 2)) + A * Real.exp (-dl * L)) := by ring
      _ ≤ K * X * (Real.exp 1 * (L ^ 2 * Real.exp (-L / 4)) +
            Real.exp 1 * Real.exp (-L / 4) + E) := by gcongr
      _ ≤ K * X * (Real.exp 1 * (128 * E) + Real.exp 1 * E + E) := by gcongr
      _ = K * (129 * Real.exp 1 + 1) * X * E := by ring
  -- unsmoothing
  have hU : |∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (μ n : ℝ) - ∑' n : ℕ, (μ n : ℝ) * Smooth1 ν ε (n / X)| ≤
      5 * X * E := by
    refine hus.trans ?_
    nlinarith
  calc |∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (μ n : ℝ)|
      = |(∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (μ n : ℝ) - ∑' n : ℕ, (μ n : ℝ) * Smooth1 ν ε (n / X)) +
          ∑' n : ℕ, (μ n : ℝ) * Smooth1 ν ε (n / X)| := by rw [sub_add_cancel]
    _ ≤ |∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (μ n : ℝ) - ∑' n : ℕ, (μ n : ℝ) * Smooth1 ν ε (n / X)| +
          |∑' n : ℕ, (μ n : ℝ) * Smooth1 ν ε (n / X)| := abs_add_le _ _
    _ ≤ 5 * X * E + K * (129 * Real.exp 1 + 1) * X * E := add_le_add hU hS
    _ = (K * (129 * Real.exp 1 + 1) + 5) * X * Real.exp (-c * L) := by rw [hE]; ring

end PNTMobiusAux

open PNTMobiusAux in
/-- **The prime number theorem for the Möbius function** with the classical
de la Vallée Poussin error term:
`|∑_{n ≤ x} μ(n)| ≤ C x exp(-c √(log x))` for `x ≥ 2`. -/
theorem pntMobius : PNTMobius := by
  obtain ⟨c, cpos, C, Cpos, L₀, L₀pos, h⟩ := mertens_bound_large
  refine ⟨c, cpos, max C (Real.exp (c * L₀)), by positivity, fun x hx => ?_⟩
  have xpos : 0 < x := by linarith
  by_cases hL : L₀ ≤ √(Real.log x)
  · refine (h x hx hL).trans ?_
    gcongr
    exact le_max_left _ _
  · replace hL := not_le.mp hL
    have htriv : |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (μ n : ℝ)| ≤ x := by
      calc |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (μ n : ℝ)| ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, |(μ n : ℝ)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (1 : ℝ) := by
            apply Finset.sum_le_sum; intro n _
            exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        _ = ⌊x⌋₊ := by simp
        _ ≤ x := Nat.floor_le xpos.le
    have h1 : 1 ≤ Real.exp (c * L₀) * Real.exp (-c * √(Real.log x)) := by
      rw [← Real.exp_add]; apply Real.one_le_exp; nlinarith
    calc |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (μ n : ℝ)| ≤ x := htriv
      _ ≤ Real.exp (c * L₀) * x * Real.exp (-c * √(Real.log x)) := by nlinarith
      _ ≤ max C (Real.exp (c * L₀)) * x * Real.exp (-c * √(Real.log x)) := by
          gcongr; exact le_max_right _ _

end MobiusDeterminant
