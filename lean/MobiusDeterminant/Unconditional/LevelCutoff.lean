import MobiusDeterminant.Unconditional.LevelDefs

/-!
# Cutoff functions for the smoothing step (paper §8, proof of Theorem 1.2)

Elementary facts about `dyBump`, `topCut` and `piece`:

* `0 ≤ dyBump ≤ 1`, `dyBump = 0` outside `(1/2, 2)`;
* `0 ≤ topCut ≤ 1`, `topCut K ν x = 1` for `x ≤ (1-ν)K`, `= 0` for `x ≥ K`;
* telescoping `∑_{a < J} dyBump (x/2^a) = st(2x - 1) - st(2(x/2^J) - 1)`;
* `∑_{a < J} piece K ν (2^a) (x/2^a) = topCut K ν x` for `x ≥ 1`, `K ≤ 2^J/2`;
* the `n`-cutoff `psiCut N ν j₀ J x = ∑_{j₀ ≤ l < J} dyBump (x/2^l) topCut N ν x` and its
  values;
* `‖∑_{j₀ ≤ l < J} 2^l ψ̂_l(0) - N‖ ≤ 2^{j₀} + νN` for `ψ_l = piece N ν 2^l`.
-/

open Finset Real MeasureTheory

namespace MobiusDeterminant

namespace Level

namespace Cutoff

/-! ## `dyBump` -/

theorem dyBump_nonneg (y : ℝ) : 0 ≤ dyBump y := by
  unfold dyBump
  rcases le_or_gt 0 y with hy | hy
  · have := smoothTransition.monotone (show y - 1 ≤ 2 * y - 1 by linarith)
    linarith
  · rw [smoothTransition.zero_of_nonpos (show y - 1 ≤ 0 by linarith)]
    simpa using smoothTransition.nonneg (2 * y - 1)

theorem dyBump_le_one (y : ℝ) : dyBump y ≤ 1 := by
  unfold dyBump
  have h1 := smoothTransition.le_one (2 * y - 1)
  have h2 := smoothTransition.nonneg (y - 1)
  linarith

theorem dyBump_eq_zero {y : ℝ} (hy : y ∉ Set.Ioo (1/2 : ℝ) 2) : dyBump y = 0 := by
  unfold dyBump
  simp only [Set.mem_Ioo, not_and_or, not_lt] at hy
  rcases hy with hy | hy
  · rw [smoothTransition.zero_of_nonpos (by linarith),
      smoothTransition.zero_of_nonpos (by linarith)]
    simp
  · rw [smoothTransition.one_of_one_le (by linarith),
      smoothTransition.one_of_one_le (by linarith)]
    simp

theorem dyBump_eq_zero_of_le {y : ℝ} (hy : y ≤ 1 / 2) : dyBump y = 0 :=
  dyBump_eq_zero (by simp only [Set.mem_Ioo, not_and_or, not_lt]; left; exact hy)

theorem dyBump_eq_zero_of_ge {y : ℝ} (hy : 2 ≤ y) : dyBump y = 0 :=
  dyBump_eq_zero (by simp only [Set.mem_Ioo, not_and_or, not_lt]; right; exact hy)

theorem continuous_dyBump : Continuous dyBump := by
  unfold dyBump
  fun_prop

/-! ## `topCut` -/

theorem topCut_nonneg (K ν x : ℝ) : 0 ≤ topCut K ν x := by
  unfold topCut
  linarith [smoothTransition.le_one ((x - (1 - ν) * K) / (ν * K))]

theorem topCut_le_one (K ν x : ℝ) : topCut K ν x ≤ 1 := by
  unfold topCut
  linarith [smoothTransition.nonneg ((x - (1 - ν) * K) / (ν * K))]

theorem topCut_eq_one {K ν x : ℝ} (hν : 0 < ν) (hK : 0 < K) (hx : x ≤ (1 - ν) * K) :
    topCut K ν x = 1 := by
  unfold topCut
  rw [smoothTransition.zero_of_nonpos]
  · simp
  · apply div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

theorem topCut_eq_zero {K ν x : ℝ} (hν : 0 < ν) (hK : 0 < K) (hx : K ≤ x) :
    topCut K ν x = 0 := by
  unfold topCut
  rw [smoothTransition.one_of_one_le]
  · simp
  · rw [le_div_iff₀ (by positivity)]
    linarith

theorem continuous_topCut (K ν : ℝ) : Continuous (topCut K ν) := by
  unfold topCut
  have : Continuous fun x : ℝ => (x - (1 - ν) * K) / (ν * K) := by fun_prop
  exact continuous_const.sub (smoothTransition.continuous.comp this)

/-! ## Telescoping -/

/-- `∑_{a < J} dyBump (x/2^a) = st(2x - 1) - st(2 (x/2^J) - 1)`. -/
theorem sum_dyBump_range (x : ℝ) (J : ℕ) :
    ∑ a ∈ Finset.range J, dyBump (x / 2 ^ a) =
      smoothTransition (2 * x - 1) - smoothTransition (2 * (x / 2 ^ J) - 1) := by
  have key : ∀ a : ℕ, dyBump (x / 2 ^ a) =
      smoothTransition (2 * (x / 2 ^ a) - 1) - smoothTransition (2 * (x / 2 ^ (a + 1)) - 1) := by
    intro a
    unfold dyBump
    congr 2
    rw [pow_succ]
    field_simp
  simp_rw [key]
  rw [Finset.sum_range_sub' (fun a => smoothTransition (2 * (x / 2 ^ a) - 1)) J]
  simp

/-- `∑_{j₀ ≤ a < J} dyBump (x/2^a) = st(2(x/2^{j₀}) - 1) - st(2 (x/2^J) - 1)`. -/
theorem sum_dyBump_Ico (x : ℝ) {j₀ J : ℕ} (h : j₀ ≤ J) :
    ∑ a ∈ Finset.Ico j₀ J, dyBump (x / 2 ^ a) =
      smoothTransition (2 * (x / 2 ^ j₀) - 1) - smoothTransition (2 * (x / 2 ^ J) - 1) := by
  rw [Finset.sum_Ico_eq_sub _ h, sum_dyBump_range, sum_dyBump_range]
  ring

/-! ## Pieces -/

theorem piece_apply_div (K ν D x : ℝ) (hD : D ≠ 0) :
    piece K ν D (x / D) = ((dyBump (x / D) * topCut K ν x : ℝ) : ℂ) := by
  unfold piece
  rw [mul_div_cancel₀ x hD]

theorem piece_eq_zero_of_ge {K ν D y : ℝ} (hy : 2 ≤ y) : piece K ν D y = 0 := by
  unfold piece
  rw [dyBump_eq_zero_of_ge hy]
  simp

theorem piece_eq_zero_of_le {K ν D y : ℝ} (hy : y ≤ 1 / 2) : piece K ν D y = 0 := by
  unfold piece
  rw [dyBump_eq_zero_of_le hy]
  simp

/-- The pieces of `topCut K ν` sum to it on `[1, ∞)` once `K ≤ 2^J/2`. -/
theorem sum_piece_range {K ν x : ℝ} (hν : 0 < ν) (hK : 0 < K) {J : ℕ}
    (hKJ : K ≤ 2 ^ J / 2) (hx : 1 ≤ x) :
    ∑ a ∈ Finset.range J, piece K ν (2 ^ a) (x / 2 ^ a) = (topCut K ν x : ℂ) := by
  have h1 : ∀ a ∈ Finset.range J, piece K ν (2 ^ a) (x / 2 ^ a) =
      ((dyBump (x / 2 ^ a) : ℝ) : ℂ) * (topCut K ν x : ℂ) := by
    intro a _
    rw [piece_apply_div K ν (2 ^ a) x (by positivity)]
    push_cast
    ring
  rw [Finset.sum_congr rfl h1, ← Finset.sum_mul]
  have hs : ∑ a ∈ Finset.range J, ((dyBump (x / 2 ^ a) : ℝ) : ℂ)
      = ((smoothTransition (2 * x - 1) - smoothTransition (2 * (x / 2 ^ J) - 1) : ℝ) : ℂ) := by
    rw [← sum_dyBump_range]
    push_cast
    rfl
  rw [hs, smoothTransition.one_of_one_le (by linarith)]
  by_cases hxJ : x ≤ 2 ^ J / 2
  · rw [smoothTransition.zero_of_nonpos]
    · simp
    · have : x / 2 ^ J ≤ 1 / 2 := by
        rw [div_le_iff₀ (by positivity)]
        linarith
      linarith
  · rw [topCut_eq_zero hν hK (by linarith)]
    simp

/-! ## The `n`-cutoff -/

/-- `Ψ(x) = ∑_{j₀ ≤ l < J} dyBump (x/2^l) topCut N ν x`. -/
noncomputable def psiCut (N ν : ℝ) (j₀ J : ℕ) (x : ℝ) : ℝ :=
  ∑ l ∈ Finset.Ico j₀ J, dyBump (x / 2 ^ l) * topCut N ν x

theorem psiCut_eq (N ν : ℝ) {j₀ J : ℕ} (h : j₀ ≤ J) (x : ℝ) :
    psiCut N ν j₀ J x =
      (smoothTransition (2 * (x / 2 ^ j₀) - 1) - smoothTransition (2 * (x / 2 ^ J) - 1))
        * topCut N ν x := by
  unfold psiCut
  rw [← Finset.sum_mul, sum_dyBump_Ico x h]

theorem psiCut_nonneg (N ν : ℝ) (j₀ J : ℕ) (x : ℝ) : 0 ≤ psiCut N ν j₀ J x :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (dyBump_nonneg _) (topCut_nonneg _ _ _)

theorem psiCut_le_one (N ν : ℝ) {j₀ J : ℕ} (h : j₀ ≤ J) (x : ℝ) : psiCut N ν j₀ J x ≤ 1 := by
  rw [psiCut_eq N ν h x]
  have h1 := smoothTransition.le_one (2 * (x / 2 ^ j₀) - 1)
  have h2 := smoothTransition.nonneg (2 * (x / 2 ^ J) - 1)
  have h3 := topCut_nonneg N ν x
  have h4 := topCut_le_one N ν x
  have h5 : smoothTransition (2 * (x / 2 ^ j₀) - 1) - smoothTransition (2 * (x / 2 ^ J) - 1)
      ≤ 1 := by linarith
  calc _ ≤ 1 * topCut N ν x := by
        rcases le_total 0 (smoothTransition (2 * (x / 2 ^ j₀) - 1) -
          smoothTransition (2 * (x / 2 ^ J) - 1)) with h6 | h6
        · exact mul_le_mul_of_nonneg_right h5 h3
        · nlinarith
    _ ≤ 1 := by linarith

theorem psiCut_eq_one {N ν x : ℝ} (hν : 0 < ν) (hN : 0 < N) {j₀ J : ℕ} (h : j₀ ≤ J)
    (hNJ : N ≤ 2 ^ J / 2) (hx1 : 2 ^ j₀ ≤ x) (hx2 : x ≤ (1 - ν) * N) :
    psiCut N ν j₀ J x = 1 := by
  rw [psiCut_eq N ν h x, topCut_eq_one hν hN hx2]
  rw [smoothTransition.one_of_one_le, smoothTransition.zero_of_nonpos]
  · simp
  · have : x / 2 ^ J ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  · have : 1 ≤ x / 2 ^ j₀ := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    linarith

theorem psiCut_eq_zero_of_ge {N ν x : ℝ} (hν : 0 < ν) (hN : 0 < N) (j₀ J : ℕ) (hx : N ≤ x) :
    psiCut N ν j₀ J x = 0 := by
  unfold psiCut
  apply Finset.sum_eq_zero
  intro _ _
  rw [topCut_eq_zero hν hN hx, mul_zero]

theorem psiCut_eq_zero_of_le {N ν x : ℝ} {j₀ J : ℕ} (h : j₀ ≤ J) (hx : x ≤ 2 ^ j₀ / 2) :
    psiCut N ν j₀ J x = 0 := by
  rw [psiCut_eq N ν h x]
  have hJ : (2 : ℝ) ^ j₀ ≤ 2 ^ J := pow_le_pow_right₀ (by norm_num) h
  rw [smoothTransition.zero_of_nonpos, smoothTransition.zero_of_nonpos]
  · simp
  · rcases le_or_gt x 0 with hx0 | hx0
    · have : x / 2 ^ J ≤ 0 := div_nonpos_of_nonpos_of_nonneg hx0 (by positivity)
      linarith
    · have : x / 2 ^ J ≤ 1 / 2 := by
        rw [div_le_iff₀ (by positivity)]
        linarith
      linarith
  · have : x / 2 ^ j₀ ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    linarith

theorem continuous_psiCut (N ν : ℝ) (j₀ J : ℕ) : Continuous (psiCut N ν j₀ J) := by
  unfold psiCut
  apply continuous_finsetSum
  intro _ _
  exact (continuous_dyBump.comp (continuous_id.div_const _)).mul (continuous_topCut N ν)

/-! ## The zero Fourier modes of the `n`-pieces -/

theorem fourierR_zero (f : ℝ → ℂ) : fourierR f 0 = ∫ x, f x := by
  unfold fourierR
  simp

theorem integrable_psiCut (N ν : ℝ) (j₀ J : ℕ) (hN : 0 < N) (hν : 0 < ν) :
    Integrable (psiCut N ν j₀ J) := by
  apply (continuous_psiCut N ν j₀ J).integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (isCompact_Icc (a := -1) (b := N))
  intro x hx
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  rcases hx with hx | hx
  · rcases le_total j₀ J with h | h
    · exact psiCut_eq_zero_of_le h (by have : (0:ℝ) < 2 ^ j₀ / 2 := by positivity
                                       linarith)
    · unfold psiCut
      rw [Finset.Ico_eq_empty_of_le h, Finset.sum_empty]
  · exact psiCut_eq_zero_of_ge hν hN j₀ J hx.le

/-- `∑_{j₀ ≤ l < J} 2^l ψ̂_l(0) = ∫ Ψ`. -/
theorem sum_fourierR_piece_zero (N ν : ℝ) (j₀ J : ℕ) :
    ∑ l ∈ Finset.Ico j₀ J, (((2 : ℝ) ^ l : ℝ) : ℂ) * fourierR (piece N ν ((2 : ℝ) ^ l)) 0
      = (((∫ x, psiCut N ν j₀ J x) : ℝ) : ℂ) := by
  have h1 : ∀ l ∈ Finset.Ico j₀ J,
      (((2 : ℝ) ^ l : ℝ) : ℂ) * fourierR (piece N ν ((2 : ℝ) ^ l)) 0
        = ∫ x, (((dyBump (x / 2 ^ l) * topCut N ν x) : ℝ) : ℂ) := by
    intro l _
    rw [fourierR_zero]
    have h2 : (∫ x, (((dyBump (x / 2 ^ l) * topCut N ν x) : ℝ) : ℂ))
        = ∫ x, piece N ν ((2 : ℝ) ^ l) (x / 2 ^ l) := by
      congr 1
      ext x
      rw [piece_apply_div N ν (2 ^ l) x (by positivity)]
    rw [h2, Measure.integral_comp_div (fun y => piece N ν ((2 : ℝ) ^ l) y) ((2 : ℝ) ^ l)]
    rw [abs_of_pos (by positivity), Complex.real_smul]
  rw [Finset.sum_congr rfl h1]
  rw [← integral_finsetSum]
  · rw [← integral_complex_ofReal]
    congr 1
    ext x
    unfold psiCut
    push_cast
    rfl
  · intro l hl
    have hint : Integrable (fun x => dyBump (x / 2 ^ l) * topCut N ν x) := by
      apply Continuous.integrable_of_hasCompactSupport
      · exact (continuous_dyBump.comp (continuous_id.div_const _)).mul (continuous_topCut N ν)
      · apply HasCompactSupport.intro (isCompact_Icc (a := 0) (b := 2 * 2 ^ l))
        intro x hx
        simp only [Set.mem_Icc, not_and_or, not_le] at hx
        rcases hx with hx | hx
        · rw [dyBump_eq_zero_of_le, zero_mul]
          have : x / 2 ^ l < 0 := div_neg_of_neg_of_pos hx (by positivity)
          linarith
        · rw [dyBump_eq_zero_of_ge, zero_mul]
          rw [le_div_iff₀ (by positivity)]
          linarith
    exact hint.ofReal

/-- `|∫Ψ - N| ≤ 2^{j₀} + νN`. -/
theorem abs_integral_psiCut_sub_le {N ν : ℝ} (hν : 0 < ν) (hN : 0 < N) {j₀ J : ℕ}
    (h : j₀ ≤ J) (hNJ : N ≤ 2 ^ J / 2) :
    |(∫ x, psiCut N ν j₀ J x) - N| ≤ 2 ^ j₀ + ν * N := by
  have hint := integrable_psiCut N ν j₀ J hN hν
  have hI1 : Integrable ((Set.Icc (0:ℝ) N).indicator (fun _ => (1:ℝ))) :=
    (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hI2 : Integrable ((Set.Icc ((2:ℝ) ^ j₀) ((1 - ν) * N)).indicator (fun _ => (1:ℝ))) :=
    (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hup : (∫ x, psiCut N ν j₀ J x) ≤ N := by
    have : (∫ x, psiCut N ν j₀ J x) ≤ ∫ x, (Set.Icc (0:ℝ) N).indicator (fun _ => (1:ℝ)) x := by
      apply integral_mono hint hI1
      intro x
      by_cases hx : x ∈ Set.Icc (0:ℝ) N
      · rw [Set.indicator_of_mem hx]
        exact psiCut_le_one N ν h x
      · rw [Set.indicator_of_notMem hx]
        simp only [Set.mem_Icc, not_and_or, not_le] at hx
        rcases hx with hx | hx
        · exact (psiCut_eq_zero_of_le h (by have : (0:ℝ) < 2 ^ j₀ / 2 := by positivity
                                            linarith)).le
        · exact (psiCut_eq_zero_of_ge hν hN j₀ J hx.le).le
    rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le hN.le] at this
    simpa using this
  have hlow : (1 - ν) * N - 2 ^ j₀ ≤ (∫ x, psiCut N ν j₀ J x) := by
    have : (∫ x, (Set.Icc ((2:ℝ) ^ j₀) ((1 - ν) * N)).indicator (fun _ => (1:ℝ)) x)
        ≤ (∫ x, psiCut N ν j₀ J x) := by
      apply integral_mono hI2 hint
      intro x
      by_cases hx : x ∈ Set.Icc ((2:ℝ) ^ j₀) ((1 - ν) * N)
      · rw [Set.indicator_of_mem hx, psiCut_eq_one hν hN h hNJ hx.1 hx.2]
      · rw [Set.indicator_of_notMem hx]
        exact psiCut_nonneg N ν j₀ J x
    rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc] at this
    simp only [smul_eq_mul, mul_one] at this
    linarith [le_max_left ((1 - ν) * N - 2 ^ j₀) 0]
  rw [abs_le]
  constructor <;> nlinarith

/-- `‖∑_{j₀ ≤ l < J} 2^l ψ̂_l(0) - N‖ ≤ 2^{j₀} + νN`, `ψ_l = piece N ν 2^l`. -/
theorem norm_sum_fourierR_piece_sub_le {N ν : ℝ} (hν : 0 < ν) (hN : 0 < N) {j₀ J : ℕ}
    (h : j₀ ≤ J) (hNJ : N ≤ 2 ^ J / 2) :
    ‖(∑ l ∈ Finset.Ico j₀ J, (((2 : ℝ) ^ l : ℝ) : ℂ) * fourierR (piece N ν ((2 : ℝ) ^ l)) 0)
        - (N : ℂ)‖ ≤ 2 ^ j₀ + ν * N := by
  rw [sum_fourierR_piece_zero N ν j₀ J, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs]
  exact abs_integral_psiCut_sub_le hν hN h hNJ

end Cutoff

end Level

end MobiusDeterminant
