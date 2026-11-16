import MobiusDeterminant.Determinant.Defs
import MobiusDeterminant.Unconditional.LevelTempered
import MobiusDeterminant.Unconditional.LevelCutoff

/-!
# Reduction of Theorem 1.3 to product weights: the cutoffs and the kernel identity

For `κ = 2` write `n = ad`, so `n + 2 = be`.  With `ν = n/X`, `δ = d/D`, `ε = e/E` we have
`a/A = ν/δ` and `b/B = (ν + 2/X)/ε`, and the four-variable Mellin separation of `W` gives

  `W(ν/δ, (ν+2/X)/ε, δ, ε) = ∫ g(τ) [ν^{-iτ₀} (ν+2/X)^{-iτ₁}] [δ^{i(τ₀-τ₂)}] [ε^{i(τ₁-τ₃)}] dτ`.

We cut off each factor smoothly:

* `psiP X j τ y` : the `ν`-factor on the `j`-th dyadic piece `ν = 2^j y`, `j < 3`
  (`∑_{j<3} dyBump (ν/2^j) = 1` on `[1,4]`);
* `phiP θ y`     : `midCut y · (3y/2)^{iθ}`, the `δ`- (resp. `ε`-) factor at scale `3D/2`
  (resp. `3E/2`), where `midCut = 1` on `[2/3, 4/3]`.

All of them are tempered on `[1/2, 2]` with `P = K (1 + ‖τ‖)` (`tempered_pieces`), and the
kernel `kerH` (sum over the pieces of the product of the three factors) integrates against `g`
to `W(ν/δ, (ν+2/X)/ε, δ, ε)` for every `ν` (`integral_kerH`).
-/

open Finset Real MeasureTheory

namespace MobiusDeterminant.Determinant.Reduction

open MobiusDeterminant.Level

/-- The parameter space of the four-variable Mellin separation. -/
abbrev E4 : Type := EuclideanSpace ℝ (Fin 4)

/-! ## Definitions -/

/-- `midCut = 1` on `[2/3, 4/3]`, `= 0` outside `(1/2, 2)`, `0 ≤ midCut ≤ 1`. -/
noncomputable def midCut (y : ℝ) : ℝ :=
  smoothTransition (6 * y - 3) * (1 - smoothTransition (3 / 2 * y - 2))

/-- The `ν`-factor on the dyadic piece `j`, as a function of `y = ν/2^j`:
`2^{-ij(τ₀+τ₁)} β(y) y^{-iτ₀} (y + 2/(2^j X))^{-iτ₁}`. -/
noncomputable def psiP (X : ℝ) (j : ℕ) (τ : E4) (y : ℝ) : ℂ :=
  Complex.exp (((-(τ 0 + τ 1) * ((j : ℝ) * Real.log 2) : ℝ) : ℂ) * Complex.I) *
    ((dyBump y : ℝ) : ℂ) * uPow (-τ 0) y * uPow (-τ 1) (y + 2 / (2 ^ j * X))

/-- The `δ`- or `ε`-factor at scale `3/2` times the original one: `midCut y · (3y/2)^{iθ}`. -/
noncomputable def phiP (θ y : ℝ) : ℂ := ((midCut y : ℝ) : ℂ) * uPow θ (3 / 2 * y)

/-- The `ν`-cutoff `∑_{j<3} β(ν/2^j)`, equal to `1` on `[1,4]`. -/
noncomputable def cutN (ν : ℝ) : ℝ := ∑ j ∈ range 3, dyBump (ν / 2 ^ j)

/-- The kernel: sum over the dyadic pieces of the product of the three factors. -/
noncomputable def kerH (X : ℝ) (τ : E4) (ν y₁ y₂ : ℝ) : ℂ :=
  ∑ j ∈ range 3, phiP (τ 0 - τ 2) y₁ * phiP (τ 1 - τ 3) y₂ * psiP X j τ (ν / 2 ^ j)

/-- The Mellin phase of `MellinSep4`. -/
noncomputable def mphase (τ : E4) (α β δ ε : ℝ) : ℂ :=
  Complex.exp (-((τ 0 * Real.log α + τ 1 * Real.log β + τ 2 * Real.log δ +
    τ 3 * Real.log ε : ℝ) : ℂ) * Complex.I)

/-! ## Elementary properties of the cutoffs -/

lemma midCut_nonneg (y : ℝ) : 0 ≤ midCut y :=
  mul_nonneg (smoothTransition.nonneg _) (by linarith [smoothTransition.le_one (3 / 2 * y - 2)])

lemma midCut_le_one (y : ℝ) : midCut y ≤ 1 := by
  unfold midCut
  have h1 := smoothTransition.nonneg (6 * y - 3)
  have h2 := smoothTransition.le_one (6 * y - 3)
  have h3 := smoothTransition.nonneg (3 / 2 * y - 2)
  have h4 := smoothTransition.le_one (3 / 2 * y - 2)
  nlinarith

lemma midCut_eq_one {y : ℝ} (hy : y ∈ Set.Icc (2 / 3 : ℝ) (4 / 3)) : midCut y = 1 := by
  obtain ⟨h1, h2⟩ := hy
  unfold midCut
  rw [smoothTransition.one_of_one_le (by linarith), smoothTransition.zero_of_nonpos (by linarith)]
  ring

lemma midCut_eq_zero {y : ℝ} (hy : y ∉ Set.Icc (1 / 2 : ℝ) 2) : midCut y = 0 := by
  simp only [Set.mem_Icc, not_and_or, not_le] at hy
  unfold midCut
  rcases hy with hy | hy
  · rw [smoothTransition.zero_of_nonpos (by linarith)]; ring
  · rw [smoothTransition.one_of_one_le (x := 3 / 2 * y - 2) (by linarith)]; ring

lemma contDiff_midCut {n : ℕ} : ContDiff ℝ n midCut :=
  (Tempered.contDiff_st.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)).mul
    (contDiff_const.sub (Tempered.contDiff_st.comp
      ((contDiff_const.mul contDiff_id).sub contDiff_const)))

lemma continuous_midCut : Continuous midCut := (contDiff_midCut (n := 0)).continuous

lemma continuous_logCut : Continuous logCut := (Tempered.contDiff_logCut (n := 0)).continuous

lemma continuous_dyBump' : Continuous dyBump := (Tempered.contDiff_dyBump (n := 0)).continuous

lemma continuous_uPow₂ : Continuous (fun p : ℝ × ℝ => uPow p.1 p.2) := by
  unfold uPow
  exact Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
    (continuous_fst.mul (continuous_logCut.comp continuous_snd))).mul continuous_const)

lemma cutN_eq_one {ν : ℝ} (hν : ν ∈ Set.Icc (1 : ℝ) 4) : cutN ν = 1 := by
  obtain ⟨h1, h2⟩ := hν
  unfold cutN
  rw [Cutoff.sum_dyBump_range, smoothTransition.one_of_one_le (by linarith),
    smoothTransition.zero_of_nonpos (by norm_num; linarith)]
  ring

lemma norm_expI (r : ℝ) : ‖Complex.exp ((r : ℂ) * Complex.I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I r

lemma psiP_eq_zero (X : ℝ) (j : ℕ) (τ : E4) {y : ℝ} (hy : y ∉ Set.Icc (1 / 2 : ℝ) 2) :
    psiP X j τ y = 0 := by
  simp [psiP, Tempered.dyBump_eq_zero_out hy]

lemma norm_psiP_le (X : ℝ) (j : ℕ) (τ : E4) (y : ℝ) : ‖psiP X j τ y‖ ≤ 1 := by
  unfold psiP
  rw [norm_mul, norm_mul, norm_mul, norm_expI, norm_uPow, norm_uPow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Tempered.dyBump_nonneg y)]
  linarith [Tempered.dyBump_le_one y]

lemma phiP_eq_zero (θ : ℝ) {y : ℝ} (hy : y ∉ Set.Icc (1 / 2 : ℝ) 2) : phiP θ y = 0 := by
  simp [phiP, midCut_eq_zero hy]

lemma norm_phiP_le (θ y : ℝ) : ‖phiP θ y‖ ≤ 1 := by
  unfold phiP
  rw [norm_mul, norm_uPow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (midCut_nonneg y)]
  linarith [midCut_le_one y]

lemma continuous_coord (i : Fin 4) : Continuous (fun τ : E4 => τ i) := by fun_prop

@[fun_prop] lemma Continuous.uPow' {α : Type*} [TopologicalSpace α] {f h : α → ℝ}
    (hf : Continuous f) (hh : Continuous h) : Continuous (fun x => uPow (f x) (h x)) :=
  continuous_uPow₂.comp (hf.prodMk hh)

@[fun_prop] lemma Continuous.dyBump' {α : Type*} [TopologicalSpace α] {f : α → ℝ}
    (hf : Continuous f) : Continuous (fun x => dyBump (f x)) :=
  continuous_dyBump'.comp hf

@[fun_prop] lemma Continuous.midCut' {α : Type*} [TopologicalSpace α] {f : α → ℝ}
    (hf : Continuous f) : Continuous (fun x => midCut (f x)) :=
  continuous_midCut.comp hf

@[fun_prop] lemma Continuous.coord' {α : Type*} [TopologicalSpace α] {f : α → E4}
    (hf : Continuous f) (i : Fin 4) : Continuous (fun x => f x i) :=
  (continuous_coord i).comp hf

lemma continuous_psiP₂ (X : ℝ) (j : ℕ) : Continuous (fun p : E4 × ℝ => psiP X j p.1 p.2) := by
  unfold psiP
  fun_prop

lemma continuous_psiP (X : ℝ) (j : ℕ) (y : ℝ) : Continuous (fun τ : E4 => psiP X j τ y) := by
  unfold psiP
  fun_prop

lemma continuous_phiP (a b : Fin 4) (y : ℝ) :
    Continuous (fun τ : E4 => phiP (τ a - τ b) y) := by
  unfold phiP
  fun_prop

lemma abs_apply_le_norm (τ : E4) (i : Fin 4) : |τ i| ≤ ‖τ‖ := by
  simpa using PiLp.norm_apply_le τ i

/-! ## Temperedness -/

/-- A `Tmp` bound with `‖f‖ ≤ 1` gives `TemperedOn` with `P = M B`. -/
lemma temperedOn_of_tmp_one {f : ℝ → ℂ} {M B : ℝ} {k : ℕ} {a b : ℝ} (hf : Tmp f M B k)
    (hM : 1 ≤ M) (hB : 1 ≤ B) (h0 : ∀ x, ‖f x‖ ≤ 1)
    (hs : ∀ x, x ∉ Set.Icc a b → f x = 0) : TemperedOn f (M * B) k a b := by
  refine ⟨hf.1, hs, fun j hj x => ?_⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simpa using h0 x
  · refine (hf.2 j hj x).trans ?_
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (le_self_pow₀ hM (by omega)) (by positivity)

/-- The three factors are tempered on `[1/2, 2]` with `P = K (1 + ‖τ‖)`. -/
theorem tempered_pieces (k : ℕ) : ∃ K : ℝ, 1 ≤ K ∧ ∀ (X : ℝ) (j : ℕ) (τ : E4),
    TemperedOn (psiP X j τ) (K * (1 + ‖τ‖)) k (1 / 2) 2 ∧
    TemperedOn (phiP (τ 0 - τ 2)) (K * (1 + ‖τ‖)) k (1 / 2) 2 ∧
    TemperedOn (phiP (τ 1 - τ 3)) (K * (1 + ‖τ‖)) k (1 / 2) 2 := by
  obtain ⟨c, hc1, hc⟩ := Tempered.tmp_uPow k
  obtain ⟨Mβ, hMβ, hβ⟩ := Tempered.exists_tmp_of_vanish
    (Tempered.contDiff_ofReal_comp (Tempered.contDiff_dyBump (n := k))) (1 / 2) 2
    (fun x hx => by simp [Tempered.dyBump_eq_zero_out hx])
  obtain ⟨Mχ, hMχ, hχ⟩ := Tempered.exists_tmp_of_vanish
    (Tempered.contDiff_ofReal_comp (contDiff_midCut (n := k))) (1 / 2) 2
    (fun x hx => by simp [midCut_eq_zero hx])
  have hK1 : 1 ≤ 6 * Mβ * Mχ * c := by
    have h1 : 1 ≤ Mβ * Mχ := one_le_mul_of_one_le_of_one_le hMβ hMχ
    have h2 : 1 ≤ Mβ * Mχ * c := one_le_mul_of_one_le_of_one_le h1 hc1
    linarith
  refine ⟨6 * Mβ * Mχ * c, hK1, fun X j τ => ?_⟩
  have hτ : 0 ≤ ‖τ‖ := norm_nonneg τ
  have hP1 : 1 ≤ 1 + ‖τ‖ := by linarith
  -- the `ν`-factor
  have hψ : TemperedOn (psiP X j τ) (6 * Mβ * Mχ * c * (1 + ‖τ‖)) k (1 / 2) 2 := by
    set cst : ℂ := Complex.exp (((-(τ 0 + τ 1) * ((j : ℝ) * Real.log 2) : ℝ) : ℂ) * Complex.I)
    have hfun : psiP X j τ = fun y => cst * ((((dyBump y : ℝ) : ℂ) * uPow (-τ 0) y) *
        uPow (-τ 1) (1 * y + 2 / (2 ^ j * X))) := by
      funext y; simp only [psiP, cst, one_mul]; ring
    have ht := Tempered.tmp_const_mul (Tempered.tmp_mul (Tempered.tmp_mul hβ (hc (-τ 0)))
      (Tempered.tmp_comp_affine (hc (-τ 1)) 1 (2 / (2 ^ j * X)))) cst
    rw [← hfun, show ‖cst‖ = 1 from norm_expI _, one_mul, mul_one, mul_one] at ht
    have hB1 : 1 ≤ 1 + c * (1 + |-τ 0|) + |(1 : ℝ)| * (c * (1 + |-τ 1|)) := by
      have : 0 ≤ c * (1 + |-τ 0|) := by positivity
      have : 0 ≤ |(1 : ℝ)| * (c * (1 + |-τ 1|)) := by positivity
      linarith
    refine temperedOn_mono_P (temperedOn_of_tmp_one ht hMβ hB1 (norm_psiP_le X j τ)
      (fun x hx => psiP_eq_zero X j τ hx)) (by positivity) ?_
    rw [abs_neg, abs_neg, abs_one, one_mul]
    have h0 := abs_apply_le_norm τ 0
    have h1 := abs_apply_le_norm τ 1
    have e1 : c * (1 + |τ 0|) ≤ c * (1 + ‖τ‖) := by gcongr
    have e2 : c * (1 + |τ 1|) ≤ c * (1 + ‖τ‖) := by gcongr
    have e3 : 1 ≤ c * (1 + ‖τ‖) := by nlinarith
    have e4 : Mβ * (1 + c * (1 + |τ 0|) + c * (1 + |τ 1|)) ≤ Mβ * (3 * (c * (1 + ‖τ‖))) := by
      gcongr; linarith
    have e5 : Mβ * (3 * (c * (1 + ‖τ‖))) ≤ 6 * Mβ * Mχ * c * (1 + ‖τ‖) := by
      have : 0 ≤ Mβ * c * (1 + ‖τ‖) := by positivity
      nlinarith
    linarith
  -- the `δ`, `ε` factors
  have hφ : ∀ a b : Fin 4,
      TemperedOn (phiP (τ a - τ b)) (6 * Mβ * Mχ * c * (1 + ‖τ‖)) k (1 / 2) 2 := by
    intro a b
    have hfun : phiP (τ a - τ b) = fun y => ((midCut y : ℝ) : ℂ) *
        uPow (τ a - τ b) (3 / 2 * y + 0) := by
      funext y; simp [phiP]
    have ht := Tempered.tmp_mul hχ (Tempered.tmp_comp_affine (hc (τ a - τ b)) (3 / 2) 0)
    rw [← hfun, mul_one] at ht
    have hB1 : 1 ≤ 1 + |(3 / 2 : ℝ)| * (c * (1 + |τ a - τ b|)) := by
      have : 0 ≤ |(3 / 2 : ℝ)| * (c * (1 + |τ a - τ b|)) := by positivity
      linarith
    refine temperedOn_mono_P (temperedOn_of_tmp_one ht hMχ hB1 (norm_phiP_le _)
      (fun x hx => phiP_eq_zero _ hx)) (by positivity) ?_
    rw [show |(3 / 2 : ℝ)| = 3 / 2 by norm_num]
    have hab : |τ a - τ b| ≤ 2 * ‖τ‖ := by
      have := abs_sub (τ a) (τ b)
      linarith [abs_apply_le_norm τ a, abs_apply_le_norm τ b]
    have e1 : c * (1 + |τ a - τ b|) ≤ 2 * (c * (1 + ‖τ‖)) := by nlinarith
    have e3 : 1 ≤ c * (1 + ‖τ‖) := by nlinarith
    have e4 : Mχ * (1 + 3 / 2 * (c * (1 + |τ a - τ b|))) ≤ Mχ * (4 * (c * (1 + ‖τ‖))) := by
      gcongr; linarith
    have e5 : Mχ * (4 * (c * (1 + ‖τ‖))) ≤ 6 * Mβ * Mχ * c * (1 + ‖τ‖) := by
      have : 0 ≤ Mχ * c * (1 + ‖τ‖) := by positivity
      nlinarith
    linarith
  exact ⟨hψ, hφ 0 2, hφ 1 3⟩

/-! ## The kernel identity -/

lemma expI_mul_expI (a b : ℝ) :
    Complex.exp ((a : ℂ) * Complex.I) * Complex.exp ((b : ℂ) * Complex.I) =
      Complex.exp (((a + b : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_add]; congr 1; push_cast; ring

/-- On the supports, the kernel is the cutoff times the Mellin phase. -/
theorem kerH_eq {X : ℝ} (hX : 1 ≤ X) (τ : E4) {ν y₁ y₂ : ℝ} (hν : 0 < ν) (hy₁ : 0 < y₁)
    (hy₂ : 0 < y₂) :
    kerH X τ ν y₁ y₂ = ((cutN ν * midCut y₁ * midCut y₂ : ℝ) : ℂ) *
      mphase τ (ν / (3 / 2 * y₁)) ((ν + 2 / X) / (3 / 2 * y₂)) (3 / 2 * y₁) (3 / 2 * y₂) := by
  unfold kerH cutN
  push_cast
  rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases h1 : midCut y₁ = 0
  · simp [phiP, h1]
  by_cases h2 : midCut y₂ = 0
  · simp [phiP, h2]
  by_cases h3 : dyBump (ν / 2 ^ j) = 0
  · simp [psiP, h3]
  have m1 : y₁ ∈ Set.Icc (1 / 2 : ℝ) 2 := by
    by_contra h; exact h1 (midCut_eq_zero h)
  have m2 : y₂ ∈ Set.Icc (1 / 2 : ℝ) 2 := by
    by_contra h; exact h2 (midCut_eq_zero h)
  have m3 : ν / 2 ^ j ∈ Set.Icc (1 / 2 : ℝ) 2 := by
    by_contra h; exact h3 (Tempered.dyBump_eq_zero_out h)
  have hX0 : 0 < X := by linarith
  have h2j : (0 : ℝ) < 2 ^ j := by positivity
  have hs0 : 0 < 2 / (2 ^ j * X) := by positivity
  have hs2 : 2 / (2 ^ j * X) ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    nlinarith
  have u1 : 3 / 2 * y₁ ∈ Set.Icc (1 / 4 : ℝ) 8 := ⟨by linarith [m1.1], by linarith [m1.2]⟩
  have u2 : 3 / 2 * y₂ ∈ Set.Icc (1 / 4 : ℝ) 8 := ⟨by linarith [m2.1], by linarith [m2.2]⟩
  have u3 : ν / 2 ^ j ∈ Set.Icc (1 / 4 : ℝ) 8 := ⟨by linarith [m3.1], by linarith [m3.2]⟩
  have u4 : ν / 2 ^ j + 2 / (2 ^ j * X) ∈ Set.Icc (1 / 4 : ℝ) 8 :=
    ⟨by linarith [m3.1], by linarith [m3.2]⟩
  unfold phiP psiP mphase
  rw [uPow_eq _ u1, uPow_eq _ u2, uPow_eq _ u3, uPow_eq _ u4]
  -- the logarithms
  have hy1' : 0 < 3 / 2 * y₁ := by positivity
  have hy2' : 0 < 3 / 2 * y₂ := by positivity
  have hν' : 0 < ν + 2 / X := by positivity
  have l1 : Real.log (ν / 2 ^ j) = Real.log ν - j * Real.log 2 := by
    rw [Real.log_div hν.ne' h2j.ne', Real.log_pow]
  have l2 : Real.log (ν / 2 ^ j + 2 / (2 ^ j * X)) = Real.log (ν + 2 / X) - j * Real.log 2 := by
    rw [show ν / 2 ^ j + 2 / (2 ^ j * X) = (ν + 2 / X) / 2 ^ j by field_simp,
      Real.log_div hν'.ne' h2j.ne', Real.log_pow]
  have l3 : Real.log (ν / (3 / 2 * y₁)) = Real.log ν - Real.log (3 / 2 * y₁) :=
    Real.log_div hν.ne' hy1'.ne'
  have l4 : Real.log ((ν + 2 / X) / (3 / 2 * y₂)) =
      Real.log (ν + 2 / X) - Real.log (3 / 2 * y₂) :=
    Real.log_div hν'.ne' hy2'.ne'
  rw [l1, l2, l3, l4]
  set E1 := Complex.exp ((((τ 0 - τ 2) * Real.log (3 / 2 * y₁) : ℝ) : ℂ) * Complex.I)
  set E2 := Complex.exp ((((τ 1 - τ 3) * Real.log (3 / 2 * y₂) : ℝ) : ℂ) * Complex.I)
  set E3 := Complex.exp (((-(τ 0 + τ 1) * ((j : ℝ) * Real.log 2) : ℝ) : ℂ) * Complex.I)
  set E4' := Complex.exp (((-τ 0 * (Real.log ν - j * Real.log 2) : ℝ) : ℂ) * Complex.I)
  set E5 := Complex.exp (((-τ 1 * (Real.log (ν + 2 / X) - j * Real.log 2) : ℝ) : ℂ) *
    Complex.I)
  have hE : E1 * E2 * E3 * E4' * E5 = Complex.exp (-((τ 0 * (Real.log ν - Real.log (3 / 2 * y₁)) +
      τ 1 * (Real.log (ν + 2 / X) - Real.log (3 / 2 * y₂)) + τ 2 * Real.log (3 / 2 * y₁) +
      τ 3 * Real.log (3 / 2 * y₂) : ℝ) : ℂ) * Complex.I) := by
    simp only [E1, E2, E3, E4', E5, expI_mul_expI]
    congr 1; push_cast; ring
  rw [← hE]
  ring

/-- The kernel vanishes for `ν ≤ 0`. -/
lemma kerH_eq_zero_of_nonpos (X : ℝ) (τ : E4) {ν : ℝ} (hν : ν ≤ 0) (y₁ y₂ : ℝ) :
    kerH X τ ν y₁ y₂ = 0 := by
  unfold kerH
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [psiP_eq_zero X j τ, mul_zero]
  intro h
  have : ν / 2 ^ j ≤ 0 := div_nonpos_of_nonpos_of_nonneg hν (by positivity)
  linarith [h.1]

/-- The kernel vanishes for `ν ∉ [1/2, 8]`. -/
lemma kerH_eq_zero_of_not_mem (X : ℝ) (τ : E4) {ν : ℝ} (hν : ν ∉ Set.Icc (1 / 2 : ℝ) 8)
    (y₁ y₂ : ℝ) : kerH X τ ν y₁ y₂ = 0 := by
  unfold kerH
  refine Finset.sum_eq_zero (fun j hj => ?_)
  rw [psiP_eq_zero X j τ, mul_zero]
  have hj3 : j < 3 := Finset.mem_range.mp hj
  intro h
  apply hν
  have h2j : (0 : ℝ) < 2 ^ j := by positivity
  have h1 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have h4 : (2 : ℝ) ^ j ≤ 4 := by
    calc (2 : ℝ) ^ j ≤ 2 ^ 2 := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = 4 := by norm_num
  obtain ⟨ha, hb⟩ := h
  rw [le_div_iff₀ h2j] at ha
  rw [div_le_iff₀ h2j] at hb
  constructor <;> nlinarith

lemma norm_kerH_le (X : ℝ) (τ : E4) (ν y₁ y₂ : ℝ) : ‖kerH X τ ν y₁ y₂‖ ≤ 3 := by
  unfold kerH
  refine (norm_sum_le _ _).trans ?_
  have : ∀ j ∈ range 3, ‖phiP (τ 0 - τ 2) y₁ * phiP (τ 1 - τ 3) y₂ * psiP X j τ (ν / 2 ^ j)‖
      ≤ 1 := by
    intro j _
    rw [norm_mul, norm_mul]
    have := norm_phiP_le (τ 0 - τ 2) y₁
    have := norm_phiP_le (τ 1 - τ 3) y₂
    have := norm_psiP_le X j τ (ν / 2 ^ j)
    have : ‖phiP (τ 0 - τ 2) y₁‖ * ‖phiP (τ 1 - τ 3) y₂‖ ≤ 1 := by
      nlinarith [norm_nonneg (phiP (τ 0 - τ 2) y₁), norm_nonneg (phiP (τ 1 - τ 3) y₂)]
    nlinarith [norm_nonneg (psiP X j τ (ν / 2 ^ j)),
      mul_nonneg (norm_nonneg (phiP (τ 0 - τ 2) y₁)) (norm_nonneg (phiP (τ 1 - τ 3) y₂))]
  refine (Finset.sum_le_sum this).trans ?_
  simp

lemma continuous_kerH₂ (X y₁ y₂ : ℝ) :
    Continuous (fun p : E4 × ℝ => kerH X p.1 p.2 y₁ y₂) := by
  unfold kerH phiP psiP
  fun_prop

/-- **The kernel integrates to the weight**: for every `ν`,
`∫ g(τ) kerH(τ; ν, y₁, y₂) dτ = W(ν/δ, (ν+2/X)/ε, δ, ε)` with `δ = 3y₁/2`, `ε = 3y₂/2`. -/
theorem integral_kerH {W : ℝ × ℝ × ℝ × ℝ → ℂ} (hW : SmoothWeight W) {g : E4 → ℂ}
    (hg : ∀ α β δ ε : ℝ, 0 < α → 0 < β → 0 < δ → 0 < ε →
      W (α, β, δ, ε) = ∫ τ, g τ * mphase τ α β δ ε)
    {X : ℝ} (hX : 1 ≤ X) {y₁ y₂ : ℝ} (hy₁ : 0 < y₁) (hy₂ : 0 < y₂) (ν : ℝ) :
    ∫ τ, g τ * kerH X τ ν y₁ y₂ =
      W (ν / (3 / 2 * y₁), (ν + 2 / X) / (3 / 2 * y₂), 3 / 2 * y₁, 3 / 2 * y₂) := by
  have hy1' : 0 < 3 / 2 * y₁ := by positivity
  have hy2' : 0 < 3 / 2 * y₂ := by positivity
  rcases le_or_gt ν 0 with hν | hν
  · simp_rw [kerH_eq_zero_of_nonpos X _ hν, mul_zero, integral_zero]
    symm
    by_contra h
    have := (hW.2 _ h).1
    have : ν / (3 / 2 * y₁) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hν hy1'.le
    linarith [this, (hW.2 _ h).1.1]
  · have hX0 : 0 < X := by linarith
    simp_rw [kerH_eq hX _ hν hy₁ hy₂]
    simp_rw [mul_left_comm (g _)]
    rw [integral_const_mul, ← hg _ _ _ _ (by positivity) (by positivity) hy1' hy2']
    by_cases hW0 : W (ν / (3 / 2 * y₁), (ν + 2 / X) / (3 / 2 * y₂), 3 / 2 * y₁, 3 / 2 * y₂) = 0
    · rw [hW0, mul_zero]
    obtain ⟨s1, -, s3, s4⟩ := hW.2 _ hW0
    have c1 : midCut y₁ = 1 := midCut_eq_one ⟨by linarith [s3.1], by linarith [s3.2]⟩
    have c2 : midCut y₂ = 1 := midCut_eq_one ⟨by linarith [s4.1], by linarith [s4.2]⟩
    have hνm : ν ∈ Set.Icc (1 : ℝ) 4 := by
      obtain ⟨a1, a2⟩ := s1
      rw [le_div_iff₀ hy1'] at a1
      rw [div_le_iff₀ hy1'] at a2
      constructor <;> nlinarith [s3.1, s3.2]
    rw [cutN_eq_one hνm, c1, c2]
    simp

end MobiusDeterminant.Determinant.Reduction
