import MobiusDeterminant.Unconditional.Interfaces

/-!
# Analytic toolkit: Mellin separation and Poisson summation in progressions

We prove the two analytic interface statements
* `mellinSeparation : MellinSeparation`;
* `poissonAPDecay : PoissonAPDecay`.

Both rest on Mathlib's Fourier analysis on `ℝ`:
`Real.one_add_pow_mul_norm_fourier_le` (decay of `𝓕 f` from integrability of derivatives),
Fourier inversion `Continuous.fourierInv_fourier_eq`, and Poisson summation
`Real.tsum_eq_tsum_fourier_of_rpow_decay`.
-/

open MeasureTheory Real Filter Topology Asymptotics
open scoped FourierTransform Nat

namespace MobiusDeterminant

namespace Toolkit

/-! ## Generalities -/

/-- `fourierR` is Mathlib's Fourier transform on `ℝ`. -/
lemma fourierR_eq (f : ℝ → ℂ) (ξ : ℝ) : fourierR f ξ = 𝓕 f ξ := by
  rw [fourierR, Real.fourier_real_eq_integral_exp_smul]
  congr 1
  ext x
  rw [smul_eq_mul]
  congr 2
  push_cast
  ring

lemma one_add_pow_le (x : ℝ) (hx : 0 ≤ x) (k : ℕ) : (1 + x) ^ k ≤ 2 ^ k * (1 + x ^ k) := by
  have h2 : (0 : ℝ) < 2 ^ k := pow_pos two_pos k
  have hxk : 0 ≤ x ^ k := pow_nonneg hx k
  rcases le_total x 1 with h | h
  · calc (1 + x) ^ k ≤ 2 ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
      _ ≤ 2 ^ k * (1 + x ^ k) := by nlinarith
  · calc (1 + x) ^ k ≤ (2 * x) ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
      _ = 2 ^ k * x ^ k := mul_pow _ _ _
      _ ≤ 2 ^ k * (1 + x ^ k) := by nlinarith

lemma one_add_sq_le_pow (x : ℝ) {k : ℕ} (hk : 2 ≤ k) : 1 + x ^ 2 ≤ (1 + |x|) ^ k := by
  have h1 : 1 + x ^ 2 ≤ (1 + |x|) ^ 2 := by
    have := abs_nonneg x
    nlinarith [sq_abs x]
  exact h1.trans (pow_le_pow_right₀ (by linarith [abs_nonneg x]) hk)

/-- If a function vanishes outside `[a,b]`, so do all its iterated derivatives. -/
lemma iteratedDeriv_vanish {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → E} {a b : ℝ} (hg : ∀ x, x ∉ Set.Icc a b → g x = 0) (j : ℕ) (x : ℝ)
    (hx : x ∉ Set.Icc a b) : iteratedDeriv j g x = 0 := by
  have hsupp : Function.support g ⊆ Set.Icc a b := fun y hy => by
    by_contra h
    exact hy (hg y h)
  have hts : tsupport g ⊆ Set.Icc a b := closure_minimal hsupp isClosed_Icc
  have h0 : iteratedFDeriv ℝ j g x = 0 := by
    by_contra h
    exact hx (hts (support_iteratedFDeriv_subset j h))
  rw [iteratedDeriv_eq_iteratedFDeriv, h0]
  rfl

lemma integrable_iteratedDeriv_of_vanish {G : ℝ → ℂ} {k : ℕ} {a b : ℝ} (hG : ContDiff ℝ k G)
    (hv : ∀ x, x ∉ Set.Icc a b → G x = 0) {j : ℕ} (hj : j ≤ k) :
    Integrable (iteratedDeriv j G) :=
  (hG.continuous_iteratedDeriv j (by exact_mod_cast hj)).integrable_of_hasCompactSupport
    (HasCompactSupport.intro isCompact_Icc (iteratedDeriv_vanish hv j))

lemma integral_norm_le_of_vanish {g : ℝ → ℂ} {a b M : ℝ} (hab : a ≤ b)
    (hg : ∀ x, x ∉ Set.Icc a b → g x = 0) (hM : ∀ x, ‖g x‖ ≤ M) :
    ∫ x, ‖g x‖ ≤ M * (b - a) := by
  have hint : Integrable (Set.indicator (Set.Icc a b) (fun _ : ℝ => M)) :=
    (integrableOn_const (by simp [Real.volume_Icc])).integrable_indicator measurableSet_Icc
  calc ∫ x, ‖g x‖ ≤ ∫ x, Set.indicator (Set.Icc a b) (fun _ : ℝ => M) x := by
        refine integral_mono_of_nonneg (ae_of_all _ fun x => norm_nonneg _) hint
          (ae_of_all _ fun x => ?_)
        by_cases hx : x ∈ Set.Icc a b
        · simp [Set.indicator_of_mem hx, hM x]
        · simp [Set.indicator_of_notMem hx, hg x hx]
    _ = M * (b - a) := by
        rw [integral_indicator_const _ measurableSet_Icc]
        simp [Real.volume_real_Icc_of_le hab, mul_comm]

/-- Fourier decay for a `C^k` function supported in `[a,b]` with derivatives bounded by `M`. -/
lemma fourier_decay_of_bound {G : ℝ → ℂ} {k : ℕ} {a b M : ℝ} (hab : a ≤ b)
    (hG : ContDiff ℝ k G) (hv : ∀ x, x ∉ Set.Icc a b → G x = 0)
    (hM : ∀ j ≤ k, ∀ x, ‖iteratedDeriv j G x‖ ≤ M) (ξ : ℝ) :
    (1 + |ξ| ^ k) * ‖𝓕 G ξ‖ ≤ 2 * M * (b - a) := by
  have h := Real.one_add_pow_mul_norm_fourier_le hG
    (fun j hj => integrable_iteratedDeriv_of_vanish hG hv hj) ξ
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (Nat.zero_le _) 0)
  have h0 : ∫ v, ‖G v‖ ≤ M * (b - a) :=
    integral_norm_le_of_vanish hab hv (fun x => by simpa using hM 0 (Nat.zero_le _) x)
  have hk : ∫ v, ‖iteratedDeriv k G v‖ ≤ M * (b - a) :=
    integral_norm_le_of_vanish hab (iteratedDeriv_vanish hv k) (hM k le_rfl)
  have hpi : ((2 * π) ^ k)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [pi_gt_three]))
  have hI : 0 ≤ ∫ v, ‖iteratedDeriv k G v‖ := integral_nonneg (fun _ => norm_nonneg _)
  have hpi0 : 0 ≤ ((2 * π) ^ k)⁻¹ := by positivity
  have hba : 0 ≤ M * (b - a) := mul_nonneg hM0 (by linarith)
  calc _ ≤ _ := h
    _ ≤ M * (b - a) + 1 * (M * (b - a)) := by
        gcongr
    _ = 2 * M * (b - a) := by ring

/-! ## Fourier decay for tempered functions -/

lemma tempered_deriv_bound {f : ℝ → ℂ} {P : ℝ} {k : ℕ} {a b : ℝ} (hP : 1 ≤ P)
    (hf : TemperedOn f P k a b) : ∀ j ≤ k, ∀ x, ‖iteratedDeriv j f x‖ ≤ P ^ k :=
  fun j hj x => (hf.2.2 j hj x).trans (pow_le_pow_right₀ hP hj)

lemma tempered_fourier_bound {f : ℝ → ℂ} {P : ℝ} {k : ℕ} {a b : ℝ} (hab : a < b) (hP : 1 ≤ P)
    (hf : TemperedOn f P k a b) (ξ : ℝ) :
    ‖fourierR f ξ‖ ≤ 2 ^ (k + 1) * (b - a) * P ^ k * (1 + |ξ|) ^ (-(k : ℝ)) := by
  have h := fourier_decay_of_bound hab.le hf.1 hf.2.1 (tempered_deriv_bound hP hf) ξ
  rw [fourierR_eq, Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv,
    le_div_iff₀ (by positivity)]
  have h2 := one_add_pow_le |ξ| (abs_nonneg ξ) k
  calc ‖𝓕 f ξ‖ * (1 + |ξ|) ^ k ≤ ‖𝓕 f ξ‖ * (2 ^ k * (1 + |ξ| ^ k)) := by gcongr
    _ = 2 ^ k * ((1 + |ξ| ^ k) * ‖𝓕 f ξ‖) := by ring
    _ ≤ 2 ^ k * (2 * P ^ k * (b - a)) := by gcongr
    _ = _ := by ring

/-! ## Poisson summation in a residue class -/

lemma fourier_affine (f : ℝ → ℂ) {X q : ℝ} (hX : 0 < X) (hq : 0 < q) (c h : ℝ) :
    𝓕 (fun y => f ((c + q * y) / X)) h =
      ((X / q : ℝ) : ℂ) * 𝓕 f (h * X / q) * Complex.exp (2 * π * Complex.I * (h * c) / q) := by
  set Φ : ℝ → ℂ := fun x => Complex.exp (2 * π * Complex.I * (h * c) / q) *
    (Complex.exp (↑(-2 * π * x * (h * X / q)) * Complex.I) • f x) with hΦ
  have key : ∀ y : ℝ, Complex.exp (↑(-2 * π * y * h) * Complex.I) • f ((c + q * y) / X) =
      Φ (q / X * y + c / X) := by
    intro y
    simp only [hΦ, smul_eq_mul]
    have e1 : (c + q * y) / X = q / X * y + c / X := by
      field_simp
      ring
    have hX' : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
    have hq'' : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
    rw [← e1, ← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    field_simp
    ring
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  simp_rw [key]
  have h1 := Measure.integral_comp_mul_left (fun z => Φ (z + c / X)) (q / X)
  rw [h1, integral_add_right_eq_self (fun z => Φ z) (c / X), hΦ]
  rw [integral_const_mul, abs_of_pos (by positivity), inv_div, Complex.real_smul]
  ring

lemma poisson_AP {f : ℝ → ℂ} {P : ℝ} {k : ℕ} {a b : ℝ} (hk : 2 ≤ k)
    (hf : TemperedOn f P k a b) {X : ℝ} (hX : 0 < X) {q : ℕ} (hq : 0 < q) (c : ℤ) :
    HasSum (fun h : ℤ => ((X / q : ℝ) : ℂ) * fourierR f (h * X / q) *
          Complex.exp (2 * π * Complex.I * ((h * c : ℤ) : ℂ) / (q : ℂ)))
        (∑' n : ℤ, if n ≡ c [ZMOD (q : ℤ)] then f (n / X) else 0) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  set G : ℝ → ℂ := fun y => f ((c + q * y) / X) with hG
  have hGv : ∀ y, y ∉ Set.Icc ((a * X - c) / q) ((b * X - c) / q) → G y = 0 := by
    intro y hy
    apply hf.2.1
    intro hmem
    apply hy
    obtain ⟨h1, h2⟩ := hmem
    rw [le_div_iff₀ hX] at h1
    rw [div_le_iff₀ hX] at h2
    constructor
    · rw [div_le_iff₀ hq']; linarith
    · rw [le_div_iff₀ hq']; linarith
  have hGc : ContDiff ℝ k G := hf.1.comp (by fun_prop)
  have hGcont : Continuous G := hGc.continuous
  have hGsupp : HasCompactSupport G := HasCompactSupport.intro isCompact_Icc hGv
  have hGO : G =O[cocompact ℝ] (|·| ^ (-(2 : ℝ))) := by
    have h0 := hGsupp
    rw [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact] at h0
    exact h0.trans_isBigO (isBigO_zero _ _)
  have hB := Real.one_add_pow_mul_norm_fourier_le hGc
    (fun j hj => integrable_iteratedDeriv_of_vanish hGc hGv hj)
  set B := (∫ v, ‖G v‖) + ((2 * π) ^ k)⁻¹ * ∫ v, ‖iteratedDeriv k G v‖ with hBdef
  have hFGO : (𝓕 G) =O[cocompact ℝ] (|·| ^ (-(2 : ℝ))) := by
    refine IsBigO.of_bound B ?_
    filter_upwards [(tendsto_norm_cocompact_atTop (E := ℝ)).eventually_ge_atTop 1] with ξ hξ
    rw [Real.norm_eq_abs] at hξ
    have hpos : 0 < |ξ| := by linarith
    rw [Real.norm_eq_abs (|ξ| ^ _), abs_of_nonneg (by positivity), Real.rpow_neg hpos.le,
      Real.rpow_two, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    have h1 : |ξ| ^ 2 ≤ 1 + |ξ| ^ k := (pow_le_pow_right₀ hξ hk).trans (by linarith)
    calc ‖𝓕 G ξ‖ * |ξ| ^ 2 ≤ ‖𝓕 G ξ‖ * (1 + |ξ| ^ k) := by gcongr
      _ = (1 + |ξ| ^ k) * ‖𝓕 G ξ‖ := mul_comm _ _
      _ ≤ B := hB ξ
  have hpois := Real.tsum_eq_tsum_fourier_of_rpow_decay hGcont one_lt_two hGO hFGO 0
  have hsum : Summable fun n : ℤ => 𝓕 G n :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      (hFGO.comp_tendsto Int.tendsto_coe_cofinite)
  have hterm : (fun h : ℤ => ((X / q : ℝ) : ℂ) * fourierR f (h * X / q) *
      Complex.exp (2 * π * Complex.I * ((h * c : ℤ) : ℂ) / (q : ℂ))) =
        fun n : ℤ => 𝓕 G n := by
    funext h
    rw [hG, fourier_affine f hX hq' c h, fourierR_eq]
    push_cast
    ring_nf
  have hlhs : (∑' n : ℤ, if n ≡ c [ZMOD (q : ℤ)] then f (n / X) else 0) =
      ∑' n : ℤ, G (0 + n) := by
    have hinj : Function.Injective (fun y : ℤ => c + (q : ℤ) * y) := by
      intro y₁ y₂ h
      have h' : (q : ℤ) * y₁ = (q : ℤ) * y₂ := add_left_cancel h
      exact mul_left_cancel₀ (by exact_mod_cast hq.ne') h'
    rw [← hinj.tsum_eq]
    · congr 1
      funext y
      have hmod : c + (q : ℤ) * y ≡ c [ZMOD (q : ℤ)] := Int.add_mul_emod_self_left c q y
      simp only [hmod, ite_true, hG, zero_add]
      push_cast
      ring_nf
    · intro n hn
      by_cases h : n ≡ c [ZMOD (q : ℤ)]
      · obtain ⟨y, hy⟩ := h.symm.dvd
        exact ⟨y, by simp only; linarith⟩
      · exact (hn (by simp [h])).elim
  rw [hterm, hlhs, hpois]
  simpa [fourier_eval_zero] using hsum.hasSum

/-! ## Mellin separation -/

/-- Derivative bound for `u ↦ f (exp u)` (Faà di Bruno, via `norm_iteratedFDeriv_comp_le`). -/
lemma exp_comp_deriv_bound {f : ℝ → ℂ} {P : ℝ} {k : ℕ} {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hP : 1 ≤ P) (hf : TemperedOn f P k a b)
    (hF : ∀ u, u ∉ Set.Icc (Real.log a) (Real.log b) → f (Real.exp u) = 0) :
    ∀ j ≤ k, ∀ u, ‖iteratedDeriv j (fun u => f (Real.exp u)) u‖ ≤
      k ! * P ^ k * (max 1 b) ^ k := by
  intro j hj u
  have hb : 0 < b := ha.trans hab
  have hP0 : 0 ≤ P := by linarith
  by_cases hu : u ∈ Set.Icc (Real.log a) (Real.log b)
  · have hexp : Real.exp u ≤ b := (Real.le_log_iff_exp_le hb).1 hu.2
    set D := max 1 (Real.exp u) with hDdef
    have hD1 : 1 ≤ D := le_max_left _ _
    have hDb : D ≤ max 1 b := max_le_max le_rfl hexp
    have h := norm_iteratedFDeriv_comp_le (𝕜 := ℝ) (g := f) (f := Real.exp) (n := j)
      (N := k) hf.1 Real.contDiff_exp (by exact_mod_cast hj) u (C := P ^ j) (D := D)
      (fun i hi => by
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
        exact (hf.2.2 i (hi.trans hj) _).trans (pow_le_pow_right₀ hP hi))
      (fun i hi1 _ => by
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate,
          Real.iter_deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos u)]
        exact (le_max_right _ _).trans (le_self_pow₀ hD1 (by omega)))
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at h
    have h1 : ((j ! : ℕ) : ℝ) ≤ (k ! : ℕ) := by exact_mod_cast Nat.factorial_le hj
    have h2 : P ^ j ≤ P ^ k := pow_le_pow_right₀ hP hj
    have h3 : D ^ j ≤ (max 1 b) ^ k :=
      (pow_le_pow_right₀ hD1 hj).trans (pow_le_pow_left₀ (by linarith) hDb k)
    calc ‖iteratedDeriv j (fun u => f (Real.exp u)) u‖
        = ‖iteratedDeriv j (f ∘ Real.exp) u‖ := rfl
      _ ≤ j ! * P ^ j * D ^ j := h
      _ ≤ k ! * P ^ k * (max 1 b) ^ k := by
        apply mul_le_mul (mul_le_mul h1 h2 (by positivity) (by positivity)) h3
          (by positivity) (by positivity)
  · rw [iteratedDeriv_vanish hF j u hu, norm_zero]
    positivity

end Toolkit

open Toolkit

/-- **Mellin separation** (paper Lemma 2.7, one variable), with `k = m + 2`. -/
theorem mellinSeparation : MellinSeparation := by
  intro a b ha hab m
  set k := m + 2 with hkdef
  have hk2 : 2 ≤ k := by omega
  set L := Real.log b - Real.log a with hL
  have hb : 0 < b := ha.trans hab
  have hLpos : 0 < L := sub_pos.2 (Real.log_lt_log ha hab)
  set D := max 1 b with hD
  have hD1 : 1 ≤ D := le_max_left _ _
  refine ⟨(4 * π) ^ k * (k ! * D ^ k) * L, by positivity, k, ?_⟩
  intro f P hP hf
  have hP0 : 0 ≤ P := by linarith
  set F : ℝ → ℂ := fun u => f (Real.exp u) with hFdef
  have hFv : ∀ u, u ∉ Set.Icc (Real.log a) (Real.log b) → F u = 0 := by
    intro u hu
    apply hf.2.1
    intro hmem
    exact hu ⟨(Real.log_le_iff_le_exp ha).2 hmem.1, (Real.le_log_iff_exp_le hb).2 hmem.2⟩
  have hFc : ContDiff ℝ k F := hf.1.comp Real.contDiff_exp
  have hMF := exp_comp_deriv_bound ha hab hP hf hFv
  set B := 2 * (k ! * P ^ k * D ^ k) * L with hBdef
  have hB : ∀ s, (1 + |s| ^ k) * ‖𝓕 F s‖ ≤ B := fun s =>
    fourier_decay_of_bound (Real.log_le_log ha hab.le) hFc hFv hMF s
  have hBnn : 0 ≤ B := by positivity
  have hFi : Integrable F := by
    simpa using integrable_iteratedDeriv_of_vanish hFc hFv (Nat.zero_le k)
  have hFFc : Continuous (𝓕 F) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hFi
  have hFFbound : ∀ s, ‖𝓕 F s‖ ≤ 2 ^ k * B * (1 + s ^ 2)⁻¹ := by
    intro s
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    have h1 := one_add_sq_le_pow s hk2
    have h2 := one_add_pow_le |s| (abs_nonneg s) k
    calc ‖𝓕 F s‖ * (1 + s ^ 2) ≤ ‖𝓕 F s‖ * (2 ^ k * (1 + |s| ^ k)) := by
          gcongr; exact h1.trans h2
      _ = 2 ^ k * ((1 + |s| ^ k) * ‖𝓕 F s‖) := by ring
      _ ≤ 2 ^ k * B := by gcongr; exact hB s
  have hFFi : Integrable (𝓕 F) :=
    (integrable_inv_one_add_sq.const_mul (2 ^ k * B)).mono' hFFc.aestronglyMeasurable
      (ae_of_all _ hFFbound)
  set c₀ : ℝ := -(2 * π)⁻¹ with hc₀
  set g : ℝ → ℂ := fun τ => (((2 * π)⁻¹ : ℝ) : ℂ) * 𝓕 F (c₀ * τ) with hgdef
  have hgc : Continuous g := continuous_const.mul (hFFc.comp (continuous_const.mul continuous_id))
  set K : ℝ := (2 * π)⁻¹ * (4 * π) ^ k * B with hK
  have hpi : 0 < π := pi_pos
  have hg : ∀ τ, (1 + |τ|) ^ m * ‖g τ‖ ≤ K * (1 + τ ^ 2)⁻¹ := by
    intro τ
    have hs : |c₀ * τ| = (2 * π)⁻¹ * |τ| := by
      rw [abs_mul, hc₀, abs_neg, abs_of_pos (by positivity)]
    have hnorm : ‖g τ‖ = (2 * π)⁻¹ * ‖𝓕 F (c₀ * τ)‖ := by
      rw [hgdef, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have e1 : (1 + |τ|) ^ m * (1 + τ ^ 2) ≤ (1 + |τ|) ^ k := by
      have : 1 + τ ^ 2 ≤ (1 + |τ|) ^ 2 := one_add_sq_le_pow τ le_rfl
      calc (1 + |τ|) ^ m * (1 + τ ^ 2) ≤ (1 + |τ|) ^ m * (1 + |τ|) ^ 2 := by gcongr
        _ = (1 + |τ|) ^ k := by rw [hkdef, pow_add]
    have e2 : 1 + |τ| ≤ 2 * π * (1 + |c₀ * τ|) := by
      rw [hs, mul_add, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
      linarith [pi_gt_three]
    have e3 : (1 + |τ|) ^ k ≤ (4 * π) ^ k * (1 + |c₀ * τ| ^ k) := by
      calc (1 + |τ|) ^ k ≤ (2 * π * (1 + |c₀ * τ|)) ^ k :=
            pow_le_pow_left₀ (by positivity) e2 k
        _ = (2 * π) ^ k * (1 + |c₀ * τ|) ^ k := mul_pow _ _ _
        _ ≤ (2 * π) ^ k * (2 ^ k * (1 + |c₀ * τ| ^ k)) := by
            gcongr; exact one_add_pow_le _ (abs_nonneg _) k
        _ = (4 * π) ^ k * (1 + |c₀ * τ| ^ k) := by rw [← mul_assoc, ← mul_pow]; ring_nf
    rw [hnorm, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    calc (1 + |τ|) ^ m * ((2 * π)⁻¹ * ‖𝓕 F (c₀ * τ)‖) * (1 + τ ^ 2)
        = (2 * π)⁻¹ * ‖𝓕 F (c₀ * τ)‖ * ((1 + |τ|) ^ m * (1 + τ ^ 2)) := by ring
      _ ≤ (2 * π)⁻¹ * ‖𝓕 F (c₀ * τ)‖ * ((4 * π) ^ k * (1 + |c₀ * τ| ^ k)) :=
          mul_le_mul_of_nonneg_left (e1.trans e3) (by positivity)
      _ = (2 * π)⁻¹ * (4 * π) ^ k * ((1 + |c₀ * τ| ^ k) * ‖𝓕 F (c₀ * τ)‖) := by ring
      _ ≤ (2 * π)⁻¹ * (4 * π) ^ k * B := by gcongr; exact hB _
  have hmaj : Integrable (fun τ : ℝ => K * (1 + τ ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul K
  have hwc : Continuous (fun τ : ℝ => (1 + |τ|) ^ m * ‖g τ‖) := by fun_prop
  refine ⟨g, ?_, ?_, ?_⟩
  · refine hmaj.mono' hwc.aestronglyMeasurable (ae_of_all _ fun τ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hg τ
  · calc ∫ τ, (1 + |τ|) ^ m * ‖g τ‖ ≤ ∫ τ, K * (1 + τ ^ 2)⁻¹ :=
          integral_mono_of_nonneg (ae_of_all _ fun τ => by positivity) hmaj (ae_of_all _ hg)
      _ = K * π := by rw [integral_const_mul, integral_univ_inv_one_add_sq]
      _ = (4 * π) ^ k * (k ! * D ^ k) * L * P ^ k := by
          rw [hK, hBdef]
          field_simp
  · intro t ht
    have hinv := congrFun (Continuous.fourierInv_fourier_eq hFc.continuous hFi hFFi) (Real.log t)
    have e1 : f t = F (Real.log t) := by simp [hFdef, Real.exp_log ht]
    rw [e1, ← hinv, Real.fourierInv_eq']
    set H : ℝ → ℂ := fun v => Complex.exp (↑(2 * π * inner ℝ v (Real.log t)) * Complex.I) •
      𝓕 F v with hH
    have key : ∀ τ, g τ * Complex.exp (-(τ * Real.log t : ℝ) * Complex.I) =
        ((2 * π)⁻¹ : ℝ) • H (c₀ * τ) := by
      intro τ
      simp only [hgdef, hH, hc₀, Complex.real_smul, smul_eq_mul]
      have : (2 * π * inner ℝ (-(2 * π)⁻¹ * τ) (Real.log t) : ℝ) = -(τ * Real.log t) := by
        rw [Real.inner_apply]
        field_simp
      rw [this, Complex.ofReal_neg]
      ring
    simp_rw [key]
    rw [integral_smul, Measure.integral_comp_mul_left H c₀, smul_smul, hc₀, inv_neg, inv_inv,
      abs_neg, abs_of_pos (by positivity), inv_mul_cancel₀ (by positivity), one_smul]

/-- **Poisson summation in a residue class, with Fourier decay** (paper Lemma 2.2). -/
theorem poissonAPDecay : PoissonAPDecay := by
  intro a b _ha hab k hk
  refine ⟨2 ^ (k + 1) * (b - a), by have := sub_pos.2 hab; positivity, ?_⟩
  intro f P hP hf
  exact ⟨fun ξ => tempered_fourier_bound hab hP hf ξ,
    fun X hX q hq c => poisson_AP hk hf hX hq c⟩

end MobiusDeterminant
