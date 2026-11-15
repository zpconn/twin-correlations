import MobiusDeterminant.Unconditional.PNTMobiusSmoothed

/-!
# Contour shift for the smoothed Mertens sum

We shift the Perron integral `∫_{(σ₀)} (1/ζ)(s) 𝓜(ν_ε)(s) X^s ds` (`σ₀ > 1`) to the rectangle
contour `σ₁ + i[-T,T]` (with `σ₁ = 1 - δ/log T` inside the zero-free region), plus two
horizontal segments at height `±T` and the two tails `σ₀ + i(|t| > T)`.  Unlike for `-ζ'/ζ`,
`1/ζ` has no pole at `s = 1` (`invZeta` fills in the removable singularity), so there is no
main term.  The result is `mobius_integral_bound`:

  `‖∫ (1/ζ)(σ₀+it) 𝓜(ν_ε)(σ₀+it) X^{σ₀+it} dt‖ ≤
      K/ε · (X^{σ₀}(1+T)^{-1/2}/(σ₀-1) + X^{σ₀}(1+T)^{-1/2} + X^{σ₁})`.
-/

open Complex Real Set Filter Topology MeasureTheory
open scoped ArithmeticFunction.Moebius Interval

namespace MobiusDeterminant
namespace PNTMobiusAux

local notation "𝓜" => mellin

/-! ## Elementary estimates -/

lemma one_add_abs_im_sq_le {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    (1 + |s.im|) ^ 2 ≤ 8 * ‖s‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  have h1 : 2 * |s.im| ≤ 1 + s.im ^ 2 := by
    nlinarith [sq_abs s.im, sq_nonneg (|s.im| - 1)]
  have h2 : (1 : ℝ) / 4 ≤ s.re * s.re := by nlinarith
  nlinarith [sq_abs s.im]

lemma rpow_half_mul_inv_sq {a : ℝ} (ha : 0 < a) :
    a ^ (1 / 2 : ℝ) * (a ^ 2)⁻¹ = a ^ (-(3 / 2) : ℝ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_neg ha.le, ← Real.rpow_add ha]; norm_num

lemma inv_sq_eq_rpow_mul {a : ℝ} (ha : 0 < a) :
    (a ^ 2)⁻¹ = a ^ (-(3 / 2) : ℝ) * a ^ (-(1 / 2) : ℝ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_neg ha.le, ← Real.rpow_add ha]; norm_num

lemma mellin_smooth_bound {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Icc (1 / 2) 2) :
    ∃ Cm > 0, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 →
      ‖𝓜 (fun x => (Smooth1 ν ε x : ℂ)) s‖ ≤ Cm / ε * ((1 + |s.im|) ^ 2)⁻¹ := by
  obtain ⟨C, Cpos, hC⟩ := MellinOfSmooth1b diffν suppν
  refine ⟨8 * C, by positivity, fun ε εpos ε1 s hs1 hs2 => ?_⟩
  have h := hC (1 / 2) (by norm_num) s hs1 hs2 ε εpos ε1
  have hsq := one_add_abs_im_sq_le hs1
  have hpos : 0 < (1 + |s.im|) ^ 2 := by positivity
  have hs0 : 0 < ‖s‖ ^ 2 := by nlinarith
  have hsne : ‖s‖ ≠ 0 := by intro h; rw [h] at hs0; norm_num at hs0
  have key : (‖s‖ ^ 2)⁻¹ ≤ 8 * ((1 + |s.im|) ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hpos]
    calc (‖s‖ ^ 2)⁻¹ * (1 + |s.im|) ^ 2 ≤ (‖s‖ ^ 2)⁻¹ * (8 * ‖s‖ ^ 2) := by gcongr
      _ = 8 := by field_simp
  calc _ ≤ C * (ε * ‖s‖ ^ 2)⁻¹ := h
    _ = C * ε⁻¹ * (‖s‖ ^ 2)⁻¹ := by rw [mul_inv]; ring
    _ ≤ C * ε⁻¹ * (8 * ((1 + |s.im|) ^ 2)⁻¹) := by gcongr
    _ = 8 * C / ε * ((1 + |s.im|) ^ 2)⁻¹ := by ring

section integrand

variable {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν) (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : Function.support ν ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
include diffν νpos suppν mass_one

lemma continuousAt_mobIntegrand {ε X : ℝ} (εpos : 0 < ε) (ε1 : ε < 1) (X_pos : 0 < X)
    {s : ℂ} (hs : 0 < s.re) (hz : riemannZeta s ≠ 0) :
    ContinuousAt (mobIntegrand ν ε X) s := by
  have hX : (X : ℂ) ≠ 0 := by exact_mod_cast X_pos.ne'
  exact ((continuousAt_invZeta hz).mul (Smooth1MellinDifferentiable diffν suppν ⟨εpos, ε1⟩
    νpos mass_one hs).continuousAt).mul (continuousAt_const_cpow hX)

lemma differentiableAt_mobIntegrand {ε X : ℝ} (εpos : 0 < ε) (ε1 : ε < 1) (X_pos : 0 < X)
    {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    DifferentiableAt ℂ (mobIntegrand ν ε X) s := by
  have hX : (X : ℂ) ≠ 0 := by exact_mod_cast X_pos.ne'
  exact ((differentiableAt_invZeta hs1 hz).mul (Smooth1MellinDifferentiable diffν suppν
    ⟨εpos, ε1⟩ νpos mass_one hs)).mul (differentiableAt_id.const_cpow (Or.inl hX))

/-- Cauchy's theorem on the rectangle `[σ₁, σ₀] × [-T, T]`. -/
lemma mobIntegrand_rect_bound {X ε σ₁ σ₀ T : ℝ} (X_pos : 0 < X) (εpos : 0 < ε) (ε1 : ε < 1)
    (σ₁pos : 0 < σ₁) (hσ : σ₁ ≤ σ₀) (hT : 0 ≤ T)
    (hnz : ∀ σ t : ℝ, σ₁ ≤ σ → σ ≤ σ₀ → |t| ≤ T → riemannZeta (σ + t * I) ≠ 0) :
    ‖∫ y : ℝ in (-T)..T, mobIntegrand ν ε X (σ₀ + y * I)‖ ≤
      ‖∫ y : ℝ in (-T)..T, mobIntegrand ν ε X (σ₁ + y * I)‖ +
      ‖∫ x : ℝ in σ₁..σ₀, mobIntegrand ν ε X (x + ((-T : ℝ) : ℂ) * I)‖ +
      ‖∫ x : ℝ in σ₁..σ₀, mobIntegrand ν ε X (x + (T : ℂ) * I)‖ := by
  set z : ℂ := (σ₁ : ℂ) + ((-T : ℝ) : ℂ) * I with hz
  set w : ℂ := (σ₀ : ℂ) + (T : ℂ) * I with hw
  have hzre : z.re = σ₁ := by simp [hz]
  have hzim : z.im = -T := by simp [hz]
  have hwre : w.re = σ₀ := by simp [hw]
  have hwim : w.im = T := by simp [hw]
  have hmem : ∀ s ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]],
      σ₁ ≤ s.re ∧ s.re ≤ σ₀ ∧ |s.im| ≤ T := by
    intro s hs
    rw [hzre, hzim, hwre, hwim, uIcc_of_le hσ, uIcc_of_le (by linarith)] at hs
    simp only [mem_reProdIm, mem_Icc] at hs
    exact ⟨hs.1.1, hs.1.2, abs_le.mpr hs.2⟩
  have hnz' : ∀ s ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]], riemannZeta s ≠ 0 := by
    intro s hs
    obtain ⟨h1, h2, h3⟩ := hmem s hs
    rw [← re_add_im s]; exact hnz _ _ h1 h2 h3
  have key := integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
    (mobIntegrand ν ε X) z w {1} (countable_singleton 1) ?_ ?_
  · rw [hzre, hzim, hwre, hwim] at key
    simp only [smul_eq_mul] at key
    set A := ∫ x : ℝ in σ₁..σ₀, mobIntegrand ν ε X (x + ((-T : ℝ) : ℂ) * I)
    set B := ∫ x : ℝ in σ₁..σ₀, mobIntegrand ν ε X (x + (T : ℂ) * I)
    set Cc := ∫ y : ℝ in (-T)..T, mobIntegrand ν ε X (σ₀ + y * I)
    set D := ∫ y : ℝ in (-T)..T, mobIntegrand ν ε X (σ₁ + y * I)
    have hA : A = ∫ x : ℝ in σ₁..σ₀, mobIntegrand ν ε X (x + (-T : ℝ) * I) := rfl
    have e : Cc = D + I * (A - B) := by
      linear_combination (-I) * key + (Cc - D) * I_sq
    rw [e]
    calc ‖D + I * (A - B)‖ ≤ ‖D‖ + ‖I * (A - B)‖ := norm_add_le _ _
      _ ≤ ‖D‖ + (‖A‖ + ‖B‖) := by
          rw [norm_mul, Complex.norm_I, one_mul]; gcongr; exact norm_sub_le A B
      _ = _ := by ring
  · intro s hs
    exact (continuousAt_mobIntegrand diffν νpos suppν mass_one εpos ε1 X_pos
      (by linarith [(hmem s hs).1]) (hnz' s hs)).continuousWithinAt
  · intro s hs
    have hs' : s ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]] :=
      ⟨Ioo_subset_Icc_self hs.1.1, Ioo_subset_Icc_self hs.1.2⟩
    exact differentiableAt_mobIntegrand diffν νpos suppν mass_one εpos ε1 X_pos
      (by linarith [(hmem s hs').1]) hs.2 (hnz' s hs')

/-- **Bound for the Perron integral of `1/ζ` after the contour shift.** -/
theorem mobius_integral_bound :
    ∃ dl > 0, dl ≤ 1 / 2 ∧ ∃ σ₂ < 1, ∃ K > 0, ∀ X ε T σ₁ σ₀ : ℝ, 1 ≤ X → 0 < ε → ε < 1 →
      3 ≤ T → 1 / 2 ≤ σ₁ → σ₂ ≤ σ₁ → σ₁ < 1 → 1 - dl / Real.log T ≤ σ₁ → 1 < σ₀ → σ₀ ≤ 2 →
      ‖∫ t : ℝ, mobIntegrand ν ε X (σ₀ + t * I)‖ ≤
        K / ε * (X ^ σ₀ * (1 + T) ^ (-(1 / 2) : ℝ) / (σ₀ - 1) +
          X ^ σ₀ * (1 + T) ^ (-(1 / 2) : ℝ) + X ^ σ₁) := by
  obtain ⟨dl, dlpos, dlle, σ₂, hσ₂, C, Cpos, hinv⟩ := inv_zeta_bound
  obtain ⟨cz, czpos, hcz⟩ := norm_inv_zeta_le_of_one_lt
  obtain ⟨Cm, Cmpos, hCm⟩ := mellin_smooth_bound diffν suppν
  set g : ℝ → ℝ := fun t => (1 + |t|) ^ (-(3 / 2) : ℝ) with hg
  have gint : Integrable g := by
    have : Integrable (fun x : ℝ => (1 + ‖x‖) ^ (-(3 / 2 : ℝ))) :=
      integrable_one_add_norm (by norm_num)
    simpa [hg, Real.norm_eq_abs] using this
  have gnn : ∀ t, 0 ≤ g t := fun t => Real.rpow_nonneg (by positivity) _
  set J := ∫ t, g t with hJ
  have Jnn : 0 ≤ J := integral_nonneg gnn
  refine ⟨dl, dlpos, dlle, σ₂, hσ₂, Cm * (cz * J + 4 * C + C * J), by positivity, ?_⟩
  intro X ε T σ₁ σ₀ hX εpos ε1 hT hσ₁h hσ₂σ₁ hσ₁1 hσ₁dl hσ₀1 hσ₀2
  have X_pos : 0 < X := by linarith
  have Tpos : 0 < T := by linarith
  set W : ℝ := (1 + T) ^ (-(1 / 2) : ℝ) with hW
  have Wnn : 0 ≤ W := Real.rpow_nonneg (by positivity) _
  -- the region where `1/ζ` is controlled
  have hreg : ∀ σ t : ℝ, σ₁ ≤ σ → σ ≤ 2 → |t| ≤ T →
      riemannZeta (σ + t * I) ≠ 0 ∧ ‖invZeta (σ + t * I)‖ ≤ C * (1 + |t|) ^ (1 / 2 : ℝ) := by
    intro σ t h1 h2 h3
    apply hinv σ t h2 (fun _ => le_trans hσ₂σ₁ h1)
    intro ht3
    have hlogt : 0 < Real.log |t| := Real.log_pos (by linarith)
    have hlogT : Real.log |t| ≤ Real.log T := Real.log_le_log (by linarith) h3
    have : dl / Real.log T ≤ dl / Real.log |t| := div_le_div_of_nonneg_left dlpos.le hlogt hlogT
    linarith
  -- pointwise bound for the integrand
  have hpt : ∀ σ t A : ℝ, 1 / 2 ≤ σ → σ ≤ 2 → ‖invZeta (σ + t * I)‖ ≤ A →
      ‖mobIntegrand ν ε X (σ + t * I)‖ ≤ A * (Cm / ε * ((1 + |t|) ^ 2)⁻¹) * X ^ σ := by
    intro σ t A h1 h2 hA
    have hre : ((σ : ℂ) + t * I).re = σ := by simp
    have him : ((σ : ℂ) + t * I).im = t := by simp
    have hM := hCm ε εpos ε1 (σ + t * I) (by rw [hre]; exact h1) (by rw [hre]; exact h2)
    rw [him] at hM
    simp only [mobIntegrand, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos X_pos, hre]
    gcongr
    exact (norm_nonneg _).trans hA
  ---------------------------------------------------------------- the line `σ₀`
  set f : ℝ → ℂ := fun t => mobIntegrand ν ε X (σ₀ + t * I) with hf
  set cA : ℝ := cz / (σ₀ - 1) * (Cm / ε) * X ^ σ₀ with hcA
  have cAnn : 0 ≤ cA := by
    have : 0 < σ₀ - 1 := by linarith
    positivity
  have hf_bd : ∀ t, ‖f t‖ ≤ cA * ((1 + |t|) ^ 2)⁻¹ := by
    intro t
    have hs1 : (σ₀ : ℂ) + t * I ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hA : ‖invZeta (σ₀ + t * I)‖ ≤ cz / (σ₀ - 1) := by
      rw [invZeta_of_ne hs1]; exact hcz σ₀ t hσ₀1 hσ₀2
    have h := hpt σ₀ t (cz / (σ₀ - 1)) (by linarith) hσ₀2 hA
    simp only [hf]
    calc _ ≤ _ := h
      _ = cA * ((1 + |t|) ^ 2)⁻¹ := by rw [hcA]; ring
  have hsq_le_g : ∀ t : ℝ, ((1 + |t|) ^ 2)⁻¹ ≤ g t := by
    intro t
    have ha : 0 < 1 + |t| := by positivity
    rw [inv_sq_eq_rpow_mul ha]
    have : (1 + |t|) ^ (-(1 / 2) : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg t]) (by norm_num)
    calc (1 + |t|) ^ (-(3 / 2) : ℝ) * (1 + |t|) ^ (-(1 / 2) : ℝ)
        ≤ (1 + |t|) ^ (-(3 / 2) : ℝ) * 1 := by gcongr
      _ = g t := by rw [mul_one]
  have hf_cont : Continuous f := by
    rw [continuous_iff_continuousAt]; intro t
    have hre : ((σ₀ : ℂ) + t * I).re = σ₀ := by simp
    have hz : riemannZeta (σ₀ + t * I) ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re (by rw [hre]; linarith)
    have h1 := continuousAt_mobIntegrand diffν νpos suppν mass_one εpos ε1 X_pos
      (s := σ₀ + t * I) (by rw [hre]; linarith) hz
    have h2 : ContinuousAt (fun t : ℝ => (σ₀ : ℂ) + t * I) t := by fun_prop
    exact ContinuousAt.comp (f := fun t : ℝ => (σ₀ : ℂ) + t * I) (g := mobIntegrand ν ε X)
      (x := t) h1 h2
  have hf_int : Integrable f :=
    (gint.const_mul cA).mono' hf_cont.aestronglyMeasurable
      (ae_of_all _ fun t => (hf_bd t).trans (by gcongr; exact hsq_le_g t))
  have hsplit : ∫ t, f t = (∫ t in (-T)..T, f t) + ∫ t in (Ioc (-T) T)ᶜ, f t := by
    rw [intervalIntegral.integral_of_le (by linarith),
      integral_add_compl measurableSet_Ioc hf_int]
  -- tails `|t| > T`
  have htail : ‖∫ t in (Ioc (-T) T)ᶜ, f t‖ ≤ cA * W * J := by
    calc ‖∫ t in (Ioc (-T) T)ᶜ, f t‖ ≤ ∫ t in (Ioc (-T) T)ᶜ, cA * W * g t := by
          apply norm_integral_le_of_norm_le ((gint.const_mul _).integrableOn)
          rw [ae_restrict_iff' measurableSet_Ioc.compl]
          refine ae_of_all _ fun t ht => ?_
          have hTt : T ≤ |t| := by
            simp only [mem_compl_iff, mem_Ioc, not_and_or, not_lt, not_le] at ht
            rcases ht with h | h
            · rw [abs_of_neg (by linarith)]; linarith
            · rw [abs_of_pos (by linarith)]; linarith
          have ha : 0 < 1 + |t| := by positivity
          have hw : (1 + |t|) ^ (-(1 / 2) : ℝ) ≤ W :=
            Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
          calc ‖f t‖ ≤ cA * ((1 + |t|) ^ 2)⁻¹ := hf_bd t
            _ = cA * (g t * (1 + |t|) ^ (-(1 / 2) : ℝ)) := by rw [inv_sq_eq_rpow_mul ha]
            _ ≤ cA * (g t * W) := by gcongr
            _ = cA * W * g t := by ring
      _ ≤ ∫ t, cA * W * g t :=
          setIntegral_le_integral (gint.const_mul _)
            (ae_of_all _ fun t => mul_nonneg (mul_nonneg cAnn Wnn) (gnn t))
      _ = cA * W * J := integral_const_mul _ _
  -- the vertical segment `σ₁ + i[-T,T]`
  have hV : ‖∫ t in (-T)..T, mobIntegrand ν ε X (σ₁ + t * I)‖ ≤ C * (Cm / ε) * X ^ σ₁ * J := by
    calc ‖∫ t in (-T)..T, mobIntegrand ν ε X (σ₁ + t * I)‖
        ≤ ∫ t in (-T)..T, C * (Cm / ε) * X ^ σ₁ * g t := by
          refine intervalIntegral.norm_integral_le_of_norm_le (by linarith)
            (ae_of_all _ fun t ht => ?_) (gint.const_mul _).intervalIntegrable
          have htT : |t| ≤ T := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
          have hA := (hreg σ₁ t le_rfl (by linarith) htT).2
          have h := hpt σ₁ t _ hσ₁h (by linarith) hA
          have ha : 0 < 1 + |t| := by positivity
          calc _ ≤ _ := h
            _ = C * (Cm / ε) * X ^ σ₁ * ((1 + |t|) ^ (1 / 2 : ℝ) * ((1 + |t|) ^ 2)⁻¹) := by
                ring
            _ = C * (Cm / ε) * X ^ σ₁ * g t := by rw [rpow_half_mul_inv_sq ha]
      _ ≤ ∫ t, C * (Cm / ε) * X ^ σ₁ * g t := by
          rw [intervalIntegral.integral_of_le (by linarith)]
          exact setIntegral_le_integral (gint.const_mul _)
            (ae_of_all _ fun t => mul_nonneg (by positivity) (gnn t))
      _ = C * (Cm / ε) * X ^ σ₁ * J := integral_const_mul _ _
  -- the horizontal segments at height `±T`
  have hH : ∀ τ : ℝ, |τ| = T →
      ‖∫ x : ℝ in σ₁..σ₀, mobIntegrand ν ε X (x + (τ : ℂ) * I)‖ ≤
        2 * (C * (Cm / ε) * X ^ σ₀ * W) := by
    intro τ hτ
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun x : ℝ => mobIntegrand ν ε X (x + (τ : ℂ) * I))
      (C := C * (Cm / ε) * X ^ σ₀ * W) (a := σ₁) (b := σ₀) (fun x hx => ?_)
    · calc _ ≤ C * (Cm / ε) * X ^ σ₀ * W * |σ₀ - σ₁| := h
        _ ≤ C * (Cm / ε) * X ^ σ₀ * W * 2 := by
            gcongr; rw [abs_of_nonneg (by linarith)]; linarith
        _ = _ := by ring
    · rw [uIoc_of_le (by linarith)] at hx
      have hA := (hreg x τ hx.1.le (by linarith [hx.2]) hτ.le).2
      have h1 := hpt x τ _ (by linarith [hx.1]) (by linarith [hx.2]) hA
      have hT1 : 0 < 1 + T := by linarith
      rw [hτ] at h1
      have e1 : (1 + T) ^ (1 / 2 : ℝ) * ((1 + T) ^ 2)⁻¹ = (1 + T) ^ (-(3 / 2) : ℝ) :=
        rpow_half_mul_inv_sq hT1
      have e2 : (1 + T) ^ (-(3 / 2) : ℝ) ≤ W :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      have e3 : X ^ x ≤ X ^ σ₀ := Real.rpow_le_rpow_of_exponent_le hX hx.2
      calc ‖mobIntegrand ν ε X (x + (τ : ℂ) * I)‖
          ≤ C * (1 + T) ^ (1 / 2 : ℝ) * (Cm / ε * ((1 + T) ^ 2)⁻¹) * X ^ x := h1
        _ = C * (Cm / ε) * X ^ x * ((1 + T) ^ (1 / 2 : ℝ) * ((1 + T) ^ 2)⁻¹) := by ring
        _ = C * (Cm / ε) * X ^ x * (1 + T) ^ (-(3 / 2) : ℝ) := by rw [e1]
        _ ≤ C * (Cm / ε) * X ^ σ₀ * W := by gcongr
  have hrect := mobIntegrand_rect_bound diffν νpos suppν mass_one X_pos εpos ε1
    (by linarith : (0 : ℝ) < σ₁) (by linarith : σ₁ ≤ σ₀) Tpos.le
    (fun σ t h1 h2 h3 => (hreg σ t h1 (by linarith) h3).1)
  have hHm := hH (-T) (by rw [abs_neg, abs_of_pos Tpos])
  have hHp := hH T (abs_of_pos Tpos)
  -- assembly
  have hσ₀1' : 0 < σ₀ - 1 := by linarith
  set a := X ^ σ₀ * W / (σ₀ - 1) with ha
  set b := X ^ σ₀ * W with hb
  set c := X ^ σ₁ with hc
  have hann : 0 ≤ a := by positivity
  have hbnn : 0 ≤ b := by positivity
  have hcnn : 0 ≤ c := by positivity
  have htotal : ‖∫ t : ℝ, mobIntegrand ν ε X (σ₀ + t * I)‖ ≤
      Cm / ε * ((cz * J) * a + (4 * C) * b + (C * J) * c) := by
    have e : ∫ t : ℝ, mobIntegrand ν ε X (σ₀ + t * I) = ∫ t, f t := rfl
    rw [e, hsplit]
    calc ‖(∫ t in (-T)..T, f t) + ∫ t in (Ioc (-T) T)ᶜ, f t‖
        ≤ ‖∫ t in (-T)..T, f t‖ + ‖∫ t in (Ioc (-T) T)ᶜ, f t‖ := norm_add_le _ _
      _ ≤ (C * (Cm / ε) * X ^ σ₁ * J + 2 * (C * (Cm / ε) * X ^ σ₀ * W) +
            2 * (C * (Cm / ε) * X ^ σ₀ * W)) + cA * W * J := by
          gcongr
          exact hrect.trans (by gcongr)
      _ = Cm / ε * ((cz * J) * a + (4 * C) * b + (C * J) * c) := by
          rw [ha, hb, hc, hcA]; field_simp; ring
  refine htotal.trans ?_
  have hp : 0 ≤ cz * J := by positivity
  have hq : 0 ≤ 4 * C := by positivity
  have hr : 0 ≤ C * J := by positivity
  calc Cm / ε * ((cz * J) * a + (4 * C) * b + (C * J) * c)
      ≤ Cm / ε * ((cz * J + 4 * C + C * J) * (a + b + c)) := by
        gcongr
        nlinarith [mul_nonneg hp hbnn, mul_nonneg hp hcnn, mul_nonneg hq hann,
          mul_nonneg hq hcnn, mul_nonneg hr hann, mul_nonneg hr hbnn]
    _ = Cm * (cz * J + 4 * C + C * J) / ε * (a + b + c) := by ring

end integrand

end PNTMobiusAux
end MobiusDeterminant
