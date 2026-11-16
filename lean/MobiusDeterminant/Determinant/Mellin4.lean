import MobiusDeterminant.Determinant.Defs
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.Inversion

/-!
# Four-variable Mellin separation (`MellinSep4`)

For `W` smooth and supported in `[1,2]⁴`, put
`f u = W (exp (-2π u₀), exp (-2π u₁), exp (-2π u₂), exp (-2π u₃))` on `EuclideanSpace ℝ (Fin 4)`.
It is smooth with compact support, hence Schwartz, so its Fourier transform `g = 𝓕 f` is
Schwartz (integrable against every polynomial weight).  Fourier inversion
`f v = ∫ 𝐞 ⟪w, v⟫ • g w dw` at `v = -(log α, log β, log δ, log ε)/(2π)` is exactly the
required separation `W(α,β,δ,ε) = ∫ g(τ) exp(-i Σ τⱼ log αⱼ) dτ`; the normalisation
`-2π` in `f` makes no further change of variables necessary.
-/

open MeasureTheory Real
open scoped ContDiff FourierTransform RealInnerProductSpace SchwartzMap

namespace MobiusDeterminant.Determinant

namespace Mellin4

/-- The exponential change of coordinates `u ↦ (exp (-2π uⱼ))ⱼ`. -/
noncomputable def expMap (u : EuclideanSpace ℝ (Fin 4)) : ℝ × ℝ × ℝ × ℝ :=
  (Real.exp (-(2 * π) * u 0), Real.exp (-(2 * π) * u 1), Real.exp (-(2 * π) * u 2),
    Real.exp (-(2 * π) * u 3))

lemma contDiff_expMap : ContDiff ℝ ∞ expMap := by
  have h : ∀ j : Fin 4,
      ContDiff ℝ ∞ (fun u : EuclideanSpace ℝ (Fin 4) => Real.exp (-(2 * π) * u j)) := fun j =>
    Real.contDiff_exp.comp (contDiff_const.mul (contDiff_piLp_apply 2))
  exact (h 0).prodMk ((h 1).prodMk ((h 2).prodMk (h 3)))

/-- If `exp (-2π t) ∈ [1,2]` then `t ∈ [-1, 0]`. -/
lemma mem_Icc_of_exp_mem {t : ℝ} (h : Real.exp (-(2 * π) * t) ∈ Set.Icc (1 : ℝ) 2) :
    t ∈ Set.Icc (-1 : ℝ) 0 := by
  obtain ⟨h1, h2⟩ := h
  have hpi := Real.pi_gt_three
  have h0 : 0 ≤ -(2 * π) * t := Real.one_le_exp_iff.mp h1
  have h3 : -(2 * π) * t + 1 ≤ 2 := (Real.add_one_le_exp _).trans h2
  constructor <;> nlinarith

lemma hasCompactSupport_comp {W : ℝ × ℝ × ℝ × ℝ → ℂ} (hW : SmoothWeight W) :
    HasCompactSupport (fun u => W (expMap u)) := by
  let K : Set (EuclideanSpace ℝ (Fin 4)) :=
    WithLp.toLp 2 '' Set.univ.pi (fun _ => Set.Icc (-1 : ℝ) 0)
  have hK : IsCompact K :=
    (isCompact_univ_pi fun _ => isCompact_Icc).image (PiLp.continuous_toLp 2 _)
  refine HasCompactSupport.intro hK fun u hu => ?_
  by_contra hne
  obtain ⟨h0, h1, h2, h3⟩ := hW.2 _ hne
  refine hu ⟨u.ofLp, ?_, WithLp.toLp_ofLp (p := 2) u⟩
  simp only [Set.mem_pi, Set.mem_univ, true_implies]
  intro j
  fin_cases j
  · exact mem_Icc_of_exp_mem h0
  · exact mem_Icc_of_exp_mem h1
  · exact mem_Icc_of_exp_mem h2
  · exact mem_Icc_of_exp_mem h3

lemma integrable_one_add_norm_pow_mul (g : 𝓢(EuclideanSpace ℝ (Fin 4), ℂ)) (m : ℕ) :
    Integrable (fun τ : EuclideanSpace ℝ (Fin 4) => (1 + ‖τ‖) ^ m * ‖g τ‖) := by
  have : (fun τ : EuclideanSpace ℝ (Fin 4) => (1 + ‖τ‖) ^ m * ‖g τ‖) =
      fun τ => ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) * (‖τ‖ ^ k * ‖g τ‖) := by
    funext τ
    rw [add_comm, add_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [one_pow, mul_one]
    ring
  rw [this]
  exact integrable_finsetSum _ fun k _ => (g.integrable_pow_mul volume k).const_mul _

/-- Fourier inversion at `v = -(log α, log β, log δ, log ε)/(2π)`. -/
lemma separation (W : ℝ × ℝ × ℝ × ℝ → ℂ) (F : 𝓢(EuclideanSpace ℝ (Fin 4), ℂ))
    (hF : ∀ u, F u = W (expMap u)) (α β δ ε : ℝ) (hα : 0 < α) (hβ : 0 < β) (hδ : 0 < δ)
    (hε : 0 < ε) :
    W (α, β, δ, ε) = ∫ τ, (𝓕 F : 𝓢(EuclideanSpace ℝ (Fin 4), ℂ)) τ * Complex.exp
      (-((τ 0 * Real.log α + τ 1 * Real.log β + τ 2 * Real.log δ + τ 3 * Real.log ε : ℝ) : ℂ)
        * Complex.I) := by
  let v : EuclideanSpace ℝ (Fin 4) :=
    WithLp.toLp 2 ![-Real.log α / (2 * π), -Real.log β / (2 * π), -Real.log δ / (2 * π),
      -Real.log ε / (2 * π)]
  have hpi : (2 * π) ≠ 0 := by positivity
  have hexp : ∀ x : ℝ, 0 < x → Real.exp (-(2 * π) * (-Real.log x / (2 * π))) = x := by
    intro x hx
    rw [show -(2 * π) * (-Real.log x / (2 * π)) = Real.log x by field_simp]
    exact Real.exp_log hx
  have hv0 : v 0 = -Real.log α / (2 * π) := rfl
  have hv1 : v 1 = -Real.log β / (2 * π) := rfl
  have hv2 : v 2 = -Real.log δ / (2 * π) := rfl
  have hv3 : v 3 = -Real.log ε / (2 * π) := rfl
  have h1 : W (α, β, δ, ε) = F v := by
    rw [hF]
    simp only [expMap, hv0, hv1, hv2, hv3, hexp α hα, hexp β hβ, hexp δ hδ, hexp ε hε]
  have hinv : (𝓕⁻ (𝓕 F : 𝓢(EuclideanSpace ℝ (Fin 4), ℂ)) : 𝓢(EuclideanSpace ℝ (Fin 4), ℂ)) = F :=
    FourierTransform.fourierInv_fourier_eq F
  rw [h1, ← DFunLike.congr_fun hinv v, SchwartzMap.fourierInv_coe,
    fourierInv_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  have hinner : 2 * π * ⟪w, v⟫ =
      -(w 0 * Real.log α + w 1 * Real.log β + w 2 * Real.log δ + w 3 * Real.log ε) := by
    simp only [PiLp.inner_apply, Fin.sum_univ_four, hv0, hv1, hv2, hv3, RCLike.inner_apply,
      conj_trivial]
    field_simp
    ring
  dsimp only
  rw [smul_eq_mul, hinner, Complex.ofReal_neg]
  exact mul_comm _ _

end Mellin4

open Mellin4 in
theorem mellinSep4 : MellinSep4 := by
  intro W hW
  have hfs : ContDiff ℝ ∞ (fun u => W (expMap u)) := hW.1.comp contDiff_expMap
  obtain ⟨F, hF⟩ : ∃ F : 𝓢(EuclideanSpace ℝ (Fin 4), ℂ), ∀ u, F u = W (expMap u) :=
    ⟨(hasCompactSupport_comp hW).toSchwartzMap hfs, fun _ => rfl⟩
  exact ⟨⇑(𝓕 F : 𝓢(EuclideanSpace ℝ (Fin 4), ℂ)), integrable_one_add_norm_pow_mul _,
    separation W F hF⟩
