import PrimeNumberTheoremAnd.StrongPNT
import Mathlib.Analysis.ODE.Gronwall

/-!
# Bounds for `1/ζ` near the line `Re s = 1`

Ingredients for the prime number theorem for `μ` with classical error term
(`MobiusDeterminant.pntMobius`), derived from PNT+ (Kontorovich–Tao):

* `invZeta`: `1/ζ` with its removable singularity at `s = 1` filled in (value `0`);
* `norm_inv_zeta_le_norm_zeta_re`: `‖ζ(σ+it)⁻¹‖ ≤ ‖ζ(σ)‖` for `σ > 1` (Dirichlet series of `μ`);
* `inv_zeta_gronwall`: integrating `ζ'/ζ` horizontally (Grönwall) controls `1/ζ` to the left;
* `inv_zeta_bound`: there are `dl > 0`, `σ₂ < 1`, `C` with `ζ(σ+it) ≠ 0` and
  `‖invZeta(σ+it)‖ ≤ C (1+|t|)^{1/2}` whenever `σ ≤ 2`, `σ ≥ σ₂` (if `|t| ≤ 3`) and
  `σ ≥ 1 - dl/log|t|` (if `|t| > 3`).

The polynomial loss `|t|^{1/2}` comes from integrating PNT+'s bound
`ζ'/ζ ≪ log² |t|` (`LogDerivZetaUniformLogSquaredBound`, valid in the de la Vallée Poussin
region `σ ≥ 1 - F/log|t|`) over a horizontal segment of length `≍ dl/log|t|` with `dl` small.
It is harmless because the Mellin transform of the smoothing decays like `|s|^{-2}`.
-/

open Complex Real Set Filter Topology
open scoped ArithmeticFunction.Moebius LSeries.notation

namespace MobiusDeterminant
namespace PNTMobiusAux

/-- `1/ζ(s)`, with the removable singularity at `s = 1` filled in by `0`. -/
noncomputable def invZeta : ℂ → ℂ := Function.update (fun s => (riemannZeta s)⁻¹) 1 0

lemma invZeta_of_ne {s : ℂ} (hs : s ≠ 1) : invZeta s = (riemannZeta s)⁻¹ := by
  simp [invZeta, Function.update_of_ne hs]

lemma tendsto_inv_riemannZeta_one :
    Tendsto (fun s => (riemannZeta s)⁻¹) (𝓝[≠] 1) (𝓝 0) := by
  have h1 : Tendsto (fun s : ℂ => s - 1) (𝓝[≠] 1) (𝓝 0) := by
    have : Tendsto (fun s : ℂ => s - 1) (𝓝 1) (𝓝 (1 - 1)) :=
      (continuous_id.sub continuous_const).tendsto 1
    simpa using this.mono_left nhdsWithin_le_nhds
  have h2 := riemannZeta_residue_one.inv₀ one_ne_zero
  have h3 := h1.mul h2
  simp only [inv_one, mul_one] at h3
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ this, one_mul]

lemma continuousAt_invZeta_one : ContinuousAt invZeta 1 :=
  continuousAt_update_same.mpr tendsto_inv_riemannZeta_one

lemma continuousAt_invZeta {s : ℂ} (hz : riemannZeta s ≠ 0) : ContinuousAt invZeta s := by
  by_cases hs : s = 1
  · subst hs; exact continuousAt_invZeta_one
  · rw [invZeta, continuousAt_update_of_ne hs]
    exact ((differentiableAt_riemannZeta hs).continuousAt).inv₀ hz

lemma differentiableAt_invZeta {s : ℂ} (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    DifferentiableAt ℂ invZeta s := by
  have h : DifferentiableAt ℂ (fun s => (riemannZeta s)⁻¹) s :=
    (differentiableAt_riemannZeta hs).inv hz
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_compl_singleton.mem_nhds hs] with z hz'
  exact invZeta_of_ne hz'

/-! ## The half-plane `Re s > 1` -/

lemma inv_riemannZeta_eq_LSeries {s : ℂ} (hs : 1 < s.re) :
    (riemannZeta s)⁻¹ = L ↗μ s := by
  have h := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs] at h
  exact (eq_inv_of_mul_eq_one_right h).symm

lemma norm_inv_zeta_le_norm_zeta_re {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    ‖(riemannZeta (σ + t * I))⁻¹‖ ≤ ‖riemannZeta σ‖ := by
  have hre : (1 : ℝ) < ((σ : ℂ) + t * I).re := by simpa using hσ
  have hre' : (1 : ℝ) < (σ : ℂ).re := by simpa using hσ
  rw [inv_riemannZeta_eq_LSeries hre, LSeries]
  have hsum1 : Summable fun n => ‖LSeries.term (fun n => (μ n : ℂ)) ((σ : ℂ) + t * I) n‖ :=
    (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hre).norm
  have hsum2 : Summable fun n => ‖LSeries.term 1 (σ : ℂ) n‖ :=
    (LSeriesSummable_one_iff.mpr hre').norm
  have hle : ∀ n, ‖LSeries.term (fun n => (μ n : ℂ)) ((σ : ℂ) + t * I) n‖ ≤
      ‖LSeries.term 1 (σ : ℂ) n‖ := by
    intro n
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero]
    split_ifs
    · rfl
    · gcongr
      simp only [Pi.one_apply, norm_one]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  -- the real series
  set r : ℕ → ℝ := fun n => ‖LSeries.term 1 (σ : ℂ) n‖ with hr
  have hterm : ∀ n, LSeries.term 1 (σ : ℂ) n = (r n : ℂ) := by
    intro n
    simp only [hr]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn]
      simp only [Pi.one_apply]
      have h1 : ((n : ℂ) ^ (σ : ℂ)) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
        rw [← ofReal_natCast]; exact (ofReal_cpow (Nat.cast_nonneg _) _).symm
      rw [h1, ← ofReal_one, ← ofReal_div, norm_real, Real.norm_of_nonneg (by positivity)]
  have hζ : riemannZeta σ = ((∑' n, r n : ℝ) : ℂ) := by
    rw [← LSeries_one_eq_riemannZeta hre', LSeries, ofReal_tsum]
    exact tsum_congr hterm
  calc ‖∑' n, LSeries.term (fun n => (μ n : ℂ)) ((σ : ℂ) + t * I) n‖
      ≤ ∑' n, ‖LSeries.term (fun n => (μ n : ℂ)) ((σ : ℂ) + t * I) n‖ :=
        norm_tsum_le_tsum_norm hsum1
    _ ≤ ∑' n, r n := hsum1.tsum_le_tsum hle hsum2
    _ = ‖riemannZeta σ‖ := by
        rw [hζ, norm_real, Real.norm_of_nonneg (tsum_nonneg fun n => norm_nonneg _)]

lemma norm_inv_zeta_le_of_one_lt :
    ∃ c > 0, ∀ σ t : ℝ, 1 < σ → σ ≤ 2 → ‖(riemannZeta (σ + t * I))⁻¹‖ ≤ c / (σ - 1) := by
  obtain ⟨c, cpos, hc⟩ := ZetaNear1BndExact
  exact ⟨c, cpos, fun σ t h1 h2 =>
    (norm_inv_zeta_le_norm_zeta_re h1 t).trans (hc σ ⟨h1, h2⟩)⟩

/-! ## Grönwall: integrating `ζ'/ζ` horizontally -/

lemma inv_zeta_gronwall {t σ σ₀ K : ℝ} (ht : t ≠ 0) (hσ : σ ≤ σ₀)
    (hnz : ∀ u ∈ Icc σ σ₀, riemannZeta (u + t * I) ≠ 0)
    (hK : ∀ u ∈ Icc σ σ₀, ‖deriv riemannZeta (u + t * I) / riemannZeta (u + t * I)‖ ≤ K) :
    ‖(riemannZeta (σ + t * I))⁻¹‖ ≤
      ‖(riemannZeta (σ₀ + t * I))⁻¹‖ * Real.exp (K * (σ₀ - σ)) := by
  set z : ℝ → ℂ := fun u => ((σ₀ - u : ℝ) : ℂ) + t * I with hz
  set f : ℝ → ℂ := fun u => (riemannZeta (z u))⁻¹ with hf
  set f' : ℝ → ℂ := fun u => deriv riemannZeta (z u) / (riemannZeta (z u)) ^ 2 with hf'
  have hz1 : ∀ u, z u ≠ 1 := by
    intro u h
    have := congrArg Complex.im h
    simp [hz] at this
    exact ht this
  have hmem : ∀ u ∈ Icc 0 (σ₀ - σ), σ₀ - u ∈ Icc σ σ₀ := by
    intro u hu; constructor <;> linarith [hu.1, hu.2]
  have hderiv : ∀ u ∈ Icc 0 (σ₀ - σ), HasDerivAt f (f' u) u := by
    intro u hu
    have hzd : HasDerivAt z (-1) u := by
      have h1 : HasDerivAt (fun u : ℝ => σ₀ - u) (-1) u := by
        simpa using (hasDerivAt_id u).const_sub σ₀
      have h2 := h1.ofReal_comp
      simpa [hz] using h2.add_const (t * I)
    have hζd : HasDerivAt riemannZeta (deriv riemannZeta (z u)) (z u) :=
      (differentiableAt_riemannZeta (hz1 u)).hasDerivAt
    have hinv : HasDerivAt (fun w => (riemannZeta w)⁻¹)
        (-(deriv riemannZeta (z u)) / (riemannZeta (z u)) ^ 2) (z u) :=
      hζd.inv (hnz _ (hmem u hu))
    have h3 : HasDerivAt (fun u => (riemannZeta (z u))⁻¹)
        ((-(deriv riemannZeta (z u)) / (riemannZeta (z u)) ^ 2) * (-1)) u := hinv.comp u hzd
    convert h3 using 1
    simp only [hf']; ring
  have hcont : ContinuousOn f (Icc 0 (σ₀ - σ)) :=
    fun u hu => (hderiv u hu).continuousAt.continuousWithinAt
  have hbound : ∀ u ∈ Ico 0 (σ₀ - σ), ‖f' u‖ ≤ K * ‖f u‖ + 0 := by
    intro u hu
    have hu' : u ∈ Icc 0 (σ₀ - σ) := Ico_subset_Icc_self hu
    have hzu : riemannZeta (z u) ≠ 0 := hnz _ (hmem u hu')
    have : f' u = deriv riemannZeta (z u) / riemannZeta (z u) * f u := by
      simp only [hf', hf]
      field_simp
    rw [this, norm_mul, add_zero]
    gcongr
    exact hK _ (hmem u hu')
  have key := norm_le_gronwallBound_of_norm_deriv_right_le hcont
    (fun u hu => (hderiv u (Ico_subset_Icc_self hu)).hasDerivWithinAt) le_rfl hbound
    (σ₀ - σ) ⟨by linarith, le_rfl⟩
  rw [gronwallBound_ε0, sub_zero] at key
  have e1 : f (σ₀ - σ) = (riemannZeta (σ + t * I))⁻¹ := by
    simp [hf, hz]
  have e2 : f 0 = (riemannZeta (σ₀ + t * I))⁻¹ := by
    simp [hf, hz]
  rw [e1, e2] at key
  exact key

/-! ## The bound for `|t| > 3` -/

lemma inv_zeta_bound_large :
    ∃ dl > 0, dl ≤ 1 / 2 ∧ ∃ C > 0, ∀ σ t : ℝ, 3 < |t| → 1 - dl / Real.log |t| ≤ σ → σ ≤ 2 →
      riemannZeta (σ + t * I) ≠ 0 ∧
        ‖(riemannZeta (σ + t * I))⁻¹‖ ≤ C * |t| ^ (1 / 2 : ℝ) := by
  obtain ⟨A₀, hA₀, hzf⟩ := ZetaZeroFree1
  obtain ⟨CL, CLpos, hCL⟩ := LogDerivZetaUniformLogSquaredBound
  obtain ⟨cz, czpos, hcz⟩ := norm_inv_zeta_le_of_one_lt
  have hF := FinIoo
  set dl : ℝ := min (min A₀ F) (1 / (8 * CL)) with hdl
  have dlpos : 0 < dl := by
    have := hA₀.1; have := hF.1
    positivity
  have dlleA : dl ≤ A₀ := (min_le_left _ _).trans (min_le_left _ _)
  have dlleF : dl ≤ F := (min_le_left _ _).trans (min_le_right _ _)
  have dlleC : dl ≤ 1 / (8 * CL) := min_le_right _ _
  have dlle : dl ≤ 1 / 2 := dlleA.trans hA₀.2
  refine ⟨dl, dlpos, dlle, 4 * cz / dl, by positivity, ?_⟩
  intro σ t ht hσ hσ2
  set Lg := Real.log |t| with hLg
  have Lg1 : 1 < Lg := logt_gt_one ht.le
  have Lgpos : 0 < Lg := by linarith
  have tne : t ≠ 0 := by intro h; simp [h] at ht; linarith
  -- non-vanishing in the region `σ ≥ 1 - dl / log |t|`
  have hnz : ∀ u, 1 - dl / Lg ≤ u → riemannZeta (u + t * I) ≠ 0 := by
    intro u hu
    by_cases hu1 : u < 1
    · apply hzf u t ht
      refine ⟨?_, hu1⟩
      rw [Real.rpow_one]
      have : dl / Lg ≤ A₀ / Lg := div_le_div_of_nonneg_right dlleA Lgpos.le
      linarith
    · apply riemannZeta_ne_zero_of_one_le_re
      simpa using (not_lt.mp hu1)
  refine ⟨hnz σ hσ, ?_⟩
  set σ₀ : ℝ := 1 + dl / Lg with hσ₀
  have dlLg : dl / Lg ≤ dl := div_le_self dlpos.le Lg1.le
  have σ₀gt : 1 < σ₀ := by
    have : 0 < dl / Lg := by positivity
    linarith
  have σ₀le : σ₀ ≤ 2 := by linarith
  -- the bound at `σ₀`
  have hσ₀bd : ‖(riemannZeta (σ₀ + t * I))⁻¹‖ ≤ cz * Lg / dl := by
    have := hcz σ₀ t σ₀gt σ₀le
    rw [show σ₀ - 1 = dl / Lg by rw [hσ₀]; ring] at this
    rwa [div_div_eq_mul_div] at this
  -- main estimate: `‖ζ⁻¹‖ ≤ (cz/dl) log|t| · exp(log|t| / 4)`
  have hmain : ‖(riemannZeta (σ + t * I))⁻¹‖ ≤ cz * Lg / dl * Real.exp (Lg / 4) := by
    by_cases hcase : σ₀ ≤ σ
    · have h1 : 1 < σ := by linarith
      have := hcz σ t h1 hσ2
      calc ‖(riemannZeta (σ + t * I))⁻¹‖ ≤ cz / (σ - 1) := this
        _ ≤ cz / (dl / Lg) := by
            apply div_le_div_of_nonneg_left czpos.le (by positivity); linarith
        _ = cz * Lg / dl := by rw [div_div_eq_mul_div]
        _ ≤ cz * Lg / dl * Real.exp (Lg / 4) := by
            apply le_mul_of_one_le_right (by positivity)
            exact Real.one_le_exp (by positivity)
    · replace hcase := not_le.mp hcase
      have hg := inv_zeta_gronwall (K := CL * Lg ^ 2) tne hcase.le
        (fun u hu => hnz u (le_trans hσ hu.1))
        (fun u hu => by
          have := hCL u t ht (by
            simp only [mem_Ici]
            have : dl / Lg ≤ F / Lg := div_le_div_of_nonneg_right dlleF Lgpos.le
            linarith [hu.1])
          simpa [Real.rpow_two, ← hLg] using this)
      refine hg.trans ?_
      gcongr
      -- `CL · Lg² · (σ₀ - σ) ≤ CL · Lg² · 2dl/Lg ≤ Lg / 4`
      have hd : σ₀ - σ ≤ 2 * dl / Lg := by
        rw [hσ₀]; have : 1 - dl / Lg ≤ σ := hσ
        have : 2 * dl / Lg = dl / Lg + dl / Lg := by ring
        linarith
      calc CL * Lg ^ 2 * (σ₀ - σ) ≤ CL * Lg ^ 2 * (2 * dl / Lg) := by gcongr
        _ = 2 * (CL * dl) * Lg := by field_simp
        _ ≤ 2 * (1 / 8) * Lg := by
            gcongr
            calc CL * dl ≤ CL * (1 / (8 * CL)) := by gcongr
              _ = 1 / 8 := by field_simp
        _ = Lg / 4 := by ring
  -- `log|t| ≤ 4 |t|^{1/4}` and `exp(log|t|/4) = |t|^{1/4}`
  have htpos : 0 < |t| := by linarith
  have hlog : Lg ≤ 4 * |t| ^ (1 / 4 : ℝ) := by
    have := Real.log_le_rpow_div htpos.le (by norm_num : (0 : ℝ) < 1 / 4)
    rw [hLg]; linarith [show |t| ^ (1 / 4 : ℝ) / (1 / 4) = 4 * |t| ^ (1 / 4 : ℝ) by ring,
      this]
  have hexp : Real.exp (Lg / 4) = |t| ^ (1 / 4 : ℝ) := by
    rw [Real.rpow_def_of_pos htpos, hLg]; ring_nf
  calc ‖(riemannZeta (σ + t * I))⁻¹‖ ≤ cz * Lg / dl * Real.exp (Lg / 4) := hmain
    _ ≤ cz * (4 * |t| ^ (1 / 4 : ℝ)) / dl * |t| ^ (1 / 4 : ℝ) := by
        rw [hexp]; gcongr
    _ = 4 * cz / dl * (|t| ^ (1 / 4 : ℝ) * |t| ^ (1 / 4 : ℝ)) := by ring
    _ = 4 * cz / dl * |t| ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_add htpos]; norm_num

/-! ## The bound for `|t| ≤ 3` -/

lemma inv_zeta_bound_small :
    ∃ σ₂ < 1, ∃ B > 0, ∀ σ t : ℝ, |t| ≤ 3 → σ₂ ≤ σ → σ ≤ 2 →
      riemannZeta (σ + t * I) ≠ 0 ∧ ‖invZeta (σ + t * I)‖ ≤ B := by
  obtain ⟨σ₂, hσ₂, hbox⟩ := ZetaNoZerosInBox 3
  have hK : IsCompact (Icc σ₂ 2 ×ℂ Icc (-3) 3) := isCompact_Icc.reProdIm isCompact_Icc
  have hcont : ContinuousOn invZeta (Icc σ₂ 2 ×ℂ Icc (-3) 3) := by
    intro s hs
    apply ContinuousAt.continuousWithinAt
    apply continuousAt_invZeta
    have hs' := hs
    simp only [mem_reProdIm, mem_Icc] at hs'
    rw [← re_add_im s]
    exact hbox s.im (abs_le.mpr hs'.2) s.re hs'.1.1
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨σ₂, hσ₂, max B 1, by positivity, ?_⟩
  intro σ t ht hσ hσ2
  refine ⟨hbox t ht σ hσ, ?_⟩
  refine (hB _ ?_).trans (le_max_left _ _)
  simp only [mem_reProdIm, mem_Icc, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
    mul_one, sub_self, add_zero, add_im, mul_im, zero_add]
  exact ⟨⟨hσ, hσ2⟩, abs_le.mp ht⟩

/-! ## The combined bound -/

/-- **Bound for `1/ζ`.**  There are `dl > 0`, `σ₂ < 1` and `C` such that `ζ(σ+it) ≠ 0` and
`‖invZeta(σ+it)‖ ≤ C (1+|t|)^{1/2}` whenever `σ ≤ 2`, `σ ≥ σ₂` if `|t| ≤ 3`, and
`σ ≥ 1 - dl/log|t|` if `|t| > 3`. -/
theorem inv_zeta_bound :
    ∃ dl > 0, dl ≤ 1 / 2 ∧ ∃ σ₂ < 1, ∃ C > 0, ∀ σ t : ℝ, σ ≤ 2 → (|t| ≤ 3 → σ₂ ≤ σ) →
      (3 < |t| → 1 - dl / Real.log |t| ≤ σ) →
      riemannZeta (σ + t * I) ≠ 0 ∧ ‖invZeta (σ + t * I)‖ ≤ C * (1 + |t|) ^ (1 / 2 : ℝ) := by
  obtain ⟨dl, dlpos, dlle, C₁, C₁pos, h₁⟩ := inv_zeta_bound_large
  obtain ⟨σ₂, hσ₂, B, Bpos, h₂⟩ := inv_zeta_bound_small
  refine ⟨dl, dlpos, dlle, σ₂, hσ₂, max C₁ B, by positivity, ?_⟩
  intro σ t hσ2 hsmall hlarge
  have h1t : (1 : ℝ) ≤ (1 + |t|) ^ (1 / 2 : ℝ) :=
    Real.one_le_rpow (by linarith [abs_nonneg t]) (by norm_num)
  by_cases ht : |t| ≤ 3
  · obtain ⟨hnz, hb⟩ := h₂ σ t ht (hsmall ht) hσ2
    refine ⟨hnz, hb.trans ?_⟩
    calc B ≤ max C₁ B := le_max_right _ _
      _ = max C₁ B * 1 := (mul_one _).symm
      _ ≤ max C₁ B * (1 + |t|) ^ (1 / 2 : ℝ) := by gcongr
  · replace ht := not_le.mp ht
    obtain ⟨hnz, hb⟩ := h₁ σ t ht (hlarge ht) hσ2
    refine ⟨hnz, ?_⟩
    have hs1 : (σ : ℂ) + t * I ≠ 1 := by
      intro h
      have := congrArg Complex.im h
      simp at this
      rw [this] at ht; simp at ht; linarith
    rw [invZeta_of_ne hs1]
    refine hb.trans ?_
    gcongr
    · exact le_max_left _ _
    · linarith

end PNTMobiusAux
end MobiusDeterminant
