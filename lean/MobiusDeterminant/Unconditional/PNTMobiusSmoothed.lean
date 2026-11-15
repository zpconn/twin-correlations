import MobiusDeterminant.Unconditional.PNTMobiusInvZeta
import PrimeNumberTheoremAnd.MediumPNT

/-!
# The smoothed Mertens sum as a Mellin–Perron integral

For a smoothing `ν` (as in PNT+'s `SmoothedChebyshevDirichlet`), `0 < ε < 1`, `X > 0` and
`1 < σ ≤ 2`:

  `∑ₙ μ(n) ν_ε(n/X) = (1/2π) ∫ (1/ζ)(σ+it) 𝓜(ν_ε)(σ+it) X^{σ+it} dt`

(`smoothedMobius_eq_integral`), where `ν_ε = Smooth1 ν ε` is PNT+'s smoothed indicator of
`(0,1]`.  The proof is PNT+'s proof of `SmoothedChebyshevDirichlet` with `Λ` replaced by `μ`
and `-ζ'/ζ` by `1/ζ`.
-/

open Complex Real Set Filter Topology MeasureTheory
open scoped ArithmeticFunction.Moebius LSeries.notation

namespace MobiusDeterminant
namespace PNTMobiusAux

local notation "𝓜" => mellin

/-- The Perron integrand `(1/ζ)(s) 𝓜(ν_ε)(s) X^s`. -/
noncomputable def mobIntegrand (ν : ℝ → ℝ) (ε X : ℝ) (s : ℂ) : ℂ :=
  invZeta s * 𝓜 (fun x => (Smooth1 ν ε x : ℂ)) s * (X : ℂ) ^ s

lemma invZeta_eq_tsum {s : ℂ} (hs : 1 < s.re) :
    invZeta s = ∑' n : ℕ, (μ n : ℂ) / (n : ℂ) ^ s := by
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; simp at hs
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
  rw [invZeta_of_ne hs1, inv_riemannZeta_eq_LSeries hs, LSeries]
  exact tsum_congr fun n => LSeries.term_of_ne_zero' hs0 _ n

set_option backward.isDefEq.respectTransparency false in
lemma smoothedMobius_aux_tsum_integral {ν : ℝ → ℝ}
    (diffν : ContDiff ℝ 1 ν) (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : Function.support ν ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ (x : ℝ) in Ioi 0, ν x / x = 1) {X : ℝ}
    (X_pos : 0 < X) {ε : ℝ} (εpos : 0 < ε)
    (ε_lt_one : ε < 1) {σ : ℝ} (σ_gt : 1 < σ) (σ_le : σ ≤ 2) :
    ∫ (t : ℝ),
      ∑' (n : ℕ), (μ n : ℂ) / (n : ℂ) ^ (σ + t * I) *
        𝓜 (fun x ↦ ↑(Smooth1 ν ε x)) (σ + t * I) * (X : ℂ) ^ (σ + t * I) =
    ∑' (n : ℕ),
      ∫ (t : ℝ), (μ n : ℂ) / (n : ℂ) ^ (σ + ↑t * I) *
        𝓜 (fun x ↦ ↑(Smooth1 ν ε x)) (σ + ↑t * I) * (X : ℂ) ^ (σ + t * I) := by
  have cont_mellin_smooth : Continuous fun (a : ℝ) ↦
      𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + ↑a * I) := by
    rw [← continuousOn_univ]
    refine ContinuousOn.comp' ?_ ?_ ?_ (t := {z : ℂ | 0 < z.re })
    · refine continuousOn_of_forall_continuousAt ?_
      intro z hz
      exact (Smooth1MellinDifferentiable diffν suppν ⟨εpos, ε_lt_one⟩
        νpos mass_one hz).continuousAt
    · fun_prop
    · simp only [mapsTo_univ_iff, mem_ofPred_eq, add_re, ofReal_re, mul_re, I_re, mul_zero,
        ofReal_im, I_im, mul_one, sub_self, add_zero, forall_const]; linarith
  have abs_two : ∀ a : ℝ, ∀ i : ℕ, ‖(i : ℂ) ^ ((σ : ℂ) + ↑a * I)‖₊ = i ^ σ := by
    intro a i
    simp_rw [← norm_toNNReal]
    rw [norm_natCast_cpow_of_re_ne_zero _ (by simp only [add_re, ofReal_re, mul_re, I_re, mul_zero,
      ofReal_im, I_im, mul_one, sub_self, add_zero, ne_eq]; linarith)]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, Real.toNNReal_of_nonneg <| rpow_nonneg (y := σ) (x := i) (by linarith)]
    norm_cast
  rw [MeasureTheory.integral_tsum]
  · have x_neq_zero : X ≠ 0 := by linarith
    intro i
    by_cases i_eq_zero : i = 0
    · simpa [i_eq_zero] using aestronglyMeasurable_const
    · apply Continuous.aestronglyMeasurable
      fun_prop (disch := simp[i_eq_zero, x_neq_zero])
  · rw [← lt_top_iff_ne_top]
    simp_rw [enorm_mul, enorm_eq_nnnorm, nnnorm_div, ← norm_toNNReal,
      Complex.norm_cpow_eq_rpow_re_of_pos X_pos, norm_toNNReal, abs_two]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero]
    simp_rw [MeasureTheory.lintegral_mul_const' (r := ↑(X ^ σ).toNNReal) (hr := by simp),
      ENNReal.tsum_mul_right]
    apply WithTop.mul_lt_top ?_ ENNReal.coe_lt_top
    conv =>
      arg 1
      arg 1
      intro i
      rw [MeasureTheory.lintegral_const_mul' (hr := by simp)]
    rw [ENNReal.tsum_mul_right]
    apply WithTop.mul_lt_top
    · rw [WithTop.lt_top_iff_ne_top, ENNReal.tsum_coe_ne_top_iff_summable_coe]
      push_cast
      convert ((ArithmeticFunction.LSeriesSummable_moebius_iff (s := σ)).mpr
        (by simp only [ofReal_re]; linarith)).norm
      rw [LSeries.term_def]
      split_ifs with h <;> simp [h]
    · simp_rw [← enorm_eq_nnnorm]
      rw [← MeasureTheory.hasFiniteIntegral_iff_enorm]
      exact SmoothedChebyshevDirichlet_aux_integrable diffν νpos suppν
            mass_one εpos ε_lt_one σ_gt σ_le |>.hasFiniteIntegral

set_option backward.isDefEq.respectTransparency false in
/-- **Mellin–Perron formula for the smoothed Mertens sum.** -/
theorem smoothedMobius_eq_integral {ν : ℝ → ℝ}
    (diffν : ContDiff ℝ 1 ν) (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : Function.support ν ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    {X : ℝ} (X_pos : 0 < X) {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1)
    {σ : ℝ} (σ_gt : 1 < σ) (σ_le : σ ≤ 2) :
    1 / (2 * π) * ∫ t : ℝ, mobIntegrand ν ε X (σ + t * I) =
      ∑' n, (μ n : ℂ) * Smooth1 ν ε (n / X) := by
  dsimp [mobIntegrand]
  calc
    _ = 1 / (2 * π) * (∫ (t : ℝ), ∑' n, (μ n : ℂ) / (n : ℂ) ^ (σ + ↑t * I) *
      mellin (fun x ↦ ↑(Smooth1 ν ε x)) (σ + ↑t * I) * X ^ (σ + ↑t * I)) := ?_
    _ = 1 / (2 * π) * (∑' n, ∫ (t : ℝ), (μ n : ℂ) / (n : ℂ) ^ (σ + ↑t * I) *
      mellin (fun x ↦ ↑(Smooth1 ν ε x)) (σ + ↑t * I) * X ^ (σ + ↑t * I)) := ?_
    _ = 1 / (2 * π) * (∑' n, (μ n : ℂ) * ∫ (t : ℝ),
      mellin (fun x ↦ ↑(Smooth1 ν ε x)) (σ + ↑t * I) *
        (X / (n : ℂ)) ^ (σ + ↑t * I)) := ?_
    _ = ∑' n, (μ n : ℂ) * (1 / (2 * π) * ∫ (t : ℝ),
      mellin (fun x ↦ ↑(Smooth1 ν ε x)) (σ + ↑t * I) *
        (X / (n : ℂ)) ^ (σ + ↑t * I)) := ?_
    _ = ∑' n, (μ n : ℂ) * (1 / (2 * π) * ∫ (t : ℝ),
      mellin (fun x ↦ ↑(Smooth1 ν ε x)) (σ + ↑t * I) *
        ((n : ℂ) / X) ^ (-(σ + ↑t * I))) := ?_
    _ = _ := ?_
  · congr; ext t
    rw [invZeta_eq_tsum]
    · rw [← tsum_mul_right, ← tsum_mul_right]
    · simp [σ_gt]
  · congr 1
    exact smoothedMobius_aux_tsum_integral diffν νpos
      suppν mass_one X_pos εpos ε_lt_one σ_gt σ_le
  · congr 1; congr 1; ext n; rw [← MeasureTheory.integral_const_mul]; congr 1; ext t
    by_cases n_ne_zero : n = 0
    · simp [n_ne_zero]
    have hn0 : (n : ℂ) ^ ((σ : ℂ) + t * I) ≠ 0 := by
      simp only [ne_eq, cpow_eq_zero_iff, Nat.cast_eq_zero, n_ne_zero, false_and,
        not_false_eq_true]
    have hXn : ((X : ℂ) / (n : ℂ)) ^ ((σ : ℂ) + t * I) * (n : ℂ) ^ ((σ : ℂ) + t * I) =
        (X : ℂ) ^ ((σ : ℂ) + t * I) := by
      have := mul_cpow_ofReal_nonneg (a := X / (n : ℝ)) (b := (n : ℝ)) (r := σ + t * I)
        (div_nonneg X_pos.le (Nat.cast_nonneg n)) (Nat.cast_nonneg n)
      push_cast at this
      rw [← this, div_mul_cancel₀ _ (by exact_mod_cast n_ne_zero)]
    rw [← hXn]
    field_simp
  · simp_rw [← tsum_mul_left, ← mul_assoc, mul_comm]
  · have ht (t : ℝ) : -(σ + t * I) = (-1) * (σ + t * I) := by simp
    have hn (n : ℂ) : (n / X) ^ (-1 : ℂ) = X / n := by simp [cpow_neg_one]
    have (n : ℕ) : (log ((n : ℂ) / (X : ℂ)) * -1).im = 0 := by
      simp [Complex.log_im, arg_eq_zero_iff, div_nonneg (Nat.cast_nonneg _) (by linarith : 0 ≤ X)]
    have h (n : ℕ) (t : ℝ) : ((n : ℂ) / X) ^ ((-1 : ℂ) * (σ + t * I)) =
        ((n / X) ^ (-1 : ℂ)) ^ (σ + ↑t * I) := by
      rw [cpow_mul] <;> {rw [this n]; simp [Real.pi_pos, Real.pi_nonneg]}
    conv => rhs; lhs; intro n; rhs; rhs; rhs; intro t; rhs; rw [ht t, h n t]; lhs; rw [hn]
  · congr
    ext n
    by_cases n_zero : n = 0
    · simp [n_zero]
    have n_pos : 0 < n := by
      simpa only [n_zero, gt_iff_lt, false_or] using (Nat.eq_zero_or_pos n)
    congr
    have := mellinInv_mellin_eq σ (f := fun x ↦ (Smooth1 ν ε x : ℂ)) (x := n / X)
      ?_ ?_ ?_ ?_
    · beta_reduce at this
      dsimp [mellinInv, VerticalIntegral] at this
      convert! this using 4
      · norm_cast
      · rw [mul_comm]
        norm_cast
    · exact div_pos (by exact_mod_cast n_pos) X_pos
    · apply Smooth1MellinConvergent diffν suppν ⟨εpos, ε_lt_one⟩
        νpos mass_one
      simp only [ofReal_re]
      linarith
    · dsimp [VerticalIntegrable]
      apply SmoothedChebyshevDirichlet_aux_integrable diffν νpos
        suppν mass_one εpos ε_lt_one σ_gt σ_le
    · refine ContinuousAt.comp (g := ofReal) RCLike.continuous_ofReal.continuousAt ?_
      exact Smooth1ContinuousAt diffν νpos suppν
        εpos (by positivity)

end PNTMobiusAux
end MobiusDeterminant
