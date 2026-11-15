import Mathlib

/-!
# `ℓ²(e)` bookkeeping for the mean-value theorem

Minkowski's inequality in `ℓ²` over a finite set of moduli (paper, Theorem 6.1, Step 1 and
Step 5), its integral form against the Mellin density (Step 5), and the trivial bound by
the number of moduli.  All are deduced from the duality bound `l2_le_of_dual`.
-/

open Finset MeasureTheory

namespace MobiusDeterminant
namespace MeanValue

/-- Cauchy–Schwarz for finite complex sums. -/
lemma norm_sum_mul_le_sqrt {ι : Type*} (s : Finset ι) (c y : ι → ℂ) :
    ‖∑ e ∈ s, c e * y e‖ ≤
      Real.sqrt (∑ e ∈ s, ‖c e‖ ^ 2) * Real.sqrt (∑ e ∈ s, ‖y e‖ ^ 2) := by
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_mul]
  exact Real.sum_mul_le_sqrt_mul_sqrt s _ _

/-- Duality: if `‖∑ c_e z_e‖ ≤ ‖c‖₂ M` for all `c`, then `‖z‖₂ ≤ M`. -/
lemma l2_le_of_dual {ι : Type*} (s : Finset ι) (z : ι → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ c : ι → ℂ, ‖∑ e ∈ s, c e * z e‖ ≤ Real.sqrt (∑ e ∈ s, ‖c e‖ ^ 2) * M) :
    Real.sqrt (∑ e ∈ s, ‖z e‖ ^ 2) ≤ M := by
  set S := ∑ e ∈ s, ‖z e‖ ^ 2 with hS
  have hS0 : 0 ≤ S := sum_nonneg fun e _ => sq_nonneg _
  have key := h (fun e => starRingEnd ℂ (z e))
  have h1 : ∑ e ∈ s, starRingEnd ℂ (z e) * z e = ((S : ℝ) : ℂ) := by
    rw [hS]; push_cast
    exact sum_congr rfl fun e _ => Complex.conj_mul' _
  have h2 : ∑ e ∈ s, ‖starRingEnd ℂ (z e)‖ ^ 2 = S := by
    rw [hS]; exact sum_congr rfl fun e _ => by rw [Complex.norm_conj]
  rw [h1, h2, Complex.norm_real, Real.norm_of_nonneg hS0] at key
  rcases eq_or_lt_of_le (Real.sqrt_nonneg S) with h0 | hpos
  · rw [← h0]; exact hM
  · have : Real.sqrt S * Real.sqrt S ≤ Real.sqrt S * M := by
      rw [Real.mul_self_sqrt hS0]; exact key
    exact le_of_mul_le_mul_left this hpos

/-- **Minkowski** in `ℓ²(s)` for finite sums. -/
lemma l2_sum_le {ι β : Type*} (s : Finset ι) (B : Finset β) (x : β → ι → ℂ) :
    Real.sqrt (∑ e ∈ s, ‖∑ b ∈ B, x b e‖ ^ 2) ≤
      ∑ b ∈ B, Real.sqrt (∑ e ∈ s, ‖x b e‖ ^ 2) := by
  refine l2_le_of_dual s _ (sum_nonneg fun _ _ => Real.sqrt_nonneg _) fun c => ?_
  simp_rw [mul_sum]
  rw [sum_comm]
  refine (norm_sum_le _ _).trans (sum_le_sum fun b _ => norm_sum_mul_le_sqrt s c (x b))

/-- Scalar multiples in `ℓ²(s)`. -/
lemma l2_smul {ι : Type*} (s : Finset ι) (a : ℂ) (x : ι → ℂ) :
    Real.sqrt (∑ e ∈ s, ‖a * x e‖ ^ 2) = ‖a‖ * Real.sqrt (∑ e ∈ s, ‖x e‖ ^ 2) := by
  simp_rw [norm_mul, mul_pow]
  rw [← mul_sum, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-- The trivial `ℓ²` bound by the number of terms. -/
lemma l2_le_card {ι : Type*} (s : Finset ι) (x : ι → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ e ∈ s, ‖x e‖ ≤ M) :
    Real.sqrt (∑ e ∈ s, ‖x e‖ ^ 2) ≤ Real.sqrt s.card * M := by
  rw [← Real.sqrt_sq hM, ← Real.sqrt_mul (Nat.cast_nonneg _)]
  apply Real.sqrt_le_sqrt
  have : ∑ e ∈ s, ‖x e‖ ^ 2 ≤ s.card • M ^ 2 :=
    sum_le_card_nsmul _ _ _ fun e he => pow_le_pow_left₀ (norm_nonneg _) (h e he) 2
  rwa [nsmul_eq_mul] at this

/-- Monotonicity of the `ℓ²` norm under pointwise domination. -/
lemma l2_mono {ι : Type*} (s : Finset ι) (x y : ι → ℂ) (h : ∀ e ∈ s, ‖x e‖ ≤ ‖y e‖) :
    Real.sqrt (∑ e ∈ s, ‖x e‖ ^ 2) ≤ Real.sqrt (∑ e ∈ s, ‖y e‖ ^ 2) :=
  Real.sqrt_le_sqrt (sum_le_sum fun e he => pow_le_pow_left₀ (norm_nonneg _) (h e he) 2)

/-- **Minkowski for the Mellin integral** (paper, Theorem 6.1, Step 5): if
`‖F(τ, ·)‖_{ℓ²} ≤ (1 + |τ|) X` for every `τ`, then
`‖∫ g(τ) F(τ, ·) dτ‖_{ℓ²} ≤ X ∫ (1 + |τ|) |g(τ)| dτ`. -/
theorem l2_integral {ι : Type*} (s : Finset ι) (g : ℝ → ℂ) (hgm : AEStronglyMeasurable g volume)
    (hgi : Integrable (fun τ => (1 + |τ|) * ‖g τ‖)) (F : ℝ → ι → ℂ)
    (hFc : ∀ e, Continuous (fun τ => F τ e)) {X : ℝ} (hX : 0 ≤ X)
    (hF : ∀ τ, Real.sqrt (∑ e ∈ s, ‖F τ e‖ ^ 2) ≤ (1 + |τ|) * X) :
    Real.sqrt (∑ e ∈ s, ‖∫ τ, g τ * F τ e‖ ^ 2) ≤ X * ∫ τ, (1 + |τ|) * ‖g τ‖ := by
  have hI0 : 0 ≤ ∫ τ, (1 + |τ|) * ‖g τ‖ :=
    integral_nonneg fun τ => mul_nonneg (by positivity) (norm_nonneg _)
  have hpt : ∀ τ e, e ∈ s → ‖F τ e‖ ≤ (1 + |τ|) * X := by
    intro τ e he
    refine le_trans ?_ (hF τ)
    rw [Real.le_sqrt (norm_nonneg _) (sum_nonneg fun _ _ => sq_nonneg _)]
    exact single_le_sum (f := fun e => ‖F τ e‖ ^ 2) (fun _ _ => sq_nonneg _) he
  have hint : ∀ e ∈ s, Integrable (fun τ => g τ * F τ e) := by
    intro e he
    refine Integrable.mono' (hgi.const_mul X) (hgm.mul (hFc e).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun τ => ?_)
    rw [norm_mul]
    calc ‖g τ‖ * ‖F τ e‖ ≤ ‖g τ‖ * ((1 + |τ|) * X) :=
          mul_le_mul_of_nonneg_left (hpt τ e he) (norm_nonneg _)
      _ = X * ((1 + |τ|) * ‖g τ‖) := by ring
  refine l2_le_of_dual s _ (mul_nonneg hX hI0) fun c => ?_
  set C := Real.sqrt (∑ e ∈ s, ‖c e‖ ^ 2) with hC
  have hC0 : 0 ≤ C := Real.sqrt_nonneg _
  have hswap : ∑ e ∈ s, c e * ∫ τ, g τ * F τ e = ∫ τ, ∑ e ∈ s, c e * (g τ * F τ e) := by
    rw [integral_finsetSum]
    · exact sum_congr rfl fun e _ => (integral_const_mul _ _).symm
    · intro e he; exact (hint e he).const_mul _
  rw [hswap]
  have hbound : ∀ τ, ‖∑ e ∈ s, c e * (g τ * F τ e)‖ ≤ C * X * ((1 + |τ|) * ‖g τ‖) := by
    intro τ
    have : ∑ e ∈ s, c e * (g τ * F τ e) = g τ * ∑ e ∈ s, c e * F τ e := by
      rw [mul_sum]; exact sum_congr rfl fun e _ => by ring
    rw [this, norm_mul]
    calc ‖g τ‖ * ‖∑ e ∈ s, c e * F τ e‖
        ≤ ‖g τ‖ * (C * ((1 + |τ|) * X)) :=
          mul_le_mul_of_nonneg_left ((norm_sum_mul_le_sqrt s c _).trans
            (mul_le_mul_of_nonneg_left (hF τ) hC0)) (norm_nonneg _)
      _ = C * X * ((1 + |τ|) * ‖g τ‖) := by ring
  refine (norm_integral_le_of_norm_le (hgi.const_mul (C * X))
    (Filter.Eventually.of_forall hbound)).trans (le_of_eq ?_)
  rw [integral_const_mul]
  ring

end MeanValue
end MobiusDeterminant
