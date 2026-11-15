import MobiusDeterminant.Basic
import MobiusDeterminant.LambdaR.Expansion
import MobiusDeterminant.LambdaR.Abel

/-!
# Assembly: the `Λ_R` twin correlation from a level of distribution

From the expansion `∑ Λ_R(n) Λ_R(n+2) = N M(R) + E`, the double Abel bound
`|E| ≤ (log R)^2 · C N^{1-δ}` (from `MobiusPairLevel θ`), and `MainTermAsymp`,
we obtain `∑_{n ≤ N} Λ_R(n) Λ_R(n+2) = 𝔖 N + O(N exp(-c √(log R)))` for `R ≤ N^θ`.
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace MobiusDeterminant

/-- `x^2 ≤ 4 e^x` for `x ≥ 0`. -/
lemma sq_le_four_mul_exp {x : ℝ} (hx : 0 ≤ x) : x ^ 2 ≤ 4 * Real.exp x := by
  have h := Real.add_one_le_exp (x / 2)
  have hexp : Real.exp x = Real.exp (x / 2) ^ 2 := by
    rw [sq, ← Real.exp_add]
    ring_nf
  rw [hexp]
  have h0 : 0 ≤ x / 2 + 1 := by linarith
  nlinarith [mul_le_mul h h h0 (le_trans h0 h)]

/-- `u^2 e^{-α u} ≤ (16/α^2) e^{-(α/2) u}` for `α > 0`, `u ≥ 0`. -/
lemma sq_mul_exp_neg_le {α u : ℝ} (hα : 0 < α) (hu : 0 ≤ u) :
    u ^ 2 * Real.exp (-α * u) ≤ 16 / α ^ 2 * Real.exp (-(α / 2) * u) := by
  have h := sq_le_four_mul_exp (x := α * u / 2) (by positivity)
  have hu2 : u ^ 2 ≤ 16 / α ^ 2 * Real.exp (α * u / 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  have hsplit : Real.exp (-(α / 2) * u) = Real.exp (α * u / 2) * Real.exp (-α * u) := by
    rw [← Real.exp_add]
    ring_nf
  rw [hsplit, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hu2 (Real.exp_pos _).le

/-- `e^{-β u} ≤ e^c e^{-c √u}` for `0 ≤ c ≤ β`, `u ≥ 0`. -/
lemma exp_neg_le_exp_mul_exp_neg_sqrt {β c u : ℝ} (hc : 0 ≤ c) (hcβ : c ≤ β) (hu : 0 ≤ u) :
    Real.exp (-β * u) ≤ Real.exp c * Real.exp (-c * Real.sqrt u) := by
  rw [← Real.exp_add, Real.exp_le_exp]
  have hs : Real.sqrt u ≤ 1 + u := by
    rw [Real.sqrt_le_iff]
    constructor <;> nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hs hc, mul_le_mul_of_nonneg_right hcβ hu]

/-- `N^{1-δ} ≤ N e^{-(δ/θ) log R}` when `0 < R ≤ N^θ`. -/
lemma rpow_one_sub_le {N R θ δ : ℝ} (hN : 0 < N) (hR : 0 < R) (hθ : 0 < θ) (hδ : 0 < δ)
    (hRN : R ≤ N ^ θ) :
    N ^ (1 - δ) ≤ N * Real.exp (-(δ / θ) * Real.log R) := by
  have hlog : Real.log R ≤ θ * Real.log N := by
    rw [← Real.log_rpow hN]
    exact Real.log_le_log hR hRN
  have h1 : δ / θ * Real.log R ≤ δ * Real.log N := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hθ]
    nlinarith
  conv_rhs => rw [← Real.exp_log hN, ← Real.exp_add]
  rw [Real.rpow_def_of_pos hN, Real.exp_le_exp]
  nlinarith

/-- The remainder sum is bounded via `MobiusPairLevel` and double Abel summation. -/
lemma abs_remSum_le {θ δ C₂ : ℝ}
    (hL : ∀ N : ℕ, 2 ≤ N → ∀ K L : ℕ,
      (K : ℝ) ≤ (N : ℝ) ^ θ → (L : ℝ) ≤ (N : ℝ) ^ θ →
        |∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 L, (μ d : ℝ) * (μ e : ℝ) * rem N d e|
          ≤ C₂ * (N : ℝ) ^ (1 - δ))
    {N : ℕ} {R : ℝ} (hN : 2 ≤ N) (hR : 1 ≤ R) (hRN : R ≤ (N : ℝ) ^ θ) :
    |∑ d ∈ Finset.Icc 1 ⌊R⌋₊, ∑ e ∈ Finset.Icc 1 ⌊R⌋₊,
        (μ d : ℝ) * (μ e : ℝ) * Real.log (R / d) * Real.log (R / e) * rem N d e|
      ≤ Real.log R ^ 2 * (C₂ * (N : ℝ) ^ (1 - δ)) := by
  have hK : ∀ k ∈ Finset.Icc 1 ⌊R⌋₊, (k : ℝ) ≤ (N : ℝ) ^ θ := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have : (k : ℝ) ≤ R := (Nat.le_floor_iff' (by omega)).mp hk.2
    linarith
  have h := abs_sum_mul_log_log_le R hR (fun d e => (μ d : ℝ) * (μ e : ℝ) * rem N d e)
    (C₂ * (N : ℝ) ^ (1 - δ)) (fun k hk l hl => hL N hN k l (hK k hk) (hK l hl))
  have heq : ∑ d ∈ Finset.Icc 1 ⌊R⌋₊, ∑ e ∈ Finset.Icc 1 ⌊R⌋₊,
        (μ d : ℝ) * (μ e : ℝ) * Real.log (R / d) * Real.log (R / e) * rem N d e =
      ∑ d ∈ Finset.Icc 1 ⌊R⌋₊, ∑ e ∈ Finset.Icc 1 ⌊R⌋₊,
        (μ d : ℝ) * (μ e : ℝ) * rem N d e * Real.log (R / d) * Real.log (R / e) := by
    refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => ?_
    ring
  rw [heq]
  exact h

theorem lambdaR_twin_of_level_of_mainTerm (θ : ℝ) (hθ : 0 < θ)
    (hL : MobiusPairLevel θ) (hM : MainTermAsymp) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ N : ℕ, ∀ R : ℝ, 2 ≤ N → 2 ≤ R → R ≤ (N : ℝ) ^ θ →
      |∑ n ∈ Finset.Icc 1 N, LambdaR R n * LambdaR R (n + 2) - twinConstant * N|
        ≤ C * N * Real.exp (-c * Real.sqrt (Real.log R)) := by
  obtain ⟨c₁, hc₁, C₁, hC₁, hM'⟩ := hM
  obtain ⟨δ, hδ, C₂, hC₂, hL'⟩ := hL
  set α := δ / θ with hα_def
  have hα : 0 < α := div_pos hδ hθ
  set c := min c₁ (α / 2) with hc_def
  have hc : 0 < c := lt_min hc₁ (by positivity)
  set C := C₁ + C₂ * (16 / α ^ 2) * Real.exp c with hC_def
  refine ⟨c, hc, C, by positivity, ?_⟩
  intro N R hN hR hRN
  have hR1 : (1 : ℝ) ≤ R := by linarith
  have hR0 : (0 : ℝ) < R := by linarith
  have hN0 : (0 : ℝ) < N := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  set u := Real.log R with hu_def
  have hu : 0 ≤ u := Real.log_nonneg hR1
  set s := Real.sqrt u with hs_def
  have hs : 0 ≤ s := Real.sqrt_nonneg u
  rw [sum_LambdaR_mul_eq]
  set E := ∑ d ∈ Finset.Icc 1 ⌊R⌋₊, ∑ e ∈ Finset.Icc 1 ⌊R⌋₊,
        (μ d : ℝ) * (μ e : ℝ) * Real.log (R / d) * Real.log (R / e) * rem N d e with hE_def
  have hE : |E| ≤ u ^ 2 * (C₂ * (N : ℝ) ^ (1 - δ)) := abs_remSum_le hL' hN hR1 hRN
  have hE' : u ^ 2 * (C₂ * (N : ℝ) ^ (1 - δ)) ≤
      C₂ * (16 / α ^ 2) * Real.exp c * N * Real.exp (-c * s) := by
    have h1 : (N : ℝ) ^ (1 - δ) ≤ N * Real.exp (-α * u) :=
      rpow_one_sub_le hN0 hR0 hθ hδ hRN
    have h2 := sq_mul_exp_neg_le hα hu
    have h3 : Real.exp (-(α / 2) * u) ≤ Real.exp c * Real.exp (-c * s) :=
      exp_neg_le_exp_mul_exp_neg_sqrt hc.le (min_le_right _ _) hu
    calc u ^ 2 * (C₂ * (N : ℝ) ^ (1 - δ))
        ≤ u ^ 2 * (C₂ * (N * Real.exp (-α * u))) := by gcongr
      _ = C₂ * N * (u ^ 2 * Real.exp (-α * u)) := by ring
      _ ≤ C₂ * N * (16 / α ^ 2 * Real.exp (-(α / 2) * u)) := by gcongr
      _ ≤ C₂ * N * (16 / α ^ 2 * (Real.exp c * Real.exp (-c * s))) := by gcongr
      _ = C₂ * (16 / α ^ 2) * Real.exp c * N * Real.exp (-c * s) := by ring
  have hMain : |(N : ℝ) * (mainSum R - twinConstant)| ≤ C₁ * N * Real.exp (-c * s) := by
    rw [abs_mul, abs_of_pos hN0]
    have h1 := hM' R hR
    have h2 : Real.exp (-c₁ * s) ≤ Real.exp (-c * s) := by
      rw [Real.exp_le_exp]
      nlinarith [min_le_left c₁ (α / 2)]
    calc (N : ℝ) * |mainSum R - twinConstant| ≤ N * (C₁ * Real.exp (-c₁ * s)) := by gcongr
      _ ≤ N * (C₁ * Real.exp (-c * s)) := by gcongr
      _ = C₁ * N * Real.exp (-c * s) := by ring
  calc |(N : ℝ) * mainSum R + E - twinConstant * N|
      = |(N : ℝ) * (mainSum R - twinConstant) + E| := by ring_nf
    _ ≤ |(N : ℝ) * (mainSum R - twinConstant)| + |E| := abs_add_le _ _
    _ ≤ C₁ * N * Real.exp (-c * s) + C₂ * (16 / α ^ 2) * Real.exp c * N * Real.exp (-c * s) :=
        add_le_add hMain (hE.trans hE')
    _ = C * N * Real.exp (-c * s) := by rw [hC_def]; ring

#print axioms lambdaR_twin_of_level_of_mainTerm

end MobiusDeterminant
