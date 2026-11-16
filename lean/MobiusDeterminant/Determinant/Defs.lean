import MobiusDeterminant.Unconditional.Interfaces

/-!
# The determinant sum (paper Theorem 1.3): definitions and interfaces

Paper §1.3.  Let `W : ℝ⁴ → ℂ` be smooth and supported in `[1,2]⁴`, let `X ≥ 3`,
`A, B ≥ 1`, `D = X/A`, `E = X/B` and `κ ∈ {2, -2}`.  Then

  `S_κ = ∑_{a,b,d,e odd, be - ad = κ} μ(d) μ(e) W(a/A, b/B, d/D, e/E)`        (paper (1.3))

and the zero frequency after Poisson summation in `a` modulo `2e` is

  `S_κ⁰ = ∑_{e odd} μ(e) A/(2e) ∑_{(d,2e)=1} μ(d) Φ(0; d/D, e/E)`,             (paper (7.3))
  `Φ(0; δ, ε) = ∫ W(α, αδ/ε + κ/(εX), δ, ε) dα`.

With `A = X^x`, `B = X^y`, `m = min(x,y)`, `M = max(x,y)`, the region is
`Ω = {(x,y) ∈ (0,1/2]² : 8m + 9M > 8}` and the saving is `σ = (8m + 9M - 8)/12`.

The formal proof is split into components whose statements are fixed here:

* `MellinSep4`     — four-variable Mellin separation of a fixed smooth weight;
* `DetTensorBound` — the error term of a smooth odd divisor-pair sum with product
  weights, in the asymmetric range of Theorem 1.3 (from the mean-value theorem);
* `OddMainBound`   — the main term of that sum is `≪ N₀ exp(-c √log D)` (from PNT for `μ`);
* `DetErrorBound`, `ZeroModeBound` — Theorem 1.3 in terms of `X, A, B`.

Since `W` vanishes outside `[1,2]⁴`, the sums over `a ≤ 2A`, `b ≤ 2B`, `d ≤ 2D`, `e ≤ 2E`
below lose no terms.
-/

open Finset Real
open scoped ArithmeticFunction.Moebius ContDiff

namespace MobiusDeterminant

namespace Determinant

/-! ## The statement -/

/-- `W` is smooth and supported in `[1,2]⁴`. -/
def SmoothWeight (W : ℝ × ℝ × ℝ × ℝ → ℂ) : Prop :=
  ContDiff ℝ ∞ W ∧
    ∀ x : ℝ × ℝ × ℝ × ℝ, W x ≠ 0 →
      x.1 ∈ Set.Icc (1 : ℝ) 2 ∧ x.2.1 ∈ Set.Icc (1 : ℝ) 2 ∧
        x.2.2.1 ∈ Set.Icc (1 : ℝ) 2 ∧ x.2.2.2 ∈ Set.Icc (1 : ℝ) 2

/-- The determinant sum `S_κ(W; A, B, D, E)` of paper (1.3), with `D = X/A`, `E = X/B`. -/
noncomputable def detSum (κ : ℤ) (W : ℝ × ℝ × ℝ × ℝ → ℂ) (A B X : ℝ) : ℂ :=
  ∑ a ∈ Icc 1 ⌊2 * A⌋₊, ∑ b ∈ Icc 1 ⌊2 * B⌋₊,
    ∑ d ∈ Icc 1 ⌊2 * (X / A)⌋₊, ∑ e ∈ Icc 1 ⌊2 * (X / B)⌋₊,
      if Odd a ∧ Odd b ∧ Odd d ∧ Odd e ∧ (b : ℤ) * e - (a : ℤ) * d = κ then
        (μ d : ℂ) * (μ e : ℂ) * W ((a : ℝ) / A, (b : ℝ) / B, (d : ℝ) / (X / A), (e : ℝ) / (X / B))
      else 0

/-- `Φ(0; δ, ε) = ∫ F(α; δ, ε) dα` with `F(α; δ, ε) = W(α, αδ/ε + κ/(εX), δ, ε)`. -/
noncomputable def Phi0 (κ : ℤ) (W : ℝ × ℝ × ℝ × ℝ → ℂ) (X δ ε : ℝ) : ℂ :=
  ∫ α : ℝ, W (α, α * δ / ε + (κ : ℝ) / (ε * X), δ, ε)

/-- The zero frequency `S_κ⁰` of paper (7.3). -/
noncomputable def zeroMode (κ : ℤ) (W : ℝ × ℝ × ℝ × ℝ → ℂ) (A B X : ℝ) : ℂ :=
  ∑ e ∈ (Icc 1 ⌊2 * (X / B)⌋₊).filter Odd,
    ∑ d ∈ (Icc 1 ⌊2 * (X / A)⌋₊).filter (fun d => Nat.Coprime d (2 * e)),
      (μ e : ℂ) * (μ d : ℂ) * ((A / (2 * e) : ℝ) : ℂ) *
        Phi0 κ W X ((d : ℝ) / (X / A)) ((e : ℝ) / (X / B))

/-- The region `Ω = {(x,y) ∈ (0,1/2]² : 8 min(x,y) + 9 max(x,y) > 8}`. -/
def Omega : Set (ℝ × ℝ) :=
  {p | 0 < p.1 ∧ p.1 ≤ 1 / 2 ∧ 0 < p.2 ∧ p.2 ≤ 1 / 2 ∧ 8 < 8 * min p.1 p.2 + 9 * max p.1 p.2}

/-- The saving `σ(x,y) = (8 min(x,y) + 9 max(x,y) - 8)/12`. -/
noncomputable def sigmaExp (p : ℝ × ℝ) : ℝ :=
  (8 * min p.1 p.2 + 9 * max p.1 p.2 - 8) / 12

/-! ## Interfaces -/

/-- **Four-variable Mellin separation** of a fixed smooth weight supported in `[1,2]⁴`:
`W(α,β,δ,ε) = ∫ g(τ) α^{-iτ₀} β^{-iτ₁} δ^{-iτ₂} ε^{-iτ₃} dτ` for positive arguments, with
`g` integrable against every polynomial weight. -/
def MellinSep4 : Prop :=
  ∀ W : ℝ × ℝ × ℝ × ℝ → ℂ, SmoothWeight W →
    ∃ g : EuclideanSpace ℝ (Fin 4) → ℂ,
      (∀ m : ℕ, MeasureTheory.Integrable (fun τ => (1 + ‖τ‖) ^ m * ‖g τ‖)) ∧
      ∀ α β δ ε : ℝ, 0 < α → 0 < β → 0 < δ → 0 < ε →
        W (α, β, δ, ε) = ∫ τ, g τ * Complex.exp
          (-((τ 0 * Real.log α + τ 1 * Real.log β + τ 2 * Real.log δ + τ 3 * Real.log ε : ℝ) : ℂ)
            * Complex.I)

/-- Odd-`n` bracket: `∑_{n ≤ 2N₀ odd, d ∣ n, e ∣ n+2} ψ(n/N₀) - N₀ ψ̂(0) ϱ(d,e)/2`.
For odd `d, e`, `ϱ(d,e)/2` is the density of the odd `n` with `d ∣ n`, `e ∣ n + 2`. -/
noncomputable def oddBracket (N₀ : ℝ) (ψ : ℝ → ℂ) (d e : ℕ) : ℂ :=
  (∑ n ∈ (Icc 1 ⌊2 * N₀⌋₊).filter (fun n => Odd n ∧ d ∣ n ∧ e ∣ n + 2), ψ ((n : ℝ) / N₀))
    - (N₀ : ℂ) * fourierR ψ 0 * ((dens d e / 2 : ℝ) : ℂ)

/-- The error term of the smooth odd divisor-pair sum with product weights. -/
noncomputable def oddDelta (N₀ D E : ℝ) (ψ φ₁ φ₂ : ℝ → ℂ) : ℂ :=
  ∑ d ∈ (Icc 1 ⌊2 * D⌋₊).filter Odd, ∑ e ∈ (Icc 1 ⌊2 * E⌋₊).filter Odd,
    (μ d : ℂ) * (μ e : ℂ) * φ₁ ((d : ℝ) / D) * φ₂ ((e : ℝ) / E) * oddBracket N₀ ψ d e

/-- The main term of the same sum. -/
noncomputable def oddMain (N₀ D E : ℝ) (ψ φ₁ φ₂ : ℝ → ℂ) : ℂ :=
  ∑ d ∈ (Icc 1 ⌊2 * D⌋₊).filter Odd, ∑ e ∈ (Icc 1 ⌊2 * E⌋₊).filter Odd,
    (μ d : ℂ) * (μ e : ℂ) * φ₁ ((d : ℝ) / D) * φ₂ ((e : ℝ) / E) *
      ((N₀ : ℂ) * fourierR ψ 0 * ((dens d e / 2 : ℝ) : ℂ))

/-- **Error term for product weights** (paper §7 in the correlation form).  With
`D_max = max(D,E)`, `D_min = min(D,E)`, `T = DE/N₀`, under the hypotheses of the mean-value
theorem with room `N₀^ε`,
`Δ ≪ P^k (N₀^{1+ε} (D_max^{-1/12} T^{3/4} + D_max^{-2/3} D_min^{1/2} T + D_min^{-1/2} T) + N₀^{1/2})`. -/
def DetTensorBound : Prop :=
  ∀ ε > (0 : ℝ), ∃ k : ℕ, ∃ C > (0 : ℝ),
    ∀ (N₀ D E P : ℝ) (ψ φ₁ φ₂ : ℝ → ℂ), 2 ≤ N₀ → 1 ≤ D → 1 ≤ E → D ≤ N₀ → E ≤ N₀ →
      N₀ ^ ε * (D * E / N₀) ≤ (max D E) ^ ((1 : ℝ) / 6) →
      (max D E) ^ ((2 : ℝ) / 3) * (N₀ ^ ε * (D * E / N₀)) ^ 2 ≤ min D E →
      1 ≤ P → TemperedOn ψ P k (1/2) 2 → TemperedOn φ₁ P k (1/2) 2 →
      TemperedOn φ₂ P k (1/2) 2 →
      ‖oddDelta N₀ D E ψ φ₁ φ₂‖ ≤ C * P ^ k *
        (N₀ ^ (1 + ε) *
            ((max D E) ^ (-(1 : ℝ) / 12) * (D * E / N₀) ^ ((3 : ℝ) / 4)
              + (max D E) ^ (-(2 : ℝ) / 3) * (min D E) ^ ((1 : ℝ) / 2) * (D * E / N₀)
              + (min D E) ^ (-(1 : ℝ) / 2) * (D * E / N₀))
          + N₀ ^ ((1 : ℝ) / 2))

/-- **Main term for product weights**: `≪ P^k N₀ exp(-c √log D)` (cancellation in `d`). -/
def OddMainBound : Prop :=
  ∃ c > (0 : ℝ), ∃ k : ℕ, ∃ C > (0 : ℝ),
    ∀ (N₀ D E P : ℝ) (ψ φ₁ φ₂ : ℝ → ℂ), 0 < N₀ → 2 ≤ D → 1 ≤ E → E ≤ D ^ 2 → 1 ≤ P →
      TemperedOn ψ P k (1/2) 2 → TemperedOn φ₁ P k (1/2) 2 → TemperedOn φ₂ P k (1/2) 2 →
      ‖oddMain N₀ D E ψ φ₁ φ₂‖ ≤ C * P ^ k * N₀ * Real.exp (-c * Real.sqrt (Real.log D))

/-- **Theorem 1.3, power-saving part, in terms of `X, A, B`**: with `D = X/A`, `E = X/B`,
`T = X/(AB)`, under the hypotheses of the mean-value theorem with room `X^ε`. -/
def DetErrorBound : Prop :=
  ∀ κ : ℤ, (κ = 2 ∨ κ = -2) → ∀ W : ℝ × ℝ × ℝ × ℝ → ℂ, SmoothWeight W →
    ∀ ε > (0 : ℝ), ∃ C > (0 : ℝ),
      ∀ X A B : ℝ, 3 ≤ X → 1 ≤ A → A ≤ Real.sqrt X → 1 ≤ B → B ≤ Real.sqrt X →
        X ^ ε * (X / (A * B)) ≤ (max (X / A) (X / B)) ^ ((1 : ℝ) / 6) →
        (max (X / A) (X / B)) ^ ((2 : ℝ) / 3) * (X ^ ε * (X / (A * B))) ^ 2
          ≤ min (X / A) (X / B) →
        ‖detSum κ W A B X - zeroMode κ W A B X‖ ≤ C *
          (X ^ (1 + ε) *
              ((max (X / A) (X / B)) ^ (-(1 : ℝ) / 12) * (X / (A * B)) ^ ((3 : ℝ) / 4)
                + (max (X / A) (X / B)) ^ (-(2 : ℝ) / 3) * (min (X / A) (X / B)) ^ ((1 : ℝ) / 2)
                    * (X / (A * B))
                + (min (X / A) (X / B)) ^ (-(1 : ℝ) / 2) * (X / (A * B)))
            + X ^ ((1 : ℝ) / 2))

/-- **Theorem 1.3, zero frequency**: `S_κ⁰ ≪_W X exp(-c √log X)` in the hard square, with
`c` absolute. -/
def ZeroModeBound : Prop :=
  ∃ c > (0 : ℝ), ∀ κ : ℤ, (κ = 2 ∨ κ = -2) → ∀ W : ℝ × ℝ × ℝ × ℝ → ℂ, SmoothWeight W →
    ∃ C > (0 : ℝ), ∀ X A B : ℝ, 3 ≤ X → 1 ≤ A → A ≤ Real.sqrt X → 1 ≤ B → B ≤ Real.sqrt X →
      ‖zeroMode κ W A B X‖ ≤ C * X * Real.exp (-c * Real.sqrt (Real.log X))

end Determinant

end MobiusDeterminant
