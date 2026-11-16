import MobiusDeterminant.Determinant.Defs

/-!
# Theorem 1.3 and Corollary 1.4: statements

The final statements, as `Prop`s.  They are proved in `Determinant/Main.lean`.
-/

open Real

namespace MobiusDeterminant

namespace Determinant

/-- **Theorem 1.3, (1.4)**: on compact `K ⊂ Ω`, `S_κ = S_κ⁰ + O_{K,W,ε}(X^{1-σ(x,y)+ε})`
uniformly for `(x,y) ∈ K`, where `A = X^x`, `B = X^y`. -/
def DetPowerSaving : Prop :=
  ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Omega →
    ∀ κ : ℤ, (κ = 2 ∨ κ = -2) → ∀ W : ℝ × ℝ × ℝ × ℝ → ℂ, SmoothWeight W →
      ∀ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ X : ℝ, 3 ≤ X → ∀ p ∈ K,
        ‖detSum κ W (X ^ p.1) (X ^ p.2) X - zeroMode κ W (X ^ p.1) (X ^ p.2) X‖
          ≤ C * X ^ (1 - sigmaExp p + ε)

/-- **Theorem 1.3, (1.5)**: `S_κ ≪_{K,W} X exp(-c √log X)` on compact `K ⊂ Ω`,
with `c` absolute. -/
def DetCancellation : Prop :=
  ∃ c > (0 : ℝ), ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Omega →
    ∀ κ : ℤ, (κ = 2 ∨ κ = -2) → ∀ W : ℝ × ℝ × ℝ × ℝ → ℂ, SmoothWeight W →
      ∃ C > (0 : ℝ), ∀ X : ℝ, 3 ≤ X → ∀ p ∈ K,
        ‖detSum κ W (X ^ p.1) (X ^ p.2) X‖ ≤ C * X * Real.exp (-c * Real.sqrt (Real.log X))

/-- **Corollary 1.4** (diagonal): for `x = y ≥ 8/17 + η`, i.e. `D = E ≤ X^{9/17 - η'}`. -/
def DetDiagonal : Prop :=
  ∃ c > (0 : ℝ), ∀ η > (0 : ℝ),
    ∀ κ : ℤ, (κ = 2 ∨ κ = -2) → ∀ W : ℝ × ℝ × ℝ × ℝ → ℂ, SmoothWeight W →
      ∃ C > (0 : ℝ), ∀ X : ℝ, 3 ≤ X → ∀ x : ℝ, 8 / 17 + η ≤ x → x ≤ 1 / 2 →
        ‖detSum κ W (X ^ x) (X ^ x) X‖ ≤ C * X * Real.exp (-c * Real.sqrt (Real.log X))

end Determinant

end MobiusDeterminant
