import MobiusDeterminant.Determinant.Mellin4
import MobiusDeterminant.Determinant.Tensor
import MobiusDeterminant.Determinant.OddMain
import MobiusDeterminant.Determinant.Reduction
import MobiusDeterminant.Determinant.Assembly

/-!
# Theorem 1.3 and Corollary 1.4, unconditionally

The components in `Determinant/` discharge the interfaces of `Determinant/Defs.lean`:

* `mellinSep4 : MellinSep4` — four-variable Mellin separation of the weight `W`;
* `detTensorBound : DetTensorBound` — the error term for product weights, from the
  mean-value theorem (Theorem 6.1) via Poisson summation, as in §8;
* `oddMainBound : OddMainBound` — the main term for product weights, from the prime number
  theorem for `μ`;
* `detErrorBound_of`, `zeroModeBound_of` — reduction of `S_κ` and `S_κ⁰` to product weights;
* `detPowerSaving_of`, `detCancellation_of`, `detDiagonal_of` — exponent bookkeeping on
  compact subsets of `Ω`.
-/

namespace MobiusDeterminant

namespace Determinant

/-- Theorem 1.3, power-saving part, in terms of `X, A, B`. -/
theorem detErrorBound : DetErrorBound :=
  detErrorBound_of mellinSep4 detTensorBound

/-- Theorem 1.3, the zero frequency. -/
theorem zeroModeBound : ZeroModeBound :=
  zeroModeBound_of mellinSep4 oddMainBound

/-- **Theorem 1.3, (1.4)**: for compact `K ⊂ Ω`, `κ = ±2`, smooth `W` supported in `[1,2]⁴`
and `ε > 0`, `S_κ = S_κ⁰ + O(X^{1-σ(x,y)+ε})` uniformly for `(x,y) ∈ K`. -/
theorem detSum_sub_zeroMode : DetPowerSaving :=
  detPowerSaving_of detErrorBound

/-- **Theorem 1.3, (1.5)**: `S_κ ≪_{K,W} X exp(-c √log X)` on compact `K ⊂ Ω`. -/
theorem detSum_cancellation : DetCancellation :=
  detCancellation_of detErrorBound zeroModeBound

/-- **Corollary 1.4**: the diagonal `x = y > 8/17`. -/
theorem detSum_diagonal : DetDiagonal :=
  detDiagonal_of detSum_cancellation

end Determinant

end MobiusDeterminant
