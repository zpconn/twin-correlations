import MobiusDeterminant.Unconditional.Interfaces

/-!
# Level of distribution (paper §8): shared definitions

Definitions shared by the files `Level*.lean` proving

  `mobiusPairLevel_of_meanValue : MeanValueThm → MellinSeparation → PoissonAPDecay →
      ∀ θ < 9/17, MobiusPairLevel θ`.

All smooth weights are supported in `[1/2, 2]` (relative to their scale).

* `Tmp f A B k`      : `f` is `C^k` and `‖f^{(j)}‖ ≤ A B^j` for `j ≤ k` (a calculus of bounds).
* `bracket N₀ ψ d e` : `∑_{d ∣ n, e ∣ n+2} ψ(n/N₀) - N₀ ψ̂(0) ϱ(d,e)`.
* `smoothDelta`      : the smooth sum `Δ` of Proposition 8.1.
* `dyBump`, `topCut`, `piece` : smooth dyadic partition of unity with a smooth top cutoff.
* `chiCut`, `logCut`, `uPow` : `uPow τ x = x^{iτ}` on `[1/4, 8]`, globally smooth.
* `ellOf`, `kapOf`, `c0Of` : the parity data of Step 2 of Proposition 8.1.
-/

open Finset Real
open scoped ArithmeticFunction.Moebius

namespace MobiusDeterminant

namespace Level

/-- `f` is `C^k` and `‖f^{(j)}(x)‖ ≤ A B^j` for all `j ≤ k` and all `x`. -/
def Tmp (f : ℝ → ℂ) (A B : ℝ) (k : ℕ) : Prop :=
  ContDiff ℝ k f ∧ ∀ j ≤ k, ∀ x, ‖iteratedDeriv j f x‖ ≤ A * B ^ j

/-- The bracket of Proposition 8.1 for one pair `(d,e)`:
`∑_{1 ≤ n ≤ 2N₀, d ∣ n, e ∣ n+2} ψ(n/N₀) - N₀ ψ̂(0) ϱ(d,e)`. -/
noncomputable def bracket (N₀ : ℝ) (ψ : ℝ → ℂ) (d e : ℕ) : ℂ :=
  (∑ n ∈ (Finset.Icc 1 ⌊2 * N₀⌋₊).filter (fun n => d ∣ n ∧ e ∣ n + 2), ψ ((n : ℝ) / N₀))
    - (N₀ : ℂ) * fourierR ψ 0 * (dens d e : ℂ)

/-- The smooth sum `Δ` of Proposition 8.1 (weights supported in `[1/2,2]`). -/
noncomputable def smoothDelta (N₀ D E : ℝ) (ψ φ₁ φ₂ : ℝ → ℂ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 ⌊2 * D⌋₊, ∑ e ∈ Finset.Icc 1 ⌊2 * E⌋₊,
    (μ d : ℂ) * (μ e : ℂ) * φ₁ ((d : ℝ) / D) * φ₂ ((e : ℝ) / E) * bracket N₀ ψ d e

/-! ## Cutoffs -/

/-- Dyadic bump `β(y) = st(2y - 1) - st(y - 1)`; it vanishes outside `(1/2, 2)`, and
`∑_{j < J} β(x / 2^j) = st(2x - 1) - st(x / 2^{J-1} - 1)` (telescoping). -/
noncomputable def dyBump (y : ℝ) : ℝ :=
  smoothTransition (2 * y - 1) - smoothTransition (y - 1)

/-- Smooth top cutoff: `1` for `x ≤ (1-ν)K`, `0` for `x ≥ K`. -/
noncomputable def topCut (K ν x : ℝ) : ℝ :=
  1 - smoothTransition ((x - (1 - ν) * K) / (ν * K))

/-- A piece of the smoothed cutoff `topCut K ν` at scale `D`, as a function of `y = x / D`. -/
noncomputable def piece (K ν D : ℝ) (y : ℝ) : ℂ :=
  ((dyBump y * topCut K ν (D * y) : ℝ) : ℂ)

/-- `χ = 1` on `[1/4, 8]`, `χ = 0` outside `(1/8, 16)`, `0 ≤ χ ≤ 1`. -/
noncomputable def chiCut (x : ℝ) : ℝ :=
  smoothTransition (8 * x - 1) * (1 - smoothTransition (x / 8 - 1))

/-- A globally smooth, compactly supported function equal to `log x` on `[1/4, 8]`
(the argument of the logarithm is everywhere positive). -/
noncomputable def logCut (x : ℝ) : ℝ :=
  Real.log (x * chiCut x + (1 - chiCut x))

/-- `uPow τ x = exp(i τ logCut x)`, which equals `x^{iτ}` on `[1/4, 8]`. -/
noncomputable def uPow (τ x : ℝ) : ℂ :=
  Complex.exp (((τ * logCut x : ℝ) : ℂ) * Complex.I)

/-! ## Parity data (Proposition 8.1, Step 2)

For `d = 2^i d'`, `e = 2^j e'` (`d', e'` odd, coprime, `i, j ≤ 1`): `[d,e] = ℓ d' e'` with
`ℓ = ellOf i j`, and `n₀/[d,e] ≡ -κ d̄'/e' (mod 1)` with `κ = kapOf i j` (`κ ℓ = 2`).
The residue class is represented by `c0Of i j d' e' = ℓ d' t`, `t ≡ -κ d̄' (mod e')`. -/

/-- `ℓ = 1` if `i = j = 0`, else `2`. -/
def ellOf (i j : ℕ) : ℕ := if i = 0 ∧ j = 0 then 1 else 2

/-- `κ = 2` if `i = j = 0`, else `1`. -/
def kapOf (i j : ℕ) : ℤ := if i = 0 ∧ j = 0 then 2 else 1

/-- Representative of the residue class `{n : 2^i d' ∣ n, 2^j e' ∣ n+2}` modulo `ℓ d' e'`. -/
noncomputable def c0Of (i j d' e' : ℕ) : ℤ :=
  (ellOf i j : ℤ) * d' * ((((-kapOf i j : ℤ) : ZMod e') * ((d' : ZMod e'))⁻¹).val : ℤ)

end Level

end MobiusDeterminant
