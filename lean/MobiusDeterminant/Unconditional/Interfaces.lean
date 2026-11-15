import MobiusDeterminant.Basic

/-!
# Interfaces for the unconditional formalization

The unconditional proof of Theorem 1.1 (paper) is split into components whose
statements are fixed here as `Prop`s.  Each component is proved in its own
file, possibly assuming other components' `Prop`s; `Unconditional/Main.lean`
chains them so that the final theorem depends on no hypotheses.

Dependency graph (→ means "is used to prove"):

* `bloomMaynardE4 : BloomMaynardE4`                       (Bloom–Maynard Thm 2, m = 2)
* `mellinSeparation : MellinSeparation`                   (analytic toolkit)
* `poissonAPDecay : PoissonAPDecay`                       (analytic toolkit)
* `BloomMaynardE4 → BalancedBoxBound`                     (paper Prop 5.1 + Steps 1, 3 of Thm 6.1)
* `BalancedBoxBound → MellinSeparation → MeanValueThm`    (paper Thm 6.1; long boxes via Lean Pool's Weil bound)
* `MeanValueThm → MellinSeparation → PoissonAPDecay → ∀ θ < 9/17, MobiusPairLevel θ`   (paper §8)
* `pntMobius : PNTMobius`                                 (prime number theorem for μ, from PNT+)

External inputs are imported from Lean Pool (`KloostermanWeil`: the Weil bound for
squarefree moduli; `BGS.NumberTheory`: the divisor bound) and from PNT+
(`PrimeNumberTheoremAnd`).  They are theorems, not hypotheses.
-/

open Finset Real
open scoped ArithmeticFunction.Moebius

namespace MobiusDeterminant

/-! ## Smooth functions with polynomially controlled derivatives -/

/-- `f` is `C^k`, vanishes outside `[a,b]`, and `‖f^{(j)}‖ ≤ P^j` for every `j ≤ k`. -/
def TemperedOn (f : ℝ → ℂ) (P : ℝ) (k : ℕ) (a b : ℝ) : Prop :=
  ContDiff ℝ k f ∧ (∀ x, x ∉ Set.Icc a b → f x = 0) ∧
    ∀ j ≤ k, ∀ x, ‖iteratedDeriv j f x‖ ≤ P ^ j

/-- Fourier transform `f̂(ξ) = ∫ f(x) e(-xξ) dx` on `ℝ`. -/
noncomputable def fourierR (f : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  ∫ x : ℝ, Complex.exp (-(2 * π * x * ξ : ℝ) * Complex.I) * f x

/-! ## Analytic toolkit -/

/-- **Mellin separation** (paper Lemma 2.7, one variable).  A tempered function on
`[a,b] ⊂ (0,∞)` is an integral of characters `t ↦ t^{-iτ}` against a density whose
`(1+|τ|)^m`-weighted `L¹` norm is `O(P^k)`. -/
def MellinSeparation : Prop :=
  ∀ a b : ℝ, 0 < a → a < b → ∀ m : ℕ, ∃ C > (0 : ℝ), ∃ k : ℕ, ∀ (f : ℝ → ℂ) (P : ℝ), 1 ≤ P →
    TemperedOn f P k a b →
    ∃ g : ℝ → ℂ,
      MeasureTheory.Integrable (fun τ : ℝ => (1 + |τ|) ^ m * ‖g τ‖) ∧
      (∫ τ : ℝ, (1 + |τ|) ^ m * ‖g τ‖) ≤ C * P ^ k ∧
      ∀ t : ℝ, 0 < t → f t = ∫ τ : ℝ, g τ * Complex.exp (-(τ * Real.log t : ℝ) * Complex.I)

/-- **Poisson summation in a residue class, with Fourier decay** (paper Lemma 2.2). -/
def PoissonAPDecay : Prop :=
  ∀ a b : ℝ, 0 < a → a < b → ∀ k : ℕ, 2 ≤ k → ∃ C > (0 : ℝ), ∀ (f : ℝ → ℂ) (P : ℝ), 1 ≤ P →
    TemperedOn f P k a b →
    (∀ ξ : ℝ, ‖fourierR f ξ‖ ≤ C * P ^ k * (1 + |ξ|) ^ (-(k : ℝ))) ∧
    ∀ X : ℝ, 0 < X → ∀ q : ℕ, 0 < q → ∀ c : ℤ,
      HasSum
        (fun h : ℤ => ((X / q : ℝ) : ℂ) * fourierR f (h * X / q) *
          Complex.exp (2 * π * Complex.I * ((h * c : ℤ) : ℂ) / (q : ℂ)))
        (∑' n : ℤ, if n ≡ c [ZMOD (q : ℤ)] then f (n / X) else 0)

/-! ## Bloom–Maynard -/

/-- Additive energy `E₄(B) = #{b₁ + b₂ = b₃ + b₄}` of a finite set of rationals. -/
def energy4 (B : Finset ℚ) : ℕ :=
  ((B ×ˢ B ×ˢ B ×ˢ B).filter (fun x => x.1 + x.2.1 = x.2.2.1 + x.2.2.2)).card

/-- **Bloom–Maynard, Theorem 2 with `m = 2`** (with the harmless loss `Q^ε` in place of
`(log Q)^C`).  Rationals are automatically reduced in `ℚ`. -/
def BloomMaynardE4 : Prop :=
  ∀ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ (Q n : ℕ) (B : Finset ℚ), 1 ≤ Q → 1 ≤ n →
    (∀ b ∈ B, 0 ≤ b ∧ b ≤ 1 ∧ b.den ≤ Q) →
    (∀ q : ℕ, (B.filter (fun b => b.den = q)).card ≤ n) →
    (energy4 B : ℝ) ≤ C * (Q : ℝ) ^ ε * ((Q : ℝ) * n) ^ 2

/-! ## The mean-value theorem -/

/-- Kloosterman fraction `e_e(h · d̄)`, with `d̄` the inverse of `d` modulo `e`. -/
noncomputable def kfrac (e : ℕ) (h : ℤ) (d : ℕ) : ℂ :=
  Complex.exp (2 * π * Complex.I *
    ((((h : ZMod e) * (d : ZMod e)⁻¹).val : ℕ) : ℂ) / (e : ℂ))

/-- `P_e = ∑_{(d,2e)=1} μ(d) V(d/D) ∑_{|h| ≤ H} ν_h e_e(h d̄)` (paper (6.1)). -/
noncomputable def Pe (D : ℝ) (V : ℝ → ℂ) (ν : ℤ → ℂ) (Hn : ℕ) (e : ℕ) : ℂ :=
  ∑ d ∈ (Finset.Icc 1 ⌊8 * D⌋₊).filter (fun d => Nat.Coprime d (2 * e)),
    (μ d : ℂ) * V (d / D) * ∑ h ∈ Finset.Icc (-(Hn : ℤ)) Hn, ν h * kfrac e h d

/-- **Theorem 6.1** (mean-value theorem), for `V` supported in `[1/8, 8]` and squarefree
moduli `e ∈ (E/8, 8E]`. -/
def MeanValueThm : Prop :=
  ∀ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∃ k : ℕ,
    ∀ (D E P : ℝ) (Hn : ℕ) (V : ℝ → ℂ) (ν : ℤ → ℂ),
      2 ≤ D → 1 ≤ E → E ≤ D → 1 ≤ Hn → (Hn : ℝ) ≤ D ^ ((1 : ℝ) / 6) →
      D ^ ((2 : ℝ) / 3) * (Hn : ℝ) ^ 2 ≤ E →
      1 ≤ P → TemperedOn V P k (1 / 8) 8 → ν 0 = 0 → (∀ h, ‖ν h‖ ≤ 1) →
      ∑ e ∈ (Finset.Ioc ⌊E / 8⌋₊ ⌊8 * E⌋₊).filter Squarefree, ‖Pe D V ν Hn e‖ ^ 2
        ≤ (C * P ^ k * D ^ ε *
            (D ^ ((11 : ℝ) / 12) * E ^ ((1 : ℝ) / 2) * (Hn : ℝ) ^ ((3 : ℝ) / 4)
              + D ^ ((1 : ℝ) / 3) * E * Hn + D * Hn)) ^ 2

/-- Balanced bilinear form `∑_{u,w} α_u β_w ∑_h ν_h e_e(h \overline{uw})` over `(uw, 2e) = 1`. -/
noncomputable def balForm (α β : ℕ → ℂ) (Umax Wmax : ℕ) (ν : ℤ → ℂ) (Hn : ℕ) (e : ℕ) : ℂ :=
  ∑ u ∈ Finset.Icc 1 Umax, ∑ w ∈ Finset.Icc 1 Wmax,
    if Nat.Coprime (u * w) (2 * e) then
      α u * β w * ∑ h ∈ Finset.Icc (-(Hn : ℤ)) Hn, ν h * kfrac e h (u * w)
    else 0

/-- **Balanced-box bound** (paper Prop 5.1 with the gcd strata of Steps 1 and 3 of
Theorem 6.1): for coefficients bounded by `1` on `(U₀, 2⁹U₀]` and `(W₀, 2⁹W₀]`,
`‖·‖_{ℓ²(e)} ≪ (U₀W₀E)^ε (U₀W₀H)^{3/4} E^{3/8} {(E + (U₀H)²)(E + W₀²)}^{1/8}`. -/
def BalancedBoxBound : Prop :=
  ∀ ε > (0 : ℝ), ∃ C > (0 : ℝ),
    ∀ (U₀ W₀ E : ℝ) (Hn : ℕ) (α β : ℕ → ℂ) (ν : ℤ → ℂ),
      1 ≤ U₀ → U₀ ≤ W₀ → 1 ≤ E → 1 ≤ Hn → (Hn : ℝ) ≤ U₀ →
      (∀ u, α u ≠ 0 → U₀ < u ∧ (u : ℝ) ≤ 2 ^ 9 * U₀) → (∀ u, ‖α u‖ ≤ 1) →
      (∀ w, β w ≠ 0 → W₀ < w ∧ (w : ℝ) ≤ 2 ^ 9 * W₀) → (∀ w, ‖β w‖ ≤ 1) →
      ν 0 = 0 → (∀ h, ‖ν h‖ ≤ 1) →
      ∑ e ∈ (Finset.Ioc ⌊E / 8⌋₊ ⌊8 * E⌋₊).filter Squarefree,
          ‖balForm α β ⌊2 ^ 9 * U₀⌋₊ ⌊2 ^ 9 * W₀⌋₊ ν Hn e‖ ^ 2
        ≤ (C * (U₀ * W₀ * E) ^ ε * (U₀ * W₀ * Hn) ^ ((3 : ℝ) / 4) * E ^ ((3 : ℝ) / 8) *
            ((E + (U₀ * Hn) ^ 2) * (E + W₀ ^ 2)) ^ ((1 : ℝ) / 8)) ^ 2

end MobiusDeterminant
