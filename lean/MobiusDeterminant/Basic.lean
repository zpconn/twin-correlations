import Mathlib

/-!
# Shared definitions

This file fixes the objects and the hypotheses used by the formalization of
the deduction

  (level of distribution for Möbius-weighted divisor pairs)
  + (prime number theorem for μ)
  ⟹  ∑_{n ≤ N} Λ_R(n) Λ_R(n+2) = 𝔖 N + O(N exp(-c √(log R)))   (R ≤ N^θ).

Hypotheses are recorded as `Prop`s, never as axioms:

* `PNTMobius`: the classical prime number theorem for the Möbius function
  with de la Vallée Poussin–Landau error term (a standard published theorem);
* `MobiusPairLevel θ`: Theorem 1.2 of the accompanying paper (proved there
  for every θ < 9/17; its own formalization is staged separately).

Everything else in the deduction is proved in Lean.
-/

open Finset Real
open scoped ArithmeticFunction.Moebius

namespace MobiusDeterminant

/-- Truncated von Mangoldt function `Λ_R(n) = ∑_{d ∣ n, d ≤ R} μ(d) log(R/d)`. -/
noncomputable def LambdaR (R : ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.filter (fun d : ℕ => (d : ℝ) ≤ R), (μ d : ℝ) * Real.log (R / (d : ℝ))

/-- Density of the integers `n` with `d ∣ n` and `e ∣ n + 2`:
`1/lcm(d,e)` if `gcd(d,e) ∣ 2`, and `0` otherwise. -/
noncomputable def dens (d e : ℕ) : ℝ :=
  if Nat.gcd d e ∣ 2 then 1 / (Nat.lcm d e : ℝ) else 0

/-- `#{1 ≤ n ≤ N : d ∣ n, e ∣ n + 2}`. -/
def pairCount (N d e : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (fun n => d ∣ n ∧ e ∣ n + 2)).card

/-- Remainder `r_N(d,e) = #{n ≤ N : d ∣ n, e ∣ n+2} - N · dens(d,e)`. -/
noncomputable def rem (N d e : ℕ) : ℝ :=
  (pairCount N d e : ℝ) - (N : ℝ) * dens d e

/-- Main-term sum `M(R) = ∑_{d,e ≤ R} μ(d) μ(e) log(R/d) log(R/e) dens(d,e)`. -/
noncomputable def mainSum (R : ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 ⌊R⌋₊, ∑ e ∈ Finset.Icc 1 ⌊R⌋₊,
    (μ d : ℝ) * (μ e : ℝ) * Real.log (R / d) * Real.log (R / e) * dens d e

/-- Local factor of the twin-prime singular series at `p`:
`2` at `p = 2`, and `1 - 1/(p-1)^2` at odd `p`. -/
noncomputable def twinLocal (p : ℕ) : ℝ :=
  if p = 2 then 2 else 1 - 1 / ((p : ℝ) - 1) ^ 2

/-- The twin-prime constant `𝔖 = 2 ∏_{p > 2} (1 - 1/(p-1)^2)`. -/
noncomputable def twinConstant : ℝ :=
  ∏' p : Nat.Primes, twinLocal (p : ℕ)

/-- `S_g(y) = ∑_{d ≤ y, (d,g)=1} μ(d) log(y/d) / d`. -/
noncomputable def Sg (g : ℕ) (y : ℝ) : ℝ :=
  ∑ d ∈ (Finset.Icc 1 ⌊y⌋₊).filter (fun d => Nat.Coprime d g),
    (μ d : ℝ) * Real.log (y / d) / d

/-! ## Hypotheses and intermediate statements -/

/-- Prime number theorem for the Möbius function with the classical error term:
`|∑_{n ≤ x} μ(n)| ≤ C x exp(-c √(log x))` for `x ≥ 2`.  Standard (Landau). -/
def PNTMobius : Prop :=
  ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ x : ℝ, 2 ≤ x →
    |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (μ n : ℝ)| ≤ C * x * Real.exp (-c * Real.sqrt (Real.log x))

/-- Level of distribution `θ` for Möbius-weighted divisor pairs: for some `δ > 0`,
all sharp boxes `d ≤ K`, `e ≤ L` with `K, L ≤ N^θ` satisfy
`|∑_{d ≤ K, e ≤ L} μ(d) μ(e) r_N(d,e)| ≤ C N^{1-δ}`.
This is Theorem 1.2 of the paper, proved there for every `θ < 9/17`. -/
def MobiusPairLevel (θ : ℝ) : Prop :=
  ∃ δ > (0 : ℝ), ∃ C > (0 : ℝ), ∀ N : ℕ, 2 ≤ N → ∀ K L : ℕ,
    (K : ℝ) ≤ (N : ℝ) ^ θ → (L : ℝ) ≤ (N : ℝ) ^ θ →
      |∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 L, (μ d : ℝ) * (μ e : ℝ) * rem N d e|
        ≤ C * (N : ℝ) ^ (1 - δ)

/-- Main-term asymptotic `M(R) = 𝔖 + O(exp(-c √(log R)))`. -/
def MainTermAsymp : Prop :=
  ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ R : ℝ, 2 ≤ R →
    |mainSum R - twinConstant| ≤ C * Real.exp (-c * Real.sqrt (Real.log R))

/-- Uniform asymptotic `S_g(y) = g/φ(g) + O(g^3 exp(-c √(log y)))`.
Interface between the two main-term files; proved from `PNTMobius`. -/
def SgAsymp : Prop :=
  ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ g : ℕ, 1 ≤ g → ∀ y : ℝ, 2 ≤ y →
    |Sg g y - (g : ℝ) / (Nat.totient g : ℝ)|
      ≤ C * (g : ℝ) ^ 3 * Real.exp (-c * Real.sqrt (Real.log y))

end MobiusDeterminant
