# Lean formalization

Lean v4.35.0, Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`.

```sh
lake exe cache get   # prebuilt Mathlib
lake build           # builds this project plus the needed parts of Lean Pool and PNT+
```

## Main theorem (unconditional)

```lean
theorem MobiusDeterminant.lambdaR_twin_correlation_unconditional
    (θ : ℝ) (hθ : 0 < θ) (hθ' : θ < 9 / 17) :
    ∃ c > 0, ∃ C > 0, ∀ N : ℕ, ∀ R : ℝ, 2 ≤ N → 2 ≤ R → R ≤ N ^ θ →
      |∑ n ∈ Finset.Icc 1 N, LambdaR R n * LambdaR R (n + 2) - twinConstant * N|
        ≤ C * N * Real.exp (-c * √(Real.log R))
```

This is Theorem 1.1 of the paper, with no hypotheses.
`#print axioms` reports only `propext`, `Classical.choice` and `Quot.sound`,
for the whole dependency cone, external libraries included.  No `sorry`,
`axiom` or `native_decide` appears in this project.  The project is about
15.5k lines.

## Components

The interfaces are fixed as `Prop`s in `Unconditional/Interfaces.lean`;
`Unconditional/Main.lean` chains the components.

| Paper | Lean theorem | Files | Lines |
|---|---|---|---|
| Thm 1.1 | `lambdaR_twin_correlation_unconditional` | `Unconditional/Main.lean` | 41 |
| §9: Λ_R from Thm 1.2 + PNT(μ) | `lambdaR_twin_correlation` | `Main.lean`, `LambdaR/`, `MainTerm/` | (part of 4.5k) |
| Thm 1.2 (θ < 9/17) | `mobiusPairLevel_of_meanValue` | `Unconditional/Level*.lean` | 4498 |
| Thm 6.1 | `meanValueThm_of` | `Unconditional/MeanValue*.lean` | 2696 |
| Prop 5.1 + strata | `balancedBoxBound_of_BM` | `Unconditional/Balanced*.lean` | 1356 |
| Bloom–Maynard Thm 2 (m = 2) | `bloomMaynardE4` | `Unconditional/BloomMaynard.lean` | 663 |
| PNT for μ, error `x e^{-c√log x}` | `pntMobius` | `Unconditional/PNTMobius*.lean` | 1202 |
| Lemmas 2.2, 2.7 | `poissonAPDecay`, `mellinSeparation` | `Unconditional/Toolkit.lean` | 382 |
| Lemmas 2.6, 3.1, 4.1, 4.3 | Heath-Brown, Korolev–Changa, energies | `Core/` | |
| Exponent computations | many | `Exponents.lean` | |

## External formalizations reused (not re-proved)

Both libraries are pinned to the same Mathlib commit as this project.

- **Lean Pool** (`LeanPool/lean-pool` @ `595ff87`):
  - `KloostermanWeil`: the Weil bound for Kloosterman sums to squarefree
    moduli, adapted from C. Dorsey's Weil Bounds Toolkit;
  - `MarkoffModP.BGS.NumberTheory.DivisorBound`: the divisor bound
    `τ(n) ≤ n^ε`.
- **PNT+** (`AlexKontorovich/PrimeNumberTheoremAnd` @ `a4fb698`):
  - the zero-free region `ZetaZeroFree1`;
  - log-derivative and `1/ζ` bounds;
  - the smoothed Mellin–Perron pipeline, adapted here from `-ζ'/ζ` to `1/ζ`.

To our knowledge two formalizations here are new: Bloom–Maynard's energy
bound, and the prime number theorem for μ with error `x exp(−c√log x)`.

## Differences from the written proof (none affect statements)

1. **Balanced boxes.** Korolev–Changa is applied to arbitrary residues
   `h·ū mod e`, grouped by the reduced fraction `h/u`.  This removes the
   paper's gcd strata `g = (h, e)`.
2. **Long boxes.** Sharp dyadic intervals and completion over ℤ/qℤ, with
   Lean Pool's Weil bound, replace the smooth Poisson step.
3. **Proposition 8.1.** One-variable Mellin separation suffices, because the
   coupled weight depends only on `h/(d'e')`.
4. **PNT for μ.** It uses a bound `1/ζ ≪ (1+|t|)^{1/2}` in the zero-free
   region, obtained by Grönwall's inequality.
5. **Theorem 1.3.** The determinant form is not formalized separately; the
   formal route goes through the correlation form, Theorem 1.2.

## Trust boundary

The kernel checks that the theorem follows from the definitions in
`Basic.lean`.  Whether those definitions faithfully encode the paper's
`Λ_R` and `𝔖` needs human review.  The file is short and documented for
this purpose.
