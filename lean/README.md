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

## Theorem 1.3 and Corollary 1.4 (unconditional)

The definitions are in `Determinant/Defs.lean` and the statements in
`Determinant/Statement.lean`.  The definitions are `detSum` (S_κ, paper
(1.3)), `zeroMode` (S_κ⁰, paper (7.3)), `Omega` and `sigmaExp`.

| Paper | Lean theorem | Statement |
|---|---|---|
| Thm 1.3, (1.4) | `Determinant.detSum_sub_zeroMode` | `DetPowerSaving`: `‖S_κ − S_κ⁰‖ ≤ C X^{1−σ(x,y)+ε}` on compact `K ⊂ Ω` |
| Thm 1.3, bound for S_κ⁰ | `Determinant.zeroModeBound` | `ZeroModeBound`: `‖S_κ⁰‖ ≤ C X exp(−c√log X)` |
| Thm 1.3, (1.5) | `Determinant.detSum_cancellation` | `DetCancellation`: `‖S_κ‖ ≤ C X exp(−c√log X)` on compact `K ⊂ Ω` |
| Cor 1.4 | `Determinant.detSum_diagonal` | `DetDiagonal` |

All are in `Determinant/Main.lean`.  `#print axioms` reports only the three
standard axioms for every theorem above and for the Theorem 1.1 result,
over the whole dependency cone with external libraries included.  No
`sorry`, `axiom` or `native_decide` appears in this project, which is about
19.9k lines.

## Section 10 of the paper: `Barrier.lean`

`Barrier.lean` checks the arithmetic and the elementary identities of the
paper's section on the barrier at level 4/7.  It formalizes **none** of the
analytic estimates quoted there (Deshouillers–Iwaniec, Irving, Polymath8a,
Maynard, Pascadi), so every *Claim* of that section remains unverified.  For
example `conrey_error_iff` says that an error term
`N^ε (R^{7/4} + N^{1/2} R^{7/8})` is a power saving exactly for `θ < 4/7`;
it does not say that the error term has that shape.

| Paper §10 | Lean (`MobiusDeterminant.Barrier`) |
|---|---|
| Lemma 10.1 and the table of levels | `saving_suffices_iff`, `level_table`, `level_chain` |
| Remark 1.5, Irving's region | `irving_diagonal_iff`, `irving_level`, `irving_at_half`, `irving_crossing` |
| Claim 10.2, exponents only | `conrey_error_iff` |
| Claim 10.3, the window | `window_nonempty_iff`, `window'_nonempty_iff`, `window_at_four_sevenths`, `window_third_condition` |
| Lemma 10.4 | `balanced_mem_window_iff`, `balanced_mem_window'_iff` |
| The box and the units at θ = 4/7 | `box_sum`, `box_at_four_sevenths`, `dual_length_eq_iff`, `mean_eq_iff` |
| (F4), pairs of solutions | `pair_of_solutions`, `positivity_gap` |
| Claim 10.6, exponents only | `ls_to_pairs`, `pairs_to_dual`, `ls_sizes` |
| Lemma 10.7 (quadratic roots, reciprocity) | `quadratic_root`, `coprime_modulus`, `kloosterman_fraction_eq_root`, `reciprocity` |
| (F9), moments of ζ | `moment_table`, `momentLength_inv` |
| The two determinants | `det_two`, `det_three` |
| Lemma 10.8 | `binding_condition_iff`, `di_conditions_balanced_iff`, `polymath_window_nonempty_iff`, `polymath_window_at_four_sevenths` |
| Claim 10.9, the two inequalities | `nogo_modulus_bound`, `nogo_saving_bound` |
| §10.6, sizes | `bblr_range_iff`, `watt_short`, `level_loss_iff`, `gm_sizes` |

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
| Thm 1.3, Cor 1.4 (assembly on compact `K ⊂ Ω`) | `detPowerSaving_of`, `detCancellation_of`, `detDiagonal_of` | `Determinant/Assembly.lean` | 185 |
| §7: S_κ − S_κ⁰ as a superposition of product-weight sums | `detErrorBound_of`, `zeroModeBound_of` | `Determinant/Reduction*.lean` | 1834 |
| §7: error term for product weights, unbalanced range | `detTensorBound` | `Determinant/Tensor*.lean` | 918 |
| §7.3: main term for product weights | `oddMainBound` | `Determinant/OddMain*.lean` | 638 |
| Four-variable Mellin separation of `W` | `mellinSep4` | `Determinant/Mellin4.lean` | 120 |

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
5. **Theorem 1.3.** Instead of Poisson summation in `a` modulo `2e`, the
   formal proof writes `n = ad` and expands `W` by a four-variable Mellin
   transform, via Schwartz-space Fourier inversion.  Each product-weight
   piece is a smooth odd divisor-pair sum.  These are handled by the §8
   machinery, generalized to unbalanced `D, E` with the exact three-term
   saving.  The zero frequency is matched with the main term by the
   substitution `n/X = α d/D`, and `κ = −2` reduces exactly to `κ = 2` by
   swapping `(a,d) ↔ (b,e)`.

## Trust boundary

The kernel checks that the theorems follow from the definitions in
`Basic.lean` and `Determinant/Defs.lean`.  Whether those definitions
faithfully encode the paper's `Λ_R`, `𝔖`, `S_κ`, `S_κ⁰`, `Ω` and `σ` needs
human review.  Both files are short and documented for this purpose.
