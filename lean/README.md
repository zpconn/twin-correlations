# Lean formalization

Lean v4.35.0 with Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`.

```sh
lake exe cache get   # fetch prebuilt Mathlib
lake build           # builds everything (~4.5k lines)
```

## What is proved

```lean
theorem MobiusDeterminant.lambdaR_twin_correlation (θ : ℝ) (hθ : 0 < θ)
    (hL : MobiusPairLevel θ) (hPNT : PNTMobius) :
    ∃ c > 0, ∃ C > 0, ∀ N : ℕ, ∀ R : ℝ, 2 ≤ N → 2 ≤ R → R ≤ N ^ θ →
      |∑ n ∈ Finset.Icc 1 N, LambdaR R n * LambdaR R (n + 2) - twinConstant * N|
        ≤ C * N * Real.exp (-c * √(Real.log R))
```

This is Theorem 1.1 of the paper, conditional on two hypotheses, which are
stated as `Prop`s in `Basic.lean` (never as `axiom`s):

| Hypothesis | Meaning | Status |
|---|---|---|
| `MobiusPairLevel θ` | Theorem 1.2: `|∑_{d≤K, e≤L} μ(d)μ(e) r_N(d,e)| ≤ C N^{1−δ}` for `K, L ≤ N^θ` | Proved in the paper for `θ < 9/17`; not formalized |
| `PNTMobius` | `|∑_{n≤x} μ(n)| ≤ C x exp(−c√log x)` | Classical (Landau); not formalized here |

`#print axioms lambdaR_twin_correlation` reports only `propext`,
`Classical.choice` and `Quot.sound`.  There is no `sorry`, `axiom` or
`native_decide` anywhere in the project.

## File map

| File | Contents | Paper |
|---|---|---|
| `Basic.lean` | Definitions (Λ_R, ϱ, r_N, M(R), 𝔖, S_g) and the hypothesis `Prop`s | §§1, 9 |
| `LambdaR/Expansion.lean` | `sum_LambdaR_mul_eq`: Σ Λ_R Λ_R = N·M(R) + Σ μμLL·r_N | Lemma 9.1 |
| `LambdaR/Abel.lean` | `abs_sum_mul_log_log_le`: double Abel summation | Lemma 9.2 |
| `LambdaR/Assembly.lean` | `lambdaR_twin_of_level_of_mainTerm` | §9.2 |
| `MainTerm/ReductionIdentity.lean` | gcd expansion; `mainSum_eq_sum_Sg` | Lemma 9.6 |
| `MainTerm/ReductionSeries.lean` | `twinConstant_eq_tsum_sfun` (Euler product); φ lower bound | Prop. 9.3 |
| `MainTerm/Reduction.lean` | `mainTermAsymp_of_sgAsymp`: tails and the final error bound | Prop. 9.3 |
| `MainTerm/MobiusSums*.lean` | `sgAsymp_of_PNT`: Σμ(n)/n = 0, S_1(z) → 1, convolution identity, Rankin | Lemmas 9.4, 9.5 |
| `Main.lean` | `lambdaR_twin_correlation`, `mainTermAsymp_of_PNT` | Thm. 1.1 |
| `Exponents.lean` | Every exponent computation in the paper (see below) | throughout |
| `Core/KorolevChanga.lean` | Lemma 3.1, for any primitive additive character of ℤ/qℤ | Lemma 3.1 |
| `Core/HeathBrown.lean` | Heath-Brown identity for μ | Lemma 2.6 |
| `Core/CRT.lean` | CRT phase identity; description of solutions of be − ad = κ | §7.2 |
| `Core/Energy.lean` | Exact counting behind the averaged energy bounds | Lemmas 4.1, 4.3 |

`Exponents.lean` covers:

* `8x + 9y > 8 ⇔ T < D^{1/9}`;
* the Step 3 case analysis of Theorem 6.1;
* the long-box condition;
* the three savings and their comparison;
* the geometry of Ω;
* the Bettin–Chandee region and its strict inclusion in Ω;
* the thresholds 16/33, 8/17, 17/33, 9/17 and 48/95;
* the exponent hypotheses used in Proposition 8.1.

## What is not formalized

The analytic proof of Theorems 1.2, 1.3 and 6.1 is not formalized.  That
proof consists of:

* Poisson summation with decay;
* separation of variables;
* divisor-bound bookkeeping;
* the Weil–Estermann bound;
* the Bloom–Maynard theorem.

Theorem 1.2 therefore enters as the hypothesis `MobiusPairLevel θ`.  The
`Core/` and `Exponents.lean` files machine-check its elementary ingredients
and all of its numerical bookkeeping.  `ROADMAP.md` lists the path to
discharging the hypotheses.

## Trust boundary

The kernel guarantees that the theorems follow from the definitions and
hypotheses as written.  Whether `Basic.lean` faithfully encodes the paper's
objects needs human review.  The file is short and documented for this
purpose.
