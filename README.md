# Twin correlations of truncated von Mangoldt functions up to level 9/17: a formalized proof and the barrier at 4/7

**Investigator:** Zach Conn

> **Status: draft, not yet verified by a human expert.**  The mathematics
> here was generated with extensive AI assistance.  See
> [`AI_DISCLOSURE.md`](AI_DISCLOSURE.md).

## What this is

A machine-checked proof of an asymptotic for twin correlations of truncated
von Mangoldt functions past level 1/2, and a synthesis of what is known
about the problem up to the barrier at level 4/7.  The exponent proved here,
9/17, is **not** a record: known methods appear to give 4/7.  The
contribution is the formalization, the proof mechanism, and the analysis of
the barrier.

## Main result

Let `Λ_R(n) = Σ_{d | n, d ≤ R} μ(d) log(R/d)`, so that `Λ_N = Λ` on
`(1, N]`.  Let `𝔖 = 2 ∏_{p>2} (1 − 1/(p−1)²)` be the twin-prime constant.

**Theorem 1.1.** For every fixed `θ < 9/17`,

```
Σ_{n ≤ N} Λ_R(n) Λ_R(n+2) = 𝔖 N + O(N exp(−c √log R))   uniformly for 2 ≤ R ≤ N^θ.
```

The truncation level `R = N^θ` is a dial between two cases:

* `θ ≤ 1/2`: classical, by the Chinese remainder theorem;
* `θ = 1`: the twin-prime conjecture.

The theorem is formalized in Lean 4 with no hypotheses (see below).  Its
proof uses no spectral theory of automorphic forms: the inputs are Weil's
bound, the Heath-Brown identity, a Korolev–Changa inequality averaged over
moduli, and the Bloom–Maynard energy bound.  That is what made a complete
formalization feasible.

## Where 9/17 stands

| Level | Source | Status |
|---|---|---|
| 48/95 | Coppola–Laporta, via Duke–Friedlander–Iwaniec | published; checked against the arXiv source |
| 17/33 | Bettin–Chandee trilinear bound (paper, Appendix A) | checked against the arXiv source |
| **9/17** | **this project** | **machine-checked** |
| 8/15 | Irving (2014), transposed from Λ to μ | AI computation, unchecked |
| 4/7 | Conrey (1989) with Deshouillers–Iwaniec, transposed to a fixed shift | AI computation, unchecked |
| 3/5, 5/8 | Maynard; Pascadi — only when the weight has a flexible factor | AI computation, unchecked |

The parity problem remains, and nothing here bears on the twin-prime
conjecture itself.

## The barrier at 4/7 (paper §10)

An attempt to pass 4/7 was made on 2026-11-15 and did not succeed.  The
paper records it, including the routes that failed:

* **Reduction.**  Decomposing both μ(d) and μ(e), every piece with a factor
  in a certain window is covered up to level 3/5.  What is left is one
  estimate: the count of `b·ℓ₁ℓ₂ − a·n₁n₂ = 2` with all six variables
  smooth, in the box (3/7, 2/7, 2/7)² — a restricted additive divisor
  problem for d₃ × d₃.
* **Equivalent forms.**  A variance of the divisor function over a thin set
  of residue classes; a mean square of exponential sums at one level; a
  second moment of L(½, f) twisted by an Atkin–Lehner sign; Weyl sums over
  roots of `qν² + 1 ≡ 0 (mod D)`; a fourth moment of ζ twisted by a
  Dirichlet polynomial of length T^{2/5+δ}.
* **Why 4/7.**  Three methods of different nature (Deshouillers–Iwaniec,
  Polymath8a Type III, Bessel's inequality in the spectral form) are tight
  at exactly 4/7, and a counting argument shows that Cauchy–Schwarz plus
  completion cannot do better.
* **Experiments.**  Both targets hold numerically with a wide margin
  (`notes/lab/`).
* **Literature examined** and found not to apply: Watt;
  Bettin–Bui–Li–Radziwiłł; Fouvry–Kowalski–Michel; Sharma; Buttcane;
  Grimmelt–Merikoski.

Statements in that section labelled *Claim* are AI exponent computations
that no human has checked.  Its arithmetic and elementary identities are
machine-checked (`lean/MobiusDeterminant/Barrier.lean`).  Working notes:
[`notes/programme-4-7.md`](notes/programme-4-7.md) and
[`notes/two-sided-structure.md`](notes/two-sided-structure.md).

## Structure of the proof

1. **Theorem 1.3 (determinant sums).**  This is cancellation in
   `Σ_{be−ad=2} μ(d)μ(e) W(...)` on `8 min(x,y) + 9 max(x,y) > 8`, with power
   saving `(8m + 9M − 8)/12` off the zero frequency.  It uses a mean-value
   theorem (Theorem 6.1) built from:
   * the Heath-Brown identity;
   * a Korolev–Changa inequality averaged over moduli;
   * the Bloom–Maynard rational-energy bound;
   * Weil's bound.
2. **Theorem 1.2 (level of distribution).**  For `K, L ≤ N^θ` with
   `θ < 9/17`, the box sums `Σ_{d≤K, e≤L} μ(d)μ(e) r_N(d,e)` are
   `≪ N^{1−δ}`.  Here `r_N(d,e) = #{n ≤ N : d | n, e | n+2} − N ϱ(d,e)`.
   The proof is Poisson summation in `n` modulo `[d,e]`, a parity and
   orientation reduction, and then Theorem 6.1 (paper §8).
3. **Theorem 1.1 (Λ_R correlations).**  Deduced from Theorem 1.2 and the
   prime number theorem for μ by an exact expansion, Abel summation, and the
   main-term evaluation `M(R) = 𝔖 + O(exp(−c√log R))` (paper §9).

## Lean formalization (`lean/`)

Theorems 1.1 and 1.3 and Corollary 1.4 are formalized in Lean 4 with
Mathlib, **with no hypotheses**:

* `MobiusDeterminant.lambdaR_twin_correlation_unconditional` (Theorem 1.1);
* `MobiusDeterminant.Determinant.detSum_sub_zeroMode`, `zeroModeBound` and
  `detSum_cancellation` (Theorem 1.3);
* `MobiusDeterminant.Determinant.detSum_diagonal` (Corollary 1.4).

`#print axioms` reports only Lean's three standard axioms, and there is no
`sorry` anywhere.  The project is about 19.9k lines.

It covers:

* the determinant sums (Theorem 1.3), with the exact saving
  `(8m + 9M − 8)/12`;
* the level of distribution (Theorem 1.2);
* the mean-value theorem (Theorem 6.1);
* Bloom–Maynard's energy bound;
* the prime number theorem for μ with classical error term;
* the deduction of Theorem 1.1;
* every exponent computation in §§1–9 of the paper (`Exponents.lean`);
* the exponent arithmetic and the elementary identities of §10
  (`Barrier.lean`).  The analytic estimates quoted in §10 are **not**
  formalized.

It reuses Lean Pool (the Weil bound for Kloosterman sums, the divisor
bound) and PNT+ (the zero-free region of ζ and its Mellin–Perron
machinery).  See [`lean/README.md`](lean/README.md) for the file map and
the trust boundary.

## Repository layout

| Path | Contents |
|---|---|
| `paper/main.tex` | The manuscript (amsart) |
| `paper/Makefile` | `make` builds `main.pdf` with `latexmk` |
| `lean/` | Lean 4 project (Lean v4.35.0, Mathlib `56a00585`; depends on Lean Pool and PNT+) |
| `notes/` | Working notes on the 4/7 barrier and the two numerical experiments (`notes/lab/`) |
| `AI_DISCLOSURE.md` | How AI was used, by whom, and what is unverified |
| `ROADMAP.md` | Verification checklist and open items |

## Building

```sh
cd paper && make                  # needs a TeX distribution with latexmk
cd lean && lake exe cache get && lake build
```

The LaTeX source passes a structural check but has not yet been compiled,
because no TeX distribution was available when it was drafted.

## External inputs

The paper relies on the following published results:

* the Weil–Estermann bound for Kloosterman sums;
* the prime number theorem for μ with classical error term;
* Bloom–Maynard, *A new upper bound for sets with no square differences*,
  Theorem 2.

The Korolev–Changa inequality and the Heath-Brown identity are proved in
the paper, and also in Lean.

## Provenance

The determinant-sum estimate was extracted from an exploratory,
AI-generated research notebook in the investigator's `twin-primes`
repository.  The main source notes are in its `research/` folder:

* `2026-08-15-direct-bettin-chandee-refinement.md`
* `2026-08-26-averaged-reciprocal-energy-endpoint.md`
* `2026-08-26-joint-mode-rational-energy-boundary.md`
* `2026-08-26-joint-mode-compression-hostile-audit.md`

The manuscript follows a shorter route than the notebook.  The following
parts are new in this write-up and are the highest priority for checking:

* the direct-route reorganization;
* the level-of-distribution theorem;
* the Λ_R deduction.

See §12.3 of the paper.  Section 10 (the barrier) was written in this
repository on 2026-11-15 and is not derived from the notebook.
