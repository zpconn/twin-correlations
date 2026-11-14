# Möbius cancellation on the determinant equation `be − ad = 2`

**Investigator:** Zach Conn

> **Status: draft, not yet verified by a human expert.**  The mathematics
> here was generated with extensive AI assistance.  See
> [`AI_DISCLOSURE.md`](AI_DISCLOSURE.md).

## The result

For a fixed smooth weight `W` supported in `[1,2]^4`, odd integers
`a, b, d, e`, and `AD = BE = X`, consider

```
S = Σ_{be − ad = ±2}  μ(d) μ(e)  W(a/A, b/B, d/D, e/E).
```

Write `A = X^x`, `B = X^y` with `0 < x, y ≤ 1/2`.  This is the range where
both Möbius variables exceed `√X`, beyond the reach of the Chinese remainder
theorem.  Put `m = min(x, y)` and `M = max(x, y)`.

**Theorem.** On every compact subset of the region `8m + 9M > 8`:

* `S = S⁰ + O(X^{1 − σ + ε})` with `σ = (8m + 9M − 8)/12`, where `S⁰` is
  an explicit zero-frequency term;
* `S⁰ ≪ X exp(−c √log X)`, and hence `S ≪ X exp(−c √log X)`.

On the diagonal `x = y` the region allows `d, e ≤ X^{9/17 − ε}`.  The same
reduction combined with the Bettin–Chandee trilinear Kloosterman-fraction
bound reaches `X^{17/33 − ε}`; that comparison still needs rechecking.

The proof uses:

1. Poisson summation in `a` modulo `2e`;
2. a single Cauchy–Schwarz step over `e`;
3. a new-in-form mean-value theorem for Möbius–Kloosterman fractions
   averaged over moduli, proved by:
   * the Heath-Brown identity;
   * a Korolev–Changa bilinear inequality applied *before* pointwise energy
     bounds, with energies averaged over the modulus;
   * the Bloom–Maynard theorem on additive energy of rationals with bounded
     denominators;
   * Weil's bound, for boxes with a long smooth variable.

## Why it matters

The twin-prime conjecture is the asymptotic `Σ_{n≤N} Λ(n)Λ(n+2) ~ 𝔖N`.  A
standard model replaces `Λ` by the truncated divisor sum

```
Λ_R(n) = Σ_{d | n, d ≤ R} μ(d) log(R/d),
```

and `Λ_N = Λ` on `(1, N]`.  So the level `R = N^θ` is a dial on the
correlation `Σ Λ_R(n)Λ_R(n+2)`:

* **θ ≤ 1/2:** classical; the Chinese remainder theorem suffices.
* **θ = 1:** the twin-prime conjecture.
* **θ > 1/2:** the only new difficulty is exactly the determinant sums
  above, with `de > N`.

Fixed-shift results past `θ = 1/2` treat μ as an arbitrary bounded sequence
and apply general Kloosterman-fraction bounds.  These move the dial only a
little:

* `1/2 + 1/190` (Coppola–Laporta, via Duke–Friedlander–Iwaniec);
* `1/2 + 1/66` for these sums via Bettin–Chandee.

Both figures still need checking.

**What is new:** using the structure of μ, the theorem reaches `1/2 + 1/34`
for these sums, roughly twice the excess.  It does so through a mean-value
theorem with Heath-Brown, modulus-averaged Korolev–Changa, and Bloom–Maynard
as ingredients, which may be useful elsewhere.  Such correlations feed into
Goldston–Yıldırım and GPY-type arguments, and into conditional results on
primes in short intervals and zeta-zero pair correlation (Walker).

**What it does not do (yet):**

* The `Λ_R` asymptotic for `θ < 9/17` needs further steps not yet carried
  out (`ROADMAP.md` §3).  Until then, the contribution is the estimate and
  the method.
* It does not bring twin primes qualitatively closer: the parity problem
  remains, and the dial moves from 0.5 to about 0.53.

## Repository layout

| Path | Contents |
|---|---|
| `paper/main.tex` | Self-contained LaTeX manuscript (amsart) |
| `paper/Makefile` | `make` builds `main.pdf` with `latexmk` |
| `AI_DISCLOSURE.md` | How AI was used, by whom, and what is unverified |
| `ROADMAP.md` | Verification checklist, open items, and Lean formalization plan |

## Building

```sh
cd paper && make        # requires a TeX distribution with latexmk
```

The source has not yet been compiled: no TeX distribution was available
when it was drafted.  It passed a structural check (balanced braces and
environments, all references and citations resolved), but expect to fix
minor typesetting issues on first build.

## External inputs

The proof relies on these published results, which are not reproved here:

* the Weil–Estermann bound for Kloosterman sums;
* the prime number theorem for μ with classical error term;
* Bloom–Maynard, *A new upper bound for sets with no square differences*,
  Theorem 2.

The Korolev–Changa inequality, the Heath-Brown identity, and all energy
lemmas are proved in the manuscript.

## Provenance

The result was extracted from an exploratory, AI-generated research notebook
in the investigator's `twin-primes` repository.  The main source notes are:

* `research/2026-08-15-direct-bettin-chandee-refinement.md` (setup, Poisson reduction, Bettin–Chandee region)
* `research/2026-08-26-averaged-reciprocal-energy-endpoint.md` (modulus-averaged Korolev–Changa argument)
* `research/2026-08-26-joint-mode-rational-energy-boundary.md` (Bloom–Maynard step and the `8x+9y>8` chamber)
* `research/2026-08-26-joint-mode-compression-hostile-audit.md` (mask repair)
* `research/2026-08-15-selected-class-crt-spectrum.md` (zero-mode treatment)

The manuscript follows a shorter route than the notebook; see §8.4 of the
paper.  The streamlining steps are new in this write-up and are the highest
priority for checking.

No claim is made about the twin-prime conjecture.
