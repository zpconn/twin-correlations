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

* **It is a two-point Möbius correlation averaged over dilations.**  With
  `n = ad`, the sum is the correlation of `μ(n/a)` with `μ((n+2)/b)`,
  averaged over `a ~ A` and `b ~ B`.  The family interpolates between two
  classical cases:
  * when `AB > X^{1+ε}`, the Chinese remainder theorem suffices;
  * at `A = B = 1`, it is essentially the binary Chowla correlation
    `Σ μ(n)μ(n+2)`, which is open.

  The theorem extends the range where cancellation is proved from the
  Chinese-remainder corner into the hard square.
* **It goes beyond the square-root barrier.**  Here the problem needs
  Kloosterman-fraction input, as passing level 1/2 does in
  Bombieri–Friedlander–Iwaniec.  The general-coefficient Bettin–Chandee
  bound reaches `d, e ≤ X^{1/2 + 1/66}`, a figure that still needs
  rechecking.  This result reaches `X^{1/2 + 1/34}`, which roughly doubles
  the excess.
* **It uses the arithmetic of μ.**  General trilinear bounds cannot see the
  Möbius coefficients.  Here three ingredients do:
  * the Heath-Brown identity;
  * a modulus-averaged Korolev–Changa inequality;
  * the Bloom–Maynard rational-energy theorem, which to our knowledge is
    new in this setting.
* **It has possible applications, not yet established.**  Correlations of
  `Λ_R` beyond `R = N^{1/2}` (the Goldston–Yıldırım / GPY setting), and
  conditional results on primes in short intervals and on zeta-zero pair
  correlation (Walker).  See `ROADMAP.md` §3.
* **Limits.**  The region is a neighbourhood of the corner `x = y = 1/2`.
  The result says nothing directly about twin primes or Chowla.

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

The manuscript follows a shorter route than the notebook; see §8.3 of the
paper.  The streamlining steps are new in this write-up and are the highest
priority for checking.

No claim is made about the twin-prime conjecture.
