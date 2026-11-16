# Twin correlations of truncated von Mangoldt functions up to level 9/17

**Investigator:** Zach Conn

> **Status: draft, not yet verified by a human expert.**  The mathematics
> here was generated with extensive AI assistance.  See
> [`AI_DISCLOSURE.md`](AI_DISCLOSURE.md).

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

Past `1/2`, general bounds for Kloosterman fractions give:

* `48/95 = 1/2 + 1/190` (Coppola–Laporta, via Duke–Friedlander–Iwaniec);
* `17/33 = 1/2 + 1/66` (the Bettin–Chandee trilinear bound; see Appendix A
  of the paper).

Both figures were checked against the authors' arXiv sources.  This result
reaches `9/17 = 1/2 + 1/34` by exploiting the arithmetic of μ.  The parity
problem remains, and nothing here bears on the twin-prime conjecture itself.

> **Novelty caveat (2026-11-15).**  A literature check found that methods
> already in print probably give more.  Irving's 2014 bound for Kloosterman
> sums over primes, transposed to μ, appears to give θ < 8/15.  Conrey's 1989
> mollifier method may give θ < 4/7.  In the analogous twisted-moment
> problem, Balasubramanian–Conrey–Heath-Brown reached 9/17 in 1985.  See
> [`ROADMAP.md`](ROADMAP.md) §0; this must be resolved before circulation.

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
`sorry` anywhere.  The project is about 19.5k lines.

It covers:

* the determinant sums (Theorem 1.3), with the exact saving
  `(8m + 9M − 8)/12`;
* the level of distribution (Theorem 1.2);
* the mean-value theorem (Theorem 6.1);
* Bloom–Maynard's energy bound;
* the prime number theorem for μ with classical error term;
* the deduction of Theorem 1.1;
* every exponent computation in the paper.

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

See §11.3 of the paper.
