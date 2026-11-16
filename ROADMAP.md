# Roadmap

## 0. Novelty (blocking: resolve before circulating)

The literature check of 2026-11-15 (paper §1.1, §1.4, Remark 1.5) found
that the headline exponent 9/17 is probably not the best one available.

- [ ] Check the transposition of Irving's estimate (Funct. Approx. 2014,
  Theorem 1.3) from Λ to μ.  The bilinear lemmas take arbitrary coefficients
  and the theorem uses only Vaughan's identity.  Inserted frequency by
  frequency, it appears to give Theorems 1.1–1.2 for **θ < 8/15**, and
  Theorem 1.3 on `11m + 4M > 7, 4m + 7M > 5`.  The latter is larger than Ω
  on the diagonal and smaller near `M = 1/2`.
- [ ] Check whether Conrey's mollifier method (Crelle 1989; see Pratt–Robles
  2018) transposes to the fixed shift, which would give **θ < 4/7**.
  Partly checked against the Pratt–Robles source (§3.2.6).  Their trilinear
  form is `Σ_a ν(a) Σ_{u,v} (μ-type)(u) r(v) e(−a ū/v)`, with `ν, r`
  arbitrary and `A ≍ UV/T`.  That is our form after Poisson summation, with
  `H = DE/N`.  The Deshouillers–Iwaniec lemma used for Type II sums takes
  arbitrary coefficients `c(a,n)` inside and absolute values over the
  modulus.  Transposed, this gives Theorem 1.2 with error
  `≪ N^ε(R^{7/4} + N^{1/2}R^{7/8})`, i.e. θ < 4/7.
- [ ] Find out how Balasubramanian–Conrey–Heath-Brown (Crelle 1985) reach
  9/17 for mollifier coefficients in the analogous problem.
- [ ] Decide how to reposition the paper.  Options:
  * restate at the best exponent and credit the method;
  * centre the paper on what is new: the Bloom–Maynard / averaged
    Korolev–Changa mechanism, the part of Ω near `M = 1/2`, and the
    formalization;
  * treat the work as a formalization paper.

## 1. Verify the manuscript

- [ ] First build of `paper/main.tex`; fix typesetting issues.
- [ ] Expert check of Theorem 6.1 (mean-value theorem):
  - [ ] gcd strata `g = (h, e)` and the `g^{-5/4}` decay (Step 1);
  - [ ] the Heath-Brown dichotomy and atom bookkeeping (Step 2);
  - [ ] the `g' = (a, u)` stratification, which replaces the notebook's
    divisor projector (Step 3);
  - [ ] the long-box bound via Lemma 2.4 (Step 4).
- [ ] Expert check of §7: the zero mode, the separation of variables.
  (§7.3 now states the hypotheses of Lemma 2.5 explicitly, after a reviewer
  query.)
- [ ] Expert check of §8:
  - [ ] Poisson summation in `n` and the four parity cases;
  - [ ] the reciprocity swap;
  - [ ] the smoothing in the proof of Theorem 1.2, including the choice of
    `δ'` against `k(η)`.
- [ ] Expert check of §9: Lemmas 9.4–9.6 and Proposition 9.3.  These are
  also machine-checked from `PNTMobius`, so the check is mainly that the
  Lean definitions match the paper.
- [ ] Check that Lemma 4.3 matches the hypotheses of Bloom–Maynard
  Theorem 2.  The arXiv v2 statement has been checked; the published
  Compositio wording has not.
- [x] Bettin–Chandee display and the 17/33 region: checked against the
  arXiv source; derivation in Appendix A; exponents machine-checked.
- [x] Coppola–Laporta 48/95: checked against the arXiv source.

## 2. Literature

- [x] Search for prior results (2026-11-15, AI research agent; see
  `AI_DISCLOSURE.md`).  Added: BCHB85, Con89, BCR17, PR18, DI82, FS11,
  Irv14, FR22, Kor18, Guria.  The description of Walker is corrected (he
  proves a fixed-shift asymptotic, nontrivial to `27/53`), and so is the
  Appendix A attribution (BCR, not BC).  Lemmas 3.1 and 4.1 are now
  attributed to Korolev (2018) and Irving (2014, Lemma 2.3).
- [x] Bibliographic data checked against Crossref / MathSciNet reference
  matching (by the agent).
- [ ] Human check of the literature claims and bibliography.
- [ ] Optional: Wright (arXiv:2604.25177, 2608.27732), special-case
  improvements of Bettin–Chandee that may affect Appendix A.

## 3. Lean formalization

Done.  `lambdaR_twin_correlation_unconditional` (Theorem 1.1) and
`Determinant.detSum_sub_zeroMode`, `zeroModeBound`, `detSum_cancellation`
and `detSum_diagonal` (Theorem 1.3, Corollary 1.4) have no hypotheses.  They
use only the standard axioms, and there is no `sorry`.  Remaining items:

- [ ] Human review that `lean/MobiusDeterminant/Basic.lean` and
  `lean/MobiusDeterminant/Determinant/Defs.lean` match the paper's
  definitions of Λ_R, 𝔖, S_κ, S_κ⁰, Ω and σ.
- [ ] Optional: upstream the new general-purpose pieces:
  * the prime number theorem for μ with classical error term (to PNT+);
  * Bloom–Maynard's energy bound;
  * the Korolev–Changa inequality;
  * four-variable Mellin separation.
