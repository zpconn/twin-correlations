# Roadmap

## 0. Positioning (decided 2026-11-15)

The literature check of 2026-11-15 found that 9/17 is not the best exponent
available, and an attempt to pass the literature bar of 4/7 did not
succeed.  The investigator's decision: the paper presents its primary
contribution as **formalization and synthesis**.  The paper, README and
disclosure now say so (paper abstract, §1.1 "Status of the exponent", §1.2,
§10).

Still open under this heading:

- [ ] Human check of the transposition of Irving's estimate (Funct. Approx.
  2014, Theorem 1.3) from Λ to μ: θ < 8/15, and Theorem 1.3 on
  `11m + 4M > 7, 4m + 7M > 5` (paper, Remark 1.5).
- [ ] Human check of the transposition of Conrey's method (Crelle 1989;
  Pratt–Robles 2018, §3.2.6) to a fixed shift: Theorem 1.2 with error
  `≪ N^ε(R^{7/4} + N^{1/2}R^{7/8})`, i.e. θ < 4/7 (paper, Claim 10.2).
  This is the bar the paper cites; it matters that it is right.
- [ ] Find out how Balasubramanian–Conrey–Heath-Brown (Crelle 1985) reach
  9/17 for mollifier coefficients in the analogous problem.
- [ ] Decide whether the title should keep "up to level 9/17".  A subtitle
  ("a formalized proof and the barrier at 4/7") was added on 2026-11-15.

## 0a. The barrier at 4/7 (paper §10)

Everything in §10 labelled *Claim* is an AI exponent computation.

- [ ] Human check of Claims 10.2, 10.3, 10.5, 10.6 and 10.9.
- [ ] Check the two secondary uncovered pieces (the mixed d₃ × d₂ problem
  and the quadratic divisor problem with coefficients N^{1/7}); the paper
  says they have not been examined.
- [ ] Claim 10.5, unconditional part: level 3/5 for twin correlations of
  well-factorable weights.  If it survives a detailed check it is a result
  beyond the 4/7 bar for a restricted class of weights, and would be the
  most direct route to a statement that exceeds the literature.
- [ ] Open questions 1–3 of paper §10.7 (the mean-square inequality (LS);
  whether the Grimmelt–Merikoski symmetric-matrix argument admits an
  average over h with d = h; the pair-correlation form on average over q).
- [ ] Rerun the experiments at larger L or with independent code
  (`notes/lab/`).

## 1. Verify the manuscript

- [ ] First build of `paper/main.tex`; fix typesetting issues.  Still not
  compiled as of 2026-11-15 (no TeX distribution available); §10 was added
  under the same structural check only.
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

Done for Theorems 1.1–1.3.  `Barrier.lean` (2026-11-15) adds the exponent
arithmetic and elementary identities of paper §10; none of the analytic
estimates quoted in §10 is formalized.  `lambdaR_twin_correlation_unconditional` (Theorem 1.1) and
`Determinant.detSum_sub_zeroMode`, `zeroModeBound`, `detSum_cancellation`
and `detSum_diagonal` (Theorem 1.3, Corollary 1.4) have no hypotheses.  They
use only the standard axioms, and there is no `sorry`.  Remaining items:

- [ ] Human review that `lean/MobiusDeterminant/Basic.lean` and
  `lean/MobiusDeterminant/Determinant/Defs.lean` match the paper's
  definitions of Λ_R, 𝔖, S_κ, S_κ⁰, Ω and σ.
- [ ] Long term: formalize Kuznetsov's formula and the
  Deshouillers–Iwaniec large sieve.  That would bring the 4/7 bar itself
  (Claim 10.2) within reach of machine checking.
- [ ] Optional: upstream the new general-purpose pieces:
  * the prime number theorem for μ with classical error term (to PNT+);
  * Bloom–Maynard's energy bound;
  * the Korolev–Changa inequality;
  * four-variable Mellin separation.
