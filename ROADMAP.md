# Roadmap

## 1. Verify the manuscript (highest priority)

- [ ] First build of `paper/main.tex`; fix typesetting issues.
- [ ] Expert check of Theorem 6.1 (mean-value theorem):
  - [ ] gcd strata `g = (h, e)` and the `g^{-5/4}` decay (Step 1);
  - [ ] the Heath-Brown dichotomy and atom bookkeeping (Step 2);
  - [ ] the `g' = (a, u)` stratification, which replaces the notebook's
    divisor projector (Step 3);
  - [ ] the long-box bound via Lemma 2.4 (Step 4).
- [ ] Expert check of §7: the zero mode, the separation of variables.
- [ ] Expert check of §8:
  - [ ] Poisson summation in `n` and the four parity cases;
  - [ ] the reciprocity swap;
  - [ ] the smoothing in the proof of Theorem 1.2, including the choice of
    `δ'` against `k(η)`.
- [ ] Expert check of §9: Lemmas 9.4–9.6 and Proposition 9.3.  These are
  also machine-checked from `PNTMobius`, so the check is mainly that the
  Lean definitions match the paper.
- [ ] Check that Lemma 4.3 matches the hypotheses of Bloom–Maynard
  Theorem 2 (sets in `[0,1]`, exact denominators, energy in `Q`).
- [x] Bettin–Chandee display and the 17/33 region: checked against the
  arXiv source; derivation in Appendix A; exponents machine-checked.
- [x] Coppola–Laporta 48/95: checked against the arXiv source.

## 2. Literature

- [ ] Confirm bibliographic details; add page numbers.
- [ ] Search for prior results on Möbius cancellation along `be − ad = h`
  beyond `√X`, on Λ_R correlations beyond `N^{1/2}` (anything newer than
  Coppola–Laporta and Walker), and on modulus-averaged Korolev–Changa
  estimates (e.g. Irving; Shparlinski; Kerr–Shparlinski–Wu–Xi).
- [ ] Confirm the claims in §1.4 of the paper ("Why this matters"):
  - [ ] that Bloom–Maynard has not previously been used for Kloosterman
    fractions;
  - [ ] that fixed-shift results past `θ = 1/2` use only general-coefficient
    bounds.

## 3. Lean formalization

Done (no `sorry`; only the standard axioms):

- [x] The Λ_R deduction, from `MobiusPairLevel θ` and `PNTMobius`:
  `lambdaR_twin_correlation`.
- [x] Exponent ledger (`Exponents.lean`).
- [x] Korolev–Changa, Heath-Brown, CRT phase, and energy counting (`Core/`).

Next:

- [ ] Human review that `Basic.lean` matches the paper's definitions.
- [ ] Discharge `PNTMobius`, e.g. from PrimeNumberTheoremAnd or Math Inc's
  `strongpnt`.  Each external repository must be built and audited with
  `#print axioms`.
- [ ] Formalize Theorem 1.2 itself.  It needs:
  * Poisson summation with decay for smooth weights;
  * separation of variables;
  * the divisor bound `τ(n) ≪ n^ε`;
  * Weil's bound (port from `charliedorsey/weil-bounds-toolkit` or LeanPool
    PR #774; squarefree moduli suffice);
  * Bloom–Maynard Theorem 2, a substantial standalone project.

  Until then, Theorem 1.2 stays an explicit hypothesis.
