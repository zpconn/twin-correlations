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

Done.  `lambdaR_twin_correlation_unconditional` (Theorem 1.1) has no
hypotheses: only the standard axioms, and no `sorry`.  Remaining items:

- [ ] Human review that `lean/MobiusDeterminant/Basic.lean` matches the
  paper's definitions of Λ_R and 𝔖.
- [ ] Optional: formalize the determinant form, Theorem 1.3, separately.
- [ ] Optional: upstream the new general-purpose pieces:
  * the prime number theorem for μ with classical error term (to PNT+);
  * Bloom–Maynard's energy bound;
  * the Korolev–Changa inequality.
