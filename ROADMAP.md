# Roadmap

## 1. Verify the manuscript (highest priority)

- [ ] First build of `paper/main.tex`; fix typesetting issues.
- [ ] Expert check of Theorem 6.1 (mean-value theorem), especially:
  - [ ] gcd strata `g = (h, e)` and the `g^{-5/4}` decay (Step 1);
  - [ ] the Heath-Brown dichotomy and atom bookkeeping (Step 2);
  - [ ] the `g' = (a, u)` stratification, which replaces the notebook's
    divisor projector (Step 3);
  - [ ] the four-case bound for `Φ(U)` (Step 3);
  - [ ] the long-box bound via Lemma 2.4 (Step 4).
- [ ] Expert check of §7: the CRT phase, the zero mode, the separation of
  variables, and the exponent arithmetic.
- [ ] Check that Lemma 4.3 matches the hypotheses of Bloom–Maynard
  Theorem 2 (sets in `[0,1]`, exact denominators, energy in `Q`).
- [ ] Independently recompute the Bettin–Chandee comparison region
  (Remark 1.3), or remove it.

## 2. Literature

- [ ] Confirm bibliographic details; add page numbers.
- [ ] Search for prior results on Möbius cancellation along `be − ad = h`
  beyond `√X`, and on modulus-averaged Korolev–Changa estimates (e.g.
  Irving; Shparlinski; Kerr–Shparlinski–Wu–Xi).
- [ ] Check the novelty claims in §1.2 of the paper ("Why this matters"):
  - [ ] that Bloom–Maynard has not previously been used for Kloosterman
    fractions;
  - [ ] the 1/66 versus 1/34 comparison;
  - [ ] the description of Walker's applications;
  - [ ] that fixed-shift results past `θ = 1/2` use only general-coefficient
    bounds.
- [ ] Confirm the state of the art for `Σ Λ_R(n) Λ_R(n+2)` beyond
  `R = N^{1/2}` (Coppola–Laporta, Walker, anything newer).

## 3. Possible headline application (not yet proved)

The diagonal case suggests an asymptotic for `Σ_{n≤N} Λ_R(n) Λ_R(n+2)` with
`R = N^θ`, `θ < 9/17`.  This needs:

- [ ] boxes with one of `d, e` below `√N` but `de > N` (outside the hard
  square), probably via Bombieri–Vinogradov for μ;
- [ ] the non-smooth cutoff `log(R/d)` at `d = R`;
- [ ] the main-term computation.

## 4. Lean 4 formalization (staged)

Mathlib, as of its 2026-10 snapshot, lacks Kloosterman sums and the Weil
bound, the Vaughan and Heath-Brown identities, zero-free regions, and
`τ(n) ≪ n^ε`.  Plan:

1. **Elementary core, Mathlib only.**
   * Korolev–Changa inequality (Lemma 3.1);
   * reciprocal-energy lemmas (Lemmas 4.1 and 4.3), with Bloom–Maynard as
     an explicit hypothesis;
   * Heath-Brown identity (Lemma 2.6);
   * the CRT phase identity;
   * the `Φ(U)` case analysis and the exponent ledger.
2. **Conditional main theorem.**  Prove Theorem 1.1 assuming, as explicit
   `Prop` hypotheses: Weil–Estermann, the prime number theorem for μ with
   error term, the divisor bound, and Bloom–Maynard.  Axiom released its
   bounded-gaps formalization in the same conditional way, assuming
   Bombieri–Vinogradov.
3. **Discharge the hypotheses.**
   * Divisor bound: elementary.
   * Weil: port from `charliedorsey/weil-bounds-toolkit` or LeanPool PR #774.
     Our moduli can be taken squarefree.
   * μ-PNT: from PrimeNumberTheoremAnd or Math Inc's `strongpnt`.
   * Bloom–Maynard: new formalization, a substantial standalone project.

   Each external repository must be built and audited with `#print axioms`
   before use.
