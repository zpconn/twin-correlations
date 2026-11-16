# AI usage disclosure

This project was produced with extensive use of generative AI.  This file
records how, so that the work can be disclosed accurately under journal and
preprint-server policies.  Most journals require disclosing AI use in the
methods or acknowledgments, and do not allow AI systems to be listed as
authors.

## Roles

* **Investigator: Zach Conn.**  Directed the research, chose what to extract,
  and is the responsible human party for this repository and manuscript.
* **AI systems.**  Generated the mathematics and drafted the text, as
  described below.  They are not authors.

## What AI did

1. **Upstream research (exploratory notebook, August 2026).**  The
   determinant-sum estimate, the reduction, the key lemmas, and their first
   proofs were produced by AI research agents in the investigator's
   `twin-primes` notebook.
   *Investigator to confirm the exact tools.*  Repository metadata indicates
   OpenAI ChatGPT produced the initial handoff reports.  An AI coding agent,
   apparently OpenAI Codex, produced the notebook.

2. **This manuscript and formalization (14–15 November 2026).**  Drafted by
   **Claude Opus 5.5 (Anthropic)** running in Claude Code, at the
   investigator's request.  This included:
   * surveying the notebook (about 380 notes) and choosing this result as the
     most significant standalone candidate;
   * reorganizing the proof into a shorter direct route (Poisson in `a`, one
     Cauchy–Schwarz over `e`, a single mean-value theorem), including
     simplifications not present in the notebook (see §11.3 of the paper);
   * Sections 8 and 9 of the paper: the level-of-distribution theorem and the
     Λ_R deduction, which are new in this manuscript;
   * Appendix A, the Bettin–Chandee comparison, checked against the arXiv
     source;
   * writing every lemma statement and proof as they appear in `paper/main.tex`;
   * the Lean 4 formalization in `lean/`, written by Claude Opus 5.5 instances
     and checked by the Lean kernel.  It reuses Lean Pool and PNT+; Lean Pool's
     Kloosterman–Weil development itself records substantial generative-AI
     contribution;
   * the literature search and bibliography.  On 15 November 2026 a
     Claude Opus 5.5 research agent ran a second literature check.  It read
     the arXiv sources of Walker, Irving, Bettin–Chandee–Radziwiłł,
     Pratt–Robles and Fouvry–Radziwiłł, and checked the bibliography against
     Crossref and MathSciNet reference matching.  It found the prior work now
     discussed in §1.1 and Remark 1.5 of the paper.  The transposition of
     Irving's estimate to μ is an AI computation and has not been checked by
     a human;
   * this repository's README, roadmap, and this disclosure.

   Independent AI reviewer instances (Claude subagents) audited parts of the
   notebook and re-derived the central exponent computation.

3. **The barrier programme and the repositioning (15 November 2026).**
   Carried out by **Claude Fable 5.2 (Anthropic)** running in Claude Code,
   at the investigator's request.  (The session changed model on
   15 November; the work in item 2 is Opus 5.5, the work here is
   Fable 5.2.)  This included:
   * the two-sided decomposition and the reduction of the problem past
     level 4/7 to one estimate (`notes/two-sided-structure.md`);
   * the attempt to pass 4/7, its equivalent reformulations, the no-go
     count, and the list of failed routes (`notes/programme-4-7.md`);
   * two numerical experiments (`notes/lab/var_nu.c`, `notes/lab/rls.c`);
   * reading, from arXiv sources, of Polymath8a, Fouvry–Kowalski–Michel,
     Bettin–Bui–Li–Radziwiłł, Buttcane, Maynard, Pascadi,
     Grimmelt–Merikoski (two papers) and Lau;
   * Section 10 of the paper, which packages all of the above;
   * `lean/MobiusDeterminant/Barrier.lean`, which checks the arithmetic and
     elementary identities of Section 10;
   * rewriting the abstract, introduction, README and roadmap so that the
     paper presents itself as a formalization and synthesis.  The
     investigator decided on that positioning.

## Verification status

* **No human expert has verified the proof.**
* AI cross-checks are not a substitute for expert refereeing: they share
  failure modes with the system that wrote the argument.
* Numerical computations in the upstream notebook are finite sanity checks.
  They are not part of the proof.
* The LaTeX source has passed a structural check but has **not been
  compiled**.
* The Lean kernel checks Theorems 1.1 and 1.3 and Corollary 1.4 with no
  hypotheses.  The proofs cover Theorems 1.2 and 6.1, Bloom–Maynard, and the
  prime number theorem for μ, and use only the standard axioms.  The kernel
  does **not** check two things:
  * that the definitions in `lean/MobiusDeterminant/Basic.lean` and
    `lean/MobiusDeterminant/Determinant/Defs.lean` match the mathematics;
  * the prose proofs in the paper.

  Appendix A and the comparisons with the literature are not formalized.
* **Section 10 of the paper has a different status from the rest.**  Its
  statements labelled *Claim* are exponent computations by AI, obtained by
  inserting published estimates into reductions.  No human has checked
  them, they are not formalized, and the hypotheses of the cited estimates
  were not verified in detail.  This includes the statement that known
  methods give level 4/7, which is the bar the paper measures itself
  against.  `Barrier.lean` checks only arithmetic and elementary
  identities.
* The numerical experiments in Section 10 are finite computations (L up to
  256) by programs that no one has reviewed.  They are not part of any
  proof.
* The exponent 9/17 is not claimed as a record.  The paper says so; see
  `ROADMAP.md` §0.
* Bibliographic data and every statement attributed to the literature were
  assembled with AI assistance.  They must be checked against the sources.
  In particular:
  * the bibliographic data of the references added for Section 10, which
    were taken from arXiv listings and from the model's memory of the
    published versions;
  * the exact statement of Bloom–Maynard Theorem 2;
  * the Korolev–Changa citation;
  * the description of Walker's applications.

  The Bettin–Chandee bound and the Coppola–Laporta exponent 48/95 have been
  checked against the authors' arXiv sources.

## Before any submission or circulation

* A human expert in analytic number theory should check every step,
  especially Sections 6–8 (the mean-value theorem, the determinant estimate,
  and the level of distribution).
* A human expert should check the Claims of Section 10 before the paper's
  comparison with the literature is relied on.
* Fill in tool names in item 1 above and in the paper's disclosure section.
* Add affiliation and contact details to `paper/main.tex`.
* Keep the disclosure section in the paper, adapted to the target venue's
  policy.
