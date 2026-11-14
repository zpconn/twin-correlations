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

2. **This manuscript (14 November 2026).**  Drafted by **Claude Opus 5.5
   (Anthropic)** running in Claude Code, at the investigator's request.  This
   included:
   * surveying the notebook (about 380 notes) and choosing this result as the
     most significant standalone candidate;
   * reorganizing the proof into a shorter direct route (Poisson in `a`, one
     Cauchy–Schwarz over `e`, a single mean-value theorem), including
     simplifications not present in the notebook (see §8.3 of the paper);
   * writing every lemma statement and proof as they appear in `paper/main.tex`;
   * the literature search and bibliography;
   * this repository's README, roadmap, and this disclosure.

   Independent AI reviewer instances (Claude subagents) audited parts of the
   notebook and re-derived the central exponent computation.

## Verification status

* **No human expert has verified the proof.**
* AI cross-checks are not a substitute for expert refereeing: they share
  failure modes with the system that wrote the argument.
* Numerical computations in the upstream notebook are finite sanity checks.
  They are not part of the proof.
* The LaTeX source has passed a structural check but has **not been
  compiled**.
* Bibliographic data and every statement attributed to the literature were
  assembled with AI assistance.  They must be checked against the sources.
  In particular:
  * the exact statement of Bloom–Maynard Theorem 2;
  * the Korolev–Changa citation;
  * the Bettin–Chandee comparison region;
  * the exponents attributed to Coppola–Laporta and Walker.

## Before any submission or circulation

* A human expert in analytic number theory should check every step,
  especially Section 6 (the mean-value theorem) and Section 7.
* Fill in tool names in item 1 above and in the paper's disclosure section.
* Add affiliation and contact details to `paper/main.tex`.
* Keep the disclosure section in the paper, adapted to the target venue's
  policy.
