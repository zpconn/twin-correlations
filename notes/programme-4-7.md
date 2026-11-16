# Programme: past level 4/7 (started 2026-11-15)

Status: research in progress; AI exploration, nothing here is checked by a
human.  Background and dead ends: `two-sided-structure.md`.

## Chosen line

Treat the stuck estimate as a **quadratic divisor problem averaged over its
coefficients** (equivalently a fourth moment of zeta twisted by a long
*smooth* Dirichlet polynomial), and attack the one step where the
Deshouillers–Iwaniec method is lossy there.

## Target, in three equivalent forms

Units: L = x^{θ/2}, H = x^{2θ−1}, K = x^{1−3θ/2}.  At θ = 4/7: H = K = L^{1/2}.
All variables carry smooth dyadic weights.

(T) Count: #{b·ℓ₁ℓ₂ − a·n₁n₂ = 2}, a, b ~ x^{1−θ}, others ~ L, equals its
    main term up to a power saving.

(Q) Quadratic divisor form: for coefficients (ℓ₁, n₁) ~ L and unknowns
    X = bℓ₂, Y = an₂ ~ x^{1−θ/2} with box-divisor weights,
        D(ℓ₁, n₁) = Σ_{ℓ₁X − n₁Y = 2} τ(X) τ(Y),
    main term ≍ L^{3/2} at θ = 4/7.  The spectral method gives each
    D(ℓ₁, n₁) with error ≍ L^{7/4}, which is larger than the main term by
    L^{1/4}.  Needed: error ≪ L^{3/2−δ} on average over (ℓ₁, n₁).

(V) Variance form: for d ~ L², r ~ L let
        ν(d, r) = #{(a, b, s) : b·r·s − a·d = 2, s ~ L, a ~ x^{1−θ}}
                = Σ_{k ≤ K} τ_L(m₀ + k·d),
    where τ_L counts divisors in [L, 2L) and m₀ ≡ 2·inv(r) (mod d).
    Mean ≍ K.  Needed: Var_{(d,r)} ν ≪ K^{2−δ}.  Deshouillers–Iwaniec gives
    K^{2+ε} at θ = 4/7.  A Poisson model predicts ≍ K.
    In words: the divisor function in progressions mod d, at length
    d^{5/4}, has small variance over the thin set of classes
    {2·inv(r) : r ≤ √d}.  Over *all* classes this is classical
    (Motohashi, Blomer, Lau–Zhao).

## Dictionary with moments of zeta

(Q) is the shift-2 term of ∫|ζ|⁴|A|² with A a smooth Dirichlet polynomial of
length T^ϑ, ϑ = θ/(2−θ):

    θ = 1/2 ↔ ϑ = 1/3,   4/7 ↔ 2/5,   3/5 ↔ 3/7,   2/3 ↔ 1/2 (sixth moment).

So the stuck range sits strictly between the fourth and sixth moments.
For arbitrary coefficients the record is ϑ < 1/4 (Watt; BBLR).

## Checks done (2026-11-15)

* Watt's bound (form of BBLR Lemma 5.2 / BCR), applied directly with
  h = h, c = 1, r = n₁, v = n₂, s = ℓ₁, p = ℓ₂:
  saves (H·VP/(RS))^{1/2} = H^{1/2}.  Needed H^{1+δ}.
* BBLR Theorem 1.3 (arXiv:1609.02539), any assignment of our variables to
  its (a, b): the error contains x^{1/2}·AB, so it needs AB < x^{1/2}.
  Our options are AB = x^{2−2θ}, x^θ, x^{1−θ/2}: fine only for θ < 1/2 or
  θ > 3/4.

## Where the loss is

In the Cauchy–Schwarz arrangement, for each pair (s, s') the method bounds
⟨A, B⟩ over forms of level ss' by ‖A‖·‖B‖, where A_j = Σ_{m~L} ρ_j(m) and
B_j = Σ_{h,h'} ρ_j(hs' − h's).  Each norm is sharp.  Writing
⟨A, B⟩ = Σ_n b_n·G(n) with G(n) = Σ_{r,d} e(2n·inv(d)/(rss')):

(RLS) Restricted large sieve.  The set N(s,s') = {hs' − h's} is a Bohr set
      of density L^{−1/2} in [−HL, HL].  The method bounds
      Σ_{n ∈ N} |G(n)|² by the sum over *all* n.  A fair share would be
      smaller by L^{1/2}; any power of that suffices.

(RLS) for most (s, s') implies (V).

## Next steps

1. Numerical check of (V): distribution of ν(d, r), ratio Var/mean, scaling
   in L.
2. Numerical check of (RLS): share of Σ|G(n)|² carried by the Bohr set.
3. Expand 1_N in characters of modulus s; (RLS) becomes a bound for
   additively twisted second moments Σ_n e(nκ/s)|G(n)|², κ ≠ 0, i.e. a
   shifted pair-correlation statement for the fractions inv(d)/(rss').
   Decide whether Kuznetsov with the twist (cusp a/s of Γ₀(ss')) handles it.

## Log

### 2026-11-15, experiment 1: target (V) (`lab/var_nu.c`)

600 random odd d per run, all odd r coprime to d.  A = L^α; α = 1.5 is
θ = 4/7, smaller α is past the barrier.

| α   | L   | K    | mean ν | Var  | Var/mean | Var/K² |
|-----|-----|------|--------|------|----------|--------|
| 1.5 | 32  | 5.7  | 1.15   | 1.14 | 1.02     | 0.036  |
| 1.5 | 64  | 8.0  | 1.65   | 1.68 | 1.02     | 0.026  |
| 1.5 | 128 | 11.3 | 2.31   | 2.46 | 1.07     | 0.019  |
| 1.5 | 256 | 16.0 | 3.23   | 3.52 | 1.09     | 0.014  |
| 1.4 | 256 | 9.2  | 1.85   | 2.15 | 1.15     | 0.025  |
| 1.3 | 256 | 5.3  | 1.07   | 1.29 | 1.20     | 0.046  |

Reading: the variance is Poisson-sized (Var ≈ 1.0–1.2 × mean), on both
sides of the barrier.  (V) asks only for Var ≪ K^{2−δ}; the data sit at K¹.
This is a sanity check that the target is true with a wide margin.  It is
not evidence about provability.

### 2026-11-15: the core sum for one level

Fix q = ss' ~ L² and n = hs' − h's ~ q^{3/4}.  Everything reduces to

    K(n; q) = Σ_{c ~ √q} Σ_{k ~ q} e(n·inv(k)/(cq)),

smooth in c and k.  Sizes: trivial q^{3/2}; Weil in k, or Kuznetsov in c,
q^{5/4}; needed q^{1−δ} (on average over n in the Bohr set and over q);
square-root cancellation q^{3/4}.

Spectral form: K(n; q) = q^{1+…} · M₁(n), with

    M₁(n) = Σ_{f of level q} ω_f X^{2it_f} λ_f(n) · Σ_{m ~ √q} λ_f(m),

a first moment of central values twisted by λ_f(n), with an oscillating
spectral weight (X ≈ q^{−7/8}).  Trivial bound q^{1/4}; needed q^{−δ}.
Both sides of the Kuznetsov formula have ≍ q terms here: the transform is
self-dual at θ = 4/7.  Poisson in k, reciprocity, and a second Kuznetsov
(cusp pair (∞, 0)) each return the same sum, up to the Atkin–Lehner sign.

Open question that defines the next step: is there a *third* expression
for M₁(n) — a reciprocity formula in the sense of Motohashi or
Blomer–Khan — in which the family is smaller than q?

### 2026-11-15, experiment 2: target (RLS) (`lab/rls.c`)

For random coprime (s, s') ~ L the program builds the point set
Θ = {2·inv(d)/(rss') : r ~ L, d ~ L², gcd(d, rss') = 1}, with P points, and
computes G(n) = Σ_Θ e(nθ) for 1 ≤ n ≤ 4HL, H = ⌊√L⌋.  Square-root
cancellation is |G(n)|² ≈ P.  Columns are means of |G(n)|²/P.

| L   | pairs | all n | gcd(n,ss')=1 | Bohr set | Bohr, coprime | (Σ_Bohr Re G)²/(#N·P) |
|-----|-------|-------|--------------|----------|---------------|------------------------|
| 16  | 40    | 0.98  | 1.19         | 0.99     | 1.16          | 0.71                   |
| 32  | 40    | 0.96  | 1.11         | 0.91     | 1.02          | 0.63                   |
| 64  | 40    | 0.99  | 1.15         | 1.03     | 1.22          | 0.54                   |
| 128 | 16    | 0.99  | 1.14         | 1.03     | 1.15          | 1.06                   |
| 256 | 3     | 0.98  | 1.09         | 0.99     | 1.09          | 0.03                   |

Reading.
* G(n) has square-root size for essentially every n ≠ 0 in the range, on
  the Bohr set and off it.  The Bohr set is not special.
* The signed sum over the Bohr set is also of square-root size, but the
  target does not need that.

### 2026-11-15: consequence — one positive inequality at one level

Needed for (T): Σ_{n ∈ N(s,s'), n≠0} |G(n)|² ≪ L^{5−δ} for most (s, s').
Sizes of the *full* sum S(q) = Σ_{0<|n|≤L^{3/2}} |G(n)|², q = ss':

    Weil, termwise      L^{6.5}
    dual large sieve    L^{5+ε}     (Kuznetsov, then Bessel's inequality;
                                     my computation, exceptional spectrum
                                     not rechecked in this form)
    needed              L^{5−δ}
    truth (exp. 2)      L^{4.5}

Since the terms are non-negative, N ⊂ [−L^{3/2}, L^{3/2}] gives

    (LS)   S(q) ≪ L^{5−δ} for most q = ss'   ⟹   level > 4/7.

So the Bohr-set structure is not needed.  The barrier is the statement
that Bessel's inequality is not sharp for one explicit vector:

* Let v_n = (ρ_g(n))_g over an orthonormal basis of level q, and
  a = Σ_{m~√q} v_m.  For n ≤ q^{3/4} the v_n are almost orthonormal; let
  V be their span (dimension q^{3/4} inside dimension ≍ q).
* G(n) ∝ ⟨D_X a, v_n⟩, where D_X multiplies the g-th coordinate by
  X^{2it_g}, X ≈ q^{−7/8}.  So S(q) ∝ ‖Π_V D_X a‖².
* Bessel: ‖Π_V D_X a‖² ≤ ‖a‖².  This is the 4/7 bound.
  Generic position would give (q^{3/4}/q)·‖a‖², which is what is observed.
* (LS) ⟺ ‖Π_V D_X a‖² ≤ q^{−δ}‖a‖².

Geometric reading.  D_X is the wave propagator on Γ₀(q)\H at time
τ = 2 log(1/X) ≈ (7/4) log q.  The vector a is a unit-scale bump at the
Fricke point i/√q.  V is the space of the first q^{3/4} Fourier modes on
the closed horocycle of height q^{−3/4}.  (LS) says the propagated wave does
not concentrate on that horocycle.  At time τ the wavefront covers the
surface e^τ/q = q^{3/4} times; Weil's bound controls each sheet, and nothing
known controls interference between sheets.  (Heuristic picture, not
checked beyond the exponent count above.)

Equivalent arithmetic form of (LS): pair correlation of the fractions
inv(k)/(cq), c ~ √q, k ~ q, at scale q^{−3/4}, with relative error
q^{−1/2−δ}.  Number variance in arcs of that length: needed ≪ mean^{4/3−δ};
Poisson is observed.

### 2026-11-15: the estimate before Cauchy–Schwarz

Keeping the divisor structure on both sides (no Cauchy–Schwarz), Kuznetsov
in (r, n₁) at level q = s·n₂ with the cusp pair (∞, 1/s) gives

    W = Σ_{s,n₂} Σ_{f ∈ B(sn₂)} ω_f h_X(t_f) η_f(n₂) · L(½, f) · Σ_{h~q^{1/4}} λ_f(h),

η_f(n₂) = Atkin–Lehner eigenvalue.  The short sum over h is the dual half of
an unbalanced approximate functional equation, so this is a **second moment
of L(½, f) over level s·n₂, twisted by the partial Atkin–Lehner sign, with
oscillating weight X^{2it}**.  It is the spectral form of (Q).

* Trivial (second moment ≪ log q): the L^{7/4} error in (Q).
* Needed: saving q^{1/8+δ} on average over (s, n₂).
* If n₂ were absent from the level (n₂ = 1) the same argument would win by
  L^{1/4}.  The argument tolerates n₂ ≤ L^{1/2}; the problem has n₂ ~ L.
  The loss is the factor √n₂ in the normalization γ = rs√n₂ of the
  Kloosterman sums for the cusp pair (∞, 1/s).

### 2026-11-15: G(n) as a Weyl sum over roots of a quadratic congruence

a_g = Σ_{m~√q} ρ_g(m) is essentially the value of g at the Fricke point
z₁ = i/√q, so G(n) is a Poincaré series evaluated at z₁.  Explicitly, with
D = qc² + d² and ν ≡ c·inv(d) (mod D):

    inv(d)/(cq) ≡ ν/D + d/(qcD)   (mod 1),      qν² + 1 ≡ 0 (mod D),

and the correction d/(qcD) ≍ L^{−5} is negligible against n ≤ L^{3/2}.  So

    G(n) = Σ_{c~L, d~L²} e(2nν(c,d)/D(c,d)) · (1 + O(L^{−7/2})):

a Weyl sum over those roots of qν² + 1 ≡ 0 (mod D) that come from
representations of D ≍ q² by the principal form qc² + d², at frequencies
n ≍ D^{3/8}.  (LS) is a mean-square bound for these sums that is uniform
in the coefficient q up to D^{1/2}.  For a fixed polynomial this is Hooley
/ Duke–Friedlander–Iwaniec / Tóth; the uniformity in q is the content.

### 2026-11-15: literature check, Grimmelt–Merikoski

arXiv:2404.08502 (determinant equations with a periodic weight, uniform in
the modulus), read from source: Theorem 1.1 and the proof sketch.

* Method: Σ_τ α(τ)·P_f(τ) over orbits τ ∈ Γ\M, spectral expansion, then
  Cauchy–Schwarz between a Fourier-coefficient sum (R, bounded by the
  Deshouillers–Iwaniec large sieve) and a point-evaluation sum (K, computed
  by the pretrace formula).  Error √(AD·K·R).
* For one pair (s, n₂), i.e. M = {n₂ | c, s | d}, Γ = Γ₀(sn₂), A = L^{3/2},
  C = D = L²: one orbit, error √(AD) = L^{7/4} (times an exceptional-
  eigenvalue factor).  This is the individual bound in (Q), not better.
* Their gain needs many orbits of one fixed Γ.  A weight is Γ-invariant
  only if it is a condition modulo the level, so each of our two
  divisibility conditions forces its modulus into the level: the level is
  ≥ L² in every arrangement, and the sum over levels is not a sum over
  orbits of one group.  No direct application.
* Still a Cauchy–Schwarz over the spectrum between two L²-sharp quantities,
  so the same structural loss as (LS).
* Related, not applicable: arXiv:2509.07556 treats d_k × d, not d₃ × d₃;
  arXiv:2505.00493 (uniform equidistribution of roots of quadratic
  congruences, an² + h, uniform in h) is the closest published statement to
  the quadratic-root form above — not yet read against our ranges.

## Open, in order

1. Done (2026-11-15), negative.  arXiv:2505.00493 Theorem 1.4 (Type I)
   treats roots of aℓ² + h ≡ 0 (mod k), k ≡ 0 (mod d), for *fixed* h ≤ X²,
   a ≤ X^{o(1)}, on average over d ≤ D ≤ X^{1/2}.  Our sum is the case
   h = d = q: the matrix (m, ℓ; ℓ, k) = ((qν²+1)/D, −qν; −qν, qD) has
   determinant q, so k ≡ 0 and ℓ ≡ 0 (mod h).  In their normalization
   K = L⁶, window X = L^{9/2}, d = h = L²; the hypotheses hold
   (d ≤ X^{1/2} barely), but the bound L^{17/4+θ/2} is for the whole sum
   over d ≤ L² and exceeds the single-d main term L^{5/2}.  Their saving
   comes from averaging over d with h fixed; we have one d per h and an
   average over h, which the theorem does not cover.
   Open sub-question: does their argument (symmetric matrices of
   determinant h, action g ↦ γgγᵀ) allow an average over h with d = h?
2. (LS) on average over q: the pair-correlation count becomes a sum of a
   restricted d₃ over values uu' + 1 with a Diophantine side condition
   (u/j has a convergent with denominator ~ L).  Decide whether the side
   condition can be Fourier-expanded without recreating level L².
3. Equivalent analytic statement to test against the literature: an
   asymptotic for ∫_T^{2T} |ζ(½+it)|⁴ |Σ_{m~M} m^{−½−it}|² dt with
   M = T^{2/5+δ}.
