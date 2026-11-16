# Programme: past level 4/7 (started 2026-11-15)

Status: research in progress; AI exploration, nothing here is checked by a
human.  Background and dead ends: `two-sided-structure.md`.  The content of
both notes is packaged in Section 10 of the paper, and its arithmetic is
checked in `lean/MobiusDeterminant/Barrier.lean`; these notes keep the
working detail and the log.

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

## Log, round 3 (2026-11-15, late)

No proof.  Six items: one correction, two small gains, three more closed
routes.

### Correction: the moment dictionary (F9) is weaker than stated

(T) is **one dyadic piece** of the off-diagonal term of
∫|ζ|⁴|Σ_{m~M} m^{−½−it}|², M = T^{2/5}: the piece in which each divisor
function is restricted to factorizations of shape (T/M)·M, i.e. the box
(3/7, 2/7, 2/7)² in exponents of N = MT.  The full moment at the same M also
contains the balanced factorizations (√T)·(√T), which give the box
(2/7, 5/14, 5/14)², closer to the cube and not covered by the method.  So
(T) does not correspond to an asymptotic for the full integral, and
"level 4/7 ↔ twist length T^{2/5}" is a statement about sizes only.  Fixed
in the paper.

### Gain 1: (LS) may be averaged over all moduli

The terms of S(q) are non-negative and every pair (s, s') gives one modulus
q = ss', so

    Σ_{q~L², all integers} S(q) ≪ L^{7−δ}   ⟹   (LS) for most q = ss'.

The modulus no longer has to be a product; q becomes a free smooth variable.
(No use found for this yet: with q as the Kuznetsov modulus one meets sums
over q of products of two Kloosterman sums to moduli cq and c'q.)

### Gain 2: exact form of the pair correlation

Let γ = (x, z; cq, k), γ' = (x', z'; c'q, k') ∈ Γ₀(q), so xk − cqz = 1 and
x'k' − c'qz' = 1.  Put J = xc' − x'c and j̃ = zk' − z'k.  Then, exactly,

    J·kk' − j̃·cc'q = k'c' − kc,
    γ⁻¹γ' = (−u, −j̃; qJ, u'),  u = c'qz − x'k,  u' = xk' − cqz',
    uu' + 1 = J·j̃·q.

J/(cc'q) is the difference of the two Kloosterman fractions inv(k)/(cq) and
inv(k')/(c'q); j̃/(kk') is the same difference after reciprocity.  S(q)
counts the solutions with |J| ≤ L^{5/2}.  Checked numerically
(1610 random cases) and in Lean (`Barrier.fraction_pair`).  My first
derivation used one "j" for both J and j̃ and was wrong; the numerical test
caught it.  This is the standard unfolding (pairs of cosets ↔ elements of
Γ₀(q)); nothing beyond Kuznetsov follows from it by itself.

### Closed: q-van der Corput in the frequency

After extending to all n ≤ L^{3/2}, the frequency n is a smooth variable
that is *longer* than each factor r, s, s' of the modulus.  So the earlier
blanket statement "no smooth variable is longer than a factor of the modulus
it meets" is false for (LS), and one differencing step applies to
Σ_n Kl(2nj; rq)·conj Kl(2nj'; r'q).

* Terms r = r' (modulus rss' ~ L³, N = L^{3/2}):
  N^{1/2}(q₁^{1/2} + q₂^{1/4}) with q₁ = L, q₂ = L² gives L^{5/4}, a saving
  of L^{1/4}.  Needed for this part alone: L^{1/2+δ}.  Note that even the
  part r = r' of S(q) is L^{11/2} by Weil, above the target L⁵; its true
  size is L^{9/2}, the size of all of S(q).
* Terms r ≠ r' (modulus ~ L⁴): one step gives nothing, two steps save
  L^{1/8}.  These terms need the square-root cancellation over r that only
  Kuznetsov supplies.

So the algebraic method and the spectral method are each short, on different
parts, and I found no way to split S(q) between them: in the spectral form
the sum over r is taken before the square.

### Closed, with a corrected description: GL(3) long-element sums

By the Chinese remainder theorem,
e(2h·inv(d)/(rs)) = e(2h·inv(sd)/r)·e(2h·inv(rd)/s), which *is* the
un-Poissoned long-element Kloosterman sum of SL₃(Z) with moduli
(D₁, D₂) = (r, s), indices (m₁, m₂) = (2h, 2h), and both inner variables
equal to d.  The obstruction is not "squared inverses" (my earlier wording)
but this: after Fourier analysis in d modulo rs the dual indices are
(k₁, k₂) with j ≡ k₁s + k₂r (mod rs), and the weight is
ŵ(k₁s + k₂r) = Σ_{n₁,n₂} e(k₁n₁n₂/r + k₂n₁n₂/s).  For d smooth of length rs
this is concentrated at j = 0 (a complete sum).  For d = n₁n₂ it is an
erratic arithmetic function of (k₁, k₂, r, s), so the level-1 formula does
not apply.  The divisor structure of d is the obstruction, as elsewhere.

### Structural remark: why the problem sits outside every trace formula tried

b·ℓ₁ℓ₂ − a·n₁n₂ = N(x) − N(y) for x = (b, ℓ₁, ℓ₂), y = (a, n₁, n₂) in the
split cubic algebra Q³; equivalently it is det(D₀ + D₁Π) for diagonal
D₀, D₁ and the cyclic permutation matrix Π.  The six monomials
N_σ(g) = Π_i g_{i,σ(i)} are invariant under g ↦ tgt' for diagonal t, t' of
determinant 1, and for integer g

    N_{(12)} = N_{(13)} = N_{(23)} = 0,  N_e·N_{(123)} ≠ 0
    ⟺  g₁₃ = g₂₁ = g₃₂ = 0.

So (T) is the contribution of one *singular* stratum of torus double cosets
in GL₃.  A test function that isolates the stratum must be supported where
three invariants of natural size N are below ½, so its spectral transform
spreads over spectral parameters of polynomial size.  In GL₂ terms the
same information is carried by the level L².  Heuristic, not checked: the
two zero conditions that the GL₂ treatment turns into a level are an
"archimedean level" in GL₃.  The generic stratum is a different sum (all
nine entries nonzero).

### Bookkeeping, unverified: unequal levels

With d ≤ N^{θ₁}, e ≤ N^{θ₂}, the window for a factor of e is
[θ₁+θ₂−1, min(3−3θ₁−θ₂, (2−θ₁−θ₂)/3)] (exceptional-spectrum term not
worked out), and the balanced factor θ₂/2 lies in it iff
2θ₁ + 5θ₂ ≤ 4 and 2θ₁ + θ₂ ≤ 2.  So the one-sided method should give the
region {2θ₁ + 5θ₂ ≤ 4} ∪ {5θ₁ + 2θ₂ ≤ 4}, whose corners with min θᵢ ≥ ½
are (½, ¾), (4/7, 4/7), (¾, ½); the product de reaches N^{5/4} at the
corners against N^{8/7} on the diagonal.  The two-sided reduction adds
nothing off the diagonal: a piece is uncovered only if both conditions fail.
Points with min θᵢ < ½ are covered by Bombieri–Vinogradov-type arguments.

## Log, round 4 (2026-11-15/16)

No proof.  This round located the difficulty inside S(q) more precisely.

### Experiment 3: the level and the two parts of S(q) (`lab/levelscan.c`)

G_q = Σ_r G_r with G_r(n) = Σ_d e(2n·inv(d)/(rq)).  Then
S(q) = Σ_r ‖G_r‖² + Σ_{r≠r'} ⟨G_r, G_r'⟩ = "diag" + "cross" (norms over
1 ≤ n ≤ 4HL).  Entries are divided by N·P, so square-root cancellation is 1.

| L  | q    | total | diag (r = r') | cross (r ≠ r') |
|----|------|-------|---------------|----------------|
| 32 | 1    | 12.21 | 25.71         | −13.50         |
| 32 | 3    | 6.63  | 8.38          | −1.76          |
| 32 | 7    | 3.59  | 3.28          | 0.30           |
| 32 | 33   | 1.07  | 0.76          | 0.32           |
| 32 | 181  | 0.80  | 0.88          | −0.08          |
| 32 | 1025 | 0.96  | 0.97          | −0.02          |
| 32 | 2047 | 1.08  | 1.00          | 0.08           |
| 64 | 1    | 25.82 | 51.62         | −25.80         |
| 64 | 7    | 6.92  | 6.90          | 0.03           |
| 64 | 65   | 1.17  | 0.66          | 0.51           |
| 64 | 513  | 0.88  | 0.90          | −0.03          |
| 64 | 4097 | 1.09  | 0.99          | 0.10           |
| 64 | 8191 | 1.00  | 1.00          | 0.01           |

Reading.
* For q ≳ L the sum S(q) is its trivial diagonal: the terms with the same
  r and the same d.  Cross terms are a few percent and have no fixed sign.
* At level q = 1 there is no square-root cancellation: |G|² ≈ 0.4·L·P.  The
  points are then the Farey neighbours of fractions with denominator ~ L
  and sit in clusters.  The level acts by multiplying numerators by inv(q)
  modulo each denominator, which scrambles the clusters; this takes effect
  once q ≳ L, i.e. once the sum over d is incomplete.
* At q = 1 the cross terms are −½ of the diagonal.  So the diagonal is
  **not** bounded by S(q), and the spectral bound for S(q) says nothing
  about it.

### Two separate problems inside (LS)

(D)  diag = Σ_r Σ_n |G_r(n)|² ≪ L^{5−δ};
(C)  |cross| ≪ L^{5−δ}.

Sizes for (D): Weil L^{11/2}; one van der Corput step in n, L^{21/4};
needed L^{5−δ}; observed L^{9/2}.

(D) is a single-modulus statement, M = rq ~ L³:

    Σ_{n ≤ M^{1/2}} |Σ_{d ~ M^{2/3}} e(n·inv(d)/M)|² ≪ M^{4/3−δ}  on average over M.

Equivalent forms of (D):
* additive correlation of inverses: the number of (d, d', j), |j| ≤ M^{1/2},
  with inv(d) − inv(d') ≡ j (mod M) is asymptotic to its expected value
  M^{5/6} with a power saving (in the coordinate x = inv(d) the map
  d ↦ d/(1 − jd) is the translation x ↦ x − j);
* points on the hyperbolas XY ≡ −inv(j)² in boxes of side M^{2/3} centred at
  (−inv(j), inv(j)), on average over |j| ≤ M^{1/2}.  One box is below the
  individual threshold M^{3/4};
* Σ_{j ≤ M^{1/2}} S(a, −b·inv(j)²; M)·e((a−b)·inv(j)/M) ≪ M^{5/6−δ} on average
  over a, b ≤ M^{1/3}: a sum of length M^{1/2} of a two-variable trace
  function, with a saving M^{1/6+δ}.  Van der Corput with a factor M^{1/3}
  saves M^{1/12}.  No known exponent pair has κ + λ < 2/3, which is what a
  purely algebraic proof for smooth M would need (best known ≈ 0.82).
* on average over r and q: #{UV + 1 = j·r·q·w, U ≡ −1 (mod j)}, a d₂ × d₄
  correlation at level ½ with a congruence twist.  This form may be within
  reach of the dispersion method; not examined.

(C) is where Kuznetsov's cancellation over r is indispensable: with r kept
outside the square there are no cross terms, but then even the observed
sizes are insufficient (L^{13/4} per pair against L^{3−δ}), because the
extension from the Bohr set to all n costs L^{1/2} and nothing recovers it.

So: the spectral method bounds diag + cross at the borderline and cannot
separate them; the algebraic method sees only diag and is short by L^{1/4}.

### The pair correlation as a d₂ × d₃ equation with a Diophantine weight

With σ = γ⁻¹γ' = (−u, −j̃; qJ, u') as in round 3, and q summed over all
integers ~ L²,

    Σ_q S(q)/N₀ = Σ_{uu' + 1 = q·J·j̃} ψ(u/J),
    ψ(x) = #{c ~ L : ‖cx‖ ≤ L^{−3/2}} = 2L^{−3/2} Σ_{|m| ≲ L^{5/2}} d_L(m) e(mx).

The term m = 0 is the expected count.  Without ψ this is the d₂ × d₃
shifted convolution, which is known with a power saving.  The weight ψ
restricts u/J to major arcs around fractions of height L; for m ≠ 0 it
shifts one Kloosterman frequency by mq:

    Σ_{J,q} Σ_{a,b ≲ L} S(a + mq, b; Jq)
      = Σ S(a·inv(q) + m, b·inv(q); J) · S(a·inv(J), b·inv(J); q),

two moduli J ~ L^{5/2} and q ~ L², both free and smooth, each appearing
inverted in the other's sum.  Not pursued further.

### Other remarks from this round

* G_q(n) depends on (n, q) only through the fraction n/q:
  G_q(n) = Σ_{x~L²} Σ_{r~L} e(−(n/q)·inv(r)/x), with n/q read modulo x.
* Elementary: Σ_x Σ_n |Σ_{r~L} e(n·inv(qr)/x)|² is diagonal up to a factor
  1 + O(L^{−1/2+ε}), by the divisor bound.  So full cancellation in r is
  free if none is asked in x, and Kuznetsov gives full cancellation in x
  and half of it in r.  (LS) asks for slightly more than half.

## Log, round 5 (2026-11-16)

No proof.  The barrier now has a one-line statistical form, supported by a
new experiment, and several more routes are closed.

### The barrier as a decorrelation statement

Let N(x, ℓ) be the number of points of Θ_q = {2·inv(d)/(rq)} in the arc
[x, x+ℓ).  Parseval gives Var_x N(x, ℓ) ≈ ℓ² Σ_{0<|n|≲1/ℓ} |G_q(n)|², so the
dual large sieve (Σ_{|n|≤N} |G_q(n)|² ≪ L^{5+ε}(1 + N/q)) says:

* at ℓ = 1/q:  Var ≪ L^{1+ε} = mean^{1+ε}.  **The method proves a variance
  of Poisson order at the scale 1/q.**
* at ℓ = K/q, 1 ≤ K ≤ q:  Var ≪ K · mean.  This is what one gets from the
  case K = 1 if the counts in the K sub-arcs are fully correlated.
* (LS) is the case K = q^{1/4}: Var ≪ K^{1−δ} · mean.

So level 4/7 is exactly "nothing is known about the correlation between
neighbouring arcs of length 1/q", and passing it needs any power saving in
that correlation, summed over q^{1/4} neighbours.  The bound at the scale
1/q is sharp, so no slack is left there.

### Experiment 4: the variance at all scales (`lab/arcs.c`)

Counts of the points in arcs of length K/q; var/mean by block size, and the
correlation coefficient of the counts in arcs at lag k.

| L   | q     | mean (K=1) | var/mean for K = 1, 2, 4, …, 512                       | lags 1–8, max abs |
|-----|-------|------------|--------------------------------------------------------|-------------------|
| 64  | 4097  | 36.7       | 1.07 1.08 1.10 1.04 1.06 1.00 1.10 0.89 1.06 0.79      | 0.025             |
| 64  | 8191  | 19.5       | 1.02 1.00 0.98 0.99 1.00 1.01 0.85 0.91 0.94 1.03      | 0.015             |
| 128 | 16385 | 62.0       | 0.97 0.96 0.93 0.92 0.88 0.94 1.01 1.09 1.18 1.13      | 0.013             |

(For large K there are few blocks and the estimate is noisy.)  The variance
is the mean at every scale, and neighbouring arcs are uncorrelated to within
the noise.  The point set is statistically Poisson at every scale tested.

### A dictionary for one arc

An arc of length 1/q is a window of r consecutive numerators y modulo rq,
which is a complete residue system modulo r and an interval of length r
modulo q.  With d(y) ∈ [L², 2L²) the inverse of y modulo q and
m(y) = (y·d(y) − 1)/q,

    N(x, 1/q) = Σ_{y in a window of length ~L} #{r ~ L : r | m(y)}.

So the counts are restricted divisor functions of the "Kloosterman
quotients" m(y) of consecutive y, and (LS) is the statement that these
divisor functions decorrelate over y-ranges of length L^{3/2}.

### Why the diagonal part is easy for unstructured moduli

If M runs over **all** integers ~ L³, then
Σ_M #{(d,d',j) : M | jdd' + d − d'} = Σ_{j,d,d'} d_{[L³]}(jdd' + d − d'),
and one may switch to the complementary divisor w ~ L^{5/2}.  Modulo w the
box has side L² = w^{4/5} > w^{3/4}, Weil's bound applies to each w, and the
error is L^{21/4} against a main term L^{11/2}.  So (D) on average over all
moduli is elementary.  For M = rq with r ~ L the divisor is structured, the
only pure congruence has modulus rq ~ L³, and the switch is not available.
Same phenomenon as in the original problem: d₂ is easy, d₃ is not.

### Closed this round

* **Hölder with a fourth moment in n.**  The n ≠ 0 part of Σ_n |G(n)|⁴ is an
  additive energy minus its expected value; it needs an asymptotic with
  relative error L^{−5/2}, and energy *upper* bounds (divisor counting
  averaged over the modulus, as in the paper) cannot see it.
* **Fourth moment in (r, d).**  Σ_{r,d} |F(r,d)|⁴ has more margin (L against
  L^{1/2}) but the level becomes s₁s₂s₃s₄ ~ L⁴ and the spectral bound saves
  only L^{1/2} of the L² needed.
* **Extending the range of n.**  Bessel's inequality is sharp at N = q, so
  S(q) = (mass up to q) − (mass in (q^{3/4}, q]).  A lower bound for the
  second term from its diagonal fails: the relevant weight has a Fourier
  transform that is negative exactly on the pairs counted by S(q).
* **Fixing r.**  For fixed r the sum over d of |F_r(d)|² needs L^{4−δ}; the
  smooth variable s can serve as the modulus with level r ~ L only, but the
  second factor of the square is then a periodic weight modulo rs', and the
  bound for periodic weights (Grimmelt–Merikoski) loses L^{7/4}.
* **Positive-definiteness in the shift.**  The correlation is an
  autocorrelation R(2) of f = restricted d₃; Bochner's inequalities relate
  R(2) to R(0), which is larger by logarithms, and no low-complexity model
  approximates f in L².
* **GL₃ lattice-point counting.**  A bump of width < 1 in the three zero
  entries isolates the count exactly as Σ_{γ ∈ SL₃(Z)} F(γ), but the region
  is a slab of thickness 1 inside a set of diameter L^{5/2}; it is
  well-rounded only for ε ≲ L^{−5/2}, and the mean ergodic theorem then
  gives nothing.  Dropping one of the three zero conditions gives
  rβ − an₁n₂ = 2, which is d₂ × d₃ and known.

### Where this leaves the programme

Five rounds, and every reformulation ends at the same statement: a power
saving in the correlation between q^{1/4} neighbouring arcs, equivalently
(LS), equivalently (T).  The known method is sharp at the single-arc scale.
The algebraic method handles the diagonal part only for unstructured
moduli.  I do not have a candidate proof strategy that is not on the closed
list.

## Log, round 6 (2026-11-16)

Still no proof.  One long shot is now closed for a definite reason, the loss
is quantified exactly, and there is a new arithmetic observation.

### Closed: the Grimmelt–Merikoski kernel theorem (their Theorem 8.1)

Read from arXiv:2505.00493 §2 (which quotes arXiv:2505.00489 Thm 8.1).  For
F a bump on the box {|x| ≤ X, y ∈ [Y, 2Y]} of the upper half-plane,

    ⟨α₁|Δ_q F|α₂⟩ ≪ (X/Y)^{1/2} Z₀^θ ⟨α₁|Δ_q k_{Z₁²}|α₁⟩^{1/2} ⟨α₂|Δ_q k_{Z₂²}|α₂⟩^{1/2},
    Z₀Z₁Z₂ ≥ X/Y,

with non-negative kernels k supported on matrices of size Z_i².  Our arc
count is this with α₂ = the Fricke point i/√q, α₁ = translations n[x₀],
X = ℓ/2, Y ≍ L^{−5}; X/Y = ℓL⁵ is the hyperbolic area of the box.  Both
kernel sums are ≥ their diagonal, so the best possible outcome is

    Σ_{x₀} |discrepancy(x₀)|² ≪ area of one box = ℓL⁵,

i.e. Var ≪ (ℓq)·mean: exactly the bound we already have.  Their gains come
from averaging the kernel sums over the level with a divisor bound and from
many orbits; neither lowers the leading factor (X/Y)^{1/2}.  The bound is
"square root of the area", the truth is "square root of the count", and
area = q × count.  **The loss is √(level), built into the first step.**

### The loss, exactly

With inner modulus variable of size S and dual length H (level q = S²,
frequencies N₀ = HS): Bessel bound / truth = 1 + q/N₀ = 1 + S/H.

* For q ≤ N₀ the dual large sieve is sharp: square-root cancellation on
  average is *proved* for levels up to the frequency range.  (Consistent
  with experiment 3, where S(q) ≈ N·P already for q ≳ L.)
* No loss needs S ≤ H; the diagonal needs S ≥ H.  So the method wants a
  factor of the modulus of size ≈ H = N^{2θ−1}, the bottom of the window.
  The balanced piece has S = L = H² at θ = 4/7.
* Even the truth of (LS) reaches only θ = 3/5: (T) needs
  S(q) ≪ L⁶H^{−2−δ}, and the true size HL⁴ meets this iff H < L^{2/3}.
  The (LS) route discards the signs over the Bohr set, which is what a proof
  past 3/5 would need.

### Base points: typical versus special

Let N_B(z) = #{γ ∈ Γ₀(q) : γz ∈ B}.  Averaged over the base point z on the
whole surface, Var_z N_B(z) ≪ mean at every scale ℓ ≥ 1/q: this is the
ordinary large sieve (over forms), and it is sharp.  At the one base point
we need (the Fricke point, a Heegner point of discriminant −4q) the same
argument loses the factor ℓq.  So (LS) is a statement that this point is
typical for the fluctuation functions z ↦ N_{B(x₀)}(z) − mean: a sup-norm
type saving of q^δ over the local Weyl bound, on average over x₀, for a
*combination* of ≍ q forms rather than a single form.

### The sum before Cauchy–Schwarz, over Gaussian integers

With c = ℓ₂r, d = n₂x, D = c² + d² and ν ≡ c·inv(d) (mod D) (so ν² ≡ −1),

    Σ_{h} Σ_{ℓ₂,n₂,r,x ~ L} e(2h·inv(n₂x)/(rℓ₂))
      = Σ_h Σ_{c,d ~ L²} d_L(c) d_L(d) e(2hν/(c²+d²)) (1 + O(L^{−7/2})).

So (T) is: the roots of ν² + 1 ≡ 0 (mod c² + d²), weighted by restricted
divisor functions of the two coordinates of the Gaussian integer d + ic,
are equidistributed at frequencies up to D^{1/8} with a saving D^{1/8+δ}.
Without the weights, or with one of them, this is easy.  The conditions
ℓ₂ | c, n₂ | d say d + ic ∈ O_{ℓ₂} ∩ i·O_{n₂} (orders of Z[i] of
conductors ℓ₂, n₂).  The corresponding point of X₀(ℓ₂n₂) is W_{n₂}(i/n₂):
it lies over i under one projection to X(1) and over the CM point iℓ₂/n₂
of conductor ℓ₂n₂ under the other.  Twisting by ring class characters does
not lower the level (the functions χ(d + ic) on P¹(Z/f) are Steinberg).

### Observation: square levels are not random to the same degree

Experiment 3 repeated for different types of q (L = 64 unless stated;
total / diag / cross as before):

| q                  | total | diag | cross |
|--------------------|-------|------|-------|
| 4099 (prime)       | 1.03  | 0.99 | 0.03  |
| 4087 = 61·67       | 0.96  | 0.99 | −0.03 |
| 4095, 4160, 4290   | 0.99, 1.00, 0.91 | 0.99 | ≈ 0 |
| 3721 = 61²         | 1.35  | 0.99 | 0.37  |
| 4489 = 67²         | 1.27  | 0.99 | 0.28  |
| 5041 = 71²         | 1.51  | 1.00 | 0.51  |
| 4225 = 65²         | 1.44  | 0.99 | 0.45  |
| 4096 = 2¹²         | 1.25  | 0.98 | 0.28  |
| 961 = 31² (L = 32) | 1.86  | 1.00 | 0.86  |

For squares the cross part is positive, 0.2–0.9 of the diagonal.  It is not
carried by frequencies sharing a factor with q (those are *smaller*,
`lab/gcdscan.c`), nor by pairs r ≡ ±r' (mod √q) (`lab/paircorr.c`: no pair
has correlation above 0.15; the excess is a small common positive
correlation spread over all pairs), nor by a quadratic-residue class of n
(`lab/legscan.c`).  The mean of Re G over n is negative, about −0.1·√P.
Cause not yet identified.  Our moduli q = ss', s ≠ s', are not squares, so
this does not affect (LS), but it shows the cross part is sensitive to the
local structure of the level.

### Square levels: a finite-size effect

More prime squares at L = 64 (cross part): 43²: 0.18, 53²: 0.23, 59²: 0.43,
61²: 0.37, 67²: 0.28, 71²: 0.51, 73²: 0.13, 83²: 0.10, 89²: 0.17,
97²: 0.12, 127²: 0.06.  Always positive, and decaying roughly like
(N/q)^{1.2} as q grows against the frequency range N = 2048.

Reading: these runs have N/q between 1/8 and 1/2, not N = q^{3/4}.  Near
N ≈ q Bessel's inequality is sharp and the constant is governed by the Gram
matrix of the vectors v_n, i.e. by Kloosterman sums S(n, n'; cq) with small
c.  For q = p² these vanish unless nn' is a quadratic residue mod p and are
2p·cos(…) otherwise, which changes that constant.  The excess disappears as
N/q → 0, so it does not bear on (LS).  **Caveat for all the experiments:**
at L ≤ 256 they probe N/q ≈ 1/16 at best, where the proved bound is only
≈ 10× the observed value; they cannot distinguish q^{3/4} from q.

### More closed routes (this round)

* **Completing the sum over q by positivity.**  G̃_q(n) = Σ_{d,r}
  e(−2n·inv(rq)/d) is defined for every integer q and is periodic in q.
  Over a full period the mean of |G̃_q(n)|² is exactly P (cross terms are
  Ramanujan sums).  (LS) asks for the mean over the short range q ~ L²,
  which is the square root of the period dd' of each cross term: the
  Pólya–Vinogradov threshold again.  Extending q by positivity costs the
  ratio of the lengths, L².
* **GL₃ again, in this picture.**  The cross terms d ≠ d' are long-element
  sums S(inv(d')·j, 2n·inv(r); d)·conj S(inv(d)·j, 2n·inv(r'); d') with both
  moduli smooth and free, but with indices n/r, n/r' that are residues, not
  integers; they would be integers only for r = r' = 1.
* **Regrouping the six variables.**  The cofactor on each side must be one
  smooth variable, so the modulus is ℓ₁ℓ₂ (4/7) or larger; factoring the
  long variable b = st only produces larger moduli.
* **Standard conjectures.**  Selberg's eigenvalue conjecture removes only
  the term already removed by Pascadi.  Lindelöf for L(½, f) in the level
  aspect gives nothing beyond the second-moment bound already used.  A
  uniform Linnik–Selberg bound for Σ_c S(m,n;cq)/c gives exactly the
  borderline (the sum over m ~ √q is then taken trivially).  So level
  > 4/7 for Λ_R does not follow from any of these.

### A cleaner split: the diagonal is elementary in the other picture

By reciprocity G_q(n) = Σ_{x~L²} K_x(n·inv(q)), with
K_x(a) = Σ_{c~L} e(−a·inv(c)/x) an incomplete Kloosterman sum of length √x
to the modulus x (x is the old variable d, c the old r).  Split S(q) by
pairs of moduli (x, x') instead of pairs (r, r'):

    S(q) = Σ_x Σ_n |K_x(n·inv(q))|²  +  Σ_{x≠x'} Σ_n K_x(n·inv(q))·conj K_x'(n·inv(q)).

* The first sum is N₀·(#(x,c) + #{(x,c,c',j) : j ≠ 0, |j| ≤ x/N₀,
  x | c' − c − q·j·c·c'}).  The integer c' − c − qjcc' is nonzero and has
  ≪ L^ε divisors x, so the second count is ≪ L^{5/2+ε} against the first,
  L³.  Hence, **for every fixed q,**

      Σ_x Σ_n |K_x(n·inv(q))|² = N₀·P·(1 + O(L^{−1/2+ε})),

  the observed value of S(q), by the divisor bound alone.  (In the (r, r')
  split of round 4 the diagonal part was the hard one; here it is free.)
* So **(LS) ⟺ the sum over pairs of distinct moduli x ≠ x' is ≪ L^{5−δ}.**
  It is ≥ −N₀P(1+o(1)) trivially and ≤ L^{5+ε} by the spectral bound.
* That sum counts (J, c, c', x, x') with x | Jqc − x' and x' | Jqc' + x,
  |J| ≤ L^{5/2}.  Solving, with w = (Jqc − x')/x, w' = (Jqc' + x)/x' and
  g = gcd(ww'+1, w'c − c'):

      ww' ≡ −1 (mod gq),   cw' ≡ c' (mod g),   g ~ L^{5/2}.

  Fourier analysis in the long variable w' (length L^{7/2}, modulus
  c'qx ~ L⁵) gives complete sums that factor exactly,

      S(kc'²q + tx², j; c'qx) = S(k·inv(q), j; x) · S(t, j; c'q),

  and the cross sum becomes Σ_{j ≲ L^{3/2}} of the product of two sums of
  Kloosterman sums of level q sharing the index j — that is, Σ_j |G_q(j)|²
  again.  The pair correlation is self-dual under every transformation
  tried.

### Experiment 7: the split by moduli, checked (`lab/xsplit.c`)

Same normalization as experiment 3, but split by pairs of the inner
variable d (the modulus x of the reciprocity picture), L = 64:

| q    | total | diag (d = d') | cross (d ≠ d') |
|------|-------|---------------|----------------|
| 1    | 25.82 | 0.990         | 24.83          |
| 7    | 6.92  | 0.991         | 5.93           |
| 65   | 1.17  | 0.991         | 0.17           |
| 4099 | 1.03  | 0.992         | 0.04           |
| 4087 | 0.96  | 0.992         | −0.04          |
| 3721 | 1.35  | 0.991         | 0.36           |
| 8191 | 1.00  | 0.992         | 0.01           |

The diagonal is 0.99 at **every** level, including q = 1 and the squares,
as the divisor-bound argument predicts.  All structure — the clustering at
small level, the excess at squares — is in the cross part.  At q = 1 it is
explained exactly: G₁(n) ≈ L²·#{c ~ L : c | n} (complete sums over d,
Ramanujan sums), so |G₁(n)|² ≈ L⁴ for the n with a divisor in [L, 2L).

### The pair correlation at level 1

Summing over all q ~ L² turns the level into a divisor function:

    Σ_q S(q)/N₀ = Σ_{σ ∈ SL₂(Z)} d_{[L²]}(σ₂₁)·m(σ),
    m(σ) = #{v = (d', c') ∈ box : vσ ∈ box},

because pairs (γ, γ') of bottom rows correspond to σ = γ'⁻¹γ, and
σ ∈ Γ₀(q) iff q | σ₂₁.  Without m(σ) this is the d₂ × d₃ problem
AD − B·J·q = 1.  The weight m(σ) asks that σ carry a small integer vector
to a small integer vector, i.e. that σ₂₁/σ₁₁ lie within L^{−5/2} of a
fraction with denominator ~ L.  For fixed (c', d', d) the entries
(σ₁₁, σ₂₁) run over a line with parameter λ ~ L^{5/2}; the divisor
condition q | σ₂₁ is complete in λ modulo q, and the size condition on σ₂₂
is c'·inv(σ₁₁)/d ∈ arc, complete in λ modulo d.  Each is elementary; jointly
the modulus is qd ~ L⁴ against a range L^{5/2}.  Same incompleteness,
L^{1/2} below what positivity can pay for, in every variable tried:

    range of (n, q):  L^{7/2}  against modulus dd' = L⁴;
    range of q alone: L²       against modulus dd' = L⁴ (square root);
    range of λ:       L^{5/2}  against modulus qd = L⁴.

## Log, round 7 (2026-11-16): deeper structure

No proof.  This round produced five further exact reformulations, each
checked against the others, and for each one the reason the known tools give
exactly the borderline.  The picture is now rigid enough to say what a proof
must contain.

### (Y) Two boxes of SL₂(Z) in the cosets of Γ⁰(q)

For c' ~ L, d' ~ L² let c̄ = inv(c') mod d' and e' = (c̄c' − 1)/d', so
M₃ = (c̄, d'; e', c') ∈ SL₂(Z).  Its class in Γ⁰(q)\SL₂(Z) ≅ P¹(Z/q) is
x = c̄·inv(d') ≡ inv(c')·(inv(d') + e') (mod q), and **exactly**

    Σ_{(c',d')} e(−ψx/q) = Σ_{(c',d')} e(−ψ·inv(d')/(c'q)) · e(−(ψ/q)·{−inv(d')/c'}).

(Checked numerically to 10⁻¹², scratch `ycheck.py`; the congruence is in
Lean as `Barrier.coset_class`.)  So the Fourier transform on Z/q of

    ν₃(x) = #{M ∈ 𝔅₃ : class of M is x},   𝔅₃ = SL₂(Z) ∩ {entries ~ (L², L²; L, L)}

is G_q(ψ) up to a harmless factor, for all ψ.  Consequences:

* Var(ν₃) = (1/q)Σ_{ψ≠0}|G_q(ψ)|² over the full range, where the dual large
  sieve is sharp: **ν₃ has variance of Poisson order (proved).**
* Let ν₁ = Σ_{k~√L} ν₃(· − k).  It counts the box 𝔅₁ = 𝔅₃·{(1,0;k,1)} with
  entries ~ (L^{5/2}, L²; L^{3/2}, L), and Var(ν₁) = (L/q)·S(q).
* **(LS) ⟺ Var(ν₁) ≪ L^{4−δ}** (Poisson would be L^{7/2}; fully correlated
  shifts give L⁴).  Equivalently: the fluctuation of ν₃ decorrelates under
  the unipotent shifts x ↦ x + k, k ≤ q^{1/4}; equivalently ν̃₃ has no
  concentration on additive frequencies |ψ| ≤ q^{3/4}.
* Summed over q the count is #{(M₁, M₃, q) : M₃M₁⁻¹ ∈ Γ⁰(q)}.

Why operator norms do not help.  In the additive Fourier basis of Z/q an
element β = (a,b;c,d) with b ≢ 0 acts by the flat matrix
(1/q)·e((ψa + ψ'd)·inv(b)/q)·S(ψψ'·inv(b)², 1; q), and the elements with
b = 0 are the unipotents, which preserve frequencies.  A ball of radius R in
SL₂(Z) contains R unipotents, which alone give the ball operator its full
norm √|ball| on low frequencies.  So "ball operators map into low
frequencies generically" is false as an operator statement, and a bound must
use the specific vector δ_{x₀}.  Lifting to SL₂(R) (Gorodnik–Nevo) is exact
for balls but loses 1/vol(𝒪) for the thin sectors that 𝔅₁, 𝔅₃ are.

### The mass zeta function and a reciprocity between scales

Let c = (c_g) be the spectral vector, b_g = c_g·ρ_g(1), μ_c(n) = |⟨c, v_n⟩|².
Then

    D_c(s) := Σ_n μ_c(n) n^{−s} = Σ_{g,g'} b_g conj(b_g') L(s, g×ḡ')/ζ(2s),

a positive-definite combination of Rankin–Selberg L-functions of conductor
q².  It has a pole at s = 1 whose residue gives **exactly the generic value**
(N/q)‖c‖² for the mass up to N, and a functional equation s ↔ 1 − s that
exchanges c with its Fricke twist Wc.  Hence

    mass of c up to N  =  (N/q)‖c‖²  +  (N/q)·Σ_n μ_{Wc}(n)·𝒲(nN/q²),

with 𝒲 of mean zero: the excess mass at scale N = q^{3/4} equals the
non-flatness of the mass distribution of Wc at the dual scale q²/N = q^{5/4}.
In pair-correlation terms: precision L^{−1} at scale L^{−3/2} is equivalent
to precision L^{−1/2} at the finer scale L^{−5/2}.  Bessel's inequality is
the trivial bound on both sides.  A sufficient (stronger) statement:
|D_c(½ + iu)| ≪ q^{−3/8−δ}‖c‖²; trivial ‖c‖², generic q^{−1/2}‖c‖².  With
b_g ≈ ω_g X^{2it_g} L(½, g) this is

    Σ_{g,g'} ω_g ω_g' X^{2i(t_g − t_g')} L(½,g) L(½,g') L(½, g×g'),

the Rankin–Selberg L-values of the GL₃ Eisenstein series g ⊞ 1, g' ⊞ 1.

### Mass in a cusp neighbourhood

Ψ = Σ_g c_g g is the wave kernel K_τ(·, z₁), τ ≈ (7/4) log q, at the Fricke
point.  By Parseval on horocycles,

    S(q) ≈ ∫_{y > q^{−3/4}} |Ψ|² dμ.

The region is an embedded neighbourhood of the cusp ∞ of area q^{3/4}, a
fraction q^{−1/4} of the surface.  **(LS) ⟺ the wave puts mass ≤ q^{−δ}‖Ψ‖²
in that cusp neighbourhood.**  The trivial bound is the total mass.  For a
single Hecke eigenform the analogous statement follows from multiplicativity
of |λ(n)|² (Holowinsky-type sieve bounds); Ψ is a combination of ≍ q forms
and the cross terms are not multiplicative.

### A thin-shell lattice point problem at radius 2τ

Expanding |Ψ|² geometrically, pairs of sheets of the wave front interfere
only where they are tangent, and

    S(q) − generic ≈ e^{−τ} T^{−3/2} Σ_{σ ∈ Γ₀(q)} χ(mid(z₁, σz₁)) · F(T(d(z₁, σz₁) − 2τ)),

F of mean zero, χ the indicator of the cusp neighbourhood.  This is a
hyperbolic lattice point count for Γ₀(q) centred at the Fricke point, in a
thin shell of radius R = 2τ = (7/2) log q, with an angular weight.  The main
term is e^R/q^{5/4}; the spectral bound for the error is e^{R/2} (local Weyl
law at z₁); needed e^{R/2}·q^{−δ}; square root of the count would be
e^{R/2}q^{−5/8}.  **So the barrier is an error term below the square root of
the area in a level-aspect circle problem.**  No bound below e^{2R/3} is
known for any group pointwise; here an average over the level and over the
angular weight is available.

### What a proof must contain

Every formulation ends in one of two equivalent shapes:

1. a positive quantity (variance, mass, mean square) for which positivity
   plus orthogonality gives the borderline and the truth is smaller by
   q^{1/4}; or
2. a signed sum (pair correlation, shell count, Σ L·L·L(g×g')) with a
   trivial bound at the borderline.

In shape 1 the operator-norm statements tried in the coset picture are
false, with unipotent elements or low Fourier coefficients as
counterexamples.  (Corrected in round 8: in the Kloosterman block picture,
where the free vector lives on the dual variable m ~ √q, the operator-norm
statement appears to be true; see Experiment 8.)  In shape 2 the cancellation needed is one that no trace
formula sees in a single application: both sides of Kuznetsov, of the
Rankin–Selberg functional equation, and of the pretrace formula have the
same number of terms at θ = 4/7.

## Log, round 8 (2026-11-16): the Kloosterman block is generic as an operator

### Experiment 8 (`lab/kblock.c`, `kscan.c`, `kscan2.c`, `krow.c`)

Poisson summation in d turns G_q(n) into Σ_m w_m K(m,n) with

    K(m,n) = Σ_{c ∈ [C,2C)} S(m,n;cq)/(cq),   m ∈ [M,2M),  1 ≤ n ≤ N,
    C = M = ⌊√q⌋,  N = ⌊q^{3/4}⌋,

and (LS) says that the smooth vector w has ‖Kᵀw‖² ≪ q^{−δ}·‖w‖².  Bessel's
inequality (= Kuznetsov + the large sieve at level q, both ranges below the
level) gives ‖K‖² ≤ O(1), i.e. top eigenvalue of KKᵀ ≤ (q/N)·(mean
eigenvalue).  The experiment computes the whole spectrum of KKᵀ.

| q (primes near)   | 280  | 1000 | 4100 | 16000 |
|-------------------|------|------|------|-------|
| number of levels  | 16   | 30   | 51   | 29    |
| median top/mean   | 2.78 | 3.09 | 3.50 | 3.24  |
| max top/mean      | 4.14 | 5.03 | 4.68 | 3.72  |
| flat (MP) edge    | 2.23 | 2.00 | 1.83 | 1.69  |
| Bessel: 1+q^{1/4} | 5.1  | 6.6  | 9.0  | 12.2  |

* The mean eigenvalue equals the generic value N·Σ_c φ(cq)/(cq)² to a few
  percent: entries of K have square-root size q^{−1/2} in mean square.
* The spectrum is a Marchenko–Pastur bulk with one or two outliers.  The top
  eigenvalue does **not** grow with q over a factor 64 in q (q^{1/4} grows by
  2.8).  An outlier is coherent in c (removing any single c does not remove
  it) and its eigenvector is roughly Hecke-multiplicative: these are
  individual low-lying forms, amplified by the logarithmic peak of the
  Bessel transform at t = 0.
* Composite levels behave the same: products of two primes near √q
  (1147, 1189, 1517, 1763: top/mean 2.1–3.7), squares (961, 1369, 1681,
  1600: 3.2–3.5), smooth (1260, 1440, 1680: 2.2–2.5).
* Single rows: Σ_{n≤N} K(m,n)²/generic for m = 1,…,8 is 1.00 ± 0.1 at
  q = 1009, 4001, 4003, 16001, 64007, where Bessel/generic = 5.6, 8, 8,
  11.3, 15.9.

### Conjecture (OP) and its smallest instance

**(OP)**  For all a, b:
Σ_{m~√q} Σ_{n≤q^{3/4}} a_m b_n Σ_{c~√q} g(c) S(m,n;cq)/(cq) ≪ q^{−δ}‖a‖‖b‖.

Known: ‖a‖‖b‖ (Deshouillers–Iwaniec; this is Bessel).  Entrywise Weil gives
q^{3/8}; an optimal entrywise bound (Linnik–Selberg in the level aspect,
|K(m,n)| ≪ q^{−1/2+ε}) gives only the Frobenius bound q^{1/8}.  Expected:
q^{−1/8}.  **(OP) ⇒ (LS) ⇒ level beyond 4/7**, and (OP) does not involve the
smooth vector at all.

**(OP₁)**  Σ_{n ≤ q^{3/4}} |Σ_{c~√q} S(1,n;cq)/(cq)|² ≪ q^{−δ}.

Known: 1 (Bessel), q^{1/4} (Weil).  Expected and observed: q^{−1/4}.
(OP₁) is the statement that the Linnik–Selberg sum in the level aspect is
≪ q^{−3/8−δ} in mean square over n ≤ q^{3/4}; Weil gives q^{−1/4} pointwise,
the spectral bound q^{−3/8} on average, the truth is q^{−1/2}.

Equivalent forms of (OP₁):

* (short incomplete Kloosterman sums, averaged over the modulus)
  ∫₀¹ |Σ_{c~C} c^{−1} Σ_{y ∈ cq·[θ, θ+1/N]} e(ȳ/(cq))|² dθ ≪ q^{1/2−δ};
  the inner sums have length exactly √modulus, the Pólya–Vinogradov
  threshold; trivial q^{3/2}, Bessel q^{1/2}, random q^{1/4}.
* (trace of Hecke operators)  Σ_{n≤N} |Tr(T_n ĥ(Δ))|² ≪ q^{2−δ} for the
  harmonic-weighted trace on Γ₀(q), ĥ(t) ≈ X^{2it}(1+|t|)^{−3/2}.
* (K is a function of the product)  K(m,n) = F(mn) up to gcd terms, with
  F(t) = Σ_c S(1,t;cq)/(cq), so (OP) is a type II estimate for F over
  t = mn ~ q^{5/4} with factors of sizes q^{1/2}, q^{3/4}, and (OP₁) is the
  mean square of F on [1, q^{3/4}].

### Where each known technique stands on (OP)

Everything is exactly at a threshold, which is what θ = 4/7 means:

| tool | needs | has |
|---|---|---|
| completion in n (Pólya–Vinogradov) for S(m,n;cq)S(m',n;c'q) | N > q | N = q^{3/4} |
| completion in n for one modulus cq | N > (cq)^{1/2} = q^{3/4} | equal |
| q-van der Corput, shift by c in m | M > c | M = c = √q |
| completion in m for the q-part Kl_q(mn·c̄²) | M > √q | equal |
| two-dimensional completion in (m,c) mod q | MC > q | equal |
| Kowalski–Michel–Sawin (prime modulus k) | MN > k^{11/12} | MN = k^{5/6} |
| second moment tr (KKᵀ)² | saving q^{1/4+2δ} | truth saves q^{1/4} |
| Bettin–Chandee trilinear Kloosterman fractions on (T) | saving L^{1/2+δ} | L^{0.175} |

The third moment tr (KKᵀ)³ ≪ (N/q)³ q^{3/4−δ} would suffice (truth
(N/q)³q^{1/2}, Bessel (N/q)³q); it counts closed alternating 6-cycles
γ₁,…,γ₆ ∈ Γ₀(q) with γ_{2i−1}⁻¹γ_{2i} and γ_{2i}γ_{2i+1}⁻¹ of small
lower-left entry.

### (T) is a box of the ternary additive divisor problem

For the record, since it locates the barrier in the literature: (T) is the
contribution to Σ_n d₃(n) d₃(n+2) of the box where both triples have sizes
(N^{1−θ}, N^{θ/2}, N^{θ/2}).  Level θ ≤ 4/7 is the range where the box is
handled by Kloostermania; the central box (1/3,1/3,1/3)² is θ = 2/3.  A
power saving for these boxes with θ > 4/7 is progress on the ternary additive
divisor problem.

### An exact dual form of (OP₁) (paper Lemma `lem:corr`, Lean `conic_param`)

For q prime, (c,c') = (cc',q) = (h,k) = 1, k = cc'q:

    Σ_{n mod k} S(1,n;cq) S(1,n;c'q) e(hn/k)
      = k·[ e(−(c²+c'²)·h̄/k)·S(1, h̄²; q) − e(−(c²+c'²)·inv(hq)/(cc')) ].

Proved (conic c'²/X + c²/Y = −hcc' modulo q, parametrised by
t = hcc'X + c'²; the excluded point t = c'² gives the second term) and
checked numerically to 10⁻¹⁰ (scratch `corrcheck2.py`).  **The Kloosterman
sum on the right does not depend on c, c'.**  Hence, by Poisson summation,

    off-diagonal of (OP₁) ≈ (N/q²) Σ_{h ≲ q^{5/4}} S(1,h̄²;q) · Φ_h,
    Φ_h = Σ_{c≠c'} (g(c)g(c')/(cc')) ŵ(hN/(cc'q)) e(q̄·(c·inv(c') + inv(c)·c')/h).

Sizes: trivial q^{1/2}; Bessel O(1); needed q^{−1/4−δ}; random q^{−5/8}.
Note S(q̄,q̄;h)·S(h̄,h̄;q) = S(1,1;hq): the sum is S(1,1;hq) with the
summation variable z restricted, modulo h, to the ratios c/c' of two
integers of size √q, a set of density q^{−1/4} in Z/h, namely the residues ρ
for which the lattice {(a,b) : a ≡ ρb mod h} has a vector shorter than
√q (typical: √h = q^{5/8}).  Equivalently ρ/h lies within 1/h of a Farey
fraction of order √q.  Without the restriction the sum over h is a sum of
S(1,1;hq)/(hq), which Kuznetsov's formula at level q makes negligible.

Each one-variable sum is again below its threshold: c of length √q against
the modulus h ≤ q^{5/4}; h of length q^{5/4} against the modulus cc'q = q²
is long enough, and completing it returns the original sum.

### Caveat on "Bessel" for arbitrary vectors

For the smooth vector the bound S(q) ≪ L^{5+ε} is elementary (count of
pairs of matrices in one coset).  For arbitrary a, b the bound ‖a‖‖b‖ in
(OP) comes from Kuznetsov and the large sieve of Deshouillers–Iwaniec and
is clean only if Γ₀(q) has no exceptional eigenvalues; unconditionally there
is a further loss of a power of q.  The numerical spectra show no sign of
it (levels up to 16400).

### Literature check for (OP) (2026-11-16)

Nothing found that states or proves (OP) or (OP₁).  Closest:

* **Pascadi, "Non-abelian amplification and bilinear forms with Kloosterman
  sums", arXiv:2511.08445** (v2 June 2026; source read).  Bilinear forms
  Σ α_m β_n S(am,n;c) with arbitrary coefficients, composite c = dd'e,
  lengths N ≤ M ≤ c (Thm 8.x):
  ‖α‖‖β‖ c^{1+o(1)} (dM³N/c³ + fM²/c² + f/d²)^{1/6}, f² | cd.
  Saving c^{−1/12} for c = p², pq with M, N ≍ √c.  Its Corollary 1.4 /
  `cor:MN-bilinear-forms-avg-c` sums over moduli c ~ C with q | c, assuming
  only q = dd'e, **with absolute values inside the sum over c**.  In our
  ranges (C = q^{3/2}, M = q^{3/4}, N = q^{1/2}, d = s = q^{1/2} = f) both
  alternatives give the factor q^{−1/12}, i.e. q^{5/12}‖a‖‖b‖ for the sum in
  (OP) (unitarity modulus by modulus is q^{1/2}; Weil/Frobenius q^{3/8};
  Bessel 1).  No modulus-by-modulus bound can reach (OP): perfect
  orthogonality √((M+N)cq) for each modulus gives q^{1/8}.
  The paper uses these bounds for the *exceptional* spectrum large sieve
  (to enlarge the range of X in Σ X^{2θ_j}|Σ α_n ρ_j(n)|² ≪ ‖α‖²), i.e. to
  establish the Bessel-level bound unconditionally in a longer range, not to
  go below it.
  Method: Fourier analysis on SL₂(Z/c), sixth moment of singular values,
  multiplicity of large irreducible representations (the Sarnak–Xue /
  Bourgain–Gamburd device), counting solutions of congruences.  Its remark
  after Thm 8.x notes that the sixth moment is lossy for M > N and points to
  Guth–Maynard for subtracting a main term.
* Kowalski–Michel–Sawin (prime modulus): needs MN > k^{11/12}; we have
  k^{5/6}.
* Milićević–Qin–Wu (cited there as simultaneous): not read.

**Can the multiplicity device be used for (OP)?**  Worked out, negative as
it stands.  Pass to the Galois cover X(q) → X(1) through z ↦ qz; the regions
{y > 1/N}, {y > 1/M} at the cusp ∞ of X₀(q) become the full preimages of the
cusp neighbourhoods {Im > q/N = q^{1/4}}, {Im > q/M = q^{1/2}} of X(1),
which are G-invariant, G = SL₂(Z/q).  The operator Π̂ = 1·D·1 on L²(X(q))
commutes with G, the newforms of prime level q are the Steinberg part
(multiplicity q), the main term lives in the trivial part, and

    q·‖Π‖^{2k} ≤ tr_{X(q)} (Π̂Π̂*)^k − tr_{X(1)} (Π̄Π̄*)^k
              = Σ_{closed k-chains in SL₂(Z)} (|G|·1[product ≡ I mod q] − 1)·(weights).

Generic size of the right-hand side: q²M(N/q)^k, so k ≥ 7 would beat Bessel.
But the weights are products of wave kernels, which oscillate; with a
positive kernel (sphere averages) the main term returns and what is needed
is the error term of an equidistribution statement mod q for chains of
elements of SL₂(Z) of norm ~√q, to relative accuracy q^{−5/4}.  This is a
Bourgain–Gamburd-type flattening statement for a walk whose single step has
only ~q elements in a group of size q³; it is a precise question, and it is
the form in which a multiplicity argument would have to be run.

## Log, round 9 (2026-11-16): the block modulus by modulus; (OP) as a statement about SL₂(Z/q)

### Experiment 9 (`lab/kmod.c`): K = Σ_c K_c

K_c(m,n) = S(m,n;cq)/(cq).  Top eigenvalues over the mean eigenvalue of KKᵀ:

| q     | KKᵀ  | Σ_c K_cK_cᵀ | Σ_c ‖K_c‖² | max_c top(K_cK_cᵀ)/mean_c |
|-------|------|-------------|------------|---------------------------|
| 1009  | 3.36 | 1.11        | 1.82       | 2.15                      |
| 4001  | 3.46 | 1.15        | 1.88       | 2.01                      |
| 16001 | 2.58 | 1.07        | 1.69       | 1.97                      |

* Each single modulus has **perfect orthogonality with no outlier**: the top
  eigenvalue of K_cK_cᵀ is at the independent-entry edge (1+√(M/N))².
* The part diagonal in c is the identity times the mean, to 10%.
* All outliers of KKᵀ come from the cross terms c ≠ c' (the low-lying forms
  are coherent in c).

So (OP) = (OP-d) + (OP-x):

* (OP-d): Σ_c ‖K_c‖² ≪ q^{−δ}, i.e. for one modulus k = cq = c·s·s',
  rows M = k^{1/3}, columns N = k^{1/2}:  ‖(S(m,n;k))‖ ≪ k^{5/6−δ}.
  Weil/Frobenius k^{11/12}; perfect k^{3/4}.  Pascadi's Thm for composite k
  gives nothing here (third term fk³/(d²M³N³) > 1 for d = k^{1/3}, second
  term > 1 for d = k^{2/3}); KMS needs MN > k^{11/12}.  A fourth moment of
  singular values with a perfect count gives M^{1/4}√(Nk) = k^{5/6}: exactly
  the threshold.
* (OP-x): ‖Σ_{c≠c'} K_cK_c'ᵀ‖ ≪ q^{−δ}.  Closed form of each term by the
  general correlation identity below.

### The correlation identity for general rows (paper `lem:corr`, Lean `conic_param_rows`)

q prime, (c,c') = (cc',q) = (h,k) = 1, q ∤ mm', k = cc'q, A = mc'² + m'c²:

    Σ_{n mod k} S(m,n;cq) S(m',n;c'q) e(hn/k)
       = k·[ e(−A·h̄/k)·S(1, mm'h̄²; q) − e(−A·inv(hq)/(cc')) ].

Checked to 10⁻⁹ (scratch `corrcheck3.py`).  The Kloosterman sum depends on
m, m' only through mm' and not on c, c'.  After Poisson summation in m, m'
the cross term becomes a count of (c,c',h,a,B) with

    ah = c' + cu,   Bh = −c + c'v,   uv ≡ −1 (mod q),   B ≡ av (mod q),

which is the pair identity of round 3 again (uu' + 1 = Jj̃q).

### (OP) is an operator norm for a ball of SL₂(Z) acting modulo q

For M = (a,b;c,d) acting on functions on Z/q by x ↦ (ax+b)/(cx+d), and
ψ_m(x) = e(mx/q):

    ⟨ψ_n, ρ(M)ψ_m⟩ = (1/q)·e((ma+nd)·inv(c)/q)·S(mn·inv(c)², 1; q).

Summing over the φ(c) matrices M_{c,d} with lower-left entry c and
0 < a, d < c, reciprocity turns the phase into the c-part of the Kloosterman
sum, and

    Σ_d ⟨ψ_n, ρ(M_{c,d})ψ_m⟩ = (1/q)·S(m,n;cq)·(1 + O((m+n)/q)).

Hence, with T_c = Σ_d M_{c,d} and P_V the projection on frequencies ≤ V,

    **(OP)  ⟺  ‖ P_{q^{3/4}} · ρ(Σ_{c~√q} c⁻¹ T_c) · P_{√q} ‖ ≪ q^{−δ}**

on the Steinberg part of L²(P¹(Z/q)).  The sum is over the ≍ q elements of
SL₂(Z) of norm ≍ √q, with total weight √q.  Bounds: √q (triangle);
1 (temperedness of the ball operator: this is Bessel, and it is where the
automorphic spectral gap enters); q^{−1/8} (generic position of the two
bands).  P_V is the average over the unipotents T^h, |h| ≤ q/V, so the
operator is ρ(F) for

    F = 𝔸_{q^{1/4}} ∗ 𝟙_{Ball(√q)} ∗ 𝔸_{√q},   𝔸_H = H⁻¹ Σ_{|h|≤H} T^h,

an element of the group algebra of SL₂(Z/q), supported on the q^{7/4}
elements of the box 𝔅₁.  Pascadi's theorem is the same statement with the
ball replaced by the single element S (and H₁ = H₂ = √c).

Why his method does not transfer as it stands.  The trace method bounds
‖ρ(F)‖^{2k} by a (character-weighted) count of closed words of length 2k,
and the count is elementary only while the words do not fill the group:

* his case: H² = c elements per step, |G| = c³, sixth moment: c³ words;
* ours: q^{7/4} elements per step, |G| = q³: a closed word of (F*F)^k has
  q^{11k/4} choices, so only k = 1 (the Frobenius norm, q^{1/8}) is short.

For k ≥ 2 the amplified sum Σ_{g∈Γ_q(s)} N_k(g)χ(g) has no main term (χ has
no invariants on Γ_q(s)) but is governed by the *fluctuation* of the word
counts N_k(g) over residue classes, and Poisson-size fluctuation gives
‖ρ(F)‖ ≲ q^{1/2+1/(8k)}·(normalisation) — Bessel again.  The cancellation
over the ball is an archimedean fact (temperedness), the gain from the bands
is a finite-group fact, and no known argument sees both at once.

### Criticality

Every arrangement tried puts every sum exactly at its threshold: the five
variables of (T) are h ~ √L and four variables ~ L; a smooth variable of
length L against a modulus L² (Pólya–Vinogradov), two of them against L²
(two-dimensional completion), the 4th moment per modulus (above), the
second moment over c (short walk only for k = 1), q-van der Corput with
q = ss' (shift s = length).  This is the same 4/7 as the length of Conrey's
mollifier (1989), which has not been improved for Möbius-type coefficients.

## Log, round 10 (2026-11-16): is the difficulty "ball + bands"?  A model with no ball

Question posed: find one argument that sees both the cancellation over the
ball of SL₂(Z) and the gain from the two band limits.  Outcome: no such
argument found, and the question is not the right one — the band-limit gain
is already out of reach in a model where the ball is absent.

### The finite-field model (MP)

Drop the c-part of S(m,n;cq) = S(mq̄,nq̄;c)·S(1,mn·c̄²;q).  For q prime,
Kl(t) = q^{−1/2}S(1,t;q), M = C = √q, N = q^{3/4}:

    K₀(m,n) = Σ_{c~C} Kl(mn·c̄²),      T(a,b) = Σ_{m~M} Σ_{n≤N} a_m b_n K₀(m,n).

**(MP)**  T(a,b) = ±(Σ a_m η(m))(Σ b_n η(n)) + O(q^{3/4−δ}‖a‖‖b‖), η = (·/q).

Sizes for T: trivial q^{9/8}; completion q^{3/4} (this is the analogue of
Bessel); expected q^{5/8}.  There is no archimedean sum here: K₀ = P_N Λ P_M
with Λ a Fourier multiplier on the cyclic group F_q^*, symbol
λ(χ) = (τ(χ)²/√q)·Σ_c χ²(c), and P_M, P_N restrictions to the intervals.

**Experiment 10** (`lab/kmodel.c`): top eigenvalues of K₀K₀ᵀ over the mean.

| q     | top3/mean       | coeff. of η⊗η | after removing η⊗η | edge | Bessel q/N |
|-------|-----------------|---------------|--------------------|------|------------|
| 1009  | 2.26 1.74 1.68  | 0.973         | 1.82 1.74 1.69     | 2.01 | 5.6        |
| 4001  | 2.18 1.79 1.72  | 0.943         | 1.83 1.77 1.72     | 1.83 | 8.0        |
| 16001 | 2.28 1.70 1.63  | 1.054         | 1.72 1.64 1.60     | 1.68 | 11.3       |
| 64007 | 2.16 1.60 1.58  | −1.011        | 1.61 1.59 1.56     | 1.56 | 15.9       |

The mean is NC to 1%; the quadratic character enters with coefficient ±1 as
computed (χ² = 1 is the one character where Σ_c χ²(c) does not cancel); and
the rest is at the independent-entry edge to 3%.  So (MP) is true
numerically with a margin q^{1/8}, in the cleanest possible form.

### What each method gives for (MP)

* **Completion** (u = mc̄² fills F_q^*, then orthogonality of Kl(un) over u):
  q^{3/4}.  Needs only ‖a ⊛ c̄²‖² ≪ C‖a‖², i.e. few solutions of
  mc'² ≡ m'c² (mod q).
* **Hölder on the Mellin side.**  T = (q−1)⁻¹ Σ_χ λ(χ) D_a(χ̄) D_b(χ̄).  Fourth
  moments are exact for lengths ≤ √q, so ‖D_a‖₄, ‖Σ_cχ²(c)‖₄ are optimal and
  (4,4,2) gives q^{3/4} again; it cannot give less, because typical values
  have no slack — the gain must come from the phases τ(χ)².
* **Two-dimensional completion in (m,n)** after Cauchy over (m,n): q.
* **Shift c → c + rs** (the family Kl(η(c+rs)⁻²) = Kl(ηr̄²(cr̄+s)⁻²) is closed
  under it), Hölder of order 2k, complete sums of products: saving
  q^{−(k−1)/(2k²)} from q^{9/8}, best k = 2: q.  Never reaches q^{3/4}.
* **Additive form.**  With ǎ(z) = Σ a_m e(mz/q), b̌ likewise,
  T = q^{−1/2} Σ_c Σ_y b̌(y)·ǎ(1/(c²y)).
* **Reduction to balanced Kloosterman matrices.**  The excess mass of
  a ↦ P_N(·) is ⟨a, Ea⟩ with

      E = √q·Σ_{0<|d|<U} (U−|d|) Σ_{c,c'} D_{c,d} 𝒦_{cc'd} D_{c',d},   U = q/N,

  D_{c,d} = diag(e(−m c̄² d̄/q)), 𝒦_ξ = (Kl(mm'ξ̄²))_{m,m'~√q}.  𝒦_ξ is exactly
  the balanced √q × √q matrix of Kowalski–Michel–Sawin and Pascadi.  Needed:
  ‖E‖ ≪ q^{2−δ}; Bessel: q².  Even *perfect* orthogonality ‖𝒦_ξ‖ ≈ q^{1/4}
  with the triangle inequality over the q^{5/4} twists (c,c',d) gives
  q^{9/4}.  So (MP) needs cancellation between the twists of size q^{1/4+δ}
  on top of the best conceivable bound for each.

### Consequences for the question

1. The obstruction is not the coexistence of an archimedean and a finite
   mechanism.  (MP) has only the finite one and is stuck at the same place,
   by the same factor q^{1/4} = q/N.
2. In the regular representation ℓ²(SL₂(Z)) the bound we want to beat is
   sharp: Σ_{|h|≤H} T^h has norm H there (Z is amenable), so
   ‖𝔸_{H₁} 𝟙_Ball 𝔸_{H₂}‖ ≍ H₁H₂√q.  The gain exists only because the bands
   have dimension < q.  Hence no argument valid for all tempered
   representations (Haagerup/rapid decay, Herz majorisation) can give it.
   (On SL₂(R) Cowling–Haagerup–Howe would give full square-root cancellation
   |𝔅₁|^{1/2} for the sector; the transfer to the lattice fails for thin
   sectors, and the numerics show the lattice norm is q^{9/8}, not q^{7/8}.)
3. What is needed is an uncertainty principle of the following kind: an
   M-dimensional and an N-dimensional space of band-limited functions on
   Z/q, M + N < q, are in general position after a multiplicative
   convolution (in (MP)) or after the ball of SL₂(Z) (in (OP)).  For one
   group element this is the KMS/Pascadi problem, where the known savings
   are q^{−1/64} and q^{−1/12} at M = N = √q and nothing at
   (√q, q^{3/4}).  Here the single element is replaced by a sum of √q
   (model) or q (ball) elements and the saving must survive the sum.

## Log, round 11 (2026-11-16): attempts on the model (MP); the smooth vector as a four-variable congruence

No proof.  Recorded: what was tried, one heuristic that was wrong, and the
most concrete form reached.

### The smooth vector in the model is a congruence in four variables of size √q

For smooth a the functional equation of Σ_m w(m/M)χ̄(m) absorbs one Gauss
sum, and Σ_{m,c} Kl(nm·c̄²) ≈ Σ_{x,c ~ √q} e(n·inv(xc²)/q).  So the model
analogue of (LS) is about the q points z = inv(xc²) of Z/q (mean spacing
1), and with X = xc², X' = x'c'²:

    N_t := #{(x,c,x',c') : inv(X) − inv(X') ≡ t (mod q)}
         = #{(1 − tX)(1 + tX') ≡ 1 (mod q)},

and over Z:  (1 − tX)(1 + tX') = 1 + t·j·q  with j ≍ tq².

**Model-(LS) ⟺ N_t = q(1 + O(q^{−δ})) on average over 0 < |t| ≤ q^{1/4}.**
Trivial: N_t ≤ N_0 ≍ q (this is Bessel).  Expected: N_t = q + O(q^{1/2+ε}).
So what is missing is *any* power saving in an asymptotic count for a
polynomial congruence in four smooth variables in a box of side exactly √q.
Variant B (xy in place of xc²): N_t = #{a₁a₂ − a₃a₄ = t : a_i ∈ I⁻¹},
I = [√q, 2√q): a sum–product equation at the critical cardinality √q
(Vinh's incidence bound needs |A| > q^{3/4}); also
N_t = Σ_P d_I(P)·d_I(P/(1−tP) mod q), the divisor function correlated with
itself along a Möbius map modulo q, and (tP−1)(tP'+1) = tqj − 1 over Z.

**Experiment 11** (`lab/mcorr.c`): ν(z) = number of representations.

| q        | model | Var/mean | max |Cov(t)|/mean, t ≤ 64 | windows U=q^{1/4}: Var/(U·mean) | if fully correlated |
|----------|-------|----------|--------------------------|----------------------------------|---------------------|
| 10⁵+3    | A     | 1.004    | 0.006                    | 1.049                            | 17.1                |
| 10⁶+3    | A     | 1.020    | 0.001                    | 1.020                            | 31.6                |
| 10⁷+19   | A     | 1.029    | < 0.0005                 | 1.029                            | 57.6                |
| 10⁷+19   | B     | 2.932    | 0.002                    | 2.934                            | 164.2               |

The shift covariances vanish to within noise at every shift (no 1/|t|
law here, unlike the coset picture of round 7 where shifted boxes
overlap).  Var/mean ≈ 1 in A; in B it grows like log q (xy = x'y').

### Tried and failed (in addition to round 10)

* **Trace method / amplifier of Pascadi** for the model operator
  𝔸_{q^{1/4}}·w·(Σ_c t_c)·𝔸_{√q}: q^{5/4} elements per step.  Unamplified
  2k-th moment gives ‖·‖ ≲ q^{5/4−1/(2k)} at best (k = 3: q^{13/12}), Bessel
  is q.  With q = ss' and the amplifier Γ_q(s), bounding |χ| ≤ 1 gives
  q^{5/4−1/(4k)}; the gain needs the signs of χ on word counts, i.e.
  equidistribution with error term — only k = 1 is elementary.
* **Type I shift with ℓ¹ in μ = mn**: redone with the safe count q^{3/2} for
  the complete sums: q^{9/8−(k−1)/(4k²)}, best q^{17/16}.  Cannot reach q^{3/4}
  because it discards the orthogonality in (m,n).
* **Voronoi heuristic (wrong).**  For variant B I argued ιD ≈ F D for the
  divisor vector D, which would give N_t ≈ Σ_P d(P)² e(tP/q) ≍ q/|t| and a
  full saving.  Voronoi says F D ≈ ι₋ F D̃ (the *transform* is ι-invariant),
  not that; the three Voronoi steps compose to the identity.  Experiment 11
  refutes the 1/|t| law directly.  Recorded so that it is not tried again.
* **Fouvry–Kowalski–Michel bound** Σ_P d(P)K(P) ≪ q^{7/8} applies to
  f(u) = Σ_P d(P) e(u·inv(P)/q) pointwise, but the mean square of f is q,
  so a pointwise q^{7/8} says nothing about the flatness of |f|² at scale
  q^{3/4}, which is what N_t measures.
* **Pair correlation of Kl₃**: f(u) = Σ_{j,j'~√q} Kl₃(ujj'), and for t ≠ 0
  every correlation Σ_u Kl₃(αu) Kl₃(βu)‾ e(−tu/q) is ≪ √q by Deligne, with
  no diagonal.  There are q² of them: q^{5/2} against the needed o(q²).
  Deligne term by term loses √q to Bessel.

### Where this leaves the search

All transformations (Poisson, Voronoi, reciprocity, Kuznetsov, Mellin) are
identities that return the same sum; the only inequalities in play are
positivity (Bessel), Deligne term by term, Hölder with moments, and
counting short words, and each has been run to its end on the model.  A
proof needs an inequality not on this list.

### Two partial facts worth keeping

* For the smooth vector in variant B, the pointwise bound of
  Fouvry–Kowalski–Michel, f(n) ≪ q^{7/8+ε}, does beat Bessel for the mass on
  [1,N] when N ≤ q^{1/4−ε} (windows U ≥ q^{3/4+ε}): N·q^{7/4} < q².  The
  range needed is N = q^{3/4}.  A pointwise bound f(n) ≪ q^{5/8−δ} would
  suffice; that is stronger than the Weyl-type exponent (it corresponds to
  L(½,χ) ≪ q^{1/16}), so the pointwise route is closed and the mean-square
  route is the only one.
* In the true problem the ratio (frequency range)/(level) is forced:
  the Cauchy–Schwarz that removes the divisor weight creates the level
  q = ss' and N₀/q = H/L = q^{−1/4}.  The other arrangements (Cauchy over d
  alone, or over (r,s,d)) are worse.

## Log, round 12 (2026-11-16): search for an inequality outside the list

### A new sufficient condition: the complete fourth moment (E4)

Let ν be the counting function on Z/q (coset counts ν₃ in the true problem,
representation numbers of the model point set otherwise), P = Σν, and
C(λ) = Σ_x ν(x)ν(x+λ) for λ ∈ Z/q.  (LS) is a bound for
Σ_{|t|≤U} (1−|t|/U)(C(t) − P²/q), U = q^{1/4}.  Cauchy–Schwarz over the
shifts, extended to *all* λ:

    |Σ_{|t|≤U} w_t (C(t) − P²/q)|  ≤  U^{1/2} · ( Σ_{λ≠0 mod q} (C(λ) − P²/q)² )^{1/2}.

**(E4)**  Σ_{λ≠0 mod q} (C(λ) − P²/q)² ≪ q^{1/4−δ} · P²·(Var/mean)².

(E4) ⇒ (LS).  The left side is the additive energy of ν minus its main
term, = q⁻¹ Σ_{ψ≠0} |ν̂(ψ)|⁴.  Independent points give ≈ P²; the trivial bound
is q·P².  So what is needed is a fourth moment of ν̂ over the **complete**
range of frequencies within q^{1/4} of flat.  No short interval occurs: the
thresholds of rounds 8–11 (sums of length √modulus) do not appear in the
statement.  This is the only genuinely different inequality found: "flatness
in L⁴ over all frequencies ⇒ no concentration on q^{3/4} of them" (with 2k-th
moments the same argument gives the full saving as k → ∞).

**Experiment 12** (`lab/e4.c`): F = Σ_{λ≠0}(N_λ − P²/q)²/P².

| q     | model A: F | max_λ |N_λ−mean|/√mean | model B: F | allowed q^{1/4} | trivial q |
|-------|------------|-------------------------|------------|-----------------|-----------|
| 5003  | 0.952      | 3.77                    | 3.57       | 8.4             | 5003      |
| 20011 | 0.960      | 3.73                    | 4.21       | 11.9            | 20011     |
| 60013 | 1.037      | 4.23                    | 4.94       | 15.7            | 60013     |

In model A the fourth moment is exactly Poisson, and *every* shift λ mod q
has square-root fluctuation (max ≈ √(2 log q)).  In model B, F ≈ (Var/mean)².

Equivalent forms of (E4), model B, A = I⁻¹ (reciprocals of [√q, 2√q)):

* additive energy of the product set: #{a₁b₁ + a₂b₂ = a₃b₃ + a₄b₄, a_i,b_i ∈ A}
  = q³ + O(q^{9/4−δ}); this is the dot-product energy of A² ⊂ F_q²;
* mean square over characters ψ mod q of the four-variable sum
  Σ_{x,y,x',y'∈I} ψ(xyx'y') ψ̄(xy + x'y') is ≪ q^{2+1/4−δ} (each is ≤ q²;
  square-root size is q);
* ‖f‖₄ within q^{1/16} of ‖f‖₂-flat for f(u) = Σ_{x,y} e(u·inv(xy)/q).

Status of (E4): not proved.  Pointwise f ≪ q^{7/8} (Fouvry–Kowalski–Michel)
gives Σ|f|⁴ ≪ q^{15/4}; needed q^{13/4−δ}.  Deligne on the complete sum over
u of four Kl₃'s gives the diagonal exactly (2q², the Poisson value) but an
error q^{7/2} from the q⁴ unpaired terms.  Completing all eight variables is
self-dual.  Rudnev-type energy bounds (|A|⁸/q + |A|^{13/2}) are vacuous at
|A| = √q because A·A already fills F_q.  The single-variable ancestor is the
additive energy of reciprocals of an interval of length √q (Heath-Brown,
Bourgain–Garaev: ≪ q^{5/4}; expected q^{1+ε}).

### Other formulations reached this round

* **Farey / adelic large sieve.**  G_q(n) depends only on the rational n/q:
  G_q(n) = Σ_{d,r} e(−2·(n·inv(q) mod d)·inv(r)/d).  So
  Σ_q S(q) = Σ_{ρ=n/q} |μ̂(ρ)|², the Fourier transform (on Ẑ, the dual of
  Q/Z) of the measure μ = Σ δ_{inv(r)/d} at all rationals of height
  (N₀,Q) near 0.  Matrix form: E = (e(−2n·inv(rq)/d)) with rows (n,q),
  columns (r,d); ‖E‖² ≤ L⁴ by completion, L^{3.5} expected; the Gram matrix of
  rows is the divisor matrix d_{L²}(nq' − n'q) of Farey determinants.
* **Cubic moment.**  (T) is the error term in
  Σ_{d=n₁n₂} Σ_{χ mod d} χ̄(2) D_B(χ)D_L(χ)D_L(χ) with lengths
  (d^{3/4}, d^{1/2}, d^{1/2}); after the functional equation of the long
  factor, W = Σ_d τ(d) Σ_{h~d^{1/4}} f_d(2h), f_d(u) = Σ_{r,s~√d} e(u·inv(rs)/d).
  So (T) ⟸ |f_d(2h)| ≪ d^{3/4−δ} on average over d = n₁n₂ and h ≤ d^{1/4}.
  FKM gives d^{7/8} for one prime d; Deshouillers–Iwaniec gives d^{3/4} on
  average: 4/7 is "FKM exponent 1/4 on average", and more than 1/4 is needed.
* **Variance of a divisor count.**  (T) ≈ Σ_m d₃(m)·ω_L(m−2)², ω_L(k) = number
  of divisors of k in [L,2L): the Turán–Kubilius variance of ω_L(m−2) under
  the measure d₃, with L² = N^{4/7}.
* **Helson matrix / Bohr lift.**  K(m,n) = F(mn).  On T^∞ all L^p norms of a
  Dirichlet polynomial are ≍ its ℓ² norm, so Hölder gives
  ‖K‖ ≤ q^ε‖Φ_F‖_{1+η}, which is at best the Frobenius bound: the form with
  shape (1, MN) is a valid test and has norm q^{1/8}.

### Errors caught this round (do not repeat)

* "τ(χ̄)L(½,χ̄)² ≈ √d·|L(½,χ)|²", which would turn f_d(u) into the twisted
  second moment with its reciprocity formula and give f_d(u) ≍ √(d/u) log d.
  Wrong by one complex conjugation: f_d(u) = φ⁻¹ Σ_χ χ̄(u) τ(χ) D(χ)², and the
  functional equation absorbs τ(χ̄), not τ(χ); what remains is τ(χ)³, i.e.
  Kl₃.  There is no diagonal main term (the zero frequencies vanish).
* Strong convergence / temperedness arguments: in ℓ²(SL₂(Z)) the bound to be
  beaten is attained, so no statement valid in the regular representation
  helps (already in round 10; re-derived via Haagerup-type inequalities).

### (E4) on the multiplicative side

Let φ(u) = |f(u)|² = |ν̂(u)|² on F_q^* and E(a) = Σ_u φ(u)φ(au), a positive
definite function on the group F_q^*.  Exactly (Parseval twice, or Schur
orthogonality for the affine group acting on mean-zero functions):

    Σ_{a ∈ F_q^*} E(a) = (Σ_u φ(u))².

(E4) says E(1) ≤ q^{1/4−δ} × the average of E(a) over all dilations a: the
autocorrelation of the mass distribution |ν̂|² under dilations is not peaked
at a = 1 by more than q^{1/4}.  (For Gaussian-like ν̂ the ratio is 2.)  With
the Mellin transform φ̂(χ) = Σ_u φ(u)χ(u): E(1) = (q−1)⁻¹ Σ_χ |φ̂(χ)|², and for
χ ≠ χ₀, in model B,

    φ̂(χ) = τ(χ)·W(χ),   W(χ) = Σ_{x,y,x',y' ∈ I} χ(xyx'y') χ̄(x'y' − xy)
                               = Σ_{z,z' ∈ 𝒵} χ̄(z − z') = Σ_λ N_λ χ̄(λ).

So **(E4) ⟺ Σ_{χ≠χ₀} |W(χ)|² ≪ q^{13/4−δ}**, and it would follow from the
pointwise bound W(χ) ≪ q^{9/8−δ} for every χ ≠ χ₀: a four-variable
multiplicative character sum over a box of side √q (q² terms; square-root
size q).  What is provable: W(χ) ≪ q^{3/2} (Thue covering of F_q by the
ratios k/x', orthogonality over the covered variable, Cauchy–Schwarz) — this
is Bessel again in the new coordinates.  Missing: a further q^{3/8+δ}.

Duality worth noting: (LS) is a bound for the *additive* twists
Σ_u |f(u)|² e(tu/q) with |t| ≤ q^{1/4}, needing any power saving; (E4) is a
bound for all the *multiplicative* twists Σ_u |f(u)|² χ(u), needing q^{3/8+δ}
in mean square.  For a quadratic form Q in four variables the transform of
χ∘Q is χ̄∘Q* (exact, Gauss sums), so sums of χ(x'y' − xy) over a box of side H
have a functional equation H ↔ q/H; the box of side √q is its centre.

**Experiment 13** (`lab/wchi.c`): W(χ) = Σ_{λ≠0} (N_λ − mean) χ(λ) for all q−2
nontrivial characters.

| q     | model | rms |W(χ)|/q | max_χ |W(χ)|/q | elementary bound √q | needed q^{1/8} |
|-------|-------|--------------|-----------------|---------------------|----------------|
| 5003  | A     | 0.956        | 3.85            | 70.7                | 2.90           |
| 20011 | A     | 0.973        | 4.45            | 141.5               | 3.45           |
| 5003  | B     | 1.851        | 8.16            | 70.7                | 2.90           |
| 20011 | B     | 2.039        | 9.30            | 141.5               | 3.45           |

Square-root size in mean square and, up to √(log q), for every character.
So the clean conjecture behind (E4) is pointwise:

    **W(χ) = Σ_{x,y,x',y' ∈ I} χ(xyx'y') χ̄(x'y' − xy) ≪ q^{1+ε} for all χ ≠ χ₀**,

a sum of q² terms at the centre of its functional equation; q^{9/8−δ} in
mean square would suffice for the model analogue of (LS), q^{3/2} is known.
In terms of L-values (functional equation of the sums of length √q):

    W(χ) ≈ τ(χ) q^{−3/2} Σ_θ conj J(θ,χ) · D(θχ̄)² · conj D(θ)²,   D(θ) = Σ_{x∈I} θ(x),

a fourth-moment-type sum over characters θ in which the two factors sit at θ
and θχ̄ and are tied by the Jacobi sum J(θ,χ).  For χ = χ₀ this is the
fourth moment of Dirichlet L-functions (asymptotic known, Young 2011, by
Kloostermania on the shifted divisor problem modulo q).  The case χ ≠ χ₀ asks
for cancellation in a *shifted, Jacobi-twisted* fourth moment.

## Log, round 13 (2026-11-16): what the threshold consists of; three reformulations

No proof.  Three reformulations and one literature check, each of which
changes what a proof has to do.

### 1. The model is the ternary divisor function in one class, at level 4/7

For q prime, I = [√q, 2√q), J an interval of length q^{3/4}:

    Σ_{0<|t|≤q^{1/4}} |ν̂(t)|² ≪ q^{2−δ}
      ⟺  #{(x,y,b) ∈ I×I×J : xyb ≡ 1 (q)} = |I|²|J|/q + O(q^{3/4−δ})
          in mean square over the position of J.

Total length q^{7/4}, modulus q = (length)^{4/7}: the same exponent as the
real problem, and the box (2/7, 2/7, 3/7).  In multiplicative characters

    error = (1/φ(q)) Σ_{χ≠χ₀} S_I(χ)² S_J(χ).

Cauchy–Schwarz with the two exact moments (Σ|S_I|⁴ = φ·E_×(I) ≍ q² log,
Σ|S_J|² = φ|J|) gives q^{7/8} for every J.  Every other route gives the
same number: FKM for Σ d(a)K(a) (saving q^{1/8}), Hölder with the
conjectural reciprocal energy J₂(√q) ≪ q^{1+ε}, the Pólya–Vinogradov
bilinear bound.  In mean square over J, Bessel gives q^{3/4} = main term.

By Mellin inversion the error is q^{−1/8} × (a Fourier coefficient, at
frequency ≍ log q in the shifts, of the cubic moment
Σ_χ L(½+iu₁,χ)L(½+iu₂,χ)L(½+iv,χ)).

Literature (checked): Zacharias, arXiv:1706.04888, Thm 1.3:
(1/(q−1)) Σ_χ L(χ,½)L(χω₁,½)L(χω₂,½)χ(ℓ) = δ_{ℓ=1} + O(q^{−1/64+ε}).
Its critical box is (½,½,½), where only an upper bound q^{3/4−η} for the
error of a count with main term q^{1/2} is needed.  The model needs the
error below the main term in the box (½,½,¾).  So the model is strictly
beyond what the cubic moment literature proves.

Over F_p[t] with p large the analogue should follow from Sawin's
square-root cancellation for factorization functions in progressions to
squarefree moduli (cited from memory; statement and range NOT re-checked):
intervals are affine subspaces there.  If so it is evidence for the truth
of (LS); the method does not transfer.  The FKM exponent 1/8 for
Σ d(a)K(a) is also quoted from memory.

### 2. (LS) is a non-concentration statement on the Bohr set

In the level-q spectral space with weights ω_f let λ(n) = (λ_f(n))_f,
ℓ_X = (X^{2it_f} L(½+it_f, f))_f and M₁(n) = ⟨ℓ_X, λ(n)⟩.  Then

* Bessel: Σ_{n≤N} |M₁(n)|² ≤ ‖ℓ_X‖² ≪ log q for N ≤ q.  For N = q^{3/4}
  the rms is q^{−3/8}, far below the q^{−1/4−δ} that is needed.
* The n that occur are the Bohr set B_q = {hs'−h's}, of size √q, density
  q^{−1/4} in [1, q^{3/4}].  Worst case all the mass sits on B_q: rms
  q^{−1/4}.  That is the threshold.

So: **needed is only that |M₁|² does not put all of its mass on a set of
density q^{−1/4}** defined by congruences modulo the two factors s, s' of
the level.  Without the twist X^{2it_f} the vector ℓ lies in
span{λ(m) : m ≤ q^{1/2+ε}} and M₁(n) = n^{−1/2}; the statement is about the
rotation U_X = diag(X^{2it_f}), whose matrix in the basis λ(·) is the
Kloosterman block.  Perfect entrywise bounds (Linnik–Selberg strength,
q^{−1/2} per entry) give exactly the threshold again: after square-root
cancellation in c for each (m,n), any cancellation in the smooth m-sum
would suffice; after Weil in k, full square-root cancellation in c plus δ
is needed.

Equivalent Gram form: v_{s,h}(r,d) = e(2h·inv(d)/(rs)), R_s = span_h v_{s,h}
(dimension √L inside C^{L³}).  (LS*) ⟸ ‖Σ_s P_{R_s}‖ ≤ L^{1/2−δ}.
Trivial: L.  Truth: ≈ 1.  Schur's test needs the first moment
Σ_{s',h'} |G_{ss'}(hs'−h's)| ≪ L^{3.5−δ} for fixed (s,h); Cotlar–Stein
loses a square root and is useless even with perfect entries.

### 3. A by-product: average over the shift (not checked line by line)

For shift k the frequencies are k·B_q.  The sets k·B_q, k ~ K₀, are
disjoint up to divisor multiplicity and lie in [1, K₀q^{3/4}], where Bessel
still costs nothing while K₀ ≤ q^{1/4}.  Hence

    Σ_{k~K₀} Σ_{n∈B_q} |G_q(kn)|² ≪ q^ε · (Bessel bound),

a saving K₀^{−1/2} per shift on average.  So at θ = 4/7 the count (T) has a
power saving for almost all shifts k in any window [K₀, 2K₀], K₀ ≥ x^ε,
and for θ slightly above 4/7 in windows of length x^{O(θ−4/7)}.  The shift
acts on ℓ_X as the Hecke operator T_k.  It does not give the fixed shift 2:
the identity T_p² − T_{p²} = 1 returns M₁(n) itself, and the dilation
(b,a) → (kb,ka) reproduces the same Gram form with a unimodular twist.

### 4. Checked and closed this round

* Fixed modulus d (statement (FM): variance over r ≤ √d of the divisor
  function modulo d at length d^{5/4}): Pólya–Vinogradov gives d^{7/4},
  needed d^{3/2−δ}.  Off threshold by d^{1/4}; the threshold in the real
  problem uses the average over d.  Not a route.
* Incomplete Kloosterman sums of length k^{2/3} to moduli k = r·s·s':
  every q-van der Corput exponent pair returns k^{1/2} (Weil) at this
  length.
* KMS bilinear bounds at (√q, q^{3/4}): weaker than Pólya–Vinogradov there
  (q^{−1/16} against q^{−1/8}); they only help for MN < q.
* Burgess for S_I(χ) (q^{7/16} pointwise) does not enter: all moments in
  the Hölder step are already saturated by typical characters.
* Bettin–Chandee on the symmetric form Σ e(2h·inv(xy)/(n₁n₂)): saving
  L^{0.175}, as in round 8.

## Log, round 14 (2026-11-16): the non-concentration form, taken apart

No proof.  The Bohr-set statement of round 13 reduces to three smaller
targets, each checked numerically (Experiment 14) and each at threshold
for a different reason.

### The Bohr set is a union of √L progressions modulo s

For |n| ≤ N = HL the second congruence is automatic:

    B_q = { n ≤ N : n ≡ h·s' (mod s) for some h ~ H },

H progressions of √L terms each, out of s ~ L residue classes.  With
m(a) = Σ_{n≡a (s)} |G_q(n)|² and m̂(k) = Σ_n |G_q(n)|² e(−kn/s):

    Σ_{n∈B} |G_q(n)|² = (H/s)·[ m̂(0) + Σ_{0<|w|≤√L} c_w m̂(w·inv_s(s')) ].

The w = 0 term is the fair share.  **Needed: the √L twisted masses
m̂(w·inv_s(s')) are ≤ L^{−δ} m̂(0) on average.**  m̂(k) is N times the
pair-correlation fluctuation of the point set
X_q = {2·inv_{rq}(d)/r} ⊂ R/qZ at the lag k·s' = w·e', e' ≡ 1 (s), ≡ 0 (s'),
with tolerance √L.  Positive-definiteness gives |m̂(k)| ≤ m̂(0), which is the
threshold, and it points the wrong way: for a positive-definite function
the origin is where concentration is natural.

Translation by e' acts on d by the unipotent map d ↦ d/(1 + inv(2)·r·d)
modulo s and the identity modulo rs'.  The full orbit set (all d mod rq) is
invariant; X_q is the 1/L-subsample with d in an interval.  Exact
coincidences z' = z + w·e' inside X_q (same r) are the roots of
w·d² + j·r·s'·w·d + 2j·s' ≡ 0 (mod s), j = ±1: about L per (r, w).

### Three sufficient statements, weaker than (LS) in different directions

(M4)  Σ_{0<|n|≤N} |G_q(n)|⁴ ≪ L^{9−δ}.  No Bohr set.  By Cauchy–Schwarz it
      gives (LS).  Equivalent: the mass of |M₁|² is spread over at least
      q^{1/2+δ} values of n (the Bohr set has exactly q^{1/2}).  Known:
      L^{10} (Weil pointwise × Bessel).  Truth: L^{7.5}.  It asks for more
      saving than (LS), so it is not a shortcut.

(R)   The H×H block M = [G_q(hs'−h's)] satisfies ‖M‖_op ≤ L^{−δ}·L^{2.5}.
      Bessel gives ‖M‖_HS ≤ L^{2.5}, so (R) holds unless M is essentially
      of rank one at the Bessel size.  (R) for all pairs gives
      ‖Σ_s P_{R_s}‖ ≤ L^{1/2−δ} by Schur's test, i.e. (LS*).  Rank one
      would need G_q(n) and G_q(n + k·s') perfectly correlated along the
      progression n ≡ hs' (s), for all k ≤ H.

(S)   The smooth matrix element 1ᵀM1 — the first moment of G over the Bohr
      set — which is all that (T) itself uses.

### Experiment 14 (`lab/blockrank.c`)

| L | H | ‖M‖²_op/‖M‖²_HS (random) | mean\|G\|²/P on block | kurtosis, all n | twisted mass avg (N^{−1/2}) |
|---|---|---|---|---|---|
| 30  | 5  | 0.510 (0.515) | 0.99 | 1.99 | 0.048 (0.058) |
| 60  | 7  | 0.397 (0.420) | 1.04 | 1.99 | 0.031 (0.035) |
| 120 | 10 | 0.323 (0.310) | 0.96 | 2.02 | 0.018 (0.020) |
| 200 | 14 | 0.221 (0.225) | 0.97 | 2.03 | 0.012 (0.013) |

(6, 6, 6, 3 pairs.)  The block has the singular-value profile of a random
complex matrix, the kurtosis of a complex Gaussian (2), and twisted masses
at the size N^{−1/2} of pure noise.  Small sizes; consistent with all of
(M4), (R), (S) holding with full margin.

### Why none of these is soft

* Hooley's conjecture R* (square-root cancellation in each incomplete
  Kloosterman sum over d) gives |G_q(n)| ≪ L^{2+ε}: exactly the threshold.
  A proof needs R*-strength in d *and* cancellation over r.
* For arbitrary coefficient vectors the vectors λ(n), n ∈ B, are
  orthonormal, so no large sieve restricted to the Bohr set can gain.  The
  gain must use the specific vector ℓ_X.
* Additive twists by k/s (s | level) of Rankin–Selberg sums: conductor
  s⁴s'² = q³, sum length q^{3/4}.  No orthogonality term by term.
* Voronoi at the cusp 1/s (conductor s²s' = N², self-dual length) turns a
  progression sum modulo s into a Kloosterman transform modulo s of the
  sequence twisted by the Atkin–Lehner sign η_f(s').  The finite Hankel
  transform is Fourier ∘ inversion ∘ Fourier, so the Bohr mass becomes the
  correlation of additive-twist sums at u and u/(1+tu), |t| ≤ √s.  This is
  the unipotent-shift form (Y) of round 7 again.
* The dispersion index j = (a'−a)/r ≤ √L appears as the denominator of
  additive twists coprime to the level, i.e. as characters χ mod j:
  the variance is a mixed moment Σ_f η_f(s') L(½,f) L(½,f⊗χ), conductor
  q^{5/2}, between the second and fourth moments in the level aspect.  For
  analytic spectral weights the Kloosterman side is dominated by moduli
  c·q with c ≍ 1 (this is why the fourth moment in the level aspect is
  known); our weight X^{2it} selects c ≍ √q and only the Maass spectrum
  with t_f ≪ 1 contributes.
* GL(2) level reciprocity does not shrink the family: every grouping of
  b·r·s − a·n₁·n₂ = 2 has level L².

### Positions

Most concrete open target after this round: decorrelation of G_q(n) and
G_q(n + k·s') along n ≡ hs' (mod s) (statement (R)), equivalently the pair
correlation of X_q at the lags w·e'.
