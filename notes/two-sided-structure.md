# Using the Möbius structure of both d and e: feasibility study (2026-11-15)

Status: exploratory, AI-generated (Claude), not checked by a human.  Exponent
bookkeeping only; no hypothesis of the cited estimates has been verified in
detail.  Sizes are exponents of x (the paper's N).

## Setting

After Poisson summation, Theorem 1.2 at level θ (d, e ~ x^θ) needs

    T = Σ_{h ~ H} Σ_d α_d Σ_e λ_e e(2h d̄/e) ≪ x^{2θ-δ},   H = x^{2θ-1}.

Literature bar: Conrey's method (Deshouillers–Iwaniec, coefficients on e and
h arbitrary) gives θ < 4/7.  It is uniform in the shift, so it also serves
the mollifier problem.

## Observation 1: a fixed shift is a fixed residue class

Our sum is `Σ_e λ_e ( #{n = a·d ≤ x : n ≡ -2 (e)} − expected )` with `a`
smooth of length x^{1-θ}.  This is the Bombieri–Friedlander–Iwaniec setting
(fixed residue, factorable moduli).  Those estimates are *not* uniform in the
residue, which is why they are unavailable for mollifiers.

## Observation 2: one flexible side suffices

Cauchy–Schwarz over (d, r) with e = r·s, then Deshouillers–Iwaniec Theorem 12
with c = r, d_DI = d (whole, arbitrary coefficients), s_DI = s s',
n = h s' − h' s.  Conditions (general form: Poisson variable of size p,
modulus of size ϑ, H = x^{ϑ-p}):

    s ≥ ϑ − p                      (diagonal)
    s ≤ 3p − ϑ,  s ≤ (1 + p − ϑ)/3  (regular spectrum)
    s ≤ 2 − 3θ  (exceptional-spectrum term of DI; removed by Pascadi's
                 refinement for structured sequences, arXiv:2505.00653)

For p = 1−θ, ϑ = θ the window for the factor s is

    W_θ = [2θ − 1, min(2(1−θ)/3, 2 − 3θ)],

nonempty for θ < 3/5 (θ < 5/8 with Pascadi's bound).  At θ = 4/7 it is
[1/7, 2/7].  So: if the modulus weight is a combination of products r·s with
s ∈ W_θ, the level is 3/5 (5/8) for **arbitrary** coefficients on d.  By the
symmetry be − ad = 2 the same holds with the roles of d and e swapped.  This
matches Maynard (arXiv:2006.07088, Prop. 5.1/8.3: level 3/5 for triply
well-factorable weights) and Pascadi (5/8).

## Observation 3: what is left is a divisor problem

Heath-Brown's identity writes μ(e) as a combination of products of very short
Möbius factors (flexible) and smooth variables.  A piece is good if some
sub-product lies in W_θ, or if it has a smooth factor of length
≥ x^{5θ/2-1} (Weil, roles swapped).  The bad pieces are, up to tiny twists,

    e = ℓ₁ℓ₂, both smooth, sizes within O(θ − 4/7) of (θ/2, θ/2),
    e = ℓ₁ℓ₂, sizes within O(θ − 4/7) of (1−θ, 2θ−1),

and μ contains the first with coefficient exactly +1 (ordered factorizations).
Bad × bad is unavoidable.  There all six variables are smooth:

    #{ b ℓ₁ ℓ₂ − a n₁ n₂ = 2 },  a, b ~ x^{1-θ},  n_i, ℓ_i ~ x^{θ/2},

a restricted case of the additive divisor problem for τ₃ × τ₃, box
(3/7, 2/7, 2/7)² at θ = 4/7.  Checked against this box, all failing for
θ > 4/7 by a margin linear in θ − 4/7:

* DI Theorem 12 directly, every assignment (scratch `two/di12.py`);
* Cauchy–Schwarz + DI in every arrangement tried (both the J₁ and J₂ terms
  are tight at 4/7; Pascadi's refinement removes only J₂);
* Maynard's and Pascadi's convolution estimates with every partition of
  {ℓ₁, ℓ₂} into three groups;
* Pascadi's triple-convolution estimate (needs D ≥ E·x^ε; fails at D ≍ E);
* Irving's Type II bound (worse: 8/15 at the balanced point);
* Polymath8a's Type III argument (arXiv:1402.0811, §8 sketch): complete all
  three variables to get Kl₃(2h₁h₂h₃; q), factor q = rs, Cauchy–Schwarz in
  h, Deligne for the correlation sums.  With Q = x^θ and H = Q³/x the two
  conditions are `R > Q⁴/x²` (diagonal) and `R < x²/Q³` (off-diagonal),
  i.e. R ∈ [4θ−2, 2−3θ], nonempty iff θ ≤ 4/7.  At θ = 4/7 the window is
  the single point R = S = x^{2/7}, which is exactly our factorization
  q = ℓ₁ℓ₂.  This is an algebraic proof of the same exponent; it uses
  neither the shape of the box nor smooth averaging over r and s.  Checked
  from the paper's model computation only, not its rigorous theorem.

The mixed case (balanced) × (1−θ, 2θ−1) is a τ₃ × τ₂ problem with a linear
twist of size x^{1/7}; (1−θ, 2θ−1)² is a quadratic divisor problem with
coefficients x^{1/7} and may be within reach of existing spectral results.

## Conclusion

* Unconditionally, for the true Λ_R: no improvement on 4/7 by this route.
  Passing 4/7 is equivalent, as far as this analysis goes, to asymptotics for
  τ₃ × τ₃ correlations in the box above, which appears to be open.
* Conditionally on those divisor asymptotics: level 3/5 (5/8).
* Unconditionally, for weights with no bad pieces on at least one side (for
  example truncated divisor sums over x^σ-smooth divisors, or well-factorable
  sieve weights on one side): level 3/5 (5/8) should follow from the
  published estimates.  Not checked in detail.

## Sources read (arXiv TeX)

Maynard, Primes in APs to large moduli II (2006.07088): Prop. 8.3 conditions
`Q₁ < N`, `N²Q₂Q₃² < x`, `N²Q₁Q₂⁴Q₃³ < x²`, `NQ₁Q₂⁵Q₃² < x²`; DI Thm 12 as
Lemma 6.7.  Pascadi (2505.00653): Prop. 5.3 (`N²Q₂Q₃² ≤ x`,
`N²Q₂⁵Q₃² ≤ x²`), Prop. 6.3 (triple convolution), Prop. 3.6 (incomplete
Kloosterman sums, I² = D²NR + (1 + C²/(R²SY))^{θ} CS(C+DR)(RS+N)).
Pratt–Robles (1706.04593) §3.2.6 for Conrey's argument.

## Attempt on the 4/7 barrier (2026-11-15, later)

Status: not broken.  Same caveats as above (AI exploration, bookkeeping only).
Units: q = x^θ is the modulus, L = q^{1/2}, H = q²/x, A = q/H.

### Dictionary

A method that saves q^κ over the trivial bound reaches θ = 1/(2−κ).
48/95, 17/33, 9/17, 8/15, 4/7, 3/5, 5/8 are κ = 1/48, 1/17, 1/9, 1/8, 1/4,
1/3, 2/5.  The binding conditions, with q = rs:

* Polymath Type III: H ≤ √r and H ≤ √s;
* Deshouillers–Iwaniec: H ≤ s, H ≤ √r, H ≤ r/√s.

At r = s = L all read H ≤ q^{1/4}.

### Equivalent forms of the stuck estimate

1. Dual: Σ_{h~H} Σ_{n₁,n₂,ℓ₁,ℓ₂~L} e(2h·inv(n₁n₂)/(ℓ₁ℓ₂)); save H^{1+δ}.
2. Hyper-Kloosterman: Σ_{h~H} Σ_{u,v~L} Σ_{ℓ₁,ℓ₂~L} Kl₃(2huv; ℓ₁ℓ₂); save
   H^{1+δ}.  Every balanced variable is self-dual under Poisson (length √q).
3. Direct: D = Σ_q Σ_{a~A} Δ_q(−2·inv(a)), where Δ_q(w) is the error term
   of #{n₁n₂ ≡ w (q), nᵢ ~ L}.  Here the trivial bound is the true order,
   so *any* power saving suffices.  Needed for A = q^{3/4−η}.
4. Equidistribution: the fractions inv(m)/m' (m, m' ~ M = x^θ, both products
   of two factors of size √M) are equidistributed at scale M^{−1/4}; needed
   at scale M^{−1/4−η}.
5. After splitting off every piece with a flexible factor, the residue is:
   the number of n ≤ x such that n and n+2 each have two prime factors in
   [P, 2P], P ≈ x^{2/7}.  All lower mixed moments of the two counts are
   known (moduli below x, or Bombieri–Vinogradov); only this one is not.

### Arrangements tried (all fail past κ = 1/4)

* One Cauchy–Schwarz with a single balanced variable inside: diagonal gain
  √L = q^{1/4} exactly.
* Both factors of the modulus inside (form 3 with Cauchy–Schwarz over a):
  the diagonal gains L, far more than needed.  The off-diagonal needs any
  power saving in Σ_{a~A} Δ_{q₁}(−2·inv(a)) Δ_{q₂}(−2·inv(a)) for typical
  q₁ ≠ q₂; equivalently an incomplete sum of length N = M^{5/8} of
  Kl₃·conj(Kl₃) to modulus M = q₁q₂ bounded by N^{3/5}.  Completion gives
  M^{1/2}; q-van der Corput with the four available factors does no better.
* One balanced variable plus h inside: off-diagonal modulus L³ against
  outer length L²: gain q^{1/8} (this is Irving's 8/15), or q^{1/4} once
  Kuznetsov is applied to the remaining smooth modulus (this is DI).
* Second Cauchy–Schwarz after the Polymath step: the remaining sum is over
  (r₁, r₂, s, t), t ~ L^{1/2}, of Kl₂(c(r₁³+r₂³)·inv(s²t); r₁r₂) times a
  complete correlation sum mod s; every variable is at or below the
  square root of every modulus it meets.
* Dirichlet characters: loses √H against the trivial bound of form 3.
* Positivity (form 5): the known moments do not determine the missing one.

### What the κ = 1/4 methods leave unused

Deshouillers–Iwaniec discards the divisor structure of d = n₁n₂ and treats
each level ss' separately.  Polymath discards the smooth averaging over r
and s and the shape of the box.  FKM's bound for Σ d(n)K(n) uses only
(n₁, n₂), saves q^{1/16} for a single h and prime q, and uses neither h
nor the modulus average.  No arrangement found combines two of these.

### GL(3)

Kl₃ sums over the modulus are the w₅ term of the SL(3,Z) Kuznetsov formula.
Buttcane (arXiv:2205.14194) isolates it: Σ_c Kl₃(·; c) f(n/c³) = spectral
sum over SL(3,Z) forms near symmetric squares.  Two obstacles for us:
(i) by his own count the trivial bound on the spectral side (C³X^{1/2},
X ≳ C) is worse than Deligne on the Kloosterman side (C³), so a gain needs
cancellation in the spectral sum from the extra averages over h, u, v;
(ii) his modulus is summed smoothly, ours is ℓ₁ℓ₂ with both factors
smooth, which would need the congruence-subgroup version and an average
over levels.  A smooth single modulus corresponds to τ₃ × τ₂, which is
already solved by GL(2) methods.

### No-go for the standard toolkit (second pass, same day)

Model: variables h (size H = q^κ), u, v, r, s (size L = q^{1/2}), summand
Kl₃(2huv; rs).  Allowed steps: Cauchy–Schwarz with an inner set I, then
completion of the product of the outer dual variables to the modulus M of
the correlation sum, with square-root cancellation assumed for every
complete sum.  Then

    saving² = min(|I|, σ),   σ = min(√M, N_O/√M),

where N_O ≤ q^{5/4} is the length of the outer dual product and
M = q · (product of the inner modulus variables).

Claim: saving ≤ q^{1/4}.  Proof: saving > q^κ with κ > 1/4 needs
|I| > q^{1/2} and σ > q^{1/2}.  The second forces M < N_O²/q ≤ q^{3/2},
so I contains at most one of r, s.  Then |I| > q^{1/2} forces a dual
variable into I, which gives N_O ≤ q and σ ≤ q/√M ≤ q^{1/4}.

A second Cauchy–Schwarz on the off-diagonal replaces σ by
√min(|I₂|, σ₂) with σ₂ ≤ √N_O ≤ q^{5/8}, so σ ≤ q^{5/16} < q^{1/2}.
Iterating further only lowers it.

So a proof past 4/7 needs a step outside this list.  Candidates examined:

* Shifting a smooth variable (Burgess / q-van der Corput): no smooth
  variable is longer than a factor of the modulus it meets.
* Splitting each smooth variable into "has a divisor in the useful range"
  and the rest: the rest is (prime) × (tiny), of relative density O(ε) per
  variable.  Re-expanding the prime by any exact identity returns the same
  smooth piece with coefficient 1, so the recursion does not contract.
  Bounding the rest trivially costs ε^c (log N)^k N, which is o(N) only
  for θ − 4/7 = o((log N)^{-1/3}).
* Variance over the long variable a: the cross term is the original sum.
* Divisor weight on the modulus via GL(2) oldforms: the family becomes all
  newforms of conductor up to q, the same size as before.
* The long-element GL(3) Kloosterman sum factors as a product of two
  classical sums with first-power cross inverses; ours has squared
  inverses, equivalently a Fourier index that moves with the moduli.
