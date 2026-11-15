import MobiusDeterminant.LambdaR.Assembly
import MobiusDeterminant.MainTerm.Reduction
import MobiusDeterminant.MainTerm.MobiusSums

/-!
# Main theorem: correlations of `Λ_R` at level `θ`

Theorem 1.1 of the paper, deduced from

* `MobiusPairLevel θ` — the level of distribution of Möbius-weighted divisor
  pairs (Theorem 1.2 of the paper, proved there for every `θ < 9/17`), and
* `PNTMobius` — the prime number theorem for `μ` with classical error term.

Every other step of the deduction (expansion, Abel summation, gcd expansion of
the main term, singular series as an Euler product, the asymptotic for `S_g`,
and all error estimates) is proved in this project.
-/

namespace MobiusDeterminant

/-- **Theorem 1.1 (formal deduction).**  If divisor pairs weighted by `μ(d)μ(e)`
have level of distribution `θ > 0`, then, assuming the prime number theorem
for `μ`,
`∑_{n ≤ N} Λ_R(n) Λ_R(n+2) = 𝔖 N + O(N exp(-c √(log R)))` uniformly for
`2 ≤ R ≤ N^θ`. -/
theorem lambdaR_twin_correlation (θ : ℝ) (hθ : 0 < θ)
    (hL : MobiusPairLevel θ) (hPNT : PNTMobius) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ N : ℕ, ∀ R : ℝ, 2 ≤ N → 2 ≤ R → R ≤ (N : ℝ) ^ θ →
      |∑ n ∈ Finset.Icc 1 N, LambdaR R n * LambdaR R (n + 2) - twinConstant * N|
        ≤ C * N * Real.exp (-c * Real.sqrt (Real.log R)) :=
  lambdaR_twin_of_level_of_mainTerm θ hθ hL
    (mainTermAsymp_of_sgAsymp (sgAsymp_of_PNT hPNT))

/-- The main-term asymptotic `M(R) = 𝔖 + O(exp(-c √(log R)))` from the PNT for `μ`. -/
theorem mainTermAsymp_of_PNT (hPNT : PNTMobius) : MainTermAsymp :=
  mainTermAsymp_of_sgAsymp (sgAsymp_of_PNT hPNT)

end MobiusDeterminant
