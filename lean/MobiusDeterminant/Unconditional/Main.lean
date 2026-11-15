import MobiusDeterminant.Main
import MobiusDeterminant.Unconditional.Toolkit
import MobiusDeterminant.Unconditional.BloomMaynard
import MobiusDeterminant.Unconditional.Balanced
import MobiusDeterminant.Unconditional.MeanValue
import MobiusDeterminant.Unconditional.Level
import MobiusDeterminant.Unconditional.PNTMobius

/-!
# Theorem 1.1, unconditionally

The components proved in `Unconditional/` discharge both hypotheses of
`lambdaR_twin_correlation`:

* `mobiusPairLevel` — Theorem 1.2 (level of distribution `θ < 9/17` for Möbius-weighted
  divisor pairs), from Bloom–Maynard (`bloomMaynardE4`), the balanced-box bound, the
  mean-value theorem (Theorem 6.1), the analytic toolkit, and Lean Pool's Weil bound;
* `pntMobius` — the prime number theorem for `μ` with classical error term, built on
  PNT+ (Kontorovich–Tao et al.).
-/

namespace MobiusDeterminant

/-- **Theorem 6.1** (mean-value theorem for Möbius–Kloosterman fractions). -/
theorem meanValueThm : MeanValueThm :=
  meanValueThm_of (balancedBoxBound_of_BM bloomMaynardE4) mellinSeparation

/-- **Theorem 1.2** (level of distribution for Möbius-weighted divisor pairs). -/
theorem mobiusPairLevel (θ : ℝ) (hθ : θ < 9 / 17) : MobiusPairLevel θ :=
  mobiusPairLevel_of_meanValue meanValueThm mellinSeparation poissonAPDecay θ hθ

/-- **Theorem 1.1** (twin correlations of truncated von Mangoldt functions up to level
`9/17`), with no hypotheses: for every `0 < θ < 9/17`,
`∑_{n ≤ N} Λ_R(n) Λ_R(n+2) = 𝔖 N + O(N exp(-c √(log R)))` uniformly for `2 ≤ R ≤ N^θ`. -/
theorem lambdaR_twin_correlation_unconditional (θ : ℝ) (hθ : 0 < θ) (hθ' : θ < 9 / 17) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ N : ℕ, ∀ R : ℝ, 2 ≤ N → 2 ≤ R → R ≤ (N : ℝ) ^ θ →
      |∑ n ∈ Finset.Icc 1 N, LambdaR R n * LambdaR R (n + 2) - twinConstant * N|
        ≤ C * N * Real.exp (-c * Real.sqrt (Real.log R)) :=
  lambdaR_twin_correlation θ hθ (mobiusPairLevel θ hθ') pntMobius

end MobiusDeterminant
