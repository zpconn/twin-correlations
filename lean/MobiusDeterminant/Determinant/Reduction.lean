import MobiusDeterminant.Determinant.ReductionIdent

/-!
# Theorem 1.3 from its components (paper §7, correlation form)

* `detErrorBound_of : MellinSep4 → DetTensorBound → DetErrorBound`;
* `zeroModeBound_of : MellinSep4 → OddMainBound → ZeroModeBound`.

For `κ = 2`, the exact identities of `ReductionIdent.lean` write
`S_2 - S_2⁰ = ∑_{j<3} ∫ g(τ) oddDelta(2^j X, 3D/2, 3E/2, ψ_{τ,j}, φ₁_τ, φ₂_τ) dτ` and
`S_2⁰ = ∑_{j<3} ∫ g(τ) oddMain(…) dτ`, with weights tempered with `P = K (1 + ‖τ‖)`.
We bound the integrands by `DetTensorBound` (with `ε/2`; its hypotheses follow from those of
`DetErrorBound` for `X ≥ X₁(ε)`, and `X < X₁` is handled by the trivial bound) and by
`OddMainBound` (at the `d`-scale `3D/2 ≥ √X`), and integrate the polynomial factor against `|g|`.
The case `κ = -2` is the case `κ = 2` for the permuted weight with `A`, `B` interchanged.
-/

open Finset Real MeasureTheory
open scoped ArithmeticFunction.Moebius

namespace MobiusDeterminant.Determinant

namespace Reduction

open MobiusDeterminant.Level

/-! ## The Mellin density -/

/-- `MellinSep4` with an integrable density (if `W = 0` on `(0,∞)⁴` take `g = 0`; otherwise
the Mellin integrand is integrable at some point, which makes `g` measurable). -/
lemma mellin_good (h4 : MellinSep4) {W : ℝ × ℝ × ℝ × ℝ → ℂ} (hW : SmoothWeight W) :
    ∃ g : E4 → ℂ, (∀ m : ℕ, Integrable (fun τ => (1 + ‖τ‖) ^ m * ‖g τ‖)) ∧ Integrable g ∧
      ∀ α β δ ε : ℝ, 0 < α → 0 < β → 0 < δ → 0 < ε →
        W (α, β, δ, ε) = ∫ τ, g τ * mphase τ α β δ ε := by
  obtain ⟨g, hm, hW'⟩ := h4 W hW
  by_cases hex : ∃ α β δ ε : ℝ, 0 < α ∧ 0 < β ∧ 0 < δ ∧ 0 < ε ∧ W (α, β, δ, ε) ≠ 0
  · obtain ⟨α, β, δ, ε, hα, hβ, hδ, hε, hne⟩ := hex
    have hint : Integrable (fun τ => g τ * mphase τ α β δ ε) := by
      by_contra h
      exact hne (by rw [hW' α β δ ε hα hβ hδ hε]; exact integral_undef h)
    have hcont : Continuous (fun τ : E4 => mphase τ α β δ ε) := by unfold mphase; fun_prop
    have hne0 : ∀ τ, mphase τ α β δ ε ≠ 0 := fun τ => Complex.exp_ne_zero _
    have hmeas : AEStronglyMeasurable g volume := by
      have : g = fun τ => (g τ * mphase τ α β δ ε) * (mphase τ α β δ ε)⁻¹ := by
        funext τ; rw [mul_assoc, mul_inv_cancel₀ (hne0 τ), mul_one]
      rw [this]
      exact hint.aestronglyMeasurable.mul (hcont.inv₀ hne0).aestronglyMeasurable
    have hgi : Integrable g := (integrable_norm_iff hmeas).mp (by simpa using hm 0)
    exact ⟨g, hm, hgi, hW'⟩
  · push Not at hex
    refine ⟨0, fun m => by simp, integrable_zero _ _ _, fun α β δ ε hα hβ hδ hε => ?_⟩
    simp [hex α β δ ε hα hβ hδ hε]

/-! ## The right-hand sides -/

/-- The right-hand side of `DetTensorBound`. -/
noncomputable def rhsT (ε N₀ D E : ℝ) : ℝ :=
  N₀ ^ (1 + ε) *
      ((max D E) ^ (-(1 : ℝ) / 12) * (D * E / N₀) ^ ((3 : ℝ) / 4)
        + (max D E) ^ (-(2 : ℝ) / 3) * (min D E) ^ ((1 : ℝ) / 2) * (D * E / N₀)
        + (min D E) ^ (-(1 : ℝ) / 2) * (D * E / N₀))
    + N₀ ^ ((1 : ℝ) / 2)

/-- The right-hand side of `DetErrorBound`. -/
noncomputable def rhsE (ε X A B : ℝ) : ℝ :=
  X ^ (1 + ε) *
      ((max (X / A) (X / B)) ^ (-(1 : ℝ) / 12) * (X / (A * B)) ^ ((3 : ℝ) / 4)
        + (max (X / A) (X / B)) ^ (-(2 : ℝ) / 3) * (min (X / A) (X / B)) ^ ((1 : ℝ) / 2)
            * (X / (A * B))
        + (min (X / A) (X / B)) ^ (-(1 : ℝ) / 2) * (X / (A * B)))
    + X ^ ((1 : ℝ) / 2)

lemma rhsE_ge {ε X A B : ℝ} (hX : 0 < X) (hA : 0 < A) (hB : 0 < B) :
    X ^ ((1 : ℝ) / 2) ≤ rhsE ε X A B := by
  unfold rhsE
  have hm : 0 < max (X / A) (X / B) := lt_max_of_lt_left (div_pos hX hA)
  have hm₀ : 0 < min (X / A) (X / B) := lt_min (div_pos hX hA) (div_pos hX hB)
  have hT : 0 < X / (A * B) := by positivity
  have : 0 ≤ X ^ (1 + ε) *
      ((max (X / A) (X / B)) ^ (-(1 : ℝ) / 12) * (X / (A * B)) ^ ((3 : ℝ) / 4)
        + (max (X / A) (X / B)) ^ (-(2 : ℝ) / 3) * (min (X / A) (X / B)) ^ ((1 : ℝ) / 2)
            * (X / (A * B))
        + (min (X / A) (X / B)) ^ (-(1 : ℝ) / 2) * (X / (A * B))) := by positivity
  linarith

lemma rpow_mul_le_of_nonpos {c m r : ℝ} (hc : 1 ≤ c) (hm : 0 ≤ m) (hr : r ≤ 0) :
    (c * m) ^ r ≤ m ^ r := by
  rw [Real.mul_rpow (by linarith) hm]
  exact mul_le_of_le_one_left (by positivity) (Real.rpow_le_one_of_one_le_of_nonpos hc hr)

lemma rpow_mul_le_of_le_one {c m r : ℝ} (hc : 1 ≤ c) (hm : 0 ≤ m) (_hr0 : 0 ≤ r) (hr : r ≤ 1) :
    (c * m) ^ r ≤ c * m ^ r := by
  rw [Real.mul_rpow (by linarith) hm]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  calc c ^ r ≤ c ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hc hr
    _ = c := Real.rpow_one c

/-- `D' E'/N_j ≤ (9/4) X/(AB)`. -/
lemma T'_le {X A B : ℝ} (hX : 0 < X) (hA : 0 < A) (hB : 0 < B) (j : ℕ) :
    3 / 2 * (X / A) * (3 / 2 * (X / B)) / (2 ^ j * X) ≤ 9 / 4 * (X / (A * B)) := by
  have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have : 3 / 2 * (X / A) * (3 / 2 * (X / B)) / (2 ^ j * X) = 9 / 4 * (X / (A * B)) / 2 ^ j := by
    field_simp
    ring
  rw [this]
  exact div_le_self (by positivity) h2j

/-- **Transfer of the bound** from `(N_j, 3D/2, 3E/2, ε/2)` to `(X, A, B, ε)`. -/
lemma rhsT_le {ε X A B : ℝ} (hε : 0 < ε) (hX : 1 ≤ X) (hA : 0 < A) (hB : 0 < B) {j : ℕ}
    (hj : j < 3) :
    rhsT (ε / 2) (2 ^ j * X) (3 / 2 * (X / A)) (3 / 2 * (X / B)) ≤
      (16 * 4 ^ (ε / 2) + 4) * rhsE ε X A B := by
  have hX0 : 0 < X := by linarith
  have hmax : max (3 / 2 * (X / A)) (3 / 2 * (X / B)) = 3 / 2 * max (X / A) (X / B) :=
    (mul_max_of_nonneg _ _ (by norm_num)).symm
  have hmin : min (3 / 2 * (X / A)) (3 / 2 * (X / B)) = 3 / 2 * min (X / A) (X / B) :=
    (mul_min_of_nonneg _ _ (by norm_num)).symm
  have hT' := T'_le hX0 hA hB j
  have h2j4 : 2 ^ j * X ≤ 4 * X := by
    have : (2 : ℝ) ^ j ≤ 4 := by
      calc (2 : ℝ) ^ j ≤ 2 ^ 2 := pow_le_pow_right₀ (by norm_num) (by omega)
        _ = 4 := by norm_num
    nlinarith
  unfold rhsT rhsE
  rw [hmax, hmin]
  set m := max (X / A) (X / B) with hm_def
  set m₀ := min (X / A) (X / B) with hm₀_def
  set T := X / (A * B) with hT_def
  set T' := 3 / 2 * (X / A) * (3 / 2 * (X / B)) / (2 ^ j * X) with hT'_def
  have hm : 0 < m := lt_max_of_lt_left (div_pos hX0 hA)
  have hm₀ : 0 < m₀ := lt_min (div_pos hX0 hA) (div_pos hX0 hB)
  have hT : 0 < T := by positivity
  have hT'0 : 0 ≤ T' := by positivity
  have b1 : (3 / 2 * m) ^ (-(1 : ℝ) / 12) ≤ m ^ (-(1 : ℝ) / 12) :=
    rpow_mul_le_of_nonpos (by norm_num) hm.le (by norm_num)
  have b2 : T' ^ ((3 : ℝ) / 4) ≤ 9 / 4 * T ^ ((3 : ℝ) / 4) :=
    (Real.rpow_le_rpow hT'0 hT' (by norm_num)).trans
      (rpow_mul_le_of_le_one (by norm_num) hT.le (by norm_num) (by norm_num))
  have b3 : (3 / 2 * m) ^ (-(2 : ℝ) / 3) ≤ m ^ (-(2 : ℝ) / 3) :=
    rpow_mul_le_of_nonpos (by norm_num) hm.le (by norm_num)
  have b4 : (3 / 2 * m₀) ^ ((1 : ℝ) / 2) ≤ 3 / 2 * m₀ ^ ((1 : ℝ) / 2) :=
    rpow_mul_le_of_le_one (by norm_num) hm₀.le (by norm_num) (by norm_num)
  have b6 : (3 / 2 * m₀) ^ (-(1 : ℝ) / 2) ≤ m₀ ^ (-(1 : ℝ) / 2) :=
    rpow_mul_le_of_nonpos (by norm_num) hm₀.le (by norm_num)
  have b7 : (2 ^ j * X) ^ (1 + ε / 2) ≤ 4 * 4 ^ (ε / 2) * X ^ (1 + ε) := by
    calc (2 ^ j * X) ^ (1 + ε / 2) ≤ (4 * X) ^ (1 + ε / 2) :=
          Real.rpow_le_rpow (by positivity) h2j4 (by positivity)
      _ = 4 ^ (1 + ε / 2) * X ^ (1 + ε / 2) := Real.mul_rpow (by norm_num) hX0.le
      _ ≤ 4 ^ (1 + ε / 2) * X ^ (1 + ε) := by
          gcongr
          linarith
      _ = 4 * 4 ^ (ε / 2) * X ^ (1 + ε) := by
          rw [Real.rpow_add (by norm_num), Real.rpow_one]
  have b8 : (2 ^ j * X) ^ ((1 : ℝ) / 2) ≤ 4 * X ^ ((1 : ℝ) / 2) := by
    calc (2 ^ j * X) ^ ((1 : ℝ) / 2) ≤ (4 * X) ^ ((1 : ℝ) / 2) :=
          Real.rpow_le_rpow (by positivity) h2j4 (by norm_num)
      _ ≤ 4 * X ^ ((1 : ℝ) / 2) :=
          rpow_mul_le_of_le_one (by norm_num) hX0.le (by norm_num) (by norm_num)
  set t1 := m ^ (-(1 : ℝ) / 12) * T ^ ((3 : ℝ) / 4) with ht1
  set t2 := m ^ (-(2 : ℝ) / 3) * m₀ ^ ((1 : ℝ) / 2) * T with ht2
  set t3 := m₀ ^ (-(1 : ℝ) / 2) * T with ht3
  have ht10 : 0 ≤ t1 := by positivity
  have ht20 : 0 ≤ t2 := by positivity
  have ht30 : 0 ≤ t3 := by positivity
  have hbr : (3 / 2 * m) ^ (-(1 : ℝ) / 12) * T' ^ ((3 : ℝ) / 4) +
      (3 / 2 * m) ^ (-(2 : ℝ) / 3) * (3 / 2 * m₀) ^ ((1 : ℝ) / 2) * T' +
      (3 / 2 * m₀) ^ (-(1 : ℝ) / 2) * T' ≤ 4 * (t1 + t2 + t3) := by
    have e1 : (3 / 2 * m) ^ (-(1 : ℝ) / 12) * T' ^ ((3 : ℝ) / 4) ≤
        m ^ (-(1 : ℝ) / 12) * (9 / 4 * T ^ ((3 : ℝ) / 4)) :=
      mul_le_mul b1 b2 (by positivity) (by positivity)
    have e2 : (3 / 2 * m) ^ (-(2 : ℝ) / 3) * (3 / 2 * m₀) ^ ((1 : ℝ) / 2) * T' ≤
        m ^ (-(2 : ℝ) / 3) * (3 / 2 * m₀ ^ ((1 : ℝ) / 2)) * (9 / 4 * T) :=
      mul_le_mul (mul_le_mul b3 b4 (by positivity) (by positivity)) hT' hT'0 (by positivity)
    have e3 : (3 / 2 * m₀) ^ (-(1 : ℝ) / 2) * T' ≤ m₀ ^ (-(1 : ℝ) / 2) * (9 / 4 * T) :=
      mul_le_mul b6 hT' hT'0 (by positivity)
    have f1 : m ^ (-(1 : ℝ) / 12) * (9 / 4 * T ^ ((3 : ℝ) / 4)) = 9 / 4 * t1 := by ring
    have f2 : m ^ (-(2 : ℝ) / 3) * (3 / 2 * m₀ ^ ((1 : ℝ) / 2)) * (9 / 4 * T) = 27 / 8 * t2 := by
      ring
    have f3 : m₀ ^ (-(1 : ℝ) / 2) * (9 / 4 * T) = 9 / 4 * t3 := by ring
    linarith
  have hbr0 : 0 ≤ (3 / 2 * m) ^ (-(1 : ℝ) / 12) * T' ^ ((3 : ℝ) / 4) +
      (3 / 2 * m) ^ (-(2 : ℝ) / 3) * (3 / 2 * m₀) ^ ((1 : ℝ) / 2) * T' +
      (3 / 2 * m₀) ^ (-(1 : ℝ) / 2) * T' := by positivity
  have hXe : 0 ≤ X ^ (1 + ε) := by positivity
  have h4e : 0 ≤ (4 : ℝ) ^ (ε / 2) := by positivity
  have hXh : 0 ≤ X ^ ((1 : ℝ) / 2) := by positivity
  have hS : 0 ≤ X ^ (1 + ε) * (t1 + t2 + t3) := by positivity
  have hS' : 0 ≤ (4 : ℝ) ^ (ε / 2) * X ^ ((1 : ℝ) / 2) := by positivity
  calc (2 ^ j * X) ^ (1 + ε / 2) * ((3 / 2 * m) ^ (-(1 : ℝ) / 12) * T' ^ ((3 : ℝ) / 4) +
        (3 / 2 * m) ^ (-(2 : ℝ) / 3) * (3 / 2 * m₀) ^ ((1 : ℝ) / 2) * T' +
        (3 / 2 * m₀) ^ (-(1 : ℝ) / 2) * T') + (2 ^ j * X) ^ ((1 : ℝ) / 2)
      ≤ 4 * 4 ^ (ε / 2) * X ^ (1 + ε) * (4 * (t1 + t2 + t3)) + 4 * X ^ ((1 : ℝ) / 2) :=
        add_le_add (mul_le_mul b7 hbr hbr0 (by positivity)) b8
    _ ≤ (16 * 4 ^ (ε / 2) + 4) * (X ^ (1 + ε) * (t1 + t2 + t3) + X ^ ((1 : ℝ) / 2)) := by
        nlinarith

/-- `A ≥ 3/2` under the hypotheses of `DetErrorBound` for `X ≥ 4`. -/
lemma ge_three_halves {ε X A B : ℝ} (hε : 0 < ε) (hX4 : 4 ≤ X) (hA1 : 1 ≤ A) (hB1 : 1 ≤ B)
    (hBX : B ≤ √X)
    (h1 : X ^ ε * (X / (A * B)) ≤ (max (X / A) (X / B)) ^ ((1 : ℝ) / 6)) : 3 / 2 ≤ A := by
  have hX0 : 0 < X := by linarith
  have hT0 : 0 < X / (A * B) := by positivity
  have hm_le : max (X / A) (X / B) ≤ X :=
    max_le (div_le_self hX0.le hA1) (div_le_self hX0.le hB1)
  have hm_pos : 0 < max (X / A) (X / B) := lt_max_of_lt_left (by positivity)
  have hXε1 : 1 ≤ X ^ ε := Real.one_le_rpow (by linarith) hε.le
  by_contra hlt
  push Not at hlt
  have hTle : X / (A * B) ≤ X ^ ((1 : ℝ) / 6) := by
    calc X / (A * B) ≤ X ^ ε * (X / (A * B)) := le_mul_of_one_le_left hT0.le hXε1
      _ ≤ (max (X / A) (X / B)) ^ ((1 : ℝ) / 6) := h1
      _ ≤ X ^ ((1 : ℝ) / 6) := Real.rpow_le_rpow hm_pos.le hm_le (by norm_num)
  have hT6 : (X / (A * B)) ^ 6 ≤ X := by
    calc (X / (A * B)) ^ 6 ≤ (X ^ ((1 : ℝ) / 6)) ^ 6 := pow_le_pow_left₀ hT0.le hTle 6
      _ = X := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]; norm_num
  have hB2 : B ^ 2 ≤ X := by
    calc B ^ 2 ≤ (√X) ^ 2 := pow_le_pow_left₀ (by linarith) hBX 2
      _ = X := Real.sq_sqrt hX0.le
  have hB6 : B ^ 6 ≤ X ^ 3 := by
    calc B ^ 6 = (B ^ 2) ^ 3 := by ring
      _ ≤ X ^ 3 := pow_le_pow_left₀ (by positivity) hB2 3
  have e : (X / (A * B)) ^ 6 * A ^ 6 * B ^ 6 = X ^ 6 := by
    have hA0 : A ≠ 0 := by positivity
    have hB0 : B ≠ 0 := by positivity
    field_simp
  have key : X ^ 4 * X ^ 2 ≤ X ^ 4 * A ^ 6 := by
    calc X ^ 4 * X ^ 2 = (X / (A * B)) ^ 6 * A ^ 6 * B ^ 6 := by rw [e]; ring
      _ ≤ X * A ^ 6 * X ^ 3 := by gcongr
      _ = X ^ 4 * A ^ 6 := by ring
  have hX2 : X ^ 2 ≤ A ^ 6 := le_of_mul_le_mul_left key (by positivity)
  have hA6 : A ^ 6 < (3 / 2) ^ 6 := pow_lt_pow_left₀ hlt (by linarith) (by norm_num)
  nlinarith

/-- **Transfer of the hypotheses** of `DetErrorBound` (room `X^ε`, `X ≥ X₁`) to those of
`DetTensorBound` (room `N^{ε/2}`) at `(N_j, 3D/2, 3E/2)`. -/
lemma hyp_transfer {ε X A B : ℝ} (hε : 0 < ε) (hX4 : 4 ≤ X)
    (hXε : (4 ^ (ε / 2) * (9 / 4)) ^ 2 ≤ X ^ ε) (hA1 : 1 ≤ A) (hAX : A ≤ √X) (hB1 : 1 ≤ B)
    (hBX : B ≤ √X)
    (h1 : X ^ ε * (X / (A * B)) ≤ (max (X / A) (X / B)) ^ ((1 : ℝ) / 6))
    (h2 : (max (X / A) (X / B)) ^ ((2 : ℝ) / 3) * (X ^ ε * (X / (A * B))) ^ 2
      ≤ min (X / A) (X / B)) {j : ℕ} (hj : j < 3) :
    2 ≤ 2 ^ j * X ∧ 1 ≤ 3 / 2 * (X / A) ∧ 1 ≤ 3 / 2 * (X / B) ∧
      3 / 2 * (X / A) ≤ 2 ^ j * X ∧ 3 / 2 * (X / B) ≤ 2 ^ j * X ∧
      (2 ^ j * X) ^ (ε / 2) * (3 / 2 * (X / A) * (3 / 2 * (X / B)) / (2 ^ j * X)) ≤
        (max (3 / 2 * (X / A)) (3 / 2 * (X / B))) ^ ((1 : ℝ) / 6) ∧
      (max (3 / 2 * (X / A)) (3 / 2 * (X / B))) ^ ((2 : ℝ) / 3) *
        ((2 ^ j * X) ^ (ε / 2) * (3 / 2 * (X / A) * (3 / 2 * (X / B)) / (2 ^ j * X))) ^ 2 ≤
          min (3 / 2 * (X / A)) (3 / 2 * (X / B)) := by
  have hX0 : 0 < X := by linarith
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  have hsX : 1 ≤ √X := Real.one_le_sqrt.mpr (by linarith)
  have hsX2 : √X * √X = X := Real.mul_self_sqrt hX0.le
  have hXA : √X ≤ X / A := by rw [le_div_iff₀ hA0]; nlinarith
  have hXB : √X ≤ X / B := by rw [le_div_iff₀ hB0]; nlinarith
  have h2j1 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have h2j4 : (2 : ℝ) ^ j ≤ 4 := by
    calc (2 : ℝ) ^ j ≤ 2 ^ 2 := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = 4 := by norm_num
  have hNX : X ≤ 2 ^ j * X := by nlinarith
  have hN4 : 2 ^ j * X ≤ 4 * X := by nlinarith
  have hA32 : 3 / 2 ≤ A := ge_three_halves hε hX4 hA1 hB1 hBX h1
  have hB32 : 3 / 2 ≤ B := ge_three_halves hε hX4 hB1 hA1 hAX
    (by rwa [max_comm, mul_comm B A])
  have hmax : max (3 / 2 * (X / A)) (3 / 2 * (X / B)) = 3 / 2 * max (X / A) (X / B) :=
    (mul_max_of_nonneg _ _ (by norm_num)).symm
  have hmin : min (3 / 2 * (X / A)) (3 / 2 * (X / B)) = 3 / 2 * min (X / A) (X / B) :=
    (mul_min_of_nonneg _ _ (by norm_num)).symm
  have hm : 0 < max (X / A) (X / B) := lt_max_of_lt_left (div_pos hX0 hA0)
  have hT0 : 0 < X / (A * B) := by positivity
  -- the room: `N^{ε/2} T' ≤ X^ε T`
  have hc : 4 ^ (ε / 2) * (9 / 4) ≤ X ^ (ε / 2) := by
    have hsq : (X ^ (ε / 2)) ^ 2 = X ^ ε := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]; ring_nf
    rw [← hsq] at hXε
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp hXε
  have hNε : (2 ^ j * X) ^ (ε / 2) ≤ 4 ^ (ε / 2) * X ^ (ε / 2) := by
    calc (2 ^ j * X) ^ (ε / 2) ≤ (4 * X) ^ (ε / 2) :=
          Real.rpow_le_rpow (by positivity) hN4 (by positivity)
      _ = 4 ^ (ε / 2) * X ^ (ε / 2) := Real.mul_rpow (by norm_num) hX0.le
  have hXε2 : X ^ ε = X ^ (ε / 2) * X ^ (ε / 2) := by
    rw [← Real.rpow_add hX0]; ring_nf
  have hroom : (2 ^ j * X) ^ (ε / 2) * (3 / 2 * (X / A) * (3 / 2 * (X / B)) / (2 ^ j * X)) ≤
      X ^ ε * (X / (A * B)) := by
    calc (2 ^ j * X) ^ (ε / 2) * (3 / 2 * (X / A) * (3 / 2 * (X / B)) / (2 ^ j * X))
        ≤ (4 ^ (ε / 2) * X ^ (ε / 2)) * (9 / 4 * (X / (A * B))) :=
          mul_le_mul hNε (T'_le hX0 hA0 hB0 j) (by positivity) (by positivity)
      _ = (4 ^ (ε / 2) * (9 / 4)) * X ^ (ε / 2) * (X / (A * B)) := by ring
      _ ≤ X ^ (ε / 2) * X ^ (ε / 2) * (X / (A * B)) := by gcongr
      _ = X ^ ε * (X / (A * B)) := by rw [hXε2]
  have hroom0 : 0 ≤ (2 ^ j * X) ^ (ε / 2) *
      (3 / 2 * (X / A) * (3 / 2 * (X / B)) / (2 ^ j * X)) := by positivity
  refine ⟨by linarith, by linarith, by linarith, ?_, ?_, ?_, ?_⟩
  · have : 3 / 2 * (X / A) ≤ X := by
      rw [← mul_div_assoc, div_le_iff₀ hA0]; nlinarith
    linarith
  · have : 3 / 2 * (X / B) ≤ X := by
      rw [← mul_div_assoc, div_le_iff₀ hB0]; nlinarith
    linarith
  · rw [hmax]
    calc _ ≤ X ^ ε * (X / (A * B)) := hroom
      _ ≤ (max (X / A) (X / B)) ^ ((1 : ℝ) / 6) := h1
      _ ≤ (3 / 2 * max (X / A) (X / B)) ^ ((1 : ℝ) / 6) :=
          Real.rpow_le_rpow hm.le (by linarith) (by norm_num)
  · rw [hmax, hmin]
    calc (3 / 2 * max (X / A) (X / B)) ^ ((2 : ℝ) / 3) *
          ((2 ^ j * X) ^ (ε / 2) * (3 / 2 * (X / A) * (3 / 2 * (X / B)) / (2 ^ j * X))) ^ 2
        ≤ (3 / 2 * (max (X / A) (X / B)) ^ ((2 : ℝ) / 3)) * (X ^ ε * (X / (A * B))) ^ 2 :=
          mul_le_mul (rpow_mul_le_of_le_one (by norm_num) hm.le (by norm_num) (by norm_num))
            (pow_le_pow_left₀ hroom0 hroom 2) (by positivity) (by positivity)
      _ = 3 / 2 * ((max (X / A) (X / B)) ^ ((2 : ℝ) / 3) * (X ^ ε * (X / (A * B))) ^ 2) := by
          ring
      _ ≤ 3 / 2 * min (X / A) (X / B) := by gcongr

/-! ## `κ = 2` -/

/-- `DetErrorBound` for `κ = 2`. -/
theorem detErrorBound_two (h4 : MellinSep4) (hT : DetTensorBound)
    {W : ℝ × ℝ × ℝ × ℝ → ℂ} (hW : SmoothWeight W) {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ X A B : ℝ, 3 ≤ X → 1 ≤ A → A ≤ Real.sqrt X → 1 ≤ B → B ≤ Real.sqrt X →
      X ^ ε * (X / (A * B)) ≤ (max (X / A) (X / B)) ^ ((1 : ℝ) / 6) →
      (max (X / A) (X / B)) ^ ((2 : ℝ) / 3) * (X ^ ε * (X / (A * B))) ^ 2
        ≤ min (X / A) (X / B) →
      ‖detSum 2 W A B X - zeroMode 2 W A B X‖ ≤ C * rhsE ε X A B := by
  obtain ⟨g, hgm, hgi, hgW⟩ := mellin_good h4 hW
  obtain ⟨k, CT, hCT, hTb⟩ := hT (ε / 2) (by positivity)
  obtain ⟨K, hK1, hK⟩ := tempered_pieces k
  obtain ⟨MW, hMW0, hMW⟩ := exists_bound_W hW
  set Ig := ∫ τ, (1 + ‖τ‖) ^ k * ‖g τ‖ with hIg
  have hIg0 : 0 ≤ Ig := integral_nonneg (fun τ => by positivity)
  set c₁ : ℝ := 4 ^ (ε / 2) * (9 / 4) with hc₁
  set X₁ : ℝ := max 4 ((c₁ ^ 2) ^ (1 / ε)) with hX₁
  set Ctr : ℝ := 16 * 4 ^ (ε / 2) + 4 with hCtr
  set Cm : ℝ := 3 * (CT * K ^ k * Ig * Ctr) with hCm
  set Cc : ℝ := 18 * X₁ ^ 2 * MW with hCc
  have hCm0 : 0 ≤ Cm := by positivity
  have hCc0 : 0 ≤ Cc := by positivity
  refine ⟨Cm + Cc + 1, by positivity, fun X A B hX hA1 hAX hB1 hBX h1 h2 => ?_⟩
  have hX0 : 0 < X := by linarith
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  have hR := rhsE_ge (ε := ε) hX0 hA0 hB0
  have hR1 : 1 ≤ X ^ ((1 : ℝ) / 2) := Real.one_le_rpow (by linarith) (by norm_num)
  have hR0 : 0 ≤ rhsE ε X A B := by linarith
  by_cases hXl : X₁ ≤ X
  · have hX4 : 4 ≤ X := le_trans (le_max_left _ _) hXl
    have hXε : c₁ ^ 2 ≤ X ^ ε := by
      calc c₁ ^ 2 = ((c₁ ^ 2) ^ (1 / ε)) ^ ε := by
            rw [← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ hε.ne', Real.rpow_one]
        _ ≤ X ^ ε := Real.rpow_le_rpow (by positivity) (le_trans (le_max_right _ _) hXl) hε.le
    rw [detSum_sub_zeroMode_eq hW hgi hgW (by linarith) hA0 hB0]
    have hpiece : ∀ j ∈ range 3, ‖∫ τ, g τ * oddDelta (2 ^ j * X) (3 / 2 * (X / A))
        (3 / 2 * (X / B)) (psiP X j τ) (phiP (τ 0 - τ 2)) (phiP (τ 1 - τ 3))‖ ≤
        CT * K ^ k * Ig * Ctr * rhsE ε X A B := by
      intro j hj
      have hj3 := Finset.mem_range.mp hj
      obtain ⟨hN2, hD1, hE1, hDN, hEN, hc1, hc2⟩ :=
        hyp_transfer hε hX4 hXε hA1 hAX hB1 hBX h1 h2 hj3
      have hrt : rhsT (ε / 2) (2 ^ j * X) (3 / 2 * (X / A)) (3 / 2 * (X / B)) ≤
          Ctr * rhsE ε X A B := rhsT_le (X := X) hε (by linarith) hA0 hB0 hj3
      have hpt : ∀ τ, ‖g τ * oddDelta (2 ^ j * X) (3 / 2 * (X / A)) (3 / 2 * (X / B))
          (psiP X j τ) (phiP (τ 0 - τ 2)) (phiP (τ 1 - τ 3))‖ ≤
          (CT * K ^ k * rhsT (ε / 2) (2 ^ j * X) (3 / 2 * (X / A)) (3 / 2 * (X / B))) *
            ((1 + ‖τ‖) ^ k * ‖g τ‖) := by
        intro τ
        obtain ⟨t1, t2, t3⟩ := hK X j τ
        have hP1 : 1 ≤ K * (1 + ‖τ‖) := by nlinarith [norm_nonneg τ]
        have hb := hTb (2 ^ j * X) (3 / 2 * (X / A)) (3 / 2 * (X / B)) (K * (1 + ‖τ‖))
          (psiP X j τ) (phiP (τ 0 - τ 2)) (phiP (τ 1 - τ 3)) hN2 hD1 hE1 hDN hEN hc1 hc2 hP1
          t1 t2 t3
        rw [norm_mul]
        calc ‖g τ‖ * ‖oddDelta (2 ^ j * X) (3 / 2 * (X / A)) (3 / 2 * (X / B))
              (psiP X j τ) (phiP (τ 0 - τ 2)) (phiP (τ 1 - τ 3))‖
            ≤ ‖g τ‖ * (CT * (K * (1 + ‖τ‖)) ^ k *
              rhsT (ε / 2) (2 ^ j * X) (3 / 2 * (X / A)) (3 / 2 * (X / B))) :=
              mul_le_mul_of_nonneg_left hb (norm_nonneg _)
          _ = _ := by rw [mul_pow]; ring
      refine (norm_integral_le_of_norm_le ((hgm k).const_mul _)
        (Filter.Eventually.of_forall hpt)).trans ?_
      rw [integral_const_mul]
      have hCK : 0 ≤ CT * K ^ k := by positivity
      calc CT * K ^ k * rhsT (ε / 2) (2 ^ j * X) (3 / 2 * (X / A)) (3 / 2 * (X / B)) * Ig
          ≤ CT * K ^ k * (Ctr * rhsE ε X A B) * Ig := by gcongr
        _ = CT * K ^ k * Ig * Ctr * rhsE ε X A B := by ring
    calc _ ≤ ∑ j ∈ range 3, ‖∫ τ, g τ * oddDelta (2 ^ j * X) (3 / 2 * (X / A))
          (3 / 2 * (X / B)) (psiP X j τ) (phiP (τ 0 - τ 2)) (phiP (τ 1 - τ 3))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _j ∈ range 3, CT * K ^ k * Ig * Ctr * rhsE ε X A B := Finset.sum_le_sum hpiece
      _ = Cm * rhsE ε X A B := by simp [hCm]; ring
      _ ≤ (Cm + Cc + 1) * rhsE ε X A B := by nlinarith
  · push Not at hXl
    have hd := norm_detSum_le hMW0 hMW 2 hX0 hA0 hB0
    have hz := norm_zeroMode_le hW hMW0 hMW 2 hX0 hA0 hB1
    have hXX : X ^ 2 ≤ X₁ ^ 2 := pow_le_pow_left₀ hX0.le hXl.le 2
    calc ‖detSum 2 W A B X - zeroMode 2 W A B X‖
        ≤ ‖detSum 2 W A B X‖ + ‖zeroMode 2 W A B X‖ := norm_sub_le _ _
      _ ≤ 16 * X ^ 2 * MW + 2 * X ^ 2 * MW := add_le_add hd hz
      _ ≤ Cc := by rw [hCc]; nlinarith
      _ ≤ Cc * X ^ ((1 : ℝ) / 2) := le_mul_of_one_le_right hCc0 hR1
      _ ≤ Cc * rhsE ε X A B := mul_le_mul_of_nonneg_left hR hCc0
      _ ≤ (Cm + Cc + 1) * rhsE ε X A B := by nlinarith

/-- `ZeroModeBound` for `κ = 2` (with an absolute constant `c`). -/
theorem zeroModeBound_two (h4 : MellinSep4) (hM : OddMainBound) :
    ∃ c > (0 : ℝ), ∀ W : ℝ × ℝ × ℝ × ℝ → ℂ, SmoothWeight W →
      ∃ C > (0 : ℝ), ∀ X A B : ℝ, 3 ≤ X → 1 ≤ A → A ≤ Real.sqrt X → 1 ≤ B →
        B ≤ Real.sqrt X →
        ‖zeroMode 2 W A B X‖ ≤ C * X * Real.exp (-c * Real.sqrt (Real.log X)) := by
  obtain ⟨c, hc, k, CM, hCM, hMb⟩ := hM
  refine ⟨c / 2, by positivity, fun W hW => ?_⟩
  obtain ⟨g, hgm, hgi, hgW⟩ := mellin_good h4 hW
  obtain ⟨K, hK1, hK⟩ := tempered_pieces k
  set Ig := ∫ τ, (1 + ‖τ‖) ^ k * ‖g τ‖ with hIg
  have hIg0 : 0 ≤ Ig := integral_nonneg (fun τ => by positivity)
  refine ⟨3 * (CM * K ^ k * Ig * 4) + 1, by positivity,
    fun X A B hX hA1 hAX hB1 hBX => ?_⟩
  have hX0 : 0 < X := by linarith
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  rw [zeroMode_eq_int hW hgi hgW (by linarith) hA0 hB0]
  have hsX0 : 0 ≤ √X := Real.sqrt_nonneg X
  have hsX2 : √X * √X = X := Real.mul_self_sqrt hX0.le
  have hXA : √X ≤ X / A := by rw [le_div_iff₀ hA0]; nlinarith
  have hXA43 : 4 / 3 ≤ X / A := by nlinarith
  have hD2 : 2 ≤ 3 / 2 * (X / A) := by linarith
  have hE1 : 1 ≤ 3 / 2 * (X / B) := by
    have : √X ≤ X / B := by rw [le_div_iff₀ hB0]; nlinarith
    nlinarith
  have hED : 3 / 2 * (X / B) ≤ (3 / 2 * (X / A)) ^ 2 := by
    have hA2 : A ^ 2 ≤ X := by
      calc A ^ 2 ≤ (√X) ^ 2 := pow_le_pow_left₀ (by linarith) hAX 2
        _ = X := Real.sq_sqrt hX0.le
    have h1 : X ≤ (X / A) ^ 2 := by
      rw [div_pow, le_div_iff₀ (by positivity)]; nlinarith
    have h2 : X / B ≤ X := div_le_self hX0.le hB1
    nlinarith
  have hexp : Real.exp (-c * Real.sqrt (Real.log (3 / 2 * (X / A)))) ≤
      Real.exp (-(c / 2) * Real.sqrt (Real.log X)) := by
    apply Real.exp_le_exp.mpr
    have hlX : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
    have hlog : Real.log X / 2 ≤ Real.log (3 / 2 * (X / A)) := by
      calc Real.log X / 2 = Real.log √X := (Real.log_sqrt hX0.le).symm
        _ ≤ Real.log (3 / 2 * (X / A)) :=
            Real.log_le_log (Real.sqrt_pos.mpr hX0) (by linarith)
    have hsq : Real.sqrt (Real.log X) / 2 ≤ Real.sqrt (Real.log (3 / 2 * (X / A))) := by
      rw [Real.le_sqrt (by positivity) (by linarith), div_pow, Real.sq_sqrt hlX]
      linarith
    nlinarith
  have hpiece : ∀ j ∈ range 3, ‖∫ τ, g τ * oddMain (2 ^ j * X) (3 / 2 * (X / A))
      (3 / 2 * (X / B)) (psiP X j τ) (phiP (τ 0 - τ 2)) (phiP (τ 1 - τ 3))‖ ≤
      CM * K ^ k * Ig * 4 * X * Real.exp (-(c / 2) * Real.sqrt (Real.log X)) := by
    intro j hj
    have hj3 := Finset.mem_range.mp hj
    have h2j4 : 2 ^ j * X ≤ 4 * X := by
      have : (2 : ℝ) ^ j ≤ 4 := by
        calc (2 : ℝ) ^ j ≤ 2 ^ 2 := pow_le_pow_right₀ (by norm_num) (by omega)
          _ = 4 := by norm_num
      nlinarith
    have hpt : ∀ τ, ‖g τ * oddMain (2 ^ j * X) (3 / 2 * (X / A)) (3 / 2 * (X / B))
        (psiP X j τ) (phiP (τ 0 - τ 2)) (phiP (τ 1 - τ 3))‖ ≤
        (CM * K ^ k * (2 ^ j * X) * Real.exp (-c * Real.sqrt (Real.log (3 / 2 * (X / A))))) *
          ((1 + ‖τ‖) ^ k * ‖g τ‖) := by
      intro τ
      obtain ⟨t1, t2, t3⟩ := hK X j τ
      have hP1 : 1 ≤ K * (1 + ‖τ‖) := by nlinarith [norm_nonneg τ]
      have hb := hMb (2 ^ j * X) (3 / 2 * (X / A)) (3 / 2 * (X / B)) (K * (1 + ‖τ‖))
        (psiP X j τ) (phiP (τ 0 - τ 2)) (phiP (τ 1 - τ 3)) (by positivity) hD2 hE1 hED hP1
        t1 t2 t3
      rw [norm_mul]
      calc ‖g τ‖ * ‖oddMain (2 ^ j * X) (3 / 2 * (X / A)) (3 / 2 * (X / B))
            (psiP X j τ) (phiP (τ 0 - τ 2)) (phiP (τ 1 - τ 3))‖
          ≤ ‖g τ‖ * (CM * (K * (1 + ‖τ‖)) ^ k * (2 ^ j * X) *
            Real.exp (-c * Real.sqrt (Real.log (3 / 2 * (X / A))))) :=
            mul_le_mul_of_nonneg_left hb (norm_nonneg _)
        _ = _ := by rw [mul_pow]; ring
    refine (norm_integral_le_of_norm_le ((hgm k).const_mul _)
      (Filter.Eventually.of_forall hpt)).trans ?_
    rw [integral_const_mul]
    calc CM * K ^ k * (2 ^ j * X) * Real.exp (-c * Real.sqrt (Real.log (3 / 2 * (X / A)))) * Ig
        ≤ CM * K ^ k * (4 * X) * Real.exp (-(c / 2) * Real.sqrt (Real.log X)) * Ig := by
          gcongr CM * K ^ k * ?_ * ?_ * Ig
      _ = CM * K ^ k * Ig * 4 * X * Real.exp (-(c / 2) * Real.sqrt (Real.log X)) := by ring
  have hE0 : 0 ≤ X * Real.exp (-(c / 2) * Real.sqrt (Real.log X)) := by positivity
  calc _ ≤ ∑ j ∈ range 3, ‖∫ τ, g τ * oddMain (2 ^ j * X) (3 / 2 * (X / A))
        (3 / 2 * (X / B)) (psiP X j τ) (phiP (τ 0 - τ 2)) (phiP (τ 1 - τ 3))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _j ∈ range 3, CM * K ^ k * Ig * 4 * X *
          Real.exp (-(c / 2) * Real.sqrt (Real.log X)) := Finset.sum_le_sum hpiece
    _ = 3 * (CM * K ^ k * Ig * 4) * (X * Real.exp (-(c / 2) * Real.sqrt (Real.log X))) := by
        simp; ring
    _ ≤ (3 * (CM * K ^ k * Ig * 4) + 1) * (X * Real.exp (-(c / 2) * Real.sqrt (Real.log X))) := by
        nlinarith
    _ = _ := by ring

end Reduction

/-! ## The theorems -/

open Reduction in
/-- **Theorem 1.3, power-saving part**, from the Mellin separation and the product-weight
error bound. -/
theorem detErrorBound_of (h4 : MellinSep4) (hT : DetTensorBound) : DetErrorBound := by
  intro κ hκ W hW ε hε
  rcases hκ with rfl | rfl
  · exact detErrorBound_two h4 hT hW hε
  · obtain ⟨C, hC, hb⟩ := detErrorBound_two h4 hT (smoothWeight_swapW hW) hε
    refine ⟨C, hC, fun X A B hX hA1 hAX hB1 hBX h1 h2 => ?_⟩
    have hX0 : 0 < X := by linarith
    rw [detSum_neg, zeroMode_neg hX0 (by linarith) (by linarith)]
    have := hb X B A hX hB1 hBX hA1 hAX (by rwa [max_comm, mul_comm B A])
      (by rwa [max_comm, min_comm, mul_comm B A])
    unfold rhsE at this
    rwa [max_comm, min_comm, mul_comm B A] at this

open Reduction in
/-- **Theorem 1.3, zero frequency**, from the Mellin separation and the product-weight main
term bound. -/
theorem zeroModeBound_of (h4 : MellinSep4) (hM : OddMainBound) : ZeroModeBound := by
  obtain ⟨c, hc, h2⟩ := zeroModeBound_two h4 hM
  refine ⟨c, hc, fun κ hκ W hW => ?_⟩
  rcases hκ with rfl | rfl
  · exact h2 W hW
  · obtain ⟨C, hC, hb⟩ := h2 (swapW W) (smoothWeight_swapW hW)
    refine ⟨C, hC, fun X A B hX hA1 hAX hB1 hBX => ?_⟩
    rw [zeroMode_neg (by linarith) (by linarith) (by linarith)]
    exact hb X B A hX hB1 hBX hA1 hAX

end MobiusDeterminant.Determinant
