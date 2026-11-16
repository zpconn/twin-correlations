import MobiusDeterminant.Unconditional.LevelFinite

/-!
# Finite-frequency part of the tensor bound (one orientation, asymmetric range)

The analogue of `Level.finite_part_bound` under the hypotheses of the mean-value theorem
instead of `B ≤ A ≤ N₀^{9/17-η}`: with `T = AB/N₀` and room `N₀^ε`,

  `N₀^ε T ≤ A^{1/6}`,  `A^{2/3} (N₀^ε T)² ≤ B`,

the frequencies `1 ≤ h ≤ M ≤ 4ℓAB N₀^{ε₀-1}` contribute
`≪ P^{kV} N₀^{1+ε} (A^{-1/12} T^{3/4} + A^{-2/3} B^{1/2} T + B^{-1/2} T)`.

Proof: as for `Level.finite_part_bound` (dyadic blocks, `blockF_tempered`, `core_block`), with
the exponent bookkeeping of `mvt_conditions'` and `phi_bound'`; the frequency length
`Hn = 2M ≤ 16 N₀^{ε₀} T` is at most `N₀^ε T` once `N₀^{ε/2} ≥ 16`.  For smaller `N₀` the
trivial bound suffices, since `N₀^{1+ε} B^{-1/2} T = N₀^ε A B^{1/2} ≥ 1`.
-/

open Finset Real
open scoped ArithmeticFunction.Moebius

namespace MobiusDeterminant

namespace Determinant

namespace Tensor

open MobiusDeterminant.Level MobiusDeterminant.Level.Finite

/-- The three terms of the tensor bound, with `A = D_max`, `B = D_min`, `T = AB/N₀`. -/
noncomputable def R3 (N₀ A B : ℝ) : ℝ :=
  A ^ (-(1 : ℝ) / 12) * (A * B / N₀) ^ ((3 : ℝ) / 4)
    + A ^ (-(2 : ℝ) / 3) * B ^ ((1 : ℝ) / 2) * (A * B / N₀)
    + B ^ (-(1 : ℝ) / 2) * (A * B / N₀)

lemma R3_nonneg {N₀ A B : ℝ} (hN : 0 < N₀) (hA : 0 < A) (hB : 0 < B) : 0 ≤ R3 N₀ A B := by
  unfold R3; positivity

/-- `N₀^{1+ε} R3 ≥ N₀^{1+ε} B^{-1/2} T = N₀^ε A B^{1/2} ≥ 1`. -/
lemma one_le_R3 {N₀ A B ε : ℝ} (hN : 1 ≤ N₀) (hε : 0 ≤ ε) (hA : 1 ≤ A) (hB : 1 ≤ B) :
    1 ≤ N₀ ^ (1 + ε) * R3 N₀ A B := by
  have hNpos : 0 < N₀ := by linarith
  have hApos : 0 < A := by linarith
  have hBpos : 0 < B := by linarith
  have h3 : 1 ≤ N₀ ^ (1 + ε) * (B ^ (-(1 : ℝ) / 2) * (A * B / N₀)) := by
    rw [← Real.log_le_log_iff (by norm_num) (by positivity), Real.log_one,
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_rpow hNpos, Real.log_rpow hBpos, Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity)]
    have h1 := Real.log_nonneg hN
    have h2 := Real.log_nonneg hA
    have h3 := Real.log_nonneg hB
    have h4 : 0 ≤ ε * Real.log N₀ := by positivity
    nlinarith
  refine h3.trans ?_
  unfold R3
  gcongr
  have : 0 ≤ A ^ (-(1 : ℝ) / 12) * (A * B / N₀) ^ ((3 : ℝ) / 4)
      + A ^ (-(2 : ℝ) / 3) * B ^ ((1 : ℝ) / 2) * (A * B / N₀) := by positivity
  linarith

/-- The hypotheses of `core_block` from those of the tensor bound. -/
lemma mvt_conditions' {N₀ A B M ℓ ε ε₀ : ℝ} (hN : 1 ≤ N₀) (h16 : 16 ≤ N₀ ^ (ε / 2))
    (hε₀2 : ε₀ ≤ ε / 2) (hℓ2 : ℓ ≤ 2) (hB : 1 ≤ B) (hBA : B ≤ A) (hAN : A ≤ N₀)
    (hM1 : 1 ≤ M) (hM : M ≤ 4 * ℓ * A * B * N₀ ^ (ε₀ - 1))
    (h1 : N₀ ^ ε * (A * B / N₀) ≤ A ^ ((1 : ℝ) / 6))
    (h2 : A ^ ((2 : ℝ) / 3) * (N₀ ^ ε * (A * B / N₀)) ^ 2 ≤ B) :
    2 ≤ A ∧ 1 ≤ B ∧ 2 * M ≤ A ^ ((1 : ℝ) / 6) ∧ A ^ ((2 : ℝ) / 3) * (2 * M) ^ 2 ≤ B ∧
      2 * M ≤ 16 * N₀ ^ ε₀ * (A * B / N₀) ∧ M ≤ 8 * N₀ := by
  have hNpos : 0 < N₀ := by linarith
  have hApos : 0 < A := by linarith
  have hBpos : 0 < B := by linarith
  have hT0 : 0 ≤ A * B / N₀ := by positivity
  have hNe : 0 < N₀ ^ ε₀ := by positivity
  have h2M : 2 * M ≤ 16 * N₀ ^ ε₀ * (A * B / N₀) := by
    have e : N₀ ^ (ε₀ - 1) = N₀ ^ ε₀ / N₀ := Real.rpow_sub_one hNpos.ne' ε₀
    rw [e] at hM
    have e2 : 4 * ℓ * A * B * (N₀ ^ ε₀ / N₀) = (4 * ℓ) * (N₀ ^ ε₀ * (A * B / N₀)) := by ring
    have e3 : 16 * N₀ ^ ε₀ * (A * B / N₀) = 2 * (8 * (N₀ ^ ε₀ * (A * B / N₀))) := by ring
    have hX : 0 ≤ N₀ ^ ε₀ * (A * B / N₀) := by positivity
    have : (4 * ℓ) * (N₀ ^ ε₀ * (A * B / N₀)) ≤ 8 * (N₀ ^ ε₀ * (A * B / N₀)) := by
      apply mul_le_mul_of_nonneg_right _ hX; linarith
    rw [e3]
    rw [e2] at hM
    linarith
  have h16' : 16 * N₀ ^ ε₀ ≤ N₀ ^ ε := by
    calc 16 * N₀ ^ ε₀ ≤ N₀ ^ (ε / 2) * N₀ ^ (ε / 2) := by
          apply mul_le_mul h16 (Real.rpow_le_rpow_of_exponent_le hN hε₀2) hNe.le (by positivity)
      _ = N₀ ^ ε := by rw [← Real.rpow_add hNpos]; ring_nf
  have h2M' : 2 * M ≤ N₀ ^ ε * (A * B / N₀) :=
    h2M.trans (mul_le_mul_of_nonneg_right h16' hT0)
  have hM6 : 2 * M ≤ A ^ ((1 : ℝ) / 6) := h2M'.trans h1
  refine ⟨?_, hB, hM6, ?_, h2M, ?_⟩
  · by_contra hA
    push Not at hA
    have : A ^ ((1 : ℝ) / 6) < 2 := by
      calc A ^ ((1 : ℝ) / 6) ≤ 2 ^ ((1 : ℝ) / 6) :=
            Real.rpow_le_rpow hApos.le hA.le (by norm_num)
        _ < 2 ^ (1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    linarith
  · calc A ^ ((2 : ℝ) / 3) * (2 * M) ^ 2 ≤ A ^ ((2 : ℝ) / 3) * (N₀ ^ ε * (A * B / N₀)) ^ 2 := by
          gcongr
      _ ≤ B := h2
  · have : A ^ ((1 : ℝ) / 6) ≤ A := by
      calc A ^ ((1 : ℝ) / 6) ≤ A ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
        _ = A := Real.rpow_one A
    linarith

/-- The three terms of the mean-value bound, after the prefactor `N₀/(ℓAB) · B^{1/2}`. -/
lemma phi_bound' {N₀ A B Hn ℓ ε₀ : ℝ} (hN : 1 ≤ N₀) (hε : 0 ≤ ε₀)
    (hℓ : 1 ≤ ℓ) (hApos : 0 < A) (hBpos : 0 < B) (hHn : 0 < Hn)
    (hH : Hn ≤ 16 * N₀ ^ ε₀ * (A * B / N₀)) :
    N₀ / (ℓ * A * B) * B ^ ((1 : ℝ) / 2) *
        (A ^ ((11 : ℝ) / 12) * B ^ ((1 : ℝ) / 2) * Hn ^ ((3 : ℝ) / 4)
          + A ^ ((1 : ℝ) / 3) * B * Hn + A * Hn)
      ≤ 16 * N₀ ^ (1 + ε₀) * R3 N₀ A B := by
  have hNpos : 0 < N₀ := by linarith
  have hℓpos : 0 < ℓ := by linarith
  have hx0 : 0 ≤ Real.log N₀ := Real.log_nonneg hN
  have hl2 := Real.log_two_gt_d9
  have hlogℓ : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ
  have hT : Real.log (A * B / N₀) = Real.log A + Real.log B - Real.log N₀ := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  have ht : Real.log Hn ≤ Real.log 16 + ε₀ * Real.log N₀ + Real.log (A * B / N₀) := by
    have := Real.log_le_log hHn hH
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_rpow hNpos] at this
    exact this
  rw [log_sixteen, hT] at ht
  have hv0 : 0 ≤ ε₀ * Real.log N₀ := by positivity
  have hpre : Real.log (N₀ / (ℓ * A * B) * B ^ ((1 : ℝ) / 2)) =
      Real.log N₀ - (Real.log ℓ + Real.log A + Real.log B) + 1 / 2 * Real.log B := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_rpow hBpos]
  have hRHS : ∀ c : ℝ, 0 < c → Real.log (c * N₀ ^ (1 + ε₀)) =
      Real.log c + (1 + ε₀) * Real.log N₀ := by
    intro c hc
    rw [Real.log_mul hc.ne' (by positivity), Real.log_rpow hNpos]
  set T : ℝ := A * B / N₀ with hTdef
  have hTpos : 0 < T := by positivity
  have hL : ∀ X : ℝ, 0 < X → Real.log (N₀ / (ℓ * A * B) * B ^ ((1 : ℝ) / 2) * X) =
      Real.log N₀ - (Real.log ℓ + Real.log A + Real.log B) + 1 / 2 * Real.log B +
        Real.log X := by
    intro X hX
    rw [Real.log_mul (by positivity) hX.ne', hpre]
  have T1 : N₀ / (ℓ * A * B) * B ^ ((1 : ℝ) / 2) *
      (A ^ ((11 : ℝ) / 12) * B ^ ((1 : ℝ) / 2) * Hn ^ ((3 : ℝ) / 4)) ≤
      8 * N₀ ^ (1 + ε₀) * (A ^ (-(1 : ℝ) / 12) * T ^ ((3 : ℝ) / 4)) := by
    have eL : Real.log (A ^ ((11 : ℝ) / 12) * B ^ ((1 : ℝ) / 2) * Hn ^ ((3 : ℝ) / 4)) =
        11 / 12 * Real.log A + 1 / 2 * Real.log B + 3 / 4 * Real.log Hn := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
        (by positivity), Real.log_rpow hApos, Real.log_rpow hBpos, Real.log_rpow hHn]
    have eR : Real.log (8 * N₀ ^ (1 + ε₀) * (A ^ (-(1 : ℝ) / 12) * T ^ ((3 : ℝ) / 4))) =
        3 * Real.log 2 + (1 + ε₀) * Real.log N₀ + (-(1 : ℝ) / 12 * Real.log A +
          3 / 4 * (Real.log A + Real.log B - Real.log N₀)) := by
      rw [Real.log_mul (by positivity) (by positivity), hRHS 8 (by norm_num), log_eight,
        Real.log_mul (by positivity) (by positivity), Real.log_rpow hApos,
        Real.log_rpow hTpos, hT]
    rw [← Real.log_le_log_iff (by positivity) (by positivity), hL _ (by positivity), eL, eR]
    nlinarith
  have T2 : N₀ / (ℓ * A * B) * B ^ ((1 : ℝ) / 2) * (A ^ ((1 : ℝ) / 3) * B * Hn)
      ≤ 16 * N₀ ^ (1 + ε₀) * (A ^ (-(2 : ℝ) / 3) * B ^ ((1 : ℝ) / 2) * T) := by
    have eL : Real.log (A ^ ((1 : ℝ) / 3) * B * Hn) =
        1 / 3 * Real.log A + Real.log B + Real.log Hn := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
        (by positivity), Real.log_rpow hApos]
    have eR : Real.log (16 * N₀ ^ (1 + ε₀) * (A ^ (-(2 : ℝ) / 3) * B ^ ((1 : ℝ) / 2) * T)) =
        4 * Real.log 2 + (1 + ε₀) * Real.log N₀ + (-(2 : ℝ) / 3 * Real.log A +
          1 / 2 * Real.log B + (Real.log A + Real.log B - Real.log N₀)) := by
      rw [Real.log_mul (by positivity) (by positivity), hRHS 16 (by norm_num), log_sixteen,
        Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
        (by positivity), Real.log_rpow hApos, Real.log_rpow hBpos, hT]
    rw [← Real.log_le_log_iff (by positivity) (by positivity), hL _ (by positivity), eL, eR]
    nlinarith
  have T3 : N₀ / (ℓ * A * B) * B ^ ((1 : ℝ) / 2) * (A * Hn) ≤
      16 * N₀ ^ (1 + ε₀) * (B ^ (-(1 : ℝ) / 2) * T) := by
    have eL : Real.log (A * Hn) = Real.log A + Real.log Hn :=
      Real.log_mul (by positivity) (by positivity)
    have eR : Real.log (16 * N₀ ^ (1 + ε₀) * (B ^ (-(1 : ℝ) / 2) * T)) =
        4 * Real.log 2 + (1 + ε₀) * Real.log N₀ + (-(1 : ℝ) / 2 * Real.log B +
          (Real.log A + Real.log B - Real.log N₀)) := by
      rw [Real.log_mul (by positivity) (by positivity), hRHS 16 (by norm_num), log_sixteen,
        Real.log_mul (by positivity) (by positivity), Real.log_rpow hBpos, hT]
    rw [← Real.log_le_log_iff (by positivity) (by positivity), hL _ (by positivity), eL, eR]
    nlinarith
  have hX1 : 0 ≤ N₀ ^ (1 + ε₀) * (A ^ (-(1 : ℝ) / 12) * T ^ ((3 : ℝ) / 4)) := by positivity
  unfold R3
  rw [← hTdef]
  calc N₀ / (ℓ * A * B) * B ^ ((1 : ℝ) / 2) *
        (A ^ ((11 : ℝ) / 12) * B ^ ((1 : ℝ) / 2) * Hn ^ ((3 : ℝ) / 4)
          + A ^ ((1 : ℝ) / 3) * B * Hn + A * Hn)
      = N₀ / (ℓ * A * B) * B ^ ((1 : ℝ) / 2) *
          (A ^ ((11 : ℝ) / 12) * B ^ ((1 : ℝ) / 2) * Hn ^ ((3 : ℝ) / 4))
        + N₀ / (ℓ * A * B) * B ^ ((1 : ℝ) / 2) * (A ^ ((1 : ℝ) / 3) * B * Hn)
        + N₀ / (ℓ * A * B) * B ^ ((1 : ℝ) / 2) * (A * Hn) := by ring
    _ ≤ 8 * N₀ ^ (1 + ε₀) * (A ^ (-(1 : ℝ) / 12) * T ^ ((3 : ℝ) / 4))
        + 16 * N₀ ^ (1 + ε₀) * (A ^ (-(2 : ℝ) / 3) * B ^ ((1 : ℝ) / 2) * T)
        + 16 * N₀ ^ (1 + ε₀) * (B ^ (-(1 : ℝ) / 2) * T) := by gcongr
    _ ≤ _ := by nlinarith

/-- **Finite-frequency part** in the range of the mean-value theorem (orientation `B ≤ A`). -/
theorem finite_part_bound' (hMV : MeanValueThm) (hM : MellinSeparation) :
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ kV : ℕ, ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ ε / 4 ∧
    ∃ C > (0 : ℝ),
    ∀ (N₀ A B P ς : ℝ) (ℓ : ℕ) (ρ σ : ℤ) (M Ma Mb : ℕ) (ψ φa φb : ℝ → ℂ),
      2 ≤ N₀ → 1 ≤ B → B ≤ A → A ≤ N₀ →
      N₀ ^ ε * (A * B / N₀) ≤ A ^ ((1 : ℝ) / 6) →
      A ^ ((2 : ℝ) / 3) * (N₀ ^ ε * (A * B / N₀)) ^ 2 ≤ B →
      (ℓ = 1 ∨ ℓ = 2) → (ς = 1 ∨ ς = -1) → |ρ| ≤ 2 → σ ≠ 0 → |σ| ≤ 2 →
      (M : ℝ) ≤ 4 * ℓ * A * B * N₀ ^ (ε₀ - 1) → ⌊2 * A⌋₊ ≤ Ma →
      1 ≤ P → TemperedOn ψ P 0 (1/2) 2 → TemperedOn φa P kV (1/2) 2 →
      (∀ x, ‖φb x‖ ≤ 1) → (∀ x, x ∉ Set.Icc (1/2 : ℝ) 2 → φb x = 0) →
      ‖∑ b ∈ (Finset.Icc 1 Mb).filter Odd,
          ∑ a ∈ (Finset.Icc 1 Ma).filter (fun a => Nat.Coprime a (2 * b)),
            (μ a : ℂ) * (μ b : ℂ) * φa ((a : ℝ) / A) * φb ((b : ℝ) / B) *
              ∑ h ∈ Finset.Icc 1 M,
                ((N₀ / (ℓ * a * b) : ℝ) : ℂ) * fourierR ψ (ς * (h * N₀ / (ℓ * a * b))) *
                  Complex.exp (2 * π * Complex.I * ((ρ * h : ℤ) : ℂ) / ((a * b : ℕ) : ℂ)) *
                  kfrac b (σ * h) a‖
        ≤ C * P ^ kV * (N₀ ^ (1 + ε) * R3 N₀ A B) := by
  intro ε hε hε1
  obtain ⟨kV, kF, Cc, hCc, hcore⟩ := core_block hMV hM (ε / 4) (by positivity)
  obtain ⟨c, hc1, cn, hcn, hblock⟩ := blockF_tempered kF
  have hkF : (0 : ℝ) ≤ kF := Nat.cast_nonneg kF
  set ε₀ : ℝ := ε / (4 * ((kF : ℝ) + 1)) with hε₀def
  have hε₀ : 0 < ε₀ := by positivity
  have hε₀k : ε₀ * kF + ε₀ = ε / 4 := by
    rw [hε₀def]; field_simp
  have hε₀4 : ε₀ ≤ ε / 4 := by nlinarith
  set δ : ℝ := ε / 4 with hδ
  set Kmain : ℝ := cn * Cc * (21 * c) ^ kF * 16 * (16 / δ + 1) with hKmain_def
  set N₁ : ℝ := (16 : ℝ) ^ ((ε / 2)⁻¹) with hN₁
  set Ktriv : ℝ := 48 * N₁ ^ 5 with hKtriv_def
  have hKmain : 0 ≤ Kmain := by rw [hKmain_def]; positivity
  have hKtriv : 0 < Ktriv := by rw [hKtriv_def]; positivity
  refine ⟨kV, ε₀, hε₀, hε₀4, Kmain + Ktriv, add_pos_of_nonneg_of_pos hKmain hKtriv, ?_⟩
  intro N₀ A B P ς ℓ ρ σ M Ma Mb ψ φa φb hN hB hBA hAN hH1 hH2 hℓ hς hρ hσ0 hσ2 hMle hMa hP
    hψ hφa hφb1 hφb0
  change ‖∑ b ∈ (Finset.Icc 1 Mb).filter Odd,
          ∑ a ∈ (Finset.Icc 1 Ma).filter (fun a => Nat.Coprime a (2 * b)),
            (μ a : ℂ) * (μ b : ℂ) * φa ((a : ℝ) / A) * φb ((b : ℝ) / B) *
              ∑ h ∈ Finset.Icc 1 M, term N₀ ς ℓ ρ σ ψ a b h‖ ≤ _
  have hNpos : 0 < N₀ := by linarith
  have hN1 : 1 ≤ N₀ := by linarith
  have hBpos : 0 < B := by linarith
  have hApos : 0 < A := by linarith
  have hA1 : 1 ≤ A := hB.trans hBA
  have hℓn : 1 ≤ ℓ := by rcases hℓ with h | h <;> omega
  have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓn
  have hℓ2 : (ℓ : ℝ) ≤ 2 := by
    have : ℓ ≤ 2 := by rcases hℓ with h | h <;> omega
    exact_mod_cast this
  have hPk : 1 ≤ P ^ kV := one_le_pow₀ hP
  have hR1 : 1 ≤ N₀ ^ (1 + ε) * R3 N₀ A B := one_le_R3 hN1 hε.le hA1 hB
  have hR0 : 0 ≤ R3 N₀ A B := R3_nonneg hNpos hApos hBpos
  have hNε : N₀ ^ (ε₀ - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hNε0 : 0 < N₀ ^ (ε₀ - 1) := by positivity
  have hMAB : (M : ℝ) ≤ 8 * A * B := by
    have h1 : ℓ * N₀ ^ (ε₀ - 1) ≤ 2 := by
      calc (ℓ : ℝ) * N₀ ^ (ε₀ - 1) ≤ 2 * 1 := mul_le_mul hℓ2 hNε hNε0.le (by norm_num)
        _ = 2 := by norm_num
    calc (M : ℝ) ≤ 4 * ℓ * A * B * N₀ ^ (ε₀ - 1) := hMle
      _ = 4 * (ℓ * N₀ ^ (ε₀ - 1)) * (A * B) := by ring
      _ ≤ 4 * 2 * (A * B) := by gcongr
      _ = 8 * A * B := by ring
  by_cases hmain : 1 ≤ M ∧ (16 : ℝ) ≤ N₀ ^ (ε / 2)
  swap
  · have htriv := trivial_bound (kV := kV) (ς := ς) (ρ := ρ) (σ := σ) (M := M) (Ma := Ma)
      (Mb := Mb) hNpos.le hApos hBpos hℓn hψ hφa hφb1 hφb0
    refine htriv.trans ?_
    have hfin : 0 ≤ (Kmain + Ktriv) * P ^ kV * (N₀ ^ (1 + ε) * R3 N₀ A B) := by positivity
    rcases not_and_or.1 hmain with hM0 | hNs
    · have : M = 0 := by omega
      subst this
      simpa using hfin
    · push Not at hNs
      have hNN₁ : N₀ ≤ N₁ := by
        have e : N₀ = (N₀ ^ (ε / 2)) ^ ((ε / 2)⁻¹) :=
          (Real.rpow_rpow_inv hNpos.le (by positivity)).symm
        rw [e, hN₁]
        exact Real.rpow_le_rpow (by positivity) hNs.le (by positivity)
      calc 6 * A * B * M * N₀ ≤ 6 * A * B * (8 * A * B) * N₀ := by gcongr
        _ = 48 * (A * B) ^ 2 * N₀ := by ring
        _ ≤ 48 * (N₀ * N₀) ^ 2 * N₀ := by gcongr; linarith
        _ = 48 * N₀ ^ 5 := by ring
        _ ≤ 48 * N₁ ^ 5 := by gcongr
        _ = Ktriv := rfl
        _ ≤ (Kmain + Ktriv) * 1 * 1 := by
          rw [mul_one, mul_one]; exact le_add_of_nonneg_left hKmain
        _ ≤ (Kmain + Ktriv) * P ^ kV * (N₀ ^ (1 + ε) * R3 N₀ A B) := by gcongr
  obtain ⟨hM1, hNbig⟩ := hmain
  have hM1r : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  obtain ⟨hA2, hB1, hHn6, hHn23, hHn16, hM8⟩ :=
    mvt_conditions' hN1 hNbig (by linarith) hℓ2 hB hBA hAN hM1r hMle hH1 hH2
  have hdec := sum_blocks ((Finset.Icc 1 Mb).filter Odd)
    (fun b => (Finset.Icc 1 Ma).filter (fun a => Nat.Coprime a (2 * b)))
    (fun a b => (μ a : ℂ) * (μ b : ℂ) * φa ((a : ℝ) / A) * φb ((b : ℝ) / B))
    (fun a b h => term N₀ ς ℓ ρ σ ψ a b h) M
  beta_reduce at hdec
  rw [hdec]
  set L := Nat.log 2 M with hL
  set Bblk : ℝ := cn * Cc * P ^ kV * ((21 * c) ^ kF * N₀ ^ (ε₀ * kF)) * N₀ ^ (ε / 4) *
    (16 * N₀ ^ (1 + ε₀) * R3 N₀ A B) with hBblk
  have hBblk0 : 0 ≤ Bblk := by rw [hBblk]; positivity
  have hblockbound : ∀ m ∈ Finset.range (L + 1),
      ‖∑ b ∈ (Finset.Icc 1 Mb).filter Odd,
          ∑ a ∈ (Finset.Icc 1 Ma).filter (fun a => Nat.Coprime a (2 * b)),
            (μ a : ℂ) * (μ b : ℂ) * φa ((a : ℝ) / A) * φb ((b : ℝ) / B) *
              ∑ h ∈ (Finset.Icc 1 M).filter (fun h => Nat.log 2 h = m),
                term N₀ ς ℓ ρ σ ψ a b h‖ ≤ Bblk := by
    intro m hm
    have hmL : m ≤ L := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
    set H : ℝ := (2 : ℝ) ^ m with hHdef
    have hHpos : 0 < H := by positivity
    have hHM : H ≤ M := by
      have : 2 ^ m ≤ M :=
        (Nat.pow_le_pow_right (by norm_num) hmL).trans (Nat.pow_log_le_self 2 (by omega))
      rw [hHdef]; exact_mod_cast this
    obtain ⟨F, hFt, hFid⟩ := hblock ψ P (ς * H * N₀ / (ℓ * A * B)) (ρ * H / (A * B)) hψ
    set blk := (Finset.Icc 1 M).filter (fun h => Nat.log 2 h = m) with hblk
    set K : ℂ := ((N₀ / (ℓ * A * B) * cn : ℝ) : ℂ) with hK
    have hbe := block_eq ((Finset.Icc 1 Mb).filter Odd)
      (fun b => (Finset.Icc 1 Ma).filter (fun a => Nat.Coprime a (2 * b)))
      (fun a b => (μ a : ℂ) * (μ b : ℂ) * φa ((a : ℝ) / A) * φb ((b : ℝ) / B))
      (fun a b h => term N₀ ς ℓ ρ σ ψ a b h)
      (fun a b (h : ℤ) => ((H / h : ℝ) : ℂ) * F ((h : ℝ) / H * (A / a) * (B / b)) *
        kfrac b (σ * h) a) blk K (by
        intro b hb a ha hc h hh
        obtain ⟨h1, _, h2m, h2m1⟩ := mem_blk hh
        have hb1 : 1 ≤ b := (Finset.mem_Icc.1 (Finset.mem_filter.1 hb).1).1
        have ha1 : 1 ≤ a := (Finset.mem_Icc.1 (Finset.mem_filter.1 ha).1).1
        have hφa0 : φa ((a : ℝ) / A) ≠ 0 := fun h0 => hc (by rw [h0]; ring)
        have hφb0' : φb ((b : ℝ) / B) ≠ 0 := fun h0 => hc (by rw [h0]; ring)
        have haA : (a : ℝ) / A ∈ Set.Icc (1 / 2 : ℝ) 2 := by
          by_contra hn; exact hφa0 (tempered_zero hφa hn)
        have hbB : (b : ℝ) / B ∈ Set.Icc (1 / 2 : ℝ) 2 := by
          by_contra hn; exact hφb0' (hφb0 _ hn)
        have ha' : (0 : ℝ) < a := by exact_mod_cast ha1
        have hb' : (0 : ℝ) < b := by exact_mod_cast hb1
        have u1 : 1 ≤ (h : ℝ) / H := by
          rw [le_div_iff₀ hHpos, one_mul, hHdef]; exact_mod_cast h2m
        have u2 : (h : ℝ) / H ≤ 2 := by
          rw [div_le_iff₀ hHpos, hHdef]
          have : (h : ℝ) < (2 : ℝ) ^ (m + 1) := by exact_mod_cast h2m1
          rw [pow_succ] at this; linarith
        have v1 : 1 / 2 ≤ A / a := by
          have := haA.2; rw [div_le_iff₀ hApos] at this
          rw [le_div_iff₀ ha']; linarith
        have v2 : A / a ≤ 2 := by
          have := haA.1; rw [le_div_iff₀ hApos] at this
          rw [div_le_iff₀ ha']; linarith
        have w1 : 1 / 2 ≤ B / b := by
          have := hbB.2; rw [div_le_iff₀ hBpos] at this
          rw [le_div_iff₀ hb']; linarith
        have w2 : B / b ≤ 2 := by
          have := hbB.1; rw [le_div_iff₀ hBpos] at this
          rw [div_le_iff₀ hb']; linarith
        have hs : (h : ℝ) / H * (A / a) * (B / b) ∈ Set.Icc (1 / 4 : ℝ) 8 := by
          constructor
          · calc (1 / 4 : ℝ) = 1 * (1 / 2) * (1 / 2) := by norm_num
              _ ≤ (h : ℝ) / H * (A / a) * (B / b) := by gcongr
          · calc (h : ℝ) / H * (A / a) * (B / b) ≤ 2 * 2 * 2 := by gcongr
              _ = 8 := by norm_num
        exact term_eq hApos hBpos hHpos hℓn ha1 hb1 h1 hcn.ne' (hFid _ hs))
    beta_reduce at hbe
    rw [hbe]
    -- the core estimate
    set Y₁ : ℝ := ς * H * N₀ / (ℓ * A * B) with hY₁
    set Y₂ : ℝ := ρ * H / (A * B) with hY₂
    set PF : ℝ := c * (1 + |Y₁| + |Y₂|) with hPF
    have hPF1 : 1 ≤ PF := by
      rw [hPF]
      exact one_le_mul_of_one_le_of_one_le hc1 (by linarith [abs_nonneg Y₁, abs_nonneg Y₂])
    have h𝓗 : ∀ h ∈ blk.map (Nat.castEmbedding : ℕ ↪ ℤ),
        H ≤ (h : ℝ) ∧ (h : ℝ) < 2 * H ∧ |σ * h| ≤ ((2 * M : ℕ) : ℤ) := by
      intro h hh
      rw [Finset.mem_map] at hh
      obtain ⟨n, hn, rfl⟩ := hh
      obtain ⟨_, nM, n2m, n2m1⟩ := mem_blk hn
      simp only [Nat.castEmbedding_apply, Int.cast_natCast]
      refine ⟨?_, ?_, ?_⟩
      · rw [hHdef]; exact_mod_cast n2m
      · have : (n : ℝ) < (2 : ℝ) ^ (m + 1) := by exact_mod_cast n2m1
        rw [pow_succ] at this; rw [hHdef]; linarith
      · have hnM : (n : ℤ) ≤ M := by exact_mod_cast nM
        calc |σ * (n : ℤ)| = |σ| * n := by rw [abs_mul, Nat.abs_cast]
          _ ≤ 2 * M := by gcongr
          _ = ((2 * M : ℕ) : ℤ) := by push_cast; ring
    have hcast : ((2 * M : ℕ) : ℝ) = 2 * (M : ℝ) := by push_cast; ring
    have hcoreb := hcore A B (2 * M) H σ (blk.map Nat.castEmbedding) Ma Mb φa φb F P PF
      hA2 hB1 hBA (by omega) (by rw [hcast]; exact hHn6) (by rw [hcast]; exact hHn23) hHpos
      hσ0 h𝓗 hMa hP hφa hφb1 hφb0 hPF1 hFt
    rw [hcast] at hcoreb
    -- bounds on the parameters
    have hY1 : |Y₁| ≤ 4 * N₀ ^ ε₀ := by
      have hς1 : |ς| = 1 := by rcases hς with h | h <;> simp [h]
      have hden : 0 < (ℓ : ℝ) * A * B := by positivity
      rw [hY₁, abs_div, abs_mul, abs_mul, hς1, abs_of_pos hHpos, abs_of_pos hNpos,
        abs_of_pos hden, div_le_iff₀ hden]
      calc 1 * H * N₀ ≤ (4 * ℓ * A * B * N₀ ^ (ε₀ - 1)) * N₀ := by
            rw [one_mul]; exact mul_le_mul_of_nonneg_right (hHM.trans hMle) hNpos.le
        _ = 4 * N₀ ^ ε₀ * (ℓ * A * B) := by
          rw [Real.rpow_sub_one hNpos.ne']; field_simp
    have hY2 : |Y₂| ≤ 16 := by
      have hden : 0 < A * B := by positivity
      have hρ' : |(ρ : ℝ)| ≤ 2 := by
        rw [← Int.cast_abs]; exact_mod_cast hρ
      rw [hY₂, abs_div, abs_mul, abs_of_pos hHpos, abs_of_pos hden, div_le_iff₀ hden]
      have h1 : ℓ * N₀ ^ (ε₀ - 1) ≤ 2 := by
        calc (ℓ : ℝ) * N₀ ^ (ε₀ - 1) ≤ 2 * 1 := mul_le_mul hℓ2 hNε hNε0.le (by norm_num)
          _ = 2 := by norm_num
      calc |(ρ : ℝ)| * H ≤ 2 * M := by gcongr
        _ ≤ 2 * (4 * ℓ * A * B * N₀ ^ (ε₀ - 1)) := by linarith
        _ = 8 * (ℓ * N₀ ^ (ε₀ - 1)) * (A * B) := by ring
        _ ≤ 8 * 2 * (A * B) := by gcongr
        _ = 16 * (A * B) := by ring
    have hNε1 : 1 ≤ N₀ ^ ε₀ := Real.one_le_rpow hN1 hε₀.le
    have hPFb : PF ≤ 21 * c * N₀ ^ ε₀ := by
      rw [hPF]
      calc c * (1 + |Y₁| + |Y₂|) ≤ c * (N₀ ^ ε₀ + 4 * N₀ ^ ε₀ + 16 * N₀ ^ ε₀) := by
            gcongr; linarith
        _ = 21 * c * N₀ ^ ε₀ := by ring
    have hPFk : PF ^ kF ≤ (21 * c) ^ kF * N₀ ^ (ε₀ * kF) := by
      calc PF ^ kF ≤ (21 * c * N₀ ^ ε₀) ^ kF := pow_le_pow_left₀ (by linarith) hPFb kF
        _ = (21 * c) ^ kF * N₀ ^ (ε₀ * kF) := by
          rw [mul_pow, Real.rpow_mul_natCast hNpos.le]
    have hAε : A ^ (ε / 4) ≤ N₀ ^ (ε / 4) :=
      Real.rpow_le_rpow hApos.le hAN (by positivity)
    have hphi := phi_bound' (Hn := 2 * (M : ℝ)) hN1 hε₀.le hℓ1 hApos hBpos (by positivity)
      hHn16
    have hKn : ‖K‖ = N₀ / (ℓ * A * B) * cn := by
      rw [hK, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [norm_mul, hKn]
    calc N₀ / (ℓ * A * B) * cn * ‖_‖
        ≤ N₀ / (ℓ * A * B) * cn * (Cc * P ^ kV * PF ^ kF * B ^ ((1 : ℝ) / 2) * A ^ (ε / 4) *
            (A ^ ((11 : ℝ) / 12) * B ^ ((1 : ℝ) / 2) * (2 * (M : ℝ)) ^ ((3 : ℝ) / 4)
              + A ^ ((1 : ℝ) / 3) * B * (2 * (M : ℝ)) + A * (2 * (M : ℝ)))) := by
          gcongr
      _ = cn * Cc * P ^ kV * PF ^ kF * A ^ (ε / 4) *
            (N₀ / (ℓ * A * B) * B ^ ((1 : ℝ) / 2) *
              (A ^ ((11 : ℝ) / 12) * B ^ ((1 : ℝ) / 2) * (2 * (M : ℝ)) ^ ((3 : ℝ) / 4)
                + A ^ ((1 : ℝ) / 3) * B * (2 * (M : ℝ)) + A * (2 * (M : ℝ)))) := by ring
      _ ≤ cn * Cc * P ^ kV * ((21 * c) ^ kF * N₀ ^ (ε₀ * kF)) * N₀ ^ (ε / 4) *
            (16 * N₀ ^ (1 + ε₀) * R3 N₀ A B) := by gcongr
      _ = Bblk := by rw [hBblk]
  have hcount := log_count (M := M) (N₀ := N₀) (δ := δ) (by positivity) (by linarith) hN1
    hM8 hM1
  have hexp : N₀ ^ δ * (N₀ ^ (ε₀ * kF) * N₀ ^ (ε / 4) * N₀ ^ (1 + ε₀)) ≤ N₀ ^ (1 + ε) := by
    rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
    apply Real.rpow_le_rpow_of_exponent_le hN1
    linarith
  calc _ ≤ ∑ m ∈ Finset.range (L + 1),
        ‖∑ b ∈ (Finset.Icc 1 Mb).filter Odd,
          ∑ a ∈ (Finset.Icc 1 Ma).filter (fun a => Nat.Coprime a (2 * b)),
            (μ a : ℂ) * (μ b : ℂ) * φa ((a : ℝ) / A) * φb ((b : ℝ) / B) *
              ∑ h ∈ (Finset.Icc 1 M).filter (fun h => Nat.log 2 h = m),
                term N₀ ς ℓ ρ σ ψ a b h‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ Finset.range (L + 1), Bblk := Finset.sum_le_sum hblockbound
    _ = ((L : ℝ) + 1) * Bblk := by simp
    _ ≤ ((16 / δ + 1) * N₀ ^ δ) * Bblk := by gcongr
    _ = Kmain * P ^ kV *
          ((N₀ ^ δ * (N₀ ^ (ε₀ * kF) * N₀ ^ (ε / 4) * N₀ ^ (1 + ε₀))) * R3 N₀ A B) := by
        rw [hBblk, hKmain_def]; ring
    _ ≤ Kmain * P ^ kV * (N₀ ^ (1 + ε) * R3 N₀ A B) := by gcongr
    _ ≤ (Kmain + Ktriv) * P ^ kV * (N₀ ^ (1 + ε) * R3 N₀ A B) := by
        gcongr; exact le_add_of_nonneg_right hKtriv.le

end Tensor

end Determinant

end MobiusDeterminant
