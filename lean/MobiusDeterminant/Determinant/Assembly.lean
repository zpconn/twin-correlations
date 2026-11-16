import MobiusDeterminant.Determinant.Statement

/-!
# Theorem 1.3 and Corollary 1.4: assembly from the interfaces

Real-exponent bookkeeping and a compactness argument turning `DetErrorBound` and
`ZeroModeBound` (stated in terms of `X, A, B`) into `DetPowerSaving`, `DetCancellation`
and `DetDiagonal` (stated in terms of `A = X^x`, `B = X^y` with `(x,y)` in a compact
`K ⊂ Ω`).

With `m = min(x,y)`, `M = max(x,y)`: `X/A = X^{1-x}`, `X/B = X^{1-y}`, `X/(AB) = X^{1-x-y}`,
`max(X/A, X/B) = X^{1-m}`, `min(X/A, X/B) = X^{1-M}`.  The three terms of `DetErrorBound`
are `X^{1+ε'}` times `X^{-σ}`, `X^{-(2m+9M-5)/6}` and `X^{-(2m+M-1)/2}`, and both
side conditions of `DetErrorBound` hold as soon as `ε' ≤ 2σ`, which is arranged uniformly
on `K` since `σ` is continuous and positive on `Ω`.
-/

open Real

namespace MobiusDeterminant

namespace Determinant

namespace Assembly

lemma continuous_sigmaExp : Continuous sigmaExp := by
  unfold sigmaExp
  exact (((continuous_const.mul (continuous_fst.min continuous_snd)).add
    (continuous_const.mul (continuous_fst.max continuous_snd))).sub continuous_const).div_const _

lemma sigmaExp_pos {p : ℝ × ℝ} (hp : p ∈ Omega) : 0 < sigmaExp p := by
  obtain ⟨-, -, -, -, h⟩ := hp
  unfold sigmaExp
  linarith

/-- `σ` is bounded below by a positive constant on a compact subset of `Ω`. -/
lemma exists_sigma_lower {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKO : K ⊆ Omega) :
    ∃ σ₀ > 0, ∀ p ∈ K, σ₀ ≤ sigmaExp p := by
  rcases K.eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, by simp [h]⟩
  · obtain ⟨p₀, hp₀, hmin⟩ := hK.exists_isMinOn h continuous_sigmaExp.continuousOn
    exact ⟨sigmaExp p₀, sigmaExp_pos (hKO hp₀), fun p hp => isMinOn_iff.mp hmin p hp⟩

lemma rpow_le_sqrt {X x : ℝ} (hX : 1 ≤ X) (hx : x ≤ 1 / 2) : X ^ x ≤ Real.sqrt X := by
  rw [Real.sqrt_eq_rpow]
  exact Real.rpow_le_rpow_of_exponent_le hX hx

/-- Final comparison of exponents in the power-saving bound. -/
lemma final_bound {X C ε' e₀ e₁ e₂ e₃ : ℝ} (hX : 1 ≤ X) (hC : 0 ≤ C)
    (h₁ : 1 + ε' + e₁ ≤ e₀) (h₂ : 1 + ε' + e₂ ≤ e₀) (h₃ : 1 + ε' + e₃ ≤ e₀)
    (h₄ : 1 / 2 ≤ e₀) :
    C * (X ^ (1 + ε') * (X ^ e₁ + X ^ e₂ + X ^ e₃) + X ^ ((1 : ℝ) / 2)) ≤
      4 * C * X ^ e₀ := by
  have hX0 : 0 < X := by linarith
  have k₁ : X ^ (1 + ε') * X ^ e₁ ≤ X ^ e₀ := by
    rw [← Real.rpow_add hX0]; exact Real.rpow_le_rpow_of_exponent_le hX h₁
  have k₂ : X ^ (1 + ε') * X ^ e₂ ≤ X ^ e₀ := by
    rw [← Real.rpow_add hX0]; exact Real.rpow_le_rpow_of_exponent_le hX h₂
  have k₃ : X ^ (1 + ε') * X ^ e₃ ≤ X ^ e₀ := by
    rw [← Real.rpow_add hX0]; exact Real.rpow_le_rpow_of_exponent_le hX h₃
  have k₄ : X ^ ((1 : ℝ) / 2) ≤ X ^ e₀ := Real.rpow_le_rpow_of_exponent_le hX h₄
  have : X ^ (1 + ε') * (X ^ e₁ + X ^ e₂ + X ^ e₃) + X ^ ((1 : ℝ) / 2) ≤ 4 * X ^ e₀ := by
    rw [mul_add, mul_add]; linarith
  calc C * (X ^ (1 + ε') * (X ^ e₁ + X ^ e₂ + X ^ e₃) + X ^ ((1 : ℝ) / 2))
      ≤ C * (4 * X ^ e₀) := mul_le_mul_of_nonneg_left this hC
    _ = 4 * C * X ^ e₀ := by ring

/-- `X^{-σ/2} ≤ e^{c²/(2σ)} exp(-c √log X)` for `X ≥ 1`. -/
lemma rpow_neg_le_exp {X σ c : ℝ} (hX : 1 ≤ X) (hσ : 0 < σ) :
    X ^ (-(σ / 2)) ≤ Real.exp (c ^ 2 / (2 * σ)) * Real.exp (-c * Real.sqrt (Real.log X)) := by
  have hX0 : 0 < X := by linarith
  rw [Real.rpow_def_of_pos hX0, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hL : 0 ≤ Real.log X := Real.log_nonneg hX
  have hs2 : Real.sqrt (Real.log X) ^ 2 = Real.log X := Real.sq_sqrt hL
  have hσ' : σ ≠ 0 := hσ.ne'
  obtain ⟨u, rfl⟩ : ∃ u, c = σ * u := ⟨c / σ, by field_simp⟩
  have e : (σ * u) ^ 2 / (2 * σ) = σ / 2 * u ^ 2 := by field_simp
  rw [e]
  generalize Real.sqrt (Real.log X) = s at hs2 ⊢
  rw [← hs2]
  nlinarith [mul_nonneg hσ.le (sq_nonneg (u - s))]

end Assembly

open Assembly

/-- **Theorem 1.3, (1.4)** from the error-term interface. -/
theorem detPowerSaving_of (hE : DetErrorBound) : DetPowerSaving := by
  intro K hK hKO κ hκ W hW ε hε
  obtain ⟨σ₀, hσ₀, hσK⟩ := exists_sigma_lower hK hKO
  obtain ⟨ε', hε'pos, hε'1, hε'2⟩ : ∃ ε', 0 < ε' ∧ ε' ≤ ε ∧ ε' ≤ 2 * σ₀ :=
    ⟨min ε (2 * σ₀), lt_min hε (by linarith), min_le_left _ _, min_le_right _ _⟩
  obtain ⟨C, hC0, hC⟩ := hE κ hκ W hW ε' hε'pos
  refine ⟨4 * C, by positivity, ?_⟩
  intro X hX p hp
  have hσp : σ₀ ≤ (8 * min p.1 p.2 + 9 * max p.1 p.2 - 8) / 12 := hσK p hp
  obtain ⟨hp1, hp1', hp2, hp2', hpΩ⟩ := hKO hp
  have hX0 : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hmM : min p.1 p.2 + max p.1 p.2 = p.1 + p.2 := min_add_max _ _
  have hm_le : min p.1 p.2 ≤ max p.1 p.2 := min_le_max
  have hM_le : max p.1 p.2 ≤ 1 / 2 := max_le hp1' hp2'
  have hσdef : sigmaExp p = (8 * min p.1 p.2 + 9 * max p.1 p.2 - 8) / 12 := rfl
  have hDx : X / X ^ p.1 = X ^ (1 - p.1) := by rw [Real.rpow_sub hX0, Real.rpow_one]
  have hDy : X / X ^ p.2 = X ^ (1 - p.2) := by rw [Real.rpow_sub hX0, Real.rpow_one]
  have hT : X / (X ^ p.1 * X ^ p.2) = X ^ (1 - p.1 - p.2) := by
    rw [sub_sub, Real.rpow_sub hX0, Real.rpow_one, Real.rpow_add hX0]
  have hmono : Monotone (fun t : ℝ => X ^ t) := Real.monotone_rpow_of_base_ge_one hX1
  have hmax : max (X / X ^ p.1) (X / X ^ p.2) = X ^ (1 - min p.1 p.2) := by
    rw [hDx, hDy, ← max_sub_sub_left]
    exact hmono.map_max.symm
  have hmin : min (X / X ^ p.1) (X / X ^ p.2) = X ^ (1 - max p.1 p.2) := by
    rw [hDx, hDy, ← min_sub_sub_left]
    exact hmono.map_min.symm
  have h₁ : X ^ ε' * (X / (X ^ p.1 * X ^ p.2)) ≤
      (max (X / X ^ p.1) (X / X ^ p.2)) ^ ((1 : ℝ) / 6) := by
    rw [hT, hmax, ← Real.rpow_mul hX0.le, ← Real.rpow_add hX0]
    apply Real.rpow_le_rpow_of_exponent_le hX1
    linarith
  have h₂ : (max (X / X ^ p.1) (X / X ^ p.2)) ^ ((2 : ℝ) / 3) *
      (X ^ ε' * (X / (X ^ p.1 * X ^ p.2))) ^ 2 ≤ min (X / X ^ p.1) (X / X ^ p.2) := by
    rw [hT, hmax, hmin, ← Real.rpow_mul hX0.le, ← Real.rpow_add hX0 ε', sq,
      ← Real.rpow_add hX0, ← Real.rpow_add hX0]
    apply Real.rpow_le_rpow_of_exponent_le hX1
    linarith
  have key := hC X (X ^ p.1) (X ^ p.2) hX (Real.one_le_rpow hX1 hp1.le)
    (rpow_le_sqrt hX1 hp1') (Real.one_le_rpow hX1 hp2.le) (rpow_le_sqrt hX1 hp2') h₁ h₂
  rw [hT, hmax, hmin] at key
  simp only [← Real.rpow_mul hX0.le, ← Real.rpow_add hX0] at key
  refine key.trans (final_bound hX1 hC0.le ?_ ?_ ?_ ?_) <;> rw [hσdef] <;> linarith

/-- **Theorem 1.3, (1.5)** from the error-term and zero-frequency interfaces. -/
theorem detCancellation_of (hE : DetErrorBound) (hZ : ZeroModeBound) : DetCancellation := by
  obtain ⟨c, hc, hZ'⟩ := hZ
  refine ⟨c, hc, ?_⟩
  intro K hK hKO κ hκ W hW
  obtain ⟨σ₀, hσ₀, hσK⟩ := exists_sigma_lower hK hKO
  obtain ⟨C₁, hC₁, h₁⟩ := detPowerSaving_of hE K hK hKO κ hκ W hW (σ₀ / 2) (by positivity)
  obtain ⟨C₂, hC₂, h₂⟩ := hZ' κ hκ W hW
  refine ⟨C₁ * Real.exp (c ^ 2 / (2 * σ₀)) + C₂, by positivity, ?_⟩
  intro X hX p hp
  have hX0 : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  obtain ⟨hp1, hp1', hp2, hp2', -⟩ := hKO hp
  have hz := h₂ X (X ^ p.1) (X ^ p.2) hX (Real.one_le_rpow hX1 hp1.le)
    (rpow_le_sqrt hX1 hp1') (Real.one_le_rpow hX1 hp2.le) (rpow_le_sqrt hX1 hp2')
  have hd := h₁ X hX p hp
  have hσp := hσK p hp
  have hpow : X ^ (1 - sigmaExp p + σ₀ / 2) ≤
      X * (Real.exp (c ^ 2 / (2 * σ₀)) * Real.exp (-c * Real.sqrt (Real.log X))) := by
    calc X ^ (1 - sigmaExp p + σ₀ / 2) ≤ X ^ (1 + -(σ₀ / 2)) :=
          Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
      _ = X * X ^ (-(σ₀ / 2)) := by rw [Real.rpow_add hX0, Real.rpow_one]
      _ ≤ X * (Real.exp (c ^ 2 / (2 * σ₀)) * Real.exp (-c * Real.sqrt (Real.log X))) :=
          mul_le_mul_of_nonneg_left (rpow_neg_le_exp hX1 hσ₀) hX0.le
  set D := detSum κ W (X ^ p.1) (X ^ p.2) X
  set Z := zeroMode κ W (X ^ p.1) (X ^ p.2) X
  calc ‖D‖ = ‖(D - Z) + Z‖ := by rw [sub_add_cancel]
    _ ≤ ‖D - Z‖ + ‖Z‖ := norm_add_le _ _
    _ ≤ C₁ * X ^ (1 - sigmaExp p + σ₀ / 2) + C₂ * X * Real.exp (-c * Real.sqrt (Real.log X)) :=
        add_le_add hd hz
    _ ≤ C₁ * (X * (Real.exp (c ^ 2 / (2 * σ₀)) * Real.exp (-c * Real.sqrt (Real.log X))))
          + C₂ * X * Real.exp (-c * Real.sqrt (Real.log X)) := by
        gcongr
    _ = (C₁ * Real.exp (c ^ 2 / (2 * σ₀)) + C₂) * X *
          Real.exp (-c * Real.sqrt (Real.log X)) := by ring

/-- **Corollary 1.4** from Theorem 1.3, (1.5). -/
theorem detDiagonal_of (hC : DetCancellation) : DetDiagonal := by
  obtain ⟨c, hc, hC'⟩ := hC
  refine ⟨c, hc, ?_⟩
  intro η hη κ hκ W hW
  have hKc : IsCompact ((fun x : ℝ => (x, x)) '' Set.Icc (8 / 17 + η) (1 / 2)) :=
    isCompact_Icc.image (by fun_prop)
  have hKO : (fun x : ℝ => (x, x)) '' Set.Icc (8 / 17 + η) (1 / 2) ⊆ Omega := by
    rintro _ ⟨x, ⟨hx1, hx2⟩, rfl⟩
    simp only [Omega, Set.mem_ofPred_eq, min_self, max_self]
    exact ⟨by linarith, hx2, by linarith, hx2, by linarith⟩
  obtain ⟨C, hC0, hCb⟩ := hC' _ hKc hKO κ hκ W hW
  exact ⟨C, hC0, fun X hX x hx1 hx2 => hCb X hX (x, x) ⟨x, ⟨hx1, hx2⟩, rfl⟩⟩

end Determinant

end MobiusDeterminant
