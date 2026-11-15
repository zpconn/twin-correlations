import MobiusDeterminant.Unconditional.MeanValueAssembly
import LeanPool.MarkoffModP.BGS.NumberTheory.DivisorBound

/-!
# The mean-value theorem (paper, Theorem 6.1)

`meanValueThm_of : BalancedBoxBound → MellinSeparation → MeanValueThm`.

Structure of the proof (files `MeanValue*.lean`):
* `MeanValueArith`: Heath-Brown's identity (`J = 5`) over `ℂ`, sharp dyadic boxes,
  collapsed coefficients `≤ τ(n)^9`;
* `MeanValueIncomplete`: incomplete Kloosterman sums over sharp intervals by completion
  over `ZMod q` and the Weil bound for squarefree moduli (Lean Pool), Abel summation for
  `n^{-iτ}`, gcd strata `g = (h,e)` and Möbius detection of `(n, 2g) = 1`;
* `MeanValueReal`: exponent bookkeeping (`Φ(U) ≪ D^{11/12}E^{1/2}H^{3/4}`, etc.);
* `MeanValueL2`: Minkowski in `ℓ²(e)`, also against the Mellin density;
* `MeanValueBox`: the dichotomy and the bound for one box (balanced: `BalancedBoxBound`;
  long: incomplete Kloosterman sums);
* `MeanValueAssembly`: Mellin separation of `V(d/D)` and the decomposition of `P_e`.
-/

open Finset Real MeasureTheory

namespace MobiusDeterminant

open MeanValue

/-- The divisor bound `τ(n) ≤ C n^ε` for all `n ≥ 1` (Lean Pool, BGS). -/
lemma exists_divBound {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) : ∃ dv : DivBound, dv.ε = ε := by
  obtain ⟨N₀, hN₀⟩ := BGS.NumberTheory.exists_threshold_card_divisors_le_rpow hε0
  refine ⟨⟨ε, N₀ + 1, hε0, hε1, by linarith [(Nat.cast_nonneg N₀ : (0 : ℝ) ≤ N₀)], ?_⟩, rfl⟩
  intro n hn
  have hpow : 1 ≤ (n : ℝ) ^ ε := Real.one_le_rpow (by exact_mod_cast hn) hε0.le
  have hN0 : (0 : ℝ) ≤ N₀ := Nat.cast_nonneg _
  by_cases h : N₀ ≤ n
  · have := hN₀ n h
    nlinarith
  · have h1 : (n.divisors.card : ℝ) ≤ n := by exact_mod_cast Nat.card_divisors_le_self n
    have h2 : (n : ℝ) ≤ N₀ := by exact_mod_cast (not_le.1 h).le
    nlinarith

/-- **Theorem 6.1** (mean-value theorem for Möbius–Kloosterman fractions), from the
balanced-box bound (paper, Prop. 5.1 with the gcd strata) and Mellin separation (Lemma 2.7). -/
theorem meanValueThm_of (hB : BalancedBoxBound) (hM : MellinSeparation) : MeanValueThm := by
  intro ε hε
  set ε₁ : ℝ := min ε 1 / 30 with hε₁
  have hmin0 : 0 < min ε 1 := lt_min hε one_pos
  have hε₁0 : 0 < ε₁ := by positivity
  have hε₁1 : ε₁ ≤ 1 := by have := min_le_right ε 1; rw [hε₁]; linarith
  have hε₁ε : ε₁ * 29 ≤ ε := by have := min_le_left ε 1; rw [hε₁]; linarith
  obtain ⟨dv, hdvε⟩ := exists_divBound hε₁0 hε₁1
  obtain ⟨CB, hCB0, hBat⟩ := balancedAt_of hB dv.hε0
  obtain ⟨CM, hCM0, k, hMk⟩ := hM (1 / 8) 8 (by norm_num) (by norm_num) 1
  have hCbox0 : 0 ≤ Cbox dv CB := by
    have := dv.hC; have := dv.hε0; unfold Cbox; positivity
  set Cfin : ℝ := 2 ^ 46 + 50 * (2 ^ 12 / ε₁) ^ 9 * Cbox dv CB * CM with hCfin
  have hCfin0 : 0 < Cfin := by positivity
  refine ⟨Cfin, hCfin0, k, ?_⟩
  intro D E P Hn V ν hD2 hE1 hED hH1 hHD hEH hP1 hV hν0 hν
  have hD0 : 0 < D := by linarith
  have hD1 : 1 ≤ D := by linarith
  have hPk : 1 ≤ P ^ k := one_le_pow₀ hP1
  have hDε : 1 ≤ D ^ ε := Real.one_le_rpow hD1 hε.le
  have hT0 : 0 ≤ target D E Hn := target_nonneg D E Hn hD0.le (by linarith)
  have hDH : D * Hn ≤ target D E Hn := by
    unfold target
    have : 0 ≤ D ^ ((11 : ℝ) / 12) * E ^ ((1 : ℝ) / 2) * (Hn : ℝ) ^ ((3 : ℝ) / 4) := by positivity
    have : 0 ≤ D ^ ((1 : ℝ) / 3) * E * Hn := by positivity
    linarith
  -- it suffices to bound the `ℓ²` norm
  suffices hsq : Real.sqrt (∑ e ∈ moduli E, ‖Pe D V ν Hn e‖ ^ 2) ≤
      Cfin * P ^ k * D ^ ε * target D E Hn by
    have h0 : 0 ≤ ∑ e ∈ moduli E, ‖Pe D V ν Hn e‖ ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
    have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq 2
    rw [Real.sq_sqrt h0] at this
    exact this
  have hVb : ∀ x, ‖V x‖ ≤ 1 := by
    intro x
    have := hV.2.2 0 (Nat.zero_le _) x
    simpa using this
  have hVsupp : ∀ x, x ∉ Set.Icc (1 / 8 : ℝ) 8 → V x = 0 := hV.2.1
  have hfinal_le : ∀ X : ℝ, X ≤ 2 ^ 46 * (D * Hn) → X ≤ Cfin * P ^ k * D ^ ε * target D E Hn := by
    intro X hX
    refine hX.trans ?_
    have h1 : (2 : ℝ) ^ 46 ≤ Cfin := by
      rw [hCfin]; have : 0 ≤ 50 * (2 ^ 12 / ε₁) ^ 9 * Cbox dv CB * CM := by positivity
      linarith
    calc (2 : ℝ) ^ 46 * (D * Hn) ≤ Cfin * 1 * 1 * target D E Hn := by
          rw [mul_one, mul_one]
          exact mul_le_mul h1 hDH (by positivity) hCfin0.le
      _ ≤ Cfin * P ^ k * D ^ ε * target D E Hn := by gcongr
  by_cases hDl : (2 : ℝ) ^ 78 ≤ D
  swap
  · -- bounded `D`: the trivial bound
    push Not at hDl
    refine hfinal_le _ ((Pe_small_bound hD2 hE1 hH1 V hVb ν hν).trans ?_)
    have h8E : Real.sqrt (8 * E) ≤ 2 ^ 41 := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith
    have : (0 : ℝ) ≤ 24 * D * Hn := by positivity
    calc Real.sqrt (8 * E) * (24 * D * Hn) ≤ 2 ^ 41 * (24 * D * Hn) :=
          mul_le_mul_of_nonneg_right h8E this
      _ ≤ 2 ^ 46 * (D * Hn) := by nlinarith
  -- large `D`
  let St : Setup := ⟨D, E, Hn, ν, hDl, hE1, hED, hH1, hHD, hEH, hν0, hν⟩
  obtain ⟨g, hgi1, hgI1, hrep0⟩ := hMk V P hP1 hV
  have hgi : Integrable (fun τ => (1 + |τ|) * ‖g τ‖) := by simpa using hgi1
  have hgI : ∫ τ, (1 + |τ|) * ‖g τ‖ ≤ CM * P ^ k := by simpa using hgI1
  have hrep : ∀ t : ℝ, 0 < t → V t = ∫ τ : ℝ, g τ * twist τ t := hrep0
  by_cases hgm : AEStronglyMeasurable g volume
  swap
  · -- a non-measurable density represents `V = 0` on `(0, ∞)`
    have hV0 : ∀ t : ℝ, 0 < t → V t = 0 := by
      intro t ht
      rw [hrep t ht, integral_undef]
      intro hint
      apply hgm
      refine (hint.aestronglyMeasurable.mul
        (Continuous.aestronglyMeasurable (f := fun τ : ℝ =>
          Complex.exp ((τ * Real.log t : ℝ) * Complex.I)) (by fun_prop))).congr
        (Filter.Eventually.of_forall fun τ => ?_)
      simp only [Pi.mul_apply, twist]
      rw [mul_assoc, ← Complex.exp_add]
      simp
    have hPe0 : ∀ e, Pe D V ν Hn e = 0 := by
      intro e
      rw [Pe_eq_sum]
      refine sum_eq_zero fun d hd => ?_
      rw [hV0 _ (div_pos (by exact_mod_cast (mem_Icc.1 hd).1) hD0), zero_mul, mul_zero]
    simp_rw [hPe0, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sum_const_zero,
      Real.sqrt_zero]
    have : 0 ≤ Cfin * P ^ k * D ^ ε * target D E Hn := by positivity
    exact this
  -- the main case
  obtain ⟨Km, hK1, hK2⟩ := exists_Km hD2
  set Lam := D ^ ε₁ with hLam
  have hLam1 : 1 ≤ Lam := Real.one_le_rpow hD1 hε₁0.le
  set Y : ℝ := Cbox dv CB * (D ^ dv.ε) ^ 20 * target D E Hn * ∫ τ, (1 + |τ|) * ‖g τ‖ with hY
  have hI0 : 0 ≤ ∫ τ, (1 + |τ|) * ‖g τ‖ :=
    integral_nonneg fun τ => mul_nonneg (by positivity) (norm_nonneg _)
  have hY0 : 0 ≤ Y := by positivity
  have hbox : ∀ j ∈ Icc 1 5, ∀ κ ∈ Fintype.piFinset (boxRange j (5 * Km) Km),
      Real.sqrt (∑ e ∈ moduli E, ‖∑ d ∈ Icc 1 (2 ^ 9 * 2 ^ (45 * Km)),
        (∏ i, boxAtom j zC (MC ((2 : ℝ) ^ Km)) i (κ i)) d *
          (V (d / D) * phiE ν Hn e d)‖ ^ 2) ≤ Y := by
    intro j hj κ hκ
    exact boxV_bound St dv hCB0 hBat hgm hgi hVsupp hrep hj hκ hK2
  have hdec : ∀ e, Pe D V ν Hn e = ∑ j ∈ Icc 1 5, hbCoeff j *
      ∑ κ ∈ Fintype.piFinset (boxRange j (5 * Km) Km),
        ∑ d ∈ Icc 1 (2 ^ 9 * 2 ^ (45 * Km)),
          (∏ i, boxAtom j zC (MC ((2 : ℝ) ^ Km)) i (κ i)) d * (V (d / D) * phiE ν Hn e d) :=
    fun e => Pe_eq_boxes hD2 V hVsupp ν Hn e hK1
  simp_rw [hdec]
  have hKm := Km_le hD2 hε₁0 hε₁1 hK2
  have hcount : (5 * Km + 1 : ℝ) ≤ 2 ^ 12 * Lam / ε₁ := by
    have h1 : 1 ≤ Lam / ε₁ := by rw [le_div_iff₀ hε₁0]; linarith
    have : (5 * Km + 1 : ℝ) ≤ 5 * (512 * Lam / ε₁) + Lam / ε₁ := by linarith
    calc (5 * Km + 1 : ℝ) ≤ 5 * (512 * Lam / ε₁) + Lam / ε₁ := this
      _ ≤ 2 ^ 12 * Lam / ε₁ := by
          have : 0 ≤ Lam / ε₁ := by positivity
          rw [show 5 * (512 * Lam / ε₁) + Lam / ε₁ = 2561 * (Lam / ε₁) by ring,
            show (2 : ℝ) ^ 12 * Lam / ε₁ = 4096 * (Lam / ε₁) by ring]
          linarith
  calc Real.sqrt (∑ e ∈ moduli E, ‖∑ j ∈ Icc 1 5, hbCoeff j *
        ∑ κ ∈ Fintype.piFinset (boxRange j (5 * Km) Km),
          ∑ d ∈ Icc 1 (2 ^ 9 * 2 ^ (45 * Km)),
            (∏ i, boxAtom j zC (MC ((2 : ℝ) ^ Km)) i (κ i)) d *
              (V (d / D) * phiE ν Hn e d)‖ ^ 2)
      ≤ ∑ j ∈ Icc 1 5, Real.sqrt (∑ e ∈ moduli E, ‖hbCoeff j *
          ∑ κ ∈ Fintype.piFinset (boxRange j (5 * Km) Km),
            ∑ d ∈ Icc 1 (2 ^ 9 * 2 ^ (45 * Km)),
              (∏ i, boxAtom j zC (MC ((2 : ℝ) ^ Km)) i (κ i)) d *
                (V (d / D) * phiE ν Hn e d)‖ ^ 2) := l2_sum_le _ _ _
    _ ≤ ∑ j ∈ Icc 1 5, 10 * ((5 * Km + 1 : ℝ) ^ 9 * Y) := by
        refine sum_le_sum fun j hj => ?_
        rw [l2_smul]
        refine mul_le_mul (norm_hbCoeff_le j) ?_ (Real.sqrt_nonneg _) (by norm_num)
        refine (l2_sum_le _ _ _).trans ?_
        calc ∑ κ ∈ Fintype.piFinset (boxRange j (5 * Km) Km), Real.sqrt (∑ e ∈ moduli E,
              ‖∑ d ∈ Icc 1 (2 ^ 9 * 2 ^ (45 * Km)),
                (∏ i, boxAtom j zC (MC ((2 : ℝ) ^ Km)) i (κ i)) d *
                  (V (d / D) * phiE ν Hn e d)‖ ^ 2)
            ≤ ∑ κ ∈ Fintype.piFinset (boxRange j (5 * Km) Km), Y :=
              sum_le_sum fun κ hκ => hbox j hj κ hκ
          _ = ((Fintype.piFinset (boxRange j (5 * Km) Km)).card : ℝ) * Y := by
              rw [sum_const, nsmul_eq_mul]
          _ ≤ (5 * Km + 1 : ℝ) ^ 9 * Y :=
              mul_le_mul_of_nonneg_right (card_piFinset_le j Km hj) hY0
    _ = 50 * ((5 * Km + 1 : ℝ) ^ 9 * Y) := by
        rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; norm_num; ring
    _ ≤ 50 * ((2 ^ 12 * Lam / ε₁) ^ 9 * (Cbox dv CB * Lam ^ 20 * target D E Hn * (CM * P ^ k))) := by
        rw [hY, hdvε]
        gcongr
    _ = (50 * (2 ^ 12 / ε₁) ^ 9 * Cbox dv CB * CM) * P ^ k * Lam ^ 29 * target D E Hn := by
        field_simp
    _ ≤ Cfin * P ^ k * D ^ ε * target D E Hn := by
        have hL29 : Lam ^ 29 ≤ D ^ ε := by
          rw [hLam, ← Real.rpow_natCast, ← Real.rpow_mul hD0.le]
          exact Real.rpow_le_rpow_of_exponent_le hD1 (by push_cast; linarith)
        have hC : 50 * (2 ^ 12 / ε₁) ^ 9 * Cbox dv CB * CM ≤ Cfin := by
          rw [hCfin]; linarith
        gcongr

end MobiusDeterminant
