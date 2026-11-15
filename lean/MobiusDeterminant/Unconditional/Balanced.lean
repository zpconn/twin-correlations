import MobiusDeterminant.Unconditional.BalancedSums

/-!
# The balanced-box bound from Bloom–Maynard

We prove `balancedBoxBound_of_BM : BloomMaynardE4 → BalancedBoxBound` (paper, Proposition 5.1
together with the strata of Steps 1 and 3 of the proof of Theorem 6.1).

## Proof

Fix `ε > 0` and put `δ = ε/3`.  For each modulus `e`:

* `balForm_e = ∑_{(h,u)} ∑_w ν_h α_u β_w e_e(h ū w̄)` (`balForm_eq`, using
  `kfrac e h d = e_e(h d̄)`);
* the phase depends on `(h, u)` only through the rational `ρ = h/u` (for `(u, e) = 1`,
  `h ū ≡ ρ.num · \overline{ρ.den}`), so we group the `(h, u)` according to `ρ`
  (`regroup`).  This replaces the two gcd strata `g = (h, e)`, `g' = (a, u)` of the paper:
  Lemma 3.1 is applied in the form `bilinear_pow_eight_le` for *arbitrary* residues (no unit
  condition on `h`), and grouping by the reduced fraction is exactly the stratification by
  `g'`.  The coefficient `γ_ρ = ∑_{h/u = ρ} ν_h α_u` satisfies
  `∑_ρ |γ_ρ|² ≤ #{h/u = h'/u'} ≪ U₀ H (U₀W₀E)^{4δ}` (`card_pairs_bound`);
* Lemma 3.1 gives `|balForm_e|⁸ ≤ ‖γ‖₂⁸ ‖β‖₂⁸ · e · I_𝓕(e) · I_𝓦(e)` (`per_modulus_bound`).

Summing over `e` with Hölder's inequality `(4,4,2)` (`holder_step`),
`(∑_e |balForm_e|²)⁴ ≤ #R² ‖γ‖⁸ ‖β‖⁸ (8E) (∑_e I_𝓕(e)) (∑_e I_𝓦(e))`, and Lemmas 4.1 and 4.3
(`sum_fracEnergy_bound`, `sum_intEnergy_bound`, with Bloom–Maynard in `energy4_le_of_BM`)
give `∑_e I_𝓕(e) ≪ (U₀W₀E)^{4δ} (U₀H)² (E + (U₀H)²)` and
`∑_e I_𝓦(e) ≪ (U₀W₀E)^{4δ} W₀² (E + W₀²)`.  Collecting,
`(∑_e |balForm_e|²)⁴ ≪ (U₀W₀E)^{8ε} E³ (U₀W₀H)⁶ (E + (U₀H)²)(E + W₀²)`,
which is the fourth power of the square of the bound in `BalancedBoxBound`.
-/

open Finset

namespace MobiusDeterminant
namespace BalancedBox

lemma mono_monomial {U W c : ℝ} (hU : 1 ≤ U) (hW : 1 ≤ W) (hc : c ≤ 2 ^ 48)
    {i j : ℕ} (hi : i ≤ 4) (hj : j ≤ 4) : c * U ^ i * W ^ j ≤ 2 ^ 48 * U ^ 4 * W ^ 4 := by
  have h1 : U ^ i ≤ U ^ 4 := pow_le_pow_right₀ hU hi
  have h2 : W ^ j ≤ W ^ 4 := pow_le_pow_right₀ hW hj
  have h3 : (0 : ℝ) ≤ U ^ i := by positivity
  have h4 : (0 : ℝ) ≤ W ^ j := by positivity
  gcongr

lemma pow_rpow_eight {x : ℝ} (hx : 0 ≤ x) (r : ℝ) (m : ℕ) (h : r * 8 = m) :
    (x ^ r) ^ 8 = x ^ m := by
  have h' : r * ((8 : ℕ) : ℝ) = ((m : ℕ) : ℝ) := by push_cast; exact h
  rw [← Real.rpow_mul_natCast hx, h', Real.rpow_natCast]

/-- The constant of `balancedBoxBound_of_BM`. -/
noncomputable def balConst (ε Cτ CB : ℝ) : ℝ :=
  (512 * (3 * 2 ^ 18 * Cτ) ^ 4 * (8 * 25 * 2 ^ 20 * CB + 81 * 2 ^ 36 * Cτ) * (2 ^ 36 * Cτ) + 1) *
    (2 ^ 12 : ℝ) ^ ε

lemma balConst_pos {ε Cτ CB : ℝ} (hCτ : 0 ≤ Cτ) (hCB : 0 ≤ CB) : 0 < balConst ε Cτ CB := by
  unfold balConst; positivity

/-- The final bookkeeping of the proof of `balancedBoxBound_of_BM`, for real numbers:
`Rc = #R`, `Pc = #{h/u = h'/u'}`, `Tc = #𝓦`, `Fc = #𝓕`, `e4 = E₄(𝓕)`, `Sx = ∑_e I_𝓕(e)`,
`Sy = ∑_e I_𝓦(e)`, `Ssum = ∑_e |balForm_e|²`, `D = X^{ε/3}` with `X = (2¹² U₀W₀E)⁴`. -/
lemma collect_bound {ε Cτ CB U₀ W₀ E H Rc Pc Tc Fc e4 Um Wm Sx Sy Ssum D : ℝ}
    (hCτ1 : 1 ≤ Cτ) (hCB : 0 < CB) (hU : 1 ≤ U₀) (hW : 1 ≤ W₀) (hE : 1 ≤ E)
    (hH1 : 1 ≤ H) (hUm : Um ≤ 2 ^ 9 * U₀) (hWm : Wm ≤ 2 ^ 9 * W₀)
    (hUm0 : 0 ≤ Um) (hRc0 : 0 ≤ Rc) (hRcard : Rc ≤ 8 * E) (hPc0 : 0 ≤ Pc) (hTc0 : 0 ≤ Tc)
    (hFc0 : 0 ≤ Fc) (he40 : 0 ≤ e4)
    (hD : D = ((2 ^ 12 * (U₀ * W₀ * E)) ^ 4) ^ (ε / 3))
    (hE4 : e4 ≤ CB * D * (2 ^ 10 * U₀ * (5 * H)) ^ 2)
    (hP : Pc ≤ (2 * H + 1) * Um * (Cτ * D)) (hFcard : Fc ≤ (2 * H + 1) * Um) (hTcard : Tc ≤ Wm)
    (hSx : Sx ≤ Rc * e4 + Fc ^ 4 * (Cτ * D))
    (hSy : Sy ≤ Rc * (Tc ^ 2 * (Cτ * D)) + Tc ^ 4 * (Cτ * D))
    (hSx0 : 0 ≤ Sx) (hSy0 : 0 ≤ Sy) (hS0 : 0 ≤ Ssum)
    (hhold : Ssum ^ 4 ≤ Rc ^ 2 * (Pc * Tc) ^ 4 * (8 * E) * (Sx * Sy)) :
    Ssum ≤ (balConst ε Cτ CB * (U₀ * W₀ * E) ^ ε * (U₀ * W₀ * H) ^ ((3 : ℝ) / 4) *
      E ^ ((3 : ℝ) / 8) * ((E + (U₀ * H) ^ 2) * (E + W₀ ^ 2)) ^ ((1 : ℝ) / 8)) ^ 2 := by
  set cX : ℝ := 8 * 25 * 2 ^ 20 * CB + 81 * 2 ^ 36 * Cτ with hcX
  set cY : ℝ := 2 ^ 36 * Cτ with hcY
  set c : ℝ := 512 * (3 * 2 ^ 18 * Cτ) ^ 4 * cX * cY with hc
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hcX0 : 0 ≤ cX := by rw [hcX]; positivity
  have hcY0 : 0 ≤ cY := by rw [hcY]; positivity
  have hE0 : 0 < E := by linarith
  have hU0 : (0 : ℝ) ≤ U₀ := by linarith
  set Λ : ℝ := 2 ^ 12 * (U₀ * W₀ * E) with hΛ
  have hΛ0 : 0 ≤ Λ := by positivity
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hWm0 : 0 ≤ Wm := hTc0.trans hTcard
  clear_value cX cY c Λ
  /- collecting the bounds -/
  have hK : Pc * Tc ≤ 3 * 2 ^ 18 * Cτ * D * (H * U₀ * W₀) := by
    have h3 : (2 * H + 1) ≤ 3 * H := by linarith
    calc Pc * Tc ≤ ((2 * H + 1) * Um * (Cτ * D)) * Wm := by gcongr
      _ ≤ ((3 * H) * (2 ^ 9 * U₀) * (Cτ * D)) * (2 ^ 9 * W₀) := by gcongr
      _ = 3 * 2 ^ 18 * Cτ * D * (H * U₀ * W₀) := by ring
  have hXs : Sx ≤ D * cX * ((U₀ * H) ^ 2 * (E + (U₀ * H) ^ 2)) := by
    refine hSx.trans ?_
    have h3 : (2 * H + 1) ≤ 3 * H := by linarith
    have hF' : Fc ≤ 3 * 2 ^ 9 * (U₀ * H) := by
      calc Fc ≤ (2 * H + 1) * Um := hFcard
        _ ≤ (3 * H) * (2 ^ 9 * U₀) := mul_le_mul h3 hUm (by positivity) (by positivity)
        _ = 3 * 2 ^ 9 * (U₀ * H) := by ring
    calc Rc * e4 + Fc ^ 4 * (Cτ * D)
        ≤ (8 * E) * (CB * D * (2 ^ 10 * U₀ * (5 * H)) ^ 2) +
            (3 * 2 ^ 9 * (U₀ * H)) ^ 4 * (Cτ * D) :=
          add_le_add (mul_le_mul hRcard hE4 (by positivity) (by positivity))
            (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hF' 4)
              (by positivity))
      _ ≤ D * cX * ((U₀ * H) ^ 2 * (E + (U₀ * H) ^ 2)) := by
          have key : D * cX * ((U₀ * H) ^ 2 * (E + (U₀ * H) ^ 2)) -
              ((8 * E) * (CB * D * (2 ^ 10 * U₀ * (5 * H)) ^ 2) +
                (3 * 2 ^ 9 * (U₀ * H)) ^ 4 * (Cτ * D)) =
              D * (U₀ * H) ^ 2 * (81 * 2 ^ 36 * Cτ * E + 8 * 25 * 2 ^ 20 * CB * (U₀ * H) ^ 2) := by
            rw [hcX]; ring
          have : 0 ≤ D * (U₀ * H) ^ 2 *
              (81 * 2 ^ 36 * Cτ * E + 8 * 25 * 2 ^ 20 * CB * (U₀ * H) ^ 2) := by positivity
          linarith
  have hYs : Sy ≤ D * cY * (W₀ ^ 2 * (E + W₀ ^ 2)) := by
    refine hSy.trans ?_
    calc Rc * (Tc ^ 2 * (Cτ * D)) + Tc ^ 4 * (Cτ * D)
        ≤ (8 * E) * ((2 ^ 9 * W₀) ^ 2 * (Cτ * D)) + (2 ^ 9 * W₀) ^ 4 * (Cτ * D) := by
          have h1 : Tc ≤ 2 ^ 9 * W₀ := hTcard.trans hWm
          have h0 : (0 : ℝ) ≤ Cτ * D := by positivity
          exact add_le_add (mul_le_mul hRcard
            (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h1 2) h0)
            (by positivity) (by positivity))
            (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h1 4) h0)
      _ ≤ D * cY * (W₀ ^ 2 * (E + W₀ ^ 2)) := by
          have key : D * cY * (W₀ ^ 2 * (E + W₀ ^ 2)) -
              ((8 * E) * ((2 ^ 9 * W₀) ^ 2 * (Cτ * D)) + (2 ^ 9 * W₀) ^ 4 * (Cτ * D)) =
              D * W₀ ^ 2 * ((2 ^ 36 - 8 * 2 ^ 18) * Cτ * E) := by
            rw [hcY]; ring
          have : 0 ≤ D * W₀ ^ 2 * ((2 ^ 36 - 8 * 2 ^ 18) * Cτ * E) := by
            have : (0 : ℝ) ≤ 2 ^ 36 - 8 * 2 ^ 18 := by norm_num
            positivity
          linarith
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = E ^ 3 * (U₀ * W₀ * H) ^ 6 * ((E + (U₀ * H) ^ 2) * (E + W₀ ^ 2)) :=
    ⟨_, rfl⟩
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  have hmain : Ssum ^ 4 ≤ c * D ^ 6 * Q := by
    refine hhold.trans ?_
    have hx0 : 0 ≤ Sx := hSx0
    have hy0 : 0 ≤ Sy := hSy0
    have hR2 : Rc ^ 2 ≤ (8 * E) ^ 2 := pow_le_pow_left₀ hRc0 hRcard 2
    have hK4 : (Pc * Tc) ^ 4 ≤ (3 * 2 ^ 18 * Cτ * D * (H * U₀ * W₀)) ^ 4 :=
      pow_le_pow_left₀ (by positivity) hK 4
    have hX00 : 0 ≤ D * cX * ((U₀ * H) ^ 2 * (E + (U₀ * H) ^ 2)) := by positivity
    have hXY : (Sx) * (Sy) ≤
        (D * cX * ((U₀ * H) ^ 2 * (E + (U₀ * H) ^ 2))) * (D * cY * (W₀ ^ 2 * (E + W₀ ^ 2))) :=
      mul_le_mul hXs hYs hy0 hX00
    calc Rc ^ 2 * (Pc * Tc) ^ 4 * (8 * E) * ((Sx) * Sy)
        ≤ (8 * E) ^ 2 * (3 * 2 ^ 18 * Cτ * D * (H * U₀ * W₀)) ^ 4 * (8 * E) *
            ((D * cX * ((U₀ * H) ^ 2 * (E + (U₀ * H) ^ 2))) *
              (D * cY * (W₀ ^ 2 * (E + W₀ ^ 2)))) := by
          have hP0 : (0 : ℝ) ≤ (Pc * Tc) ^ 4 := by positivity
          have hE80 : (0 : ℝ) ≤ (8 * E) ^ 2 := by positivity
          have h1 : Rc ^ 2 * (Pc * Tc) ^ 4 ≤
              (8 * E) ^ 2 * (3 * 2 ^ 18 * Cτ * D * (H * U₀ * W₀)) ^ 4 :=
            mul_le_mul hR2 hK4 hP0 hE80
          have hE8 : (0 : ℝ) ≤ 8 * E := by positivity
          have h2 : Rc ^ 2 * (Pc * Tc) ^ 4 * (8 * E) ≤
              (8 * E) ^ 2 * (3 * 2 ^ 18 * Cτ * D * (H * U₀ * W₀)) ^ 4 * (8 * E) :=
            mul_le_mul_of_nonneg_right h1 hE8
          have h3 : (0 : ℝ) ≤ (8 * E) ^ 2 * (3 * 2 ^ 18 * Cτ * D * (H * U₀ * W₀)) ^ 4 * (8 * E) := by
            positivity
          exact mul_le_mul h2 hXY (mul_nonneg hx0 hy0) h3
      _ = c * D ^ 6 * Q := by rw [hc, hQ]; ring
  /- the exponents -/
  have hD6 : D ^ 6 = ((2 ^ 12 : ℝ) ^ ε * (U₀ * W₀ * E) ^ ε) ^ 8 := by
    rw [← Real.mul_rpow (by positivity) (by positivity), ← hΛ]
    rw [hD, ← Real.rpow_natCast_mul hΛ0, ← Real.rpow_mul_natCast hΛ0,
      ← Real.rpow_mul_natCast hΛ0]
    congr 1; push_cast; ring
  obtain ⟨A8, hA8⟩ : ∃ A8 : ℝ, A8 = ((2 ^ 12 : ℝ) ^ ε * (U₀ * W₀ * E) ^ ε) ^ 8 := ⟨_, rfl⟩
  rw [← hA8] at hD6
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = (c + 1) * (2 ^ 12 : ℝ) ^ ε * (U₀ * W₀ * E) ^ ε *
      (U₀ * W₀ * H) ^ ((3 : ℝ) / 4) * E ^ ((3 : ℝ) / 8) *
      ((E + (U₀ * H) ^ 2) * (E + W₀ ^ 2)) ^ ((1 : ℝ) / 8) := ⟨_, rfl⟩
  have hB8 : (B ^ 2) ^ 4 = (c + 1) ^ 8 * A8 * Q := by
    have e1 : ((U₀ * W₀ * H) ^ ((3 : ℝ) / 4)) ^ 8 = (U₀ * W₀ * H) ^ 6 :=
      pow_rpow_eight (by positivity) _ 6 (by norm_num)
    have e2 : (E ^ ((3 : ℝ) / 8)) ^ 8 = E ^ 3 := pow_rpow_eight (by positivity) _ 3 (by norm_num)
    have e3 : (((E + (U₀ * H) ^ 2) * (E + W₀ ^ 2)) ^ ((1 : ℝ) / 8)) ^ 8 =
        ((E + (U₀ * H) ^ 2) * (E + W₀ ^ 2)) ^ 1 :=
      pow_rpow_eight (by positivity) _ 1 (by norm_num)
    calc (B ^ 2) ^ 4 = (c + 1) ^ 8 * ((2 ^ 12 : ℝ) ^ ε * (U₀ * W₀ * E) ^ ε) ^ 8 *
          ((U₀ * W₀ * H) ^ ((3 : ℝ) / 4)) ^ 8 * (E ^ ((3 : ℝ) / 8)) ^ 8 *
          (((E + (U₀ * H) ^ 2) * (E + W₀ ^ 2)) ^ ((1 : ℝ) / 8)) ^ 8 := by
          rw [hB]; ring
      _ = (c + 1) ^ 8 * A8 * Q := by
          rw [e1, e2, e3, hQ, hA8]; ring
  have hB0 : 0 ≤ B ^ 2 := sq_nonneg _
  have hBc : balConst ε Cτ CB = (c + 1) * (2 ^ 12 : ℝ) ^ ε := by rw [balConst, hc, hcX, hcY]
  rw [hBc, ← hB]
  rw [← pow_le_pow_iff_left₀ hS0 hB0 (by norm_num : (4 : ℕ) ≠ 0), hB8]
  refine hmain.trans ?_
  rw [hD6]
  have hc1 : c ≤ (c + 1) ^ 8 := by
    have h1 : (1 : ℝ) ≤ c + 1 := by linarith only [hc0]
    have : c + 1 ≤ (c + 1) ^ 8 := le_self_pow₀ h1 (by norm_num)
    linarith only [this]
  have hA80 : 0 ≤ A8 := by rw [hA8]; positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc1 hA80) hQ0


end BalancedBox

open BalancedBox

/-- **The balanced-box bound** (paper, Proposition 5.1 with the gcd strata of Steps 1 and 3 of
the proof of Theorem 6.1), from the Bloom–Maynard energy bound. -/
theorem balancedBoxBound_of_BM (hBM : BloomMaynardE4) : BalancedBoxBound := by
  intro ε hε
  have hδ : 0 < ε / 3 := by positivity
  obtain ⟨Cτ, hCτ1, hCτ⟩ := divisor_bound hδ
  obtain ⟨CB, hCB, hBMδ⟩ := energy4_le_of_BM hBM hδ
  refine ⟨balConst ε Cτ CB, balConst_pos (by linarith) hCB.le, ?_⟩
  intro U₀ W₀ E Hn α β ν hU hUW hE hH hHU hαs hαb hβs hβb hν0 hνb
  have hW : 1 ≤ W₀ := hU.trans hUW
  have hH1 : (1 : ℝ) ≤ Hn := by exact_mod_cast hH
  set Umax := ⌊(2 : ℝ) ^ 9 * U₀⌋₊ with hUmax
  set Wmax := ⌊(2 : ℝ) ^ 9 * W₀⌋₊ with hWmax
  set R := (Ioc ⌊E / 8⌋₊ ⌊8 * E⌋₊).filter Squarefree with hRdef
  set S := hu_set α Umax Hn with hSdef
  set T := w_set β Wmax with hTdef
  set F := S.image frac with hFdef
  set Λ : ℝ := 2 ^ 12 * (U₀ * W₀ * E) with hΛ
  set X : ℝ := Λ ^ 4 with hXdef
  set D : ℝ := X ^ (ε / 3) with hD
  have hΛ0 : 0 ≤ Λ := by positivity
  have hX0 : 0 ≤ X := by positivity
  have hD0 : 0 ≤ D := by positivity
  /- basic facts -/
  have hUm : (Umax : ℝ) ≤ 2 ^ 9 * U₀ := Nat.floor_le (by positivity)
  have hWm : (Wmax : ℝ) ≤ 2 ^ 9 * W₀ := Nat.floor_le (by positivity)
  have hUm1 : 1 ≤ Umax := Nat.le_floor (by push_cast; linarith)
  have hR : ∀ e ∈ R, 1 ≤ e ∧ (e : ℝ) ≤ 8 * E := by
    intro e he
    simp only [hRdef, mem_filter, mem_Ioc] at he
    refine ⟨by omega, ?_⟩
    have : (e : ℝ) ≤ ⌊8 * E⌋₊ := by exact_mod_cast he.1.2
    exact this.trans (Nat.floor_le (by positivity))
  have hRcard : (R.card : ℝ) ≤ 8 * E := by
    have h1 : R.card ≤ ⌊8 * E⌋₊ := by
      refine (card_filter_le _ _).trans ?_
      rw [Nat.card_Ioc]; omega
    have h2 : (R.card : ℝ) ≤ ⌊8 * E⌋₊ := by exact_mod_cast h1
    exact h2.trans (Nat.floor_le (by positivity))
  have hS : ∀ s ∈ S, s.1 ≠ 0 ∧ |s.1| ≤ Hn ∧ 1 ≤ s.2 ∧ s.2 ≤ Umax := fun s hs =>
    let h := mem_hu_set hs; ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  have hT : ∀ w ∈ T, 1 ≤ w ∧ w ≤ Wmax := fun w hw =>
    let h := mem_w_set hw; ⟨h.1, h.2.1⟩
  have hScard : (S.card : ℝ) ≤ (2 * Hn + 1) * Umax := by
    have : S.card ≤ (2 * Hn + 1) * Umax := by
      refine (card_filter_le _ _).trans (le_of_eq ?_)
      have e1 : ((Hn : ℤ) + 1 - -(Hn : ℤ)).toNat = 2 * Hn + 1 := by omega
      rw [card_product, Int.card_Icc, Nat.card_Icc, e1, Nat.add_sub_cancel]
    exact_mod_cast this
  have hFcard : (F.card : ℝ) ≤ (2 * Hn + 1) * Umax :=
    le_trans (by exact_mod_cast card_image_le) hScard
  have hTcard : (T.card : ℝ) ≤ Wmax := by
    have : T.card ≤ Wmax := by
      refine (card_filter_le _ _).trans (le_of_eq ?_)
      rw [Nat.card_Icc, Nat.add_sub_cancel]
    exact_mod_cast this
  /- the size conditions defining `X` -/
  have hXbig : 2 ^ 48 * U₀ ^ 4 * W₀ ^ 4 ≤ X := by
    have : X = 2 ^ 48 * U₀ ^ 4 * W₀ ^ 4 * E ^ 4 := by simp only [hXdef, hΛ]; ring
    rw [this]
    have : (1 : ℝ) ≤ E ^ 4 := one_le_pow₀ hE
    have : (0 : ℝ) ≤ 2 ^ 48 * U₀ ^ 4 * W₀ ^ 4 := by positivity
    nlinarith
  have hU0 : (0 : ℝ) ≤ U₀ := by linarith
  have hHU' : (Hn : ℝ) ≤ U₀ := hHU
  have hX1 : (Hn : ℝ) * Umax ≤ X := by
    calc (Hn : ℝ) * Umax ≤ U₀ * (2 ^ 9 * U₀) := by gcongr
      _ = 2 ^ 9 * U₀ ^ 2 * W₀ ^ 0 := by ring
      _ ≤ 2 ^ 48 * U₀ ^ 4 * W₀ ^ 4 := mono_monomial hU hW (by norm_num)
          (by norm_num) (by norm_num)
      _ ≤ X := hXbig
  have hX2 : 4 * (Hn : ℝ) * (Umax : ℝ) ^ 3 ≤ X := by
    calc 4 * (Hn : ℝ) * (Umax : ℝ) ^ 3 ≤ 4 * U₀ * (2 ^ 9 * U₀) ^ 3 := by gcongr
      _ = 2 ^ 29 * U₀ ^ 4 * W₀ ^ 0 := by ring
      _ ≤ 2 ^ 48 * U₀ ^ 4 * W₀ ^ 4 := mono_monomial hU hW (by norm_num)
          (by norm_num) (by norm_num)
      _ ≤ X := hXbig
  have hX3 : (Wmax : ℝ) ^ 4 ≤ X := by
    calc (Wmax : ℝ) ^ 4 ≤ (2 ^ 9 * W₀) ^ 4 := by gcongr
      _ = 2 ^ 36 * U₀ ^ 0 * W₀ ^ 4 := by ring
      _ ≤ 2 ^ 48 * U₀ ^ 4 * W₀ ^ 4 := mono_monomial hU hW (by norm_num)
          (by norm_num) (by norm_num)
      _ ≤ X := hXbig
  have hX4 : 2 * (Wmax : ℝ) ^ 3 ≤ X := by
    calc 2 * (Wmax : ℝ) ^ 3 ≤ 2 * (2 ^ 9 * W₀) ^ 3 := by gcongr
      _ = 2 ^ 28 * U₀ ^ 0 * W₀ ^ 3 := by ring
      _ ≤ 2 ^ 48 * U₀ ^ 4 * W₀ ^ 4 := mono_monomial hU hW (by norm_num)
          (by norm_num) (by norm_num)
      _ ≤ X := hXbig
  have hX5 : (((2 * Umax : ℕ)) : ℝ) ≤ X := by
    push_cast
    calc 2 * (Umax : ℝ) ≤ 2 * (2 ^ 9 * U₀) := by gcongr
      _ = 2 ^ 10 * U₀ ^ 1 * W₀ ^ 0 := by ring
      _ ≤ 2 ^ 48 * U₀ ^ 4 * W₀ ^ 4 := mono_monomial hU hW (by norm_num)
          (by norm_num) (by norm_num)
      _ ≤ X := hXbig
  /- the fractions -/
  have hF1 : ∀ ρ ∈ F, |ρ.num| ≤ Hn ∧ ρ.den ≤ Umax := by
    intro ρ hρ
    obtain ⟨s, hs, rfl⟩ := mem_image.1 hρ
    obtain ⟨h1, h2, h3, h4⟩ := hS s hs
    exact ⟨(abs_num_div_le h1 (by omega)).trans h2, (den_div_le _ (by omega)).trans h4⟩
  have hF2 : ∀ ρ ∈ F, ∃ h : ℤ, ∃ u : ℕ, 0 < u ∧ u ≤ Umax ∧ |h| ≤ Hn ∧ |h| ≤ u ∧
      ρ = h / u := by
    intro ρ hρ
    obtain ⟨s, hs, rfl⟩ := mem_image.1 hρ
    obtain ⟨h1, h2, h3, h4⟩ := hS s hs
    have hα : α s.2 ≠ 0 := (mem_hu_set hs).2.2.2.2
    have hlt : (Hn : ℝ) < s.2 := hHU'.trans_lt (hαs _ hα).1
    have hlt' : (Hn : ℤ) < s.2 := by exact_mod_cast hlt
    exact ⟨s.1, s.2, by omega, h4, h2, by linarith, rfl⟩
  /- Bloom–Maynard -/
  have hE4 : (energy4 F : ℝ) ≤ CB * D * (2 ^ 10 * U₀ * (5 * Hn)) ^ 2 := by
    refine (hBMδ Hn Umax F hUm1 hF2).trans ?_
    have a1 : (((2 * Umax : ℕ)) : ℝ) ^ (ε / 3) ≤ D :=
      Real.rpow_le_rpow (by positivity) hX5 hδ.le
    have a2 : (((2 * Umax : ℕ)) : ℝ) * ((4 * Hn + 1 : ℕ) : ℝ) ≤ 2 ^ 10 * U₀ * (5 * Hn) := by
      push_cast
      have : (4 : ℝ) * Hn + 1 ≤ 5 * Hn := by linarith
      calc 2 * (Umax : ℝ) * (4 * Hn + 1) ≤ 2 * (2 ^ 9 * U₀) * (5 * Hn) := by gcongr
        _ = 2 ^ 10 * U₀ * (5 * Hn) := by ring
    have a3 : (0 : ℝ) ≤ (((2 * Umax : ℕ)) : ℝ) * ((4 * Hn + 1 : ℕ) : ℝ) := by positivity
    gcongr
  /- coincidences `h/u = h'/u'` -/
  set P := ((S ×ˢ S).filter (fun p => frac p.1 = frac p.2)).card with hPdef
  have hP : (P : ℝ) ≤ (2 * Hn + 1) * Umax * (Cτ * D) :=
    card_pairs_bound Hn Umax S hS hCτ hδ hCτ1 hX1
  /- energies averaged over `e` -/
  set x : ℕ → ℝ := fun e => (((F ×ˢ F ×ˢ F ×ˢ F).filter (FracCountedQ e)).card : ℝ) with hx
  set y : ℕ → ℝ := fun e => (((T ×ˢ T ×ˢ T ×ˢ T).filter (Energy.IntCounted e)).card : ℝ)
    with hy
  have hSx : ∑ e ∈ R, x e ≤ (R.card : ℝ) * energy4 F + (F.card : ℝ) ^ 4 * (Cτ * D) :=
    sum_fracEnergy_bound R F Hn Umax hF1 hCτ hδ hCτ1 hX2
  have hSy : ∑ e ∈ R, y e ≤
      (R.card : ℝ) * ((T.card : ℝ) ^ 2 * (Cτ * D)) + (T.card : ℝ) ^ 4 * (Cτ * D) :=
    sum_intEnergy_bound R T Wmax hT hCτ hδ hCτ1 hX3 hX4
  /- Lemma 3.1 for each modulus, then Hölder -/
  have hper : ∀ e ∈ R, (‖balForm α β Umax Wmax ν Hn e‖ ^ 2) ^ 4 ≤
      ((P : ℝ) * T.card) ^ 4 * (8 * E) * (x e * y e) := by
    intro e he
    have : NeZero e := ⟨by have := (hR e he).1; omega⟩
    have h := per_modulus_bound α β Umax Wmax ν Hn e hν0 hνb hαb hβb
    have hx0 : 0 ≤ x e := by positivity
    have hy0 : 0 ≤ y e := by positivity
    calc (‖balForm α β Umax Wmax ν Hn e‖ ^ 2) ^ 4 = ‖balForm α β Umax Wmax ν Hn e‖ ^ 8 := by
          ring
      _ ≤ (P : ℝ) ^ 4 * (T.card : ℝ) ^ 4 * (e : ℝ) * x e * y e := h
      _ = ((P : ℝ) * T.card) ^ 4 * (e : ℝ) * (x e * y e) := by ring
      _ ≤ ((P : ℝ) * T.card) ^ 4 * (8 * E) * (x e * y e) := by
          gcongr
          exact (hR e he).2
  have hhold := holder_step R (fun e => ‖balForm α β Umax Wmax ν Hn e‖ ^ 2) x y
    ((P : ℝ) * T.card) (8 * E) (by positivity) (fun e => by positivity)
    (fun e => by positivity) hper
  beta_reduce at hhold
  exact collect_bound hCτ1 hCB hU hW hE hH1 hUm hWm (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) hRcard (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) hD hE4 hP hFcard hTcard hSx hSy
    (sum_nonneg (fun e _ => Nat.cast_nonneg _)) (sum_nonneg (fun e _ => Nat.cast_nonneg _))
    (sum_nonneg (fun _ _ => sq_nonneg _)) hhold

end MobiusDeterminant
