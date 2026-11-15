import MobiusDeterminant.Unconditional.BalancedForm

/-!
# Balanced boxes: energies averaged over the modulus

Paper, Lemmas 4.1 and 4.3 (second claims), in the form needed for `balancedBoxBound_of_BM`,
with the divisor bound `τ(n) ≤ C_τ n^δ` inserted for `n ≤ X`.
-/

open Finset

namespace MobiusDeterminant
namespace BalancedBox

/-- Paper, Lemma 4.3 (second claim): for a finite set `F` of rationals with numerators at most
`H` and denominators at most `Umax` in absolute value, and any finite set `R` of moduli,
`∑_{e∈R} I_𝓕(e) ≤ #R · E₄(F) + #F⁴ · C_τ X^δ` whenever `4 H Umax³ ≤ X`. -/
theorem sum_fracEnergy_bound (R : Finset ℕ) (F : Finset ℚ) (Hn Umax : ℕ)
    (hF : ∀ ρ ∈ F, |ρ.num| ≤ Hn ∧ ρ.den ≤ Umax) {δ Cτ X : ℝ}
    (hCτ : ∀ n : ℕ, 1 ≤ n → (n.divisors.card : ℝ) ≤ Cτ * (n : ℝ) ^ δ) (hδ : 0 < δ)
    (hCτ1 : 1 ≤ Cτ) (hX : 4 * (Hn : ℝ) * (Umax : ℝ) ^ 3 ≤ X) :
    ∑ e ∈ R, (((F ×ˢ F ×ˢ F ×ˢ F).filter (FracCountedQ e)).card : ℝ) ≤
      (R.card : ℝ) * energy4 F + (F.card : ℝ) ^ 4 * (Cτ * X ^ δ) := by
  have h := sum_count_le R (F ×ˢ F ×ˢ F ×ˢ F) deltaQ FracCountedQ
    (fun _ _ _ _ h => dvd_deltaQ h)
  have h0 : ((F ×ˢ F ×ˢ F ×ˢ F).filter (fun t => deltaQ t = 0)).card = energy4 F := by
    unfold energy4
    congr 1
    exact filter_congr (fun t _ => deltaQ_eq_zero_iff t)
  rw [h0] at h
  have h1 : ∀ t ∈ (F ×ˢ F ×ˢ F ×ˢ F).filter (fun t => deltaQ t ≠ 0),
      ((R.filter (fun q : ℕ => (q : ℤ) ∣ deltaQ t)).card : ℝ) ≤ Cτ * X ^ δ := by
    intro t ht
    simp only [mem_filter, mem_product] at ht
    obtain ⟨⟨h1, h2, h3, h4⟩, hΔ⟩ := ht
    have hb : |deltaQ t| ≤ 4 * (Hn : ℤ) * (Umax : ℤ) ^ 3 :=
      abs_deltaQ_le (hF _ h1) (hF _ h2) (hF _ h3) (hF _ h4)
    have hb' : ((deltaQ t).natAbs : ℝ) ≤ X := by
      have : ((deltaQ t).natAbs : ℤ) ≤ 4 * (Hn : ℤ) * (Umax : ℤ) ^ 3 := by
        rw [Int.natCast_natAbs]; exact hb
      have : ((deltaQ t).natAbs : ℝ) ≤ 4 * (Hn : ℝ) * (Umax : ℝ) ^ 3 := by exact_mod_cast this
      linarith
    calc ((R.filter (fun q : ℕ => (q : ℤ) ∣ deltaQ t)).card : ℝ)
        ≤ (deltaQ t).natAbs.divisors.card := by exact_mod_cast card_filter_dvd_le R hΔ
      _ ≤ Cτ * X ^ δ :=
          divisor_bound_le hδ hCτ hCτ1 (Int.natAbs_pos.2 hΔ) hb'
  have h2 : (∑ t ∈ (F ×ˢ F ×ˢ F ×ˢ F).filter (fun t => deltaQ t ≠ 0),
      ((R.filter (fun q : ℕ => (q : ℤ) ∣ deltaQ t)).card : ℝ)) ≤
      (F.card : ℝ) ^ 4 * (Cτ * X ^ δ) := by
    refine (sum_le_sum h1).trans ?_
    rw [sum_const, nsmul_eq_mul]
    have hpos : 0 ≤ Cτ * X ^ δ := by
      have : 0 ≤ X := le_trans (by positivity) hX
      positivity
    refine mul_le_mul_of_nonneg_right ?_ hpos
    have : ((F ×ˢ F ×ˢ F ×ˢ F).filter (fun t => deltaQ t ≠ 0)).card ≤ F.card ^ 4 := by
      refine (card_filter_le _ _).trans (le_of_eq ?_)
      simp only [card_product]; ring
    exact_mod_cast this
  have h' : (∑ e ∈ R, (((F ×ˢ F ×ˢ F ×ˢ F).filter (FracCountedQ e)).card : ℝ)) ≤
      (R.card : ℝ) * energy4 F + ∑ t ∈ (F ×ˢ F ×ˢ F ×ˢ F).filter (fun t => deltaQ t ≠ 0),
        ((R.filter (fun q : ℕ => (q : ℤ) ∣ deltaQ t)).card : ℝ) := by
    exact_mod_cast h
  linarith

/-- Paper, Lemma 4.1 (for the `w`): for `T ⊂ [1, Wmax]` and any finite set `R` of moduli,
`∑_{e∈R} I_𝓦(e) ≤ #R · #T² · C_τ X^δ + #T⁴ · C_τ X^δ` whenever `Wmax⁴ ≤ X` and
`2 Wmax³ ≤ X`. -/
theorem sum_intEnergy_bound (R : Finset ℕ) (T : Finset ℕ) (Wmax : ℕ)
    (hT : ∀ w ∈ T, 1 ≤ w ∧ w ≤ Wmax) {δ Cτ X : ℝ}
    (hCτ : ∀ n : ℕ, 1 ≤ n → (n.divisors.card : ℝ) ≤ Cτ * (n : ℝ) ^ δ) (hδ : 0 < δ)
    (hCτ1 : 1 ≤ Cτ) (hX1 : (Wmax : ℝ) ^ 4 ≤ X) (hX2 : 2 * (Wmax : ℝ) ^ 3 ≤ X) :
    ∑ e ∈ R, (((T ×ˢ T ×ˢ T ×ˢ T).filter (Energy.IntCounted e)).card : ℝ) ≤
      (R.card : ℝ) * ((T.card : ℝ) ^ 2 * (Cτ * X ^ δ)) + (T.card : ℝ) ^ 4 * (Cτ * X ^ δ) := by
  have h := sum_count_le R (T ×ˢ T ×ˢ T ×ˢ T) Energy.intDelta Energy.IntCounted
    (fun _ _ _ _ h => Energy.dvd_intDelta h)
  -- the rational solutions
  have h0 : (((T ×ˢ T ×ˢ T ×ˢ T).filter (fun t => Energy.intDelta t = 0)).card : ℝ) ≤
      (T.card : ℝ) ^ 2 * (Cτ * X ^ δ) := by
    have := card_intDelta_zero_le T (fun w hw => (hT w hw).1)
    calc (((T ×ˢ T ×ˢ T ×ˢ T).filter (fun t => Energy.intDelta t = 0)).card : ℝ)
        ≤ ∑ p ∈ T ×ˢ T, (((p.1 * p.2) ^ 2).divisors.card : ℝ) := by exact_mod_cast this
      _ ≤ ∑ _p ∈ T ×ˢ T, Cτ * X ^ δ := by
          refine sum_le_sum (fun p hp => ?_)
          rw [mem_product] at hp
          have a1 := hT _ hp.1
          have a2 := hT _ hp.2
          have hn : 0 < (p.1 * p.2) ^ 2 := by have := a1.1; have := a2.1; positivity
          refine divisor_bound_le hδ hCτ hCτ1 hn ?_
          have b1 : (p.1 : ℝ) ≤ Wmax := by exact_mod_cast a1.2
          have b2 : (p.2 : ℝ) ≤ Wmax := by exact_mod_cast a2.2
          have b0 : (0 : ℝ) ≤ p.1 := by positivity
          have b0' : (0 : ℝ) ≤ p.2 := by positivity
          push_cast
          calc ((p.1 : ℝ) * p.2) ^ 2 ≤ ((Wmax : ℝ) * Wmax) ^ 2 := by gcongr
            _ = (Wmax : ℝ) ^ 4 := by ring
            _ ≤ X := hX1
      _ = (T.card : ℝ) ^ 2 * (Cτ * X ^ δ) := by
          rw [sum_const, nsmul_eq_mul, card_product]; push_cast; ring
  -- the quadruples with `Δ ≠ 0`
  have h1 : ∀ t ∈ (T ×ˢ T ×ˢ T ×ˢ T).filter (fun t => Energy.intDelta t ≠ 0),
      ((R.filter (fun q : ℕ => (q : ℤ) ∣ Energy.intDelta t)).card : ℝ) ≤ Cτ * X ^ δ := by
    intro t ht
    simp only [mem_filter, mem_product] at ht
    obtain ⟨⟨h1, h2, h3, h4⟩, hΔ⟩ := ht
    have hb : |Energy.intDelta t| ≤ 2 * (Wmax : ℤ) ^ 3 :=
      Energy.abs_intDelta_le (hT _ h1).2 (hT _ h2).2 (hT _ h3).2 (hT _ h4).2
    have hb' : ((Energy.intDelta t).natAbs : ℝ) ≤ X := by
      have : ((Energy.intDelta t).natAbs : ℤ) ≤ 2 * (Wmax : ℤ) ^ 3 := by
        rw [Int.natCast_natAbs]; exact hb
      have : ((Energy.intDelta t).natAbs : ℝ) ≤ 2 * (Wmax : ℝ) ^ 3 := by exact_mod_cast this
      linarith
    calc ((R.filter (fun q : ℕ => (q : ℤ) ∣ Energy.intDelta t)).card : ℝ)
        ≤ (Energy.intDelta t).natAbs.divisors.card := by exact_mod_cast card_filter_dvd_le R hΔ
      _ ≤ Cτ * X ^ δ :=
          divisor_bound_le hδ hCτ hCτ1 (Int.natAbs_pos.2 hΔ) hb'
  have h2 : (∑ t ∈ (T ×ˢ T ×ˢ T ×ˢ T).filter (fun t => Energy.intDelta t ≠ 0),
      ((R.filter (fun q : ℕ => (q : ℤ) ∣ Energy.intDelta t)).card : ℝ)) ≤
      (T.card : ℝ) ^ 4 * (Cτ * X ^ δ) := by
    refine (sum_le_sum h1).trans ?_
    rw [sum_const, nsmul_eq_mul]
    have hpos : 0 ≤ Cτ * X ^ δ := by
      have : 0 ≤ X := le_trans (by positivity) hX2
      positivity
    refine mul_le_mul_of_nonneg_right ?_ hpos
    have : ((T ×ˢ T ×ˢ T ×ˢ T).filter (fun t => Energy.intDelta t ≠ 0)).card ≤ T.card ^ 4 := by
      refine (card_filter_le _ _).trans (le_of_eq ?_)
      simp only [card_product]; ring
    exact_mod_cast this
  have h' : (∑ e ∈ R, (((T ×ˢ T ×ˢ T ×ˢ T).filter (Energy.IntCounted e)).card : ℝ)) ≤
      (R.card : ℝ) * ((T ×ˢ T ×ˢ T ×ˢ T).filter (fun t => Energy.intDelta t = 0)).card +
        ∑ t ∈ (T ×ˢ T ×ˢ T ×ˢ T).filter (fun t => Energy.intDelta t ≠ 0),
          ((R.filter (fun q : ℕ => (q : ℤ) ∣ Energy.intDelta t)).card : ℝ) := by
    exact_mod_cast h
  have hR : (0 : ℝ) ≤ R.card := by positivity
  nlinarith

/-- The coincidences `h/u = h'/u'` in a set `S ⊂ ([-H,H] ∖ {0}) × [1, Umax]` number at most
`(2H+1) Umax · C_τ X^δ` whenever `H Umax ≤ X`. -/
theorem card_pairs_bound (Hn Umax : ℕ) (S : Finset (ℤ × ℕ))
    (hS : ∀ s ∈ S, s.1 ≠ 0 ∧ |s.1| ≤ Hn ∧ 1 ≤ s.2 ∧ s.2 ≤ Umax) {δ Cτ X : ℝ}
    (hCτ : ∀ n : ℕ, 1 ≤ n → (n.divisors.card : ℝ) ≤ Cτ * (n : ℝ) ^ δ) (hδ : 0 < δ)
    (hCτ1 : 1 ≤ Cτ) (hX : (Hn : ℝ) * Umax ≤ X) :
    (((S ×ˢ S).filter (fun p => frac p.1 = frac p.2)).card : ℝ) ≤
      (2 * Hn + 1) * Umax * (Cτ * X ^ δ) := by
  have h : ((S ×ˢ S).filter (fun p => frac p.1 = frac p.2)).card ≤
      ∑ x ∈ (Icc (-(Hn : ℤ)) Hn ×ˢ Icc 1 Umax).filter (fun x => x.1 ≠ 0),
        (x.1.natAbs * x.2).divisors.card := card_pairs_le Hn Umax S hS
  have h' : (((S ×ˢ S).filter (fun p => frac p.1 = frac p.2)).card : ℝ) ≤
      ∑ x ∈ (Icc (-(Hn : ℤ)) Hn ×ˢ Icc 1 Umax).filter (fun x => x.1 ≠ 0),
        ((x.1.natAbs * x.2).divisors.card : ℝ) := by
    exact_mod_cast h
  refine h'.trans ?_
  calc ∑ x ∈ (Icc (-(Hn : ℤ)) Hn ×ˢ Icc 1 Umax).filter (fun x => x.1 ≠ 0),
        ((x.1.natAbs * x.2).divisors.card : ℝ)
      ≤ ∑ _x ∈ (Icc (-(Hn : ℤ)) Hn ×ˢ Icc 1 Umax).filter (fun x => x.1 ≠ 0), Cτ * X ^ δ := by
        refine sum_le_sum (fun x hx => ?_)
        simp only [mem_filter, mem_product, mem_Icc] at hx
        have a1 : x.1.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hx.2
        have a2 : x.2 ≠ 0 := by omega
        have hn : 0 < x.1.natAbs * x.2 := by positivity
        refine divisor_bound_le hδ hCτ hCτ1 hn ?_
        have b1 : (x.1.natAbs : ℝ) ≤ Hn := by
          have : (x.1.natAbs : ℤ) ≤ Hn := by
            rw [Int.natCast_natAbs]; exact abs_le.2 hx.1.1
          exact_mod_cast this
        have b2 : (x.2 : ℝ) ≤ Umax := by exact_mod_cast hx.1.2.2
        push_cast
        calc (x.1.natAbs : ℝ) * x.2 ≤ Hn * Umax := by gcongr
          _ ≤ X := hX
    _ = ((((Icc (-(Hn : ℤ)) Hn ×ˢ Icc 1 Umax).filter (fun x => x.1 ≠ 0)).card : ℕ) : ℝ) *
          (Cτ * X ^ δ) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (2 * Hn + 1) * Umax * (Cτ * X ^ δ) := by
        have hpos : 0 ≤ Cτ * X ^ δ := by
          have : 0 ≤ X := le_trans (by positivity) hX
          positivity
        gcongr
        have : ((Icc (-(Hn : ℤ)) Hn ×ˢ Icc 1 Umax).filter (fun x => x.1 ≠ 0)).card ≤
            (2 * Hn + 1) * Umax := by
          refine (card_filter_le _ _).trans (le_of_eq ?_)
          have e1 : ((Hn : ℤ) + 1 - -(Hn : ℤ)).toNat = 2 * Hn + 1 := by omega
          rw [card_product, Int.card_Icc, Nat.card_Icc, e1, Nat.add_sub_cancel]
        exact_mod_cast this

end BalancedBox
end MobiusDeterminant
