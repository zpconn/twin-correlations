import MobiusDeterminant.Unconditional.Interfaces
import MobiusDeterminant.Core.KorolevChanga
import MobiusDeterminant.Core.Energy
import LeanPool.MarkoffModP.BGS.NumberTheory.DivisorBound

/-!
# Balanced boxes: generic lemmas

Auxiliary results for `balancedBoxBound_of_BM` (paper, Proposition 5.1 and Steps 1, 3 of
the proof of Theorem 6.1):

* the divisor bound in the form `τ(n) ≤ C n^δ` for all `n ≥ 1`;
* Lemma 3.1 (Korolev–Changa) for families indexed by finsets;
* the double count of Lemmas 4.1 / 4.3 for an arbitrary finite set of moduli;
* the Hölder step `(4, 4, 2)` of the proof of Proposition 5.1, in eighth-power form;
* `kfrac` as the standard additive character of `ZMod e`.
-/

open Finset

namespace MobiusDeterminant
namespace BalancedBox

/-! ## The divisor bound -/

/-- Divisor bound (paper, Lemma 2.1): `τ(n) ≤ C n^δ` for every `n ≥ 1`. -/
theorem divisor_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ C ≥ (1 : ℝ), ∀ n : ℕ, 1 ≤ n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ δ := by
  obtain ⟨N, hN⟩ := BGS.NumberTheory.exists_threshold_card_divisors_le_rpow hδ
  refine ⟨1 + ∑ m ∈ range N, (m.divisors.card : ℝ), ?_, ?_⟩
  · have : 0 ≤ ∑ m ∈ range N, (m.divisors.card : ℝ) := sum_nonneg (fun _ _ => by positivity)
    linarith
  intro n hn
  have hpow : (1 : ℝ) ≤ (n : ℝ) ^ δ :=
    Real.one_le_rpow (by exact_mod_cast hn) hδ.le
  have hS : 0 ≤ ∑ m ∈ range N, (m.divisors.card : ℝ) := sum_nonneg (fun _ _ => by positivity)
  rcases lt_or_ge n N with h | h
  · have h1 : (n.divisors.card : ℝ) ≤ ∑ m ∈ range N, (m.divisors.card : ℝ) :=
      single_le_sum (f := fun m => (m.divisors.card : ℝ)) (fun _ _ => by positivity)
        (mem_range.2 h)
    nlinarith
  · have := hN n h
    nlinarith

/-- Divisor bound with a cap: if `1 ≤ n ≤ X` then `τ(n) ≤ C X^δ`. -/
theorem divisor_bound_le {δ : ℝ} (hδ : 0 < δ) {C : ℝ}
    (hC : ∀ n : ℕ, 1 ≤ n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ δ) (hC1 : 1 ≤ C)
    {n : ℕ} {X : ℝ} (hn : 1 ≤ n) (hX : (n : ℝ) ≤ X) :
    (n.divisors.card : ℝ) ≤ C * X ^ δ := by
  refine (hC n hn).trans ?_
  gcongr

/-! ## Lemma 3.1 for finsets -/

lemma energy_coe_finset {q : ℕ} {α : Type*} (S : Finset α) (a : α → ZMod q) :
    KorolevChanga.energy (fun i : S => a i) =
      ((S ×ˢ S ×ˢ S ×ˢ S).filter
        (fun t => a t.1 + a t.2.1 = a t.2.2.1 + a t.2.2.2)).card := by
  classical
  have h1 := KorolevChanga.energy_eq_sum (R := ℕ) (fun i : S => a i)
  simp only [Nat.cast_id] at h1
  rw [h1, card_filter]
  simp only [Fintype.sum_prod_type, sum_product]
  rw [← sum_coe_sort S]
  refine sum_congr rfl (fun i _ => ?_)
  rw [← sum_coe_sort S]
  refine sum_congr rfl (fun j _ => ?_)
  rw [← sum_coe_sort S]
  refine sum_congr rfl (fun k _ => ?_)
  rw [← sum_coe_sort S]

/-- **Lemma 3.1 (paper), finset form**, for the standard character `e_q` and arbitrary
residues `a i` (the `z̄`) and `b k` (the `w̄`):
`|∑_{i∈S} ∑_{k∈T} γ_i δ_k e_q(a_i b_k)|⁸ ≤ ‖γ‖₂⁸ ‖δ‖₂⁸ · q · E(a) · E(b)`. -/
theorem kc_finset {q : ℕ} [NeZero q] {α β : Type*} (S : Finset α) (T : Finset β)
    (a : α → ZMod q) (b : β → ZMod q) (γ : α → ℂ) (δ : β → ℂ) :
    ‖∑ i ∈ S, ∑ k ∈ T, γ i * δ k * ZMod.stdAddChar (a i * b k)‖ ^ 8 ≤
      (∑ i ∈ S, ‖γ i‖ ^ 2) ^ 4 * (∑ k ∈ T, ‖δ k‖ ^ 2) ^ 4 * (q : ℝ) *
        ((S ×ˢ S ×ˢ S ×ˢ S).filter
          (fun t => a t.1 + a t.2.1 = a t.2.2.1 + a t.2.2.2)).card *
        ((T ×ˢ T ×ˢ T ×ˢ T).filter
          (fun t => b t.1 + b t.2.1 = b t.2.2.1 + b t.2.2.2)).card := by
  have h := KorolevChanga.bilinear_pow_eight_le ZMod.stdAddChar (ZMod.isPrimitive_stdAddChar q)
    (ι := S) (κ := T) 1 isUnit_one (fun i => a i) (fun k => b k) (fun i => γ i) (fun k => δ k)
  rw [energy_coe_finset, energy_coe_finset] at h
  simp only [one_mul] at h
  have e1 : ∑ i : S, ∑ k : T, γ i * δ k * ZMod.stdAddChar (a i * b k) =
      ∑ i ∈ S, ∑ k ∈ T, γ i * δ k * ZMod.stdAddChar (a i * b k) := by
    rw [← sum_coe_sort S]
    refine sum_congr rfl (fun i _ => ?_)
    rw [← sum_coe_sort T]
  have e2 : ∑ i : S, ‖γ i‖ ^ 2 = ∑ i ∈ S, ‖γ i‖ ^ 2 := sum_coe_sort S (fun i => ‖γ i‖ ^ 2)
  have e3 : ∑ k : T, ‖δ k‖ ^ 2 = ∑ k ∈ T, ‖δ k‖ ^ 2 := sum_coe_sort T (fun k => ‖δ k‖ ^ 2)
  rw [e1, e2, e3] at h
  exact h

/-! ## The double count for an arbitrary set of moduli -/

/-- Paper, Lemmas 4.1 and 4.3 (counting skeleton) for an arbitrary finite set `R` of
moduli: `∑_{q∈R} #{t : P q t} ≤ #R·#{Δ = 0} + ∑_{Δ t ≠ 0} #{q ∈ R : q ∣ Δ t}`. -/
theorem sum_count_le {α : Type*} (R : Finset ℕ) (S : Finset α) (Δ : α → ℤ)
    (P : ℕ → α → Prop) [∀ q t, Decidable (P q t)]
    (hP : ∀ q ∈ R, ∀ t ∈ S, P q t → (q : ℤ) ∣ Δ t) :
    ∑ q ∈ R, (S.filter (P q)).card ≤
      R.card * (S.filter (fun t => Δ t = 0)).card +
        ∑ t ∈ S.filter (fun t => Δ t ≠ 0), (R.filter (fun q : ℕ => (q : ℤ) ∣ Δ t)).card := by
  classical
  have swap : ∑ q ∈ R, (S.filter (P q)).card
      = ∑ t ∈ S, (R.filter (fun q => P q t)).card := by
    simp only [card_eq_sum_ones, sum_filter]
    exact sum_comm
  rw [swap, ← sum_filter_add_sum_filter_not S (fun t => Δ t = 0)]
  apply add_le_add
  · calc ∑ t ∈ S.filter (fun t => Δ t = 0), (R.filter (fun q => P q t)).card
        ≤ ∑ _t ∈ S.filter (fun t => Δ t = 0), R.card :=
          sum_le_sum (fun t _ => card_filter_le _ _)
      _ = R.card * (S.filter (fun t => Δ t = 0)).card := by
          rw [sum_const, smul_eq_mul, mul_comm]
  · apply sum_le_sum
    intro t ht
    apply card_le_card
    intro q hq
    simp only [mem_filter] at hq ⊢
    exact ⟨hq.1, hP q hq.1 t (mem_filter.1 ht).1 hq.2⟩

/-- `#{q ∈ R : q ∣ Δ} ≤ τ(|Δ|)` for `Δ ≠ 0`. -/
theorem card_filter_dvd_le (R : Finset ℕ) {Δ : ℤ} (hΔ : Δ ≠ 0) :
    (R.filter (fun q : ℕ => (q : ℤ) ∣ Δ)).card ≤ Δ.natAbs.divisors.card := by
  apply card_le_card
  intro q hq
  simp only [mem_filter] at hq
  rw [Nat.mem_divisors]
  exact ⟨Int.natCast_dvd.mp hq.2, Int.natAbs_ne_zero.mpr hΔ⟩

/-! ## The Hölder step -/

/-- The Hölder step `(4,4,2)` of the proof of Proposition 5.1, in fourth-power form: if
`A_e ≥ 0` and `A_e⁴ ≤ K⁴ · Y₀ · x_e y_e` for `e ∈ R`, then
`(∑_{e∈R} A_e)⁴ ≤ #R² · K⁴ · Y₀ · (∑ x_e)(∑ y_e)`. -/
theorem holder_step (R : Finset ℕ) (A x y : ℕ → ℝ) (K Y₀ : ℝ) (hY₀ : 0 ≤ Y₀)
    (hx : ∀ e, 0 ≤ x e) (hy : ∀ e, 0 ≤ y e)
    (hb : ∀ e ∈ R, A e ^ 4 ≤ K ^ 4 * Y₀ * (x e * y e)) :
    (∑ e ∈ R, A e) ^ 4 ≤ (R.card : ℝ) ^ 2 * K ^ 4 * Y₀ * ((∑ e ∈ R, x e) * ∑ e ∈ R, y e) := by
  have hsq : ∀ e ∈ R, A e ^ 2 ≤ K ^ 2 * Real.sqrt Y₀ * (Real.sqrt (x e) * Real.sqrt (y e)) := by
    intro e he
    have h1 : A e ^ 2 = Real.sqrt (A e ^ 4) := by
      rw [show A e ^ 4 = (A e ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    rw [h1]
    calc Real.sqrt (A e ^ 4) ≤ Real.sqrt (K ^ 4 * Y₀ * (x e * y e)) := Real.sqrt_le_sqrt (hb e he)
      _ = K ^ 2 * Real.sqrt Y₀ * (Real.sqrt (x e) * Real.sqrt (y e)) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
          Real.sqrt_mul (hx e), show K ^ 4 = (K ^ 2) ^ 2 by ring,
          Real.sqrt_sq (by positivity)]
  have hS2 : ∑ e ∈ R, A e ^ 2 ≤
      K ^ 2 * Real.sqrt Y₀ * (Real.sqrt (∑ e ∈ R, x e) * Real.sqrt (∑ e ∈ R, y e)) := by
    calc ∑ e ∈ R, A e ^ 2
        ≤ ∑ e ∈ R, K ^ 2 * Real.sqrt Y₀ * (Real.sqrt (x e) * Real.sqrt (y e)) :=
          sum_le_sum hsq
      _ = K ^ 2 * Real.sqrt Y₀ * ∑ e ∈ R, Real.sqrt (x e) * Real.sqrt (y e) := by
          rw [mul_sum]
      _ ≤ _ := by
          gcongr
          exact Real.sum_sqrt_mul_sqrt_le R hx hy
  have hS2' : (∑ e ∈ R, A e ^ 2) ^ 2 ≤ K ^ 4 * Y₀ * ((∑ e ∈ R, x e) * ∑ e ∈ R, y e) := by
    have h0 : 0 ≤ ∑ e ∈ R, A e ^ 2 := sum_nonneg (fun _ _ => sq_nonneg _)
    have hX : 0 ≤ ∑ e ∈ R, x e := sum_nonneg (fun e _ => hx e)
    have hYs : 0 ≤ ∑ e ∈ R, y e := sum_nonneg (fun e _ => hy e)
    calc (∑ e ∈ R, A e ^ 2) ^ 2
        ≤ (K ^ 2 * Real.sqrt Y₀ * (Real.sqrt (∑ e ∈ R, x e) * Real.sqrt (∑ e ∈ R, y e))) ^ 2 := by
          gcongr
      _ = K ^ 4 * Y₀ * ((∑ e ∈ R, x e) * ∑ e ∈ R, y e) := by
          rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hY₀, Real.sq_sqrt hX, Real.sq_sqrt hYs]
          ring
  have hCS : (∑ e ∈ R, A e) ^ 2 ≤ (R.card : ℝ) * ∑ e ∈ R, A e ^ 2 := sq_sum_le_card_mul_sum_sq
  calc (∑ e ∈ R, A e) ^ 4 = ((∑ e ∈ R, A e) ^ 2) ^ 2 := by ring
    _ ≤ ((R.card : ℝ) * ∑ e ∈ R, A e ^ 2) ^ 2 := by
        gcongr
    _ = (R.card : ℝ) ^ 2 * (∑ e ∈ R, A e ^ 2) ^ 2 := by ring
    _ ≤ (R.card : ℝ) ^ 2 * (K ^ 4 * Y₀ * ((∑ e ∈ R, x e) * ∑ e ∈ R, y e)) := by gcongr
    _ = _ := by ring

/-! ## Kloosterman fractions as additive characters -/

/-- `kfrac e h d = e_e(h d̄)` is the standard additive character of `ZMod e`. -/
theorem kfrac_eq_stdAddChar (e : ℕ) [NeZero e] (h : ℤ) (d : ℕ) :
    kfrac e h d = ZMod.stdAddChar ((h : ZMod e) * (d : ZMod e)⁻¹) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply, kfrac]

/-- `\overline{uw} = ū w̄` modulo `e` for `u, w` coprime to `e`. -/
theorem inv_natCast_mul {e u w : ℕ} (hu : Nat.Coprime u e) (hw : Nat.Coprime w e) :
    (((u * w : ℕ) : ZMod e))⁻¹ = (u : ZMod e)⁻¹ * (w : ZMod e)⁻¹ := by
  have huw : Nat.Coprime (u * w) e := Nat.coprime_mul_iff_left.2 ⟨hu, hw⟩
  have h1 := ZMod.coe_mul_inv_eq_one _ huw
  have h2 := ZMod.coe_mul_inv_eq_one _ hu
  have h3 := ZMod.coe_mul_inv_eq_one _ hw
  push_cast at h1 ⊢
  calc ((u : ZMod e) * w)⁻¹ = ((u : ZMod e) * w)⁻¹ * ((u * (u : ZMod e)⁻¹) * (w * (w : ZMod e)⁻¹)) := by
        rw [h2, h3]; ring
    _ = (((u : ZMod e) * w) * ((u : ZMod e) * w)⁻¹) * ((u : ZMod e)⁻¹ * (w : ZMod e)⁻¹) := by ring
    _ = _ := by rw [h1]; ring

end BalancedBox
end MobiusDeterminant
