import Mathlib

/-!
# Reciprocal energies averaged over the modulus: exact counting forms
(paper, Section 4, Lemmas 4.1 and 4.3)

The analytic content of Lemmas 4.1 and 4.3 is a double count: a quadruple
counted by the energy modulo `q` satisfies `q ∣ Δ`.  Quadruples with `Δ = 0`
are exact rational solutions and are counted for every one of the (at most
`Q`, resp. `Q + 1`) moduli `q ∈ (Q, 2Q]`; a quadruple with `Δ ≠ 0` is counted
only for the moduli `q ∈ (Q, 2Q]` dividing `Δ`, of which there are at most
`τ(|Δ|)`.  We prove this exactly (no `≪`), together with

* the algebra `x̄₁ + x̄₂ ≡ x̄₃ + x̄₄ (mod q) ⟹ q ∣ Δ` for
  `Δ = (x₁+x₂)x₃x₄ - (x₃+x₄)x₁x₂` (Lemma 4.1), and
  `a₁ū₁ + a₂ū₂ ≡ a₃ū₃ + a₄ū₄ (mod q) ⟹ q ∣ Δ` for
  `Δ = a₁u₂u₃u₄ + a₂u₁u₃u₄ - a₃u₁u₂u₄ - a₄u₁u₂u₃` (Lemma 4.3);
* `Δ = 0 ↔` the exact rational equation;
* the size bounds `|Δ| ≤ 2N³` and `|Δ| ≤ 4 M' U³`;
* the identity `(ax - b)(ay - b) = b²` for `1/x + 1/y = a/b`, and the resulting
  bound `#{(x, y) ∈ ℕ_{>0}² : 1/x + 1/y = a/b} ≤ τ(b²)`.
-/

namespace MobiusDeterminant

namespace Energy

open Finset

/-! ## The abstract double count -/

/-- Paper, Lemmas 4.1 and 4.3 (the counting skeleton).  Let `S` be a finite set
of quadruples (or any objects), `Δ : S → ℤ`, and `P q t` the event "`t` is
counted by the energy modulo `q`", with `P q t → q ∣ Δ t`.  Then
`∑_{Q<q≤2Q} #{t : P q t} ≤ Q·#{t : Δ t = 0} + ∑_{t : Δ t ≠ 0} #{q ∈ (Q,2Q] : q ∣ Δ t}`. -/
theorem sum_energy_le {α : Type*} (S : Finset α) (Δ : α → ℤ) (P : ℕ → α → Prop)
    [∀ q t, Decidable (P q t)] (hP : ∀ q t, t ∈ S → P q t → (q : ℤ) ∣ Δ t) (Q : ℕ) :
    ∑ q ∈ Ioc Q (2 * Q), (S.filter (P q)).card ≤
      Q * (S.filter (fun t => Δ t = 0)).card +
        ∑ t ∈ S.filter (fun t => Δ t ≠ 0),
          ((Ioc Q (2 * Q)).filter (fun q : ℕ => (q : ℤ) ∣ Δ t)).card := by
  classical
  have swap : ∑ q ∈ Ioc Q (2 * Q), (S.filter (P q)).card
      = ∑ t ∈ S, ((Ioc Q (2 * Q)).filter (fun q => P q t)).card := by
    simp only [card_eq_sum_ones, sum_filter]
    exact sum_comm
  rw [swap, ← sum_filter_add_sum_filter_not S (fun t => Δ t = 0)]
  apply add_le_add
  · calc ∑ t ∈ S.filter (fun t => Δ t = 0), ((Ioc Q (2 * Q)).filter (fun q => P q t)).card
        ≤ ∑ _t ∈ S.filter (fun t => Δ t = 0), Q := by
          apply sum_le_sum
          intro t _
          calc ((Ioc Q (2 * Q)).filter (fun q => P q t)).card ≤ (Ioc Q (2 * Q)).card :=
                card_filter_le _ _
            _ = Q := by rw [Nat.card_Ioc]; omega
      _ = Q * (S.filter (fun t => Δ t = 0)).card := by rw [sum_const, smul_eq_mul, mul_comm]
  · apply sum_le_sum
    intro t ht
    apply card_le_card
    intro q hq
    simp only [mem_filter] at hq ⊢
    exact ⟨hq.1, hP q t (mem_filter.1 ht).1 hq.2⟩

/-- The number of moduli `q ∈ (Q, 2Q]` dividing a nonzero integer `Δ` is at most
`τ(|Δ|)` (paper, Lemma 4.1: "contributes for at most `τ(|Δ|)` moduli"). -/
theorem card_dvd_le_tau {Δ : ℤ} (hΔ : Δ ≠ 0) (Q : ℕ) :
    ((Ioc Q (2 * Q)).filter (fun q : ℕ => (q : ℤ) ∣ Δ)).card ≤ Δ.natAbs.divisors.card := by
  apply card_le_card
  intro q hq
  simp only [mem_filter] at hq
  rw [Nat.mem_divisors]
  exact ⟨Int.natCast_dvd.mp hq.2, Int.natAbs_ne_zero.mpr hΔ⟩

/-- Paper, Lemmas 4.1 and 4.3, with the divisor bound inserted:
`∑_{Q<q≤2Q} I(q) ≤ Q·#{Δ = 0} + ∑_{Δ ≠ 0} τ(|Δ|)`. -/
theorem sum_energy_le_tau {α : Type*} (S : Finset α) (Δ : α → ℤ) (P : ℕ → α → Prop)
    [∀ q t, Decidable (P q t)] (hP : ∀ q t, t ∈ S → P q t → (q : ℤ) ∣ Δ t) (Q : ℕ) :
    ∑ q ∈ Ioc Q (2 * Q), (S.filter (P q)).card ≤
      Q * (S.filter (fun t => Δ t = 0)).card +
        ∑ t ∈ S.filter (fun t => Δ t ≠ 0), (Δ t).natAbs.divisors.card := by
  refine (sum_energy_le S Δ P hP Q).trans (add_le_add le_rfl (sum_le_sum fun t ht => ?_))
  exact card_dvd_le_tau (mem_filter.1 ht).2 Q

/-- For real `Q ≥ 0`, the number of integers `q` with `Q < q ≤ 2Q` is at most
`Q + 1` (paper: "each counted for at most `Q + 1` moduli"). -/
theorem card_dyadic_le {Q : ℝ} (hQ : 0 ≤ Q) :
    ((Ioc ⌊Q⌋₊ ⌊2 * Q⌋₊).card : ℝ) ≤ Q + 1 := by
  rw [Nat.card_Ioc]
  have h1 : (⌊2 * Q⌋₊ : ℝ) ≤ 2 * Q := Nat.floor_le (by positivity)
  have h2 : Q < (⌊Q⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one Q
  rcases le_total ⌊2 * Q⌋₊ ⌊Q⌋₊ with h | h
  · rw [Nat.sub_eq_zero_of_le h]; simp; linarith
  · rw [Nat.cast_sub h]; linarith

/-- The integers `q` with `Q < q ≤ 2Q` (real `Q ≥ 0`) are exactly
`Ioc ⌊Q⌋₊ ⌊2Q⌋₊`. -/
theorem mem_dyadic_iff {Q : ℝ} (hQ : 0 ≤ Q) (q : ℕ) :
    q ∈ Ioc ⌊Q⌋₊ ⌊2 * Q⌋₊ ↔ Q < q ∧ (q : ℝ) ≤ 2 * Q := by
  rw [mem_Ioc, Nat.floor_lt hQ, Nat.le_floor_iff (by positivity)]

/-! ## Lemma 4.1: integers -/

/-- A quadruple of naturals. -/
abbrev Quad := ℕ × ℕ × ℕ × ℕ

/-- `Δ = (x₁+x₂)x₃x₄ - (x₃+x₄)x₁x₂` (paper, proof of Lemma 4.1). -/
def intDelta (t : Quad) : ℤ :=
  ((t.1 : ℤ) + t.2.1) * t.2.2.1 * t.2.2.2 - ((t.2.2.1 : ℤ) + t.2.2.2) * t.1 * t.2.1

/-- The event "`t` is counted by `I(q; 𝓘)`": all entries are units modulo `q`
and `x̄₁ + x̄₂ ≡ x̄₃ + x̄₄ (mod q)`. -/
def IntCounted (q : ℕ) (t : Quad) : Prop :=
  Nat.Coprime t.1 q ∧ Nat.Coprime t.2.1 q ∧ Nat.Coprime t.2.2.1 q ∧ Nat.Coprime t.2.2.2 q ∧
    ((t.1 : ZMod q)⁻¹ + (t.2.1 : ZMod q)⁻¹ = (t.2.2.1 : ZMod q)⁻¹ + (t.2.2.2 : ZMod q)⁻¹)

instance (q : ℕ) (t : Quad) : Decidable (IntCounted q t) := by
  unfold IntCounted; infer_instance

/-- The reciprocal energy `I_𝓘(q)` of the units of a finite set `𝓘 ⊂ ℕ` modulo `q`
(paper, Section 3 and Lemma 4.1). -/
def intEnergy (I : Finset ℕ) (q : ℕ) : ℕ :=
  ((I ×ˢ I ×ˢ I ×ˢ I).filter (IntCounted q)).card

/-- Paper, proof of Lemma 4.1: "Clearing denominators, a counted quadruple
satisfies `q ∣ Δ`." -/
theorem dvd_intDelta {q : ℕ} {t : Quad} (h : IntCounted q t) : (q : ℤ) ∣ intDelta t := by
  obtain ⟨c1, c2, c3, c4, heq⟩ := h
  have h1 := ZMod.coe_mul_inv_eq_one _ c1
  have h2 := ZMod.coe_mul_inv_eq_one _ c2
  have h3 := ZMod.coe_mul_inv_eq_one _ c3
  have h4 := ZMod.coe_mul_inv_eq_one _ c4
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  unfold intDelta
  push_cast
  set u1 := (t.1 : ZMod q)
  set u2 := (t.2.1 : ZMod q)
  set u3 := (t.2.2.1 : ZMod q)
  set u4 := (t.2.2.2 : ZMod q)
  linear_combination (u1 * u2 * u3 * u4) * heq - (u2 * u3 * u4) * h1 - (u1 * u3 * u4) * h2
    + (u1 * u2 * u4) * h3 + (u1 * u2 * u3) * h4

/-- Paper, proof of Lemma 4.1: for positive entries, `Δ = 0` iff
`1/x₁ + 1/x₂ = 1/x₃ + 1/x₄` in `ℚ`. -/
theorem intDelta_eq_zero_iff {t : Quad} (h1 : 0 < t.1) (h2 : 0 < t.2.1) (h3 : 0 < t.2.2.1)
    (h4 : 0 < t.2.2.2) :
    intDelta t = 0 ↔
      (1 / t.1 + 1 / t.2.1 : ℚ) = 1 / t.2.2.1 + 1 / t.2.2.2 := by
  have e1 : (t.1 : ℚ) ≠ 0 := by positivity
  have e2 : (t.2.1 : ℚ) ≠ 0 := by positivity
  have e3 : (t.2.2.1 : ℚ) ≠ 0 := by positivity
  have e4 : (t.2.2.2 : ℚ) ≠ 0 := by positivity
  have key : (1 / t.1 + 1 / t.2.1 : ℚ) - (1 / t.2.2.1 + 1 / t.2.2.2)
      = (intDelta t : ℚ) / (t.1 * t.2.1 * t.2.2.1 * t.2.2.2) := by
    unfold intDelta; push_cast; field_simp; ring
  rw [← sub_eq_zero (a := (1 / (t.1 : ℚ) + 1 / t.2.1)), key, div_eq_zero_iff]
  have : (t.1 * t.2.1 * t.2.2.1 * t.2.2.2 : ℚ) ≠ 0 := by positivity
  simp [this]

/-- Paper, Lemma 4.1, exact form: for every finite `𝓘 ⊂ ℕ` and `Q`,
`∑_{Q<q≤2Q} I_𝓘(q) ≤ Q·#{rational solutions} + ∑_{Δ ≠ 0} #{q ∈ (Q,2Q] : q ∣ Δ}`,
where "rational solutions" are the quadruples in `𝓘⁴` with `Δ = 0`. -/
theorem sum_intEnergy_le (I : Finset ℕ) (Q : ℕ) :
    ∑ q ∈ Ioc Q (2 * Q), intEnergy I q ≤
      Q * ((I ×ˢ I ×ˢ I ×ˢ I).filter (fun t => intDelta t = 0)).card +
        ∑ t ∈ (I ×ˢ I ×ˢ I ×ˢ I).filter (fun t => intDelta t ≠ 0),
          ((Ioc Q (2 * Q)).filter (fun q : ℕ => (q : ℤ) ∣ intDelta t)).card :=
  sum_energy_le _ intDelta IntCounted (fun _ _ _ h => dvd_intDelta h) Q

/-- Paper, Lemma 4.1, exact form with the divisor bound:
`∑_{Q<q≤2Q} I_𝓘(q) ≤ Q·#{Δ = 0} + ∑_{Δ ≠ 0} τ(|Δ|)`; when `𝓘 ⊂ ℕ_{>0}` the
`Δ = 0` quadruples are exactly the solutions of `1/x₁+1/x₂ = 1/x₃+1/x₄`. -/
theorem sum_intEnergy_le_tau (I : Finset ℕ) (Q : ℕ) :
    ∑ q ∈ Ioc Q (2 * Q), intEnergy I q ≤
      Q * ((I ×ˢ I ×ˢ I ×ˢ I).filter (fun t => intDelta t = 0)).card +
        ∑ t ∈ (I ×ˢ I ×ˢ I ×ˢ I).filter (fun t => intDelta t ≠ 0),
          (intDelta t).natAbs.divisors.card :=
  sum_energy_le_tau _ intDelta IntCounted (fun _ _ _ h => dvd_intDelta h) Q

/-- Paper, proof of Lemma 4.1: "`|Δ| ≪ N³`"; precisely, if all `xᵢ ≤ N` then
`|Δ| ≤ 2N³`. -/
theorem abs_intDelta_le {t : Quad} {N : ℕ} (h1 : t.1 ≤ N) (h2 : t.2.1 ≤ N) (h3 : t.2.2.1 ≤ N)
    (h4 : t.2.2.2 ≤ N) : |intDelta t| ≤ 2 * (N : ℤ) ^ 3 := by
  unfold intDelta
  have a1 : (t.1 : ℤ) ≤ N := by exact_mod_cast h1
  have a2 : (t.2.1 : ℤ) ≤ N := by exact_mod_cast h2
  have a3 : (t.2.2.1 : ℤ) ≤ N := by exact_mod_cast h3
  have a4 : (t.2.2.2 : ℤ) ≤ N := by exact_mod_cast h4
  have b1 : (0 : ℤ) ≤ t.1 := by positivity
  have b2 : (0 : ℤ) ≤ t.2.1 := by positivity
  have b3 : (0 : ℤ) ≤ t.2.2.1 := by positivity
  have b4 : (0 : ℤ) ≤ t.2.2.2 := by positivity
  have hA : ((t.1 : ℤ) + t.2.1) * t.2.2.1 * t.2.2.2 ≤ 2 * (N : ℤ) ^ 3 := by
    have : ((t.1 : ℤ) + t.2.1) * t.2.2.1 * t.2.2.2 ≤ (N + N) * N * N :=
      mul_le_mul (mul_le_mul (by linarith) a3 b3 (by positivity)) a4 b4 (by positivity)
    nlinarith
  have hB : ((t.2.2.1 : ℤ) + t.2.2.2) * t.1 * t.2.1 ≤ 2 * (N : ℤ) ^ 3 := by
    have : ((t.2.2.1 : ℤ) + t.2.2.2) * t.1 * t.2.1 ≤ (N + N) * N * N :=
      mul_le_mul (mul_le_mul (by linarith) a1 b1 (by positivity)) a2 b2 (by positivity)
    nlinarith
  have hA0 : 0 ≤ ((t.1 : ℤ) + t.2.1) * t.2.2.1 * t.2.2.2 := by positivity
  have hB0 : 0 ≤ ((t.2.2.1 : ℤ) + t.2.2.2) * t.1 * t.2.1 := by positivity
  rw [abs_le]
  constructor <;> linarith

/-! ## Lemma 4.3: reduced fractions -/

/-- A fraction `a/u` recorded as the pair `(a, u)`. -/
abbrev Frac := ℤ × ℕ

/-- `Δ = a₁u₂u₃u₄ + a₂u₁u₃u₄ - a₃u₁u₂u₄ - a₄u₁u₂u₃` (paper, proof of Lemma 4.3). -/
def fracDelta (t : Frac × Frac × Frac × Frac) : ℤ :=
  t.1.1 * t.2.1.2 * t.2.2.1.2 * t.2.2.2.2 + t.2.1.1 * t.1.2 * t.2.2.1.2 * t.2.2.2.2
    - t.2.2.1.1 * t.1.2 * t.2.1.2 * t.2.2.2.2 - t.2.2.2.1 * t.1.2 * t.2.1.2 * t.2.2.1.2

/-- The event "`t` is counted by `I_𝓕(q)`": numerators and denominators are units
modulo `q`, and `a₁ū₁ + a₂ū₂ ≡ a₃ū₃ + a₄ū₄ (mod q)`. -/
def FracCounted (q : ℕ) (t : Frac × Frac × Frac × Frac) : Prop :=
  (IsCoprime t.1.1 q ∧ IsCoprime t.2.1.1 q ∧ IsCoprime t.2.2.1.1 q ∧ IsCoprime t.2.2.2.1 q) ∧
  (Nat.Coprime t.1.2 q ∧ Nat.Coprime t.2.1.2 q ∧ Nat.Coprime t.2.2.1.2 q ∧
    Nat.Coprime t.2.2.2.2 q) ∧
  ((t.1.1 : ZMod q) * (t.1.2 : ZMod q)⁻¹ + (t.2.1.1 : ZMod q) * (t.2.1.2 : ZMod q)⁻¹
    = (t.2.2.1.1 : ZMod q) * (t.2.2.1.2 : ZMod q)⁻¹ + (t.2.2.2.1 : ZMod q) * (t.2.2.2.2 : ZMod q)⁻¹)

instance (q : ℕ) (t : Frac × Frac × Frac × Frac) : Decidable (FracCounted q t) := by
  unfold FracCounted
  have : ∀ a : ℤ, Decidable (IsCoprime a (q : ℤ)) := fun a => by
    rw [Int.isCoprime_iff_gcd_eq_one]; infer_instance
  infer_instance

/-- The energy `I_𝓕(q)` of a finite set of fractions modulo `q` (paper,
Lemma 4.3). -/
def fracEnergy (F : Finset Frac) (q : ℕ) : ℕ :=
  ((F ×ˢ F ×ˢ F ×ˢ F).filter (FracCounted q)).card

/-- Paper, proof of Lemma 4.3: "a counted quadruple satisfies `q ∣ Δ`". -/
theorem dvd_fracDelta {q : ℕ} {t : Frac × Frac × Frac × Frac} (h : FracCounted q t) :
    (q : ℤ) ∣ fracDelta t := by
  obtain ⟨-, ⟨c1, c2, c3, c4⟩, heq⟩ := h
  have h1 := ZMod.coe_mul_inv_eq_one _ c1
  have h2 := ZMod.coe_mul_inv_eq_one _ c2
  have h3 := ZMod.coe_mul_inv_eq_one _ c3
  have h4 := ZMod.coe_mul_inv_eq_one _ c4
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  unfold fracDelta
  push_cast
  set u1 := (t.1.2 : ZMod q)
  set u2 := (t.2.1.2 : ZMod q)
  set u3 := (t.2.2.1.2 : ZMod q)
  set u4 := (t.2.2.2.2 : ZMod q)
  set a1 := (t.1.1 : ZMod q)
  set a2 := (t.2.1.1 : ZMod q)
  set a3 := (t.2.2.1.1 : ZMod q)
  set a4 := (t.2.2.2.1 : ZMod q)
  linear_combination (u1 * u2 * u3 * u4) * heq - (a1 * u2 * u3 * u4) * h1
    - (a2 * u1 * u3 * u4) * h2 + (a3 * u1 * u2 * u4) * h3 + (a4 * u1 * u2 * u3) * h4

/-- Paper, proof of Lemma 4.3: for nonzero denominators, `Δ = 0` iff
`a₁/u₁ + a₂/u₂ = a₃/u₃ + a₄/u₄` exactly in `ℚ`. -/
theorem fracDelta_eq_zero_iff {t : Frac × Frac × Frac × Frac} (h1 : 0 < t.1.2)
    (h2 : 0 < t.2.1.2) (h3 : 0 < t.2.2.1.2) (h4 : 0 < t.2.2.2.2) :
    fracDelta t = 0 ↔
      ((t.1.1 : ℚ) / t.1.2 + t.2.1.1 / t.2.1.2 : ℚ) = t.2.2.1.1 / t.2.2.1.2 + t.2.2.2.1 / t.2.2.2.2 := by
  have e1 : (t.1.2 : ℚ) ≠ 0 := by positivity
  have e2 : (t.2.1.2 : ℚ) ≠ 0 := by positivity
  have e3 : (t.2.2.1.2 : ℚ) ≠ 0 := by positivity
  have e4 : (t.2.2.2.2 : ℚ) ≠ 0 := by positivity
  have key : ((t.1.1 : ℚ) / t.1.2 + t.2.1.1 / t.2.1.2) - (t.2.2.1.1 / t.2.2.1.2 + t.2.2.2.1 / t.2.2.2.2)
      = (fracDelta t : ℚ) / (t.1.2 * t.2.1.2 * t.2.2.1.2 * t.2.2.2.2) := by
    unfold fracDelta; push_cast; field_simp; ring
  rw [← sub_eq_zero (a := ((t.1.1 : ℚ) / t.1.2 + t.2.1.1 / t.2.1.2)), key, div_eq_zero_iff]
  have : (t.1.2 * t.2.1.2 * t.2.2.1.2 * t.2.2.2.2 : ℚ) ≠ 0 := by positivity
  simp [this]

/-- Paper, Lemma 4.3 (second claim), exact form:
`∑_{Q<q≤2Q} I_𝓕(q) ≤ Q·#{exact rational solutions} + ∑_{Δ ≠ 0} #{q ∈ (Q,2Q] : q ∣ Δ}`. -/
theorem sum_fracEnergy_le (F : Finset Frac) (Q : ℕ) :
    ∑ q ∈ Ioc Q (2 * Q), fracEnergy F q ≤
      Q * ((F ×ˢ F ×ˢ F ×ˢ F).filter (fun t => fracDelta t = 0)).card +
        ∑ t ∈ (F ×ˢ F ×ˢ F ×ˢ F).filter (fun t => fracDelta t ≠ 0),
          ((Ioc Q (2 * Q)).filter (fun q : ℕ => (q : ℤ) ∣ fracDelta t)).card :=
  sum_energy_le _ fracDelta FracCounted (fun _ _ _ h => dvd_fracDelta h) Q

/-- Paper, Lemma 4.3 with the divisor bound:
`∑_{Q<q≤2Q} I_𝓕(q) ≤ Q·#{Δ = 0} + ∑_{Δ ≠ 0} τ(|Δ|)`. -/
theorem sum_fracEnergy_le_tau (F : Finset Frac) (Q : ℕ) :
    ∑ q ∈ Ioc Q (2 * Q), fracEnergy F q ≤
      Q * ((F ×ˢ F ×ˢ F ×ˢ F).filter (fun t => fracDelta t = 0)).card +
        ∑ t ∈ (F ×ˢ F ×ˢ F ×ˢ F).filter (fun t => fracDelta t ≠ 0),
          (fracDelta t).natAbs.divisors.card :=
  sum_energy_le_tau _ fracDelta FracCounted (fun _ _ _ h => dvd_fracDelta h) Q

/-- Paper, proof of Lemma 4.3: "`0 < |Δ| ≪ U'^4`"; precisely, if `|aᵢ| ≤ M` and
`uᵢ ≤ U`, then `|Δ| ≤ 4 M U³`. -/
theorem abs_fracDelta_le {t : Frac × Frac × Frac × Frac} {M U : ℕ}
    (ha1 : |t.1.1| ≤ M) (ha2 : |t.2.1.1| ≤ M) (ha3 : |t.2.2.1.1| ≤ M) (ha4 : |t.2.2.2.1| ≤ M)
    (hu1 : t.1.2 ≤ U) (hu2 : t.2.1.2 ≤ U) (hu3 : t.2.2.1.2 ≤ U) (hu4 : t.2.2.2.2 ≤ U) :
    |fracDelta t| ≤ 4 * (M : ℤ) * (U : ℤ) ^ 3 := by
  have hU : ∀ {u : ℕ}, u ≤ U → |(u : ℤ)| ≤ U := fun h => by
    rw [abs_of_nonneg (by positivity)]; exact_mod_cast h
  have term : ∀ (a : ℤ) (u v w : ℕ), |a| ≤ M → u ≤ U → v ≤ U → w ≤ U →
      |a * u * v * w| ≤ (M : ℤ) * U ^ 3 := by
    intro a u v w ha hu hv hw
    rw [abs_mul, abs_mul, abs_mul]
    have := mul_le_mul (mul_le_mul (mul_le_mul ha (hU hu) (abs_nonneg _) (by positivity))
      (hU hv) (abs_nonneg _) (by positivity)) (hU hw) (abs_nonneg _) (by positivity)
    calc _ ≤ (M : ℤ) * U * U * U := this
      _ = (M : ℤ) * U ^ 3 := by ring
  unfold fracDelta
  have k1 := term _ _ _ _ ha1 hu2 hu3 hu4
  have k2 := term _ _ _ _ ha2 hu1 hu3 hu4
  have k3 := term _ _ _ _ ha3 hu1 hu2 hu4
  have k4 := term _ _ _ _ ha4 hu1 hu2 hu3
  calc _ ≤ |t.1.1 * t.2.1.2 * t.2.2.1.2 * t.2.2.2.2| + |t.2.1.1 * t.1.2 * t.2.2.1.2 * t.2.2.2.2|
          + |t.2.2.1.1 * t.1.2 * t.2.1.2 * t.2.2.2.2| + |t.2.2.2.1 * t.1.2 * t.2.1.2 * t.2.2.1.2| := by
        refine (abs_sub _ _).trans ?_
        refine add_le_add ((abs_sub _ _).trans ?_) le_rfl
        exact add_le_add (abs_add_le _ _) le_rfl
    _ ≤ _ := by linarith

/-! ## Representations `1/x + 1/y = a/b` -/

/-- Paper, proof of Lemma 4.1: each representation `1/x + 1/y = a/b`, written as
`b(x + y) = axy`, satisfies `(ax - b)(ay - b) = b²` (in any commutative ring). -/
theorem rep_identity {R : Type*} [CommRing R] {a b x y : R} (h : b * (x + y) = a * x * y) :
    (a * x - b) * (a * y - b) = b ^ 2 := by
  linear_combination (-a) * h

/-- Field form: if `x, y, b ≠ 0` and `1/x + 1/y = a/b` then `(ax - b)(ay - b) = b²`. -/
theorem rep_identity_field {K : Type*} [Field K] {a b x y : K} (hx : x ≠ 0) (hy : y ≠ 0)
    (hb : b ≠ 0) (h : 1 / x + 1 / y = a / b) : (a * x - b) * (a * y - b) = b ^ 2 := by
  apply rep_identity
  field_simp at h
  linear_combination h

/-- Paper, proof of Lemma 4.1: "there are at most `2τ(b²)` representations";
in fact for `a, b ≥ 1` the number of pairs of positive integers `(x, y)` with
`b(x + y) = axy` (i.e. `1/x + 1/y = a/b`) is at most `τ(b²)`, via the injection
`(x, y) ↦ ax - b ∈ {divisors of b²}`. -/
theorem card_reps_le (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    {p : ℕ × ℕ | 0 < p.1 ∧ 0 < p.2 ∧ b * (p.1 + p.2) = a * p.1 * p.2}.ncard
      ≤ (b ^ 2).divisors.card := by
  rw [← Set.ncard_coe_finset]
  -- for a solution, `ax > b`
  have key : ∀ x y : ℕ, 0 < x → 0 < y → b * (x + y) = a * x * y →
      b < a * x ∧ ((a * x - b : ℕ) : ℤ) * ((a * y - b : ℕ) : ℤ) = (b : ℤ) ^ 2 ∧ b < a * y := by
    intro x y hx hy h
    have hz : (b : ℤ) * (x + y) = a * x * y := by exact_mod_cast h
    have hax : b < a * x := by
      by_contra hc
      rw [not_lt] at hc
      have : (a : ℤ) * x ≤ b := by exact_mod_cast hc
      have hy' : (0 : ℤ) < y := by exact_mod_cast hy
      have hx' : (0 : ℤ) < x := by exact_mod_cast hx
      have hb' : (0 : ℤ) < b := by exact_mod_cast hb
      nlinarith
    have hay : b < a * y := by
      by_contra hc
      rw [not_lt] at hc
      have : (a : ℤ) * y ≤ b := by exact_mod_cast hc
      have hy' : (0 : ℤ) < y := by exact_mod_cast hy
      have hx' : (0 : ℤ) < x := by exact_mod_cast hx
      have hb' : (0 : ℤ) < b := by exact_mod_cast hb
      nlinarith
    refine ⟨hax, ?_, hay⟩
    push_cast [hax.le, hay.le]
    exact rep_identity hz
  apply Set.ncard_le_ncard_of_injOn (fun p : ℕ × ℕ => a * p.1 - b)
  · rintro ⟨x, y⟩ ⟨hx, hy, h⟩
    obtain ⟨hax, hid, hay⟩ := key x y hx hy h
    simp only [Finset.mem_coe, Nat.mem_divisors]
    refine ⟨?_, by positivity⟩
    have : ((a * x - b : ℕ) : ℤ) ∣ ((b ^ 2 : ℕ) : ℤ) := ⟨_, by push_cast; exact hid.symm⟩
    exact_mod_cast this
  · rintro ⟨x, y⟩ ⟨hx, hy, h⟩ ⟨x', y'⟩ ⟨hx', hy', h'⟩ heq
    simp only at heq
    obtain ⟨hax, hid, hay⟩ := key x y hx hy h
    obtain ⟨hax', hid', hay'⟩ := key x' y' hx' hy' h'
    have hxx : x = x' := by
      have : a * x = a * x' := by omega
      exact Nat.eq_of_mul_eq_mul_left ha this
    subst hxx
    have hne : ((a * x - b : ℕ) : ℤ) ≠ 0 := by
      have : 0 < a * x - b := by omega
      positivity
    have : ((a * y - b : ℕ) : ℤ) = ((a * y' - b : ℕ) : ℤ) :=
      mul_left_cancel₀ hne (hid.trans hid'.symm)
    have hyy : a * y = a * y' := by
      have := Int.ofNat.inj this
      omega
    rw [Nat.eq_of_mul_eq_mul_left ha hyy]

end Energy

end MobiusDeterminant
