import Mathlib

/-!
# A bilinear inequality of Korolev–Changa type (paper, Lemma 3.1)

For a finite *labelled* family `𝒴` of units modulo `q` (residues may repeat) the paper
puts
`I(q;𝒴) = #{(y₁,y₂,y₃,y₄) ∈ 𝒴⁴ : ȳ₁ + ȳ₂ ≡ ȳ₃ + ȳ₄ (mod q)}`
and proves (Lemma 3.1)
`|∑_{z ∈ 𝒵} ∑_{w ∈ 𝒴} γ_z β_w e_q(c z̄ w̄)| ≤ ‖γ‖₂ ‖β‖₂ {q I(q;𝒵) I(q;𝒴)}^{1/8}`.

We formalize the equivalent eighth-power form
`|ℬ|⁸ ≤ ‖γ‖₂⁸ ‖β‖₂⁸ · q · I(q;𝒵) · I(q;𝒴)`
for an arbitrary primitive additive character `ψ : AddChar (ZMod q) ℂ` (for instance
`ZMod.stdAddChar`, i.e. `e_q`).  Labelled families are maps from finite index types.

The general statement `bilinear_pow_eight_le` is phrased for arbitrary residues
`a i`, `b k` (playing the role of `z̄`, `w̄`); `korolevChanga` specializes it to families of
units and their inverses, and `korolevChanga_rpow` gives the paper's `^{1/8}` form.

The proof follows the paper: Cauchy–Schwarz over `z`; expansion of `∑_z |S(z)|²` as
`∑_{w₁,w₂} β̄_{w₁} β_{w₂} G(w̄₂ - w̄₁)` (we use `S·S̄` instead of `ρ_z S(z)²`, which gives
differences instead of sums; the resulting count is the same energy); Cauchy–Schwarz over
`(w₁,w₂)` and over `λ`; and orthogonality, which gives `∑_λ |G(λ)|⁴ = q · I(q;𝒵)` exactly.
-/

open Finset ComplexConjugate

namespace MobiusDeterminant
namespace KorolevChanga

variable {q : ℕ} [NeZero q]

/-- Additive energy of a labelled family `a : ι → ZMod q`:
`#{(i₁,i₂,i₃,i₄) : a i₁ + a i₂ = a i₃ + a i₄}`. -/
def energy {ι : Type*} [Fintype ι] (a : ι → ZMod q) : ℕ :=
  (univ.filter (fun t : ι × ι × ι × ι => a t.1 + a t.2.1 = a t.2.2.1 + a t.2.2.2)).card

/-- The paper's `I(q;𝒴)` for a labelled family of units `y : ι → (ZMod q)ˣ`:
the additive energy of the inverses `ȳ`. -/
def invEnergy {ι : Type*} [Fintype ι] (y : ι → (ZMod q)ˣ) : ℕ :=
  energy (fun i => (((y i)⁻¹ : (ZMod q)ˣ) : ZMod q))

omit [NeZero q] in
lemma energy_eq_sum {R : Type*} [AddCommMonoidWithOne R] {ι : Type*} [Fintype ι]
    (a : ι → ZMod q) :
    (energy a : R) = ∑ t : ι × ι × ι × ι,
      if a t.1 + a t.2.1 = a t.2.2.1 + a t.2.2.2 then (1 : R) else 0 := by
  unfold energy
  rw [Finset.natCast_card_filter]

/-- The exponential sum `G(λ) = ∑_z e_q(c λ z̄)` of the proof of Lemma 3.1 (with `ρ_z = 1`). -/
noncomputable def G (ψ : AddChar (ZMod q) ℂ) {ι : Type*} [Fintype ι] (c : ZMod q)
    (a : ι → ZMod q) (l : ZMod q) : ℂ :=
  ∑ i, ψ (l * (c * a i))

variable (ψ : AddChar (ZMod q) ℂ)

lemma normSq_G_eq {ι : Type*} [Fintype ι] (c : ZMod q) (a : ι → ZMod q) (l : ZMod q) :
    (((‖G ψ c a l‖ ^ 2 : ℝ)) : ℂ) = ∑ p : ι × ι, ψ (l * (c * (a p.1 - a p.2))) := by
  have h : (((‖G ψ c a l‖ ^ 2 : ℝ)) : ℂ) = G ψ c a l * conj (G ψ c a l) := by
    rw [Complex.mul_conj']; push_cast; ring
  rw [h, G, map_sum, Finset.sum_mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
  rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]
  dsimp only
  congr 1; ring

/-- Fourth moment of `G`: by orthogonality, `∑_λ |G(λ)|⁴ = q · I(q;𝒵)` (paper, proof of
Lemma 3.1). -/
theorem sum_norm_G_pow_four (hψ : ψ.IsPrimitive) {ι : Type*} [Fintype ι] (c : ZMod q)
    (hc : IsUnit c) (a : ι → ZMod q) :
    ∑ l, ‖G ψ c a l‖ ^ 4 = (q : ℝ) * energy a := by
  apply Complex.ofReal_injective
  have h1 : ∀ l, (((‖G ψ c a l‖ ^ 4 : ℝ)) : ℂ) = ∑ p : ι × ι, ∑ p' : ι × ι,
      ψ (l * (c * (a p.1 - a p.2 + (a p'.1 - a p'.2)))) := by
    intro l
    have : (‖G ψ c a l‖ ^ 4 : ℝ) = (‖G ψ c a l‖ ^ 2) ^ 2 := by ring
    rw [this, Complex.ofReal_pow, normSq_G_eq, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun p' _ => ?_))
    rw [← AddChar.map_add_eq_mul]
    congr 1; ring
  push_cast
  simp_rw [← Complex.ofReal_pow]
  rw [Finset.sum_congr rfl (fun l _ => h1 l)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun p _ => Finset.sum_comm)]
  simp_rw [AddChar.sum_mulShift _ hψ, ZMod.card, Nat.cast_ite, Nat.cast_zero]
  rw [energy_eq_sum (R := ℂ)]
  rw [Finset.mul_sum, ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv
    { toFun := fun x => (x.1.1, x.2.1, x.1.2, x.2.2)
      invFun := fun t => ((t.1, t.2.2.1), (t.2.1, t.2.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl } _ _ (fun x => ?_)
  simp only [Equiv.coe_fn_mk]
  have hiff : c * (a x.1.1 - a x.1.2 + (a x.2.1 - a x.2.2)) = 0 ↔
      a x.1.1 + a x.2.1 = a x.1.2 + a x.2.2 := by
    rw [hc.mul_right_eq_zero]
    constructor <;> intro h <;> linear_combination h
  by_cases h : a x.1.1 + a x.2.1 = a x.1.2 + a x.2.2
  · simp [hiff, h]
  · simp [hiff, h]

omit [NeZero q] in
/-- Fibre decomposition: `∑_{(k₁,k₂)} f(b k₂ - b k₁) = ∑_λ j(λ) f(λ)` where
`j(λ) = #{(k₁,k₂) : b k₂ - b k₁ = λ}`. -/
lemma sum_comp_diff [Fintype (ZMod q)] {κ : Type*} [Fintype κ] (b : κ → ZMod q)
    (f : ZMod q → ℝ) :
    ∑ p : κ × κ, f (b p.2 - b p.1) =
      ∑ l, (∑ p : κ × κ, if b p.2 - b p.1 = l then (1 : ℝ) else 0) * f l := by
  simp_rw [Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

omit [NeZero q] in
/-- `∑_λ j(λ)² = I(q;𝒴)`, with `j(λ) = #{(k₁,k₂) : b k₂ - b k₁ = λ}` (differences instead of
sums; the count is the same energy). -/
lemma sum_fiber_sq [Fintype (ZMod q)] {κ : Type*} [Fintype κ] (b : κ → ZMod q) :
    ∑ l, (∑ p : κ × κ, if b p.2 - b p.1 = l then (1 : ℝ) else 0) ^ 2 = energy b := by
  set j : ZMod q → ℝ := fun l => ∑ p : κ × κ, if b p.2 - b p.1 = l then (1 : ℝ) else 0
    with hj
  have : ∑ l, j l ^ 2 = ∑ p : κ × κ, j (b p.2 - b p.1) := by
    rw [sum_comp_diff b j]; simp_rw [sq]; rfl
  rw [this, energy_eq_sum (R := ℝ), hj, ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv
    { toFun := fun x => (x.1.2, x.2.1, x.2.2, x.1.1)
      invFun := fun t => ((t.2.2.2, t.1), (t.2.1, t.2.2.1))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl } _ _ (fun x => ?_)
  simp only [Equiv.coe_fn_mk]
  have hiff : b x.2.2 - b x.2.1 = b x.1.2 - b x.1.1 ↔
      b x.1.2 + b x.2.1 = b x.2.2 + b x.1.1 := by
    constructor <;> intro h <;> linear_combination -h
  by_cases h : b x.1.2 + b x.2.1 = b x.2.2 + b x.1.1
  · simp [hiff, h]
  · simp [hiff, h]

/-- **Lemma 3.1 (Korolev–Changa type bilinear inequality), general residues.**
For a primitive additive character `ψ` of `ZMod q`, a unit `c`, finite labelled families of
residues `a i` (the `z̄`) and `b k` (the `w̄`) and complex coefficients `γ`, `β`:
`|∑_i ∑_k γ_i β_k ψ(c a_i b_k)|⁸ ≤ ‖γ‖₂⁸ ‖β‖₂⁸ · q · E(a) · E(b)`,
where `E` is the additive energy `#{x₁ + x₂ = x₃ + x₄}`. -/
theorem bilinear_pow_eight_le (hψ : ψ.IsPrimitive) {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ZMod q) (hc : IsUnit c) (a : ι → ZMod q) (b : κ → ZMod q) (γ : ι → ℂ) (β : κ → ℂ) :
    ‖∑ i, ∑ k, γ i * β k * ψ (c * a i * b k)‖ ^ 8 ≤
      (∑ i, ‖γ i‖ ^ 2) ^ 4 * (∑ k, ‖β k‖ ^ 2) ^ 4 * (q : ℝ) * energy a * energy b := by
  set S : ι → ℂ := fun i => ∑ k, β k * ψ (c * a i * b k) with hS
  set Γ : ℝ := ∑ i, ‖γ i‖ ^ 2 with hΓ
  set Bt : ℝ := ∑ k, ‖β k‖ ^ 2 with hBt
  set P : ℝ := ∑ i, ‖S i‖ ^ 2 with hP
  set R : ℝ := ∑ p : κ × κ, ‖G ψ c a (b p.2 - b p.1)‖ ^ 2 with hR
  have hΓ0 : 0 ≤ Γ := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hBt0 : 0 ≤ Bt := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hP0 : 0 ≤ P := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hR0 : 0 ≤ R := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  -- Step 1: Cauchy–Schwarz over `z`.
  have h1 : ‖∑ i, ∑ k, γ i * β k * ψ (c * a i * b k)‖ ^ 2 ≤ Γ * P := by
    have e : ∑ i, ∑ k, γ i * β k * ψ (c * a i * b k) = ∑ i, γ i * S i := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hS, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring
    rw [e]
    calc ‖∑ i, γ i * S i‖ ^ 2 ≤ (∑ i, ‖γ i‖ * ‖S i‖) ^ 2 := by
          gcongr
          refine (norm_sum_le _ _).trans (le_of_eq ?_)
          simp
      _ ≤ Γ * P := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  -- Step 2: expand `∑_z |S(z)|²` and apply Cauchy–Schwarz over `(w₁,w₂)`.
  have h2 : P ^ 2 ≤ Bt ^ 2 * R := by
    have e : ((P : ℝ) : ℂ) = ∑ p : κ × κ, β p.2 * conj (β p.1) * G ψ c a (b p.2 - b p.1) := by
      have e1 : ∀ i, (((‖S i‖ ^ 2 : ℝ)) : ℂ) = ∑ p : κ × κ,
          β p.2 * conj (β p.1) * ψ ((b p.2 - b p.1) * (c * a i)) := by
        intro i
        have : (((‖S i‖ ^ 2 : ℝ)) : ℂ) = S i * conj (S i) := by
          rw [Complex.mul_conj']; push_cast; ring
        rw [this, hS, map_sum, Finset.sum_mul_sum, Fintype.sum_prod_type,
          Finset.sum_comm]
        refine Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun k2 _ => ?_))
        dsimp only
        rw [(starRingEnd ℂ).map_mul, ← AddChar.map_neg_eq_conj]
        have : ψ (c * a i * b k2) * ψ (-(c * a i * b k1)) =
            ψ ((b k2 - b k1) * (c * a i)) := by
          rw [← AddChar.map_add_eq_mul]; congr 1; ring
        rw [← this]; ring
      rw [hP]; push_cast
      simp_rw [← Complex.ofReal_pow]
      rw [Finset.sum_congr rfl (fun i _ => e1 i), Finset.sum_comm]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [G, Finset.mul_sum]
    have hle : P ≤ ∑ p : κ × κ, (‖β p.1‖ * ‖β p.2‖) * ‖G ψ c a (b p.2 - b p.1)‖ := by
      have : P = ‖((P : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_of_nonneg hP0]
      rw [this, e]
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl (fun p _ => ?_)
      simp only [Complex.norm_conj, norm_mul]; ring
    calc P ^ 2 ≤ (∑ p : κ × κ, (‖β p.1‖ * ‖β p.2‖) * ‖G ψ c a (b p.2 - b p.1)‖) ^ 2 := by
          gcongr
      _ ≤ (∑ p : κ × κ, (‖β p.1‖ * ‖β p.2‖) ^ 2) * R :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = Bt ^ 2 * R := by
          congr 1
          rw [hBt, sq, Finset.sum_mul_sum, Fintype.sum_prod_type]
          refine Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun k2 _ => ?_))
          dsimp only; ring
  -- Step 3: Cauchy–Schwarz over `λ` and orthogonality.
  have h3 : R ^ 2 ≤ (energy b : ℝ) * ((q : ℝ) * energy a) := by
    rw [hR, sum_comp_diff b (fun l => ‖G ψ c a l‖ ^ 2)]
    calc (∑ l, (∑ p : κ × κ, if b p.2 - b p.1 = l then (1 : ℝ) else 0) *
            ‖G ψ c a l‖ ^ 2) ^ 2
        ≤ (∑ l, (∑ p : κ × κ, if b p.2 - b p.1 = l then (1 : ℝ) else 0) ^ 2) *
            ∑ l, (‖G ψ c a l‖ ^ 2) ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = (energy b : ℝ) * ((q : ℝ) * energy a) := by
          rw [sum_fiber_sq, ← sum_norm_G_pow_four ψ hψ c hc a]
          congr 1
          refine Finset.sum_congr rfl (fun l _ => ?_)
          ring
  -- Assembly.
  calc ‖∑ i, ∑ k, γ i * β k * ψ (c * a i * b k)‖ ^ 8
      = (‖∑ i, ∑ k, γ i * β k * ψ (c * a i * b k)‖ ^ 2) ^ 4 := by ring
    _ ≤ (Γ * P) ^ 4 := by gcongr
    _ = Γ ^ 4 * (P ^ 2) ^ 2 := by ring
    _ ≤ Γ ^ 4 * (Bt ^ 2 * R) ^ 2 := by gcongr
    _ = Γ ^ 4 * Bt ^ 4 * R ^ 2 := by ring
    _ ≤ Γ ^ 4 * Bt ^ 4 * ((energy b : ℝ) * ((q : ℝ) * energy a)) := by gcongr
    _ = Γ ^ 4 * Bt ^ 4 * (q : ℝ) * energy a * energy b := by ring

/-- **Lemma 3.1 (paper), eighth-power form.**  Let `ψ` be a primitive additive character of
`ZMod q` (e.g. `e_q`), `c` a unit, and `z : ι → (ZMod q)ˣ`, `w : κ → (ZMod q)ˣ` finite
labelled families of units with complex coefficients `γ`, `β`.  Then
`|∑_z ∑_w γ_z β_w ψ(c z̄ w̄)|⁸ ≤ ‖γ‖₂⁸ ‖β‖₂⁸ · q · I(q;𝒵) · I(q;𝒴)`. -/
theorem korolevChanga (hψ : ψ.IsPrimitive) {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : (ZMod q)ˣ) (z : ι → (ZMod q)ˣ) (w : κ → (ZMod q)ˣ) (γ : ι → ℂ) (β : κ → ℂ) :
    ‖∑ i, ∑ k, γ i * β k *
        ψ ((c : ZMod q) * (((z i)⁻¹ : (ZMod q)ˣ) : ZMod q) * (((w k)⁻¹ : (ZMod q)ˣ) : ZMod q))‖ ^ 8
      ≤ (∑ i, ‖γ i‖ ^ 2) ^ 4 * (∑ k, ‖β k‖ ^ 2) ^ 4 * (q : ℝ) * invEnergy z * invEnergy w :=
  bilinear_pow_eight_le ψ hψ (c : ZMod q) c.isUnit _ _ γ β

/-- **Lemma 3.1 (paper), as stated:**
`|∑_z ∑_w γ_z β_w ψ(c z̄ w̄)| ≤ ‖γ‖₂ ‖β‖₂ {q I(q;𝒵) I(q;𝒴)}^{1/8}`. -/
theorem korolevChanga_rpow (hψ : ψ.IsPrimitive) {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : (ZMod q)ˣ) (z : ι → (ZMod q)ˣ) (w : κ → (ZMod q)ˣ) (γ : ι → ℂ) (β : κ → ℂ) :
    ‖∑ i, ∑ k, γ i * β k *
        ψ ((c : ZMod q) * (((z i)⁻¹ : (ZMod q)ˣ) : ZMod q) * (((w k)⁻¹ : (ZMod q)ˣ) : ZMod q))‖
      ≤ Real.sqrt (∑ i, ‖γ i‖ ^ 2) * Real.sqrt (∑ k, ‖β k‖ ^ 2) *
          ((q : ℝ) * invEnergy z * invEnergy w) ^ (1 / 8 : ℝ) := by
  have hΓ : 0 ≤ ∑ i, ‖γ i‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hB : 0 ≤ ∑ k, ‖β k‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hX : 0 ≤ (q : ℝ) * invEnergy z * invEnergy w := by positivity
  refine le_of_pow_le_pow_left₀ (n := 8) (by norm_num) (by positivity) ?_
  have h8 : (((q : ℝ) * invEnergy z * invEnergy w) ^ (1 / 8 : ℝ)) ^ 8 =
      (q : ℝ) * invEnergy z * invEnergy w := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX]; norm_num
  have hs : ∀ t : ℝ, 0 ≤ t → Real.sqrt t ^ 8 = t ^ 4 := by
    intro t ht
    rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, Real.sq_sqrt ht]
  rw [mul_pow, mul_pow, h8, hs _ hΓ, hs _ hB]
  calc _ ≤ _ := korolevChanga ψ hψ c z w γ β
    _ = _ := by ring

/-- Lemma 3.1 for the standard character `e_q = ZMod.stdAddChar`. -/
theorem korolevChanga_std {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : (ZMod q)ˣ) (z : ι → (ZMod q)ˣ) (w : κ → (ZMod q)ˣ) (γ : ι → ℂ) (β : κ → ℂ) :
    ‖∑ i, ∑ k, γ i * β k * ZMod.stdAddChar
        ((c : ZMod q) * (((z i)⁻¹ : (ZMod q)ˣ) : ZMod q) * (((w k)⁻¹ : (ZMod q)ˣ) : ZMod q))‖
      ≤ Real.sqrt (∑ i, ‖γ i‖ ^ 2) * Real.sqrt (∑ k, ‖β k‖ ^ 2) *
          ((q : ℝ) * invEnergy z * invEnergy w) ^ (1 / 8 : ℝ) :=
  korolevChanga_rpow _ (ZMod.isPrimitive_stdAddChar q) c z w γ β

end KorolevChanga
end MobiusDeterminant
