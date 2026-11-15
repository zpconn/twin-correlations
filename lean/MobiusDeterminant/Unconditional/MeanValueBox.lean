import MobiusDeterminant.Unconditional.MeanValueIncomplete
import MobiusDeterminant.Unconditional.MeanValueArith
import MobiusDeterminant.Unconditional.MeanValueL2
import MobiusDeterminant.Unconditional.MeanValueReal

/-!
# One Heath-Brown box (paper, Theorem 6.1, Steps 2–4)

A *box* is a Dirichlet product `T = ∏_{i ∈ ι} A_i` of at most `9` sharp dyadic atoms
`A_i` supported in `[2^{κ_i}, 2^{κ_i + 1})`, each either a full indicator (an `n`-atom of
the Heath-Brown identity) or short (`2^{5κ_i} ≤ 256 D`, an `m`-atom), whose product range
meets `[D/8, 8D]`.  After Mellin separation the box contributes
```
B_e(τ) = ∑_d T(d) (d/D)^{-iτ} φ_e(d),   φ_e(d) = 𝟙_{(d,2e)=1} ∑_{|h| ≤ H} ν_h e_e(h d̄).
```
We prove `‖B(τ)‖_{ℓ²(e)} ≪ (1 + |τ|) D^{20ε} (D^{11/12}E^{1/2}H^{3/4} + D^{1/3}EH + DH)`
(`box_bound`), by the dichotomy of Step 2:
* **balanced boxes** (Step 3): a sub-product of size in `[D^{1/3}, D^{2/3}]` exists; we
  apply `BalancedBoxBound` and `phi_bound`;
* **long boxes** (Step 4): an `n`-atom of size `> D^{2/3}`; we use `longInner_bound`.
-/

open Finset Real ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace MobiusDeterminant
namespace MeanValue

/-- `φ_e(d) = 𝟙_{(d,2e)=1} ∑_{|h| ≤ H} ν_h e_e(h d̄)`. -/
noncomputable def phiE (ν : ℤ → ℂ) (Hn e d : ℕ) : ℂ :=
  if Nat.Coprime d (2 * e) then ∑ h ∈ Icc (-(Hn : ℤ)) Hn, ν h * kfrac e h d else 0

/-- The squarefree moduli `e ∈ (E/8, 8E]`. -/
noncomputable def moduli (E : ℝ) : Finset ℕ := (Ioc ⌊E / 8⌋₊ ⌊8 * E⌋₊).filter Squarefree

/-- The bound of Theorem 6.1 (without the factors `C P^k D^ε`). -/
noncomputable def target (D E : ℝ) (Hn : ℕ) : ℝ :=
  D ^ ((11 : ℝ) / 12) * E ^ ((1 : ℝ) / 2) * (Hn : ℝ) ^ ((3 : ℝ) / 4)
    + D ^ ((1 : ℝ) / 3) * E * Hn + D * Hn

/-- The contribution `∑_{d ≤ N} T(d) (d/D)^{-iτ} φ_e(d)` of one box at one `τ`. -/
noncomputable def boxSum (T : ArithmeticFunction ℂ) (N : ℕ) (D τ : ℝ) (ν : ℤ → ℂ)
    (Hn e : ℕ) : ℂ :=
  ∑ d ∈ Icc 1 N, T d * (twist τ (d / D) * phiE ν Hn e d)

/-- The standing hypotheses of Theorem 6.1, with `D ≥ 2^{78}`. -/
structure Setup where
  D : ℝ
  E : ℝ
  Hn : ℕ
  ν : ℤ → ℂ
  hD : (2 : ℝ) ^ 78 ≤ D
  hE1 : 1 ≤ E
  hED : E ≤ D
  hH1 : 1 ≤ Hn
  hHD : (Hn : ℝ) ≤ D ^ ((1 : ℝ) / 6)
  hEH : D ^ ((2 : ℝ) / 3) * (Hn : ℝ) ^ 2 ≤ E
  hν0 : ν 0 = 0
  hν : ∀ h, ‖ν h‖ ≤ 1

/-- The divisor bound `τ(n) ≤ C n^ε` (Lemma 2.1), at a fixed small exponent. -/
structure DivBound where
  ε : ℝ
  C : ℝ
  hε0 : 0 < ε
  hε1 : ε ≤ 1
  hC : 1 ≤ C
  hdiv : ∀ n : ℕ, 1 ≤ n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε

/-- A Heath-Brown box with sharp dyadic atoms. -/
structure Box (D : ℝ) (ι : Type*) [Fintype ι] where
  κ : ι → ℕ
  A : ι → ArithmeticFunction ℂ
  hcard : Fintype.card ι ≤ 9
  hsupp : ∀ i n, A i n ≠ 0 → 2 ^ κ i ≤ n ∧ n < 2 ^ (κ i + 1)
  hbdd : ∀ i n, ‖A i n‖ ≤ 1
  htype : ∀ i, (∀ n, 2 ^ κ i ≤ n → n < 2 ^ (κ i + 1) → A i n = 1) ∨
    ((2 : ℝ) ^ κ i) ^ 5 ≤ 256 * D
  hP1 : ∏ i, (2 : ℝ) ^ κ i ≤ 8 * D
  hP2 : D / 2 ^ 12 ≤ ∏ i, (2 : ℝ) ^ κ i

/-- `BalancedBoxBound` at a fixed exponent and constant. -/
def BalancedAt (ε CB : ℝ) : Prop :=
  ∀ (U₀ W₀ E : ℝ) (Hn : ℕ) (α β : ℕ → ℂ) (ν : ℤ → ℂ),
    1 ≤ U₀ → U₀ ≤ W₀ → 1 ≤ E → 1 ≤ Hn → (Hn : ℝ) ≤ U₀ →
    (∀ u, α u ≠ 0 → U₀ < u ∧ (u : ℝ) ≤ 2 ^ 9 * U₀) → (∀ u, ‖α u‖ ≤ 1) →
    (∀ w, β w ≠ 0 → W₀ < w ∧ (w : ℝ) ≤ 2 ^ 9 * W₀) → (∀ w, ‖β w‖ ≤ 1) →
    ν 0 = 0 → (∀ h, ‖ν h‖ ≤ 1) →
    ∑ e ∈ (Finset.Ioc ⌊E / 8⌋₊ ⌊8 * E⌋₊).filter Squarefree,
        ‖balForm α β ⌊2 ^ 9 * U₀⌋₊ ⌊2 ^ 9 * W₀⌋₊ ν Hn e‖ ^ 2
      ≤ (CB * (U₀ * W₀ * E) ^ ε * (U₀ * W₀ * Hn) ^ ((3 : ℝ) / 4) * E ^ ((3 : ℝ) / 8) *
          ((E + (U₀ * Hn) ^ 2) * (E + W₀ ^ 2)) ^ ((1 : ℝ) / 8)) ^ 2

lemma balancedAt_of (hB : BalancedBoxBound) {ε : ℝ} (hε : 0 < ε) :
    ∃ CB > (0 : ℝ), BalancedAt ε CB := hB ε hε

/-! ## Generalities on boxes -/

lemma twist_prod_div (τ : ℝ) {D : ℝ} (hD : 0 < D) {u w : ℕ} (hu : 1 ≤ u) (hw : 1 ≤ w) :
    twist τ (((u * w : ℕ) : ℝ) / D) =
      twist τ u * twist τ w * Complex.exp ((τ * Real.log D : ℝ) * Complex.I) := by
  have hu0 : (0 : ℝ) < u := by exact_mod_cast hu
  have hw0 : (0 : ℝ) < w := by exact_mod_cast hw
  rw [twist_div τ (by positivity) hD, Nat.cast_mul, twist_mul τ hu0 hw0]

lemma prod_two_pow_succ {ι : Type*} (S : Finset ι) (κ : ι → ℕ) :
    ∏ i ∈ S, (2 : ℕ) ^ (κ i + 1) = 2 ^ S.card * ∏ i ∈ S, 2 ^ κ i := by
  simp_rw [pow_succ]
  rw [prod_mul_distrib, prod_const, mul_comm]

variable {ι : Type*} [Fintype ι]

namespace Box

variable {D : ℝ} (B : Box D ι)

lemma supp_le (i : ι) (n : ℕ) (h : B.A i n ≠ 0) : 2 ^ B.κ i ≤ n ∧ n ≤ 2 ^ (B.κ i + 1) :=
  ⟨(B.hsupp i n h).1, (B.hsupp i n h).2.le⟩

lemma cast_prod (S : Finset ι) :
    ((∏ i ∈ S, 2 ^ B.κ i : ℕ) : ℝ) = ∏ i ∈ S, (2 : ℝ) ^ B.κ i := by push_cast; rfl

lemma total_le : ((2 ^ Fintype.card ι * ∏ i, 2 ^ B.κ i : ℕ) : ℝ) ≤ 2 ^ 12 * D := by
  push_cast
  have h9 : (2 : ℝ) ^ Fintype.card ι ≤ 2 ^ 9 := pow_le_pow_right₀ (by norm_num) B.hcard
  have hP := B.hP1
  have hP0 : 0 ≤ ∏ i, (2 : ℝ) ^ B.κ i := by positivity
  calc (2 : ℝ) ^ Fintype.card ι * ∏ i, (2 : ℝ) ^ B.κ i ≤ 2 ^ 9 * (8 * D) :=
        mul_le_mul h9 hP hP0 (by positivity)
    _ = 2 ^ 12 * D := by ring

variable [DecidableEq ι]

/-- Support of a sub-product of the atoms. -/
lemma prod_supp (S : Finset ι) (n : ℕ) (h : (∏ i ∈ S, B.A i) n ≠ 0) :
    ∏ i ∈ S, 2 ^ B.κ i ≤ n ∧ n ≤ 2 ^ S.card * ∏ i ∈ S, 2 ^ B.κ i := by
  have := prod_support B.A (fun i => 2 ^ B.κ i) (fun i => 2 ^ (B.κ i + 1)) S
    (fun i _ n hn => B.supp_le i n hn) n h
  rwa [prod_two_pow_succ] at this

omit [DecidableEq ι] in
lemma prod_hi_le (S : Finset ι) :
    2 ^ S.card * ∏ i ∈ S, 2 ^ B.κ i ≤ 2 ^ Fintype.card ι * ∏ i, 2 ^ B.κ i := by
  rw [← Finset.card_univ, ← prod_two_pow_succ, ← prod_two_pow_succ]
  exact Finset.prod_le_prod_of_subset_of_one_le (subset_univ S)
    (fun i _ _ => Nat.one_le_two_pow)

/-- The collapsed coefficients are `≤ (C 2^{12} D^ε)^9` (Lemma 2.1). -/
lemma coeff_bound (dv : DivBound) (hD : 1 ≤ D) (S : Finset ι) (u : ℕ) :
    ‖(∏ i ∈ S, B.A i) u‖ ≤ (dv.C * 2 ^ 12 * D ^ dv.ε) ^ 9 := by
  have hD0 : 0 ≤ D := by linarith
  have hbase : 1 ≤ dv.C * 2 ^ 12 * D ^ dv.ε := by
    have := Real.one_le_rpow hD dv.hε0.le
    have : (1 : ℝ) ≤ 2 ^ 12 := by norm_num
    nlinarith [dv.hC]
  by_cases hu : (∏ i ∈ S, B.A i) u = 0
  · rw [hu, norm_zero]; positivity
  obtain ⟨_, h2⟩ := B.prod_supp S u hu
  have hu1 : 1 ≤ u := by
    rcases Nat.eq_zero_or_pos u with h | h
    · exact absurd (by rw [h]; exact ArithmeticFunction.map_zero) hu
    · exact h
  have huD : (u : ℝ) ≤ 2 ^ 12 * D := by
    have := h2.trans (B.prod_hi_le S)
    have h' : (u : ℝ) ≤ ((2 ^ Fintype.card ι * ∏ i, 2 ^ B.κ i : ℕ) : ℝ) := by exact_mod_cast this
    exact h'.trans B.total_le
  have hτ : (u.divisors.card : ℝ) ≤ dv.C * 2 ^ 12 * D ^ dv.ε := by
    refine (dv.hdiv u hu1).trans ?_
    have h1 : (u : ℝ) ^ dv.ε ≤ (2 ^ 12 * D) ^ dv.ε :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) huD dv.hε0.le
    have h2 := rpow_mul_le_mul (c := 2 ^ 12) (by norm_num) hD0 dv.hε1
    calc dv.C * (u : ℝ) ^ dv.ε ≤ dv.C * (2 ^ 12 * D ^ dv.ε) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (by linarith [dv.hC])
      _ = dv.C * 2 ^ 12 * D ^ dv.ε := by ring
  have hS9 : S.card ≤ 9 := (card_le_univ S).trans B.hcard
  calc ‖(∏ i ∈ S, B.A i) u‖ ≤ (u.divisors.card : ℝ) ^ S.card := norm_prod_le B.A B.hbdd S u
    _ ≤ (dv.C * 2 ^ 12 * D ^ dv.ε) ^ S.card := pow_le_pow_left₀ (Nat.cast_nonneg _) hτ _
    _ ≤ (dv.C * 2 ^ 12 * D ^ dv.ε) ^ 9 := pow_le_pow_right₀ hbase hS9

lemma prod_hi_mul_le (S : Finset ι) {N u w : ℕ}
    (hN : 2 ^ Fintype.card ι * ∏ i, 2 ^ B.κ i ≤ N)
    (hu : u ≤ 2 ^ S.card * ∏ i ∈ S, 2 ^ B.κ i) (hw : w ≤ 2 ^ Sᶜ.card * ∏ i ∈ Sᶜ, 2 ^ B.κ i) :
    u * w ≤ N := by
  refine (Nat.mul_le_mul hu hw).trans (le_trans (le_of_eq ?_) hN)
  rw [← prod_two_pow_succ, ← prod_two_pow_succ, prod_mul_prod_compl, prod_two_pow_succ,
    card_univ]

end Box

variable [DecidableEq ι]

/-! ## Balanced boxes (paper, Theorem 6.1, Step 3) -/

lemma norm_cexp_mul_I (x : ℝ) : ‖Complex.exp ((x : ℂ) * Complex.I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I x

/-- **Balanced boxes** (paper, Theorem 6.1, Step 3): if the atoms split into two groups of
sizes `U₀ ≤ W₀`, both `≥ 2^{-12} D^{1/3}`, then `BalancedBoxBound` and `phi_bound` give
`‖B(τ)‖_{ℓ²} ≪ D^{20 ε} D^{11/12} E^{1/2} H^{3/4}`. -/
theorem balanced_bound (St : Setup) (dv : DivBound) {CB : ℝ} (hCB0 : 0 < CB)
    (hB : BalancedAt dv.ε CB)
    (B : Box St.D ι) (N : ℕ) (hN : 2 ^ Fintype.card ι * ∏ i, 2 ^ B.κ i ≤ N) (S : Finset ι)
    (hS : St.D ^ ((1 : ℝ) / 3) / 2 ^ 12 ≤ ∏ i ∈ S, (2 : ℝ) ^ B.κ i)
    (hSc : St.D ^ ((1 : ℝ) / 3) / 2 ^ 12 ≤ ∏ i ∈ Sᶜ, (2 : ℝ) ^ B.κ i)
    (hle : ∏ i ∈ S, (2 : ℝ) ^ B.κ i ≤ ∏ i ∈ Sᶜ, (2 : ℝ) ^ B.κ i) (τ : ℝ) :
    Real.sqrt (∑ e ∈ moduli St.E, ‖boxSum (∏ i, B.A i) N St.D τ St.ν St.Hn e‖ ^ 2) ≤
      (dv.C * 2 ^ 12 * St.D ^ dv.ε) ^ 18 * (2 ^ 6 * CB * St.D ^ (2 * dv.ε)) *
        (St.D ^ ((11 : ℝ) / 12) * St.E ^ ((1 : ℝ) / 2) * (St.Hn : ℝ) ^ ((3 : ℝ) / 4)) := by
  rcases St with ⟨D, E, Hn, ν, hD, hE1, hED, hH1, hHD, hEH, hν0, hν⟩
  dsimp only at *
  have hD0 : 0 < D := lt_of_lt_of_le (by positivity) hD
  have hD1 : 1 ≤ D := le_trans (by norm_num) hD
  have hthird := one_le_D_third_div hD
  set PS := ∏ i ∈ S, (2 : ℝ) ^ B.κ i with hPSdef
  set PSc := ∏ i ∈ Sᶜ, (2 : ℝ) ^ B.κ i with hPScdef
  have hPS0 : 0 < PS := by positivity
  have hPSc0 : 0 < PSc := by positivity
  have hP : PS * PSc ≤ 8 * D := by rw [hPSdef, hPScdef, prod_mul_prod_compl]; exact B.hP1
  -- both groups are nonempty, hence have at most `8` atoms
  have hne : ∀ T : Finset ι, D ^ ((1 : ℝ) / 3) / 2 ^ 12 ≤ ∏ i ∈ T, (2 : ℝ) ^ B.κ i →
      T.Nonempty := by
    intro T hT
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, prod_empty] at hT
    linarith
  have hS1 := (hne S hS).card_pos
  have hSc1 := (hne Sᶜ hSc).card_pos
  have hcompl := card_compl S
  have hcardι := B.hcard
  have hSle : S.card ≤ Fintype.card ι := card_le_univ S
  have hcS : S.card ≤ 8 := by omega
  have hcSc : Sᶜ.card ≤ 8 := by omega
  set U₀ := PS / 2 with hU₀
  set W₀ := PSc / 2 with hW₀
  set Amax := (dv.C * 2 ^ 12 * D ^ dv.ε) ^ 9 with hAmax
  have hA1 : 1 ≤ Amax := by
    have := Real.one_le_rpow hD1 dv.hε0.le
    have : 1 ≤ dv.C * 2 ^ 12 * D ^ dv.ε := by nlinarith [dv.hC]
    exact one_le_pow₀ this
  have hA0 : (0 : ℝ) < Amax := by linarith
  set α₀ := ∏ i ∈ S, B.A i with hα₀
  set β₀ := ∏ i ∈ Sᶜ, B.A i with hβ₀
  have hα₀b : ∀ u, ‖α₀ u‖ ≤ Amax := B.coeff_bound dv hD1 S
  have hβ₀b : ∀ w, ‖β₀ w‖ ≤ Amax := B.coeff_bound dv hD1 Sᶜ
  -- real supports
  have hsuppR : ∀ T : Finset ι, T.card ≤ 8 → ∀ u, (∏ i ∈ T, B.A i) u ≠ 0 →
      ∏ i ∈ T, (2 : ℝ) ^ B.κ i ≤ u ∧ (u : ℝ) ≤ 2 ^ 8 * ∏ i ∈ T, (2 : ℝ) ^ B.κ i := by
    intro T hT u hu
    obtain ⟨h1, h2⟩ := B.prod_supp T u hu
    have h1' : ((∏ i ∈ T, 2 ^ B.κ i : ℕ) : ℝ) ≤ u := by exact_mod_cast h1
    have h2' : (u : ℝ) ≤ ((2 ^ T.card * ∏ i ∈ T, 2 ^ B.κ i : ℕ) : ℝ) := by exact_mod_cast h2
    rw [B.cast_prod] at h1'
    push_cast at h2'
    refine ⟨h1', h2'.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hT) (by positivity)
  set c' := Complex.exp ((τ * Real.log D : ℝ) * Complex.I) with hc'
  set α : ℕ → ℂ := fun u => α₀ u * twist τ u / Amax with hα
  set β : ℕ → ℂ := fun w => β₀ w * twist τ w / Amax with hβ
  have hAC : (Amax : ℂ) ≠ 0 := by exact_mod_cast hA0.ne'
  have hid : ∀ e, boxSum (∏ i, B.A i) N D τ ν Hn e =
      ((Amax : ℂ) ^ 2 * c') * balForm α β ⌊2 ^ 9 * U₀⌋₊ ⌊2 ^ 9 * W₀⌋₊ ν Hn e := by
    intro e
    unfold boxSum balForm
    rw [← prod_mul_prod_compl S B.A]
    rw [sum_mul_split α₀ β₀ _ N ⌊2 ^ 9 * U₀⌋₊ ⌊2 ^ 9 * W₀⌋₊]
    · rw [mul_sum]
      refine sum_congr rfl fun u hu => ?_
      rw [mul_sum]
      refine sum_congr rfl fun w hw => ?_
      have hu1 : 1 ≤ u := (mem_Icc.1 hu).1
      have hw1 : 1 ≤ w := (mem_Icc.1 hw).1
      rw [twist_prod_div τ hD0 hu1 hw1]
      unfold phiE
      split_ifs with hc
      · simp only [hα, hβ]
        field_simp
        rw [hc']; ring
      · simp
    · intro u hu
      apply Nat.le_floor
      have := (hsuppR S hcS u hu).2
      rw [hU₀]; linarith
    · intro w hw
      apply Nat.le_floor
      have := (hsuppR Sᶜ hcSc w hw).2
      rw [hW₀]; linarith
    · intro u w hu hw
      exact B.prod_hi_mul_le S hN (B.prod_supp S u hu).2 (B.prod_supp Sᶜ w hw).2
  -- the balanced bound
  have hU1 : 1 ≤ U₀ := by rw [hU₀]; linarith
  have hHU : (Hn : ℝ) ≤ U₀ := by
    have := D_sixth_le hD
    rw [hU₀]
    have : D ^ ((1 : ℝ) / 3) / 2 ^ 13 = (D ^ ((1 : ℝ) / 3) / 2 ^ 12) / 2 := by ring
    linarith
  have hUW : U₀ ≤ W₀ := by rw [hU₀, hW₀]; linarith
  have hαsupp : ∀ u, α u ≠ 0 → U₀ < u ∧ (u : ℝ) ≤ 2 ^ 9 * U₀ := by
    intro u hu
    have hu' : α₀ u ≠ 0 := by
      intro h; apply hu; simp only [hα, h, zero_mul, zero_div]
    obtain ⟨h1, h2⟩ := hsuppR S hcS u hu'
    constructor <;> rw [hU₀] <;> linarith
  have hβsupp : ∀ w, β w ≠ 0 → W₀ < w ∧ (w : ℝ) ≤ 2 ^ 9 * W₀ := by
    intro w hw
    have hw' : β₀ w ≠ 0 := by
      intro h; apply hw; simp only [hβ, h, zero_mul, zero_div]
    obtain ⟨h1, h2⟩ := hsuppR Sᶜ hcSc w hw'
    constructor <;> rw [hW₀] <;> linarith
  have hαb : ∀ u, ‖α u‖ ≤ 1 := by
    intro u
    simp only [hα, norm_div, norm_mul, norm_twist, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hA0.le]
    rw [div_le_one hA0]; exact hα₀b u
  have hβb : ∀ w, ‖β w‖ ≤ 1 := by
    intro w
    simp only [hβ, norm_div, norm_mul, norm_twist, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hA0.le]
    rw [div_le_one hA0]; exact hβ₀b w
  have hbal := hB U₀ W₀ E Hn α β ν hU1 hUW hE1 hH1 hHU hαsupp hαb hβsupp hβb hν0 hν
  have hl2 : Real.sqrt (∑ e ∈ moduli E, ‖boxSum (∏ i, B.A i) N D τ ν Hn e‖ ^ 2) =
      Amax ^ 2 * Real.sqrt (∑ e ∈ moduli E,
        ‖balForm α β ⌊2 ^ 9 * U₀⌋₊ ⌊2 ^ 9 * W₀⌋₊ ν Hn e‖ ^ 2) := by
    simp_rw [hid]
    rw [l2_smul, norm_mul, hc', norm_cexp_mul_I, mul_one, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg hA0.le]
  rw [hl2]
  set Φ := (U₀ * W₀ * Hn) ^ ((3 : ℝ) / 4) * E ^ ((3 : ℝ) / 8) *
    ((E + (U₀ * Hn) ^ 2) * (E + W₀ ^ 2)) ^ ((1 : ℝ) / 8) with hΦ
  have hprod : U₀ * W₀ ≤ 2 * D := by
    rw [hU₀, hW₀]; nlinarith
  have hphi : Φ ≤ 2 ^ 5 * (D ^ ((11 : ℝ) / 12) * E ^ ((1 : ℝ) / 2) * (Hn : ℝ) ^ ((3 : ℝ) / 4)) :=
    phi_bound hD1 hE1 hED (by exact_mod_cast hH1) hHD hEH
      (by rw [hU₀]; have : D ^ ((1 : ℝ) / 3) / 2 ^ 13 = (D ^ ((1 : ℝ) / 3) / 2 ^ 12) / 2 := by ring
          linarith) hUW hprod
  have hΦ0 : 0 ≤ Φ := by positivity
  have hW1 : 0 < W₀ := by linarith
  have hEε : (U₀ * W₀ * E) ^ dv.ε ≤ 2 * D ^ (2 * dv.ε) := by
    have h1 : U₀ * W₀ * E ≤ 2 * D ^ 2 := by nlinarith
    calc (U₀ * W₀ * E) ^ dv.ε ≤ (2 * D ^ 2) ^ dv.ε :=
          Real.rpow_le_rpow (by positivity) h1 dv.hε0.le
      _ ≤ 2 * (D ^ 2) ^ dv.ε := rpow_mul_le_mul (by norm_num) (by positivity) dv.hε1
      _ = 2 * D ^ (2 * dv.ε) := by
          rw [← Real.rpow_natCast D 2, ← Real.rpow_mul hD0.le]; norm_num
  have hCB : 0 ≤ CB := hCB0.le
  have hsq : Real.sqrt (∑ e ∈ moduli E, ‖balForm α β ⌊2 ^ 9 * U₀⌋₊ ⌊2 ^ 9 * W₀⌋₊ ν Hn e‖ ^ 2)
      ≤ CB * (U₀ * W₀ * E) ^ dv.ε * Φ := by
    have h := Real.sqrt_le_sqrt hbal
    rw [Real.sqrt_sq (by positivity)] at h
    unfold moduli
    calc _ ≤ _ := h
      _ = CB * (U₀ * W₀ * E) ^ dv.ε * Φ := by rw [hΦ]; ring
  calc Amax ^ 2 * Real.sqrt (∑ e ∈ moduli E,
        ‖balForm α β ⌊2 ^ 9 * U₀⌋₊ ⌊2 ^ 9 * W₀⌋₊ ν Hn e‖ ^ 2)
      ≤ Amax ^ 2 * (CB * (2 * D ^ (2 * dv.ε)) *
          (2 ^ 5 * (D ^ ((11 : ℝ) / 12) * E ^ ((1 : ℝ) / 2) * (Hn : ℝ) ^ ((3 : ℝ) / 4)))) := by
        refine mul_le_mul_of_nonneg_left (hsq.trans ?_) (by positivity)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hEε hCB) hphi hΦ0 (by positivity)
    _ = (dv.C * 2 ^ 12 * D ^ dv.ε) ^ 18 * (2 ^ 6 * CB * D ^ (2 * dv.ε)) *
          (D ^ ((11 : ℝ) / 12) * E ^ ((1 : ℝ) / 2) * (Hn : ℝ) ^ ((3 : ℝ) / 4)) := by
        rw [hAmax]; ring

/-! ## Long boxes (paper, Theorem 6.1, Step 4) -/

lemma card_Icc_int (H : ℕ) : (Icc (-(H : ℤ)) H).card = 2 * H + 1 := by
  rw [Int.card_Icc]; omega

/-- Counting `k ≤ K` with bounded coefficients. -/
lemma sum_norm_le_of_supp (f : ℕ → ℂ) (N : ℕ) {K A : ℝ} (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hf : ∀ k, f k ≠ 0 → (k : ℝ) ≤ K) (hfA : ∀ k, ‖f k‖ ≤ A) :
    ∑ k ∈ Icc 1 N, ‖f k‖ ≤ K * A := by
  have h1 : ∑ k ∈ Icc 1 N, ‖f k‖ ≤ ∑ k ∈ Icc 1 N, (if (k : ℝ) ≤ K then A else 0) := by
    refine sum_le_sum fun k _ => ?_
    by_cases hk : f k = 0
    · rw [hk, norm_zero]; split_ifs <;> simp [hA]
    · rw [ite_eq_left (hf k hk)]; exact hfA k
  refine h1.trans ?_
  rw [← sum_filter, sum_const, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ hA
  have hsub : (Icc 1 N).filter (fun k : ℕ => (k : ℝ) ≤ K) ⊆ Icc 1 ⌊K⌋₊ := by
    intro k hk
    simp only [mem_filter, mem_Icc] at hk ⊢
    exact ⟨hk.1.1, Nat.le_floor hk.2⟩
  calc (((Icc 1 N).filter (fun k : ℕ => (k : ℝ) ≤ K)).card : ℝ) ≤ (Icc 1 ⌊K⌋₊).card := by
        exact_mod_cast card_le_card hsub
    _ = ⌊K⌋₊ := by rw [Nat.card_Icc]; simp
    _ ≤ K := Nat.floor_le hK

/-- The long-box identity: `B_e(τ) = ∑_k K(k) D^{iτ} k^{-iτ} ∑_h ν_h L_e(h, k)`, where `L_e` is
the inner sum over the long atom `n ∈ [s, 2s)`. -/
lemma long_identity (D : ℝ) (hD0 : 0 < D) (B : Box D ι) (N : ℕ)
    (hN : 2 ^ Fintype.card ι * ∏ i, 2 ^ B.κ i ≤ N) (i₀ : ι)
    (hζ : ∀ n, 2 ^ B.κ i₀ ≤ n → n < 2 ^ (B.κ i₀ + 1) → B.A i₀ n = 1) (τ : ℝ) (ν : ℤ → ℂ)
    (Hn e : ℕ) :
    boxSum (∏ i, B.A i) N D τ ν Hn e =
      ∑ k ∈ Icc 1 N, (∏ i ∈ ({i₀} : Finset ι)ᶜ, B.A i) k *
        (Complex.exp ((τ * Real.log D : ℝ) * Complex.I) * twist τ k *
          ∑ h ∈ Icc (-(Hn : ℤ)) Hn, ν h * longInner e h k (2 ^ B.κ i₀) (2 ^ B.κ i₀) τ) := by
  set s := 2 ^ B.κ i₀ with hs
  set K := ∏ i ∈ ({i₀} : Finset ι)ᶜ, B.A i with hK
  have hT : ∏ i, B.A i = B.A i₀ * K := by
    rw [← prod_mul_prod_compl {i₀} B.A, prod_singleton]
  have hs2 : 2 ^ (B.κ i₀ + 1) = s + s := by rw [pow_succ, hs]; ring
  -- supports
  have hn_le : ∀ n, B.A i₀ n ≠ 0 → n ≤ 2 ^ ({i₀} : Finset ι).card * ∏ i ∈ {i₀}, 2 ^ B.κ i := by
    intro n hn
    have := B.prod_supp {i₀} n (by rwa [prod_singleton])
    exact this.2
  unfold boxSum
  rw [hT, sum_mul_split (B.A i₀) K _ N N N]
  · rw [sum_comm]
    refine sum_congr rfl fun k hk => ?_
    have hk1 : 1 ≤ k := (mem_Icc.1 hk).1
    -- restrict `n` to the long interval
    have hrestrict : ∑ n ∈ Icc 1 N, B.A i₀ n * K k *
          (twist τ (((n * k : ℕ) : ℝ) / D) * phiE ν Hn e (n * k)) =
        ∑ n ∈ Ico s (s + s), K k *
          (twist τ (((n * k : ℕ) : ℝ) / D) * phiE ν Hn e (n * k)) := by
      rw [← sum_filter_add_sum_filter_not (Icc 1 N) (fun n => n ∈ Ico s (s + s))]
      have h0 : ∑ n ∈ (Icc 1 N).filter (fun n => n ∉ Ico s (s + s)), B.A i₀ n * K k *
          (twist τ (((n * k : ℕ) : ℝ) / D) * phiE ν Hn e (n * k)) = 0 := by
        refine sum_eq_zero fun n hn => ?_
        have hn' := (mem_filter.1 hn).2
        have : B.A i₀ n = 0 := by
          by_contra hc
          have := B.hsupp i₀ n hc
          rw [hs2] at this
          exact hn' (mem_Ico.2 this)
        rw [this, zero_mul, zero_mul]
      rw [h0, add_zero]
      have hfilt : (Icc 1 N).filter (fun n => n ∈ Ico s (s + s)) = Ico s (s + s) := by
        ext n
        simp only [mem_filter, mem_Icc, mem_Ico, and_iff_right_iff_imp]
        intro hn
        have h1 : 1 ≤ s := Nat.one_le_two_pow
        have h2 : s + s ≤ N := by
          have := B.prod_hi_le {i₀}
          rw [card_singleton, prod_singleton] at this
          omega
        omega
      rw [hfilt]
      refine sum_congr rfl fun n hn => ?_
      rw [hζ n (mem_Ico.1 hn).1 (by rw [hs2]; exact (mem_Ico.1 hn).2), one_mul]
    rw [hrestrict, ← mul_sum]
    congr 1
    unfold longInner
    simp_rw [mul_sum]
    conv_rhs => rw [sum_comm]
    refine sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := le_trans Nat.one_le_two_pow (mem_Ico.1 hn).1
    rw [twist_prod_div τ hD0 hn1 hk1]
    unfold phiE
    split_ifs with hc
    · rw [mul_sum]
      refine sum_congr rfl fun h _ => ?_
      ring
    · rw [mul_zero]
      symm
      refine sum_eq_zero fun h _ => ?_
      simp
  · intro n hn
    exact (hn_le n hn).trans ((B.prod_hi_le {i₀}).trans hN)
  · intro k hk
    exact ((B.prod_supp _ k hk).2.trans (B.prod_hi_le _)).trans hN
  · intro n k hn hk
    exact B.prod_hi_mul_le {i₀} hN (hn_le n hn) (B.prod_supp _ k hk).2

lemma mem_moduli {E : ℝ} (hE : 1 ≤ E) {e : ℕ} (he : e ∈ moduli E) :
    1 ≤ e ∧ Squarefree e ∧ (e : ℝ) ≤ 8 * E ∧ E / 8 < e := by
  simp only [moduli, mem_filter, mem_Ioc] at he
  obtain ⟨⟨h1, h2⟩, h3⟩ := he
  refine ⟨by omega, h3, ?_, ?_⟩
  · exact (Nat.cast_le.2 h2).trans (Nat.floor_le (by linarith))
  · have := Nat.lt_floor_add_one (E / 8)
    have h4 : ((⌊E / 8⌋₊ + 1 : ℕ) : ℝ) ≤ e := by exact_mod_cast h1
    push_cast at h4
    linarith

lemma card_moduli_le {E : ℝ} (hE : 1 ≤ E) : ((moduli E).card : ℝ) ≤ 8 * E := by
  have h1 : (moduli E).card ≤ ⌊8 * E⌋₊ := by
    unfold moduli
    refine (card_filter_le _ _).trans ?_
    rw [Nat.card_Ioc]; omega
  calc ((moduli E).card : ℝ) ≤ ⌊8 * E⌋₊ := by exact_mod_cast h1
    _ ≤ 8 * E := Nat.floor_le (by linarith)

/-- **Long boxes** (paper, Theorem 6.1, Step 4): if some `n`-atom has size `> D^{2/3}`, then
`‖B(τ)‖_{ℓ²} ≪ D^{12ε} (1 + |τ|) (D^{1/3} E H + D H^{3/2})`. -/
theorem long_bound (St : Setup) (dv : DivBound) (B : Box St.D ι) (N : ℕ)
    (hN : 2 ^ Fintype.card ι * ∏ i, 2 ^ B.κ i ≤ N) (i₀ : ι)
    (hζ : ∀ n, 2 ^ B.κ i₀ ≤ n → n < 2 ^ (B.κ i₀ + 1) → B.A i₀ n = 1)
    (hbig : St.D ^ ((2 : ℝ) / 3) < (2 : ℝ) ^ B.κ i₀) (τ : ℝ) :
    Real.sqrt (∑ e ∈ moduli St.E, ‖boxSum (∏ i, B.A i) N St.D τ St.ν St.Hn e‖ ^ 2) ≤
      (dv.C * 2 ^ 12 * St.D ^ dv.ε) ^ 9 * (2 ^ 30 * dv.C ^ 2 * (St.D ^ dv.ε) ^ 3 / dv.ε) *
        (1 + |τ|) * (St.D ^ ((1 : ℝ) / 3) * St.E * St.Hn +
          St.D * (St.Hn * Real.sqrt St.Hn)) := by
  rcases St with ⟨D, E, Hn, ν, hD, hE1, hED, hH1, hHD, hEH, hν0, hν⟩
  dsimp only at *
  have hD0 : 0 < D := lt_of_lt_of_le (by positivity) hD
  have hD1 : 1 ≤ D := le_trans (by norm_num) hD
  have hE0 : 0 < E := by linarith
  have hH1' : (1 : ℝ) ≤ Hn := by exact_mod_cast hH1
  have hε := dv.hε0
  set Lam := D ^ dv.ε with hLam
  have hLam1 : 1 ≤ Lam := Real.one_le_rpow hD1 dv.hε0.le
  set Amax := (dv.C * 2 ^ 12 * Lam) ^ 9 with hAmax
  have hA0 : 0 ≤ Amax := by have := dv.hC; positivity
  set K := ∏ i ∈ ({i₀} : Finset ι)ᶜ, B.A i with hK
  set sR : ℝ := (2 : ℝ) ^ B.κ i₀ with hsR
  have hsR0 : 0 < sR := by positivity
  set Kmax : ℝ := 2 ^ ({i₀} : Finset ι)ᶜ.card * ∏ i ∈ ({i₀} : Finset ι)ᶜ, (2 : ℝ) ^ B.κ i
    with hKmax
  have hKmax0 : 0 ≤ Kmax := by positivity
  have hKsupp : ∀ k, K k ≠ 0 → (k : ℝ) ≤ Kmax := by
    intro k hk
    have := (B.prod_supp _ k hk).2
    have h' : (k : ℝ) ≤ ((2 ^ ({i₀} : Finset ι)ᶜ.card *
        ∏ i ∈ ({i₀} : Finset ι)ᶜ, 2 ^ B.κ i : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h'
    exact h'
  have hKb : ∀ k, ‖K k‖ ≤ Amax := B.coeff_bound dv hD1 _
  -- sizes
  have hcardc : ({i₀} : Finset ι)ᶜ.card ≤ 8 := by
    rw [card_compl, card_singleton]; have := B.hcard; omega
  have hPsplit : sR * ∏ i ∈ ({i₀} : Finset ι)ᶜ, (2 : ℝ) ^ B.κ i = ∏ i, (2 : ℝ) ^ B.κ i := by
    rw [hsR, ← prod_singleton (fun i => (2 : ℝ) ^ B.κ i) i₀, prod_mul_prod_compl]
  have hKs : Kmax * sR ≤ 2 ^ 11 * D := by
    have h8 : (2 : ℝ) ^ ({i₀} : Finset ι)ᶜ.card ≤ 2 ^ 8 := pow_le_pow_right₀ (by norm_num) hcardc
    calc Kmax * sR = 2 ^ ({i₀} : Finset ι)ᶜ.card * (sR * ∏ i ∈ ({i₀} : Finset ι)ᶜ,
          (2 : ℝ) ^ B.κ i) := by rw [hKmax]; ring
      _ ≤ 2 ^ 8 * (8 * D) := by
          rw [hPsplit]; exact mul_le_mul h8 B.hP1 (by positivity) (by positivity)
      _ = 2 ^ 11 * D := by ring
  have hKm : Kmax ≤ 2 ^ 11 * D ^ ((1 : ℝ) / 3) := by
    have hDs : D = D ^ ((1 : ℝ) / 3) * D ^ ((2 : ℝ) / 3) := D_eq_third_mul hD0
    have h1 : Kmax * sR ≤ 2 ^ 11 * D ^ ((1 : ℝ) / 3) * sR := by
      calc Kmax * sR ≤ 2 ^ 11 * D := hKs
        _ = 2 ^ 11 * D ^ ((1 : ℝ) / 3) * D ^ ((2 : ℝ) / 3) := by
            conv_lhs => rw [hDs]
            ring
        _ ≤ 2 ^ 11 * D ^ ((1 : ℝ) / 3) * sR :=
            mul_le_mul_of_nonneg_left hbig.le (by positivity)
    exact le_of_mul_le_mul_right h1 hsR0
  -- the pointwise bound for each modulus
  set M : ℝ := Amax * (3 * Hn) * (128 * dv.C ^ 2 * Lam ^ 2) * (1 + 2 * |τ|) *
    (2 ^ 11 * D ^ ((1 : ℝ) / 3) * Real.sqrt (8 * E) * (9 * Lam / dv.ε) +
      2 ^ 11 * D * Real.sqrt Hn * (Real.sqrt 8 / Real.sqrt E)) with hM
  have hM0 : 0 ≤ M := by have := dv.hC; positivity
  have hpt : ∀ e ∈ moduli E, ‖boxSum (∏ i, B.A i) N D τ ν Hn e‖ ≤ M := by
    intro e he
    obtain ⟨he1, hsqe, heE, heE'⟩ := mem_moduli hE1 he
    have he0 : 0 < e := he1
    have heR : (1 : ℝ) ≤ e := by exact_mod_cast he1
    -- the inner bound, uniformly in `h`
    set LB : ℝ := ((2 * e).divisors.card : ℝ) * e.divisors.card *
      (Real.sqrt e * (1 + Real.log e) + sR * Real.sqrt Hn / Real.sqrt e) * (1 + 2 * |τ|)
      with hLB
    have hLB0 : 0 ≤ LB := by
      have := Real.log_nonneg heR; positivity
    have hinner : ∀ k, ‖∑ h ∈ Icc (-(Hn : ℤ)) Hn, ν h *
        longInner e h k (2 ^ B.κ i₀) (2 ^ B.κ i₀) τ‖ ≤ (2 * Hn + 1) * LB := by
      intro k
      refine (norm_sum_le _ _).trans ?_
      have : ∀ h ∈ Icc (-(Hn : ℤ)) Hn,
          ‖ν h * longInner e h k (2 ^ B.κ i₀) (2 ^ B.κ i₀) τ‖ ≤ LB := by
        intro h hh
        by_cases h0 : h = 0
        · rw [h0, hν0, zero_mul, norm_zero]; exact hLB0
        rw [norm_mul]
        have hl := longInner_bound he0 hsqe h0 k (2 ^ B.κ i₀) (2 ^ B.κ i₀) Nat.one_le_two_pow
          le_rfl τ
        have hhH : |(h : ℝ)| ≤ Hn := by
          have := mem_Icc.1 hh
          rw [abs_le]; constructor <;> push_cast <;> [linarith [(by exact_mod_cast this.1 :
            (-(Hn : ℝ)) ≤ h)]; exact_mod_cast this.2]
        have hl' : ‖longInner e h k (2 ^ B.κ i₀) (2 ^ B.κ i₀) τ‖ ≤ LB := by
          refine hl.trans ?_
          rw [hLB]
          push_cast
          have := Real.log_nonneg heR
          gcongr
        calc ‖ν h‖ * ‖longInner e h k (2 ^ B.κ i₀) (2 ^ B.κ i₀) τ‖ ≤ 1 * LB :=
              mul_le_mul (hν h) hl' (norm_nonneg _) zero_le_one
          _ = LB := one_mul _
      refine (sum_le_sum this).trans (le_of_eq ?_)
      rw [sum_const, card_Icc_int, nsmul_eq_mul]
      push_cast; ring
    have hbox : ‖boxSum (∏ i, B.A i) N D τ ν Hn e‖ ≤ Kmax * Amax * ((2 * Hn + 1) * LB) := by
      rw [long_identity D hD0 B N hN i₀ hζ τ ν Hn e]
      refine (norm_sum_le _ _).trans ?_
      calc ∑ k ∈ Icc 1 N, ‖K k * (Complex.exp ((τ * Real.log D : ℝ) * Complex.I) *
            twist τ k * ∑ h ∈ Icc (-(Hn : ℤ)) Hn, ν h *
              longInner e h k (2 ^ B.κ i₀) (2 ^ B.κ i₀) τ)‖
          ≤ ∑ k ∈ Icc 1 N, ‖K k‖ * ((2 * Hn + 1) * LB) := by
            refine sum_le_sum fun k _ => ?_
            rw [norm_mul, norm_mul, norm_mul, norm_cexp_mul_I, norm_twist, one_mul, one_mul]
            exact mul_le_mul_of_nonneg_left (hinner k) (norm_nonneg _)
        _ = (∑ k ∈ Icc 1 N, ‖K k‖) * ((2 * Hn + 1) * LB) := by rw [sum_mul]
        _ ≤ (Kmax * Amax) * ((2 * Hn + 1) * LB) :=
            mul_le_mul_of_nonneg_right (sum_norm_le_of_supp K N hKmax0 hA0 hKsupp hKb)
              (by positivity)
    refine hbox.trans ?_
    -- numerical bounds
    have hτ2 : ((2 * e).divisors.card : ℝ) ≤ 16 * dv.C * Lam := by
      refine (dv.hdiv (2 * e) (by omega)).trans ?_
      have h1 : ((2 * e : ℕ) : ℝ) ≤ 16 * D := by push_cast; linarith
      have h2 : ((2 * e : ℕ) : ℝ) ^ dv.ε ≤ (16 * D) ^ dv.ε :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) h1 dv.hε0.le
      have h3 := rpow_mul_le_mul (c := 16) (by norm_num) hD0.le dv.hε1
      have := dv.hC
      calc dv.C * ((2 * e : ℕ) : ℝ) ^ dv.ε ≤ dv.C * (16 * Lam) :=
            mul_le_mul_of_nonneg_left (h2.trans h3) (by linarith)
        _ = 16 * dv.C * Lam := by ring
    have hτ1 : (e.divisors.card : ℝ) ≤ 8 * dv.C * Lam := by
      refine (dv.hdiv e he1).trans ?_
      have h1 : (e : ℝ) ≤ 8 * D := by linarith
      have h2 : (e : ℝ) ^ dv.ε ≤ (8 * D) ^ dv.ε :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) h1 dv.hε0.le
      have h3 := rpow_mul_le_mul (c := 8) (by norm_num) hD0.le dv.hε1
      have := dv.hC
      calc dv.C * (e : ℝ) ^ dv.ε ≤ dv.C * (8 * Lam) :=
            mul_le_mul_of_nonneg_left (h2.trans h3) (by linarith)
        _ = 8 * dv.C * Lam := by ring
    have hlog : 1 + Real.log e ≤ 9 * Lam / dv.ε :=
      one_add_log_le heR (by linarith) hD1 dv.hε0 dv.hε1
    have hsqe8 : Real.sqrt e ≤ Real.sqrt (8 * E) := Real.sqrt_le_sqrt heE
    have hinv : 1 / Real.sqrt e ≤ Real.sqrt 8 / Real.sqrt E := by
      have hpos : 0 < Real.sqrt (E / 8) := Real.sqrt_pos.2 (by positivity)
      have h1 : Real.sqrt (E / 8) ≤ Real.sqrt e := Real.sqrt_le_sqrt heE'.le
      have h2 : 1 / Real.sqrt e ≤ 1 / Real.sqrt (E / 8) := one_div_le_one_div_of_le hpos h1
      have h3 : 1 / Real.sqrt (E / 8) = Real.sqrt 8 / Real.sqrt E := by
        rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 8), one_div_div]
      linarith
    have hpart1 : Kmax * (Real.sqrt e * (1 + Real.log e)) ≤
        2 ^ 11 * D ^ ((1 : ℝ) / 3) * Real.sqrt (8 * E) * (9 * Lam / dv.ε) := by
      have := Real.log_nonneg heR
      calc Kmax * (Real.sqrt e * (1 + Real.log e))
          ≤ (2 ^ 11 * D ^ ((1 : ℝ) / 3)) * (Real.sqrt (8 * E) * (9 * Lam / dv.ε)) := by
            gcongr
        _ = _ := by ring
    have hpart2 : Kmax * (sR * Real.sqrt Hn / Real.sqrt e) ≤
        2 ^ 11 * D * Real.sqrt Hn * (Real.sqrt 8 / Real.sqrt E) := by
      calc Kmax * (sR * Real.sqrt Hn / Real.sqrt e)
          = (Kmax * sR) * Real.sqrt Hn * (1 / Real.sqrt e) := by ring
        _ ≤ (2 ^ 11 * D) * Real.sqrt Hn * (Real.sqrt 8 / Real.sqrt E) := by
            gcongr
    have hH3 : (2 * (Hn : ℝ) + 1) ≤ 3 * Hn := by linarith
    have htotal : Kmax * ((Real.sqrt e * (1 + Real.log e) + sR * Real.sqrt Hn / Real.sqrt e)) ≤
        2 ^ 11 * D ^ ((1 : ℝ) / 3) * Real.sqrt (8 * E) * (9 * Lam / dv.ε) +
          2 ^ 11 * D * Real.sqrt Hn * (Real.sqrt 8 / Real.sqrt E) := by
      rw [mul_add]; exact add_le_add hpart1 hpart2
    have hdd : ((2 * e).divisors.card : ℝ) * e.divisors.card ≤ 128 * dv.C ^ 2 * Lam ^ 2 := by
      calc ((2 * e).divisors.card : ℝ) * e.divisors.card ≤ (16 * dv.C * Lam) * (8 * dv.C * Lam) :=
            mul_le_mul hτ2 hτ1 (Nat.cast_nonneg _) (by have := dv.hC; positivity)
        _ = 128 * dv.C ^ 2 * Lam ^ 2 := by ring
    have hτ0 : 0 ≤ 1 + 2 * |τ| := by have := abs_nonneg τ; linarith
    have hX0 : 0 ≤ Real.sqrt e * (1 + Real.log e) + sR * Real.sqrt Hn / Real.sqrt e := by
      have := Real.log_nonneg heR; positivity
    calc Kmax * Amax * ((2 * Hn + 1) * LB)
        = Amax * (2 * Hn + 1) * (((2 * e).divisors.card : ℝ) * e.divisors.card) *
            (1 + 2 * |τ|) * (Kmax * ((Real.sqrt e * (1 + Real.log e) +
              sR * Real.sqrt Hn / Real.sqrt e))) := by rw [hLB]; ring
      _ ≤ Amax * (3 * Hn) * (128 * dv.C ^ 2 * Lam ^ 2) * (1 + 2 * |τ|) *
            (2 ^ 11 * D ^ ((1 : ℝ) / 3) * Real.sqrt (8 * E) * (9 * Lam / dv.ε) +
              2 ^ 11 * D * Real.sqrt Hn * (Real.sqrt 8 / Real.sqrt E)) := by
          gcongr
      _ = M := by rw [hM]
  -- the `ℓ²` bound
  have hl2 := l2_le_card (moduli E) (fun e => boxSum (∏ i, B.A i) N D τ ν Hn e) hM0 hpt
  refine hl2.trans ?_
  have hcard : Real.sqrt (moduli E).card ≤ Real.sqrt (8 * E) :=
    Real.sqrt_le_sqrt (card_moduli_le hE1)
  have hsq8E : Real.sqrt (8 * E) * Real.sqrt (8 * E) = 8 * E := Real.mul_self_sqrt (by positivity)
  have hsq8 : Real.sqrt (8 * E) * (Real.sqrt 8 / Real.sqrt E) = 8 := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8)]
    have hE' : 0 < Real.sqrt E := Real.sqrt_pos.2 hE0
    field_simp
    rw [Real.sq_sqrt (by norm_num)]
  have hLamε : 1 ≤ 9 * Lam / dv.ε := by
    rw [le_div_iff₀ dv.hε0]; nlinarith [dv.hε1]
  calc Real.sqrt (moduli E).card * M ≤ Real.sqrt (8 * E) * M :=
        mul_le_mul_of_nonneg_right hcard hM0
    _ = Amax * (3 * Hn) * (128 * dv.C ^ 2 * Lam ^ 2) * (1 + 2 * |τ|) *
          (2 ^ 11 * D ^ ((1 : ℝ) / 3) * (Real.sqrt (8 * E) * Real.sqrt (8 * E)) *
            (9 * Lam / dv.ε) +
            2 ^ 11 * D * Real.sqrt Hn * (Real.sqrt (8 * E) * (Real.sqrt 8 / Real.sqrt E))) := by
        rw [hM]; ring
    _ = Amax * (3 * Hn) * (128 * dv.C ^ 2 * Lam ^ 2) * (1 + 2 * |τ|) * 2 ^ 14 *
          ((9 * Lam / dv.ε) * (D ^ ((1 : ℝ) / 3) * E) + D * Real.sqrt Hn) := by
        rw [hsq8E, hsq8]; ring
    _ ≤ Amax * (3 * Hn) * (128 * dv.C ^ 2 * Lam ^ 2) * (2 * (1 + |τ|)) * 2 ^ 14 *
          ((9 * Lam / dv.ε) * (D ^ ((1 : ℝ) / 3) * E) + (9 * Lam / dv.ε) * (D * Real.sqrt Hn)) := by
        have h1 : 1 + 2 * |τ| ≤ 2 * (1 + |τ|) := by linarith [abs_nonneg τ]
        have h2 : D * Real.sqrt Hn ≤ (9 * Lam / dv.ε) * (D * Real.sqrt Hn) :=
          le_mul_of_one_le_left (by positivity) hLamε
        have := dv.hC
        gcongr
    _ = Amax * (2 ^ 22 * 27 * dv.C ^ 2 * Lam ^ 3 / dv.ε) * (1 + |τ|) *
          (D ^ ((1 : ℝ) / 3) * E * Hn + D * (Hn * Real.sqrt Hn)) := by
        field_simp
        ring
    _ ≤ Amax * (2 ^ 30 * dv.C ^ 2 * Lam ^ 3 / dv.ε) * (1 + |τ|) *
          (D ^ ((1 : ℝ) / 3) * E * Hn + D * (Hn * Real.sqrt Hn)) := by
        have := dv.hC
        gcongr
        norm_num

/-! ## The dichotomy and the bound for one box (paper, Theorem 6.1, Step 2) -/

omit [Fintype ι] in
/-- **The dichotomy** (paper, Theorem 6.1, Step 2): if every atom has size `≤ a²` and the
total size is `≥ a > 1`, some sub-product has size in `[a, a²]`.  (Either one atom has size
`≥ a`, or the first partial product exceeding `a` is `< a²`.) -/
lemma exists_balanced_subset [Fintype ι] (s : ι → ℝ) (hs : ∀ i, 1 ≤ s i) {a : ℝ} (ha : 1 < a)
    (hsmall : ∀ i, s i ≤ a ^ 2) (hP : a ≤ ∏ i, s i) :
    ∃ S : Finset ι, a ≤ ∏ i ∈ S, s i ∧ ∏ i ∈ S, s i ≤ a ^ 2 := by
  by_cases h : ∃ i, a ≤ s i
  · obtain ⟨i, hi⟩ := h
    exact ⟨{i}, by rwa [prod_singleton], by rw [prod_singleton]; exact hsmall i⟩
  push Not at h
  have key : ∀ T : Finset ι, a ≤ ∏ i ∈ T, s i →
      ∃ S ⊆ T, a ≤ ∏ i ∈ S, s i ∧ ∏ i ∈ S, s i ≤ a ^ 2 := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro hT; rw [prod_empty] at hT; linarith
    | insert j T hj ih =>
      intro hT
      by_cases hT' : a ≤ ∏ i ∈ T, s i
      · obtain ⟨S, hS, h1, h2⟩ := ih hT'
        exact ⟨S, hS.trans (subset_insert _ _), h1, h2⟩
      · push Not at hT'
        refine ⟨insert j T, subset_refl _, hT, ?_⟩
        rw [prod_insert hj]
        have h0 : 0 ≤ ∏ i ∈ T, s i := prod_nonneg (fun i _ => by linarith [hs i])
        have hj0 : 0 ≤ s j := by linarith [hs j]
        nlinarith [h j]
  obtain ⟨S, -, h1, h2⟩ := key univ hP
  exact ⟨S, h1, h2⟩

/-- The constant of `box_bound`. -/
noncomputable def Cbox (dv : DivBound) (CB : ℝ) : ℝ :=
  (dv.C * 2 ^ 12) ^ 18 * 2 ^ 6 * CB + (dv.C * 2 ^ 12) ^ 9 * 2 ^ 30 * dv.C ^ 2 / dv.ε

lemma target_nonneg (D E : ℝ) (Hn : ℕ) (hD : 0 ≤ D) (hE : 0 ≤ E) : 0 ≤ target D E Hn := by
  unfold target; positivity

/-- **One box** (paper, Theorem 6.1, Steps 2–4): for every `τ`,
`‖B(τ)‖_{ℓ²(e)} ≤ C (1 + |τ|) D^{20ε} (D^{11/12}E^{1/2}H^{3/4} + D^{1/3}EH + DH)`. -/
theorem box_bound (St : Setup) (dv : DivBound) {CB : ℝ} (hCB0 : 0 < CB)
    (hB : BalancedAt dv.ε CB) (B : Box St.D ι) (N : ℕ)
    (hN : 2 ^ Fintype.card ι * ∏ i, 2 ^ B.κ i ≤ N) (τ : ℝ) :
    Real.sqrt (∑ e ∈ moduli St.E, ‖boxSum (∏ i, B.A i) N St.D τ St.ν St.Hn e‖ ^ 2) ≤
      Cbox dv CB * (1 + |τ|) * (St.D ^ dv.ε) ^ 20 * target St.D St.E St.Hn := by
  have hD0 : 0 < St.D := lt_of_lt_of_le (by positivity) St.hD
  have hD1 : 1 ≤ St.D := le_trans (by norm_num) St.hD
  have hE0 : 0 ≤ St.E := by linarith [St.hE1]
  have hLam1 : 1 ≤ St.D ^ dv.ε := Real.one_le_rpow hD1 dv.hε0.le
  have hτ1 : 1 ≤ 1 + |τ| := by linarith [abs_nonneg τ]
  have hT0 := target_nonneg St.D St.E St.Hn hD0.le hE0
  have hC := dv.hC
  have hε := dv.hε0
  have hH1 : (1 : ℝ) ≤ St.Hn := by exact_mod_cast St.hH1
  have hCbal : 0 ≤ (dv.C * 2 ^ 12) ^ 18 * 2 ^ 6 * CB := by positivity
  have hClong : 0 ≤ (dv.C * 2 ^ 12) ^ 9 * 2 ^ 30 * dv.C ^ 2 / dv.ε := by positivity
  by_cases hlong : ∃ i₀, (∀ n, 2 ^ B.κ i₀ ≤ n → n < 2 ^ (B.κ i₀ + 1) → B.A i₀ n = 1) ∧
      St.D ^ ((2 : ℝ) / 3) < (2 : ℝ) ^ B.κ i₀
  · obtain ⟨i₀, hζ, hbig⟩ := hlong
    refine (long_bound St dv B N hN i₀ hζ hbig τ).trans ?_
    have htar : St.D ^ ((1 : ℝ) / 3) * St.E * St.Hn + St.D * (St.Hn * Real.sqrt St.Hn) ≤
        target St.D St.E St.Hn := by
      have := long_target hD1 hH1 St.hEH
      unfold target
      have : 0 ≤ St.D ^ ((1 : ℝ) / 3) * St.E * St.Hn := by positivity
      have : 0 ≤ St.D * (St.Hn : ℝ) := by positivity
      linarith
    have hpow : (St.D ^ dv.ε) ^ 12 ≤ (St.D ^ dv.ε) ^ 20 := pow_le_pow_right₀ hLam1 (by norm_num)
    calc (dv.C * 2 ^ 12 * St.D ^ dv.ε) ^ 9 * (2 ^ 30 * dv.C ^ 2 * (St.D ^ dv.ε) ^ 3 / dv.ε) *
          (1 + |τ|) * (St.D ^ ((1 : ℝ) / 3) * St.E * St.Hn + St.D * (St.Hn * Real.sqrt St.Hn))
        = ((dv.C * 2 ^ 12) ^ 9 * 2 ^ 30 * dv.C ^ 2 / dv.ε) * (1 + |τ|) * (St.D ^ dv.ε) ^ 12 *
            (St.D ^ ((1 : ℝ) / 3) * St.E * St.Hn + St.D * (St.Hn * Real.sqrt St.Hn)) := by ring
      _ ≤ ((dv.C * 2 ^ 12) ^ 9 * 2 ^ 30 * dv.C ^ 2 / dv.ε) * (1 + |τ|) * (St.D ^ dv.ε) ^ 20 *
            target St.D St.E St.Hn := by gcongr
      _ ≤ Cbox dv CB * (1 + |τ|) * (St.D ^ dv.ε) ^ 20 * target St.D St.E St.Hn := by
          unfold Cbox; gcongr; linarith
  push Not at hlong
  have hsmall : ∀ i, (2 : ℝ) ^ B.κ i ≤ St.D ^ ((2 : ℝ) / 3) := by
    intro i
    rcases B.htype i with h | h
    · exact hlong i h
    · exact le_twothirds_of_pow_five St.hD h
  have ha : 1 < St.D ^ ((1 : ℝ) / 3) := by
    have := one_le_D_third_div St.hD
    have : St.D ^ ((1 : ℝ) / 3) = 2 ^ 12 * (St.D ^ ((1 : ℝ) / 3) / 2 ^ 12) := by ring
    linarith
  have hP : St.D ^ ((1 : ℝ) / 3) ≤ ∏ i, (2 : ℝ) ^ B.κ i :=
    (D_third_le_div St.hD).trans B.hP2
  obtain ⟨S, hS1, hS2⟩ := exists_balanced_subset (fun i => (2 : ℝ) ^ B.κ i)
    (fun i => one_le_pow₀ one_le_two) ha (by rwa [← D_twothirds_eq hD0]) hP
  have hthird := one_le_D_third_div St.hD
  have hlow : St.D ^ ((1 : ℝ) / 3) / 2 ^ 12 ≤ ∏ i ∈ S, (2 : ℝ) ^ B.κ i := by
    have : St.D ^ ((1 : ℝ) / 3) / 2 ^ 12 ≤ St.D ^ ((1 : ℝ) / 3) := by
      apply div_le_self (by positivity) (by norm_num)
    linarith
  have hlowc : St.D ^ ((1 : ℝ) / 3) / 2 ^ 12 ≤ ∏ i ∈ Sᶜ, (2 : ℝ) ^ B.κ i := by
    have hsplit := prod_mul_prod_compl S (fun i => (2 : ℝ) ^ B.κ i)
    have h1 : St.D / 2 ^ 12 ≤ (∏ i ∈ S, (2 : ℝ) ^ B.κ i) * ∏ i ∈ Sᶜ, (2 : ℝ) ^ B.κ i := by
      rw [hsplit]; exact B.hP2
    have h2 : (∏ i ∈ S, (2 : ℝ) ^ B.κ i) * ∏ i ∈ Sᶜ, (2 : ℝ) ^ B.κ i ≤
        St.D ^ ((2 : ℝ) / 3) * ∏ i ∈ Sᶜ, (2 : ℝ) ^ B.κ i :=
      mul_le_mul_of_nonneg_right (by rw [D_twothirds_eq hD0]; exact hS2) (by positivity)
    have hDs := D_eq_third_mul hD0
    have h3 : St.D ^ ((2 : ℝ) / 3) * (St.D ^ ((1 : ℝ) / 3) / 2 ^ 12) ≤
        St.D ^ ((2 : ℝ) / 3) * ∏ i ∈ Sᶜ, (2 : ℝ) ^ B.κ i := by
      have : St.D ^ ((2 : ℝ) / 3) * (St.D ^ ((1 : ℝ) / 3) / 2 ^ 12) = St.D / 2 ^ 12 := by
        conv_rhs => rw [hDs]
        ring
      rw [this]; linarith
    exact le_of_mul_le_mul_left h3 (by positivity)
  have hbal_to_target : ∀ X : ℝ, X ≤ (dv.C * 2 ^ 12 * St.D ^ dv.ε) ^ 18 *
        (2 ^ 6 * CB * St.D ^ (2 * dv.ε)) *
        (St.D ^ ((11 : ℝ) / 12) * St.E ^ ((1 : ℝ) / 2) * (St.Hn : ℝ) ^ ((3 : ℝ) / 4)) →
      X ≤ Cbox dv CB * (1 + |τ|) * (St.D ^ dv.ε) ^ 20 * target St.D St.E St.Hn := by
    intro X hX
    refine hX.trans ?_
    have h2ε : St.D ^ (2 * dv.ε) = (St.D ^ dv.ε) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hD0.le]; ring_nf
    have htar : St.D ^ ((11 : ℝ) / 12) * St.E ^ ((1 : ℝ) / 2) * (St.Hn : ℝ) ^ ((3 : ℝ) / 4) ≤
        target St.D St.E St.Hn := by
      unfold target
      have : 0 ≤ St.D ^ ((1 : ℝ) / 3) * St.E * St.Hn := by positivity
      have : 0 ≤ St.D * (St.Hn : ℝ) := by positivity
      linarith
    rw [h2ε]
    calc (dv.C * 2 ^ 12 * St.D ^ dv.ε) ^ 18 * (2 ^ 6 * CB * (St.D ^ dv.ε) ^ 2) *
          (St.D ^ ((11 : ℝ) / 12) * St.E ^ ((1 : ℝ) / 2) * (St.Hn : ℝ) ^ ((3 : ℝ) / 4))
        = ((dv.C * 2 ^ 12) ^ 18 * 2 ^ 6 * CB) * 1 * (St.D ^ dv.ε) ^ 20 *
            (St.D ^ ((11 : ℝ) / 12) * St.E ^ ((1 : ℝ) / 2) * (St.Hn : ℝ) ^ ((3 : ℝ) / 4)) := by
          ring
      _ ≤ Cbox dv CB * (1 + |τ|) * (St.D ^ dv.ε) ^ 20 * target St.D St.E St.Hn := by
          unfold Cbox; gcongr; linarith
  by_cases hle : ∏ i ∈ S, (2 : ℝ) ^ B.κ i ≤ ∏ i ∈ Sᶜ, (2 : ℝ) ^ B.κ i
  · exact hbal_to_target _ (balanced_bound St dv hCB0 hB B N hN S hlow hlowc hle τ)
  · push Not at hle
    have hlow' : St.D ^ ((1 : ℝ) / 3) / 2 ^ 12 ≤ ∏ i ∈ Sᶜᶜ, (2 : ℝ) ^ B.κ i := by
      rwa [compl_compl]
    have hle' : ∏ i ∈ Sᶜ, (2 : ℝ) ^ B.κ i ≤ ∏ i ∈ Sᶜᶜ, (2 : ℝ) ^ B.κ i := by
      rw [compl_compl]; exact hle.le
    exact hbal_to_target _ (balanced_bound St dv hCB0 hB B N hN Sᶜ hlowc hlow' hle' τ)

end MeanValue
end MobiusDeterminant
