import MobiusDeterminant.Core.HeathBrown

/-!
# Arithmetic-function bookkeeping for the mean-value theorem (paper, Theorem 6.1, Step 2)

* sharp dyadic pieces `dy f k = f · 𝟙_{[2^k, 2^{k+1})}`;
* supports and sizes of Dirichlet products of dyadic atoms;
* the trivial bound `|(f₁ ⋯ f_s)(n)| ≤ τ(n)^s` for atoms bounded by `1`
  (the collapsed coefficients of Step 3);
* the regrouping identity `∑_d (f * g)(d) ψ(d) = ∑_{u,w} f(u) g(w) ψ(uw)`;
* the Heath-Brown identity (Lemma 2.6, `J = 5`) over `ℂ`, expanded into sharp dyadic boxes.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace MobiusDeterminant
namespace MeanValue

lemma af_sum_apply {ι : Type*} (s : Finset ι) (f : ι → ArithmeticFunction ℂ) (n : ℕ) :
    (∑ i ∈ s, f i) n = ∑ i ∈ s, f i n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, ArithmeticFunction.add_apply, ih]

/-! ## Sharp dyadic pieces -/

/-- The sharp dyadic piece `f · 𝟙_{[2^k, 2^{k+1})}`. -/
noncomputable def dy (f : ArithmeticFunction ℂ) (k : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n ≠ 0 ∧ Nat.log 2 n = k then f n else 0, by simp⟩

lemma dy_apply (f : ArithmeticFunction ℂ) (k n : ℕ) :
    dy f k n = if n ≠ 0 ∧ Nat.log 2 n = k then f n else 0 := rfl

lemma mem_dyadic_iff {k n : ℕ} : (n ≠ 0 ∧ Nat.log 2 n = k) ↔ (2 ^ k ≤ n ∧ n < 2 ^ (k + 1)) := by
  constructor
  · rintro ⟨hn, rfl⟩
    exact ⟨Nat.pow_log_le_self 2 hn, Nat.lt_pow_succ_log_self (by norm_num) n⟩
  · rintro ⟨h1, h2⟩
    have hn : n ≠ 0 := by have := Nat.one_le_two_pow (n := k); omega
    exact ⟨hn, (Nat.log_eq_iff (Or.inr ⟨by norm_num, hn⟩)).2 ⟨h1, h2⟩⟩

lemma dy_supp {f : ArithmeticFunction ℂ} {k n : ℕ} (h : dy f k n ≠ 0) :
    2 ^ k ≤ n ∧ n < 2 ^ (k + 1) := by
  rw [dy_apply] at h
  by_cases hc : n ≠ 0 ∧ Nat.log 2 n = k
  · exact mem_dyadic_iff.1 hc
  · exact absurd (ite_eq_right hc) h

lemma dy_eq_of_mem {f : ArithmeticFunction ℂ} {k n : ℕ} (h1 : 2 ^ k ≤ n) (h2 : n < 2 ^ (k + 1)) :
    dy f k n = f n := by
  rw [dy_apply, ite_eq_left (mem_dyadic_iff.2 ⟨h1, h2⟩)]

lemma norm_dy_le {f : ArithmeticFunction ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (k n : ℕ) : ‖dy f k n‖ ≤ 1 := by
  rw [dy_apply]
  split_ifs
  · exact hf n
  · simp

lemma dy_sum (f : ArithmeticFunction ℂ) (K n : ℕ) (hn : n < 2 ^ (K + 1)) :
    ∑ k ∈ range (K + 1), dy f k n = f n := by
  by_cases h0 : n = 0
  · subst h0; simp
  rw [sum_eq_single (Nat.log 2 n)]
  · rw [dy_apply, ite_eq_left ⟨h0, rfl⟩]
  · intro k _ hk
    rw [dy_apply, ite_eq_right]
    rintro ⟨_, h⟩; exact hk h.symm
  · intro h
    exact absurd (mem_range.2 (Nat.log_lt_of_lt_pow h0 hn)) h

/-! ## Supports and sizes of products -/

lemma exists_of_mul_apply_ne_zero {f g : ArithmeticFunction ℂ} {n : ℕ} (h : (f * g) n ≠ 0) :
    ∃ x ∈ n.divisorsAntidiagonal, f x.1 ≠ 0 ∧ g x.2 ≠ 0 := by
  rw [mul_apply] at h
  obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact ⟨x, hx, left_ne_zero_of_mul hne, right_ne_zero_of_mul hne⟩

/-- Support of a product of atoms: if each `A i` (`i ∈ S`) is supported in `[lo i, hi i]`,
then `∏_{i ∈ S} A i` is supported in `[∏ lo, ∏ hi]`. -/
lemma prod_support {ι : Type*} [DecidableEq ι] (A : ι → ArithmeticFunction ℂ) (lo hi : ι → ℕ)
    (S : Finset ι) (h : ∀ i ∈ S, ∀ n, A i n ≠ 0 → lo i ≤ n ∧ n ≤ hi i) :
    ∀ n, (∏ i ∈ S, A i) n ≠ 0 → ∏ i ∈ S, lo i ≤ n ∧ n ≤ ∏ i ∈ S, hi i := by
  induction S using Finset.induction_on with
  | empty =>
    intro n hn
    simp only [prod_empty, one_apply] at hn ⊢
    split_ifs at hn with h1
    · omega
    · exact absurd rfl hn
  | insert a S ha ih =>
    intro n hn
    rw [prod_insert ha] at hn
    obtain ⟨x, hx, h1, h2⟩ := exists_of_mul_apply_ne_zero hn
    have hxn := (Nat.mem_divisorsAntidiagonal.1 hx).1
    obtain ⟨l1, u1⟩ := h a (mem_insert_self a S) _ h1
    obtain ⟨l2, u2⟩ := ih (fun i hi => h i (mem_insert_of_mem hi)) _ h2
    rw [prod_insert ha, prod_insert ha, ← hxn]
    exact ⟨Nat.mul_le_mul l1 l2, Nat.mul_le_mul u1 u2⟩

lemma card_divisorsAntidiagonal (n : ℕ) : n.divisorsAntidiagonal.card = n.divisors.card := by
  rw [← Nat.map_div_right_divisors, card_map]

/-- The collapsed coefficient of `s` atoms bounded by `1` is at most `τ(n)^s`. -/
lemma norm_prod_le {ι : Type*} [DecidableEq ι] (A : ι → ArithmeticFunction ℂ)
    (hA : ∀ i n, ‖A i n‖ ≤ 1) (S : Finset ι) :
    ∀ n, ‖(∏ i ∈ S, A i) n‖ ≤ (n.divisors.card : ℝ) ^ S.card := by
  induction S using Finset.induction_on with
  | empty =>
    intro n
    simp only [prod_empty, one_apply, card_empty, pow_zero]
    split_ifs <;> simp
  | insert a S ha ih =>
    intro n
    rw [prod_insert ha, mul_apply, card_insert_of_notMem ha]
    by_cases hn : n = 0
    · subst hn; simp
    calc ‖∑ x ∈ n.divisorsAntidiagonal, A a x.1 * (∏ i ∈ S, A i) x.2‖
        ≤ ∑ x ∈ n.divisorsAntidiagonal, ‖A a x.1 * (∏ i ∈ S, A i) x.2‖ := norm_sum_le _ _
      _ ≤ ∑ x ∈ n.divisorsAntidiagonal, (n.divisors.card : ℝ) ^ S.card := by
          refine sum_le_sum fun x hx => ?_
          rw [norm_mul]
          have hx2 : x.2 ∣ n := Nat.dvd_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx)
          have hc : (x.2.divisors.card : ℝ) ≤ n.divisors.card := by
            exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hn hx2)
          calc ‖A a x.1‖ * ‖(∏ i ∈ S, A i) x.2‖ ≤ 1 * (x.2.divisors.card : ℝ) ^ S.card :=
                mul_le_mul (hA a _) (ih _) (norm_nonneg _) zero_le_one
            _ ≤ (n.divisors.card : ℝ) ^ S.card := by
                rw [one_mul]; exact pow_le_pow_left₀ (Nat.cast_nonneg _) hc _
      _ = (n.divisors.card : ℝ) ^ (S.card + 1) := by
          rw [sum_const, card_divisorsAntidiagonal, nsmul_eq_mul, pow_succ]; ring

/-! ## Regrouping a Dirichlet product -/

/-- `∑_{d ≤ N} (f * g)(d) ψ(d) = ∑_{u ≤ M₁} ∑_{w ≤ M₂} f(u) g(w) ψ(uw)` when the supports fit. -/
lemma sum_mul_split (f g : ArithmeticFunction ℂ) (ψ : ℕ → ℂ) (N M₁ M₂ : ℕ)
    (hf : ∀ u, f u ≠ 0 → u ≤ M₁) (hg : ∀ w, g w ≠ 0 → w ≤ M₂)
    (hN : ∀ u w, f u ≠ 0 → g w ≠ 0 → u * w ≤ N) :
    ∑ d ∈ Icc 1 N, (f * g) d * ψ d =
      ∑ u ∈ Icc 1 M₁, ∑ w ∈ Icc 1 M₂, f u * g w * ψ (u * w) := by
  set F : ℕ × ℕ → ℂ := fun x => f x.1 * g x.2 * ψ (x.1 * x.2) with hF
  set T := (Icc 1 M₁ ×ˢ Icc 1 M₂).filter (fun x : ℕ × ℕ => f x.1 ≠ 0 ∧ g x.2 ≠ 0) with hT
  have hRHS : ∑ u ∈ Icc 1 M₁, ∑ w ∈ Icc 1 M₂, f u * g w * ψ (u * w) = ∑ x ∈ T, F x := by
    rw [hT, sum_filter_of_ne, sum_product]
    intro x _ hx
    exact ⟨left_ne_zero_of_mul (left_ne_zero_of_mul hx),
      right_ne_zero_of_mul (left_ne_zero_of_mul hx)⟩
  rw [hRHS]
  have hmaps : ∀ x ∈ T, x.1 * x.2 ∈ Icc 1 N := by
    intro x hx
    simp only [hT, mem_filter, mem_product, mem_Icc] at hx
    refine mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.2 ?_, hN _ _ hx.2.1 hx.2.2⟩
    exact mul_ne_zero (by omega) (by omega)
  rw [← sum_fiberwise_of_maps_to hmaps]
  refine sum_congr rfl fun d hd => ?_
  have hd0 : d ≠ 0 := by have := (mem_Icc.1 hd).1; omega
  rw [mul_apply, sum_mul]
  symm
  apply sum_subset_zero_on_sdiff
  · intro x hx
    simp only [mem_filter] at hx
    exact Nat.mem_divisorsAntidiagonal.2 ⟨hx.2, hd0⟩
  · intro x hx
    obtain ⟨hxa, hxT⟩ := mem_sdiff.1 hx
    have hxd := (Nat.mem_divisorsAntidiagonal.1 hxa).1
    by_cases h1 : f x.1 = 0
    · simp [h1]
    by_cases h2 : g x.2 = 0
    · simp [h2]
    exfalso
    have hx1 : 1 ≤ x.1 := Nat.one_le_iff_ne_zero.2 (by rintro h; rw [h, zero_mul] at hxd; omega)
    have hx2 : 1 ≤ x.2 := Nat.one_le_iff_ne_zero.2 (by rintro h; rw [h, mul_zero] at hxd; omega)
    exact hxT (mem_filter.2 ⟨mem_filter.2 ⟨mem_product.2 ⟨mem_Icc.2 ⟨hx1, hf _ h1⟩,
      mem_Icc.2 ⟨hx2, hg _ h2⟩⟩, h1, h2⟩, hxd⟩)
  · intro x hx
    simp only [mem_filter] at hx
    rw [hF]
    simp only
    rw [hx.2]

/-! ## Agreement of products on initial segments -/

lemma mul_agree {f f' g g' : ArithmeticFunction ℂ} {B : ℕ} (hf : ∀ n < B, f n = f' n)
    (hg : ∀ n < B, g n = g' n) : ∀ n < B, (f * g) n = (f' * g') n := by
  intro n hn
  rw [mul_apply, mul_apply]
  refine sum_congr rfl fun x hx => ?_
  have h1 := Nat.divisor_le (Nat.fst_mem_divisors_of_mem_antidiagonal hx)
  have h2 := Nat.divisor_le (Nat.snd_mem_divisors_of_mem_antidiagonal hx)
  rw [hf _ (by omega), hg _ (by omega)]

lemma pow_agree {f f' : ArithmeticFunction ℂ} {B : ℕ} (hf : ∀ n < B, f n = f' n) (m : ℕ) :
    ∀ n < B, (f ^ m) n = (f' ^ m) n := by
  induction m with
  | zero => intro n _; rfl
  | succ m ih => rw [pow_succ, pow_succ]; exact mul_agree ih hf

/-! ## The Heath-Brown identity over `ℂ` -/

lemma intCoe_pow' (f : ArithmeticFunction ℤ) (m : ℕ) :
    ((f ^ m : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) = (f : ArithmeticFunction ℂ) ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, intCoe_one]
  | succ m ih => rw [pow_succ, intCoe_mul, ih, pow_succ]

/-- `ζ` over `ℂ`. -/
noncomputable abbrev zC : ArithmeticFunction ℂ := (ζ : ArithmeticFunction ℂ)

/-- The truncated Möbius function `M_Z` over `ℂ`. -/
noncomputable def MC (Z : ℝ) : ArithmeticFunction ℂ :=
  ((HeathBrown.truncMu Z : ArithmeticFunction ℤ) : ArithmeticFunction ℂ)

lemma MC_apply (Z : ℝ) (n : ℕ) : MC Z n = if (n : ℝ) ≤ Z then ((μ n : ℤ) : ℂ) else 0 := by
  rw [MC, intCoe_apply, HeathBrown.truncMu_apply]
  split_ifs <;> simp

lemma norm_MC_le (Z : ℝ) (n : ℕ) : ‖MC Z n‖ ≤ 1 := by
  rw [MC_apply]
  split_ifs
  · rw [Complex.norm_intCast]; exact_mod_cast abs_moebius_le_one
  · simp

lemma zC_apply (n : ℕ) : zC n = if n = 0 then 0 else 1 := by
  simp [zC, natCoe_apply, zeta_apply]

lemma norm_zC_le (n : ℕ) : ‖zC n‖ ≤ 1 := by
  rw [zC_apply]; split_ifs <;> simp

/-- Coefficients `(-1)^{j-1} C(5,j)` of the Heath-Brown identity with `J = 5`. -/
noncomputable def hbCoeff (j : ℕ) : ℂ := (((-1) ^ (j - 1) * (Nat.choose 5 j : ℤ) : ℤ) : ℂ)

lemma norm_hbCoeff_le (j : ℕ) : ‖hbCoeff j‖ ≤ 10 := by
  rw [hbCoeff, Complex.norm_intCast]
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast, abs_mul,
    abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
  have : Nat.choose 5 j ≤ 10 :=
    (Nat.choose_le_middle j 5).trans (by decide)
  exact_mod_cast this

/-- **Heath-Brown identity** (paper, Lemma 2.6) with `J = 5`, over `ℂ`. -/
theorem heathBrown_complex {Z : ℝ} (hZ : 0 ≤ Z) {n : ℕ} (hn1 : 1 ≤ n) (hn : (n : ℝ) ≤ Z ^ 5) :
    ((μ n : ℤ) : ℂ) = ∑ j ∈ Icc 1 5, hbCoeff j * (zC ^ (j - 1) * MC Z ^ j) n := by
  rw [HeathBrown.heathBrown_identity (by norm_num) hZ hn1 hn]
  push_cast
  refine sum_congr rfl fun j _ => ?_
  rw [hbCoeff]
  push_cast
  congr 1
  rw [← intCoe_apply, intCoe_mul, intCoe_pow', intCoe_pow', MC]
  rfl

/-! ## Expansion into sharp dyadic boxes -/

/-- Ranges of the dyadic exponents of the `j-1` `ζ`-atoms and the `j` `M_Z`-atoms. -/
def boxRange (j Kz Km : ℕ) : Fin (j - 1) ⊕ Fin j → Finset ℕ :=
  Sum.elim (fun _ => range (Kz + 1)) (fun _ => range (Km + 1))

/-- The atoms of a box: `ζ · 𝟙_{[2^k,2^{k+1})}` or `M_Z · 𝟙_{[2^k,2^{k+1})}`. -/
noncomputable def boxAtom (j : ℕ) (fz fm : ArithmeticFunction ℂ) :
    Fin (j - 1) ⊕ Fin j → ℕ → ArithmeticFunction ℂ :=
  Sum.elim (fun _ k => dy fz k) (fun _ k => dy fm k)

lemma prod_sum_expand (j Kz Km : ℕ) (fz fm : ArithmeticFunction ℂ) :
    (∑ k ∈ range (Kz + 1), dy fz k) ^ (j - 1) * (∑ k ∈ range (Km + 1), dy fm k) ^ j =
      ∑ κ ∈ Fintype.piFinset (boxRange j Kz Km), ∏ i, boxAtom j fz fm i (κ i) := by
  rw [← Finset.prod_univ_sum, Fintype.prod_sum_type]
  simp [boxRange, boxAtom, prod_const]

/-- **Box expansion of `μ`** (paper, Theorem 6.1, Step 2): with `Z = 2^{Km}`, for
`1 ≤ d ≤ Z^5` and `d < 2^{Kz+1}`,
`μ(d) = ∑_{j=1}^{5} c_j ∑_{κ} (∏_i A_{j,i,κ_i})(d)`. -/
theorem mu_box_expansion (Kz Km : ℕ) {d : ℕ} (hd1 : 1 ≤ d)
    (hdZ : (d : ℝ) ≤ ((2 : ℝ) ^ Km) ^ 5) (hdK : d < 2 ^ (Kz + 1)) :
    ((μ d : ℤ) : ℂ) = ∑ j ∈ Icc 1 5, hbCoeff j *
      ∑ κ ∈ Fintype.piFinset (boxRange j Kz Km),
        (∏ i, boxAtom j zC (MC ((2 : ℝ) ^ Km)) i (κ i)) d := by
  rw [heathBrown_complex (by positivity) hd1 hdZ]
  refine sum_congr rfl fun j _ => ?_
  congr 1
  rw [← af_sum_apply, ← prod_sum_expand]
  have hz : ∀ n < 2 ^ (Kz + 1), zC n = (∑ k ∈ range (Kz + 1), dy zC k) n := by
    intro n hn; rw [af_sum_apply, dy_sum _ _ _ hn]
  have hm : ∀ n < 2 ^ (Kz + 1), MC ((2 : ℝ) ^ Km) n =
      (∑ k ∈ range (Km + 1), dy (MC ((2 : ℝ) ^ Km)) k) n := by
    intro n _
    rw [af_sum_apply]
    by_cases h0 : MC ((2 : ℝ) ^ Km) n = 0
    · rw [h0]; symm
      refine sum_eq_zero fun k _ => ?_
      rw [dy_apply]; split_ifs <;> simp [h0]
    · have hle : (n : ℝ) ≤ (2 : ℝ) ^ Km := by
        by_contra hc
        exact h0 (by rw [MC_apply, ite_eq_right hc])
      have hlt : n < 2 ^ (Km + 1) := by
        have : (n : ℝ) < (2 : ℝ) ^ (Km + 1) := by
          rw [pow_succ]; linarith [pow_pos (two_pos (α := ℝ)) Km]
        exact_mod_cast this
      rw [dy_sum _ _ _ hlt]
  exact mul_agree (pow_agree hz _) (pow_agree hm _) d hdK

end MeanValue
end MobiusDeterminant
