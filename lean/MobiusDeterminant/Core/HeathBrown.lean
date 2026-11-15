import Mathlib

/-!
# The Heath-Brown identity (paper, Lemma 2.6)

For `J ≥ 1`, `Z ≥ 0` (the paper takes `Z ≥ 1`) and `1 ≤ n ≤ Z^J`,
```
μ(n) = ∑_{j=1}^{J} (-1)^{j-1} C(J,j) ∑_{m₁⋯m_j n₁⋯n_{j-1} = n, mᵢ ≤ Z} μ(m₁)⋯μ(m_j).
```
We prove it in the ring of arithmetic functions `ArithmeticFunction ℤ` (Dirichlet
convolution), with `M_Z(m) = μ(m) 𝟙_{m ≤ Z}` the truncated Möbius function: the inner
sum is the value at `n` of `ζ^{j-1} * M_Z^j`.

Proof (as in the paper): the coefficients of `1 - ζ M_Z` vanish on `[1, Z]`, hence those of
`(1 - ζ M_Z)^J` vanish on `[1, Z^J]`, and so do those of `μ (1 - ζ M_Z)^J`; expanding the
latter by the binomial theorem and using `μ ζ = 1` gives the identity.
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace MobiusDeterminant
namespace HeathBrown

/-- The truncated Möbius function `M_Z(m) = μ(m)` for `m ≤ Z`, `0` otherwise
(the Dirichlet polynomial `M_Z(s) = ∑_{m ≤ Z} μ(m) m^{-s}` of Lemma 2.6). -/
noncomputable def truncMu (Z : ℝ) : ArithmeticFunction ℤ :=
  ⟨fun m => if (m : ℝ) ≤ Z then μ m else 0, by simp⟩

/-- Values of the truncated Möbius function of Lemma 2.6. -/
theorem truncMu_apply (Z : ℝ) (m : ℕ) :
    truncMu Z m = if (m : ℝ) ≤ Z then μ m else 0 := rfl

/-- `ζ` as an arithmetic function with integer values. -/
abbrev zetaZ : ArithmeticFunction ℤ := (ζ : ArithmeticFunction ℤ)

/-- Evaluation at `n`, as an additive homomorphism (comparison of coefficients in Lemma 2.6). -/
def evalAt (n : ℕ) : ArithmeticFunction ℤ →+ ℤ where
  toFun f := f n
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem evalAt_apply (n : ℕ) (f : ArithmeticFunction ℤ) : evalAt n f = f n := rfl

/-- Lemma 2.6, first step: the coefficients of `1 - ζ M_Z` vanish at every `n ≤ Z`
(trivially at `n = 0`; for `1 ≤ n ≤ Z` this is `∑_{d ∣ n} μ(d) = [n = 1]`). -/
theorem one_sub_zeta_mul_truncMu_apply {Z : ℝ} {n : ℕ} (hn : (n : ℝ) ≤ Z) :
    (1 - zetaZ * truncMu Z) n = 0 := by
  have h1 : (zetaZ * truncMu Z) n = (1 : ArithmeticFunction ℤ) n := by
    rw [coe_zeta_mul_apply, ← coe_zeta_mul_moebius, coe_zeta_mul_apply]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hdn : d ≤ n := Nat.divisor_le hd
    have : (d : ℝ) ≤ Z := le_trans (by exact_mod_cast hdn) hn
    simp [truncMu_apply, this]
  have := map_sub (evalAt n) 1 (zetaZ * truncMu Z)
  simp only [evalAt_apply] at this
  rw [this, h1, sub_self]

/-- Support of a Dirichlet product (Lemma 2.6): if `f` vanishes on `[1, A]` and `g` on `[1, B]`
(`A, B ≥ 0`), then `f * g` vanishes on `[1, A B]`. -/
theorem mul_apply_eq_zero_of_vanish {f g : ArithmeticFunction ℤ} {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ A → f n = 0)
    (hg : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ B → g n = 0)
    {n : ℕ} (hn1 : 1 ≤ n) (hn : (n : ℝ) ≤ A * B) : (f * g) n = 0 := by
  rw [mul_apply]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Nat.mem_divisorsAntidiagonal] at hx
  obtain ⟨hxn, -⟩ := hx
  have h1 : 1 ≤ x.1 := by
    rcases Nat.eq_zero_or_pos x.1 with h | h
    · rw [h, zero_mul] at hxn; omega
    · exact h
  have h2 : 1 ≤ x.2 := by
    rcases Nat.eq_zero_or_pos x.2 with h | h
    · rw [h, mul_zero] at hxn; omega
    · exact h
  by_cases ha : (x.1 : ℝ) ≤ A
  · rw [hf _ h1 ha, zero_mul]
  by_cases hb : (x.2 : ℝ) ≤ B
  · rw [hg _ h2 hb, mul_zero]
  exfalso
  rw [not_le] at ha hb
  have hx2pos : (0 : ℝ) < x.2 := lt_of_le_of_lt hB hb
  have : A * B < (n : ℝ) := by
    rw [← hxn, Nat.cast_mul]
    calc A * B ≤ A * x.2 := mul_le_mul_of_nonneg_left hb.le hA
      _ < x.1 * x.2 := mul_lt_mul_of_pos_right ha hx2pos
  linarith

/-- If `g` vanishes on `[1, A]`, so does `f * g` (Lemma 2.6: `ζ^{-1} = μ` times
`(1 - ζ M_Z)^J`). -/
theorem mul_apply_eq_zero_of_vanish_right {f g : ArithmeticFunction ℤ} {A : ℝ}
    (hg : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ A → g n = 0)
    {n : ℕ} (hn1 : 1 ≤ n) (hn : (n : ℝ) ≤ A) : (f * g) n = 0 := by
  rw [mul_apply]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Nat.mem_divisorsAntidiagonal] at hx
  obtain ⟨hxn, -⟩ := hx
  have h2 : 1 ≤ x.2 := by
    rcases Nat.eq_zero_or_pos x.2 with h | h
    · rw [h, mul_zero] at hxn; omega
    · exact h
  have hle : x.2 ≤ n := Nat.le_of_dvd (by omega) ⟨x.1, by rw [← hxn, mul_comm]⟩
  rw [hg _ h2 (le_trans (by exact_mod_cast hle) hn), mul_zero]

/-- Lemma 2.6, second step: the coefficients of `(1 - ζ M_Z)^J` vanish on `[1, Z^J]`. -/
theorem one_sub_zeta_mul_truncMu_pow_apply {Z : ℝ} (hZ : 0 ≤ Z) {J : ℕ} (hJ : 1 ≤ J)
    {n : ℕ} (hn1 : 1 ≤ n) (hn : (n : ℝ) ≤ Z ^ J) :
    ((1 - zetaZ * truncMu Z) ^ J) n = 0 := by
  induction J, hJ using Nat.le_induction generalizing n with
  | base => rw [pow_one]; exact one_sub_zeta_mul_truncMu_apply (by simpa using hn)
  | succ J hJ ih =>
    rw [pow_succ]
    refine mul_apply_eq_zero_of_vanish (pow_nonneg hZ J) hZ (fun m hm1 hm => ih hm1 hm)
      (fun _ _ hm => one_sub_zeta_mul_truncMu_apply hm) hn1 ?_
    rwa [← pow_succ]

/-- The binomial expansion of `μ (1 - ζ M)^J` in the ring of arithmetic functions,
using `μ ζ = 1` (proof of Lemma 2.6). -/
theorem moebius_mul_one_sub_pow (J : ℕ) (M : ArithmeticFunction ℤ) :
    (μ : ArithmeticFunction ℤ) * (1 - zetaZ * M) ^ J
      = μ + ∑ j ∈ range J, ((-1) ^ (j + 1) * (J.choose (j + 1) : ℤ)) • (zetaZ ^ j * M ^ (j + 1)) := by
  have hmz : (μ : ArithmeticFunction ℤ) * zetaZ = 1 := moebius_mul_coe_zeta
  rw [sub_eq_add_neg, add_comm, add_pow, Finset.mul_sum, Finset.sum_range_succ', add_comm]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [zsmul_eq_mul]
    push_cast
    linear_combination ((-1 : ArithmeticFunction ℤ) ^ (j + 1) * (J.choose (j + 1) : ArithmeticFunction ℤ)
      * zetaZ ^ j * M ^ (j + 1)) * hmz

/-- **Heath-Brown identity** (paper, Lemma 2.6), in Dirichlet-convolution form.
For `J ≥ 1`, `Z ≥ 0` and `1 ≤ n ≤ Z^J`,
`μ(n) = ∑_{j=1}^{J} (-1)^{j-1} C(J,j) (ζ^{j-1} M_Z^j)(n)`,
where `(ζ^{j-1} M_Z^j)(n) = ∑_{m₁⋯m_j n₁⋯n_{j-1} = n, mᵢ ≤ Z} μ(m₁)⋯μ(m_j)`. -/
theorem heathBrown_identity {J : ℕ} (hJ : 1 ≤ J) {Z : ℝ} (hZ : 0 ≤ Z) {n : ℕ} (hn1 : 1 ≤ n)
    (hn : (n : ℝ) ≤ Z ^ J) :
    μ n = ∑ j ∈ Icc 1 J,
      (-1) ^ (j - 1) * (J.choose j : ℤ) * ((zetaZ ^ (j - 1) * truncMu Z ^ j) n) := by
  have hvan : ((μ : ArithmeticFunction ℤ) * (1 - zetaZ * truncMu Z) ^ J) n = 0 :=
    mul_apply_eq_zero_of_vanish_right
      (fun _ hm1 hm => one_sub_zeta_mul_truncMu_pow_apply hZ hJ hm1 hm) hn1 hn
  have hexp := congrArg (evalAt n) (moebius_mul_one_sub_pow J (truncMu Z))
  rw [evalAt_apply, hvan, map_add, map_sum] at hexp
  simp only [map_zsmul, evalAt_apply, smul_eq_mul] at hexp
  have hreindex : ∑ j ∈ Icc 1 J,
      (-1) ^ (j - 1) * (J.choose j : ℤ) * ((zetaZ ^ (j - 1) * truncMu Z ^ j) n)
      = ∑ j ∈ range J,
      (-1) ^ j * (J.choose (j + 1) : ℤ) * ((zetaZ ^ j * truncMu Z ^ (j + 1)) n) := by
    refine Finset.sum_nbij' (fun j => j - 1) (fun j => j + 1) ?_ ?_ ?_ ?_ ?_
    · intro j hj; simp only [mem_Icc, mem_range] at hj ⊢; omega
    · intro j hj; simp only [mem_Icc, mem_range] at hj ⊢; omega
    · intro j hj; simp only [mem_Icc] at hj; omega
    · intro j _; simp
    · intro j hj
      simp only [mem_Icc] at hj
      obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      simp
  rw [hreindex]
  have hneg : ∑ j ∈ range J,
      (-1) ^ j * (J.choose (j + 1) : ℤ) * ((zetaZ ^ j * truncMu Z ^ (j + 1)) n)
      = -∑ j ∈ range J,
      (-1) ^ (j + 1) * (J.choose (j + 1) : ℤ) * ((zetaZ ^ j * truncMu Z ^ (j + 1)) n) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hneg]
  linarith

/-! ## Unfolding the Dirichlet powers as sums over tuples -/

/-- `(f^k)(n) = ∑_{a₁⋯a_k = n} f(a₁)⋯f(a_k)` (unfolding the inner sums of Lemma 2.6). -/
theorem pow_apply_eq_sum_finMulAntidiag (f : ArithmeticFunction ℤ) (k n : ℕ) :
    (f ^ k) n = ∑ a ∈ Nat.finMulAntidiag k n, ∏ i, f (a i) := by
  induction k generalizing n with
  | zero =>
    by_cases hn : n = 1
    · subst hn; simp [Nat.finMulAntidiag_one, one_apply]
    · rw [Nat.finMulAntidiag_zero_left hn]; simp [one_apply, hn]
  | succ k ih =>
    rw [pow_succ', mul_apply]
    simp_rw [ih, Finset.mul_sum]
    rw [Finset.sum_sigma']
    refine Finset.sum_bij' (fun x _ => Fin.cons x.1.1 x.2)
      (fun s _ => ⟨(s 0, ∏ i : Fin k, s i.succ), Fin.tail s⟩) ?_ ?_ ?_ ?_ ?_
    · rintro ⟨⟨a, b⟩, t⟩ hx
      simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal, Nat.mem_finMulAntidiag] at hx ⊢
      refine ⟨?_, hx.1.2⟩
      rw [Fin.prod_cons, hx.2.1, hx.1.1]
    · intro s hs
      simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal, Nat.mem_finMulAntidiag] at hs ⊢
      rw [Fin.prod_univ_succ] at hs
      refine ⟨⟨hs.1, hs.2⟩, rfl, ?_⟩
      intro h0
      rw [h0, mul_zero] at hs
      exact hs.2 hs.1.symm
    · rintro ⟨⟨a, b⟩, t⟩ hx
      simp only [Finset.mem_sigma, Nat.mem_finMulAntidiag] at hx
      simp only [Fin.cons_zero, Fin.cons_succ, Fin.tail_cons, hx.2.1]
    · intro s _
      simp
    · rintro ⟨⟨a, b⟩, t⟩ _
      simp [Fin.prod_univ_succ]

/-- `(f^a g^b)(n) = ∑_{s₁⋯s_a t₁⋯t_b = n} f(s₁)⋯f(s_a) g(t₁)⋯g(t_b)`, the tuples
ranging over divisors of `n` (unfolding the inner sums of Lemma 2.6). -/
theorem pow_mul_pow_apply (f g : ArithmeticFunction ℤ) (a b n : ℕ) :
    (f ^ a * g ^ b) n = ∑ p ∈ ((Fintype.piFinset fun _ : Fin a => n.divisors) ×ˢ
        (Fintype.piFinset fun _ : Fin b => n.divisors)).filter
        (fun p => (∏ i, p.1 i) * (∏ i, p.2 i) = n),
      (∏ i, f (p.1 i)) * ∏ i, g (p.2 i) := by
  rw [mul_apply]
  simp_rw [pow_apply_eq_sum_finMulAntidiag, Finset.sum_mul_sum, ← Finset.sum_product']
  rw [Finset.sum_sigma']
  refine Finset.sum_bij' (fun x _ => x.2)
    (fun p _ => ⟨(∏ i, p.1 i, ∏ i, p.2 i), p⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨⟨u, v⟩, ⟨s, t⟩⟩ hx
    simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal, Finset.mem_product,
      Nat.mem_finMulAntidiag] at hx
    obtain ⟨⟨huv, hn⟩, ⟨hs, hu⟩, ⟨ht, hv⟩⟩ := hx
    simp only [Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset, Nat.mem_divisors]
    refine ⟨⟨fun i => ⟨?_, hn⟩, fun i => ⟨?_, hn⟩⟩, by rw [hs, ht, huv]⟩
    · rw [← huv, ← hs]
      exact Dvd.dvd.mul_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) _
    · rw [← huv, ← ht]
      exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) _
  · rintro ⟨s, t⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset,
      Nat.mem_divisors] at hp
    obtain ⟨⟨hs, ht⟩, hst⟩ := hp
    have hn : n ≠ 0 := by
      intro hn0
      rw [hn0, mul_eq_zero, Finset.prod_eq_zero_iff, Finset.prod_eq_zero_iff] at hst
      rcases hst with ⟨i, -, hi⟩ | ⟨i, -, hi⟩
      · exact (hs i).2 hn0
      · exact (ht i).2 hn0
    have hu : ∏ i, s i ≠ 0 := fun h => hn (by rw [← hst, h, zero_mul])
    have hv : ∏ i, t i ≠ 0 := fun h => hn (by rw [← hst, h, mul_zero])
    simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal, Finset.mem_product,
      Nat.mem_finMulAntidiag]
    refine ⟨⟨hst, hn⟩, ?_, ?_⟩ <;> simp_all
  · rintro ⟨⟨u, v⟩, ⟨s, t⟩⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_product, Nat.mem_finMulAntidiag] at hx
    simp only [hx.2.1.1, hx.2.2.1]
  · intro p _
    rfl
  · intro x _
    rfl

/-- The inner sum of Lemma 2.6 written out:
`(ζ^{j-1} M_Z^j)(n) = ∑_{m₁⋯m_j n₁⋯n_{j-1} = n, mᵢ ≤ Z} μ(m₁)⋯μ(m_j)`
(all `mᵢ, nᵢ` range over divisors of `n`). -/
theorem zeta_pow_mul_truncMu_pow_apply (Z : ℝ) (j n : ℕ) :
    (zetaZ ^ (j - 1) * truncMu Z ^ j) n
      = ∑ p ∈ ((Fintype.piFinset fun _ : Fin j => n.divisors) ×ˢ
          (Fintype.piFinset fun _ : Fin (j - 1) => n.divisors)).filter
          (fun p => (∏ i, p.1 i) * (∏ i, p.2 i) = n ∧ ∀ i, (p.1 i : ℝ) ≤ Z),
        ∏ i, μ (p.1 i) := by
  rw [mul_comm, pow_mul_pow_apply, ← Finset.filter_filter,
    Finset.sum_filter (fun p : (Fin j → ℕ) × (Fin (j - 1) → ℕ) => ∀ i, (p.1 i : ℝ) ≤ Z)]
  refine Finset.sum_congr rfl fun p hp => ?_
  simp only [Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset,
    Nat.mem_divisors] at hp
  have hz : ∏ i, zetaZ (p.2 i) = 1 := by
    refine Finset.prod_eq_one fun i _ => ?_
    have : p.2 i ≠ 0 := fun h => (hp.1.2 i).2 (by rw [← h]; simpa [h] using (hp.1.2 i).1)
    simp [natCoe_apply, zeta_apply, this]
  rw [hz, mul_one]
  by_cases h : ∀ i, (p.1 i : ℝ) ≤ Z
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
    exact Finset.prod_congr rfl fun i _ => by simp [truncMu_apply, h i]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h)]
    push Not at h
    obtain ⟨i, hi⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [truncMu_apply, not_le.mpr hi])

/-- **Heath-Brown identity** (paper, Lemma 2.6), fully explicit form: for `J ≥ 1`, `Z ≥ 0`
and `1 ≤ n ≤ Z^J`,
`μ(n) = ∑_{j=1}^{J} (-1)^{j-1} C(J,j) ∑_{m₁⋯m_j n₁⋯n_{j-1} = n, mᵢ ≤ Z} μ(m₁)⋯μ(m_j)`,
the tuples `(m, n')` ranging over `Fin j → ℕ` and `Fin (j-1) → ℕ` (necessarily of divisors
of `n`). -/
theorem heathBrown_identity_explicit {J : ℕ} (hJ : 1 ≤ J) {Z : ℝ} (hZ : 0 ≤ Z) {n : ℕ}
    (hn1 : 1 ≤ n) (hn : (n : ℝ) ≤ Z ^ J) :
    μ n = ∑ j ∈ Icc 1 J, (-1) ^ (j - 1) * (J.choose j : ℤ) *
      ∑ p ∈ ((Fintype.piFinset fun _ : Fin j => n.divisors) ×ˢ
          (Fintype.piFinset fun _ : Fin (j - 1) => n.divisors)).filter
          (fun p => (∏ i, p.1 i) * (∏ i, p.2 i) = n ∧ ∀ i, (p.1 i : ℝ) ≤ Z),
        ∏ i, μ (p.1 i) := by
  rw [heathBrown_identity hJ hZ hn1 hn]
  simp_rw [zeta_pow_mul_truncMu_pow_apply]

end HeathBrown
end MobiusDeterminant
