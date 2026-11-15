import MobiusDeterminant.Unconditional.BalancedEnergy

/-!
# Balanced boxes: the bilinear form for a single modulus

For a fixed modulus `e` we rewrite `balForm` as a bilinear form in the variables
`(h, u)` and `w` with phase `e_e(h ū w̄)`, group the variables `(h, u)` according to the
reduced fraction `ρ = h/u` (the phase depends only on `ρ`; this is the stratification
`g' = (a, u)` of Step 3 of the proof of Theorem 6.1), and apply Lemma 3.1.
-/

open Finset

namespace MobiusDeterminant
namespace BalancedBox

/-! ## Grouping by the fraction `h/u` -/

/-- Grouping a bilinear sum according to the value of `f`, when the phase factors through
`f`. -/
theorem regroup {σ κ : Type*} (S : Finset σ) (T : Finset κ) (f : σ → ℚ) (c : σ → ℂ)
    (d : κ → ℂ) (φ : σ → κ → ℂ) (Φ : ℚ → κ → ℂ)
    (h : ∀ s ∈ S, ∀ k ∈ T, φ s k = Φ (f s) k) :
    ∑ s ∈ S, ∑ k ∈ T, c s * d k * φ s k =
      ∑ ρ ∈ S.image f, ∑ k ∈ T, (∑ s ∈ S.filter (fun s => f s = ρ), c s) * d k * Φ ρ k := by
  classical
  rw [← sum_fiberwise_of_maps_to (g := f) (t := S.image f) (fun s hs => mem_image_of_mem f hs)]
  refine sum_congr rfl (fun ρ _ => ?_)
  simp_rw [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl (fun k hk => sum_congr rfl (fun s hs => ?_))
  rw [mem_filter] at hs
  rw [h s hs.1 k hk, hs.2]

/-- `∑_ρ |∑_{f s = ρ} c_s|² ≤ #{(s, s') : f s = f s'}` for `|c| ≤ 1`. -/
theorem sum_norm_fiber_sq_le {σ : Type*} (S : Finset σ) (f : σ → ℚ) (c : σ → ℂ)
    (hc : ∀ s ∈ S, ‖c s‖ ≤ 1) :
    ∑ ρ ∈ S.image f, ‖∑ s ∈ S.filter (fun s => f s = ρ), c s‖ ^ 2 ≤
      ((S ×ˢ S).filter (fun p => f p.1 = f p.2)).card := by
  classical
  have h1 : ∀ ρ, ‖∑ s ∈ S.filter (fun s => f s = ρ), c s‖ ^ 2 ≤
      (((S.filter (fun s => f s = ρ)).card : ℕ) : ℝ) ^ 2 := by
    intro ρ
    have : ‖∑ s ∈ S.filter (fun s => f s = ρ), c s‖ ≤ (S.filter (fun s => f s = ρ)).card := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ s ∈ S.filter (fun s => f s = ρ), ‖c s‖
          ≤ ∑ _s ∈ S.filter (fun s => f s = ρ), (1 : ℝ) :=
            sum_le_sum (fun s hs => hc s (mem_filter.1 hs).1)
        _ = _ := by simp
    gcongr
  refine (sum_le_sum (fun ρ _ => h1 ρ)).trans (le_of_eq ?_)
  norm_cast
  have h2 : ∀ ρ ∈ S.image f, (S.filter (fun s => f s = ρ)).card ^ 2 =
      ∑ s ∈ S.filter (fun s => f s = ρ), (S.filter (fun s' => f s' = f s)).card := by
    intro ρ _
    rw [sq, ← smul_eq_mul, ← sum_const]
    refine sum_congr rfl (fun s hs => ?_)
    rw [(mem_filter.1 hs).2]
  rw [sum_congr rfl h2, sum_fiberwise_of_maps_to (fun s hs => mem_image_of_mem f hs)
    (fun s => (S.filter (fun s' => f s' = f s)).card)]
  rw [card_filter, sum_product]
  refine sum_congr rfl (fun s _ => ?_)
  rw [card_filter]
  refine sum_congr rfl (fun s' _ => ?_)
  simp only [eq_comm]

/-! ## The sets of variables -/

/-- The variables `(h, u)`: `h ≠ 0`, `|h| ≤ H`, `1 ≤ u ≤ Umax`, `α u ≠ 0`. -/
noncomputable def hu_set (α : ℕ → ℂ) (Umax Hn : ℕ) : Finset (ℤ × ℕ) :=
  (Icc (-(Hn : ℤ)) Hn ×ˢ Icc 1 Umax).filter (fun s => s.1 ≠ 0 ∧ α s.2 ≠ 0)

/-- The variables `w`: `1 ≤ w ≤ Wmax`, `β w ≠ 0`. -/
noncomputable def w_set (β : ℕ → ℂ) (Wmax : ℕ) : Finset ℕ :=
  (Icc 1 Wmax).filter (fun w => β w ≠ 0)

/-- The fraction `h/u`. -/
def frac (s : ℤ × ℕ) : ℚ := (s.1 : ℚ) / (s.2 : ℚ)

/-- `balForm` as a bilinear form in `(h, u)` and `w` with phase `e_e(h ū w̄)`. -/
theorem balForm_eq (α β : ℕ → ℂ) (Umax Wmax : ℕ) (ν : ℤ → ℂ) (Hn : ℕ) (e : ℕ) [NeZero e]
    (hν : ν 0 = 0) :
    balForm α β Umax Wmax ν Hn e =
      ∑ s ∈ (hu_set α Umax Hn).filter (fun s => Nat.Coprime s.2 (2 * e)),
        ∑ w ∈ (w_set β Wmax).filter (fun w => Nat.Coprime w (2 * e)),
          (ν s.1 * α s.2) * β w *
            ZMod.stdAddChar ((s.1 : ZMod e) * (s.2 : ZMod e)⁻¹ * (w : ZMod e)⁻¹) := by
  classical
  set G : ℤ → ℕ → ℕ → ℂ := fun h u w =>
    if ((h ≠ 0 ∧ α u ≠ 0) ∧ Nat.Coprime u (2 * e)) ∧ (β w ≠ 0 ∧ Nat.Coprime w (2 * e)) then
      (ν h * α u) * β w * ZMod.stdAddChar ((h : ZMod e) * (u : ZMod e)⁻¹ * (w : ZMod e)⁻¹)
    else 0 with hG
  -- the right side
  have hR : ∑ s ∈ (hu_set α Umax Hn).filter (fun s => Nat.Coprime s.2 (2 * e)),
        ∑ w ∈ (w_set β Wmax).filter (fun w => Nat.Coprime w (2 * e)),
          (ν s.1 * α s.2) * β w *
            ZMod.stdAddChar ((s.1 : ZMod e) * (s.2 : ZMod e)⁻¹ * (w : ZMod e)⁻¹) =
      ∑ u ∈ Icc 1 Umax, ∑ w ∈ Icc 1 Wmax, ∑ h ∈ Icc (-(Hn : ℤ)) Hn, G h u w := by
    unfold hu_set w_set
    rw [filter_filter, filter_filter, sum_filter, sum_product, sum_comm]
    refine sum_congr rfl (fun u _ => ?_)
    rw [sum_comm]
    refine sum_congr rfl (fun h _ => ?_)
    rw [sum_filter]
    simp only [hG]
    by_cases h1 : (h ≠ 0 ∧ α u ≠ 0) ∧ Nat.Coprime u (2 * e)
    · rw [ite_eq_left h1]
      refine sum_congr rfl (fun w _ => ?_)
      by_cases h2 : β w ≠ 0 ∧ Nat.Coprime w (2 * e)
      · rw [ite_eq_left h2, ite_eq_left ⟨h1, h2⟩]
      · rw [ite_eq_right h2, ite_eq_right (fun h => h2 h.2)]
    · rw [ite_eq_right h1]
      symm
      refine sum_eq_zero (fun w _ => ?_)
      rw [ite_eq_right (fun h => h1 h.1)]
  rw [hR]
  unfold balForm
  refine sum_congr rfl (fun u _ => sum_congr rfl (fun w _ => ?_))
  by_cases hc : Nat.Coprime (u * w) (2 * e)
  · rw [ite_eq_left hc]
    have hc' := Nat.coprime_mul_iff_left.1 hc
    have hue : Nat.Coprime u e := Nat.Coprime.coprime_dvd_right (dvd_mul_left e 2) hc'.1
    have hwe : Nat.Coprime w e := Nat.Coprime.coprime_dvd_right (dvd_mul_left e 2) hc'.2
    rw [mul_sum]
    refine sum_congr rfl (fun h _ => ?_)
    simp only [hG]
    rw [kfrac_eq_stdAddChar, inv_natCast_mul hue hwe]
    by_cases h0 : h = 0
    · subst h0; simp [hν]
    by_cases ha : α u = 0
    · simp [ha]
    by_cases hb : β w = 0
    · simp [hb]
    rw [ite_eq_left ⟨⟨⟨h0, ha⟩, hc'.1⟩, hb, hc'.2⟩, mul_assoc ((h : ZMod e))]
    ring
  · rw [ite_eq_right hc]
    symm
    refine sum_eq_zero (fun h _ => ?_)
    simp only [hG]
    rw [ite_eq_right]
    rintro ⟨⟨_, h1⟩, _, h2⟩
    exact hc (Nat.coprime_mul_iff_left.2 ⟨h1, h2⟩)

/-! ## Lemma 3.1 for a single modulus -/

lemma mem_hu_set {α : ℕ → ℂ} {Umax Hn : ℕ} {s : ℤ × ℕ} (hs : s ∈ hu_set α Umax Hn) :
    s.1 ≠ 0 ∧ |s.1| ≤ Hn ∧ 1 ≤ s.2 ∧ s.2 ≤ Umax ∧ α s.2 ≠ 0 := by
  unfold hu_set at hs
  simp only [mem_filter, mem_product, mem_Icc] at hs
  exact ⟨hs.2.1, abs_le.2 hs.1.1, hs.1.2.1, hs.1.2.2, hs.2.2⟩

lemma mem_w_set {β : ℕ → ℂ} {Wmax : ℕ} {w : ℕ} (hw : w ∈ w_set β Wmax) :
    1 ≤ w ∧ w ≤ Wmax ∧ β w ≠ 0 := by
  unfold w_set at hw
  simp only [mem_filter, mem_Icc] at hw
  exact ⟨hw.1.1, hw.1.2, hw.2⟩

/-- **Lemma 3.1 for the balanced form at a single modulus `e`**:
`|balForm_e|⁸ ≤ P⁴ · #W⁴ · e · I_𝓕(e) · I_𝓦(e)`, where `P` is the number of coincidences
`h/u = h'/u'`, `I_𝓕(e)` the energy modulo `e` of the fractions `h/u` and `I_𝓦(e)` the
reciprocal energy of the `w`. -/
theorem per_modulus_bound (α β : ℕ → ℂ) (Umax Wmax : ℕ) (ν : ℤ → ℂ) (Hn : ℕ) (e : ℕ)
    [NeZero e] (hν : ν 0 = 0) (hνb : ∀ h, ‖ν h‖ ≤ 1) (hα : ∀ u, ‖α u‖ ≤ 1)
    (hβ : ∀ w, ‖β w‖ ≤ 1) :
    ‖balForm α β Umax Wmax ν Hn e‖ ^ 8 ≤
      (((hu_set α Umax Hn ×ˢ hu_set α Umax Hn).filter
          (fun p => frac p.1 = frac p.2)).card : ℝ) ^ 4 *
        ((w_set β Wmax).card : ℝ) ^ 4 * (e : ℝ) *
        ((((hu_set α Umax Hn).image frac) ×ˢ ((hu_set α Umax Hn).image frac) ×ˢ
          ((hu_set α Umax Hn).image frac) ×ˢ ((hu_set α Umax Hn).image frac)).filter
            (FracCountedQ e)).card *
        (((w_set β Wmax) ×ˢ (w_set β Wmax) ×ˢ (w_set β Wmax) ×ˢ (w_set β Wmax)).filter
            (Energy.IntCounted e)).card := by
  classical
  set S := hu_set α Umax Hn with hS
  set T := w_set β Wmax with hT
  set Se := S.filter (fun s => Nat.Coprime s.2 (2 * e)) with hSe
  set Te := T.filter (fun w => Nat.Coprime w (2 * e)) with hTe
  set F := S.image frac with hF
  have hcop : ∀ {x : ℕ}, Nat.Coprime x (2 * e) → Nat.Coprime x e :=
    fun h => Nat.Coprime.coprime_dvd_right (dvd_mul_left e 2) h
  rw [balForm_eq _ _ _ _ _ _ _ hν]
  rw [regroup Se Te frac (fun s => ν s.1 * α s.2) β
    (fun s w => ZMod.stdAddChar ((s.1 : ZMod e) * (s.2 : ZMod e)⁻¹ * (w : ZMod e)⁻¹))
    (fun ρ w => ZMod.stdAddChar (ratRes e ρ * (w : ZMod e)⁻¹)) ?_]
  swap
  · intro s hs w _
    rw [mem_filter] at hs
    have := mem_hu_set hs.1
    simp only [frac]
    rw [ratRes_div s.1 (by omega) (hcop hs.2)]
  refine (kc_finset (Se.image frac) Te (ratRes e) (fun w => (w : ZMod e)⁻¹) _ β).trans ?_
  -- the four factors
  have hγ : ∑ ρ ∈ Se.image frac, ‖∑ s ∈ Se.filter (fun s => frac s = ρ), ν s.1 * α s.2‖ ^ 2 ≤
      ((S ×ˢ S).filter (fun p => frac p.1 = frac p.2)).card := by
    refine (sum_norm_fiber_sq_le Se frac _ (fun s _ => ?_)).trans ?_
    · rw [norm_mul]
      nlinarith [hνb s.1, hα s.2, norm_nonneg (ν s.1), norm_nonneg (α s.2)]
    · exact_mod_cast card_le_card (filter_subset_filter _
        (product_subset_product (filter_subset _ _) (filter_subset _ _)))
  have hβ' : ∑ w ∈ Te, ‖β w‖ ^ 2 ≤ T.card := by
    calc ∑ w ∈ Te, ‖β w‖ ^ 2 ≤ ∑ _w ∈ Te, (1 : ℝ) :=
          sum_le_sum (fun w _ => by
            have := hβ w
            have h0 := norm_nonneg (β w)
            nlinarith)
      _ = Te.card := by simp
      _ ≤ T.card := by exact_mod_cast card_le_card (filter_subset _ _)
  have hEa : ((Se.image frac ×ˢ Se.image frac ×ˢ Se.image frac ×ˢ Se.image frac).filter
      (fun t => ratRes e t.1 + ratRes e t.2.1 = ratRes e t.2.2.1 + ratRes e t.2.2.2)).card ≤
      ((F ×ˢ F ×ˢ F ×ˢ F).filter (FracCountedQ e)).card := by
    apply card_le_card
    have hsub : Se.image frac ⊆ F := image_subset_image (filter_subset _ _)
    have hden : ∀ ρ ∈ Se.image frac, Nat.Coprime ρ.den e := by
      intro ρ hρ
      obtain ⟨s, hs, rfl⟩ := mem_image.1 hρ
      exact den_div_coprime _ (hcop (mem_filter.1 hs).2)
    intro t ht
    simp only [mem_filter, mem_product] at ht ⊢
    obtain ⟨⟨h1, h2, h3, h4⟩, hrel⟩ := ht
    exact ⟨⟨hsub h1, hsub h2, hsub h3, hsub h4⟩,
      ⟨hden _ h1, hden _ h2, hden _ h3, hden _ h4⟩, hrel⟩
  have hEb : ((Te ×ˢ Te ×ˢ Te ×ˢ Te).filter (fun t =>
      (t.1 : ZMod e)⁻¹ + (t.2.1 : ZMod e)⁻¹ = (t.2.2.1 : ZMod e)⁻¹ + (t.2.2.2 : ZMod e)⁻¹)).card ≤
      ((T ×ˢ T ×ˢ T ×ˢ T).filter (Energy.IntCounted e)).card := by
    apply card_le_card
    intro t ht
    simp only [mem_filter, mem_product, hTe] at ht ⊢
    obtain ⟨⟨⟨h1, c1⟩, ⟨h2, c2⟩, ⟨h3, c3⟩, ⟨h4, c4⟩⟩, hrel⟩ := ht
    exact ⟨⟨h1, h2, h3, h4⟩, hcop c1, hcop c2, hcop c3, hcop c4, hrel⟩
  have h0γ : 0 ≤ ∑ ρ ∈ Se.image frac,
      ‖∑ s ∈ Se.filter (fun s => frac s = ρ), ν s.1 * α s.2‖ ^ 2 :=
    sum_nonneg (fun _ _ => sq_nonneg _)
  have h0β : 0 ≤ ∑ w ∈ Te, ‖β w‖ ^ 2 := sum_nonneg (fun _ _ => sq_nonneg _)
  gcongr

end BalancedBox
end MobiusDeterminant
