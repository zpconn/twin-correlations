import MobiusDeterminant.Unconditional.BalancedLemmas

/-!
# Balanced boxes: energies of fractions and of reciprocals

Paper, Section 4 (Lemmas 4.1–4.3), in the form needed for `balancedBoxBound_of_BM`:

* rationals `ρ` as residues `ρ.num · \overline{ρ.den}` modulo `e`, and the divisibility
  `e ∣ Δ` for quadruples counted by the energy modulo `e` (no condition on numerators);
* the Bloom–Maynard bound for sets of fractions `h/u` with `|h| ≤ H`, `|h| ≤ u ≤ Umax`
  (via the affine map `ρ ↦ (ρ+1)/2` into `[0,1]`);
* the number of coincidences `h/u = h'/u'`, via the divisor bound;
* the number of rational solutions of `1/w₁ + 1/w₂ = 1/w₃ + 1/w₄`.
-/

open Finset

namespace MobiusDeterminant
namespace BalancedBox

/-! ## Rationals modulo `e` -/

/-- The residue `ρ.num · \overline{ρ.den}` of a rational modulo `e`. -/
noncomputable def ratRes (e : ℕ) (ρ : ℚ) : ZMod e := (ρ.num : ZMod e) * (ρ.den : ZMod e)⁻¹

/-- `Δ` of Lemma 4.3 for a quadruple of rationals, written in lowest terms. -/
def deltaQ (t : ℚ × ℚ × ℚ × ℚ) : ℤ :=
  Energy.fracDelta ((t.1.num, t.1.den), (t.2.1.num, t.2.1.den), (t.2.2.1.num, t.2.2.1.den),
    (t.2.2.2.num, t.2.2.2.den))

/-- The event "`t` is counted by the energy of `ρ ↦ ratRes e ρ`". -/
def FracCountedQ (e : ℕ) (t : ℚ × ℚ × ℚ × ℚ) : Prop :=
  (Nat.Coprime t.1.den e ∧ Nat.Coprime t.2.1.den e ∧ Nat.Coprime t.2.2.1.den e ∧
    Nat.Coprime t.2.2.2.den e) ∧
  ratRes e t.1 + ratRes e t.2.1 = ratRes e t.2.2.1 + ratRes e t.2.2.2

noncomputable instance (e : ℕ) (t : ℚ × ℚ × ℚ × ℚ) : Decidable (FracCountedQ e t) := by
  unfold FracCountedQ; exact Classical.dec _

/-- A counted quadruple satisfies `e ∣ Δ` (paper, proof of Lemma 4.3). -/
theorem dvd_deltaQ {e : ℕ} {t : ℚ × ℚ × ℚ × ℚ} (h : FracCountedQ e t) :
    (e : ℤ) ∣ deltaQ t := by
  obtain ⟨⟨c1, c2, c3, c4⟩, heq⟩ := h
  have h1 := ZMod.coe_mul_inv_eq_one _ c1
  have h2 := ZMod.coe_mul_inv_eq_one _ c2
  have h3 := ZMod.coe_mul_inv_eq_one _ c3
  have h4 := ZMod.coe_mul_inv_eq_one _ c4
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  unfold deltaQ Energy.fracDelta
  unfold ratRes at heq
  push_cast
  set u1 := (t.1.den : ZMod e)
  set u2 := (t.2.1.den : ZMod e)
  set u3 := (t.2.2.1.den : ZMod e)
  set u4 := (t.2.2.2.den : ZMod e)
  set a1 := (t.1.num : ZMod e)
  set a2 := (t.2.1.num : ZMod e)
  set a3 := (t.2.2.1.num : ZMod e)
  set a4 := (t.2.2.2.num : ZMod e)
  linear_combination (u1 * u2 * u3 * u4) * heq - (a1 * u2 * u3 * u4) * h1
    - (a2 * u1 * u3 * u4) * h2 + (a3 * u1 * u2 * u4) * h3 + (a4 * u1 * u2 * u3) * h4

/-- `Δ = 0` iff the quadruple is an exact additive coincidence in `ℚ`. -/
theorem deltaQ_eq_zero_iff (t : ℚ × ℚ × ℚ × ℚ) :
    deltaQ t = 0 ↔ t.1 + t.2.1 = t.2.2.1 + t.2.2.2 := by
  unfold deltaQ
  rw [Energy.fracDelta_eq_zero_iff (by simpa using t.1.den_pos) (by simpa using t.2.1.den_pos)
    (by simpa using t.2.2.1.den_pos) (by simpa using t.2.2.2.den_pos)]
  simp only [Rat.num_div_den]

/-- `|Δ| ≤ 4 M U³` if all numerators are at most `M` and all denominators at most `U`. -/
theorem abs_deltaQ_le {t : ℚ × ℚ × ℚ × ℚ} {M U : ℕ}
    (h1 : |t.1.num| ≤ M ∧ t.1.den ≤ U) (h2 : |t.2.1.num| ≤ M ∧ t.2.1.den ≤ U)
    (h3 : |t.2.2.1.num| ≤ M ∧ t.2.2.1.den ≤ U) (h4 : |t.2.2.2.num| ≤ M ∧ t.2.2.2.den ≤ U) :
    |deltaQ t| ≤ 4 * (M : ℤ) * (U : ℤ) ^ 3 :=
  Energy.abs_fracDelta_le h1.1 h2.1 h3.1 h4.1 h1.2 h2.2 h3.2 h4.2

/-! ## The fraction `h/u` -/

lemma div_eq_divInt (h : ℤ) (u : ℕ) : (h : ℚ) / (u : ℚ) = Rat.divInt h u := by
  rw [Rat.divInt_eq_div]; push_cast; rfl

/-- The reduced denominator of `h/u` divides `u`. -/
lemma den_div_dvd (h : ℤ) (u : ℕ) : ((h : ℚ) / (u : ℚ)).den ∣ u := by
  rw [div_eq_divInt]
  exact_mod_cast Rat.den_dvd h u

lemma den_div_le (h : ℤ) {u : ℕ} (hu : 0 < u) : ((h : ℚ) / (u : ℚ)).den ≤ u :=
  Nat.le_of_dvd hu (den_div_dvd h u)

/-- The reduced numerator of `h/u` is at most `|h|`. -/
lemma abs_num_div_le {h : ℤ} (hh : h ≠ 0) {u : ℕ} (hu : 0 < u) :
    |((h : ℚ) / (u : ℚ)).num| ≤ |h| := by
  rw [div_eq_divInt]
  have hd : (Rat.divInt h u).num ∣ h := Rat.num_dvd h (by exact_mod_cast hu.ne')
  exact Int.le_of_dvd (abs_pos.2 hh) ((abs_dvd_abs _ _).2 hd)

/-- Cross-multiplication: `h · ρ.den = ρ.num · u` for `ρ = h/u`. -/
lemma cross_mul (h : ℤ) {u : ℕ} (hu : 0 < u) :
    h * ((h : ℚ) / (u : ℚ)).den = ((h : ℚ) / (u : ℚ)).num * u := by
  set ρ := (h : ℚ) / (u : ℚ) with hρ
  have hu' : (u : ℚ) ≠ 0 := by exact_mod_cast hu.ne'
  have hden : (ρ.den : ℚ) ≠ 0 := by exact_mod_cast ρ.den_pos.ne'
  have key : (ρ.num : ℚ) / ρ.den = (h : ℚ) / u := by rw [Rat.num_div_den]
  rw [div_eq_div_iff hden hu'] at key
  exact_mod_cast key.symm

/-- `h ū ≡ ρ.num \overline{ρ.den} (mod e)` for `ρ = h/u`, `(u, e) = 1`. -/
theorem ratRes_div {e : ℕ} (h : ℤ) {u : ℕ} (hu : 0 < u) (hue : Nat.Coprime u e) :
    ratRes e ((h : ℚ) / (u : ℚ)) = (h : ZMod e) * (u : ZMod e)⁻¹ := by
  set ρ := (h : ℚ) / (u : ℚ) with hρ
  have hde : Nat.Coprime ρ.den e := Nat.Coprime.coprime_dvd_left (den_div_dvd h u) hue
  have hd := ZMod.coe_mul_inv_eq_one _ hde
  have hu1 := ZMod.coe_mul_inv_eq_one _ hue
  have eq : ((h * ρ.den : ℤ) : ZMod e) = ((ρ.num * u : ℤ) : ZMod e) := by
    rw [cross_mul h hu]
  push_cast at eq
  unfold ratRes
  linear_combination (-((u : ZMod e)⁻¹ * (ρ.den : ZMod e)⁻¹)) * eq
    + ((h : ZMod e) * (u : ZMod e)⁻¹) * hd - ((ρ.num : ZMod e) * (ρ.den : ZMod e)⁻¹) * hu1

/-- The reduced denominator of `h/u` is coprime to `e` if `u` is. -/
lemma den_div_coprime {e : ℕ} (h : ℤ) {u : ℕ} (hue : Nat.Coprime u e) :
    Nat.Coprime ((h : ℚ) / (u : ℚ)).den e :=
  Nat.Coprime.coprime_dvd_left (den_div_dvd h u) hue

/-! ## Bloom–Maynard for the fractions `h/u` -/

/-- Paper, Lemma 4.3 (first claim), from Bloom–Maynard: a finite set `F` of rationals of the
form `h/u` with `|h| ≤ H`, `|h| ≤ u ≤ Umax` has
`E₄(F) ≤ C (2Umax)^δ (2Umax (4H+1))²`.  The affine map `ρ ↦ (ρ+1)/2` (which preserves additive
energy) sends `F` into `[0,1]`, with denominators at most `2Umax` and at most `4H+1` elements
of each exact denominator. -/
theorem energy4_le_of_BM (hBM : BloomMaynardE4) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > (0 : ℝ), ∀ (H Umax : ℕ) (F : Finset ℚ), 1 ≤ Umax →
      (∀ ρ ∈ F, ∃ h : ℤ, ∃ u : ℕ, 0 < u ∧ u ≤ Umax ∧ |h| ≤ H ∧ |h| ≤ u ∧ ρ = h / u) →
      (energy4 F : ℝ) ≤ C * ((2 * Umax : ℕ) : ℝ) ^ δ *
        (((2 * Umax : ℕ) : ℝ) * ((4 * H + 1 : ℕ) : ℝ)) ^ 2 := by
  obtain ⟨C, hC, hBMC⟩ := hBM δ hδ
  refine ⟨C, hC, fun H Umax F hU hF => ?_⟩
  set φ : ℚ → ℚ := fun ρ => (ρ + 1) / 2 with hφ
  set B := F.image φ with hB
  -- properties of the image
  have key : ∀ b ∈ B, 0 ≤ b ∧ b ≤ 1 ∧ b.den ≤ 2 * Umax ∧ |2 * b.num - b.den| ≤ 2 * H := by
    intro b hb
    obtain ⟨ρ, hρ, rfl⟩ := mem_image.1 hb
    obtain ⟨h, u, hu, huU, hhH, hhu, rfl⟩ := hF ρ hρ
    have hu' : (0 : ℚ) < u := by exact_mod_cast hu
    have hhu' : |(h : ℚ)| ≤ u := by exact_mod_cast hhu
    have habs := abs_le.1 hhu'
    have hb_eq : φ ((h : ℚ) / u) = ((h + u : ℤ) : ℚ) / ((2 * u : ℕ) : ℚ) := by
      simp only [hφ]; push_cast; field_simp
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hb_eq]; push_cast
      apply div_nonneg (by linarith) (by positivity)
    · rw [hb_eq]; push_cast
      rw [div_le_one (by positivity)]; linarith
    · rw [hb_eq]
      exact (Nat.le_of_dvd (by omega) (den_div_dvd _ _)).trans (by omega)
    · set b := φ ((h : ℚ) / u) with hbdef
      have hden : (b.den : ℚ) ≠ 0 := by exact_mod_cast b.den_pos.ne'
      have e1 : (b.num : ℚ) / b.den = ((h + u : ℤ) : ℚ) / ((2 * u : ℕ) : ℚ) := by
        rw [Rat.num_div_den, hb_eq]
      rw [div_eq_div_iff hden (by positivity)] at e1
      have e2 : b.num * (2 * u : ℕ) = (h + u) * b.den := by exact_mod_cast e1
      push_cast at e2
      have e3 : (2 * b.num - b.den) * (u : ℤ) = h * b.den := by linear_combination e2
      have hdu : (b.den : ℤ) ≤ 2 * u := by
        have := (Nat.le_of_dvd (by omega) (den_div_dvd (h + u) (2 * u)))
        rw [← hb_eq] at this
        exact_mod_cast this
      have e4 : |2 * b.num - b.den| * (u : ℤ) = |h| * b.den := by
        rw [← abs_of_pos (show (0 : ℤ) < u by exact_mod_cast hu), ← abs_mul, e3, abs_mul,
          abs_of_pos (show (0 : ℤ) < b.den by exact_mod_cast b.den_pos)]
      have hupos : (0 : ℤ) < u := by exact_mod_cast hu
      have e5 : |2 * b.num - b.den| * (u : ℤ) ≤ (2 * H) * u := by
        rw [e4]
        calc |h| * (b.den : ℤ) ≤ H * (2 * u) :=
              mul_le_mul hhH hdu (by positivity) (by positivity)
          _ = (2 * H) * u := by ring
      exact le_of_mul_le_mul_right e5 hupos
  -- the Bloom–Maynard hypotheses for `B`
  have hBM1 : ∀ b ∈ B, 0 ≤ b ∧ b ≤ 1 ∧ b.den ≤ 2 * Umax := fun b hb =>
    ⟨(key b hb).1, (key b hb).2.1, (key b hb).2.2.1⟩
  have hBM2 : ∀ q : ℕ, (B.filter (fun b => b.den = q)).card ≤ 4 * H + 1 := by
    intro q
    have hcard : (Icc (-(2 * H : ℤ)) (2 * H)).card = 4 * H + 1 := by
      rw [Int.card_Icc]; omega
    rw [← hcard]
    refine card_le_card_of_injOn (fun b => 2 * b.num - q) ?_ ?_
    · intro b hb
      simp only [coe_filter, Set.mem_ofPred_eq] at hb
      simp only [coe_Icc, Set.mem_Icc]
      have := (key b hb.1).2.2.2
      rw [hb.2] at this
      exact abs_le.1 this
    · intro b hb b' hb' hbb
      simp only [coe_filter, Set.mem_ofPred_eq] at hb hb'
      have hnum : b.num = b'.num := by simp only at hbb; linarith
      exact Rat.ext hnum (hb.2.trans hb'.2.symm)
  have hE := hBMC (2 * Umax) (4 * H + 1) B (by omega) (by omega) hBM1 hBM2
  -- energy is preserved by `φ`
  have hFB : energy4 F ≤ energy4 B := by
    unfold energy4
    refine card_le_card_of_injOn (fun t => (φ t.1, φ t.2.1, φ t.2.2.1, φ t.2.2.2)) ?_ ?_
    · intro t ht
      simp only [coe_filter, Set.mem_ofPred_eq, mem_product] at ht
      simp only [coe_filter, Set.mem_ofPred_eq, mem_product]
      refine ⟨⟨mem_image_of_mem _ ht.1.1, mem_image_of_mem _ ht.1.2.1, mem_image_of_mem _ ht.1.2.2.1,
        mem_image_of_mem _ ht.1.2.2.2⟩, ?_⟩
      simp only [hφ]; linarith [ht.2]
    · intro t _ t' _ htt
      simp only [hφ, Prod.mk.injEq] at htt
      obtain ⟨h1, h2, h3, h4⟩ := htt
      exact Prod.ext (by linarith) (Prod.ext (by linarith) (Prod.ext (by linarith) (by linarith)))
  calc (energy4 F : ℝ) ≤ energy4 B := by exact_mod_cast hFB
    _ ≤ _ := by push_cast at hE ⊢; exact hE

/-! ## Coincidences `h/u = h'/u'` -/

/-- The number of pairs `(h,u), (h',u')` in `S` with `h/u = h'/u'` is at most
`∑_{(h,u')} τ(|h| u')`: given `(h, u')`, the pair `(h', u)` is determined by the divisor `u` of
`h u' = h' u`. -/
theorem card_pairs_le (H Umax : ℕ) (S : Finset (ℤ × ℕ))
    (hS : ∀ s ∈ S, s.1 ≠ 0 ∧ |s.1| ≤ H ∧ 1 ≤ s.2 ∧ s.2 ≤ Umax) :
    ((S ×ˢ S).filter (fun p => (p.1.1 : ℚ) / p.1.2 = p.2.1 / p.2.2)).card ≤
      ∑ x ∈ (Icc (-(H : ℤ)) H ×ˢ Icc 1 Umax).filter (fun x => x.1 ≠ 0),
        (x.1.natAbs * x.2).divisors.card := by
  set A := (Icc (-(H : ℤ)) H ×ˢ Icc 1 Umax).filter (fun x => x.1 ≠ 0) with hA
  set Z := (A ×ˢ Icc 1 Umax).filter (fun y => y.2 ∣ y.1.1.natAbs * y.1.2) with hZ
  have cross : ∀ p ∈ (S ×ˢ S).filter (fun p => (p.1.1 : ℚ) / p.1.2 = p.2.1 / p.2.2),
      p.1.1 * (p.2.2 : ℤ) = p.2.1 * p.1.2 := by
    intro p hp
    simp only [mem_filter, mem_product] at hp
    have h1 := (hS _ hp.1.1).2.2.1
    have h2 := (hS _ hp.1.2).2.2.1
    have e := hp.2
    rw [div_eq_div_iff (by positivity) (by positivity)] at e
    exact_mod_cast e
  have h1 : ((S ×ˢ S).filter (fun p => (p.1.1 : ℚ) / p.1.2 = p.2.1 / p.2.2)).card ≤ Z.card := by
    refine card_le_card_of_injOn (fun p => ((p.1.1, p.2.2), p.1.2)) ?_ ?_
    · intro p hp
      have hc := cross p hp
      simp only [coe_filter, mem_product, Set.mem_ofPred_eq] at hp
      obtain ⟨hp1, hp2, hp3, hp4⟩ := hS _ hp.1.1
      obtain ⟨hq1, hq2, hq3, hq4⟩ := hS _ hp.1.2
      simp only [hZ, hA, coe_filter, mem_product, mem_filter, mem_Icc, Set.mem_ofPred_eq]
      refine ⟨⟨⟨⟨abs_le.1 hp2, hq3, hq4⟩, hp1⟩, hp3, hp4⟩, ?_⟩
      have : (p.1.2 : ℤ) ∣ p.1.1 * p.2.2 := ⟨p.2.1, by rw [hc]; ring⟩
      have := Int.natAbs_dvd_natAbs.2 this
      simpa [Int.natAbs_mul] using this
    · intro p hp p' hp' hpp
      have hc := cross p hp
      have hc' := cross p' hp'
      simp only [Prod.mk.injEq] at hpp
      obtain ⟨⟨e1, e2⟩, e3⟩ := hpp
      simp only [coe_filter, mem_product, Set.mem_ofPred_eq] at hp
      have hpos := (hS _ hp.1.1).2.2.1
      have e4 : p.2.1 = p'.2.1 := by
        have : p.2.1 * (p.1.2 : ℤ) = p'.2.1 * p.1.2 := by
          rw [← hc, e1, e2, hc', e3]
        exact mul_right_cancel₀ (by positivity) this
      exact Prod.ext (Prod.ext e1 e3) (Prod.ext e4 e2)
  have h2 : Z.card ≤ ∑ x ∈ A, (x.1.natAbs * x.2).divisors.card := by
    rw [hZ, card_filter, sum_product]
    refine sum_le_sum (fun x hx => ?_)
    rw [← card_filter]
    apply card_le_card
    intro u hu
    simp only [mem_filter, mem_Icc] at hu
    simp only [hA, mem_filter, mem_product, mem_Icc] at hx
    rw [Nat.mem_divisors]
    refine ⟨hu.2, ?_⟩
    have : x.1.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hx.2
    have : x.2 ≠ 0 := by omega
    positivity
  exact h1.trans h2

/-! ## Rational solutions of `1/w₁ + 1/w₂ = 1/w₃ + 1/w₄` -/

/-- Finset form of `Energy.card_reps_le`: the pairs `(x,y)` of positive integers with
`b(x+y) = axy` number at most `τ(b²)`. -/
theorem card_reps_finset (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (A : Finset (ℕ × ℕ))
    (hA : ∀ p ∈ A, 0 < p.1 ∧ 0 < p.2 ∧ b * (p.1 + p.2) = a * p.1 * p.2) :
    A.card ≤ (b ^ 2).divisors.card := by
  have key : ∀ x y : ℕ, 0 < x → 0 < y → b * (x + y) = a * x * y →
      b < a * x ∧ ((a * x - b : ℕ) : ℤ) * ((a * y - b : ℕ) : ℤ) = (b : ℤ) ^ 2 ∧ b < a * y := by
    intro x y hx hy h
    have hz : (b : ℤ) * (x + y) = a * x * y := by exact_mod_cast h
    have hy' : (0 : ℤ) < y := by exact_mod_cast hy
    have hx' : (0 : ℤ) < x := by exact_mod_cast hx
    have hb' : (0 : ℤ) < b := by exact_mod_cast hb
    have hax : b < a * x := by
      by_contra hc
      rw [not_lt] at hc
      have : (a : ℤ) * x ≤ b := by exact_mod_cast hc
      nlinarith
    have hay : b < a * y := by
      by_contra hc
      rw [not_lt] at hc
      have : (a : ℤ) * y ≤ b := by exact_mod_cast hc
      nlinarith
    refine ⟨hax, ?_, hay⟩
    push_cast [hax.le, hay.le]
    exact Energy.rep_identity hz
  refine card_le_card_of_injOn (fun p : ℕ × ℕ => a * p.1 - b) ?_ ?_
  · intro p hp
    obtain ⟨hx, hy, h⟩ := hA p hp
    obtain ⟨hax, hid, hay⟩ := key p.1 p.2 hx hy h
    rw [Finset.mem_coe, Nat.mem_divisors]
    refine ⟨?_, by positivity⟩
    have : ((a * p.1 - b : ℕ) : ℤ) ∣ ((b ^ 2 : ℕ) : ℤ) := ⟨_, by push_cast; exact hid.symm⟩
    exact_mod_cast this
  · intro p hp p' hp' heq
    obtain ⟨hx, hy, h⟩ := hA p hp
    obtain ⟨hx', hy', h'⟩ := hA p' hp'
    simp only at heq
    obtain ⟨hax, hid, hay⟩ := key p.1 p.2 hx hy h
    obtain ⟨hax', hid', hay'⟩ := key p'.1 p'.2 hx' hy' h'
    have hxx : p.1 = p'.1 := by
      have : a * p.1 = a * p'.1 := by omega
      exact Nat.eq_of_mul_eq_mul_left ha this
    have hne : ((a * p.1 - b : ℕ) : ℤ) ≠ 0 := by
      have : 0 < a * p.1 - b := by omega
      positivity
    have : ((a * p.2 - b : ℕ) : ℤ) = ((a * p'.2 - b : ℕ) : ℤ) := by
      rw [hxx] at hne hid
      exact mul_left_cancel₀ hne (hid.trans hid'.symm)
    have hyy : a * p.2 = a * p'.2 := by
      have := Int.ofNat.inj this
      omega
    exact Prod.ext hxx (Nat.eq_of_mul_eq_mul_left ha hyy)

/-- Paper, proof of Lemma 4.1: the quadruples in `T⁴` (`T ⊂ ℕ_{>0}`) with `Δ = 0`, i.e. with
`1/w₁ + 1/w₂ = 1/w₃ + 1/w₄`, number at most `∑_{w₁,w₂} τ((w₁w₂)²)`. -/
theorem card_intDelta_zero_le (T : Finset ℕ) (hT : ∀ w ∈ T, 0 < w) :
    ((T ×ˢ T ×ˢ T ×ˢ T).filter (fun t => Energy.intDelta t = 0)).card ≤
      ∑ p ∈ T ×ˢ T, ((p.1 * p.2) ^ 2).divisors.card := by
  rw [card_filter]
  simp only [sum_product]
  refine sum_le_sum (fun w1 hw1 => sum_le_sum (fun w2 hw2 => ?_))
  have hsum : (∑ x ∈ T, ∑ y ∈ T, if Energy.intDelta (w1, w2, x, y) = 0 then 1 else 0) =
      ((T ×ˢ T).filter (fun p => Energy.intDelta (w1, w2, p.1, p.2) = 0)).card := by
    rw [card_filter, sum_product]
  rw [hsum]
  have h1 := hT w1 hw1
  have h2 := hT w2 hw2
  refine card_reps_finset (w1 + w2) (w1 * w2) (by omega) (by positivity) _ (fun p hp => ?_)
  simp only [mem_filter, mem_product] at hp
  refine ⟨hT _ hp.1.1, hT _ hp.1.2, ?_⟩
  have e := hp.2
  unfold Energy.intDelta at e
  simp only at e
  have : ((w1 * w2 * (p.1 + p.2) : ℕ) : ℤ) = (((w1 + w2) * p.1 * p.2 : ℕ) : ℤ) := by
    push_cast; linarith
  exact_mod_cast this

end BalancedBox
end MobiusDeterminant
