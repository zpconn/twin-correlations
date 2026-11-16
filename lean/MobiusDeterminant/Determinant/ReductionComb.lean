import MobiusDeterminant.Determinant.Defs

/-!
# Reduction of Theorem 1.3: combinatorial identities

* `detSum_two_eq`  : for `κ = 2`, `S_κ` as a sum over odd `d, e` (at the enlarged scales
  `3D/2`, `3E/2`) and odd `n ≤ 8X` with `d ∣ n`, `e ∣ n + 2` (`n = ad`, `n + 2 = be`);
* `zeroMode_two_eq` : the zero mode `S_2⁰` as `∑_{d,e odd} μ(d)μ(e) (ϱ(d,e)/2) X δ Φ(0; δ, ε)`;
* `detSum_neg`, `zeroMode_neg` : the case `κ = -2` is the case `κ = 2` for the permuted weight
  `W'(α,β,δ,ε) = W(β,α,ε,δ)` with `A` and `B` interchanged;
* crude bounds `‖S_κ‖ ≤ 16 X² sup‖W‖`, `‖S_κ⁰‖ ≤ 2 X² sup‖W‖`.
-/

open Finset Real MeasureTheory
open scoped ArithmeticFunction.Moebius

namespace MobiusDeterminant.Determinant.Reduction

/-! ## Generalities -/

/-- Two sums agree if the summands agree on the common part and vanish elsewhere. -/
lemma sum_congr_supp {ι M : Type*} [AddCommMonoid M] [DecidableEq ι] {s t : Finset ι}
    {f g : ι → M} (h1 : ∀ i ∈ s, i ∉ t → f i = 0) (h2 : ∀ i ∈ t, i ∉ s → g i = 0)
    (h3 : ∀ i ∈ s, i ∈ t → f i = g i) : ∑ i ∈ s, f i = ∑ i ∈ t, g i := by
  rw [← Finset.sum_subset (Finset.inter_subset_left : s ∩ t ⊆ s)
      (fun i hi hni => h1 i hi (fun ht => hni (Finset.mem_inter.mpr ⟨hi, ht⟩))),
    ← Finset.sum_subset (Finset.inter_subset_right : s ∩ t ⊆ t)
      (fun i hi hni => h2 i hi (fun hs => hni (Finset.mem_inter.mpr ⟨hs, hi⟩)))]
  exact Finset.sum_congr rfl (fun i hi => h3 i (Finset.mem_inter.mp hi).1
    (Finset.mem_inter.mp hi).2)

lemma sum_filter_filter {α β M : Type*} [AddCommMonoid M] {s : Finset α} {t : Finset β}
    (p : α → Prop) (q : α → β → Prop) [DecidablePred p] [∀ a, DecidablePred (q a)]
    (f : α → β → M) :
    ∑ a ∈ s.filter p, ∑ b ∈ t.filter (q a), f a b =
      ∑ a ∈ s, ∑ b ∈ t, if p a ∧ q a b then f a b else 0 := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_filter]
  by_cases h : p a <;> simp [h]

lemma W_eq_zero_1 {W : ℝ × ℝ × ℝ × ℝ → ℂ} (hW : SmoothWeight W) {a b c d : ℝ}
    (h : a ∉ Set.Icc (1 : ℝ) 2) : W (a, b, c, d) = 0 := by
  by_contra h'; exact h (hW.2 _ h').1

lemma W_eq_zero_2 {W : ℝ × ℝ × ℝ × ℝ → ℂ} (hW : SmoothWeight W) {a b c d : ℝ}
    (h : b ∉ Set.Icc (1 : ℝ) 2) : W (a, b, c, d) = 0 := by
  by_contra h'; exact h (hW.2 _ h').2.1

lemma W_eq_zero_3 {W : ℝ × ℝ × ℝ × ℝ → ℂ} (hW : SmoothWeight W) {a b c d : ℝ}
    (h : c ∉ Set.Icc (1 : ℝ) 2) : W (a, b, c, d) = 0 := by
  by_contra h'; exact h (hW.2 _ h').2.2.1

lemma W_eq_zero_4 {W : ℝ × ℝ × ℝ × ℝ → ℂ} (hW : SmoothWeight W) {a b c d : ℝ}
    (h : d ∉ Set.Icc (1 : ℝ) 2) : W (a, b, c, d) = 0 := by
  by_contra h'; exact h (hW.2 _ h').2.2.2

lemma Phi0_eq_zero_3 {W : ℝ × ℝ × ℝ × ℝ → ℂ} (hW : SmoothWeight W) (κ : ℤ) (X : ℝ)
    {δ ε : ℝ} (h : δ ∉ Set.Icc (1 : ℝ) 2) : Phi0 κ W X δ ε = 0 := by
  unfold Phi0
  simp_rw [W_eq_zero_3 hW h, integral_zero]

lemma Phi0_eq_zero_4 {W : ℝ × ℝ × ℝ × ℝ → ℂ} (hW : SmoothWeight W) (κ : ℤ) (X : ℝ)
    {δ ε : ℝ} (h : ε ∉ Set.Icc (1 : ℝ) 2) : Phi0 κ W X δ ε = 0 := by
  unfold Phi0
  simp_rw [W_eq_zero_4 hW h, integral_zero]

/-- `d > ⌊2D⌋₊` forces `d/D > 2`. -/
lemma not_mem_of_floor_lt {D : ℝ} (hD : 0 < D) {d : ℕ} (hd : ⌊2 * D⌋₊ < d) :
    (d : ℝ) / D ∉ Set.Icc (1 : ℝ) 2 := by
  intro h
  have h2 := h.2
  rw [div_le_iff₀ hD] at h2
  have : d ≤ ⌊2 * D⌋₊ := Nat.le_floor (by linarith)
  omega

lemma le_floor_of_div_le {D : ℝ} (hD : 0 < D) {d : ℕ} (h : (d : ℝ) / D ≤ 2) :
    d ≤ ⌊2 * D⌋₊ := by
  rw [div_le_iff₀ hD] at h
  exact Nat.le_floor (by linarith)

/-! ## `κ = 2`: the determinant sum as a divisor-pair sum -/

/-- For fixed odd `d, e`, the solutions `(a,b)` of `be - ad = 2` correspond to the odd `n`
with `d ∣ n`, `e ∣ n + 2` (`n = ad`). -/
lemma inner_ab_eq {W : ℝ × ℝ × ℝ × ℝ → ℂ} (hW : SmoothWeight W) {X A B : ℝ} (hX : 0 < X)
    (hA : 0 < A) (hB : 0 < B) {d e : ℕ} (hd : 1 ≤ d) (he : 1 ≤ e) (hdo : Odd d) (heo : Odd e) :
    ∑ a ∈ Icc 1 ⌊2 * A⌋₊, ∑ b ∈ Icc 1 ⌊2 * B⌋₊,
      (if Odd a ∧ Odd b ∧ Odd d ∧ Odd e ∧ (b : ℤ) * e - (a : ℤ) * d = 2 then
        (μ d : ℂ) * (μ e : ℂ) * W ((a : ℝ) / A, (b : ℝ) / B, (d : ℝ) / (X / A), (e : ℝ) / (X / B))
      else 0) =
    (μ d : ℂ) * (μ e : ℂ) * ∑ n ∈ (Icc 1 ⌊8 * X⌋₊).filter (fun n => Odd n ∧ d ∣ n ∧ e ∣ n + 2),
      W ((n : ℝ) / d / A, ((n : ℝ) + 2) / e / B, (d : ℝ) / (X / A), (e : ℝ) / (X / B)) := by
  rw [← Finset.sum_product', Finset.mul_sum]
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have he0 : (0 : ℝ) < e := by exact_mod_cast he
  have hDA : 0 < X / A := div_pos hX hA
  refine Finset.sum_bij_ne_zero (fun p _ _ => p.1 * d) ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ hab hne
    obtain ⟨⟨hao, hbo, -, -, hbe⟩, hv⟩ := ite_ne_right_iff.mp hne
    have hW0 := right_ne_zero_of_mul hv
    obtain ⟨s1, -, s3, -⟩ := hW.2 _ hW0
    simp only [Finset.mem_product, Finset.mem_Icc] at hab
    simp only [Finset.mem_filter, Finset.mem_Icc]
    have hbe' : (a * d + 2 : ℤ) = b * e := by linarith
    have hbe'' : a * d + 2 = b * e := by exact_mod_cast hbe'
    refine ⟨⟨by nlinarith [hab.1.1], ?_⟩, Nat.odd_mul.mpr ⟨hao, hdo⟩, dvd_mul_left _ _,
      ⟨b, by rw [hbe'', mul_comm]⟩⟩
    apply Nat.le_floor
    have h1 : (a : ℝ) ≤ 2 * A := by have := s1.2; rwa [div_le_iff₀ hA] at this
    have h2 : (d : ℝ) ≤ 2 * (X / A) := by have := s3.2; rwa [div_le_iff₀ hDA] at this
    have h3 : (a : ℝ) * d ≤ 2 * A * (2 * (X / A)) :=
      mul_le_mul h1 h2 (by positivity) (by positivity)
    have h4 : 2 * A * (2 * (X / A)) = 4 * X := by field_simp; ring
    push_cast
    linarith
  · rintro ⟨a₁, b₁⟩ h₁ hn₁ ⟨a₂, b₂⟩ h₂ hn₂ heq
    obtain ⟨⟨-, -, -, -, hbe₁⟩, -⟩ := ite_ne_right_iff.mp hn₁
    obtain ⟨⟨-, -, -, -, hbe₂⟩, -⟩ := ite_ne_right_iff.mp hn₂
    simp only at heq
    have ha : a₁ = a₂ := Nat.eq_of_mul_eq_mul_right (by omega) heq
    subst ha
    have hb : (b₁ : ℤ) * e = b₂ * e := by linarith
    have hb' : b₁ * e = b₂ * e := by exact_mod_cast hb
    rw [Nat.eq_of_mul_eq_mul_right (by omega) hb']
  · intro n hn hne
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, -⟩, hno, ⟨a, rfl⟩, ⟨b, hb⟩⟩ := hn
    have hW0 := right_ne_zero_of_mul hne
    obtain ⟨s1, s2, -, -⟩ := hW.2 _ hW0
    have ha : ((d * a : ℕ) : ℝ) / d = a := by push_cast; field_simp
    have hb' : (((d * a : ℕ) : ℝ) + 2) / e = b := by
      rw [div_eq_iff he0.ne']; exact_mod_cast (by rw [hb]; ring : d * a + 2 = b * e)
    rw [ha] at s1
    rw [hb'] at s2
    have ha1 : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with h | h
      · subst h; simp at hn1
      · exact h
    have hb1 : 1 ≤ b := by
      rcases Nat.eq_zero_or_pos b with h | h
      · subst h; simp at hb
      · exact h
    have hao : Odd a := (Nat.odd_mul.mp hno).2
    have hbo : Odd b := by
      have : Odd (e * b) := by rw [← hb]; exact hno.add_even even_two
      exact (Nat.odd_mul.mp this).2
    refine ⟨(a, b), ?_, ?_, by simp [mul_comm]⟩
    · simp only [Finset.mem_product, Finset.mem_Icc]
      exact ⟨⟨ha1, le_floor_of_div_le hA s1.2⟩, ⟨hb1, le_floor_of_div_le hB s2.2⟩⟩
    · have hbe : (b : ℤ) * e - (a : ℤ) * d = 2 := by
        have : (d * a + 2 : ℤ) = e * b := by exact_mod_cast hb
        linarith
      rw [ite_eq_left ⟨hao, hbo, hdo, heo, hbe⟩]
      rwa [ha, hb'] at hne
  · rintro ⟨a, b⟩ hab hne
    obtain ⟨⟨hao, hbo, -, -, hbe⟩, -⟩ := ite_ne_right_iff.mp hne
    rw [ite_eq_left ⟨hao, hbo, hdo, heo, hbe⟩]
    have hbe' : ((a * d : ℕ) : ℝ) + 2 = b * e := by
      have : (a * d + 2 : ℤ) = b * e := by linarith
      exact_mod_cast this
    have ha : ((a * d : ℕ) : ℝ) / d = a := by push_cast; field_simp
    have hb' : (((a * d : ℕ) : ℝ) + 2) / e = b := by rw [hbe']; field_simp
    simp only
    rw [ha, hb']

/-- **`S_2` as a divisor-pair sum** at the scales `D' = 3D/2`, `E' = 3E/2`. -/
theorem detSum_two_eq {W : ℝ × ℝ × ℝ × ℝ → ℂ} (hW : SmoothWeight W) {X A B : ℝ} (hX : 0 < X)
    (hA : 0 < A) (hB : 0 < B) :
    detSum 2 W A B X =
      ∑ d ∈ (Icc 1 ⌊2 * (3 / 2 * (X / A))⌋₊).filter Odd,
        ∑ e ∈ (Icc 1 ⌊2 * (3 / 2 * (X / B))⌋₊).filter Odd,
          (μ d : ℂ) * (μ e : ℂ) *
            ∑ n ∈ (Icc 1 ⌊8 * X⌋₊).filter (fun n => Odd n ∧ d ∣ n ∧ e ∣ n + 2),
              W ((n : ℝ) / d / A, ((n : ℝ) + 2) / e / B, (d : ℝ) / (X / A),
                (e : ℝ) / (X / B)) := by
  have hDA : 0 < X / A := div_pos hX hA
  have hEB : 0 < X / B := div_pos hX hB
  unfold detSum
  -- move the `d, e` sums outside
  have step1 :
      ∑ a ∈ Icc 1 ⌊2 * A⌋₊, ∑ b ∈ Icc 1 ⌊2 * B⌋₊, ∑ d ∈ Icc 1 ⌊2 * (X / A)⌋₊,
        ∑ e ∈ Icc 1 ⌊2 * (X / B)⌋₊,
          (if Odd a ∧ Odd b ∧ Odd d ∧ Odd e ∧ (b : ℤ) * e - (a : ℤ) * d = 2 then
            (μ d : ℂ) * (μ e : ℂ) *
              W ((a : ℝ) / A, (b : ℝ) / B, (d : ℝ) / (X / A), (e : ℝ) / (X / B))
          else 0) =
      ∑ d ∈ Icc 1 ⌊2 * (X / A)⌋₊, ∑ e ∈ Icc 1 ⌊2 * (X / B)⌋₊,
        ∑ a ∈ Icc 1 ⌊2 * A⌋₊, ∑ b ∈ Icc 1 ⌊2 * B⌋₊,
          (if Odd a ∧ Odd b ∧ Odd d ∧ Odd e ∧ (b : ℤ) * e - (a : ℤ) * d = 2 then
            (μ d : ℂ) * (μ e : ℂ) *
              W ((a : ℝ) / A, (b : ℝ) / B, (d : ℝ) / (X / A), (e : ℝ) / (X / B))
          else 0) := by
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm), Finset.sum_comm]
  rw [step1]
  set T : ℕ → ℕ → ℂ := fun d e => (μ d : ℂ) * (μ e : ℂ) *
    ∑ n ∈ (Icc 1 ⌊8 * X⌋₊).filter (fun n => Odd n ∧ d ∣ n ∧ e ∣ n + 2),
      W ((n : ℝ) / d / A, ((n : ℝ) + 2) / e / B, (d : ℝ) / (X / A), (e : ℝ) / (X / B)) with hT
  have hTd : ∀ d e : ℕ, ⌊2 * (X / A)⌋₊ < d → T d e = 0 := by
    intro d e hd
    simp only [hT]
    rw [Finset.sum_eq_zero (fun n _ => W_eq_zero_3 hW (not_mem_of_floor_lt hDA hd)), mul_zero]
  have hTe : ∀ d e : ℕ, ⌊2 * (X / B)⌋₊ < e → T d e = 0 := by
    intro d e he
    simp only [hT]
    rw [Finset.sum_eq_zero (fun n _ => W_eq_zero_4 hW (not_mem_of_floor_lt hEB he)), mul_zero]
  have hfl1 : ⌊2 * (X / A)⌋₊ ≤ ⌊2 * (3 / 2 * (X / A))⌋₊ := Nat.floor_mono (by linarith)
  have hfl2 : ⌊2 * (X / B)⌋₊ ≤ ⌊2 * (3 / 2 * (X / B))⌋₊ := Nat.floor_mono (by linarith)
  refine sum_congr_supp ?_ ?_ ?_
  · intro d hd hnd
    have hdo : ¬ Odd d := by
      intro h; apply hnd
      simp only [Finset.mem_filter, Finset.mem_Icc] at hd ⊢
      exact ⟨⟨hd.1, hd.2.trans hfl1⟩, h⟩
    refine Finset.sum_eq_zero (fun e _ => Finset.sum_eq_zero (fun a _ =>
      Finset.sum_eq_zero (fun b _ => ?_)))
    rw [ite_eq_right (by tauto)]
  · intro d hd hnd
    simp only [Finset.mem_filter, Finset.mem_Icc] at hd hnd
    exact Finset.sum_eq_zero (fun e _ => hTd d e (by omega))
  · intro d hd hd'
    simp only [Finset.mem_filter, Finset.mem_Icc] at hd'
    obtain ⟨⟨hd1, -⟩, hdo⟩ := hd'
    refine sum_congr_supp ?_ ?_ ?_
    · intro e he hne
      have heo : ¬ Odd e := by
        intro h; apply hne
        simp only [Finset.mem_filter, Finset.mem_Icc] at he ⊢
        exact ⟨⟨he.1, he.2.trans hfl2⟩, h⟩
      refine Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun b _ => ?_))
      rw [ite_eq_right (by tauto)]
    · intro e he hne
      simp only [Finset.mem_filter, Finset.mem_Icc] at he hne
      exact hTe d e (by omega)
    · intro e he he'
      simp only [Finset.mem_filter, Finset.mem_Icc] at he'
      exact inner_ab_eq hW hX hA hB hd1 he'.1.1 hdo he'.2

/-! ## `κ = 2`: the zero mode -/

/-- For odd coprime `d, e`, `ϱ(d,e)/2 · X · d/D = A/(2e)`. -/
lemma dens_mul_eq {X A : ℝ} (hX : 0 < X) (hA : 0 < A) {d e : ℕ} (hd : 1 ≤ d) (he : 1 ≤ e)
    (hde : Nat.Coprime d e) :
    dens d e / 2 * (X * ((d : ℝ) / (X / A))) = A / (2 * e) := by
  unfold dens
  rw [ite_eq_left (by rw [hde.gcd_eq_one]; exact one_dvd 2), hde.lcm_eq_mul]
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have he0 : (0 : ℝ) < e := by exact_mod_cast he
  push_cast
  field_simp

/-- For odd `d` and `¬ (d, 2e) = 1`, `ϱ(d,e) = 0`. -/
lemma dens_eq_zero_of_not_coprime {d e : ℕ} (hdo : Odd d) (h : ¬ Nat.Coprime d (2 * e)) :
    dens d e = 0 := by
  unfold dens
  rw [ite_eq_right]
  intro hdvd
  apply h
  rw [Nat.coprime_mul_iff_right]
  refine ⟨Nat.coprime_two_right.mpr hdo, ?_⟩
  have hodd : Odd (Nat.gcd d e) := hdo.of_dvd_nat (Nat.gcd_dvd_left d e)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exact h1
  · rw [h2] at hodd; exact absurd hodd (by decide)

/-- **The zero mode `S_2⁰`** as a sum over odd `d, e` at the scales `3D/2`, `3E/2`. -/
theorem zeroMode_two_eq {W : ℝ × ℝ × ℝ × ℝ → ℂ} (hW : SmoothWeight W) {X A B : ℝ}
    (hX : 0 < X) (hA : 0 < A) (hB : 0 < B) :
    ∑ d ∈ (Icc 1 ⌊2 * (3 / 2 * (X / A))⌋₊).filter Odd,
      ∑ e ∈ (Icc 1 ⌊2 * (3 / 2 * (X / B))⌋₊).filter Odd,
        (μ d : ℂ) * (μ e : ℂ) * ((dens d e / 2 * (X * ((d : ℝ) / (X / A))) : ℝ) : ℂ) *
          Phi0 2 W X ((d : ℝ) / (X / A)) ((e : ℝ) / (X / B)) = zeroMode 2 W A B X := by
  have hDA : 0 < X / A := div_pos hX hA
  have hEB : 0 < X / B := div_pos hX hB
  have hfl1 : ⌊2 * (X / A)⌋₊ ≤ ⌊2 * (3 / 2 * (X / A))⌋₊ := Nat.floor_mono (by linarith)
  have hfl2 : ⌊2 * (X / B)⌋₊ ≤ ⌊2 * (3 / 2 * (X / B))⌋₊ := Nat.floor_mono (by linarith)
  rw [Finset.sum_comm]
  unfold zeroMode
  refine sum_congr_supp ?_ ?_ ?_
  · intro e he hne
    simp only [Finset.mem_filter, Finset.mem_Icc] at he hne
    have : ⌊2 * (X / B)⌋₊ < e := by
      by_contra h; exact hne ⟨⟨he.1.1, by omega⟩, he.2⟩
    refine Finset.sum_eq_zero (fun d _ => ?_)
    rw [Phi0_eq_zero_4 hW _ _ (not_mem_of_floor_lt hEB this), mul_zero]
  · intro e he hne
    simp only [Finset.mem_filter, Finset.mem_Icc] at he hne
    exact absurd ⟨⟨he.1.1, he.1.2.trans hfl2⟩, he.2⟩ hne
  · intro e he he'
    simp only [Finset.mem_filter, Finset.mem_Icc] at he he'
    refine sum_congr_supp ?_ ?_ ?_
    · intro d hd hnd
      simp only [Finset.mem_filter, Finset.mem_Icc] at hd hnd
      by_cases hle : d ≤ ⌊2 * (X / A)⌋₊
      · have hnc : ¬ Nat.Coprime d (2 * e) := fun h => hnd ⟨⟨hd.1.1, hle⟩, h⟩
        rw [dens_eq_zero_of_not_coprime hd.2 hnc]
        simp
      · rw [Phi0_eq_zero_3 hW _ _ (not_mem_of_floor_lt hDA (by omega))]
        simp
    · intro d hd hnd
      simp only [Finset.mem_filter, Finset.mem_Icc] at hd hnd
      exfalso
      apply hnd
      refine ⟨⟨hd.1.1, hd.1.2.trans hfl1⟩, ?_⟩
      have := (Nat.coprime_mul_iff_right.mp hd.2).1
      exact Nat.coprime_two_right.mp this
    · intro d hd hd'
      simp only [Finset.mem_filter, Finset.mem_Icc] at hd hd'
      have hde : Nat.Coprime d e := (Nat.coprime_mul_iff_right.mp hd'.2).2
      rw [dens_mul_eq hX hA hd.1.1 he.1.1 hde]
      ring

/-! ## `κ = -2` -/

/-- The permuted weight `W'(α,β,δ,ε) = W(β,α,ε,δ)`. -/
def swapW (W : ℝ × ℝ × ℝ × ℝ → ℂ) : ℝ × ℝ × ℝ × ℝ → ℂ :=
  fun p => W (p.2.1, p.1, p.2.2.2, p.2.2.1)

lemma smoothWeight_swapW {W : ℝ × ℝ × ℝ × ℝ → ℂ} (hW : SmoothWeight W) :
    SmoothWeight (swapW W) := by
  refine ⟨?_, fun x hx => ?_⟩
  · unfold swapW
    exact hW.1.comp (by fun_prop)
  · obtain ⟨h1, h2, h3, h4⟩ := hW.2 _ hx
    exact ⟨h2, h1, h4, h3⟩

theorem detSum_neg (W : ℝ × ℝ × ℝ × ℝ → ℂ) (A B X : ℝ) :
    detSum (-2) W A B X = detSum 2 (swapW W) B A X := by
  unfold detSum
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun a _ => ?_))
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun d _ => ?_))
  have hiff : (Odd a ∧ Odd b ∧ Odd d ∧ Odd e ∧ (b : ℤ) * e - (a : ℤ) * d = -2) ↔
      (Odd b ∧ Odd a ∧ Odd e ∧ Odd d ∧ (a : ℤ) * d - (b : ℤ) * e = 2) := by
    constructor
    · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨h2, h1, h4, h3, by linarith⟩
    · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨h2, h1, h4, h3, by linarith⟩
  by_cases h : Odd a ∧ Odd b ∧ Odd d ∧ Odd e ∧ (b : ℤ) * e - (a : ℤ) * d = -2
  · rw [ite_eq_left h, ite_eq_left (hiff.mp h)]
    simp only [swapW]
    ring
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (hiff.mpr h'))]

/-- `Φ'(0; ε, δ) = (δ/ε) Φ(0; δ, ε)` for the permuted weight (substitution
`α ↦ αε/δ + 2/(δX)`). -/
lemma Phi0_swap (W : ℝ × ℝ × ℝ × ℝ → ℂ) {X δ ε : ℝ} (hX : X ≠ 0) (hδ : 0 < δ) (hε : 0 < ε) :
    Phi0 2 (swapW W) X ε δ = ((δ / ε : ℝ) : ℂ) * Phi0 (-2) W X δ ε := by
  unfold Phi0 swapW
  simp only
  set f : ℝ → ℂ := fun β => W (β, β * δ / ε + ((-2 : ℤ) : ℝ) / (ε * X), δ, ε) with hf
  have hpt : ∀ α : ℝ, W (α * ε / δ + ((2 : ℤ) : ℝ) / (δ * X), α, δ, ε) =
      (fun y => f (y + 2 / (δ * X))) (ε / δ * α) := by
    intro α
    simp only [hf]
    congr 1
    refine Prod.ext ?_ (Prod.ext ?_ rfl)
    · push_cast; ring
    · simp only
      push_cast
      field_simp
      ring
  simp_rw [hpt]
  rw [Measure.integral_comp_mul_left (fun y => f (y + 2 / (δ * X))) (ε / δ),
    integral_add_right_eq_self f (2 / (δ * X))]
  rw [inv_div, abs_of_pos (div_pos hδ hε), Complex.real_smul]

theorem zeroMode_neg {W : ℝ × ℝ × ℝ × ℝ → ℂ} {X A B : ℝ} (hX : 0 < X) (hA : 0 < A)
    (hB : 0 < B) : zeroMode (-2) W A B X = zeroMode 2 (swapW W) B A X := by
  unfold zeroMode
  rw [sum_filter_filter, sum_filter_filter, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d hd => Finset.sum_congr rfl (fun e he => ?_))
  simp only [Finset.mem_Icc] at hd he
  have hiff : (Odd e ∧ Nat.Coprime d (2 * e)) ↔ (Odd d ∧ Nat.Coprime e (2 * d)) := by
    rw [Nat.coprime_mul_iff_right, Nat.coprime_mul_iff_right, Nat.coprime_two_right,
      Nat.coprime_two_right, Nat.coprime_comm (m := e)]
    tauto
  by_cases h : Odd e ∧ Nat.Coprime d (2 * e)
  · rw [ite_eq_left h, ite_eq_left (hiff.mp h)]
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.1
    have he0 : (0 : ℝ) < e := by exact_mod_cast he.1
    rw [Phi0_swap W hX.ne' (div_pos hd0 (div_pos hX hA)) (div_pos he0 (div_pos hX hB))]
    have hc : (B / (2 * d) * (((d : ℝ) / (X / A)) / ((e : ℝ) / (X / B))) : ℝ) = A / (2 * e) := by
      field_simp
    rw [← hc]
    push_cast
    ring
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (hiff.mpr h'))]

/-! ## Crude bounds -/

lemma exists_bound_W {W : ℝ × ℝ × ℝ × ℝ → ℂ} (hW : SmoothWeight W) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p, ‖W p‖ ≤ M := by
  have hc : HasCompactSupport W := by
    refine HasCompactSupport.intro ((isCompact_Icc (a := (1 : ℝ)) (b := 2)).prod
      ((isCompact_Icc (a := (1 : ℝ)) (b := 2)).prod ((isCompact_Icc (a := (1 : ℝ)) (b := 2)).prod
        (isCompact_Icc (a := (1 : ℝ)) (b := 2))))) (fun x hx => ?_)
    by_contra h
    obtain ⟨h1, h2, h3, h4⟩ := hW.2 x h
    exact hx ⟨h1, h2, h3, h4⟩
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuous hW.1.continuous
  exact ⟨max M 0, le_max_right _ _, fun p => (hM p).trans (le_max_left _ _)⟩

lemma norm_Phi0_le {W : ℝ × ℝ × ℝ × ℝ → ℂ} (hW : SmoothWeight W) {M : ℝ}
    (hM : ∀ p, ‖W p‖ ≤ M) (κ : ℤ) (X δ ε : ℝ) : ‖Phi0 κ W X δ ε‖ ≤ M := by
  unfold Phi0
  have hint : Integrable (Set.indicator (Set.Icc (1 : ℝ) 2) (fun _ => M)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp))
  refine (norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall (fun α => ?_))).trans ?_
  · by_cases hα : α ∈ Set.Icc (1 : ℝ) 2
    · rw [Set.indicator_of_mem hα]; exact hM _
    · rw [Set.indicator_of_notMem hα, W_eq_zero_1 hW hα, norm_zero]
  · rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le (by norm_num)]
    simp only [smul_eq_mul]
    norm_num

lemma norm_sum_le_card {ι : Type*} {s : Finset ι} {f : ι → ℂ} {x M : ℝ} (hM : 0 ≤ M)
    (hs : (s.card : ℝ) ≤ x) (h : ∀ i ∈ s, ‖f i‖ ≤ M) : ‖∑ i ∈ s, f i‖ ≤ x * M := by
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum h).trans ?_)
  rw [Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right hs hM

lemma card_Icc_le {x : ℝ} (hx : 0 ≤ x) : ((Icc 1 ⌊x⌋₊).card : ℝ) ≤ x := by
  rw [Nat.card_Icc, Nat.add_sub_cancel]
  exact Nat.floor_le hx

lemma card_filter_Icc_le {x : ℝ} (hx : 0 ≤ x) (p : ℕ → Prop) [DecidablePred p] :
    (((Icc 1 ⌊x⌋₊).filter p).card : ℝ) ≤ x :=
  (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans (card_Icc_le hx)

lemma norm_detSum_le {W : ℝ × ℝ × ℝ × ℝ → ℂ} {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ p, ‖W p‖ ≤ M)
    (κ : ℤ) {X A B : ℝ} (hX : 0 < X) (hA : 0 < A) (hB : 0 < B) :
    ‖detSum κ W A B X‖ ≤ 16 * X ^ 2 * M := by
  unfold detSum
  have hb : ∀ a b d e : ℕ, ‖(if Odd a ∧ Odd b ∧ Odd d ∧ Odd e ∧ (b : ℤ) * e - (a : ℤ) * d = κ
      then (μ d : ℂ) * (μ e : ℂ) *
        W ((a : ℝ) / A, (b : ℝ) / B, (d : ℝ) / (X / A), (e : ℝ) / (X / B)) else 0)‖ ≤ M := by
    intro a b d e
    split_ifs
    · rw [norm_mul, norm_mul]
      have h1 : ‖(μ d : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      have h2 : ‖(μ e : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      have h3 := hM ((a : ℝ) / A, (b : ℝ) / B, (d : ℝ) / (X / A), (e : ℝ) / (X / B))
      have h12 : ‖(μ d : ℂ)‖ * ‖(μ e : ℂ)‖ ≤ 1 := by
        nlinarith [norm_nonneg (μ d : ℂ), norm_nonneg (μ e : ℂ)]
      nlinarith [norm_nonneg (μ d : ℂ), norm_nonneg (μ e : ℂ),
        mul_nonneg (norm_nonneg (μ d : ℂ)) (norm_nonneg (μ e : ℂ)), norm_nonneg (W
          ((a : ℝ) / A, (b : ℝ) / B, (d : ℝ) / (X / A), (e : ℝ) / (X / B)))]
    · simpa using hM0
  have hDA : 0 < X / A := div_pos hX hA
  have hEB : 0 < X / B := div_pos hX hB
  refine (norm_sum_le_card (by positivity) (card_Icc_le (by positivity)) (fun a _ =>
    norm_sum_le_card (by positivity) (card_Icc_le (by positivity)) (fun b _ =>
      norm_sum_le_card (by positivity) (card_Icc_le (by positivity)) (fun d _ =>
        norm_sum_le_card hM0 (card_Icc_le (by positivity)) (fun e _ => hb a b d e))))).trans
    (le_of_eq ?_)
  field_simp
  ring

lemma norm_zeroMode_le {W : ℝ × ℝ × ℝ × ℝ → ℂ} (hW : SmoothWeight W) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ p, ‖W p‖ ≤ M) (κ : ℤ) {X A B : ℝ} (hX : 0 < X) (hA : 0 < A) (hB : 1 ≤ B) :
    ‖zeroMode κ W A B X‖ ≤ 2 * X ^ 2 * M := by
  unfold zeroMode
  have hDA : 0 < X / A := div_pos hX hA
  have hEB : 0 < X / B := div_pos hX (by linarith)
  have hb : ∀ e d : ℕ, 1 ≤ e → ‖(μ e : ℂ) * (μ d : ℂ) * ((A / (2 * e) : ℝ) : ℂ) *
      Phi0 κ W X ((d : ℝ) / (X / A)) ((e : ℝ) / (X / B))‖ ≤ A / 2 * M := by
    intro e d he
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 : ‖(μ e : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have h2 : ‖(μ d : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
    have h3 : |A / (2 * e)| ≤ A / 2 := by
      rw [abs_of_pos (by positivity)]
      exact div_le_div_of_nonneg_left hA.le (by norm_num) (by linarith)
    have h4 := norm_Phi0_le hW hM κ X ((d : ℝ) / (X / A)) ((e : ℝ) / (X / B))
    have h12 : ‖(μ e : ℂ)‖ * ‖(μ d : ℂ)‖ ≤ 1 := by
      nlinarith [norm_nonneg (μ d : ℂ), norm_nonneg (μ e : ℂ)]
    have h123 : ‖(μ e : ℂ)‖ * ‖(μ d : ℂ)‖ * |A / (2 * e)| ≤ A / 2 := by
      nlinarith [abs_nonneg (A / (2 * e)), mul_nonneg (norm_nonneg (μ e : ℂ))
        (norm_nonneg (μ d : ℂ))]
    exact mul_le_mul h123 h4 (norm_nonneg _) (by positivity)
  refine (norm_sum_le_card (by positivity) (card_filter_Icc_le (by positivity) _) (fun e he =>
    norm_sum_le_card (by positivity) (card_filter_Icc_le (by positivity) _) (fun d _ =>
      hb e d ?_))).trans ?_
  · simp only [Finset.mem_filter, Finset.mem_Icc] at he; exact he.1.1
  · have hXB : X / B ≤ X := div_le_self hX.le hB
    have : 2 * (X / B) * (2 * (X / A) * (A / 2 * M)) = 2 * X * (X / B) * M := by
      field_simp
    rw [this]
    have : 2 * X * (X / B) * M ≤ 2 * X * X * M := by gcongr
    nlinarith

end MobiusDeterminant.Determinant.Reduction
