import MobiusDeterminant.MainTerm.MobiusSumsSmooth

/-!
# `S_g(y) = g/φ(g) + O(g³ exp(-c √log y))` from the PNT for `μ`

Main result: `sgAsymp_of_PNT : PNTMobius → SgAsymp`.

Proof outline (the ingredients live in `MobiusSumsAnalytic`, `MobiusSumsMobius`,
`MobiusSumsSmooth`):

1. `|S₁(z) - 1| ≤ C exp(-c √log z)` for `z ≥ 1` (`S1_bound`);
2. `S_g(y) = ∑_{k ≤ y, k ∣ g^∞} S₁(y/k)/k` (`Sg_eq`);
3. `∑_{k ∣ g^∞} 1/k = g/φ(g)` and `∑_{k ∣ g^∞} k^{-1/2} ≤ g²` (`hasSum_Fg`,
   `prod_eq_div_totient`, `prod_half_le`);
4. split at `k ≤ √y` and use Rankin's trick `1/k ≤ y^{-1/4} k^{-1/2}` for `k > √y`.
-/

open Finset Real Filter Topology
open scoped ArithmeticFunction.Moebius

namespace MobiusDeterminant
namespace MobiusSums

lemma chiF_real_bounds (g k : ℕ) : 0 ≤ (chiF g k : ℝ) ∧ (chiF g k : ℝ) ≤ 1 := by
  rw [chiF_apply]; split_ifs <;> simp

/-- `w₁(k) = 1_{k ∣ g^∞} / k`. -/
noncomputable def w1 (g : ℕ) : ℕ → ℝ := fun k => (chiF g k : ℝ) * (1 / (k : ℝ))

/-- `w₂(k) = 1_{k ∣ g^∞} / √k`. -/
noncomputable def w2 (g : ℕ) : ℕ → ℝ := fun k => (chiF g k : ℝ) * (1 / (k : ℝ) ^ (1 / 2 : ℝ))

lemma w1_nonneg (g k : ℕ) : 0 ≤ w1 g k :=
  mul_nonneg (chiF_real_bounds g k).1 (by positivity)

lemma w2_nonneg (g k : ℕ) : 0 ≤ w2 g k :=
  mul_nonneg (chiF_real_bounds g k).1 (by positivity)

/-- Rankin's trick: `1/k ≤ Y^{-1/2} k^{-1/2}` for `k ≥ Y`. -/
lemma rankin_pt {Y : ℝ} (hY : 0 < Y) {k : ℕ} (hk : Y ≤ k) :
    1 / (k : ℝ) ≤ 1 / √Y * (1 / (k : ℝ) ^ (1 / 2 : ℝ)) := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le hY hk
  rw [← Real.sqrt_eq_rpow, one_div_mul_one_div]
  have hsY : 0 < √Y := Real.sqrt_pos.mpr hY
  have hsk : 0 < √(k : ℝ) := Real.sqrt_pos.mpr hk0
  rw [one_div_le_one_div hk0 (by positivity)]
  calc √Y * √(k : ℝ) ≤ √(k : ℝ) * √(k : ℝ) :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hk) hsk.le
    _ = k := Real.mul_self_sqrt hk0.le

lemma w1_le_w2 {Y : ℝ} (hY : 0 < Y) (g : ℕ) {k : ℕ} (hk : Y ≤ k) :
    w1 g k ≤ 1 / √Y * w2 g k := by
  unfold w1 w2
  have := rankin_pt hY hk
  have h0 := (chiF_real_bounds g k).1
  calc (chiF g k : ℝ) * (1 / (k : ℝ)) ≤
      (chiF g k : ℝ) * (1 / √Y * (1 / (k : ℝ) ^ (1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left this h0
    _ = 1 / √Y * ((chiF g k : ℝ) * (1 / (k : ℝ) ^ (1 / 2 : ℝ))) := by ring

lemma ep_sqrt_le {c y : ℝ} (hc : 0 ≤ c) (hy : 1 ≤ y) : ep c (√y) ≤ ep (c / 2) y := by
  unfold ep
  apply Real.exp_le_exp.mpr
  rw [Real.log_sqrt (by linarith)]
  have hL : 0 ≤ Real.log y := Real.log_nonneg hy
  have h1 : √(Real.log y) / 2 ≤ √(Real.log y / 2) := by
    rw [Real.le_sqrt (by positivity) (by positivity), div_pow, Real.sq_sqrt hL]
    linarith
  nlinarith

lemma inv_sqrt_sqrt_le (c : ℝ) {y : ℝ} (hy : 1 ≤ y) :
    1 / √(√y) ≤ Real.exp (c ^ 2) * ep c y := by
  have hy0 : 0 < y := by linarith
  have hs : 0 < √(√y) := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hy0)
  have hlog : Real.log (√(√y)) = Real.log y / 4 := by
    rw [Real.log_sqrt (Real.sqrt_nonneg _), Real.log_sqrt hy0.le]; ring
  have he : 1 / √(√y) = Real.exp (-(Real.log y / 4)) := by
    rw [← hlog, Real.exp_neg, Real.exp_log hs, one_div]
  rw [he]
  unfold ep
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hL : 0 ≤ Real.log y := Real.log_nonneg hy
  have := Real.sq_sqrt hL
  nlinarith [sq_nonneg (√(Real.log y) / 2 - c)]

/-- **Main result.** The PNT for `μ` with de la Vallée Poussin error term implies the uniform
asymptotic `S_g(y) = g/φ(g) + O(g³ exp(-c √log y))`. -/
theorem sgAsymp_of_PNT_aux (h : PNTMobius) : SgAsymp := by
  obtain ⟨c₂, hc₂, C₂, hC₂, hS⟩ := S1_bound h
  refine ⟨c₂ / 2, half_pos hc₂, C₂ + (C₂ + 1) * Real.exp ((c₂ / 2) ^ 2), by positivity,
    fun g hg y hy => ?_⟩
  have hg0 : g ≠ 0 := by omega
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hy0 : 0 < y := by linarith
  have hy1 : 1 ≤ y := by linarith
  have hsy : 0 < √y := Real.sqrt_pos.mpr hy0
  have hsyy : √y ≤ y := by
    rw [Real.sqrt_le_left hy0.le]; nlinarith
  -- the two series over `g`-smooth numbers
  have hH1 : HasSum (w1 g) ((g : ℝ) / (Nat.totient g : ℝ)) := by
    have := hasSum_Fg g (σ := 1) one_pos
    rw [prod_eq_div_totient g hg0] at this
    simp only [Real.rpow_one] at this
    exact this
  have hH2 : HasSum (w2 g) (∏ p ∈ g.primeFactors, (1 - 1 / (p : ℝ) ^ (1 / 2 : ℝ))⁻¹) :=
    hasSum_Fg g (by norm_num)
  set P2 := ∏ p ∈ g.primeFactors, (1 - 1 / (p : ℝ) ^ (1 / 2 : ℝ))⁻¹ with hP2
  set G := (g : ℝ) / (Nat.totient g : ℝ) with hG
  have hP2le : P2 ≤ (g : ℝ) ^ 2 := prod_half_le g hg0
  have hG0 : 0 ≤ G := by positivity
  have hGle : G ≤ g := by
    apply div_le_self (by positivity)
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hg0)
  have hs1 := hH1.summable
  have hs2 := hH2.summable
  set N := ⌊y⌋₊ with hN
  have hNy : (N : ℝ) ≤ y := Nat.floor_le hy0.le
  have hyN : y < N + 1 := Nat.lt_floor_add_one y
  -- split `g/φ(g)` at `N`
  have hsplit := hs1.sum_add_tsum_nat_add (N + 1)
  rw [hH1.tsum_eq, sum_range_succ_eq_Icc] at hsplit
  have hw10 : w1 g 0 = 0 := by simp [w1]
  rw [hw10, zero_add] at hsplit
  rw [Sg_eq g hg0 y, ← hsplit]
  set T := ∑' i, w1 g (i + (N + 1)) with hT
  have hdiff : ∑ a ∈ Icc 1 N, (chiF g a : ℝ) * (S1 (y / a) / a) - (∑ k ∈ Icc 1 N, w1 g k + T) =
      ∑ a ∈ Icc 1 N, (chiF g a : ℝ) * ((S1 (y / a) - 1) / a) - T := by
    rw [← sub_sub, ← Finset.sum_sub_distrib]
    congr 1
    apply sum_congr rfl
    intro a _
    simp only [w1]
    ring
  rw [hdiff]
  -- the tail
  have hT0 : 0 ≤ T := tsum_nonneg (fun i => w1_nonneg g _)
  have hTle : T ≤ 1 / √(√y) * P2 := by
    have hs1' : Summable (fun i => w1 g (i + (N + 1))) := (summable_nat_add_iff (N + 1)).mpr hs1
    have hs2' : Summable (fun i => w2 g (i + (N + 1))) := (summable_nat_add_iff (N + 1)).mpr hs2
    have hpt : ∀ i : ℕ, w1 g (i + (N + 1)) ≤ 1 / √(√y) * w2 g (i + (N + 1)) := by
      intro i
      apply w1_le_w2 hsy
      push_cast
      have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      linarith
    calc T ≤ ∑' i, 1 / √(√y) * w2 g (i + (N + 1)) := hs1'.tsum_le_tsum hpt (hs2'.mul_left _)
      _ = 1 / √(√y) * ∑' i, w2 g (i + (N + 1)) := tsum_mul_left
      _ ≤ 1 / √(√y) * P2 := by
        gcongr
        rw [← hH2.tsum_eq]
        exact tsum_tail_le hs2 (w2_nonneg g) (N + 1)
  -- the main sum
  have hpt : ∀ a ∈ Icc 1 N, |(chiF g a : ℝ) * ((S1 (y / a) - 1) / a)| ≤
      C₂ * ep c₂ (√y) * w1 g a + C₂ * (1 / √(√y)) * w2 g a := by
    intro a ha
    have ha1 : 1 ≤ a := (mem_Icc.mp ha).1
    have ha0 : (0 : ℝ) < a := by exact_mod_cast ha1
    have haN : (a : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp ha).2
    have hya : 1 ≤ y / a := by rw [le_div_iff₀ ha0]; linarith
    have hSa := hS (y / a) hya
    obtain ⟨hχ0, hχ1⟩ := chiF_real_bounds g a
    have hw1 := w1_nonneg g a
    have hw2 := w2_nonneg g a
    rw [abs_mul, abs_of_nonneg hχ0, abs_div, abs_of_pos ha0]
    by_cases hcase : (a : ℝ) ≤ √y
    · have hle : √y ≤ y / a := by
        rw [le_div_iff₀ ha0]
        calc √y * a ≤ √y * √y := mul_le_mul_of_nonneg_left hcase hsy.le
          _ = y := Real.mul_self_sqrt hy0.le
      have hep : ep c₂ (y / a) ≤ ep c₂ (√y) := ep_anti hc₂.le hsy hle
      have h1 : |S1 (y / a) - 1| ≤ C₂ * ep c₂ (√y) :=
        hSa.trans (mul_le_mul_of_nonneg_left hep hC₂.le)
      calc (chiF g a : ℝ) * (|S1 (y / a) - 1| / a) ≤
          (chiF g a : ℝ) * (C₂ * ep c₂ (√y) / a) := by
            apply mul_le_mul_of_nonneg_left _ hχ0
            exact div_le_div_of_nonneg_right h1 ha0.le
        _ = C₂ * ep c₂ (√y) * w1 g a := by simp only [w1]; ring
        _ ≤ C₂ * ep c₂ (√y) * w1 g a + C₂ * (1 / √(√y)) * w2 g a := by
            have : 0 ≤ C₂ * (1 / √(√y)) * w2 g a := by positivity
            linarith
    · rw [not_le] at hcase
      have h1 : |S1 (y / a) - 1| ≤ C₂ := by
        have := ep_le_one hc₂.le (y / a)
        nlinarith
      have hr := w1_le_w2 hsy g hcase.le
      calc (chiF g a : ℝ) * (|S1 (y / a) - 1| / a) ≤ (chiF g a : ℝ) * (C₂ / a) := by
            apply mul_le_mul_of_nonneg_left _ hχ0
            exact div_le_div_of_nonneg_right h1 ha0.le
        _ = C₂ * w1 g a := by simp only [w1]; ring
        _ ≤ C₂ * (1 / √(√y) * w2 g a) := mul_le_mul_of_nonneg_left hr hC₂.le
        _ ≤ C₂ * ep c₂ (√y) * w1 g a + C₂ * (1 / √(√y)) * w2 g a := by
            have : 0 ≤ C₂ * ep c₂ (√y) * w1 g a := by
              have := ep_pos c₂ (√y); positivity
            linarith
  have hmain : |∑ a ∈ Icc 1 N, (chiF g a : ℝ) * ((S1 (y / a) - 1) / a)| ≤
      C₂ * ep c₂ (√y) * G + C₂ * (1 / √(√y)) * P2 := by
    calc |∑ a ∈ Icc 1 N, (chiF g a : ℝ) * ((S1 (y / a) - 1) / a)|
        ≤ ∑ a ∈ Icc 1 N, |(chiF g a : ℝ) * ((S1 (y / a) - 1) / a)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a ∈ Icc 1 N, (C₂ * ep c₂ (√y) * w1 g a + C₂ * (1 / √(√y)) * w2 g a) :=
          sum_le_sum hpt
      _ = C₂ * ep c₂ (√y) * ∑ a ∈ Icc 1 N, w1 g a + C₂ * (1 / √(√y)) * ∑ a ∈ Icc 1 N, w2 g a := by
          rw [sum_add_distrib, ← mul_sum, ← mul_sum]
      _ ≤ C₂ * ep c₂ (√y) * G + C₂ * (1 / √(√y)) * P2 := by
          have he := ep_pos c₂ (√y)
          have h1 : ∑ a ∈ Icc 1 N, w1 g a ≤ G := by
            rw [← hH1.tsum_eq]
            exact hs1.sum_le_tsum _ (fun i _ => w1_nonneg g i)
          have h2 : ∑ a ∈ Icc 1 N, w2 g a ≤ P2 := by
            rw [← hH2.tsum_eq]
            exact hs2.sum_le_tsum _ (fun i _ => w2_nonneg g i)
          gcongr
  -- assemble
  set c' := c₂ / 2 with hc'
  have hep1 : ep c₂ (√y) ≤ ep c' y := ep_sqrt_le hc₂.le hy1
  have hep2 : 1 / √(√y) ≤ Real.exp (c' ^ 2) * ep c' y := inv_sqrt_sqrt_le c' hy1
  have he := ep_pos c' y
  have hE : 0 < Real.exp (c' ^ 2) := Real.exp_pos _
  have hP20 : 0 ≤ P2 := le_trans (by positivity) (hH2.tsum_eq ▸ tsum_nonneg (w2_nonneg g))
  have hg3a : (g : ℝ) ≤ (g : ℝ) ^ 3 := by nlinarith
  have hg3b : (g : ℝ) ^ 2 ≤ (g : ℝ) ^ 3 := by nlinarith
  have hq : 0 ≤ 1 / √(√y) := by positivity
  calc |∑ a ∈ Icc 1 N, (chiF g a : ℝ) * ((S1 (y / a) - 1) / a) - T|
      ≤ |∑ a ∈ Icc 1 N, (chiF g a : ℝ) * ((S1 (y / a) - 1) / a)| + |T| := abs_sub _ _
    _ ≤ (C₂ * ep c₂ (√y) * G + C₂ * (1 / √(√y)) * P2) + 1 / √(√y) * P2 := by
        rw [abs_of_nonneg hT0]; exact add_le_add hmain hTle
    _ = C₂ * ep c₂ (√y) * G + (C₂ + 1) * (1 / √(√y)) * P2 := by ring
    _ ≤ C₂ * ep c' y * g + (C₂ + 1) * (Real.exp (c' ^ 2) * ep c' y) * (g : ℝ) ^ 2 := by
        gcongr
    _ ≤ C₂ * ep c' y * (g : ℝ) ^ 3 + (C₂ + 1) * (Real.exp (c' ^ 2) * ep c' y) * (g : ℝ) ^ 3 := by
        gcongr
    _ = (C₂ + (C₂ + 1) * Real.exp (c' ^ 2)) * (g : ℝ) ^ 3 * ep c' y := by ring

end MobiusSums

/-- `PNTMobius ⟹ SgAsymp`. -/
theorem sgAsymp_of_PNT (h : PNTMobius) : SgAsymp := MobiusSums.sgAsymp_of_PNT_aux h

end MobiusDeterminant
