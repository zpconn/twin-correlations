import MobiusDeterminant.Determinant.Defs
import MobiusDeterminant.Determinant.OddMainArith
import MobiusDeterminant.Unconditional.LevelTempered

/-!
# The main term of the odd divisor-pair sum (`OddMainBound`)

For odd `d, e`, `dens d e = 1/(de)` if `(d,e) = 1` and `0` otherwise, so

  `oddMain = ∑_{e odd} μ(e) φ₂(e/E) N₀ ψ̂(0)/(2e) · T(2e)`,
  `T(q) = ∑_{d ≤ 2D, (d,q)=1} μ(d) φ₁(d/D)/d`.

Summation by parts against `M_q(n) = ∑_{d ≤ n, (d,q)=1} μ(d)` (`Mq_bound`) and
`|f(n) - f(n+1)| ≤ (2P+4)/D²` for `f(n) = φ₁(n/D)/n` gives `T(q) ≪ P exp(-c √log D)` uniformly
in `q ≤ 4D²` (`T_bound`).  Then `|ψ̂(0)| ≤ 3/2` and `∑_{e ≤ 2E} |φ₂(e/E)|/e ≤ 4`.
We take `k = 1` in `OddMainBound`.
-/

open Finset Real
open scoped ArithmeticFunction.Moebius

namespace MobiusDeterminant
namespace Determinant
namespace OddMain

open MobiusSums

/-! ## Summation by parts -/

lemma sum_by_parts_complex (a w : ℕ → ℂ) (N : ℕ) :
    ∑ i ∈ Icc 1 N, a i * w i = (∑ i ∈ Icc 1 N, a i) * w N +
      ∑ i ∈ range N, (∑ j ∈ Icc 1 i, a j) * (w i - w (i + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega),
      Finset.sum_range_succ, ih]
    ring

/-! ## Tempered weights with `k = 1` -/

lemma tempered_norm_le {φ : ℝ → ℂ} {P : ℝ} (hφ : TemperedOn φ P 1 (1 / 2) 2) (x : ℝ) :
    ‖φ x‖ ≤ 1 := by
  have := hφ.2.2 0 (Nat.zero_le _) x
  simpa using this

lemma tempered_lip {φ : ℝ → ℂ} {P : ℝ} (hφ : TemperedOn φ P 1 (1 / 2) 2) (x y : ℝ) :
    ‖φ y - φ x‖ ≤ P * |y - x| := by
  have hd : Differentiable ℝ φ := hφ.1.differentiable (by norm_num)
  have := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.univ) (f := φ) (C := P)
    (fun z _ => hd z) (fun z _ => by
      have h := hφ.2.2 1 le_rfl z
      rwa [iteratedDeriv_one, pow_one] at h) convex_univ (Set.mem_univ x) (Set.mem_univ y)
  simpa [Real.norm_eq_abs] using this

lemma tempered_mem {φ : ℝ → ℂ} {P : ℝ} (hφ : TemperedOn φ P 1 (1 / 2) 2) {x : ℝ}
    (hx : φ x ≠ 0) : 1 / 2 ≤ x ∧ x ≤ 2 := by
  by_contra h
  exact hx (hφ.2.1 x (fun hm => h ⟨hm.1, hm.2⟩))

/-- `|f(i) - f(i+1)| ≤ (2P + 4)/D²` for `f(n) = φ(n/D)/n`, when `i + 1 ≥ D/2`. -/
lemma w_diff_le {φ : ℝ → ℂ} {P D : ℝ} (hφ : TemperedOn φ P 1 (1 / 2) 2) (hD : 0 < D)
    (i : ℕ) (hi : 1 ≤ i) (hi2 : D / 2 ≤ (i : ℝ) + 1) :
    ‖φ ((i : ℝ) / D) / (i : ℂ) - φ (((i : ℝ) + 1) / D) / ((i : ℂ) + 1)‖ ≤ (2 * P + 4) / D ^ 2 := by
  have hi0 : (0 : ℝ) < i := by exact_mod_cast hi
  have hi1 : (0 : ℝ) < (i : ℝ) + 1 := by linarith
  have key : φ ((i : ℝ) / D) / (i : ℂ) - φ (((i : ℝ) + 1) / D) / ((i : ℂ) + 1) =
      (φ ((i : ℝ) / D) - φ (((i : ℝ) + 1) / D)) * (((1 / ((i : ℝ) + 1)) : ℝ) : ℂ) +
        φ ((i : ℝ) / D) * (((1 / ((i : ℝ) * ((i : ℝ) + 1))) : ℝ) : ℂ) := by
    have h1 : (i : ℂ) ≠ 0 := by exact_mod_cast hi0.ne'
    have h2 : (i : ℂ) + 1 ≠ 0 := by exact_mod_cast hi1.ne'
    push_cast
    field_simp
    ring
  rw [key]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (by positivity), abs_of_pos (by positivity)]
  have hP : 0 ≤ P := by
    have := (norm_nonneg _).trans (tempered_lip hφ 0 1)
    simpa using this
  have hA : ‖φ ((i : ℝ) / D) - φ (((i : ℝ) + 1) / D)‖ * (1 / ((i : ℝ) + 1)) ≤ 2 * P / D ^ 2 := by
    have h1 := tempered_lip hφ (((i : ℝ) + 1) / D) ((i : ℝ) / D)
    have h2 : |(i : ℝ) / D - ((i : ℝ) + 1) / D| = 1 / D := by
      rw [div_sub_div_same, show (i : ℝ) - ((i : ℝ) + 1) = -1 by ring, abs_div, abs_neg,
        abs_one, abs_of_pos hD]
    rw [h2] at h1
    have h3 : 1 / ((i : ℝ) + 1) ≤ 2 / D := by
      rw [div_le_div_iff₀ hi1 hD]; linarith
    calc ‖φ ((i : ℝ) / D) - φ (((i : ℝ) + 1) / D)‖ * (1 / ((i : ℝ) + 1))
        ≤ (P * (1 / D)) * (2 / D) := by gcongr
      _ = 2 * P / D ^ 2 := by field_simp
  have hB : ‖φ ((i : ℝ) / D)‖ * (1 / ((i : ℝ) * ((i : ℝ) + 1))) ≤ 4 / D ^ 2 := by
    by_cases h0 : φ ((i : ℝ) / D) = 0
    · rw [h0, norm_zero, zero_mul]; positivity
    · have hm := (tempered_mem hφ h0).1
      have hiD : D / 2 ≤ i := by
        rw [le_div_iff₀ hD] at hm; linarith
      have h3 : 1 / ((i : ℝ) * ((i : ℝ) + 1)) ≤ 4 / D ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
      calc ‖φ ((i : ℝ) / D)‖ * (1 / ((i : ℝ) * ((i : ℝ) + 1))) ≤ 1 * (4 / D ^ 2) := by
            gcongr
            exact tempered_norm_le hφ _
        _ = 4 / D ^ 2 := one_mul _
  calc _ ≤ 2 * P / D ^ 2 + 4 / D ^ 2 := add_le_add hA hB
    _ = (2 * P + 4) / D ^ 2 := by ring

/-! ## The smooth sum `T(q) = ∑_{(d,q)=1} μ(d) φ(d/D)/d` -/

theorem T_bound : ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ (D P : ℝ) (φ : ℝ → ℂ) (q : ℕ), 2 ≤ D →
    1 ≤ P → TemperedOn φ P 1 (1 / 2) 2 → 1 ≤ q → (q : ℝ) ≤ 4 * D ^ 2 →
      ‖∑ d ∈ Icc 1 ⌊2 * D⌋₊, ((psiC q d : ℤ) : ℂ) * (φ ((d : ℝ) / D) / (d : ℂ))‖ ≤
        C * P * ep c D := by
  obtain ⟨c, hc, CA, hCA, hA⟩ := Mq_bound
  refine ⟨c, hc, 18 * CA, by positivity, ?_⟩
  intro D P φ q hD hP hφ hq1 hqD
  have hD0 : 0 < D := by linarith
  set N := ⌊2 * D⌋₊ with hN
  have hN1 : (N : ℝ) ≤ 2 * D := Nat.floor_le (by positivity)
  have hN2 : 2 * D < (N : ℝ) + 1 := Nat.lt_floor_add_one _
  set w : ℕ → ℂ := fun i => φ ((i : ℝ) / D) / (i : ℂ) with hw
  set a : ℕ → ℂ := fun i => ((psiC q i : ℤ) : ℂ) with ha
  have hwN : w (N + 1) = 0 := by
    simp only [hw]
    rw [hφ.2.1 _ ?_, zero_div]
    intro hm
    have h2 := hm.2
    rw [div_le_iff₀ hD0] at h2
    push_cast at h2
    linarith
  have hsum : ∑ d ∈ Icc 1 N, ((psiC q d : ℤ) : ℂ) * (φ ((d : ℝ) / D) / (d : ℂ)) =
      ∑ i ∈ Icc 1 (N + 1), a i * w i := by
    rw [Finset.sum_Icc_succ_top (by omega), hwN, mul_zero, add_zero]
  rw [hsum, sum_by_parts_complex, hwN, mul_zero, zero_add]
  have hAeq : ∀ i, ∑ j ∈ Icc 1 i, a j = ((Mq q i : ℝ) : ℂ) := by
    intro i; simp only [ha, Mq]; push_cast; rfl
  set E := ep c D with hE
  have hEpos : 0 < E := ep_pos _ _
  have hpt : ∀ i ∈ range (N + 1), ‖(∑ j ∈ Icc 1 i, a j) * (w i - w (i + 1))‖ ≤
      CA * D * E * ((2 * P + 4) / D ^ 2) := by
    intro i hi
    have hiN : i ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have hiN' : (i : ℝ) ≤ 2 * D := (Nat.cast_le.mpr hiN).trans hN1
    have hR : 0 ≤ CA * D * E * ((2 * P + 4) / D ^ 2) := by positivity
    rcases Nat.eq_zero_or_pos i with rfl | hi1
    · simp only [Icc_eq_empty_of_lt one_pos, sum_empty, zero_mul, norm_zero]
      exact hR
    by_cases hz : φ ((i : ℝ) / D) = 0 ∧ φ (((i : ℝ) + 1) / D) = 0
    · have h1 : w i - w (i + 1) = 0 := by
        simp only [hw]; push_cast; rw [hz.1, hz.2]; simp
      rw [h1, mul_zero, norm_zero]; exact hR
    · have hi2 : D / 2 ≤ (i : ℝ) + 1 := by
        rcases not_and_or.mp hz with h | h
        · have := (tempered_mem hφ h).1
          rw [le_div_iff₀ hD0] at this; linarith
        · have := (tempered_mem hφ h).1
          rw [le_div_iff₀ hD0] at this; linarith
      have hi1R : (1 : ℝ) ≤ i := by exact_mod_cast hi1
      have hiD : D / 4 ≤ (i : ℝ) := by linarith
      have hMq := hA D q i hD hq1 hqD hi1 hiD hiN'
      rw [hAeq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hwd : ‖w i - w (i + 1)‖ ≤ (2 * P + 4) / D ^ 2 := by
        have := w_diff_le hφ hD0 i hi1 hi2
        simp only [hw]; push_cast; exact this
      exact mul_le_mul hMq hwd (norm_nonneg _) (by positivity)
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ _ hpt).trans ?_
  rw [card_range, nsmul_eq_mul]
  have hN3 : ((N + 1 : ℕ) : ℝ) ≤ 3 * D := by push_cast; linarith
  calc ((N + 1 : ℕ) : ℝ) * (CA * D * E * ((2 * P + 4) / D ^ 2))
      ≤ (3 * D) * (CA * D * E * ((2 * P + 4) / D ^ 2)) := by gcongr
    _ = 3 * CA * E * (2 * P + 4) := by field_simp
    _ ≤ 3 * CA * E * (6 * P) := by gcongr; linarith
    _ = 18 * CA * P * E := by ring

/-! ## Assembly -/

lemma dens_odd {d e : ℕ} (hd : Odd d) :
    dens d e = if Nat.Coprime d e then 1 / ((d : ℝ) * e) else 0 := by
  unfold dens
  by_cases h : Nat.Coprime d e
  · rw [ite_eq_left (by rw [h.gcd_eq_one]; exact one_dvd 2), ite_eq_left h, h.lcm_eq_mul]
    push_cast; rfl
  · rw [ite_eq_right h, ite_eq_right]
    intro h2
    apply h
    have hodd : Odd (Nat.gcd d e) := Odd.of_dvd_nat hd (Nat.gcd_dvd_left d e)
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h1
    · exact h1
    · rw [h1] at hodd; exact absurd hodd (by decide)

lemma oddMain_eq (N₀ D E : ℝ) (ψ φ₁ φ₂ : ℝ → ℂ) :
    oddMain N₀ D E ψ φ₁ φ₂ = ∑ e ∈ (Icc 1 ⌊2 * E⌋₊).filter Odd,
      ((μ e : ℂ) * φ₂ ((e : ℝ) / E) * ((N₀ : ℂ) * fourierR ψ 0 * ((1 / (2 * (e : ℝ)) : ℝ) : ℂ))) *
        ∑ d ∈ Icc 1 ⌊2 * D⌋₊, ((psiC (2 * e) d : ℤ) : ℂ) * (φ₁ ((d : ℝ) / D) / (d : ℂ)) := by
  unfold oddMain
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro e he
  simp only [mem_filter, mem_Icc] at he
  have he0 : (0 : ℝ) < e := by exact_mod_cast he.1.1
  rw [Finset.mul_sum, Finset.sum_filter]
  apply sum_congr rfl
  intro d hd
  simp only [mem_Icc] at hd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.1
  rw [psiC_apply]
  by_cases hdo : Odd d
  · rw [ite_eq_left hdo, dens_odd hdo]
    by_cases hc : Nat.Coprime d e
    · have hc2 : Nat.Coprime d (2 * e) :=
        Nat.coprime_mul_iff_right.mpr ⟨Nat.coprime_two_right.mpr hdo, hc⟩
      rw [ite_eq_left hc, ite_eq_left hc2]
      have h1 : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
      have h2 : (e : ℂ) ≠ 0 := by exact_mod_cast he0.ne'
      push_cast
      field_simp
    · have hc2 : ¬ Nat.Coprime d (2 * e) := fun h => hc (Nat.coprime_mul_iff_right.mp h).2
      rw [ite_eq_right hc, ite_eq_right hc2]
      simp
  · have hc2 : ¬ Nat.Coprime d (2 * e) :=
      fun h => hdo (Nat.coprime_two_right.mp (Nat.coprime_mul_iff_right.mp h).1)
    rw [ite_eq_right hdo, ite_eq_right hc2]
    simp

end OddMain

open OddMain MobiusSums in
theorem oddMainBound : OddMainBound := by
  obtain ⟨c, hc, CT, hCT, hT⟩ := T_bound
  refine ⟨c, hc, 1, 3 * CT, by positivity, ?_⟩
  intro N₀ D E P ψ φ₁ φ₂ hN₀ hD hE hED hP hψ hφ₁ hφ₂
  rw [oddMain_eq, pow_one]
  have hE0 : 0 < E := by linarith
  set ε := ep c D with hε
  have hεpos : 0 < ε := ep_pos _ _
  have hψ0 : ‖fourierR ψ 0‖ ≤ 3 / 2 := Level.norm_fourierR_le hψ 0
  set M := ⌊2 * E⌋₊ with hM
  have hM1 : (M : ℝ) ≤ 2 * E := Nat.floor_le (by positivity)
  have hpt : ∀ e ∈ (Icc 1 M).filter Odd,
      ‖((μ e : ℂ) * φ₂ ((e : ℝ) / E) * ((N₀ : ℂ) * fourierR ψ 0 * ((1 / (2 * (e : ℝ)) : ℝ) : ℂ))) *
        ∑ d ∈ Icc 1 ⌊2 * D⌋₊, ((psiC (2 * e) d : ℤ) : ℂ) * (φ₁ ((d : ℝ) / D) / (d : ℂ))‖ ≤
      (3 / 2 * N₀ / E) * (CT * P * ε) := by
    intro e he
    simp only [mem_filter, mem_Icc] at he
    have he1 : 1 ≤ e := he.1.1
    have he0 : (0 : ℝ) < e := by exact_mod_cast he1
    have heM : (e : ℝ) ≤ 2 * E := (Nat.cast_le.mpr he.1.2).trans hM1
    have hq : ((2 * e : ℕ) : ℝ) ≤ 4 * D ^ 2 := by push_cast; nlinarith
    have hTe := hT D P φ₁ (2 * e) hD hP hφ₁ (by omega) hq
    rw [norm_mul]
    refine mul_le_mul ?_ hTe (norm_nonneg _) (by positivity)
    rw [norm_mul, norm_mul, norm_mul, norm_mul]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hN₀,
      abs_of_pos (show (0 : ℝ) < 1 / (2 * (e : ℝ)) by positivity)]
    have hμ : ‖(μ e : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]; exact_mod_cast abs_moebius_real_le e
    have hφe : ‖φ₂ ((e : ℝ) / E)‖ * (1 / (2 * (e : ℝ))) ≤ 1 / E := by
      by_cases h0 : φ₂ ((e : ℝ) / E) = 0
      · rw [h0, norm_zero, zero_mul]; positivity
      · have hm := (tempered_mem hφ₂ h0).1
        rw [le_div_iff₀ hE0] at hm
        calc ‖φ₂ ((e : ℝ) / E)‖ * (1 / (2 * (e : ℝ))) ≤ 1 * (1 / (2 * (e : ℝ))) := by
              gcongr; exact tempered_norm_le hφ₂ _
          _ ≤ 1 / E := by
              rw [one_mul, div_le_div_iff₀ (by positivity) hE0]; linarith
    calc ‖(μ e : ℂ)‖ * ‖φ₂ ((e : ℝ) / E)‖ * (N₀ * ‖fourierR ψ 0‖ * (1 / (2 * (e : ℝ))))
        = ‖(μ e : ℂ)‖ * (‖φ₂ ((e : ℝ) / E)‖ * (1 / (2 * (e : ℝ)))) * (N₀ * ‖fourierR ψ 0‖) := by
          ring
      _ ≤ 1 * (1 / E) * (N₀ * (3 / 2)) := by gcongr
      _ = 3 / 2 * N₀ / E := by ring
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ _ hpt).trans ?_
  rw [nsmul_eq_mul]
  have hcard : (((Icc 1 M).filter Odd).card : ℝ) ≤ 2 * E := by
    have h1 : ((Icc 1 M).filter Odd).card ≤ M := by
      refine (Finset.card_filter_le _ _).trans ?_
      simp
    exact (Nat.cast_le.mpr h1).trans hM1
  calc (((Icc 1 M).filter Odd).card : ℝ) * (3 / 2 * N₀ / E * (CT * P * ε))
      ≤ (2 * E) * (3 / 2 * N₀ / E * (CT * P * ε)) := by gcongr
    _ = 3 * CT * P * N₀ * ε := by field_simp
    _ = 3 * CT * P * N₀ * Real.exp (-c * Real.sqrt (Real.log D)) := rfl

end Determinant
end MobiusDeterminant
