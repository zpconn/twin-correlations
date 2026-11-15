import MobiusDeterminant.Unconditional.LevelDefs

/-!
# Poisson summation for one pair `(d,e)` (Proposition 8.1, Steps 1 and 4)

For `d, e` whose admissible `n` form one class `c₀` modulo `q` with `ϱ(d,e) = 1/q`,
`bracket N₀ ψ d e` equals the sum of the nonzero Poisson frequencies; we keep `1 ≤ |h| ≤ M`
and bound the tail `|h| > M` by the Fourier decay of `ψ`.
-/

open Finset Real
open scoped ArithmeticFunction.Moebius

namespace MobiusDeterminant

namespace Level

namespace Poisson

lemma norm_exp_phase (m : ℤ) (q : ℕ) :
    ‖Complex.exp (2 * π * Complex.I * (m : ℂ) / (q : ℂ))‖ = 1 := by
  have : 2 * (π : ℂ) * Complex.I * (m : ℂ) / (q : ℂ) = ((2 * π * m / q : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

/-- The class sum over `ℤ` equals the finite sum in `bracket`. -/
lemma class_tsum_eq {N₀ : ℝ} (hN₀ : 0 < N₀) {ψ : ℝ → ℂ}
    (hsupp : ∀ x, x ∉ Set.Icc (1/2 : ℝ) 2 → ψ x = 0) {d e q : ℕ} {c₀ : ℤ}
    (hclass : ∀ n : ℕ, (d ∣ n ∧ e ∣ n + 2) ↔ (n : ℤ) ≡ c₀ [ZMOD (q : ℤ)]) :
    (∑' n : ℤ, if n ≡ c₀ [ZMOD (q : ℤ)] then ψ ((n : ℝ) / N₀) else 0) =
      ∑ n ∈ (Finset.Icc 1 ⌊2 * N₀⌋₊).filter (fun n => d ∣ n ∧ e ∣ n + 2), ψ ((n : ℝ) / N₀) := by
  set s : Finset ℤ := (Finset.Icc 1 ⌊2 * N₀⌋₊).map ⟨Nat.cast, Nat.cast_injective⟩ with hs
  rw [tsum_eq_sum (s := s)]
  · rw [hs, Finset.sum_map, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [Function.Embedding.coeFn_mk, Int.cast_natCast]
    exact if_congr (hclass n).symm rfl rfl
  · intro b hb
    have hz : ψ ((b : ℝ) / N₀) = 0 := by
      apply hsupp
      intro hmem
      apply hb
      rw [hs, Finset.mem_map]
      have h1 : (1 : ℝ) / 2 ≤ (b : ℝ) / N₀ := hmem.1
      have h2 : (b : ℝ) / N₀ ≤ 2 := hmem.2
      rw [le_div_iff₀ hN₀] at h1
      rw [div_le_iff₀ hN₀] at h2
      have hb0 : (0 : ℝ) < b := by nlinarith
      have hb1 : (1 : ℤ) ≤ b := by exact_mod_cast hb0
      refine ⟨b.toNat, ?_, ?_⟩
      · rw [Finset.mem_Icc]
        constructor
        · omega
        · apply Nat.le_floor
          have : ((b.toNat : ℕ) : ℝ) = (b : ℝ) := by
            have : ((b.toNat : ℕ) : ℤ) = b := Int.toNat_of_nonneg (by omega)
            exact_mod_cast this
          rw [this]; linarith
      · simp only [Function.Embedding.coeFn_mk]
        exact Int.toNat_of_nonneg (by omega)
    simp [hz]

/-- Tail term bound: for `|h| ≥ M+1`, `‖(N₀/q) ψ̂(hN₀/q) e(·)‖ ≤ K / h²`. -/
lemma tail_term {N₀ C₀ P : ℝ} {k : ℕ} (hk : 2 ≤ k) (hN₀ : 0 < N₀) (hC₀ : 0 < C₀) (hP : 1 ≤ P)
    {ψ : ℝ → ℂ} (hdec : ∀ ξ : ℝ, ‖fourierR ψ ξ‖ ≤ C₀ * P ^ k * (1 + |ξ|) ^ (-(k : ℝ)))
    {q : ℕ} (hq : 0 < q) (c₀ : ℤ) (M : ℕ) (h : ℤ) (hh : (M : ℝ) + 1 ≤ |(h : ℝ)|) :
    ‖((N₀ / q : ℝ) : ℂ) * fourierR ψ (h * N₀ / q) *
        Complex.exp (2 * π * Complex.I * ((h * c₀ : ℤ) : ℂ) / (q : ℂ))‖
      ≤ C₀ * P ^ k * ((q : ℝ) / N₀) / (((M : ℝ) + 1) * N₀ / q) ^ (k - 2) * (1 / (h : ℝ) ^ 2) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  set X : ℝ := ((M : ℝ) + 1) * N₀ / q with hX
  have hXpos : 0 < X := by positivity
  set u : ℝ := |(h : ℝ)| * N₀ / q with hu
  have hXu : X ≤ u := by
    rw [hX, hu]; gcongr
  have hupos : 0 < u := lt_of_lt_of_le hXpos hXu
  have habs : |(h : ℝ) * N₀ / q| = u := by
    rw [hu, abs_div, abs_mul, abs_of_pos hN₀, abs_of_pos hqR]
  rw [norm_mul, norm_mul, norm_exp_phase, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < N₀ / q)]
  have hd := hdec ((h : ℝ) * N₀ / q)
  rw [habs] at hd
  have hpow : (1 + u) ^ (-(k : ℝ)) ≤ 1 / (u ^ 2 * X ^ (k - 2)) := by
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← one_div]
    apply one_div_le_one_div_of_le (by positivity)
    calc u ^ 2 * X ^ (k - 2) ≤ u ^ 2 * u ^ (k - 2) := by gcongr
      _ = u ^ k := by rw [← pow_add]; congr 1; omega
      _ ≤ (1 + u) ^ k := by gcongr; linarith
  have hh0 : (h : ℝ) ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hh; linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
  have hu2 : u ^ 2 = (h : ℝ) ^ 2 * N₀ ^ 2 / (q : ℝ) ^ 2 := by
    rw [hu, div_pow, mul_pow, sq_abs]
  calc N₀ / q * ‖fourierR ψ (h * N₀ / q)‖
      ≤ N₀ / q * (C₀ * P ^ k * (1 / (u ^ 2 * X ^ (k - 2)))) := by
        gcongr
        exact hd.trans (by gcongr)
    _ = C₀ * P ^ k * ((q : ℝ) / N₀) / X ^ (k - 2) * (1 / (h : ℝ) ^ 2) := by
        rw [hu2]
        field_simp

theorem bracket_poisson (hP : PoissonAPDecay) : ∀ k : ℕ, 2 ≤ k → ∃ C > (0 : ℝ),
    ∀ (N₀ P : ℝ) (ψ : ℝ → ℂ), 0 < N₀ → 1 ≤ P → TemperedOn ψ P k (1/2) 2 →
    ∀ (d e q : ℕ) (c₀ : ℤ), 0 < q →
    (∀ n : ℕ, (d ∣ n ∧ e ∣ n + 2) ↔ (n : ℤ) ≡ c₀ [ZMOD (q : ℤ)]) →
    dens d e = 1 / (q : ℝ) → ∀ M : ℕ,
    ‖bracket N₀ ψ d e - ∑ h ∈ Finset.Icc 1 M, ((N₀ / q : ℝ) : ℂ) *
        (fourierR ψ (h * N₀ / q) *
            Complex.exp (2 * π * Complex.I * (((h : ℤ) * c₀ : ℤ) : ℂ) / (q : ℂ)) +
          fourierR ψ (-(h * N₀ / q)) *
            Complex.exp (2 * π * Complex.I * ((-(h : ℤ) * c₀ : ℤ) : ℂ) / (q : ℂ)))‖
      ≤ C * P ^ k * ((q : ℝ) / N₀) / (((M : ℝ) + 1) * N₀ / q) ^ (k - 2) := by
  intro k hk
  obtain ⟨C₀, hC₀, hdec⟩ := hP (1/2) 2 (by norm_num) (by norm_num) k hk
  -- the constant `∑_{n ≥ 0} 1/(n+1)^2`
  have hsum1 : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).mpr (summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    simpa [Nat.cast_add, Nat.cast_one] using this
  set S₂ : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2 with hS₂
  have hS₂0 : 0 ≤ S₂ := tsum_nonneg fun n => by positivity
  refine ⟨2 * C₀ * S₂ + 1, by positivity, ?_⟩
  intro N₀ P ψ hN₀ hP1 hψ d e q c₀ hq hclass hdens M
  obtain ⟨hdecay, hpois⟩ := hdec ψ P hP1 hψ
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsum := hpois N₀ hN₀ q hq c₀
  set f : ℤ → ℂ := fun h : ℤ => ((N₀ / q : ℝ) : ℂ) * fourierR ψ (h * N₀ / q) *
      Complex.exp (2 * π * Complex.I * ((h * c₀ : ℤ) : ℂ) / (q : ℂ)) with hf
  rw [class_tsum_eq hN₀ hψ.2.1 hclass] at hsum
  set S := ∑ n ∈ (Finset.Icc 1 ⌊2 * N₀⌋₊).filter (fun n => d ∣ n ∧ e ∣ n + 2),
    ψ ((n : ℝ) / N₀) with hS
  -- bracket = S - f 0
  have hf0 : f 0 = (N₀ : ℂ) * fourierR ψ 0 * (dens d e : ℂ) := by
    rw [hf]
    simp only [Int.cast_zero, zero_mul, zero_div, mul_zero,
      Complex.exp_zero, mul_one]
    rw [hdens]
    push_cast
    ring
  have hbr : bracket N₀ ψ d e = S - f 0 := by
    rw [bracket, hf0]
  -- fold over `±h`
  set u : ℕ → ℂ := fun n => f n + f (-n) with hu
  have hU := hsum.nat_add_neg
  have hUs : Summable u := hU.summable
  have hsplit := hUs.sum_add_tsum_nat_add (M + 1)
  rw [hU.tsum_eq] at hsplit
  have hrange : ∑ i ∈ Finset.range (M + 1), u i = 2 * f 0 + ∑ h ∈ Finset.Icc 1 M, u h := by
    rw [Finset.sum_range_succ', Finset.range_eq_Ico, Finset.sum_Ico_add']
    simp only [hu, Nat.cast_zero, neg_zero]
    rw [show Finset.Ico (0 + 1) (M + 1) = Finset.Icc 1 M by
      rw [zero_add]; exact Finset.Ico_add_one_right_eq_Icc 1 M]
    ring
  have hfinite : ∑ h ∈ Finset.Icc 1 M, ((N₀ / q : ℝ) : ℂ) *
        (fourierR ψ (h * N₀ / q) *
            Complex.exp (2 * π * Complex.I * (((h : ℤ) * c₀ : ℤ) : ℂ) / (q : ℂ)) +
          fourierR ψ (-(h * N₀ / q)) *
            Complex.exp (2 * π * Complex.I * ((-(h : ℤ) * c₀ : ℤ) : ℂ) / (q : ℂ)))
      = ∑ h ∈ Finset.Icc 1 M, u h := by
    refine Finset.sum_congr rfl fun h _ => ?_
    simp only [hu, hf, Int.cast_natCast, Int.cast_neg]
    rw [show (-(h : ℝ)) * N₀ / q = -(h * N₀ / q) by ring]
    ring
  rw [hbr, hfinite]
  have htail : S - f 0 - ∑ h ∈ Finset.Icc 1 M, u h = ∑' i : ℕ, u (i + (M + 1)) := by
    rw [hrange] at hsplit
    linear_combination -hsplit
  rw [htail]
  set K : ℝ := C₀ * P ^ k * ((q : ℝ) / N₀) / (((M : ℝ) + 1) * N₀ / q) ^ (k - 2) with hK
  have hK0 : 0 ≤ K := by positivity
  have hbound : ∀ i : ℕ, ‖u (i + (M + 1))‖ ≤ 2 * K * (1 / ((i : ℝ) + 1) ^ 2) := by
    intro i
    have hm : (M : ℝ) + 1 ≤ ((i + (M + 1) : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg i : (0:ℝ) ≤ i)]
    have hm' : ((i : ℝ) + 1) ^ 2 ≤ (((i + (M + 1) : ℕ) : ℤ) : ℝ) ^ 2 := by
      push_cast; gcongr; linarith [(Nat.cast_nonneg M : (0:ℝ) ≤ M)]
    have hipos : (0 : ℝ) < ((i : ℝ) + 1) ^ 2 := by positivity
    have h1 := tail_term hk hN₀ hC₀ hP1 hdecay hq c₀ M ((i + (M + 1) : ℕ) : ℤ)
      (by rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]; exact hm)
    have h2 : ‖f (-((i + (M + 1) : ℕ) : ℤ))‖ ≤ K * (1 / (((i + (M + 1) : ℕ) : ℤ) : ℝ) ^ 2) :=
      (tail_term hk hN₀ hC₀ hP1 hdecay hq c₀ M (-((i + (M + 1) : ℕ) : ℤ))
        (by rw [Int.cast_neg, abs_neg, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]
            exact hm)).trans (le_of_eq (by rw [Int.cast_neg, neg_sq]))
    have h3 : K * (1 / (((i + (M + 1) : ℕ) : ℤ) : ℝ) ^ 2) ≤ K * (1 / ((i : ℝ) + 1) ^ 2) := by
      gcongr
    calc ‖u (i + (M + 1))‖ ≤ ‖f ((i + (M + 1) : ℕ) : ℤ)‖ + ‖f (-((i + (M + 1) : ℕ) : ℤ))‖ := by
          simp only [hu]; push_cast; exact norm_add_le _ _
      _ ≤ K * (1 / (((i + (M + 1) : ℕ) : ℤ) : ℝ) ^ 2) +
            K * (1 / (((i + (M + 1) : ℕ) : ℤ) : ℝ) ^ 2) := by
          exact add_le_add h1 h2
      _ ≤ 2 * K * (1 / ((i : ℝ) + 1) ^ 2) := by linarith
  have hg : HasSum (fun i : ℕ => 2 * K * (1 / ((i : ℝ) + 1) ^ 2)) (2 * K * S₂) :=
    hsum1.hasSum.mul_left (2 * K)
  calc ‖∑' i : ℕ, u (i + (M + 1))‖ ≤ 2 * K * S₂ := tsum_of_norm_bounded hg hbound
    _ = (2 * C₀ * S₂) * P ^ k * ((q : ℝ) / N₀) / (((M : ℝ) + 1) * N₀ / q) ^ (k - 2) := by
        rw [hK]; ring
    _ ≤ (2 * C₀ * S₂ + 1) * P ^ k * ((q : ℝ) / N₀) / (((M : ℝ) + 1) * N₀ / q) ^ (k - 2) := by
        gcongr; linarith

end Poisson

end Level

end MobiusDeterminant
