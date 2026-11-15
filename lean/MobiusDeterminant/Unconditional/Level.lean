import MobiusDeterminant.Unconditional.LevelSmooth
import MobiusDeterminant.Unconditional.LevelSmoothing
import MobiusDeterminant.Unconditional.LevelTempered
import MobiusDeterminant.Unconditional.LevelArith

/-!
# Theorem 1.2: level of distribution `θ < 9/17` for Möbius-weighted divisor pairs

Paper §8, "Proof of Theorem 1.2".  Given `θ < 9/17` fix `η = min(1/100, (9/17 - θ)/3)`, let
`k` be the order of Proposition 8.1 (`smoothDelta_bound`), put `δ' = η/(2(k+1))` and
`ν = N^{-δ'}`.

* Trivial range: `|Σ(K,L)| ≤ KL` since `|r_N| ≤ 1`; so assume `KL > N^{1-δ'}`, whence
  `K, L > N^{1-δ'-θ}`.
* Smoothing (`smoothing_decomp`): `Σ(K,L)` is a sum of `O((log N)^3)` smooth sums `Δ`, up to
  `O(N^{δ'/4}(νN + N/K + N/L + K + L + 2^{j₀})) = O(N^{1-3δ'/4})`, with `2^{j₀} ≍ N^{1-δ'}`.
* Each `Δ` has `D, E ≤ 2N^θ ≤ N₀^{9/17-η}` and weights tempered with `P = c/ν`
  (`piece_tempered`), so `Δ ≪ ν^{-k} N^{1-η} ≤ N^{1-η/2}`.

Altogether `Σ(K,L) ≪ N^{1-δ'/4}`.
-/

open Finset Real
open scoped ArithmeticFunction.Moebius

namespace MobiusDeterminant

namespace Level

namespace Main

/-- Trivial bound `|Σ(K,L)| ≤ KL`, from `|μ| ≤ 1` and `|r_N| ≤ 1`. -/
lemma abs_sum_le (N K L : ℕ) :
    |∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 L, (μ d : ℝ) * (μ e : ℝ) * rem N d e|
      ≤ (K : ℝ) * L := by
  calc _ ≤ ∑ d ∈ Finset.Icc 1 K, |∑ e ∈ Finset.Icc 1 L, (μ d : ℝ) * (μ e : ℝ) * rem N d e| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 L, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun e he => ?_)
      have hd1 : 0 < d := by simp at hd; omega
      have he1 : 0 < e := by simp at he; omega
      rw [abs_mul, abs_mul]
      have h1 : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      have h2 : |(μ e : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      have h3 := abs_rem_le_one N d e hd1 he1
      calc |(μ d : ℝ)| * |(μ e : ℝ)| * |rem N d e| ≤ 1 * 1 * 1 := by
            gcongr
        _ = 1 := by ring
    _ = K * L := by simp

/-- `X ≤ N^α` for all large `N`. -/
lemma exists_nat_rpow_ge {α : ℝ} (hα : 0 < α) (X : ℝ) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → X ≤ (N : ℝ) ^ α := by
  have h := (tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp (h.eventually_ge_atTop X)
  exact ⟨N₁, fun N hN => hN₁ N hN⟩

/-- `log₂ N + 2 ≪_α N^α`. -/
lemma natlog_le {α : ℝ} (hα : 0 < α) :
    ∃ C > (0 : ℝ), ∀ N : ℕ, 1 ≤ N → ((Nat.log 2 N : ℝ) + 2) ≤ C * (N : ℝ) ^ α := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨2 + 1 / (α * Real.log 2), by positivity, fun N hN => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNα : 1 ≤ (N : ℝ) ^ α := Real.one_le_rpow hN1 hα.le
  have hlog : (Nat.log 2 N : ℝ) * Real.log 2 ≤ Real.log N := by
    have h1 : 2 ^ (Nat.log 2 N) ≤ N := Nat.pow_log_le_self 2 (by omega)
    have h2 : ((2 : ℝ) ^ (Nat.log 2 N)) ≤ N := by exact_mod_cast h1
    have := Real.log_le_log (by positivity) h2
    rwa [Real.log_pow] at this
  have hlog2 : Real.log N ≤ (N : ℝ) ^ α / α := Real.log_le_rpow_div (by positivity) hα
  have h3 : (Nat.log 2 N : ℝ) ≤ (N : ℝ) ^ α / (α * Real.log 2) := by
    rw [le_div_iff₀ (by positivity)]
    calc (Nat.log 2 N : ℝ) * (α * Real.log 2) = α * ((Nat.log 2 N : ℝ) * Real.log 2) := by ring
      _ ≤ α * ((N : ℝ) ^ α / α) := by gcongr; exact hlog.trans hlog2
      _ = (N : ℝ) ^ α := by field_simp
  calc ((Nat.log 2 N : ℝ) + 2) ≤ (N : ℝ) ^ α / (α * Real.log 2) + 2 * (N : ℝ) ^ α := by
        linarith
    _ = (2 + 1 / (α * Real.log 2)) * (N : ℝ) ^ α := by ring

/-- `2^a ≤ 2K` for `a ≤ log₂ K + 1`. -/
lemma two_pow_le_two_mul {K a : ℕ} (hK : 1 ≤ K) (ha : a < Nat.log 2 K + 2) :
    (2 : ℝ) ^ a ≤ 2 * K := by
  have h1 : 2 ^ (Nat.log 2 K) ≤ K := Nat.pow_log_le_self 2 (by omega)
  have h2 : 2 ^ a ≤ 2 ^ (Nat.log 2 K + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 2 ^ a ≤ 2 * K := by rw [pow_succ] at h2; omega
  exact_mod_cast h3

/-- The piece scales satisfy the size hypothesis of Proposition 8.1:
`2^a ≤ 2N^θ ≤ (2^l)^{9/17-η}` when `2^l > N^{1-δ'}/2`. -/
lemma scale_le {θ η δ' : ℝ} {N : ℕ} {D N₀ : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 100)
    (hηθ : θ ≤ 9 / 17 - 3 * η) (hδ'0 : 0 < δ') (hδ'η : δ' ≤ η / 2) (hN1 : (1 : ℝ) ≤ N)
    (hN4 : 4 ≤ (N : ℝ) ^ (3 * η / 2)) (hD : D ≤ 2 * (N : ℝ) ^ θ)
    (hN₀ : (N : ℝ) ^ (1 - δ') / 2 ≤ N₀) : D ≤ N₀ ^ (9 / 17 - η) := by
  set c : ℝ := 9 / 17 - η with hc_def
  have hc0 : 0 < c := by rw [hc_def]; linarith
  have hc1 : c ≤ 1 := by rw [hc_def]; linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hA : 0 < (N : ℝ) ^ (1 - δ') / 2 := by positivity
  -- `N₀^c ≥ (N^{1-δ'}/2)^c ≥ N^{(1-δ')c}/2`
  have h1 : ((N : ℝ) ^ (1 - δ') / 2) ^ c ≤ N₀ ^ c :=
    Real.rpow_le_rpow hA.le hN₀ hc0.le
  have h2 : ((N : ℝ) ^ (1 - δ') / 2) ^ c = (N : ℝ) ^ ((1 - δ') * c) / 2 ^ c := by
    rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_mul hNpos.le]
  have h2c : (2 : ℝ) ^ c ≤ 2 := by
    calc (2 : ℝ) ^ c ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hc1
      _ = 2 := Real.rpow_one 2
  have h3 : (N : ℝ) ^ ((1 - δ') * c) / 2 ≤ (N : ℝ) ^ ((1 - δ') * c) / 2 ^ c := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity) h2c
  -- `N^{(1-δ')c} ≥ N^{θ + 3η/2} = N^θ N^{3η/2} ≥ 4 N^θ`
  have hexp : θ + 3 * η / 2 ≤ (1 - δ') * c := by
    have : δ' * c ≤ δ' := by nlinarith
    rw [hc_def] at this ⊢
    nlinarith
  have h4 : (N : ℝ) ^ (θ + 3 * η / 2) ≤ (N : ℝ) ^ ((1 - δ') * c) :=
    Real.rpow_le_rpow_of_exponent_le hN1 hexp
  have h5 : (N : ℝ) ^ (θ + 3 * η / 2) = (N : ℝ) ^ θ * (N : ℝ) ^ (3 * η / 2) :=
    Real.rpow_add hNpos _ _
  have hNθ : 0 ≤ (N : ℝ) ^ θ := by positivity
  calc D ≤ 2 * (N : ℝ) ^ θ := hD
    _ ≤ (N : ℝ) ^ θ * (N : ℝ) ^ (3 * η / 2) / 2 := by nlinarith
    _ = (N : ℝ) ^ (θ + 3 * η / 2) / 2 := by rw [h5]
    _ ≤ (N : ℝ) ^ ((1 - δ') * c) / 2 := by gcongr
    _ ≤ (N : ℝ) ^ ((1 - δ') * c) / 2 ^ c := h3
    _ = ((N : ℝ) ^ (1 - δ') / 2) ^ c := h2.symm
    _ ≤ N₀ ^ c := h1

end Main

end Level

open Level Level.Main in
set_option maxHeartbeats 1000000 in
/-- **Theorem 1.2** (paper): Möbius-weighted divisor pairs have every level of
distribution `θ < 9/17`, assuming the mean-value theorem (Theorem 6.1) and the analytic
toolkit (Mellin separation, Poisson summation in progressions). -/
theorem mobiusPairLevel_of_meanValue (hMV : MeanValueThm) (hM : MellinSeparation)
    (hP : PoissonAPDecay) : ∀ θ : ℝ, θ < 9 / 17 → MobiusPairLevel θ := by
  intro θ hθ
  -- parameters
  set η : ℝ := min (1 / 100) ((9 / 17 - θ) / 3) with hη_def
  have hη0 : 0 < η := lt_min (by norm_num) (by linarith)
  have hη1 : η ≤ 1 / 100 := min_le_left _ _
  have hηθ : θ ≤ 9 / 17 - 3 * η := by
    have := min_le_right (1 / 100 : ℝ) ((9 / 17 - θ) / 3); linarith
  obtain ⟨k, CΔ, hCΔ, hΔ⟩ := smoothDelta_bound hMV hM hP η hη0 hη1
  obtain ⟨c, hc1, hc⟩ := piece_tempered k
  set δ' : ℝ := η / (2 * ((k : ℝ) + 1)) with hδ'_def
  have hk0 : (0 : ℝ) ≤ k := k.cast_nonneg
  have hδ'0 : 0 < δ' := by positivity
  have hδ'η : δ' ≤ η / 2 := by
    rw [hδ'_def, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hkδ' : (k : ℝ) * δ' ≤ η / 2 := by
    rw [hδ'_def, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  obtain ⟨Cs, hCs, hs⟩ := smoothing_decomp (δ' / 4) (by positivity)
  obtain ⟨Cl, hCl, hl⟩ := natlog_le (α := η / 12) (by positivity)
  obtain ⟨N₁, hN₁⟩ := exists_nat_rpow_ge hδ'0 2
  obtain ⟨N₂, hN₂⟩ := exists_nat_rpow_ge (show 0 < 3 * η / 2 by positivity) 4
  set Nst : ℕ := max (max N₁ N₂) 2 with hNst
  set Cfin : ℝ := (Nst : ℝ) ^ 2 + 2 * CΔ * c ^ k * Cl ^ 3 + 6 * Cs with hCfin
  have hNst2 : (2 : ℝ) ≤ Nst := by exact_mod_cast le_max_right _ _
  have hCfin_pos : 0 < Cfin := by positivity
  refine ⟨δ' / 4, by positivity, Cfin, hCfin_pos, ?_⟩
  intro N hN K L hK hL
  set S := ∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 L, (μ d : ℝ) * (μ e : ℝ) * rem N d e
    with hS
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hNpos : (0 : ℝ) < N := by linarith only [hN1]
  have hNpow : 1 ≤ (N : ℝ) ^ (1 - δ' / 4) := Real.one_le_rpow hN1 (by linarith only [hδ'η, hη1, hδ'0])
  have htriv : |S| ≤ (K : ℝ) * L := abs_sum_le N K L
  have hθ1 : θ ≤ 1 := by linarith only [hθ]
  have hNθN : (N : ℝ) ^ θ ≤ N := by
    simpa using Real.rpow_le_rpow_of_exponent_le hN1 hθ1
  have hKN : (K : ℝ) ≤ N := hK.trans hNθN
  have hLN : (L : ℝ) ≤ N := hL.trans hNθN
  have hK0 : (0 : ℝ) ≤ K := K.cast_nonneg
  have hL0 : (0 : ℝ) ≤ L := L.cast_nonneg
  -- Case: `N` below the threshold.
  by_cases hNs : N < Nst
  · have hNlt : (N : ℝ) ≤ Nst := by exact_mod_cast hNs.le
    calc |S| ≤ (K : ℝ) * L := htriv
      _ ≤ (N : ℝ) * N := mul_le_mul hKN hLN hL0 hNpos.le
      _ ≤ (Nst : ℝ) ^ 2 := by nlinarith only [hNlt, hNpos]
      _ ≤ Cfin := by
        have : 0 ≤ 2 * CΔ * c ^ k * Cl ^ 3 := by positivity
        rw [hCfin]; linarith only [this, hCs]
      _ ≤ Cfin * (N : ℝ) ^ (1 - δ' / 4) := le_mul_of_one_le_right hCfin_pos.le hNpow
  push Not at hNs
  have hNN₁ : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hNs
  have hNN₂ : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hNs
  have hNδ : 2 ≤ (N : ℝ) ^ δ' := hN₁ N hNN₁
  have hN4 : 4 ≤ (N : ℝ) ^ (3 * η / 2) := hN₂ N hNN₂
  -- Case: trivial range.
  by_cases hKL : (K : ℝ) * L ≤ (N : ℝ) ^ (1 - δ')
  · calc |S| ≤ (K : ℝ) * L := htriv
      _ ≤ (N : ℝ) ^ (1 - δ') := hKL
      _ ≤ (N : ℝ) ^ (1 - δ' / 4) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [hδ'0])
      _ ≤ Cfin * (N : ℝ) ^ (1 - δ' / 4) := by
        have h0 : 0 ≤ 2 * CΔ * c ^ k * Cl ^ 3 := by positivity
        have : 1 ≤ Cfin := by rw [hCfin]; nlinarith only [h0, hCs, hNst2]
        exact le_mul_of_one_le_left (by positivity) this
  push Not at hKL
  -- Main case.
  have hKpos : 1 ≤ K := by
    rcases Nat.eq_zero_or_pos K with h | h
    · subst h; simp at hKL; linarith only [hKL, Real.rpow_nonneg hNpos.le (1 - δ')]
    · exact h
  have hLpos : 1 ≤ L := by
    rcases Nat.eq_zero_or_pos L with h | h
    · subst h; simp at hKL; linarith only [hKL, Real.rpow_nonneg hNpos.le (1 - δ')]
    · exact h
  have hKNn : K ≤ N := by exact_mod_cast hKN
  have hLNn : L ≤ N := by exact_mod_cast hLN
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hKpos
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hLpos
  -- `N/K, N/L ≤ N^{θ+δ'}`.
  have hNθpos : 0 < (N : ℝ) ^ θ := Real.rpow_pos_of_pos hNpos θ
  have hsplit : (N : ℝ) ^ (1 - δ') = (N : ℝ) ^ (1 - δ' - θ) * (N : ℝ) ^ θ := by
    rw [← Real.rpow_add hNpos]; ring_nf
  have hsplit2 : (N : ℝ) = (N : ℝ) ^ (1 - δ' - θ) * (N : ℝ) ^ (θ + δ') := by
    rw [← Real.rpow_add hNpos]; ring_nf; simp
  have hKbig : (N : ℝ) ^ (1 - δ' - θ) < K := by
    by_contra h
    push Not at h
    have : (K : ℝ) * L ≤ (N : ℝ) ^ (1 - δ' - θ) * (N : ℝ) ^ θ :=
      mul_le_mul h hL hL0 (by positivity)
    linarith only [this, hsplit, hKL]
  have hLbig : (N : ℝ) ^ (1 - δ' - θ) < L := by
    by_contra h
    push Not at h
    have : (K : ℝ) * L ≤ (N : ℝ) ^ θ * (N : ℝ) ^ (1 - δ' - θ) :=
      mul_le_mul hK h hL0 hNθpos.le
    linarith only [this, hsplit, hKL]
  have hNK : (N : ℝ) / K ≤ (N : ℝ) ^ (θ + δ') := by
    rw [div_le_iff₀ (by linarith only [hK1])]
    calc (N : ℝ) = (N : ℝ) ^ (1 - δ' - θ) * (N : ℝ) ^ (θ + δ') := hsplit2
      _ ≤ K * (N : ℝ) ^ (θ + δ') := by gcongr
      _ = (N : ℝ) ^ (θ + δ') * K := by ring
  have hNL : (N : ℝ) / L ≤ (N : ℝ) ^ (θ + δ') := by
    rw [div_le_iff₀ (by linarith only [hL1])]
    calc (N : ℝ) = (N : ℝ) ^ (1 - δ' - θ) * (N : ℝ) ^ (θ + δ') := hsplit2
      _ ≤ L * (N : ℝ) ^ (θ + δ') := by gcongr
      _ = (N : ℝ) ^ (θ + δ') * L := by ring
  have hθδ : θ + δ' ≤ 1 - δ' := by linarith only [hηθ, hδ'η, hη1, hη0]
  have hθδ2 : θ ≤ 1 - δ' := by linarith only [hηθ, hδ'η, hη1, hη0]
  have hpow1 : (N : ℝ) ^ (θ + δ') ≤ (N : ℝ) ^ (1 - δ') :=
    Real.rpow_le_rpow_of_exponent_le hN1 hθδ
  have hpow2 : (N : ℝ) ^ θ ≤ (N : ℝ) ^ (1 - δ') :=
    Real.rpow_le_rpow_of_exponent_le hN1 hθδ2
  -- `ν = N^{-δ'}`.
  set ν : ℝ := (N : ℝ) ^ (-δ') with hν_def
  have hνpos : 0 < ν := Real.rpow_pos_of_pos hNpos _
  have hνmul : ν * (N : ℝ) ^ δ' = 1 := by
    rw [hν_def, ← Real.rpow_add hNpos]; simp
  have hν_half : ν ≤ 1 / 2 := by
    have : ν * 2 ≤ ν * (N : ℝ) ^ δ' := by gcongr
    linarith only [this, hνmul]
  have hν1 : ν ≤ 1 := by linarith only [hν_half]
  have hνN : ν * N = (N : ℝ) ^ (1 - δ') := by
    rw [hν_def, show (1 - δ') = -δ' + 1 by ring, Real.rpow_add hNpos, Real.rpow_one]
  -- `j₀` with `N^{1-δ'}/2 < 2^{j₀} ≤ N^{1-δ'}`.
  have hN1δ : 2 ≤ (N : ℝ) ^ (1 - δ') := by
    calc (2 : ℝ) ≤ (N : ℝ) ^ δ' := hNδ
      _ ≤ (N : ℝ) ^ (1 - δ') := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [hδ'η, hη1])
  set m : ℕ := ⌊(N : ℝ) ^ (1 - δ')⌋₊ with hm_def
  have hm2 : 2 ≤ m := Nat.le_floor (by exact_mod_cast hN1δ)
  set j₀ : ℕ := Nat.log 2 m with hj₀_def
  have hj₀1 : 1 ≤ j₀ := Nat.log_pos (by norm_num) hm2
  have hj₀m : 2 ^ j₀ ≤ m := Nat.pow_log_le_self 2 (by omega)
  have hmle : (m : ℝ) ≤ (N : ℝ) ^ (1 - δ') := Nat.floor_le (by positivity)
  have h2j₀ : (2 : ℝ) ^ j₀ ≤ (N : ℝ) ^ (1 - δ') := by
    have : ((2 ^ j₀ : ℕ) : ℝ) ≤ m := by exact_mod_cast hj₀m
    push_cast at this
    linarith only [this, hmle]
  have h2j₀N : 2 ^ j₀ ≤ N := by
    have h' : (N : ℝ) ^ (1 - δ') ≤ N := by
      simpa using Real.rpow_le_rpow_of_exponent_le hN1 (show 1 - δ' ≤ 1 by linarith only [hδ'0])
    have : ((2 ^ j₀ : ℕ) : ℝ) ≤ N := by push_cast; linarith only [h', h2j₀]
    exact_mod_cast this
  have h2j₀big : (N : ℝ) ^ (1 - δ') / 2 < (2 : ℝ) ^ j₀ := by
    have h1 : m < 2 ^ (j₀ + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
    have h2 : (N : ℝ) ^ (1 - δ') < m + 1 := Nat.lt_floor_add_one _
    have h3 : (m : ℝ) + 1 ≤ 2 ^ (j₀ + 1) := by exact_mod_cast h1
    rw [pow_succ] at h3
    linarith only [h2, h3]
  -- The smoothing decomposition.
  have hdec := hs N K L j₀ ν hN hKpos hLpos hKNn hLNn hνpos hν_half hj₀1 h2j₀N
  set X := ∑ a ∈ Finset.range (Nat.log 2 K + 2), ∑ b ∈ Finset.range (Nat.log 2 L + 2),
      ∑ l ∈ Finset.Ico j₀ (Nat.log 2 N + 2),
        smoothDelta ((2 : ℝ) ^ l) ((2 : ℝ) ^ a) ((2 : ℝ) ^ b)
          (piece (N : ℝ) ν ((2 : ℝ) ^ l)) (piece (K : ℝ) ν ((2 : ℝ) ^ a))
          (piece (L : ℝ) ν ((2 : ℝ) ^ b)) with hX
  -- error term
  have herr : ‖((S : ℝ) : ℂ) - X‖ ≤ 6 * Cs * (N : ℝ) ^ (1 - δ' / 4) := by
    refine hdec.trans ?_
    have hKle : (K : ℝ) ≤ (N : ℝ) ^ (1 - δ') := hK.trans hpow2
    have hLle : (L : ℝ) ≤ (N : ℝ) ^ (1 - δ') := hL.trans hpow2
    have hsum : ν * N + N / K + N / L + K + L + 2 ^ j₀ ≤ 6 * (N : ℝ) ^ (1 - δ') := by
      rw [hνN]; linarith only [hNK, hNL, hpow1, hKle, hLle, h2j₀]
    have hprod : (N : ℝ) ^ (δ' / 4) * (N : ℝ) ^ (1 - δ') = (N : ℝ) ^ (1 - 3 * δ' / 4) := by
      rw [← Real.rpow_add hNpos]; ring_nf
    have hmono : (N : ℝ) ^ (1 - 3 * δ' / 4) ≤ (N : ℝ) ^ (1 - δ' / 4) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [hδ'0])
    calc Cs * (N : ℝ) ^ (δ' / 4) * (ν * N + N / K + N / L + K + L + 2 ^ j₀)
        ≤ Cs * (N : ℝ) ^ (δ' / 4) * (6 * (N : ℝ) ^ (1 - δ')) := by gcongr
      _ = 6 * Cs * ((N : ℝ) ^ (δ' / 4) * (N : ℝ) ^ (1 - δ')) := by ring
      _ = 6 * Cs * (N : ℝ) ^ (1 - 3 * δ' / 4) := by rw [hprod]
      _ ≤ 6 * Cs * (N : ℝ) ^ (1 - δ' / 4) := by gcongr
  -- each piece
  have hP1 : 1 ≤ c / ν := by rw [le_div_iff₀ hνpos]; linarith only [hc1, hν1]
  have hcν : (c / ν) ^ k ≤ c ^ k * (N : ℝ) ^ (η / 2) := by
    have h1 : c / ν = c * (N : ℝ) ^ δ' := by
      rw [div_eq_iff hνpos.ne']
      linear_combination (-c) * hνmul
    rw [h1, mul_pow]
    gcongr
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [hkδ'])
  have hpiece : ∀ a ∈ Finset.range (Nat.log 2 K + 2), ∀ b ∈ Finset.range (Nat.log 2 L + 2),
      ∀ l ∈ Finset.Ico j₀ (Nat.log 2 N + 2),
      ‖smoothDelta ((2 : ℝ) ^ l) ((2 : ℝ) ^ a) ((2 : ℝ) ^ b)
          (piece (N : ℝ) ν ((2 : ℝ) ^ l)) (piece (K : ℝ) ν ((2 : ℝ) ^ a))
          (piece (L : ℝ) ν ((2 : ℝ) ^ b))‖ ≤ 2 * CΔ * c ^ k * (N : ℝ) ^ (1 - η / 2) := by
    intro a ha b hb l hl
    rw [Finset.mem_range] at ha hb
    rw [Finset.mem_Ico] at hl
    have hl2 : (2 : ℝ) ≤ 2 ^ l := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ l := pow_le_pow_right₀ (by norm_num) (by omega)
    have hlN : (2 : ℝ) ^ l ≤ 2 * N := two_pow_le_two_mul (by omega) hl.2
    have hlbig : (N : ℝ) ^ (1 - δ') / 2 ≤ 2 ^ l := by
      have : (2 : ℝ) ^ j₀ ≤ 2 ^ l := pow_le_pow_right₀ (by norm_num) hl.1
      linarith only [this, h2j₀big]
    have haK : (2 : ℝ) ^ a ≤ 2 * K := two_pow_le_two_mul hKpos ha
    have hbL : (2 : ℝ) ^ b ≤ 2 * L := two_pow_le_two_mul hLpos hb
    have ha1 : (1 : ℝ) ≤ 2 ^ a := one_le_pow₀ (by norm_num)
    have hb1 : (1 : ℝ) ≤ 2 ^ b := one_le_pow₀ (by norm_num)
    have hDle : (2 : ℝ) ^ a ≤ ((2 : ℝ) ^ l) ^ (9 / 17 - η) :=
      scale_le hη0 hη1 hηθ hδ'0 hδ'η hN1 hN4 (by linarith only [haK, hK]) hlbig
    have hEle : (2 : ℝ) ^ b ≤ ((2 : ℝ) ^ l) ^ (9 / 17 - η) :=
      scale_le hη0 hη1 hηθ hδ'0 hδ'η hN1 hN4 (by linarith only [hbL, hL]) hlbig
    have hψ := hc (N : ℝ) ν ((2 : ℝ) ^ l) hνpos hν1 hNpos (by positivity) hlN
    have hφ₁ := hc (K : ℝ) ν ((2 : ℝ) ^ a) hνpos hν1 (by linarith only [hK1]) (by positivity) haK
    have hφ₂ := hc (L : ℝ) ν ((2 : ℝ) ^ b) hνpos hν1 (by linarith only [hL1]) (by positivity) hbL
    have hb := hΔ ((2 : ℝ) ^ l) ((2 : ℝ) ^ a) ((2 : ℝ) ^ b) (c / ν) _ _ _ hl2 ha1 hb1
      hDle hEle hP1 hψ hφ₁ hφ₂
    refine hb.trans ?_
    have hN0pow : ((2 : ℝ) ^ l) ^ (1 - η) ≤ 2 * (N : ℝ) ^ (1 - η) := by
      calc ((2 : ℝ) ^ l) ^ (1 - η) ≤ (2 * (N : ℝ)) ^ (1 - η) :=
            Real.rpow_le_rpow (by positivity) hlN (by linarith only [hη1])
        _ = 2 ^ (1 - η) * (N : ℝ) ^ (1 - η) := Real.mul_rpow (by norm_num) hNpos.le
        _ ≤ 2 * (N : ℝ) ^ (1 - η) := by
          gcongr
          calc (2 : ℝ) ^ (1 - η) ≤ 2 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hη0])
            _ = 2 := Real.rpow_one 2
    have hprod : (N : ℝ) ^ (η / 2) * (N : ℝ) ^ (1 - η) = (N : ℝ) ^ (1 - η / 2) := by
      rw [← Real.rpow_add hNpos]; ring_nf
    calc CΔ * (c / ν) ^ k * ((2 : ℝ) ^ l) ^ (1 - η)
        ≤ CΔ * (c ^ k * (N : ℝ) ^ (η / 2)) * (2 * (N : ℝ) ^ (1 - η)) := by
          gcongr
      _ = 2 * CΔ * c ^ k * ((N : ℝ) ^ (η / 2) * (N : ℝ) ^ (1 - η)) := by ring
      _ = 2 * CΔ * c ^ k * (N : ℝ) ^ (1 - η / 2) := by rw [hprod]
  -- number of pieces
  have hcount : ((Finset.range (Nat.log 2 K + 2)).card : ℝ) *
      ((Finset.range (Nat.log 2 L + 2)).card : ℝ) *
      ((Finset.Ico j₀ (Nat.log 2 N + 2)).card : ℝ) ≤ Cl ^ 3 * (N : ℝ) ^ (η / 4) := by
    simp only [Finset.card_range, Nat.card_Ico]
    have hlogK : Nat.log 2 K ≤ Nat.log 2 N := Nat.log_mono_right hKNn
    have hlogL : Nat.log 2 L ≤ Nat.log 2 N := Nat.log_mono_right hLNn
    have hlN := hl N (by omega)
    have h1 : ((Nat.log 2 K + 2 : ℕ) : ℝ) ≤ (Nat.log 2 N : ℝ) + 2 := by
      push_cast; exact_mod_cast (by omega : Nat.log 2 K + 2 ≤ Nat.log 2 N + 2)
    have h2 : ((Nat.log 2 L + 2 : ℕ) : ℝ) ≤ (Nat.log 2 N : ℝ) + 2 := by
      push_cast; exact_mod_cast (by omega : Nat.log 2 L + 2 ≤ Nat.log 2 N + 2)
    have h3 : ((Nat.log 2 N + 2 - j₀ : ℕ) : ℝ) ≤ (Nat.log 2 N : ℝ) + 2 := by
      have : Nat.log 2 N + 2 - j₀ ≤ Nat.log 2 N + 2 := Nat.sub_le _ _
      exact_mod_cast this
    have hcube : ((Nat.log 2 N : ℝ) + 2) ^ 3 ≤ (Cl * (N : ℝ) ^ (η / 12)) ^ 3 := by
      gcongr
    have hpow3 : (Cl * (N : ℝ) ^ (η / 12)) ^ 3 = Cl ^ 3 * (N : ℝ) ^ (η / 4) := by
      rw [mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ (η / 12)) 3, ← Real.rpow_mul hNpos.le]
      congr 2
      push_cast
      ring
    calc ((Nat.log 2 K + 2 : ℕ) : ℝ) * ((Nat.log 2 L + 2 : ℕ) : ℝ) *
          ((Nat.log 2 N + 2 - j₀ : ℕ) : ℝ)
        ≤ ((Nat.log 2 N : ℝ) + 2) * ((Nat.log 2 N : ℝ) + 2) * ((Nat.log 2 N : ℝ) + 2) := by
          gcongr
      _ = ((Nat.log 2 N : ℝ) + 2) ^ 3 := by ring
      _ ≤ Cl ^ 3 * (N : ℝ) ^ (η / 4) := hcube.trans hpow3.le
  have hXbound : ‖X‖ ≤ 2 * CΔ * c ^ k * Cl ^ 3 * (N : ℝ) ^ (1 - δ' / 4) := by
    have hB0 : 0 ≤ 2 * CΔ * c ^ k * (N : ℝ) ^ (1 - η / 2) := by positivity
    calc ‖X‖ ≤ ∑ a ∈ Finset.range (Nat.log 2 K + 2), ∑ b ∈ Finset.range (Nat.log 2 L + 2),
          ∑ l ∈ Finset.Ico j₀ (Nat.log 2 N + 2), 2 * CΔ * c ^ k * (N : ℝ) ^ (1 - η / 2) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a ha => ?_)
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b hb => ?_)
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l hl => ?_)
          exact hpiece a ha b hb l hl
      _ = ((Finset.range (Nat.log 2 K + 2)).card : ℝ) *
            ((Finset.range (Nat.log 2 L + 2)).card : ℝ) *
            ((Finset.Ico j₀ (Nat.log 2 N + 2)).card : ℝ) *
            (2 * CΔ * c ^ k * (N : ℝ) ^ (1 - η / 2)) := by
          simp only [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ Cl ^ 3 * (N : ℝ) ^ (η / 4) * (2 * CΔ * c ^ k * (N : ℝ) ^ (1 - η / 2)) := by
          gcongr
      _ = 2 * CΔ * c ^ k * Cl ^ 3 * ((N : ℝ) ^ (η / 4) * (N : ℝ) ^ (1 - η / 2)) := by ring
      _ = 2 * CΔ * c ^ k * Cl ^ 3 * (N : ℝ) ^ (1 - η / 4) := by
          rw [← Real.rpow_add hNpos]; ring_nf
      _ ≤ 2 * CΔ * c ^ k * Cl ^ 3 * (N : ℝ) ^ (1 - δ' / 4) := by
          gcongr 2 * CΔ * c ^ k * Cl ^ 3 * ?_
          exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [hδ'η, hη0])
  -- conclusion
  have hSnorm : |S| = ‖((S : ℝ) : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
  calc |S| = ‖((S : ℝ) : ℂ)‖ := hSnorm
    _ ≤ ‖((S : ℝ) : ℂ) - X‖ + ‖X‖ := by
        have := norm_add_le (((S : ℝ) : ℂ) - X) X
        simpa using this
    _ ≤ 6 * Cs * (N : ℝ) ^ (1 - δ' / 4) + 2 * CΔ * c ^ k * Cl ^ 3 * (N : ℝ) ^ (1 - δ' / 4) :=
        add_le_add herr hXbound
    _ ≤ Cfin * (N : ℝ) ^ (1 - δ' / 4) := by
        rw [hCfin]
        have : 0 ≤ (N : ℝ) ^ (1 - δ' / 4) := by positivity
        nlinarith only [mul_nonneg (sq_nonneg (Nst : ℝ)) this]

end MobiusDeterminant
