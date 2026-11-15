import MobiusDeterminant.Unconditional.LevelDefs
import MobiusDeterminant.Unconditional.LevelArith
import MobiusDeterminant.Unconditional.LevelCutoff

/-!
# Smoothing the sharp cutoffs (paper §8, proof of Theorem 1.2)

We prove `smoothing_decomp`: the sharp sum `Σ(K,L) = ∑_{d ≤ K, e ≤ L} μ(d) μ(e) r_N(d,e)`
equals the sum of the smooth sums `Δ` over the dyadic pieces, up to an error
`O(N^ε (νN + N/K + N/L + K + L + 2^{j₀}))`.

Steps:
1. (exact identity) `∑_{a,b,l} Δ_{a,b,l} = ∑_{d ≤ K, e ≤ L} μμ t_K(d) t_L(e) G(d,e)` with
   `G(d,e) = ∑_{n ≤ N, d ∣ n, e ∣ n+2} Ψ(n) - Z ϱ(d,e)`, `Z = ∑_l 2^l ψ̂_l(0)`;
2. (errors) `|1 - t_K t_L| ≤ 1_{d > (1-ν)K} + 1_{e > (1-ν)L}`, `|r_N| ≤ C_N + N ϱ`, and
   `r_N - G = ∑_{n} (1 - Ψ(n)) - (N - Z) ϱ`; the resulting sums are bounded with the divisor
   bound and harmonic sums.
-/

open Finset Real
open scoped ArithmeticFunction.Moebius

namespace MobiusDeterminant

namespace Level

namespace Smoothing

open Cutoff

/-! ## Range manipulations -/

theorem sum_Icc_eq_of_vanish {g : ℕ → ℂ} {M M₁ M₂ : ℕ} (h₁ : M ≤ M₁) (h₂ : M ≤ M₂)
    (hg : ∀ d, M < d → g d = 0) : ∑ d ∈ Finset.Icc 1 M₁, g d = ∑ d ∈ Finset.Icc 1 M₂, g d := by
  have key : ∀ M', M ≤ M' → ∑ d ∈ Finset.Icc 1 M', g d = ∑ d ∈ Finset.Icc 1 M, g d := by
    intro M' hM'
    symm
    apply Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hM')
    intro d hd hdn
    apply hg
    simp only [Finset.mem_Icc, not_and, not_le] at hd hdn
    exact hdn hd.1
  rw [key M₁ h₁, key M₂ h₂]

theorem piece_div_eq_zero {K ν : ℝ} (hν : 0 < ν) (hK : 0 < K) (a d : ℕ)
    (hd : K ≤ d ∨ 2 * 2 ^ a ≤ (d : ℝ)) : piece K ν ((2 : ℝ) ^ a) ((d : ℝ) / 2 ^ a) = 0 := by
  rw [piece_apply_div K ν _ _ (by positivity)]
  rcases hd with hd | hd
  · rw [topCut_eq_zero hν hK hd]
    simp
  · rw [dyBump_eq_zero_of_ge]
    · simp
    · rw [le_div_iff₀ (by positivity)]
      linarith

theorem piece_div_vanish {K : ℕ} {ν : ℝ} (hν : 0 < ν) (hK : 1 ≤ K) (a d : ℕ)
    (hd : min K ⌊2 * (2 : ℝ) ^ a⌋₊ < d) :
    piece (K : ℝ) ν ((2 : ℝ) ^ a) ((d : ℝ) / 2 ^ a) = 0 := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  apply piece_div_eq_zero hν hK' a d
  rcases min_lt_iff.mp hd with h1 | h1
  · left
    exact_mod_cast h1.le
  · right
    exact (Nat.lt_of_floor_lt h1).le

/-- The `n`-part of a bracket at a piece. -/
noncomputable def Bn (N : ℕ) (ν : ℝ) (l d e : ℕ) : ℂ :=
  (∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n ∧ e ∣ n + 2),
      (((dyBump ((n : ℝ) / 2 ^ l) * topCut (N : ℝ) ν (n : ℝ)) : ℝ) : ℂ))
    - (((2 : ℝ) ^ l : ℝ) : ℂ) * fourierR (piece (N : ℝ) ν ((2 : ℝ) ^ l)) 0 * (dens d e : ℂ)

theorem bracket_piece {N : ℕ} {ν : ℝ} (hν : 0 < ν) (hN : 1 ≤ N) (l d e : ℕ) :
    bracket ((2 : ℝ) ^ l) (piece (N : ℝ) ν ((2 : ℝ) ^ l)) d e = Bn N ν l d e := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  unfold bracket Bn
  congr 1
  rw [Finset.sum_filter, Finset.sum_filter]
  rw [sum_Icc_eq_of_vanish (M := min N ⌊2 * (2 : ℝ) ^ l⌋₊) (min_le_right _ _) (min_le_left _ _)]
  · apply Finset.sum_congr rfl
    intro n _
    split_ifs
    · rw [piece_apply_div _ _ _ _ (by positivity)]
    · rfl
  · intro n hn
    rw [piece_div_vanish hν hN l n hn]
    simp

theorem smoothDelta_piece {N K L : ℕ} {ν : ℝ} (hν : 0 < ν) (hN : 1 ≤ N) (hK : 1 ≤ K)
    (hL : 1 ≤ L) (a b l : ℕ) :
    smoothDelta ((2 : ℝ) ^ l) ((2 : ℝ) ^ a) ((2 : ℝ) ^ b)
        (piece (N : ℝ) ν ((2 : ℝ) ^ l)) (piece (K : ℝ) ν ((2 : ℝ) ^ a))
        (piece (L : ℝ) ν ((2 : ℝ) ^ b))
      = ∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 L,
          (μ d : ℂ) * (μ e : ℂ) * piece (K : ℝ) ν ((2 : ℝ) ^ a) ((d : ℝ) / 2 ^ a) *
            piece (L : ℝ) ν ((2 : ℝ) ^ b) ((e : ℝ) / 2 ^ b) * Bn N ν l d e := by
  unfold smoothDelta
  rw [sum_Icc_eq_of_vanish (M := min K ⌊2 * (2 : ℝ) ^ a⌋₊) (min_le_right _ _) (min_le_left _ _)]
  · apply Finset.sum_congr rfl
    intro d _
    rw [sum_Icc_eq_of_vanish (M := min L ⌊2 * (2 : ℝ) ^ b⌋₊) (min_le_right _ _)
      (min_le_left _ _)]
    · apply Finset.sum_congr rfl
      intro e _
      rw [bracket_piece hν hN]
    · intro e he
      rw [piece_div_vanish hν hL b e he]
      simp
  · intro d hd
    rw [piece_div_vanish hν hK a d hd]
    simp

/-- A five-fold rearrangement of finite sums. -/
theorem rearrange {α β γ δ ε : Type*} (A : Finset α) (B : Finset β) (Λ : Finset γ)
    (Ds : Finset δ) (Es : Finset ε) (c : δ → ε → ℂ) (X : α → δ → ℂ) (Y : β → ε → ℂ)
    (W : γ → δ → ε → ℂ) :
    ∑ a ∈ A, ∑ b ∈ B, ∑ l ∈ Λ, ∑ d ∈ Ds, ∑ e ∈ Es, c d e * X a d * Y b e * W l d e =
      ∑ d ∈ Ds, ∑ e ∈ Es, c d e * (∑ a ∈ A, X a d) * (∑ b ∈ B, Y b e) *
        (∑ l ∈ Λ, W l d e) := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  simp_rw [Finset.sum_comm (s := Λ) (t := Ds), Finset.sum_comm (s := B) (t := Ds),
    Finset.sum_comm (s := A) (t := Ds), Finset.sum_comm (s := Λ) (t := Es),
    Finset.sum_comm (s := B) (t := Es), Finset.sum_comm (s := A) (t := Es)]
  simp_rw [Finset.sum_comm (s := Λ) (t := B), Finset.sum_comm (s := Λ) (t := A),
    Finset.sum_comm (s := B) (t := A)]

theorem le_two_pow_log (K : ℕ) : (K : ℝ) ≤ 2 ^ (Nat.log 2 K + 2) / 2 := by
  have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) K
  have h' : (K : ℝ) < 2 ^ (Nat.log 2 K + 1) := by exact_mod_cast h
  rw [pow_succ 2 (Nat.log 2 K + 1)]
  linarith

/-- The zero modes `Z = ∑_l 2^l ψ̂_l(0)`. -/
noncomputable def Zsum (N : ℕ) (ν : ℝ) (j₀ J : ℕ) : ℂ :=
  ∑ l ∈ Finset.Ico j₀ J, (((2 : ℝ) ^ l : ℝ) : ℂ) * fourierR (piece (N : ℝ) ν ((2 : ℝ) ^ l)) 0

/-- `G(d,e) = ∑_{n ≤ N, d ∣ n, e ∣ n+2} Ψ(n) - Z ϱ(d,e)`. -/
noncomputable def Gfun (N : ℕ) (ν : ℝ) (j₀ J d e : ℕ) : ℂ :=
  (∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n ∧ e ∣ n + 2),
      ((psiCut (N : ℝ) ν j₀ J (n : ℝ) : ℝ) : ℂ)) - Zsum N ν j₀ J * (dens d e : ℂ)

theorem sum_Bn (N : ℕ) (ν : ℝ) (j₀ J d e : ℕ) :
    ∑ l ∈ Finset.Ico j₀ J, Bn N ν l d e = Gfun N ν j₀ J d e := by
  unfold Bn Gfun Zsum psiCut
  rw [Finset.sum_sub_distrib, Finset.sum_comm, ← Finset.sum_mul]
  push_cast
  rfl

/-- Step 1: the exact identity. -/
theorem decomp_identity {N K L : ℕ} {ν : ℝ} (hν : 0 < ν) (hN : 1 ≤ N) (hK : 1 ≤ K)
    (hL : 1 ≤ L) (j₀ : ℕ) :
    ∑ a ∈ Finset.range (Nat.log 2 K + 2), ∑ b ∈ Finset.range (Nat.log 2 L + 2),
        ∑ l ∈ Finset.Ico j₀ (Nat.log 2 N + 2),
          smoothDelta ((2 : ℝ) ^ l) ((2 : ℝ) ^ a) ((2 : ℝ) ^ b)
            (piece (N : ℝ) ν ((2 : ℝ) ^ l)) (piece (K : ℝ) ν ((2 : ℝ) ^ a))
            (piece (L : ℝ) ν ((2 : ℝ) ^ b))
      = ∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 L,
          (μ d : ℂ) * (μ e : ℂ) * (topCut (K : ℝ) ν d : ℂ) * (topCut (L : ℝ) ν e : ℂ) *
            Gfun N ν j₀ (Nat.log 2 N + 2) d e := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  simp_rw [smoothDelta_piece hν hN hK hL]
  rw [rearrange (c := fun d e => (μ d : ℂ) * (μ e : ℂ))
    (X := fun a d => piece (K : ℝ) ν ((2 : ℝ) ^ a) ((d : ℝ) / 2 ^ a))
    (Y := fun b e => piece (L : ℝ) ν ((2 : ℝ) ^ b) ((e : ℝ) / 2 ^ b))
    (W := fun l d e => Bn N ν l d e)]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast (Finset.mem_Icc.mp he).1
  rw [sum_piece_range hν hK' (le_two_pow_log K) hd1, sum_piece_range hν hL' (le_two_pow_log L) he1,
    sum_Bn]

/-! ## Counting lemmas -/

/-- Indicator of the boundary range `d > (1-ν)K`. -/
noncomputable def ind (K : ℕ) (ν : ℝ) (d : ℕ) : ℝ :=
  if (1 - ν) * (K : ℝ) < (d : ℝ) then 1 else 0

theorem ind_nonneg (K : ℕ) (ν : ℝ) (d : ℕ) : 0 ≤ ind K ν d := by
  unfold ind; split_ifs <;> norm_num

theorem ind_le_one (K : ℕ) (ν : ℝ) (d : ℕ) : ind K ν d ≤ 1 := by
  unfold ind; split_ifs <;> norm_num

theorem card_filter_gt_le (K : ℕ) {ν : ℝ} (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) :
    ((((Finset.Icc 1 K).filter (fun d : ℕ => (1 - ν) * (K : ℝ) < (d : ℝ))).card : ℕ) : ℝ)
      ≤ ν * K + 1 := by
  set m := ⌊(1 - ν) * (K : ℝ)⌋₊ with hm
  have hsub : (Finset.Icc 1 K).filter (fun d : ℕ => (1 - ν) * (K : ℝ) < (d : ℝ))
      ⊆ Finset.Icc (m + 1) K := by
    intro d hd
    simp only [Finset.mem_filter, Finset.mem_Icc] at hd ⊢
    refine ⟨?_, hd.1.2⟩
    have h1 : (m : ℝ) ≤ (1 - ν) * K := Nat.floor_le (by nlinarith)
    have h2 : (m : ℝ) < d := lt_of_le_of_lt h1 hd.2
    exact_mod_cast h2
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hcard
  have hmK : m ≤ K := by
    have : (m : ℝ) ≤ K := by
      calc (m : ℝ) ≤ (1 - ν) * K := Nat.floor_le (by nlinarith)
        _ ≤ K := by nlinarith
    exact_mod_cast this
  have hlt : (1 - ν) * (K : ℝ) < m + 1 := Nat.lt_floor_add_one _
  have : (((K + 1 - (m + 1) : ℕ)) : ℝ) = K - m := by
    rw [show K + 1 - (m + 1) = K - m by omega, Nat.cast_sub hmK]
  calc _ ≤ (((K + 1 - (m + 1) : ℕ)) : ℝ) := by exact_mod_cast hcard
    _ = K - m := this
    _ ≤ ν * K + 1 := by linarith

theorem sum_ind_div_le (K : ℕ) (hK : 1 ≤ K) {ν : ℝ} (hν0 : 0 < ν) (hν : ν ≤ 1 / 2) :
    ∑ d ∈ Finset.Icc 1 K, ind K ν d / d ≤ 2 * ν + 2 / K := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have h1 : ∀ d ∈ Finset.Icc 1 K, ind K ν d / d ≤
      if (1 - ν) * (K : ℝ) < (d : ℝ) then 2 / (K : ℝ) else 0 := by
    intro d hd
    unfold ind
    split_ifs with h
    · rw [div_le_div_iff₀ (by linarith [show (0:ℝ) ≤ (1 - ν) * K by nlinarith]) hK']
      nlinarith
    · simp
  calc _ ≤ ∑ d ∈ Finset.Icc 1 K, if (1 - ν) * (K : ℝ) < (d : ℝ) then 2 / (K : ℝ) else 0 :=
        Finset.sum_le_sum h1
    _ = 2 / K * (((Finset.Icc 1 K).filter
          (fun d : ℕ => (1 - ν) * (K : ℝ) < (d : ℝ))).card : ℕ) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ 2 / K * (ν * K + 1) := by
        apply mul_le_mul_of_nonneg_left (card_filter_gt_le K hν0.le (by linarith))
        positivity
    _ = 2 * ν + 2 / K := by field_simp

theorem card_filter_dvd_le (S : Finset ℕ) {m : ℕ} (hm : m ≠ 0) :
    (S.filter (· ∣ m)).card ≤ m.divisors.card := by
  apply Finset.card_le_card
  intro x hx
  rw [Finset.mem_filter] at hx
  exact Nat.mem_divisors.mpr ⟨hx.2, hm⟩

theorem card_Icc_filter_dvd (N d : ℕ) : ((Finset.Icc 1 N).filter (d ∣ ·)).card = N / d := by
  rw [show Finset.Icc 1 N = Finset.Ioc 0 N from rfl]
  exact Nat.Ioc_filter_dvd_card_eq_div N d

theorem card_Icc_filter_dvd_add_two_le (N e : ℕ) :
    ((Finset.Icc 1 N).filter (fun n => e ∣ n + 2)).card ≤ (N + 2) / e := by
  rw [← Nat.Ioc_filter_dvd_card_eq_div (N + 2) e]
  apply Finset.card_le_card_of_injOn (fun n => n + 2)
  · intro n hn
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hn
    simp only [Finset.coe_filter, Finset.mem_Ioc, Set.mem_ofPred_eq]
    exact ⟨⟨by omega, by omega⟩, hn.2⟩
  · intro a _ b _ h
    simpa using h

theorem pairCount_eq_sum (N d e : ℕ) :
    (pairCount N d e : ℝ) =
      ∑ n ∈ Finset.Icc 1 N, if d ∣ n ∧ e ∣ n + 2 then (1 : ℝ) else 0 := by
  unfold pairCount
  rw [Finset.card_filter]
  push_cast
  rfl

theorem sum_pairCount_e_le {N L d : ℕ} {T : ℝ}
    (hT : ∀ m, 1 ≤ m → m ≤ N + 2 → (m.divisors.card : ℝ) ≤ T) :
    ∑ e ∈ Finset.Icc 1 L, (pairCount N d e : ℝ) ≤ T * ((N / d : ℕ) : ℝ) := by
  simp_rw [pairCount_eq_sum]
  rw [Finset.sum_comm]
  have h2 : ∀ n ∈ Finset.Icc 1 N,
      (∑ e ∈ Finset.Icc 1 L, if d ∣ n ∧ e ∣ n + 2 then (1:ℝ) else 0)
        ≤ if d ∣ n then T else 0 := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    split_ifs with hdn
    · simp only [hdn, true_and]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      calc (((Finset.Icc 1 L).filter (fun e => e ∣ n + 2)).card : ℝ)
          ≤ ((n + 2).divisors.card : ℝ) := by
            exact_mod_cast card_filter_dvd_le (Finset.Icc 1 L) (m := n + 2) (by omega)
        _ ≤ T := hT (n + 2) (by omega) (by omega)
    · simp [hdn]
  calc _ ≤ ∑ n ∈ Finset.Icc 1 N, if d ∣ n then T else 0 := Finset.sum_le_sum h2
    _ = T * (((Finset.Icc 1 N).filter (d ∣ ·)).card : ℝ) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ = T * ((N / d : ℕ) : ℝ) := by rw [card_Icc_filter_dvd]

theorem sum_pairCount_d_le {N K e : ℕ} {T : ℝ}
    (hT : ∀ m, 1 ≤ m → m ≤ N + 2 → (m.divisors.card : ℝ) ≤ T) (hT0 : 0 ≤ T) :
    ∑ d ∈ Finset.Icc 1 K, (pairCount N d e : ℝ) ≤ T * (((N + 2) / e : ℕ) : ℝ) := by
  simp_rw [pairCount_eq_sum]
  rw [Finset.sum_comm]
  have h2 : ∀ n ∈ Finset.Icc 1 N,
      (∑ d ∈ Finset.Icc 1 K, if d ∣ n ∧ e ∣ n + 2 then (1:ℝ) else 0)
        ≤ if e ∣ n + 2 then T else 0 := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    split_ifs with hen
    · simp only [hen, and_true]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      calc (((Finset.Icc 1 K).filter (fun d => d ∣ n)).card : ℝ)
          ≤ (n.divisors.card : ℝ) := by
            exact_mod_cast card_filter_dvd_le (Finset.Icc 1 K) (m := n) (by omega)
        _ ≤ T := hT n (by omega) (by omega)
    · simp [hen]
  calc _ ≤ ∑ n ∈ Finset.Icc 1 N, if e ∣ n + 2 then T else 0 := Finset.sum_le_sum h2
    _ = T * (((Finset.Icc 1 N).filter (fun n => e ∣ n + 2)).card : ℝ) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ T * (((N + 2) / e : ℕ) : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ hT0
        exact_mod_cast card_Icc_filter_dvd_add_two_le N e

theorem sum_sum_filter_le {N K L : ℕ} {T : ℝ}
    (hT : ∀ m, 1 ≤ m → m ≤ N + 2 → (m.divisors.card : ℝ) ≤ T) (hT0 : 0 ≤ T)
    (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) :
    ∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 L,
        ∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n ∧ e ∣ n + 2), w n
      ≤ T ^ 2 * ∑ n ∈ Finset.Icc 1 N, w n := by
  simp_rw [Finset.sum_filter]
  simp_rw [Finset.sum_comm (s := Finset.Icc 1 L) (t := Finset.Icc 1 N),
    Finset.sum_comm (s := Finset.Icc 1 K) (t := Finset.Icc 1 N)]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  rw [Finset.mem_Icc] at hn
  have h1 : ∀ d e, (if d ∣ n ∧ e ∣ n + 2 then w n else 0) =
      (if d ∣ n then (1:ℝ) else 0) * ((if e ∣ n + 2 then (1:ℝ) else 0) * w n) := by
    intro d e
    split_ifs <;> simp_all
  simp_rw [h1, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hA : (((Finset.Icc 1 K).filter (fun d => d ∣ n)).card : ℝ) ≤ T :=
    le_trans (by exact_mod_cast card_filter_dvd_le (Finset.Icc 1 K) (m := n) (by omega))
      (hT n (by omega) (by omega))
  have hB : (((Finset.Icc 1 L).filter (fun e => e ∣ n + 2)).card : ℝ) ≤ T :=
    le_trans (by exact_mod_cast card_filter_dvd_le (Finset.Icc 1 L) (m := n + 2) (by omega))
      (hT (n + 2) (by omega) (by omega))
  have hwn := hw n
  calc _ ≤ T * (T * w n) := by
        apply mul_le_mul hA (mul_le_mul_of_nonneg_right hB hwn) (by positivity) hT0
    _ = T ^ 2 * w n := by ring

/-! ## The `n`-cutoff and the densities -/

theorem sum_abs_one_sub_psi_le {N j₀ J : ℕ} {ν : ℝ} (hν0 : 0 < ν) (hν1 : ν ≤ 1) (hN : 1 ≤ N)
    (hj : j₀ ≤ J) (hNJ : (N : ℝ) ≤ 2 ^ J / 2) :
    ∑ n ∈ Finset.Icc 1 N, |1 - psiCut (N : ℝ) ν j₀ J (n : ℝ)| ≤ 2 ^ j₀ + ν * N + 1 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : ∀ n ∈ Finset.Icc 1 N, |1 - psiCut (N : ℝ) ν j₀ J (n : ℝ)| ≤
      (if n < 2 ^ j₀ then (1 : ℝ) else 0) + ind N ν n := by
    intro n _
    have h0 := psiCut_nonneg (N : ℝ) ν j₀ J (n : ℝ)
    have h1' := psiCut_le_one (N : ℝ) ν hj (n : ℝ)
    have habs : |1 - psiCut (N : ℝ) ν j₀ J (n : ℝ)| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    unfold ind
    by_cases ha : n < 2 ^ j₀
    · simp only [ha, ite_true]
      split_ifs <;> linarith
    · by_cases hb : (1 - ν) * (N : ℝ) < (n : ℝ)
      · simp only [ha, hb, ite_true, ite_false]
        linarith
      · simp only [ha, hb, ite_false]
        have ha' : (2 : ℝ) ^ j₀ ≤ n := by exact_mod_cast not_lt.mp ha
        have hb : (n : ℝ) ≤ (1 - ν) * N := not_lt.mp hb
        rw [psiCut_eq_one hν0 hN' hj hNJ ha' hb]
        simp
  calc _ ≤ ∑ n ∈ Finset.Icc 1 N, ((if n < 2 ^ j₀ then (1 : ℝ) else 0) + ind N ν n) :=
        Finset.sum_le_sum h1
    _ = (((Finset.Icc 1 N).filter (fun n => n < 2 ^ j₀)).card : ℝ) +
          (((Finset.Icc 1 N).filter (fun d : ℕ => (1 - ν) * (N : ℝ) < (d : ℝ))).card : ℝ) := by
        rw [Finset.sum_add_distrib]
        unfold ind
        rw [← Finset.sum_filter, ← Finset.sum_filter]
        simp
    _ ≤ 2 ^ j₀ + (ν * N + 1) := by
        gcongr
        · have : ((Finset.Icc 1 N).filter (fun n => n < 2 ^ j₀)) ⊆ Finset.range (2 ^ j₀) := by
            intro n hn
            simp only [Finset.mem_filter] at hn
            exact Finset.mem_range.mpr hn.2
          have := Finset.card_le_card this
          rw [Finset.card_range] at this
          exact_mod_cast this
        · exact card_filter_gt_le N hν0.le hν1
    _ = 2 ^ j₀ + ν * N + 1 := by ring

theorem sum_dens_weighted_le (K L : ℕ) (u : ℕ → ℝ) (v : ℕ → ℝ) (hu : ∀ d, 0 ≤ u d)
    (hv : ∀ e, 0 ≤ v e) :
    ∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 L, u d * v e * dens d e ≤
      2 * (∑ d ∈ Finset.Icc 1 K, u d / d) * (∑ e ∈ Finset.Icc 1 L, v e / e) := by
  rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e he
  have hd0 : 0 < d := (Finset.mem_Icc.mp hd).1
  have he0 : 0 < e := (Finset.mem_Icc.mp he).1
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd0
  have he' : (0 : ℝ) < e := by exact_mod_cast he0
  have h := dens_le d e hd0 he0
  have huv : 0 ≤ u d * v e := mul_nonneg (hu d) (hv e)
  calc u d * v e * dens d e ≤ u d * v e * (2 / ((d : ℝ) * e)) :=
        mul_le_mul_of_nonneg_left h huv
    _ = 2 * (u d / d * (v e / e)) := by field_simp

/-! ## The pointwise error -/

theorem norm_mu_le (d : ℕ) : ‖(μ d : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_intCast]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one

theorem one_sub_topCut_mul_le {K L : ℕ} {ν : ℝ} (hν0 : 0 < ν) (hK : 1 ≤ K) (hL : 1 ≤ L)
    (d e : ℕ) :
    1 - topCut (K : ℝ) ν d * topCut (L : ℝ) ν e ≤ ind K ν d + ind L ν e := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have h0 : 0 ≤ topCut (K : ℝ) ν d * topCut (L : ℝ) ν e :=
    mul_nonneg (topCut_nonneg _ _ _) (topCut_nonneg _ _ _)
  unfold ind
  by_cases ha : (1 - ν) * (K : ℝ) < (d : ℝ)
  · simp only [ha, ite_true]
    have := ind_nonneg L ν e
    unfold ind at this
    linarith
  · by_cases hb : (1 - ν) * (L : ℝ) < (e : ℝ)
    · simp only [ha, hb, ite_true, ite_false]
      linarith
    · simp only [ha, hb, ite_false]
      rw [topCut_eq_one hν0 hK' (not_lt.mp ha), topCut_eq_one hν0 hL' (not_lt.mp hb)]
      norm_num

theorem rem_sub_G (N : ℕ) (ν : ℝ) (j₀ J d e : ℕ) :
    (rem N d e : ℂ) - Gfun N ν j₀ J d e =
      (∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n ∧ e ∣ n + 2),
          (((1 - psiCut (N : ℝ) ν j₀ J (n : ℝ)) : ℝ) : ℂ))
        - ((N : ℂ) - Zsum N ν j₀ J) * (dens d e : ℂ) := by
  unfold rem Gfun pairCount
  rw [Finset.card_eq_sum_ones]
  push_cast
  rw [Finset.sum_sub_distrib]
  ring

theorem pointwise_bound {N K L : ℕ} {ν : ℝ} (hν0 : 0 < ν) (hK : 1 ≤ K) (hL : 1 ≤ L)
    (j₀ J d e : ℕ) :
    ‖(μ d : ℂ) * (μ e : ℂ) * (rem N d e : ℂ) -
        (μ d : ℂ) * (μ e : ℂ) * (topCut (K : ℝ) ν d : ℂ) * (topCut (L : ℝ) ν e : ℂ) *
          Gfun N ν j₀ J d e‖
      ≤ ind K ν d * pairCount N d e + ind L ν e * pairCount N d e
        + N * (ind K ν d * 1 * dens d e) + N * (1 * ind L ν e * dens d e)
        + ∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n ∧ e ∣ n + 2),
            |1 - psiCut (N : ℝ) ν j₀ J (n : ℝ)|
        + ‖(N : ℂ) - Zsum N ν j₀ J‖ * (1 * 1 * dens d e) := by
  set a := topCut (K : ℝ) ν d
  set b := topCut (L : ℝ) ν e
  set r := rem N d e
  set G := Gfun N ν j₀ J d e
  have ha0 : 0 ≤ a := topCut_nonneg _ _ _
  have ha1 : a ≤ 1 := topCut_le_one _ _ _
  have hb0 : 0 ≤ b := topCut_nonneg _ _ _
  have hb1 : b ≤ 1 := topCut_le_one _ _ _
  have hab0 : 0 ≤ a * b := mul_nonneg ha0 hb0
  have hab1 : a * b ≤ 1 := by nlinarith
  have hdens := dens_nonneg d e
  have hpc : (0 : ℝ) ≤ pairCount N d e := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hr : |r| ≤ pairCount N d e + N * dens d e := by
    have : r = pairCount N d e - N * dens d e := rfl
    rw [this, abs_le]
    constructor <;> nlinarith
  have hrG : ‖(r : ℂ) - G‖ ≤ ∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n ∧ e ∣ n + 2),
        |1 - psiCut (N : ℝ) ν j₀ J (n : ℝ)| + ‖(N : ℂ) - Zsum N ν j₀ J‖ * dens d e := by
    rw [rem_sub_G]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · refine (norm_sum_le _ _).trans (le_of_eq ?_)
      apply Finset.sum_congr rfl
      intro n _
      rw [Complex.norm_real, Real.norm_eq_abs]
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hdens]
  have hsplit : (μ d : ℂ) * (μ e : ℂ) * (r : ℂ) - (μ d : ℂ) * (μ e : ℂ) * (a : ℂ) * (b : ℂ) * G
      = (μ d : ℂ) * (μ e : ℂ) * ((((1 - a * b) : ℝ) : ℂ) * (r : ℂ) +
          ((a * b : ℝ) : ℂ) * ((r : ℂ) - G)) := by
    push_cast; ring
  rw [hsplit, norm_mul, norm_mul]
  have hμ : ‖(μ d : ℂ)‖ * ‖(μ e : ℂ)‖ ≤ 1 := by
    have := norm_mu_le d; have := norm_mu_le e
    calc _ ≤ 1 * 1 := mul_le_mul (norm_mu_le d) (norm_mu_le e) (norm_nonneg _) (by norm_num)
      _ = 1 := by ring
  have hin : ‖(((1 - a * b) : ℝ) : ℂ) * (r : ℂ) + ((a * b : ℝ) : ℂ) * ((r : ℂ) - G)‖
      ≤ (ind K ν d + ind L ν e) * (pairCount N d e + N * dens d e) +
        (∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n ∧ e ∣ n + 2),
          |1 - psiCut (N : ℝ) ν j₀ J (n : ℝ)| + ‖(N : ℂ) - Zsum N ν j₀ J‖ * dens d e) := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (by linarith)]
      exact mul_le_mul (one_sub_topCut_mul_le hν0 hK hL d e) hr (abs_nonneg _)
        (add_nonneg (ind_nonneg _ _ _) (ind_nonneg _ _ _))
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hab0]
      calc a * b * ‖(r : ℂ) - G‖ ≤ 1 * ‖(r : ℂ) - G‖ :=
            mul_le_mul_of_nonneg_right hab1 (norm_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact hrG
  have hRHS0 : 0 ≤ (ind K ν d + ind L ν e) * (pairCount N d e + N * dens d e) +
        (∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n ∧ e ∣ n + 2),
          |1 - psiCut (N : ℝ) ν j₀ J (n : ℝ)| + ‖(N : ℂ) - Zsum N ν j₀ J‖ * dens d e) := by
    have := ind_nonneg K ν d; have := ind_nonneg L ν e
    have : 0 ≤ ∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n ∧ e ∣ n + 2),
          |1 - psiCut (N : ℝ) ν j₀ J (n : ℝ)| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have : 0 ≤ ‖(N : ℂ) - Zsum N ν j₀ J‖ * dens d e := mul_nonneg (norm_nonneg _) hdens
    positivity
  calc ‖(μ d : ℂ)‖ * ‖(μ e : ℂ)‖ * ‖(((1 - a * b) : ℝ) : ℂ) * (r : ℂ) +
          ((a * b : ℝ) : ℂ) * ((r : ℂ) - G)‖
      ≤ 1 * ((ind K ν d + ind L ν e) * (pairCount N d e + N * dens d e) +
        (∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n ∧ e ∣ n + 2),
          |1 - psiCut (N : ℝ) ν j₀ J (n : ℝ)| + ‖(N : ℂ) - Zsum N ν j₀ J‖ * dens d e)) :=
        mul_le_mul hμ hin (norm_nonneg _) (by norm_num)
    _ = _ := by ring

/-! ## The total error -/

theorem error_bound {N K L j₀ : ℕ} {ν T : ℝ} (hN : 2 ≤ N) (hK : 1 ≤ K) (hL : 1 ≤ L)
    (hν0 : 0 < ν) (hν : ν ≤ 1 / 2) (hj : j₀ ≤ Nat.log 2 N + 2)
    (hT : ∀ m, 1 ≤ m → m ≤ N + 2 → (m.divisors.card : ℝ) ≤ T) (hT0 : 0 ≤ T) :
    ‖((∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 L, (μ d : ℝ) * (μ e : ℝ) * rem N d e : ℝ) : ℂ)
        - ∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 L,
          (μ d : ℂ) * (μ e : ℂ) * (topCut (K : ℝ) ν d : ℂ) * (topCut (L : ℝ) ν e : ℂ) *
            Gfun N ν j₀ (Nat.log 2 N + 2) d e‖
      ≤ T * N * (2 * ν + 2 / K) + T * (N + 2) * (2 * ν + 2 / L)
        + N * (2 * (2 * ν + 2 / K) * (1 + Real.log L))
        + N * (2 * (1 + Real.log K) * (2 * ν + 2 / L))
        + T ^ 2 * (2 ^ j₀ + ν * N + 1)
        + (2 ^ j₀ + ν * N) * (2 * (1 + Real.log K) * (1 + Real.log L)) := by
  set J := Nat.log 2 N + 2 with hJ
  have hN1 : 1 ≤ N := by omega
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN1
  have hcast : ((∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 L,
      (μ d : ℝ) * (μ e : ℝ) * rem N d e : ℝ) : ℂ)
      = ∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 L, (μ d : ℂ) * (μ e : ℂ) * (rem N d e : ℂ) := by
    push_cast; rfl
  rw [hcast, ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  -- the six bounds
  have h1 : ∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 L, ind K ν d * (pairCount N d e : ℝ)
      ≤ T * N * (2 * ν + 2 / K) := by
    simp_rw [← Finset.mul_sum]
    calc _ ≤ ∑ d ∈ Finset.Icc 1 K, ind K ν d * (T * ((N : ℝ) / d)) := by
          apply Finset.sum_le_sum
          intro d _
          apply mul_le_mul_of_nonneg_left _ (ind_nonneg _ _ _)
          refine (sum_pairCount_e_le hT).trans ?_
          exact mul_le_mul_of_nonneg_left (Nat.cast_div_le) hT0
      _ = T * N * ∑ d ∈ Finset.Icc 1 K, ind K ν d / d := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d _
          ring
      _ ≤ T * N * (2 * ν + 2 / K) :=
          mul_le_mul_of_nonneg_left (sum_ind_div_le K hK hν0 hν) (by positivity)
  have h2 : ∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 L, ind L ν e * (pairCount N d e : ℝ)
      ≤ T * (N + 2) * (2 * ν + 2 / L) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    calc _ ≤ ∑ e ∈ Finset.Icc 1 L, ind L ν e * (T * (((N : ℝ) + 2) / e)) := by
          apply Finset.sum_le_sum
          intro e _
          apply mul_le_mul_of_nonneg_left _ (ind_nonneg _ _ _)
          refine (sum_pairCount_d_le hT hT0).trans ?_
          apply mul_le_mul_of_nonneg_left _ hT0
          have := Nat.cast_div_le (α := ℝ) (m := N + 2) (n := e)
          push_cast at this
          exact this
      _ = T * (N + 2) * ∑ e ∈ Finset.Icc 1 L, ind L ν e / e := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e _
          ring
      _ ≤ T * (N + 2) * (2 * ν + 2 / L) :=
          mul_le_mul_of_nonneg_left (sum_ind_div_le L hL hν0 hν) (by positivity)
  have hhK := sum_inv_le_log K
  have hhL := sum_inv_le_log L
  have hhK0 : 0 ≤ ∑ d ∈ Finset.Icc 1 K, (1 : ℝ) / d :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hhL0 : 0 ≤ ∑ e ∈ Finset.Icc 1 L, (1 : ℝ) / e :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hiK0 : 0 ≤ ∑ d ∈ Finset.Icc 1 K, ind K ν d / d :=
    Finset.sum_nonneg fun _ _ => div_nonneg (ind_nonneg _ _ _) (Nat.cast_nonneg _)
  have hiL0 : 0 ≤ ∑ e ∈ Finset.Icc 1 L, ind L ν e / e :=
    Finset.sum_nonneg fun _ _ => div_nonneg (ind_nonneg _ _ _) (Nat.cast_nonneg _)
  have hiK := sum_ind_div_le K hK hν0 hν
  have hiL := sum_ind_div_le L hL hν0 hν
  have h3 : ∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 L, (N : ℝ) * (ind K ν d * 1 * dens d e)
      ≤ N * (2 * (2 * ν + 2 / K) * (1 + Real.log L)) := by
    rw [show (∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 L, (N : ℝ) * (ind K ν d * 1 * dens d e))
        = N * ∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 L, ind K ν d * 1 * dens d e by
      simp only [Finset.mul_sum]]
    apply mul_le_mul_of_nonneg_left _ hN'.le
    refine (sum_dens_weighted_le K L (ind K ν) (fun _ => 1) (ind_nonneg K ν)
      (fun _ => by norm_num)).trans ?_
    have := mul_le_mul hiK hhL hhL0 (by positivity)
    nlinarith
  have h4 : ∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 L, (N : ℝ) * (1 * ind L ν e * dens d e)
      ≤ N * (2 * (1 + Real.log K) * (2 * ν + 2 / L)) := by
    rw [show (∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 L, (N : ℝ) * (1 * ind L ν e * dens d e))
        = N * ∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 L, 1 * ind L ν e * dens d e by
      simp only [Finset.mul_sum]]
    apply mul_le_mul_of_nonneg_left _ hN'.le
    refine (sum_dens_weighted_le K L (fun _ => 1) (ind L ν) (fun _ => by norm_num)
      (ind_nonneg L ν)).trans ?_
    have := mul_le_mul hhK hiL hiL0 (by linarith)
    nlinarith
  have h5 : ∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 L,
      ∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n ∧ e ∣ n + 2),
        |1 - psiCut (N : ℝ) ν j₀ J (n : ℝ)|
      ≤ T ^ 2 * (2 ^ j₀ + ν * N + 1) := by
    refine (sum_sum_filter_le hT hT0 _ (fun n => abs_nonneg _)).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact sum_abs_one_sub_psi_le hν0 (by linarith) hN1 hj (le_two_pow_log N)
  have hZ : ‖(N : ℂ) - Zsum N ν j₀ J‖ ≤ 2 ^ j₀ + ν * N := by
    rw [norm_sub_rev]
    exact norm_sum_fourierR_piece_sub_le hν0 hN' hj (le_two_pow_log N)
  have h6 : ∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 L,
      ‖(N : ℂ) - Zsum N ν j₀ J‖ * (1 * 1 * dens d e)
      ≤ (2 ^ j₀ + ν * N) * (2 * (1 + Real.log K) * (1 + Real.log L)) := by
    rw [show (∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 L,
        ‖(N : ℂ) - Zsum N ν j₀ J‖ * (1 * 1 * dens d e))
        = ‖(N : ℂ) - Zsum N ν j₀ J‖ *
          ∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 L, (1 : ℝ) * 1 * dens d e by
      simp only [Finset.mul_sum]]
    have hs := sum_dens_weighted_le K L (fun _ => 1) (fun _ => 1) (fun _ => by norm_num)
      (fun _ => by norm_num)
    have hs0 : 0 ≤ ∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 L, (1 : ℝ) * 1 * dens d e :=
      Finset.sum_nonneg fun d _ => Finset.sum_nonneg fun e _ => by
        have := dens_nonneg d e
        linarith
    have hs' : ∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 L, (1 : ℝ) * 1 * dens d e
        ≤ 2 * (1 + Real.log K) * (1 + Real.log L) := by
      refine hs.trans ?_
      have := mul_le_mul hhK hhL hhL0 (by linarith)
      nlinarith
    exact mul_le_mul hZ hs' hs0 (by positivity)
  calc _ ≤ ∑ d ∈ Finset.Icc 1 K, ‖∑ e ∈ Finset.Icc 1 L, ((μ d : ℂ) * (μ e : ℂ) * (rem N d e : ℂ)
          - (μ d : ℂ) * (μ e : ℂ) * (topCut (K : ℝ) ν d : ℂ) * (topCut (L : ℝ) ν e : ℂ) *
            Gfun N ν j₀ J d e)‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 L, ‖(μ d : ℂ) * (μ e : ℂ) * (rem N d e : ℂ)
          - (μ d : ℂ) * (μ e : ℂ) * (topCut (K : ℝ) ν d : ℂ) * (topCut (L : ℝ) ν e : ℂ) *
            Gfun N ν j₀ J d e‖ := Finset.sum_le_sum fun d _ => norm_sum_le _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 L,
          (ind K ν d * pairCount N d e + ind L ν e * pairCount N d e
          + N * (ind K ν d * 1 * dens d e) + N * (1 * ind L ν e * dens d e)
          + ∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n ∧ e ∣ n + 2),
              |1 - psiCut (N : ℝ) ν j₀ J (n : ℝ)|
          + ‖(N : ℂ) - Zsum N ν j₀ J‖ * (1 * 1 * dens d e)) :=
        Finset.sum_le_sum fun d _ => Finset.sum_le_sum fun e _ =>
          pointwise_bound hν0 hK hL j₀ J d e
    _ = (∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 L, ind K ν d * (pairCount N d e : ℝ))
        + (∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 L, ind L ν e * (pairCount N d e : ℝ))
        + (∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 L, (N : ℝ) * (ind K ν d * 1 * dens d e))
        + (∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 L, (N : ℝ) * (1 * ind L ν e * dens d e))
        + (∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 L,
            ∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n ∧ e ∣ n + 2),
              |1 - psiCut (N : ℝ) ν j₀ J (n : ℝ)|)
        + (∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 L,
            ‖(N : ℂ) - Zsum N ν j₀ J‖ * (1 * 1 * dens d e)) := by
        simp only [Finset.sum_add_distrib]
    _ ≤ _ := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add h1 h2) h3) h4) h5) h6

/-- The numerical bookkeeping of the error terms. -/
theorem numeric_bound {N K L ν T Cτ c u g lK lL : ℝ} (hN : 2 ≤ N) (hK : 1 ≤ K) (hL : 1 ≤ L)
    (hν : 0 < ν) (hT0 : 0 ≤ T) (hTu : T ≤ Cτ * u) (hu : 1 ≤ u) (hc : 1 ≤ c) (hCτ : 1 ≤ Cτ)
    (hlK0 : 0 ≤ lK) (hlK : lK ≤ c * u) (hlL0 : 0 ≤ lL) (hlL : lL ≤ c * u) (hg : 1 ≤ g) :
    T * N * (2 * ν + 2 / K) + T * (N + 2) * (2 * ν + 2 / L) + N * (2 * (2 * ν + 2 / K) * lL)
      + N * (2 * lK * (2 * ν + 2 / L)) + T ^ 2 * (g + ν * N + 1) + (g + ν * N) * (2 * lK * lL)
      ≤ (6 * Cτ + 8 * c + 2 * Cτ ^ 2 + 2 * c ^ 2) * (u * u) *
          (ν * N + N / K + N / L + K + L + g) := by
  have hN0 : 0 < N := by linarith
  have ha0 : 0 ≤ ν * N := by positivity
  have hb0 : 0 ≤ N / K := by positivity
  have hb'0 : 0 ≤ N / L := by positivity
  set X := ν * N + N / K + N / L + K + L + g with hX
  have hX0 : 0 ≤ X := by positivity
  have e1 : T * N * (2 * ν + 2 / K) = T * (2 * (ν * N) + 2 * (N / K)) := by ring
  have e2 : T * (N + 2) * (2 * ν + 2 / L) ≤ T * (4 * (ν * N) + 4 * (N / L)) := by
    have h2 : (0 : ℝ) ≤ 2 * ν + 2 / L := by positivity
    calc T * (N + 2) * (2 * ν + 2 / L) ≤ T * (2 * N) * (2 * ν + 2 / L) := by
          apply mul_le_mul_of_nonneg_right _ h2
          apply mul_le_mul_of_nonneg_left (by linarith) hT0
      _ = T * (4 * (ν * N) + 4 * (N / L)) := by ring
  have e3 : N * (2 * (2 * ν + 2 / K) * lL) = (4 * (ν * N) + 4 * (N / K)) * lL := by ring
  have e4 : N * (2 * lK * (2 * ν + 2 / L)) = (4 * (ν * N) + 4 * (N / L)) * lK := by ring
  have A1 : T * (2 * (ν * N) + 2 * (N / K)) ≤ Cτ * u * (2 * X) :=
    mul_le_mul hTu (by linarith) (by positivity) (by positivity)
  have A2 : T * (4 * (ν * N) + 4 * (N / L)) ≤ Cτ * u * (4 * X) :=
    mul_le_mul hTu (by linarith) (by positivity) (by positivity)
  have A3 : (4 * (ν * N) + 4 * (N / K)) * lL ≤ (4 * X) * (c * u) :=
    mul_le_mul (by linarith) hlL hlL0 (by positivity)
  have A4 : (4 * (ν * N) + 4 * (N / L)) * lK ≤ (4 * X) * (c * u) :=
    mul_le_mul (by linarith) hlK hlK0 (by positivity)
  have A5 : T ^ 2 * (g + ν * N + 1) ≤ (Cτ * u) ^ 2 * (2 * X) :=
    mul_le_mul (pow_le_pow_left₀ hT0 hTu 2) (by linarith) (by positivity) (by positivity)
  have A6 : (g + ν * N) * (2 * lK * lL) ≤ X * (2 * (c * u) * (c * u)) := by
    apply mul_le_mul (by linarith) _ (by positivity) hX0
    have := mul_le_mul hlK hlL hlL0 (by positivity)
    linarith
  have h1 : Cτ * u * X ≤ Cτ * (u * u) * X := by
    apply mul_le_mul_of_nonneg_right _ hX0
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    nlinarith
  have h2 : c * u * X ≤ c * (u * u) * X := by
    apply mul_le_mul_of_nonneg_right _ hX0
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    nlinarith
  have r1 : Cτ * u * (2 * X) + Cτ * u * (4 * X) + (4 * X) * (c * u) + (4 * X) * (c * u)
      + (Cτ * u) ^ 2 * (2 * X) + X * (2 * (c * u) * (c * u))
      = 6 * (Cτ * u * X) + 8 * (c * u * X) + 2 * (Cτ ^ 2 * (u * u) * X)
        + 2 * (c ^ 2 * (u * u) * X) := by ring
  have r2 : (6 * Cτ + 8 * c + 2 * Cτ ^ 2 + 2 * c ^ 2) * (u * u) * X
      = 6 * (Cτ * (u * u) * X) + 8 * (c * (u * u) * X) + 2 * (Cτ ^ 2 * (u * u) * X)
        + 2 * (c ^ 2 * (u * u) * X) := by ring
  rw [e1, e3, e4, r2]
  have := r1
  linarith

end Smoothing

open Smoothing Cutoff in
/-- **Smoothing** (paper, proof of Theorem 1.2): the sharp sum `Σ(K,L)` is the sum of the
smooth sums `Δ` over the dyadic pieces up to `O(N^ε (νN + N/K + N/L + K + L + 2^{j₀}))`. -/
theorem smoothing_decomp :
    ∀ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ (N K L j₀ : ℕ) (ν : ℝ),
      2 ≤ N → 1 ≤ K → 1 ≤ L → K ≤ N → L ≤ N → 0 < ν → ν ≤ 1 / 2 → 1 ≤ j₀ → 2 ^ j₀ ≤ N →
      ‖((∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 L, (μ d : ℝ) * (μ e : ℝ) * rem N d e : ℝ) : ℂ)
        - ∑ a ∈ Finset.range (Nat.log 2 K + 2), ∑ b ∈ Finset.range (Nat.log 2 L + 2),
            ∑ l ∈ Finset.Ico j₀ (Nat.log 2 N + 2),
              smoothDelta ((2 : ℝ) ^ l) ((2 : ℝ) ^ a) ((2 : ℝ) ^ b)
                (piece (N : ℝ) ν ((2 : ℝ) ^ l)) (piece (K : ℝ) ν ((2 : ℝ) ^ a))
                (piece (L : ℝ) ν ((2 : ℝ) ^ b))‖
        ≤ C * (N : ℝ) ^ ε * (ν * N + N / K + N / L + K + L + 2 ^ j₀) := by
  intro ε hε
  obtain ⟨Cτ, hCτ1, hCτ⟩ := card_divisors_le_rpow (ε := ε / 4) (by positivity)
  have hc1 : 1 ≤ 1 + 2 / ε := by
    have : 0 < 2 / ε := by positivity
    linarith
  refine ⟨6 * Cτ + 8 * (1 + 2 / ε) + 2 * Cτ ^ 2 + 2 * (1 + 2 / ε) ^ 2, by positivity, ?_⟩
  intro N K L j₀ ν hN hK hL hKN hLN hν0 hν hj₀ hj₀N
  rw [decomp_identity hν0 (by omega) hK hL j₀]
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hKN' : (K : ℝ) ≤ N := by exact_mod_cast hKN
  have hLN' : (L : ℝ) ≤ N := by exact_mod_cast hLN
  have hT : ∀ m, 1 ≤ m → m ≤ N + 2 →
      (m.divisors.card : ℝ) ≤ Cτ * ((N : ℝ) + 2) ^ (ε / 4) := by
    intro m hm1 hm2
    refine (hCτ m hm1).trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
    apply Real.rpow_le_rpow (by positivity) _ (by positivity)
    have : ((m : ℕ) : ℝ) ≤ ((N + 2 : ℕ) : ℝ) := by exact_mod_cast hm2
    push_cast at this
    exact this
  have hT0 : 0 ≤ Cτ * ((N : ℝ) + 2) ^ (ε / 4) := by
    have : 0 ≤ ((N : ℝ) + 2) ^ (ε / 4) := by positivity
    nlinarith
  have hj : j₀ ≤ Nat.log 2 N + 2 := by
    have := Nat.le_log_of_pow_le (by norm_num) hj₀N
    omega
  refine (error_bound hN hK hL hν0 hν hj hT hT0).trans ?_
  have hu1 : 1 ≤ (N : ℝ) ^ (ε / 2) := Real.one_le_rpow (by linarith) (by positivity)
  have huu : (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) = (N : ℝ) ^ ε := by
    rw [← Real.rpow_add hN0]
    congr 1
    ring
  have hTu : Cτ * ((N : ℝ) + 2) ^ (ε / 4) ≤ Cτ * (N : ℝ) ^ (ε / 2) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    calc ((N : ℝ) + 2) ^ (ε / 4) ≤ ((N : ℝ) ^ 2) ^ (ε / 4) :=
          Real.rpow_le_rpow (by positivity) (by nlinarith) (by positivity)
      _ = (N : ℝ) ^ (ε / 2) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
          congr 1
          push_cast
          ring
  have hlogN : 1 + Real.log N ≤ (1 + 2 / ε) * (N : ℝ) ^ (ε / 2) := by
    have h1 := Real.log_le_rpow_div hN0.le (show 0 < ε / 2 by positivity)
    have : (N : ℝ) ^ (ε / 2) / (ε / 2) = 2 / ε * (N : ℝ) ^ (ε / 2) := by
      field_simp
    rw [this] at h1
    nlinarith
  have hlogK : 1 + Real.log K ≤ (1 + 2 / ε) * (N : ℝ) ^ (ε / 2) := by
    have := Real.log_le_log (by linarith) hKN'
    linarith
  have hlogL : 1 + Real.log L ≤ (1 + 2 / ε) * (N : ℝ) ^ (ε / 2) := by
    have := Real.log_le_log (by linarith) hLN'
    linarith
  have hlogK0 : 0 ≤ 1 + Real.log K := by
    have := Real.log_nonneg hK1
    linarith
  have hlogL0 : 0 ≤ 1 + Real.log L := by
    have := Real.log_nonneg hL1
    linarith
  have hg : (1 : ℝ) ≤ 2 ^ j₀ := one_le_pow₀ (by norm_num)
  have key := numeric_bound hN2 hK1 hL1 hν0 hT0 hTu hu1 hc1 hCτ1 hlogK0 hlogK hlogL0 hlogL hg
  rw [huu] at key
  calc _ ≤ _ := key
    _ = _ := by ring

end Level

end MobiusDeterminant
