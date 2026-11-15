import MobiusDeterminant.Unconditional.LevelDefs
import MobiusDeterminant.Unconditional.LevelPoisson
import MobiusDeterminant.Unconditional.LevelArith
import MobiusDeterminant.Unconditional.LevelTempered
import MobiusDeterminant.Unconditional.LevelFinite

/-!
# Proposition 8.1: the smooth level of distribution

`smoothDelta_bound`: for weights `ψ, φ₁, φ₂` tempered on `[1/2, 2]`, and `D, E ≤ N₀^{9/17-η}`,
`Δ ≪ P^k N₀^{1-η}`.

Proof: parity split `d = 2^i d'`, `e = 2^j e'` (`sum_mobius_parity`), restriction to coprime
odd `d', e'` (`bracket_eq_zero_of_not_dvd`), Poisson summation per pair (`bracket_poisson`,
with the CRT data of `pair_class`) truncated at `M = ⌊4ℓD'E'N₀^{ε₀-1}⌋`, the tail being
negligible, and the finite part bounded by `finite_part_bound` in the orientation `E' ≤ D'`
(directly) or `D' < E'` (after reciprocity, `kfrac_reciprocity`, and `sum_odd_coprime_comm`).
-/

open Finset Real
open scoped ArithmeticFunction.Moebius

namespace MobiusDeterminant

namespace Level

namespace Smooth

/-- One parity class `(i,j)` of the smooth sum, over odd `e'` and `d'` coprime to `2e'`. -/
noncomputable def Tij (N₀ D E : ℝ) (ψ φ₁ φ₂ : ℝ → ℂ) (i j : ℕ) : ℂ :=
  ∑ e' ∈ (Finset.Icc 1 (⌊2 * E⌋₊ / 2 ^ j)).filter Odd,
    ∑ d' ∈ (Finset.Icc 1 (⌊2 * D⌋₊ / 2 ^ i)).filter (fun a => Nat.Coprime a (2 * e')),
      (μ d' : ℂ) * (μ e' : ℂ) * φ₁ ((d' : ℝ) / (D / 2 ^ i)) * φ₂ ((e' : ℝ) / (E / 2 ^ j)) *
        bracket N₀ ψ (2 ^ i * d') (2 ^ j * e')

lemma coprime_two_mul_iff {a b : ℕ} : Nat.Coprime a (2 * b) ↔ Odd a ∧ Nat.Coprime a b := by
  rw [Nat.coprime_mul_iff_right, Nat.coprime_two_right]

/-- Brackets of odd non-coprime pairs vanish. -/
lemma bracket_noncop (N₀ : ℝ) (ψ : ℝ → ℂ) (i j : ℕ) {d e : ℕ} (hd : Odd d)
    (hde : ¬ Nat.Coprime d e) : bracket N₀ ψ (2 ^ i * d) (2 ^ j * e) = 0 := by
  apply bracket_eq_zero_of_not_dvd
  intro h2
  apply hde
  have hg : Nat.gcd d e ∣ 2 :=
    (Nat.gcd_dvd_gcd_mul_left_left d e (2 ^ i) |>.trans
      (Nat.gcd_dvd_gcd_mul_left_right _ e (2 ^ j))).trans h2
  have hodd : Odd (Nat.gcd d e) := Odd.of_dvd_nat hd (Nat.gcd_dvd_left d e)
  have hle : Nat.gcd d e ≤ 2 := Nat.le_of_dvd (by norm_num) hg
  have hpos : 0 < Nat.gcd d e := Nat.gcd_pos_of_pos_left _ hd.pos
  interval_cases h : Nat.gcd d e
  · exact h
  · exact absurd hodd (by decide)

/-- Restricting odd `d` to `d` coprime to `2e` when the summand vanishes otherwise. -/
lemma sum_odd_eq_sum_cop (Y : Finset ℕ) (e : ℕ) (F : ℕ → ℂ)
    (hF : ∀ d, Odd d → ¬ Nat.Coprime d e → F d = 0) :
    ∑ d ∈ Y.filter Odd, F d = ∑ d ∈ Y.filter (fun a => Nat.Coprime a (2 * e)), F d := by
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases hd : Odd d
  · by_cases hc : Nat.Coprime d e
    · simp [hd, hc, coprime_two_mul_iff]
    · simp [hd, hc, coprime_two_mul_iff, hF d hd hc]
  · simp [hd, coprime_two_mul_iff]

lemma floor_two_mul_div_le (X : ℝ) (hX : 0 ≤ X) (i : ℕ) :
    ⌊2 * (X / 2 ^ i)⌋₊ ≤ ⌊2 * X⌋₊ / 2 ^ i := by
  rw [Nat.le_div_iff_mul_le (by positivity)]
  apply Nat.le_floor
  push_cast
  have h1 : (⌊2 * (X / 2 ^ i)⌋₊ : ℝ) ≤ 2 * (X / 2 ^ i) := Nat.floor_le (by positivity)
  have h2 : (0 : ℝ) < 2 ^ i := by positivity
  calc (⌊2 * (X / 2 ^ i)⌋₊ : ℝ) * 2 ^ i ≤ 2 * (X / 2 ^ i) * 2 ^ i := by gcongr
    _ = 2 * X := by field_simp

/-- Reorder the odd double sum and restrict it to coprime pairs. -/
lemma reorder (X Y : Finset ℕ) (G : ℕ → ℕ → ℂ)
    (hG : ∀ d e, Odd d → Odd e → ¬ Nat.Coprime d e → G d e = 0) :
    ∑ d ∈ Y.filter Odd, ∑ e ∈ X.filter Odd, G d e =
      ∑ e ∈ X.filter Odd, ∑ d ∈ Y.filter (fun a => Nat.Coprime a (2 * e)), G d e := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e he => ?_
  have heo : Odd e := (Finset.mem_filter.mp he).2
  exact sum_odd_eq_sum_cop Y e (fun d => G d e) (fun d hd hc => hG d e hd heo hc)

/-- Parity split of `Δ` into the four classes `T_{ij}`. -/
lemma smoothDelta_split (N₀ D E : ℝ) (ψ φ₁ φ₂ : ℝ → ℂ) :
    smoothDelta N₀ D E ψ φ₁ φ₂ =
      Tij N₀ D E ψ φ₁ φ₂ 0 0 - Tij N₀ D E ψ φ₁ φ₂ 0 1 - Tij N₀ D E ψ φ₁ φ₂ 1 0
        + Tij N₀ D E ψ φ₁ φ₂ 1 1 := by
  set H : ℕ → ℕ → ℂ := fun d e => φ₁ ((d : ℝ) / D) * φ₂ ((e : ℝ) / E) * bracket N₀ ψ d e
    with hH
  -- the four classes as double sums over odd variables
  have hT : ∀ i j : ℕ, Tij N₀ D E ψ φ₁ φ₂ i j =
      ∑ d ∈ (Finset.Icc 1 (⌊2 * D⌋₊ / 2 ^ i)).filter Odd,
        ∑ e ∈ (Finset.Icc 1 (⌊2 * E⌋₊ / 2 ^ j)).filter Odd,
          (μ d : ℂ) * ((μ e : ℂ) * H (2 ^ i * d) (2 ^ j * e)) := by
    intro i j
    rw [reorder]
    · refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun d _ => ?_
      simp only [hH, div_div_eq_mul_div]
      push_cast
      rw [mul_comm (d : ℝ), mul_comm (e : ℝ)]
      ring
    · intro d e hd _ hc
      simp [hH, bracket_noncop N₀ ψ i j hd hc]
  rw [hT 0 0, hT 0 1, hT 1 0, hT 1 1]
  simp only [pow_zero, pow_one, one_mul, Nat.div_one]
  have h0 : smoothDelta N₀ D E ψ φ₁ φ₂ = ∑ d ∈ Finset.Icc 1 ⌊2 * D⌋₊,
      (μ d : ℂ) * ∑ e ∈ Finset.Icc 1 ⌊2 * E⌋₊, (μ e : ℂ) * H d e := by
    rw [smoothDelta]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [hH]; ring
  rw [h0, sum_mobius_parity]
  simp only [sum_mobius_parity ⌊2 * E⌋₊, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  ring

lemma norm_mu_le (n : ℕ) : ‖(μ n : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_intCast]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one

lemma norm_le_one_of_tempered {f : ℝ → ℂ} {P : ℝ} {k : ℕ} {a b : ℝ}
    (hf : TemperedOn f P k a b) (x : ℝ) : ‖f x‖ ≤ 1 := by
  have := hf.2.2 0 (Nat.zero_le _) x
  simpa using this

lemma mem_of_ne_zero {f : ℝ → ℂ} {P : ℝ} {k : ℕ} {a b : ℝ}
    (hf : TemperedOn f P k a b) {x : ℝ} (hx : f x ≠ 0) : x ∈ Set.Icc a b := by
  by_contra h
  exact hx (hf.2.1 x h)

/-- The Poisson tail ratio is at most `(Q/N₀)/N₀³` once `M + 1 > Q N₀^{ε₀-1}`, `q ≤ Q`. -/
lemma tail_ratio_le {N₀ ε₀ q Q : ℝ} {kψ M : ℕ} (hN₀ : 1 ≤ N₀)
    (hk : (3 : ℝ) ≤ ε₀ * ((kψ - 2 : ℕ) : ℝ)) (hq : 0 < q) (hqQ : q ≤ Q)
    (hM : Q * N₀ ^ (ε₀ - 1) < (M : ℝ) + 1) :
    (q / N₀) / (((M : ℝ) + 1) * N₀ / q) ^ (kψ - 2) ≤ (Q / N₀) / N₀ ^ 3 := by
  have hN0 : 0 < N₀ := by linarith
  have hQ : 0 < Q := lt_of_lt_of_le hq hqQ
  have hX : N₀ ^ ε₀ ≤ ((M : ℝ) + 1) * N₀ / q := by
    rw [le_div_iff₀ hq]
    have h1 : N₀ ^ ε₀ = N₀ ^ (ε₀ - 1) * N₀ := by
      rw [← Real.rpow_add_one hN0.ne']; ring_nf
    calc N₀ ^ ε₀ * q ≤ N₀ ^ ε₀ * Q := by gcongr
      _ = Q * N₀ ^ (ε₀ - 1) * N₀ := by rw [h1]; ring
      _ ≤ ((M : ℝ) + 1) * N₀ := by gcongr
  have hpow : N₀ ^ 3 ≤ (((M : ℝ) + 1) * N₀ / q) ^ (kψ - 2) := by
    calc N₀ ^ 3 = N₀ ^ ((3 : ℕ) : ℝ) := by rw [Real.rpow_natCast]
      _ ≤ N₀ ^ (ε₀ * ((kψ - 2 : ℕ) : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hN₀ (by exact_mod_cast hk)
      _ = (N₀ ^ ε₀) ^ (kψ - 2) := by rw [Real.rpow_mul hN0.le, Real.rpow_natCast]
      _ ≤ (((M : ℝ) + 1) * N₀ / q) ^ (kψ - 2) := by
          gcongr
  apply div_le_div₀ (by positivity) (by gcongr) (by positivity) hpow

/-- Bound for one parity class. -/
theorem T_bound (hMV : MeanValueThm) (hM : MellinSeparation) (hP : PoissonAPDecay)
    (η : ℝ) (hη : 0 < η) (hη' : η ≤ 1 / 100) : ∃ k : ℕ, ∃ C > (0 : ℝ),
    ∀ (N₀ D E P : ℝ) (ψ φ₁ φ₂ : ℝ → ℂ), 2 ≤ N₀ → 1 ≤ D → 1 ≤ E →
      D ≤ N₀ ^ (9 / 17 - η) → E ≤ N₀ ^ (9 / 17 - η) → 1 ≤ P →
      TemperedOn ψ P k (1/2) 2 → TemperedOn φ₁ P k (1/2) 2 → TemperedOn φ₂ P k (1/2) 2 →
      ∀ i j : ℕ, i ≤ 1 → j ≤ 1 → ‖Tij N₀ D E ψ φ₁ φ₂ i j‖ ≤ C * P ^ k * N₀ ^ (1 - η) := by
  obtain ⟨kV, ε₀, hε₀, hε₀', CF, hCF, hF⟩ := finite_part_bound hMV hM η hη hη'
  set kψ : ℕ := ⌈3 / ε₀⌉₊ + 2 with hkψ
  have hkψ2 : 2 ≤ kψ := by omega
  have hk3 : (3 : ℝ) ≤ ε₀ * ((kψ - 2 : ℕ) : ℝ) := by
    have h1 : kψ - 2 = ⌈3 / ε₀⌉₊ := by omega
    rw [h1]
    have h2 := Nat.le_ceil (3 / ε₀)
    rw [div_le_iff₀ hε₀] at h2
    linarith
  obtain ⟨CP, hCP, hPo⟩ := Poisson.bracket_poisson hP kψ hkψ2
  refine ⟨max kV kψ, 2 * CF + 32 * CP, by positivity, ?_⟩
  intro N₀ D E P ψ φ₁ φ₂ hN₀ hD hE hDc hEc hP1 hψ hφ₁ hφ₂ i j hi hj
  unfold Tij
  have hN0pos : (0 : ℝ) < N₀ := by linarith
  have hN0one : (1 : ℝ) ≤ N₀ := by linarith
  have hcN : N₀ ^ (9 / 17 - η) ≤ N₀ := by
    calc N₀ ^ (9 / 17 - η) ≤ N₀ ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN0one (by linarith)
      _ = N₀ := Real.rpow_one N₀
  have hDN : D ≤ N₀ := hDc.trans hcN
  have hEN : E ≤ N₀ := hEc.trans hcN
  have hkV : kV ≤ max kV kψ := le_max_left _ _
  have hkψ' : kψ ≤ max kV kψ := le_max_right _ _
  have hψ0 : TemperedOn ψ P 0 (1/2) 2 := temperedOn_mono_k hψ (Nat.zero_le _)
  have hψk : TemperedOn ψ P kψ (1/2) 2 := temperedOn_mono_k hψ hkψ'
  have hφ₁V : TemperedOn φ₁ P kV (1/2) 2 := temperedOn_mono_k hφ₁ hkV
  have hφ₂V : TemperedOn φ₂ P kV (1/2) 2 := temperedOn_mono_k hφ₂ hkV
  have h2i : (1 : ℝ) ≤ 2 ^ i ∧ (2 : ℝ) ^ i ≤ 2 := by
    interval_cases i <;> norm_num
  have h2j : (1 : ℝ) ≤ 2 ^ j ∧ (2 : ℝ) ^ j ≤ 2 := by
    interval_cases j <;> norm_num
  have hℓκ : (ellOf i j = 1 ∧ kapOf i j = 2) ∨ (ellOf i j = 2 ∧ kapOf i j = 1) := ellOf_kapOf
  set ℓ : ℕ := ellOf i j with hℓdef
  set κ : ℤ := kapOf i j with hκdef
  have hℓ : ℓ = 1 ∨ ℓ = 2 := by
    rcases hℓκ with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hκ0 : κ ≠ 0 := by rcases hℓκ with h | h <;> rw [h.2] <;> norm_num
  have hκ2 : |κ| ≤ 2 := by rcases hℓκ with h | h <;> rw [h.2] <;> norm_num
  have hℓR : (1 : ℝ) ≤ ℓ ∧ (ℓ : ℝ) ≤ 2 := by rcases hℓ with h | h <;> rw [h] <;> norm_num
  have hℓpos : 0 < ℓ := by rcases hℓ with h | h <;> rw [h] <;> norm_num
  set D' : ℝ := D / 2 ^ i with hD'
  set E' : ℝ := E / 2 ^ j with hE'
  have hD'half : 1 / 2 ≤ D' := by
    rw [hD', le_div_iff₀ (by positivity)]; nlinarith
  have hE'half : 1 / 2 ≤ E' := by
    rw [hE', le_div_iff₀ (by positivity)]; nlinarith
  have hD'pos : 0 < D' := by linarith
  have hE'pos : 0 < E' := by linarith
  have hD'D : D' ≤ D := div_le_self (by linarith) h2i.1
  have hE'E : E' ≤ E := div_le_self (by linarith) h2j.1
  set MD : ℕ := ⌊2 * D⌋₊ / 2 ^ i with hMD
  set ME : ℕ := ⌊2 * E⌋₊ / 2 ^ j with hME
  have hMDle : ⌊2 * D'⌋₊ ≤ MD := floor_two_mul_div_le D (by linarith) i
  have hMEle : ⌊2 * E'⌋₊ ≤ ME := floor_two_mul_div_le E (by linarith) j
  have hMDR : (MD : ℝ) ≤ 2 * D := by
    have h1 : MD ≤ ⌊2 * D⌋₊ := Nat.div_le_self _ _
    have h2 : (⌊2 * D⌋₊ : ℝ) ≤ 2 * D := Nat.floor_le (by linarith)
    exact (Nat.cast_le.mpr h1).trans h2
  have hMER : (ME : ℝ) ≤ 2 * E := by
    have h1 : ME ≤ ⌊2 * E⌋₊ := Nat.div_le_self _ _
    have h2 : (⌊2 * E⌋₊ : ℝ) ≤ 2 * E := Nat.floor_le (by linarith)
    exact (Nat.cast_le.mpr h1).trans h2
  set M : ℕ := ⌊4 * (ℓ : ℝ) * D' * E' * N₀ ^ (ε₀ - 1)⌋₊ with hMdef
  have hMle : (M : ℝ) ≤ 4 * ℓ * D' * E' * N₀ ^ (ε₀ - 1) := Nat.floor_le (by positivity)
  have hMlt : 4 * (ℓ : ℝ) * D' * E' * N₀ ^ (ε₀ - 1) < (M : ℝ) + 1 := Nat.lt_floor_add_one _
  -- the finite parts
  set Fs : ℝ → ℤ → ℕ → ℕ → ℂ := fun ς σ d e => ∑ h ∈ Finset.Icc 1 M,
      ((N₀ / (ℓ * d * e) : ℝ) : ℂ) * fourierR ψ (ς * (h * N₀ / (ℓ * d * e))) *
        kfrac e (σ * h) d with hFs
  have hS : ∀ (ς : ℝ) (σ : ℤ), (ς = 1 ∨ ς = -1) → σ ≠ 0 → |σ| ≤ 2 →
      ‖∑ e ∈ (Finset.Icc 1 ME).filter Odd,
          ∑ d ∈ (Finset.Icc 1 MD).filter (fun a => Nat.Coprime a (2 * e)),
            (μ d : ℂ) * (μ e : ℂ) * φ₁ ((d : ℝ) / D') * φ₂ ((e : ℝ) / E') * Fs ς σ d e‖
        ≤ CF * P ^ kV * N₀ ^ (1 - η) := by
    intro ς σ hς hσ0 hσ2
    by_cases hor : E' ≤ D'
    · have := hF N₀ D' E' P ς ℓ 0 σ M MD ME ψ φ₁ φ₂ hN₀ hE'half hor (hD'D.trans hDc) hℓ hς
        (by norm_num) hσ0 hσ2 hMle hMDle hP1 hψ0 hφ₁V (norm_le_one_of_tempered hφ₂) hφ₂.2.1
      refine le_trans (le_of_eq ?_) this
      congr 1
      refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun d _ => ?_
      congr 1
      refine Finset.sum_congr rfl fun h _ => ?_
      simp only [zero_mul, Int.cast_zero, mul_zero, zero_div, Complex.exp_zero, mul_one]
    · rw [not_le] at hor
      have := hF N₀ E' D' P ς ℓ σ (-σ) M ME MD ψ φ₂ φ₁ hN₀ hD'half hor.le (hE'E.trans hEc) hℓ hς
        hσ2 (neg_ne_zero.mpr hσ0) (by rwa [abs_neg]) (by linarith) hMEle hP1 hψ0 hφ₂V
        (norm_le_one_of_tempered hφ₁) hφ₁.2.1
      refine le_trans (le_of_eq ?_) this
      congr 1
      -- reciprocity inside, then exchange the two variables
      have hrec : ∑ e ∈ (Finset.Icc 1 ME).filter Odd,
          ∑ d ∈ (Finset.Icc 1 MD).filter (fun a => Nat.Coprime a (2 * e)),
            (μ d : ℂ) * (μ e : ℂ) * φ₁ ((d : ℝ) / D') * φ₂ ((e : ℝ) / E') * Fs ς σ d e =
          ∑ e ∈ (Finset.Icc 1 ME).filter Odd,
          ∑ d ∈ (Finset.Icc 1 MD).filter (fun a => Nat.Coprime a (2 * e)),
            (μ d : ℂ) * (μ e : ℂ) * φ₁ ((d : ℝ) / D') * φ₂ ((e : ℝ) / E') *
              ∑ h ∈ Finset.Icc 1 M, ((N₀ / (ℓ * d * e) : ℝ) : ℂ) *
                fourierR ψ (ς * (h * N₀ / (ℓ * d * e))) *
                (Complex.exp (2 * π * Complex.I * ((σ * h : ℤ) : ℂ) / ((d * e : ℕ) : ℂ)) *
                  kfrac d (-(σ * h)) e) := by
        refine Finset.sum_congr rfl fun e he => Finset.sum_congr rfl fun d hd => ?_
        have he' := Finset.mem_filter.mp he
        have hd' := Finset.mem_filter.mp hd
        have hcop : Nat.Coprime d e := (coprime_two_mul_iff.mp hd'.2).2
        have hd1 : 0 < d := (Finset.mem_Icc.mp hd'.1).1
        have he1 : 0 < e := (Finset.mem_Icc.mp he'.1).1
        congr 1
        refine Finset.sum_congr rfl fun h _ => ?_
        rw [kfrac_reciprocity hd1 he1 hcop]
      rw [hrec, sum_odd_coprime_comm]
      refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => ?_
      have hsum : ∑ h ∈ Finset.Icc 1 M, ((N₀ / (ℓ * d * e) : ℝ) : ℂ) *
                fourierR ψ (ς * (h * N₀ / (ℓ * d * e))) *
                (Complex.exp (2 * π * Complex.I * ((σ * h : ℤ) : ℂ) / ((d * e : ℕ) : ℂ)) *
                  kfrac d (-(σ * h)) e) =
          ∑ h ∈ Finset.Icc 1 M, ((N₀ / (ℓ * e * d) : ℝ) : ℂ) *
                fourierR ψ (ς * (h * N₀ / (ℓ * e * d))) *
                Complex.exp (2 * π * Complex.I * ((σ * h : ℤ) : ℂ) / ((e * d : ℕ) : ℂ)) *
                  kfrac d (-σ * h) e := by
        refine Finset.sum_congr rfl fun h _ => ?_
        rw [show (ℓ : ℝ) * e * d = ℓ * d * e by ring, Nat.mul_comm e d, neg_mul]
        ring
      rw [hsum]
      ring
  -- decomposition of each bracket
  have hsplit3 : ∀ e d : ℕ, (μ d : ℂ) * (μ e : ℂ) * φ₁ ((d : ℝ) / D') * φ₂ ((e : ℝ) / E') *
        bracket N₀ ψ (2 ^ i * d) (2 ^ j * e) =
      (μ d : ℂ) * (μ e : ℂ) * φ₁ ((d : ℝ) / D') * φ₂ ((e : ℝ) / E') * Fs 1 (-κ) d e +
      (μ d : ℂ) * (μ e : ℂ) * φ₁ ((d : ℝ) / D') * φ₂ ((e : ℝ) / E') * Fs (-1) κ d e +
      (μ d : ℂ) * (μ e : ℂ) * φ₁ ((d : ℝ) / D') * φ₂ ((e : ℝ) / E') *
        (bracket N₀ ψ (2 ^ i * d) (2 ^ j * e) - Fs 1 (-κ) d e - Fs (-1) κ d e) := by
    intro e d; ring
  simp only [hsplit3, Finset.sum_add_distrib]
  -- the Poisson tails
  have hErr : ‖∑ e ∈ (Finset.Icc 1 ME).filter Odd,
          ∑ d ∈ (Finset.Icc 1 MD).filter (fun a => Nat.Coprime a (2 * e)),
            (μ d : ℂ) * (μ e : ℂ) * φ₁ ((d : ℝ) / D') * φ₂ ((e : ℝ) / E') *
              (bracket N₀ ψ (2 ^ i * d) (2 ^ j * e) - Fs 1 (-κ) d e - Fs (-1) κ d e)‖
        ≤ 32 * CP * P ^ kψ := by
    set Bp : ℝ := CP * P ^ kψ * ((4 * ℓ * D' * E') / N₀) / N₀ ^ 3 with hBp
    have hBp0 : 0 ≤ Bp := by positivity
    have hterm : ∀ e ∈ (Finset.Icc 1 ME).filter Odd,
        ∀ d ∈ (Finset.Icc 1 MD).filter (fun a => Nat.Coprime a (2 * e)),
        ‖(μ d : ℂ) * (μ e : ℂ) * φ₁ ((d : ℝ) / D') * φ₂ ((e : ℝ) / E') *
              (bracket N₀ ψ (2 ^ i * d) (2 ^ j * e) - Fs 1 (-κ) d e - Fs (-1) κ d e)‖ ≤ Bp := by
      intro e he d hd
      by_cases hz : φ₁ ((d : ℝ) / D') = 0 ∨ φ₂ ((e : ℝ) / E') = 0
      · rcases hz with hz | hz <;> simp [hz, hBp0]
      rw [not_or] at hz
      obtain ⟨hz1, hz2⟩ := hz
      have hm1 := mem_of_ne_zero hφ₁ hz1
      have hm2 := mem_of_ne_zero hφ₂ hz2
      have hdle : (d : ℝ) ≤ 2 * D' := by
        have := hm1.2; rwa [div_le_iff₀ hD'pos] at this
      have hele : (e : ℝ) ≤ 2 * E' := by
        have := hm2.2; rwa [div_le_iff₀ hE'pos] at this
      have he' := Finset.mem_filter.mp he
      have hd' := Finset.mem_filter.mp hd
      obtain ⟨hdo, hcop⟩ := coprime_two_mul_iff.mp hd'.2
      have heo : Odd e := he'.2
      have hd1 : 0 < d := (Finset.mem_Icc.mp hd'.1).1
      have he1 : 0 < e := (Finset.mem_Icc.mp he'.1).1
      obtain ⟨hcl, hdn, hph⟩ := pair_class hi hj hdo heo hcop
      simp only [← hℓdef, ← hκdef] at hcl hdn hph
      have hqpos : 0 < ℓ * d * e := by positivity
      have hPB := hPo N₀ P ψ hN0pos hP1 hψk (2 ^ i * d) (2 ^ j * e) (ℓ * d * e)
        (c0Of i j d e) hqpos hcl hdn M
      have hfin : ∑ h ∈ Finset.Icc 1 M, ((N₀ / ((ℓ * d * e : ℕ) : ℝ) : ℝ) : ℂ) *
            (fourierR ψ (h * N₀ / ((ℓ * d * e : ℕ) : ℝ)) *
                Complex.exp (2 * π * Complex.I * (((h : ℤ) * c0Of i j d e : ℤ) : ℂ) /
                  ((ℓ * d * e : ℕ) : ℂ)) +
              fourierR ψ (-(h * N₀ / ((ℓ * d * e : ℕ) : ℝ))) *
                Complex.exp (2 * π * Complex.I * ((-(h : ℤ) * c0Of i j d e : ℤ) : ℂ) /
                  ((ℓ * d * e : ℕ) : ℂ)))
          = Fs 1 (-κ) d e + Fs (-1) κ d e := by
        rw [hFs]
        dsimp only
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun h _ => ?_
        rw [hph, hph, show -κ * -(h : ℤ) = κ * h by ring]
        push_cast
        ring_nf
      rw [hfin] at hPB
      have hqQ : ((ℓ * d * e : ℕ) : ℝ) ≤ 4 * ℓ * D' * E' := by
        push_cast
        have h0 : (0 : ℝ) ≤ ℓ := by positivity
        calc (ℓ : ℝ) * d * e ≤ ℓ * (2 * D') * (2 * E') := by gcongr
          _ = 4 * ℓ * D' * E' := by ring
      have hratio := tail_ratio_le (kψ := kψ) (M := M) hN0one hk3
        (by exact_mod_cast hqpos) hqQ hMlt
      have hw : ‖(μ d : ℂ) * (μ e : ℂ) * φ₁ ((d : ℝ) / D') * φ₂ ((e : ℝ) / E')‖ ≤ 1 := by
        rw [norm_mul, norm_mul, norm_mul]
        have := norm_mu_le d
        have := norm_mu_le e
        have := norm_le_one_of_tempered hφ₁ ((d : ℝ) / D')
        have := norm_le_one_of_tempered hφ₂ ((e : ℝ) / E')
        have h1 : 0 ≤ ‖(μ d : ℂ)‖ := norm_nonneg _
        have h2 : 0 ≤ ‖(μ e : ℂ)‖ := norm_nonneg _
        have h3 : 0 ≤ ‖φ₁ ((d : ℝ) / D')‖ := norm_nonneg _
        have h4 : 0 ≤ ‖φ₂ ((e : ℝ) / E')‖ := norm_nonneg _
        calc ‖(μ d : ℂ)‖ * ‖(μ e : ℂ)‖ * ‖φ₁ ((d : ℝ) / D')‖ * ‖φ₂ ((e : ℝ) / E')‖
            ≤ 1 * 1 * 1 * 1 := by gcongr
          _ = 1 := by norm_num
      rw [norm_mul]
      have hR : ‖bracket N₀ ψ (2 ^ i * d) (2 ^ j * e) - Fs 1 (-κ) d e - Fs (-1) κ d e‖ ≤ Bp := by
        rw [sub_sub]
        refine hPB.trans ?_
        rw [mul_div_assoc (CP * P ^ kψ)]
        calc CP * P ^ kψ * (((ℓ * d * e : ℕ) : ℝ) / N₀ /
              (((M : ℝ) + 1) * N₀ / ((ℓ * d * e : ℕ) : ℝ)) ^ (kψ - 2))
            ≤ CP * P ^ kψ * ((4 * ℓ * D' * E') / N₀ / N₀ ^ 3) := by gcongr
          _ = Bp := by rw [hBp]; ring
      calc _ ≤ 1 * Bp := by gcongr
        _ = Bp := one_mul _
    have hDE : D * E ≤ N₀ ^ 2 := by
      rw [sq]; exact mul_le_mul hDN hEN (by linarith) (by linarith)
    have hQle : 4 * (ℓ : ℝ) * D' * E' ≤ 8 * D * E := by
      calc 4 * (ℓ : ℝ) * D' * E' ≤ 4 * 2 * D * E := by
            have : (0 : ℝ) ≤ ℓ := by positivity
            gcongr
            exact hℓR.2
        _ = 8 * D * E := by ring
    calc _ ≤ ∑ e ∈ (Finset.Icc 1 ME).filter Odd,
            ∑ d ∈ (Finset.Icc 1 MD).filter (fun a => Nat.Coprime a (2 * e)),
            ‖(μ d : ℂ) * (μ e : ℂ) * φ₁ ((d : ℝ) / D') * φ₂ ((e : ℝ) / E') *
              (bracket N₀ ψ (2 ^ i * d) (2 ^ j * e) - Fs 1 (-κ) d e - Fs (-1) κ d e)‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun e _ => norm_sum_le _ _)
      _ ≤ ∑ e ∈ (Finset.Icc 1 ME).filter Odd,
            ∑ d ∈ (Finset.Icc 1 MD).filter (fun a => Nat.Coprime a (2 * e)), Bp :=
          Finset.sum_le_sum fun e he => Finset.sum_le_sum fun d hd => hterm e he d hd
      _ ≤ ∑ e ∈ (Finset.Icc 1 ME).filter Odd, ∑ d ∈ Finset.Icc 1 MD, Bp := by
          refine Finset.sum_le_sum fun e _ => ?_
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => hBp0)
      _ ≤ ∑ e ∈ Finset.Icc 1 ME, ∑ d ∈ Finset.Icc 1 MD, Bp :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => Finset.sum_nonneg fun _ _ => hBp0)
      _ = (ME : ℝ) * MD * Bp := by
          simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
          ring
      _ ≤ (2 * E) * (2 * D) * Bp := by gcongr
      _ ≤ (2 * E) * (2 * D) * (CP * P ^ kψ * ((8 * D * E) / N₀) / N₀ ^ 3) := by
          rw [hBp]; gcongr
      _ = 32 * CP * P ^ kψ * ((D * E) ^ 2 / N₀ ^ 4) := by
          field_simp
          ring
      _ ≤ 32 * CP * P ^ kψ * 1 := by
          gcongr
          rw [div_le_one (by positivity)]
          calc (D * E) ^ 2 ≤ (N₀ ^ 2) ^ 2 := by gcongr
            _ = N₀ ^ 4 := by ring
      _ = 32 * CP * P ^ kψ := mul_one _
  have h1 := hS 1 (-κ) (Or.inl rfl) (neg_ne_zero.mpr hκ0) (by rwa [abs_neg])
  have h2 := hS (-1) κ (Or.inr rfl) hκ0 hκ2
  have hPV : P ^ kV ≤ P ^ max kV kψ := pow_le_pow_right₀ hP1 hkV
  have hPψ : P ^ kψ ≤ P ^ max kV kψ := pow_le_pow_right₀ hP1 hkψ'
  have hN1 : (1 : ℝ) ≤ N₀ ^ (1 - η) := Real.one_le_rpow hN0one (by linarith)
  have hPpos : 0 < P ^ max kV kψ := by positivity
  calc _ ≤ _ := norm_add₃_le
    _ ≤ CF * P ^ kV * N₀ ^ (1 - η) + CF * P ^ kV * N₀ ^ (1 - η) + 32 * CP * P ^ kψ := by
        gcongr
    _ ≤ CF * P ^ max kV kψ * N₀ ^ (1 - η) + CF * P ^ max kV kψ * N₀ ^ (1 - η) +
          32 * CP * (P ^ max kV kψ * N₀ ^ (1 - η)) := by
        gcongr
        calc P ^ kψ ≤ P ^ max kV kψ := hPψ
          _ = P ^ max kV kψ * 1 := (mul_one _).symm
          _ ≤ P ^ max kV kψ * N₀ ^ (1 - η) := by gcongr
    _ = (2 * CF + 32 * CP) * P ^ max kV kψ * N₀ ^ (1 - η) := by ring

end Smooth

open Smooth in
/-- **Proposition 8.1** (smooth version of the level of distribution). -/
theorem smoothDelta_bound (hMV : MeanValueThm) (hM : MellinSeparation)
    (hP : PoissonAPDecay) :
    ∀ η : ℝ, 0 < η → η ≤ 1 / 100 → ∃ k : ℕ, ∃ C > (0 : ℝ),
    ∀ (N₀ D E P : ℝ) (ψ φ₁ φ₂ : ℝ → ℂ), 2 ≤ N₀ → 1 ≤ D → 1 ≤ E →
      D ≤ N₀ ^ (9 / 17 - η) → E ≤ N₀ ^ (9 / 17 - η) → 1 ≤ P →
      TemperedOn ψ P k (1/2) 2 → TemperedOn φ₁ P k (1/2) 2 → TemperedOn φ₂ P k (1/2) 2 →
      ‖smoothDelta N₀ D E ψ φ₁ φ₂‖ ≤ C * P ^ k * N₀ ^ (1 - η) := by
  intro η hη hη'
  obtain ⟨k, C, hC, hT⟩ := T_bound hMV hM hP η hη hη'
  refine ⟨k, 4 * C, by positivity, ?_⟩
  intro N₀ D E P ψ φ₁ φ₂ hN₀ hD hE hDc hEc hP1 hψ hφ₁ hφ₂
  have hb := hT N₀ D E P ψ φ₁ φ₂ hN₀ hD hE hDc hEc hP1 hψ hφ₁ hφ₂
  rw [smoothDelta_split]
  calc _ ≤ ‖Tij N₀ D E ψ φ₁ φ₂ 0 0 - Tij N₀ D E ψ φ₁ φ₂ 0 1 - Tij N₀ D E ψ φ₁ φ₂ 1 0‖
          + ‖Tij N₀ D E ψ φ₁ φ₂ 1 1‖ := norm_add_le _ _
    _ ≤ ‖Tij N₀ D E ψ φ₁ φ₂ 0 0‖ + ‖Tij N₀ D E ψ φ₁ φ₂ 0 1‖ + ‖Tij N₀ D E ψ φ₁ φ₂ 1 0‖
          + ‖Tij N₀ D E ψ φ₁ φ₂ 1 1‖ := by
        gcongr
        exact (norm_sub_le _ _).trans (by gcongr; exact norm_sub_le _ _)
    _ ≤ C * P ^ k * N₀ ^ (1 - η) + C * P ^ k * N₀ ^ (1 - η) + C * P ^ k * N₀ ^ (1 - η)
          + C * P ^ k * N₀ ^ (1 - η) := by
        gcongr
        · exact hb 0 0 (by norm_num) (by norm_num)
        · exact hb 0 1 (by norm_num) (by norm_num)
        · exact hb 1 0 (by norm_num) (by norm_num)
        · exact hb 1 1 (by norm_num) (by norm_num)
    _ = 4 * C * P ^ k * N₀ ^ (1 - η) := by ring

end Level

end MobiusDeterminant
