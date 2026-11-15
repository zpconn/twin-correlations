import MobiusDeterminant.Unconditional.LevelDefs
import MobiusDeterminant.Unconditional.LevelTempered
import MobiusDeterminant.Unconditional.LevelCore

/-!
# Finite-frequency part of Proposition 8.1 (one orientation)

We prove `finite_part_bound`: after Poisson summation, the frequencies `1 ≤ h ≤ M` with
`M ≤ 4ℓAB N₀^{ε₀-1}` contribute `O(P^{kV} N₀^{1-η})`.

Proof: dyadic blocks `2^m ≤ h < 2^{m+1}`; in each block the coupled weight is
`(N₀/(ℓAB)) (H/h) cn F(s)`, `s = (h/H)(A/a)(B/b)`, with `F` from `blockF_tempered`; then
`core_block` and exponent bookkeeping (done with logarithms).  Small `N₀` is trivial.
-/

open Finset Real
open scoped ArithmeticFunction.Moebius

namespace MobiusDeterminant

namespace Level

namespace Finite

/-! ## Norms of phases -/

lemma norm_cexp_two_pi (r : ℝ) : ‖Complex.exp (2 * π * Complex.I * (r : ℂ))‖ = 1 := by
  have : 2 * (π : ℂ) * Complex.I * (r : ℂ) = ((2 * π * r : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

lemma norm_cexp_two_pi_div (x y : ℝ) :
    ‖Complex.exp (2 * π * Complex.I * (x : ℂ) / (y : ℂ))‖ = 1 := by
  have : 2 * (π : ℂ) * Complex.I * (x : ℂ) / (y : ℂ) = 2 * π * Complex.I * ((x / y : ℝ) : ℂ) := by
    push_cast; ring
  rw [this, norm_cexp_two_pi]

lemma norm_cexp_int_nat (n : ℤ) (q : ℕ) :
    ‖Complex.exp (2 * π * Complex.I * (n : ℂ) / (q : ℂ))‖ = 1 := by
  have h := norm_cexp_two_pi_div (n : ℝ) (q : ℝ)
  simpa using h

lemma norm_kfrac (e : ℕ) (h : ℤ) (d : ℕ) : ‖kfrac e h d‖ = 1 := by
  unfold kfrac
  have h := norm_cexp_two_pi_div ((((h : ZMod e) * (d : ZMod e)⁻¹).val : ℕ) : ℝ) (e : ℝ)
  simpa using h

/-! ## Tempered functions: trivial facts -/

lemma tempered_norm_le_one {f : ℝ → ℂ} {P : ℝ} {k : ℕ} {a b : ℝ}
    (hf : TemperedOn f P k a b) (x : ℝ) : ‖f x‖ ≤ 1 := by
  have := hf.2.2 0 (Nat.zero_le _) x
  simpa using this

lemma tempered_zero {f : ℝ → ℂ} {P : ℝ} {k : ℕ} {a b : ℝ}
    (hf : TemperedOn f P k a b) {x : ℝ} (hx : x ∉ Set.Icc a b) : f x = 0 :=
  hf.2.1 x hx

/-- Sum of a weight bounded by `1` and vanishing beyond `X`, over positive integers. -/
lemma sum_weight_le {s : Finset ℕ} {f : ℕ → ℝ} {X : ℝ} (hs : ∀ a ∈ s, 1 ≤ a)
    (h1 : ∀ a, f a ≤ 1) (hz : ∀ a : ℕ, X < a → f a = 0) (hX : 0 ≤ X) :
    ∑ a ∈ s, f a ≤ X := by
  calc ∑ a ∈ s, f a ≤ ∑ a ∈ s.filter (fun a : ℕ => (a : ℝ) ≤ X), (1 : ℝ) := by
        rw [Finset.sum_filter]
        apply Finset.sum_le_sum
        intro a _
        split_ifs with h
        · exact h1 a
        · rw [hz a (lt_of_not_ge h)]
    _ = ((s.filter (fun a : ℕ => (a : ℝ) ≤ X)).card : ℝ) := by simp
    _ ≤ ((Finset.Icc 1 ⌊X⌋₊).card : ℝ) := by
        gcongr
        intro a ha
        rw [Finset.mem_filter] at ha
        rw [Finset.mem_Icc]
        exact ⟨hs a ha.1, Nat.le_floor ha.2⟩
    _ ≤ X := by
        simp only [Nat.card_Icc, add_tsub_cancel_right]
        exact Nat.floor_le hX

/-- `∑_a ‖φ(a/A)‖ ≤ 2A` for `φ` bounded by `1` and supported in `[1/2, 2]`. -/
lemma sum_phi_le {s : Finset ℕ} {φ : ℝ → ℂ} {A : ℝ} (hA : 0 < A) (hs : ∀ a ∈ s, 1 ≤ a)
    (h1 : ∀ x, ‖φ x‖ ≤ 1) (h0 : ∀ x, x ∉ Set.Icc (1/2 : ℝ) 2 → φ x = 0) :
    ∑ a ∈ s, ‖φ ((a : ℝ) / A)‖ ≤ 2 * A := by
  apply sum_weight_le hs (fun a => h1 _) _ (by linarith)
  intro a ha
  rw [h0, norm_zero]
  intro hmem
  have := hmem.2
  rw [div_le_iff₀ hA] at this
  linarith


/-- The summand of `finite_part_bound` (frequency `h`). -/
noncomputable def term (N₀ ς : ℝ) (ℓ : ℕ) (ρ σ : ℤ) (ψ : ℝ → ℂ) (a b h : ℕ) : ℂ :=
  ((N₀ / (ℓ * a * b) : ℝ) : ℂ) * fourierR ψ (ς * (h * N₀ / (ℓ * a * b))) *
    Complex.exp (2 * π * Complex.I * ((ρ * h : ℤ) : ℂ) / ((a * b : ℕ) : ℂ)) *
    kfrac b (σ * h) a

lemma norm_term_le {N₀ ς P : ℝ} {ℓ : ℕ} {ρ σ : ℤ} {ψ : ℝ → ℂ} {a b h : ℕ}
    (hN : 0 ≤ N₀) (hℓ : 1 ≤ ℓ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hψ : TemperedOn ψ P 0 (1/2) 2) :
    ‖term N₀ ς ℓ ρ σ ψ a b h‖ ≤ 3 / 2 * N₀ := by
  unfold term
  rw [norm_mul, norm_mul, norm_mul, norm_kfrac, norm_cexp_int_nat, mul_one, mul_one,
    Complex.norm_real, Real.norm_eq_abs]
  have hden : (1 : ℝ) ≤ ℓ * a * b := by
    have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    have : (1 : ℝ) ≤ a := by exact_mod_cast ha
    have : (1 : ℝ) ≤ b := by exact_mod_cast hb
    calc (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ ℓ * a * b := by gcongr
  have h1 : |N₀ / (ℓ * a * b)| ≤ N₀ := by
    rw [abs_of_nonneg (div_nonneg hN (by linarith))]
    exact div_le_self hN hden
  have h2 := norm_fourierR_le hψ (ς * (h * N₀ / (ℓ * a * b)))
  calc |N₀ / (ℓ * a * b)| * ‖fourierR ψ (ς * (h * N₀ / (ℓ * a * b)))‖
      ≤ N₀ * (3 / 2) := by gcongr
    _ = 3 / 2 * N₀ := by ring

lemma trivial_bound {N₀ A B P ς : ℝ} {ℓ : ℕ} {ρ σ : ℤ} {M Ma Mb kV : ℕ} {ψ φa φb : ℝ → ℂ}
    (hN : 0 ≤ N₀) (hA : 0 < A) (hB : 0 < B) (hℓ : 1 ≤ ℓ)
    (hψ : TemperedOn ψ P 0 (1/2) 2) (hφa : TemperedOn φa P kV (1/2) 2)
    (hφb1 : ∀ x, ‖φb x‖ ≤ 1) (hφb0 : ∀ x, x ∉ Set.Icc (1/2 : ℝ) 2 → φb x = 0) :
    ‖∑ b ∈ (Finset.Icc 1 Mb).filter Odd,
          ∑ a ∈ (Finset.Icc 1 Ma).filter (fun a => Nat.Coprime a (2 * b)),
            (μ a : ℂ) * (μ b : ℂ) * φa ((a : ℝ) / A) * φb ((b : ℝ) / B) *
              ∑ h ∈ Finset.Icc 1 M, term N₀ ς ℓ ρ σ ψ a b h‖
      ≤ 6 * A * B * M * N₀ := by
  have hX : 0 ≤ (M : ℝ) * (3 / 2 * N₀) := by positivity
  have hinner : ∀ b ∈ (Finset.Icc 1 Mb).filter Odd,
      ∀ a ∈ (Finset.Icc 1 Ma).filter (fun a => Nat.Coprime a (2 * b)),
      ‖(μ a : ℂ) * (μ b : ℂ) * φa ((a : ℝ) / A) * φb ((b : ℝ) / B) *
          ∑ h ∈ Finset.Icc 1 M, term N₀ ς ℓ ρ σ ψ a b h‖
        ≤ ‖φb ((b : ℝ) / B)‖ * (‖φa ((a : ℝ) / A)‖ * ((M : ℝ) * (3 / 2 * N₀))) := by
    intro b hb a ha
    have hb1 : 1 ≤ b := (Finset.mem_Icc.1 (Finset.mem_filter.1 hb).1).1
    have ha1 : 1 ≤ a := (Finset.mem_Icc.1 (Finset.mem_filter.1 ha).1).1
    have hsum : ‖∑ h ∈ Finset.Icc 1 M, term N₀ ς ℓ ρ σ ψ a b h‖ ≤ (M : ℝ) * (3 / 2 * N₀) := by
      calc ‖∑ h ∈ Finset.Icc 1 M, term N₀ ς ℓ ρ σ ψ a b h‖
          ≤ ∑ h ∈ Finset.Icc 1 M, ‖term N₀ ς ℓ ρ σ ψ a b h‖ := norm_sum_le _ _
        _ ≤ ∑ h ∈ Finset.Icc 1 M, (3 / 2 * N₀) :=
            Finset.sum_le_sum fun h _ => norm_term_le hN hℓ ha1 hb1 hψ
        _ = (M : ℝ) * (3 / 2 * N₀) := by simp
    have hμa : ‖(μ a : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have hμb : ‖(μ b : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    rw [norm_mul, norm_mul, norm_mul, norm_mul]
    calc ‖(μ a : ℂ)‖ * ‖(μ b : ℂ)‖ * ‖φa ((a : ℝ) / A)‖ * ‖φb ((b : ℝ) / B)‖ *
          ‖∑ h ∈ Finset.Icc 1 M, term N₀ ς ℓ ρ σ ψ a b h‖
        ≤ 1 * 1 * ‖φa ((a : ℝ) / A)‖ * ‖φb ((b : ℝ) / B)‖ * ((M : ℝ) * (3 / 2 * N₀)) := by
          gcongr
      _ = ‖φb ((b : ℝ) / B)‖ * (‖φa ((a : ℝ) / A)‖ * ((M : ℝ) * (3 / 2 * N₀))) := by ring
  calc _ ≤ ∑ b ∈ (Finset.Icc 1 Mb).filter Odd,
          ‖∑ a ∈ (Finset.Icc 1 Ma).filter (fun a => Nat.Coprime a (2 * b)),
            (μ a : ℂ) * (μ b : ℂ) * φa ((a : ℝ) / A) * φb ((b : ℝ) / B) *
              ∑ h ∈ Finset.Icc 1 M, term N₀ ς ℓ ρ σ ψ a b h‖ := norm_sum_le _ _
    _ ≤ ∑ b ∈ (Finset.Icc 1 Mb).filter Odd, ∑ a ∈ (Finset.Icc 1 Ma).filter
          (fun a => Nat.Coprime a (2 * b)),
          ‖φb ((b : ℝ) / B)‖ * (‖φa ((a : ℝ) / A)‖ * ((M : ℝ) * (3 / 2 * N₀))) := by
        apply Finset.sum_le_sum
        intro b hb
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun a ha => hinner b hb a ha)
    _ = ∑ b ∈ (Finset.Icc 1 Mb).filter Odd, ‖φb ((b : ℝ) / B)‖ *
          ((∑ a ∈ (Finset.Icc 1 Ma).filter (fun a => Nat.Coprime a (2 * b)),
            ‖φa ((a : ℝ) / A)‖) * ((M : ℝ) * (3 / 2 * N₀))) := by
        simp only [Finset.mul_sum, Finset.sum_mul]
    _ ≤ ∑ b ∈ (Finset.Icc 1 Mb).filter Odd, ‖φb ((b : ℝ) / B)‖ *
          ((2 * A) * ((M : ℝ) * (3 / 2 * N₀))) := by
        apply Finset.sum_le_sum
        intro b _
        gcongr
        apply sum_phi_le hA _ (tempered_norm_le_one hφa) (fun x hx => tempered_zero hφa hx)
        intro a ha
        exact (Finset.mem_Icc.1 (Finset.mem_filter.1 ha).1).1
    _ = (∑ b ∈ (Finset.Icc 1 Mb).filter Odd, ‖φb ((b : ℝ) / B)‖) *
          ((2 * A) * ((M : ℝ) * (3 / 2 * N₀))) := by rw [Finset.sum_mul]
    _ ≤ (2 * B) * ((2 * A) * ((M : ℝ) * (3 / 2 * N₀))) := by
        gcongr
        apply sum_phi_le hB _ hφb1 hφb0
        intro b hb
        exact (Finset.mem_Icc.1 (Finset.mem_filter.1 hb).1).1
    _ = 6 * A * B * M * N₀ := by ring

/-! ## Exponent bookkeeping (via logarithms) -/

lemma log_four : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num

lemma log_eight : Real.log 8 = 3 * Real.log 2 := by
  rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num

lemma log_sixteen : Real.log 16 = 4 * Real.log 2 := by
  rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num

/-- The hypotheses of `core_block` in the main range. -/
lemma mvt_conditions {N₀ A B M ℓ η ε₀ : ℝ} (hN : (2 : ℝ) ^ 400 ≤ N₀) (hη : 0 < η)
    (hη1 : η ≤ 1 / 100) (hε : 0 < ε₀) (hε1 : ε₀ ≤ 1 / 1000) (hℓ1 : 1 ≤ ℓ) (hℓ2 : ℓ ≤ 2)
    (hB : 1 / 2 ≤ B) (hBA : B ≤ A) (hA : A ≤ N₀ ^ (9 / 17 - η)) (hM1 : 1 ≤ M)
    (hM : M ≤ 4 * ℓ * A * B * N₀ ^ (ε₀ - 1)) :
    2 ≤ A ∧ 1 ≤ B ∧ 2 * M ≤ A ^ ((1 : ℝ) / 6) ∧ A ^ ((2 : ℝ) / 3) * (2 * M) ^ 2 ≤ B ∧
      2 * M ≤ 16 * A * B * N₀ ^ (ε₀ - 1) ∧ M ≤ 8 * N₀ := by
  have hNpos : 0 < N₀ := lt_of_lt_of_le (by positivity) hN
  have hBpos : 0 < B := by linarith
  have hApos : 0 < A := by linarith
  have hMpos : 0 < M := by linarith
  have hℓpos : 0 < ℓ := by linarith
  have hl2 := Real.log_two_gt_d9
  have hx : 400 * Real.log 2 ≤ Real.log N₀ := by
    have := Real.log_le_log (by positivity) hN
    rwa [Real.log_pow] at this
  have ha : Real.log A ≤ (9 / 17 - η) * Real.log N₀ := by
    have := Real.log_le_log hApos hA
    rwa [Real.log_rpow hNpos] at this
  have hba : Real.log B ≤ Real.log A := Real.log_le_log hBpos hBA
  have hlogℓ : Real.log ℓ ≤ Real.log 2 := Real.log_le_log hℓpos hℓ2
  have hm0 : 0 ≤ Real.log M := Real.log_nonneg hM1
  have hm : Real.log M ≤ Real.log 4 + Real.log ℓ + Real.log A + Real.log B +
      (ε₀ - 1) * Real.log N₀ := by
    have := Real.log_le_log hMpos hM
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_rpow hNpos] at this
    exact this
  rw [log_four] at hm
  have hx0 : 0 ≤ Real.log N₀ := by linarith
  have hu0 : 0 ≤ η * Real.log N₀ := by positivity
  have hu1 : η * Real.log N₀ ≤ Real.log N₀ / 100 := by nlinarith
  have hv0 : 0 ≤ ε₀ * Real.log N₀ := by positivity
  have hv1 : ε₀ * Real.log N₀ ≤ Real.log N₀ / 1000 := by nlinarith
  have hlog2M : Real.log (2 * M) = Real.log 2 + Real.log M :=
    Real.log_mul (by norm_num) hMpos.ne'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Real.log_le_log_iff (by norm_num) hApos]
    nlinarith
  · rw [← Real.log_le_log_iff (by norm_num) hBpos, Real.log_one]
    nlinarith
  · rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_rpow hApos, hlog2M]
    nlinarith
  · rw [← Real.log_le_log_iff (by positivity) hBpos, Real.log_mul (by positivity) (by positivity),
      Real.log_rpow hApos, Real.log_pow, hlog2M]
    push_cast
    nlinarith
  · have h4 : 0 < A * B * N₀ ^ (ε₀ - 1) := by positivity
    nlinarith
  · rw [← Real.log_le_log_iff hMpos (by positivity), Real.log_mul (by norm_num) hNpos.ne',
      log_eight]
    nlinarith

/-- The three terms of the mean-value bound, after the prefactor `N₀/(ℓAB) · B^{1/2}`. -/
lemma phi_bound {N₀ A B Hn ℓ η ε₀ : ℝ} (hN : 1 ≤ N₀) (hη : 0 < η) (hε : 0 ≤ ε₀)
    (hℓ : 1 ≤ ℓ) (hApos : 0 < A) (hBpos : 0 < B) (hHn : 0 < Hn) (hBA : B ≤ A)
    (hA : A ≤ N₀ ^ (9 / 17 - η)) (hH : Hn ≤ 16 * A * B * N₀ ^ (ε₀ - 1)) :
    N₀ / (ℓ * A * B) * B ^ ((1 : ℝ) / 2) *
        (A ^ ((11 : ℝ) / 12) * B ^ ((1 : ℝ) / 2) * Hn ^ ((3 : ℝ) / 4)
          + A ^ ((1 : ℝ) / 3) * B * Hn + A * Hn)
      ≤ 40 * N₀ ^ (1 - 17 * η / 12 + ε₀) := by
  have hNpos : 0 < N₀ := by linarith
  have hℓpos : 0 < ℓ := by linarith
  have hx0 : 0 ≤ Real.log N₀ := Real.log_nonneg hN
  have hl2 := Real.log_two_gt_d9
  have ha : Real.log A ≤ (9 / 17 - η) * Real.log N₀ := by
    have := Real.log_le_log hApos hA
    rwa [Real.log_rpow hNpos] at this
  have hba : Real.log B ≤ Real.log A := Real.log_le_log hBpos hBA
  have hlogℓ : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ
  have ht : Real.log Hn ≤ Real.log 16 + Real.log A + Real.log B + (ε₀ - 1) * Real.log N₀ := by
    have := Real.log_le_log hHn hH
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_rpow hNpos] at this
    exact this
  rw [log_sixteen] at ht
  have hu0 : 0 ≤ η * Real.log N₀ := by positivity
  have hv0 : 0 ≤ ε₀ * Real.log N₀ := by positivity
  have hpre : Real.log (N₀ / (ℓ * A * B) * B ^ ((1 : ℝ) / 2)) =
      Real.log N₀ - (Real.log ℓ + Real.log A + Real.log B) + 1 / 2 * Real.log B := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_rpow hBpos]
  set e := 1 - 17 * η / 12 + ε₀ with he
  have hRHS : ∀ c : ℝ, 0 < c → Real.log (c * N₀ ^ e) = Real.log c + e * Real.log N₀ := by
    intro c hc
    rw [Real.log_mul hc.ne' (by positivity), Real.log_rpow hNpos]
  have T1 : N₀ / (ℓ * A * B) * B ^ ((1 : ℝ) / 2) *
      (A ^ ((11 : ℝ) / 12) * B ^ ((1 : ℝ) / 2) * Hn ^ ((3 : ℝ) / 4)) ≤ 8 * N₀ ^ e := by
    rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_mul (by positivity)
      (by positivity), hpre, hRHS 8 (by norm_num), log_eight,
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_rpow hApos, Real.log_rpow hBpos, Real.log_rpow hHn, he]
    nlinarith
  have T2 : N₀ / (ℓ * A * B) * B ^ ((1 : ℝ) / 2) * (A ^ ((1 : ℝ) / 3) * B * Hn)
      ≤ 16 * N₀ ^ e := by
    rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_mul (by positivity)
      (by positivity), hpre, hRHS 16 (by norm_num), log_sixteen,
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_rpow hApos, he]
    nlinarith
  have T3 : N₀ / (ℓ * A * B) * B ^ ((1 : ℝ) / 2) * (A * Hn) ≤ 16 * N₀ ^ e := by
    rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_mul (by positivity)
      (by positivity), hpre, hRHS 16 (by norm_num), log_sixteen,
      Real.log_mul (by positivity) (by positivity), he]
    nlinarith
  calc N₀ / (ℓ * A * B) * B ^ ((1 : ℝ) / 2) *
        (A ^ ((11 : ℝ) / 12) * B ^ ((1 : ℝ) / 2) * Hn ^ ((3 : ℝ) / 4)
          + A ^ ((1 : ℝ) / 3) * B * Hn + A * Hn)
      = N₀ / (ℓ * A * B) * B ^ ((1 : ℝ) / 2) *
          (A ^ ((11 : ℝ) / 12) * B ^ ((1 : ℝ) / 2) * Hn ^ ((3 : ℝ) / 4))
        + N₀ / (ℓ * A * B) * B ^ ((1 : ℝ) / 2) * (A ^ ((1 : ℝ) / 3) * B * Hn)
        + N₀ / (ℓ * A * B) * B ^ ((1 : ℝ) / 2) * (A * Hn) := by ring
    _ ≤ 8 * N₀ ^ e + 16 * N₀ ^ e + 16 * N₀ ^ e := by gcongr
    _ = 40 * N₀ ^ e := by ring

/-- Number of dyadic blocks. -/
lemma log_count {M : ℕ} {N₀ δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hN : 1 ≤ N₀)
    (hM : (M : ℝ) ≤ 8 * N₀) (hM1 : 1 ≤ M) :
    (Nat.log 2 M : ℝ) + 1 ≤ (16 / δ + 1) * N₀ ^ δ := by
  set L := Nat.log 2 M
  have h2L : ((2 : ℝ) ^ L) ≤ M := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : M ≠ 0)
  have hl2 := Real.log_two_gt_d9
  have hlog : (L : ℝ) * Real.log 2 ≤ ((2 : ℝ) ^ L) ^ δ / δ := by
    have := Real.log_le_rpow_div (x := (2 : ℝ) ^ L) (by positivity) hδ
    rwa [Real.log_pow] at this
  have h8 : ((2 : ℝ) ^ L) ^ δ ≤ 8 * N₀ ^ δ := by
    calc ((2 : ℝ) ^ L) ^ δ ≤ (8 * N₀) ^ δ :=
          Real.rpow_le_rpow (by positivity) (h2L.trans hM) hδ.le
      _ = 8 ^ δ * N₀ ^ δ := Real.mul_rpow (by norm_num) (by linarith)
      _ ≤ 8 * N₀ ^ δ := by
          gcongr
          calc (8 : ℝ) ^ δ ≤ 8 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hδ1
            _ = 8 := Real.rpow_one 8
  have hNδ : 1 ≤ N₀ ^ δ := Real.one_le_rpow hN hδ.le
  have hL : (L : ℝ) ≤ 16 / δ * N₀ ^ δ := by
    have h1 : (L : ℝ) * Real.log 2 ≤ 8 * N₀ ^ δ / δ :=
      hlog.trans (div_le_div_of_nonneg_right h8 hδ.le)
    have h2 : (L : ℝ) * (1 / 2) ≤ (L : ℝ) * Real.log 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
    have h3 : 8 * N₀ ^ δ / δ = 8 / δ * N₀ ^ δ := by ring
    have h4 : (16 : ℝ) / δ * N₀ ^ δ = 2 * (8 / δ * N₀ ^ δ) := by ring
    linarith
  nlinarith

/-! ## Dyadic decomposition of the frequencies -/

lemma sum_blocks (Bs : Finset ℕ) (As : ℕ → Finset ℕ) (coef : ℕ → ℕ → ℂ)
    (G : ℕ → ℕ → ℕ → ℂ) (M : ℕ) :
    ∑ b ∈ Bs, ∑ a ∈ As b, coef a b * ∑ h ∈ Finset.Icc 1 M, G a b h =
      ∑ m ∈ Finset.range (Nat.log 2 M + 1), ∑ b ∈ Bs, ∑ a ∈ As b, coef a b *
        ∑ h ∈ (Finset.Icc 1 M).filter (fun h => Nat.log 2 h = m), G a b h := by
  have hfib : ∀ a b, ∑ h ∈ Finset.Icc 1 M, G a b h =
      ∑ m ∈ Finset.range (Nat.log 2 M + 1),
        ∑ h ∈ (Finset.Icc 1 M).filter (fun h => Nat.log 2 h = m), G a b h := by
    intro a b
    refine (Finset.sum_fiberwise_of_maps_to (g := fun h => Nat.log 2 h) ?_ _).symm
    intro h hh
    rw [Finset.mem_range]
    have := Nat.log_mono_right (b := 2) (Finset.mem_Icc.1 hh).2
    omega
  calc ∑ b ∈ Bs, ∑ a ∈ As b, coef a b * ∑ h ∈ Finset.Icc 1 M, G a b h
      = ∑ b ∈ Bs, ∑ a ∈ As b, ∑ m ∈ Finset.range (Nat.log 2 M + 1), coef a b *
          ∑ h ∈ (Finset.Icc 1 M).filter (fun h => Nat.log 2 h = m), G a b h := by
        apply Finset.sum_congr rfl; intro b _; apply Finset.sum_congr rfl; intro a _
        rw [hfib, Finset.mul_sum]
    _ = ∑ b ∈ Bs, ∑ m ∈ Finset.range (Nat.log 2 M + 1), ∑ a ∈ As b, coef a b *
          ∑ h ∈ (Finset.Icc 1 M).filter (fun h => Nat.log 2 h = m), G a b h := by
        apply Finset.sum_congr rfl; intro b _; exact Finset.sum_comm
    _ = _ := Finset.sum_comm

lemma block_eq (Bs : Finset ℕ) (As : ℕ → Finset ℕ) (coef : ℕ → ℕ → ℂ)
    (G : ℕ → ℕ → ℕ → ℂ) (G' : ℕ → ℕ → ℤ → ℂ) (blk : Finset ℕ) (K : ℂ)
    (hG : ∀ b ∈ Bs, ∀ a ∈ As b, coef a b ≠ 0 → ∀ h ∈ blk, G a b h = K * G' a b (h : ℤ)) :
    ∑ b ∈ Bs, ∑ a ∈ As b, coef a b * ∑ h ∈ blk, G a b h =
      K * ∑ b ∈ Bs, ∑ a ∈ As b, coef a b * ∑ h ∈ blk.map Nat.castEmbedding, G' a b h := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro b hb
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a ha
  by_cases hc : coef a b = 0
  · simp [hc]
  rw [Finset.sum_map, Finset.sum_congr rfl (fun h hh => hG b hb a ha hc h hh), ← Finset.mul_sum]
  simp only [Nat.castEmbedding_apply]
  ring

lemma mem_blk {M m h : ℕ} (hh : h ∈ (Finset.Icc 1 M).filter (fun h => Nat.log 2 h = m)) :
    1 ≤ h ∧ h ≤ M ∧ 2 ^ m ≤ h ∧ h < 2 ^ (m + 1) := by
  rw [Finset.mem_filter, Finset.mem_Icc] at hh
  obtain ⟨⟨h1, h2⟩, h3⟩ := hh
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [← h3]; exact Nat.pow_log_le_self 2 (by omega)
  · rw [← h3]; exact Nat.lt_pow_succ_log_self (by norm_num) h

/-- The weight identity on one block. -/
lemma term_eq {N₀ A B ς H cn : ℝ} {ℓ : ℕ} {ρ σ : ℤ} {ψ F : ℝ → ℂ} {a b h : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hH : 0 < H) (hℓ : 1 ≤ ℓ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hh : 1 ≤ h) (hcn : cn ≠ 0)
    (hF : F ((h : ℝ) / H * (A / a) * (B / b)) * cn =
      (((h : ℝ) / H * (A / a) * (B / b) : ℝ) : ℂ) *
        fourierR ψ (ς * H * N₀ / (ℓ * A * B) * ((h : ℝ) / H * (A / a) * (B / b))) *
        Complex.exp (2 * π * Complex.I *
          ((ρ * H / (A * B) * ((h : ℝ) / H * (A / a) * (B / b)) : ℝ) : ℂ))) :
    term N₀ ς ℓ ρ σ ψ a b h =
      ((N₀ / (ℓ * A * B) * cn : ℝ) : ℂ) * (((H / ((h : ℤ) : ℝ) : ℝ) : ℂ) *
        F (((h : ℤ) : ℝ) / H * (A / a) * (B / b)) * kfrac b (σ * (h : ℤ)) a) := by
  simp only [Int.cast_natCast]
  set s : ℝ := (h : ℝ) / H * (A / a) * (B / b) with hs
  have hℓ' : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have r1 : N₀ / (ℓ * A * B) * (H / h) * s = N₀ / (ℓ * a * b) := by
    rw [hs]; field_simp
  have r2 : ς * H * N₀ / (ℓ * A * B) * s = ς * (h * N₀ / (ℓ * a * b)) := by
    rw [hs]; field_simp
  have r3 : ρ * H / (A * B) * s = (ρ : ℝ) * h / (a * b) := by
    rw [hs]; field_simp
  have hcn' : (cn : ℂ) ≠ 0 := by exact_mod_cast hcn
  have hFs : F s = (s : ℂ) * fourierR ψ (ς * H * N₀ / (ℓ * A * B) * s) *
      Complex.exp (2 * π * Complex.I * ((ρ * H / (A * B) * s : ℝ) : ℂ)) / cn := by
    rw [eq_div_iff hcn']; exact hF
  have e1 : ((N₀ / (ℓ * a * b) : ℝ) : ℂ) =
      ((N₀ / (ℓ * A * B) : ℝ) : ℂ) * ((H / h : ℝ) : ℂ) * (s : ℂ) := by
    rw [← r1]; push_cast; ring
  have e3 : Complex.exp (2 * π * Complex.I * ((ρ * h : ℤ) : ℂ) / ((a * b : ℕ) : ℂ)) =
      Complex.exp (2 * π * Complex.I * ((ρ * H / (A * B) * s : ℝ) : ℂ)) := by
    rw [r3]; congr 1; push_cast; ring
  unfold term
  rw [e1, ← r2, e3, hFs, Complex.ofReal_mul]
  field_simp
  push_cast
  ring

end Finite

set_option maxHeartbeats 1000000 in
open MobiusDeterminant.Level.Finite in
theorem finite_part_bound (hMV : MeanValueThm) (hM : MellinSeparation) :
    ∀ η : ℝ, 0 < η → η ≤ 1 / 100 → ∃ kV : ℕ, ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
    ∃ C > (0 : ℝ),
    ∀ (N₀ A B P ς : ℝ) (ℓ : ℕ) (ρ σ : ℤ) (M Ma Mb : ℕ) (ψ φa φb : ℝ → ℂ),
      2 ≤ N₀ → 1 / 2 ≤ B → B ≤ A → A ≤ N₀ ^ (9 / 17 - η) → (ℓ = 1 ∨ ℓ = 2) →
      (ς = 1 ∨ ς = -1) → |ρ| ≤ 2 → σ ≠ 0 → |σ| ≤ 2 →
      (M : ℝ) ≤ 4 * ℓ * A * B * N₀ ^ (ε₀ - 1) → ⌊2 * A⌋₊ ≤ Ma →
      1 ≤ P → TemperedOn ψ P 0 (1/2) 2 → TemperedOn φa P kV (1/2) 2 →
      (∀ x, ‖φb x‖ ≤ 1) → (∀ x, x ∉ Set.Icc (1/2 : ℝ) 2 → φb x = 0) →
      ‖∑ b ∈ (Finset.Icc 1 Mb).filter Odd,
          ∑ a ∈ (Finset.Icc 1 Ma).filter (fun a => Nat.Coprime a (2 * b)),
            (μ a : ℂ) * (μ b : ℂ) * φa ((a : ℝ) / A) * φb ((b : ℝ) / B) *
              ∑ h ∈ Finset.Icc 1 M,
                ((N₀ / (ℓ * a * b) : ℝ) : ℂ) * fourierR ψ (ς * (h * N₀ / (ℓ * a * b))) *
                  Complex.exp (2 * π * Complex.I * ((ρ * h : ℤ) : ℂ) / ((a * b : ℕ) : ℂ)) *
                  kfrac b (σ * h) a‖
        ≤ C * P ^ kV * N₀ ^ (1 - η) := by
  intro η hη hη1
  obtain ⟨kV, kF, Cc, hCc, hcore⟩ := core_block hMV hM (η / 12) (by positivity)
  obtain ⟨c, hc1, cn, hcn, hblock⟩ := blockF_tempered kF
  have hkF : (0 : ℝ) ≤ kF := Nat.cast_nonneg kF
  set ε₀ : ℝ := η / (12 * ((kF : ℝ) + 2)) with hε₀def
  have hε₀ : 0 < ε₀ := by positivity
  have hε₀1 : ε₀ ≤ 1 / 1000 := by
    rw [hε₀def, div_le_iff₀ (by positivity)]; nlinarith
  have hε₀k : ε₀ * kF + ε₀ ≤ η / 12 := by
    have e : ε₀ * kF + ε₀ = η / 12 * (((kF : ℝ) + 1) / ((kF : ℝ) + 2)) := by
      rw [hε₀def]; field_simp
    rw [e]
    have : ((kF : ℝ) + 1) / ((kF : ℝ) + 2) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    nlinarith
  set Kmain : ℝ := cn * Cc * (21 * c) ^ kF * 40 * (16 / (η / 12) + 1) with hKmain_def
  set Ktriv : ℝ := 48 * ((2 : ℝ) ^ 400) ^ 5 with hKtriv_def
  have hKmain : 0 ≤ Kmain := by rw [hKmain_def]; positivity
  have hKtriv : 0 < Ktriv := by rw [hKtriv_def]; positivity
  refine ⟨kV, ε₀, hε₀, hε₀1, Kmain + Ktriv, add_pos_of_nonneg_of_pos hKmain hKtriv, ?_⟩
  intro N₀ A B P ς ℓ ρ σ M Ma Mb ψ φa φb hN hB hBA hA hℓ hς hρ hσ0 hσ2 hMle hMa hP hψ hφa
    hφb1 hφb0
  change ‖∑ b ∈ (Finset.Icc 1 Mb).filter Odd,
          ∑ a ∈ (Finset.Icc 1 Ma).filter (fun a => Nat.Coprime a (2 * b)),
            (μ a : ℂ) * (μ b : ℂ) * φa ((a : ℝ) / A) * φb ((b : ℝ) / B) *
              ∑ h ∈ Finset.Icc 1 M, term N₀ ς ℓ ρ σ ψ a b h‖ ≤ _
  have hNpos : 0 < N₀ := by linarith
  have hN1 : 1 ≤ N₀ := by linarith
  have hBpos : 0 < B := by linarith
  have hApos : 0 < A := by linarith
  have hℓn : 1 ≤ ℓ := by rcases hℓ with h | h <;> omega
  have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓn
  have hℓ2 : (ℓ : ℝ) ≤ 2 := by
    have : ℓ ≤ 2 := by rcases hℓ with h | h <;> omega
    exact_mod_cast this
  have hPk : 1 ≤ P ^ kV := one_le_pow₀ hP
  have hNe : 1 ≤ N₀ ^ (1 - η) := Real.one_le_rpow hN1 (by linarith)
  have hAN : A ≤ N₀ := by
    refine hA.trans ?_
    calc N₀ ^ (9 / 17 - η) ≤ N₀ ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ = N₀ := Real.rpow_one N₀
  have hNε : N₀ ^ (ε₀ - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hNε0 : 0 < N₀ ^ (ε₀ - 1) := by positivity
  have hMAB : (M : ℝ) ≤ 8 * A * B := by
    have h1 : ℓ * N₀ ^ (ε₀ - 1) ≤ 2 := by
      calc (ℓ : ℝ) * N₀ ^ (ε₀ - 1) ≤ 2 * 1 := mul_le_mul hℓ2 hNε hNε0.le (by norm_num)
        _ = 2 := by norm_num
    calc (M : ℝ) ≤ 4 * ℓ * A * B * N₀ ^ (ε₀ - 1) := hMle
      _ = 4 * (ℓ * N₀ ^ (ε₀ - 1)) * (A * B) := by ring
      _ ≤ 4 * 2 * (A * B) := by gcongr
      _ = 8 * A * B := by ring
  by_cases hmain : 1 ≤ M ∧ (2 : ℝ) ^ 400 ≤ N₀
  swap
  · have htriv := trivial_bound (kV := kV) (ς := ς) (ρ := ρ) (σ := σ) (M := M) (Ma := Ma)
      (Mb := Mb) hNpos.le hApos hBpos hℓn hψ hφa hφb1 hφb0
    refine htriv.trans ?_
    have hfin : 0 ≤ (Kmain + Ktriv) * P ^ kV * N₀ ^ (1 - η) := by positivity
    rcases not_and_or.1 hmain with hM0 | hNs
    · have : M = 0 := by omega
      subst this
      simpa using hfin
    · push Not at hNs
      calc 6 * A * B * M * N₀ ≤ 6 * A * B * (8 * A * B) * N₀ := by gcongr
        _ = 48 * (A * B) ^ 2 * N₀ := by ring
        _ ≤ 48 * (N₀ * N₀) ^ 2 * N₀ := by gcongr; linarith
        _ = 48 * N₀ ^ 5 := by ring
        _ ≤ 48 * ((2 : ℝ) ^ 400) ^ 5 := by gcongr
        _ = Ktriv := rfl
        _ ≤ (Kmain + Ktriv) * 1 * 1 := by
          rw [mul_one, mul_one]; exact le_add_of_nonneg_left hKmain
        _ ≤ (Kmain + Ktriv) * P ^ kV * N₀ ^ (1 - η) := by gcongr
  obtain ⟨hM1, hNbig⟩ := hmain
  have hM1r : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  obtain ⟨hA2, hB1, hHn6, hHn23, hHn16, hM8⟩ :=
    mvt_conditions hNbig hη hη1 hε₀ hε₀1 hℓ1 hℓ2 hB hBA hA hM1r hMle
  have hdec := sum_blocks ((Finset.Icc 1 Mb).filter Odd)
    (fun b => (Finset.Icc 1 Ma).filter (fun a => Nat.Coprime a (2 * b)))
    (fun a b => (μ a : ℂ) * (μ b : ℂ) * φa ((a : ℝ) / A) * φb ((b : ℝ) / B))
    (fun a b h => term N₀ ς ℓ ρ σ ψ a b h) M
  beta_reduce at hdec
  rw [hdec]
  set L := Nat.log 2 M with hL
  set Bblk : ℝ := cn * Cc * P ^ kV * ((21 * c) ^ kF * N₀ ^ (ε₀ * kF)) * N₀ ^ (η / 12) *
    (40 * N₀ ^ (1 - 17 * η / 12 + ε₀)) with hBblk
  have hBblk0 : 0 ≤ Bblk := by rw [hBblk]; positivity
  have hblockbound : ∀ m ∈ Finset.range (L + 1),
      ‖∑ b ∈ (Finset.Icc 1 Mb).filter Odd,
          ∑ a ∈ (Finset.Icc 1 Ma).filter (fun a => Nat.Coprime a (2 * b)),
            (μ a : ℂ) * (μ b : ℂ) * φa ((a : ℝ) / A) * φb ((b : ℝ) / B) *
              ∑ h ∈ (Finset.Icc 1 M).filter (fun h => Nat.log 2 h = m),
                term N₀ ς ℓ ρ σ ψ a b h‖ ≤ Bblk := by
    intro m hm
    have hmL : m ≤ L := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
    set H : ℝ := (2 : ℝ) ^ m with hHdef
    have hHpos : 0 < H := by positivity
    have hHM : H ≤ M := by
      have : 2 ^ m ≤ M :=
        (Nat.pow_le_pow_right (by norm_num) hmL).trans (Nat.pow_log_le_self 2 (by omega))
      rw [hHdef]; exact_mod_cast this
    obtain ⟨F, hFt, hFid⟩ := hblock ψ P (ς * H * N₀ / (ℓ * A * B)) (ρ * H / (A * B)) hψ
    set blk := (Finset.Icc 1 M).filter (fun h => Nat.log 2 h = m) with hblk
    set K : ℂ := ((N₀ / (ℓ * A * B) * cn : ℝ) : ℂ) with hK
    have hbe := block_eq ((Finset.Icc 1 Mb).filter Odd)
      (fun b => (Finset.Icc 1 Ma).filter (fun a => Nat.Coprime a (2 * b)))
      (fun a b => (μ a : ℂ) * (μ b : ℂ) * φa ((a : ℝ) / A) * φb ((b : ℝ) / B))
      (fun a b h => term N₀ ς ℓ ρ σ ψ a b h)
      (fun a b (h : ℤ) => ((H / h : ℝ) : ℂ) * F ((h : ℝ) / H * (A / a) * (B / b)) *
        kfrac b (σ * h) a) blk K (by
        intro b hb a ha hc h hh
        obtain ⟨h1, _, h2m, h2m1⟩ := mem_blk hh
        have hb1 : 1 ≤ b := (Finset.mem_Icc.1 (Finset.mem_filter.1 hb).1).1
        have ha1 : 1 ≤ a := (Finset.mem_Icc.1 (Finset.mem_filter.1 ha).1).1
        have hφa0 : φa ((a : ℝ) / A) ≠ 0 := fun h0 => hc (by rw [h0]; ring)
        have hφb0' : φb ((b : ℝ) / B) ≠ 0 := fun h0 => hc (by rw [h0]; ring)
        have haA : (a : ℝ) / A ∈ Set.Icc (1 / 2 : ℝ) 2 := by
          by_contra hn; exact hφa0 (tempered_zero hφa hn)
        have hbB : (b : ℝ) / B ∈ Set.Icc (1 / 2 : ℝ) 2 := by
          by_contra hn; exact hφb0' (hφb0 _ hn)
        have ha' : (0 : ℝ) < a := by exact_mod_cast ha1
        have hb' : (0 : ℝ) < b := by exact_mod_cast hb1
        have u1 : 1 ≤ (h : ℝ) / H := by
          rw [le_div_iff₀ hHpos, one_mul, hHdef]; exact_mod_cast h2m
        have u2 : (h : ℝ) / H ≤ 2 := by
          rw [div_le_iff₀ hHpos, hHdef]
          have : (h : ℝ) < (2 : ℝ) ^ (m + 1) := by exact_mod_cast h2m1
          rw [pow_succ] at this; linarith
        have v1 : 1 / 2 ≤ A / a := by
          have := haA.2; rw [div_le_iff₀ hApos] at this
          rw [le_div_iff₀ ha']; linarith
        have v2 : A / a ≤ 2 := by
          have := haA.1; rw [le_div_iff₀ hApos] at this
          rw [div_le_iff₀ ha']; linarith
        have w1 : 1 / 2 ≤ B / b := by
          have := hbB.2; rw [div_le_iff₀ hBpos] at this
          rw [le_div_iff₀ hb']; linarith
        have w2 : B / b ≤ 2 := by
          have := hbB.1; rw [le_div_iff₀ hBpos] at this
          rw [div_le_iff₀ hb']; linarith
        have hs : (h : ℝ) / H * (A / a) * (B / b) ∈ Set.Icc (1 / 4 : ℝ) 8 := by
          constructor
          · calc (1 / 4 : ℝ) = 1 * (1 / 2) * (1 / 2) := by norm_num
              _ ≤ (h : ℝ) / H * (A / a) * (B / b) := by gcongr
          · calc (h : ℝ) / H * (A / a) * (B / b) ≤ 2 * 2 * 2 := by gcongr
              _ = 8 := by norm_num
        exact term_eq hApos hBpos hHpos hℓn ha1 hb1 h1 hcn.ne' (hFid _ hs))
    beta_reduce at hbe
    rw [hbe]
    -- the core estimate
    set Y₁ : ℝ := ς * H * N₀ / (ℓ * A * B) with hY₁
    set Y₂ : ℝ := ρ * H / (A * B) with hY₂
    set PF : ℝ := c * (1 + |Y₁| + |Y₂|) with hPF
    have hPF1 : 1 ≤ PF := by
      rw [hPF]
      exact one_le_mul_of_one_le_of_one_le hc1 (by linarith [abs_nonneg Y₁, abs_nonneg Y₂])
    have h𝓗 : ∀ h ∈ blk.map (Nat.castEmbedding : ℕ ↪ ℤ),
        H ≤ (h : ℝ) ∧ (h : ℝ) < 2 * H ∧ |σ * h| ≤ ((2 * M : ℕ) : ℤ) := by
      intro h hh
      rw [Finset.mem_map] at hh
      obtain ⟨n, hn, rfl⟩ := hh
      obtain ⟨_, nM, n2m, n2m1⟩ := mem_blk hn
      simp only [Nat.castEmbedding_apply, Int.cast_natCast]
      refine ⟨?_, ?_, ?_⟩
      · rw [hHdef]; exact_mod_cast n2m
      · have : (n : ℝ) < (2 : ℝ) ^ (m + 1) := by exact_mod_cast n2m1
        rw [pow_succ] at this; rw [hHdef]; linarith
      · have hnM : (n : ℤ) ≤ M := by exact_mod_cast nM
        calc |σ * (n : ℤ)| = |σ| * n := by rw [abs_mul, Nat.abs_cast]
          _ ≤ 2 * M := by gcongr
          _ = ((2 * M : ℕ) : ℤ) := by push_cast; ring
    have hcast : ((2 * M : ℕ) : ℝ) = 2 * (M : ℝ) := by push_cast; ring
    have hcoreb := hcore A B (2 * M) H σ (blk.map Nat.castEmbedding) Ma Mb φa φb F P PF
      hA2 hB1 hBA (by omega) (by rw [hcast]; exact hHn6) (by rw [hcast]; exact hHn23) hHpos
      hσ0 h𝓗 hMa hP hφa hφb1 hφb0 hPF1 hFt
    rw [hcast] at hcoreb
    -- bounds on the parameters
    have hY1 : |Y₁| ≤ 4 * N₀ ^ ε₀ := by
      have hς1 : |ς| = 1 := by rcases hς with h | h <;> simp [h]
      have hden : 0 < (ℓ : ℝ) * A * B := by positivity
      rw [hY₁, abs_div, abs_mul, abs_mul, hς1, abs_of_pos hHpos, abs_of_pos hNpos,
        abs_of_pos hden, div_le_iff₀ hden]
      calc 1 * H * N₀ ≤ (4 * ℓ * A * B * N₀ ^ (ε₀ - 1)) * N₀ := by
            rw [one_mul]; exact mul_le_mul_of_nonneg_right (hHM.trans hMle) hNpos.le
        _ = 4 * N₀ ^ ε₀ * (ℓ * A * B) := by
          rw [Real.rpow_sub_one hNpos.ne']; field_simp
    have hY2 : |Y₂| ≤ 16 := by
      have hden : 0 < A * B := by positivity
      have hρ' : |(ρ : ℝ)| ≤ 2 := by
        rw [← Int.cast_abs]; exact_mod_cast hρ
      rw [hY₂, abs_div, abs_mul, abs_of_pos hHpos, abs_of_pos hden, div_le_iff₀ hden]
      have h1 : ℓ * N₀ ^ (ε₀ - 1) ≤ 2 := by
        calc (ℓ : ℝ) * N₀ ^ (ε₀ - 1) ≤ 2 * 1 := mul_le_mul hℓ2 hNε hNε0.le (by norm_num)
          _ = 2 := by norm_num
      calc |(ρ : ℝ)| * H ≤ 2 * M := by gcongr
        _ ≤ 2 * (4 * ℓ * A * B * N₀ ^ (ε₀ - 1)) := by linarith
        _ = 8 * (ℓ * N₀ ^ (ε₀ - 1)) * (A * B) := by ring
        _ ≤ 8 * 2 * (A * B) := by gcongr
        _ = 16 * (A * B) := by ring
    have hNε1 : 1 ≤ N₀ ^ ε₀ := Real.one_le_rpow hN1 hε₀.le
    have hPFb : PF ≤ 21 * c * N₀ ^ ε₀ := by
      rw [hPF]
      calc c * (1 + |Y₁| + |Y₂|) ≤ c * (N₀ ^ ε₀ + 4 * N₀ ^ ε₀ + 16 * N₀ ^ ε₀) := by
            gcongr; linarith
        _ = 21 * c * N₀ ^ ε₀ := by ring
    have hPFk : PF ^ kF ≤ (21 * c) ^ kF * N₀ ^ (ε₀ * kF) := by
      calc PF ^ kF ≤ (21 * c * N₀ ^ ε₀) ^ kF := pow_le_pow_left₀ (by linarith) hPFb kF
        _ = (21 * c) ^ kF * N₀ ^ (ε₀ * kF) := by
          rw [mul_pow, Real.rpow_mul_natCast hNpos.le]
    have hAε : A ^ (η / 12) ≤ N₀ ^ (η / 12) :=
      Real.rpow_le_rpow hApos.le hAN (by positivity)
    have hphi := phi_bound (Hn := 2 * (M : ℝ)) hN1 hη hε₀.le hℓ1 hApos hBpos (by positivity)
      hBA hA hHn16
    have hKn : ‖K‖ = N₀ / (ℓ * A * B) * cn := by
      rw [hK, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [norm_mul, hKn]
    calc N₀ / (ℓ * A * B) * cn * ‖_‖
        ≤ N₀ / (ℓ * A * B) * cn * (Cc * P ^ kV * PF ^ kF * B ^ ((1 : ℝ) / 2) * A ^ (η / 12) *
            (A ^ ((11 : ℝ) / 12) * B ^ ((1 : ℝ) / 2) * (2 * (M : ℝ)) ^ ((3 : ℝ) / 4)
              + A ^ ((1 : ℝ) / 3) * B * (2 * (M : ℝ)) + A * (2 * (M : ℝ)))) := by
          gcongr
      _ = cn * Cc * P ^ kV * PF ^ kF * A ^ (η / 12) *
            (N₀ / (ℓ * A * B) * B ^ ((1 : ℝ) / 2) *
              (A ^ ((11 : ℝ) / 12) * B ^ ((1 : ℝ) / 2) * (2 * (M : ℝ)) ^ ((3 : ℝ) / 4)
                + A ^ ((1 : ℝ) / 3) * B * (2 * (M : ℝ)) + A * (2 * (M : ℝ)))) := by ring
      _ ≤ cn * Cc * P ^ kV * ((21 * c) ^ kF * N₀ ^ (ε₀ * kF)) * N₀ ^ (η / 12) *
            (40 * N₀ ^ (1 - 17 * η / 12 + ε₀)) := by gcongr
      _ = Bblk := by rw [hBblk]
  have hcount := log_count (M := M) (N₀ := N₀) (δ := η / 12) (by positivity) (by linarith) hN1
    hM8 hM1
  have hexp : N₀ ^ (η / 12) * (N₀ ^ (ε₀ * kF) * N₀ ^ (η / 12) * N₀ ^ (1 - 17 * η / 12 + ε₀))
      ≤ N₀ ^ (1 - η) := by
    rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
    apply Real.rpow_le_rpow_of_exponent_le hN1
    linarith
  calc _ ≤ ∑ m ∈ Finset.range (L + 1),
        ‖∑ b ∈ (Finset.Icc 1 Mb).filter Odd,
          ∑ a ∈ (Finset.Icc 1 Ma).filter (fun a => Nat.Coprime a (2 * b)),
            (μ a : ℂ) * (μ b : ℂ) * φa ((a : ℝ) / A) * φb ((b : ℝ) / B) *
              ∑ h ∈ (Finset.Icc 1 M).filter (fun h => Nat.log 2 h = m),
                term N₀ ς ℓ ρ σ ψ a b h‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ Finset.range (L + 1), Bblk := Finset.sum_le_sum hblockbound
    _ = ((L : ℝ) + 1) * Bblk := by simp
    _ ≤ ((16 / (η / 12) + 1) * N₀ ^ (η / 12)) * Bblk := by gcongr
    _ = Kmain * P ^ kV *
          (N₀ ^ (η / 12) * (N₀ ^ (ε₀ * kF) * N₀ ^ (η / 12) * N₀ ^ (1 - 17 * η / 12 + ε₀))) := by
        rw [hBblk, hKmain_def]; ring
    _ ≤ Kmain * P ^ kV * N₀ ^ (1 - η) := by gcongr
    _ ≤ (Kmain + Ktriv) * P ^ kV * N₀ ^ (1 - η) := by
        gcongr; exact le_add_of_nonneg_right hKtriv.le

end Level

end MobiusDeterminant
