import MobiusDeterminant.Determinant.Defs
import MobiusDeterminant.Determinant.TensorFinite
import MobiusDeterminant.Unconditional.Main

/-!
# The error term for product weights (`DetTensorBound`)

`detTensorBound : DetTensorBound`.  With `D_max = max(D,E)`, `D_min = min(D,E)`, `T = DE/N₀`,
under the hypotheses of the mean-value theorem with room `N₀^ε`,

  `Δ ≪ P^k (N₀^{1+ε} (D_max^{-1/12} T^{3/4} + D_max^{-2/3} D_min^{1/2} T + D_min^{-1/2} T)
          + N₀^{1/2})`.

Proof (as for `Level.Smooth.T_bound`, paper §8 with the asymmetric mean-value theorem):

* odd `n`: for odd `d, e`, `oddBracket(d,e) = bracket(d,e) - bracket(2d,e)` (`oddBracket_eq`),
  so `Δ = U₀₀ - U₁₀` (`oddDelta_split`), where `U_{ij}` runs over odd `e` and `d` coprime to
  `2e` (non-coprime pairs have vanishing brackets) with brackets at `(2^i d, 2^j e)`;
* each `U_{ij}`: Poisson summation per pair (`bracket_poisson` with the CRT data of
  `pair_class`), truncated at `M = ⌊4ℓDE N₀^{ε₀-1}⌋`; the tail is `O(P^k)`; the finite part is
  bounded by `finite_part_bound'` in the orientation `E ≤ D` directly, or for `D < E` after
  reciprocity (`kfrac_reciprocity`, `sum_odd_coprime_comm`).
-/

open Finset Real
open scoped ArithmeticFunction.Moebius

namespace MobiusDeterminant

namespace Determinant

namespace Tensor

open MobiusDeterminant.Level MobiusDeterminant.Level.Smooth

/-- One parity class of the odd sum at effective scales `D, E`: odd `e`, `d` coprime to `2e`,
brackets at `(2^i d, 2^j e)`. -/
noncomputable def Uij (N₀ D E : ℝ) (ψ φ₁ φ₂ : ℝ → ℂ) (i j : ℕ) : ℂ :=
  ∑ e ∈ (Finset.Icc 1 ⌊2 * E⌋₊).filter Odd,
    ∑ d ∈ (Finset.Icc 1 ⌊2 * D⌋₊).filter (fun a => Nat.Coprime a (2 * e)),
      (μ d : ℂ) * (μ e : ℂ) * φ₁ ((d : ℝ) / D) * φ₂ ((e : ℝ) / E) *
        bracket N₀ ψ (2 ^ i * d) (2 ^ j * e)

/-! ## Odd `n` -/

lemma two_mul_dvd_iff {n d : ℕ} (hd : Odd d) : 2 * d ∣ n ↔ 2 ∣ n ∧ d ∣ n :=
  ⟨fun h => ⟨(Dvd.intro _ rfl).trans h, (Dvd.intro_left _ rfl).trans h⟩,
   fun h => Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.coprime_two_left.mpr hd) h.1 h.2⟩

lemma dens_two_mul {d e : ℕ} (hd : 0 < d) (he : Odd e) : dens (2 * d) e = dens d e / 2 := by
  have hg : Nat.gcd (2 * d) e = Nat.gcd d e :=
    Nat.Coprime.gcd_mul_left_cancel d (Nat.coprime_two_left.mpr he)
  have hl : Nat.lcm (2 * d) e = 2 * Nat.lcm d e := by
    have h1 := Nat.gcd_mul_lcm (2 * d) e
    have h2 := Nat.gcd_mul_lcm d e
    have hpos : 0 < Nat.gcd d e := Nat.gcd_pos_of_pos_left _ hd
    rw [hg] at h1
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [h1, mul_left_comm, h2, mul_assoc]
  unfold dens
  rw [hg, hl]
  split_ifs
  · push_cast
    field_simp
  · simp

/-- For odd `d, e`: `oddBracket(d,e) = bracket(d,e) - bracket(2d,e)`. -/
lemma oddBracket_eq (N₀ : ℝ) (ψ : ℝ → ℂ) {d e : ℕ} (hd : Odd d) (he : Odd e) :
    oddBracket N₀ ψ d e = bracket N₀ ψ d e - bracket N₀ ψ (2 * d) e := by
  have hsum : ∑ n ∈ (Finset.Icc 1 ⌊2 * N₀⌋₊).filter (fun n => d ∣ n ∧ e ∣ n + 2),
        ψ ((n : ℝ) / N₀) =
      ∑ n ∈ (Finset.Icc 1 ⌊2 * N₀⌋₊).filter (fun n => Odd n ∧ d ∣ n ∧ e ∣ n + 2),
        ψ ((n : ℝ) / N₀) +
      ∑ n ∈ (Finset.Icc 1 ⌊2 * N₀⌋₊).filter (fun n => 2 * d ∣ n ∧ e ∣ n + 2),
        ψ ((n : ℝ) / N₀) := by
    simp only [Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rcases Nat.even_or_odd n with hn | hn
    · have hn' : ¬ Odd n := Nat.not_odd_iff_even.mpr hn
      have h2 : 2 ∣ n := hn.two_dvd
      simp [hn', two_mul_dvd_iff hd, h2]
    · have h2 : ¬ 2 ∣ n := by
        rw [← even_iff_two_dvd, Nat.not_even_iff_odd]; exact hn
      simp [hn, two_mul_dvd_iff hd, h2]
  unfold oddBracket bracket
  rw [hsum, dens_two_mul hd.pos he]
  push_cast
  ring

/-- `Δ = U₀₀ - U₁₀`. -/
lemma oddDelta_split (N₀ D E : ℝ) (ψ φ₁ φ₂ : ℝ → ℂ) :
    oddDelta N₀ D E ψ φ₁ φ₂ = Uij N₀ D E ψ φ₁ φ₂ 0 0 - Uij N₀ D E ψ φ₁ φ₂ 1 0 := by
  have hU : ∀ i : ℕ, Uij N₀ D E ψ φ₁ φ₂ i 0 =
      ∑ d ∈ (Finset.Icc 1 ⌊2 * D⌋₊).filter Odd, ∑ e ∈ (Finset.Icc 1 ⌊2 * E⌋₊).filter Odd,
        (μ d : ℂ) * (μ e : ℂ) * φ₁ ((d : ℝ) / D) * φ₂ ((e : ℝ) / E) *
          bracket N₀ ψ (2 ^ i * d) (2 ^ 0 * e) := by
    intro i
    rw [reorder]
    · rfl
    · intro d e hd _ hc
      rw [bracket_noncop N₀ ψ i 0 hd hc, mul_zero]
  rw [hU 0, hU 1, ← Finset.sum_sub_distrib]
  unfold oddDelta
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [oddBracket_eq N₀ ψ (Finset.mem_filter.mp hd).2 (Finset.mem_filter.mp he).2]
  simp only [pow_zero, pow_one, one_mul]
  ring

/-! ## One parity class -/

/-- Bound for one parity class `U_{ij}` in the range of the mean-value theorem. -/
theorem U_bound (hMV : MeanValueThm) (hM : MellinSeparation) (hP : PoissonAPDecay)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) : ∃ k : ℕ, ∃ C > (0 : ℝ),
    ∀ (N₀ D E P : ℝ) (ψ φ₁ φ₂ : ℝ → ℂ), 2 ≤ N₀ → 1 ≤ D → 1 ≤ E → D ≤ N₀ → E ≤ N₀ →
      N₀ ^ ε * (D * E / N₀) ≤ (max D E) ^ ((1 : ℝ) / 6) →
      (max D E) ^ ((2 : ℝ) / 3) * (N₀ ^ ε * (D * E / N₀)) ^ 2 ≤ min D E →
      1 ≤ P → TemperedOn ψ P k (1/2) 2 → TemperedOn φ₁ P k (1/2) 2 →
      TemperedOn φ₂ P k (1/2) 2 →
      ∀ i j : ℕ, i ≤ 1 → j ≤ 1 →
        ‖Uij N₀ D E ψ φ₁ φ₂ i j‖ ≤ C * P ^ k *
          (N₀ ^ (1 + ε) * R3 N₀ (max D E) (min D E) + N₀ ^ ((1 : ℝ) / 2)) := by
  obtain ⟨kV, ε₀, hε₀, hε₀', CF, hCF, hF⟩ := finite_part_bound' hMV hM ε hε hε1
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
  intro N₀ D E P ψ φ₁ φ₂ hN₀ hD hE hDN hEN hH1 hH2 hP1 hψ hφ₁ hφ₂ i j hi hj
  unfold Uij
  have hN0pos : (0 : ℝ) < N₀ := by linarith
  have hN0one : (1 : ℝ) ≤ N₀ := by linarith
  have hkV : kV ≤ max kV kψ := le_max_left _ _
  have hkψ' : kψ ≤ max kV kψ := le_max_right _ _
  have hψ0 : TemperedOn ψ P 0 (1/2) 2 := temperedOn_mono_k hψ (Nat.zero_le _)
  have hψk : TemperedOn ψ P kψ (1/2) 2 := temperedOn_mono_k hψ hkψ'
  have hφ₁V : TemperedOn φ₁ P kV (1/2) 2 := temperedOn_mono_k hφ₁ hkV
  have hφ₂V : TemperedOn φ₂ P kV (1/2) 2 := temperedOn_mono_k hφ₂ hkV
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
  have hDpos : 0 < D := by linarith
  have hEpos : 0 < E := by linarith
  set MD : ℕ := ⌊2 * D⌋₊ with hMD
  set ME : ℕ := ⌊2 * E⌋₊ with hME
  have hMDR : (MD : ℝ) ≤ 2 * D := Nat.floor_le (by linarith)
  have hMER : (ME : ℝ) ≤ 2 * E := Nat.floor_le (by linarith)
  set M : ℕ := ⌊4 * (ℓ : ℝ) * D * E * N₀ ^ (ε₀ - 1)⌋₊ with hMdef
  have hMle : (M : ℝ) ≤ 4 * ℓ * D * E * N₀ ^ (ε₀ - 1) := Nat.floor_le (by positivity)
  have hMlt : 4 * (ℓ : ℝ) * D * E * N₀ ^ (ε₀ - 1) < (M : ℝ) + 1 := Nat.lt_floor_add_one _
  set X : ℝ := N₀ ^ (1 + ε) * R3 N₀ (max D E) (min D E) with hX
  have hX0 : 0 ≤ X := by
    have := R3_nonneg (A := max D E) hN0pos (lt_max_of_lt_left hDpos) (lt_min hDpos hEpos)
    positivity
  -- the finite parts
  set Fs : ℝ → ℤ → ℕ → ℕ → ℂ := fun ς σ d e => ∑ h ∈ Finset.Icc 1 M,
      ((N₀ / (ℓ * d * e) : ℝ) : ℂ) * fourierR ψ (ς * (h * N₀ / (ℓ * d * e))) *
        kfrac e (σ * h) d with hFs
  have hS : ∀ (ς : ℝ) (σ : ℤ), (ς = 1 ∨ ς = -1) → σ ≠ 0 → |σ| ≤ 2 →
      ‖∑ e ∈ (Finset.Icc 1 ME).filter Odd,
          ∑ d ∈ (Finset.Icc 1 MD).filter (fun a => Nat.Coprime a (2 * e)),
            (μ d : ℂ) * (μ e : ℂ) * φ₁ ((d : ℝ) / D) * φ₂ ((e : ℝ) / E) * Fs ς σ d e‖
        ≤ CF * P ^ kV * X := by
    intro ς σ hς hσ0 hσ2
    by_cases hor : E ≤ D
    · have hmax : max D E = D := max_eq_left hor
      have hmin : min D E = E := min_eq_right hor
      rw [hmax] at hH1
      rw [hmax, hmin] at hH2
      rw [hX, hmax, hmin]
      have := hF N₀ D E P ς ℓ 0 σ M MD ME ψ φ₁ φ₂ hN₀ hE hor hDN hH1 hH2 hℓ hς
        (by norm_num) hσ0 hσ2 hMle le_rfl hP1 hψ0 hφ₁V (norm_le_one_of_tempered hφ₂) hφ₂.2.1
      refine le_trans (le_of_eq ?_) this
      congr 1
      refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun d _ => ?_
      congr 1
      refine Finset.sum_congr rfl fun h _ => ?_
      simp only [zero_mul, Int.cast_zero, mul_zero, zero_div, Complex.exp_zero, mul_one]
    · rw [not_le] at hor
      have hmax : max D E = E := max_eq_right hor.le
      have hmin : min D E = D := min_eq_left hor.le
      rw [hmax, mul_comm D E] at hH1
      rw [hmax, hmin, mul_comm D E] at hH2
      rw [hX, hmax, hmin]
      have hMle' : (M : ℝ) ≤ 4 * ℓ * E * D * N₀ ^ (ε₀ - 1) := by
        calc (M : ℝ) ≤ 4 * ℓ * D * E * N₀ ^ (ε₀ - 1) := hMle
          _ = 4 * ℓ * E * D * N₀ ^ (ε₀ - 1) := by ring
      have := hF N₀ E D P ς ℓ σ (-σ) M ME MD ψ φ₂ φ₁ hN₀ hD hor.le hEN hH1 hH2 hℓ hς
        hσ2 (neg_ne_zero.mpr hσ0) (by rwa [abs_neg]) hMle' le_rfl hP1 hψ0 hφ₂V
        (norm_le_one_of_tempered hφ₁) hφ₁.2.1
      refine le_trans (le_of_eq ?_) this
      congr 1
      -- reciprocity inside, then exchange the two variables
      have hrec : ∑ e ∈ (Finset.Icc 1 ME).filter Odd,
          ∑ d ∈ (Finset.Icc 1 MD).filter (fun a => Nat.Coprime a (2 * e)),
            (μ d : ℂ) * (μ e : ℂ) * φ₁ ((d : ℝ) / D) * φ₂ ((e : ℝ) / E) * Fs ς σ d e =
          ∑ e ∈ (Finset.Icc 1 ME).filter Odd,
          ∑ d ∈ (Finset.Icc 1 MD).filter (fun a => Nat.Coprime a (2 * e)),
            (μ d : ℂ) * (μ e : ℂ) * φ₁ ((d : ℝ) / D) * φ₂ ((e : ℝ) / E) *
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
  have hsplit3 : ∀ e d : ℕ, (μ d : ℂ) * (μ e : ℂ) * φ₁ ((d : ℝ) / D) * φ₂ ((e : ℝ) / E) *
        bracket N₀ ψ (2 ^ i * d) (2 ^ j * e) =
      (μ d : ℂ) * (μ e : ℂ) * φ₁ ((d : ℝ) / D) * φ₂ ((e : ℝ) / E) * Fs 1 (-κ) d e +
      (μ d : ℂ) * (μ e : ℂ) * φ₁ ((d : ℝ) / D) * φ₂ ((e : ℝ) / E) * Fs (-1) κ d e +
      (μ d : ℂ) * (μ e : ℂ) * φ₁ ((d : ℝ) / D) * φ₂ ((e : ℝ) / E) *
        (bracket N₀ ψ (2 ^ i * d) (2 ^ j * e) - Fs 1 (-κ) d e - Fs (-1) κ d e) := by
    intro e d; ring
  simp only [hsplit3, Finset.sum_add_distrib]
  -- the Poisson tails
  have hErr : ‖∑ e ∈ (Finset.Icc 1 ME).filter Odd,
          ∑ d ∈ (Finset.Icc 1 MD).filter (fun a => Nat.Coprime a (2 * e)),
            (μ d : ℂ) * (μ e : ℂ) * φ₁ ((d : ℝ) / D) * φ₂ ((e : ℝ) / E) *
              (bracket N₀ ψ (2 ^ i * d) (2 ^ j * e) - Fs 1 (-κ) d e - Fs (-1) κ d e)‖
        ≤ 32 * CP * P ^ kψ := by
    set Bp : ℝ := CP * P ^ kψ * ((4 * ℓ * D * E) / N₀) / N₀ ^ 3 with hBp
    have hBp0 : 0 ≤ Bp := by positivity
    have hterm : ∀ e ∈ (Finset.Icc 1 ME).filter Odd,
        ∀ d ∈ (Finset.Icc 1 MD).filter (fun a => Nat.Coprime a (2 * e)),
        ‖(μ d : ℂ) * (μ e : ℂ) * φ₁ ((d : ℝ) / D) * φ₂ ((e : ℝ) / E) *
              (bracket N₀ ψ (2 ^ i * d) (2 ^ j * e) - Fs 1 (-κ) d e - Fs (-1) κ d e)‖ ≤ Bp := by
      intro e he d hd
      by_cases hz : φ₁ ((d : ℝ) / D) = 0 ∨ φ₂ ((e : ℝ) / E) = 0
      · rcases hz with hz | hz <;> simp [hz, hBp0]
      rw [not_or] at hz
      obtain ⟨hz1, hz2⟩ := hz
      have hm1 := mem_of_ne_zero hφ₁ hz1
      have hm2 := mem_of_ne_zero hφ₂ hz2
      have hdle : (d : ℝ) ≤ 2 * D := by
        have := hm1.2; rwa [div_le_iff₀ hDpos] at this
      have hele : (e : ℝ) ≤ 2 * E := by
        have := hm2.2; rwa [div_le_iff₀ hEpos] at this
      have he' := Finset.mem_filter.mp he
      have hd' := Finset.mem_filter.mp hd
      obtain ⟨hdo, hcop⟩ := coprime_two_mul_iff.mp hd'.2
      have heo : Odd e := he'.2
      obtain ⟨hcl, hdn, hph⟩ := pair_class hi hj hdo heo hcop
      simp only [← hℓdef, ← hκdef] at hcl hdn hph
      have hd1 : 0 < d := (Finset.mem_Icc.mp hd'.1).1
      have he1 : 0 < e := (Finset.mem_Icc.mp he'.1).1
      have hℓpos : 0 < ℓ := by rcases hℓ with h | h <;> rw [h] <;> norm_num
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
      have hqQ : ((ℓ * d * e : ℕ) : ℝ) ≤ 4 * ℓ * D * E := by
        push_cast
        have h0 : (0 : ℝ) ≤ ℓ := by positivity
        calc (ℓ : ℝ) * d * e ≤ ℓ * (2 * D) * (2 * E) := by gcongr
          _ = 4 * ℓ * D * E := by ring
      have hratio := tail_ratio_le (kψ := kψ) (M := M) hN0one hk3
        (by exact_mod_cast hqpos) hqQ hMlt
      have hw : ‖(μ d : ℂ) * (μ e : ℂ) * φ₁ ((d : ℝ) / D) * φ₂ ((e : ℝ) / E)‖ ≤ 1 := by
        rw [norm_mul, norm_mul, norm_mul]
        have := norm_mu_le d
        have := norm_mu_le e
        have := norm_le_one_of_tempered hφ₁ ((d : ℝ) / D)
        have := norm_le_one_of_tempered hφ₂ ((e : ℝ) / E)
        have h1 : 0 ≤ ‖(μ d : ℂ)‖ := norm_nonneg _
        have h2 : 0 ≤ ‖(μ e : ℂ)‖ := norm_nonneg _
        have h3 : 0 ≤ ‖φ₁ ((d : ℝ) / D)‖ := norm_nonneg _
        have h4 : 0 ≤ ‖φ₂ ((e : ℝ) / E)‖ := norm_nonneg _
        calc ‖(μ d : ℂ)‖ * ‖(μ e : ℂ)‖ * ‖φ₁ ((d : ℝ) / D)‖ * ‖φ₂ ((e : ℝ) / E)‖
            ≤ 1 * 1 * 1 * 1 := by gcongr
          _ = 1 := by norm_num
      rw [norm_mul]
      have hR : ‖bracket N₀ ψ (2 ^ i * d) (2 ^ j * e) - Fs 1 (-κ) d e - Fs (-1) κ d e‖ ≤ Bp := by
        rw [sub_sub]
        refine hPB.trans ?_
        rw [mul_div_assoc (CP * P ^ kψ)]
        calc CP * P ^ kψ * (((ℓ * d * e : ℕ) : ℝ) / N₀ /
              (((M : ℝ) + 1) * N₀ / ((ℓ * d * e : ℕ) : ℝ)) ^ (kψ - 2))
            ≤ CP * P ^ kψ * ((4 * ℓ * D * E) / N₀ / N₀ ^ 3) := by gcongr
          _ = Bp := by rw [hBp]; ring
      calc _ ≤ 1 * Bp := by gcongr
        _ = Bp := one_mul _
    have hDE : D * E ≤ N₀ ^ 2 := by
      rw [sq]; exact mul_le_mul hDN hEN (by linarith) (by linarith)
    have hQle : 4 * (ℓ : ℝ) * D * E ≤ 8 * D * E := by
      calc 4 * (ℓ : ℝ) * D * E ≤ 4 * 2 * D * E := by
            have : (0 : ℝ) ≤ ℓ := by positivity
            gcongr
            exact hℓR.2
        _ = 8 * D * E := by ring
    calc _ ≤ ∑ e ∈ (Finset.Icc 1 ME).filter Odd,
            ∑ d ∈ (Finset.Icc 1 MD).filter (fun a => Nat.Coprime a (2 * e)),
            ‖(μ d : ℂ) * (μ e : ℂ) * φ₁ ((d : ℝ) / D) * φ₂ ((e : ℝ) / E) *
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
  have hN1 : (1 : ℝ) ≤ N₀ ^ ((1 : ℝ) / 2) := Real.one_le_rpow hN0one (by norm_num)
  have hPpos : 0 < P ^ max kV kψ := by positivity
  calc _ ≤ _ := norm_add₃_le
    _ ≤ CF * P ^ kV * X + CF * P ^ kV * X + 32 * CP * P ^ kψ := by
        gcongr
    _ ≤ CF * P ^ max kV kψ * (X + N₀ ^ ((1 : ℝ) / 2)) +
          CF * P ^ max kV kψ * (X + N₀ ^ ((1 : ℝ) / 2)) +
          32 * CP * (P ^ max kV kψ * (X + N₀ ^ ((1 : ℝ) / 2))) := by
        gcongr
        · linarith
        · linarith
        · calc P ^ kψ ≤ P ^ max kV kψ := hPψ
            _ = P ^ max kV kψ * 1 := (mul_one _).symm
            _ ≤ P ^ max kV kψ * (X + N₀ ^ ((1 : ℝ) / 2)) := by gcongr; linarith
    _ = (2 * CF + 32 * CP) * P ^ max kV kψ * (X + N₀ ^ ((1 : ℝ) / 2)) := by ring

end Tensor


open Tensor in
/-- **The error term for product weights** (paper §7 in the correlation form). -/
theorem detTensorBound : DetTensorBound := by
  intro ε hε
  set ε' : ℝ := min ε 1 with hε'
  have hε'0 : 0 < ε' := lt_min hε one_pos
  have hε'1 : ε' ≤ 1 := min_le_right _ _
  have hε'ε : ε' ≤ ε := min_le_left _ _
  obtain ⟨k, C, hC, hU⟩ := U_bound meanValueThm mellinSeparation poissonAPDecay ε' hε'0 hε'1
  refine ⟨k, 2 * C, by positivity, ?_⟩
  intro N₀ D E P ψ φ₁ φ₂ hN₀ hD hE hDN hEN hH1 hH2 hP1 hψ hφ₁ hφ₂
  have hN1 : (1 : ℝ) ≤ N₀ := by linarith
  have hNpos : (0 : ℝ) < N₀ := by linarith
  have hDpos : 0 < D := by linarith
  have hEpos : 0 < E := by linarith
  have hT0 : 0 ≤ D * E / N₀ := by positivity
  have hNe : N₀ ^ ε' ≤ N₀ ^ ε := Real.rpow_le_rpow_of_exponent_le hN1 hε'ε
  have hH1' : N₀ ^ ε' * (D * E / N₀) ≤ (max D E) ^ ((1 : ℝ) / 6) :=
    (mul_le_mul_of_nonneg_right hNe hT0).trans hH1
  have hH2' : (max D E) ^ ((2 : ℝ) / 3) * (N₀ ^ ε' * (D * E / N₀)) ^ 2 ≤ min D E := by
    refine le_trans ?_ hH2
    gcongr
  have hb := hU N₀ D E P ψ φ₁ φ₂ hN₀ hD hE hDN hEN hH1' hH2' hP1 hψ hφ₁ hφ₂
  have hR0 : 0 ≤ R3 N₀ (max D E) (min D E) :=
    R3_nonneg (A := max D E) hNpos (lt_max_of_lt_left hDpos) (lt_min hDpos hEpos)
  have hR : R3 N₀ (max D E) (min D E) =
      (max D E) ^ (-(1 : ℝ) / 12) * (D * E / N₀) ^ ((3 : ℝ) / 4)
        + (max D E) ^ (-(2 : ℝ) / 3) * (min D E) ^ ((1 : ℝ) / 2) * (D * E / N₀)
        + (min D E) ^ (-(1 : ℝ) / 2) * (D * E / N₀) := by
    unfold R3
    rw [mul_comm (max D E) (min D E), min_mul_max]
  have hNε : N₀ ^ (1 + ε') ≤ N₀ ^ (1 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  rw [← hR, oddDelta_split]
  have hPk : 0 ≤ C * P ^ k := by positivity
  calc ‖Uij N₀ D E ψ φ₁ φ₂ 0 0 - Uij N₀ D E ψ φ₁ φ₂ 1 0‖
      ≤ ‖Uij N₀ D E ψ φ₁ φ₂ 0 0‖ + ‖Uij N₀ D E ψ φ₁ φ₂ 1 0‖ := norm_sub_le _ _
    _ ≤ C * P ^ k * (N₀ ^ (1 + ε') * R3 N₀ (max D E) (min D E) + N₀ ^ ((1 : ℝ) / 2)) +
        C * P ^ k * (N₀ ^ (1 + ε') * R3 N₀ (max D E) (min D E) + N₀ ^ ((1 : ℝ) / 2)) :=
        add_le_add (hb 0 0 (by norm_num) (by norm_num)) (hb 1 0 (by norm_num) (by norm_num))
    _ ≤ C * P ^ k * (N₀ ^ (1 + ε) * R3 N₀ (max D E) (min D E) + N₀ ^ ((1 : ℝ) / 2)) +
        C * P ^ k * (N₀ ^ (1 + ε) * R3 N₀ (max D E) (min D E) + N₀ ^ ((1 : ℝ) / 2)) := by
        gcongr
    _ = 2 * C * P ^ k * (N₀ ^ (1 + ε) * R3 N₀ (max D E) (min D E) + N₀ ^ ((1 : ℝ) / 2)) := by
        ring

end Determinant

end MobiusDeterminant
