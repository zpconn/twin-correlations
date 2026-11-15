import MobiusDeterminant.Unconditional.LevelDefs
import MobiusDeterminant.Unconditional.LevelTempered

/-!
# Core block estimate (paper §8, Steps 5–6)

For one dyadic block of frequencies `h ∈ 𝓗 ⊆ [H, 2H)`, Mellin separation of the coupled
weight `F(s)`, `s = (h/H)(A/a)(B/b)`, factors `s^{-iτ}` into `(h/H)^{-iτ} (a/A)^{iτ} (b/B)^{iτ}`;
for each `τ` the sum becomes `∑_b μ(b) w_τ(b) P_b` with `P_b = Pe A V_τ ν_τ Hn b`, which
Cauchy–Schwarz and the mean-value theorem bound; integrating against the Mellin density
gives `core_block`.
-/

open Finset Real MeasureTheory
open scoped ArithmeticFunction.Moebius

namespace MobiusDeterminant

namespace Level

namespace Core

/-- If one Mellin coefficient is nonzero, the Mellin density is integrable. -/
theorem integrable_of_ne {g : ℝ → ℂ} {m : ℕ}
    (hint : Integrable (fun τ : ℝ => (1 + |τ|) ^ m * ‖g τ‖)) {t : ℝ}
    (hne : ∫ τ : ℝ, g τ * Complex.exp (-(τ * Real.log t : ℝ) * Complex.I) ≠ 0) :
    Integrable g := by
  have hi : Integrable (fun τ : ℝ => g τ * Complex.exp (-(τ * Real.log t : ℝ) * Complex.I)) := by
    by_contra h
    exact hne (integral_undef h)
  have hcont : Continuous (fun τ : ℝ => Complex.exp ((τ * Real.log t : ℝ) * Complex.I)) := by
    fun_prop
  have hmeas : AEStronglyMeasurable g volume := by
    have : g = fun τ => (g τ * Complex.exp (-(τ * Real.log t : ℝ) * Complex.I)) *
        Complex.exp ((τ * Real.log t : ℝ) * Complex.I) := by
      funext τ
      rw [mul_assoc, ← Complex.exp_add]
      simp
    rw [this]
    exact hi.aestronglyMeasurable.mul hcont.aestronglyMeasurable
  refine hint.mono' hmeas (ae_of_all _ fun τ => ?_)
  have h1 : (1 : ℝ) ≤ (1 + |τ|) ^ m := one_le_pow₀ (by linarith [abs_nonneg τ])
  have h2 : 0 ≤ ‖g τ‖ := norm_nonneg _
  nlinarith

theorem norm_exp_neg_mul_I (x : ℝ) : ‖Complex.exp (-(x : ℂ) * Complex.I)‖ = 1 := by
  rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I]

theorem integrable_mul_exp {g : ℝ → ℂ} (hg : Integrable g) (c : ℝ) :
    Integrable (fun τ : ℝ => g τ * Complex.exp (-(τ * c : ℝ) * Complex.I)) := by
  have hb : ∀ τ : ℝ, ‖Complex.exp (-(τ * c : ℝ) * Complex.I)‖ ≤ 1 :=
    fun τ => le_of_eq (norm_exp_neg_mul_I _)
  have hcont : Continuous (fun τ : ℝ => Complex.exp (-(τ * c : ℝ) * Complex.I)) := by
    fun_prop
  have := hg.bdd_mul hcont.aestronglyMeasurable (ae_of_all _ hb)
  exact this.congr (ae_of_all _ fun τ => mul_comm _ _)

/-- Reindexing the frequencies `h ↦ σ h`. -/
theorem sum_reindex (𝓗 : Finset ℤ) (σ : ℤ) (Hn : ℕ) (c k : ℤ → ℂ)
    (hσ : ∀ h ∈ 𝓗, |σ * h| ≤ Hn) :
    ∑ h ∈ 𝓗, c h * k (σ * h) =
      ∑ h' ∈ Finset.Icc (-(Hn : ℤ)) Hn, (∑ h ∈ 𝓗, if σ * h = h' then c h else 0) * k h' := by
  simp_rw [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h hh => ?_
  rw [Finset.sum_ite_eq, ite_eq_left]
  rw [Finset.mem_Icc]
  exact abs_le.mp (hσ h hh)

/-- Changing the (filtered) range `Icc 1 M` of a sum whose terms vanish beyond `M₀`. -/
theorem sum_filter_extend {T : ℕ → ℂ} {M₀ M₁ M₂ : ℕ} (h1 : M₀ ≤ M₁) (h2 : M₀ ≤ M₂)
    (hT : ∀ a, M₀ < a → T a = 0) (p : ℕ → Prop) [DecidablePred p] :
    ∑ a ∈ (Finset.Icc 1 M₁).filter p, T a = ∑ a ∈ (Finset.Icc 1 M₂).filter p, T a := by
  have key : ∀ M, M₀ ≤ M → ∑ a ∈ (Finset.Icc 1 M₀).filter p, T a =
      ∑ a ∈ (Finset.Icc 1 M).filter p, T a := by
    intro M hM
    apply Finset.sum_subset
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_Icc] at ha ⊢
      exact ⟨⟨ha.1.1, ha.1.2.trans hM⟩, ha.2⟩
    · intro a ha hna
      apply hT
      simp only [Finset.mem_filter, Finset.mem_Icc] at ha hna
      by_contra hle
      exact hna ⟨⟨ha.1.1, not_lt.mp hle⟩, ha.2⟩
  rw [← key M₁ h1, key M₂ h2]

/-- Splitting the Mellin phase `s^{-iτ}`, `s = (h/H)(A/a)(B/b)`. -/
theorem split_phase (τ : ℝ) {h H a A b B : ℝ} (hh : 0 < h) (hH : 0 < H) (ha : 0 < a)
    (hA : 0 < A) (hb : 0 < b) (hB : 0 < B) :
    Complex.exp (-(τ * Real.log (h / H * (A / a) * (B / b)) : ℝ) * Complex.I) =
      Complex.exp (-(τ * Real.log (h / H) : ℝ) * Complex.I) *
        Complex.exp ((τ * Real.log (a / A) : ℝ) * Complex.I) *
        Complex.exp ((τ * Real.log (b / B) : ℝ) * Complex.I) := by
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have hlog : Real.log (h / H * (A / a) * (B / b)) =
      Real.log (h / H) - Real.log (a / A) - Real.log (b / B) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_div hA.ne' ha.ne', Real.log_div hB.ne' hb.ne', Real.log_div ha.ne' hA.ne',
      Real.log_div hb.ne' hB.ne']
    ring
  rw [hlog]
  push_cast
  ring

/-- On the support of `φ`, `x^{iτ} = uPow τ x`. -/
theorem phi_mul_exp_eq {φ : ℝ → ℂ} (hφ : ∀ x, x ∉ Set.Icc (1/2 : ℝ) 2 → φ x = 0) (τ x : ℝ) :
    φ x * Complex.exp ((τ * Real.log x : ℝ) * Complex.I) = φ x * uPow τ x := by
  by_cases hx : x ∈ Set.Icc (1/2 : ℝ) 2
  · rw [uPow_eq τ ⟨by linarith [hx.1], by linarith [hx.2]⟩]
  · rw [hφ x hx, zero_mul, zero_mul]

/-- The frequency coefficients `ν_τ(h') = ∑_{h ∈ 𝓗, σ h = h'} (H/h)(h/H)^{-iτ}`. -/
noncomputable def nuT (𝓗 : Finset ℤ) (σ : ℤ) (H τ : ℝ) (h' : ℤ) : ℂ :=
  ∑ h ∈ 𝓗, if σ * h = h' then
    ((H / h : ℝ) : ℂ) * Complex.exp (-(τ * Real.log (h / H) : ℝ) * Complex.I) else 0

theorem nuT_zero {𝓗 : Finset ℤ} {σ : ℤ} {H : ℝ} (τ : ℝ) (hσ : σ ≠ 0)
    (h𝓗 : ∀ h ∈ 𝓗, h ≠ 0) : nuT 𝓗 σ H τ 0 = 0 := by
  unfold nuT
  refine Finset.sum_eq_zero fun h hh => ?_
  rw [ite_eq_right]
  exact mul_ne_zero hσ (h𝓗 h hh)

theorem norm_nuT_le {𝓗 : Finset ℤ} {σ : ℤ} {H : ℝ} (τ : ℝ) (hσ : σ ≠ 0) (hH : 0 < H)
    (h𝓗 : ∀ h ∈ 𝓗, H ≤ (h : ℝ)) (h' : ℤ) : ‖nuT 𝓗 σ H τ h'‖ ≤ 1 := by
  unfold nuT
  by_cases hex : ∃ h₀ ∈ 𝓗, σ * h₀ = h'
  · obtain ⟨h₀, hh₀, he⟩ := hex
    rw [Finset.sum_eq_single_of_mem h₀ hh₀ (fun h hh hne => ite_eq_right (fun e => hne
      (mul_left_cancel₀ hσ (e.trans he.symm))))]
    rw [ite_eq_left he, norm_mul, norm_exp_neg_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have h0 : 0 < (h₀ : ℝ) := lt_of_lt_of_le hH (h𝓗 h₀ hh₀)
    rw [abs_of_pos (by positivity), div_le_one h0]
    exact h𝓗 h₀ hh₀
  · push Not at hex
    rw [Finset.sum_eq_zero fun h hh => ite_eq_right (hex h hh), norm_zero]
    exact zero_le_one

/-- Cauchy–Schwarz over `b`, followed by an `ℓ²` bound on the `Q b`. -/
theorem cs_bound {B Y : ℝ} (hB : 1 ≤ B) (Mb : ℕ) (w Q : ℕ → ℂ) (hw1 : ∀ b, ‖w b‖ ≤ 1)
    (hw0 : ∀ b : ℕ, (b : ℝ) / B ∉ Set.Icc (1/2 : ℝ) 2 → w b = 0) (hY : 0 ≤ Y)
    (hQ : ∑ e ∈ (Finset.Ioc ⌊B / 8⌋₊ ⌊8 * B⌋₊).filter Squarefree, ‖Q e‖ ^ 2 ≤ Y ^ 2) :
    ‖∑ b ∈ (Finset.Icc 1 Mb).filter Odd, (μ b : ℂ) * w b * Q b‖ ≤
      Real.sqrt 2 * B ^ ((1 : ℝ) / 2) * Y := by
  classical
  have hB0 : 0 < B := by linarith
  set S' := ((Finset.Icc 1 Mb).filter Odd).filter
    (fun b : ℕ => Squarefree b ∧ (b : ℝ) / B ∈ Set.Icc (1/2 : ℝ) 2) with hS'
  have hmu : ∀ b : ℕ, ‖(μ b : ℂ)‖ ≤ 1 := by
    intro b
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have step1 : ‖∑ b ∈ (Finset.Icc 1 Mb).filter Odd, (μ b : ℂ) * w b * Q b‖ ≤
      ∑ b ∈ S', ‖Q b‖ := by
    refine (norm_sum_le _ _).trans ?_
    rw [← Finset.sum_filter_of_ne (p := fun b : ℕ => Squarefree b ∧ (b : ℝ) / B ∈ Set.Icc (1/2 : ℝ) 2)]
    · refine Finset.sum_le_sum fun b _ => ?_
      rw [norm_mul, norm_mul]
      have := hmu b
      have := hw1 b
      have : 0 ≤ ‖Q b‖ := norm_nonneg _
      calc ‖(μ b : ℂ)‖ * ‖w b‖ * ‖Q b‖ ≤ 1 * 1 * ‖Q b‖ := by gcongr
        _ = ‖Q b‖ := by ring
    · intro b _ hne
      refine ⟨?_, ?_⟩
      · by_contra hsq
        apply hne
        rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
        simp
      · by_contra hI
        apply hne
        rw [hw0 b hI]
        simp
  have hsub : S' ⊆ (Finset.Ioc ⌊B / 8⌋₊ ⌊8 * B⌋₊).filter Squarefree := by
    intro b hb
    simp only [hS', Finset.mem_filter, Finset.mem_Icc, Set.mem_Icc] at hb
    obtain ⟨⟨⟨hb1, _⟩, _⟩, hsq, hlo, hhi⟩ := hb
    rw [le_div_iff₀ hB0] at hlo
    rw [div_le_iff₀ hB0] at hhi
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨?_, ?_⟩, hsq⟩
    · rw [Nat.floor_lt (by positivity)]
      linarith
    · rw [Nat.le_floor_iff (by positivity)]
      linarith
  have hcard : (S'.card : ℝ) ≤ 2 * B := by
    have hsub2 : S' ⊆ Finset.Icc 1 ⌊2 * B⌋₊ := by
      intro b hb
      simp only [hS', Finset.mem_filter, Finset.mem_Icc, Set.mem_Icc] at hb
      obtain ⟨⟨⟨hb1, _⟩, _⟩, _, _, hhi⟩ := hb
      rw [div_le_iff₀ hB0] at hhi
      simp only [Finset.mem_Icc]
      refine ⟨hb1, ?_⟩
      rw [Nat.le_floor_iff (by positivity)]
      linarith
    have h1 := Finset.card_le_card hsub2
    rw [Nat.card_Icc, Nat.add_sub_cancel] at h1
    calc (S'.card : ℝ) ≤ (⌊2 * B⌋₊ : ℝ) := by exact_mod_cast h1
      _ ≤ 2 * B := Nat.floor_le (by positivity)
  have hsq : (∑ b ∈ S', ‖Q b‖) ^ 2 ≤ 2 * B * Y ^ 2 := by
    calc (∑ b ∈ S', ‖Q b‖) ^ 2 ≤ (S'.card : ℝ) * ∑ b ∈ S', ‖Q b‖ ^ 2 :=
          sq_sum_le_card_mul_sum_sq
      _ ≤ (2 * B) * Y ^ 2 := by
          apply mul_le_mul hcard _ (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
          exact (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans hQ
  have hsqrt : ∑ b ∈ S', ‖Q b‖ ≤ Real.sqrt (2 * B * Y ^ 2) :=
    (le_abs_self _).trans (Real.abs_le_sqrt hsq)
  rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num), Real.sqrt_sq hY,
    Real.sqrt_eq_rpow B] at hsqrt
  exact step1.trans hsqrt

/-- `∑_{h'} ν_τ(h') k(h') = ∑_{h ∈ 𝓗} (H/h)(h/H)^{-iτ} k(σ h)`. -/
theorem nuT_sum (𝓗 : Finset ℤ) (σ : ℤ) (H τ : ℝ) (Hn : ℕ) (k : ℤ → ℂ)
    (hσ : ∀ h ∈ 𝓗, |σ * h| ≤ Hn) :
    ∑ h' ∈ Finset.Icc (-(Hn : ℤ)) Hn, nuT 𝓗 σ H τ h' * k h' =
      ∑ h ∈ 𝓗, ((H / h : ℝ) : ℂ) * Complex.exp (-(τ * Real.log (h / H) : ℝ) * Complex.I) *
        k (σ * h) :=
  (sum_reindex 𝓗 σ Hn _ k hσ).symm

end Core

open MobiusDeterminant.Level.Core in
theorem core_block (hMV : MeanValueThm) (hM : MellinSeparation) :
    ∀ ε > (0 : ℝ), ∃ kV kF : ℕ, ∃ C > (0 : ℝ),
    ∀ (A B : ℝ) (Hn : ℕ) (H : ℝ) (σ : ℤ) (𝓗 : Finset ℤ) (Ma Mb : ℕ)
      (φa φb F : ℝ → ℂ) (P PF : ℝ),
      2 ≤ A → 1 ≤ B → B ≤ A → 1 ≤ Hn → (Hn : ℝ) ≤ A ^ ((1 : ℝ) / 6) →
      A ^ ((2 : ℝ) / 3) * (Hn : ℝ) ^ 2 ≤ B → 0 < H → σ ≠ 0 →
      (∀ h ∈ 𝓗, H ≤ (h : ℝ) ∧ (h : ℝ) < 2 * H ∧ |σ * h| ≤ Hn) →
      ⌊2 * A⌋₊ ≤ Ma →
      1 ≤ P → TemperedOn φa P kV (1/2) 2 →
      (∀ x, ‖φb x‖ ≤ 1) → (∀ x, x ∉ Set.Icc (1/2 : ℝ) 2 → φb x = 0) →
      1 ≤ PF → TemperedOn F PF kF (1/8) 16 →
      ‖∑ b ∈ (Finset.Icc 1 Mb).filter Odd,
          ∑ a ∈ (Finset.Icc 1 Ma).filter (fun a => Nat.Coprime a (2 * b)),
            (μ a : ℂ) * (μ b : ℂ) * φa ((a : ℝ) / A) * φb ((b : ℝ) / B) *
              ∑ h ∈ 𝓗, ((H / h : ℝ) : ℂ) * F ((h : ℝ) / H * (A / a) * (B / b)) *
                kfrac b (σ * h) a‖
        ≤ C * P ^ kV * PF ^ kF * B ^ ((1 : ℝ) / 2) * A ^ ε *
            (A ^ ((11 : ℝ) / 12) * B ^ ((1 : ℝ) / 2) * (Hn : ℝ) ^ ((3 : ℝ) / 4)
              + A ^ ((1 : ℝ) / 3) * B * Hn + A * Hn) := by
  intro ε hε
  obtain ⟨CMV, hCMV, kV, hMVb⟩ := hMV ε hε
  obtain ⟨CM, hCM, kF, hMb⟩ := hM (1/8) 16 (by norm_num) (by norm_num) kV
  obtain ⟨c₀, hc₀, hV⟩ := V_tempered kV
  refine ⟨kV, kF, Real.sqrt 2 * CMV * c₀ ^ kV * CM, by positivity, ?_⟩
  intro A B Hn H σ 𝓗 Ma Mb φa φb F P PF hA2 hB1 hBA hHn1 hHn6 hHnE hH hσ h𝓗 hMa hP hφa
    hφb1 hφb0 hPF hF
  obtain ⟨g, hgint, hgbd, hgrep⟩ := hMb F PF hPF hF
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  have hφa0 : ∀ x, x ∉ Set.Icc (1/2 : ℝ) 2 → φa x = 0 := hφa.2.1
  have hh0 : ∀ h ∈ 𝓗, 0 < (h : ℝ) := fun h hh => lt_of_lt_of_le hH (h𝓗 h hh).1
  have hb1 : ∀ b ∈ (Finset.Icc 1 Mb).filter Odd, (1 : ℝ) ≤ b := by
    intro b hb
    have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1
    exact_mod_cast this
  have ha1 : ∀ b : ℕ, ∀ a ∈ (Finset.Icc 1 Ma).filter (fun a => Nat.Coprime a (2 * b)),
      (1 : ℝ) ≤ a := by
    intro b a ha
    have := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1
    exact_mod_cast this
  have hpos : ∀ b ∈ (Finset.Icc 1 Mb).filter Odd,
      ∀ a ∈ (Finset.Icc 1 Ma).filter (fun a => Nat.Coprime a (2 * b)), ∀ h ∈ 𝓗,
      0 < (h : ℝ) / H * (A / a) * (B / b) := by
    intro b hb a ha h hh
    have := hb1 b hb
    have := ha1 b a ha
    have := hh0 h hh
    positivity
  set X : ℝ := A ^ ((11 : ℝ) / 12) * B ^ ((1 : ℝ) / 2) * (Hn : ℝ) ^ ((3 : ℝ) / 4)
      + A ^ ((1 : ℝ) / 3) * B * Hn + A * Hn with hX
  have hX0 : 0 ≤ X := by positivity
  have hRHS0 : 0 ≤ Real.sqrt 2 * CMV * c₀ ^ kV * CM * P ^ kV * PF ^ kF * B ^ ((1 : ℝ) / 2) *
      A ^ ε * X := by positivity
  by_cases hgi : Integrable g
  swap
  · have hF0 : ∀ t : ℝ, 0 < t → F t = 0 := by
      intro t ht
      rw [hgrep t ht]
      by_contra hne
      exact hgi (integrable_of_ne hgint hne)
    refine (le_of_eq ?_).trans hRHS0
    rw [norm_eq_zero]
    refine Finset.sum_eq_zero fun b hb => Finset.sum_eq_zero fun a ha => ?_
    rw [Finset.sum_eq_zero fun h hh => by rw [hF0 _ (hpos b hb a ha h hh), mul_zero, zero_mul],
      mul_zero]
  -- the inner sum for fixed `τ`: Cauchy–Schwarz and the mean-value theorem
  have hInner : ∀ τ : ℝ, ‖∑ b ∈ (Finset.Icc 1 Mb).filter Odd, (μ b : ℂ) *
        (φb ((b : ℝ) / B) * Complex.exp ((τ * Real.log ((b : ℝ) / B) : ℝ) * Complex.I)) *
        Pe A (fun x => φa x * uPow τ x) (nuT 𝓗 σ H τ) Hn b‖ ≤
      Real.sqrt 2 * B ^ ((1 : ℝ) / 2) * (CMV * (c₀ * P * (1 + |τ|)) ^ kV * A ^ ε * X) := by
    intro τ
    have hPV : 1 ≤ c₀ * P * (1 + |τ|) := by
      have : 1 ≤ 1 + |τ| := by linarith [abs_nonneg τ]
      calc (1 : ℝ) = 1 * 1 * 1 := by ring
        _ ≤ c₀ * P * (1 + |τ|) := by gcongr
    refine cs_bound hB1 Mb _ _ ?_ ?_ (by positivity) ?_
    · intro b
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
      exact hφb1 _
    · intro b hb
      rw [hφb0 _ hb, zero_mul]
    · exact hMVb A B (c₀ * P * (1 + |τ|)) Hn _ _ hA2 hB1 hBA hHn1 hHn6 hHnE hPV
        (hV φa P τ hP hφa)
        (nuT_zero τ hσ fun h hh => by have := (hh0 h hh).ne'; exact_mod_cast this)
        (norm_nuT_le τ hσ hH fun h hh => (h𝓗 h hh).1)
  -- the pointwise expansion of `g τ · (inner sum)`
  have hpt : ∀ τ : ℝ, g τ * ∑ b ∈ (Finset.Icc 1 Mb).filter Odd, (μ b : ℂ) *
        (φb ((b : ℝ) / B) * Complex.exp ((τ * Real.log ((b : ℝ) / B) : ℝ) * Complex.I)) *
        Pe A (fun x => φa x * uPow τ x) (nuT 𝓗 σ H τ) Hn b =
      ∑ b ∈ (Finset.Icc 1 Mb).filter Odd,
        ∑ a ∈ (Finset.Icc 1 Ma).filter (fun a => Nat.Coprime a (2 * b)), ∑ h ∈ 𝓗,
          (μ a : ℂ) * (μ b : ℂ) * φa ((a : ℝ) / A) * φb ((b : ℝ) / B) *
            (((H / h : ℝ) : ℂ) * kfrac b (σ * h) a) *
            (g τ * Complex.exp (-(τ * Real.log ((h : ℝ) / H * (A / a) * (B / b)) : ℝ) *
              Complex.I)) := by
    intro τ
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hb0 : (0 : ℝ) < b := lt_of_lt_of_le one_pos (hb1 b hb)
    simp only [Pe]
    rw [sum_filter_extend (M₀ := ⌊2 * A⌋₊) (Nat.floor_mono (by linarith)) hMa ?_]
    swap
    · intro a ha
      have hlt : 2 * A < (a : ℝ) := (Nat.floor_lt (by positivity)).mp ha
      have : (a : ℝ) / A ∉ Set.Icc (1/2 : ℝ) 2 := by
        intro hmem
        have := hmem.2
        rw [div_le_iff₀ hA0] at this
        linarith
      rw [hφa0 _ this, zero_mul, mul_zero, zero_mul]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    have ha0 : (0 : ℝ) < a := lt_of_lt_of_le one_pos (ha1 b a ha)
    rw [nuT_sum 𝓗 σ H τ Hn (fun h' => kfrac b h' a) (fun h hh => (h𝓗 h hh).2.2)]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h hh => ?_
    rw [split_phase τ (hh0 h hh) hH ha0 hA0 hb0 hB0, ← phi_mul_exp_eq hφa0 τ ((a : ℝ) / A)]
    ring
  -- exchange of the finite sums with the Mellin integral
  have hS : (∑ b ∈ (Finset.Icc 1 Mb).filter Odd,
          ∑ a ∈ (Finset.Icc 1 Ma).filter (fun a => Nat.Coprime a (2 * b)),
            (μ a : ℂ) * (μ b : ℂ) * φa ((a : ℝ) / A) * φb ((b : ℝ) / B) *
              ∑ h ∈ 𝓗, ((H / h : ℝ) : ℂ) * F ((h : ℝ) / H * (A / a) * (B / b)) *
                kfrac b (σ * h) a) =
      ∫ τ : ℝ, g τ * ∑ b ∈ (Finset.Icc 1 Mb).filter Odd, (μ b : ℂ) *
        (φb ((b : ℝ) / B) * Complex.exp ((τ * Real.log ((b : ℝ) / B) : ℝ) * Complex.I)) *
        Pe A (fun x => φa x * uPow τ x) (nuT 𝓗 σ H τ) Hn b := by
    simp_rw [hpt]
    have hI : ∀ (b a : ℕ) (h : ℤ) (c : ℂ), Integrable (fun τ : ℝ => c *
        (g τ * Complex.exp (-(τ * Real.log ((h : ℝ) / H * (A / a) * (B / b)) : ℝ) *
          Complex.I))) :=
      fun b a h c => (integrable_mul_exp hgi _).const_mul c
    rw [integral_finsetSum _ fun b _ => integrable_finsetSum _ fun a _ =>
      integrable_finsetSum _ fun h _ => hI b a h _]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun h _ => hI b a h _]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [integral_finsetSum _ fun h _ => hI b a h _, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h hh => ?_
    rw [integral_const_mul, hgrep _ (hpos b hb a ha h hh)]
    ring
  rw [hS]
  set K : ℝ := Real.sqrt 2 * B ^ ((1 : ℝ) / 2) * (CMV * (c₀ * P) ^ kV * A ^ ε * X) with hK
  have hK0 : 0 ≤ K := by positivity
  refine (norm_integral_le_of_norm_le (hgint.const_mul K) (ae_of_all _ fun τ => ?_)).trans ?_
  · rw [norm_mul]
    refine (mul_le_mul_of_nonneg_left (hInner τ) (norm_nonneg _)).trans (le_of_eq ?_)
    rw [hK, mul_pow, mul_pow]
    ring
  · rw [integral_const_mul]
    calc K * ∫ τ : ℝ, (1 + |τ|) ^ kV * ‖g τ‖ ≤ K * (CM * PF ^ kF) :=
          mul_le_mul_of_nonneg_left hgbd hK0
      _ = _ := by rw [hK, mul_pow]; ring

end Level

end MobiusDeterminant
