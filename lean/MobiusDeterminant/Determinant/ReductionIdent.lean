import MobiusDeterminant.Determinant.ReductionCut
import MobiusDeterminant.Determinant.ReductionComb

/-!
# Reduction of Theorem 1.3: the exact identities

For `κ = 2`, `X ≥ 1`, `A, B > 0`, with `N_j = 2^j X` (`j < 3`), `D' = 3D/2`, `E' = 3E/2`
and the product weights `ψ_{τ,j} = psiP X j τ`, `φ₁_τ = phiP (τ₀ - τ₂)`, `φ₂_τ = phiP (τ₁ - τ₃)`:

* `detSum_eq_int`  : `S_2 = ∑_j ∫ g(τ) oddSum(N_j, D', E', ψ_{τ,j}, φ₁_τ, φ₂_τ) dτ`;
* `zeroMode_eq_int` : `S_2⁰ = ∑_j ∫ g(τ) oddMain(N_j, D', E', ψ_{τ,j}, φ₁_τ, φ₂_τ) dτ`
  (Fubini and the substitution `ν = αδ`);
* `detSum_sub_zeroMode_eq` : `S_2 - S_2⁰ = ∑_j ∫ g(τ) oddDelta(…) dτ`.
-/

open Finset Real MeasureTheory
open scoped ArithmeticFunction.Moebius

namespace MobiusDeterminant.Determinant.Reduction

open MobiusDeterminant.Level

/-- The divisor-pair sum without its main term. -/
noncomputable def oddSum (N₀ D E : ℝ) (ψ φ₁ φ₂ : ℝ → ℂ) : ℂ :=
  ∑ d ∈ (Icc 1 ⌊2 * D⌋₊).filter Odd, ∑ e ∈ (Icc 1 ⌊2 * E⌋₊).filter Odd,
    (μ d : ℂ) * (μ e : ℂ) * φ₁ ((d : ℝ) / D) * φ₂ ((e : ℝ) / E) *
      ∑ n ∈ (Icc 1 ⌊2 * N₀⌋₊).filter (fun n => Odd n ∧ d ∣ n ∧ e ∣ n + 2), ψ ((n : ℝ) / N₀)

lemma oddDelta_eq (N₀ D E : ℝ) (ψ φ₁ φ₂ : ℝ → ℂ) :
    oddDelta N₀ D E ψ φ₁ φ₂ = oddSum N₀ D E ψ φ₁ φ₂ - oddMain N₀ D E ψ φ₁ φ₂ := by
  unfold oddDelta oddSum oddMain oddBracket
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  ring

/-! ## Bounded measurable functions of `τ` -/

/-- `h` is a.e.-strongly measurable and bounded, so `g h` is integrable for integrable `g`. -/
def Good (h : E4 → ℂ) : Prop :=
  AEStronglyMeasurable h volume ∧ ∃ C : ℝ, ∀ τ, ‖h τ‖ ≤ C

lemma Good.of_continuous {h : E4 → ℂ} (hc : Continuous h) {C : ℝ} (hb : ∀ τ, ‖h τ‖ ≤ C) :
    Good h := ⟨hc.aestronglyMeasurable, C, hb⟩

lemma Good.const (c : ℂ) : Good (fun _ => c) :=
  Good.of_continuous continuous_const (fun _ => le_rfl)

lemma Good.mul {h₁ h₂ : E4 → ℂ} (g₁ : Good h₁) (g₂ : Good h₂) :
    Good (fun τ => h₁ τ * h₂ τ) := by
  obtain ⟨m₁, C₁, b₁⟩ := g₁
  obtain ⟨m₂, C₂, b₂⟩ := g₂
  refine ⟨m₁.mul m₂, C₁ * C₂, fun τ => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (b₁ τ) (b₂ τ) (norm_nonneg _) ((norm_nonneg _).trans (b₁ τ))

lemma Good.add {h₁ h₂ : E4 → ℂ} (g₁ : Good h₁) (g₂ : Good h₂) :
    Good (fun τ => h₁ τ + h₂ τ) := by
  obtain ⟨m₁, C₁, b₁⟩ := g₁
  obtain ⟨m₂, C₂, b₂⟩ := g₂
  exact ⟨m₁.add m₂, C₁ + C₂, fun τ => (norm_add_le _ _).trans (add_le_add (b₁ τ) (b₂ τ))⟩

lemma Good.sum {ι : Type*} (s : Finset ι) {h : ι → E4 → ℂ} (hg : ∀ i ∈ s, Good (h i)) :
    Good (fun τ => ∑ i ∈ s, h i τ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Good.const 0
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (hg a (Finset.mem_insert_self a s)).add
      (ih (fun i hi => hg i (Finset.mem_insert_of_mem hi)))

lemma Good.integrable {g h : E4 → ℂ} (hgi : Integrable g) (hh : Good h) :
    Integrable (fun τ => g τ * h τ) := by
  obtain ⟨m, C, b⟩ := hh
  exact hgi.mul_bdd m (Filter.Eventually.of_forall b)

lemma good_psiP (X : ℝ) (j : ℕ) (y : ℝ) : Good (fun τ => psiP X j τ y) :=
  Good.of_continuous (continuous_psiP X j y) (fun τ => norm_psiP_le X j τ y)

lemma good_phiP (a b : Fin 4) (y : ℝ) : Good (fun τ => phiP (τ a - τ b) y) :=
  Good.of_continuous (continuous_phiP a b y) (fun _ => norm_phiP_le _ y)

lemma good_fourier (X : ℝ) (j : ℕ) : Good (fun τ => fourierR (psiP X j τ) 0) := by
  simp_rw [Cutoff.fourierR_zero]
  refine ⟨?_, 3 / 2, fun τ => ?_⟩
  · exact ((continuous_psiP₂ X j).aestronglyMeasurable).integral_prod_right'
  · refine (norm_integral_le_integral_norm _).trans ?_
    have := Tempered.integral_norm_le (norm_psiP_le X j τ) (fun x hx => psiP_eq_zero X j τ hx)
    linarith

lemma good_oddSum (N₀ D E X : ℝ) (j : ℕ) :
    Good (fun τ => oddSum N₀ D E (psiP X j τ) (phiP (τ 0 - τ 2)) (phiP (τ 1 - τ 3))) := by
  unfold oddSum
  refine Good.sum _ (fun d _ => Good.sum _ (fun e _ => ?_))
  exact ((((Good.const _).mul (good_phiP 0 2 _)).mul (good_phiP 1 3 _)).mul
    (Good.sum _ (fun n _ => good_psiP X j _)))

lemma good_oddMain (N₀ D E X : ℝ) (j : ℕ) :
    Good (fun τ => oddMain N₀ D E (psiP X j τ) (phiP (τ 0 - τ 2)) (phiP (τ 1 - τ 3))) := by
  unfold oddMain
  refine Good.sum _ (fun d _ => Good.sum _ (fun e _ => ?_))
  exact ((((Good.const _).mul (good_phiP 0 2 _)).mul (good_phiP 1 3 _)).mul
    (((Good.const _).mul (good_fourier X j)).mul (Good.const _)))

/-! ## Interchanging finite sums and integrals -/

lemma integral_sum2 {α β : Type*} (s : Finset α) (t : Finset β) (F : α → β → E4 → ℂ)
    (hF : ∀ a b, Integrable (F a b)) :
    ∫ τ, ∑ a ∈ s, ∑ b ∈ t, F a b τ = ∑ a ∈ s, ∑ b ∈ t, ∫ τ, F a b τ := by
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => hF a b))]
  exact Finset.sum_congr rfl (fun a _ => integral_finsetSum _ (fun b _ => hF a b))

lemma integral_sum3 {α β γ : Type*} (s : Finset α) (t : Finset β) (u : α → β → Finset γ)
    (F : α → β → γ → E4 → ℂ) (hF : ∀ a b c, Integrable (F a b c)) :
    ∫ τ, ∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u a b, F a b c τ =
      ∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u a b, ∫ τ, F a b c τ := by
  rw [integral_sum2 s t _ (fun a b => integrable_finsetSum _ (fun c _ => hF a b c))]
  exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
    integral_finsetSum _ (fun c _ => hF a b c)))

/-! ## The determinant sum -/

lemma three_halves (x D : ℝ) (hD : D ≠ 0) : 3 / 2 * (x / (3 / 2 * D)) = x / D := by
  field_simp

/-- `S_2 = ∑_j ∫ g · oddSum_j`. -/
theorem detSum_eq_int {W : ℝ × ℝ × ℝ × ℝ → ℂ} (hW : SmoothWeight W) {g : E4 → ℂ}
    (hgi : Integrable g)
    (hg : ∀ α β δ ε : ℝ, 0 < α → 0 < β → 0 < δ → 0 < ε →
      W (α, β, δ, ε) = ∫ τ, g τ * mphase τ α β δ ε)
    {X A B : ℝ} (hX : 1 ≤ X) (hA : 0 < A) (hB : 0 < B) :
    detSum 2 W A B X = ∑ j ∈ range 3, ∫ τ, g τ *
      oddSum (2 ^ j * X) (3 / 2 * (X / A)) (3 / 2 * (X / B)) (psiP X j τ)
        (phiP (τ 0 - τ 2)) (phiP (τ 1 - τ 3)) := by
  have hX0 : 0 < X := by linarith
  have hDA : 0 < X / A := div_pos hX0 hA
  have hEB : 0 < X / B := div_pos hX0 hB
  set Dp := 3 / 2 * (X / A) with hDp
  set Ep := 3 / 2 * (X / B) with hEp
  have hDp0 : 0 < Dp := by positivity
  have hEp0 : 0 < Ep := by positivity
  -- the τ-integrals of the individual terms
  set I : ℕ → ℕ → ℕ → ℕ → ℂ := fun j d e n => ∫ τ, g τ *
    (phiP (τ 0 - τ 2) ((d : ℝ) / Dp) * phiP (τ 1 - τ 3) ((e : ℝ) / Ep) *
      psiP X j τ ((n : ℝ) / (2 ^ j * X))) with hI
  have hexp : ∀ j : ℕ, ∫ τ, g τ * oddSum (2 ^ j * X) Dp Ep (psiP X j τ) (phiP (τ 0 - τ 2))
      (phiP (τ 1 - τ 3)) =
      ∑ d ∈ (Icc 1 ⌊2 * Dp⌋₊).filter Odd, ∑ e ∈ (Icc 1 ⌊2 * Ep⌋₊).filter Odd,
        (μ d : ℂ) * (μ e : ℂ) *
          ∑ n ∈ (Icc 1 ⌊2 * (2 ^ j * X)⌋₊).filter (fun n => Odd n ∧ d ∣ n ∧ e ∣ n + 2),
            I j d e n := by
    intro j
    have hpt : ∀ τ, g τ * oddSum (2 ^ j * X) Dp Ep (psiP X j τ) (phiP (τ 0 - τ 2))
        (phiP (τ 1 - τ 3)) =
        ∑ d ∈ (Icc 1 ⌊2 * Dp⌋₊).filter Odd, ∑ e ∈ (Icc 1 ⌊2 * Ep⌋₊).filter Odd,
          ∑ n ∈ (Icc 1 ⌊2 * (2 ^ j * X)⌋₊).filter (fun n => Odd n ∧ d ∣ n ∧ e ∣ n + 2),
            (μ d : ℂ) * (μ e : ℂ) * (g τ * (phiP (τ 0 - τ 2) ((d : ℝ) / Dp) *
              phiP (τ 1 - τ 3) ((e : ℝ) / Ep) * psiP X j τ ((n : ℝ) / (2 ^ j * X)))) := by
      intro τ
      unfold oddSum
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun d _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      ring
    simp_rw [hpt]
    rw [integral_sum3 _ _ _ _ (fun d e n => ((good_phiP 0 2 _).mul (good_phiP 1 3 _) |>.mul
      (good_psiP X j _) |>.integrable hgi).const_mul _)]
    refine Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_))
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [integral_const_mul]
  simp_rw [hexp]
  rw [detSum_two_eq hW hX0 hA hB]
  -- reorder: `j` innermost
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun e he => ?_)
  rw [← Finset.mul_sum]
  congr 1
  symm
  simp only [Finset.mem_filter, Finset.mem_Icc] at hd he
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.1.1
  have he0 : (0 : ℝ) < e := by exact_mod_cast he.1.1
  set R := (Icc 1 ⌊8 * X⌋₊).filter (fun n => Odd n ∧ d ∣ n ∧ e ∣ n + 2) with hR
  -- extend the `n`-ranges
  have hext : ∀ j ∈ range 3,
      ∑ n ∈ (Icc 1 ⌊2 * (2 ^ j * X)⌋₊).filter (fun n => Odd n ∧ d ∣ n ∧ e ∣ n + 2), I j d e n =
        ∑ n ∈ R, I j d e n := by
    intro j hj
    have hj3 : j < 3 := Finset.mem_range.mp hj
    have h2j : (2 : ℝ) ^ j ≤ 4 := by
      calc (2 : ℝ) ^ j ≤ 2 ^ 2 := pow_le_pow_right₀ (by norm_num) (by omega)
        _ = 4 := by norm_num
    apply Finset.sum_subset
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc, hR] at hn ⊢
      refine ⟨⟨hn.1.1, hn.1.2.trans (Nat.floor_mono (by nlinarith))⟩, hn.2⟩
    · intro n hn hnj
      simp only [Finset.mem_filter, Finset.mem_Icc, hR] at hn hnj
      have hlt : ⌊2 * (2 ^ j * X)⌋₊ < n := by
        by_contra h; exact hnj ⟨⟨hn.1.1, by omega⟩, hn.2⟩
      have hout : (n : ℝ) / (2 ^ j * X) ∉ Set.Icc (1 / 2 : ℝ) 2 := by
        intro h
        have h2 := h.2
        rw [div_le_iff₀ (by positivity)] at h2
        have : n ≤ ⌊2 * (2 ^ j * X)⌋₊ := Nat.le_floor (by linarith)
        omega
      simp only [hI]
      simp_rw [psiP_eq_zero X j _ hout, mul_zero, integral_zero]
  rw [Finset.sum_congr rfl hext, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  -- the sum over the pieces is the kernel
  have hker : ∑ j ∈ range 3, I j d e n =
      ∫ τ, g τ * kerH X τ ((n : ℝ) / X) ((d : ℝ) / Dp) ((e : ℝ) / Ep) := by
    simp only [hI]
    rw [← integral_finsetSum _ (fun j _ => ((good_phiP 0 2 _).mul (good_phiP 1 3 _) |>.mul
      (good_psiP X j _) |>.integrable hgi))]
    congr 1
    funext τ
    unfold kerH
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [show (n : ℝ) / (2 ^ j * X) = (n : ℝ) / X / 2 ^ j by rw [div_div, mul_comm]]
  rw [hker, integral_kerH hW hg hX (by positivity) (by positivity)]
  rw [three_halves _ _ hDA.ne', three_halves _ _ hEB.ne']
  congr 1
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · simp only; field_simp
  · simp only; field_simp

/-! ## The zero mode -/

/-- The substitution `ν = αδ`: `∫ W(ν/δ, (ν+2/X)/ε, δ, ε) dν = δ Φ(0; δ, ε)`. -/
lemma integral_W_sub (W : ℝ × ℝ × ℝ × ℝ → ℂ) {X δ ε : ℝ} (hX : X ≠ 0) (hδ : 0 < δ)
    (hε : ε ≠ 0) :
    ∫ ν, W (ν / δ, (ν + 2 / X) / ε, δ, ε) = ((δ : ℝ) : ℂ) * Phi0 2 W X δ ε := by
  unfold Phi0
  set f : ℝ → ℂ := fun α => W (α, α * δ / ε + ((2 : ℤ) : ℝ) / (ε * X), δ, ε) with hf
  have hpt : ∀ ν : ℝ, W (ν / δ, (ν + 2 / X) / ε, δ, ε) = f (ν / δ) := by
    intro ν
    simp only [hf]
    congr 1
    refine Prod.ext rfl (Prod.ext ?_ rfl)
    simp only
    push_cast
    field_simp
  simp_rw [hpt]
  rw [Measure.integral_comp_div f δ, abs_of_pos hδ, Complex.real_smul]

lemma integrable_psiP_div (X : ℝ) (j : ℕ) (τ : E4) :
    Integrable (fun ν => psiP X j τ (ν / 2 ^ j)) := by
  have h2j : (0 : ℝ) < 2 ^ j := by positivity
  have hc : Continuous (fun ν => psiP X j τ (ν / 2 ^ j)) := by
    unfold psiP; fun_prop
  refine hc.integrable_of_hasCompactSupport
    (Tempered.hasCompactSupport_of_vanish (a := 2 ^ j / 2) (b := 2 ^ j * 2) (fun ν hν => ?_))
  apply psiP_eq_zero
  intro h
  apply hν
  obtain ⟨h1, h2⟩ := h
  rw [le_div_iff₀ h2j] at h1
  rw [div_le_iff₀ h2j] at h2
  constructor <;> linarith

lemma integrable_gker {g : E4 → ℂ} (hgi : Integrable g) (X y₁ y₂ : ℝ) :
    Integrable (Function.uncurry fun τ ν => g τ * kerH X τ ν y₁ y₂) (volume.prod volume) := by
  have hb : Integrable (fun z : E4 × ℝ => ‖g z.1‖ *
      Set.indicator (Set.Icc (1 / 2 : ℝ) 8) (fun _ => (3 : ℝ)) z.2) (volume.prod volume) :=
    hgi.norm.mul_prod ((integrable_indicator_iff measurableSet_Icc).mpr
      (integrableOn_const (by simp)))
  refine hb.mono' ?_ (Filter.Eventually.of_forall (fun z => ?_))
  · exact (hgi.aestronglyMeasurable.comp_fst).mul
      (continuous_kerH₂ X y₁ y₂).aestronglyMeasurable
  · simp only [Function.uncurry]
    rw [norm_mul]
    by_cases hz : z.2 ∈ Set.Icc (1 / 2 : ℝ) 8
    · rw [Set.indicator_of_mem hz]
      exact mul_le_mul_of_nonneg_left (norm_kerH_le X z.1 z.2 y₁ y₂) (norm_nonneg _)
    · rw [Set.indicator_of_notMem hz, kerH_eq_zero_of_not_mem X z.1 hz]
      simp

/-- **The main term for one pair `(d, e)`**:
`∑_j ∫ g(τ) φ₁_τ(y₁) φ₂_τ(y₂) N_j ψ̂_{τ,j}(0) dτ = X δ Φ(0; δ, ε)`, `δ = 3y₁/2`, `ε = 3y₂/2`. -/
theorem main_de {W : ℝ × ℝ × ℝ × ℝ → ℂ} (hW : SmoothWeight W) {g : E4 → ℂ}
    (hgi : Integrable g)
    (hg : ∀ α β δ ε : ℝ, 0 < α → 0 < β → 0 < δ → 0 < ε →
      W (α, β, δ, ε) = ∫ τ, g τ * mphase τ α β δ ε)
    {X : ℝ} (hX : 1 ≤ X) {y₁ y₂ : ℝ} (hy₁ : 0 < y₁) (hy₂ : 0 < y₂) :
    ∑ j ∈ range 3, ∫ τ, g τ * (phiP (τ 0 - τ 2) y₁ * phiP (τ 1 - τ 3) y₂ *
      ((((2 : ℝ) ^ j * X : ℝ) : ℂ) * fourierR (psiP X j τ) 0)) =
      ((X * (3 / 2 * y₁) : ℝ) : ℂ) * Phi0 2 W X (3 / 2 * y₁) (3 / 2 * y₂) := by
  have hX0 : 0 < X := by linarith
  rw [← integral_finsetSum _ (fun j _ => (((good_phiP 0 2 _).mul (good_phiP 1 3 _)).mul
    ((Good.const _).mul (good_fourier X j))).integrable hgi)]
  -- pointwise in `τ`: the sum over the pieces is `X ∫ g kerH dν`
  have hpt : ∀ τ : E4, ∑ j ∈ range 3, g τ * (phiP (τ 0 - τ 2) y₁ * phiP (τ 1 - τ 3) y₂ *
      ((((2 : ℝ) ^ j * X : ℝ) : ℂ) * fourierR (psiP X j τ) 0)) =
      (X : ℂ) * ∫ ν, g τ * kerH X τ ν y₁ y₂ := by
    intro τ
    unfold kerH
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum _ (fun j _ => (integrable_psiP_div X j τ).const_mul _ |>.const_mul _),
      Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp_rw [← mul_assoc (g τ)]
    rw [integral_const_mul, Measure.integral_comp_div (psiP X j τ) (2 ^ j),
      Cutoff.fourierR_zero, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ j), Complex.real_smul]
    push_cast
    ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_integral_swap (integrable_gker hgi X y₁ y₂)]
  simp_rw [integral_kerH hW hg hX hy₁ hy₂]
  rw [integral_W_sub W hX0.ne' (by positivity) (by positivity)]
  push_cast
  ring

/-- `S_2⁰ = ∑_j ∫ g · oddMain_j`. -/
theorem zeroMode_eq_int {W : ℝ × ℝ × ℝ × ℝ → ℂ} (hW : SmoothWeight W) {g : E4 → ℂ}
    (hgi : Integrable g)
    (hg : ∀ α β δ ε : ℝ, 0 < α → 0 < β → 0 < δ → 0 < ε →
      W (α, β, δ, ε) = ∫ τ, g τ * mphase τ α β δ ε)
    {X A B : ℝ} (hX : 1 ≤ X) (hA : 0 < A) (hB : 0 < B) :
    zeroMode 2 W A B X = ∑ j ∈ range 3, ∫ τ, g τ *
      oddMain (2 ^ j * X) (3 / 2 * (X / A)) (3 / 2 * (X / B)) (psiP X j τ)
        (phiP (τ 0 - τ 2)) (phiP (τ 1 - τ 3)) := by
  have hX0 : 0 < X := by linarith
  have hDA : 0 < X / A := div_pos hX0 hA
  have hEB : 0 < X / B := div_pos hX0 hB
  set Dp := 3 / 2 * (X / A) with hDp
  set Ep := 3 / 2 * (X / B) with hEp
  have hexp : ∀ j : ℕ, ∫ τ, g τ * oddMain (2 ^ j * X) Dp Ep (psiP X j τ) (phiP (τ 0 - τ 2))
      (phiP (τ 1 - τ 3)) =
      ∑ d ∈ (Icc 1 ⌊2 * Dp⌋₊).filter Odd, ∑ e ∈ (Icc 1 ⌊2 * Ep⌋₊).filter Odd,
        (μ d : ℂ) * (μ e : ℂ) * ((dens d e / 2 : ℝ) : ℂ) *
          ∫ τ, g τ * (phiP (τ 0 - τ 2) ((d : ℝ) / Dp) * phiP (τ 1 - τ 3) ((e : ℝ) / Ep) *
            ((((2 : ℝ) ^ j * X : ℝ) : ℂ) * fourierR (psiP X j τ) 0)) := by
    intro j
    have hpt : ∀ τ, g τ * oddMain (2 ^ j * X) Dp Ep (psiP X j τ) (phiP (τ 0 - τ 2))
        (phiP (τ 1 - τ 3)) =
        ∑ d ∈ (Icc 1 ⌊2 * Dp⌋₊).filter Odd, ∑ e ∈ (Icc 1 ⌊2 * Ep⌋₊).filter Odd,
          (μ d : ℂ) * (μ e : ℂ) * ((dens d e / 2 : ℝ) : ℂ) *
            (g τ * (phiP (τ 0 - τ 2) ((d : ℝ) / Dp) * phiP (τ 1 - τ 3) ((e : ℝ) / Ep) *
              ((((2 : ℝ) ^ j * X : ℝ) : ℂ) * fourierR (psiP X j τ) 0))) := by
      intro τ
      unfold oddMain
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun d _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      ring
    simp_rw [hpt]
    rw [integral_sum2 _ _ _ (fun d e => ((((good_phiP 0 2 _).mul (good_phiP 1 3 _)).mul
      ((Good.const _).mul (good_fourier X j))).integrable hgi).const_mul _)]
    refine Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_))
    rw [integral_const_mul]
  simp_rw [hexp]
  rw [← zeroMode_two_eq hW hX0 hA hB]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun e he => ?_)
  rw [← Finset.mul_sum]
  simp only [Finset.mem_filter, Finset.mem_Icc] at hd he
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.1.1
  have he0 : (0 : ℝ) < e := by exact_mod_cast he.1.1
  rw [main_de hW hgi hg hX (by positivity) (by positivity), three_halves _ _ hDA.ne',
    three_halves _ _ hEB.ne']
  push_cast
  ring

/-- **The exact identity**: `S_2 - S_2⁰ = ∑_j ∫ g · oddDelta_j`. -/
theorem detSum_sub_zeroMode_eq {W : ℝ × ℝ × ℝ × ℝ → ℂ} (hW : SmoothWeight W) {g : E4 → ℂ}
    (hgi : Integrable g)
    (hg : ∀ α β δ ε : ℝ, 0 < α → 0 < β → 0 < δ → 0 < ε →
      W (α, β, δ, ε) = ∫ τ, g τ * mphase τ α β δ ε)
    {X A B : ℝ} (hX : 1 ≤ X) (hA : 0 < A) (hB : 0 < B) :
    detSum 2 W A B X - zeroMode 2 W A B X = ∑ j ∈ range 3, ∫ τ, g τ *
      oddDelta (2 ^ j * X) (3 / 2 * (X / A)) (3 / 2 * (X / B)) (psiP X j τ)
        (phiP (τ 0 - τ 2)) (phiP (τ 1 - τ 3)) := by
  rw [detSum_eq_int hW hgi hg hX hA hB, zeroMode_eq_int hW hgi hg hX hA hB,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← integral_sub ((good_oddSum _ _ _ X j).integrable hgi)
    ((good_oddMain _ _ _ X j).integrable hgi)]
  congr 1
  funext τ
  rw [oddDelta_eq, mul_sub]

end MobiusDeterminant.Determinant.Reduction
