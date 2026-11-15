import MobiusDeterminant.Unconditional.MeanValueBox

/-!
# Assembly of the mean-value theorem (paper, Theorem 6.1, Steps 2 and 5)

* `Pe_eq_boxes`: the Heath-Brown identity (`J = 5`, `Z = 2^{K}` with `Z^5 ≍ D`) splits `P_e`
  into the `O((log D)^9)` sharp dyadic boxes;
* `boxV_bound`: Mellin separation of `V(d/D)` and `box_bound`, integrated against the
  Mellin density;
* `Pe_small_bound`: the trivial bound, used for bounded `D`.
-/

open Finset Real ArithmeticFunction MeasureTheory
open scoped ArithmeticFunction.Moebius

namespace MobiusDeterminant
namespace MeanValue

/-! ## Rewriting `P_e` -/

lemma Pe_eq_sum (D : ℝ) (V : ℝ → ℂ) (ν : ℤ → ℂ) (Hn e : ℕ) :
    Pe D V ν Hn e = ∑ d ∈ Icc 1 ⌊8 * D⌋₊, ((μ d : ℤ) : ℂ) * (V (d / D) * phiE ν Hn e d) := by
  unfold Pe phiE
  rw [sum_filter]
  refine sum_congr rfl fun d _ => ?_
  split_ifs <;> simp [mul_assoc]

lemma norm_kfrac (e : ℕ) (h : ℤ) (d : ℕ) : ‖kfrac e h d‖ = 1 := by
  unfold kfrac
  rw [show 2 * (π : ℂ) * Complex.I * ((((h : ZMod e) * (d : ZMod e)⁻¹).val : ℕ) : ℂ) / (e : ℂ) =
      (((2 * π * (((h : ZMod e) * (d : ZMod e)⁻¹).val : ℕ) / e) : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma norm_phiE_le (ν : ℤ → ℂ) (hν : ∀ h, ‖ν h‖ ≤ 1) (Hn e d : ℕ) :
    ‖phiE ν Hn e d‖ ≤ 2 * Hn + 1 := by
  unfold phiE
  split_ifs
  · refine (norm_sum_le _ _).trans ?_
    calc ∑ h ∈ Icc (-(Hn : ℤ)) Hn, ‖ν h * kfrac e h d‖ ≤ ∑ h ∈ Icc (-(Hn : ℤ)) Hn, (1 : ℝ) := by
          refine sum_le_sum fun h _ => ?_
          rw [norm_mul, norm_kfrac, mul_one]; exact hν h
      _ = 2 * Hn + 1 := by rw [sum_const, card_Icc_int, nsmul_eq_mul]; push_cast; ring
  · rw [norm_zero]; positivity

/-- **Bounded `D`**: the trivial bound `‖P‖_{ℓ²} ≤ √(8E) · 24 D H`. -/
theorem Pe_small_bound {D E : ℝ} (hD : 2 ≤ D) (hE : 1 ≤ E) {Hn : ℕ} (hH : 1 ≤ Hn) (V : ℝ → ℂ)
    (hV : ∀ x, ‖V x‖ ≤ 1) (ν : ℤ → ℂ) (hν : ∀ h, ‖ν h‖ ≤ 1) :
    Real.sqrt (∑ e ∈ moduli E, ‖Pe D V ν Hn e‖ ^ 2) ≤ Real.sqrt (8 * E) * (24 * D * Hn) := by
  have hD0 : 0 < D := by linarith
  have hH1 : (1 : ℝ) ≤ Hn := by exact_mod_cast hH
  have hpt : ∀ e ∈ moduli E, ‖Pe D V ν Hn e‖ ≤ 24 * D * Hn := by
    intro e _
    rw [Pe_eq_sum]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ d ∈ Icc 1 ⌊8 * D⌋₊, ‖((μ d : ℤ) : ℂ) * (V (d / D) * phiE ν Hn e d)‖
        ≤ ∑ d ∈ Icc 1 ⌊8 * D⌋₊, (2 * (Hn : ℝ) + 1) := by
          refine sum_le_sum fun d _ => ?_
          rw [norm_mul, norm_mul]
          have hmu : ‖((μ d : ℤ) : ℂ)‖ ≤ 1 := by
            rw [Complex.norm_intCast]; exact_mod_cast abs_moebius_le_one
          calc ‖((μ d : ℤ) : ℂ)‖ * (‖V (d / D)‖ * ‖phiE ν Hn e d‖) ≤ 1 * (1 * (2 * Hn + 1)) :=
                mul_le_mul hmu (mul_le_mul (hV _) (norm_phiE_le ν hν Hn e d) (norm_nonneg _)
                  zero_le_one) (by positivity) zero_le_one
            _ = 2 * Hn + 1 := by ring
      _ = (⌊8 * D⌋₊ : ℝ) * (2 * Hn + 1) := by
          rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
      _ ≤ (8 * D) * (3 * Hn) := by
          refine mul_le_mul (Nat.floor_le (by positivity)) (by linarith) (by positivity)
            (by positivity)
      _ = 24 * D * Hn := by ring
  refine (l2_le_card _ _ (by positivity) hpt).trans ?_
  exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (card_moduli_le hE)) (by positivity)

/-! ## The dyadic parameters -/

/-- `K` with `8D ≤ 32^K ≤ 256 D`, so that `Z = 2^K` satisfies `8D ≤ Z^5 ≤ 256 D`. -/
lemma exists_Km {D : ℝ} (hD : 2 ≤ D) :
    ∃ K : ℕ, 8 * D ≤ (32 : ℝ) ^ K ∧ (32 : ℝ) ^ K ≤ 256 * D := by
  have hex : ∃ K : ℕ, 8 * D ≤ (32 : ℝ) ^ K := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (8 * D) (by norm_num : (1 : ℝ) < 32)
    exact ⟨n, hn.le⟩
  classical
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  have h0 : Nat.find hex ≠ 0 := by
    intro h
    have := Nat.find_spec hex
    rw [h, pow_zero] at this
    linarith
  have hmin := Nat.find_min hex (Nat.sub_lt (Nat.pos_of_ne_zero h0) one_pos)
  push Not at hmin
  have : (32 : ℝ) ^ Nat.find hex = 32 * 32 ^ (Nat.find hex - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [this]
  linarith

lemma Km_le {D ε : ℝ} (hD : 2 ≤ D) (hε0 : 0 < ε) (hε1 : ε ≤ 1) {K : ℕ}
    (hK : (32 : ℝ) ^ K ≤ 256 * D) : (K : ℝ) ≤ 512 * D ^ ε / ε := by
  have hD0 : 0 < D := by linarith
  have h2K : (2 : ℝ) ^ K ≤ 256 * D :=
    le_trans (pow_le_pow_left₀ (by norm_num) (by norm_num) K) hK
  have hlog : (K : ℝ) * Real.log 2 ≤ Real.log (256 * D) := by
    rw [← Real.log_pow]; exact Real.log_le_log (by positivity) h2K
  have h1 : Real.log (256 * D) ≤ (256 * D) ^ ε / ε := Real.log_le_rpow_div (by positivity) hε0
  have h2 : (256 * D) ^ ε ≤ 256 * D ^ ε := rpow_mul_le_mul (by norm_num) hD0.le hε1
  have hl2 : (1 : ℝ) / 2 ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have h3 : (K : ℝ) * (1 / 2) ≤ 256 * D ^ ε / ε := by
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    calc (K : ℝ) * (1 / 2) ≤ K * Real.log 2 := mul_le_mul_of_nonneg_left hl2 hK0
      _ ≤ (256 * D) ^ ε / ε := hlog.trans h1
      _ ≤ 256 * D ^ ε / ε := div_le_div_of_nonneg_right h2 hε0.le
  have : 512 * D ^ ε / ε = 2 * (256 * D ^ ε / ε) := by ring
  linarith

/-! ## The boxes of the Heath-Brown decomposition -/

/-- The Heath-Brown boxes satisfy the hypotheses of `box_bound` (when they meet `[D/8, 8D]`). -/
noncomputable def hbBox {D : ℝ} {j Km : ℕ} (hj : j ∈ Icc 1 5) {κ : Fin (j - 1) ⊕ Fin j → ℕ}
    (hκ : κ ∈ Fintype.piFinset (boxRange j (5 * Km) Km)) (h32 : (32 : ℝ) ^ Km ≤ 256 * D)
    (hP1 : ∏ i, (2 : ℝ) ^ κ i ≤ 8 * D) (hP2 : D / 2 ^ 12 ≤ ∏ i, (2 : ℝ) ^ κ i) :
    Box D (Fin (j - 1) ⊕ Fin j) where
  κ := κ
  A := fun i => boxAtom j zC (MC ((2 : ℝ) ^ Km)) i (κ i)
  hcard := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
    have := (mem_Icc.1 hj).2; omega
  hsupp := by
    intro i n hn
    rcases i with a | b
    · exact dy_supp hn
    · exact dy_supp hn
  hbdd := by
    intro i n
    rcases i with a | b
    · exact norm_dy_le norm_zC_le _ _
    · exact norm_dy_le (norm_MC_le _) _ _
  htype := by
    intro i
    rcases i with a | b
    · left
      intro n h1 h2
      show dy zC (κ (Sum.inl a)) n = 1
      rw [dy_eq_of_mem h1 h2, zC_apply, ite_eq_right]
      have := Nat.one_le_two_pow (n := κ (Sum.inl a)); omega
    · right
      have hb := Fintype.mem_piFinset.1 hκ (Sum.inr b)
      simp only [boxRange, Sum.elim_inr, mem_range] at hb
      calc ((2 : ℝ) ^ κ (Sum.inr b)) ^ 5 ≤ ((2 : ℝ) ^ Km) ^ 5 :=
            pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega)) 5
        _ = (32 : ℝ) ^ Km := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
        _ ≤ 256 * D := h32
  hP1 := hP1
  hP2 := hP2

lemma hbBox_A {D : ℝ} {j Km : ℕ} (hj : j ∈ Icc 1 5) {κ : Fin (j - 1) ⊕ Fin j → ℕ}
    (hκ : κ ∈ Fintype.piFinset (boxRange j (5 * Km) Km)) (h32 : (32 : ℝ) ^ Km ≤ 256 * D)
    (hP1 : ∏ i, (2 : ℝ) ^ κ i ≤ 8 * D) (hP2 : D / 2 ^ 12 ≤ ∏ i, (2 : ℝ) ^ κ i) :
    (hbBox hj hκ h32 hP1 hP2).A = fun i => boxAtom j zC (MC ((2 : ℝ) ^ Km)) i (κ i) := rfl

lemma box_total_le {j Km : ℕ} (hj : j ∈ Icc 1 5) {κ : Fin (j - 1) ⊕ Fin j → ℕ}
    (hκ : κ ∈ Fintype.piFinset (boxRange j (5 * Km) Km)) :
    2 ^ Fintype.card (Fin (j - 1) ⊕ Fin j) * ∏ i, 2 ^ κ i ≤ 2 ^ 9 * 2 ^ (45 * Km) := by
  have hc : Fintype.card (Fin (j - 1) ⊕ Fin j) ≤ 9 := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
    have := (mem_Icc.1 hj).2; omega
  have hκle : ∀ i, κ i ≤ 5 * Km := by
    intro i
    have := Fintype.mem_piFinset.1 hκ i
    rcases i with a | b
    · simp only [boxRange, Sum.elim_inl, mem_range] at this; omega
    · simp only [boxRange, Sum.elim_inr, mem_range] at this; omega
  refine Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hc) ?_
  rw [prod_pow_eq_pow_sum]
  apply Nat.pow_le_pow_right (by norm_num)
  calc ∑ i, κ i ≤ ∑ _i : Fin (j - 1) ⊕ Fin j, 5 * Km := sum_le_sum fun i _ => hκle i
    _ = Fintype.card (Fin (j - 1) ⊕ Fin j) * (5 * Km) := by rw [sum_const, card_univ, smul_eq_mul]
    _ ≤ 9 * (5 * Km) := Nat.mul_le_mul_right _ hc
    _ = 45 * Km := by ring

lemma card_piFinset_le (j Km : ℕ) (hj : j ∈ Icc 1 5) :
    ((Fintype.piFinset (boxRange j (5 * Km) Km)).card : ℝ) ≤ (5 * Km + 1 : ℝ) ^ 9 := by
  rw [Fintype.card_piFinset]
  have hc : Fintype.card (Fin (j - 1) ⊕ Fin j) ≤ 9 := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
    have := (mem_Icc.1 hj).2; omega
  have h1 : ∏ i, (boxRange j (5 * Km) Km i).card ≤ (5 * Km + 1) ^ 9 := by
    calc ∏ i, (boxRange j (5 * Km) Km i).card ≤ ∏ _i : Fin (j - 1) ⊕ Fin j, (5 * Km + 1) := by
          refine Finset.prod_le_prod fun i _ => ?_
          rcases i with a | b
          · simp [boxRange]
          · simp [boxRange]; omega
      _ = (5 * Km + 1) ^ Fintype.card (Fin (j - 1) ⊕ Fin j) := by rw [prod_const, card_univ]
      _ ≤ (5 * Km + 1) ^ 9 := Nat.pow_le_pow_right (by omega) hc
  exact_mod_cast h1

/-! ## `P_e` as a sum over boxes (paper, Theorem 6.1, Step 2) -/

/-- **Box decomposition of `P_e`**: Heath-Brown's identity with `J = 5`, `Z = 2^{Km}`, and the
sharp dyadic decomposition of every atom. -/
theorem Pe_eq_boxes {D : ℝ} (hD : 2 ≤ D) (V : ℝ → ℂ)
    (hV : ∀ x, x ∉ Set.Icc (1 / 8 : ℝ) 8 → V x = 0) (ν : ℤ → ℂ) (Hn e : ℕ) {Km : ℕ}
    (hK1 : 8 * D ≤ (32 : ℝ) ^ Km) :
    Pe D V ν Hn e = ∑ j ∈ Icc 1 5, hbCoeff j *
      ∑ κ ∈ Fintype.piFinset (boxRange j (5 * Km) Km),
        ∑ d ∈ Icc 1 (2 ^ 9 * 2 ^ (45 * Km)),
          (∏ i, boxAtom j zC (MC ((2 : ℝ) ^ Km)) i (κ i)) d * (V (d / D) * phiE ν Hn e d) := by
  have hD0 : 0 < D := by linarith
  have h32 : (32 : ℝ) ^ Km = (2 : ℝ) ^ (5 * Km) := by rw [pow_mul]; norm_num
  rw [Pe_eq_sum]
  -- expand `μ` on `[1, 8D]`
  have hexp : ∀ d ∈ Icc 1 ⌊8 * D⌋₊, ((μ d : ℤ) : ℂ) * (V (d / D) * phiE ν Hn e d) =
      ∑ j ∈ Icc 1 5, hbCoeff j * ∑ κ ∈ Fintype.piFinset (boxRange j (5 * Km) Km),
        (∏ i, boxAtom j zC (MC ((2 : ℝ) ^ Km)) i (κ i)) d * (V (d / D) * phiE ν Hn e d) := by
    intro d hd
    obtain ⟨hd1, hd2⟩ := mem_Icc.1 hd
    have hdR : (d : ℝ) ≤ 8 * D := (Nat.cast_le.2 hd2).trans (Nat.floor_le (by positivity))
    have hdZ : (d : ℝ) ≤ ((2 : ℝ) ^ Km) ^ 5 := by
      rw [← pow_mul, mul_comm, ← h32]; linarith
    have hdK : d < 2 ^ (5 * Km + 1) := by
      have : (d : ℝ) < (2 : ℝ) ^ (5 * Km + 1) := by
        rw [pow_succ, ← h32]; linarith [pow_pos (by norm_num : (0 : ℝ) < 32) Km]
      exact_mod_cast this
    rw [mu_box_expansion (5 * Km) Km hd1 hdZ hdK, sum_mul]
    refine sum_congr rfl fun j _ => ?_
    rw [mul_assoc, sum_mul]
  rw [sum_congr rfl hexp, sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [← mul_sum, sum_comm]
  congr 1
  refine sum_congr rfl fun κ _ => ?_
  -- extend the range of `d` (the extra terms have `V(d/D) = 0`)
  apply sum_subset
  · intro d hd
    obtain ⟨hd1, hd2⟩ := mem_Icc.1 hd
    refine mem_Icc.2 ⟨hd1, hd2.trans ?_⟩
    have h1 : (⌊8 * D⌋₊ : ℝ) ≤ (2 : ℝ) ^ (5 * Km) := by
      rw [← h32]; exact (Nat.floor_le (by positivity)).trans hK1
    have h2 : ⌊8 * D⌋₊ ≤ 2 ^ (5 * Km) := by exact_mod_cast h1
    calc ⌊8 * D⌋₊ ≤ 2 ^ (5 * Km) := h2
      _ ≤ 2 ^ 9 * 2 ^ (45 * Km) := by
          rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · intro d hd hd'
    have hd1 := (mem_Icc.1 hd).1
    have hgt : ⌊8 * D⌋₊ < d := by
      by_contra h
      exact hd' (mem_Icc.2 ⟨hd1, not_lt.1 h⟩)
    have hgtR : 8 * D < d := by
      have := Nat.lt_floor_add_one (8 * D)
      have h' : ((⌊8 * D⌋₊ + 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast hgt
      push_cast at h'
      linarith
    have hV0 : V (d / D) = 0 := by
      apply hV
      intro hmem
      have := hmem.2
      rw [div_le_iff₀ hD0] at this
      linarith
    rw [hV0, zero_mul, mul_zero]

/-! ## One box, after Mellin separation (paper, Theorem 6.1, Step 5) -/

lemma continuous_twist (t : ℝ) : Continuous fun τ : ℝ => twist τ t := by
  unfold twist; fun_prop

lemma boxSum_continuous (T : ArithmeticFunction ℂ) (N : ℕ) (D : ℝ) (ν : ℤ → ℂ) (Hn e : ℕ) :
    Continuous fun τ => boxSum T N D τ ν Hn e := by
  unfold boxSum
  refine continuous_finsetSum _ fun d _ => ?_
  exact continuous_const.mul ((continuous_twist _).mul continuous_const)

lemma integrable_g_twist {g : ℝ → ℂ} (hgm : AEStronglyMeasurable g volume)
    (hgi : Integrable (fun τ => (1 + |τ|) * ‖g τ‖)) (t : ℝ) :
    Integrable (fun τ => g τ * twist τ t) := by
  have hg : Integrable g := by
    refine Integrable.mono' hgi hgm (Filter.Eventually.of_forall fun τ => ?_)
    have : 1 ≤ 1 + |τ| := by linarith [abs_nonneg τ]
    nlinarith [norm_nonneg (g τ)]
  have := hg.bdd_mul (c := 1) (continuous_twist t).aestronglyMeasurable
    (Filter.Eventually.of_forall fun τ => (norm_twist τ t).le)
  refine this.congr (Filter.Eventually.of_forall fun τ => ?_)
  simp only [mul_comm]

/-- **Mellin separation of one box**: `∑_d T(d) V(d/D) φ_e(d) = ∫ g(τ) B_e(τ) dτ`. -/
lemma box_mellin (T : ArithmeticFunction ℂ) (N : ℕ) {D : ℝ} (hD0 : 0 < D) (ν : ℤ → ℂ)
    (Hn e : ℕ) {g : ℝ → ℂ} (hgm : AEStronglyMeasurable g volume)
    (hgi : Integrable (fun τ => (1 + |τ|) * ‖g τ‖)) {V : ℝ → ℂ}
    (hrep : ∀ t : ℝ, 0 < t → V t = ∫ τ : ℝ, g τ * twist τ t) :
    ∑ d ∈ Icc 1 N, T d * (V (d / D) * phiE ν Hn e d) =
      ∫ τ, g τ * boxSum T N D τ ν Hn e := by
  unfold boxSum
  simp_rw [mul_sum]
  rw [integral_finsetSum]
  · refine sum_congr rfl fun d hd => ?_
    have hd0 : (0 : ℝ) < d / D := div_pos (by exact_mod_cast (mem_Icc.1 hd).1) hD0
    rw [hrep _ hd0]
    have : ∀ τ, g τ * (T d * (twist τ (d / D) * phiE ν Hn e d)) =
        (T d * phiE ν Hn e d) * (g τ * twist τ (d / D)) := fun τ => by ring
    simp_rw [this]
    rw [integral_const_mul]
    ring
  · intro d _
    have := (integrable_g_twist hgm hgi ((d : ℝ) / D)).const_mul (T d * phiE ν Hn e d)
    refine this.congr (Filter.Eventually.of_forall fun τ => ?_)
    simp only
    ring

/-- **One Heath-Brown box with the weight `V(d/D)`** (paper, Theorem 6.1, Steps 2–5). -/
theorem boxV_bound (St : Setup) (dv : DivBound) {CB : ℝ} (hCB0 : 0 < CB)
    (hB : BalancedAt dv.ε CB) {g : ℝ → ℂ} (hgm : AEStronglyMeasurable g volume)
    (hgi : Integrable (fun τ => (1 + |τ|) * ‖g τ‖)) {V : ℝ → ℂ}
    (hV : ∀ x, x ∉ Set.Icc (1 / 8 : ℝ) 8 → V x = 0)
    (hrep : ∀ t : ℝ, 0 < t → V t = ∫ τ : ℝ, g τ * twist τ t) {j Km : ℕ} (hj : j ∈ Icc 1 5)
    {κ : Fin (j - 1) ⊕ Fin j → ℕ} (hκ : κ ∈ Fintype.piFinset (boxRange j (5 * Km) Km))
    (h32 : (32 : ℝ) ^ Km ≤ 256 * St.D) :
    Real.sqrt (∑ e ∈ moduli St.E, ‖∑ d ∈ Icc 1 (2 ^ 9 * 2 ^ (45 * Km)),
        (∏ i, boxAtom j zC (MC ((2 : ℝ) ^ Km)) i (κ i)) d *
          (V (d / St.D) * phiE St.ν St.Hn e d)‖ ^ 2) ≤
      Cbox dv CB * (St.D ^ dv.ε) ^ 20 * target St.D St.E St.Hn *
        ∫ τ, (1 + |τ|) * ‖g τ‖ := by
  have hD0 : 0 < St.D := lt_of_lt_of_le (by positivity) St.hD
  have hD1 : 1 ≤ St.D := le_trans (by norm_num) St.hD
  have hX0 : 0 ≤ Cbox dv CB * (St.D ^ dv.ε) ^ 20 * target St.D St.E St.Hn := by
    have := dv.hC; have := dv.hε0
    have := target_nonneg St.D St.E St.Hn hD0.le (by linarith [St.hE1])
    unfold Cbox; positivity
  have hI0 : 0 ≤ ∫ τ, (1 + |τ|) * ‖g τ‖ :=
    integral_nonneg fun τ => mul_nonneg (by positivity) (norm_nonneg _)
  set T := ∏ i, boxAtom j zC (MC ((2 : ℝ) ^ Km)) i (κ i) with hT
  by_cases hmeet : ∏ i, (2 : ℝ) ^ κ i ≤ 8 * St.D ∧ St.D / 2 ^ 12 ≤ ∏ i, (2 : ℝ) ^ κ i
  · set B := hbBox hj hκ h32 hmeet.1 hmeet.2 with hBdef
    have hTB : T = ∏ i, B.A i := by rw [hT, hBdef, hbBox_A]
    simp_rw [box_mellin T _ hD0 St.ν St.Hn _ hgm hgi hrep]
    refine (l2_integral (moduli St.E) g hgm hgi
      (fun τ e => boxSum T (2 ^ 9 * 2 ^ (45 * Km)) St.D τ St.ν St.Hn e)
      (fun e => boxSum_continuous _ _ _ _ _ _) hX0 fun τ => ?_).trans (le_of_eq (by ring))
    rw [hTB]
    refine (box_bound St dv hCB0 hB B _ (box_total_le hj hκ) τ).trans (le_of_eq ?_)
    ring
  · -- the box does not meet `[D/8, 8D]`: all terms vanish
    have hsupp : ∀ d, T d ≠ 0 →
        ∏ i, 2 ^ κ i ≤ d ∧ d ≤ 2 ^ Fintype.card (Fin (j - 1) ⊕ Fin j) * ∏ i, 2 ^ κ i := by
      intro d hd
      have := prod_support (fun i => boxAtom j zC (MC ((2 : ℝ) ^ Km)) i (κ i))
        (fun i => 2 ^ κ i) (fun i => 2 ^ (κ i + 1)) univ (fun i _ n hn => by
          rcases i with a | b
          · exact ⟨(dy_supp hn).1, (dy_supp hn).2.le⟩
          · exact ⟨(dy_supp hn).1, (dy_supp hn).2.le⟩) d hd
      rwa [prod_two_pow_succ, card_univ] at this
    have hc9 : Fintype.card (Fin (j - 1) ⊕ Fin j) ≤ 9 := by
      rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
      have := (mem_Icc.1 hj).2; omega
    have hzero : ∀ e, ∑ d ∈ Icc 1 (2 ^ 9 * 2 ^ (45 * Km)),
        T d * (V (d / St.D) * phiE St.ν St.Hn e d) = 0 := by
      intro e
      refine sum_eq_zero fun d _ => ?_
      by_cases hd : T d = 0
      · rw [hd, zero_mul]
      obtain ⟨h1, h2⟩ := hsupp d hd
      have h1R : ∏ i, (2 : ℝ) ^ κ i ≤ d := by exact_mod_cast h1
      have h2R : (d : ℝ) ≤ 2 ^ 9 * ∏ i, (2 : ℝ) ^ κ i := by
        have : (d : ℝ) ≤ ((2 ^ Fintype.card (Fin (j - 1) ⊕ Fin j) * ∏ i, 2 ^ κ i : ℕ) : ℝ) := by
          exact_mod_cast h2
        push_cast at this
        exact this.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hc9)
          (by positivity))
      have hV0 : V (d / St.D) = 0 := by
        apply hV
        intro hmem
        rw [Set.mem_Icc, le_div_iff₀ hD0, div_le_iff₀ hD0] at hmem
        apply hmeet
        constructor
        · linarith
        · rw [div_le_iff₀ (by positivity)]; nlinarith
      rw [hV0, zero_mul, mul_zero]
    simp_rw [hzero, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sum_const_zero,
      Real.sqrt_zero]
    exact mul_nonneg hX0 hI0

end MeanValue
end MobiusDeterminant
