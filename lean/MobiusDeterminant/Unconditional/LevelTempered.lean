import MobiusDeterminant.Unconditional.LevelDefs

/-!
# Tempered weights for the level of distribution (paper §8)

A small calculus of derivative bounds (`Tmp f A B k`: `‖f^{(j)}‖ ≤ A B^j` for `j ≤ k`) and the
temperedness of the concrete weights used in Proposition 8.1 and in the proof of Theorem 1.2:

* `V_tempered`      : `φ · x^{iτ}` is tempered with `P_V = c₀ P (1 + |τ|)`;
* `blockF_tempered` : the coupled weight `s ↦ s ψ̂(Y₁ s) e(Y₂ s)` (smoothly cut off);
* `piece_tempered`  : the pieces of the smoothed sharp cutoffs, with `P = c/ν`.
-/

open Finset Real MeasureTheory Filter Topology
open scoped ArithmeticFunction.Moebius FourierTransform

namespace MobiusDeterminant

namespace Level

namespace Tempered

/-! ## Generalities on iterated derivatives -/

/-- If `f` vanishes outside `[a,b]`, so do all its iterated derivatives. -/
lemma iteratedDeriv_eq_zero_of_vanish {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {a b : ℝ} (hf : ∀ x, x ∉ Set.Icc a b → f x = 0) (j : ℕ) {x : ℝ}
    (hx : x ∉ Set.Icc a b) : iteratedDeriv j f x = 0 := by
  have hev : f =ᶠ[𝓝 x] fun _ => (0 : F) := by
    filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hx] with y hy using hf y hy
  rw [hev.iteratedDeriv_eq]
  simp

/-- A `C^k` function whose first `k` derivatives are bounded by `1` outside a compact
interval has all of them bounded by some `M ≥ 1`. -/
lemma exists_bound_iteratedDeriv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {k : ℕ} (hf : ContDiff ℝ k f) (a b : ℝ)
    (hout : ∀ j ≤ k, ∀ x, x ∉ Set.Icc a b → ‖iteratedDeriv j f x‖ ≤ 1) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ j ≤ k, ∀ x, ‖iteratedDeriv j f x‖ ≤ M := by
  set g : ℝ → ℝ := fun x => ∑ j ∈ Finset.range (k + 1), ‖iteratedDeriv j f x‖ with hg
  have hgc : Continuous g := by
    refine continuous_finsetSum _ (fun j hj => ?_)
    have hj' : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    exact (hf.continuous_iteratedDeriv j (by exact_mod_cast hj')).norm
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    hgc.continuousOn
  refine ⟨max C 1, le_max_right _ _, fun j hj x => ?_⟩
  by_cases hx : x ∈ Set.Icc a b
  · have h1 : ‖iteratedDeriv j f x‖ ≤ g x :=
      Finset.single_le_sum (f := fun j => ‖iteratedDeriv j f x‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    have h2 := hC x hx
    rw [Real.norm_eq_abs] at h2
    exact h1.trans ((le_abs_self _).trans (h2.trans (le_max_left _ _)))
  · exact (hout j hj x hx).trans (le_max_right _ _)

/-! ## The `Tmp` calculus -/

lemma tmp_mono_B {f : ℝ → ℂ} {A B B' : ℝ} {k : ℕ} (hf : Tmp f A B k) (hB : 0 ≤ B)
    (hBB : B ≤ B') : Tmp f A B' k := by
  refine ⟨hf.1, fun j hj x => (hf.2 j hj x).trans ?_⟩
  have hA : 0 ≤ A := by
    have := (norm_nonneg _).trans (hf.2 0 (Nat.zero_le _) x)
    simpa using this
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hB hBB j) hA

lemma tmp_mul {f g : ℝ → ℂ} {A₁ B₁ A₂ B₂ : ℝ} {k : ℕ} (hf : Tmp f A₁ B₁ k)
    (hg : Tmp g A₂ B₂ k) :
    Tmp (fun x => f x * g x) (A₁ * A₂) (B₁ + B₂) k := by
  refine ⟨hf.1.mul hg.1, fun j hj x => ?_⟩
  have hfx : ContDiffAt ℝ j f x := (hf.1.of_le (by exact_mod_cast hj)).contDiffAt
  have hgx : ContDiffAt ℝ j g x := (hg.1.of_le (by exact_mod_cast hj)).contDiffAt
  have hmul := iteratedDeriv_mul hfx hgx
  have hfun : (fun x => f x * g x) = f * g := rfl
  rw [hfun, hmul]
  calc ‖∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℂ) * iteratedDeriv i f x * iteratedDeriv (j - i) g x‖
      ≤ ∑ i ∈ Finset.range (j + 1), ‖(j.choose i : ℂ) * iteratedDeriv i f x *
          iteratedDeriv (j - i) g x‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (A₁ * B₁ ^ i) * (A₂ * B₂ ^ (j - i)) := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        rw [norm_mul, norm_mul, Complex.norm_natCast]
        have h1 := hf.2 i (hi'.trans hj) x
        have h2 := hg.2 (j - i) ((Nat.sub_le _ _).trans hj) x
        have hA₁ : 0 ≤ A₁ * B₁ ^ i := (norm_nonneg _).trans h1
        exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2
          (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hA₁)
    _ = A₁ * A₂ * (B₁ + B₂) ^ j := by
        rw [add_pow, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring

lemma tmp_comp_affine {f : ℝ → ℂ} {A B : ℝ} {k : ℕ} (hf : Tmp f A B k) (a b : ℝ) :
    Tmp (fun x => f (a * x + b)) A (|a| * B) k := by
  set g : ℝ → ℂ := fun y => f (y + b) with hgdef
  have hgc : ContDiff ℝ k g := hf.1.comp (contDiff_id.add contDiff_const)
  have hfun : (fun x => f (a * x + b)) = fun x => g (a * x) := rfl
  refine ⟨?_, fun j hj x => ?_⟩
  · rw [hfun]; exact hgc.comp (contDiff_const.mul contDiff_id)
  · rw [hfun, iteratedDeriv_comp_const_smul (hgc.of_le (by exact_mod_cast hj)) a]
    simp only
    rw [hgdef, iteratedDeriv_comp_add_const, norm_smul, norm_pow, Real.norm_eq_abs]
    calc |a| ^ j * ‖iteratedDeriv j f (a * x + b)‖ ≤ |a| ^ j * (A * B ^ j) :=
          mul_le_mul_of_nonneg_left (hf.2 j hj _) (pow_nonneg (abs_nonneg a) j)
      _ = A * (|a| * B) ^ j := by ring

lemma tmp_const_mul {f : ℝ → ℂ} {A B : ℝ} {k : ℕ} (hf : Tmp f A B k) (c : ℂ) :
    Tmp (fun x => c * f x) (‖c‖ * A) B k := by
  refine ⟨contDiff_const.mul hf.1, fun j hj x => ?_⟩
  rw [iteratedDeriv_const_mul c (hf.1.of_le (by exact_mod_cast hj)).contDiffAt, norm_mul,
    mul_assoc]
  exact mul_le_mul_of_nonneg_left (hf.2 j hj x) (norm_nonneg c)

/-- From `Tmp` to `TemperedOn`, normalising by `A`. -/
lemma temperedOn_of_tmp {f : ℝ → ℂ} {A B : ℝ} {k : ℕ} {a b : ℝ} (hf : Tmp f A B k)
    (hA : 0 < A) (hsupp : ∀ x, x ∉ Set.Icc a b → f x = 0) :
    TemperedOn (fun x => f x / A) B k a b := by
  refine ⟨hf.1.div_const _, fun x hx => by simp [hsupp x hx], fun j hj x => ?_⟩
  rw [iteratedDeriv_div_const, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA,
    div_le_iff₀ hA, mul_comm]
  exact hf.2 j hj x

lemma tmp_of_temperedOn {f : ℝ → ℂ} {P : ℝ} {k : ℕ} {a b : ℝ} (h : TemperedOn f P k a b) :
    Tmp f 1 P k :=
  ⟨h.1, fun j hj x => by simpa using h.2.2 j hj x⟩


/-! ## Concrete smooth functions -/

lemma contDiff_st {n : ℕ} : ContDiff ℝ n smoothTransition :=
  (smoothTransition.contDiff (n := ⊤)).of_le (by exact_mod_cast le_top)

lemma contDiff_ofReal_comp {f : ℝ → ℝ} {n : ℕ} (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (fun x => (f x : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp hf

/-- Bounded derivatives for a `C^k` function vanishing outside `[a,b]`. -/
lemma exists_tmp_of_vanish {f : ℝ → ℂ} {k : ℕ} (hf : ContDiff ℝ k f) (a b : ℝ)
    (hs : ∀ x, x ∉ Set.Icc a b → f x = 0) : ∃ M : ℝ, 1 ≤ M ∧ Tmp f M 1 k := by
  obtain ⟨M, hM1, hM⟩ := exists_bound_iteratedDeriv hf a b (fun j _ x hx => by
    rw [iteratedDeriv_eq_zero_of_vanish hs j hx]; simp)
  exact ⟨M, hM1, hf, fun j hj x => by simpa using hM j hj x⟩

lemma exists_tmp_of_vanish_real {f : ℝ → ℝ} {k : ℕ} (hf : ContDiff ℝ k f) (a b : ℝ)
    (hs : ∀ x, x ∉ Set.Icc a b → f x = 0) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ j ≤ k, ∀ x, ‖iteratedDeriv j f x‖ ≤ M :=
  exists_bound_iteratedDeriv hf a b (fun j _ x hx => by
    rw [iteratedDeriv_eq_zero_of_vanish hs j hx]; simp)

/-- `x ↦ c - st x` (as a complex function) has bounded derivatives, if `|c - st| ≤ 1`. -/
lemma exists_tmp_st (c : ℝ) (hc : ∀ x, |c - smoothTransition x| ≤ 1) (k : ℕ) :
    ∃ M : ℝ, 1 ≤ M ∧ Tmp (fun x => ((c - smoothTransition x : ℝ) : ℂ)) M 1 k := by
  have hcd : ContDiff ℝ k (fun x => ((c - smoothTransition x : ℝ) : ℂ)) :=
    contDiff_ofReal_comp (contDiff_const.sub contDiff_st)
  obtain ⟨M, hM1, hM⟩ := exists_bound_iteratedDeriv hcd 0 1 (fun j _ x hx => by
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [iteratedDeriv_zero, Complex.norm_real, Real.norm_eq_abs]; exact hc x
    · have hev : (fun x => ((c - smoothTransition x : ℝ) : ℂ)) =ᶠ[𝓝 x]
          fun _ => ((c - (if x < 0 then 0 else 1) : ℝ) : ℂ) := by
        simp only [Set.mem_Icc, not_and_or, not_le] at hx
        rcases hx with hx | hx
        · filter_upwards [Iio_mem_nhds hx] with y hy
          simp [smoothTransition.zero_of_nonpos (le_of_lt hy), hx]
        · filter_upwards [Ioi_mem_nhds hx] with y hy
          simp [smoothTransition.one_of_one_le (le_of_lt hy), (by linarith : ¬ x < 0)]
      rw [hev.iteratedDeriv_eq, iteratedDeriv_const, ite_eq_right (Nat.pos_iff_ne_zero.mp hj)]
      simp)
  exact ⟨M, hM1, hcd, fun j hj x => by simpa using hM j hj x⟩

lemma st_abs_le (x : ℝ) : |smoothTransition x| ≤ 1 := by
  rw [abs_of_nonneg (smoothTransition.nonneg x)]; exact smoothTransition.le_one x

lemma one_sub_st_abs_le (x : ℝ) : |1 - smoothTransition x| ≤ 1 := by
  have h1 := smoothTransition.nonneg x
  have h2 := smoothTransition.le_one x
  rw [abs_le]; constructor <;> linarith

/-- `iteratedDeriv` of `t ↦ exp(c t)`. -/
lemma iteratedDeriv_expMul (c : ℂ) (i : ℕ) :
    iteratedDeriv i (fun t : ℝ => Complex.exp (c * t)) =
      fun t : ℝ => c ^ i * Complex.exp (c * (t : ℂ)) := by
  induction i with
  | zero => funext t; simp
  | succ i ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have h : HasDerivAt (fun t : ℝ => c ^ i * Complex.exp (c * t))
        (c ^ i * (Complex.exp (c * t) * (c * 1))) t :=
      (((hasDerivAt_id t).ofReal_comp.const_mul c).cexp).const_mul (c ^ i)
    rw [h.deriv]
    ring

lemma contDiff_expMul (c : ℂ) {n : ℕ} : ContDiff ℝ n (fun t : ℝ => Complex.exp (c * t)) :=
  Complex.contDiff_exp.comp (contDiff_const.mul (contDiff_ofReal_comp contDiff_id))

/-- `t ↦ exp(i r t)` has `‖·^{(j)}‖ = |r|^j`. -/
lemma tmp_expI (r : ℝ) (k : ℕ) :
    Tmp (fun t : ℝ => Complex.exp (((r * t : ℝ) : ℂ) * Complex.I)) 1 |r| k := by
  have hfun : (fun t : ℝ => Complex.exp (((r * t : ℝ) : ℂ) * Complex.I)) =
      fun t : ℝ => Complex.exp ((r * Complex.I) * t) := by
    funext t; push_cast; ring_nf
  rw [hfun]
  refine ⟨contDiff_expMul _, fun j _ x => ?_⟩
  rw [iteratedDeriv_expMul, norm_mul, norm_pow]
  have h1 : ‖(r : ℂ) * Complex.I‖ = |r| := by simp
  have h2 : ‖Complex.exp ((r * Complex.I) * (x : ℂ))‖ = 1 := by
    rw [show (r : ℂ) * Complex.I * (x : ℂ) = ((r * x : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [h1, h2]; simp

/-! ### `chiCut`, `logCut` -/

lemma chiCut_nonneg (x : ℝ) : 0 ≤ chiCut x :=
  mul_nonneg (smoothTransition.nonneg _) (by linarith [smoothTransition.le_one (x / 8 - 1)])

lemma chiCut_le_one (x : ℝ) : chiCut x ≤ 1 := by
  unfold chiCut
  have h1 := smoothTransition.nonneg (8 * x - 1)
  have h2 := smoothTransition.le_one (8 * x - 1)
  have h3 := smoothTransition.nonneg (x / 8 - 1)
  have h4 := smoothTransition.le_one (x / 8 - 1)
  nlinarith

lemma chiCut_eq_one {x : ℝ} (hx : x ∈ Set.Icc (1/4 : ℝ) 8) : chiCut x = 1 := by
  obtain ⟨h1, h2⟩ := hx
  unfold chiCut
  rw [smoothTransition.one_of_one_le (by linarith), smoothTransition.zero_of_nonpos (by linarith)]
  ring

lemma chiCut_eq_zero {x : ℝ} (hx : x ∉ Set.Icc (1/8 : ℝ) 16) : chiCut x = 0 := by
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  unfold chiCut
  rcases hx with hx | hx
  · rw [smoothTransition.zero_of_nonpos (by linarith)]; ring
  · rw [smoothTransition.one_of_one_le (x := x / 8 - 1) (by linarith)]; ring

lemma chiCut_eq_zero_of_le {x : ℝ} (hx : x ≤ 1 / 8) : chiCut x = 0 := by
  unfold chiCut
  rw [smoothTransition.zero_of_nonpos (by linarith)]; ring

lemma contDiff_chiCut {n : ℕ} : ContDiff ℝ n chiCut :=
  (contDiff_st.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)).mul
    (contDiff_const.sub (contDiff_st.comp ((contDiff_id.div_const _).sub contDiff_const)))

lemma logCut_arg_pos (x : ℝ) : 0 < x * chiCut x + (1 - chiCut x) := by
  have h0 := chiCut_nonneg x
  have h1 := chiCut_le_one x
  by_cases hx : x ≤ 1 / 8
  · rw [chiCut_eq_zero_of_le hx]; norm_num
  · push Not at hx
    rcases eq_or_lt_of_le h1 with h | h
    · rw [h]; linarith
    · nlinarith

lemma contDiff_logCut {n : ℕ} : ContDiff ℝ n logCut :=
  ((contDiff_id.mul contDiff_chiCut).add (contDiff_const.sub contDiff_chiCut)).log
    (fun x => (logCut_arg_pos x).ne')

lemma logCut_eq {x : ℝ} (hx : x ∈ Set.Icc (1/4 : ℝ) 8) : logCut x = Real.log x := by
  unfold logCut; rw [chiCut_eq_one hx]; ring_nf

lemma logCut_eq_zero {x : ℝ} (hx : x ∉ Set.Icc (1/8 : ℝ) 16) : logCut x = 0 := by
  unfold logCut; rw [chiCut_eq_zero hx]; simp

/-- Bounds for the derivatives of `uPow τ` (Faà di Bruno). -/
lemma tmp_uPow (k : ℕ) : ∃ c : ℝ, 1 ≤ c ∧ ∀ τ : ℝ, Tmp (uPow τ) 1 (c * (1 + |τ|)) k := by
  obtain ⟨ML, hML1, hML⟩ := exists_tmp_of_vanish_real (contDiff_logCut (n := k)) (1/8) 16
    (fun x hx => logCut_eq_zero hx)
  refine ⟨(k + 1) * ML, by nlinarith, fun τ => ?_⟩
  set g : ℝ → ℂ := fun t : ℝ => Complex.exp (((τ : ℂ) * Complex.I) * t) with hg
  have hfun : uPow τ = g ∘ logCut := by
    funext x; simp only [uPow, hg, Function.comp]; push_cast; ring_nf
  have hgc : ContDiff ℝ k g := contDiff_expMul _
  refine ⟨hfun ▸ hgc.comp contDiff_logCut, fun j hj x => ?_⟩
  rw [hfun, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have hb := norm_iteratedFDeriv_comp_le (n := j) (N := k) hgc contDiff_logCut
    (by exact_mod_cast hj) x (C := (1 + |τ|) ^ j) (D := ML)
    (fun i hi => by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hg, iteratedDeriv_expMul, norm_mul,
        norm_pow]
      have h1 : ‖(τ : ℂ) * Complex.I‖ = |τ| := by simp
      have h2 : ‖Complex.exp ((τ : ℂ) * Complex.I * ((logCut x : ℝ) : ℂ))‖ = 1 := by
        rw [show (τ : ℂ) * Complex.I * ((logCut x : ℝ) : ℂ) =
          ((τ * logCut x : ℝ) : ℂ) * Complex.I by push_cast; ring]
        exact Complex.norm_exp_ofReal_mul_I _
      rw [h1, h2, mul_one]
      calc |τ| ^ i ≤ (1 + |τ|) ^ i := pow_le_pow_left₀ (abs_nonneg τ) (by linarith) i
        _ ≤ (1 + |τ|) ^ j := pow_le_pow_right₀ (by linarith [abs_nonneg τ]) hi)
    (fun i hi1 hi2 => by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      exact (hML i (hi2.trans hj) x).trans (le_self_pow₀ hML1 (by omega)))
  refine hb.trans ?_
  have hfac : (j.factorial : ℝ) ≤ ((k : ℝ) + 1) ^ j := by
    have h1 : j.factorial ≤ j ^ j := Nat.factorial_le_pow j
    have h2 : j ^ j ≤ (k + 1) ^ j := Nat.pow_le_pow_left (by omega) j
    exact_mod_cast h1.trans h2
  have hτ : 0 ≤ 1 + |τ| := by linarith [abs_nonneg τ]
  calc (j.factorial : ℝ) * (1 + |τ|) ^ j * ML ^ j ≤ ((k : ℝ) + 1) ^ j * (1 + |τ|) ^ j * ML ^ j := by
        gcongr
    _ = 1 * ((k + 1) * ML * (1 + |τ|)) ^ j := by rw [mul_pow, mul_pow]; ring

/-! ### Fourier transforms -/

lemma fourierR_eq_fourier (f : ℝ → ℂ) : fourierR f = 𝓕 f := by
  funext ξ
  rw [fourierR, Real.fourier_real_eq_integral_exp_smul]
  congr 1
  ext x
  rw [smul_eq_mul]
  congr 2
  push_cast
  ring

/-- `∫ ‖h‖ ≤ (3/2) M` for `h` bounded by `M` and supported in `[1/2, 2]`. -/
lemma integral_norm_le {h : ℝ → ℂ} {M : ℝ} (hb : ∀ x, ‖h x‖ ≤ M)
    (hs : ∀ x, x ∉ Set.Icc (1/2 : ℝ) 2 → h x = 0) : ∫ x, ‖h x‖ ≤ 3 / 2 * M := by
  have hle : ∀ x, ‖h x‖ ≤ Set.indicator (Set.Icc (1/2 : ℝ) 2) (fun _ => M) x := by
    intro x
    by_cases hx : x ∈ Set.Icc (1/2 : ℝ) 2
    · rw [Set.indicator_of_mem hx]; exact hb x
    · rw [Set.indicator_of_notMem hx, hs x hx]; simp
  have hint : Integrable (Set.indicator (Set.Icc (1/2 : ℝ) 2) (fun _ => M)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp))
  calc ∫ x, ‖h x‖ ≤ ∫ x, Set.indicator (Set.Icc (1/2 : ℝ) 2) (fun _ => M) x :=
        integral_mono_of_nonneg (Eventually.of_forall (fun x => norm_nonneg _)) hint
          (Eventually.of_forall hle)
    _ = 3 / 2 * M := by
        rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le (by norm_num)]
        simp only [smul_eq_mul]; norm_num

lemma hasCompactSupport_of_vanish {h : ℝ → ℂ} {a b : ℝ}
    (hs : ∀ x, x ∉ Set.Icc a b → h x = 0) : HasCompactSupport h :=
  HasCompactSupport.intro isCompact_Icc hs

/-- Derivative bounds for `ψ̂` when `‖ψ‖ ≤ 1` and `ψ` is continuous, supported in `[1/2,2]`. -/
lemma tmp_fourier {ψ : ℝ → ℂ} (hc : Continuous ψ) (hb : ∀ x, ‖ψ x‖ ≤ 1)
    (hs : ∀ x, x ∉ Set.Icc (1/2 : ℝ) 2 → ψ x = 0) (k : ℕ) :
    Tmp (𝓕 ψ) (3 / 2) (4 * π) k := by
  have hint : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n • ψ x) := fun n =>
    ((continuous_pow n).smul hc).integrable_of_hasCompactSupport
      (hasCompactSupport_of_vanish (a := 1/2) (b := 2) (fun x hx => by simp [hs x hx]))
  have hint' : ∀ n : ℕ, Integrable (fun x : ℝ => ‖x‖ ^ n * ‖ψ x‖) := fun n => by
    refine ((hint n).norm).congr (Eventually.of_forall (fun x => ?_))
    simp
  have hcd : ContDiff ℝ (k : ℕ∞) (𝓕 ψ) := Real.contDiff_fourier (fun n _ => hint' n)
  refine ⟨by exact_mod_cast hcd, fun j hj ξ => ?_⟩
  rw [Real.iteratedDeriv_fourier (N := (k : ℕ∞)) (fun n _ => hint n) (by exact_mod_cast hj)]
  refine (Real.norm_fourier_le_integral_norm _ ξ).trans ?_
  have := integral_norm_le (h := fun x : ℝ => (-2 * π * Complex.I * x) ^ j • ψ x)
    (M := (4 * π) ^ j) (fun x => ?_) (fun x hx => by simp [hs x hx])
  · exact this
  · by_cases hx : x ∈ Set.Icc (1/2 : ℝ) 2
    · rw [norm_smul, norm_pow]
      have h1 : ‖-2 * (π : ℂ) * Complex.I * (x : ℂ)‖ = 2 * π * |x| := by
        simp [abs_of_pos Real.pi_pos]
      rw [h1]
      have hx2 : |x| ≤ 2 := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
      calc (2 * π * |x|) ^ j * ‖ψ x‖ ≤ (2 * π * |x|) ^ j * 1 :=
            mul_le_mul_of_nonneg_left (hb x) (by positivity)
        _ ≤ (4 * π) ^ j := by
            rw [mul_one]
            exact pow_le_pow_left₀ (by positivity) (by nlinarith [Real.pi_pos]) j
    · rw [hs x hx]; simp; positivity

/-! ### `dyBump`, `topCut` -/

lemma dyBump_eq_zero_out {y : ℝ} (hy : y ∉ Set.Icc (1/2 : ℝ) 2) : dyBump y = 0 := by
  simp only [Set.mem_Icc, not_and_or, not_le] at hy
  unfold dyBump
  rcases hy with hy | hy
  · rw [smoothTransition.zero_of_nonpos (x := 2 * y - 1) (by linarith),
      smoothTransition.zero_of_nonpos (x := y - 1) (by linarith)]; ring
  · rw [smoothTransition.one_of_one_le (x := 2 * y - 1) (by linarith),
      smoothTransition.one_of_one_le (x := y - 1) (by linarith)]; ring

lemma dyBump_nonneg (y : ℝ) : 0 ≤ dyBump y := by
  unfold dyBump
  rcases le_or_gt 0 y with hy | hy
  · linarith [smoothTransition.monotone (show y - 1 ≤ 2 * y - 1 by linarith)]
  · rw [smoothTransition.zero_of_nonpos (x := 2 * y - 1) (by linarith),
      smoothTransition.zero_of_nonpos (x := y - 1) (by linarith)]; norm_num

lemma dyBump_le_one (y : ℝ) : dyBump y ≤ 1 := by
  unfold dyBump
  linarith [smoothTransition.le_one (2 * y - 1), smoothTransition.nonneg (y - 1)]

lemma topCut_nonneg (K ν x : ℝ) : 0 ≤ topCut K ν x := by
  unfold topCut; linarith [smoothTransition.le_one ((x - (1 - ν) * K) / (ν * K))]

lemma topCut_le_one (K ν x : ℝ) : topCut K ν x ≤ 1 := by
  unfold topCut; linarith [smoothTransition.nonneg ((x - (1 - ν) * K) / (ν * K))]

lemma contDiff_dyBump {n : ℕ} : ContDiff ℝ n dyBump :=
  (contDiff_st.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)).sub
    (contDiff_st.comp (contDiff_id.sub contDiff_const))

end Tempered

open Tempered

theorem temperedOn_mono_k {f : ℝ → ℂ} {P : ℝ} {k k' : ℕ} {a b : ℝ}
    (h : TemperedOn f P k a b) (hk : k' ≤ k) : TemperedOn f P k' a b :=
  ⟨h.1.of_le (by exact_mod_cast hk), h.2.1, fun j hj x => h.2.2 j (hj.trans hk) x⟩

theorem temperedOn_mono_P {f : ℝ → ℂ} {P P' : ℝ} {k : ℕ} {a b : ℝ}
    (h : TemperedOn f P k a b) (hP : 0 ≤ P) (hPP : P ≤ P') : TemperedOn f P' k a b :=
  ⟨h.1, h.2.1, fun j hj x => (h.2.2 j hj x).trans (pow_le_pow_left₀ hP hPP j)⟩

/-- `|ψ̂(ξ)| ≤ 3/2` for `ψ` bounded by `1` and supported in `[1/2, 2]`. -/
theorem norm_fourierR_le {ψ : ℝ → ℂ} {P : ℝ} {k : ℕ} (hψ : TemperedOn ψ P k (1/2) 2)
    (ξ : ℝ) : ‖fourierR ψ ξ‖ ≤ 3 / 2 := by
  rw [fourierR_eq_fourier]
  refine (Real.norm_fourier_le_integral_norm _ ξ).trans ?_
  have := integral_norm_le (h := ψ) (M := 1)
    (fun x => by simpa using hψ.2.2 0 (Nat.zero_le _) x) hψ.2.1
  linarith

/-- `uPow τ x = x^{iτ}` on `[1/4, 8]`. -/
theorem uPow_eq (τ : ℝ) {x : ℝ} (hx : x ∈ Set.Icc (1/4 : ℝ) 8) :
    uPow τ x = Complex.exp (((τ * Real.log x : ℝ) : ℂ) * Complex.I) := by
  unfold uPow; rw [logCut_eq hx]

theorem norm_uPow (τ x : ℝ) : ‖uPow τ x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- The weight `V_τ = φ · x^{iτ}` fed to the mean-value theorem is tempered with
`P_V = c₀ P (1 + |τ|)`. -/
theorem V_tempered (k : ℕ) : ∃ c₀ : ℝ, 1 ≤ c₀ ∧ ∀ (φ : ℝ → ℂ) (P τ : ℝ), 1 ≤ P →
    TemperedOn φ P k (1/2) 2 →
    TemperedOn (fun x => φ x * uPow τ x) (c₀ * P * (1 + |τ|)) k (1/8) 8 := by
  obtain ⟨c, hc1, hc⟩ := tmp_uPow k
  refine ⟨1 + c, by linarith, fun φ P τ hP hφ => ?_⟩
  have hm := tmp_mul (tmp_of_temperedOn hφ) (hc τ)
  have hτ : 0 ≤ |τ| := abs_nonneg τ
  refine ⟨hm.1, fun x hx => ?_, fun j hj x => ?_⟩
  · have : x ∉ Set.Icc (1/2 : ℝ) 2 := fun h => hx ⟨by linarith [h.1], by linarith [h.2]⟩
    simp [hφ.2.1 x this]
  · refine (hm.2 j hj x).trans ?_
    simp only [one_mul]
    have h0 : 0 ≤ P + c * (1 + |τ|) := by nlinarith
    apply pow_le_pow_left₀ h0
    have h1 : P ≤ P * (1 + |τ|) := by nlinarith
    have h2 : c * (1 + |τ|) ≤ c * P * (1 + |τ|) := by
      have : c * (1 + |τ|) * 1 ≤ c * (1 + |τ|) * P :=
        mul_le_mul_of_nonneg_left hP (by positivity)
      linarith
    nlinarith

/-- The coupled weight `s ↦ s ψ̂(Y₁ s) e(Y₂ s)`, cut off smoothly to `[1/8, 16]` and
normalised by `cn`, is tempered with `P_F = c (1 + |Y₁| + |Y₂|)`. -/
theorem blockF_tempered (kF : ℕ) : ∃ c : ℝ, 1 ≤ c ∧ ∃ cn : ℝ, 0 < cn ∧
    ∀ (ψ : ℝ → ℂ) (P Y₁ Y₂ : ℝ), TemperedOn ψ P 0 (1/2) 2 →
    ∃ F : ℝ → ℂ, TemperedOn F (c * (1 + |Y₁| + |Y₂|)) kF (1/8) 16 ∧
      ∀ s ∈ Set.Icc (1/4 : ℝ) 8,
        F s * cn = (s : ℂ) * fourierR ψ (Y₁ * s) *
          Complex.exp (2 * π * Complex.I * ((Y₂ * s : ℝ) : ℂ)) := by
  have hχc : ContDiff ℝ kF (fun s : ℝ => ((s * chiCut s : ℝ) : ℂ)) :=
    contDiff_ofReal_comp (contDiff_id.mul contDiff_chiCut)
  obtain ⟨Aχ, hAχ, hχ⟩ := exists_tmp_of_vanish hχc (1/8) 16
    (fun x hx => by simp [chiCut_eq_zero hx])
  have hcn : 0 < Aχ * (3 / 2) * 1 := by positivity
  refine ⟨4 * π, by nlinarith [Real.pi_gt_three], Aχ * (3 / 2) * 1, hcn,
    fun ψ P Y₁ Y₂ hψ => ?_⟩
  have hψc : Continuous ψ := hψ.1.continuous
  have hψb : ∀ x, ‖ψ x‖ ≤ 1 := fun x => by simpa using hψ.2.2 0 le_rfl x
  have hF := tmp_fourier hψc hψb hψ.2.1 kF
  have hF' : Tmp (fun s => fourierR ψ (Y₁ * s)) (3 / 2) (|Y₁| * (4 * π)) kF := by
    have := tmp_comp_affine hF Y₁ 0
    simpa [fourierR_eq_fourier] using this
  have hE : Tmp (fun s : ℝ => Complex.exp (2 * π * Complex.I * ((Y₂ * s : ℝ) : ℂ))) 1
      |2 * π * Y₂| kF := by
    have hfun : (fun s : ℝ => Complex.exp (2 * π * Complex.I * ((Y₂ * s : ℝ) : ℂ))) =
        fun t : ℝ => Complex.exp ((((2 * π * Y₂) * t : ℝ) : ℂ) * Complex.I) := by
      funext t; push_cast; ring_nf
    rw [hfun]; exact tmp_expI _ _
  have hprod := tmp_mul (tmp_mul hχ hF') hE
  refine ⟨fun x => ((x * chiCut x : ℝ) : ℂ) * fourierR ψ (Y₁ * x) *
      Complex.exp (2 * π * Complex.I * ((Y₂ * x : ℝ) : ℂ)) / ((Aχ * (3 / 2) * 1 : ℝ) : ℂ),
    ?_, ?_⟩
  · have ht := temperedOn_of_tmp hprod hcn (a := 1/8) (b := 16)
      (fun x hx => by simp [chiCut_eq_zero hx])
    refine temperedOn_mono_P ht (by positivity) ?_
    have hpi := Real.pi_gt_three
    have h1 : |2 * π * Y₂| = 2 * π * |Y₂| := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
    rw [h1]
    nlinarith [abs_nonneg Y₁, abs_nonneg Y₂]
  · intro s hs
    have hne : ((Aχ * (3 / 2) * 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hcn.ne'
    simp only
    rw [div_mul_cancel₀ _ hne, chiCut_eq_one hs]
    push_cast; ring

/-- The pieces of the smoothed cutoffs are tempered with `P = c/ν`. -/
theorem piece_tempered (k : ℕ) : ∃ c : ℝ, 1 ≤ c ∧ ∀ K ν D : ℝ, 0 < ν → ν ≤ 1 → 0 < K →
    0 < D → D ≤ 2 * K → TemperedOn (piece K ν D) (c / ν) k (1/2) 2 := by
  obtain ⟨Aβ, hAβ, hβ⟩ := exists_tmp_of_vanish
    (contDiff_ofReal_comp (contDiff_dyBump (n := k))) (1/2) 2
    (fun x hx => by simp [dyBump_eq_zero_out hx])
  obtain ⟨M, hM, hst⟩ := exists_tmp_st 1 one_sub_st_abs_le k
  refine ⟨3 * (Aβ * M), by nlinarith, fun K ν D hν hν1 hK hD hDK => ?_⟩
  set a : ℝ := D / (ν * K) with ha
  set b : ℝ := -((1 - ν) * K) / (ν * K) with hb
  have hpiece : piece K ν D =
      fun y => ((dyBump y : ℝ) : ℂ) * ((1 - smoothTransition (a * y + b) : ℝ) : ℂ) := by
    funext y
    simp only [piece, topCut]
    rw [show (D * y - (1 - ν) * K) / (ν * K) = a * y + b by rw [ha, hb]; ring]
    push_cast; ring
  have hprod := tmp_mul hβ (tmp_comp_affine hst a b)
  have ha0 : 0 ≤ a := by positivity
  have ha2 : a ≤ 2 / ν := by
    rw [ha, div_le_div_iff₀ (by positivity) hν]
    nlinarith
  have hAM : 1 ≤ Aβ * M := by nlinarith
  rw [hpiece]
  refine ⟨hprod.1, fun x hx => by simp [dyBump_eq_zero_out hx], fun j hj x => ?_⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp only [iteratedDeriv_zero, pow_zero]
    rw [← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs, abs_le]
    have h1 := dyBump_nonneg x
    have h2 := dyBump_le_one x
    have h3 := smoothTransition.nonneg (a * x + b)
    have h4 := smoothTransition.le_one (a * x + b)
    constructor <;> nlinarith
  · refine (hprod.2 j hj x).trans ?_
    rw [abs_of_nonneg ha0, mul_one]
    have hB : 1 + a ≤ 3 / ν := by
      have : 1 ≤ 1 / ν := by rw [le_div_iff₀ hν]; linarith
      have h3 : 3 / ν = 1 / ν + 2 / ν := by ring
      linarith
    calc Aβ * M * (1 + a) ^ j ≤ (Aβ * M) ^ j * (1 + a) ^ j :=
          mul_le_mul_of_nonneg_right (le_self_pow₀ hAM (by omega)) (by positivity)
      _ = (Aβ * M * (1 + a)) ^ j := (mul_pow (Aβ * M) (1 + a) j).symm
      _ ≤ (3 * (Aβ * M) / ν) ^ j := by
          apply pow_le_pow_left₀ (by positivity)
          rw [show 3 * (Aβ * M) / ν = Aβ * M * (3 / ν) by ring]
          exact mul_le_mul_of_nonneg_left hB (by positivity)

end Level

end MobiusDeterminant
