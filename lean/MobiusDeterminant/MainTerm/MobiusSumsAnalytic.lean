import MobiusDeterminant.Basic

/-!
# Analytic helper lemmas for the Möbius sums

* the weight `ep c x = exp(-c √(log x))` and its elementary properties;
* summability of `ep b n / n` and tail bounds;
* discrete summation by parts (finite and infinite);
* elementary inequalities for `x^{-σ} - y^{-σ}`;
* the input from the Riemann zeta function:
  `(∑ μ(n) n^{-1-s}) / s → 1` as `s → 0⁺`.
-/

open Finset Real Filter Topology
open scoped ArithmeticFunction.Moebius

namespace MobiusDeterminant
namespace MobiusSums

/-- `ep c x = exp(-c √(log x))`. -/
noncomputable def ep (c x : ℝ) : ℝ := Real.exp (-c * Real.sqrt (Real.log x))

lemma ep_pos (c x : ℝ) : 0 < ep c x := Real.exp_pos _

lemma ep_le_one {c : ℝ} (hc : 0 ≤ c) (x : ℝ) : ep c x ≤ 1 := by
  unfold ep
  rw [Real.exp_le_one_iff]
  have := Real.sqrt_nonneg (Real.log x)
  nlinarith

lemma ep_anti {c x y : ℝ} (hc : 0 ≤ c) (hy : 0 < y) (hxy : y ≤ x) : ep c x ≤ ep c y := by
  unfold ep
  apply Real.exp_le_exp.mpr
  have : Real.sqrt (Real.log y) ≤ Real.sqrt (Real.log x) :=
    Real.sqrt_le_sqrt (Real.log_le_log hy hxy)
  nlinarith

lemma ep_mono_c {a b : ℝ} (hab : a ≤ b) (x : ℝ) : ep b x ≤ ep a x := by
  unfold ep
  apply Real.exp_le_exp.mpr
  have := Real.sqrt_nonneg (Real.log x)
  nlinarith

lemma ep_add (a b x : ℝ) : ep (a + b) x = ep a x * ep b x := by
  unfold ep; rw [← Real.exp_add]; ring_nf

lemma ep_half (a x : ℝ) : ep a x = ep (a / 2) x * ep (a / 2) x := by
  rw [← ep_add]; ring_nf

/-- Passing from `N` to `z` when `log z ≤ log N + 1`. -/
lemma ep_shift {b N z : ℝ} (hb : 0 ≤ b) (hN : 1 ≤ N) (hz : Real.log z ≤ Real.log N + 1) :
    ep b N ≤ Real.exp b * ep b z := by
  unfold ep
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hL : 0 ≤ Real.log N := Real.log_nonneg hN
  have h1 : Real.sqrt (Real.log z) ≤ Real.sqrt (Real.log N + 1) := Real.sqrt_le_sqrt hz
  have h2 : Real.sqrt (Real.log N + 1) ≤ Real.sqrt (Real.log N) + 1 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have := Real.sq_sqrt hL
    have := Real.sqrt_nonneg (Real.log N)
    nlinarith
  nlinarith

/-! ## Summability of `ep b n / n` -/

lemma exp_neg_le_of_pos {x : ℝ} (hx : 0 < x) : Real.exp (-x) ≤ 24 / x ^ 4 := by
  have h := Real.pow_div_factorial_le_exp x hx.le 4
  have h4 : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [h4] at h
  have hx4 : 0 < x ^ 4 := by positivity
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos x) hx4]
  linarith

lemma summable_exp_neg_sqrt {b : ℝ} (hb : 0 < b) :
    Summable (fun k : ℕ => Real.exp (-b * Real.sqrt (k * Real.log 2))) := by
  rw [← summable_nat_add_iff 1]
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hsum : Summable (fun k : ℕ => (24 / (b ^ 4 * Real.log 2 ^ 2)) * (1 / ((k : ℝ) + 1) ^ 2)) := by
    apply Summable.mul_left
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    simpa using this
  refine Summable.of_nonneg_of_le (fun k => (Real.exp_pos _).le) (fun k => ?_) hsum
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hu : 0 < ((k + 1 : ℕ) : ℝ) * Real.log 2 := by push_cast; positivity
  have hx : 0 < b * Real.sqrt (((k + 1 : ℕ) : ℝ) * Real.log 2) := by
    have := Real.sqrt_pos.mpr hu
    positivity
  have h := exp_neg_le_of_pos hx
  rw [neg_mul]
  refine h.trans (le_of_eq ?_)
  have hs : Real.sqrt (((k + 1 : ℕ) : ℝ) * Real.log 2) ^ 4 = (((k : ℝ) + 1) * Real.log 2) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hu.le]
    push_cast; ring
  rw [mul_pow, hs]
  field_simp

lemma summable_ep_div {b : ℝ} (hb : 0 < b) : Summable (fun n : ℕ => ep b n / n) := by
  have hnn : ∀ n : ℕ, 0 ≤ ep b n / n := fun n => div_nonneg (ep_pos _ _).le (Nat.cast_nonneg _)
  rw [← summable_condensed_iff_of_nonneg hnn]
  · have : (fun k : ℕ => (2 : ℝ) ^ k * (ep b ((2 ^ k : ℕ) : ℝ) / ((2 ^ k : ℕ) : ℝ))) =
        fun k : ℕ => Real.exp (-b * Real.sqrt ((k : ℝ) * Real.log 2)) := by
      funext k
      push_cast
      rw [mul_div_cancel₀ _ (by positivity)]
      unfold ep
      rw [Real.log_pow]
    rw [this]
    exact summable_exp_neg_sqrt hb
  · intro m n hm hmn
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
    calc ep b n / n ≤ ep b m / n := by
          gcongr
          exact ep_anti hb.le hm' hmn'
      _ ≤ ep b m / m := by
          gcongr
          exact (ep_pos _ _).le

lemma tsum_tail_le {f : ℕ → ℝ} (hf : Summable f) (h0 : ∀ n, 0 ≤ f n) (N : ℕ) :
    ∑' i, f (i + N) ≤ ∑' i, f i := by
  rw [← hf.sum_add_tsum_nat_add N]
  have : 0 ≤ ∑ i ∈ range N, f i := sum_nonneg (fun i _ => h0 i)
  linarith

/-- Tail bound: `∑_{n ≥ N} ep b n / n ≤ K ep (b/2) N`. -/
lemma tail_ep_div {b : ℝ} (hb : 0 < b) : ∃ K > 0, ∀ N : ℕ, 1 ≤ N →
    ∑' i : ℕ, ep b ((i + N : ℕ) : ℝ) / ((i + N : ℕ) : ℝ) ≤ K * ep (b / 2) N := by
  have hb2 : 0 < b / 2 := half_pos hb
  have hs := summable_ep_div hb2
  have hnn : ∀ n : ℕ, 0 ≤ ep (b / 2) n / n := fun n => div_nonneg (ep_pos _ _).le (Nat.cast_nonneg _)
  set S := ∑' n : ℕ, ep (b / 2) n / n with hS
  have hS0 : 0 ≤ S := tsum_nonneg hnn
  refine ⟨S + 1, by linarith, fun N hN => ?_⟩
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs' : Summable (fun i : ℕ => ep (b / 2) ((i + N : ℕ) : ℝ) / ((i + N : ℕ) : ℝ)) :=
    (summable_nat_add_iff N).mpr hs
  have hpt : ∀ i : ℕ, ep b ((i + N : ℕ) : ℝ) / ((i + N : ℕ) : ℝ) ≤
      ep (b / 2) N * (ep (b / 2) ((i + N : ℕ) : ℝ) / ((i + N : ℕ) : ℝ)) := by
    intro i
    rw [ep_half b, mul_div_assoc]
    gcongr
    · exact div_nonneg (ep_pos _ _).le (Nat.cast_nonneg _)
    · apply ep_anti hb2.le (by linarith)
      push_cast; linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
  have hsb : Summable (fun i : ℕ => ep b ((i + N : ℕ) : ℝ) / ((i + N : ℕ) : ℝ)) :=
    Summable.of_nonneg_of_le (fun i => div_nonneg (ep_pos _ _).le (Nat.cast_nonneg _)) hpt
      (hs'.mul_left _)
  calc ∑' i : ℕ, ep b ((i + N : ℕ) : ℝ) / ((i + N : ℕ) : ℝ)
      ≤ ∑' i : ℕ, ep (b / 2) N * (ep (b / 2) ((i + N : ℕ) : ℝ) / ((i + N : ℕ) : ℝ)) :=
        hsb.tsum_le_tsum hpt (hs'.mul_left _)
    _ = ep (b / 2) N * ∑' i : ℕ, ep (b / 2) ((i + N : ℕ) : ℝ) / ((i + N : ℕ) : ℝ) :=
        tsum_mul_left
    _ ≤ ep (b / 2) N * S := by
        gcongr
        · exact (ep_pos _ _).le
        · exact tsum_tail_le (f := fun n : ℕ => ep (b / 2) n / n) hs hnn N
    _ ≤ (S + 1) * ep (b / 2) N := by
        have := ep_pos (b / 2) N
        nlinarith

lemma abs_tsum_le {f B : ℕ → ℝ} (hB : Summable B) (h : ∀ i, |f i| ≤ B i) :
    |∑' i, f i| ≤ ∑' i, B i := by
  have := tsum_of_norm_bounded (f := f) hB.hasSum (fun i => by simpa [Real.norm_eq_abs] using h i)
  simpa [Real.norm_eq_abs] using this

/-! ## Summation by parts -/

lemma sum_by_parts (a w : ℕ → ℝ) (N : ℕ) :
    ∑ i ∈ Icc 1 N, a i * w i = (∑ i ∈ Icc 1 N, a i) * w N +
      ∑ i ∈ range N, (∑ j ∈ Icc 1 i, a j) * (w i - w (i + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega),
      Finset.sum_range_succ, ih]
    ring

lemma sum_range_succ_eq_Icc (f : ℕ → ℝ) (N : ℕ) :
    ∑ i ∈ range (N + 1), f i = f 0 + ∑ i ∈ Icc 1 N, f i := by
  induction N with
  | zero => simp
  | succ N ih => rw [sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]; ring

lemma tsum_by_parts (a w : ℕ → ℝ) (ha0 : a 0 = 0)
    (hsum : Summable (fun n => a n * w n))
    (hv : Summable (fun i => (∑ j ∈ Icc 1 i, a j) * (w i - w (i + 1))))
    (hlim : Tendsto (fun N => (∑ j ∈ Icc 1 N, a j) * w N) atTop (𝓝 0)) :
    ∑' n, a n * w n = ∑' i, (∑ j ∈ Icc 1 i, a j) * (w i - w (i + 1)) := by
  have h1 : Tendsto (fun N => ∑ i ∈ range (N + 1), a i * w i) atTop (𝓝 (∑' n, a n * w n)) :=
    (hsum.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  have h2 := hlim.add hv.hasSum.tendsto_sum_nat
  rw [zero_add] at h2
  refine tendsto_nhds_unique h1 ?_
  convert h2 using 1
  funext N
  rw [sum_range_succ_eq_Icc, ha0, zero_mul, zero_add, sum_by_parts]

/-! ## Elementary inequalities -/

lemma inv_rpow_sub_le {x y σ : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hσ : 0 ≤ σ) :
    0 ≤ 1 / x ^ σ - 1 / y ^ σ ∧
      1 / x ^ σ - 1 / y ^ σ ≤ 1 / x ^ σ * (σ * (Real.log y - Real.log x)) := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hy, one_div, one_div, ← Real.exp_neg,
    ← Real.exp_neg]
  have hab : Real.log x * σ ≤ Real.log y * σ :=
    mul_le_mul_of_nonneg_right (Real.log_le_log hx hxy) hσ
  constructor
  · linarith [Real.exp_le_exp.mpr (neg_le_neg hab)]
  · have h1 : Real.exp (-(Real.log y * σ)) =
        Real.exp (-(Real.log x * σ)) * Real.exp (-(Real.log y * σ - Real.log x * σ)) := by
      rw [← Real.exp_add]; ring_nf
    have h2 := Real.one_sub_le_exp_neg (Real.log y * σ - Real.log x * σ)
    rw [h1]
    have h3 : 0 < Real.exp (-(Real.log x * σ)) := Real.exp_pos _
    have : σ * (Real.log y - Real.log x) = Real.log y * σ - Real.log x * σ := by ring
    rw [this]
    nlinarith

lemma log_succ_sub_log_le {x : ℝ} (hx : 0 < x) :
    0 ≤ Real.log (x + 1) - Real.log x ∧ Real.log (x + 1) - Real.log x ≤ 1 / x := by
  constructor
  · linarith [Real.log_le_log hx (by linarith : x ≤ x + 1)]
  · rw [← Real.log_div (by positivity) hx.ne']
    have := Real.log_le_sub_one_of_pos (show 0 < (x + 1) / x by positivity)
    have h2 : (x + 1) / x - 1 = 1 / x := by field_simp; ring
    linarith

/-! ## Input from the Riemann zeta function -/

/-- `ζ(σ) · ∑ μ(n) n^{-σ} = 1` for real `σ > 1`. -/
lemma zeta_mul_moebius_real {σ : ℝ} (hσ : 1 < σ) :
    (∑' n : ℕ, 1 / (n : ℝ) ^ σ) * (∑' n : ℕ, (μ n : ℝ) / (n : ℝ) ^ σ) = 1 := by
  have h := LSeries_one_mul_Lseries_moebius (s := (σ : ℂ)) (by simpa using hσ)
  have hσ0 : σ ≠ 0 := by linarith
  have e1 : LSeries 1 (σ : ℂ) = ((∑' n : ℕ, 1 / (n : ℝ) ^ σ : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum, LSeries]
    refine tsum_congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term, Real.zero_rpow hσ0]
    · rw [LSeries.term_of_ne_zero hn]
      push_cast
      rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
      simp
  have e2 : LSeries (fun n => ((μ n : ℤ) : ℂ)) (σ : ℂ) =
      ((∑' n : ℕ, (μ n : ℝ) / (n : ℝ) ^ σ : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum, LSeries]
    refine tsum_congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term, Real.zero_rpow hσ0]
    · rw [LSeries.term_of_ne_zero hn]
      push_cast
      rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
      simp
  rw [e1, e2] at h
  exact_mod_cast h

/-- The Dirichlet series `A(s) = ∑ μ(n) n^{-1-s}`. -/
noncomputable def Aser (s : ℝ) : ℝ := ∑' n : ℕ, (μ n : ℝ) / (n : ℝ) ^ (1 + s)

/-- `A(s)/s → 1` as `s → 0⁺` (from the simple pole of `ζ` at `1`). -/
lemma tendsto_Aser_div : Tendsto (fun s => Aser s / s) (𝓝[>] 0) (𝓝 1) := by
  have hmap : Tendsto (fun s : ℝ => 1 + s) (𝓝[>] 0) (𝓝[>] 1) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Tendsto (fun s : ℝ => 1 + s) (𝓝 0) (𝓝 (1 + 0)) :=
        (continuous_const.add continuous_id).tendsto 0
      rw [add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [Set.mem_Ioi] at hs ⊢
      linarith
  have h := (tendsto_sub_mul_tsum_nat_rpow.comp hmap).inv₀ one_ne_zero
  rw [inv_one] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [Set.mem_Ioi] at hs
  have hprod := zeta_mul_moebius_real (σ := 1 + s) (by linarith)
  simp only [Function.comp_apply, Aser]
  rw [add_sub_cancel_left]
  have hZ : (∑' n : ℕ, 1 / (n : ℝ) ^ (1 + s)) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hprod; exact zero_ne_one hprod
  field_simp
  linarith

lemma tendsto_Aser : Tendsto Aser (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun s : ℝ => s * (Aser s / s)) (𝓝[>] 0) (𝓝 (0 * 1)) :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).mul tendsto_Aser_div
  rw [zero_mul] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [Set.mem_Ioi] at hs
  field_simp

end MobiusSums
end MobiusDeterminant
