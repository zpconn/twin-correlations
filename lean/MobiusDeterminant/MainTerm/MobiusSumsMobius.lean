import MobiusDeterminant.MainTerm.MobiusSumsAnalytic

/-!
# From the PNT for `μ` to `∑_{n ≤ z} μ(n) log(z/n)/n = 1 + O(exp(-c √log z))`

* `M(N) = ∑_{n ≤ N} μ(n)`, `m(N) = ∑_{n ≤ N} μ(n)/n`;
* `|m(N)| ≤ C exp(-c √log N)` (`mf_bound`), using `∑ μ(n)/n = 0` which comes from
  `∑ μ(n) n^{-1-s} → 0` as `s → 0⁺`;
* `S₁(z) = ∑_{n ≤ z} μ(n) log(z/n)/n = 1 + O(exp(-c √log z))` (`S1_bound`), using
  `∑ m(i) log((i+1)/i) = 1`, which comes from `(∑ μ(n) n^{-1-s})/s → 1`.
-/

open Finset Real Filter Topology
open scoped ArithmeticFunction.Moebius

namespace MobiusDeterminant
namespace MobiusSums

/-- `M(N) = ∑_{n ≤ N} μ(n)`. -/
noncomputable def Mf (n : ℕ) : ℝ := ∑ i ∈ Icc 1 n, (μ i : ℝ)

/-- `m(N) = ∑_{n ≤ N} μ(n)/n`. -/
noncomputable def mf (n : ℕ) : ℝ := ∑ i ∈ Icc 1 n, (μ i : ℝ) / i

/-- `S₁(z) = ∑_{n ≤ z} μ(n) log(z/n)/n`. -/
noncomputable def S1 (z : ℝ) : ℝ := ∑ n ∈ Icc 1 ⌊z⌋₊, (μ n : ℝ) * Real.log (z / n) / n

lemma Mf_zero : Mf 0 = 0 := by simp [Mf]
lemma mf_zero : mf 0 = 0 := by simp [mf]

lemma abs_moebius_real_le (n : ℕ) : |(μ n : ℝ)| ≤ 1 := by
  have := ArithmeticFunction.abs_moebius_le_one (n := n)
  exact_mod_cast this

lemma abs_Mf_le (n : ℕ) : |Mf n| ≤ n := by
  unfold Mf
  calc |∑ i ∈ Icc 1 n, (μ i : ℝ)| ≤ ∑ i ∈ Icc 1 n, |(μ i : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Icc 1 n, (1 : ℝ) := sum_le_sum (fun i _ => abs_moebius_real_le i)
    _ = n := by simp

lemma Mf_bound (h : PNTMobius) :
    ∃ c > 0, ∃ C > 0, ∀ n : ℕ, 1 ≤ n → |Mf n| ≤ C * n * ep c n := by
  obtain ⟨c, hc, C, hC, hP⟩ := h
  refine ⟨c, hc, max C 1, by positivity, fun n hn => ?_⟩
  rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | h2
  · simp [Mf, ep]
  · have := hP n (by exact_mod_cast h2)
    rw [Nat.floor_natCast] at this
    calc |Mf n| ≤ C * n * ep c n := this
      _ ≤ max C 1 * n * ep c n := by
          have := ep_pos c n
          gcongr
          exact le_max_left _ _

/-! ## The bound for `m(N)` -/

/-- `u(i) = M(i) (1/i - 1/(i+1))`. -/
noncomputable def uM (i : ℕ) : ℝ := Mf i * (1 / (i : ℝ) - 1 / ((i + 1 : ℕ) : ℝ))

lemma mf_eq (N : ℕ) : mf N = Mf N * (1 / (N : ℝ)) + ∑ i ∈ range N, uM i := by
  have := sum_by_parts (fun i => (μ i : ℝ)) (fun i => 1 / (i : ℝ)) N
  unfold mf uM Mf
  rw [← this]
  exact sum_congr rfl (fun i _ => div_eq_mul_one_div _ _)

lemma abs_uM_le {c C₀ : ℝ} (hM : ∀ n : ℕ, 1 ≤ n → |Mf n| ≤ C₀ * n * ep c n) (hC₀ : 0 < C₀)
    (i : ℕ) : |uM i| ≤ C₀ * (ep c i / i) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [uM, Mf_zero]
  have hx : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hx0 : (0 : ℝ) < i := by linarith
  have hd : 1 / (i : ℝ) - 1 / ((i + 1 : ℕ) : ℝ) = 1 / ((i : ℝ) * ((i : ℝ) + 1)) := by
    push_cast; field_simp; ring
  rw [uM, hd, abs_mul, abs_of_pos (show (0 : ℝ) < 1 / ((i : ℝ) * ((i : ℝ) + 1)) by positivity)]
  have he := ep_pos c i
  calc |Mf i| * (1 / ((i : ℝ) * ((i : ℝ) + 1))) ≤
      C₀ * i * ep c i * (1 / ((i : ℝ) * ((i : ℝ) + 1))) := by
        gcongr; exact hM i hi
    _ = C₀ * (ep c i / ((i : ℝ) + 1)) := by field_simp
    _ ≤ C₀ * (ep c i / i) := by gcongr; linarith

/-- `∑ M(i)(1/i - 1/(i+1)) = 0`, i.e. `∑ μ(n)/n = 0`. -/
lemma tsum_uM_eq_zero {c C₀ : ℝ} (hc : 0 < c) (hC₀ : 0 < C₀)
    (hM : ∀ n : ℕ, 1 ≤ n → |Mf n| ≤ C₀ * n * ep c n) : ∑' i, uM i = 0 := by
  set fS : ℝ → ℕ → ℝ := fun s i =>
    Mf i * (1 / (i : ℝ) ^ (1 + s) - 1 / ((i + 1 : ℕ) : ℝ) ^ (1 + s)) with hfS
  set bound : ℕ → ℝ := fun i => 2 * C₀ * (ep c i / i) with hbound
  have hbs : Summable bound := (summable_ep_div hc).mul_left (2 * C₀)
  have hfb : ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ i : ℕ, |fS s i| ≤ bound i := by
    intro s hs hs1 i
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [fS, bound, Mf_zero]
    have hx : (1 : ℝ) ≤ i := by exact_mod_cast hi
    have hx0 : (0 : ℝ) < i := by linarith
    obtain ⟨hD0, hD1⟩ := inv_rpow_sub_le hx0 (show (i : ℝ) ≤ (i : ℝ) + 1 by linarith)
      (show (0 : ℝ) ≤ 1 + s by linarith)
    obtain ⟨hl0, hl⟩ := log_succ_sub_log_le hx0
    have hpow : 1 / (i : ℝ) ^ (1 + s) ≤ 1 / (i : ℝ) := by
      gcongr
      exact Real.self_le_rpow_of_one_le hx (by linarith)
    have hD2 : 1 / (i : ℝ) ^ (1 + s) - 1 / ((i : ℝ) + 1) ^ (1 + s) ≤ 2 / (i : ℝ) ^ 2 := by
      calc _ ≤ 1 / (i : ℝ) ^ (1 + s) * ((1 + s) * (Real.log ((i : ℝ) + 1) - Real.log i)) := hD1
        _ ≤ 1 / (i : ℝ) * (2 * (1 / (i : ℝ))) := by
          apply mul_le_mul hpow _ (by positivity) (by positivity)
          apply mul_le_mul (by linarith) hl hl0 (by norm_num)
        _ = 2 / (i : ℝ) ^ 2 := by ring
    simp only [fS, bound]
    push_cast
    rw [abs_mul, abs_of_nonneg hD0]
    have he := ep_pos c i
    calc |Mf i| * (1 / (i : ℝ) ^ (1 + s) - 1 / ((i : ℝ) + 1) ^ (1 + s)) ≤
        (C₀ * i * ep c i) * (2 / (i : ℝ) ^ 2) :=
          mul_le_mul (hM i hi) hD2 hD0 (by positivity)
      _ = 2 * C₀ * (ep c i / i) := by field_simp
  have hA : ∀ s : ℝ, 0 < s → s ≤ 1 → Aser s = ∑' i, fS s i := by
    intro s hs hs1
    have hsum0 : Summable (fun n : ℕ => (μ n : ℝ) * (1 / (n : ℝ) ^ (1 + s))) := by
      refine Summable.of_norm_bounded
        (Real.summable_one_div_nat_rpow.mpr (by linarith : (1 : ℝ) < 1 + s)) (fun n => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : 0 ≤ 1 / (n : ℝ) ^ (1 + s) := by positivity
      rw [abs_of_nonneg h1]
      calc |(μ n : ℝ)| * (1 / (n : ℝ) ^ (1 + s)) ≤ 1 * (1 / (n : ℝ) ^ (1 + s)) :=
            mul_le_mul_of_nonneg_right (abs_moebius_real_le n) h1
        _ = _ := one_mul _
    have hv : Summable (fS s) :=
      Summable.of_norm_bounded hbs (fun i => by rw [Real.norm_eq_abs]; exact hfb s hs hs1 i)
    have hlim : Tendsto (fun N : ℕ => (∑ j ∈ Icc 1 N, (μ j : ℝ)) * (1 / (N : ℝ) ^ (1 + s)))
        atTop (𝓝 0) := by
      have ht : Tendsto (fun N : ℕ => 1 / (N : ℝ) ^ s) atTop (𝓝 0) := by
        have := (tendsto_rpow_neg_atTop hs).comp tendsto_natCast_atTop_atTop
        refine this.congr (fun N => ?_)
        simp [Function.comp_apply, Real.rpow_neg (Nat.cast_nonneg N)]
      refine squeeze_zero_norm (fun N => ?_) ht
      rcases Nat.eq_zero_or_pos N with rfl | hN
      · simp; positivity
      have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (N : ℝ) ^ (1 + s))]
      have hMN := abs_Mf_le N
      unfold Mf at hMN
      calc |∑ j ∈ Icc 1 N, (μ j : ℝ)| * (1 / (N : ℝ) ^ (1 + s)) ≤
          N * (1 / (N : ℝ) ^ (1 + s)) := by gcongr
        _ = 1 / (N : ℝ) ^ s := by
          rw [Real.rpow_add hN0, Real.rpow_one]
          field_simp
    have := tsum_by_parts (fun n => (μ n : ℝ)) (fun n => 1 / (n : ℝ) ^ (1 + s)) (by simp)
      hsum0 hv hlim
    unfold Aser
    rw [show (∑' n : ℕ, (μ n : ℝ) / (n : ℝ) ^ (1 + s)) =
        ∑' n : ℕ, (μ n : ℝ) * (1 / (n : ℝ) ^ (1 + s)) from
        tsum_congr (fun n => div_eq_mul_one_div _ _), this]
    rfl
  have hpt : ∀ i : ℕ, Tendsto (fun s => fS s i) (𝓝[>] 0) (𝓝 (uM i)) := by
    intro i
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [fS, uM, Mf_zero]
    have hx0 : (0 : ℝ) < i := by exact_mod_cast hi
    have hcont : ContinuousAt (fun s : ℝ => fS s i) 0 := by
      simp only [fS]
      push_cast
      fun_prop (disch := positivity)
    have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    convert this using 2
    simp [fS, uM]
  have hD := tendsto_tsum_of_dominated_convergence hbs hpt (by
    filter_upwards [Ioo_mem_nhdsGT one_pos] with s hs
    exact fun i => by rw [Real.norm_eq_abs]; exact hfb s hs.1 hs.2.le i)
  have hD' : Tendsto Aser (𝓝[>] 0) (𝓝 (∑' i, uM i)) := by
    refine hD.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT one_pos] with s hs
    exact (hA s hs.1 hs.2.le).symm
  exact tendsto_nhds_unique hD' tendsto_Aser

/-- `|m(N)| ≤ C exp(-c √log N)`. -/
lemma mf_bound (h : PNTMobius) : ∃ c > 0, ∃ C > 0, ∀ n : ℕ, |mf n| ≤ C * ep c n := by
  obtain ⟨c, hc, C₀, hC₀, hM⟩ := Mf_bound h
  have hI := tsum_uM_eq_zero hc hC₀ hM
  obtain ⟨K, hK, hT⟩ := tail_ep_div hc
  refine ⟨c / 2, half_pos hc, C₀ * (1 + K), by positivity, fun N => ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [mf_zero, abs_zero]; have := ep_pos (c / 2) ((0 : ℕ) : ℝ); positivity
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsB : Summable (fun i : ℕ => C₀ * (ep c i / i)) := (summable_ep_div hc).mul_left C₀
  have hsU : Summable uM :=
    Summable.of_norm_bounded hsB (fun i => by rw [Real.norm_eq_abs]; exact abs_uM_le hM hC₀ i)
  have hsplit := hsU.sum_add_tsum_nat_add N
  rw [hI] at hsplit
  rw [mf_eq N, show ∑ i ∈ range N, uM i = -∑' i, uM (i + N) by linarith]
  have hsB' : Summable (fun i : ℕ => C₀ * (ep c ((i + N : ℕ) : ℝ) / ((i + N : ℕ) : ℝ))) :=
    (summable_nat_add_iff N).mpr hsB
  have htail : |∑' i, uM (i + N)| ≤ C₀ * (K * ep (c / 2) N) := by
    calc |∑' i, uM (i + N)| ≤ ∑' i : ℕ, C₀ * (ep c ((i + N : ℕ) : ℝ) / ((i + N : ℕ) : ℝ)) :=
          abs_tsum_le hsB' (fun i => abs_uM_le hM hC₀ (i + N))
      _ = C₀ * ∑' i : ℕ, ep c ((i + N : ℕ) : ℝ) / ((i + N : ℕ) : ℝ) := tsum_mul_left
      _ ≤ C₀ * (K * ep (c / 2) N) := by gcongr; exact hT N hN
  have hfirst : |Mf N * (1 / (N : ℝ))| ≤ C₀ * ep (c / 2) N := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (N : ℝ))]
    calc |Mf N| * (1 / (N : ℝ)) ≤ C₀ * N * ep c N * (1 / (N : ℝ)) := by
          gcongr; exact hM N hN
      _ = C₀ * ep c N := by field_simp
      _ ≤ C₀ * ep (c / 2) N := by gcongr; exact ep_mono_c (by linarith) _
  calc |Mf N * (1 / (N : ℝ)) + -∑' i, uM (i + N)|
      ≤ |Mf N * (1 / (N : ℝ))| + |∑' i, uM (i + N)| := by
        rw [← abs_neg (∑' i, uM (i + N))]; exact abs_add_le _ _
    _ ≤ C₀ * ep (c / 2) N + C₀ * (K * ep (c / 2) N) := add_le_add hfirst htail
    _ = C₀ * (1 + K) * ep (c / 2) N := by ring

/-! ## The bound for `S₁` -/

/-- `t(i) = m(i) (log(i+1) - log i)`. -/
noncomputable def tM (i : ℕ) : ℝ := mf i * (Real.log ((i + 1 : ℕ) : ℝ) - Real.log (i : ℝ))

lemma S1_eq (z : ℝ) (hz : 1 ≤ z) :
    S1 z = mf ⌊z⌋₊ * (Real.log z - Real.log ⌊z⌋₊) + ∑ i ∈ range ⌊z⌋₊, tM i := by
  have := sum_by_parts (fun n => (μ n : ℝ) / n) (fun n => Real.log z - Real.log n) ⌊z⌋₊
  unfold S1
  have e : ∀ n ∈ Icc 1 ⌊z⌋₊, (μ n : ℝ) * Real.log (z / n) / n =
      (μ n : ℝ) / n * (Real.log z - Real.log n) := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [Real.log_div (by positivity) this.ne']
    ring
  rw [sum_congr rfl e, this]
  congr 1
  apply sum_congr rfl
  intro i _
  simp only [tM, mf]
  ring

lemma abs_tM_le {c C : ℝ} (hm : ∀ n : ℕ, |mf n| ≤ C * ep c n) (i : ℕ) :
    |tM i| ≤ C * (ep c i / i) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [tM, mf_zero]
  have hx0 : (0 : ℝ) < i := by exact_mod_cast hi
  obtain ⟨hl0, hl⟩ := log_succ_sub_log_le hx0
  unfold tM
  push_cast
  rw [abs_mul, abs_of_nonneg hl0]
  calc |mf i| * (Real.log ((i : ℝ) + 1) - Real.log i) ≤ (C * ep c i) * (1 / (i : ℝ)) :=
        mul_le_mul (hm i) hl hl0 (le_trans (abs_nonneg _) (hm i))
    _ = C * (ep c i / i) := by ring

lemma tendsto_slope_log (i : ℝ) (hi : 0 < i) :
    Tendsto (fun s : ℝ => (1 / i ^ s - 1 / (i + 1) ^ s) / s) (𝓝[>] 0)
      (𝓝 (Real.log (i + 1) - Real.log i)) := by
  have h1 : HasDerivAt (fun s : ℝ => Real.exp (-(Real.log i * s))) (-Real.log i) 0 := by
    have := ((hasDerivAt_id' (0 : ℝ)).const_mul (Real.log i)).neg.exp
    simpa using this
  have h2 : HasDerivAt (fun s : ℝ => Real.exp (-(Real.log (i + 1) * s))) (-Real.log (i + 1)) 0 := by
    have := ((hasDerivAt_id' (0 : ℝ)).const_mul (Real.log (i + 1))).neg.exp
    simpa using this
  have h := (h1.sub h2).tendsto_slope_zero_right
  have e : (-Real.log i - -Real.log (i + 1)) = Real.log (i + 1) - Real.log i := by ring
  rw [e] at h
  refine h.congr (fun s => ?_)
  simp only [Pi.sub_apply, zero_add, mul_zero, neg_zero, Real.exp_zero, sub_self, sub_zero,
    smul_eq_mul]
  rw [Real.rpow_def_of_pos hi, Real.rpow_def_of_pos (by linarith : (0 : ℝ) < i + 1), one_div,
    one_div, ← Real.exp_neg, ← Real.exp_neg]
  ring_nf

/-- `∑ m(i) log((i+1)/i) = 1`. -/
lemma tsum_tM_eq_one {c₁ C₁ : ℝ} (hc₁ : 0 < c₁) (hC₁ : 0 < C₁)
    (hm : ∀ n : ℕ, |mf n| ≤ C₁ * ep c₁ n) : ∑' i, tM i = 1 := by
  set gS : ℝ → ℕ → ℝ := fun s i =>
    mf i * ((1 / (i : ℝ) ^ s - 1 / ((i + 1 : ℕ) : ℝ) ^ s) / s) with hgS
  set bound : ℕ → ℝ := fun i => C₁ * (ep c₁ i / i) with hbound
  have hbs : Summable bound := (summable_ep_div hc₁).mul_left C₁
  have hgb : ∀ s : ℝ, 0 < s → ∀ i : ℕ, |gS s i| ≤ bound i := by
    intro s hs i
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [gS, bound, mf_zero]
    have hx : (1 : ℝ) ≤ i := by exact_mod_cast hi
    have hx0 : (0 : ℝ) < i := by linarith
    obtain ⟨hD0, hD1⟩ := inv_rpow_sub_le hx0 (show (i : ℝ) ≤ (i : ℝ) + 1 by linarith) hs.le
    obtain ⟨hl0, hl⟩ := log_succ_sub_log_le hx0
    have hpow : 1 / (i : ℝ) ^ s ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact Real.one_le_rpow hx hs.le
    have hD2 : (1 / (i : ℝ) ^ s - 1 / ((i : ℝ) + 1) ^ s) / s ≤ 1 / (i : ℝ) := by
      rw [div_le_iff₀ hs]
      calc _ ≤ 1 / (i : ℝ) ^ s * (s * (Real.log ((i : ℝ) + 1) - Real.log i)) := hD1
        _ ≤ 1 * (s * (1 / (i : ℝ))) := by
          apply mul_le_mul hpow _ (by positivity) (by norm_num)
          exact mul_le_mul_of_nonneg_left hl hs.le
        _ = 1 / (i : ℝ) * s := by ring
    have hD0' : 0 ≤ (1 / (i : ℝ) ^ s - 1 / ((i : ℝ) + 1) ^ s) / s := div_nonneg hD0 hs.le
    simp only [gS, bound]
    push_cast
    rw [abs_mul, abs_of_nonneg hD0']
    calc |mf i| * ((1 / (i : ℝ) ^ s - 1 / ((i : ℝ) + 1) ^ s) / s) ≤
        (C₁ * ep c₁ i) * (1 / (i : ℝ)) :=
          mul_le_mul (hm i) hD2 hD0' (le_trans (abs_nonneg _) (hm i))
      _ = C₁ * (ep c₁ i / i) := by ring
  have hA : ∀ s : ℝ, 0 < s → Aser s / s = ∑' i, gS s i := by
    intro s hs
    have hs0 : s ≠ 0 := hs.ne'
    have e1 : ∀ n : ℕ, (μ n : ℝ) / (n : ℝ) ^ (1 + s) = (μ n : ℝ) / n * (1 / (n : ℝ) ^ s) := by
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      rw [Real.rpow_add hn0, Real.rpow_one]
      field_simp
    have hsum1 : Summable (fun n : ℕ => (μ n : ℝ) / (n : ℝ) ^ (1 + s)) := by
      refine Summable.of_norm_bounded
        (Real.summable_one_div_nat_rpow.mpr (by linarith : (1 : ℝ) < 1 + s)) (fun n => ?_)
      rw [Real.norm_eq_abs, abs_div]
      have h1 : 0 ≤ (n : ℝ) ^ (1 + s) := by positivity
      rw [abs_of_nonneg h1]
      exact div_le_div_of_nonneg_right (abs_moebius_real_le n) h1
    have hsum0 : Summable (fun n : ℕ => (μ n : ℝ) / n * (1 / (n : ℝ) ^ s)) := by
      simpa [e1] using hsum1
    have hgs : Summable (gS s) :=
      Summable.of_norm_bounded hbs (fun i => by rw [Real.norm_eq_abs]; exact hgb s hs i)
    have hv : Summable (fun i : ℕ => (∑ j ∈ Icc 1 i, (μ j : ℝ) / j) *
        (1 / (i : ℝ) ^ s - 1 / ((i + 1 : ℕ) : ℝ) ^ s)) := by
      refine (hgs.mul_left s).congr (fun i => ?_)
      simp only [gS, mf]
      field_simp
    have hlim : Tendsto (fun N : ℕ => (∑ j ∈ Icc 1 N, (μ j : ℝ) / j) * (1 / (N : ℝ) ^ s))
        atTop (𝓝 0) := by
      have ht : Tendsto (fun N : ℕ => C₁ * (1 / (N : ℝ) ^ s)) atTop (𝓝 0) := by
        have := ((tendsto_rpow_neg_atTop hs).comp tendsto_natCast_atTop_atTop).const_mul C₁
        rw [mul_zero] at this
        refine this.congr (fun N => ?_)
        simp [Function.comp_apply, Real.rpow_neg (Nat.cast_nonneg N)]
      refine squeeze_zero_norm (fun N => ?_) ht
      have h1 : 0 ≤ 1 / (N : ℝ) ^ s := by positivity
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h1]
      have hmN : |mf N| ≤ C₁ := (hm N).trans (by
        have := ep_le_one hc₁.le (N : ℝ); nlinarith)
      exact mul_le_mul_of_nonneg_right hmN h1
    have := tsum_by_parts (fun n => (μ n : ℝ) / n) (fun n => 1 / (n : ℝ) ^ s) (by simp)
      hsum0 hv hlim
    unfold Aser
    rw [tsum_congr e1, this]
    rw [← tsum_div_const]
    refine tsum_congr (fun i => ?_)
    simp only [gS, mf]
    ring
  have hpt : ∀ i : ℕ, Tendsto (fun s => gS s i) (𝓝[>] 0) (𝓝 (tM i)) := by
    intro i
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [gS, tM, mf_zero]
    have hx0 : (0 : ℝ) < i := by exact_mod_cast hi
    have := (tendsto_slope_log (i : ℝ) hx0).const_mul (mf i)
    simp only [gS, tM]
    push_cast
    exact this
  have hD := tendsto_tsum_of_dominated_convergence hbs hpt (by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact fun i => by rw [Real.norm_eq_abs]; exact hgb s hs i)
  have hD' : Tendsto (fun s => Aser s / s) (𝓝[>] 0) (𝓝 (∑' i, tM i)) := by
    refine hD.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (hA s hs).symm
  exact tendsto_nhds_unique hD' tendsto_Aser_div

/-- `|S₁(z) - 1| ≤ C exp(-c √log z)` for `z ≥ 1`. -/
lemma S1_bound (h : PNTMobius) :
    ∃ c > 0, ∃ C > 0, ∀ z : ℝ, 1 ≤ z → |S1 z - 1| ≤ C * ep c z := by
  obtain ⟨c₁, hc₁, C₁, hC₁, hm⟩ := mf_bound h
  have hV := tsum_tM_eq_one hc₁ hC₁ hm
  obtain ⟨K, hK, hT⟩ := tail_ep_div hc₁
  refine ⟨c₁ / 2, half_pos hc₁, C₁ * (1 + K) * Real.exp (c₁ / 2), by positivity, fun z hz => ?_⟩
  set N := ⌊z⌋₊ with hNdef
  have hN : 1 ≤ N := Nat.le_floor (by simpa using hz)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNz : (N : ℝ) ≤ z := Nat.floor_le (by linarith)
  have hzN : z < N + 1 := Nat.lt_floor_add_one z
  have hN0 : (0 : ℝ) < N := by linarith
  have hlog0 : 0 ≤ Real.log z - Real.log N := by
    linarith [Real.log_le_log hN0 hNz]
  have hlog1 : Real.log z - Real.log N ≤ 1 := by
    rw [← Real.log_div (by linarith) hN0.ne']
    have := Real.log_le_sub_one_of_pos (show 0 < z / N by positivity)
    have h2 : z / N ≤ 2 := by
      rw [div_le_iff₀ hN0]; linarith
    linarith
  have hsB : Summable (fun i : ℕ => C₁ * (ep c₁ i / i)) := (summable_ep_div hc₁).mul_left C₁
  have hsT : Summable tM :=
    Summable.of_norm_bounded hsB (fun i => by rw [Real.norm_eq_abs]; exact abs_tM_le hm i)
  have hsplit := hsT.sum_add_tsum_nat_add N
  rw [hV] at hsplit
  rw [S1_eq z hz, ← hNdef]
  have hsB' : Summable (fun i : ℕ => C₁ * (ep c₁ ((i + N : ℕ) : ℝ) / ((i + N : ℕ) : ℝ))) :=
    (summable_nat_add_iff N).mpr hsB
  have htail : |∑' i, tM (i + N)| ≤ C₁ * (K * ep (c₁ / 2) N) := by
    calc |∑' i, tM (i + N)| ≤ ∑' i : ℕ, C₁ * (ep c₁ ((i + N : ℕ) : ℝ) / ((i + N : ℕ) : ℝ)) :=
          abs_tsum_le hsB' (fun i => abs_tM_le hm (i + N))
      _ = C₁ * ∑' i : ℕ, ep c₁ ((i + N : ℕ) : ℝ) / ((i + N : ℕ) : ℝ) := tsum_mul_left
      _ ≤ C₁ * (K * ep (c₁ / 2) N) := by gcongr; exact hT N hN
  have hfirst : |mf N * (Real.log z - Real.log N)| ≤ C₁ * ep (c₁ / 2) N := by
    rw [abs_mul, abs_of_nonneg hlog0]
    calc |mf N| * (Real.log z - Real.log N) ≤ (C₁ * ep c₁ N) * 1 :=
          mul_le_mul (hm N) hlog1 hlog0 (le_trans (abs_nonneg _) (hm N))
      _ ≤ C₁ * ep (c₁ / 2) N := by
          rw [mul_one]; gcongr; exact ep_mono_c (by linarith) _
  have hshift : ep (c₁ / 2) N ≤ Real.exp (c₁ / 2) * ep (c₁ / 2) z :=
    ep_shift (by linarith) hN1 (by linarith)
  have heq : mf N * (Real.log z - Real.log N) + ∑ i ∈ range N, tM i - 1 =
      mf N * (Real.log z - Real.log N) - ∑' i, tM (i + N) := by linarith
  rw [heq]
  calc |mf N * (Real.log z - Real.log N) - ∑' i, tM (i + N)|
      ≤ |mf N * (Real.log z - Real.log N)| + |∑' i, tM (i + N)| := abs_sub _ _
    _ ≤ C₁ * ep (c₁ / 2) N + C₁ * (K * ep (c₁ / 2) N) := add_le_add hfirst htail
    _ = C₁ * (1 + K) * ep (c₁ / 2) N := by ring
    _ ≤ C₁ * (1 + K) * (Real.exp (c₁ / 2) * ep (c₁ / 2) z) := by gcongr
    _ = C₁ * (1 + K) * Real.exp (c₁ / 2) * ep (c₁ / 2) z := by ring

end MobiusSums
end MobiusDeterminant
