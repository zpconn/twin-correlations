import MobiusDeterminant.Unconditional.Interfaces
import LeanPool.KloostermanWeil

/-!
# Incomplete Kloosterman sums over sharp intervals (paper, Theorem 6.1, Step 4)

For the long boxes of the mean-value theorem we need, for a squarefree modulus `e`,
a frequency `h ≠ 0`, a unit `k` and a sharp interval `[x₀, x₀ + L)`, the bound
```
∑_{x₀ ≤ n < x₀+L, (nk, 2e) = 1} n^{-iτ} e_e(h \overline{nk})
  ≪ τ(2e) τ(e) (√e (1 + log e) + L √|h| / √e) (1 + |τ|).
```
Proof:
* reduce `e_e(h ·)` to the modulus `q = e/(h,e)` (`kfrac_eq_reduced`);
* detect `(n, 2g) = 1` by Möbius inversion, `g = (h, e)`;
* complete the sum over `ZMod q` (Lean Pool: centered Fourier completion plus the Weil
  bound `kloostermanUnitSum_squarefree_unit_le`);
* remove `n^{-iτ}` by Abel summation (`abel_bound`).
-/

open Finset Real
open scoped ArithmeticFunction.Moebius

namespace MobiusDeterminant
namespace MeanValue

/-! ## The characters `t ↦ t^{-iτ}` -/

/-- `twist τ t = t^{-iτ} = exp(-iτ log t)`, the character produced by Mellin separation. -/
noncomputable def twist (τ t : ℝ) : ℂ := Complex.exp (-(τ * Real.log t : ℝ) * Complex.I)

lemma twist_eq (τ t : ℝ) :
    twist τ t = Complex.exp (((-(τ * Real.log t) : ℝ) : ℂ) * Complex.I) := by
  unfold twist; push_cast; ring_nf

lemma norm_twist (τ t : ℝ) : ‖twist τ t‖ = 1 := by
  rw [twist_eq]; exact Complex.norm_exp_ofReal_mul_I _

lemma twist_mul (τ : ℝ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    twist τ (s * t) = twist τ s * twist τ t := by
  unfold twist
  rw [Real.log_mul hs.ne' ht.ne', ← Complex.exp_add]
  congr 1; push_cast; ring

/-- `(s/t)^{-iτ} = s^{-iτ} t^{iτ}`. -/
lemma twist_div (τ : ℝ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    twist τ (s / t) = twist τ s * Complex.exp ((τ * Real.log t : ℝ) * Complex.I) := by
  unfold twist
  rw [Real.log_div hs.ne' ht.ne', ← Complex.exp_add]
  congr 1; push_cast; ring

lemma norm_exp_mul_I (x : ℝ) : ‖Complex.exp ((x : ℂ) * Complex.I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I x

lemma norm_twist_sub_le (τ s t : ℝ) :
    ‖twist τ s - twist τ t‖ ≤ |τ| * |Real.log s - Real.log t| := by
  have h : twist τ s = twist τ t *
      Complex.exp (Complex.I * ((-(τ * (Real.log s - Real.log t)) : ℝ) : ℂ)) := by
    unfold twist
    rw [← Complex.exp_add]
    congr 1; push_cast; ring
  rw [h, ← mul_sub_one, norm_mul, norm_twist, one_mul]
  refine (Real.norm_exp_I_mul_ofReal_sub_one_le).trans ?_
  rw [Real.norm_eq_abs, abs_neg, abs_mul]

/-- Total variation of `n ↦ n^{-iτ}` along `y₀, y₀+1, …, y₀+m`. -/
lemma twist_variation (τ : ℝ) (y₀ m : ℕ) (hy : 1 ≤ y₀) :
    ∑ j ∈ range m, ‖twist τ ((y₀ + (j + 1) : ℕ) : ℝ) - twist τ ((y₀ + j : ℕ) : ℝ)‖
      ≤ |τ| * (Real.log ((y₀ + m : ℕ) : ℝ) - Real.log (y₀ : ℝ)) := by
  have hstep : ∀ j ∈ range m,
      ‖twist τ ((y₀ + (j + 1) : ℕ) : ℝ) - twist τ ((y₀ + j : ℕ) : ℝ)‖
        ≤ |τ| * (Real.log ((y₀ + (j + 1) : ℕ) : ℝ) - Real.log ((y₀ + j : ℕ) : ℝ)) := by
    intro j _
    refine (norm_twist_sub_le τ _ _).trans (le_of_eq ?_)
    congr 1
    rw [abs_of_nonneg]
    rw [sub_nonneg]
    apply Real.log_le_log
    · have : (1 : ℝ) ≤ ((y₀ + j : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ y₀ + j)
      linarith
    · exact_mod_cast (by omega : y₀ + j ≤ y₀ + (j + 1))
  refine (sum_le_sum hstep).trans (le_of_eq ?_)
  rw [← mul_sum]
  congr 1
  have := Finset.sum_range_sub (fun j => Real.log ((y₀ + j : ℕ) : ℝ)) m
  simpa using this

/-! ## Abel summation -/

/-- Discrete Abel summation: a uniform bound `M` for the initial partial sums of `c`
gives `‖∑ c_j w_j‖ ≤ M (1 + ∑ ‖w_{j+1} - w_j‖)` for weights `‖w_j‖ ≤ 1`. -/
theorem abel_bound (c w : ℕ → ℂ) (L : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hpre : ∀ m ≤ L, ‖∑ j ∈ range m, c j‖ ≤ M) (hw : ∀ j, ‖w j‖ ≤ 1) :
    ‖∑ j ∈ range L, c j * w j‖ ≤
      M * (1 + ∑ j ∈ range (L - 1), ‖w (j + 1) - w j‖) := by
  have hparts := Finset.sum_range_by_parts' c w L
  simp only [smul_eq_mul] at hparts
  rw [hparts]
  have h1 : ‖(∑ i ∈ range L, c i) * w (L - 1)‖ ≤ M := by
    rw [norm_mul]
    calc ‖∑ i ∈ range L, c i‖ * ‖w (L - 1)‖ ≤ M * 1 :=
          mul_le_mul (hpre L le_rfl) (hw _) (norm_nonneg _) hM
      _ = M := mul_one M
  have h2 : ‖∑ i ∈ range (L - 1), (∑ j ∈ range (i + 1), c j) * (w (i + 1) - w i)‖ ≤
      ∑ i ∈ range (L - 1), M * ‖w (i + 1) - w i‖ := by
    refine (norm_sum_le _ _).trans (sum_le_sum fun i hi => ?_)
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_right (hpre _ ?_) (norm_nonneg _)
    simp only [mem_range] at hi; omega
  calc _ ≤ ‖(∑ i ∈ range L, c i) * w (L - 1)‖ +
        ‖∑ i ∈ range (L - 1), (∑ j ∈ range (i + 1), c j) * (w (i + 1) - w i)‖ :=
        norm_sub_le _ _
    _ ≤ M + ∑ i ∈ range (L - 1), M * ‖w (i + 1) - w i‖ := add_le_add h1 h2
    _ = M * (1 + ∑ j ∈ range (L - 1), ‖w (j + 1) - w j‖) := by rw [← mul_sum]; ring

/-! ## Incomplete Kloosterman sums: completion and the Weil bound -/

open KloostermanWeil in
/-- **Incomplete Kloosterman sums over a sharp interval** (paper, Lemma 2.4 with sharp
cutoffs): for squarefree `q` and a unit `b`,
`‖∑_{j<L} rP_q(b; x + j)‖ ≤ 2^{ω(q)} (√q (1 + log q) + L/√q)`,
where `rP_q(b; y) = 𝟙_{y ∈ (ℤ/q)^×} e_q(b y⁻¹)`.  Proof: split off the mean, complete the
centered part (Lean Pool) and bound both by Weil. -/
theorem rp_interval_bound {q : ℕ} [NeZero q] (hsq : Squarefree q) {b : ZMod q}
    (hb : IsUnit b) (x : ZMod q) (L : ℕ) :
    ‖∑ j ∈ range L, reciprocalPhase q b (x + (j : ZMod q))‖ ≤
      (2 : ℝ) ^ q.primeFactors.card * (Real.sqrt q * (1 + Real.log q) + L / Real.sqrt q) := by
  have hW := kloostermanUnitSum_squarefree_unit_le prime_bound hsq
  have hsplit : ∑ j ∈ range L, reciprocalPhase q b (x + (j : ZMod q)) =
      centeredIntervalSum q b x L + L * reciprocalMean q b := by
    unfold centeredIntervalSum centeredReciprocalPhase
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have hc : ‖centeredIntervalSum q b x L‖ ≤
      ((2 : ℝ) ^ q.primeFactors.card * Real.sqrt q) * (1 + Real.log q) :=
    centeredIntervalSum_norm_le_of_dft_bound b x L (by positivity) (fun h hh => by
      rw [dft_centeredReciprocalPhase_nonzero q b hh]
      exact hW b (-h) hb)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hsq0 : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq0
  have hm : ‖reciprocalMean q b‖ ≤ (2 : ℝ) ^ q.primeFactors.card / Real.sqrt q := by
    unfold reciprocalMean
    have hsum : ∑ y : ZMod q, reciprocalPhase q b y = kloostermanUnitSum q b 0 := by
      rw [← sum_reciprocalPhase_eq_kloostermanUnitSum]
      simp
    rw [hsum, norm_mul, norm_inv, Complex.norm_natCast]
    calc (q : ℝ)⁻¹ * ‖kloostermanUnitSum q b 0‖
        ≤ (q : ℝ)⁻¹ * ((2 : ℝ) ^ q.primeFactors.card * Real.sqrt q) :=
          mul_le_mul_of_nonneg_left (hW b 0 hb) (by positivity)
      _ = (2 : ℝ) ^ q.primeFactors.card * (Real.sqrt q / q) := by ring
      _ = (2 : ℝ) ^ q.primeFactors.card / Real.sqrt q := by
          rw [Real.sqrt_div_self']; ring
  rw [hsplit]
  calc ‖centeredIntervalSum q b x L + L * reciprocalMean q b‖
      ≤ ‖centeredIntervalSum q b x L‖ + ‖(L : ℂ) * reciprocalMean q b‖ := norm_add_le _ _
    _ ≤ ((2 : ℝ) ^ q.primeFactors.card * Real.sqrt q) * (1 + Real.log q) +
          L * ((2 : ℝ) ^ q.primeFactors.card / Real.sqrt q) := by
        gcongr
        rw [norm_mul, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg _)
    _ = _ := by ring

open KloostermanWeil in
/-- The incomplete Kloosterman sum twisted by `v^{-iτ}`, over `v ∈ [y₀, y₀ + L)` with
`y₀ + L ≤ 3y₀ + 1`. -/
theorem twisted_rp_bound {q : ℕ} [NeZero q] (hsq : Squarefree q) {b : ZMod q}
    (hb : IsUnit b) (τ : ℝ) (y₀ L : ℕ) (hy₀ : 1 ≤ y₀) (hL : y₀ + L ≤ 3 * y₀ + 1) :
    ‖∑ v ∈ Ico y₀ (y₀ + L), twist τ v * reciprocalPhase q b (v : ZMod q)‖ ≤
      (2 : ℝ) ^ q.primeFactors.card * (Real.sqrt q * (1 + Real.log q) + L / Real.sqrt q) *
        (1 + 2 * |τ|) := by
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [add_tsub_cancel_left]
  set M : ℝ := (2 : ℝ) ^ q.primeFactors.card *
    (Real.sqrt q * (1 + Real.log q) + L / Real.sqrt q) with hMdef
  have hM0 : 0 ≤ M := by positivity
  have key := abel_bound (fun j => reciprocalPhase q b ((y₀ : ZMod q) + (j : ZMod q)))
    (fun j => twist τ ((y₀ + j : ℕ) : ℝ)) L hM0 (fun m hm => by
      refine (rp_interval_bound hsq hb (y₀ : ZMod q) m).trans ?_
      rw [hMdef]
      gcongr) (fun j => (norm_twist _ _).le)
  have hvar := twist_variation τ y₀ (L - 1) hy₀
  have hlog : Real.log ((y₀ + (L - 1) : ℕ) : ℝ) - Real.log (y₀ : ℝ) ≤ 2 := by
    have hy0 : (0 : ℝ) < y₀ := by exact_mod_cast hy₀
    rw [← Real.log_div (by positivity) hy0.ne']
    have h3 : ((y₀ + (L - 1) : ℕ) : ℝ) / y₀ ≤ 3 := by
      rw [div_le_iff₀ hy0]
      exact_mod_cast (by omega : y₀ + (L - 1) ≤ 3 * y₀)
    have hpos : 0 < ((y₀ + (L - 1) : ℕ) : ℝ) / y₀ := by
      apply div_pos _ hy0
      exact_mod_cast (by omega : 0 < y₀ + (L - 1))
    linarith [Real.log_le_sub_one_of_pos hpos]
  have hsum_eq : ∑ j ∈ range L, twist τ ((y₀ + j : ℕ) : ℝ) *
        reciprocalPhase q b ((y₀ + j : ℕ) : ZMod q) =
      ∑ j ∈ range L, reciprocalPhase q b ((y₀ : ZMod q) + (j : ZMod q)) *
        twist τ ((y₀ + j : ℕ) : ℝ) := by
    refine sum_congr rfl fun j _ => ?_
    rw [mul_comm]; push_cast; rfl
  rw [hsum_eq]
  refine key.trans ?_
  gcongr
  calc ∑ j ∈ range (L - 1), ‖twist τ ((y₀ + (j + 1) : ℕ) : ℝ) - twist τ ((y₀ + j : ℕ) : ℝ)‖
      ≤ |τ| * (Real.log ((y₀ + (L - 1) : ℕ) : ℝ) - Real.log (y₀ : ℝ)) := hvar
    _ ≤ |τ| * 2 := mul_le_mul_of_nonneg_left hlog (abs_nonneg τ)
    _ = 2 * |τ| := by ring

/-! ## Reduction of the Kloosterman fraction to the modulus `e/(h,e)` -/

lemma kfrac_eq_stdAddChar (e : ℕ) [NeZero e] (h : ℤ) (d : ℕ) :
    kfrac e h d = ZMod.stdAddChar ((h : ZMod e) * (d : ZMod e)⁻¹) := by
  set z : ZMod e := (h : ZMod e) * (d : ZMod e)⁻¹
  have hz : (((z.val : ℕ) : ℤ) : ZMod e) = z := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [← hz, ZMod.stdAddChar_coe]
  unfold kfrac
  push_cast
  rfl

/-- Inverse of a product of units in `ZMod q`. -/
lemma zmod_mul_inv {q : ℕ} {x y : ZMod q} (hx : IsUnit x) (hy : IsUnit y) :
    (x * y)⁻¹ = x⁻¹ * y⁻¹ := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨w, rfl⟩ := hy
  rw [← Units.val_mul, ZMod.inv_coe_unit, ZMod.inv_coe_unit, ZMod.inv_coe_unit, mul_inv,
    Units.val_mul]

/-- **Gcd reduction** (paper, Theorem 6.1, Step 1): if `e = gq` and `h = ga`, then for
`(d, e) = 1`, `e_e(h d̄) = e_q(a d̄)`. -/
theorem kfrac_eq_reduced {e g q : ℕ} (he0 : e ≠ 0) (he : e = g * q) [NeZero q] {h a : ℤ}
    (ha : h = g * a) {d : ℕ} (hd : Nat.Coprime d e) :
    kfrac e h d = ZMod.stdAddChar ((a : ZMod q) * (d : ZMod q)⁻¹) := by
  have : NeZero e := ⟨he0⟩
  have hg : g ≠ 0 := by rintro rfl; simp at he; exact he0 he
  rw [kfrac_eq_stdAddChar]
  set Y : ℕ := ((a : ZMod q) * (d : ZMod q)⁻¹).val with hYdef
  have hdq : Nat.Coprime d q := Nat.Coprime.coprime_dvd_right ⟨g, by rw [he, mul_comm]⟩ hd
  have hYq : ((Y : ℤ) : ZMod q) = (a : ZMod q) * (d : ZMod q)⁻¹ := by
    rw [Int.cast_natCast, hYdef, ZMod.natCast_zmod_val]
  -- `q ∣ Y d - a`
  have h1 : (q : ℤ) ∣ (Y : ℤ) * d - a := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [show ((Y : ℕ) : ZMod q) = ((Y : ℤ) : ZMod q) by push_cast; rfl, hYq, mul_assoc,
      mul_comm ((d : ZMod q)⁻¹), ZMod.coe_mul_inv_eq_one d hdq, mul_one, sub_self]
  -- hence `e ∣ g Y d - h`
  have h2 : (e : ℤ) ∣ (g : ℤ) * Y * d - h := by
    rw [ha, he]
    push_cast
    rw [show (g : ℤ) * Y * d - g * a = g * (Y * d - a) by ring]
    exact mul_dvd_mul_left _ h1
  have hz : (h : ZMod e) * (d : ZMod e)⁻¹ = (((g : ℤ) * Y : ℤ) : ZMod e) := by
    have h3 : ((h : ℤ) : ZMod e) = (((g : ℤ) * Y * d : ℤ) : ZMod e) :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2 h2
    rw [h3]
    push_cast
    rw [mul_assoc, mul_assoc, ZMod.coe_mul_inv_eq_one d hd, mul_one]
  rw [hz, ZMod.stdAddChar_coe, ← hYq, ZMod.stdAddChar_coe]
  congr 1
  rw [he]
  have hgC : (g : ℂ) ≠ 0 := by exact_mod_cast hg
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  push_cast
  field_simp

/-! ## Möbius detection of a coprimality condition and reindexing -/

/-- `𝟙_{(n,m)=1} = ∑_{δ ∣ m, δ ∣ n} μ(δ)`. -/
lemma coprime_indicator (n m : ℕ) (hm : m ≠ 0) :
    (if Nat.Coprime n m then (1 : ℂ) else 0) =
      ∑ δ ∈ m.divisors.filter (· ∣ n), ((μ δ : ℤ) : ℂ) := by
  have hg : Nat.gcd n m ≠ 0 := (Nat.gcd_pos_of_pos_right n (Nat.pos_of_ne_zero hm)).ne'
  have hfilter : m.divisors.filter (· ∣ n) = (Nat.gcd n m).divisors := by
    ext δ
    simp only [mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨⟨h2, h1⟩, hg⟩
    · rintro ⟨⟨h1, h2⟩, _⟩; exact ⟨⟨h2, hm⟩, h1⟩
  rw [hfilter]
  have key := congrArg (fun f : ArithmeticFunction ℂ => f (Nat.gcd n m))
    (ArithmeticFunction.coe_zeta_mul_coe_moebius (R := ℂ))
  simp only [ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.one_apply,
    ArithmeticFunction.intCoe_apply] at key
  rw [key]

lemma ceil_div_le_iff {δ x v : ℕ} (hδ : 0 < δ) : (x + δ - 1) / δ ≤ v ↔ x ≤ δ * v := by
  rw [Nat.div_le_iff_le_mul_add_pred hδ]
  generalize δ * v = t
  omega

/-- The multiples of `δ` in `[x₀, x₀ + L)` are `δ v`, `v ∈ [⌈x₀/δ⌉, ⌈(x₀+L)/δ⌉)`. -/
lemma image_mul_Ico (x₀ L δ : ℕ) (hδ : 0 < δ) :
    (Ico ((x₀ + δ - 1) / δ) ((x₀ + L + δ - 1) / δ)).image (δ * ·) =
      (Ico x₀ (x₀ + L)).filter (δ ∣ ·) := by
  ext n
  simp only [mem_image, mem_Ico, mem_filter]
  constructor
  · rintro ⟨v, ⟨h1, h2⟩, rfl⟩
    refine ⟨⟨(ceil_div_le_iff hδ).1 h1, ?_⟩, dvd_mul_right _ _⟩
    by_contra hc
    exact absurd ((ceil_div_le_iff hδ).2 (not_lt.1 hc)) (not_le.2 h2)
  · rintro ⟨⟨h1, h2⟩, ⟨v, rfl⟩⟩
    refine ⟨v, ⟨(ceil_div_le_iff hδ).2 h1, ?_⟩, rfl⟩
    by_contra hc
    exact absurd ((ceil_div_le_iff hδ).1 (not_lt.1 hc)) (not_le.2 h2)

lemma sum_filter_dvd_Ico (F : ℕ → ℂ) (x₀ L δ : ℕ) (hδ : 0 < δ) :
    ∑ n ∈ (Ico x₀ (x₀ + L)).filter (δ ∣ ·), F n =
      ∑ v ∈ Ico ((x₀ + δ - 1) / δ) ((x₀ + L + δ - 1) / δ), F (δ * v) := by
  rw [← image_mul_Ico x₀ L δ hδ, sum_image]
  intro a _ b _ hab
  exact Nat.eq_of_mul_eq_mul_left hδ hab

open KloostermanWeil in
lemma rp_mul_left {q : ℕ} [NeZero q] (b : ZMod q) {δ : ℕ} (hδ : Nat.Coprime δ q) (v : ℕ) :
    reciprocalPhase q b ((δ * v : ℕ) : ZMod q) =
      reciprocalPhase q (b * (δ : ZMod q)⁻¹) (v : ZMod q) := by
  unfold reciprocalPhase
  push_cast
  have hu : IsUnit (δ : ZMod q) := (ZMod.isUnit_iff_coprime δ q).2 hδ
  by_cases hv : IsUnit (v : ZMod q)
  · rw [ite_eq_left (hu.mul hv), ite_eq_left hv, zmod_mul_inv hu hv, mul_assoc]
  · rw [ite_eq_right (fun h => hv (isUnit_of_mul_isUnit_right h)), ite_eq_right hv]

open KloostermanWeil in
lemma rp_eq_zero_of_not_coprime {q : ℕ} [NeZero q] (b : ZMod q) {n : ℕ}
    (hn : ¬ Nat.Coprime n q) : reciprocalPhase q b (n : ZMod q) = 0 := by
  unfold reciprocalPhase
  rw [ite_eq_right]
  rwa [ZMod.isUnit_iff_coprime]

/-- `2^{ω(n)} ≤ τ(n)`. -/
lemma two_pow_card_primeFactors_le {n : ℕ} (hn : n ≠ 0) :
    2 ^ n.primeFactors.card ≤ n.divisors.card := by
  rw [Nat.card_divisors hn]
  refine Finset.pow_card_le_prod _ _ _ fun p hp => ?_
  have := (Nat.mem_primeFactors.1 hp)
  have := Nat.Prime.factorization_pos_of_dvd this.1 hn this.2.1
  omega

lemma card_divisors_le_of_dvd {m n : ℕ} (hn : n ≠ 0) (h : m ∣ n) :
    m.divisors.card ≤ n.divisors.card :=
  Finset.card_le_card (Nat.divisors_subset_of_dvd hn h)

/-! ## The long-box inner sum -/

/-- The long-box inner sum
`∑_{x₀ ≤ n < x₀+L, (nk,2e)=1} n^{-iτ} e_e(h \overline{nk})` (paper, Theorem 6.1, Step 4). -/
noncomputable def longInner (e : ℕ) (h : ℤ) (k x₀ L : ℕ) (τ : ℝ) : ℂ :=
  ∑ n ∈ Ico x₀ (x₀ + L),
    if Nat.Coprime (n * k) (2 * e) then twist τ n * kfrac e h (n * k) else 0

open KloostermanWeil in
/-- **Long-box inner sum bound** (paper, Theorem 6.1, Step 4, via Lemma 2.4 with the Weil
bound): for squarefree `e`, `h ≠ 0` and `L ≤ x₀`,
`‖∑_{x₀ ≤ n < x₀+L, (nk,2e)=1} n^{-iτ} e_e(h \overline{nk})‖
  ≤ τ(2e) τ(e) (√e (1 + log e) + L √|h| / √e) (1 + 2|τ|)`. -/
theorem longInner_bound {e : ℕ} (he : 0 < e) (hsq : Squarefree e) {h : ℤ} (hh : h ≠ 0)
    (k x₀ L : ℕ) (hx₀ : 1 ≤ x₀) (hL : L ≤ x₀) (τ : ℝ) :
    ‖longInner e h k x₀ L τ‖ ≤ ((2 * e).divisors.card : ℝ) * e.divisors.card *
      (Real.sqrt e * (1 + Real.log e) + L * Real.sqrt |(h : ℝ)| / Real.sqrt e) *
        (1 + 2 * |τ|) := by
  by_cases hk : Nat.Coprime k (2 * e)
  swap
  · have : longInner e h k x₀ L τ = 0 := by
      unfold longInner
      refine sum_eq_zero fun n _ => ?_
      rw [ite_eq_right]
      intro hc; exact hk (Nat.Coprime.coprime_mul_left hc)
    rw [this, norm_zero]; positivity
  -- the gcd strata `g = (h, e)`, `e = g q`, `h = g a`
  obtain ⟨g, hgdef⟩ : ∃ g : ℕ, g = Int.gcd h e := ⟨_, rfl⟩
  have hge : g ∣ e := by rw [hgdef]; exact Int.natCast_dvd_natCast.1 (Int.gcd_dvd_right h e)
  obtain ⟨q, hq⟩ := hge
  obtain ⟨a, ha⟩ : (g : ℤ) ∣ h := by rw [hgdef]; exact Int.gcd_dvd_left h e
  have he0 : e ≠ 0 := he.ne'
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq; exact he0 hq
  have hg0 : g ≠ 0 := by rintro hg; rw [hg, zero_mul] at hq; exact he0 hq
  have : NeZero q := ⟨hq0⟩
  have hsqq : Squarefree q := hsq.squarefree_of_dvd ⟨g, by rw [hq, mul_comm]⟩
  have hkq : Nat.Coprime k q :=
    Nat.Coprime.coprime_dvd_right ⟨2 * g, by rw [hq]; ring⟩ hk
  -- `(a, q) = 1`
  have haq : Int.gcd a q = 1 := by
    have h1 : Int.gcd h e = g := hgdef.symm
    rw [ha, hq, Nat.cast_mul, Int.gcd_mul_left, Int.natAbs_natCast] at h1
    have : g * Int.gcd a q = g * 1 := by rw [h1, mul_one]
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hg0) this
  have hau : IsUnit (a : ZMod q) := by
    obtain ⟨u, v, huv⟩ := Int.isCoprime_iff_gcd_eq_one.2 haq
    have := congrArg (fun z : ℤ => (z : ZMod q)) huv
    push_cast at this
    rw [ZMod.natCast_self, mul_zero, add_zero] at this
    exact IsUnit.of_mul_eq_one_right (u : ZMod q) this
  have hku : IsUnit (k : ZMod q) := (ZMod.isUnit_iff_coprime k q).2 hkq
  have hinv : ∀ {x : ZMod q}, IsUnit x → IsUnit x⁻¹ := by
    intro x hx
    obtain ⟨u, rfl⟩ := hx
    rw [ZMod.inv_coe_unit]
    exact (u⁻¹).isUnit
  set b : ZMod q := (a : ZMod q) * (k : ZMod q)⁻¹ with hbdef
  have hb : IsUnit b := hau.mul (hinv hku)
  have h2g0 : 2 * g ≠ 0 := by positivity
  have hcop_e : ∀ {n : ℕ}, Nat.Coprime (n * k) (2 * e) → Nat.Coprime n (2 * e) :=
    fun hc => (Nat.coprime_mul_iff_left.1 hc).1
  -- rewriting the summand at the reduced modulus
  have hterm : ∀ n : ℕ,
      (if Nat.Coprime (n * k) (2 * e) then twist τ n * kfrac e h (n * k) else 0) =
        (if Nat.Coprime n (2 * g) then (1 : ℂ) else 0) *
          (twist τ n * reciprocalPhase q b (n : ZMod q)) := by
    intro n
    by_cases h1 : Nat.Coprime n (2 * g)
    · by_cases h2 : Nat.Coprime n q
      · have hn2e : Nat.Coprime n (2 * e) := by
          rw [show 2 * e = 2 * g * q by rw [hq]; ring]
          exact Nat.Coprime.mul_right h1 h2
        have hc : Nat.Coprime (n * k) (2 * e) := Nat.coprime_mul_iff_left.2 ⟨hn2e, hk⟩
        rw [ite_eq_left hc, ite_eq_left h1, one_mul]
        congr 1
        have hce : Nat.Coprime (n * k) e := Nat.Coprime.coprime_dvd_right ⟨2, by ring⟩ hc
        rw [kfrac_eq_reduced he0 hq ha hce]
        unfold reciprocalPhase
        have hnu : IsUnit (n : ZMod q) := (ZMod.isUnit_iff_coprime n q).2 h2
        rw [ite_eq_left hnu, Nat.cast_mul, zmod_mul_inv hnu hku, hbdef]
        ring_nf
      · rw [ite_eq_left h1, one_mul, rp_eq_zero_of_not_coprime b h2, mul_zero, ite_eq_right]
        intro hc; apply h2
        exact Nat.Coprime.coprime_dvd_right ⟨2 * g, by rw [hq]; ring⟩ (hcop_e hc)
    · rw [ite_eq_right h1, zero_mul, ite_eq_right]
      intro hc; apply h1
      exact Nat.Coprime.coprime_dvd_right ⟨q, by rw [hq]; ring⟩ (hcop_e hc)
  -- Möbius detection of `(n, 2g) = 1`
  have hsum : longInner e h k x₀ L τ = ∑ δ ∈ (2 * g).divisors, ((μ δ : ℤ) : ℂ) *
      ∑ n ∈ (Ico x₀ (x₀ + L)).filter (δ ∣ ·), twist τ n * reciprocalPhase q b (n : ZMod q) := by
    unfold longInner
    simp_rw [hterm, coprime_indicator _ _ h2g0, Finset.sum_mul]
    rw [Finset.sum_comm' (t' := (2 * g).divisors) (s' := fun δ => (Ico x₀ (x₀ + L)).filter (δ ∣ ·))]
    · refine sum_congr rfl fun δ _ => ?_
      rw [Finset.mul_sum]
    · intro n δ
      simp only [mem_filter, mem_Ico]
      tauto
  -- the bound for one `δ`
  set Bq : ℝ := (2 : ℝ) ^ q.primeFactors.card *
    (Real.sqrt q * (1 + Real.log q) + L / Real.sqrt q) * (1 + 2 * |τ|) with hBq
  have hBq0 : 0 ≤ Bq := by positivity
  have hper : ∀ δ ∈ (2 * g).divisors,
      ‖∑ n ∈ (Ico x₀ (x₀ + L)).filter (δ ∣ ·), twist τ n * reciprocalPhase q b (n : ZMod q)‖
        ≤ Bq := by
    intro δ hδ
    have hδ0 : 0 < δ := Nat.pos_of_mem_divisors hδ
    by_cases hδq : Nat.Coprime δ q
    · rw [sum_filter_dvd_Ico _ x₀ L δ hδ0]
      set y₀ := (x₀ + δ - 1) / δ with hy₀def
      set y₁ := (x₀ + L + δ - 1) / δ with hy₁def
      have hy₀ : 1 ≤ y₀ := by
        by_contra hc
        have h0 : y₀ ≤ 0 := by omega
        rw [hy₀def, ceil_div_le_iff hδ0] at h0
        omega
      have hx₀y : x₀ ≤ δ * y₀ := (ceil_div_le_iff hδ0).1 le_rfl
      have hy₁ : y₁ ≤ 2 * y₀ := by
        by_contra hc
        push Not at hc
        have h1 : δ * (2 * y₀) < x₀ + L := by
          by_contra h'
          push Not at h'
          have := (ceil_div_le_iff hδ0).2 h'
          omega
        nlinarith
      have hcard : y₁ - y₀ ≤ L := by
        have h1 := card_image_of_injective (Ico y₀ y₁)
          (fun a b (hab : δ * a = δ * b) => Nat.eq_of_mul_eq_mul_left hδ0 hab)
        rw [image_mul_Ico x₀ L δ hδ0] at h1
        have h2 := card_filter_le (Ico x₀ (x₀ + L)) (δ ∣ ·)
        simp only [Nat.card_Ico] at h1 h2
        omega
      have hIco : Ico y₀ y₁ = Ico y₀ (y₀ + (y₁ - y₀)) := by
        rcases le_total y₀ y₁ with h | h
        · congr 1; omega
        · rw [Ico_eq_empty_of_le h, Ico_eq_empty_of_le (by omega)]
      have hrw : ∑ v ∈ Ico y₀ y₁, twist τ ((δ * v : ℕ) : ℝ) *
            reciprocalPhase q b ((δ * v : ℕ) : ZMod q) =
          twist τ δ * ∑ v ∈ Ico y₀ y₁, twist τ v *
            reciprocalPhase q (b * (δ : ZMod q)⁻¹) (v : ZMod q) := by
        rw [mul_sum]
        refine sum_congr rfl fun v hv => ?_
        have hv0 : (0 : ℝ) < v := by
          have := (mem_Ico.1 hv).1; exact_mod_cast (by omega : 0 < v)
        have hδ0' : (0 : ℝ) < δ := by exact_mod_cast hδ0
        rw [rp_mul_left b hδq v, Nat.cast_mul, twist_mul τ hδ0' hv0]
        ring
      rw [hrw, norm_mul, norm_twist, one_mul, hIco]
      have hδu : IsUnit (δ : ZMod q) := (ZMod.isUnit_iff_coprime δ q).2 hδq
      refine (twisted_rp_bound hsqq (hb.mul (hinv hδu)) τ y₀ (y₁ - y₀) hy₀
        (by omega)).trans ?_
      rw [hBq]
      gcongr
    · have h0 : ∑ n ∈ (Ico x₀ (x₀ + L)).filter (δ ∣ ·),
          twist τ n * reciprocalPhase q b (n : ZMod q) = 0 := by
        refine sum_eq_zero fun n hn => ?_
        obtain ⟨_, hdn⟩ := mem_filter.1 hn
        rw [rp_eq_zero_of_not_coprime b (fun hc => hδq (Nat.Coprime.coprime_dvd_left hdn hc)),
          mul_zero]
      rw [h0, norm_zero]
      exact hBq0
  -- summing over `δ ∣ 2g`
  have htot : ‖longInner e h k x₀ L τ‖ ≤ ((2 * g).divisors.card : ℝ) * Bq := by
    rw [hsum]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ δ ∈ (2 * g).divisors, ‖((μ δ : ℤ) : ℂ) *
          ∑ n ∈ (Ico x₀ (x₀ + L)).filter (δ ∣ ·), twist τ n * reciprocalPhase q b (n : ZMod q)‖
        ≤ ∑ δ ∈ (2 * g).divisors, Bq := by
          refine sum_le_sum fun δ hδ => ?_
          rw [norm_mul]
          have hmu : ‖((μ δ : ℤ) : ℂ)‖ ≤ 1 := by
            rw [Complex.norm_intCast]
            exact_mod_cast ArithmeticFunction.abs_moebius_le_one
          calc _ ≤ 1 * Bq := mul_le_mul hmu (hper δ hδ) (norm_nonneg _) zero_le_one
            _ = Bq := one_mul _
      _ = ((2 * g).divisors.card : ℝ) * Bq := by rw [sum_const, nsmul_eq_mul]
  refine htot.trans ?_
  -- comparison with the `e`-quantities
  have hqe : q ≤ e := Nat.le_of_dvd he ⟨g, by rw [hq, mul_comm]⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hq0
  have hc1 : ((2 * g).divisors.card : ℝ) ≤ (2 * e).divisors.card := by
    exact_mod_cast card_divisors_le_of_dvd (by positivity) (mul_dvd_mul_left 2 ⟨q, hq⟩)
  have hc2 : (2 : ℝ) ^ q.primeFactors.card ≤ e.divisors.card := by
    have := (two_pow_card_primeFactors_le hq0).trans
      (card_divisors_le_of_dvd he0 ⟨g, by rw [hq, mul_comm]⟩)
    exact_mod_cast this
  have hc3 : Real.sqrt q * (1 + Real.log q) ≤ Real.sqrt e * (1 + Real.log e) := by
    have hqe' : (q : ℝ) ≤ e := by exact_mod_cast hqe
    gcongr
  have hc4 : (L : ℝ) / Real.sqrt q ≤ L * Real.sqrt |(h : ℝ)| / Real.sqrt e := by
    have hgh : (g : ℝ) ≤ |(h : ℝ)| := by
      have h1 : (g : ℤ) ≤ |h| := Int.le_of_dvd (abs_pos.2 hh) ((dvd_abs _ _).2 ⟨a, ha⟩)
      have h2 : ((g : ℤ) : ℝ) ≤ ((|h| : ℤ) : ℝ) := by exact_mod_cast h1
      rwa [Int.cast_abs, Int.cast_natCast] at h2
    have hsqe : Real.sqrt e = Real.sqrt g * Real.sqrt q := by
      rw [hq, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _)]
    have hg1 : 0 < Real.sqrt g := Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hg0)
    have hsq0 : 0 < Real.sqrt q := Real.sqrt_pos.2 (by linarith)
    rw [hsqe, div_le_div_iff₀ hsq0 (by positivity)]
    have : Real.sqrt g ≤ Real.sqrt |(h : ℝ)| := Real.sqrt_le_sqrt hgh
    have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
    calc (L : ℝ) * (Real.sqrt g * Real.sqrt q) = (L * Real.sqrt q) * Real.sqrt g := by ring
      _ ≤ (L * Real.sqrt q) * Real.sqrt |(h : ℝ)| :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = L * Real.sqrt |(h : ℝ)| * Real.sqrt q := by ring
  rw [hBq]
  have hA0 : 0 ≤ Real.sqrt q * (1 + Real.log q) + L / Real.sqrt q := by
    have := Real.log_nonneg hq1; positivity
  calc ((2 * g).divisors.card : ℝ) * ((2 : ℝ) ^ q.primeFactors.card *
        (Real.sqrt q * (1 + Real.log q) + L / Real.sqrt q) * (1 + 2 * |τ|))
      ≤ ((2 * e).divisors.card : ℝ) * ((e.divisors.card : ℝ) *
        (Real.sqrt e * (1 + Real.log e) + L * Real.sqrt |(h : ℝ)| / Real.sqrt e) *
          (1 + 2 * |τ|)) := by
        have hτ0 : 0 ≤ 1 + 2 * |τ| := by have := abs_nonneg τ; linarith
        have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
        have hE0 : 0 ≤ Real.sqrt e * (1 + Real.log e) + L * Real.sqrt |(h : ℝ)| / Real.sqrt e :=
          add_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by linarith [Real.log_nonneg he1]))
            (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))
              (Real.sqrt_nonneg _))
        have h2p : (0 : ℝ) ≤ (2 : ℝ) ^ q.primeFactors.card := pow_nonneg zero_le_two _
        refine mul_le_mul hc1 (mul_le_mul (mul_le_mul hc2 (add_le_add hc3 hc4) hA0
          (Nat.cast_nonneg _)) le_rfl hτ0 (mul_nonneg (Nat.cast_nonneg _) hE0))
          (mul_nonneg (mul_nonneg h2p hA0) hτ0) (Nat.cast_nonneg _)
    _ = _ := by ring

end MeanValue
end MobiusDeterminant
