import Mathlib

/-!
# The literature bar and the barrier at level `4/7`: machine-checked bookkeeping

Section "The literature bar and the barrier at `4/7`" of `paper/main.tex`
compares the exponent `9/17` of this project with what other methods give,
and reduces the problem of passing level `4/7` to one explicit estimate.
None of the analytic inputs discussed there (Deshouillers–Iwaniec, Irving,
Polymath8a, …) is formalized.  This file checks only

* the exponent arithmetic of that section (`B1`–`B7`), and
* the elementary algebraic identities behind its reformulations (`B8`).

So a statement such as `conrey_error_iff` below says: *if* the error term
has the stated shape, *then* it is a power saving exactly for `θ < 4/7`.
It does not say that the error term has that shape.

Conventions: sizes are exponents of `x`.  `θ` is the level, so the modulus
is `q = x^θ`; the dual length is `H = q²/x = x^{2θ-1}`; `L = q^{1/2}`.
-/

namespace MobiusDeterminant

namespace Barrier

/-! ## B1. From a saving to a level -/

/-- The level reached by a method that saves `q^κ` over the trivial bound. -/
noncomputable def levelOfSaving (κ : ℝ) : ℝ := 1 / (2 - κ)

/-- A saving `q^κ` beats the dual length `H = q²/x` exactly below the level
`1/(2-κ)`: in exponents of `x`, `2θ - 1 < κθ ↔ θ < 1/(2-κ)`. -/
theorem saving_suffices_iff {θ κ : ℝ} (hκ : κ < 2) :
    2 * θ - 1 < κ * θ ↔ θ < levelOfSaving κ := by
  have h : 0 < 2 - κ := by linarith
  unfold levelOfSaving
  rw [lt_div_iff₀ h]
  constructor <;> intro h' <;> nlinarith

/-- The dictionary of the paper: `κ = 1/48, 1/17, 1/9, 1/8, 1/4, 1/3, 2/5`
correspond to the levels `48/95, 17/33, 9/17, 8/15, 4/7, 3/5, 5/8`. -/
theorem level_table :
    levelOfSaving (1 / 48) = 48 / 95 ∧ levelOfSaving (1 / 17) = 17 / 33 ∧
    levelOfSaving (1 / 9) = 9 / 17 ∧ levelOfSaving (1 / 8) = 8 / 15 ∧
    levelOfSaving (1 / 4) = 4 / 7 ∧ levelOfSaving (1 / 3) = 3 / 5 ∧
    levelOfSaving (2 / 5) = 5 / 8 := by
  unfold levelOfSaving
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

/-- The levels in the dictionary are strictly increasing. -/
theorem level_chain :
    (1 / 2 : ℝ) < 48 / 95 ∧ (48 / 95 : ℝ) < 17 / 33 ∧ (17 / 33 : ℝ) < 9 / 17 ∧
    (9 / 17 : ℝ) < 8 / 15 ∧ (8 / 15 : ℝ) < 4 / 7 ∧ (4 / 7 : ℝ) < 3 / 5 ∧
    (3 / 5 : ℝ) < 5 / 8 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

/-! ## B2. Transposed estimates from the literature -/

/-- Irving's estimate transposed to `μ` (Remark "Comparison" of the paper)
gives cancellation when `11m + 4M > 7` and `4m + 7M > 5`.  On the diagonal
`m = M = x` this is `x > 7/15`. -/
theorem irving_diagonal_iff {x : ℝ} :
    (11 * x + 4 * x > 7 ∧ 4 * x + 7 * x > 5) ↔ x > 7 / 15 := by
  constructor
  · rintro ⟨h1, _⟩; linarith
  · intro h; constructor <;> linarith

/-- `x > 7/15` is the level `D = X^{1-x} < X^{8/15}`. -/
theorem irving_level {x : ℝ} : x > 7 / 15 ↔ 1 - x < 8 / 15 := by
  constructor <;> intro h <;> linarith

/-- At `M = 1/2` Irving's region is `m > 5/11`, smaller than the region
`m > 7/16` of the paper. -/
theorem irving_at_half {m : ℝ} :
    (11 * m + 4 * (1 / 2) > 7 ∧ 4 * m + 7 * (1 / 2) > 5) ↔ m > 5 / 11 := by
  constructor
  · rintro ⟨h1, _⟩; linarith
  · intro h; constructor <;> linarith

theorem irving_vs_omega_at_half : (7 / 16 : ℝ) < 5 / 11 := by norm_num

/-- The boundaries `11m + 4M = 7` and `8m + 9M = 8` cross at
`(31/67, 32/67)`. -/
theorem irving_crossing {m M : ℝ} :
    (11 * m + 4 * M = 7 ∧ 8 * m + 9 * M = 8) ↔ (m = 31 / 67 ∧ M = 32 / 67) := by
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨rfl, rfl⟩; constructor <;> norm_num

/-- Conrey's method through the Deshouillers–Iwaniec estimate, transposed to
the fixed shift, has error `N^ε (R^{7/4} + N^{1/2} R^{7/8})`.  With
`R = N^θ` both terms are a power saving over `N` exactly for `θ < 4/7`. -/
theorem conrey_error_iff {θ : ℝ} :
    (7 / 4 * θ < 1 ∧ 1 / 2 + 7 / 8 * θ < 1) ↔ θ < 4 / 7 := by
  constructor
  · rintro ⟨h1, _⟩; linarith
  · intro h; constructor <;> linarith

/-! ## B3. The window for a flexible factor -/

/-- Lower end of the window for the size of a factor `s` of the modulus. -/
def windowLo (θ : ℝ) : ℝ := 2 * θ - 1

/-- Upper end of the window, with the exceptional-spectrum term. -/
noncomputable def windowHi (θ : ℝ) : ℝ := min (2 * (1 - θ) / 3) (2 - 3 * θ)

/-- Upper end of the window without the exceptional-spectrum term. -/
noncomputable def windowHi' (θ : ℝ) : ℝ := 2 * (1 - θ) / 3

/-- The window is nonempty exactly up to level `3/5`. -/
theorem window_nonempty_iff {θ : ℝ} : windowLo θ ≤ windowHi θ ↔ θ ≤ 3 / 5 := by
  unfold windowLo windowHi
  rw [le_min_iff]
  constructor
  · rintro ⟨_, h2⟩; linarith
  · intro h; constructor <;> linarith

/-- Without the exceptional-spectrum term it is nonempty up to level `5/8`. -/
theorem window'_nonempty_iff {θ : ℝ} : windowLo θ ≤ windowHi' θ ↔ θ ≤ 5 / 8 := by
  unfold windowLo windowHi'
  constructor <;> intro h <;> linarith

/-- At `θ = 4/7` the window is `[1/7, 2/7]`. -/
theorem window_at_four_sevenths :
    windowLo (4 / 7) = 1 / 7 ∧ windowHi (4 / 7) = 2 / 7 := by
  unfold windowLo windowHi
  constructor
  · norm_num
  · rw [show (2 * (1 - 4 / 7) / 3 : ℝ) = 2 / 7 by norm_num,
      show (2 - 3 * (4 / 7) : ℝ) = 2 / 7 by norm_num, min_self]

/-- The balanced factorization `e = ℓ₁ℓ₂`, `ℓᵢ ≍ x^{θ/2}`, has a factor in
the window exactly up to level `4/7`. -/
theorem balanced_mem_window_iff {θ : ℝ} (hθ : 0 < θ) :
    (windowLo θ ≤ θ / 2 ∧ θ / 2 ≤ windowHi θ) ↔ θ ≤ 4 / 7 := by
  unfold windowLo windowHi
  rw [le_min_iff]
  constructor
  · rintro ⟨_, _, h3⟩; linarith
  · intro h; refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- Removing the exceptional-spectrum term does not help the balanced
factorization: the other upper bound is tight at the same level. -/
theorem balanced_mem_window'_iff {θ : ℝ} (hθ : 0 < θ) :
    (windowLo θ ≤ θ / 2 ∧ θ / 2 ≤ windowHi' θ) ↔ θ ≤ 4 / 7 := by
  unfold windowLo windowHi'
  constructor
  · rintro ⟨_, h2⟩; linarith
  · intro h; constructor <;> linarith

/-! ## B4. The stuck box -/

/-- The six-variable equation `b ℓ₁ ℓ₂ - a n₁ n₂ = 2` lives in the box
`(1-θ, θ/2, θ/2)²`; each side has size `x`. -/
theorem box_sum (θ : ℝ) : (1 - θ) + θ / 2 + θ / 2 = 1 := by ring

/-- At `θ = 4/7` the box is `(3/7, 2/7, 2/7)`. -/
theorem box_at_four_sevenths :
    (1 - 4 / 7 : ℝ) = 3 / 7 ∧ ((4 / 7 : ℝ) / 2) = 2 / 7 := by
  constructor <;> norm_num

/-- With `L = x^{θ/2}`, the dual length `H = x^{2θ-1}` equals `L^{1/2}`
exactly at `θ = 4/7`. -/
theorem dual_length_eq_iff {θ : ℝ} : 2 * θ - 1 = θ / 2 / 2 ↔ θ = 4 / 7 := by
  constructor <;> intro h <;> linarith

/-- The mean of the count in the variance form, `K = x^{1-3θ/2}`, equals
`L^{1/2}` exactly at `θ = 4/7`. -/
theorem mean_eq_iff {θ : ℝ} : 1 - 3 * θ / 2 = θ / 2 / 2 ↔ θ = 4 / 7 := by
  constructor <;> intro h <;> linarith

/-! ## B5. Three methods, one exponent -/

/-- All binding conditions of the Deshouillers–Iwaniec and the Polymath8a
Type III arguments read `H ≤ q^{1/4}` at `r = s = L`.  In exponents of `x`
this is `θ ≤ 4/7`. -/
theorem binding_condition_iff {θ : ℝ} : 2 * θ - 1 ≤ θ / 4 ↔ θ ≤ 4 / 7 := by
  constructor <;> intro h <;> linarith

/-- Deshouillers–Iwaniec: `H ≤ s`, `H ≤ √r`, `H ≤ r/√s` with `q = rs`.  At
`r = s = θ/2` (exponents of `x`) all three hold iff `θ ≤ 4/7`. -/
theorem di_conditions_balanced_iff {θ : ℝ} (hθ : 0 < θ) :
    (2 * θ - 1 ≤ θ / 2 ∧ 2 * θ - 1 ≤ θ / 2 / 2 ∧ 2 * θ - 1 ≤ θ / 2 - θ / 2 / 2)
      ↔ θ ≤ 4 / 7 := by
  constructor
  · rintro ⟨_, h2, _⟩; linarith
  · intro h; refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- Polymath8a Type III: the factor `R` of the modulus must satisfy
`4θ - 2 ≤ R ≤ 2 - 3θ`.  The interval is nonempty iff `θ ≤ 4/7`. -/
theorem polymath_window_nonempty_iff {θ : ℝ} : 4 * θ - 2 ≤ 2 - 3 * θ ↔ θ ≤ 4 / 7 := by
  constructor <;> intro h <;> linarith

/-- At `θ = 4/7` the Polymath window is the single point `2/7 = θ/2`, the
balanced factorization. -/
theorem polymath_window_at_four_sevenths :
    (4 * (4 / 7) - 2 : ℝ) = 2 / 7 ∧ (2 - 3 * (4 / 7) : ℝ) = 2 / 7 ∧
    ((4 / 7 : ℝ) / 2) = 2 / 7 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-- The no-go count for Cauchy–Schwarz, completion and square-root
cancellation (exponents of `q`): if the inner set has size `> 1/2` and the
completion saving `σ = min(M/2, N_O - M/2)` is `> 1/2`, where the outer dual
product has length `N_O ≤ 5/4`, then the modulus `M` of the correlation sum
is `< 3/2`. -/
theorem nogo_modulus_bound {M NO : ℝ} (hNO : NO ≤ 5 / 4)
    (hσ : 1 / 2 < min (M / 2) (NO - M / 2)) : M < 3 / 2 := by
  rw [lt_min_iff] at hσ
  linarith [hσ.2]

/-- Second half of the no-go count: once a dual variable is inside, the
outer dual product has length `N_O ≤ 1`, and with `M ≥ 3/2` (the modulus `q`
times one inner factor of size `1/2`) the saving is at most `1/4`. -/
theorem nogo_saving_bound {M NO : ℝ} (hNO : NO ≤ 1) (hM : 3 / 2 ≤ M) :
    min (M / 2) (NO - M / 2) ≤ 1 / 4 := by
  exact (min_le_right _ _).trans (by linarith)

/-! ## B6. Moments of the zeta function -/

/-- Level `θ` corresponds to a twist of length `T^ϑ` in the fourth moment,
`ϑ = θ/(2-θ)`. -/
noncomputable def momentLength (θ : ℝ) : ℝ := θ / (2 - θ)

theorem moment_table :
    momentLength (1 / 2) = 1 / 3 ∧ momentLength (4 / 7) = 2 / 5 ∧
    momentLength (3 / 5) = 3 / 7 ∧ momentLength (2 / 3) = 1 / 2 := by
  unfold momentLength
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num

/-- The inverse dictionary: `θ = 2ϑ/(1+ϑ)`. -/
theorem momentLength_inv {θ : ℝ} (hθ : θ < 2) :
    2 * momentLength θ / (1 + momentLength θ) = θ := by
  have h : (2 - θ) ≠ 0 := by linarith
  unfold momentLength
  have h2 : (1 + θ / (2 - θ)) = 2 / (2 - θ) := by field_simp; ring
  rw [h2]
  field_simp

/-! ## B7. The mean-square target `(LS)` (exponents of `L = q^{1/2}`) -/

/-- Cauchy–Schwarz over the `L` frequencies of one pair `(s, s')`, then the
sum over the `L²` pairs: a mean-square bound `L^{5-2δ}` gives `L^{5-δ}`. -/
theorem ls_to_pairs (δ : ℝ) : (1 + (5 - 2 * δ)) / 2 + 2 = 5 - δ := by ring

/-- The first Cauchy–Schwarz over the `L³` pairs `(r, d)`: a bound `L^{5-δ}`
for the squared inner sums gives `L^{4-δ/2}` for the dual sum, against the
trivial `L^{9/2}` and the required `L^{4-δ'}`. -/
theorem pairs_to_dual (δ : ℝ) : (3 + (5 - δ)) / 2 = 4 - δ / 2 := by ring

/-- The four sizes of the full mean square in the paper's table:
Weil termwise `13/2`, Bessel `5`, observed `9/2`; the target is anything
below `5`. -/
theorem ls_sizes :
    (3 / 2 + 2 * (5 / 2) : ℝ) = 13 / 2 ∧ (3 / 2 + 3 : ℝ) = 9 / 2 ∧
    (9 / 2 : ℝ) < 5 ∧ (5 : ℝ) < 13 / 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num

/-! ## B8. Elementary identities behind the reformulations -/

/-- The variance form.  Two solutions of `b r s - a d = 2` with the same
`(r, d)` satisfy `(b s - b' s') r = (a - a') d`. -/
theorem pair_of_solutions {a b s a' b' s' r d : ℤ}
    (h : b * r * s - a * d = 2) (h' : b' * r * s' - a' * d = 2) :
    (b * s - b' * s') * r = (a - a') * d := by
  linear_combination h - h'

/-- The count as a determinant equation: `det [[br, an₁], [n₂, s]]`. -/
theorem det_two (b r s a n₁ n₂ : ℤ) :
    Matrix.det !![b * r, a * n₁; n₂, s] = b * r * s - a * n₁ * n₂ := by
  rw [Matrix.det_fin_two_of]

/-- `xyz + uvw` is the determinant of a `3 × 3` matrix with three zero
entries.  With `(x, y, z, u, v, w) = (b, r, s, a, -n₁, n₂)` this is
`brs - an₁n₂`. -/
theorem det_three {R : Type*} [CommRing R] (x y z u v w : R) :
    Matrix.det !![x, u, 0; 0, y, v; w, 0, z] = x * y * z + u * v * w := by
  simp [Matrix.det_fin_three]

/-- Roots of a quadratic congruence.  If `D = qc² + d²` and `e` inverts `d`
modulo `D`, then `ν = ce` satisfies `qν² + 1 ≡ 0 (mod D)`. -/
theorem quadratic_root {q c d e : ℤ} (h : (q * c ^ 2 + d ^ 2) ∣ d * e - 1) :
    (q * c ^ 2 + d ^ 2) ∣ q * (c * e) ^ 2 + 1 := by
  obtain ⟨k, hk⟩ := h
  exact ⟨e ^ 2 - k * (d * e + 1), by linear_combination (-(d * e + 1)) * hk⟩

/-- The modulus `cq` is coprime to `D = qc² + d²` when it is coprime to `d`. -/
theorem coprime_modulus {q c d : ℤ} (h : IsCoprime (c * q) d) :
    IsCoprime (c * q) (q * c ^ 2 + d ^ 2) := by
  have h2 : IsCoprime (c * q) (d ^ 2) := h.pow_right
  have h3 : q * c ^ 2 + d ^ 2 = d ^ 2 + c * q * c := by ring
  rw [h3]
  exact h2.add_mul_left_right c

/-- The Kloosterman fraction as a quadratic root.  Let `x` invert `d` modulo
`cq` and `e` invert `d` modulo `D = qc² + d²`.  Then
`x/(cq) - ce/D - d/(cqD)` is an integer:
`inv(d)/(cq) ≡ ν/D + d/(qcD) (mod 1)` with `ν = ce`. -/
theorem kloosterman_fraction_eq_root {q c d x e : ℤ} (hcop : IsCoprime (c * q) d)
    (hx : (c * q) ∣ d * x - 1) (he : (q * c ^ 2 + d ^ 2) ∣ d * e - 1) :
    (c * q * (q * c ^ 2 + d ^ 2)) ∣
      x * (q * c ^ 2 + d ^ 2) - c ^ 2 * q * e - d := by
  refine (coprime_modulus hcop).mul_dvd ?_ ?_
  · obtain ⟨k, hk⟩ := hx
    exact ⟨c * x - c * e + d * k, by linear_combination d * hk⟩
  · obtain ⟨k, hk⟩ := he
    exact ⟨x - e + d * k, by linear_combination d * hk⟩

/-- Reciprocity for Kloosterman fractions.  If `x` inverts `k` modulo `m` and
`y` inverts `m` modulo `k`, then `x/m + y/k - 1/(km)` is an integer:
`inv(k)/m ≡ -inv(m)/k + 1/(km) (mod 1)`. -/
theorem reciprocity {k m x y : ℤ} (hcop : IsCoprime k m)
    (hx : m ∣ k * x - 1) (hy : k ∣ m * y - 1) :
    (k * m) ∣ k * x + m * y - 1 := by
  refine hcop.mul_dvd ?_ ?_
  · obtain ⟨j, hj⟩ := hy
    exact ⟨x + j, by linear_combination hj⟩
  · obtain ⟨j, hj⟩ := hx
    exact ⟨y + j, by linear_combination hj⟩

/-- Pairs of Kloosterman fractions.  Let `(x, z; cq, k)` and
`(x', z'; c'q, k')` have determinant `1`, and put `J = xc' - x'c`,
`j = zk' - z'k`.  Then `J/(cc'q)` and `j/(kk')` are the difference of the
fractions `inv(k)/(cq)`, `inv(k')/(c'q)` before and after reciprocity, and
`(-u, -j; qJ, u')` with `u = c'qz - x'k`, `u' = xk' - cqz'` has
determinant `1`. -/
theorem fraction_pair {x k z c q x' k' z' c' : ℤ}
    (h : x * k - c * q * z = 1) (h' : x' * k' - c' * q * z' = 1) :
    (x * c' - x' * c) * k * k' - (z * k' - z' * k) * c * c' * q = k' * c' - k * c ∧
    (c' * q * z - x' * k) * (x * k' - c * q * z') + 1
      = (x * c' - x' * c) * (z * k' - z' * k) * q := by
  constructor
  · linear_combination (c' * k') * h - (c * k) * h'
  · linear_combination (-(x' * k' - c' * q * z')) * h - h'

/-- The class of a row in `P¹(Z/q)`.  If `c̄c' - d'e' = 1` and `D` inverts `d'`
modulo `q`, then `c'·(c̄·D) ≡ D + e' (mod q)`: the class `c̄/d'` of the row
`(c̄, d')` is `inv(c')·(inv(d') + e')`. -/
theorem coset_class {q c' d' cbar e' D : ℤ} (h : cbar * c' - d' * e' = 1)
    (hD : q ∣ d' * D - 1) : q ∣ c' * (cbar * D) - (D + e') := by
  obtain ⟨k, hk⟩ := hD
  exact ⟨e' * k, by linear_combination D * h + e' * hk⟩

/-- One step of `q`-van der Corput in the frequency (exponents of `L`):
length `3/2`, modulus factors `q₁ = 1`, `q₂ = 2`.  The bound
`N^{1/2}(q₁^{1/2} + q₂^{1/4})` has exponent `5/4`, a saving of `1/4`
against the `1/2` that is needed. -/
theorem vdc_frequency :
    ((3 / 2 : ℝ) / 2 + max ((1 : ℝ) / 2) (2 / 4)) = 5 / 4 ∧
    ((3 / 2 : ℝ) - 5 / 4) = 1 / 4 ∧ (1 / 4 : ℝ) < 1 / 2 := by
  refine ⟨?_, by norm_num, by norm_num⟩
  rw [max_eq_left (by norm_num)]; norm_num

/-- The moment dictionary is about sizes only: at `ϑ = 2/5` the restricted
factorization gives the box `(3/7, 2/7, 2/7)` and the balanced one gives
`(2/7, 5/14, 5/14)` (exponents of `N = MT`, `M = T^{2/5}`). -/
theorem moment_boxes :
    ((2 / 5 : ℝ) / (1 + 2 / 5)) = 2 / 7 ∧ ((1 - 2 / 5 : ℝ) / (1 + 2 / 5)) = 3 / 7 ∧
    ((1 / 2 : ℝ) / (1 + 2 / 5)) = 5 / 14 ∧ (2 / 7 : ℝ) + 5 / 14 + 5 / 14 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num

/-! ## B9. Sizes in the literature checks -/

/-- The third regular-spectrum condition `s ≤ 3p - ϑ` of the window, with
`p = 1 - θ` and `ϑ = θ`, is implied by `s ≤ 2(1-θ)/3` for `θ ≤ 7/10`. -/
theorem window_third_condition {θ s : ℝ} (hθ : θ ≤ 7 / 10)
    (hs : s ≤ 2 * (1 - θ) / 3) : s ≤ 3 * (1 - θ) - θ := by
  linarith

/-- The quadratic divisor theorem of Bettin–Bui–Li–Radziwiłł needs its two
coefficient ranges to satisfy `AB < x^{1/2}`.  The three assignments of our
variables give `AB = x^{2-2θ}`, `x^θ`, `x^{1-θ/2}`; one of them is below
`x^{1/2}` only if `θ < 1/2` or `θ > 3/4`. -/
theorem bblr_range_iff {θ : ℝ} (hθ : θ ≤ 1) :
    (2 - 2 * θ < 1 / 2 ∨ θ < 1 / 2 ∨ 1 - θ / 2 < 1 / 2) ↔ (θ < 1 / 2 ∨ 3 / 4 < θ) := by
  constructor
  · rintro (h | h | h)
    · right; linarith
    · left; exact h
    · exfalso; linarith
  · rintro (h | h)
    · right; left; exact h
    · left; linarith

/-- Watt's bound saves `H^{1/2}`; the stuck estimate needs `H^{1+δ}`. -/
theorem watt_short {δ : ℝ} (hδ : 0 < δ) : (1 / 2 : ℝ) < 1 + δ := by linarith

/-- Level-aspect loss before Cauchy–Schwarz (exponents of `L`): the spectral
bound `L^{7/4} n₂^{1/2}` beats the target `L²` only for `n₂ < L^{1/2}`. -/
theorem level_loss_iff {ν : ℝ} : 7 / 4 + ν / 2 < 2 ↔ ν < 1 / 2 := by
  constructor <;> intro h <;> linarith

/-- The Type I estimate of Grimmelt–Merikoski in our ranges (exponents of
`L`): `K = 6`, window `X = 9/2`, `d = h = 2`.  The hypothesis `d ≤ X^{1/2}`
holds; the bound `D^{1/2} X^{1/2} (D^{1/2} + h^{1/4})` has exponent `17/4`,
which exceeds the single-`d` main term `X/d` of exponent `5/2`. -/
theorem gm_sizes :
    (2 : ℝ) ≤ (9 / 2) / 2 ∧
    ((2 : ℝ) / 2 + (9 / 2) / 2 + max ((2 : ℝ) / 2) (2 / 4)) = 17 / 4 ∧
    ((9 / 2 : ℝ) - 2) = 5 / 2 ∧ (5 / 2 : ℝ) < 17 / 4 := by
  refine ⟨by norm_num, ?_, by norm_num, by norm_num⟩
  rw [max_eq_left (by norm_num)]; norm_num

/-- Positivity alone: bounding the variance over the thin set of classes by
the variance over all classes loses `L^{1/2}` (exponents of `L`:
`(d/|R|)·K = 1 + 1/2` against the required `K² = 1`). -/
theorem positivity_gap : ((1 : ℝ) + 1 / 2) - 2 * (1 / 2) = 1 / 2 := by norm_num

/-! ## B9. The Kloosterman block (Experiment 5, statements (OP), (OP₁)) -/

/-- The conic behind the correlation lemma (`lem:corr`).  Over a field, put
`t = h c c' X + c'²` and `Y = -c/(h c') + c c'/(h t)`.  Then `(X, Y)` lies on
`c'²/X + c²/Y = -h c c'`, and `X + Y` is a Kloosterman phase in `t` plus the
constant `-(c² + c'²)/(h c c')`.  This is the computation modulo `q` that
turns `∑ₙ S(1,n;cq) S(1,n;c'q) e(hn/k)` into `S(1, h̄²; q)`. -/
theorem conic_param {K : Type*} [Field K] {h c c' X t : K} (hh : h ≠ 0) (hc : c ≠ 0)
    (hc' : c' ≠ 0) (hX : X ≠ 0) (ht : t ≠ 0) (htX : t = h * c * c' * X + c' ^ 2) :
    c' ^ 2 / X + c ^ 2 / (-c / (h * c') + c * c' / (h * t)) = -(h * c * c') ∧
    X + (-c / (h * c') + c * c' / (h * t))
      = t / (h * c * c') + c * c' / (h * t) - (c ^ 2 + c' ^ 2) / (h * c * c') := by
  have hY : -c / (h * c') + c * c' / (h * t) = -(c ^ 2 * X) / t := by
    field_simp
    rw [htX]; ring
  have hX' : X = (t - c' ^ 2) / (h * c * c') := by
    rw [htX]; field_simp; ring
  refine ⟨?_, ?_⟩
  · rw [hY]
    have : c ^ 2 / (-(c ^ 2 * X) / t) = -t / X := by field_simp
    rw [this, htX]; field_simp; ring
  · rw [hX']; field_simp; ring

/-- The same computation for general rows `m, m'` (the general form of
`lem:corr`): `m X + m' Y` is a Kloosterman phase in `t` with product of
coefficients `m m' / h²`, independent of `c, c'`, plus the constant
`-(m c'² + m' c²)/(h c c')`. -/
theorem conic_param_rows {K : Type*} [Field K] {h c c' X t m m' : K} (hh : h ≠ 0)
    (hc : c ≠ 0) (hc' : c' ≠ 0) (ht : t ≠ 0) (htX : t = h * c * c' * X + c' ^ 2) :
    m * X + m' * (-c / (h * c') + c * c' / (h * t))
      = m * t / (h * c * c') + m' * c * c' / (h * t)
        - (m * c' ^ 2 + m' * c ^ 2) / (h * c * c') ∧
    (m / (h * c * c')) * (m' * c * c' / h) = m * m' / h ^ 2 := by
  have hX' : X = (t - c' ^ 2) / (h * c * c') := by
    rw [htX]; field_simp; ring
  refine ⟨?_, ?_⟩
  · rw [hX']; field_simp; ring
  · field_simp

/-- The excluded point of the conic: `X = 0` exactly when `t = c'²`, and there
the phase `t/(hcc') + cc'/(ht) - (c² + c'²)/(hcc')` vanishes.  This is the
term `-1` in the correlation lemma. -/
theorem conic_excluded {K : Type*} [Field K] {h c c' : K} (hh : h ≠ 0) (hc : c ≠ 0)
    (hc' : c' ≠ 0) :
    c' ^ 2 / (h * c * c') + c * c' / (h * c' ^ 2) - (c ^ 2 + c' ^ 2) / (h * c * c') = 0 := by
  field_simp; ring

/-- Sizes for (OP) (exponents of `q`): rows `M = 1/2`, columns `N = 3/4`,
entries of mean square `-1`.  Frobenius norm `1/8`, independent-entry norm
`-1/8`, and the ratio of the Bessel bound `0` to the mean eigenvalue `N - 1`
is `1/4`. -/
theorem op_sizes :
    ((1 / 2 : ℝ) + 3 / 4 - 1) / 2 = 1 / 8 ∧
    (max (1 / 2 : ℝ) (3 / 4) - 1) / 2 = -1 / 8 ∧
    (0 : ℝ) - (3 / 4 - 1) = 1 / 4 := by
  refine ⟨by norm_num, ?_, by norm_num⟩
  rw [max_eq_right (by norm_num)]; norm_num

/-- Why the third moment could suffice and the second cannot (exponents of
`q`, in units of the mean eigenvalue): from `tr (KKᵀ)^k ≤ q^{1/2 + η}` one
gets top eigenvalue `≤ q^{(1/2 + η)/k}`, which beats Bessel's `1/4` iff
`η < k/4 - 1/2`; for `k = 2` this needs `η < 0`, for `k = 3` it allows
`η < 1/4`. -/
theorem moment_room {η : ℝ} (k : ℝ) (hk : 0 < k) :
    (1 / 2 + η) / k < 1 / 4 ↔ η < k / 4 - 1 / 2 := by
  rw [div_lt_iff₀ hk]; constructor <;> intro h <;> linarith

end Barrier

end MobiusDeterminant
