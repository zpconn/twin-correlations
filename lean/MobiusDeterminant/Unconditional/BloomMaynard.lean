import MobiusDeterminant.Unconditional.Interfaces
import LeanPool.MarkoffModP.BGS.NumberTheory.DivisorBound

/-!
# Bloom–Maynard: additive energy of rationals with small denominators (`m = 2`)

We prove `bloomMaynardE4 : BloomMaynardE4`: if `B ⊂ ℚ ∩ [0,1]` has all denominators `≤ Q`
and at most `n` elements of each exact denominator, then `E₄(B) ≪_ε Q^ε (Qn)²`.

The proof follows Bloom–Maynard (§3, Lemma `le:rat`) specialised to `m = 2`, but with a
*weighted* popularity threshold which avoids the dyadic decomposition of `lem-toref`.
Write `E₄(B) = ∑_{(c,b) ∈ B²} r(c + b)` with `r(s) = #{(b₁,b₂) ∈ B² : b₁ + b₂ = s}`.
Colour the edge `(a, b)` (`a = c + b = α/k`, `b = β/ℓ` reduced) by `(d, f)` with
`d = gcd(k, ℓ)`, `f = gcd((αℓ - βk)/d, d)`; there are at most `τ(k)²` colours at `a`.
Call the edge popular if `r(a) ≤ 2 τ(k)² · #{b' ∈ B : colour(a, b') = colour(a, b)}`.

* Non-popular edges carry at most `E₄(B)/2` (each `a` has at most `r(a)/2` non-popular
  neighbours).
* Popular edges with difference `c = γ/q` are sorted by the signature `(k/d, ℓ/d, d/f, f)`,
  whose first three entries divide `q`.  Within a signature class, a double count over the
  common neighbours `b'` (which all have `d ∣ den b'`) gives the bound
  `2 τ(k)² (2e + 1) n ⌊Q/d⌋ ≪ τ(k)² n Q / f`, since the numerators of the `a`'s sharing a
  neighbour are congruent modulo `(k/d) f` and lie in `[0, 2k]`.

Summing, `E₄(B) ≤ E₄(B)/2 + |B| · Q^{O(δ)} n Q log Q`, and the divisor bound
`τ(m) ≪_δ m^δ` (Lean Pool, `BGS.NumberTheory`) finishes the proof.  Elements `0 = 0/1` and
`1 = 1/1` need no special treatment.
-/

open Finset

namespace MobiusDeterminant
namespace BloomMaynard

/-- `rep B s = #{(b₁, b₂) ∈ B² : b₁ + b₂ = s}`. -/
def rep (B : Finset ℚ) (s : ℚ) : ℕ := ((B ×ˢ B).filter (fun p => p.1 + p.2 = s)).card

/-- `d = gcd(k, ℓ)` for `a = ·/k`, `b = ·/ℓ`. -/
def colD (a b : ℚ) : ℕ := Nat.gcd a.den b.den

/-- `N = (a ℓ - b k)/d`. -/
def colN (a b : ℚ) : ℤ :=
  a.num * ((b.den / colD a b : ℕ) : ℤ) - b.num * ((a.den / colD a b : ℕ) : ℤ)

/-- `f = gcd(N, d)`. -/
def colF (a b : ℚ) : ℕ := Int.gcd (colN a b) (colD a b)

/-- The colour `(d, f)` of the edge `(a, b)`. -/
def colour (a b : ℚ) : ℕ × ℕ := (colD a b, colF a b)

lemma colD_pos (a b : ℚ) : 0 < colD a b := Nat.gcd_pos_of_pos_left _ a.den_pos

lemma colD_dvd_left (a b : ℚ) : colD a b ∣ a.den := Nat.gcd_dvd_left _ _

lemma colD_dvd_right (a b : ℚ) : colD a b ∣ b.den := Nat.gcd_dvd_right _ _

lemma colF_dvd (a b : ℚ) : colF a b ∣ colD a b := by
  have h := Int.gcd_dvd_right (colN a b) (colD a b)
  exact Int.natCast_dvd_natCast.mp h

lemma colF_pos (a b : ℚ) : 0 < colF a b :=
  Int.gcd_pos_of_ne_zero_right _ (by exact_mod_cast (colD_pos a b).ne')

lemma colF_dvd_N (a b : ℚ) : (colF a b : ℤ) ∣ colN a b := Int.gcd_dvd_left _ _

lemma isCoprime_num_of_dvd (a : ℚ) {m : ℕ} (hm : m ∣ a.den) : IsCoprime a.num (m : ℤ) := by
  have h0 : IsCoprime a.num (a.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs]
    simpa using a.reduced
  exact h0.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.mpr hm)

lemma coprime_quot (a b : ℚ) :
    IsCoprime ((a.den / colD a b : ℕ) : ℤ) ((b.den / colD a b : ℕ) : ℤ) := by
  rw [Nat.isCoprime_iff_coprime]
  exact Nat.coprime_div_gcd_div_gcd (colD_pos a b)

lemma isCoprime_N_left (a b : ℚ) : IsCoprime (colN a b) ((a.den / colD a b : ℕ) : ℤ) := by
  have h1 : IsCoprime (a.num * ((b.den / colD a b : ℕ) : ℤ)) ((a.den / colD a b : ℕ) : ℤ) :=
    IsCoprime.mul_left (isCoprime_num_of_dvd a (Nat.div_dvd_of_dvd (colD_dvd_left a b)))
      (coprime_quot a b).symm
  have h2 := h1.add_mul_left_left (-b.num)
  unfold colN
  convert h2 using 1
  ring

lemma isCoprime_N_right (a b : ℚ) : IsCoprime (colN a b) ((b.den / colD a b : ℕ) : ℤ) := by
  have h1 : IsCoprime (b.num * ((a.den / colD a b : ℕ) : ℤ)) ((b.den / colD a b : ℕ) : ℤ) :=
    IsCoprime.mul_left (isCoprime_num_of_dvd b (Nat.div_dvd_of_dvd (colD_dvd_right a b)))
      (coprime_quot a b)
  have h2 := h1.neg_left.add_mul_left_left (a.num)
  unfold colN
  convert h2 using 1
  ring

lemma coprime_F_left (a b : ℚ) : Nat.Coprime (colF a b) (a.den / colD a b) := by
  rw [← Nat.isCoprime_iff_coprime]
  exact (isCoprime_N_left a b).of_isCoprime_of_dvd_left (colF_dvd_N a b)

lemma isCoprime_F_right (a b : ℚ) :
    IsCoprime (colF a b : ℤ) ((b.den / colD a b : ℕ) : ℤ) :=
  (isCoprime_N_right a b).of_isCoprime_of_dvd_left (colF_dvd_N a b)

/-- The basic identity `(a - b) · k' ℓ' d = N`. -/
lemma sub_mul_eq_N (a b : ℚ) :
    (a - b) * (((a.den / colD a b : ℕ) : ℚ) * ((b.den / colD a b : ℕ) : ℚ) * (colD a b : ℚ))
      = (colN a b : ℚ) := by
  have hk : ((a.den / colD a b : ℕ) : ℚ) * (colD a b : ℚ) = a.den := by
    exact_mod_cast Nat.div_mul_cancel (colD_dvd_left a b)
  have hl : ((b.den / colD a b : ℕ) : ℚ) * (colD a b : ℚ) = b.den := by
    exact_mod_cast Nat.div_mul_cancel (colD_dvd_right a b)
  have h1 : a * (((a.den / colD a b : ℕ) : ℚ) * (colD a b : ℚ)) = a.num := by
    rw [hk]; exact Rat.mul_den_eq_num a
  have h2 : b * (((b.den / colD a b : ℕ) : ℚ) * (colD a b : ℚ)) = b.num := by
    rw [hl]; exact Rat.mul_den_eq_num b
  unfold colN
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast]
  linear_combination ((b.den / colD a b : ℕ) : ℚ) * h1 - ((a.den / colD a b : ℕ) : ℚ) * h2

/-- Signature `(k', ℓ', e, f)` of the edge `(a, b)`, where `k' = k/d`, `ℓ' = ℓ/d`, `e = d/f`. -/
def sig (a b : ℚ) : ℕ × ℕ × ℕ × ℕ :=
  (a.den / colD a b, b.den / colD a b, colD a b / colF a b, colF a b)

lemma num_mul_eq (a b : ℚ) :
    (a - b).num * (((a.den / colD a b : ℕ) : ℤ) * ((b.den / colD a b : ℕ) : ℤ) * (colD a b : ℤ))
      = colN a b * (a - b).den := by
  have h := sub_mul_eq_N a b
  have h2 := Rat.mul_den_eq_num (a - b)
  have : ((a - b).num : ℚ) * (((a.den / colD a b : ℕ) : ℚ) * ((b.den / colD a b : ℕ) : ℚ)
      * (colD a b : ℚ)) = (colN a b : ℚ) * (a - b).den := by
    rw [← h2, ← h]; ring
  apply Int.cast_injective (α := ℚ)
  simp only [Int.cast_mul, Int.cast_natCast]
  exact this

lemma sig1_dvd (a b : ℚ) : a.den / colD a b ∣ (a - b).den := by
  have h := num_mul_eq a b
  have hdvd : ((a.den / colD a b : ℕ) : ℤ) ∣ colN a b * (a - b).den := by
    rw [← h]
    exact ⟨(a - b).num * (((b.den / colD a b : ℕ) : ℤ) * (colD a b : ℤ)), by ring⟩
  exact Int.natCast_dvd_natCast.mp ((isCoprime_N_left a b).symm.dvd_of_dvd_mul_left hdvd)

lemma sig2_dvd (a b : ℚ) : b.den / colD a b ∣ (a - b).den := by
  have h := num_mul_eq a b
  have hdvd : ((b.den / colD a b : ℕ) : ℤ) ∣ colN a b * (a - b).den := by
    rw [← h]
    exact ⟨(a - b).num * (((a.den / colD a b : ℕ) : ℤ) * (colD a b : ℤ)), by ring⟩
  exact Int.natCast_dvd_natCast.mp ((isCoprime_N_right a b).symm.dvd_of_dvd_mul_left hdvd)

lemma sig3_dvd (a b : ℚ) : colD a b / colF a b ∣ (a - b).den := by
  have h := num_mul_eq a b
  set f := colF a b with hf
  set d := colD a b with hd
  have hfpos : (0 : ℤ) < f := by exact_mod_cast colF_pos a b
  have hfd : f ∣ d := colF_dvd a b
  have hN : colN a b = f * (colN a b / f) := (Int.mul_ediv_cancel' (colF_dvd_N a b)).symm
  have hdd : (d : ℤ) = f * ((d / f : ℕ) : ℤ) := by
    exact_mod_cast (Nat.mul_div_cancel' hfd).symm
  have hcop : IsCoprime ((d / f : ℕ) : ℤ) (colN a b / f) := by
    have := Int.gcd_div_gcd_div_gcd (i := colN a b) (j := (d : ℤ)) (by
      have := colF_pos a b; simpa [colF] using this)
    rw [← Int.isCoprime_iff_gcd_eq_one] at this
    have hg : ((colN a b).gcd (d : ℤ) : ℤ) = f := rfl
    rw [hg] at this
    rw [Int.natCast_div]
    exact this.symm
  rw [hdd] at h
  conv_rhs at h => rw [hN]
  have h' : (a - b).num * (((a.den / d : ℕ) : ℤ) * ((b.den / d : ℕ) : ℤ) * ((d / f : ℕ) : ℤ))
      = (colN a b / f) * (a - b).den := by
    have hf0 : (f : ℤ) ≠ 0 := hfpos.ne'
    apply mul_left_cancel₀ hf0
    linear_combination h
  have hdvd : ((d / f : ℕ) : ℤ) ∣ (colN a b / f) * (a - b).den := by
    rw [← h']
    exact ⟨(a - b).num * (((a.den / d : ℕ) : ℤ) * ((b.den / d : ℕ) : ℤ)), by ring⟩
  exact Int.natCast_dvd_natCast.mp (hcop.dvd_of_dvd_mul_left hdvd)

lemma dvd_num_sub_of_same_class {a₁ b₁ a₂ b₂ : ℚ} (h : a₁ - b₁ = a₂ - b₂)
    (ha : a₁.den = a₂.den) (hb : b₁.den = b₂.den) :
    ((a₁.den / colD a₁ b₁ : ℕ) : ℤ) ∣ a₁.num - a₂.num := by
  have hD : colD a₂ b₂ = colD a₁ b₁ := by unfold colD; rw [ha, hb]
  have h1 := sub_mul_eq_N a₁ b₁
  have h2 := sub_mul_eq_N a₂ b₂
  rw [hD, ← ha, ← hb, ← h] at h2
  have hN : colN a₁ b₁ = colN a₂ b₂ := by exact_mod_cast h1.symm.trans h2
  unfold colN at hN
  rw [hD, ← ha, ← hb] at hN
  have : ((a₁.den / colD a₁ b₁ : ℕ) : ℤ) ∣ (a₁.num - a₂.num) * ((b₁.den / colD a₁ b₁ : ℕ) : ℤ) :=
    ⟨b₁.num - b₂.num, by linear_combination hN⟩
  exact (coprime_quot a₁ b₁).dvd_of_dvd_mul_right this

lemma dvd_num_sub_of_shared {a₁ a₂ b : ℚ} (ha : a₁.den = a₂.den)
    (hc : colour a₁ b = colour a₂ b) :
    (colF a₁ b : ℤ) ∣ a₁.num - a₂.num := by
  have hD : colD a₂ b = colD a₁ b := by unfold colD; rw [ha]
  have hF : colF a₂ b = colF a₁ b := (congrArg Prod.snd hc).symm
  have h1 := colF_dvd_N a₁ b
  have h2 := colF_dvd_N a₂ b
  rw [hF] at h2
  have h3 := dvd_sub h1 h2
  have : colN a₁ b - colN a₂ b = (a₁.num - a₂.num) * ((b.den / colD a₁ b : ℕ) : ℤ) := by
    unfold colN; rw [hD, ha]; ring
  rw [this] at h3
  exact (isCoprime_F_right a₁ b).dvd_of_dvd_mul_right h3

lemma card_le_of_dvd_sub (S : Finset ℤ) (m : ℤ) (t : ℕ) (hm : 0 < m)
    (hS : ∀ x ∈ S, 0 ≤ x ∧ x ≤ m * t) (hd : ∀ x ∈ S, ∀ y ∈ S, m ∣ x - y) :
    S.card ≤ t + 1 := by
  have key : S.card ≤ (Finset.Icc (0:ℤ) t).card := by
    apply Finset.card_le_card_of_injOn (fun x => x / m)
    · intro x hx
      simp only [Finset.coe_Icc, Set.mem_Icc]
      obtain ⟨h0, h1⟩ := hS x hx
      constructor
      · exact Int.ediv_nonneg h0 hm.le
      · calc x / m ≤ (m * t) / m := Int.ediv_le_ediv hm h1
          _ = t := by rw [Int.mul_ediv_cancel_left _ hm.ne']
    · intro x hx y hy hxy
      have hmod : x % m = y % m :=
        Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd (hd x hx y hy))
      have hx' := Int.emod_add_mul_ediv x m
      have hy' := Int.emod_add_mul_ediv y m
      simp only at hxy
      rw [← hx', ← hy', hmod, hxy]
  rw [Int.card_Icc] at key
  omega

/-- Neighbours of `a` in `B` along edges of colour `col`. -/
def nbr (B : Finset ℚ) (a : ℚ) (col : ℕ × ℕ) : Finset ℚ := B.filter (fun b => colour a b = col)

/-- The edge `(a, b)` is popular (weighted threshold `rep B a / (2 τ(k)²)`). -/
def Popular (B : Finset ℚ) (a b : ℚ) : Prop :=
  rep B a ≤ 2 * a.den.divisors.card ^ 2 * (nbr B a (colour a b)).card

instance (B : Finset ℚ) (a b : ℚ) : Decidable (Popular B a b) := by
  unfold Popular; infer_instance

lemma colour_mem (a b : ℚ) : colour a b ∈ a.den.divisors ×ˢ a.den.divisors := by
  simp only [colour, Finset.mem_product, Nat.mem_divisors]
  exact ⟨⟨colD_dvd_left a b, a.den_pos.ne'⟩,
    ⟨(colF_dvd a b).trans (colD_dvd_left a b), a.den_pos.ne'⟩⟩

lemma two_mul_card_nonpop_le (B : Finset ℚ) (a : ℚ) :
    2 * (B.filter (fun b => ¬ Popular B a b)).card ≤ rep B a := by
  set s := B.filter (fun b => ¬ Popular B a b) with hs_def
  set τ := a.den.divisors.card with hτ_def
  have hτ : 0 < τ := Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr a.den_pos.ne'⟩
  have hs := Finset.card_eq_sum_card_fiberwise (f := colour a) (s := s)
    (t := a.den.divisors ×ˢ a.den.divisors) (fun b _ => colour_mem a b)
  have hfib : ∀ col ∈ a.den.divisors ×ˢ a.den.divisors,
      2 * τ ^ 2 * (s.filter (fun b => colour a b = col)).card ≤ rep B a := by
    intro col _
    by_cases hne : (s.filter (fun b => colour a b = col)).Nonempty
    · obtain ⟨b₀, hb₀⟩ := hne
      simp only [s, Finset.mem_filter] at hb₀
      obtain ⟨⟨_, hnp⟩, hcol⟩ := hb₀
      unfold Popular at hnp
      rw [hcol] at hnp
      have hsub : (s.filter (fun b => colour a b = col)) ⊆ nbr B a col := by
        intro b hb
        simp only [s, nbr, Finset.mem_filter] at hb ⊢
        exact ⟨hb.1.1, hb.2⟩
      have := Finset.card_le_card hsub
      calc 2 * τ ^ 2 * _ ≤ 2 * τ ^ 2 * (nbr B a col).card := Nat.mul_le_mul_left _ this
        _ ≤ rep B a := (not_le.mp hnp).le
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]; simp
  have hsum : τ ^ 2 * (2 * s.card) ≤ τ ^ 2 * rep B a := by
    have : τ ^ 2 * (2 * s.card) = ∑ col ∈ a.den.divisors ×ˢ a.den.divisors,
        2 * τ ^ 2 * (s.filter (fun b => colour a b = col)).card := by
      rw [← Finset.mul_sum, ← hs]; ring
    rw [this]
    calc _ ≤ ∑ col ∈ a.den.divisors ×ˢ a.den.divisors, rep B a := Finset.sum_le_sum hfib
      _ = τ ^ 2 * rep B a := by
        rw [Finset.sum_const, Finset.card_product, smul_eq_mul]; ring
  exact Nat.le_of_mul_le_mul_left hsum (by positivity)

lemma energy4_eq (B : Finset ℚ) : energy4 B = ∑ p ∈ B ×ˢ B, rep B (p.1 + p.2) := by
  have h1 : energy4 B = (((B ×ˢ B) ×ˢ (B ×ˢ B)).filter
      (fun uv : (ℚ × ℚ) × (ℚ × ℚ) => uv.2.1 + uv.2.2 = uv.1.1 + uv.1.2)).card := by
    unfold energy4
    apply Finset.card_nbij' (fun x => ((x.2.2.1, x.2.2.2), (x.1, x.2.1)))
      (fun uv => (uv.2.1, uv.2.2, uv.1.1, uv.1.2))
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_product] at hx ⊢
      exact ⟨⟨⟨hx.1.2.2.1, hx.1.2.2.2⟩, ⟨hx.1.1, hx.1.2.1⟩⟩, hx.2⟩
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_product] at hx ⊢
      exact ⟨⟨hx.1.2.1, hx.1.2.2, hx.1.1.1, hx.1.1.2⟩, hx.2⟩
    · intro x _; rfl
    · intro x _; rfl
  rw [h1, Finset.card_filter, Finset.sum_product]
  apply Finset.sum_congr rfl; intro u _
  unfold rep; rw [Finset.card_filter]

lemma nonpop_sum_le (B : Finset ℚ) :
    2 * ∑ p ∈ (B ×ˢ B).filter (fun p => ¬ Popular B (p.1 + p.2) p.2), rep B (p.1 + p.2)
      ≤ energy4 B := by
  rw [energy4_eq]
  have h1 : ∑ p ∈ (B ×ˢ B).filter (fun p => ¬ Popular B (p.1 + p.2) p.2), rep B (p.1 + p.2)
      = ∑ p' ∈ B ×ˢ B, ((B ×ˢ B).filter
          (fun p => ¬ Popular B (p.1 + p.2) p.2 ∧ p.1 + p.2 = p'.1 + p'.2)).card := by
    unfold rep
    simp only [Finset.card_filter]
    rw [Finset.sum_filter]
    have hh : ∀ p ∈ B ×ˢ B, (if ¬ Popular B (p.1 + p.2) p.2 then
        ∑ i ∈ B ×ˢ B, (if i.1 + i.2 = p.1 + p.2 then 1 else 0) else 0)
        = ∑ i ∈ B ×ˢ B, (if ¬ Popular B (p.1 + p.2) p.2 ∧ p.1 + p.2 = i.1 + i.2 then 1 else 0) := by
      intro p _
      by_cases hp : Popular B (p.1 + p.2) p.2
      · simp [hp]
      · simp only [hp, not_false_eq_true, ↓reduceIte]
        apply Finset.sum_congr rfl; intro i _
        by_cases h : i.1 + i.2 = p.1 + p.2
        · simp [h]
        · have h' : ¬ (p.1 + p.2 = i.1 + i.2) := fun e => h e.symm
          simp [h, h']
    rw [Finset.sum_congr rfl hh, Finset.sum_comm]
  rw [h1, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p' _
  refine le_trans ?_ (two_mul_card_nonpop_le B (p'.1 + p'.2))
  apply Nat.mul_le_mul_left
  apply Finset.card_le_card_of_injOn (fun p => p.2)
  · intro p hp
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_product] at hp ⊢
    obtain ⟨⟨_, hp2⟩, hnp, he⟩ := hp
    rw [he] at hnp
    exact ⟨hp2, hnp⟩
  · intro p hp q hq hpq
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hp hq
    simp only at hpq
    have : p.1 = q.1 := by
      have h := hp.2.2.trans hq.2.2.symm
      rw [hpq] at h; exact add_right_cancel h
    exact Prod.ext this hpq

lemma pop_sum_eq (B : Finset ℚ) :
    ∑ p ∈ (B ×ˢ B).filter (fun p => Popular B (p.1 + p.2) p.2), rep B (p.1 + p.2)
      = ∑ c ∈ B, ∑ b ∈ B.filter (fun b => Popular B (c + b) b), rep B (c + b) := by
  rw [Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl; intro c _
  rw [Finset.sum_filter]

lemma card_filter_dvd_den_le {B : Finset ℚ} {Q n : ℕ} (hB : ∀ b ∈ B, b.den ≤ Q)
    (hn : ∀ q : ℕ, (B.filter (fun b => b.den = q)).card ≤ n) (d : ℕ) :
    (B.filter (fun b => d ∣ b.den)).card ≤ n * (Q / d) := by
  set S := B.filter (fun b => d ∣ b.den) with hS
  have hmaps : Set.MapsTo (fun b : ℚ => b.den) (S : Set ℚ)
      ((Finset.Ioc 0 Q).filter (fun x => d ∣ x) : Set ℕ) := by
    intro b hb
    simp only [S, Finset.coe_filter, Finset.mem_Ioc, Set.mem_ofPred_eq] at hb ⊢
    exact ⟨⟨b.den_pos, hB b hb.1⟩, hb.2⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  calc ∑ ℓ ∈ (Finset.Ioc 0 Q).filter (fun x => d ∣ x), (S.filter (fun b => b.den = ℓ)).card
      ≤ ∑ ℓ ∈ (Finset.Ioc 0 Q).filter (fun x => d ∣ x), n := by
        apply Finset.sum_le_sum; intro ℓ _
        exact le_trans (Finset.card_le_card
          (Finset.filter_subset_filter _ (Finset.filter_subset _ _))) (hn ℓ)
    _ = n * (Q / d) := by
        rw [Finset.sum_const, Nat.Ioc_filter_dvd_card_eq_div, smul_eq_mul, mul_comm]

/-- Main counting step: the popular edges from `c` with a fixed signature. -/
lemma class_sum_le {B : Finset ℚ} {Q n : ℕ}
    (hB : ∀ b ∈ B, 0 ≤ b ∧ b ≤ 1 ∧ b.den ≤ Q)
    (hn : ∀ q : ℕ, (B.filter (fun b => b.den = q)).card ≤ n)
    {c : ℚ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (k' l' e f : ℕ) :
    ∑ b ∈ (B.filter (fun b => Popular B (c + b) b)).filter
        (fun b => sig (c + b) b = (k', l', e, f)), rep B (c + b)
      ≤ 2 * (k' * (e * f)).divisors.card ^ 2 * ((2 * e + 1) * (n * (Q / (e * f)))) := by
  set T := (B.filter (fun b => Popular B (c + b) b)).filter
    (fun b => sig (c + b) b = (k', l', e, f)) with hT_def
  have hT : ∀ b ∈ T, b ∈ B ∧ Popular B (c + b) b ∧ (c + b).den = k' * (e * f) ∧
      b.den = l' * (e * f) ∧ colour (c + b) b = (e * f, f) ∧
      (c + b).den / colD (c + b) b = k' ∧ colF (c + b) b = f := by
    intro b hb
    simp only [T, Finset.mem_filter, sig, Prod.mk.injEq] at hb
    obtain ⟨⟨hbB, hpop⟩, h1, h2, h3, h4⟩ := hb
    have hD : colD (c + b) b = e * f := by
      rw [← h3, ← h4, Nat.div_mul_cancel (colF_dvd _ _)]
    refine ⟨hbB, hpop, ?_, ?_, ?_, h1, h4⟩
    · rw [← h1, ← hD, Nat.div_mul_cancel (colD_dvd_left _ _)]
    · rw [← h2, ← hD, Nat.div_mul_cancel (colD_dvd_right _ _)]
    · simp only [colour, hD, h4]
  set τ := (k' * (e * f)).divisors.card
  -- Step 1: popularity
  have step1 : ∑ b ∈ T, rep B (c + b) ≤ ∑ b ∈ T, 2 * τ ^ 2 * (nbr B (c + b) (e * f, f)).card := by
    apply Finset.sum_le_sum; intro b hb
    obtain ⟨_, hpop, hden, _, hcol, _, _⟩ := hT b hb
    unfold Popular at hpop
    rw [hden, hcol] at hpop
    exact hpop
  -- Step 2: double counting
  have step2 : ∑ b ∈ T, (nbr B (c + b) (e * f, f)).card
      = ∑ b' ∈ B, (T.filter (fun b => colour (c + b) b' = (e * f, f))).card := by
    unfold nbr
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  -- Step 3: each `b'` is shared by few `b`
  have step3 : ∀ b' ∈ B, (T.filter (fun b => colour (c + b) b' = (e * f, f))).card
      ≤ if e * f ∣ b'.den then 2 * e + 1 else 0 := by
    intro b' _
    set U := T.filter (fun b => colour (c + b) b' = (e * f, f)) with hU
    have hU' : ∀ b ∈ U, b ∈ T ∧ colour (c + b) b' = (e * f, f) := by
      intro b hb; simpa [U] using hb
    split_ifs with hdvd
    · have hinj : Set.InjOn (fun b : ℚ => (c + b).num) (U : Set ℚ) := by
        intro b₁ hb₁ b₂ hb₂ h
        have h1 := (hT b₁ (hU' b₁ hb₁).1).2.2.1
        have h2 := (hT b₂ (hU' b₂ hb₂).1).2.2.1
        have : c + b₁ = c + b₂ := Rat.ext h (h1.trans h2.symm)
        exact add_left_cancel this
      rcases U.eq_empty_or_nonempty with hUe | ⟨b₀, hb₀⟩
      · rw [hUe]; simp
      obtain ⟨_, _, hden₀, _, _, _, hf₀⟩ := hT b₀ (hU' b₀ hb₀).1
      have hkpos : 0 < k' * (e * f) := hden₀ ▸ (c + b₀).den_pos
      have hk'pos : 0 < k' := Nat.pos_of_mul_pos_right hkpos
      have hfpos : 0 < f := hf₀ ▸ colF_pos _ _
      rw [← Finset.card_image_of_injOn hinj]
      apply card_le_of_dvd_sub _ ((k' : ℤ) * f) (2 * e)
      · exact_mod_cast Nat.mul_pos hk'pos hfpos
      · intro x hx
        rw [Finset.mem_image] at hx
        obtain ⟨b, hb, rfl⟩ := hx
        obtain ⟨hbB, _, hden, _⟩ := hT b (hU' b hb).1
        have hb0 := (hB b hbB).1
        have hb1 := (hB b hbB).2.1
        constructor
        · exact Rat.num_nonneg.mpr (by linarith)
        · have h := Rat.mul_den_eq_num (c + b)
          have : ((c + b).num : ℚ) ≤ ((k' * f * (2 * e) : ℕ) : ℚ) := by
            rw [← h, hden]
            push_cast
            have h2 : (c + b) ≤ 2 := by linarith
            have hX : (0 : ℚ) ≤ k' * (e * f) := by positivity
            nlinarith [mul_le_mul_of_nonneg_right h2 hX]
          exact_mod_cast this
      · intro x hx y hy
        rw [Finset.mem_image] at hx hy
        obtain ⟨b₁, hb₁, rfl⟩ := hx
        obtain ⟨b₂, hb₂, rfl⟩ := hy
        obtain ⟨_, _, hden₁, hl₁, _, hk₁, hf₁⟩ := hT b₁ (hU' b₁ hb₁).1
        obtain ⟨_, _, hden₂, hl₂, _, _, _⟩ := hT b₂ (hU' b₂ hb₂).1
        have hA : (k' : ℤ) ∣ (c + b₁).num - (c + b₂).num := by
          have := dvd_num_sub_of_same_class (a₁ := c + b₁) (b₁ := b₁) (a₂ := c + b₂) (b₂ := b₂)
            (by ring) (hden₁.trans hden₂.symm) (hl₁.trans hl₂.symm)
          rwa [hk₁] at this
        have hF : (f : ℤ) ∣ (c + b₁).num - (c + b₂).num := by
          have := dvd_num_sub_of_shared (a₁ := c + b₁) (a₂ := c + b₂) (b := b')
            (hden₁.trans hden₂.symm) ((hU' b₁ hb₁).2.trans (hU' b₂ hb₂).2.symm)
          have hf' : colF (c + b₁) b' = f := congrArg Prod.snd (hU' b₁ hb₁).2
          rwa [hf'] at this
        have hcop : IsCoprime (k' : ℤ) (f : ℤ) := by
          have := coprime_F_left (c + b₁) b₁
          rw [hk₁, hf₁] at this
          exact Nat.isCoprime_iff_coprime.mpr this.symm
        exact hcop.mul_dvd hA hF
    · apply le_of_eq
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro b hb
      have hcol := (hU' b hb).2
      have : colD (c + b) b' = e * f := congrArg Prod.fst hcol
      exact hdvd (this ▸ colD_dvd_right (c + b) b')
  calc ∑ b ∈ T, rep B (c + b) ≤ ∑ b ∈ T, 2 * τ ^ 2 * (nbr B (c + b) (e * f, f)).card := step1
    _ = 2 * τ ^ 2 * ∑ b' ∈ B, (T.filter (fun b => colour (c + b) b' = (e * f, f))).card := by
        rw [← Finset.mul_sum, step2]
    _ ≤ 2 * τ ^ 2 * ∑ b' ∈ B, (if e * f ∣ b'.den then 2 * e + 1 else 0) := by
        apply Nat.mul_le_mul_left; exact Finset.sum_le_sum step3
    _ = 2 * τ ^ 2 * ((2 * e + 1) * (B.filter (fun b => e * f ∣ b.den)).card) := by
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm (B.filter _).card]
    _ ≤ _ := by
        apply Nat.mul_le_mul_left; apply Nat.mul_le_mul_left
        exact card_filter_dvd_den_le (fun b hb => (hB b hb).2.2) hn _

/-- The possible signatures `(k', ℓ', e, f)` of edges with difference of denominator `q`. -/
def sigSet (q Q : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  q.divisors ×ˢ q.divisors ×ˢ q.divisors ×ˢ Finset.Icc 1 Q

/-- The bound of `class_sum_le` for the signature `σ`. -/
def classBound (n Q : ℕ) (σ : ℕ × ℕ × ℕ × ℕ) : ℕ :=
  2 * (σ.1 * (σ.2.2.1 * σ.2.2.2)).divisors.card ^ 2 *
    ((2 * σ.2.2.1 + 1) * (n * (Q / (σ.2.2.1 * σ.2.2.2))))

lemma sig_mem {Q : ℕ} {c b : ℚ} (hb : b.den ≤ Q) : sig (c + b) b ∈ sigSet c.den Q := by
  have hc : (c + b) - b = c := add_sub_cancel_right c b
  have h1 := sig1_dvd (c + b) b
  have h2 := sig2_dvd (c + b) b
  have h3 := sig3_dvd (c + b) b
  rw [hc] at h1 h2 h3
  simp only [sig, sigSet, Finset.mem_product, Nat.mem_divisors, Finset.mem_Icc]
  refine ⟨⟨h1, c.den_pos.ne'⟩, ⟨h2, c.den_pos.ne'⟩, ⟨h3, c.den_pos.ne'⟩, colF_pos _ _, ?_⟩
  exact le_trans (Nat.le_of_dvd b.den_pos ((colF_dvd _ _).trans (colD_dvd_right _ _))) hb

lemma pop_sum_le {B : Finset ℚ} {Q n : ℕ}
    (hB : ∀ b ∈ B, 0 ≤ b ∧ b ≤ 1 ∧ b.den ≤ Q)
    (hn : ∀ q : ℕ, (B.filter (fun b => b.den = q)).card ≤ n) :
    ∑ p ∈ (B ×ˢ B).filter (fun p => Popular B (p.1 + p.2) p.2), rep B (p.1 + p.2)
      ≤ ∑ c ∈ B, ∑ σ ∈ sigSet c.den Q, classBound n Q σ := by
  rw [pop_sum_eq]
  apply Finset.sum_le_sum; intro c hc
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun b => sig (c + b) b) (t := sigSet c.den Q)
    (fun b hb => sig_mem ((hB b (Finset.mem_filter.mp hb).1).2.2))]
  apply Finset.sum_le_sum; intro σ _
  obtain ⟨k', l', e, f⟩ := σ
  exact class_sum_le hB hn (hB c hc).1 (hB c hc).2.1 k' l' e f

theorem energy4_le_nat {B : Finset ℚ} {Q n : ℕ}
    (hB : ∀ b ∈ B, 0 ≤ b ∧ b ≤ 1 ∧ b.den ≤ Q)
    (hn : ∀ q : ℕ, (B.filter (fun b => b.den = q)).card ≤ n) :
    energy4 B ≤ 2 * ∑ c ∈ B, ∑ σ ∈ sigSet c.den Q, classBound n Q σ := by
  have hsplit := Finset.sum_filter_add_sum_filter_not (B ×ˢ B)
    (fun p => Popular B (p.1 + p.2) p.2) (fun p => rep B (p.1 + p.2))
  rw [← energy4_eq] at hsplit
  have h1 := pop_sum_le hB hn
  have h2 := nonpop_sum_le B
  omega

lemma card_le_mul {B : Finset ℚ} {Q n : ℕ} (hB : ∀ b ∈ B, b.den ≤ Q)
    (hn : ∀ q : ℕ, (B.filter (fun b => b.den = q)).card ≤ n) : B.card ≤ Q * n := by
  have hmaps : Set.MapsTo (fun b : ℚ => b.den) (B : Set ℚ) (Finset.Icc 1 Q : Set ℕ) := by
    intro b hb
    simp only [Finset.coe_Icc, Set.mem_Icc]
    exact ⟨b.den_pos, hB b hb⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  calc ∑ q ∈ Finset.Icc 1 Q, (B.filter (fun b => b.den = q)).card ≤ ∑ q ∈ Finset.Icc 1 Q, n :=
        Finset.sum_le_sum (fun q _ => hn q)
    _ = Q * n := by simp

/-! ### Analytic bookkeeping -/

lemma divisor_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ m : ℕ, 1 ≤ m → (m.divisors.card : ℝ) ≤ C * (m : ℝ) ^ δ := by
  obtain ⟨N, hN⟩ := BGS.NumberTheory.exists_threshold_card_divisors_le_rpow hδ
  refine ⟨N + 1, by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)], fun m hm => ?_⟩
  have hm1 : (1 : ℝ) ≤ (m : ℝ) ^ δ := Real.one_le_rpow (by exact_mod_cast hm) hδ.le
  by_cases h : N ≤ m
  · have := hN m h
    nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  · replace h := not_le.mp h
    have h1 : (m.divisors.card : ℝ) ≤ m := by exact_mod_cast Nat.card_divisors_le_self m
    have h2 : (m : ℝ) ≤ N := by exact_mod_cast h.le
    nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]

lemma sum_sigSet (q Q : ℕ) (g : ℕ → ℝ) :
    ∑ σ ∈ sigSet q Q, g σ.2.2.2 = (q.divisors.card : ℝ) ^ 3 * ∑ f ∈ Finset.Icc 1 Q, g f := by
  simp only [sigSet, Finset.sum_product, Finset.sum_const, nsmul_eq_mul]
  ring

lemma harmonic_sum_le (Q : ℕ) :
    ∑ f ∈ Finset.Icc 1 Q, (1 / (f : ℝ)) ≤ 1 + Real.log Q := by
  have h := harmonic_le_one_add_log Q
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  simpa [one_div] using h

lemma classBound_le {C δ : ℝ} (hδ : 0 < δ) (hC1 : 1 ≤ C)
    (hC : ∀ m : ℕ, 1 ≤ m → (m.divisors.card : ℝ) ≤ C * (m : ℝ) ^ δ)
    {Q n q : ℕ} (hQ : 1 ≤ Q) (hq : q ≤ Q) {σ : ℕ × ℕ × ℕ × ℕ} (hσ : σ ∈ sigSet q Q) :
    (classBound n Q σ : ℝ) ≤ 6 * (C * ((Q : ℝ) ^ δ) ^ 3) ^ 2 * n * Q * (1 / (σ.2.2.2 : ℝ)) := by
  obtain ⟨k', l', e, f⟩ := σ
  simp only [sigSet, Finset.mem_product, Nat.mem_divisors, Finset.mem_Icc] at hσ
  obtain ⟨⟨hk, hq0⟩, _, ⟨he, _⟩, hf1, hfQ⟩ := hσ
  have hk' : k' ≤ Q := (Nat.le_of_dvd (Nat.pos_of_ne_zero hq0) hk).trans hq
  have he' : e ≤ Q := (Nat.le_of_dvd (Nat.pos_of_ne_zero hq0) he).trans hq
  have hk1 : 1 ≤ k' := Nat.pos_of_dvd_of_pos hk (Nat.pos_of_ne_zero hq0)
  have he1 : 1 ≤ e := Nat.pos_of_dvd_of_pos he (Nat.pos_of_ne_zero hq0)
  set m := k' * (e * f) with hm
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hmQ : m ≤ Q ^ 3 := by
    calc m ≤ Q * (Q * Q) := Nat.mul_le_mul hk' (Nat.mul_le_mul he' hfQ)
      _ = Q ^ 3 := by ring
  have hQ0 : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
  have hτ : (m.divisors.card : ℝ) ≤ C * ((Q : ℝ) ^ δ) ^ 3 := by
    calc (m.divisors.card : ℝ) ≤ C * (m : ℝ) ^ δ := hC m hm1
      _ ≤ C * ((Q : ℝ) ^ 3) ^ δ := by
          gcongr
          exact_mod_cast hmQ
      _ = C * ((Q : ℝ) ^ δ) ^ 3 := by rw [Real.rpow_pow_comm hQ0]
  have hdiv : ((Q / (e * f) : ℕ) : ℝ) ≤ (Q : ℝ) / ((e : ℝ) * f) := by
    have := Nat.cast_div_le (α := ℝ) (m := Q) (n := e * f)
    simpa using this
  have he1' : (1 : ℝ) ≤ e := by exact_mod_cast he1
  have hf1' : (1 : ℝ) ≤ f := by exact_mod_cast hf1
  have h3 : ((2 * e + 1 : ℕ) : ℝ) * ((Q / (e * f) : ℕ) : ℝ) ≤ 3 * Q * (1 / (f : ℝ)) := by
    calc ((2 * e + 1 : ℕ) : ℝ) * ((Q / (e * f) : ℕ) : ℝ) ≤ (3 * e) * ((Q : ℝ) / ((e : ℝ) * f)) := by
          gcongr
          · push_cast; linarith
      _ = 3 * Q * (1 / (f : ℝ)) := by field_simp
  unfold classBound
  simp only
  rw [← hm]
  have hτ0 : (0 : ℝ) ≤ m.divisors.card := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  calc ((2 * m.divisors.card ^ 2 * ((2 * e + 1) * (n * (Q / (e * f)))) : ℕ) : ℝ)
      = 2 * (m.divisors.card : ℝ) ^ 2 * n *
          (((2 * e + 1 : ℕ) : ℝ) * ((Q / (e * f) : ℕ) : ℝ)) := by push_cast; ring
    _ ≤ 2 * (C * ((Q : ℝ) ^ δ) ^ 3) ^ 2 * n * (3 * Q * (1 / (f : ℝ))) := by
        gcongr
    _ = 6 * (C * ((Q : ℝ) ^ δ) ^ 3) ^ 2 * n * Q * (1 / (f : ℝ)) := by ring

end BloomMaynard

open BloomMaynard in
/-- **Bloom–Maynard, Theorem 2 with `m = 2`**, with a `Q^ε` loss. -/
theorem bloomMaynardE4 : BloomMaynardE4 := by
  intro ε hε
  set δ := ε / 10 with hδ_def
  have hδ : 0 < δ := by positivity
  obtain ⟨C, hC1, hC⟩ := divisor_bound hδ
  refine ⟨12 * C ^ 5 * (1 + 1 / δ), by positivity, ?_⟩
  intro Q n B hQ _ hB hn
  set X := (Q : ℝ) ^ δ with hX
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hX1 : 1 ≤ X := Real.one_le_rpow hQ1 hδ.le
  have hXε : X ^ 10 = (Q : ℝ) ^ ε := by
    rw [hX, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    rw [hδ_def]; push_cast; ring
  have hH : ∑ f ∈ Finset.Icc 1 Q, (1 / (f : ℝ)) ≤ (1 + 1 / δ) * X := by
    have h1 := harmonic_sum_le Q
    have h2 : Real.log Q ≤ X / δ := Real.log_le_rpow_div (by positivity) hδ
    have h3 : X / δ = (1 / δ) * X := by ring
    have h4 : 0 ≤ 1 / δ := by positivity
    nlinarith
  set K := 6 * (C * X ^ 3) ^ 2 * n * Q with hK_def
  have hK : 0 ≤ K := by positivity
  have hc : ∀ c ∈ B, (∑ σ ∈ sigSet c.den Q, (classBound n Q σ : ℝ))
      ≤ (C * X) ^ 3 * K * ((1 + 1 / δ) * X) := by
    intro c hcB
    have hq : c.den ≤ Q := (hB c hcB).2.2
    have hτ : (c.den.divisors.card : ℝ) ≤ C * X := by
      calc _ ≤ C * (c.den : ℝ) ^ δ := hC _ c.den_pos
        _ ≤ C * X := mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hq) hδ.le) (by linarith)
    have hHnn : 0 ≤ ∑ f ∈ Finset.Icc 1 Q, (1 / (f : ℝ)) :=
      Finset.sum_nonneg (fun _ _ => by positivity)
    calc ∑ σ ∈ sigSet c.den Q, (classBound n Q σ : ℝ)
        ≤ ∑ σ ∈ sigSet c.den Q, K * (1 / (σ.2.2.2 : ℝ)) :=
          Finset.sum_le_sum (fun σ hσ => classBound_le hδ hC1 hC hQ hq hσ)
      _ = (c.den.divisors.card : ℝ) ^ 3 * ∑ f ∈ Finset.Icc 1 Q, K * (1 / (f : ℝ)) :=
          sum_sigSet _ _ (fun f => K * (1 / (f : ℝ)))
      _ = (c.den.divisors.card : ℝ) ^ 3 * K * ∑ f ∈ Finset.Icc 1 Q, (1 / (f : ℝ)) := by
          rw [← Finset.mul_sum]; ring
      _ ≤ (C * X) ^ 3 * K * ((1 + 1 / δ) * X) := by gcongr
  have hmain := energy4_le_nat hB hn
  have hcard := card_le_mul (fun b hb => (hB b hb).2.2) hn
  have hpos : 0 ≤ (C * X) ^ 3 * K * ((1 + 1 / δ) * X) := by positivity
  have hE : (energy4 B : ℝ) ≤ 2 * ((Q * n : ℕ) : ℝ) * ((C * X) ^ 3 * K * ((1 + 1 / δ) * X)) := by
    calc (energy4 B : ℝ)
        ≤ ((2 * ∑ c ∈ B, ∑ σ ∈ sigSet c.den Q, classBound n Q σ : ℕ) : ℝ) := by
          exact_mod_cast hmain
      _ = 2 * ∑ c ∈ B, ∑ σ ∈ sigSet c.den Q, (classBound n Q σ : ℝ) := by push_cast; ring
      _ ≤ 2 * ∑ c ∈ B, ((C * X) ^ 3 * K * ((1 + 1 / δ) * X)) := by
          gcongr with c hcB; exact hc c hcB
      _ = 2 * (B.card : ℝ) * ((C * X) ^ 3 * K * ((1 + 1 / δ) * X)) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ 2 * ((Q * n : ℕ) : ℝ) * ((C * X) ^ 3 * K * ((1 + 1 / δ) * X)) := by
          gcongr
  calc (energy4 B : ℝ) ≤ _ := hE
    _ = 12 * C ^ 5 * (1 + 1 / δ) * X ^ 10 * ((Q : ℝ) * n) ^ 2 := by
        rw [hK_def]; push_cast; ring
    _ = 12 * C ^ 5 * (1 + 1 / δ) * (Q : ℝ) ^ ε * ((Q : ℝ) * n) ^ 2 := by rw [hXε]

end MobiusDeterminant
