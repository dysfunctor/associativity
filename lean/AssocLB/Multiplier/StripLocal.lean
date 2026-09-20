/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/
import AssocLB.Multiplier.Encoding

/-!
# Strip-local multipliers

Paper: Section 4 (Strip-local multipliers): Definition [def:g-strip] (`g`-strip), Definition
[def:g-sparse] (`g`-sparse restriction), Definition [def:strip-local] (strip-local).

## Main definitions

* `InStrip g b c`: the column `c` lies in the `g`-strip with base `b * g`, the interval of
  columns `[b*g, (b+1)*g)`. A `g`-column is a column divisible by `g`.
* `InputRestriction n`: a restriction of the input bit-vectors of an `n`-bit multiplier, a
  partial assignment to the bits of `x` and of `y`. `InputRestriction.Extends ρ x y` says that
  the bit-vectors `x, y` agree with `ρ` on the assigned bits.
* `InputRestriction.ForcedZero ρ i j`: the partial product `t_{i,j}` is forced to `0`, since
  `ρ` sets `x_i` or `y_j` to `0`; `InputRestriction.liveInColumn ρ c` is the set of partial
  products not forced to `0` in column `c`.
* `InputRestriction.IsSparse ρ g`: Definition [def:g-sparse].
* `MulEncoding.LocalAt M ρ g b w`: under `ρ`, the wire `w` computes a Boolean function of the
  partial products of the `g`-strip with base `b * g`. `MulEncoding.WiresStripLocal M`: under
  every `g`-sparse restriction, every wire is a function of the partial products of a single
  strip. `StripLocal M`, for a family `M : ∀ n, MulEncoding n`: the clauses have bounded width
  and every member's wires are strip-local, Definition [def:strip-local].
* `ppCount x y c`: the number of partial products in column `c` that evaluate to `1`.

## Main results

* `Bits.toNat_mul_toNat_eq_sum_ppCount`: the product is the column-wise sum
  `∑ c, ppCount x y c · 2^c`.
* `MulEncoding.toNat_strip_eq_ppCount`, Observation [obs:strip-counts]: under a `g`-sparse
  restriction, for every extension `x, y`, the `g` output bits of the strip with base `b * g`
  represent, in binary, the number of partial products in column `b * g` evaluating to `1`.
  The proof reads the strip off the product: sparsity makes the column-wise sum a base-`2^g`
  expansion whose digits are the counts of the `g`-columns (`digit_of_sparse_sum`).

## Design notes

* "A wire is constant or a Boolean function of the partial products of a single strip" is
  formalized as: the value of the wire on extensions of `ρ` depends only on the partial
  products of some strip (`LocalAt` with an existential strip). A constant wire qualifies with
  any strip, so constants need no separate clause.
* "Its clauses have constant width" is meaningful only for a family of encodings, one per
  input width; so `StripLocal` is a property of a family `M : ∀ n, MulEncoding n`, with one
  width bound for all `n`, and the locality half is stated per encoding.
* Sparsity counts partial products by their index pairs `(i, j)`, in columns `i + j`, exactly
  as the paper does; the bound `2^(g-1)` is the paper's threshold.

## Instances

* Proposition [prop:array-strip-local], the array multiplier family is strip-local, is
  `arrayMul_stripLocal` in `AssocLB.Multiplier.ArrayStripLocal`; Proposition
  [prop:wallace-strip-local] (appendix) is `wallaceMul_stripLocal` in
  `AssocLB.Multiplier.WallaceStripLocal`.
-/

namespace AssocLB

/-! ### Strips and columns -/

/-- The column `c` lies in the `g`-strip with base `b * g`, the interval of columns
`[b*g, (b+1)*g)`.

Paper: Definition [def:g-strip]. -/
def InStrip (g b c : ℕ) : Prop := b * g ≤ c ∧ c < (b + 1) * g

instance (g b c : ℕ) : Decidable (InStrip g b c) :=
  inferInstanceAs (Decidable (b * g ≤ c ∧ c < (b + 1) * g))

/-- Every column lies in exactly one `g`-strip, the one with base `(c / g) * g`. -/
theorem inStrip_iff {g b c : ℕ} (hg : 0 < g) : InStrip g b c ↔ b = c / g := by
  constructor
  · rintro ⟨h₁, h₂⟩
    exact (Nat.div_eq_of_lt_le (by linarith) (by linarith)).symm
  · rintro rfl
    exact ⟨Nat.div_mul_le_self c g, by rw [add_mul, one_mul]; exact Nat.lt_div_mul_add hg⟩

/-! ### Restrictions of the input bit-vectors -/

/-- A restriction of the input bit-vectors of an `n`-bit multiplier: a partial assignment to
the bits of `x` and to the bits of `y`.

Paper: Definition [def:g-sparse]. -/
structure InputRestriction (n : ℕ) where
  /-- The assigned bits of `x`. -/
  x : Fin n → Option Bool
  /-- The assigned bits of `y`. -/
  y : Fin n → Option Bool

namespace InputRestriction

variable {n : ℕ} (ρ : InputRestriction n)

/-- The bit-vectors `x, y` extend `ρ`: they agree with it on the assigned bits. -/
def Extends (x y : Bits n) : Prop :=
  (∀ i b, ρ.x i = some b → x i = b) ∧ ∀ j b, ρ.y j = some b → y j = b

/-- The partial product `t_{i,j}` is forced to `0` by `ρ`: `ρ` sets `x_i` or `y_j` to `0`. -/
def ForcedZero (i j : Fin n) : Prop := ρ.x i = some false ∨ ρ.y j = some false

instance (i j : Fin n) : Decidable (ρ.ForcedZero i j) :=
  inferInstanceAs (Decidable (ρ.x i = some false ∨ ρ.y j = some false))

/-- A partial product forced to `0` evaluates to `0` on every extension. -/
theorem partialProduct_eq_false_of_forcedZero {x y : Bits n} (h : ρ.Extends x y) {i j : Fin n}
    (hij : ρ.ForcedZero i j) : partialProduct x y i j = false := by
  rcases hij with hi | hj
  · simp [partialProduct, h.1 i false hi]
  · simp [partialProduct, h.2 j false hj]

/-- The partial products not forced to `0` lying in column `c`. -/
def liveInColumn (c : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => (p.1 : ℕ) + p.2 = c ∧ ¬ ρ.ForcedZero p.1 p.2

theorem mem_liveInColumn {c : ℕ} {p : Fin n × Fin n} :
    p ∈ ρ.liveInColumn c ↔ (p.1 : ℕ) + p.2 = c ∧ ¬ ρ.ForcedZero p.1 p.2 := by
  simp [liveInColumn]

/-- `ρ` is `g`-sparse: every partial product not forced to `0` lies in a `g`-column, and each
`g`-column contains strictly fewer than `2^(g-1)` of them.

Paper: Definition [def:g-sparse]. -/
def IsSparse (g : ℕ) : Prop :=
  (∀ i j : Fin n, ¬ ρ.ForcedZero i j → g ∣ (i : ℕ) + j) ∧
    ∀ c, (ρ.liveInColumn c).card < 2 ^ (g - 1)

end InputRestriction

/-! ### Strip-locality -/

/-- The number of partial products in column `c` that evaluate to `1` on the inputs `x, y`. -/
def ppCount {n : ℕ} (x y : Bits n) (c : ℕ) : ℕ :=
  (Finset.univ.filter fun p : Fin n × Fin n =>
    (p.1 : ℕ) + p.2 = c ∧ partialProduct x y p.1 p.2 = true).card

namespace MulEncoding

variable {n : ℕ} (M : MulEncoding n)

/-- Under the restriction `ρ`, the wire `w` computes a Boolean function of the partial products
of the `g`-strip with base `b * g`: its value on extensions of `ρ` depends only on those partial
products. A constant wire qualifies with any strip.

Paper: Definition [def:strip-local]. -/
def LocalAt (ρ : InputRestriction n) (g b : ℕ) (w : M.Wire) : Prop :=
  ∀ x y x' y' : Bits n, ρ.Extends x y → ρ.Extends x' y' →
    (∀ i j : Fin n, InStrip g b ((i : ℕ) + j) → partialProduct x y i j = partialProduct x' y' i j) →
    M.fn w x y = M.fn w x' y'

/-- The locality half of strip-locality: under every `g`-sparse restriction of the inputs,
every wire is constant or a Boolean function of the partial products of a single strip.

Paper: Definition [def:strip-local]. -/
def WiresStripLocal : Prop :=
  ∀ g, 1 ≤ g → ∀ ρ : InputRestriction n, ρ.IsSparse g → ∀ w, ∃ b, M.LocalAt ρ g b w

end MulEncoding

/-- A family of exact multiplier encodings is strip-local: its clauses have bounded width and
every member's wires are strip-local.

Paper: Definition [def:strip-local]. -/
def StripLocal (M : ∀ n, MulEncoding n) : Prop :=
  (∃ k, ∀ n, (M n).cnf.width ≤ k) ∧ ∀ n, (M n).WiresStripLocal

/-! ### The product as a column-wise sum -/

/-- The product of two bit-vectors is the column-wise sum of the partial products evaluating
to `1`, weighted by the columns.

Paper: Definition [def:partial-products]. -/
theorem Bits.toNat_mul_toNat_eq_sum_ppCount {n : ℕ} (x y : Bits n) :
    Bits.toNat x * Bits.toNat y = ∑ c ∈ Finset.range (2 * n), ppCount x y c * 2 ^ c := by
  rw [Bits.toNat_mul_toNat, ← Fintype.sum_prod_type',
    ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.range (2 * n))
      (g := fun p : Fin n × Fin n => (p.1 : ℕ) + p.2)
      (fun p _ => Finset.mem_range.mpr (by have := p.1.isLt; have := p.2.isLt; omega))]
  refine Finset.sum_congr rfl fun c _ => ?_
  have h1 : ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => (p.1 : ℕ) + p.2 = c),
      (partialProduct x y p.1 p.2).toNat * 2 ^ ((p.1 : ℕ) + p.2) =
      ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => (p.1 : ℕ) + p.2 = c),
      (partialProduct x y p.1 p.2).toNat * 2 ^ c :=
    Finset.sum_congr rfl fun p hp => by rw [(Finset.mem_filter.mp hp).2]
  rw [h1, ← Finset.sum_mul, ppCount, ← Finset.filter_filter, Finset.card_filter]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  cases partialProduct x y p.1 p.2 <;> simp

/-! ### Digit extraction -/

/-- The low columns of a column-wise sum supported on `g`-columns with digits below `2^g` stay
below the next strip boundary. -/
theorem sum_range_mul_lt_two_pow (g : ℕ) (hg : 1 ≤ g) (N : ℕ → ℕ)
    (hN0 : ∀ c, N c ≠ 0 → g ∣ c) (hNlt : ∀ c, N c < 2 ^ g) :
    ∀ b, ∑ c ∈ Finset.range (b * g), N c * 2 ^ c < 2 ^ (b * g) := by
  intro b
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.add_one_mul, Finset.sum_range_add, pow_add]
    have hrest : ∑ r ∈ Finset.range g, N (b * g + r) * 2 ^ (b * g + r) =
        N (b * g) * 2 ^ (b * g) := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro r hr hr0
        have hzero : N (b * g + r) = 0 := by
          by_contra h
          obtain ⟨q, hq⟩ := hN0 _ h
          have hdvd : g ∣ r := by
            have hr' : r = g * q - g * b := by rw [mul_comm g b]; omega
            rw [hr', ← Nat.mul_sub]
            exact Dvd.intro _ rfl
          exact absurd (Finset.mem_range.mp hr)
            (not_lt.mpr (Nat.le_of_dvd (Nat.pos_of_ne_zero hr0) hdvd))
        simp [hzero]
      · intro h0
        exact absurd (Finset.mem_range.mpr hg) h0
    rw [hrest]
    have h1 : (N (b * g) + 1) * 2 ^ (b * g) ≤ 2 ^ g * 2 ^ (b * g) :=
      Nat.mul_le_mul_right _ (hNlt _)
    nlinarith [ih, h1]

/-- Extracting a base-`2^g` digit: for a column-wise sum supported on `g`-columns with digits
below `2^g`, the bits `[b*g, (b+1)*g)` represent the digit of column `b * g`. -/
theorem digit_of_sparse_sum (g : ℕ) (hg : 1 ≤ g) (N : ℕ → ℕ) (K : ℕ)
    (hN0 : ∀ c, N c ≠ 0 → g ∣ c) (hNlt : ∀ c, N c < 2 ^ g) (b : ℕ) (hb : b * g < K) :
    ((∑ c ∈ Finset.range K, N c * 2 ^ c) / 2 ^ (b * g)) % 2 ^ g = N (b * g) := by
  rw [← Finset.sum_range_add_sum_Ico _ (le_of_lt hb), Finset.sum_eq_sum_Ico_succ_bot hb]
  have hA := sum_range_mul_lt_two_pow g hg N hN0 hNlt b
  have hC : 2 ^ ((b + 1) * g) ∣ ∑ c ∈ Finset.Ico (b * g + 1) K, N c * 2 ^ c := by
    apply Finset.dvd_sum
    intro c hc
    rw [Finset.mem_Ico] at hc
    by_cases h0 : N c = 0
    · simp [h0]
    · obtain ⟨q, rfl⟩ := hN0 c h0
      have hbq : b < q := Nat.lt_of_mul_lt_mul_right (a := g) (by linarith [hc.1])
      exact Dvd.dvd.mul_left (pow_dvd_pow 2 (by nlinarith)) _
  obtain ⟨H, hH⟩ := hC
  rw [hH]
  have e : ∑ c ∈ Finset.range (b * g), N c * 2 ^ c +
      (N (b * g) * 2 ^ (b * g) + 2 ^ ((b + 1) * g) * H) =
      ∑ c ∈ Finset.range (b * g), N c * 2 ^ c + 2 ^ (b * g) * (N (b * g) + 2 ^ g * H) := by
    rw [Nat.add_one_mul, pow_add]
    ring
  rw [e, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hA, zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hNlt _)]

/-! ### Strips count their partial products -/

theorem ppCount_le_card_liveInColumn {n : ℕ} (ρ : InputRestriction n) {x y : Bits n}
    (hxy : ρ.Extends x y) (c : ℕ) : ppCount x y c ≤ (ρ.liveInColumn c).card := by
  apply Finset.card_le_card
  intro p hp
  rw [Finset.mem_filter] at hp
  rw [InputRestriction.mem_liveInColumn]
  refine ⟨hp.2.1, fun hf => ?_⟩
  rw [ρ.partialProduct_eq_false_of_forcedZero hxy hf] at hp
  exact Bool.false_ne_true hp.2.2

/-- Under a `g`-sparse restriction, only `g`-columns hold partial products evaluating to `1`. -/
theorem InputRestriction.IsSparse.dvd_of_ppCount_ne_zero {n : ℕ} {ρ : InputRestriction n}
    {g : ℕ} (hρ : ρ.IsSparse g) {x y : Bits n} (hxy : ρ.Extends x y) {c : ℕ}
    (hc : ppCount x y c ≠ 0) : g ∣ c := by
  obtain ⟨p, hp⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hc)
  rw [Finset.mem_filter] at hp
  obtain ⟨-, hcol, hpp⟩ := hp
  rw [← hcol]
  apply hρ.1
  intro hf
  rw [ρ.partialProduct_eq_false_of_forcedZero hxy hf] at hpp
  exact Bool.false_ne_true hpp

/-- **Strips count their partial products.** Under a `g`-sparse restriction, for every
extension `x, y` of it, the `g` output bits of the strip with base `b * g` represent, in binary,
the number of partial products in column `b * g` that evaluate to `1`.

Paper: Observation [obs:strip-counts]. -/
theorem MulEncoding.toNat_strip_eq_ppCount {n : ℕ} (M : MulEncoding n) {g : ℕ} (hg : 1 ≤ g)
    {ρ : InputRestriction n} (hρ : ρ.IsSparse g) {x y : Bits n} (hxy : ρ.Extends x y) (b : ℕ)
    (hb : (b + 1) * g ≤ 2 * n) :
    Bits.toNat (fun k : Fin g =>
        M.fn (M.out ⟨b * g + k, by have := k.isLt; nlinarith⟩) x y) =
      ppCount x y (b * g) := by
  have hout : ∀ i : Fin (2 * n),
      M.fn (M.out i) x y = (Bits.toNat x * Bits.toNat y).testBit i := by
    intro i
    rw [← M.toNat_out x y, Bits.testBit_toNat]
  simp only [hout]
  rw [Bits.toNat_testBit_shift, Bits.toNat_mul_toNat_eq_sum_ppCount]
  refine digit_of_sparse_sum g hg _ (2 * n) (fun c hc => hρ.dvd_of_ppCount_ne_zero hxy hc)
    (fun c => ?_) b (by nlinarith)
  calc ppCount x y c ≤ (ρ.liveInColumn c).card := ppCount_le_card_liveInColumn ρ hxy c
    _ < 2 ^ (g - 1) := hρ.2 c
    _ ≤ 2 ^ g := Nat.pow_le_pow_right two_pos (Nat.sub_le g 1)

/-- Under a `g`-sparse restriction, the partial products in column `c` evaluating to `1` number
fewer than `2^g`. -/
theorem InputRestriction.IsSparse.ppCount_lt {n : ℕ} {ρ : InputRestriction n} {g : ℕ}
    (hρ : ρ.IsSparse g) {x y : Bits n} (hxy : ρ.Extends x y) (c : ℕ) : ppCount x y c < 2 ^ g :=
  calc ppCount x y c ≤ (ρ.liveInColumn c).card := ppCount_le_card_liveInColumn ρ hxy c
    _ < 2 ^ (g - 1) := hρ.2 c
    _ ≤ 2 ^ g := Nat.pow_le_pow_right two_pos (Nat.sub_le g 1)

/-- **Every output bit is a bit of its strip's count.** Under a `g`-sparse restriction whose
partial products not forced to `0` all lie in columns below a multiple `n₀ ≤ 2n` of `g`, for
every extension `x, y` the output bit at column `c` is bit `c mod g` of the number of partial
products in column `(c / g) g` evaluating to `1`. Columns at or beyond `n₀` hold no partial
product and their output bits are `0`.

Paper: Observation [obs:strip-counts]. -/
theorem MulEncoding.fn_out_eq_testBit_ppCount {n : ℕ} (M : MulEncoding n) {g : ℕ} (hg : 1 ≤ g)
    {ρ : InputRestriction n} (hρ : ρ.IsSparse g) {x y : Bits n} (hxy : ρ.Extends x y) {n₀ : ℕ}
    (hg₀ : g ∣ n₀) (hn₀ : n₀ ≤ 2 * n) (hlive : ∀ c, (ρ.liveInColumn c).Nonempty → c < n₀)
    (c : Fin (2 * n)) :
    M.fn (M.out c) x y = (ppCount x y (c / g * g)).testBit (c % g) := by
  have hpp0 : ∀ c, n₀ ≤ c → ppCount x y c = 0 := by
    intro c hc
    refine Nat.eq_zero_of_le_zero ((ppCount_le_card_liveInColumn ρ hxy c).trans (le_of_eq ?_))
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro p hp
    exact absurd (hlive c ⟨p, hp⟩) (not_lt.mpr hc)
  by_cases hc : (c : ℕ) < n₀
  · have hb : ((c : ℕ) / g + 1) * g ≤ 2 * n := by
      have h1 : (c : ℕ) / g < n₀ / g := Nat.div_lt_div_of_lt_of_dvd hg₀ hc
      have h2 : ((c : ℕ) / g + 1) * g ≤ n₀ / g * g := Nat.mul_le_mul_right g h1
      rw [Nat.div_mul_cancel hg₀] at h2
      exact h2.trans hn₀
    have hstrip := M.toNat_strip_eq_ppCount hg hρ hxy ((c : ℕ) / g) hb
    have hk : (c : ℕ) % g < g := Nat.mod_lt _ hg
    have hceq : (c : ℕ) / g * g + (c : ℕ) % g = c := by
      rw [Nat.mul_comm]
      exact Nat.div_add_mod _ _
    rw [← hstrip, Bits.testBit_toNat', dif_pos hk]
    congr 2
    exact Fin.ext hceq.symm
  · rw [not_lt] at hc
    have hcol : n₀ ≤ (c : ℕ) / g * g := by
      have h1 : n₀ / g ≤ (c : ℕ) / g := Nat.div_le_div_right hc
      have h2 := Nat.mul_le_mul_right g h1
      rwa [Nat.div_mul_cancel hg₀] at h2
    rw [hpp0 _ hcol, Nat.zero_testBit]
    have hout : M.fn (M.out c) x y = (Bits.toNat x * Bits.toNat y).testBit c := by
      rw [← M.toNat_out x y, Bits.testBit_toNat]
    rw [hout]
    apply Nat.testBit_eq_false_of_lt
    calc Bits.toNat x * Bits.toNat y
        = ∑ c ∈ Finset.range (2 * n), ppCount x y c * 2 ^ c :=
          Bits.toNat_mul_toNat_eq_sum_ppCount x y
      _ = ∑ c ∈ Finset.range (n₀ / g * g), ppCount x y c * 2 ^ c := by
          rw [Nat.div_mul_cancel hg₀]
          symm
          refine Finset.sum_subset (Finset.range_mono hn₀) fun c' hc' hc'' => ?_
          rw [Finset.mem_range, not_lt] at hc''
          rw [hpp0 c' hc'', Nat.zero_mul]
      _ < 2 ^ (n₀ / g * g) :=
          sum_range_mul_lt_two_pow g hg _ (fun c hc => hρ.dvd_of_ppCount_ne_zero hxy hc)
            (fun c => hρ.ppCount_lt hxy c) _
      _ ≤ 2 ^ (c : ℕ) := by
          rw [Nat.div_mul_cancel hg₀]
          exact Nat.pow_le_pow_right two_pos hc

end AssocLB
