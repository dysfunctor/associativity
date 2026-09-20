/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/
import AssocLB.Multiplier.ArrayMultiplier
import AssocLB.Multiplier.StripLocal

/-!
# The array multiplier is strip-local

Paper: Section 4, Proposition [prop:array-strip-local].

## Main results

* `ArrayWire.rowPrefix`: the prefix form of the row identity, for the full adders of a row up to
  a position `p`: the sum bits up to `p` together with the carry out of position `p` represent
  the partial products and the bits from above up to `p`.
* Weight sums of partial products: `ArrayWire.ppWeight`, and the identities relating the
  product of `x` with the low bits of `y` to the weights of the partial products of the low
  rows, split at a column `C` (`ArrayWire.sum_ppWeight_rows`, `ArrayWire.sum_ppWeight_split`).

* `ArrayWire.carry_eq_false_of_dvd`, the boundary-carry lemma: under a `g`-sparse restriction no
  carry enters a `g`-column.
* `ArrayWire.eval_local`: every wire is a function of the partial products of the strip of its
  column, by induction along the grid; `arrayMul_stripLocal`, Proposition
  [prop:array-strip-local]: the family `arrayMul` is strip-local.

## Design notes

* The paper's argument is that a carry into column `(b+1)g` has weight `2^((b+1)g)`, which the
  partial products below that column cannot supply under sparsity. This is made precise
  without tracking the state of the grid: the carry out of the adder at column `C` in a row is
  bounded by the weight of that row's partial products up to `C` plus the bits arriving from
  above up to `C`, and the latter are the low `C + 1` bits of the product of `x` with the low
  bits of `y` (by `ArrayWire.invariant` and `ArrayWire.shift`), hence at most the weight of the
  partial products of the previous rows up to column `C`.
-/

namespace AssocLB

namespace ArrayWire

variable {m : ℕ} (x y : Bits (m + 1))

/-! ### The prefix form of the row identity -/

/-- The full adders of row `r` up to position `p` preserve the total weight: the sum bits up to
`p` with the carry out of position `p` represent the partial products and the bits from above
up to `p`. -/
theorem rowPrefix (r : Fin (m + 1)) (p : ℕ) (hp : p + 1 ≤ m + 1) :
    Bits.toNat (fun i : Fin (p + 1) => (circuit m).eval x y (.sum (Fin.castLE hp i) r)) +
      ((circuit m).eval x y (.carry (Fin.castLE hp (Fin.last p)) r)).toNat * 2 ^ (p + 1) =
      Bits.toNat (fun i : Fin (p + 1) => x (Fin.castLE hp i) && y r) +
        Bits.toNat (fun i : Fin (p + 1) => evalAbove x y (Fin.castLE hp i) r) := by
  have := FullAdder.ripple (fun i : Fin (p + 1) => x (Fin.castLE hp i) && y r)
    (fun i => evalAbove x y (Fin.castLE hp i) r)
    (fun i => (circuit m).eval x y (.sum (Fin.castLE hp i) r))
    (fun i => evalLeft x y (Fin.castLE hp i) r)
    (fun i => (circuit m).eval x y (.carry (Fin.castLE hp i) r))
    (fun i => by
      have h1 : Fin.castLE hp i.succ = (Fin.castLE (by omega : p ≤ m) i).succ := Fin.ext rfl
      have h2 : Fin.castLE hp i.castSucc = (Fin.castLE (by omega : p ≤ m) i).castSucc :=
        Fin.ext rfl
      rw [h1, h2, evalLeft_succ])
    (fun i => fa x y _ r)
  rwa [Fin.castLE_zero, evalLeft_zero, Bool.toNat_false, add_zero] at this

/-! ### Weights of partial products -/

/-- The weight `t_{i,j} 2^(i+j)` of the partial product `(i, j)`. -/
def ppWeight (q : Fin (m + 1) × Fin (m + 1)) : ℕ :=
  (partialProduct x y q.1 q.2).toNat * 2 ^ ((q.1 : ℕ) + q.2)

/-- The total weight of the partial products in columns up to `C` is the column-wise sum of the
counts. -/
theorem sum_ppWeight_le_col (C : ℕ) :
    ∑ q ∈ Finset.univ.filter (fun q : Fin (m + 1) × Fin (m + 1) => (q.1 : ℕ) + q.2 ≤ C),
      ppWeight x y q = ∑ c ∈ Finset.range (C + 1), ppCount x y c * 2 ^ c := by
  rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.range (C + 1))
    (g := fun q : Fin (m + 1) × Fin (m + 1) => (q.1 : ℕ) + q.2)
    (fun q hq => Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hq).2))]
  refine Finset.sum_congr rfl fun c hc => ?_
  have hcC : c ≤ C := Nat.lt_succ_iff.mp (Finset.mem_range.mp hc)
  have h1 : (Finset.univ.filter fun q : Fin (m + 1) × Fin (m + 1) => (q.1 : ℕ) + q.2 ≤ C).filter
      (fun q => (q.1 : ℕ) + q.2 = c) =
      Finset.univ.filter fun q : Fin (m + 1) × Fin (m + 1) => (q.1 : ℕ) + q.2 = c := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨h ▸ hcC, h⟩
  have h2 : ∑ q ∈ Finset.univ.filter (fun q : Fin (m + 1) × Fin (m + 1) => (q.1 : ℕ) + q.2 = c),
      ppWeight x y q =
      ∑ q ∈ Finset.univ.filter (fun q : Fin (m + 1) × Fin (m + 1) => (q.1 : ℕ) + q.2 = c),
      (partialProduct x y q.1 q.2).toNat * 2 ^ c :=
    Finset.sum_congr rfl fun q hq => by rw [ppWeight, (Finset.mem_filter.mp hq).2]
  rw [h1, h2, ← Finset.sum_mul, ppCount, ← Finset.filter_filter, Finset.card_filter]
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  cases partialProduct x y q.1 q.2 <;> simp

/-- The product of `x` with the low `r + 1` bits of `y` is the total weight of the partial
products of the rows up to `r`. -/
theorem sum_ppWeight_rows (r : ℕ) (hr : r ≤ m) :
    Bits.toNat x * ∑ k ∈ Finset.range (r + 1), (y' y k).toNat * 2 ^ k =
      ∑ q ∈ Finset.univ.filter (fun q : Fin (m + 1) × Fin (m + 1) => (q.2 : ℕ) ≤ r),
        ppWeight x y q := by
  have hrange : ∑ k ∈ Finset.range (r + 1), (y' y k).toNat * 2 ^ k =
      ∑ j : Fin (m + 1), if (j : ℕ) ≤ r then (y j).toNat * 2 ^ (j : ℕ) else 0 := by
    have h1 : ∑ k ∈ Finset.range (r + 1), (y' y k).toNat * 2 ^ k =
        ∑ k ∈ Finset.range (m + 1), if k ≤ r then (y' y k).toNat * 2 ^ k else 0 := by
      rw [← Finset.sum_filter]
      congr 1
      ext k
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [h1, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hj : (j : ℕ) ≤ m := Nat.lt_succ_iff.mp j.isLt
    by_cases hjr : (j : ℕ) ≤ r <;> simp [y', hjr, hj]
  rw [hrange, Finset.mul_sum, Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hjr : (j : ℕ) ≤ r
  · simp only [hjr, if_true, ppWeight, Bits.toNat, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [partialProduct]
    cases x i <;> cases y j <;> simp [pow_add]
  · simp [hjr]

/-- Splitting the weight of the rows up to `r` at column `C`: the part above `C` is a multiple
of `2^(C+1)`. -/
theorem sum_ppWeight_split (r C : ℕ) :
    ∑ q ∈ Finset.univ.filter (fun q : Fin (m + 1) × Fin (m + 1) => (q.2 : ℕ) ≤ r),
        ppWeight x y q =
      (∑ q ∈ Finset.univ.filter
          (fun q : Fin (m + 1) × Fin (m + 1) => (q.2 : ℕ) ≤ r ∧ (q.1 : ℕ) + q.2 ≤ C),
        ppWeight x y q) +
      2 ^ (C + 1) * ((∑ q ∈ Finset.univ.filter
          (fun q : Fin (m + 1) × Fin (m + 1) => (q.2 : ℕ) ≤ r ∧ ¬ (q.1 : ℕ) + q.2 ≤ C),
        ppWeight x y q) / 2 ^ (C + 1)) := by
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun q : Fin (m + 1) × Fin (m + 1) =>
    (q.1 : ℕ) + q.2 ≤ C), Finset.filter_filter, Finset.filter_filter]
  congr 1
  rw [Nat.mul_div_cancel' ]
  apply Finset.dvd_sum
  intro q hq
  rw [Finset.mem_filter] at hq
  exact Dvd.dvd.mul_left (pow_dvd_pow 2 (by omega)) _

/-- The weight of the partial products of row `r` up to position `p`, in terms of the row's
truncated partial-product vector. -/
theorem sum_ppWeight_row (r : Fin (m + 1)) (p : ℕ) (hp : p + 1 ≤ m + 1) :
    ∑ q ∈ Finset.univ.filter
        (fun q : Fin (m + 1) × Fin (m + 1) => q.2 = r ∧ (q.1 : ℕ) + q.2 ≤ p + r),
      ppWeight x y q =
      2 ^ (r : ℕ) * Bits.toNat (fun i : Fin (p + 1) => x (Fin.castLE hp i) && y r) := by
  have himage : Finset.univ.filter
      (fun q : Fin (m + 1) × Fin (m + 1) => q.2 = r ∧ (q.1 : ℕ) + q.2 ≤ p + r) =
      (Finset.univ : Finset (Fin (p + 1))).image fun i => (Fin.castLE hp i, r) := by
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, hle⟩
      exact ⟨⟨i, by omega⟩, Fin.ext rfl, rfl⟩
    · rintro ⟨k, rfl, rfl⟩
      exact ⟨rfl, by simp; omega⟩
  rw [himage, Finset.sum_image (fun a _ b _ h => Fin.castLE_injective hp (Prod.mk.inj h).1),
    Bits.toNat, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ppWeight, partialProduct, Fin.val_castLE]
  ring

/-! ### The boundary-carry lemma -/

/-- The bits arriving from above in row `r`, up to position `p`, weigh at most the partial
products of the rows below `r` in the columns up to `p + r`. -/
theorem above_weight_le (r : ℕ) (hr : r ≤ m) (p : ℕ) (hp : p + 1 ≤ m + 1) :
    2 ^ r * Bits.toNat (fun i : Fin (p + 1) => evalAbove x y (Fin.castLE hp i) ⟨r, by omega⟩) ≤
      ∑ q ∈ Finset.univ.filter
        (fun q : Fin (m + 1) × Fin (m + 1) => (q.2 : ℕ) < r ∧ (q.1 : ℕ) + q.2 ≤ p + r),
        ppWeight x y q := by
  cases r with
  | zero =>
    have h0 : (⟨0, by omega⟩ : Fin (m + 1)) = 0 := rfl
    simp [h0]
  | succ r' =>
    have hr' : r' < m + 1 := by omega
    have hinv := invariant x y r' hr'
    have hs := shift x y r' (by omega)
    have hs0 : s0 x y r' = (circuit m).eval x y (.sum 0 ⟨r', hr'⟩) := by simp [s0, hr']
    have hsplit : Bits.toNat (fun i => evalAbove x y i ⟨r' + 1, by omega⟩) =
        Bits.toNat (fun i : Fin (p + 1) => evalAbove x y (Fin.castLE hp i) ⟨r' + 1, by omega⟩) +
          2 ^ (p + 1) * Bits.toNat
            (fun i : Fin (m - p) => evalAbove x y ⟨p + 1 + i, by omega⟩ ⟨r' + 1, by omega⟩) :=
      Bits.toNat_split _ p (by omega)
    have hF : ∑ k ∈ Finset.range (r' + 1), (s0 x y k).toNat * 2 ^ k < 2 ^ (r' + 1) := by
      rw [← Fin.sum_univ_eq_sum_range (fun k => (s0 x y k).toNat * 2 ^ k)]
      exact Bits.toNat_lt fun k : Fin (r' + 1) => s0 x y k
    have hAlt := Bits.toNat_lt
      fun i : Fin (p + 1) => evalAbove x y (Fin.castLE hp i) ⟨r' + 1, by omega⟩
    have hXY : Bits.toNat x * ∑ k ∈ Finset.range (r' + 1), (y' y k).toNat * 2 ^ k =
        (∑ k ∈ Finset.range (r' + 1), (s0 x y k).toNat * 2 ^ k +
          2 ^ (r' + 1) * Bits.toNat
            (fun i : Fin (p + 1) => evalAbove x y (Fin.castLE hp i) ⟨r' + 1, by omega⟩)) +
        2 ^ (p + (r' + 1) + 1) * Bits.toNat
          (fun i : Fin (m - p) => evalAbove x y ⟨p + 1 + i, by omega⟩ ⟨r' + 1, by omega⟩) := by
      rw [← hinv, Finset.sum_range_succ, hs0, ← hs, hsplit]
      ring
    have hlow : ∑ k ∈ Finset.range (r' + 1), (s0 x y k).toNat * 2 ^ k +
        2 ^ (r' + 1) * Bits.toNat
          (fun i : Fin (p + 1) => evalAbove x y (Fin.castLE hp i) ⟨r' + 1, by omega⟩) <
        2 ^ (p + (r' + 1) + 1) := by
      have h1 : 2 ^ (r' + 1) * (Bits.toNat
          (fun i : Fin (p + 1) => evalAbove x y (Fin.castLE hp i) ⟨r' + 1, by omega⟩) + 1) ≤
          2 ^ (r' + 1) * 2 ^ (p + 1) := Nat.mul_le_mul_left _ hAlt
      rw [show 2 ^ (p + (r' + 1) + 1) = 2 ^ (r' + 1) * 2 ^ (p + 1) by ring]
      linarith
    have hmod : (Bits.toNat x * ∑ k ∈ Finset.range (r' + 1), (y' y k).toNat * 2 ^ k) %
        2 ^ (p + (r' + 1) + 1) =
        ∑ k ∈ Finset.range (r' + 1), (s0 x y k).toNat * 2 ^ k +
          2 ^ (r' + 1) * Bits.toNat
            (fun i : Fin (p + 1) => evalAbove x y (Fin.castLE hp i) ⟨r' + 1, by omega⟩) := by
      rw [hXY, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlow]
    have hW := sum_ppWeight_rows x y r' (by omega)
    rw [sum_ppWeight_split x y r' (p + (r' + 1))] at hW
    have hle : ∑ k ∈ Finset.range (r' + 1), (s0 x y k).toNat * 2 ^ k +
        2 ^ (r' + 1) * Bits.toNat
          (fun i : Fin (p + 1) => evalAbove x y (Fin.castLE hp i) ⟨r' + 1, by omega⟩) ≤
        ∑ q ∈ Finset.univ.filter (fun q : Fin (m + 1) × Fin (m + 1) =>
          (q.2 : ℕ) ≤ r' ∧ (q.1 : ℕ) + q.2 ≤ p + (r' + 1)), ppWeight x y q := by
      rw [← hmod, hW, Nat.add_mul_mod_self_left]
      exact Nat.mod_le _ _
    calc 2 ^ (r' + 1) * Bits.toNat
          (fun i : Fin (p + 1) => evalAbove x y (Fin.castLE hp i) ⟨r' + 1, by omega⟩) ≤
        ∑ k ∈ Finset.range (r' + 1), (s0 x y k).toNat * 2 ^ k +
          2 ^ (r' + 1) * Bits.toNat
            (fun i : Fin (p + 1) => evalAbove x y (Fin.castLE hp i) ⟨r' + 1, by omega⟩) :=
          Nat.le_add_left _ _
      _ ≤ _ := hle
      _ = _ := by
          congr 1
          apply Finset.filter_congr
          intro q _
          constructor <;> intro h <;> exact ⟨by omega, h.2⟩

/-- **No carry enters a `g`-column.** Under a `g`-sparse restriction, for every extension of it,
the carry out of position `p` of row `r` is `0` whenever it enters a `g`-column, that is,
whenever `g` divides `p + r + 1`.

Paper: proof of Proposition [prop:array-strip-local]. -/
theorem carry_eq_false_of_dvd {g : ℕ} (hg : 1 ≤ g) {ρ : InputRestriction (m + 1)}
    (hρ : ρ.IsSparse g) (hxy : ρ.Extends x y) (r : ℕ) (hr : r ≤ m) (p : ℕ) (hp : p ≤ m)
    (hdvd : g ∣ p + r + 1) :
    (circuit m).eval x y (.carry ⟨p, by omega⟩ ⟨r, by omega⟩) = false := by
  have hp1 : p + 1 ≤ m + 1 := by omega
  have hrow := rowPrefix x y ⟨r, by omega⟩ p hp1
  rw [show Fin.castLE hp1 (Fin.last p) = (⟨p, by omega⟩ : Fin (m + 1)) from rfl] at hrow
  have hT := sum_ppWeight_row x y ⟨r, by omega⟩ p hp1
  have hA := above_weight_le x y r hr p hp1
  have hW : ∑ q ∈ Finset.univ.filter
      (fun q : Fin (m + 1) × Fin (m + 1) => (q.1 : ℕ) + q.2 ≤ p + r), ppWeight x y q <
      2 ^ (p + r + 1) := by
    obtain ⟨b, hb⟩ := hdvd
    rw [sum_ppWeight_le_col, show p + r + 1 = b * g by rw [hb, mul_comm]]
    exact sum_range_mul_lt_two_pow g hg (ppCount x y)
      (fun c hc => hρ.dvd_of_ppCount_ne_zero hxy hc)
      (fun c => ((ppCount_le_card_liveInColumn ρ hxy c).trans_lt (hρ.2 c)).trans_le
        (Nat.pow_le_pow_right two_pos (Nat.sub_le g 1))) b
  have hsum : ∑ q ∈ Finset.univ.filter
        (fun q : Fin (m + 1) × Fin (m + 1) => q.2 = ⟨r, by omega⟩ ∧ (q.1 : ℕ) + q.2 ≤ p + r),
        ppWeight x y q +
      ∑ q ∈ Finset.univ.filter
        (fun q : Fin (m + 1) × Fin (m + 1) => (q.2 : ℕ) < r ∧ (q.1 : ℕ) + q.2 ≤ p + r),
        ppWeight x y q ≤
      ∑ q ∈ Finset.univ.filter
        (fun q : Fin (m + 1) × Fin (m + 1) => (q.1 : ℕ) + q.2 ≤ p + r), ppWeight x y q := by
    rw [← Finset.sum_union]
    · apply Finset.sum_le_sum_of_subset
      intro q hq
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter] at hq
      rw [Finset.mem_filter]
      rcases hq with ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> exact ⟨Finset.mem_univ _, h⟩
    · rw [Finset.disjoint_filter]
      intro q _ h1 h2
      have := congrArg Fin.val h1.1
      simp at this
      omega
  have key : ((circuit m).eval x y (.carry ⟨p, by omega⟩ ⟨r, by omega⟩)).toNat *
      2 ^ (p + r + 1) < 2 ^ (p + r + 1) := by
    calc ((circuit m).eval x y (.carry ⟨p, by omega⟩ ⟨r, by omega⟩)).toNat * 2 ^ (p + r + 1)
        = 2 ^ r * (((circuit m).eval x y (.carry ⟨p, by omega⟩ ⟨r, by omega⟩)).toNat *
            2 ^ (p + 1)) := by ring
      _ ≤ 2 ^ r * (Bits.toNat (fun i : Fin (p + 1) => x (Fin.castLE hp1 i) && y ⟨r, by omega⟩) +
            Bits.toNat (fun i : Fin (p + 1) => evalAbove x y (Fin.castLE hp1 i) ⟨r, by omega⟩)) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = 2 ^ r * Bits.toNat (fun i : Fin (p + 1) => x (Fin.castLE hp1 i) && y ⟨r, by omega⟩) +
            2 ^ r * Bits.toNat
              (fun i : Fin (p + 1) => evalAbove x y (Fin.castLE hp1 i) ⟨r, by omega⟩) := by
          ring
      _ ≤ _ := add_le_add (le_of_eq hT.symm) hA
      _ ≤ _ := hsum
      _ < 2 ^ (p + r + 1) := hW
  rcases Bool.eq_false_or_eq_true ((circuit m).eval x y (.carry ⟨p, by omega⟩ ⟨r, by omega⟩))
    with h | h
  · rw [h] at key
    simp at key
  · exact h

/-! ### Locality -/

/-- The column of a wire: that of its partial product or of its full adder. -/
def col : ArrayWire m → ℕ
  | .zero => 0
  | .pp i j => i + j
  | .sum i j => i + j
  | .carry i j => i + j

omit x y in
/-- The column below a column of a strip lies in the same strip unless the column is a
`g`-column. -/
theorem inStrip_pred {g b c : ℕ} (h : InStrip g b c) (hc : ¬ g ∣ c) : InStrip g b (c - 1) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, by omega⟩
  rcases Nat.eq_or_lt_of_le h1 with h1 | h1
  · exact absurd ⟨b, by rw [← h1, mul_comm]⟩ hc
  · omega

/-- The bits arriving from above agree on two extensions, given that the lower-rank wires of the
strip agree. -/
theorem evalAbove_congr {g : ℕ} (hg : 1 ≤ g) {ρ : InputRestriction (m + 1)} (hρ : ρ.IsSparse g)
    {x' y' : Bits (m + 1)} (hxy : ρ.Extends x y) (hxy' : ρ.Extends x' y') {b : ℕ}
    (i j : Fin (m + 1)) (hw : InStrip g b ((i : ℕ) + j))
    (ih : ∀ w', rank w' < 2 + (i : ℕ) + (m + 1) * j → InStrip g b (col w') →
      (circuit m).eval x y w' = (circuit m).eval x' y' w') :
    evalAbove x y i j = evalAbove x' y' i j := by
  induction j using Fin.cases with
  | zero => simp
  | succ j' =>
    induction i using Fin.lastCases with
    | last =>
      rw [evalAbove_last_succ, evalAbove_last_succ]
      by_cases hdvd : g ∣ m + j' + 1
      · have h1 : (circuit m).eval x y (.carry (Fin.last m) j'.castSucc) = false :=
          carry_eq_false_of_dvd x y hg hρ hxy j' (by omega) m le_rfl hdvd
        have h2 : (circuit m).eval x' y' (.carry (Fin.last m) j'.castSucc) = false :=
          carry_eq_false_of_dvd x' y' hg hρ hxy' j' (by omega) m le_rfl hdvd
        rw [h1, h2]
      · apply ih
        · simp only [rank, Fin.val_last, Fin.val_castSucc, Fin.val_succ, Nat.mul_add_one]
          omega
        · have := inStrip_pred hw (by simpa [Nat.add_assoc] using hdvd)
          simpa [col] using this
    | cast i' =>
      rw [evalAbove_castSucc_succ, evalAbove_castSucc_succ]
      apply ih
      · simp only [rank, Fin.val_castSucc, Fin.val_succ, Nat.mul_add_one]
        have := i'.isLt
        omega
      · convert hw using 2
        simp only [col, Fin.val_succ, Fin.val_castSucc]
        omega

/-- The carry inputs agree on two extensions, given that the lower-rank wires of the strip
agree. -/
theorem evalLeft_congr {g : ℕ} (hg : 1 ≤ g) {ρ : InputRestriction (m + 1)} (hρ : ρ.IsSparse g)
    {x' y' : Bits (m + 1)} (hxy : ρ.Extends x y) (hxy' : ρ.Extends x' y') {b : ℕ}
    (i j : Fin (m + 1)) (hw : InStrip g b ((i : ℕ) + j))
    (ih : ∀ w', rank w' < 2 + (i : ℕ) + (m + 1) * j → InStrip g b (col w') →
      (circuit m).eval x y w' = (circuit m).eval x' y' w') :
    evalLeft x y i j = evalLeft x' y' i j := by
  induction i using Fin.cases with
  | zero => simp
  | succ i' =>
    rw [evalLeft_succ, evalLeft_succ]
    by_cases hdvd : g ∣ i' + j + 1
    · have h1 : (circuit m).eval x y (.carry i'.castSucc j) = false :=
        carry_eq_false_of_dvd x y hg hρ hxy j (by omega) i' (by omega) hdvd
      have h2 : (circuit m).eval x' y' (.carry i'.castSucc j) = false :=
        carry_eq_false_of_dvd x' y' hg hρ hxy' j (by omega) i' (by omega) hdvd
      rw [h1, h2]
    · apply ih
      · simp only [rank, Fin.val_castSucc, Fin.val_succ]
        omega
      · have := inStrip_pred hw (by simpa [Nat.add_right_comm] using hdvd)
        simpa [col] using this

/-- Under a `g`-sparse restriction, every wire computes a function of the partial products of
the strip of its column: two extensions agreeing on those partial products give the wire the
same value. -/
theorem eval_local {g : ℕ} (hg : 1 ≤ g) {ρ : InputRestriction (m + 1)} (hρ : ρ.IsSparse g)
    {x' y' : Bits (m + 1)} (hxy : ρ.Extends x y) (hxy' : ρ.Extends x' y') {b : ℕ}
    (hagree : ∀ i j : Fin (m + 1), InStrip g b ((i : ℕ) + j) →
      partialProduct x y i j = partialProduct x' y' i j)
    (w : ArrayWire m) (hw : InStrip g b (col w)) :
    (circuit m).eval x y w = (circuit m).eval x' y' w := by
  revert hw
  induction w using (circuit m).toCircuit.rank_induction with
  | h w ih =>
    intro hw
    cases w with
    | zero => simp
    | pp i j =>
      rw [eval_pp, eval_pp]
      exact hagree i j hw
    | sum i j =>
      have hpp : (x i && y j) = (x' i && y' j) := hagree i j hw
      rw [eval_sum, eval_sum, hpp,
        evalAbove_congr x y hg hρ hxy hxy' i j hw fun w' h1 h2 => ih w' h1 h2,
        evalLeft_congr x y hg hρ hxy hxy' i j hw fun w' h1 h2 => ih w' h1 h2]
    | carry i j =>
      have hpp : (x i && y j) = (x' i && y' j) := hagree i j hw
      rw [eval_carry, eval_carry, hpp,
        evalAbove_congr x y hg hρ hxy hxy' i j hw fun w' h1 h2 => ih w' h1 h2,
        evalLeft_congr x y hg hρ hxy hxy' i j hw fun w' h1 h2 => ih w' h1 h2]

omit x y in
/-- The wires of the `(m+1)`-bit array multiplier are strip-local. -/
theorem wiresStripLocal (m : ℕ) : (arrayMul (m + 1)).WiresStripLocal := by
  intro g hg ρ hρ w
  refine ⟨col w / g, ?_⟩
  intro x y x' y' hxy hxy' hagree
  exact eval_local x y hg hρ hxy hxy' hagree w ((inStrip_iff (by omega)).mpr rfl)

end ArrayWire

/-- **The array multiplier is strip-local.**

Paper: Proposition [prop:array-strip-local]. -/
theorem arrayMul_stripLocal : StripLocal arrayMul := by
  refine ⟨⟨4, fun n => ?_⟩, fun n => ?_⟩
  · cases n with
    | zero => simp [arrayMul, CNF.width]
    | succ m =>
      exact MulEncoding.width_ofMulCircuit_le (ArrayWire.circuit m) (ArrayWire.out m)
        (ArrayWire.out_injective m) ArrayWire.toNat_out 3 fun w => by
          cases w <;> simp [ArrayWire.circuit, ArrayWire.gate, Gate.const, Gate.and2, Gate.xor3,
            Gate.maj3]
  · cases n with
    | zero => exact fun _ _ _ _ w => Empty.elim w
    | succ m => exact ArrayWire.wiresStripLocal m

end AssocLB
