/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/
import AssocLB.Multiplier.Encoding

/-!
# Carry-lookahead addition: the semantics

Paper: Appendix (Wallace-tree multipliers are strip-local), Definition [def:cla] (carry-lookahead
adder) and the interval identities in the proof of Lemma [lem:cla-local].

## Main definitions

* `CLA.prop a b t = a_t ⊕ b_t`, `CLA.gen a b t = a_t ∧ b_t`: the propagate and generate signals
  of the addition of the bit sequences `a` and `b`; `CLA.carry a b i`: the carry into position
  `i`; `CLA.sumBit a b i`: the sum bit.
* `foldCarry p q lo r c`: the carry propagated through the positions `lo, …, lo + r - 1` from
  the carry-in `c` by the recurrence `c ↦ q_t ⊕ (p_t ∧ c)`; `allProp p lo r`: the group
  propagate `⋀_{t < r} p_{lo + t}`. With `c = 0`, `foldCarry` is the group generate `Q_I` of the
  paper.

## Main results

* `CLA.carry_eq_foldCarry`: the carry recurrence `c_{i+1} = q_i ⊕ (p_i ∧ c_i)`, unwound over an
  interval.
* `foldCarry_add`, `foldCarry_eq_xor`, `foldCarry_blocks`, `allProp_blocks`: the composition of
  group pairs over adjacent intervals and over the sub-blocks of a block, which is what the
  circuitry of each level of the carry-lookahead adder computes.
* `foldCarry_of_zero_at`, `allProp_of_zero_at`: a position with `p_s = q_s = 0` in an interval
  makes the group propagate `0` and lets the group generate depend only on the later positions.
* `CLA.toNat_sumBit`: the sum bits and the final carry represent `a + b`.
-/

namespace AssocLB

/-! ### Folding the carry recurrence over an interval -/

section Fold

variable (p q : ℕ → Bool)

/-- The carry propagated through the positions `lo, …, lo + r - 1` from the carry-in `c`, by
the recurrence `c ↦ q_t ⊕ (p_t ∧ c)`. With `c = 0` this is the group generate `Q_{[lo, lo+r)}`
of the paper. -/
def foldCarry (lo : ℕ) : ℕ → Bool → Bool
  | 0, c => c
  | r + 1, c => q (lo + r) ^^ (p (lo + r) && foldCarry lo r c)

/-- The group propagate `P_{[lo, lo+r)} = ⋀_{t < r} p_{lo + t}`. -/
def allProp (lo r : ℕ) : Bool := decide (∀ t, t < r → p (lo + t) = true)

@[simp] theorem foldCarry_zero (lo : ℕ) (c : Bool) : foldCarry p q lo 0 c = c := rfl

theorem foldCarry_succ (lo r : ℕ) (c : Bool) :
    foldCarry p q lo (r + 1) c = (q (lo + r) ^^ (p (lo + r) && foldCarry p q lo r c)) := rfl

@[simp] theorem allProp_zero (lo : ℕ) : allProp p lo 0 = true := by
  simp [allProp]

theorem allProp_succ (lo r : ℕ) : allProp p lo (r + 1) = (allProp p lo r && p (lo + r)) := by
  rw [Bool.eq_iff_iff, Bool.and_eq_true, allProp, allProp, decide_eq_true_iff,
    decide_eq_true_iff]
  constructor
  · intro h
    exact ⟨fun t ht => h t (by omega), h r (by omega)⟩
  · rintro ⟨h1, h2⟩ t ht
    rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | rfl
    · exact h1 t ht
    · exact h2

/-- Splitting an interval: fold the first part, then the second from its result. -/
theorem foldCarry_one (lo : ℕ) (c : Bool) : foldCarry p q lo 1 c = (q lo ^^ (p lo && c)) := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, foldCarry_succ, foldCarry_zero, Nat.add_zero]

theorem allProp_one (lo : ℕ) : allProp p lo 1 = p lo := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, allProp_succ, allProp_zero, Nat.add_zero, Bool.true_and]

theorem foldCarry_add (lo r₁ r₂ : ℕ) (c : Bool) :
    foldCarry p q lo (r₁ + r₂) c = foldCarry p q (lo + r₁) r₂ (foldCarry p q lo r₁ c) := by
  induction r₂ with
  | zero => rfl
  | succ r₂ ih =>
    rw [← Nat.add_assoc, foldCarry_succ, foldCarry_succ, ih, Nat.add_assoc]

theorem allProp_add (lo r₁ r₂ : ℕ) :
    allProp p lo (r₁ + r₂) = (allProp p lo r₁ && allProp p (lo + r₁) r₂) := by
  induction r₂ with
  | zero => simp
  | succ r₂ ih =>
    rw [← Nat.add_assoc, allProp_succ, allProp_succ, ih, Nat.add_assoc, Bool.and_assoc]

/-- The carry out of an interval is its group generate, or its carry-in if it propagates:
`foldCarry lo r c = Q ⊕ (P ∧ c)`. -/
theorem foldCarry_eq_xor (lo r : ℕ) (c : Bool) :
    foldCarry p q lo r c = (foldCarry p q lo r false ^^ (allProp p lo r && c)) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [foldCarry_succ, foldCarry_succ, allProp_succ, ih]
    generalize p (lo + r) = P
    generalize q (lo + r) = Q
    generalize foldCarry p q lo r false = F
    generalize allProp p lo r = A
    cases P <;> cases Q <;> cases F <;> cases A <;> cases c <;> rfl

/-- The group pairs of `r` consecutive blocks of length `s` compose to the group pair of their
union: folding the block recurrence over the pairs is folding the bit recurrence over the
positions. -/
theorem foldCarry_blocks (lo s r : ℕ) (c : Bool) :
    foldCarry (fun t => allProp p (lo + t * s) s) (fun t => foldCarry p q (lo + t * s) s false)
      0 r c = foldCarry p q lo (r * s) c := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [foldCarry_succ, Nat.zero_add, ih, Nat.succ_mul, foldCarry_add,
      foldCarry_eq_xor p q (lo + r * s) s (foldCarry p q lo (r * s) c)]

theorem allProp_blocks (lo s r : ℕ) :
    allProp (fun t => allProp p (lo + t * s) s) 0 r = allProp p lo (r * s) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [allProp_succ, Nat.zero_add, ih, Nat.succ_mul, allProp_add]

/-- Folding depends only on the signals at the positions folded over. -/
theorem foldCarry_congr {p' q' : ℕ → Bool} (lo r : ℕ) (c : Bool)
    (h : ∀ t, lo ≤ t → t < lo + r → p t = p' t ∧ q t = q' t) :
    foldCarry p q lo r c = foldCarry p' q' lo r c := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [foldCarry_succ, foldCarry_succ, (h (lo + r) (by omega) (by omega)).1,
      (h (lo + r) (by omega) (by omega)).2, ih fun t h1 h2 => h t h1 (by omega)]

theorem allProp_congr {p' : ℕ → Bool} (lo r : ℕ)
    (h : ∀ t, lo ≤ t → t < lo + r → p t = p' t) : allProp p lo r = allProp p' lo r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [allProp_succ, allProp_succ, h (lo + r) (by omega) (by omega),
      ih fun t h1 h2 => h t h1 (by omega)]

/-- A position with `p_s = 0` in the interval makes the group propagate `0`. -/
theorem allProp_of_zero_at {lo r s : ℕ} (hs : lo ≤ s ∧ s < lo + r) (hp : p s = false) :
    allProp p lo r = false := by
  simp only [allProp, decide_eq_false_iff_not, not_forall]
  exact ⟨s - lo, by omega, by rw [Nat.add_sub_cancel' hs.1, hp]; exact Bool.false_ne_true⟩

/-- A position with `p_s = q_s = 0` in the interval kills the carry from before it: the group
generate depends only on the positions after `s`. -/
theorem foldCarry_of_zero_at {lo r s : ℕ} (hs : lo ≤ s ∧ s < lo + r) (hp : p s = false)
    (hq : q s = false) (c : Bool) :
    foldCarry p q lo r c = foldCarry p q (s + 1) (lo + r - (s + 1)) false := by
  have hr : foldCarry p q lo r c = foldCarry p q lo ((s - lo + 1) + (lo + r - (s + 1))) c := by
    congr 1
    omega
  rw [hr, foldCarry_add, show lo + (s - lo + 1) = s + 1 by omega]
  congr 1
  rw [foldCarry_succ, show lo + (s - lo) = s by omega, hp, hq]
  rfl

end Fold

/-! ### The carries of an addition -/

namespace CLA

variable (a b : ℕ → Bool)

/-- The propagate signal `p_t = a_t ⊕ b_t`. -/
def prop (t : ℕ) : Bool := a t ^^ b t

/-- The generate signal `q_t = a_t ∧ b_t`. -/
def gen (t : ℕ) : Bool := a t && b t

/-- The carry into position `i` of the addition `a + b`: `c_0 = 0`,
`c_{i+1} = MAJ(a_i, b_i, c_i)`. -/
def carry : ℕ → Bool
  | 0 => false
  | i + 1 => FullAdder.carry (a i) (b i) (carry i)

/-- The sum bit `(a + b)_i = a_i ⊕ b_i ⊕ c_i`. -/
def sumBit (i : ℕ) : Bool := FullAdder.sum (a i) (b i) (carry a b i)

@[simp] theorem carry_zero : carry a b 0 = false := rfl

theorem carry_succ (i : ℕ) : carry a b (i + 1) = FullAdder.carry (a i) (b i) (carry a b i) := rfl

/-- The carry recurrence in propagate–generate form: `c_{i+1} = q_i ⊕ (p_i ∧ c_i)`. -/
theorem carry_succ_eq (i : ℕ) : carry a b (i + 1) = (gen a b i ^^ (prop a b i && carry a b i)) := by
  rw [carry_succ, gen, prop, FullAdder.carry]
  cases a i <;> cases b i <;> cases carry a b i <;> rfl

/-- The carry recurrence unwound over an interval: the carry out of `[lo, lo + r)` is the fold
of the recurrence from the carry into `lo`. -/
theorem carry_eq_foldCarry (lo r : ℕ) :
    carry a b (lo + r) = foldCarry (prop a b) (gen a b) lo r (carry a b lo) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [← Nat.add_assoc, carry_succ_eq, foldCarry_succ, ih]

/-- The carry into `i` is the group generate of `[0, i)`. -/
theorem carry_eq (i : ℕ) : carry a b i = foldCarry (prop a b) (gen a b) 0 i false := by
  have := carry_eq_foldCarry a b 0 i
  rwa [Nat.zero_add, carry_zero] at this

theorem sumBit_eq (i : ℕ) : sumBit a b i = (prop a b i ^^ carry a b i) := by
  rw [sumBit, prop, FullAdder.sum]

/-- The sum bits below `W` together with the carry into `W` represent the sum of the values of
`a` and `b` below `W`. -/
theorem toNat_sumBit (W : ℕ) :
    (∑ i ∈ Finset.range W, (sumBit a b i).toNat * 2 ^ i) + (carry a b W).toNat * 2 ^ W =
      ∑ i ∈ Finset.range W, ((a i).toNat + (b i).toNat) * 2 ^ i := by
  induction W with
  | zero => simp
  | succ W ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, carry_succ, pow_succ]
    have h := FullAdder.toNat_sum_add_two_mul_toNat_carry (a W) (b W) (carry a b W)
    rw [← sumBit] at h
    zify at ih h ⊢
    linear_combination ih + (2 : ℤ) ^ W * h

end CLA

end AssocLB
