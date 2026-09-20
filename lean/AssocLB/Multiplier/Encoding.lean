/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/
import AssocLB.Resolution.Basic

/-!
# Multiplier encodings

Paper: Section 2 (Preliminaries), paragraph "Notation" (bit-vectors), Definition
[def:exact-encoding] (exact multiplier encoding) and Definition [def:partial-products] (partial
products, arithmetic weight, columns), together with the full adder.

## Main definitions

* `Bits n`: `n`-bit vectors `Fin n → Bool`, bit `i` having weight `2^i`; `Bits.toNat` is the
  integer represented.
* `partialProduct x y i j`: the partial product `t_{i,j} = x_i ∧ y_j`, of arithmetic weight
  `2^(i+j)`, lying in column `i + j`.
* `FullAdder.sum`, `FullAdder.carry`: the outputs `a₀ ⊕ a₁ ⊕ a₂` and `MAJ(a₀, a₁, a₂)` of a
  full adder.
* `MulVar n W`: the variables of a multiplier encoding, the bits `x i`, `y j` of the two
  `n`-bit inputs and the wires `wire w`.
* `MulEncoding n`: an exact multiplier encoding. It bundles the type of wires, the CNF over
  `MulVar n Wire`, the Boolean function `fn w` of the input bit-vectors computed by each wire,
  the designated `2n`-bit output, and two properties: exactness, the satisfying assignments are
  exactly those in which every wire takes the value of its function, and correctness, the
  output computes the product.
* `MulEncoding.eval M x y`: the assignment determined by the inputs `x, y`, in which every wire
  takes the value of its function.

## Main results

* `Bits.testBit_toNat`, `Bits.toNat_injective`: bit `i` of `Bits.toNat b` is `b i`, so a
  bit-vector is determined by its value; `Bits.toNat_lt`: the value is below `2^n`.
* `Bits.toNat_mul_toNat`: the product of two bit-vectors is the weighted sum of the partial
  products (Definition [def:partial-products]).
* `FullAdder.toNat_sum_add_two_mul_toNat_carry`: the inputs and outputs of a full adder have
  the same total weight.
* `MulEncoding.sat_eval`, `MulEncoding.eq_eval_of_sat`: for each pair of inputs, `eval` is the
  unique satisfying assignment; `MulEncoding.toNat_out_of_sat`: under a satisfying assignment
  the output bits represent the product of the inputs.

## Design notes

* Bit-vectors are functions on `Fin n` and the represented integer is a `Finset` sum, matching
  the paper's `∑ x_i 2^i`; `BitVec` is not used, since the bits of a multiplier are variables
  and the value of a bit-vector is only ever read off an assignment.
* The variables of an encoding form the inductive type `MulVar n W` rather than an arbitrary
  type with injections, so that input bits and wires are syntactically distinct and no
  side conditions are needed. Copies of an encoding inside the associativity formula are made
  by substitution (`CNF.subst`), which also performs the zero-padding of inputs.
* The wire functions `fn` are data and exactness is a property; the paper's "each wire
  computes a Boolean function of the inputs" determines `fn` uniquely, see `eq_eval_of_sat`.
* The `2n` output wires are required to be distinct (`out_injective`), as "a designated
  `2n`-bit output" intends.
* The array multiplier (Figure [fig:array-multiplier]) and the Wallace tree (appendix) are
  built as Tseitin encodings of circuits (`AssocLB.Multiplier.Circuit`, with exactness proved
  once for all circuits) in `AssocLB.Multiplier.ArrayMultiplier` and
  `AssocLB.Multiplier.WallaceTree`.
-/

namespace AssocLB

/-! ### Bit-vectors -/

/-- An `n`-bit vector, indexed from `0`, least significant bit first.

Paper: Section 2, "Notation". -/
abbrev Bits (n : ℕ) := Fin n → Bool

namespace Bits

open Finset

/-- The integer represented by a bit-vector: bit `i` has weight `2^i`.

Paper: Section 2, "Notation". -/
def toNat {n : ℕ} (b : Bits n) : ℕ := ∑ i : Fin n, (b i).toNat * 2 ^ (i : ℕ)

@[simp] theorem toNat_zero (b : Bits 0) : toNat b = 0 := by
  simp [toNat]

theorem toNat_succ {n : ℕ} (b : Bits (n + 1)) :
    toNat b = (b 0).toNat + 2 * toNat (fun i => b i.succ) := by
  simp only [toNat, Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ,
    mul_sum]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  ring

theorem toNat_lt {n : ℕ} (b : Bits n) : toNat b < 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [toNat_succ, pow_succ]
    have h₁ := ih fun i => b i.succ
    have h₂ := Bool.toNat_le (b 0)
    omega

/-- Bit `i` of the represented integer is the bit `b i`. -/
theorem testBit_toNat {n : ℕ} (b : Bits n) (i : Fin n) : (toNat b).testBit i = b i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    rw [toNat_succ]
    cases i using Fin.cases with
    | zero =>
      rw [Fin.val_zero, Nat.testBit_zero, Nat.add_mul_mod_self_left]
      cases b 0 <;> simp
    | succ j =>
      rw [Fin.val_succ, Nat.testBit_add_one, Nat.add_mul_div_left _ _ two_pos,
        Nat.div_eq_of_lt (Bool.toNat_lt _), zero_add]
      exact ih _ j

/-- A bit-vector is determined by the integer it represents. -/
theorem toNat_injective (n : ℕ) : Function.Injective (toNat (n := n)) := by
  intro b b' h
  funext i
  rw [← testBit_toNat b i, ← testBit_toNat b' i, h]

theorem toNat_inj {n : ℕ} {b b' : Bits n} : toNat b = toNat b' ↔ b = b' :=
  (toNat_injective n).eq_iff

@[simp] theorem toNat_const_false {n : ℕ} : toNat (fun _ : Fin n => false) = 0 := by
  simp [toNat]

/-- Appending a top bit. -/
theorem toNat_snoc {n : ℕ} (b : Bits n) (t : Bool) :
    toNat (Fin.snoc b t : Fin (n + 1) → Bool) = toNat b + t.toNat * 2 ^ n := by
  simp [toNat, Fin.sum_univ_castSucc]

/-- Appending bit-vectors: the high part is shifted by the length of the low part. -/
theorem toNat_append {p q : ℕ} (lo : Bits p) (hi : Bits q) :
    toNat (Fin.append lo hi) = toNat lo + 2 ^ p * toNat hi := by
  simp only [toNat, Fin.sum_univ_add, Fin.append_left, Fin.append_right, Fin.val_castAdd,
    Fin.val_natAdd, mul_sum]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  rw [pow_add]
  ring

/-- Reindexing by a cast does not change the value. -/
theorem toNat_cast {p q : ℕ} (h : p = q) (b : Bits q) :
    toNat (fun i => b (Fin.cast h i)) = toNat b := by
  subst h
  rfl

theorem toNat_and_right {n : ℕ} (x : Bits n) (b : Bool) :
    toNat (fun i => x i && b) = b.toNat * toNat x := by
  cases b <;> simp [toNat, mul_sum]

/-- Bit `i` of the represented integer, for any `i`: the bit `b i` if `i < n`, and `0`
beyond. -/
theorem testBit_toNat' {n : ℕ} (b : Bits n) (i : ℕ) :
    (toNat b).testBit i = if h : i < n then b ⟨i, h⟩ else false := by
  split_ifs with h
  · exact testBit_toNat b ⟨i, h⟩
  · exact Nat.testBit_lt_two_pow
      ((toNat_lt b).trans_le (Nat.pow_le_pow_right two_pos (by omega)))

/-- Splitting a bit-vector after position `p`: the value is that of the low `p + 1` bits plus
`2^(p+1)` times that of the remaining bits. -/
theorem toNat_split {m : ℕ} (v : Bits (m + 1)) (p : ℕ) (hp : p ≤ m) :
    toNat v = toNat (fun i : Fin (p + 1) => v (Fin.castLE (by omega) i)) +
      2 ^ (p + 1) * toNat (fun i : Fin (m - p) => v ⟨p + 1 + i, by omega⟩) := by
  have h : (p + 1) + (m - p) = m + 1 := by omega
  have key : ∀ k, Fin.append (fun i : Fin (p + 1) => v (Fin.castLE (by omega) i))
      (fun i : Fin (m - p) => v ⟨p + 1 + i, by omega⟩) k = v (Fin.cast h k) := by
    intro k
    induction k using Fin.addCases with
    | left k =>
      rw [Fin.append_left]
      congr 1
    | right k =>
      rw [Fin.append_right]
      congr 1
  have hv : v = fun k => Fin.append (fun i : Fin (p + 1) => v (Fin.castLE (by omega) i))
      (fun i : Fin (m - p) => v ⟨p + 1 + i, by omega⟩) (Fin.cast h.symm k) := by
    funext k
    rw [key]
    congr 1
  conv_lhs => rw [hv]
  rw [toNat_cast, toNat_append]

/-- The `g` bits of `P` starting at position `s` represent `(P / 2^s) % 2^g`. -/
theorem toNat_testBit_shift (P s g : ℕ) :
    toNat (fun k : Fin g => P.testBit (s + k)) = (P / 2 ^ s) % 2 ^ g := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_toNat', Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases h : i < g <;> simp [h, Nat.add_comm]

/-- Zero-extension of a bit-vector to length `k` (a truncation if `k < n`). -/
def zeroExtend {n : ℕ} (b : Bits n) (k : ℕ) : Bits k :=
  fun j => if h : (j : ℕ) < n then b ⟨j, h⟩ else false

/-- Zero-extension does not change the value. -/
theorem toNat_zeroExtend {n k : ℕ} (b : Bits n) (h : n ≤ k) :
    toNat (zeroExtend b k) = toNat b := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_toNat', testBit_toNat']
  simp only [zeroExtend]
  split_ifs <;> first | rfl | omega

end Bits

/-! ### Partial products and full adders -/

/-- The partial product `t_{i,j} = x_i ∧ y_j`, of arithmetic weight `2^(i+j)`, lying in column
`i + j`.

Paper: Definition [def:partial-products]. -/
def partialProduct {n : ℕ} (x y : Bits n) (i j : Fin n) : Bool := x i && y j

/-- The product of two bit-vectors is the weighted sum of their partial products.

Paper: Definition [def:partial-products]. -/
theorem Bits.toNat_mul_toNat {n : ℕ} (x y : Bits n) :
    Bits.toNat x * Bits.toNat y =
      ∑ i : Fin n, ∑ j : Fin n, (partialProduct x y i j).toNat * 2 ^ ((i : ℕ) + j) := by
  rw [Bits.toNat, Bits.toNat, Fintype.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [partialProduct]
  cases x i <;> cases y j <;> simp [pow_add]

namespace FullAdder

/-- The sum output `a₀ ⊕ a₁ ⊕ a₂` of a full adder, of the weight of its inputs.

Paper: Section 2, after Definition [def:partial-products]. -/
def sum (a₀ a₁ a₂ : Bool) : Bool := a₀ ^^ a₁ ^^ a₂

/-- The carry output `MAJ(a₀, a₁, a₂)` of a full adder, of twice the weight of its inputs.

Paper: Section 2, after Definition [def:partial-products]. -/
def carry (a₀ a₁ a₂ : Bool) : Bool := (a₀ && a₁) || (a₁ && a₂) || (a₀ && a₂)

/-- The inputs and outputs of a full adder have the same total weight. -/
theorem toNat_sum_add_two_mul_toNat_carry (a₀ a₁ a₂ : Bool) :
    (sum a₀ a₁ a₂).toNat + 2 * (carry a₀ a₁ a₂).toNat = a₀.toNat + a₁.toNat + a₂.toNat := by
  cases a₀ <;> cases a₁ <;> cases a₂ <;> decide

end FullAdder

/-! ### Exact multiplier encodings -/

/-- The variables of a multiplier encoding with `n`-bit inputs and wires `W`: the input bits
`x i` and `y j`, and the wires `wire w`.

Paper: Definition [def:exact-encoding]. -/
inductive MulVar (n : ℕ) (W : Type*)
  /-- The bit `x_i` of the first input. -/
  | x (i : Fin n) : MulVar n W
  /-- The bit `y_j` of the second input. -/
  | y (j : Fin n) : MulVar n W
  /-- The wire `w`. -/
  | wire (w : W) : MulVar n W
  deriving DecidableEq

/-- An exact multiplier encoding `Mul_n(x, y; xy)`: a CNF over the input bits and the wires,
each wire computing a Boolean function of the inputs, with a designated `2n`-bit output
computing the product.

Paper: Definition [def:exact-encoding]. -/
structure MulEncoding (n : ℕ) where
  /-- The wires: the variables of the encoding other than the input bits. -/
  Wire : Type
  [decEq : DecidableEq Wire]
  /-- The CNF, over the input bits and the wires. -/
  cnf : CNF (MulVar n Wire)
  /-- The Boolean function of the two input bit-vectors computed by each wire. -/
  fn : Wire → Bits n → Bits n → Bool
  /-- The designated `2n`-bit output. -/
  out : Fin (2 * n) → Wire
  /-- The output bits are distinct wires. -/
  out_injective : Function.Injective out
  /-- Exactness: the satisfying assignments are exactly those in which every wire takes the
  value of its function of the inputs. -/
  sat_iff : ∀ α : MulVar n Wire → Bool,
    cnf.Sat α ↔ ∀ w, α (MulVar.wire w) = fn w (α ∘ MulVar.x) (α ∘ MulVar.y)
  /-- The output computes the product of the inputs. -/
  toNat_out : ∀ x y : Bits n, Bits.toNat (fun i => fn (out i) x y) = Bits.toNat x * Bits.toNat y

attribute [instance] MulEncoding.decEq

namespace MulEncoding

variable {n : ℕ} (M : MulEncoding n)

/-- The assignment determined by the inputs `x, y`: every wire takes the value of its
function. -/
def eval (x y : Bits n) : MulVar n M.Wire → Bool
  | .x i => x i
  | .y j => y j
  | .wire w => M.fn w x y

@[simp] theorem eval_x (x y : Bits n) (i : Fin n) : M.eval x y (.x i) = x i := rfl

@[simp] theorem eval_y (x y : Bits n) (j : Fin n) : M.eval x y (.y j) = y j := rfl

@[simp] theorem eval_wire (x y : Bits n) (w : M.Wire) : M.eval x y (.wire w) = M.fn w x y := rfl

/-- The assignment determined by the inputs satisfies the encoding. -/
theorem sat_eval (x y : Bits n) : M.cnf.Sat (M.eval x y) :=
  (M.sat_iff _).mpr fun _ => rfl

theorem satisfiable : M.cnf.Satisfiable :=
  ⟨M.eval (fun _ => false) (fun _ => false), M.sat_eval _ _⟩

/-- A satisfying assignment is the one determined by its inputs. -/
theorem eq_eval_of_sat {α : MulVar n M.Wire → Bool} (h : M.cnf.Sat α) :
    α = M.eval (α ∘ MulVar.x) (α ∘ MulVar.y) := by
  funext v
  cases v with
  | x i => rfl
  | y j => rfl
  | wire w => exact (M.sat_iff α).mp h w

/-- Under a satisfying assignment, the output bits represent the product of the inputs. -/
theorem toNat_out_of_sat {α : MulVar n M.Wire → Bool} (h : M.cnf.Sat α) :
    Bits.toNat (fun i => α (MulVar.wire (M.out i))) =
      Bits.toNat (α ∘ MulVar.x) * Bits.toNat (α ∘ MulVar.y) := by
  rw [← M.toNat_out]
  congr 1
  funext i
  exact (M.sat_iff α).mp h (M.out i)

end MulEncoding

end AssocLB
