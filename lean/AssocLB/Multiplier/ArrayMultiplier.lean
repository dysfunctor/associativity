/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/
import AssocLB.Multiplier.Circuit

/-!
# The array multiplier

Paper: Section 2 (Preliminaries), Figure [fig:array-multiplier]: the array multiplier computes
each partial product by an AND gate and sums them with a grid of full adders, and "this is an
exact multiplier encoding".

## Main definitions

* `ArrayWire m`: the wires of the `(m+1)`-bit array multiplier: the constant `zero`, the partial
  products `pp i j`, and the sum and carry outputs `sum i j`, `carry i j` of the full adder at
  position `i` of row `j`.
* `ArrayWire.circuit m`: the circuit. Row `j` adds the partial products `t_{i,j}` to the running
  sum by a ripple-carry chain of full adders: the adder at position `i` of row `j` adds `t_{i,j}`,
  the sum bit arriving from the row above (`ArrayWire.above`), and the carry from position
  `i - 1` (`ArrayWire.left`). Row `0` and position `0` read the constant `zero`.
* `ArrayWire.out m`: the output wires, the final sum bits `s_{0,j}` (`ArrayWire.outLo`), then
  the remaining sum bits of the last row and its final carry (`ArrayWire.outHi`).
* `arrayMul n`: the array multiplier as an exact multiplier encoding, for every `n`.

## Main results

* `ArrayWire.toNat_out`: the output represents the product of the inputs. The proof follows the
  arithmetic of the grid: a ripple-carry chain of full adders preserves the total weight
  (`FullAdder.ripple`, applied row by row in `ArrayWire.row`), the sum bits shift by one position
  from one row to the next (`ArrayWire.shift`), and the value accumulated after each row is the
  product of `x` with the low bits of `y` (`ArrayWire.invariant`).

## Design notes

* The multiplier is defined for `m + 1` bits, so that the top position `Fin.last m` and the
  shifts `Fin.succ`, `Fin.castSucc` are available; `arrayMul 0` is the empty encoding.
* Rows are ripple-carry. The carries run along a row, and the only wires crossing a column
  boundary are carries, as the proof of Proposition [prop:array-strip-local] needs.
* Every full adder is uniform, of fan-in 3, with its boundary inputs read from the constant wire
  `zero`; so all clauses have width at most `4`.
-/

namespace AssocLB

/-! ### Ripple-carry chains -/

/-- A ripple-carry chain of full adders preserves the total weight. With carry-in `cin i` and
carry-out `cout i` at position `i`, where `cin (i + 1) = cout i`, and each adder adding `t i`,
`a i` and `cin i`, the sum bits together with the final carry-out represent `t + a + cin 0`. -/
theorem FullAdder.ripple : ∀ {p : ℕ} (t a s cin cout : Bits (p + 1)),
    (∀ i : Fin p, cin i.succ = cout i.castSucc) →
    (∀ i, (s i).toNat + 2 * (cout i).toNat = (t i).toNat + (a i).toNat + (cin i).toNat) →
    Bits.toNat s + (cout (Fin.last p)).toNat * 2 ^ (p + 1) =
      Bits.toNat t + Bits.toNat a + (cin 0).toNat := by
  intro p
  induction p with
  | zero =>
    intro t a s cin cout _ hfa
    have := hfa 0
    simp only [Bits.toNat_succ, Bits.toNat_zero, Fin.last_zero, zero_add, pow_one, mul_zero,
      add_zero]
    omega
  | succ p ih =>
    intro t a s cin cout hchain hfa
    have h0 := hfa 0
    have htail := ih (fun i => t i.succ) (fun i => a i.succ) (fun i => s i.succ)
      (fun i => cin i.succ) (fun i => cout i.succ)
      (fun i => by rw [Fin.succ_castSucc]; exact hchain i.succ) (fun i => hfa i.succ)
    rw [hchain 0, Fin.castSucc_zero, Fin.succ_last] at htail
    rw [Bits.toNat_succ s, Bits.toNat_succ t, Bits.toNat_succ a, pow_succ]
    linarith [h0, htail]

/-! ### The circuit -/

/-- The wires of the `(m+1)`-bit array multiplier. -/
inductive ArrayWire (m : ℕ)
  /-- The constant `0`. -/
  | zero
  /-- The partial product `t_{i,j} = x_i ∧ y_j`. -/
  | pp (i j : Fin (m + 1))
  /-- The sum output of the full adder at position `i` of row `j`. -/
  | sum (i j : Fin (m + 1))
  /-- The carry output of the full adder at position `i` of row `j`. -/
  | carry (i j : Fin (m + 1))
  deriving DecidableEq, Fintype

namespace ArrayWire

variable {m : ℕ}

/-- The variable feeding the "sum from above" input of the full adder at position `i` of row
`j`: the constant `0` in row `0`; otherwise the sum output at position `i + 1` of the previous
row, or at the top position the final carry of the previous row. -/
def above (i j : Fin (m + 1)) : MulVar (m + 1) (ArrayWire m) :=
  Fin.cases (.wire .zero)
    (fun j' => Fin.lastCases (.wire (.carry (Fin.last m) j'.castSucc))
      (fun i' => .wire (.sum i'.succ j'.castSucc)) i) j

/-- The variable feeding the carry input of the full adder at position `i` of row `j`: the
constant `0` at position `0`, otherwise the carry output of position `i - 1`. -/
def left (i j : Fin (m + 1)) : MulVar (m + 1) (ArrayWire m) :=
  Fin.cases (.wire .zero) (fun i' => .wire (.carry i'.castSucc j)) i

@[simp] theorem above_zero (i : Fin (m + 1)) : above i 0 = .wire .zero := by
  simp [above]

@[simp] theorem above_castSucc_succ (i' j' : Fin m) :
    above i'.castSucc j'.succ = .wire (.sum i'.succ j'.castSucc) := by
  simp [above]

@[simp] theorem above_last_succ (j' : Fin m) :
    above (Fin.last m) j'.succ = .wire (.carry (Fin.last m) j'.castSucc) := by
  simp [above]

@[simp] theorem left_zero (j : Fin (m + 1)) : left 0 j = .wire .zero := by
  simp [left]

@[simp] theorem left_succ (i' : Fin m) (j : Fin (m + 1)) :
    left i'.succ j = .wire (.carry i'.castSucc j) := by
  simp [left]

/-- The gate of each wire. -/
def gate : ArrayWire m → Gate (MulVar (m + 1) (ArrayWire m))
  | .zero => Gate.const false
  | .pp i j => Gate.and2 (.x i) (.y j)
  | .sum i j => Gate.xor3 (.wire (.pp i j)) (above i j) (left i j)
  | .carry i j => Gate.maj3 (.wire (.pp i j)) (above i j) (left i j)

/-- A rank decreasing along gate inputs: the constant, then the partial products, then the
adders in row-major order. -/
def rank : ArrayWire m → ℕ
  | .zero => 0
  | .pp _ _ => 1
  | .sum i j => 2 + i.val + (m + 1) * j.val
  | .carry i j => 2 + i.val + (m + 1) * j.val

theorem rank_lt_of_above {i j : Fin (m + 1)} {w : ArrayWire m}
    (h : above i j = MulVar.wire w) : rank w < 2 + i.val + (m + 1) * j.val := by
  induction j using Fin.cases with
  | zero =>
    rw [above_zero] at h
    cases h
    simp only [rank]
    omega
  | succ j' =>
    induction i using Fin.lastCases with
    | last =>
      rw [above_last_succ] at h
      cases h
      simp only [rank, Fin.val_last, Fin.val_castSucc, Fin.val_succ, Nat.mul_add_one]
      omega
    | cast i' =>
      rw [above_castSucc_succ] at h
      cases h
      simp only [rank, Fin.val_castSucc, Fin.val_succ, Nat.mul_add_one]
      have := i'.isLt
      omega

theorem rank_lt_of_left {i j : Fin (m + 1)} {w : ArrayWire m}
    (h : left i j = MulVar.wire w) : rank w < 2 + i.val + (m + 1) * j.val := by
  induction i using Fin.cases with
  | zero =>
    rw [left_zero] at h
    cases h
    simp only [rank]
    omega
  | succ i' =>
    rw [left_succ] at h
    cases h
    simp only [rank, Fin.val_castSucc, Fin.val_succ]
    omega

theorem rank_lt (w : ArrayWire m) (k : Fin (gate w).arity) (w' : ArrayWire m)
    (h : (gate w).inputs k = MulVar.wire w') : rank w' < rank w := by
  cases w with
  | zero => exact k.elim0
  | pp i j =>
    change (Gate.and2 (MulVar.x i) (MulVar.y j)).inputs k = _ at h
    rcases Gate.inputs_and2 _ _ k with hk | hk <;> rw [hk] at h <;> cases h
  | sum i j =>
    change (Gate.xor3 (MulVar.wire (.pp i j)) (above i j) (left i j)).inputs k = _ at h
    rcases Gate.inputs_xor3 _ _ _ k with hk | hk | hk <;> rw [hk] at h
    · cases h
      simp only [rank]
      omega
    · exact rank_lt_of_above h
    · exact rank_lt_of_left h
  | carry i j =>
    change (Gate.maj3 (MulVar.wire (.pp i j)) (above i j) (left i j)).inputs k = _ at h
    rcases Gate.inputs_maj3 _ _ _ k with hk | hk | hk <;> rw [hk] at h
    · cases h
      simp only [rank]
      omega
    · exact rank_lt_of_above h
    · exact rank_lt_of_left h

/-- The array multiplier circuit for `(m + 1)`-bit inputs. -/
def circuit (m : ℕ) : MulCircuit (m + 1) (ArrayWire m) where
  gate := gate
  rank := rank
  rank_lt := rank_lt

@[simp] theorem circuit_gate (w : ArrayWire m) : (circuit m).gate w = gate w := rfl

/-! ### Evaluation -/

variable (x y : Bits (m + 1))

/-- The value of the "sum from above" input at position `i` of row `j`. -/
def evalAbove (i j : Fin (m + 1)) : Bool :=
  (circuit m).toCircuit.evalAssign (MulVar.ofInputs x y) (above i j)

/-- The value of the carry input at position `i` of row `j`. -/
def evalLeft (i j : Fin (m + 1)) : Bool :=
  (circuit m).toCircuit.evalAssign (MulVar.ofInputs x y) (left i j)

@[simp] theorem eval_zero : (circuit m).eval x y .zero = false := by
  rw [MulCircuit.eval_eq]
  rfl

@[simp] theorem eval_pp (i j : Fin (m + 1)) : (circuit m).eval x y (.pp i j) = (x i && y j) := by
  rw [MulCircuit.eval_eq]
  simp [gate, Gate.and2]

theorem eval_sum (i j : Fin (m + 1)) :
    (circuit m).eval x y (.sum i j) =
      FullAdder.sum (x i && y j) (evalAbove x y i j) (evalLeft x y i j) := by
  rw [MulCircuit.eval_eq]
  simp [gate, Gate.xor3, evalAbove, evalLeft]

theorem eval_carry (i j : Fin (m + 1)) :
    (circuit m).eval x y (.carry i j) =
      FullAdder.carry (x i && y j) (evalAbove x y i j) (evalLeft x y i j) := by
  rw [MulCircuit.eval_eq]
  simp [gate, Gate.maj3, evalAbove, evalLeft]

/-- The weight identity of the full adder at position `i` of row `j`. -/
theorem fa (i j : Fin (m + 1)) :
    ((circuit m).eval x y (.sum i j)).toNat + 2 * ((circuit m).eval x y (.carry i j)).toNat =
      (x i && y j).toNat + (evalAbove x y i j).toNat + (evalLeft x y i j).toNat := by
  rw [eval_sum, eval_carry, FullAdder.toNat_sum_add_two_mul_toNat_carry]

@[simp] theorem evalAbove_zero (i : Fin (m + 1)) : evalAbove x y i 0 = false := by
  simp [evalAbove]

theorem evalAbove_castSucc_succ (i' j' : Fin m) :
    evalAbove x y i'.castSucc j'.succ = (circuit m).eval x y (.sum i'.succ j'.castSucc) := by
  simp [evalAbove]

theorem evalAbove_last_succ (j' : Fin m) :
    evalAbove x y (Fin.last m) j'.succ =
      (circuit m).eval x y (.carry (Fin.last m) j'.castSucc) := by
  simp [evalAbove]

@[simp] theorem evalLeft_zero (j : Fin (m + 1)) : evalLeft x y 0 j = false := by
  simp [evalLeft]

theorem evalLeft_succ (i' : Fin m) (j : Fin (m + 1)) :
    evalLeft x y i'.succ j = (circuit m).eval x y (.carry i'.castSucc j) := by
  simp [evalLeft]

/-- Row `j` adds `y_j · x` to the bits arriving from above: the sum bits and the final carry of
the row represent their total. -/
theorem row (j : Fin (m + 1)) :
    Bits.toNat (fun i => (circuit m).eval x y (.sum i j)) +
      ((circuit m).eval x y (.carry (Fin.last m) j)).toNat * 2 ^ (m + 1) =
      (y j).toNat * Bits.toNat x + Bits.toNat (fun i => evalAbove x y i j) := by
  have := FullAdder.ripple (fun i => x i && y j) (fun i => evalAbove x y i j)
    (fun i => (circuit m).eval x y (.sum i j)) (fun i => evalLeft x y i j)
    (fun i => (circuit m).eval x y (.carry i j)) (fun i => evalLeft_succ x y i j)
    (fun i => fa x y i j)
  rwa [evalLeft_zero, Bool.toNat_false, add_zero, Bits.toNat_and_right] at this

/-- The bits arriving from above in row `j + 1` are the sum bits of row `j` shifted down by one
position, with the final carry of row `j` on top. -/
theorem shift (j : ℕ) (hj : j < m) :
    2 * Bits.toNat (fun i => evalAbove x y i ⟨j + 1, by omega⟩) +
      ((circuit m).eval x y (.sum 0 ⟨j, by omega⟩)).toNat =
      Bits.toNat (fun i => (circuit m).eval x y (.sum i ⟨j, by omega⟩)) +
        ((circuit m).eval x y (.carry (Fin.last m) ⟨j, by omega⟩)).toNat * 2 ^ (m + 1) := by
  have hA : (fun i => evalAbove x y i ⟨j + 1, by omega⟩) =
      Fin.snoc (fun i' : Fin m => (circuit m).eval x y (.sum i'.succ ⟨j, by omega⟩))
        ((circuit m).eval x y (.carry (Fin.last m) ⟨j, by omega⟩)) := by
    funext i
    induction i using Fin.lastCases with
    | last =>
      rw [Fin.snoc_last]
      exact evalAbove_last_succ x y ⟨j, hj⟩
    | cast i' =>
      rw [Fin.snoc_castSucc]
      exact evalAbove_castSucc_succ x y i' ⟨j, hj⟩
  rw [hA, Bits.toNat_snoc]
  simp only [Bits.toNat_succ, pow_succ]
  ring

/-- The final sum bit `s_{0,k}`, extended by `false`. -/
def s0 (k : ℕ) : Bool :=
  if h : k < m + 1 then (circuit m).eval x y (.sum 0 ⟨k, h⟩) else false

/-- The bit `y_k`, extended by `false`. -/
def y' (k : ℕ) : Bool := if h : k < m + 1 then y ⟨k, h⟩ else false

/-- After row `j`, the final bits `s_{0,k}` for `k < j` together with the sum bits and the final
carry of row `j`, placed at column `j`, represent `x` times the low `j + 1` bits of `y`. -/
theorem invariant (j : ℕ) (hj : j < m + 1) :
    (∑ k ∈ Finset.range j, (s0 x y k).toNat * 2 ^ k) +
      (Bits.toNat (fun i => (circuit m).eval x y (.sum i ⟨j, hj⟩)) +
        ((circuit m).eval x y (.carry (Fin.last m) ⟨j, hj⟩)).toNat * 2 ^ (m + 1)) * 2 ^ j =
      Bits.toNat x * ∑ k ∈ Finset.range (j + 1), (y' y k).toNat * 2 ^ k := by
  induction j with
  | zero =>
    have h0 : (⟨0, hj⟩ : Fin (m + 1)) = 0 := rfl
    rw [row, h0]
    simp [y', mul_comm]
  | succ j ih =>
    have hj' : j < m + 1 := by omega
    specialize ih hj'
    have hs := shift x y j (by omega)
    have hr := row x y ⟨j + 1, hj⟩
    have hs0 : s0 x y j = (circuit m).eval x y (.sum 0 ⟨j, hj'⟩) := by simp [s0, hj']
    have hy' : y' y (j + 1) = y ⟨j + 1, hj⟩ := by simp [y', hj]
    rw [Finset.sum_range_succ, Finset.sum_range_succ (fun k => (y' y k).toNat * 2 ^ k) (j + 1),
      hs0, hy', hr]
    have hs2 : (2 * Bits.toNat (fun i => evalAbove x y i ⟨j + 1, hj⟩) +
        ((circuit m).eval x y (.sum 0 ⟨j, hj'⟩)).toNat) * 2 ^ j =
        (Bits.toNat (fun i => (circuit m).eval x y (.sum i ⟨j, hj'⟩)) +
          ((circuit m).eval x y (.carry (Fin.last m) ⟨j, hj'⟩)).toNat * 2 ^ (m + 1)) * 2 ^ j := by
      rw [hs]
    rw [pow_succ]
    linarith [ih, hs2]

/-! ### The output -/

/-- The low output wires: the final sum bits `s_{0,j}`. -/
def outLo (m : ℕ) (j : Fin (m + 1)) : ArrayWire m := sum 0 j

/-- The high output wires: the sum bits `s_{i,m}` of the last row for `i ≥ 1`, then its final
carry. -/
def outHi (m : ℕ) : Fin (m + 1) → ArrayWire m :=
  Fin.snoc (fun i : Fin m => sum i.succ (Fin.last m)) (carry (Fin.last m) (Fin.last m))

@[simp] theorem outHi_castSucc (i : Fin m) : outHi m i.castSucc = sum i.succ (Fin.last m) := by
  simp [outHi]

@[simp] theorem outHi_last : outHi m (Fin.last m) = carry (Fin.last m) (Fin.last m) := by
  simp [outHi]

theorem two_mul_succ (m : ℕ) : 2 * (m + 1) = (m + 1) + (m + 1) := by ring

/-- The output wires: the low part, then the high part. -/
def out (m : ℕ) (k : Fin (2 * (m + 1))) : ArrayWire m :=
  Fin.append (outLo m) (outHi m) (Fin.cast (two_mul_succ m) k)

theorem outLo_injective (m : ℕ) : Function.Injective (outLo m) :=
  fun _ _ h => (ArrayWire.sum.inj h).2

theorem outHi_injective (m : ℕ) : Function.Injective (outHi m) := by
  intro a b hab
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last => rfl
    | cast b =>
      rw [outHi_last, outHi_castSucc] at hab
      cases hab
  | cast a =>
    induction b using Fin.lastCases with
    | last =>
      rw [outHi_castSucc, outHi_last] at hab
      cases hab
    | cast b =>
      rw [outHi_castSucc, outHi_castSucc] at hab
      rw [Fin.succ_inj.mp (ArrayWire.sum.inj hab).1]

theorem outLo_ne_outHi (m : ℕ) (j i : Fin (m + 1)) : outLo m j ≠ outHi m i := by
  induction i using Fin.lastCases with
  | last =>
    rw [outHi_last]
    exact fun h => by cases h
  | cast i =>
    rw [outHi_castSucc]
    intro h
    exact Fin.succ_ne_zero i (ArrayWire.sum.inj h).1.symm

theorem out_injective (m : ℕ) : Function.Injective (out m) := by
  intro k k' h
  have happ : Function.Injective (Fin.append (outLo m) (outHi m)) := by
    intro a b hab
    induction a using Fin.addCases with
    | left a =>
      induction b using Fin.addCases with
      | left b =>
        rw [Fin.append_left, Fin.append_left] at hab
        rw [outLo_injective m hab]
      | right b =>
        rw [Fin.append_left, Fin.append_right] at hab
        exact absurd hab (outLo_ne_outHi m a b)
    | right a =>
      induction b using Fin.addCases with
      | left b =>
        rw [Fin.append_right, Fin.append_left] at hab
        exact absurd hab.symm (outLo_ne_outHi m b a)
      | right b =>
        rw [Fin.append_right, Fin.append_right] at hab
        rw [outHi_injective m hab]
  have hcast : Function.Injective (Fin.cast (two_mul_succ m)) := fun a b hab =>
    Fin.ext (by simpa using congrArg Fin.val hab)
  exact hcast (happ h)

/-- The output represents the product of the inputs. -/
theorem toNat_out :
    Bits.toNat (fun k => (circuit m).eval x y (out m k)) = Bits.toNat x * Bits.toNat y := by
  have h1 : Bits.toNat (fun k => (circuit m).eval x y (out m k)) =
      Bits.toNat (fun k => (circuit m).eval x y (Fin.append (outLo m) (outHi m) k)) :=
    Bits.toNat_cast (two_mul_succ m)
      (fun k => (circuit m).eval x y (Fin.append (outLo m) (outHi m) k))
  have h2 : (fun k => (circuit m).eval x y (Fin.append (outLo m) (outHi m) k)) =
      Fin.append (fun j => (circuit m).eval x y (outLo m j))
        (fun i => (circuit m).eval x y (outHi m i)) := by
    funext k
    induction k using Fin.addCases with
    | left k => rw [Fin.append_left, Fin.append_left]
    | right k => rw [Fin.append_right, Fin.append_right]
  have h3 : (fun i => (circuit m).eval x y (outHi m i)) =
      Fin.snoc (fun i : Fin m => (circuit m).eval x y (sum i.succ (Fin.last m)))
        ((circuit m).eval x y (carry (Fin.last m) (Fin.last m))) := by
    funext i
    induction i using Fin.lastCases with
    | last => simp
    | cast i => simp
  have hlo : Bits.toNat (fun j => (circuit m).eval x y (outLo m j)) =
      ∑ k ∈ Finset.range (m + 1), (s0 x y k).toNat * 2 ^ k := by
    rw [Bits.toNat, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi : (i : ℕ) ≤ m := Nat.lt_succ_iff.mp i.isLt
    simp [s0, outLo, hi]
  have hy : Bits.toNat y = ∑ k ∈ Finset.range (m + 1), (y' y k).toNat * 2 ^ k := by
    rw [Bits.toNat, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi : (i : ℕ) ≤ m := Nat.lt_succ_iff.mp i.isLt
    simp [y', hi]
  have hinv := invariant x y m (Nat.lt_succ_self m)
  have hlast : (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) = Fin.last m := rfl
  rw [hlast] at hinv
  have hs0 : s0 x y m = (circuit m).eval x y (sum 0 (Fin.last m)) := by
    rw [s0, dif_pos (Nat.lt_succ_self m)]
    rfl
  have hS := Bits.toNat_succ (fun i => (circuit m).eval x y (sum i (Fin.last m)))
  rw [h1, h2, Bits.toNat_append, h3, Bits.toNat_snoc, hlo, Finset.sum_range_succ, hs0, hy,
    ← hinv, hS, pow_succ]
  ring

end ArrayWire

/-- The array multiplier as an exact multiplier encoding.

Paper: Section 2, Figure [fig:array-multiplier]. -/
def arrayMul : (n : ℕ) → MulEncoding n
  | 0 =>
    { Wire := Empty
      cnf := ∅
      fn := fun w => w.elim
      out := fun k => k.elim0
      out_injective := fun k => k.elim0
      sat_iff := fun _ => by simp [CNF.Sat]
      toNat_out := fun x y => by
        rw [Bits.toNat_zero x, Bits.toNat_zero y]
        exact Bits.toNat_zero _ }
  | m + 1 =>
    MulEncoding.ofMulCircuit (ArrayWire.circuit m) (ArrayWire.out m) (ArrayWire.out_injective m)
      (ArrayWire.toNat_out)

end AssocLB
