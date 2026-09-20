/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/
import AssocLB.Multiplier.Encoding

/-!
# Boolean circuits and their Tseitin encodings

Paper: Section 2 (Preliminaries). The array multiplier "computes each partial product by an AND
gate and uses a grid of full adders", and its clauses are the Tseitin clauses of these gates;
likewise the Wallace tree of the appendix and the miter gates of Definition [def:assoc].

## Main definitions

* `Gate V`: a gate over the variables `V`, a Boolean function of `arity` input variables.
  `Gate.clauses g o` are its Tseitin clauses with output variable `o`: for each pattern `b` of
  input values, the clause saying that if the inputs take the values `b` then `o` takes the
  value `g.fn b`. Smart constructors: `Gate.const`, `Gate.and2`, `Gate.xor2`, `Gate.xor3`,
  `Gate.maj3`.
* `Circuit V W`: a circuit over the variables `V` with wires `W`. Every wire is a variable, has
  a gate, and has a rank which strictly decreases along the inputs of its gate, so that gates
  can be evaluated recursively. `Circuit.eval c α w` is the value of the wire `w` when the input
  variables take the values given by `α`, and `Circuit.tseitin c` is the CNF of all gate
  clauses.
* `MulCircuit n W`: a circuit over `MulVar n W` whose wires are the `wire` variables;
  `MulEncoding.ofMulCircuit` is the exact multiplier encoding of such a circuit, once its
  designated output is shown to compute the product.

## Main results

* `Gate.sat_clauses_iff`: the Tseitin clauses of a gate are satisfied exactly when the output
  variable takes the value of the gate function at the input variables.
* `Circuit.sat_tseitin_iff`: exactness. An assignment satisfies the Tseitin encoding of a
  circuit exactly when every wire takes the value computed by the circuit from the assignment's
  values on the input variables.
* `Circuit.width_tseitin_le`: the clauses have width at most the fan-in plus one.

## Design notes

* Gates are arbitrary Boolean functions with the full truth-table clause set, `2^arity` clauses
  of width `arity + 1`. The paper's Tseitin clauses for AND, XOR and MAJ are a subset with the
  same satisfying assignments; any exact clause set of constant width would do, and this one
  is uniform.
* Wires are named, by the type `W`, rather than positions in a list, so that the array
  multiplier can name its partial products, sums and carries by row and column. Acyclicity is a
  rank function, the simplest well-founded order to supply for a grid.
* The variable type `V` is arbitrary and the wires embed in it (`wire`), with a partial inverse
  `toWire?`. A gate's inputs may be any variables; those recognized as wires are evaluated
  recursively, the others are read from the assignment. So the miter gates of `Assoc_n` can
  read the outputs of two multipliers as inputs without renaming, and `Circuit.eval` depends on
  the assignment only at non-wire variables (`Circuit.eval_congr`).
-/

namespace AssocLB

/-! ### Gates and their Tseitin clauses -/

/-- A gate over the variables `V`: a Boolean function of `arity` input variables. -/
structure Gate (V : Type*) where
  /-- The number of inputs. -/
  arity : ℕ
  /-- The input variables. -/
  inputs : Fin arity → V
  /-- The function computed. -/
  fn : (Fin arity → Bool) → Bool

namespace Gate

variable {V : Type*}

/-- The constant gate with value `b`. -/
def const (b : Bool) : Gate V := ⟨0, Fin.elim0, fun _ => b⟩

/-- The AND gate `a ∧ b`. -/
def and2 (a b : V) : Gate V := ⟨2, ![a, b], fun v => v 0 && v 1⟩

/-- The XOR gate `a ⊕ b`. -/
def xor2 (a b : V) : Gate V := ⟨2, ![a, b], fun v => v 0 ^^ v 1⟩

/-- The sum gate `a₀ ⊕ a₁ ⊕ a₂` of a full adder. -/
def xor3 (a₀ a₁ a₂ : V) : Gate V :=
  ⟨3, ![a₀, a₁, a₂], fun v => FullAdder.sum (v 0) (v 1) (v 2)⟩

/-- The carry gate `MAJ(a₀, a₁, a₂)` of a full adder. -/
def maj3 (a₀ a₁ a₂ : V) : Gate V :=
  ⟨3, ![a₀, a₁, a₂], fun v => FullAdder.carry (v 0) (v 1) (v 2)⟩

@[simp] theorem fn_const_comp (b : Bool) (β : V → Bool) :
    (const b).fn (β ∘ (const b).inputs) = b :=
  rfl

@[simp] theorem fn_and2_comp (a b : V) (β : V → Bool) :
    (and2 a b).fn (β ∘ (and2 a b).inputs) = (β a && β b) := by
  simp [and2]

@[simp] theorem fn_xor2_comp (a b : V) (β : V → Bool) :
    (xor2 a b).fn (β ∘ (xor2 a b).inputs) = (β a ^^ β b) := by
  simp [xor2]

@[simp] theorem fn_xor3_comp (a₀ a₁ a₂ : V) (β : V → Bool) :
    (xor3 a₀ a₁ a₂).fn (β ∘ (xor3 a₀ a₁ a₂).inputs) = FullAdder.sum (β a₀) (β a₁) (β a₂) := by
  simp [xor3]

@[simp] theorem fn_maj3_comp (a₀ a₁ a₂ : V) (β : V → Bool) :
    (maj3 a₀ a₁ a₂).fn (β ∘ (maj3 a₀ a₁ a₂).inputs) = FullAdder.carry (β a₀) (β a₁) (β a₂) := by
  simp [maj3]

theorem inputs_and2 (a b : V) (k : Fin 2) :
    (and2 a b).inputs k = a ∨ (and2 a b).inputs k = b := by
  fin_cases k <;> simp [and2]

theorem inputs_xor2 (a b : V) (k : Fin 2) :
    (xor2 a b).inputs k = a ∨ (xor2 a b).inputs k = b := by
  fin_cases k <;> simp [xor2]

theorem inputs_xor3 (a₀ a₁ a₂ : V) (k : Fin 3) :
    (xor3 a₀ a₁ a₂).inputs k = a₀ ∨ (xor3 a₀ a₁ a₂).inputs k = a₁ ∨
      (xor3 a₀ a₁ a₂).inputs k = a₂ := by
  fin_cases k <;> simp [xor3]

theorem inputs_maj3 (a₀ a₁ a₂ : V) (k : Fin 3) :
    (maj3 a₀ a₁ a₂).inputs k = a₀ ∨ (maj3 a₀ a₁ a₂).inputs k = a₁ ∨
      (maj3 a₀ a₁ a₂).inputs k = a₂ := by
  fin_cases k <;> simp [maj3]

variable [DecidableEq V]

/-- The Tseitin clause of the gate `g` with output variable `o` for the input pattern `b`: if
the inputs take the values `b`, then `o` takes the value `g.fn b`. -/
def clause (g : Gate V) (o : V) (b : Fin g.arity → Bool) : Clause V :=
  (Finset.univ.image fun i => (⟨g.inputs i, !b i⟩ : Literal V)) ∪ {⟨o, g.fn b⟩}

/-- The Tseitin clauses of the gate `g` with output variable `o`: one clause per input pattern. -/
def clauses (g : Gate V) (o : V) : CNF V := Finset.univ.image (g.clause o)

theorem card_clause_le (g : Gate V) (o : V) (b : Fin g.arity → Bool) :
    (g.clause o b).card ≤ g.arity + 1 :=
  (Finset.card_union_le _ _).trans
    (Nat.add_le_add (Finset.card_image_le.trans_eq (Finset.card_fin _))
      (Finset.card_singleton _).le)

/-- The Tseitin clauses of a gate are satisfied exactly when the output variable takes the value
of the gate function at the input variables. -/
theorem sat_clauses_iff (g : Gate V) (o : V) (β : V → Bool) :
    CNF.Sat β (g.clauses o) ↔ β o = g.fn (β ∘ g.inputs) := by
  constructor
  · intro h
    obtain ⟨l, hl, hs⟩ :=
      h _ (Finset.mem_image_of_mem (g.clause o) (Finset.mem_univ (β ∘ g.inputs)))
    simp only [clause, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_singleton] at hl
    rcases hl with ⟨i, rfl⟩ | rfl
    · exact absurd hs (by simp [Literal.Sat])
    · exact hs
  · intro h C hC
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hC
    by_cases hb : β ∘ g.inputs = b
    · refine ⟨⟨o, g.fn b⟩, Finset.mem_union_right _ (Finset.mem_singleton_self _), ?_⟩
      change β o = g.fn b
      rw [h, hb]
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp hb
      refine ⟨⟨g.inputs i, !b i⟩,
        Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)), ?_⟩
      simpa [Literal.Sat, Bool.eq_not] using hi

end Gate

/-! ### Circuits -/

/-- A circuit over the variables `V` with wires `W`. Each wire is a variable (`wire`), recognized
among the variables by `toWire?`, and is computed by a gate whose inputs are variables: inputs
of the circuit, or wires of smaller rank. -/
structure Circuit (V W : Type*) where
  /-- The wires as variables. -/
  wire : W → V
  /-- Recognizing the wires among the variables. -/
  toWire? : V → Option W
  toWire?_wire : ∀ w, toWire? (wire w) = some w
  eq_wire_of_toWire? : ∀ {v : V} {w : W}, toWire? v = some w → v = wire w
  /-- The gate computing each wire. -/
  gate : W → Gate V
  /-- A rank on wires, strictly decreasing along the inputs of gates. -/
  rank : W → ℕ
  rank_lt : ∀ w i w', toWire? ((gate w).inputs i) = some w' → rank w' < rank w

namespace Circuit

variable {V W : Type*} (c : Circuit V W)

theorem wire_injective : Function.Injective c.wire := by
  intro w w' h
  have := c.toWire?_wire w
  rw [h, c.toWire?_wire] at this
  exact (Option.some.inj this).symm

/-- Induction on wires along the rank. -/
theorem rank_induction {P : W → Prop} (h : ∀ w, (∀ w', c.rank w' < c.rank w → P w') → P w)
    (w : W) : P w :=
  (measure c.rank).wf.induction w fun w ih => h w fun w' hw' => ih w' hw'

/-- The value of the wire `w` when the input variables take the values given by `α`: the gate of
`w` is applied to the values of its inputs, wires being evaluated recursively. -/
def eval (α : V → Bool) (w : W) : Bool :=
  (c.gate w).fn fun i =>
    match _h : c.toWire? ((c.gate w).inputs i) with
    | some w' => eval α w'
    | none => α ((c.gate w).inputs i)
termination_by c.rank w
decreasing_by exact c.rank_lt w i w' ‹_›

/-- The assignment evaluating the circuit: wires take their computed values, the other
variables keep their values under `α`. -/
def evalAssign (α : V → Bool) (v : V) : Bool :=
  match c.toWire? v with
  | some w => c.eval α w
  | none => α v

theorem evalAssign_of_eq_none {α : V → Bool} {v : V} (h : c.toWire? v = none) :
    c.evalAssign α v = α v := by
  simp [evalAssign, h]

theorem evalAssign_of_eq_some {α : V → Bool} {v : V} {w : W} (h : c.toWire? v = some w) :
    c.evalAssign α v = c.eval α w := by
  simp [evalAssign, h]

@[simp] theorem evalAssign_wire (α : V → Bool) (w : W) : c.evalAssign α (c.wire w) = c.eval α w :=
  c.evalAssign_of_eq_some (c.toWire?_wire w)

/-- Unfolding the evaluation of a wire: its gate applied to the evaluated inputs. -/
theorem eval_eq (α : V → Bool) (w : W) :
    c.eval α w = (c.gate w).fn fun i => c.evalAssign α ((c.gate w).inputs i) := by
  rw [eval]
  congr 1
  funext i
  unfold evalAssign
  split <;> rename_i h <;> simp [h]

/-- The value of a wire depends on the assignment only at the variables that are not wires. -/
theorem eval_congr {α α' : V → Bool} (hα : ∀ v, c.toWire? v = none → α v = α' v) (w : W) :
    c.eval α w = c.eval α' w := by
  induction w using c.rank_induction with
  | h w ih =>
    rw [eval_eq, eval_eq]
    congr 1
    funext i
    rcases hx : c.toWire? ((c.gate w).inputs i) with _ | w'
    · rw [c.evalAssign_of_eq_none hx, c.evalAssign_of_eq_none hx]
      exact hα _ hx
    · rw [c.evalAssign_of_eq_some hx, c.evalAssign_of_eq_some hx]
      exact ih w' (c.rank_lt w i w' hx)

section Tseitin

variable [DecidableEq V] [Fintype W]

/-- The Tseitin encoding of the circuit: the Tseitin clauses of all its gates. -/
def tseitin : CNF V := Finset.univ.biUnion fun w => (c.gate w).clauses (c.wire w)

/-- An assignment satisfies the Tseitin encoding exactly when every wire takes the value of its
gate at the current values of the gate's inputs. -/
theorem sat_tseitin_iff_fn (β : V → Bool) :
    CNF.Sat β c.tseitin ↔ ∀ w, β (c.wire w) = (c.gate w).fn (β ∘ (c.gate w).inputs) := by
  constructor
  · intro h w
    exact (Gate.sat_clauses_iff _ _ β).mp fun C hC =>
      h C (Finset.mem_biUnion.mpr ⟨w, Finset.mem_univ w, hC⟩)
  · intro h C hC
    obtain ⟨w, -, hC⟩ := Finset.mem_biUnion.mp hC
    exact (Gate.sat_clauses_iff _ _ β).mpr (h w) C hC

/-- **Exactness of the Tseitin encoding.** An assignment satisfies the Tseitin encoding of a
circuit exactly when every wire takes the value computed by the circuit from the assignment's
values on the input variables. -/
theorem sat_tseitin_iff (β : V → Bool) :
    CNF.Sat β c.tseitin ↔ ∀ w, β (c.wire w) = c.eval β w := by
  rw [sat_tseitin_iff_fn]
  have key : ∀ w, (∀ w', c.rank w' < c.rank w → β (c.wire w') = c.eval β w') →
      (c.gate w).fn (β ∘ (c.gate w).inputs) = c.eval β w := by
    intro w ih
    rw [eval_eq]
    congr 1
    funext i
    rcases hx : c.toWire? ((c.gate w).inputs i) with _ | w'
    · rw [c.evalAssign_of_eq_none hx]
      rfl
    · rw [c.evalAssign_of_eq_some hx, ← ih w' (c.rank_lt w i w' hx), Function.comp_apply,
        c.eq_wire_of_toWire? hx]
  constructor
  · intro h w
    induction w using c.rank_induction with
    | h w ih =>
      rw [h w]
      exact key w ih
  · intro h w
    rw [h w, key w fun w' _ => h w']

/-- The Tseitin clauses have width at most the fan-in plus one. -/
theorem width_tseitin_le (k : ℕ) (hk : ∀ w, (c.gate w).arity ≤ k) : c.tseitin.width ≤ k + 1 := by
  refine Finset.sup_le fun C hC => ?_
  obtain ⟨w, -, hC⟩ := Finset.mem_biUnion.mp hC
  obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hC
  exact ((c.gate w).card_clause_le _ b).trans (Nat.add_le_add_right (hk w) 1)

end Tseitin

end Circuit

/-! ### Circuits over the variables of a multiplier encoding -/

namespace MulVar

variable {n : ℕ} {W : Type*}

/-- Recognizing the wires among the variables of a multiplier encoding. -/
def toWire? : MulVar n W → Option W
  | .wire w => some w
  | _ => none

@[simp] theorem toWire?_x (i : Fin n) : (x i : MulVar n W).toWire? = none := rfl

@[simp] theorem toWire?_y (j : Fin n) : (y j : MulVar n W).toWire? = none := rfl

@[simp] theorem toWire?_wire (w : W) : (wire w : MulVar n W).toWire? = some w := rfl

theorem toWire?_eq_some_iff {v : MulVar n W} {w : W} : v.toWire? = some w ↔ v = wire w := by
  cases v <;> simp [toWire?]

/-- The assignment of the input variables given by two bit-vectors; wires get `false`. -/
def ofInputs (x y : Bits n) : MulVar n W → Bool
  | .x i => x i
  | .y j => y j
  | .wire _ => false

@[simp] theorem ofInputs_x (x y : Bits n) (i : Fin n) : ofInputs (W := W) x y (.x i) = x i := rfl

@[simp] theorem ofInputs_y (x y : Bits n) (j : Fin n) : ofInputs (W := W) x y (.y j) = y j := rfl

end MulVar

/-- A circuit over the variables `MulVar n W` of a multiplier encoding whose wires are the
`wire` variables: the gate of each wire, and a rank strictly decreasing along gate inputs. -/
structure MulCircuit (n : ℕ) (W : Type*) where
  /-- The gate computing each wire. -/
  gate : W → Gate (MulVar n W)
  /-- A rank on wires, strictly decreasing along the inputs of gates. -/
  rank : W → ℕ
  rank_lt : ∀ w i w', (gate w).inputs i = MulVar.wire w' → rank w' < rank w

namespace MulCircuit

variable {n : ℕ} {W : Type*} (c : MulCircuit n W)

/-- The underlying circuit. -/
def toCircuit : Circuit (MulVar n W) W where
  wire := MulVar.wire
  toWire? := MulVar.toWire?
  toWire?_wire _ := rfl
  eq_wire_of_toWire? h := MulVar.toWire?_eq_some_iff.mp h
  gate := c.gate
  rank := c.rank
  rank_lt w i w' h := c.rank_lt w i w' (MulVar.toWire?_eq_some_iff.mp h)

/-- The value of the wire `w` on the inputs `x, y`. -/
def eval (x y : Bits n) (w : W) : Bool := c.toCircuit.eval (MulVar.ofInputs x y) w

/-- Unfolding the value of a wire: its gate applied to the values of its inputs. -/
theorem eval_eq (x y : Bits n) (w : W) :
    c.eval x y w = (c.gate w).fn fun i => c.toCircuit.evalAssign (MulVar.ofInputs x y)
      ((c.gate w).inputs i) :=
  c.toCircuit.eval_eq _ w

@[simp] theorem evalAssign_x (x y : Bits n) (i : Fin n) :
    c.toCircuit.evalAssign (MulVar.ofInputs x y) (.x i) = x i :=
  c.toCircuit.evalAssign_of_eq_none rfl

@[simp] theorem evalAssign_y (x y : Bits n) (j : Fin n) :
    c.toCircuit.evalAssign (MulVar.ofInputs x y) (.y j) = y j :=
  c.toCircuit.evalAssign_of_eq_none rfl

@[simp] theorem evalAssign_wire (x y : Bits n) (w : W) :
    c.toCircuit.evalAssign (MulVar.ofInputs x y) (.wire w) = c.eval x y w :=
  c.toCircuit.evalAssign_of_eq_some rfl

/-- The value of a wire under any assignment is its value on the assignment's inputs. -/
theorem toCircuit_eval (α : MulVar n W → Bool) (w : W) :
    c.toCircuit.eval α w = c.eval (α ∘ MulVar.x) (α ∘ MulVar.y) w := by
  refine c.toCircuit.eval_congr (fun v hv => ?_) w
  cases v with
  | x i => rfl
  | y j => rfl
  | wire w => exact absurd hv (by simp [toCircuit])

end MulCircuit

/-- The exact multiplier encoding of a circuit over `MulVar n W`: the Tseitin encoding, with the
wire functions given by evaluation, once the designated output is shown to compute the
product. -/
def MulEncoding.ofMulCircuit {n : ℕ} {W : Type} [DecidableEq W] [Fintype W] (c : MulCircuit n W)
    (out : Fin (2 * n) → W) (out_injective : Function.Injective out)
    (toNat_out : ∀ x y : Bits n,
      Bits.toNat (fun i => c.eval x y (out i)) = Bits.toNat x * Bits.toNat y) :
    MulEncoding n where
  Wire := W
  cnf := c.toCircuit.tseitin
  fn w x y := c.eval x y w
  out := out
  out_injective := out_injective
  sat_iff α := by
    rw [c.toCircuit.sat_tseitin_iff]
    exact forall_congr' fun w => by rw [c.toCircuit_eval]; rfl
  toNat_out := toNat_out

/-- The clauses of the encoding of a circuit have width at most the fan-in plus one. -/
theorem MulEncoding.width_ofMulCircuit_le {n : ℕ} {W : Type} [DecidableEq W] [Fintype W]
    (c : MulCircuit n W) (out : Fin (2 * n) → W) (out_injective : Function.Injective out)
    (toNat_out : ∀ x y : Bits n,
      Bits.toNat (fun i => c.eval x y (out i)) = Bits.toNat x * Bits.toNat y)
    (k : ℕ) (hk : ∀ w, (c.gate w).arity ≤ k) :
    (MulEncoding.ofMulCircuit c out out_injective toNat_out).cnf.width ≤ k + 1 :=
  c.toCircuit.width_tseitin_le k hk

end AssocLB
