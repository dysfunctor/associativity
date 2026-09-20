/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/
import Mathlib

/-!
# CNF formulas

Paper: Section 2 (Preliminaries), paragraph "CNF formulas".

## Main definitions

* `AssocLB.Literal V`: a literal over the variable type `V`, a variable with a sign. `lᶜ` is the
  complementary literal; `Literal.pos v` and `Literal.neg v` are the two literals of `v`.
* `AssocLB.Clause V`: a clause, a finite set of literals (`Finset (Literal V)`). Its width is
  `C.card`, and `∅` is the empty clause `⊥`. `Clause.IsTautology C` says that `C` contains
  complementary literals.
* `AssocLB.CNF V`: a CNF formula, a finite set of clauses. `CNF.width Φ` is the maximum width of
  its clauses and `CNF.vars Φ` the set of variables occurring in it.
* Assignments are functions `V → Bool`. `Literal.Sat α l`, `Clause.Sat α C` and `CNF.Sat α Φ`
  say that `α` satisfies `l`, `C` or `Φ`. `CNF.Implies Φ C` says that every assignment
  satisfying `Φ` satisfies `C`.

## Design notes

* Clauses are sets, as in the paper, so the width of a clause is its cardinality and a clause
  never contains a literal twice.
* A CNF is a finite set of clauses rather than a conjunction: the paper treats formulas as
  sets ("the clauses of `Φ`", "`Φ` contains a subclause").
* Assignments are total. Restrictions, i.e. partial assignments, belong to
  `AssocLB.Resolution.Substitution`.
* Satisfaction and implication are propositions; satisfaction is decidable.
-/

namespace AssocLB

/-- A literal over the variable type `V`: a variable together with a sign. The literal
`⟨v, true⟩` is the variable `v` itself and `⟨v, false⟩` is its negation `¬v`.

Paper: Section 2, "CNF formulas". -/
@[ext]
structure Literal (V : Type*) where
  /-- The variable of the literal. -/
  var : V
  /-- The sign: `true` for the positive literal `v`, `false` for the negative literal `¬v`. -/
  sign : Bool
  deriving DecidableEq

namespace Literal

variable {V : Type*}

/-- The positive literal `v`. -/
def pos (v : V) : Literal V := ⟨v, true⟩

/-- The negative literal `¬v`. -/
def neg (v : V) : Literal V := ⟨v, false⟩

/-- The complementary literal `lᶜ` is `l` with its sign flipped. -/
instance : Compl (Literal V) := ⟨fun l => ⟨l.var, !l.sign⟩⟩

@[simp] theorem compl_var (l : Literal V) : lᶜ.var = l.var := rfl

@[simp] theorem compl_sign (l : Literal V) : lᶜ.sign = !l.sign := rfl

@[simp] theorem compl_mk (v : V) (b : Bool) : (⟨v, b⟩ : Literal V)ᶜ = ⟨v, !b⟩ := rfl

@[simp] theorem compl_compl (l : Literal V) : lᶜᶜ = l := by
  ext <;> simp

@[simp] theorem var_pos (v : V) : (pos v).var = v := rfl

@[simp] theorem sign_pos (v : V) : (pos v).sign = true := rfl

@[simp] theorem var_neg (v : V) : (neg v).var = v := rfl

@[simp] theorem sign_neg (v : V) : (neg v).sign = false := rfl

@[simp] theorem compl_pos (v : V) : (pos v)ᶜ = neg v := rfl

@[simp] theorem compl_neg (v : V) : (neg v)ᶜ = pos v := rfl

theorem compl_ne (l : Literal V) : lᶜ ≠ l := by
  intro h
  have := congrArg sign h
  simp at this

/-- Every literal is the positive or the negative literal of its variable. -/
theorem eq_pos_or_eq_neg (l : Literal V) : l = pos l.var ∨ l = neg l.var := by
  rcases l with ⟨v, _ | _⟩ <;> simp [pos, neg]

/-- `Literal.Sat α l`: the assignment `α` satisfies the literal `l`, that is, `α` gives the
variable of `l` the sign of `l`. -/
def Sat (α : V → Bool) (l : Literal V) : Prop := α l.var = l.sign

instance (α : V → Bool) (l : Literal V) : Decidable (Sat α l) :=
  inferInstanceAs (Decidable (α l.var = l.sign))

@[simp] theorem sat_pos_iff (α : V → Bool) (v : V) : Sat α (pos v) ↔ α v = true := Iff.rfl

@[simp] theorem sat_neg_iff (α : V → Bool) (v : V) : Sat α (neg v) ↔ α v = false := Iff.rfl

/-- An assignment satisfies exactly one of `l` and `lᶜ`. -/
@[simp] theorem sat_compl_iff (α : V → Bool) (l : Literal V) : Sat α lᶜ ↔ ¬ Sat α l := by
  simp [Sat, Bool.eq_not]

/-- The literals over the variables of `X`. -/
def ofVars [DecidableEq V] (X : Finset V) : Finset (Literal V) :=
  (X ×ˢ (Finset.univ : Finset Bool)).image fun p => ⟨p.1, p.2⟩

theorem mem_ofVars [DecidableEq V] {X : Finset V} {l : Literal V} :
    l ∈ ofVars X ↔ l.var ∈ X := by
  constructor
  · intro h
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
    exact (Finset.mem_product.mp hp).1
  · intro h
    exact Finset.mem_image.mpr
      ⟨(l.var, l.sign), Finset.mem_product.mpr ⟨h, Finset.mem_univ _⟩, rfl⟩

/-- There are at most `2 |X|` literals over the variables `X`. -/
theorem card_ofVars_le [DecidableEq V] (X : Finset V) : (ofVars X).card ≤ 2 * X.card := by
  refine Finset.card_image_le.trans_eq ?_
  rw [Finset.card_product, Finset.card_univ, Fintype.card_bool, Nat.mul_comm]

end Literal

/-- A clause: a finite set of literals, read as their disjunction. The width of a clause is its
number of literals `C.card`, and the empty clause `∅` is the clause `⊥`.

Paper: Section 2, "CNF formulas". -/
abbrev Clause (V : Type*) := Finset (Literal V)

namespace Clause

variable {V : Type*}

/-- A clause is a tautology if it contains complementary literals.

Paper: Section 2, "CNF formulas". -/
def IsTautology (C : Clause V) : Prop := ∃ l ∈ C, lᶜ ∈ C

instance [DecidableEq V] (C : Clause V) : Decidable C.IsTautology :=
  inferInstanceAs (Decidable (∃ l ∈ C, lᶜ ∈ C))

/-- The set of variables occurring in a clause. -/
def vars [DecidableEq V] (C : Clause V) : Finset V := C.image Literal.var

theorem mem_vars [DecidableEq V] {C : Clause V} {v : V} : v ∈ C.vars ↔ ∃ l ∈ C, l.var = v :=
  Finset.mem_image

theorem subset_ofVars [DecidableEq V] {C : Clause V} {X : Finset V} (h : C.vars ⊆ X) :
    C ⊆ Literal.ofVars X := fun l hl =>
  Literal.mem_ofVars.mpr (h (mem_vars.mpr ⟨l, hl, rfl⟩))

/-- There are at most `2 ^ (2 |X|)` clauses over the variables `X`. -/
theorem card_le_of_vars_subset [DecidableEq V] {T : Finset (Clause V)} {X : Finset V}
    (h : ∀ C ∈ T, C.vars ⊆ X) : T.card ≤ 2 ^ (2 * X.card) :=
  calc T.card ≤ (Literal.ofVars X).powerset.card :=
        Finset.card_le_card fun C hC => Finset.mem_powerset.mpr (subset_ofVars (h C hC))
    _ = 2 ^ (Literal.ofVars X).card := Finset.card_powerset _
    _ ≤ 2 ^ (2 * X.card) := Nat.pow_le_pow_right two_pos (Literal.card_ofVars_le X)

/-- `Clause.Sat α C`: the assignment `α` satisfies some literal of `C`. -/
def Sat (α : V → Bool) (C : Clause V) : Prop := ∃ l ∈ C, l.Sat α

instance (α : V → Bool) (C : Clause V) : Decidable (Sat α C) :=
  inferInstanceAs (Decidable (∃ l ∈ C, l.Sat α))

@[simp] theorem not_sat_empty (α : V → Bool) : ¬ Sat α (∅ : Clause V) := by
  simp [Sat]

theorem sat_of_mem {α : V → Bool} {C : Clause V} {l : Literal V} (hl : l ∈ C) (h : l.Sat α) :
    Sat α C :=
  ⟨l, hl, h⟩

/-- Satisfaction of a clause depends only on the values of its variables. -/
theorem sat_congr [DecidableEq V] {α α' : V → Bool} {C : Clause V}
    (h : ∀ v ∈ C.vars, α v = α' v) : Sat α C ↔ Sat α' C := by
  constructor <;> rintro ⟨l, hl, hs⟩ <;> refine ⟨l, hl, ?_⟩ <;> rw [Literal.Sat] at hs ⊢
  · rw [← h l.var (mem_vars.mpr ⟨l, hl, rfl⟩)]
    exact hs
  · rw [h l.var (mem_vars.mpr ⟨l, hl, rfl⟩)]
    exact hs

/-- Satisfaction is monotone in the clause: a superclause of a satisfied clause is satisfied. -/
theorem Sat.mono {α : V → Bool} {C D : Clause V} (hC : Sat α C) (h : C ⊆ D) : Sat α D :=
  let ⟨l, hl, hs⟩ := hC
  ⟨l, h hl, hs⟩

/-- A tautology is satisfied by every assignment. -/
theorem IsTautology.sat {C : Clause V} (h : C.IsTautology) (α : V → Bool) : Sat α C := by
  obtain ⟨l, hl, hlc⟩ := h
  by_cases hs : l.Sat α
  · exact ⟨l, hl, hs⟩
  · exact ⟨lᶜ, hlc, (Literal.sat_compl_iff α l).mpr hs⟩

end Clause

/-- A CNF formula: a finite set of clauses, read as their conjunction.

Paper: Section 2, "CNF formulas". -/
abbrev CNF (V : Type*) := Finset (Clause V)

namespace CNF

variable {V : Type*}

/-- The width `w(Φ)` of a CNF: the maximum width of its clauses, and `0` for the empty CNF.

Paper: Section 2, "CNF formulas". -/
def width (Φ : CNF V) : ℕ := Φ.sup Finset.card

theorem card_le_width {Φ : CNF V} {C : Clause V} (h : C ∈ Φ) : C.card ≤ Φ.width :=
  Finset.le_sup (f := Finset.card) h

/-- The set of variables occurring in a CNF. -/
def vars [DecidableEq V] (Φ : CNF V) : Finset V := Φ.biUnion Clause.vars

theorem mem_vars [DecidableEq V] {Φ : CNF V} {v : V} :
    v ∈ Φ.vars ↔ ∃ C ∈ Φ, ∃ l ∈ C, l.var = v := by
  simp [vars, Clause.mem_vars]

/-- `CNF.Sat α Φ`: the assignment `α` satisfies every clause of `Φ`. -/
def Sat (α : V → Bool) (Φ : CNF V) : Prop := ∀ C ∈ Φ, Clause.Sat α C

instance (α : V → Bool) (Φ : CNF V) : Decidable (Sat α Φ) :=
  inferInstanceAs (Decidable (∀ C ∈ Φ, Clause.Sat α C))

theorem sat_union_iff [DecidableEq V] {α : V → Bool} {Φ Ψ : CNF V} :
    Sat α (Φ ∪ Ψ) ↔ Sat α Φ ∧ Sat α Ψ :=
  Finset.forall_mem_union

theorem sat_singleton_iff {α : V → Bool} {C : Clause V} :
    Sat α ({C} : CNF V) ↔ Clause.Sat α C := by
  simp [Sat]

theorem sat_biUnion_iff [DecidableEq V] {ι : Type*} {s : Finset ι} {f : ι → CNF V}
    {α : V → Bool} : Sat α (s.biUnion f) ↔ ∀ i ∈ s, Sat α (f i) := by
  constructor
  · intro h i hi C hC
    exact h C (Finset.mem_biUnion.mpr ⟨i, hi, hC⟩)
  · intro h C hC
    obtain ⟨i, hi, hC⟩ := Finset.mem_biUnion.mp hC
    exact h i hi C hC

/-- A CNF is satisfiable if some assignment satisfies it. -/
def Satisfiable (Φ : CNF V) : Prop := ∃ α, Sat α Φ

/-- Satisfaction is antitone in the CNF: an assignment satisfying `Φ'` satisfies every
`Φ ⊆ Φ'`. -/
theorem Sat.subset {α : V → Bool} {Φ Φ' : CNF V} (hα : Sat α Φ') (h : Φ ⊆ Φ') : Sat α Φ :=
  fun C hC => hα C (h hC)

/-- A CNF is unsatisfiable if no assignment satisfies it. -/
def Unsatisfiable (Φ : CNF V) : Prop := ¬ Φ.Satisfiable

/-- Unsatisfiability is monotone in the CNF. -/
theorem Unsatisfiable.mono {Φ Φ' : CNF V} (hΦ : Φ.Unsatisfiable) (h : Φ ⊆ Φ') :
    Φ'.Unsatisfiable := by
  rintro ⟨α, hα⟩
  exact hΦ ⟨α, hα.subset h⟩

/-- `CNF.Implies Φ C`: the clause `C` is implied by `Φ`, that is, every assignment satisfying
`Φ` satisfies `C`.

Paper: Section 2, "Resolution". -/
def Implies (Φ : CNF V) (C : Clause V) : Prop := ∀ α, Sat α Φ → Clause.Sat α C

theorem implies_of_mem {Φ : CNF V} {C : Clause V} (h : C ∈ Φ) : Φ.Implies C :=
  fun _ hα => hα C h

theorem Implies.mono {Φ : CNF V} {C D : Clause V} (h : Φ.Implies C) (hCD : C ⊆ D) :
    Φ.Implies D :=
  fun α hα => (h α hα).mono hCD

/-- A CNF implies the empty clause if and only if it is unsatisfiable. -/
theorem implies_empty_iff (Φ : CNF V) : Φ.Implies ∅ ↔ Φ.Unsatisfiable := by
  simp [Implies, Unsatisfiable, Satisfiable]

end CNF

end AssocLB
