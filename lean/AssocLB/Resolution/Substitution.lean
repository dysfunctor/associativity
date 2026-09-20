/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/
import AssocLB.Resolution.Derivation

/-!
# Restrictions and substitutions

Paper: Section 2 (Preliminaries), paragraphs "Restrictions" and "Substitutions";
Lemma [lem:substitution] (substitution lemma). The restriction lemma below is its special case
for restrictions, and the subclause observation is used implicitly in the proof of
Lemma [lem:reduction].

## Main definitions

* `Restriction V`: a partial assignment `V → Option Bool`. A literal is satisfied
  (`Literal.SatBy`) or falsified (`Literal.FalsifiedBy`) by `ρ` when `ρ` gives its variable the
  right or the wrong sign. A clause is satisfied by `ρ` (`Clause.SatBy`) if one of its literals
  is, and otherwise survives `ρ` (`Clause.Survives`). `Clause.restrict ρ C` is `C↾ρ`, the clause
  `C` with its falsified literals removed, and `CNF.restrict ρ Φ` is `Φ↾ρ`, the restrictions of
  the clauses of `Φ` that survive `ρ`.
* `LitConst V'`: a Boolean constant or a literal over `V'`, the possible images of a variable
  under a substitution. `Subst V V'` is `V → LitConst V'`, and `Literal.subst σ l` extends `σ`
  to literals by `σ(¬x) = ¬σ(x)`.
* A clause is satisfied by `σ` (`Clause.SatUnder`) if one of its literals maps to `1`,
  tautological under `σ` (`Clause.TautUnder`) if two of its literals map to complementary
  literals, and otherwise survives `σ` (`Clause.SurvivesUnder`). `Clause.subst σ C` is `C^σ`,
  the images of the literals of `C` with the constants dropped, and `CNF.subst σ Φ` is `Φ^σ`,
  the images of the clauses of `Φ` that survive `σ`.
* `Restriction.toSubst ρ`: the restriction `ρ` read as a substitution, mapping each assigned
  variable to its constant and each unassigned variable to itself.
* `Subst.pullback σ α`: the assignment `α ∘ σ` of `V`, giving each variable the value of its
  image under the assignment `α` of `V'`.

## Main results

* `CNF.sat_subst_iff`: `α` satisfies `Φ^σ` if and only if `α ∘ σ` satisfies `Φ`. Hence `Φ^σ` is
  unsatisfiable whenever `Φ` is (`CNF.Unsatisfiable.subst`).
* `CNF.subst_toSubst`: `Φ^ρ` is `Φ↾ρ` without its tautological clauses; in particular
  `Φ^ρ ⊆ Φ↾ρ` (`CNF.subst_toSubst_subset`).
* `Refutation.subst`, the substitution lemma (Lemma [lem:substitution]): a refutation of `Φ`
  yields a refutation of `Φ^σ` of at most the same size. `Refutation.restrict` is the
  special case of Lemma [lem:substitution] for restrictions, and `Refutation.of_subclauses` is
  the observation, used implicitly in the proof of Lemma [lem:reduction], that a refutation may
  start from subclauses of its initial clauses.
* Behind them is one simulation argument, `IsDerivation.exists_simulation`: given a derivation
  from `Φ`, a substitution `σ` and a clause `W`, any CNF `Ψ` containing a subclause of `C^σ ∪ W`
  for each surviving initial clause `C` derives a subclause of `C^σ ∪ W` for each surviving
  clause `C` of the derivation, in at most the same number of lines. The substitution lemma is
  the case `Ψ = Φ^σ`, `W = ∅`; the observation is the case of the identity substitution; and
  `Refutation.exists_lift`, the lifting of a refutation of `Φ↾ρ` to a derivation from `Φ` of a
  subclause of the falsified literals, is the identity substitution with `W` the falsified
  literals. Lifting is what completeness (`AssocLB.Resolution.Completeness`) needs.

## Design notes

* The paper's proof of the restriction lemma uses `Φ^ρ = Φ↾ρ`. This holds only up to
  tautological clauses: a clause of `Φ` with complementary literals on variables that `ρ` leaves
  unassigned survives `ρ`, but is tautological under `ρ` read as a substitution. The lemma is
  unaffected, since `Φ^ρ ⊆ Φ↾ρ` and a derivation from a subset of `Φ↾ρ` is a derivation
  from `Φ↾ρ`.
* `Clause.TautUnder` quantifies over the common target literal, as in the paper; its
  decidability, needed to select the surviving clauses, goes through `LitConst.IsLit`.

## Design notes on the simulation

* The invariant of the induction, over the sequence with its accumulator `S` of earlier
  clauses, is that every surviving clause of `S` has a simulated subclause in the accumulator
  `S'` of the new sequence. A line of the new sequence is added only when its clause is not yet
  in `S'`, since a derivation has no rule for repeating a clause.
* The case analysis of the paper's proof sketch is `Clause.exists_step`: with `σ(x)` a constant,
  the premise whose pivot literal maps to `0` survives and its simulated subclause is reused;
  with `σ(x)` a literal `ℓ`, at most one premise is tautological under `σ`, and either one
  simulated subclause already works or the two resolve on the variable of `ℓ`.
-/

namespace AssocLB

variable {V V' : Type*}

/-! ### Restrictions -/

/-- A restriction: a partial assignment to the variables, `none` on the unassigned ones.

Paper: Section 2, "Restrictions". -/
abbrev Restriction (V : Type*) := V → Option Bool

namespace Literal

/-- `ρ` satisfies the literal `l`: it gives the variable of `l` the sign of `l`. -/
def SatBy (ρ : Restriction V) (l : Literal V) : Prop := ρ l.var = some l.sign

/-- `ρ` falsifies the literal `l`: it gives the variable of `l` the opposite sign. -/
def FalsifiedBy (ρ : Restriction V) (l : Literal V) : Prop := ρ l.var = some (!l.sign)

instance (ρ : Restriction V) (l : Literal V) : Decidable (SatBy ρ l) :=
  inferInstanceAs (Decidable (ρ l.var = some l.sign))

instance (ρ : Restriction V) (l : Literal V) : Decidable (FalsifiedBy ρ l) :=
  inferInstanceAs (Decidable (ρ l.var = some (!l.sign)))

@[simp] theorem satBy_compl_iff (ρ : Restriction V) (l : Literal V) :
    SatBy ρ lᶜ ↔ FalsifiedBy ρ l :=
  Iff.rfl

@[simp] theorem falsifiedBy_compl_iff (ρ : Restriction V) (l : Literal V) :
    FalsifiedBy ρ lᶜ ↔ SatBy ρ l := by
  simp [SatBy, FalsifiedBy]

theorem SatBy.not_falsifiedBy {ρ : Restriction V} {l : Literal V} (h : SatBy ρ l) :
    ¬ FalsifiedBy ρ l := by
  intro h'
  rw [FalsifiedBy, SatBy.eq_def] at *
  rw [h] at h'
  simp at h'

/-- A literal neither satisfied nor falsified by `ρ` has an unassigned variable. -/
theorem eq_none_of_not_satBy_of_not_falsifiedBy {ρ : Restriction V} {l : Literal V}
    (h₁ : ¬ SatBy ρ l) (h₂ : ¬ FalsifiedBy ρ l) : ρ l.var = none := by
  rcases l with ⟨v, s⟩
  simp only [SatBy, FalsifiedBy] at h₁ h₂
  rcases h : ρ v with _ | b
  · rfl
  · rw [h] at h₁ h₂
    cases b <;> cases s <;> simp_all

end Literal

namespace Clause

/-- `ρ` satisfies the clause `C` if it satisfies some literal of `C`.

Paper: Section 2, "Restrictions". -/
def SatBy (ρ : Restriction V) (C : Clause V) : Prop := ∃ l ∈ C, l.SatBy ρ

instance (ρ : Restriction V) (C : Clause V) : Decidable (SatBy ρ C) :=
  inferInstanceAs (Decidable (∃ l ∈ C, l.SatBy ρ))

/-- The clause `C` survives `ρ` if `ρ` satisfies no literal of it.

Paper: Section 2, "Restrictions". -/
def Survives (ρ : Restriction V) (C : Clause V) : Prop := ¬ SatBy ρ C

instance (ρ : Restriction V) (C : Clause V) : Decidable (Survives ρ C) :=
  inferInstanceAs (Decidable (¬ SatBy ρ C))

/-- The restricted clause `C↾ρ`: `C` with its falsified literals removed.

Paper: Section 2, "Restrictions". -/
def restrict (ρ : Restriction V) (C : Clause V) : Clause V :=
  C.filter fun l => ¬ l.FalsifiedBy ρ

@[simp] theorem mem_restrict {ρ : Restriction V} {C : Clause V} {l : Literal V} :
    l ∈ C.restrict ρ ↔ l ∈ C ∧ ¬ l.FalsifiedBy ρ :=
  Finset.mem_filter

theorem restrict_subset (ρ : Restriction V) (C : Clause V) : C.restrict ρ ⊆ C :=
  Finset.filter_subset _ _

@[simp] theorem restrict_empty (ρ : Restriction V) : (∅ : Clause V).restrict ρ = ∅ :=
  Finset.filter_empty _

@[simp] theorem survives_empty (ρ : Restriction V) : Survives ρ (∅ : Clause V) := by
  simp [Survives, SatBy]

end Clause

namespace CNF

variable [DecidableEq V]

/-- The restricted CNF `Φ↾ρ`: the restrictions of the clauses of `Φ` that survive `ρ`.

Paper: Section 2, "Restrictions". -/
def restrict (ρ : Restriction V) (Φ : CNF V) : CNF V :=
  (Φ.filter (Clause.Survives ρ)).image (Clause.restrict ρ)

theorem mem_restrict {ρ : Restriction V} {Φ : CNF V} {D : Clause V} :
    D ∈ Φ.restrict ρ ↔ ∃ C ∈ Φ, C.Survives ρ ∧ C.restrict ρ = D := by
  simp [restrict, and_assoc]

end CNF

/-! ### Substitutions -/

/-- A Boolean constant or a literal over `V`: the possible images of a variable under a
substitution.

Paper: Section 2, "Substitutions". -/
inductive LitConst (V : Type*)
  /-- The constant `b`. -/
  | const (b : Bool) : LitConst V
  /-- The literal `l`. -/
  | lit (l : Literal V) : LitConst V
  deriving DecidableEq

namespace LitConst

/-- Negation: `¬b` for a constant and `lᶜ` for a literal. -/
instance : Compl (LitConst V) :=
  ⟨fun x => match x with
    | const b => const (!b)
    | lit l => lit lᶜ⟩

@[simp] theorem compl_const (b : Bool) : (const b : LitConst V)ᶜ = const (!b) := rfl

@[simp] theorem compl_lit (l : Literal V) : (lit l)ᶜ = lit lᶜ := rfl

@[simp] theorem compl_compl (x : LitConst V) : xᶜᶜ = x := by
  cases x <;> simp

/-- `x` is a literal rather than a constant. -/
def IsLit : LitConst V → Prop
  | const _ => False
  | lit _ => True

instance : DecidablePred (IsLit (V := V))
  | const _ => isFalse fun h => h
  | lit _ => isTrue trivial

@[simp] theorem not_isLit_const (b : Bool) : ¬ IsLit (const b : LitConst V) := fun h => h

@[simp] theorem isLit_lit (l : Literal V) : IsLit (lit l) := trivial

theorem isLit_iff {x : LitConst V} : x.IsLit ↔ ∃ l, x = lit l := by
  cases x <;> simp

/-- The literals of `x`: `{l}` if `x` is the literal `l`, and `∅` if `x` is a constant. -/
def toClause : LitConst V → Clause V
  | const _ => ∅
  | lit l => {l}

@[simp] theorem toClause_const (b : Bool) : (const b : LitConst V).toClause = ∅ := rfl

@[simp] theorem toClause_lit (l : Literal V) : (lit l).toClause = {l} := rfl

@[simp] theorem mem_toClause {x : LitConst V} {l : Literal V} : l ∈ x.toClause ↔ x = lit l := by
  cases x with
  | const b => simp [toClause]
  | lit l' => simp [toClause, eq_comm]

theorem card_toClause_le (x : LitConst V) : x.toClause.card ≤ 1 := by
  cases x <;> simp [toClause]

/-- The value of `x` under the assignment `α`: the constant itself, or the truth value of the
literal. -/
def eval (α : V → Bool) : LitConst V → Bool
  | const b => b
  | lit l => decide (l.Sat α)

@[simp] theorem eval_const (α : V → Bool) (b : Bool) : eval α (const b : LitConst V) = b := rfl

@[simp] theorem eval_lit (α : V → Bool) (l : Literal V) : eval α (lit l) = decide (l.Sat α) :=
  rfl

@[simp] theorem eval_compl (α : V → Bool) (x : LitConst V) : eval α xᶜ = !eval α x := by
  cases x <;> simp

end LitConst

/-- A substitution: maps each variable of `V` to a constant or to a literal over `V'`. Distinct
variables may map to the same literal.

Paper: Section 2, "Substitutions". -/
abbrev Subst (V V' : Type*) := V → LitConst V'

namespace Literal

/-- The image `σ(l)` of a literal: `σ(x)` for the literal `x` and `¬σ(x)` for the literal `¬x`.

Paper: Section 2, "Substitutions". -/
def subst (σ : Subst V V') (l : Literal V) : LitConst V' :=
  bif l.sign then σ l.var else (σ l.var)ᶜ

@[simp] theorem subst_pos (σ : Subst V V') (v : V) : (pos v).subst σ = σ v := rfl

@[simp] theorem subst_neg (σ : Subst V V') (v : V) : (neg v).subst σ = (σ v)ᶜ := rfl

/-- `σ(¬x) = ¬σ(x)`. -/
@[simp] theorem subst_compl (σ : Subst V V') (l : Literal V) : lᶜ.subst σ = (l.subst σ)ᶜ := by
  rcases l with ⟨v, _ | _⟩ <;> simp [subst]

end Literal

namespace Subst

/-- The pullback `α ∘ σ` of an assignment `α` of `V'` along `σ`: each variable `v` of `V` gets
the value of `σ v` under `α`. -/
def pullback (σ : Subst V V') (α : V' → Bool) : V → Bool := fun v => (σ v).eval α

@[simp] theorem pullback_apply (σ : Subst V V') (α : V' → Bool) (v : V) :
    σ.pullback α v = (σ v).eval α :=
  rfl

end Subst

namespace Literal

/-- The pullback of `α` satisfies `l` exactly when `α` makes `σ(l)` true. -/
theorem sat_pullback_iff (σ : Subst V V') (α : V' → Bool) (l : Literal V) :
    Sat (σ.pullback α) l ↔ (l.subst σ).eval α = true := by
  rcases l with ⟨v, _ | _⟩ <;> simp [Sat, subst]

end Literal

namespace Clause

/-- `C` is satisfied by `σ`: some literal of `C` maps to the constant `1`.

Paper: Section 2, "Substitutions". -/
def SatUnder (σ : Subst V V') (C : Clause V) : Prop := ∃ l ∈ C, l.subst σ = .const true

/-- `C` is tautological under `σ`: two literals of `C` map to complementary literals.

Paper: Section 2, "Substitutions". -/
def TautUnder (σ : Subst V V') (C : Clause V) : Prop :=
  ∃ l ∈ C, ∃ l' ∈ C, ∃ m : Literal V', l.subst σ = .lit m ∧ l'.subst σ = .lit mᶜ

/-- `C` survives `σ`: it is neither satisfied by nor tautological under `σ`.

Paper: Section 2, "Substitutions". -/
def SurvivesUnder (σ : Subst V V') (C : Clause V) : Prop := ¬ SatUnder σ C ∧ ¬ TautUnder σ C

theorem tautUnder_iff (σ : Subst V V') (C : Clause V) :
    TautUnder σ C ↔ ∃ l ∈ C, ∃ l' ∈ C, (l.subst σ).IsLit ∧ l'.subst σ = (l.subst σ)ᶜ := by
  constructor
  · rintro ⟨l, hl, l', hl', m, hm, hm'⟩
    exact ⟨l, hl, l', hl', by simp [hm], by simp [hm, hm']⟩
  · rintro ⟨l, hl, l', hl', hlit, hl'σ⟩
    obtain ⟨m, hm⟩ := LitConst.isLit_iff.mp hlit
    exact ⟨l, hl, l', hl', m, hm, by simp [hl'σ, hm]⟩

@[simp] theorem survivesUnder_empty (σ : Subst V V') : SurvivesUnder σ (∅ : Clause V) := by
  simp [SurvivesUnder, SatUnder, TautUnder]

-- Sanity check: a tautology never survives a substitution, being satisfied by or tautological
-- under it.
example {C : Clause V} (h : C.IsTautology) (σ : Subst V V') : ¬ SurvivesUnder σ C := by
  obtain ⟨l, hl, hlc⟩ := h
  rintro ⟨hsat, htaut⟩
  generalize hx : l.subst σ = x
  cases x with
  | const b =>
    cases b
    · exact hsat ⟨lᶜ, hlc, by simp [hx]⟩
    · exact hsat ⟨l, hl, hx⟩
  | lit m => exact htaut ⟨l, hl, lᶜ, hlc, m, hx, by simp [hx]⟩

variable [DecidableEq V']

instance (σ : Subst V V') (C : Clause V) : Decidable (SatUnder σ C) :=
  inferInstanceAs (Decidable (∃ l ∈ C, l.subst σ = .const true))

instance (σ : Subst V V') (C : Clause V) : Decidable (TautUnder σ C) :=
  decidable_of_iff _ (tautUnder_iff σ C).symm

instance (σ : Subst V V') (C : Clause V) : Decidable (SurvivesUnder σ C) :=
  inferInstanceAs (Decidable (¬ SatUnder σ C ∧ ¬ TautUnder σ C))

/-- The image `C^σ` of a clause: the images of its literals, with the constants dropped.

Paper: Section 2, "Substitutions". -/
def subst (σ : Subst V V') (C : Clause V) : Clause V' :=
  C.biUnion fun l => (l.subst σ).toClause

@[simp] theorem mem_subst {σ : Subst V V'} {C : Clause V} {m : Literal V'} :
    m ∈ C.subst σ ↔ ∃ l ∈ C, l.subst σ = .lit m := by
  simp [subst]

@[simp] theorem subst_empty (σ : Subst V V') : (∅ : Clause V).subst σ = ∅ := by
  simp [subst]

theorem subst_mono {σ : Subst V V'} {C D : Clause V} (h : C ⊆ D) : C.subst σ ⊆ D.subst σ :=
  Finset.biUnion_subset_biUnion_of_subset_left _ h

/-- Substitution does not increase the width of a clause. -/
theorem card_subst_le (σ : Subst V V') (C : Clause V) : (C.subst σ).card ≤ C.card :=
  Finset.card_biUnion_le.trans <| by
    calc ∑ l ∈ C, (l.subst σ).toClause.card ≤ ∑ _l ∈ C, 1 :=
          Finset.sum_le_sum fun l _ => LitConst.card_toClause_le _
      _ = C.card := by simp

/-- For a clause not satisfied by `σ`, an assignment satisfies `C^σ` if and only if its pullback
satisfies `C`. -/
theorem sat_subst_iff {σ : Subst V V'} {C : Clause V} (h : ¬ SatUnder σ C) (α : V' → Bool) :
    Sat α (C.subst σ) ↔ Sat (σ.pullback α) C := by
  constructor
  · rintro ⟨m, hm, hmα⟩
    obtain ⟨l, hl, hlm⟩ := mem_subst.mp hm
    refine ⟨l, hl, ?_⟩
    rw [Literal.sat_pullback_iff, hlm]
    simpa using hmα
  · rintro ⟨l, hl, hlα⟩
    rw [Literal.sat_pullback_iff] at hlα
    generalize hx : l.subst σ = x at hlα
    cases x with
    | const b =>
      have hb : b = true := by simpa using hlα
      exact absurd ⟨l, hl, hb ▸ hx⟩ h
    | lit m => exact ⟨m, mem_subst.mpr ⟨l, hl, hx⟩, by simpa using hlα⟩

end Clause

namespace CNF

variable [DecidableEq V']

/-- The image `Φ^σ` of a CNF: the images of its clauses that survive `σ`.

Paper: Section 2, "Substitutions". -/
def subst (σ : Subst V V') (Φ : CNF V) : CNF V' :=
  (Φ.filter (Clause.SurvivesUnder σ)).image (Clause.subst σ)

theorem mem_subst {σ : Subst V V'} {Φ : CNF V} {D : Clause V'} :
    D ∈ Φ.subst σ ↔ ∃ C ∈ Φ, C.SurvivesUnder σ ∧ C.subst σ = D := by
  simp [subst, and_assoc]

/-- The clauses of `Φ^σ` are not tautologies: tautological images are discarded. -/
theorem not_isTautology_of_mem_subst {σ : Subst V V'} {Φ : CNF V} {D : Clause V'}
    (hD : D ∈ Φ.subst σ) : ¬ D.IsTautology := by
  obtain ⟨C, -, ⟨-, htaut⟩, rfl⟩ := mem_subst.mp hD
  rintro ⟨m, hm, hm'⟩
  obtain ⟨l, hl, hlm⟩ := Clause.mem_subst.mp hm
  obtain ⟨l', hl', hl'm⟩ := Clause.mem_subst.mp hm'
  exact htaut ⟨l, hl, l', hl', m, hlm, hl'm⟩

/-- An assignment satisfies `Φ^σ` if and only if its pullback satisfies `Φ`. -/
theorem sat_subst_iff (σ : Subst V V') (Φ : CNF V) (α : V' → Bool) :
    Sat α (Φ.subst σ) ↔ Sat (σ.pullback α) Φ := by
  constructor
  · intro hα C hC
    by_cases hsat : C.SatUnder σ
    · obtain ⟨l, hl, hlσ⟩ := hsat
      exact ⟨l, hl, by rw [Literal.sat_pullback_iff, hlσ]; rfl⟩
    by_cases htaut : C.TautUnder σ
    · obtain ⟨l, hl, l', hl', m, hm, hm'⟩ := htaut
      by_cases hmα : m.Sat α
      · exact ⟨l, hl, by rw [Literal.sat_pullback_iff, hm]; simpa using hmα⟩
      · exact ⟨l', hl', by rw [Literal.sat_pullback_iff, hm']; simpa using hmα⟩
    · exact (Clause.sat_subst_iff hsat α).mp (hα _ (mem_subst.mpr ⟨C, hC, ⟨hsat, htaut⟩, rfl⟩))
  · intro hα D hD
    obtain ⟨C, hC, hsurv, rfl⟩ := mem_subst.mp hD
    exact (Clause.sat_subst_iff hsurv.1 α).mpr (hα C hC)

/-- Substitution preserves unsatisfiability. -/
theorem Unsatisfiable.subst {Φ : CNF V} (h : Φ.Unsatisfiable) (σ : Subst V V') :
    (Φ.subst σ).Unsatisfiable := by
  rintro ⟨α, hα⟩
  exact h ⟨σ.pullback α, (sat_subst_iff σ Φ α).mp hα⟩

/-- Substitution does not increase the width of a CNF. -/
theorem width_subst_le (σ : Subst V V') (Φ : CNF V) : (Φ.subst σ).width ≤ Φ.width := by
  refine Finset.sup_le fun D hD => ?_
  obtain ⟨C, hC, -, rfl⟩ := mem_subst.mp hD
  exact (Clause.card_subst_le σ C).trans (card_le_width hC)

end CNF

/-! ### Restrictions as substitutions -/

namespace Restriction

/-- The restriction `ρ` as a substitution: each assigned variable maps to its constant and each
unassigned variable to itself.

Paper: Section 2, "Substitutions". -/
def toSubst (ρ : Restriction V) : Subst V V := fun v =>
  match ρ v with
  | some b => .const b
  | none => .lit (.pos v)

theorem toSubst_of_eq_some {ρ : Restriction V} {v : V} {b : Bool} (h : ρ v = some b) :
    ρ.toSubst v = .const b := by
  simp [toSubst, h]

theorem toSubst_of_eq_none {ρ : Restriction V} {v : V} (h : ρ v = none) :
    ρ.toSubst v = .lit (.pos v) := by
  simp [toSubst, h]

end Restriction

namespace Literal

/-- Under `ρ` read as a substitution, a literal maps to `1` exactly when `ρ` satisfies it. -/
theorem subst_toSubst_eq_const_true_iff (ρ : Restriction V) (l : Literal V) :
    l.subst ρ.toSubst = .const true ↔ l.SatBy ρ := by
  rcases l with ⟨v, s⟩
  rcases hv : ρ v with _ | b <;> cases s <;> simp [subst, Restriction.toSubst, hv, SatBy]

-- Sanity check: under `ρ` read as a substitution, a literal maps to `0` exactly when `ρ`
-- falsifies it.
example (ρ : Restriction V) (l : Literal V) :
    l.subst ρ.toSubst = .const false ↔ l.FalsifiedBy ρ := by
  rcases l with ⟨v, s⟩
  rcases hv : ρ v with _ | b <;> cases s <;> simp [subst, Restriction.toSubst, hv, FalsifiedBy]

/-- Under `ρ` read as a substitution, a literal maps to a literal exactly when its variable is
unassigned, and then it maps to itself. -/
theorem subst_toSubst_eq_lit_iff (ρ : Restriction V) (l m : Literal V) :
    l.subst ρ.toSubst = .lit m ↔ ρ l.var = none ∧ l = m := by
  rcases l with ⟨v, s⟩
  rcases hv : ρ v with _ | b <;> cases s <;> simp [subst, Restriction.toSubst, hv, pos]

end Literal

namespace Clause

theorem satUnder_toSubst_iff (ρ : Restriction V) (C : Clause V) :
    SatUnder ρ.toSubst C ↔ SatBy ρ C := by
  simp [SatUnder, SatBy, Literal.subst_toSubst_eq_const_true_iff]

/-- A clause is tautological under `ρ` read as a substitution exactly when its restriction is a
tautology. -/
theorem tautUnder_toSubst_iff (ρ : Restriction V) (C : Clause V) :
    TautUnder ρ.toSubst C ↔ (C.restrict ρ).IsTautology := by
  constructor
  · rintro ⟨l, hl, l', hl', m, hm, hm'⟩
    rw [Literal.subst_toSubst_eq_lit_iff] at hm hm'
    obtain ⟨hlv, rfl⟩ := hm
    obtain ⟨-, rfl⟩ := hm'
    exact ⟨_, mem_restrict.mpr ⟨hl, by simp [Literal.FalsifiedBy, hlv]⟩,
      mem_restrict.mpr ⟨hl', by simp [Literal.FalsifiedBy, hlv]⟩⟩
  · rintro ⟨l, hl, hlc⟩
    rw [mem_restrict] at hl hlc
    have hv : ρ l.var = none :=
      Literal.eq_none_of_not_satBy_of_not_falsifiedBy
        (fun h => hlc.2 ((Literal.falsifiedBy_compl_iff ρ l).mpr h)) hl.2
    refine ⟨l, hl.1, lᶜ, hlc.1, l, ?_, ?_⟩
    · exact (Literal.subst_toSubst_eq_lit_iff ρ l l).mpr ⟨hv, rfl⟩
    · exact (Literal.subst_toSubst_eq_lit_iff ρ lᶜ lᶜ).mpr ⟨by simpa using hv, rfl⟩

variable [DecidableEq V]

/-- The image of a surviving clause under `ρ` read as a substitution is its restriction. -/
theorem subst_toSubst (ρ : Restriction V) (C : Clause V) (h : C.Survives ρ) :
    C.subst ρ.toSubst = C.restrict ρ := by
  ext m
  simp only [mem_subst, mem_restrict, Literal.subst_toSubst_eq_lit_iff]
  constructor
  · rintro ⟨l, hl, hv, rfl⟩
    exact ⟨hl, by simp [Literal.FalsifiedBy, hv]⟩
  · rintro ⟨hm, hf⟩
    exact ⟨m, hm, Literal.eq_none_of_not_satBy_of_not_falsifiedBy (fun hs => h ⟨m, hm, hs⟩) hf,
      rfl⟩

end Clause

namespace CNF

variable [DecidableEq V]

/-- `Φ^ρ` is `Φ↾ρ` without its tautological clauses. -/
theorem subst_toSubst (ρ : Restriction V) (Φ : CNF V) :
    Φ.subst ρ.toSubst = (Φ.restrict ρ).filter fun D => ¬ D.IsTautology := by
  ext D
  rw [mem_subst, Finset.mem_filter, mem_restrict]
  constructor
  · rintro ⟨C, hC, ⟨hsat, htaut⟩, rfl⟩
    have hsurv : C.Survives ρ := (Clause.satUnder_toSubst_iff ρ C).not.mp hsat
    rw [Clause.subst_toSubst ρ C hsurv]
    exact ⟨⟨C, hC, hsurv, rfl⟩, (Clause.tautUnder_toSubst_iff ρ C).not.mp htaut⟩
  · rintro ⟨⟨C, hC, hsurv, rfl⟩, htaut⟩
    exact ⟨C, hC, ⟨(Clause.satUnder_toSubst_iff ρ C).not.mpr hsurv,
      (Clause.tautUnder_toSubst_iff ρ C).not.mpr htaut⟩, Clause.subst_toSubst ρ C hsurv⟩

/-- `Φ^ρ ⊆ Φ↾ρ`; the two agree when `Φ↾ρ` has no tautological clauses. -/
theorem subst_toSubst_subset (ρ : Restriction V) (Φ : CNF V) :
    Φ.subst ρ.toSubst ⊆ Φ.restrict ρ := by
  rw [subst_toSubst]
  exact Finset.filter_subset _ _

end CNF

/-! ### The identity substitution -/

/-- The identity substitution, mapping every variable to itself. -/
def Subst.id (V : Type*) : Subst V V := fun v => .lit (.pos v)

@[simp] theorem Literal.subst_id (l : Literal V) : l.subst (Subst.id V) = .lit l := by
  rcases l with ⟨v, _ | _⟩ <;> simp [Literal.subst, Subst.id, Literal.pos]

-- Sanity check: a clause survives the identity substitution exactly when it is not a tautology.
example (C : Clause V) : Clause.SurvivesUnder (Subst.id V) C ↔ ¬ C.IsTautology := by
  simp [Clause.SurvivesUnder, Clause.SatUnder, Clause.TautUnder, Clause.IsTautology]

@[simp] theorem Clause.subst_id [DecidableEq V] (C : Clause V) : C.subst (Subst.id V) = C := by
  ext m
  simp

/-! ### The substitution lemma -/

/-- A finite set contained in `T ∪ {a}` and not containing `a` is contained in `T`. -/
theorem subset_of_subset_union_singleton {α : Type*} [DecidableEq α] {D T : Finset α} {a : α}
    (h : D ⊆ T ∪ {a}) (ha : a ∉ D) : D ⊆ T := fun _ hm =>
  (Finset.mem_union.mp (h hm)).resolve_right fun h' => ha (Finset.mem_singleton.mp h' ▸ hm)

namespace Clause

variable [DecidableEq V']

/-- A clause whose image contains a literal and its complement is tautological under `σ`. -/
theorem tautUnder_of_mem_subst_of_compl_mem_subst {σ : Subst V V'} {C : Clause V}
    {ℓ : Literal V'} (hℓ : ℓ ∈ C.subst σ) (hℓc : ℓᶜ ∈ C.subst σ) : TautUnder σ C := by
  obtain ⟨l, hl, hlℓ⟩ := mem_subst.mp hℓ
  obtain ⟨l', hl', hl'ℓ⟩ := mem_subst.mp hℓc
  exact ⟨l, hl, l', hl', ℓ, hlℓ, hl'ℓ⟩

/-- Clauses `D₁ ⊆ E₁ ∪ {ℓ}` and `D₂ ⊆ E₂ ∪ {ℓᶜ}` containing `ℓ` and `ℓᶜ` respectively resolve,
in one order or the other, to a subclause of `E₁ ∪ E₂`. -/
theorem exists_isResolvent_subset {E₁ E₂ D₁ D₂ : Clause V'} {ℓ : Literal V'}
    (h₁ : D₁ ⊆ E₁ ∪ {ℓ}) (h₂ : D₂ ⊆ E₂ ∪ {ℓᶜ}) (hℓ₁ : ℓ ∈ D₁) (hℓ₂ : ℓᶜ ∈ D₂) :
    ∃ D ⊆ E₁ ∪ E₂, IsResolvent D D₁ D₂ ∨ IsResolvent D D₂ D₁ := by
  have key : ∀ {D E : Clause V'} {m a : Literal V'}, D ⊆ E ∪ {a} → m ∈ D → m ≠ a → m ∈ E :=
    fun hDE hm hne => (Finset.mem_union.mp (hDE hm)).resolve_right
      fun h => hne (Finset.mem_singleton.mp h)
  rcases Literal.eq_pos_or_eq_neg ℓ with hℓ | hℓ
  · obtain ⟨y, rfl⟩ : ∃ y, ℓ = Literal.pos y := ⟨_, hℓ⟩
    refine ⟨resolvent D₁ D₂ y, ?_, Or.inl ⟨y, hℓ₁, by simpa using hℓ₂, rfl⟩⟩
    intro m hm
    rcases mem_resolvent.mp hm with ⟨hne, hmD⟩ | ⟨hne, hmD⟩
    · exact Finset.mem_union_left _ (key h₁ hmD hne)
    · exact Finset.mem_union_right _ (key h₂ hmD (by simpa using hne))
  · obtain ⟨y, rfl⟩ : ∃ y, ℓ = Literal.neg y := ⟨_, hℓ⟩
    refine ⟨resolvent D₂ D₁ y, ?_, Or.inr ⟨y, by simpa using hℓ₂, hℓ₁, rfl⟩⟩
    intro m hm
    rcases mem_resolvent.mp hm with ⟨hne, hmD⟩ | ⟨hne, hmD⟩
    · exact Finset.mem_union_right _ (key h₂ hmD (by simpa using hne))
    · exact Finset.mem_union_left _ (key h₁ hmD hne)

section

variable [DecidableEq V]

theorem subst_union (σ : Subst V V') (C D : Clause V) :
    (C ∪ D).subst σ = C.subst σ ∪ D.subst σ := by
  ext m
  simp [or_and_right, exists_or]

/-- The image of `C` is contained in the image of `C ∖ {p}` together with the image of `p`. -/
theorem subst_subset_subst_erase_union (σ : Subst V V') (C : Clause V) (p : Literal V) :
    C.subst σ ⊆ subst σ (C.erase p) ∪ (p.subst σ).toClause := by
  intro m hm
  obtain ⟨l, hl, hlm⟩ := mem_subst.mp hm
  by_cases hlp : l = p
  · exact Finset.mem_union_right _ (LitConst.mem_toClause.mpr (hlp ▸ hlm))
  · exact Finset.mem_union_left _ (mem_subst.mpr ⟨l, Finset.mem_erase.mpr ⟨hlp, hl⟩, hlm⟩)

omit [DecidableEq V'] in
/-- If `C` survives `σ`, `P ∖ {p} ⊆ C`, and `p` maps to `0`, then `P` survives `σ`. -/
theorem survivesUnder_of_erase_subset {σ : Subst V V'} {C P : Clause V} {p : Literal V}
    (hC : SurvivesUnder σ C) (hsub : P.erase p ⊆ C) (hp : p.subst σ = .const false) :
    SurvivesUnder σ P := by
  have hne : ∀ {l : Literal V}, l ∈ P → (l.subst σ).IsLit ∨ l.subst σ = .const true →
      l ∈ C := by
    intro l hl h
    refine hsub (Finset.mem_erase.mpr ⟨?_, hl⟩)
    rintro rfl
    rw [hp] at h
    simp at h
  constructor
  · rintro ⟨l, hl, hlσ⟩
    exact hC.1 ⟨l, hne hl (Or.inr hlσ), hlσ⟩
  · rintro ⟨l, hl, l', hl', m, hm, hm'⟩
    exact hC.2 ⟨l, hne hl (Or.inl (by simp [hm])), l', hne hl' (Or.inl (by simp [hm'])), m, hm,
      hm'⟩

omit [DecidableEq V'] in
/-- If `C` survives `σ`, `P ∖ {p} ⊆ C`, and `p` maps to a literal, then `P` is not satisfied
by `σ`. -/
theorem not_satUnder_of_erase_subset {σ : Subst V V'} {C P : Clause V} {p : Literal V}
    {ℓ : Literal V'} (hC : SurvivesUnder σ C) (hsub : P.erase p ⊆ C) (hp : p.subst σ = .lit ℓ) :
    ¬ SatUnder σ P := by
  rintro ⟨l, hl, hlσ⟩
  refine hC.1 ⟨l, hsub (Finset.mem_erase.mpr ⟨?_, hl⟩), hlσ⟩
  rintro rfl
  rw [hp] at hlσ
  simp at hlσ

/-- If `C` survives `σ`, `P ∖ {p} ⊆ C`, `p` maps to the literal `ℓ`, and `P` is tautological
under `σ`, then `ℓᶜ ∈ C^σ`. -/
theorem compl_mem_subst_of_tautUnder {σ : Subst V V'} {C P : Clause V} {p : Literal V}
    {ℓ : Literal V'} (hC : SurvivesUnder σ C) (hsub : P.erase p ⊆ C) (hp : p.subst σ = .lit ℓ)
    (ht : TautUnder σ P) : ℓᶜ ∈ C.subst σ := by
  obtain ⟨l, hl, l', hl', m, hm, hm'⟩ := ht
  by_cases hlp : l = p
  · have hmℓ : m = ℓ := by
      rw [hlp, hp] at hm
      exact (LitConst.lit.inj hm).symm
    have hl'p : l' ≠ p := by
      intro h
      rw [h, hp, hmℓ] at hm'
      exact Literal.compl_ne ℓ (LitConst.lit.inj hm').symm
    rw [hmℓ] at hm'
    exact mem_subst.mpr ⟨l', hsub (Finset.mem_erase.mpr ⟨hl'p, hl'⟩), hm'⟩
  · by_cases hl'p : l' = p
    · have hmℓ : m = ℓᶜ := by
        rw [hl'p, hp] at hm'
        rw [LitConst.lit.inj hm', Literal.compl_compl]
      rw [hmℓ] at hm
      exact mem_subst.mpr ⟨l, hsub (Finset.mem_erase.mpr ⟨hlp, hl⟩), hm⟩
    · exact (hC.2 ⟨l, hsub (Finset.mem_erase.mpr ⟨hlp, hl⟩), l',
        hsub (Finset.mem_erase.mpr ⟨hl'p, hl'⟩), m, hm, hm'⟩).elim

/-- The local step of the simulation. Let `C` be a resolvent of two available clauses whose
surviving members have simulated subclauses in `S'`. If `C` survives `σ`, then some subclause
of `C^σ ∪ W` is in `S'` or is a resolvent of two clauses of `S'`. -/
theorem exists_step (σ : Subst V V') (W : Clause V') {S : Finset (Clause V)}
    {S' : Finset (Clause V')}
    (hS : ∀ C ∈ S, SurvivesUnder σ C → ∃ D ∈ S', D ⊆ C.subst σ ∪ W)
    {C : Clause V} (hC : SurvivesUnder σ C) (h : ∃ C₁ ∈ S, ∃ C₂ ∈ S, IsResolvent C C₁ C₂) :
    ∃ D ⊆ C.subst σ ∪ W, D ∈ S' ∨ ∃ D₁ ∈ S', ∃ D₂ ∈ S', IsResolvent D D₁ D₂ := by
  obtain ⟨C₁, h₁, C₂, h₂, x, -, -, rfl⟩ := h
  set T := (resolvent C₁ C₂ x).subst σ ∪ W
  have hsub₁ : C₁.erase (Literal.pos x) ⊆ resolvent C₁ C₂ x := Finset.subset_union_left
  have hsub₂ : C₂.erase (Literal.neg x) ⊆ resolvent C₁ C₂ x := Finset.subset_union_right
  have hE₁ : subst σ (C₁.erase (Literal.pos x)) ⊆ T :=
    (subst_mono hsub₁).trans Finset.subset_union_left
  have hE₂ : subst σ (C₂.erase (Literal.neg x)) ⊆ T :=
    (subst_mono hsub₂).trans Finset.subset_union_left
  have hW : W ⊆ T := Finset.subset_union_right
  have hp₁ : (Literal.pos x).subst σ = σ x := Literal.subst_pos σ x
  have hp₂ : (Literal.neg x).subst σ = (σ x)ᶜ := Literal.subst_neg σ x
  have hC₁ := subst_subset_subst_erase_union σ C₁ (Literal.pos x)
  have hC₂ := subst_subset_subst_erase_union σ C₂ (Literal.neg x)
  rw [hp₁] at hC₁
  rw [hp₂] at hC₂
  cases hσx : σ x with
  | const b =>
    rw [hσx] at hp₁ hp₂ hC₁ hC₂
    cases b with
    | false =>
      obtain ⟨D₁, hD₁, hD₁sub⟩ := hS C₁ h₁ (survivesUnder_of_erase_subset hC hsub₁ hp₁)
      rw [LitConst.toClause_const, Finset.union_empty] at hC₁
      exact ⟨D₁, hD₁sub.trans (Finset.union_subset (hC₁.trans hE₁) hW), Or.inl hD₁⟩
    | true =>
      rw [LitConst.compl_const, Bool.not_true] at hp₂ hC₂
      obtain ⟨D₂, hD₂, hD₂sub⟩ := hS C₂ h₂ (survivesUnder_of_erase_subset hC hsub₂ hp₂)
      rw [LitConst.toClause_const, Finset.union_empty] at hC₂
      exact ⟨D₂, hD₂sub.trans (Finset.union_subset (hC₂.trans hE₂) hW), Or.inl hD₂⟩
  | lit ℓ =>
    rw [hσx] at hp₁ hp₂ hC₁ hC₂
    rw [LitConst.compl_lit] at hp₂ hC₂
    rw [LitConst.toClause_lit] at hC₁ hC₂
    have hns₁ := not_satUnder_of_erase_subset hC hsub₁ hp₁
    have hns₂ := not_satUnder_of_erase_subset hC hsub₂ hp₂
    have hD₁T : ∀ D₁ ⊆ C₁.subst σ ∪ W, D₁ ⊆ T ∪ {ℓ} := fun D₁ hD₁ =>
      hD₁.trans (Finset.union_subset (hC₁.trans (Finset.union_subset_union_left hE₁))
        (hW.trans Finset.subset_union_left))
    have hD₂T : ∀ D₂ ⊆ C₂.subst σ ∪ W, D₂ ⊆ T ∪ {ℓᶜ} := fun D₂ hD₂ =>
      hD₂.trans (Finset.union_subset (hC₂.trans (Finset.union_subset_union_left hE₂))
        (hW.trans Finset.subset_union_left))
    by_cases ht₁ : TautUnder σ C₁
    · have hℓc := compl_mem_subst_of_tautUnder hC hsub₁ hp₁ ht₁
      by_cases ht₂ : TautUnder σ C₂
      · have hℓ := compl_mem_subst_of_tautUnder hC hsub₂ hp₂ ht₂
        rw [Literal.compl_compl] at hℓ
        exact absurd (tautUnder_of_mem_subst_of_compl_mem_subst hℓ hℓc) hC.2
      · obtain ⟨D₂, hD₂, hD₂sub⟩ := hS C₂ h₂ ⟨hns₂, ht₂⟩
        exact ⟨D₂, (hD₂T D₂ hD₂sub).trans (Finset.union_subset (Finset.Subset.refl _)
          (Finset.singleton_subset_iff.mpr (Finset.mem_union_left _ hℓc))), Or.inl hD₂⟩
    · by_cases ht₂ : TautUnder σ C₂
      · have hℓ := compl_mem_subst_of_tautUnder hC hsub₂ hp₂ ht₂
        rw [Literal.compl_compl] at hℓ
        obtain ⟨D₁, hD₁, hD₁sub⟩ := hS C₁ h₁ ⟨hns₁, ht₁⟩
        exact ⟨D₁, (hD₁T D₁ hD₁sub).trans (Finset.union_subset (Finset.Subset.refl _)
          (Finset.singleton_subset_iff.mpr (Finset.mem_union_left _ hℓ))), Or.inl hD₁⟩
      · obtain ⟨D₁, hD₁, hD₁sub⟩ := hS C₁ h₁ ⟨hns₁, ht₁⟩
        obtain ⟨D₂, hD₂, hD₂sub⟩ := hS C₂ h₂ ⟨hns₂, ht₂⟩
        have hD₁' := hD₁T D₁ hD₁sub
        have hD₂' := hD₂T D₂ hD₂sub
        by_cases hℓ₁ : ℓ ∈ D₁
        · by_cases hℓ₂ : ℓᶜ ∈ D₂
          · obtain ⟨D, hDsub, hres⟩ := exists_isResolvent_subset hD₁' hD₂' hℓ₁ hℓ₂
            rw [Finset.union_self] at hDsub
            refine ⟨D, hDsub, Or.inr ?_⟩
            rcases hres with hres | hres
            · exact ⟨D₁, hD₁, D₂, hD₂, hres⟩
            · exact ⟨D₂, hD₂, D₁, hD₁, hres⟩
          · exact ⟨D₂, subset_of_subset_union_singleton hD₂' hℓ₂, Or.inl hD₂⟩
        · exact ⟨D₁, subset_of_subset_union_singleton hD₁' hℓ₁, Or.inl hD₁⟩

end

end Clause

section Simulation

variable [DecidableEq V] [DecidableEq V']

/-- The simulation of a derivation under a substitution. Let `π` be a derivation from `Φ` with
the clauses of `S` available, and let `Ψ` contain a subclause of `C^σ ∪ W` for each surviving
initial clause `C` of `π`. If every surviving clause of `S` has a subclause of `C^σ ∪ W` in `S'`,
then `Ψ` has a derivation `π'` with the clauses of `S'` available, of at most the length of `π`,
that together with `S'` contains a subclause of `C^σ ∪ W` for every surviving clause `C` of `π`.

Paper: proof of Lemma [lem:substitution]. -/
theorem IsDerivation.exists_simulation (σ : Subst V V') (W : Clause V') {Φ : CNF V}
    {Ψ : CNF V'} {π : List (Clause V)} {S : Finset (Clause V)} {S' : Finset (Clause V')}
    (h : IsDerivation Φ S π)
    (hΦ : ∀ C ∈ π, C ∈ Φ → Clause.SurvivesUnder σ C → ∃ D ∈ Ψ, D ⊆ C.subst σ ∪ W)
    (hS : ∀ C ∈ S, Clause.SurvivesUnder σ C → ∃ D ∈ S', D ⊆ C.subst σ ∪ W) :
    ∃ π' : List (Clause V'), IsDerivation Ψ S' π' ∧ π'.length ≤ π.length ∧
      ∀ C ∈ π, Clause.SurvivesUnder σ C → ∃ D, (D ∈ S' ∨ D ∈ π') ∧ D ⊆ C.subst σ ∪ W := by
  induction π generalizing S S' with
  | nil => exact ⟨[], trivial, le_rfl, by simp⟩
  | cons C π ih =>
    obtain ⟨hC, hπ⟩ := h
    have hΦ' : ∀ C' ∈ π, C' ∈ Φ → Clause.SurvivesUnder σ C' → ∃ D ∈ Ψ, D ⊆ C'.subst σ ∪ W :=
      fun C' hC' => hΦ C' (List.mem_cons_of_mem _ hC')
    by_cases hsurv : Clause.SurvivesUnder σ C
    · have hD : ∃ D ⊆ C.subst σ ∪ W,
          D ∈ S' ∨ D ∈ Ψ ∨ ∃ D₁ ∈ S', ∃ D₂ ∈ S', Clause.IsResolvent D D₁ D₂ := by
        rcases hC with hC | hC
        · obtain ⟨D, hD, hDsub⟩ := hΦ C List.mem_cons_self hC hsurv
          exact ⟨D, hDsub, Or.inr (Or.inl hD)⟩
        · obtain ⟨D, hDsub, hD⟩ := Clause.exists_step σ W hS hsurv hC
          exact ⟨D, hDsub, hD.imp_right Or.inr⟩
      obtain ⟨D, hDsub, hD⟩ := hD
      rcases hD with hD | hD
      · obtain ⟨π', hπ', hlen, hcov⟩ := ih hπ hΦ' (S' := S') (by
          intro C' hC' hs'
          rcases Finset.mem_insert.mp hC' with rfl | hC'
          · exact ⟨D, hD, hDsub⟩
          · exact hS C' hC' hs')
        refine ⟨π', hπ', hlen.trans (Nat.le_succ _), ?_⟩
        intro C' hC' hs'
        rcases List.mem_cons.mp hC' with rfl | hC'
        · exact ⟨D, Or.inl hD, hDsub⟩
        · exact hcov C' hC' hs'
      · obtain ⟨π', hπ', hlen, hcov⟩ := ih hπ hΦ' (S' := insert D S') (by
          intro C' hC' hs'
          rcases Finset.mem_insert.mp hC' with rfl | hC'
          · exact ⟨D, Finset.mem_insert_self _ _, hDsub⟩
          · obtain ⟨D', hD', hD'sub⟩ := hS C' hC' hs'
            exact ⟨D', Finset.mem_insert_of_mem hD', hD'sub⟩)
        refine ⟨D :: π', ⟨hD, hπ'⟩, Nat.succ_le_succ hlen, ?_⟩
        intro C' hC' hs'
        rcases List.mem_cons.mp hC' with rfl | hC'
        · exact ⟨D, Or.inr List.mem_cons_self, hDsub⟩
        · obtain ⟨D', hD', hD'sub⟩ := hcov C' hC' hs'
          refine ⟨D', ?_, hD'sub⟩
          rcases hD' with hD' | hD'
          · rcases Finset.mem_insert.mp hD' with rfl | hD'
            · exact Or.inr List.mem_cons_self
            · exact Or.inl hD'
          · exact Or.inr (List.mem_cons_of_mem _ hD')
    · obtain ⟨π', hπ', hlen, hcov⟩ := ih hπ hΦ' (S' := S') (by
        intro C' hC' hs'
        rcases Finset.mem_insert.mp hC' with rfl | hC'
        · exact absurd hs' hsurv
        · exact hS C' hC' hs')
      refine ⟨π', hπ', hlen.trans (Nat.le_succ _), ?_⟩
      intro C' hC' hs'
      rcases List.mem_cons.mp hC' with rfl | hC'
      · exact absurd hs' hsurv
      · exact hcov C' hC' hs'

/-- A derivation of a clause `C` surviving `σ` simulates, over any CNF `Ψ` containing a subclause
of `C'^σ ∪ W` for each surviving initial clause `C'` of the derivation, as a derivation from `Ψ`
of a subclause of `C^σ ∪ W` of at most the same size. -/
theorem Derivation.exists_simulation {Φ : CNF V} {C : Clause V} (π : Derivation Φ C)
    (σ : Subst V V') (W : Clause V') {Ψ : CNF V'}
    (hΦ : ∀ C' ∈ π.lines, C' ∈ Φ → Clause.SurvivesUnder σ C' → ∃ D ∈ Ψ, D ⊆ C'.subst σ ∪ W)
    (hC : Clause.SurvivesUnder σ C) :
    ∃ D ⊆ C.subst σ ∪ W, ∃ π' : Derivation Ψ D, π'.size ≤ π.size := by
  obtain ⟨π', hπ', hlen, hcov⟩ := π.isDerivation.exists_simulation σ W hΦ (by simp)
  obtain ⟨D, hD, hDsub⟩ := hcov C π.mem_lines hC
  rcases hD with hD | hD
  · exact absurd hD (Finset.notMem_empty _)
  · obtain ⟨π'', hπ''⟩ := Derivation.exists_of_mem hπ' hD
    exact ⟨D, hDsub, π'', hπ''.trans hlen⟩

/-- **Substitution lemma.** A refutation of `Φ` yields a refutation of `Φ^σ` of at most the same
size.

Paper: Lemma [lem:substitution]. -/
theorem Refutation.subst {Φ : CNF V} (π : Refutation Φ) (σ : Subst V V') :
    ∃ π' : Refutation (Φ.subst σ), π'.size ≤ π.size := by
  obtain ⟨D, hD, π', hπ'⟩ := π.exists_simulation σ ∅ (Ψ := Φ.subst σ)
    (fun C _ hC hs => ⟨C.subst σ, CNF.mem_subst.mpr ⟨C, hC, hs, rfl⟩, Finset.subset_union_left⟩)
    (Clause.survivesUnder_empty σ)
  rw [Clause.subst_empty, Finset.empty_union, Finset.subset_empty] at hD
  subst hD
  exact ⟨π', hπ'⟩

end Simulation

section

variable [DecidableEq V]

/-- **Restriction lemma.** A refutation of `Φ` yields a refutation of `Φ↾ρ` of at most the same
size. It is the substitution lemma for `ρ` read as a substitution, together with
`Φ^ρ ⊆ Φ↾ρ`.

Paper: the special case of Lemma [lem:substitution] for restrictions. -/
theorem Refutation.restrict {Φ : CNF V} (π : Refutation Φ) (ρ : Restriction V) :
    ∃ π' : Refutation (Φ.restrict ρ), π'.size ≤ π.size := by
  obtain ⟨π', hπ'⟩ := π.subst ρ.toSubst
  exact ⟨π'.mono (CNF.subst_toSubst_subset ρ Φ), hπ'⟩

/-- **Subclauses of initial clauses suffice.** If `Φ` contains a subclause of each initial
clause of a refutation `π` of `Ψ`, then `Φ` has a refutation of at most the size of `π`.

Paper: used implicitly in the proof of Lemma [lem:reduction], where subclauses of the initial
clauses are derived. -/
theorem Refutation.of_subclauses {Ψ Φ : CNF V} (π : Refutation Ψ)
    (h : ∀ C ∈ π.lines, C ∈ Ψ → ∃ D ∈ Φ, D ⊆ C) : ∃ π' : Refutation Φ, π'.size ≤ π.size := by
  obtain ⟨D, hD, π', hπ'⟩ := π.exists_simulation (Subst.id V) ∅ (Ψ := Φ)
    (fun C hC hCΨ _ => by simpa using h C hC hCΨ) (Clause.survivesUnder_empty _)
  rw [Clause.subst_empty, Finset.empty_union, Finset.subset_empty] at hD
  subst hD
  exact ⟨π', hπ'⟩

end

/-! ### Extensions and pullbacks of restrictions -/

/-- `α` extends `ρ`: it agrees with `ρ` on the variables `ρ` assigns. -/
def Restriction.Extends (ρ : Restriction V) (α : V → Bool) : Prop := ∀ v b, ρ v = some b → α v = b

namespace LitConst

/-- The value of a literal or constant under a restriction, when determined: a constant, or
the value of a literal whose variable is assigned. -/
def restrictEval (ρ : Restriction V) : LitConst V → Option Bool
  | const b => some b
  | lit l => (ρ l.var).map fun b => b == l.sign

@[simp] theorem restrictEval_const (ρ : Restriction V) (b : Bool) :
    restrictEval ρ (const b) = some b := rfl

@[simp] theorem restrictEval_lit (ρ : Restriction V) (l : Literal V) :
    restrictEval ρ (lit l) = (ρ l.var).map fun b => b == l.sign := rfl

end LitConst

/-- The restriction induced on `V` by a substitution `σ : Subst V V'` and a restriction of
`V'`: a variable mapped to a constant is set to it, and a variable mapped to a literal is set
to the literal's value when the literal's variable is assigned. -/
def Restriction.comap (σ : Subst V V') (ρ : Restriction V') : Restriction V := fun v =>
  (σ v).restrictEval ρ

@[simp] theorem Restriction.comap_apply (σ : Subst V V') (ρ : Restriction V') (v : V) :
    ρ.comap σ v = (σ v).restrictEval ρ := rfl

/-- An assignment extending `ρ` pulls back along `σ` to an assignment extending `ρ.comap σ`. -/
theorem Restriction.Extends.comap {σ : Subst V V'} {ρ : Restriction V'} {α : V' → Bool}
    (h : ρ.Extends α) : (ρ.comap σ).Extends (σ.pullback α) := by
  intro v b hb
  rw [Restriction.comap_apply] at hb
  rw [Subst.pullback_apply]
  cases hσ : σ v with
  | const b' =>
    rw [hσ] at hb
    simp only [LitConst.restrictEval_const, Option.some.injEq] at hb
    rw [hb]
    rfl
  | lit l =>
    rw [hσ] at hb
    simp only [LitConst.restrictEval_lit, Option.map_eq_some_iff] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    rcases l with ⟨w, s⟩
    have hw := h w a ha
    cases a <;> cases s <;> simp [Literal.Sat, hw]

/-- A literal of a surviving clause that survives the restriction is unassigned by it. -/
theorem Clause.eq_none_of_mem_restrict {ρ : Restriction V} {C : Clause V} (hC : C.Survives ρ)
    {l : Literal V} (hl : l ∈ C.restrict ρ) : ρ l.var = none := by
  rw [Clause.mem_restrict] at hl
  exact Literal.eq_none_of_not_satBy_of_not_falsifiedBy (fun hs => hC ⟨l, hl.1, hs⟩) hl.2

/-- An assignment extending `ρ` satisfies a restricted clause iff it satisfies the clause. -/
theorem Clause.sat_restrict_iff_of_extends {ρ : Restriction V} {α : V → Bool} (hα : ρ.Extends α)
    (C : Clause V) : Sat α (C.restrict ρ) ↔ Sat α C := by
  constructor
  · exact fun h => h.mono (C.restrict_subset ρ)
  · rintro ⟨l, hl, hs⟩
    refine ⟨l, Clause.mem_restrict.mpr ⟨hl, fun hf => ?_⟩, hs⟩
    rw [Literal.FalsifiedBy] at hf
    rw [Literal.Sat, hα _ _ hf] at hs
    exact Bool.not_ne_self _ hs

/-- A clause satisfied by `ρ` is satisfied by every assignment extending `ρ`. -/
theorem Clause.SatBy.sat {ρ : Restriction V} {C : Clause V} (h : C.SatBy ρ) {α : V → Bool}
    (hα : ρ.Extends α) : Sat α C := by
  obtain ⟨l, hl, hs⟩ := h
  exact ⟨l, hl, hα _ _ hs⟩

/-- An assignment extending `ρ` satisfies `Φ↾ρ` iff it satisfies `Φ`. -/
theorem CNF.sat_restrict_iff_of_extends [DecidableEq V] {ρ : Restriction V} {α : V → Bool}
    (hα : ρ.Extends α) (Φ : CNF V) : Sat α (Φ.restrict ρ) ↔ Sat α Φ := by
  constructor
  · intro h C hC
    by_cases hs : C.Survives ρ
    · exact (Clause.sat_restrict_iff_of_extends hα C).mp
        (h _ (CNF.mem_restrict.mpr ⟨C, hC, hs, rfl⟩))
    · exact Clause.SatBy.sat (not_not.mp hs) hα
  · intro h D hD
    obtain ⟨C, hC, -, rfl⟩ := CNF.mem_restrict.mp hD
    exact (Clause.sat_restrict_iff_of_extends hα C).mpr (h C hC)

-- Sanity check: an assignment extending `ρ` that satisfies `Φ` satisfies `Φ↾ρ`.
example [DecidableEq V] {ρ : Restriction V} {α : V → Bool} (hα : ρ.Extends α) {Φ : CNF V}
    (h : CNF.Sat α Φ) : CNF.Sat α (Φ.restrict ρ) :=
  (CNF.sat_restrict_iff_of_extends hα Φ).mpr h

/-! ### Single-variable restrictions and lifting -/

namespace Restriction

variable [DecidableEq V]

/-- The restriction assigning `b` to `x` and nothing to the other variables. -/
def single (x : V) (b : Bool) : Restriction V := fun v => if v = x then some b else none

@[simp] theorem single_self (x : V) (b : Bool) : single x b x = some b := by
  simp [single]

theorem single_of_ne {x v : V} (b : Bool) (h : v ≠ x) : single x b v = none := by
  simp [single, h]

/-- The only literal falsified by `single x b` is `⟨x, !b⟩`. -/
theorem falsifiedBy_single_iff {x : V} {b : Bool} {l : Literal V} :
    l.FalsifiedBy (single x b) ↔ l = ⟨x, !b⟩ := by
  rcases l with ⟨v, s⟩
  by_cases hv : v = x
  · subst hv
    cases b <;> cases s <;> simp [Literal.FalsifiedBy]
  · simp [Literal.FalsifiedBy, single_of_ne _ hv, hv]

omit [DecidableEq V] in
/-- The pullback along `ρ` of an assignment takes the values fixed by `ρ`. -/
theorem pullback_toSubst_of_eq_some {ρ : Restriction V} {v : V} {b : Bool} (h : ρ v = some b)
    (α : V → Bool) : ρ.toSubst.pullback α v = b := by
  simp [toSubst_of_eq_some h]

end Restriction

namespace CNF

variable [DecidableEq V]

/-- The variables of `Φ↾ρ` are variables of `Φ` left unassigned by `ρ`. -/
theorem vars_restrict_subset (ρ : Restriction V) (Φ : CNF V) :
    (Φ.restrict ρ).vars ⊆ Φ.vars.filter fun v => ρ v = none := by
  intro v hv
  obtain ⟨D, hD, l, hl, rfl⟩ := mem_vars.mp hv
  obtain ⟨C, hC, hsurv, rfl⟩ := mem_restrict.mp hD
  obtain ⟨hlC, hlf⟩ := Clause.mem_restrict.mp hl
  refine Finset.mem_filter.mpr ⟨mem_vars.mpr ⟨C, hC, l, hlC, rfl⟩, ?_⟩
  exact Literal.eq_none_of_not_satBy_of_not_falsifiedBy (fun hs => hsurv ⟨l, hlC, hs⟩) hlf

/-- An assignment satisfying `Φ↾ρ` satisfies `Φ` once overridden by `ρ`. -/
theorem sat_pullback_of_sat_restrict {ρ : Restriction V} {Φ : CNF V} {α : V → Bool}
    (hα : Sat α (Φ.restrict ρ)) : Sat (ρ.toSubst.pullback α) Φ :=
  (sat_subst_iff ρ.toSubst Φ α).mp (hα.subset (subst_toSubst_subset ρ Φ))

/-- Restriction preserves unsatisfiability. -/
theorem Unsatisfiable.restrict {Φ : CNF V} (h : Φ.Unsatisfiable) (ρ : Restriction V) :
    (Φ.restrict ρ).Unsatisfiable :=
  (h.subst ρ.toSubst).mono (subst_toSubst_subset ρ Φ)

end CNF

/-- **Lifting.** A refutation of `Φ↾ρ` lifts to a derivation from `Φ` of a subclause of any
clause `W` containing the literals of `Φ` falsified by `ρ`, of at most the same size. This is
the simulation for the identity substitution with `W` added. -/
theorem Refutation.exists_lift [DecidableEq V] {Φ : CNF V} {ρ : Restriction V}
    (π : Refutation (Φ.restrict ρ)) (W : Clause V)
    (hW : ∀ C ∈ Φ, ∀ l ∈ C, l.FalsifiedBy ρ → l ∈ W) :
    ∃ D ⊆ W, ∃ π' : Derivation Φ D, π'.size ≤ π.size := by
  have hΦ : ∀ E ∈ π.lines, E ∈ Φ.restrict ρ → Clause.SurvivesUnder (Subst.id V) E →
      ∃ D ∈ Φ, D ⊆ E.subst (Subst.id V) ∪ W := by
    intro E _ hE _
    obtain ⟨C, hC, -, rfl⟩ := CNF.mem_restrict.mp hE
    refine ⟨C, hC, ?_⟩
    rw [Clause.subst_id]
    intro l hl
    by_cases hf : l.FalsifiedBy ρ
    · exact Finset.mem_union_right _ (hW C hC l hl hf)
    · exact Finset.mem_union_left _ (Clause.mem_restrict.mpr ⟨hl, hf⟩)
  obtain ⟨D, hD, π', hπ'⟩ :=
    π.exists_simulation (Subst.id V) W hΦ (Clause.survivesUnder_empty _)
  rw [Clause.subst_empty, Finset.empty_union] at hD
  exact ⟨D, hD, π', hπ'⟩

end AssocLB
