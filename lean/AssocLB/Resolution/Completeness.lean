/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/
import AssocLB.Resolution.Substitution

/-!
# Completeness of resolution

Paper: Section 2 (Preliminaries), paragraph "Resolution": resolution is complete, in that a CNF
is unsatisfiable if and only if it has a refutation, and if `Φ` implies a nontautological clause
`C`, then some subclause of `C` has a resolution derivation from `Φ`.

## Main results

* `CNF.Unsatisfiable.nonempty_refutation`: refutational completeness. The proof is by induction
  on a finite set of variables containing those of the CNF: restrict a variable `x` to both
  values, refute both restrictions by induction, lift the two refutations
  (`Refutation.exists_lift`) to derivations from `Φ` of subclauses of `{x}` and `{¬x}`, and
  resolve them unless one of them is already empty.
* `CNF.unsatisfiable_iff_nonempty_refutation`: soundness and completeness together.
* `CNF.Implies.exists_derivation`: implicational completeness. For a nontautological clause `C`
  implied by `Φ`, the restriction `Clause.falsifying C` falsifying every literal of `C` makes
  `Φ` unsatisfiable, and the refutation of `Φ↾ρ` lifts to a derivation from `Φ` of a subclause
  of `C`.

## Design notes

* Existence of a refutation is stated as `Nonempty (Refutation Φ)`, since `Refutation Φ` is a
  type. No size bound is claimed; the variable-elimination proof gives an exponential one.
-/

namespace AssocLB

variable {V : Type*} [DecidableEq V]

/-- The restriction falsifying every literal of a nontautological clause `C`: `x ↦ 0` if the
literal `x` is in `C`, `x ↦ 1` if `¬x` is in `C`, and unassigned otherwise. -/
def Clause.falsifying (C : Clause V) : Restriction V := fun v =>
  if Literal.pos v ∈ C then some false else if Literal.neg v ∈ C then some true else none

/-- For a nontautological clause `C`, the literals falsified by `C.falsifying` are exactly the
literals of `C`. -/
theorem Clause.falsifiedBy_falsifying_iff {C : Clause V} (hC : ¬ C.IsTautology)
    {l : Literal V} : l.FalsifiedBy C.falsifying ↔ l ∈ C := by
  rcases l with ⟨v, s⟩
  by_cases hp : Literal.pos v ∈ C <;> by_cases hn : Literal.neg v ∈ C
  · exact (hC ⟨Literal.pos v, hp, by simpa using hn⟩).elim
  · cases s
    · change _ ↔ Literal.neg v ∈ C
      simp [Literal.FalsifiedBy, falsifying, hp, hn]
    · change _ ↔ Literal.pos v ∈ C
      simp [Literal.FalsifiedBy, falsifying, hp]
  · cases s
    · change _ ↔ Literal.neg v ∈ C
      simp [Literal.FalsifiedBy, falsifying, hp, hn]
    · change _ ↔ Literal.pos v ∈ C
      simp [Literal.FalsifiedBy, falsifying, hp, hn]
  · cases s
    · change _ ↔ Literal.neg v ∈ C
      simp [Literal.FalsifiedBy, falsifying, hp, hn]
    · change _ ↔ Literal.pos v ∈ C
      simp [Literal.FalsifiedBy, falsifying, hp, hn]

/-- Refutational completeness, by induction on a finite set of variables containing those of
the CNF. -/
theorem CNF.Unsatisfiable.nonempty_refutation_aux (X : Finset V) :
    ∀ Φ : CNF V, Φ.vars ⊆ X → Φ.Unsatisfiable → Nonempty (Refutation Φ) := by
  induction X using Finset.induction_on with
  | empty =>
    intro Φ hX h
    have hmem : (∅ : Clause V) ∈ Φ := by
      by_contra hne
      refine h ⟨fun _ => true, fun C hC => ?_⟩
      obtain ⟨l, hl⟩ := Finset.nonempty_iff_ne_empty.mpr fun hC0 => hne (hC0 ▸ hC)
      exact absurd (hX (CNF.mem_vars.mpr ⟨C, hC, l, hl, rfl⟩)) (Finset.notMem_empty _)
    exact ⟨Derivation.single hmem⟩
  | insert x X _ ih =>
    intro Φ hX h
    have hsub : ∀ b, (Φ.restrict (Restriction.single x b)).vars ⊆ X := by
      intro b v hv
      obtain ⟨hvΦ, hv0⟩ := Finset.mem_filter.mp (CNF.vars_restrict_subset _ Φ hv)
      rcases Finset.mem_insert.mp (hX hvΦ) with rfl | hvX
      · simp at hv0
      · exact hvX
    obtain ⟨π₁⟩ := ih _ (hsub true) (h.restrict _)
    obtain ⟨π₀⟩ := ih _ (hsub false) (h.restrict _)
    obtain ⟨D₁, hD₁, π₁', -⟩ := π₁.exists_lift {Literal.neg x} (by
      intro C _ l _ hf
      rw [Restriction.falsifiedBy_single_iff] at hf
      simp [hf, Literal.neg])
    obtain ⟨D₀, hD₀, π₀', -⟩ := π₀.exists_lift {Literal.pos x} (by
      intro C _ l _ hf
      rw [Restriction.falsifiedBy_single_iff] at hf
      simp [hf, Literal.pos])
    rcases Finset.subset_singleton_iff.mp hD₁ with rfl | rfl
    · exact ⟨π₁'⟩
    · rcases Finset.subset_singleton_iff.mp hD₀ with rfl | rfl
      · exact ⟨π₀'⟩
      · refine ⟨(π₀'.resolve π₁' x (Finset.mem_singleton_self _)
          (Finset.mem_singleton_self _)).copy ?_⟩
        simp [Clause.resolvent]

/-- **Refutational completeness.** An unsatisfiable CNF has a resolution refutation.

Paper: Section 2, "Resolution". -/
theorem CNF.Unsatisfiable.nonempty_refutation {Φ : CNF V} (h : Φ.Unsatisfiable) :
    Nonempty (Refutation Φ) :=
  nonempty_refutation_aux Φ.vars Φ (Finset.Subset.refl _) h

/-- Resolution is sound and complete: a CNF is unsatisfiable if and only if it has a
refutation.

Paper: Section 2, "Resolution". -/
theorem CNF.unsatisfiable_iff_nonempty_refutation (Φ : CNF V) :
    Φ.Unsatisfiable ↔ Nonempty (Refutation Φ) :=
  ⟨CNF.Unsatisfiable.nonempty_refutation, fun ⟨π⟩ => π.unsatisfiable⟩

/-- **Implicational completeness.** If `Φ` implies a nontautological clause `C`, then some
subclause of `C` has a resolution derivation from `Φ`.

Paper: Section 2, "Resolution". -/
theorem CNF.Implies.exists_derivation {Φ : CNF V} {C : Clause V} (h : Φ.Implies C)
    (hC : ¬ C.IsTautology) : ∃ D ⊆ C, Nonempty (Derivation Φ D) := by
  have hunsat : (Φ.restrict C.falsifying).Unsatisfiable := by
    rintro ⟨α, hα⟩
    obtain ⟨l, hl, hs⟩ := h _ (CNF.sat_pullback_of_sat_restrict hα)
    have hf : C.falsifying l.var = some (!l.sign) := (Clause.falsifiedBy_falsifying_iff hC).mpr hl
    rw [Literal.Sat, Restriction.pullback_toSubst_of_eq_some hf] at hs
    simp at hs
  obtain ⟨π⟩ := hunsat.nonempty_refutation
  obtain ⟨D, hD, π', -⟩ :=
    π.exists_lift C fun _ _ l _ hf => (Clause.falsifiedBy_falsifying_iff hC).mp hf
  exact ⟨D, hD, ⟨π'⟩⟩

/-- Implicational completeness with a size bound: the derivation can be taken of size at most
`2 ^ (2 N)`, where `N` is the number of variables of `Φ`.

Paper: Section 2, "Resolution"; used in Lemma [lem:star-local-derivations]. -/
theorem CNF.Implies.exists_derivation_size_le {Φ : CNF V} {C : Clause V} (h : Φ.Implies C)
    (hC : ¬ C.IsTautology) :
    ∃ D ⊆ C, ∃ π : Derivation Φ D, π.size ≤ 2 ^ (2 * Φ.vars.card) := by
  obtain ⟨D, hD, ⟨π⟩⟩ := h.exists_derivation hC
  obtain ⟨π', hπ'⟩ := π.exists_size_le
  exact ⟨D, hD, π', hπ'⟩

end AssocLB
