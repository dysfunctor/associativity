/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/
import AssocLB.Resolution.Basic

/-!
# Resolution derivations

Paper: Section 2 (Preliminaries), paragraph "Resolution".

## Main definitions

* `Clause.resolvent C₁ C₂ x`: the resolvent `(C₁ ∖ {x}) ∪ (C₂ ∖ {¬x})` of `C₁` and `C₂` on the
  pivot `x`. `Clause.IsResolvent C C₁ C₂` says that `C` is the resolvent of `C₁` and `C₂` on
  some pivot `x` with `x ∈ C₁` and `¬x ∈ C₂`.
* `IsDerivation Φ S π`: every clause of the sequence `π` is an initial clause of `Φ` or a
  resolvent of two clauses that lie in `S` or occur earlier in `π`. A derivation in the paper's
  sense is the case `S = ∅`; the parameter `S` is the accumulator of the recursion, and it lets
  derivations be concatenated.
* `Derivation Φ C`: a sequence of clauses satisfying `IsDerivation Φ ∅` whose last clause is
  `C`; `Refutation Φ` is a derivation of the empty clause. `Derivation.size` is the number of
  clauses and `Derivation.width` the maximum width of a clause.

## Main results

* `Derivation.implies`: soundness, a derived clause is implied by the CNF.
* `Refutation.unsatisfiable`: a CNF with a refutation is unsatisfiable.
* `IsDerivation.mono`, `Derivation.mono`: monotonicity in the CNF; `IsDerivation.append_left`
  and `Derivation.exists_of_mem`: prefixes of derivations are derivations, so every clause of a
  derivation sequence has a derivation of at most the sequence's length.
* `IsDerivation.append`, `Derivation.resolve`: derivations concatenate, and the conclusions of
  two derivations can be resolved; `Derivation.single` derives an initial clause.

## Design notes

* Derivations are lists in the paper's order, and size counts clauses with multiplicity, as in
  the paper. The minimum refutation size `size_Res(Φ)` and the minimum refutation width
  `w(Φ ⊢ ⊥)` are not defined as numbers: lower bounds are stated for every refutation, which
  avoids `ℕ∞` and infima over refutations.
* The resolvent removes the pivot from both premises, so the paper's `A ∨ x` and `B ∨ ¬x` are
  read with `x ∉ A` and `¬x ∉ B`. Resolving premises that clash on further variables is allowed
  and yields a tautology.
* `AssocLB.Derivation` shadows Mathlib's `Derivation` (of algebras) inside this namespace.

The subclause observation (a refutation may start from subclauses of its initial clauses, used
implicitly in the proof of Lemma [lem:reduction]) is proved in
`AssocLB.Resolution.Substitution`, as a corollary of the simulation argument behind the
substitution lemma, and completeness in `AssocLB.Resolution.Completeness`.
-/

namespace AssocLB

variable {V : Type*}

namespace Clause

variable [DecidableEq V]

/-- The resolvent of `C₁` and `C₂` on the pivot variable `x`: `(C₁ ∖ {x}) ∪ (C₂ ∖ {¬x})`.

Paper: Section 2, "Resolution". -/
def resolvent (C₁ C₂ : Clause V) (x : V) : Clause V :=
  C₁.erase (Literal.pos x) ∪ C₂.erase (Literal.neg x)

/-- `Clause.IsResolvent C C₁ C₂`: `C` is the resolvent of `C₁` and `C₂` on some pivot `x`
occurring positively in `C₁` and negatively in `C₂`.

Paper: Section 2, "Resolution". -/
def IsResolvent (C C₁ C₂ : Clause V) : Prop :=
  ∃ x, Literal.pos x ∈ C₁ ∧ Literal.neg x ∈ C₂ ∧ C = resolvent C₁ C₂ x

theorem mem_resolvent {C₁ C₂ : Clause V} {x : V} {m : Literal V} :
    m ∈ resolvent C₁ C₂ x ↔ (m ≠ Literal.pos x ∧ m ∈ C₁) ∨ (m ≠ Literal.neg x ∧ m ∈ C₂) := by
  simp [resolvent]

/-- The variables of a resolvent are among those of its premises. -/
theorem vars_resolvent_subset (C₁ C₂ : Clause V) (x : V) :
    (resolvent C₁ C₂ x).vars ⊆ C₁.vars ∪ C₂.vars := by
  intro v hv
  obtain ⟨l, hl, rfl⟩ := mem_vars.mp hv
  rcases mem_resolvent.mp hl with ⟨-, hl⟩ | ⟨-, hl⟩
  · exact Finset.mem_union_left _ (mem_vars.mpr ⟨l, hl, rfl⟩)
  · exact Finset.mem_union_right _ (mem_vars.mpr ⟨l, hl, rfl⟩)

/-- Soundness of the resolution rule: an assignment satisfying both premises satisfies the
resolvent. -/
theorem Sat.resolvent {α : V → Bool} {C₁ C₂ : Clause V} (x : V) (h₁ : Sat α C₁)
    (h₂ : Sat α C₂) : Sat α (resolvent C₁ C₂ x) := by
  obtain ⟨l₁, hl₁, hs₁⟩ := h₁
  obtain ⟨l₂, hl₂, hs₂⟩ := h₂
  by_cases hx : α x = true
  · refine ⟨l₂, Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨?_, hl₂⟩), hs₂⟩
    rintro rfl
    exact Bool.false_ne_true (((Literal.sat_neg_iff α x).mp hs₂).symm.trans hx)
  · refine ⟨l₁, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨?_, hl₁⟩), hs₁⟩
    rintro rfl
    exact hx ((Literal.sat_pos_iff α x).mp hs₁)

/-- A resolvent of two clauses implied by `Φ` is implied by `Φ`. -/
theorem IsResolvent.implies {Φ : CNF V} {C C₁ C₂ : Clause V} (h : IsResolvent C C₁ C₂)
    (h₁ : Φ.Implies C₁) (h₂ : Φ.Implies C₂) : Φ.Implies C := by
  obtain ⟨x, -, -, rfl⟩ := h
  exact fun α hα => (h₁ α hα).resolvent x (h₂ α hα)

end Clause

section Derivation

variable [DecidableEq V]

/-- `IsDerivation Φ S π`: every clause of the sequence `π`, read left to right, is an initial
clause belonging to `Φ` or a resolvent of two clauses that lie in `S` or occur earlier in `π`.
A resolution derivation in the paper's sense is the case `S = ∅`; the set `S` accumulates the
earlier clauses along the recursion.

Paper: Section 2, "Resolution". -/
def IsDerivation (Φ : CNF V) : Finset (Clause V) → List (Clause V) → Prop
  | _, [] => True
  | S, C :: π =>
    (C ∈ Φ ∨ ∃ C₁ ∈ S, ∃ C₂ ∈ S, Clause.IsResolvent C C₁ C₂) ∧ IsDerivation Φ (insert C S) π

@[simp] theorem isDerivation_nil (Φ : CNF V) (S : Finset (Clause V)) : IsDerivation Φ S [] :=
  trivial

@[simp] theorem isDerivation_cons (Φ : CNF V) (S : Finset (Clause V)) (C : Clause V)
    (π : List (Clause V)) :
    IsDerivation Φ S (C :: π) ↔
      (C ∈ Φ ∨ ∃ C₁ ∈ S, ∃ C₂ ∈ S, Clause.IsResolvent C C₁ C₂) ∧
        IsDerivation Φ (insert C S) π :=
  Iff.rfl

/-- Soundness: if `Φ` implies every clause of `S`, then it implies every clause of a derivation
from `Φ` with the clauses of `S` available. -/
theorem IsDerivation.implies {Φ : CNF V} {S : Finset (Clause V)} {π : List (Clause V)}
    (h : IsDerivation Φ S π) (hS : ∀ D ∈ S, Φ.Implies D) : ∀ D ∈ π, Φ.Implies D := by
  induction π generalizing S with
  | nil => simp
  | cons C π ih =>
    obtain ⟨hC, hπ⟩ := h
    have hC' : Φ.Implies C := by
      rcases hC with hC | ⟨C₁, h₁, C₂, h₂, hres⟩
      · exact CNF.implies_of_mem hC
      · exact hres.implies (hS C₁ h₁) (hS C₂ h₂)
    have hS' : ∀ D ∈ insert C S, Φ.Implies D := by
      intro D hD
      rcases Finset.mem_insert.mp hD with rfl | hD
      · exact hC'
      · exact hS D hD
    intro D hD
    rcases List.mem_cons.mp hD with rfl | hD
    · exact hC'
    · exact ih hπ hS' D hD

/-- The variables of the clauses of a derivation are among those of `Φ` and of the available
clauses `S`. -/
theorem IsDerivation.vars_subset {Φ : CNF V} {S : Finset (Clause V)} {π : List (Clause V)}
    (h : IsDerivation Φ S π) {X : Finset V} (hΦ : Φ.vars ⊆ X) (hS : ∀ D ∈ S, D.vars ⊆ X) :
    ∀ D ∈ π, D.vars ⊆ X := by
  induction π generalizing S with
  | nil => simp
  | cons C π ih =>
    obtain ⟨hC, hπ⟩ := h
    have hC' : C.vars ⊆ X := by
      rcases hC with hC | ⟨C₁, h₁, C₂, h₂, x, -, -, rfl⟩
      · exact fun v hv => hΦ (CNF.mem_vars.mpr ⟨C, hC, Clause.mem_vars.mp hv⟩)
      · exact (Clause.vars_resolvent_subset C₁ C₂ x).trans
          (Finset.union_subset (hS C₁ h₁) (hS C₂ h₂))
    have hS' : ∀ D ∈ insert C S, D.vars ⊆ X := by
      intro D hD
      rcases Finset.mem_insert.mp hD with rfl | hD
      · exact hC'
      · exact hS D hD
    intro D hD
    rcases List.mem_cons.mp hD with rfl | hD
    · exact hC'
    · exact ih hπ hS' D hD

/-- Repeated clauses can be dropped: every derivation sequence has a subsequence without
repetitions and without clauses of `S` that is again a derivation and still contains every
clause of the original sequence outside `S`. -/
theorem IsDerivation.exists_nodup {Φ : CNF V} {S : Finset (Clause V)} {π : List (Clause V)}
    (h : IsDerivation Φ S π) :
    ∃ π' : List (Clause V), IsDerivation Φ S π' ∧ π'.Nodup ∧ (∀ D ∈ π', D ∉ S) ∧
      (∀ D ∈ π', D ∈ π) ∧ ∀ D ∈ π, D ∈ S ∨ D ∈ π' := by
  induction π generalizing S with
  | nil => exact ⟨[], trivial, List.nodup_nil, by simp, by simp, by simp⟩
  | cons C π ih =>
    obtain ⟨hC, hπ⟩ := h
    by_cases hCS : C ∈ S
    · rw [Finset.insert_eq_of_mem hCS] at hπ
      obtain ⟨π', h₁, h₂, h₃, h₄, h₅⟩ := ih hπ
      refine ⟨π', h₁, h₂, h₃, fun D hD => List.mem_cons_of_mem _ (h₄ D hD), fun D hD => ?_⟩
      rcases List.mem_cons.mp hD with rfl | hD
      · exact Or.inl hCS
      · exact h₅ D hD
    · obtain ⟨π', h₁, h₂, h₃, h₄, h₅⟩ := ih hπ
      refine ⟨C :: π', ⟨hC, h₁⟩,
        List.nodup_cons.mpr ⟨fun hC' => h₃ C hC' (Finset.mem_insert_self _ _), h₂⟩,
        fun D hD => ?_, fun D hD => ?_, fun D hD => ?_⟩
      · rcases List.mem_cons.mp hD with rfl | hD
        · exact hCS
        · exact fun hDS => h₃ D hD (Finset.mem_insert_of_mem hDS)
      · rcases List.mem_cons.mp hD with rfl | hD
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (h₄ D hD)
      · rcases List.mem_cons.mp hD with rfl | hD
        · exact Or.inr List.mem_cons_self
        · rcases h₅ D hD with hDS | hD'
          · rcases Finset.mem_insert.mp hDS with rfl | hDS
            · exact Or.inr List.mem_cons_self
            · exact Or.inl hDS
          · exact Or.inr (List.mem_cons_of_mem _ hD')

/-- Changing the initial clauses: a derivation from `Ψ` whose initial clauses all lie in the
accumulator `S` is, after dropping those initial-clause steps, a derivation from any `Φ`. -/
theorem IsDerivation.exists_of_initial_mem_acc {Ψ Φ : CNF V} {S : Finset (Clause V)}
    {π : List (Clause V)} (h : IsDerivation Ψ S π) (hΨ : ∀ C ∈ π, C ∈ Ψ → C ∈ S) :
    ∃ π' : List (Clause V), IsDerivation Φ S π' ∧ π'.length ≤ π.length ∧
      ∀ D ∈ π, D ∈ S ∨ D ∈ π' := by
  induction π generalizing S with
  | nil => exact ⟨[], trivial, le_rfl, by simp⟩
  | cons C π ih =>
    obtain ⟨hC, hπ⟩ := h
    by_cases hCS : C ∈ S
    · rw [Finset.insert_eq_of_mem hCS] at hπ
      obtain ⟨π', h₁, h₂, h₃⟩ := ih hπ fun D hD hDΨ => hΨ D (List.mem_cons_of_mem _ hD) hDΨ
      refine ⟨π', h₁, h₂.trans (Nat.le_succ _), fun D hD => ?_⟩
      rcases List.mem_cons.mp hD with rfl | hD
      · exact Or.inl hCS
      · exact h₃ D hD
    · have hres : ∃ C₁ ∈ S, ∃ C₂ ∈ S, Clause.IsResolvent C C₁ C₂ := by
        rcases hC with hC | hC
        · exact absurd (hΨ C List.mem_cons_self hC) hCS
        · exact hC
      obtain ⟨π', h₁, h₂, h₃⟩ := ih hπ fun D hD hDΨ =>
        Finset.mem_insert_of_mem (hΨ D (List.mem_cons_of_mem _ hD) hDΨ)
      refine ⟨C :: π', ⟨Or.inr hres, h₁⟩, Nat.succ_le_succ h₂, fun D hD => ?_⟩
      rcases List.mem_cons.mp hD with rfl | hD
      · exact Or.inr List.mem_cons_self
      · rcases h₃ D hD with hDS | hD'
        · rcases Finset.mem_insert.mp hDS with rfl | hDS
          · exact Or.inr List.mem_cons_self
          · exact Or.inl hDS
        · exact Or.inr (List.mem_cons_of_mem _ hD')

/-- The first clause of a derivation failing a property `P` that holds for the initial clauses
and for the available clauses `S` is a resolvent of two clauses satisfying `P`. -/
theorem IsDerivation.exists_resolvent_of_not {Φ : CNF V} {S : Finset (Clause V)}
    {π : List (Clause V)} (h : IsDerivation Φ S π) (P : Clause V → Prop)
    (hΦ : ∀ C ∈ Φ, P C) (hS : ∀ C ∈ S, P C) {D : Clause V} (hD : D ∈ π) (hPD : ¬ P D) :
    ∃ C ∈ π, ¬ P C ∧ ∃ C₁ C₂, (C₁ ∈ S ∨ C₁ ∈ π) ∧ (C₂ ∈ S ∨ C₂ ∈ π) ∧ P C₁ ∧ P C₂ ∧
      Clause.IsResolvent C C₁ C₂ := by
  induction π generalizing S with
  | nil => simp at hD
  | cons C π ih =>
    obtain ⟨hC, hπ⟩ := h
    by_cases hPC : P C
    · have hS' : ∀ D ∈ insert C S, P D := by
        intro D hD
        rcases Finset.mem_insert.mp hD with rfl | hD
        · exact hPC
        · exact hS D hD
      have hDπ : D ∈ π := by
        rcases List.mem_cons.mp hD with rfl | hD
        · exact absurd hPC hPD
        · exact hD
      obtain ⟨C', hC', hPC', C₁, C₂, h₁, h₂, hP₁, hP₂, hres⟩ := ih hπ hS' hDπ
      have hlift : ∀ {D}, (D ∈ insert C S ∨ D ∈ π) → D ∈ S ∨ D ∈ C :: π := by
        rintro D (hD | hD)
        · rcases Finset.mem_insert.mp hD with rfl | hD
          · exact Or.inr List.mem_cons_self
          · exact Or.inl hD
        · exact Or.inr (List.mem_cons_of_mem _ hD)
      exact ⟨C', List.mem_cons_of_mem _ hC', hPC', C₁, C₂, hlift h₁, hlift h₂, hP₁, hP₂, hres⟩
    · rcases hC with hC | ⟨C₁, h₁, C₂, h₂, hres⟩
      · exact absurd (hΦ C hC) hPC
      · exact ⟨C, List.mem_cons_self, hPC, C₁, C₂, Or.inl h₁, Or.inl h₂, hS C₁ h₁, hS C₂ h₂,
          hres⟩

/-- Monotonicity in the CNF: a derivation from `Φ` is a derivation from any `Φ' ⊇ Φ`. -/
theorem IsDerivation.mono {Φ Φ' : CNF V} (hΦ : Φ ⊆ Φ') {S : Finset (Clause V)}
    {π : List (Clause V)} (h : IsDerivation Φ S π) : IsDerivation Φ' S π := by
  induction π generalizing S with
  | nil => trivial
  | cons C π ih =>
    obtain ⟨hC, hπ⟩ := h
    exact ⟨hC.imp_left fun hC => hΦ hC, ih hπ⟩

/-- A prefix of a derivation is a derivation. -/
theorem IsDerivation.append_left {Φ : CNF V} {S : Finset (Clause V)} {π₁ π₂ : List (Clause V)}
    (h : IsDerivation Φ S (π₁ ++ π₂)) : IsDerivation Φ S π₁ := by
  induction π₁ generalizing S with
  | nil => trivial
  | cons C π₁ ih =>
    rw [List.cons_append] at h
    obtain ⟨hC, hπ⟩ := h
    exact ⟨hC, ih hπ⟩

/-- A derivation with the clauses of `S` available is one with the clauses of any `S' ⊇ S`
available. -/
theorem IsDerivation.mono_acc {Φ : CNF V} {S S' : Finset (Clause V)} (hS : S ⊆ S')
    {π : List (Clause V)} (h : IsDerivation Φ S π) : IsDerivation Φ S' π := by
  induction π generalizing S S' with
  | nil => trivial
  | cons C π ih =>
    obtain ⟨hC, hπ⟩ := h
    refine ⟨hC.imp_right ?_, ih (Finset.insert_subset_insert C hS) hπ⟩
    rintro ⟨C₁, h₁, C₂, h₂, hres⟩
    exact ⟨C₁, hS h₁, C₂, hS h₂, hres⟩

/-- Derivations concatenate: the second may use the clauses of the first. -/
theorem IsDerivation.append {Φ : CNF V} {S : Finset (Clause V)} {π₁ π₂ : List (Clause V)}
    (h₁ : IsDerivation Φ S π₁) (h₂ : IsDerivation Φ (S ∪ π₁.toFinset) π₂) :
    IsDerivation Φ S (π₁ ++ π₂) := by
  induction π₁ generalizing S with
  | nil => simpa using h₂
  | cons C π₁ ih =>
    obtain ⟨hC, hπ₁⟩ := h₁
    rw [List.cons_append]
    refine ⟨hC, ih hπ₁ ?_⟩
    rwa [show insert C S ∪ π₁.toFinset = S ∪ (C :: π₁).toFinset by
      ext; simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_cons]; tauto]

/-- A resolution derivation of the clause `C` from the CNF `Φ`: a sequence of clauses, each an
initial clause of `Φ` or a resolvent of two earlier clauses of the sequence, whose last clause
is `C`.

Paper: Section 2, "Resolution". -/
structure Derivation (Φ : CNF V) (C : Clause V) where
  /-- The clauses of the derivation, in derivation order. -/
  lines : List (Clause V)
  /-- Each clause is an initial clause of `Φ` or a resolvent of two earlier clauses. -/
  isDerivation : IsDerivation Φ ∅ lines
  /-- The last clause of the sequence is `C`. -/
  getLast?_lines : lines.getLast? = some C

/-- A resolution refutation of `Φ`: a derivation of the empty clause `⊥`.

Paper: Section 2, "Resolution". -/
abbrev Refutation (Φ : CNF V) := Derivation Φ ∅

namespace Derivation

variable {Φ : CNF V} {C : Clause V}

/-- The size of a derivation: its number of clauses.

Paper: Section 2, "Resolution". -/
def size (π : Derivation Φ C) : ℕ := π.lines.length

/-- The width of a derivation: the maximum width of its clauses.

Paper: Section 2, "Resolution". -/
def width (π : Derivation Φ C) : ℕ := π.lines.toFinset.sup Finset.card

theorem lines_ne_nil (π : Derivation Φ C) : π.lines ≠ [] := by
  intro h
  have := π.getLast?_lines
  simp [h] at this

theorem size_pos (π : Derivation Φ C) : 0 < π.size :=
  List.length_pos_iff.mpr π.lines_ne_nil

/-- The derived clause occurs in the derivation. -/
theorem mem_lines (π : Derivation Φ C) : C ∈ π.lines := by
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp π.getLast?_lines
  simp [hys]

theorem card_le_width (π : Derivation Φ C) {D : Clause V} (hD : D ∈ π.lines) :
    D.card ≤ π.width :=
  Finset.le_sup (f := Finset.card) (List.mem_toFinset.mpr hD)

/-- Soundness: a derived clause is implied by the CNF. -/
theorem implies (π : Derivation Φ C) : Φ.Implies C :=
  π.isDerivation.implies (by simp) C π.mem_lines

/-- Monotonicity in the CNF: a derivation from `Φ` is a derivation from any `Φ' ⊇ Φ`. -/
def mono {Φ' : CNF V} (hΦ : Φ ⊆ Φ') (π : Derivation Φ C) : Derivation Φ' C where
  lines := π.lines
  isDerivation := π.isDerivation.mono hΦ
  getLast?_lines := π.getLast?_lines

@[simp] theorem size_mono {Φ' : CNF V} (hΦ : Φ ⊆ Φ') (π : Derivation Φ C) :
    (π.mono hΦ).size = π.size :=
  rfl

/-- The one-line derivation of an initial clause. -/
def single (h : C ∈ Φ) : Derivation Φ C where
  lines := [C]
  isDerivation := ⟨Or.inl h, trivial⟩
  getLast?_lines := rfl

@[simp] theorem size_single (h : C ∈ Φ) : (single h).size = 1 := rfl

/-- Transport a derivation along an equality of its conclusion. -/
def copy (π : Derivation Φ C) {D : Clause V} (h : C = D) : Derivation Φ D where
  lines := π.lines
  isDerivation := π.isDerivation
  getLast?_lines := h ▸ π.getLast?_lines

@[simp] theorem size_copy (π : Derivation Φ C) {D : Clause V} (h : C = D) :
    (π.copy h).size = π.size :=
  rfl

/-- Resolve the conclusions of two derivations: concatenate them and append the resolvent. -/
def resolve {C₁ C₂ : Clause V} (π₁ : Derivation Φ C₁) (π₂ : Derivation Φ C₂) (x : V)
    (h₁ : Literal.pos x ∈ C₁) (h₂ : Literal.neg x ∈ C₂) :
    Derivation Φ (Clause.resolvent C₁ C₂ x) where
  lines := π₁.lines ++ π₂.lines ++ [Clause.resolvent C₁ C₂ x]
  isDerivation := by
    refine (π₁.isDerivation.append (π₂.isDerivation.mono_acc (Finset.empty_subset _))).append ?_
    refine ⟨Or.inr ⟨C₁, ?_, C₂, ?_, x, h₁, h₂, rfl⟩, trivial⟩
    · simp [π₁.mem_lines]
    · simp [π₂.mem_lines]
  getLast?_lines := List.getLast?_concat

@[simp] theorem size_resolve {C₁ C₂ : Clause V} (π₁ : Derivation Φ C₁) (π₂ : Derivation Φ C₂)
    (x : V) (h₁ : Literal.pos x ∈ C₁) (h₂ : Literal.neg x ∈ C₂) :
    (π₁.resolve π₂ x h₁ h₂).size = π₁.size + π₂.size + 1 := by
  simp [size, resolve, Nat.add_assoc]

/-- Every clause of a derivation sequence has a derivation of at most the sequence's length,
obtained by truncating the sequence after the clause. -/
theorem exists_of_mem {π : List (Clause V)} (h : IsDerivation Φ ∅ π) {D : Clause V}
    (hD : D ∈ π) : ∃ π' : Derivation Φ D, π'.size ≤ π.length := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hD
  refine ⟨⟨s ++ [D], ?_, List.getLast?_concat⟩, ?_⟩
  · have h' : IsDerivation Φ ∅ ((s ++ [D]) ++ t) := by simpa using h
    exact h'.append_left
  · simp only [size, List.length_append, List.length_cons, List.length_nil]
    omega

/-- If the derived clause fails a property `P` that holds for the initial clauses, then some
clause of the derivation failing `P` is a resolvent of two clauses of the derivation
satisfying `P`: the first clause failing `P`. -/
theorem exists_resolvent_of_not (π : Derivation Φ C) (P : Clause V → Prop)
    (hΦ : ∀ D ∈ Φ, P D) (hC : ¬ P C) :
    ∃ D ∈ π.lines, ¬ P D ∧ ∃ C₁ ∈ π.lines, ∃ C₂ ∈ π.lines, P C₁ ∧ P C₂ ∧
      Clause.IsResolvent D C₁ C₂ := by
  obtain ⟨D, hD, hPD, C₁, C₂, h₁, h₂, hP₁, hP₂, hres⟩ :=
    π.isDerivation.exists_resolvent_of_not P hΦ (by simp) π.mem_lines hC
  exact ⟨D, hD, hPD, C₁, h₁.resolve_left (Finset.notMem_empty _),
    C₂, h₂.resolve_left (Finset.notMem_empty _), hP₁, hP₂, hres⟩

/-- Every derivation can be replaced by one of the same conclusion without repeated clauses;
its size is then at most the number of clauses over the variables of `Φ`. -/
theorem exists_size_le (π : Derivation Φ C) :
    ∃ π' : Derivation Φ C, π'.size ≤ 2 ^ (2 * Φ.vars.card) := by
  obtain ⟨π₁, h₁, h₂, -, -, h₅⟩ := π.isDerivation.exists_nodup
  have hC : C ∈ π₁ := (h₅ C π.mem_lines).resolve_left (Finset.notMem_empty C)
  obtain ⟨π', hπ'⟩ := exists_of_mem h₁ hC
  refine ⟨π', hπ'.trans ?_⟩
  rw [← List.toFinset_card_of_nodup h₂]
  exact Clause.card_le_of_vars_subset fun D hD =>
    h₁.vars_subset (Finset.Subset.refl _) (by simp) D (List.mem_toFinset.mp hD)

end Derivation

/-- Derivations of subclauses of the clauses of a list, each of size at most `K`, concatenate
into one derivation sequence of length at most `K` times the length of the list. -/
theorem exists_isDerivation_concat {Φ : CNF V} {K : ℕ} (L : List (Clause V))
    (h : ∀ C ∈ L, ∃ D ⊆ C, ∃ δ : Derivation Φ D, δ.size ≤ K) :
    ∃ π : List (Clause V), IsDerivation Φ ∅ π ∧ π.length ≤ K * L.length ∧
      ∀ C ∈ L, ∃ D ∈ π, D ⊆ C := by
  induction L with
  | nil => exact ⟨[], trivial, by simp, by simp⟩
  | cons C L ih =>
    obtain ⟨D, hD, δ, hδ⟩ := h C List.mem_cons_self
    obtain ⟨π, hπ, hlen, hsub⟩ := ih fun C' hC' => h C' (List.mem_cons_of_mem _ hC')
    refine ⟨δ.lines ++ π, δ.isDerivation.append (hπ.mono_acc (Finset.empty_subset _)), ?_, ?_⟩
    · rw [List.length_append, List.length_cons, Nat.mul_succ]
      have : δ.lines.length ≤ K := hδ
      omega
    · intro C' hC'
      rcases List.mem_cons.mp hC' with rfl | hC'
      · exact ⟨D, List.mem_append_left _ δ.mem_lines, hD⟩
      · obtain ⟨D', hD', hsub'⟩ := hsub C' hC'
        exact ⟨D', List.mem_append_right _ hD', hsub'⟩

/-- Soundness: a CNF with a resolution refutation is unsatisfiable. -/
theorem Refutation.unsatisfiable {Φ : CNF V} (π : Refutation Φ) : Φ.Unsatisfiable :=
  (CNF.implies_empty_iff Φ).mp π.implies

end Derivation

end AssocLB
