/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/
import AssocLB.Resolution.SizeWidth

/-!
# Width transfer to local extensions

Paper: Section 5, Lemma [lem:width-transfer] (Width transfer). Let
`Φ^ext = Φ ∧ ⋀_f Def(Z_f)` extend a CNF `Φ` by extension variables `Z_f`, where `Def(Z_f)`
expresses `Z_f = f(x_f)` for a tuple `x_f` of at most `Δ` variables of `Φ`. Then every
resolution refutation of `Φ^ext` has width at least `w(Φ ⊢ ⊥) / (2Δ)`.

## Main definitions

* `extendBy f α`: the assignment to `V ⊕ Z` extending `α : V → Bool` by the defining
  functions, `z ↦ f z α`. A clause `C` of `Φ^ext` is satisfied by `extendBy f α` exactly when
  the paper's `Ĉ`, obtained by replacing each extension variable by its defining function, is
  satisfied by `α`.
* `Literal.support S l`, `Clause.support S C`: the variables of `Φ` that a literal or a clause
  depends on after this replacement, `{v}` for a literal over `v : V` and the support `S z` for
  a literal over `z : Z`; the paper's `vars(Ĉ)`.
* `CNF.narrow Φ k X`: the nontautological clauses over the variables `X` with a derivation
  from `Φ` of width at most `k`.

## Main results

* `IsDerivation.forall_lines`: induction along a derivation.
* `Derivation.exists_width_le_of_compose`: composing narrow derivations. If the
  nontautological clauses of `F` have derivations from `Φ` of width at most `k`, and `F` lies
  over at most `k` variables, then a derivation of a nontautological clause `C` from `F` yields
  a derivation from `Φ` of a subclause of `C` of width at most `k`.
* `CNF.Implies.exists_derivation_width_le`: implicational completeness with a width bound, the
  paper's "a derivation never leaves the variables of its premises".
* `width_transfer`: Lemma [lem:width-transfer]. A refutation of `Φ^ext` of width `w` yields a
  refutation of `Φ` of width at most `2Δw`.

## Design notes

* The variables of `Φ^ext` form the sum type `V ⊕ Z`, as `SPMVar` does; `Φ` is a CNF over this
  type mentioning only variables of `V`, so no renaming of variables is needed.
* The clauses `Def(Z_f)` enter only through their soundness: every clause of `Φ^ext` outside
  `Φ` holds under every assignment `extendBy f α`. The defining function `f z` is a function
  of all assignments to `V` that depends only on the at most `Δ` variables of its support.
* The proof follows the paper. The paper represents each line `Ĉ` by an equivalent CNF over
  its variables and fills in each resolution step by implicational completeness within the at
  most `2Δw` variables of the two premises. Here the representing CNF is `CNF.narrow`, the
  narrow clauses over the support of `C`, and the invariant along the refutation is that these
  clauses imply `Ĉ`. Implicational completeness produces subclauses and possibly tautological
  intermediate clauses; the simulation `IsDerivation.exists_simulation_sublist` with the
  identity substitution removes the tautologies, so that every clause of the derivation is a
  nontautological clause over the at most `2Δw` variables of the premises, hence of width at
  most `2Δw`.
-/

namespace AssocLB

variable {V : Type*} [DecidableEq V]

/-! ### Induction along a derivation -/

/-- Induction along a derivation. A property of clauses that holds for the available clauses
`S` and for the initial clauses occurring in the derivation, and that a resolvent occurring in
the derivation inherits from its two premises, holds for every clause of the derivation. -/
theorem IsDerivation.forall_lines {Φ : CNF V} {S : Finset (Clause V)} {π : List (Clause V)}
    (h : IsDerivation Φ S π) (P : Clause V → Prop) (hS : ∀ C ∈ S, P C)
    (hinit : ∀ C ∈ π, C ∈ Φ → P C)
    (hres : ∀ C ∈ π, ∀ C₁ C₂, (C₁ ∈ S ∨ C₁ ∈ π) → (C₂ ∈ S ∨ C₂ ∈ π) →
      Clause.IsResolvent C C₁ C₂ → P C₁ → P C₂ → P C) :
    ∀ C ∈ π, P C := by
  induction π generalizing S with
  | nil => simp
  | cons C π ih =>
    obtain ⟨hC, hπ⟩ := h
    have hPC : P C := by
      rcases hC with hC | ⟨C₁, h₁, C₂, h₂, hr⟩
      · exact hinit C List.mem_cons_self hC
      · exact hres C List.mem_cons_self C₁ C₂ (Or.inl h₁) (Or.inl h₂) hr (hS C₁ h₁) (hS C₂ h₂)
    have hS' : ∀ D ∈ insert C S, P D := by
      intro D hD
      rcases Finset.mem_insert.mp hD with rfl | hD
      · exact hPC
      · exact hS D hD
    have hlift : ∀ {D}, (D ∈ insert C S ∨ D ∈ π) → D ∈ S ∨ D ∈ C :: π := by
      rintro D (hD | hD)
      · rcases Finset.mem_insert.mp hD with rfl | hD
        · exact Or.inr List.mem_cons_self
        · exact Or.inl hD
      · exact Or.inr (List.mem_cons_of_mem _ hD)
    have ih' := ih hπ hS' (fun D hD => hinit D (List.mem_cons_of_mem _ hD))
      (fun D hD C₁ C₂ h₁ h₂ => hres D (List.mem_cons_of_mem _ hD) C₁ C₂ (hlift h₁) (hlift h₂))
    intro D hD
    rcases List.mem_cons.mp hD with rfl | hD
    · exact hPC
    · exact ih' D hD

/-! ### Nontautological clauses -/

namespace Clause

omit [DecidableEq V] in
/-- A clause survives the identity substitution exactly when it is not a tautology. -/
theorem survivesUnder_id_iff (C : Clause V) :
    SurvivesUnder (Subst.id V) C ↔ ¬ C.IsTautology := by
  simp [SurvivesUnder, SatUnder, TautUnder, IsTautology]

omit [DecidableEq V] in
/-- A subclause of a nontautological clause is nontautological. -/
theorem not_isTautology_of_subset {C D : Clause V} (h : D ⊆ C) (hC : ¬ C.IsTautology) :
    ¬ D.IsTautology := fun ⟨l, hl, hlc⟩ => hC ⟨l, h hl, h hlc⟩

/-- The variables of a subclause are among those of the clause. -/
theorem vars_mono {C D : Clause V} (h : C ⊆ D) : C.vars ⊆ D.vars :=
  Finset.image_subset_image h

/-- A nontautological clause has at most one literal per variable, so its width is at most its
number of variables. -/
theorem card_le_card_vars {C : Clause V} (hC : ¬ C.IsTautology) : C.card ≤ C.vars.card := by
  refine (Finset.card_image_of_injOn fun l hl l' hl' hll' => ?_).symm.le
  by_contra hne
  refine hC ⟨l, hl, ?_⟩
  rcases l with ⟨v, s⟩
  rcases l' with ⟨v', s'⟩
  change v = v' at hll'
  subst hll'
  have hs : s ≠ s' := fun h => hne (by rw [h])
  cases s <;> cases s' <;> first | exact absurd rfl hs | exact hl'

end Clause

/-- The variables of a clause of a CNF are among those of the CNF. -/
theorem CNF.subset_vars_of_mem {Φ : CNF V} {C : Clause V} (h : C ∈ Φ) : C.vars ⊆ Φ.vars := by
  intro v hv
  obtain ⟨l, hl, rfl⟩ := Clause.mem_vars.mp hv
  exact CNF.mem_vars.mpr ⟨C, h, l, hl, rfl⟩

/-! ### Composing narrow derivations -/

/-- Derivations of width at most `k` of the clauses of a list concatenate into one derivation
sequence of clauses of width at most `k` containing them. -/
theorem exists_isDerivation_concat_width {Φ : CNF V} {k : ℕ} (L : List (Clause V))
    (h : ∀ C ∈ L, ∃ δ : Derivation Φ C, δ.width ≤ k) :
    ∃ π : List (Clause V), IsDerivation Φ ∅ π ∧ (∀ D ∈ π, D.card ≤ k) ∧ ∀ C ∈ L, C ∈ π := by
  induction L with
  | nil => exact ⟨[], trivial, by simp, by simp⟩
  | cons C L ih =>
    obtain ⟨δ, hδ⟩ := h C List.mem_cons_self
    obtain ⟨π, hπ, hk, hmem⟩ := ih fun C' hC' => h C' (List.mem_cons_of_mem _ hC')
    refine ⟨δ.lines ++ π, δ.isDerivation.append (hπ.mono_acc (Finset.empty_subset _)), ?_, ?_⟩
    · intro D hD
      rcases List.mem_append.mp hD with hD | hD
      · exact (δ.card_le_width hD).trans hδ
      · exact hk D hD
    · intro C' hC'
      rcases List.mem_cons.mp hC' with rfl | hC'
      · exact List.mem_append_left _ δ.mem_lines
      · exact List.mem_append_right _ (hmem C' hC')

/-- **Composing narrow derivations.** Let the nontautological clauses of `F` have derivations
from `Φ` of width at most `k`, and let `F` lie over a set `X` of at most `k` variables. Then a
derivation of a nontautological clause `C` from `F` yields a derivation from `Φ` of a subclause
of `C` of width at most `k`: the simulation with the identity substitution replaces the initial
clauses of the derivation by their narrow derivations and drops its tautological clauses, and
every remaining clause is a nontautological clause over `X`.

Paper: proof of Lemma [lem:width-transfer], "the two premise CNFs together have at most `2Δw`
variables, so the intermediate steps have width at most `2Δw`". -/
theorem Derivation.exists_width_le_of_compose {Φ F : CNF V} {k : ℕ}
    (hF : ∀ D ∈ F, ¬ D.IsTautology → ∃ δ : Derivation Φ D, δ.width ≤ k) {X : Finset V}
    (hX : X.card ≤ k) (hFX : F.vars ⊆ X) {C : Clause V} (hC : ¬ C.IsTautology)
    (δ : Derivation F C) : ∃ D ⊆ C, ∃ δ' : Derivation Φ D, δ'.width ≤ k := by
  -- the narrow derivations of the nontautological clauses of `F`, concatenated
  obtain ⟨π₀, hπ₀, hk₀, hmem₀⟩ :=
    exists_isDerivation_concat_width (F.filter fun D => ¬ D.IsTautology).toList fun D hD => by
      rw [Finset.mem_toList, Finset.mem_filter] at hD
      exact hF D hD.1 hD.2
  -- every clause of `δ` lies over `X`
  have hvars : ∀ D ∈ δ.lines, D.vars ⊆ X := δ.isDerivation.vars_subset hFX (by simp)
  -- simulate `δ` with the identity substitution, its initial clauses being available in `π₀`
  obtain ⟨πs, π', hsub, hall, hπ', hcov⟩ := δ.isDerivation.exists_simulation_sublist
    (Subst.id V) ∅ (Ψ := Φ) (S₀ := π₀.toFinset) (S' := π₀.toFinset) (Finset.Subset.refl _)
    (fun D _ hD hsurv => ⟨D, by simp, Or.inr (Or.inl (List.mem_toFinset.mpr (hmem₀ D (by
      rw [Finset.mem_toList, Finset.mem_filter]
      exact ⟨hD, (Clause.survivesUnder_id_iff D).mp hsurv⟩))))⟩)
    (by simp)
  obtain ⟨D, hD, hDC⟩ := hcov C δ.mem_lines ((Clause.survivesUnder_id_iff C).mpr hC)
  rw [Clause.subst_id, Finset.union_empty] at hDC
  -- the clauses of `π'` are nontautological clauses over `X`
  have hk' : ∀ E ∈ π', E.card ≤ k := by
    intro E hE
    obtain ⟨E₀, hE₀, hsurv₀, hEE₀⟩ := forall₂_exists_of_mem hall hE
    rw [Clause.subst_id, Finset.union_empty] at hEE₀
    have hE₀taut := (Clause.survivesUnder_id_iff E₀).mp hsurv₀
    have hEX : E.vars ⊆ X := (Clause.vars_mono hEE₀).trans (hvars E₀ (hsub.subset hE₀))
    calc E.card ≤ E.vars.card :=
          Clause.card_le_card_vars (Clause.not_isTautology_of_subset hEE₀ hE₀taut)
      _ ≤ X.card := Finset.card_le_card hEX
      _ ≤ k := hX
  -- concatenate, and truncate after the subclause `D` of `C`
  have hπ : IsDerivation Φ ∅ (π₀ ++ π') := hπ₀.append (by simpa using hπ')
  have hDmem : D ∈ π₀ ++ π' := by
    rcases hD with hD | hD
    · exact List.mem_append_left _ (List.mem_toFinset.mp hD)
    · exact List.mem_append_right _ hD
  obtain ⟨δ', hδ'⟩ := Derivation.exists_of_mem_sublist hπ hDmem
  refine ⟨D, hDC, δ', δ'.width_le fun E hE => ?_⟩
  rcases List.mem_append.mp (hδ'.subset hE) with hE | hE
  · exact hk₀ E hE
  · exact hk' E hE

/-- **Implicational completeness with a width bound.** If `Φ` implies a nontautological clause
`C`, then some subclause of `C` has a derivation from `Φ` of width at most the number of
variables of `Φ`.

Paper: proof of Lemma [lem:width-transfer]. -/
theorem CNF.Implies.exists_derivation_width_le {Φ : CNF V} {C : Clause V} (h : Φ.Implies C)
    (hC : ¬ C.IsTautology) : ∃ D ⊆ C, ∃ π : Derivation Φ D, π.width ≤ Φ.vars.card := by
  obtain ⟨D, hD, ⟨δ⟩⟩ := h.exists_derivation hC
  obtain ⟨D', hD', δ', hδ'⟩ := δ.exists_width_le_of_compose (Φ := Φ) (X := Φ.vars)
    (fun E hE hE' => ⟨Derivation.single hE, (Derivation.single hE).width_le fun E' hE'' => by
      obtain rfl : E' = E := List.mem_singleton.mp hE''
      exact (Clause.card_le_card_vars hE').trans
        (Finset.card_le_card (CNF.subset_vars_of_mem hE))⟩)
    le_rfl (Finset.Subset.refl _) (Clause.not_isTautology_of_subset hD hC)
  exact ⟨D', hD'.trans hD, δ', hδ'⟩

/-! ### Local extensions -/

section Transfer

variable {Z : Type*} [DecidableEq Z]

/-- The assignment to `V ⊕ Z` extending `α : V → Bool` by the defining functions `f`. A clause
`C` over `V ⊕ Z` is satisfied by `extendBy f α` exactly when the paper's `Ĉ`, obtained from
`C` by replacing each extension variable by its defining function, is satisfied by `α`. -/
def extendBy (f : Z → (V → Bool) → Bool) (α : V → Bool) : V ⊕ Z → Bool :=
  Sum.elim α fun z => f z α

omit [DecidableEq V] [DecidableEq Z] in
@[simp] theorem extendBy_inl (f : Z → (V → Bool) → Bool) (α : V → Bool) (v : V) :
    extendBy f α (Sum.inl v) = α v := rfl

omit [DecidableEq V] [DecidableEq Z] in
@[simp] theorem extendBy_inr (f : Z → (V → Bool) → Bool) (α : V → Bool) (z : Z) :
    extendBy f α (Sum.inr z) = f z α := rfl

namespace Literal

/-- The variables of `V` that a literal over `V ⊕ Z` depends on after the extension variables
are replaced by their defining functions: `{v}` for a literal over `v : V`, and the support
`S z` for a literal over `z : Z`. -/
def support (S : Z → Finset V) (l : Literal (V ⊕ Z)) : Finset V :=
  Sum.elim (fun v => {v}) S l.var

omit [DecidableEq V] [DecidableEq Z] in
@[simp] theorem support_inl (S : Z → Finset V) (v : V) (b : Bool) :
    support S (⟨Sum.inl v, b⟩ : Literal (V ⊕ Z)) = {v} := rfl

omit [DecidableEq V] [DecidableEq Z] in
@[simp] theorem support_inr (S : Z → Finset V) (z : Z) (b : Bool) :
    support S (⟨Sum.inr z, b⟩ : Literal (V ⊕ Z)) = S z := rfl

end Literal

namespace Clause

/-- The variables of `V` that a clause over `V ⊕ Z` depends on after the replacement: the
paper's `vars(Ĉ)`. -/
def support (S : Z → Finset V) (C : Clause (V ⊕ Z)) : Finset V := C.biUnion (Literal.support S)

variable {S : Z → Finset V}

omit [DecidableEq Z] in
/-- A clause of width `w` whose literals have supports of size at most `Δ ≥ 1` depends on at
most `Δ w` variables. -/
theorem card_support_le {Δ : ℕ} (hΔ : 1 ≤ Δ) (hS : ∀ z, (S z).card ≤ Δ) (C : Clause (V ⊕ Z)) :
    (C.support S).card ≤ Δ * C.card :=
  calc (C.support S).card ≤ ∑ l ∈ C, (Literal.support S l).card := Finset.card_biUnion_le
    _ ≤ C.card • Δ := Finset.sum_le_card_nsmul _ _ _ fun l _ => by
        rcases l with ⟨v | z, b⟩
        · simpa using hΔ
        · simpa using hS z
    _ = Δ * C.card := by rw [smul_eq_mul, mul_comm]

/-- A variable of `V` occurring in `C` lies in its support. -/
theorem mem_support_of_inl_mem_vars {C : Clause (V ⊕ Z)} {v : V} (h : Sum.inl v ∈ C.vars) :
    v ∈ C.support S := by
  obtain ⟨l, hl, hlv⟩ := mem_vars.mp h
  refine Finset.mem_biUnion.mpr ⟨l, hl, ?_⟩
  simp [Literal.support, hlv]

/-- The support of a resolvent lies in the supports of its premises. -/
theorem support_resolvent_subset (S : Z → Finset V) (C₁ C₂ : Clause (V ⊕ Z)) (x : V ⊕ Z) :
    (resolvent C₁ C₂ x).support S ⊆ C₁.support S ∪ C₂.support S := by
  intro v hv
  obtain ⟨l, hl, hlv⟩ := Finset.mem_biUnion.mp hv
  rcases mem_resolvent.mp hl with ⟨-, hl⟩ | ⟨-, hl⟩
  · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨l, hl, hlv⟩)
  · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨l, hl, hlv⟩)

omit [DecidableEq Z] in
/-- `Ĉ` depends only on the support of `C`: assignments agreeing on the support satisfy `C`
alike after extension. -/
theorem sat_extendBy_congr {f : Z → (V → Bool) → Bool}
    (hf : ∀ z, ∀ α β : V → Bool, (∀ v ∈ S z, α v = β v) → f z α = f z β)
    {C : Clause (V ⊕ Z)} {α β : V → Bool} (h : ∀ v ∈ C.support S, α v = β v) :
    Sat (extendBy f α) C ↔ Sat (extendBy f β) C := by
  classical
  refine sat_congr fun x hx => ?_
  obtain ⟨l, hl, rfl⟩ := mem_vars.mp hx
  have hsupp : Literal.support S l ⊆ C.support S := Finset.subset_biUnion_of_mem _ hl
  rcases l with ⟨v | z, b⟩
  · exact h v (hsupp (Finset.mem_singleton_self v))
  · exact hf z α β fun v hv => h v (hsupp hv)

end Clause

namespace CNF

open Classical in
/-- The nontautological clauses over the variables `X` having a derivation from `Φ` of width at
most `k`: the CNF that represents, in the proof of Lemma [lem:width-transfer], a line depending
on the variables `X`. -/
noncomputable def narrow (Φ : CNF V) (k : ℕ) (X : Finset V) : CNF V :=
  (Literal.ofVars X).powerset.filter fun D =>
    ¬ D.IsTautology ∧ ∃ δ : Derivation Φ D, δ.width ≤ k

theorem mem_narrow {Φ : CNF V} {k : ℕ} {X : Finset V} {D : Clause V} :
    D ∈ Φ.narrow k X ↔ D.vars ⊆ X ∧ ¬ D.IsTautology ∧ ∃ δ : Derivation Φ D, δ.width ≤ k := by
  classical
  simp only [narrow, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun v hv => ?_, h₂⟩
    obtain ⟨l, hl, rfl⟩ := Clause.mem_vars.mp hv
    exact Literal.mem_ofVars.mp (h₁ hl)
  · rintro ⟨h₁, h₂⟩
    exact ⟨Clause.subset_ofVars h₁, h₂⟩

theorem narrow_mono {Φ : CNF V} {k : ℕ} {X X' : Finset V} (h : X ⊆ X') :
    Φ.narrow k X ⊆ Φ.narrow k X' := by
  intro D hD
  rw [mem_narrow] at hD ⊢
  exact ⟨hD.1.trans h, hD.2⟩

theorem vars_narrow_subset (Φ : CNF V) (k : ℕ) (X : Finset V) : (Φ.narrow k X).vars ⊆ X := by
  intro v hv
  obtain ⟨D, hD, l, hl, rfl⟩ := mem_vars.mp hv
  exact (mem_narrow.mp hD).1 (Clause.mem_vars.mpr ⟨l, hl, rfl⟩)

end CNF

/-- **Width transfer**, Lemma [lem:width-transfer]. Let `Φ` be a CNF over the variables `V`,
inside the variable type `V ⊕ Z`, and let `Ψ` extend `Φ` by clauses that hold whenever each
extension variable `z : Z` takes the value `f z α` of its defining function, a function
depending only on the support `S z` of at most `Δ ≥ 1` variables of `V`. Then a refutation of
`Ψ` of width `w` yields a refutation of `Φ` of width at most `2Δw`. -/
theorem width_transfer {Φ Ψ : CNF (V ⊕ Z)} {f : Z → (V → Bool) → Bool} {S : Z → Finset V}
    {Δ : ℕ} (hΔ : 1 ≤ Δ) (hS : ∀ z, (S z).card ≤ Δ)
    (hf : ∀ z, ∀ α β : V → Bool, (∀ v ∈ S z, α v = β v) → f z α = f z β)
    (hΦ : ∀ C ∈ Φ, ∀ l ∈ C, ∃ v, l.var = Sum.inl v)
    (hΨ : ∀ C ∈ Ψ, C ∈ Φ ∨ ∀ α, Clause.Sat (extendBy f α) C)
    (π : Refutation Ψ) : ∃ π' : Refutation Φ, π'.width ≤ 2 * Δ * π.width := by
  classical
  set k := 2 * Δ * π.width with hk
  -- the invariant along `π`: the narrow clauses over the support of `C` imply `Ĉ`
  have hP : ∀ C ∈ π.lines, ∀ α : V → Bool,
      CNF.Sat (extendBy f α) (Φ.narrow k ((C.support S).image Sum.inl)) →
        Clause.Sat (extendBy f α) C := by
    refine π.isDerivation.forall_lines
      (fun C => ∀ α : V → Bool,
        CNF.Sat (extendBy f α) (Φ.narrow k ((C.support S).image Sum.inl)) →
          Clause.Sat (extendBy f α) C) (by simp) ?_ ?_
    · -- initial clauses: a nontautological clause of `Φ` is itself narrow, and a clause of
      -- `Ψ` outside `Φ` holds under every extended assignment
      intro C hCπ hCΨ α hα
      rcases hΨ C hCΨ with hCΦ | hsound
      · by_cases htaut : C.IsTautology
        · exact htaut.sat _
        · refine hα C (CNF.mem_narrow.mpr ⟨?_, htaut, Derivation.single hCΦ, ?_⟩)
          · intro x hx
            obtain ⟨l, hl, rfl⟩ := Clause.mem_vars.mp hx
            obtain ⟨v, hv⟩ := hΦ C hCΦ l hl
            rw [hv]
            exact Finset.mem_image_of_mem _ (Clause.mem_support_of_inl_mem_vars (hv ▸ hx))
          · refine (Derivation.single hCΦ).width_le fun D hD => ?_
            obtain rfl : D = C := List.mem_singleton.mp hD
            exact (π.card_le_width hCπ).trans (Nat.le_mul_of_pos_left _ (by omega))
      · exact hsound α
    · -- resolvents: simulate the step within the supports of the two premises
      intro C hCπ C₁ C₂ h₁ h₂ hres hP₁ hP₂ α hα
      have hw₁ : C₁.card ≤ π.width := π.card_le_width (h₁.resolve_left (Finset.notMem_empty _))
      have hw₂ : C₂.card ≤ π.width := π.card_le_width (h₂.resolve_left (Finset.notMem_empty _))
      obtain ⟨x, -, -, rfl⟩ := hres
      by_contra hC
      -- the variables of the two premises, at most `2Δw` of them
      set Y : Finset V := C₁.support S ∪ C₂.support S with hY
      have hYk : (Y.image (Sum.inl : V → V ⊕ Z)).card ≤ k :=
        calc (Y.image (Sum.inl : V → V ⊕ Z)).card ≤ Y.card := Finset.card_image_le
          _ ≤ (C₁.support S).card + (C₂.support S).card := Finset.card_union_le _ _
          _ ≤ Δ * C₁.card + Δ * C₂.card :=
              Nat.add_le_add (Clause.card_support_le hΔ hS C₁) (Clause.card_support_le hΔ hS C₂)
          _ ≤ Δ * π.width + Δ * π.width :=
              Nat.add_le_add (Nat.mul_le_mul_left _ hw₁) (Nat.mul_le_mul_left _ hw₂)
          _ = k := by rw [hk]; ring
      -- the clause over the support of the resolvent that `α` falsifies
      set D₀ : Clause (V ⊕ Z) :=
        ((Clause.resolvent C₁ C₂ x).support S).image fun v => ⟨Sum.inl v, !α v⟩ with hD₀
      have hD₀taut : ¬ D₀.IsTautology := by
        rintro ⟨l, hl, hlc⟩
        obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hl
        obtain ⟨v', -, hv'⟩ := Finset.mem_image.mp hlc
        rw [Literal.compl_mk, Literal.mk.injEq] at hv'
        obtain ⟨h1, h2⟩ := hv'
        obtain rfl : v' = v := Sum.inl_injective h1
        simp at h2
      have hD₀vars : D₀.vars ⊆ ((Clause.resolvent C₁ C₂ x).support S).image Sum.inl := by
        intro y hy
        obtain ⟨l, hl, rfl⟩ := Clause.mem_vars.mp hy
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hl
        exact Finset.mem_image_of_mem _ hv
      have hD₀unsat : ¬ Clause.Sat (extendBy f α) D₀ := by
        rintro ⟨l, hl, hs⟩
        obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hl
        simp [Literal.Sat] at hs
      -- the narrow clauses over `Y` imply `Ĉ₁` and `Ĉ₂`, hence `Ĉ`, hence `D₀`
      set F := Φ.narrow k (Y.image Sum.inl) with hF
      have himp : F.Implies D₀ := by
        intro β' hβ'
        set β : V → Bool := fun v => β' (Sum.inl v) with hβ
        have hFβ : CNF.Sat (extendBy f β) F := by
          intro D hD
          refine (Clause.sat_congr fun y hy => ?_).mp (hβ' D hD)
          obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp ((CNF.mem_narrow.mp hD).1 hy)
          rfl
        have hC₁ : Clause.Sat (extendBy f β) C₁ := hP₁ β (hFβ.subset
          (CNF.narrow_mono (Finset.image_subset_image Finset.subset_union_left)))
        have hC₂ : Clause.Sat (extendBy f β) C₂ := hP₂ β (hFβ.subset
          (CNF.narrow_mono (Finset.image_subset_image Finset.subset_union_right)))
        by_contra hnot
        refine hC ((Clause.sat_extendBy_congr hf (β := β) fun v hv => ?_).mpr
          (hC₁.resolvent x hC₂))
        by_contra hne
        have hβv : β v = !α v := by
          cases hαv : α v <;> cases hβv : β v <;> simp_all
        exact hnot ⟨⟨Sum.inl v, !α v⟩, Finset.mem_image_of_mem _ hv, hβv⟩
      -- derive a subclause of `D₀` from `F`, hence from `Φ` within width `k`
      obtain ⟨D₁, hD₁, ⟨δ⟩⟩ := himp.exists_derivation hD₀taut
      obtain ⟨D₂, hD₂, δ', hδ'⟩ := δ.exists_width_le_of_compose (Φ := Φ)
        (fun D hD _ => (CNF.mem_narrow.mp hD).2.2) hYk (CNF.vars_narrow_subset _ _ _)
        (Clause.not_isTautology_of_subset hD₁ hD₀taut)
      have hD₂mem : D₂ ∈ Φ.narrow k (((Clause.resolvent C₁ C₂ x).support S).image Sum.inl) :=
        CNF.mem_narrow.mpr ⟨(Clause.vars_mono (hD₂.trans hD₁)).trans hD₀vars,
          Clause.not_isTautology_of_subset (hD₂.trans hD₁) hD₀taut, δ', hδ'⟩
      exact hD₀unsat ((hα D₂ hD₂mem).mono (hD₂.trans hD₁))
  -- the empty clause has empty support, so a narrow clause over no variables exists: `⊥`
  by_contra hnone
  refine Clause.not_sat_empty (extendBy f fun _ => true)
    (hP (∅ : Clause (V ⊕ Z)) π.mem_lines (fun _ => true) fun D hD => ?_)
  exfalso
  obtain ⟨hDv, -, δ, hδ⟩ := CNF.mem_narrow.mp hD
  have hDempty : D = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun l hl => ?_
    have := hDv (Clause.mem_vars.mpr ⟨l, hl, rfl⟩)
    simp [Clause.support] at this
  subst hDempty
  exact hnone ⟨δ, hδ⟩

end Transfer

end AssocLB
