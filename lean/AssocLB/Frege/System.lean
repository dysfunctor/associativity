/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/
import AssocLB.Frege.Formula

/-!
# Frege systems and derivations

Paper: Section 9.1 (Bounded-depth Frege systems), paragraph "Frege systems": rules, systems,
derivations, refutations, their depth and size, and the Compose step of the proof of Lemma
[lem:frege-transfer].

## Main definitions

* `FregeRule`: an inference rule `F₁ … F_j / F` over the schematic variables `Fin k`;
  `FregeRule.Sound r`: the rule is sound.
* `Frege.IsInference R S F`: `F` is the conclusion of an instance of a rule of `R` whose
  premises lie in `S`, an instance being a substitution of arbitrary formulas for the
  schematic variables.
* `Frege.IsDerivation R Γ S π`: every formula of the sequence `π` belongs to `Γ` or follows by
  a rule of `R` from formulas in `S` or earlier in `π`. As for resolution, `S` is the
  accumulator of the recursion, and a derivation in the paper's sense is the case `S = ∅`.
* `Frege.Derivation R Γ G`: a sequence satisfying `IsDerivation R Γ ∅` whose last formula is
  `G`; `Frege.Refutation R Γ` is a derivation of `⊥`. `Derivation.size` is the total size of
  the formulas and `Derivation.depth` their maximum depth.
* `Frege.Complete R`: implicational completeness, every formula implied by finitely many
  formulas has a derivation from them.
* `FregeSystem`: a finite list of sound rules that is implicationally complete;
  `FregeSystem.Derivation`, `FregeSystem.Refutation`.

## Main results

* `Frege.Derivation.implies`: soundness, a derived formula is implied by `Γ`;
  `Frege.Refutation.not_sat`: a set of formulas with a refutation is unsatisfiable.
* `Frege.Derivation.single`, `Frege.Derivation.mono`, `Frege.Derivation.exists_of_mem`:
  initial formulas have one-line derivations, derivations are monotone in `Γ`, and every
  formula of a derivation sequence has a derivation of no greater size and depth.
* `Frege.IsDerivation.mono_acc`, `Frege.IsDerivation.append`,
  `Frege.IsDerivation.exists_drop_initial`, `Frege.exists_isDerivation_concat`: the
  accumulator can be enlarged, derivation sequences concatenate, initial-formula steps whose
  formulas are already available can be dropped (which turns a derivation from `Γ` into one
  from any `Γ'` containing the remaining initial formulas), and derivations of the formulas of
  a list concatenate into one sequence containing them all. These are the ingredients of the
  Compose step and of the cut `Frege.Derivation.exists_trans`: a derivation of `A` from `Γ`
  and one of `B` from `Γ` and `A` give a derivation of `B` from `Γ` of at most the total size.
* `Frege.Derivation.exists_trans_le`: the cut in the form the reduction uses, from a derivation
  of `A` from `Γ` and one of `B` from `A` alone, with the sizes added and any common bound on
  the two depths carried over.
* `Frege.Derivation.copy`: the conclusion can be rewritten along an equality.
* `Frege.Refutation.compose`: the Compose step. If `Γ` has a refutation `π` and every initial
  formula `F` of `π` has a derivation from `Γ'` of size at most `K |F|` and depth at most `D`,
  then `Γ'` has a refutation of size at most `(K + 1) |π|` and depth at most `max(depth π, D)`.

## Design notes

* The paper fixes an arbitrary Frege system; here a system is a term `𝓕 : FregeSystem`, and
  every statement of Section 9 is universally quantified over it. Håstad's lower bound enters
  as the hypothesis `HastadGridPM 𝓕` (`AssocLB.Frege.Hastad`).
* Soundness and implicational completeness are fields of `FregeSystem`, as the paper requires
  both of a Frege system. Completeness is stated for finitely many premises over the variables
  `Fin k` (Cook–Reckhow); the general case follows by renaming, which is a substitution.
  No instance of `FregeSystem` is constructed: the lower bound is for every Frege system, and
  the existence of complete systems is classical (Cook–Reckhow).
* Derivations are lists, size counts symbols with multiplicity, and the minimum refutation
  size `size_F^d(Φ)` is not defined as a number: bounds are stated for every refutation of
  depth at most `d`, as for resolution.
* Rule instances substitute formulas for the schematic variables; premises are matched as
  formulas, with no flattening, which is where binary disjunction pays off.
* `Frege.Derivation` and `Frege.Refutation` live in the namespace `Frege` to keep them apart
  from the resolution derivations `AssocLB.Derivation`.
-/

namespace AssocLB

/-- A Frege rule `F₁ … F_j / F` over the schematic variables `p₁, …, p_k`, represented by the
type `Fin k`.

Paper: Section 9.1, "Frege systems". -/
structure FregeRule where
  /-- The number `k` of schematic variables. -/
  arity : ℕ
  /-- The premises `F₁, …, F_j`. -/
  premises : List (Formula (Fin arity))
  /-- The conclusion `F`. -/
  conclusion : Formula (Fin arity)

namespace FregeRule

/-- A rule is sound if every assignment to its schematic variables satisfying its premises
satisfies its conclusion. -/
def Sound (r : FregeRule) : Prop :=
  ∀ α : Fin r.arity → Bool, (∀ P ∈ r.premises, P.eval α = true) → r.conclusion.eval α = true

end FregeRule

namespace Frege

variable {V : Type*}

/-- `Frege.IsInference R S F`: `F` follows from formulas of `S` by an instance of a rule of
`R`, that is, for some rule `r ∈ R` and some formulas `σ` substituted for its schematic
variables, every substituted premise lies in `S` and `F` is the substituted conclusion.

Paper: Section 9.1, "Frege systems". -/
def IsInference (R : List FregeRule) (S : Finset (Formula V)) (F : Formula V) : Prop :=
  ∃ r ∈ R, ∃ σ : Fin r.arity → Formula V,
    (∀ P ∈ r.premises, P.subst σ ∈ S) ∧ F = r.conclusion.subst σ

/-- Rule instances are monotone in the available formulas. -/
theorem IsInference.mono {R : List FregeRule} {S S' : Finset (Formula V)} (hS : S ⊆ S')
    {F : Formula V} (h : IsInference R S F) : IsInference R S' F := by
  obtain ⟨r, hr, σ, hprem, rfl⟩ := h
  exact ⟨r, hr, σ, fun P hP => hS (hprem P hP), rfl⟩

variable [DecidableEq V]

/-- `Frege.IsDerivation R Γ S π`: every formula of the sequence `π`, read left to right, belongs
to `Γ` or follows by a rule of `R` from formulas that lie in `S` or occur earlier in `π`. A
derivation in the paper's sense is the case `S = ∅`.

Paper: Section 9.1, "Frege systems". -/
def IsDerivation (R : List FregeRule) (Γ : Set (Formula V)) :
    Finset (Formula V) → List (Formula V) → Prop
  | _, [] => True
  | S, F :: π => (F ∈ Γ ∨ IsInference R S F) ∧ IsDerivation R Γ (insert F S) π

@[simp] theorem isDerivation_nil (R : List FregeRule) (Γ : Set (Formula V))
    (S : Finset (Formula V)) : IsDerivation R Γ S [] :=
  trivial

@[simp] theorem isDerivation_cons (R : List FregeRule) (Γ : Set (Formula V))
    (S : Finset (Formula V)) (F : Formula V) (π : List (Formula V)) :
    IsDerivation R Γ S (F :: π) ↔
      (F ∈ Γ ∨ IsInference R S F) ∧ IsDerivation R Γ (insert F S) π :=
  Iff.rfl

/-- Soundness of derivation sequences: if the rules are sound and `Γ` implies every formula of
`S`, then `Γ` implies every formula of the sequence. -/
theorem IsDerivation.implies {R : List FregeRule} (hR : ∀ r ∈ R, r.Sound) {Γ : Set (Formula V)}
    {S : Finset (Formula V)} {π : List (Formula V)} (h : IsDerivation R Γ S π)
    (hS : ∀ F ∈ S, Formula.Implies Γ F) : ∀ F ∈ π, Formula.Implies Γ F := by
  induction π generalizing S with
  | nil => simp
  | cons F π ih =>
    obtain ⟨hF, hπ⟩ := h
    have hF' : Formula.Implies Γ F := by
      rcases hF with hF | ⟨r, hr, σ, hprem, rfl⟩
      · exact Formula.implies_of_mem hF
      · intro α hα
        rw [Formula.eval_subst]
        exact hR r hr _ fun P hP => by
          rw [← Formula.eval_subst]
          exact hS _ (hprem P hP) α hα
    have hS' : ∀ D ∈ insert F S, Formula.Implies Γ D := by
      intro D hD
      rcases Finset.mem_insert.mp hD with rfl | hD
      · exact hF'
      · exact hS D hD
    intro D hD
    rcases List.mem_cons.mp hD with rfl | hD
    · exact hF'
    · exact ih hπ hS' D hD

/-- Monotonicity in the initial formulas. -/
theorem IsDerivation.mono {R : List FregeRule} {Γ Γ' : Set (Formula V)} (hΓ : Γ ⊆ Γ')
    {S : Finset (Formula V)} {π : List (Formula V)} (h : IsDerivation R Γ S π) :
    IsDerivation R Γ' S π := by
  induction π generalizing S with
  | nil => trivial
  | cons F π ih =>
    obtain ⟨hF, hπ⟩ := h
    exact ⟨hF.imp_left fun h => hΓ h, ih hπ⟩

/-- Prefixes of derivation sequences are derivation sequences. -/
theorem IsDerivation.append_left {R : List FregeRule} {Γ : Set (Formula V)}
    {S : Finset (Formula V)} {π₁ π₂ : List (Formula V)} (h : IsDerivation R Γ S (π₁ ++ π₂)) :
    IsDerivation R Γ S π₁ := by
  induction π₁ generalizing S with
  | nil => trivial
  | cons F π₁ ih =>
    obtain ⟨hF, hπ⟩ := h
    exact ⟨hF, ih hπ⟩

/-- Derivation sequences concatenate. -/
theorem IsDerivation.append {R : List FregeRule} {Γ : Set (Formula V)} {S : Finset (Formula V)}
    {π₁ π₂ : List (Formula V)} (h₁ : IsDerivation R Γ S π₁)
    (h₂ : IsDerivation R Γ (S ∪ π₁.toFinset) π₂) : IsDerivation R Γ S (π₁ ++ π₂) := by
  induction π₁ generalizing S with
  | nil => simpa using h₂
  | cons F π₁ ih =>
    obtain ⟨hF, hπ⟩ := h₁
    refine ⟨hF, ih hπ ?_⟩
    rw [Finset.insert_union, ← Finset.union_insert, ← List.toFinset_cons]
    exact h₂

/-- Monotonicity in the accumulator of available formulas. -/
theorem IsDerivation.mono_acc {R : List FregeRule} {Γ : Set (Formula V)}
    {S S' : Finset (Formula V)} (hS : S ⊆ S') {π : List (Formula V)}
    (h : IsDerivation R Γ S π) : IsDerivation R Γ S' π := by
  induction π generalizing S S' with
  | nil => trivial
  | cons F π ih =>
    obtain ⟨hF, hπ⟩ := h
    exact ⟨hF.imp_right (IsInference.mono hS), ih (Finset.insert_subset_insert F hS) hπ⟩

/-- Changing the initial formulas: in a derivation from `Γ`, the initial-formula steps whose
formulas lie in the accumulator `S` can be dropped, and the result is a derivation from any
`Γ'` containing the remaining initial formulas, of no greater total size and with the same
formulas outside `S`. -/
theorem IsDerivation.exists_drop_initial {R : List FregeRule} {Γ Γ' : Set (Formula V)}
    {S : Finset (Formula V)} {π : List (Formula V)} (h : IsDerivation R Γ S π)
    (hΓ : ∀ F ∈ π, F ∈ Γ → F ∈ S ∨ F ∈ Γ') :
    ∃ π' : List (Formula V), IsDerivation R Γ' S π' ∧
      (π'.map Formula.size).sum ≤ (π.map Formula.size).sum ∧
      (∀ F ∈ π', F ∈ π) ∧ ∀ F ∈ π, F ∈ S ∨ F ∈ π' := by
  induction π generalizing S with
  | nil => exact ⟨[], trivial, le_rfl, by simp, by simp⟩
  | cons F π ih =>
    obtain ⟨hF, hπ⟩ := h
    by_cases hFS : F ∈ S
    · rw [Finset.insert_eq_of_mem hFS] at hπ
      obtain ⟨π', h₁, h₂, h₃, h₄⟩ := ih hπ fun G hG => hΓ G (List.mem_cons_of_mem F hG)
      refine ⟨π', h₁, h₂.trans (by simp only [List.map_cons, List.sum_cons]; omega),
        fun G hG => List.mem_cons_of_mem F (h₃ G hG), fun G hG => ?_⟩
      rcases List.mem_cons.mp hG with rfl | hG
      · exact Or.inl hFS
      · exact h₄ G hG
    · have hF' : F ∈ Γ' ∨ IsInference R S F := by
        rcases hF with hFΓ | hinf
        · exact Or.inl ((hΓ F List.mem_cons_self hFΓ).resolve_left hFS)
        · exact Or.inr hinf
      obtain ⟨π', h₁, h₂, h₃, h₄⟩ := ih hπ fun G hG hGΓ =>
        (hΓ G (List.mem_cons_of_mem F hG) hGΓ).imp_left Finset.mem_insert_of_mem
      refine ⟨F :: π', ⟨hF', h₁⟩, ?_, fun G hG => ?_, fun G hG => ?_⟩
      · simp only [List.map_cons, List.sum_cons]
        omega
      · rcases List.mem_cons.mp hG with rfl | hG
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem F (h₃ G hG)
      · rcases List.mem_cons.mp hG with rfl | hG
        · exact Or.inr List.mem_cons_self
        · rcases h₄ G hG with hGS | hG'
          · rcases Finset.mem_insert.mp hGS with rfl | hGS
            · exact Or.inr List.mem_cons_self
            · exact Or.inl hGS
          · exact Or.inr (List.mem_cons_of_mem F hG')

/-- Changing the initial formulas: a derivation from `Γ` whose initial formulas all lie in the
accumulator `S` is, after dropping those initial-formula steps, a derivation from any `Γ'`, of
no greater total size, with the same formulas outside `S`. -/
theorem IsDerivation.exists_of_initial_mem_acc {R : List FregeRule} {Γ Γ' : Set (Formula V)}
    {S : Finset (Formula V)} {π : List (Formula V)} (h : IsDerivation R Γ S π)
    (hΓ : ∀ F ∈ π, F ∈ Γ → F ∈ S) :
    ∃ π' : List (Formula V), IsDerivation R Γ' S π' ∧
      (π'.map Formula.size).sum ≤ (π.map Formula.size).sum ∧
      (∀ F ∈ π', F ∈ π) ∧ ∀ F ∈ π, F ∈ S ∨ F ∈ π' :=
  h.exists_drop_initial fun F hF hFΓ => Or.inl (hΓ F hF hFΓ)

/-- A Frege derivation of `G` from `Γ` in the system with rules `R`: a sequence of formulas,
each in `Γ` or following from earlier ones by a rule, whose last formula is `G`.

Paper: Section 9.1, "Frege systems". -/
structure Derivation (R : List FregeRule) (Γ : Set (Formula V)) (G : Formula V) where
  /-- The formulas of the derivation, in derivation order. -/
  lines : List (Formula V)
  /-- Each formula is in `Γ` or follows from earlier formulas by a rule. -/
  isDerivation : IsDerivation R Γ ∅ lines
  /-- The last formula is `G`. -/
  getLast?_lines : lines.getLast? = some G

/-- A Frege refutation of `Γ`: a derivation of `⊥`.

Paper: Section 9.1, "Frege systems". -/
abbrev Refutation (R : List FregeRule) (Γ : Set (Formula V)) := Derivation R Γ Formula.bot

namespace Derivation

variable {R : List FregeRule} {Γ : Set (Formula V)} {G : Formula V}

/-- The size of a derivation: the total size of its formulas.

Paper: Section 9.1, "Frege systems". -/
def size (π : Derivation R Γ G) : ℕ := (π.lines.map Formula.size).sum

/-- The depth of a derivation: the maximum depth of its formulas.

Paper: Section 9.1, "Frege systems". -/
def depth (π : Derivation R Γ G) : ℕ := π.lines.toFinset.sup Formula.depth

theorem lines_ne_nil (π : Derivation R Γ G) : π.lines ≠ [] := by
  intro h
  have := π.getLast?_lines
  rw [h] at this
  simp at this

theorem mem_lines (π : Derivation R Γ G) : G ∈ π.lines :=
  List.mem_of_getLast? π.getLast?_lines

theorem size_le_size {π : Derivation R Γ G} {F : Formula V} (h : F ∈ π.lines) :
    F.size ≤ π.size :=
  List.le_sum_of_mem (List.mem_map_of_mem h)

theorem size_pos (π : Derivation R Γ G) : 0 < π.size :=
  (G.size_pos).trans_le (size_le_size π.mem_lines)

theorem depth_le_depth {π : Derivation R Γ G} {F : Formula V} (h : F ∈ π.lines) :
    F.depth ≤ π.depth :=
  Finset.le_sup (f := Formula.depth) (List.mem_toFinset.mpr h)

theorem depth_le_iff {π : Derivation R Γ G} {d : ℕ} : π.depth ≤ d ↔ ∀ F ∈ π.lines, F.depth ≤ d := by
  simp [depth, Finset.sup_le_iff]

/-- Soundness: a derived formula is implied by `Γ`. -/
theorem implies (hR : ∀ r ∈ R, r.Sound) (π : Derivation R Γ G) : Formula.Implies Γ G :=
  π.isDerivation.implies hR (by simp) G π.mem_lines

/-- The one-line derivation of an initial formula. -/
def single (h : G ∈ Γ) : Derivation R Γ G where
  lines := [G]
  isDerivation := ⟨Or.inl h, trivial⟩
  getLast?_lines := rfl

@[simp] theorem size_single (h : G ∈ Γ) : (single (R := R) h).size = G.size := by
  simp [size, single]

@[simp] theorem depth_single (h : G ∈ Γ) : (single (R := R) h).depth = G.depth := by
  simp [depth, single]

/-- Monotonicity in the initial formulas. -/
def mono {Γ' : Set (Formula V)} (hΓ : Γ ⊆ Γ') (π : Derivation R Γ G) : Derivation R Γ' G where
  lines := π.lines
  isDerivation := π.isDerivation.mono hΓ
  getLast?_lines := π.getLast?_lines

@[simp] theorem size_mono {Γ' : Set (Formula V)} (hΓ : Γ ⊆ Γ') (π : Derivation R Γ G) :
    (π.mono hΓ).size = π.size := rfl

@[simp] theorem depth_mono {Γ' : Set (Formula V)} (hΓ : Γ ⊆ Γ') (π : Derivation R Γ G) :
    (π.mono hΓ).depth = π.depth := rfl

/-- Changing the conclusion along an equality. -/
def copy (π : Derivation R Γ G) {G' : Formula V} (h : G = G') : Derivation R Γ G' where
  lines := π.lines
  isDerivation := π.isDerivation
  getLast?_lines := h ▸ π.getLast?_lines

@[simp] theorem lines_copy (π : Derivation R Γ G) {G' : Formula V} (h : G = G') :
    (π.copy h).lines = π.lines := rfl

@[simp] theorem size_copy (π : Derivation R Γ G) {G' : Formula V} (h : G = G') :
    (π.copy h).size = π.size := rfl

@[simp] theorem depth_copy (π : Derivation R Γ G) {G' : Formula V} (h : G = G') :
    (π.copy h).depth = π.depth := rfl

/-- Every formula of a derivation sequence has a derivation, of no greater size and depth. -/
theorem exists_of_mem {π : List (Formula V)} (h : IsDerivation R Γ ∅ π) {F : Formula V}
    (hF : F ∈ π) :
    ∃ δ : Derivation R Γ F, δ.size ≤ (π.map Formula.size).sum ∧
      ∀ F' ∈ δ.lines, F' ∈ π := by
  obtain ⟨π₁, π₂, rfl⟩ := List.append_of_mem hF
  rw [List.append_cons] at h
  refine ⟨⟨π₁ ++ [F], h.append_left, by simp⟩, ?_, ?_⟩
  · simp only [size, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
      List.map_nil, List.sum_nil]
    omega
  · intro F' hF'
    rw [List.append_cons]
    exact List.mem_append_left _ hF'

/-- **Cut.** A derivation of `A` from `Γ` followed by a derivation of `B` from `Γ` and `A` give a
derivation of `B` from `Γ` of size at most the sum of the sizes, all of whose formulas occur in
one of the two derivations: the steps of the second derivation that use `A` as an initial
formula are already derived. -/
theorem exists_trans {A B : Formula V} (δ₁ : Derivation R Γ A)
    (δ₂ : Derivation R (insert A Γ) B) :
    ∃ δ : Derivation R Γ B, δ.size ≤ δ₁.size + δ₂.size ∧
      ∀ F ∈ δ.lines, F ∈ δ₁.lines ∨ F ∈ δ₂.lines := by
  obtain ⟨π₂, hπ₂, hsize₂, hsub₂, hmem₂⟩ := (δ₂.isDerivation.mono_acc
    (Finset.empty_subset δ₁.lines.toFinset)).exists_drop_initial (Γ' := Γ) fun F _ hF => by
      rcases Set.mem_insert_iff.mp hF with rfl | hF
      · exact Or.inl (List.mem_toFinset.mpr δ₁.mem_lines)
      · exact Or.inr hF
  have hfull : IsDerivation R Γ ∅ (δ₁.lines ++ π₂) :=
    δ₁.isDerivation.append (by rwa [Finset.empty_union])
  have hB : B ∈ δ₁.lines ++ π₂ := by
    rcases hmem₂ _ δ₂.mem_lines with h0 | h0
    · exact List.mem_append_left _ (List.mem_toFinset.mp h0)
    · exact List.mem_append_right _ h0
  obtain ⟨δ, hδs, hδl⟩ := exists_of_mem hfull hB
  refine ⟨δ, ?_, fun F hF => ?_⟩
  · rw [List.map_append, List.sum_append] at hδs
    exact hδs.trans (Nat.add_le_add_left hsize₂ _)
  · rcases List.mem_append.mp (hδl F hF) with hF | hF
    · exact Or.inl hF
    · exact Or.inr (hsub₂ F hF)

/-- **Cut, with bounds.** A derivation of `A` from `Γ` and one of `B` from `A` alone give a
derivation of `B` from `Γ` whose size is at most the sum of the sizes and whose depth is at
most any common bound on the two depths: every line comes from one of the two derivations. -/
theorem exists_trans_le {A B : Formula V} (δ₁ : Derivation R Γ A) (δ₂ : Derivation R {A} B)
    {d : ℕ} (hd₁ : δ₁.depth ≤ d) (hd₂ : δ₂.depth ≤ d) :
    ∃ δ : Derivation R Γ B, δ.depth ≤ d ∧ δ.size ≤ δ₁.size + δ₂.size := by
  have hsub : ({A} : Set (Formula V)) ⊆ insert A Γ :=
    Set.singleton_subset_iff.mpr (Set.mem_insert _ _)
  obtain ⟨δ, hδs, hδl⟩ := δ₁.exists_trans (δ₂.mono hsub)
  rw [size_mono] at hδs
  refine ⟨δ, depth_le_iff.mpr fun F hF => ?_, hδs⟩
  rcases hδl F hF with hF | hF
  · exact (δ₁.depth_le_depth hF).trans hd₁
  · exact ((δ₂.mono hsub).depth_le_depth hF).trans (by rwa [depth_mono])

end Derivation

/-- A set of formulas with a refutation in a sound system is unsatisfiable. -/
theorem Refutation.not_sat {R : List FregeRule} (hR : ∀ r ∈ R, r.Sound) {Γ : Set (Formula V)}
    (π : Refutation R Γ) : ¬ ∃ α : V → Bool, ∀ F ∈ Γ, F.eval α = true := by
  rintro ⟨α, hα⟩
  have := π.implies hR α hα
  simp at this

/-- Concatenating derivations: derivations from `Γ'` of the formulas of a list `L`, each of
size at most `K` times its formula and of depth at most `D`, concatenate to a derivation
sequence from `Γ'` containing every formula of `L`, of total size at most `K` times the total
size of `L` and with all formulas of depth at most `D`. -/
theorem exists_isDerivation_concat {R : List FregeRule} {Γ' : Set (Formula V)} {K D : ℕ}
    (L : List (Formula V))
    (h : ∀ F ∈ L, ∃ δ : Derivation R Γ' F, δ.size ≤ K * F.size ∧ δ.depth ≤ D) :
    ∃ π₀ : List (Formula V), IsDerivation R Γ' ∅ π₀ ∧
      (π₀.map Formula.size).sum ≤ K * (L.map Formula.size).sum ∧
      (∀ F ∈ π₀, F.depth ≤ D) ∧ ∀ F ∈ L, F ∈ π₀ := by
  induction L with
  | nil => exact ⟨[], trivial, by simp, by simp, by simp⟩
  | cons F L ih =>
    obtain ⟨δ, hδs, hδd⟩ := h F List.mem_cons_self
    obtain ⟨π₀, h₁, h₂, h₃, h₄⟩ := ih fun G hG => h G (List.mem_cons_of_mem F hG)
    refine ⟨δ.lines ++ π₀, δ.isDerivation.append (h₁.mono_acc (Finset.empty_subset _)), ?_,
      fun G hG => ?_, fun G hG => ?_⟩
    · rw [List.map_append, List.sum_append, List.map_cons, List.sum_cons, Nat.mul_add]
      exact Nat.add_le_add hδs h₂
    · rcases List.mem_append.mp hG with hG | hG
      · exact (δ.depth_le_depth hG).trans hδd
      · exact h₃ G hG
    · rcases List.mem_cons.mp hG with rfl | hG
      · exact List.mem_append_left _ δ.mem_lines
      · exact List.mem_append_right _ (h₄ G hG)

/-- **The Compose step.** If `Γ` has a refutation `π` and every initial formula `F` of `π` has
a derivation from `Γ'` of size at most `K |F|` and depth at most `D`, then `Γ'` has a
refutation of size at most `(K + 1) |π|` and depth at most `max(depth π, D)`: derive the
initial formulas first, then run `π` on them.

Paper: Section 6.1, Compose, as used in the proof of Lemma [lem:frege-transfer]. -/
theorem Refutation.compose {R : List FregeRule} {Γ Γ' : Set (Formula V)} (π : Refutation R Γ)
    {K D : ℕ} (h : ∀ F ∈ π.lines, F ∈ Γ →
      ∃ δ : Derivation R Γ' F, δ.size ≤ K * F.size ∧ δ.depth ≤ D) :
    ∃ π' : Refutation R Γ', π'.size ≤ (K + 1) * π.size ∧ π'.depth ≤ max π.depth D := by
  classical
  -- derivations of the initial formulas that `π` uses
  obtain ⟨π₀, hπ₀, hsize₀, hdepth₀, hmem₀⟩ := exists_isDerivation_concat
    (π.lines.filter fun F => decide (F ∈ Γ)) fun F hF => by
      rw [List.mem_filter, decide_eq_true_eq] at hF
      exact h F hF.1 hF.2
  -- `π` runs on them: its initial-formula steps are already derived
  obtain ⟨π₂, hπ₂, hsize₂, hsub₂, hmem₂⟩ := (π.isDerivation.mono_acc
    (Finset.empty_subset π₀.toFinset)).exists_of_initial_mem_acc (Γ' := Γ') fun F hF hFΓ =>
      List.mem_toFinset.mpr (hmem₀ F (List.mem_filter.mpr ⟨hF, decide_eq_true hFΓ⟩))
  have hfull : IsDerivation R Γ' ∅ (π₀ ++ π₂) := hπ₀.append (by rwa [Finset.empty_union])
  have hbot : Formula.bot ∈ π₀ ++ π₂ := by
    rcases hmem₂ _ π.mem_lines with h0 | h0
    · exact List.mem_append_left _ (List.mem_toFinset.mp h0)
    · exact List.mem_append_right _ h0
  obtain ⟨π', hπ's, hπ'l⟩ := Derivation.exists_of_mem hfull hbot
  refine ⟨π', ?_, ?_⟩
  · have hA : ((π.lines.filter fun F => decide (F ∈ Γ)).map Formula.size).sum ≤ π.size :=
      List.Sublist.sum_le_sum (List.filter_sublist.map Formula.size) fun _ _ => Nat.zero_le _
    rw [List.map_append, List.sum_append] at hπ's
    calc π'.size ≤ (π₀.map Formula.size).sum + (π₂.map Formula.size).sum := hπ's
      _ ≤ K * π.size + π.size :=
          Nat.add_le_add (hsize₀.trans (Nat.mul_le_mul_left K hA)) hsize₂
      _ = (K + 1) * π.size := by ring
  · rw [Derivation.depth_le_iff]
    intro F hF
    rcases List.mem_append.mp (hπ'l F hF) with hF | hF
    · exact (hdepth₀ F hF).trans (le_max_right _ _)
    · exact (π.depth_le_depth (hsub₂ F hF)).trans (le_max_left _ _)

/-- Implicational completeness (Cook–Reckhow): a formula implied by finitely many formulas has
a derivation from them. Stated over the variables `Fin k`; renaming, a substitution, gives the
general case.

Paper: Section 9.1, "Frege systems". -/
def Complete (R : List FregeRule) : Prop :=
  ∀ (k : ℕ) (Γ : Finset (Formula (Fin k))) (G : Formula (Fin k)),
    Formula.Implies (↑Γ) G → Nonempty (Derivation R (↑Γ) G)

end Frege

/-- A Frege system: a finite list of sound inference rules that is implicationally complete.

Paper: Section 9.1, "Frege systems". -/
structure FregeSystem where
  /-- The inference rules. -/
  rules : List FregeRule
  /-- Every rule is sound. -/
  sound : ∀ r ∈ rules, r.Sound
  /-- The rules are implicationally complete. -/
  complete : Frege.Complete rules

namespace FregeSystem

variable (𝓕 : FregeSystem) {V : Type*} [DecidableEq V]

/-- A derivation in the system `𝓕`. -/
abbrev Derivation (Γ : Set (Formula V)) (G : Formula V) := Frege.Derivation 𝓕.rules Γ G

/-- A refutation in the system `𝓕`. -/
abbrev Refutation (Γ : Set (Formula V)) := Frege.Refutation 𝓕.rules Γ

/-- Soundness of the system: a derived formula is implied by `Γ`. -/
theorem implies {Γ : Set (Formula V)} {G : Formula V} (π : 𝓕.Derivation Γ G) :
    Formula.Implies Γ G :=
  π.implies 𝓕.sound

/-- A set of formulas with a refutation in `𝓕` is unsatisfiable. -/
theorem not_sat_of_refutation {Γ : Set (Formula V)} (π : 𝓕.Refutation Γ) :
    ¬ ∃ α : V → Bool, ∀ F ∈ Γ, F.eval α = true :=
  π.not_sat 𝓕.sound

end FregeSystem

end AssocLB
