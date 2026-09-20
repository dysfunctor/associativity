/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/
import AssocLB.Resolution.Completeness

/-!
# The size–width tradeoff

Paper: Section 2 (Preliminaries), Theorem [thm:bw] (Ben-Sasson and Wigderson): for an
unsatisfiable CNF `Φ` with `N` variables,
`size_Res(Φ) ≥ exp(Ω((w(Φ ⊢ ⊥) - w(Φ))² / N))`.

## Main definitions

* `BWTradeoff`: Theorem [thm:bw] as a proposition, in its width-upper-bound form: there is an
  absolute constant `c > 0` such that for every CNF `Φ` over `N` variables, every refutation
  of size `S` can be replaced by one of width at most `w(Φ) + √(c N log S)`.
* `Restriction.ofLit m`: the restriction setting the literal `m` to `1`.

## Main results

* `IsDerivation.exists_simulation_sublist`: the simulation of Lemma [lem:substitution] with a
  line-by-line correspondence: the simulating sequence is obtained from a sublist of the
  original by replacing each clause `C` by a subclause of `C^σ ∪ W`. It gives width bounds
  and bounds on the number of clauses with a given property.
* `Refutation.exists_restrict_width`: restricting a refutation does not increase its width and
  keeps at most the surviving clauses of any given width.
* `Refutation.exists_lift_width`: lifting a refutation of `Φ↾ρ` to a derivation from `Φ`
  increases the width by at most the number of literals added back.
* `Refutation.exists_of_unit`: a derivation of a unit clause `{m}` and a refutation of
  `Φ↾(m := 1)` combine into a refutation of `Φ` of no larger width.
* `exists_literal_fat`: some literal occurs in at least a `d / 2N` fraction of the clauses
  of width more than `d` of a sequence.
* `exists_width_le_of_fat`: the induction of Ben-Sasson and Wigderson: a refutation with
  fewer than `(1 - d/2N)^{-b}` clauses of width more than `d` yields one of width at most
  `w(Φ) + d + b`.
* `bwTradeoff`: Theorem [thm:bw], with the constant `c = 32`.

## Design notes

* The proof follows Ben-Sasson and Wigderson, *Short proofs are narrow*, Theorem 3.5. The
  induction is on the number of variables of `Φ`, over the fixed variable type `V`, so the
  averaging always counts `2|V|` literals.
* Clauses of width more than `d` are counted with multiplicity, as `List.countP` over the
  sequence of the refutation; only upper bounds are used.
-/

namespace AssocLB

variable {V : Type*}

/-! ### Counting along a line-by-line correspondence -/

theorem forall₂_countP_le {α β : Type*} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) {p : β → Bool} {q : α → Bool}
    (hpq : ∀ a b, R a b → p b = true → q a = true) : l₂.countP p ≤ l₁.countP q := by
  induction h with
  | nil => simp
  | @cons a b l₁ l₂ hab _ ih =>
    rw [List.countP_cons, List.countP_cons]
    by_cases hp : p b = true
    · rw [if_pos hp, if_pos (hpq a b hab hp)]
      omega
    · rw [if_neg hp]
      split_ifs <;> omega

theorem forall₂_exists_of_mem {α β : Type*} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) {b : β} (hb : b ∈ l₂) : ∃ a ∈ l₁, R a b := by
  induction h with
  | nil => simp at hb
  | @cons a b' l₁ l₂ hab _ ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨a, List.mem_cons_self, hab⟩
    · obtain ⟨a', ha', h'⟩ := ih hb
      exact ⟨a', List.mem_cons_of_mem _ ha', h'⟩

/-! ### The simulation, line by line -/

section Simulation

variable [DecidableEq V] {V' : Type*} [DecidableEq V']

/-- The simulation of Lemma [lem:substitution], line by line. Let `π` be a derivation from
`Φ` with the clauses of `S` available, and let the initial clauses of `π` surviving `σ` have
subclauses of `C^σ ∪ W` in `Ψ`, in the available clauses `S₀ ⊆ S'`, or as resolvents of
clauses of `S₀`. If every surviving clause of `S` has a subclause of `C^σ ∪ W` in `S'`, then
`Ψ` has a derivation `π'` with the clauses of `S'` available, obtained from a sublist `π₀` of `π`
by replacing each clause `C` by a subclause of `C^σ ∪ W`, that together with `S'` contains a
subclause of `C^σ ∪ W` for every surviving clause `C` of `π`. -/
theorem IsDerivation.exists_simulation_sublist (σ : Subst V V') (W : Clause V') {Φ : CNF V}
    {Ψ : CNF V'} {π : List (Clause V)} {S : Finset (Clause V)} {S₀ S' : Finset (Clause V')}
    (h : IsDerivation Φ S π) (hS₀ : S₀ ⊆ S')
    (hΦ : ∀ C ∈ π, C ∈ Φ → Clause.SurvivesUnder σ C → ∃ D ⊆ C.subst σ ∪ W,
      D ∈ Ψ ∨ D ∈ S₀ ∨ ∃ D₁ ∈ S₀, ∃ D₂ ∈ S₀, Clause.IsResolvent D D₁ D₂)
    (hS : ∀ C ∈ S, Clause.SurvivesUnder σ C → ∃ D ∈ S', D ⊆ C.subst σ ∪ W) :
    ∃ π₀ : List (Clause V), ∃ π' : List (Clause V'), π₀.Sublist π ∧
      List.Forall₂ (fun C D => Clause.SurvivesUnder σ C ∧ D ⊆ C.subst σ ∪ W) π₀ π' ∧
      IsDerivation Ψ S' π' ∧
      ∀ C ∈ π, Clause.SurvivesUnder σ C → ∃ D, (D ∈ S' ∨ D ∈ π') ∧ D ⊆ C.subst σ ∪ W := by
  induction π generalizing S S' with
  | nil => exact ⟨[], [], List.Sublist.refl _, List.Forall₂.nil, trivial, by simp⟩
  | cons C π ih =>
    obtain ⟨hC, hπ⟩ := h
    have hΦ' : ∀ C' ∈ π, C' ∈ Φ → Clause.SurvivesUnder σ C' → ∃ D ⊆ C'.subst σ ∪ W,
        D ∈ Ψ ∨ D ∈ S₀ ∨ ∃ D₁ ∈ S₀, ∃ D₂ ∈ S₀, Clause.IsResolvent D D₁ D₂ :=
      fun C' hC' => hΦ C' (List.mem_cons_of_mem _ hC')
    by_cases hsurv : Clause.SurvivesUnder σ C
    · have hD : ∃ D ⊆ C.subst σ ∪ W,
          D ∈ S' ∨ D ∈ Ψ ∨ ∃ D₁ ∈ S', ∃ D₂ ∈ S', Clause.IsResolvent D D₁ D₂ := by
        rcases hC with hC | hC
        · obtain ⟨D, hDsub, hD⟩ := hΦ C List.mem_cons_self hC hsurv
          refine ⟨D, hDsub, ?_⟩
          rcases hD with hD | hD | ⟨D₁, h₁, D₂, h₂, hres⟩
          · exact Or.inr (Or.inl hD)
          · exact Or.inl (hS₀ hD)
          · exact Or.inr (Or.inr ⟨D₁, hS₀ h₁, D₂, hS₀ h₂, hres⟩)
        · obtain ⟨D, hDsub, hD⟩ := Clause.exists_step σ W hS hsurv hC
          exact ⟨D, hDsub, hD.imp_right Or.inr⟩
      obtain ⟨D, hDsub, hD⟩ := hD
      rcases hD with hD | hD
      · obtain ⟨π₀, π', hsub, hall, hπ', hcov⟩ := ih hπ hS₀ hΦ' (S' := S') (by
          intro C' hC' hs'
          rcases Finset.mem_insert.mp hC' with rfl | hC'
          · exact ⟨D, hD, hDsub⟩
          · exact hS C' hC' hs')
        refine ⟨π₀, π', hsub.cons C, hall, hπ', ?_⟩
        intro C' hC' hs'
        rcases List.mem_cons.mp hC' with rfl | hC'
        · exact ⟨D, Or.inl hD, hDsub⟩
        · exact hcov C' hC' hs'
      · obtain ⟨π₀, π', hsub, hall, hπ', hcov⟩ := ih hπ (hS₀.trans (Finset.subset_insert D S'))
          hΦ' (S' := insert D S') (by
          intro C' hC' hs'
          rcases Finset.mem_insert.mp hC' with rfl | hC'
          · exact ⟨D, Finset.mem_insert_self _ _, hDsub⟩
          · obtain ⟨D', hD', hD'sub⟩ := hS C' hC' hs'
            exact ⟨D', Finset.mem_insert_of_mem hD', hD'sub⟩)
        refine ⟨C :: π₀, D :: π', hsub.cons_cons C, List.Forall₂.cons ⟨hsurv, hDsub⟩ hall,
          ⟨hD, hπ'⟩, ?_⟩
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
    · obtain ⟨π₀, π', hsub, hall, hπ', hcov⟩ := ih hπ hS₀ hΦ' (S' := S') (by
        intro C' hC' hs'
        rcases Finset.mem_insert.mp hC' with rfl | hC'
        · exact absurd hs' hsurv
        · exact hS C' hC' hs')
      refine ⟨π₀, π', hsub.cons C, hall, hπ', ?_⟩
      intro C' hC' hs'
      rcases List.mem_cons.mp hC' with rfl | hC'
      · exact absurd hs' hsurv
      · exact hcov C' hC' hs'

end Simulation

/-! ### Width bookkeeping for derivations -/

namespace Derivation

variable [DecidableEq V] {Φ : CNF V} {C : Clause V}

/-- A clause of a derivation sequence has a derivation whose sequence is a sublist of it: the
prefix ending at the clause. -/
theorem exists_of_mem_sublist {π : List (Clause V)} (h : IsDerivation Φ ∅ π) {D : Clause V}
    (hD : D ∈ π) : ∃ π' : Derivation Φ D, π'.lines.Sublist π := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hD
  refine ⟨⟨s ++ [D], ?_, List.getLast?_concat⟩, ?_⟩
  · have h' : IsDerivation Φ ∅ ((s ++ [D]) ++ t) := by simpa using h
    exact h'.append_left
  · exact ((List.nil_sublist t).cons_cons D).append_left s

theorem width_le (π : Derivation Φ C) {k : ℕ} (h : ∀ D ∈ π.lines, D.card ≤ k) :
    π.width ≤ k :=
  Finset.sup_le fun D hD => h D (List.mem_toFinset.mp hD)

/-- The width is at most `k` when no clause of the derivation has width more than `k`. -/
theorem width_le_of_countP_eq_zero (π : Derivation Φ C) {k : ℕ}
    (h : (π.lines.countP fun D => decide (k < D.card)) = 0) : π.width ≤ k :=
  π.width_le fun D hD => by
    have := List.countP_eq_zero.mp h D hD
    simpa using this

theorem countP_gt_width_eq_zero (π : Derivation Φ C) :
    (π.lines.countP fun D => decide (π.width < D.card)) = 0 :=
  List.countP_eq_zero.mpr fun D hD => by simpa using π.card_le_width hD

end Derivation

section Width

variable [DecidableEq V]

/-- **Restriction with width bookkeeping.** A refutation restricted by `ρ` has at most the
same width, and for every `d` at most as many clauses of width more than `d` as the original
refutation has surviving clauses of width more than `d`. -/
theorem Refutation.exists_restrict_width {Φ : CNF V} (π : Refutation Φ) (ρ : Restriction V) :
    ∃ π' : Refutation (Φ.restrict ρ), π'.width ≤ π.width ∧
      ∀ d : ℕ, (π'.lines.countP fun D => decide (d < D.card)) ≤
        π.lines.countP fun C => decide (C.Survives ρ ∧ d < C.card) := by
  obtain ⟨π₀, π₁, hsub, hall, hπ₁, hcov⟩ := π.isDerivation.exists_simulation_sublist
    ρ.toSubst ∅ (Ψ := Φ.subst ρ.toSubst) (S₀ := ∅) (S' := ∅) (Finset.Subset.refl _)
    (fun C _ hC hs => ⟨C.subst ρ.toSubst, Finset.subset_union_left,
      Or.inl (CNF.mem_subst.mpr ⟨C, hC, hs, rfl⟩)⟩) (by simp)
  obtain ⟨D, hD, hDsub⟩ := hcov ∅ π.mem_lines (Clause.survivesUnder_empty _)
  rw [Clause.subst_empty, Finset.empty_union, Finset.subset_empty] at hDsub
  subst hDsub
  rcases hD with hD | hD
  · exact absurd hD (Finset.notMem_empty _)
  obtain ⟨π', hπ'⟩ := Derivation.exists_of_mem_sublist hπ₁ hD
  have hcount : ∀ d : ℕ, (π'.lines.countP fun D => decide (d < D.card)) ≤
      π.lines.countP fun C => decide (C.Survives ρ ∧ d < C.card) := by
    intro d
    calc (π'.lines.countP fun D => decide (d < D.card))
        ≤ π₁.countP fun D => decide (d < D.card) := hπ'.countP_le
      _ ≤ π₀.countP fun C => decide (C.Survives ρ ∧ d < C.card) := by
          refine forall₂_countP_le hall ?_
          intro C D ⟨hs, hDsub⟩ hp
          simp only [decide_eq_true_eq] at hp ⊢
          refine ⟨fun hsat => hs.1 ((Clause.satUnder_toSubst_iff ρ C).mpr hsat), ?_⟩
          rw [Finset.union_empty] at hDsub
          exact lt_of_lt_of_le hp ((Finset.card_le_card hDsub).trans (Clause.card_subst_le _ _))
      _ ≤ _ := hsub.countP_le
  refine ⟨π'.mono (CNF.subst_toSubst_subset ρ Φ), ?_, hcount⟩
  refine Derivation.width_le_of_countP_eq_zero _ (Nat.eq_zero_of_le_zero ?_)
  calc _ ≤ π.lines.countP fun C => decide (C.Survives ρ ∧ π.width < C.card) := hcount π.width
    _ ≤ π.lines.countP fun C => decide (π.width < C.card) :=
        List.countP_mono_left fun C _ h => by simpa using (by simpa using h : _ ∧ _).2
    _ = 0 := π.countP_gt_width_eq_zero

/-- **Lifting with width bookkeeping.** A refutation of `Φ↾ρ` lifts to a derivation from `Φ`
of a subclause of any clause `W` containing the literals of `Φ` falsified by `ρ`, of width at
most the width of the refutation plus `|W|`. -/
theorem Refutation.exists_lift_width {Φ : CNF V} {ρ : Restriction V}
    (π : Refutation (Φ.restrict ρ)) (W : Clause V)
    (hW : ∀ C ∈ Φ, ∀ l ∈ C, l.FalsifiedBy ρ → l ∈ W) :
    ∃ D ⊆ W, ∃ π' : Derivation Φ D, π'.width ≤ π.width + W.card := by
  have hΦ : ∀ E ∈ π.lines, E ∈ Φ.restrict ρ → Clause.SurvivesUnder (Subst.id V) E →
      ∃ D ⊆ E.subst (Subst.id V) ∪ W, D ∈ Φ ∨ D ∈ (∅ : Finset (Clause V)) ∨
        ∃ D₁ ∈ (∅ : Finset (Clause V)), ∃ D₂ ∈ (∅ : Finset (Clause V)),
          Clause.IsResolvent D D₁ D₂ := by
    intro E _ hE _
    obtain ⟨C, hC, -, rfl⟩ := CNF.mem_restrict.mp hE
    refine ⟨C, ?_, Or.inl hC⟩
    rw [Clause.subst_id]
    intro l hl
    by_cases hf : l.FalsifiedBy ρ
    · exact Finset.mem_union_right _ (hW C hC l hl hf)
    · exact Finset.mem_union_left _ (Clause.mem_restrict.mpr ⟨hl, hf⟩)
  obtain ⟨π₀, π₁, hsub, hall, hπ₁, hcov⟩ := π.isDerivation.exists_simulation_sublist
    (Subst.id V) W (Ψ := Φ) (S₀ := ∅) (S' := ∅) (Finset.Subset.refl _) hΦ (by simp)
  obtain ⟨D, hD, hDsub⟩ := hcov ∅ π.mem_lines (Clause.survivesUnder_empty _)
  rw [Clause.subst_empty, Finset.empty_union] at hDsub
  rcases hD with hD | hD
  · exact absurd hD (Finset.notMem_empty _)
  obtain ⟨π', hπ'⟩ := Derivation.exists_of_mem_sublist hπ₁ hD
  refine ⟨D, hDsub, π', Derivation.width_le_of_countP_eq_zero π' (Nat.eq_zero_of_le_zero ?_)⟩
  calc (π'.lines.countP fun E => decide (π.width + W.card < E.card))
      ≤ π₁.countP fun E => decide (π.width + W.card < E.card) := hπ'.countP_le
    _ ≤ π₀.countP fun C => decide (π.width < C.card) := by
        refine forall₂_countP_le hall ?_
        intro C E ⟨_, hE⟩ hp
        simp only [decide_eq_true_eq] at hp ⊢
        have h1 : E.card ≤ (C.subst (Subst.id V) ∪ W).card := Finset.card_le_card hE
        have h2 : (C.subst (Subst.id V) ∪ W).card ≤ C.card + W.card := by
          rw [Clause.subst_id]
          exact Finset.card_union_le _ _
        omega
    _ ≤ π.lines.countP fun C => decide (π.width < C.card) := hsub.countP_le
    _ = 0 := π.countP_gt_width_eq_zero

end Width

/-! ### Restrictions of a single literal -/

/-- The restriction setting the literal `m` to `1` and nothing else. -/
def Restriction.ofLit [DecidableEq V] (m : Literal V) : Restriction V :=
  Restriction.single m.var m.sign

variable [DecidableEq V]

theorem Literal.satBy_ofLit_iff (m l : Literal V) : l.SatBy (Restriction.ofLit m) ↔ l = m := by
  unfold Literal.SatBy Restriction.ofLit Restriction.single
  rcases l with ⟨v, s⟩
  rcases m with ⟨w, t⟩
  simp only [Literal.mk.injEq]
  split_ifs with h
  · simp [h, eq_comm]
  · simp [h]

theorem Literal.falsifiedBy_ofLit_iff (m l : Literal V) :
    l.FalsifiedBy (Restriction.ofLit m) ↔ l = mᶜ := by
  rw [← Literal.satBy_compl_iff, Literal.satBy_ofLit_iff]
  constructor
  · rintro rfl
    simp
  · rintro rfl
    simp

theorem Clause.survives_ofLit_iff (m : Literal V) (C : Clause V) :
    C.Survives (Restriction.ofLit m) ↔ m ∉ C := by
  simp [Clause.Survives, Clause.SatBy, Literal.satBy_ofLit_iff]

theorem Clause.restrict_ofLit (m : Literal V) (C : Clause V) :
    C.restrict (Restriction.ofLit m) = C.erase mᶜ := by
  ext l
  simp [Clause.mem_restrict, Literal.falsifiedBy_ofLit_iff, Finset.mem_erase, and_comm]

/-- Restricting a literal removes its variable from the formula. -/
theorem CNF.vars_restrict_ofLit_subset (m : Literal V) (Φ : CNF V) :
    (Φ.restrict (Restriction.ofLit m)).vars ⊆ Φ.vars.erase m.var := by
  intro v hv
  obtain ⟨D, hD, l, hl, rfl⟩ := CNF.mem_vars.mp hv
  obtain ⟨C, hC, hsurv, rfl⟩ := CNF.mem_restrict.mp hD
  rw [Clause.mem_restrict, Literal.falsifiedBy_ofLit_iff] at hl
  rw [Clause.survives_ofLit_iff] at hsurv
  refine Finset.mem_erase.mpr ⟨?_, CNF.mem_vars.mpr ⟨C, hC, l, hl.1, rfl⟩⟩
  intro hvar
  rcases l with ⟨v, s⟩
  rcases m with ⟨w, t⟩
  simp only at hvar
  subst hvar
  cases s <;> cases t <;> simp_all

theorem CNF.width_restrict_le (ρ : Restriction V) (Φ : CNF V) :
    (Φ.restrict ρ).width ≤ Φ.width := by
  refine Finset.sup_le fun D hD => ?_
  obtain ⟨C, hC, -, rfl⟩ := CNF.mem_restrict.mp hD
  exact (Finset.card_le_card (Clause.restrict_subset ρ C)).trans (CNF.card_le_width hC)

theorem isDerivation_of_forall_mem {Φ : CNF V} (S : Finset (Clause V)) :
    ∀ L : List (Clause V), (∀ C ∈ L, C ∈ Φ) → IsDerivation Φ S L
  | [], _ => trivial
  | C :: L, h => ⟨Or.inl (h C List.mem_cons_self),
      isDerivation_of_forall_mem _ L fun C' hC' => h C' (List.mem_cons_of_mem _ hC')⟩

/-- **Combining a unit clause with a restricted refutation.** A derivation from `Φ` of the
unit clause `{m}` and a refutation of `Φ↾(m := 1)` give a refutation of `Φ`, of width at most
the largest of the widths of `Φ`, of the derivation and of the refutation: every clause of
`Φ↾(m := 1)` is a clause of `Φ` or its resolvent with `{m}`. -/
theorem Refutation.exists_of_unit {Φ : CNF V} {m : Literal V} (δ : Derivation Φ {m})
    (π₀ : Refutation (Φ.restrict (Restriction.ofLit m))) :
    ∃ π' : Refutation Φ, π'.width ≤ max (max Φ.width δ.width) π₀.width := by
  set L : List (Clause V) := Φ.toList ++ δ.lines with hL
  have hLder : IsDerivation Φ ∅ L :=
    IsDerivation.append (isDerivation_of_forall_mem ∅ _ fun C hC => Finset.mem_toList.mp hC)
      (δ.isDerivation.mono_acc (Finset.empty_subset _))
  have hm : ({m} : Clause V) ∈ L.toFinset :=
    List.mem_toFinset.mpr (List.mem_append_right _ δ.mem_lines)
  have hΦL : ∀ C ∈ Φ, C ∈ L.toFinset := fun C hC =>
    List.mem_toFinset.mpr (List.mem_append_left _ (Finset.mem_toList.mpr hC))
  have hΦ : ∀ E ∈ π₀.lines, E ∈ Φ.restrict (Restriction.ofLit m) →
      Clause.SurvivesUnder (Subst.id V) E → ∃ D ⊆ E.subst (Subst.id V) ∪ ∅,
        D ∈ Φ ∨ D ∈ L.toFinset ∨ ∃ D₁ ∈ L.toFinset, ∃ D₂ ∈ L.toFinset,
          Clause.IsResolvent D D₁ D₂ := by
    intro E _ hE _
    obtain ⟨C, hC, hsurv, rfl⟩ := CNF.mem_restrict.mp hE
    rw [Clause.restrict_ofLit, Clause.subst_id, Finset.union_empty]
    rw [Clause.survives_ofLit_iff] at hsurv
    by_cases hmc : mᶜ ∈ C
    · refine ⟨C.erase mᶜ, Finset.Subset.refl _, Or.inr (Or.inr ?_)⟩
      rcases m with ⟨x, s⟩
      cases s
      · refine ⟨C, hΦL C hC, {⟨x, false⟩}, hm, x, hmc, Finset.mem_singleton_self _, ?_⟩
        simp [Clause.resolvent, Literal.pos, Literal.neg]
      · refine ⟨{⟨x, true⟩}, hm, C, hΦL C hC, x, Finset.mem_singleton_self _, hmc, ?_⟩
        simp [Clause.resolvent, Literal.pos, Literal.neg]
    · exact ⟨C, by rw [Finset.erase_eq_of_notMem hmc], Or.inl hC⟩
  obtain ⟨π₁', π₁, hsub, hall, hπ₁, hcov⟩ := π₀.isDerivation.exists_simulation_sublist
    (Subst.id V) ∅ (Ψ := Φ) (S₀ := L.toFinset) (S' := L.toFinset) (Finset.Subset.refl _) hΦ
    (by simp)
  obtain ⟨D, hD, hDsub⟩ := hcov ∅ π₀.mem_lines (Clause.survivesUnder_empty _)
  rw [Clause.subst_empty, Finset.empty_union, Finset.subset_empty] at hDsub
  subst hDsub
  have hfull : IsDerivation Φ ∅ (L ++ π₁) := hLder.append (by simpa using hπ₁)
  have hmem : (∅ : Clause V) ∈ L ++ π₁ := by
    rcases hD with hD | hD
    · exact List.mem_append_left _ (List.mem_toFinset.mp hD)
    · exact List.mem_append_right _ hD
  obtain ⟨π', hπ'⟩ := Derivation.exists_of_mem_sublist hfull hmem
  refine ⟨π', π'.width_le fun E hE => ?_⟩
  rcases List.mem_append.mp (hπ'.subset hE) with hE | hE
  · rcases List.mem_append.mp hE with hE | hE
    · exact ((CNF.card_le_width (Finset.mem_toList.mp hE)).trans (le_max_left _ _)).trans
        (le_max_left _ _)
    · exact ((δ.card_le_width hE).trans (le_max_right _ _)).trans (le_max_left _ _)
  · obtain ⟨C, hC, -, hR⟩ := forall₂_exists_of_mem hall hE
    rw [Clause.subst_id, Finset.union_empty] at hR
    exact ((Finset.card_le_card hR).trans (π₀.card_le_width (hsub.subset hC))).trans
      (le_max_right _ _)

/-! ### Fat clauses -/

section Fat

variable [Fintype V]

/-- Double counting: summing over all literals the number of clauses of width more than `d`
containing the literal gives the total width of these clauses. -/
theorem sum_countP_mem (d : ℕ) (L : List (Clause V)) :
    ∑ ℓ ∈ Literal.ofVars (Finset.univ : Finset V),
        L.countP (fun C => decide (d < C.card ∧ ℓ ∈ C)) =
      ((L.filter fun C => decide (d < C.card)).map Finset.card).sum := by
  induction L with
  | nil => simp
  | cons C L ih =>
    simp only [List.countP_cons, Finset.sum_add_distrib, ih]
    by_cases hC : d < C.card
    · rw [List.filter_cons_of_pos (by simpa using hC), List.map_cons, List.sum_cons]
      have : ∑ ℓ ∈ Literal.ofVars (Finset.univ : Finset V),
          (if decide (d < C.card ∧ ℓ ∈ C) = true then 1 else 0) = C.card := by
        simp only [decide_eq_true_eq, hC, true_and]
        rw [Finset.sum_boole, Finset.filter_mem_eq_inter,
          Finset.inter_eq_right.mpr (Clause.subset_ofVars (Finset.subset_univ _))]
        simp
      omega
    · rw [List.filter_cons_of_neg (by simpa using hC)]
      simp [hC]

omit [DecidableEq V] [Fintype V] in
theorem length_mul_le_sum_card (d : ℕ) :
    ∀ L : List (Clause V), (∀ C ∈ L, d ≤ C.card) → L.length * d ≤ (L.map Finset.card).sum
  | [], _ => by simp
  | C :: L, h => by
    rw [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have := length_mul_le_sum_card d L fun C' hC' => h C' (List.mem_cons_of_mem _ hC')
    have := h C List.mem_cons_self
    omega

/-- **Averaging.** If a sequence of clauses over `V` has `F > 0` clauses of width more than `d`,
some literal occurs in at least `d F / 2|V|` of them. -/
theorem exists_literal_fat (d : ℕ) (L : List (Clause V))
    (hF : 0 < L.countP fun C => decide (d < C.card)) :
    ∃ ℓ : Literal V, d * L.countP (fun C => decide (d < C.card)) ≤
      2 * Fintype.card V * L.countP (fun C => decide (d < C.card ∧ ℓ ∈ C)) := by
  set F := L.countP fun C => decide (d < C.card) with hFdef
  set Lit := Literal.ofVars (Finset.univ : Finset V) with hLit
  have hsum : d * F ≤ ∑ ℓ ∈ Lit, L.countP (fun C => decide (d < C.card ∧ ℓ ∈ C)) := by
    rw [hLit, sum_countP_mem, hFdef, List.countP_eq_length_filter, mul_comm]
    exact length_mul_le_sum_card d _ fun C hC => by
      have := List.mem_filter.mp hC
      simp only [decide_eq_true_eq] at this
      exact this.2.le
  have hne : Lit.Nonempty := by
    obtain ⟨C, -, hp⟩ := List.countP_pos_iff.mp hF
    simp only [decide_eq_true_eq] at hp
    obtain ⟨l, hl⟩ := Finset.card_pos.mp (by omega : 0 < C.card)
    exact ⟨l, Literal.mem_ofVars.mpr (Finset.mem_univ _)⟩
  have hcard : Lit.card ≤ 2 * Fintype.card V := by
    simpa using Literal.card_ofVars_le (Finset.univ : Finset V)
  obtain ⟨ℓ, -, hℓ⟩ := Finset.exists_le_of_sum_le hne (f := fun _ => d * F)
    (g := fun ℓ => 2 * Fintype.card V * L.countP (fun C => decide (d < C.card ∧ ℓ ∈ C))) (by
      rw [Finset.sum_const, smul_eq_mul, ← Finset.mul_sum]
      calc Lit.card * (d * F) ≤ 2 * Fintype.card V * (d * F) := Nat.mul_le_mul_right _ hcard
        _ ≤ 2 * Fintype.card V * ∑ ℓ ∈ Lit, L.countP (fun C => decide (d < C.card ∧ ℓ ∈ C)) :=
          Nat.mul_le_mul_left _ hsum)
  exact ⟨ℓ, hℓ⟩

omit [Fintype V] in
theorem countP_fat_split (d : ℕ) (ℓ : Literal V) (L : List (Clause V)) :
    (L.countP fun C => decide (d < C.card ∧ ℓ ∉ C)) +
      (L.countP fun C => decide (d < C.card ∧ ℓ ∈ C)) =
      L.countP fun C => decide (d < C.card) := by
  induction L with
  | nil => simp
  | cons C L ih =>
    rw [List.countP_cons, List.countP_cons, List.countP_cons]
    simp only [decide_eq_true_eq]
    generalize (L.countP fun C => decide (d < C.card ∧ ℓ ∉ C)) = a at ih ⊢
    generalize (L.countP fun C => decide (d < C.card ∧ ℓ ∈ C)) = b at ih ⊢
    generalize (L.countP fun C => decide (d < C.card)) = c at ih ⊢
    by_cases h1 : d < C.card <;> by_cases h2 : ℓ ∈ C <;> simp [h1, h2] <;> omega

omit [Fintype V] in
/-- The variables of a refutation lie in those of `Φ`. -/
theorem Refutation.vars_subset {Φ : CNF V} (π : Refutation Φ) {C : Clause V}
    (hC : C ∈ π.lines) : C.vars ⊆ Φ.vars :=
  π.isDerivation.vars_subset (Finset.Subset.refl _) (by simp) C hC

/-- **The induction of Ben-Sasson and Wigderson.** Let `0 < d ≤ 2N` where `N = |V|`. If a CNF
`Φ` over `V` has a refutation with `F` clauses of width more than `d`, where
`F (1 - d/2N)^b < 1`, then `Φ` has a refutation of width at most `w(Φ) + d + b`. -/
theorem exists_width_le_of_fat {d : ℕ} (hd : 0 < d) (hdn : d ≤ 2 * Fintype.card V) :
    ∀ k, ∀ Φ : CNF V, Φ.vars.card ≤ k → ∀ b : ℕ, ∀ π : Refutation Φ,
      ((π.lines.countP fun C => decide (d < C.card) : ℕ) : ℝ) *
        (1 - (d : ℝ) / (2 * Fintype.card V)) ^ b < 1 →
      ∃ π' : Refutation Φ, π'.width ≤ Φ.width + d + b := by
  set n := Fintype.card V with hn
  set t : ℝ := 1 - (d : ℝ) / (2 * n) with ht
  have hn0 : (0 : ℝ) < 2 * n := by
    have : 0 < 2 * n := by omega
    exact_mod_cast this
  have ht0 : 0 ≤ t := by
    rw [ht, sub_nonneg, div_le_one hn0]
    exact_mod_cast hdn
  -- the inductive step, given the induction hypothesis for fewer variables
  have step : ∀ k, (∀ Φ : CNF V, Φ.vars.card ≤ k → ∀ b : ℕ, ∀ π : Refutation Φ,
      ((π.lines.countP fun C => decide (d < C.card) : ℕ) : ℝ) * t ^ b < 1 →
      ∃ π' : Refutation Φ, π'.width ≤ Φ.width + d + b) →
      ∀ Φ : CNF V, Φ.vars.card ≤ k + 1 → ∀ b : ℕ, ∀ π : Refutation Φ,
      ((π.lines.countP fun C => decide (d < C.card) : ℕ) : ℝ) * t ^ b < 1 →
      ∃ π' : Refutation Φ, π'.width ≤ Φ.width + d + b := by
    intro k ih Φ hk b π hF
    set F := π.lines.countP fun C => decide (d < C.card) with hFdef
    by_cases hF0 : F = 0
    · exact ⟨π, (π.width_le_of_countP_eq_zero hF0).trans (by omega)⟩
    have hFpos : 0 < F := Nat.pos_of_ne_zero hF0
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := by
      rcases b with _ | b'
      · exfalso
        rw [pow_zero, mul_one] at hF
        have : (1 : ℝ) ≤ F := by exact_mod_cast hFpos
        linarith
      · exact ⟨b', rfl⟩
    obtain ⟨ℓ, hℓ⟩ := exists_literal_fat d π.lines hFpos
    rw [← hFdef] at hℓ
    set G := π.lines.countP fun C => decide (d < C.card ∧ ℓ ∈ C) with hGdef
    have hGpos : 0 < G := by
      by_contra h
      have hG0 : G = 0 := by omega
      rw [hG0, mul_zero] at hℓ
      have := Nat.mul_pos hd hFpos
      omega
    have hvar : ℓ.var ∈ Φ.vars := by
      obtain ⟨C, hC, hp⟩ := List.countP_pos_iff.mp hGpos
      simp only [decide_eq_true_eq] at hp
      exact π.vars_subset hC (Clause.mem_vars.mpr ⟨ℓ, hp.2, rfl⟩)
    have hsplit := countP_fat_split d ℓ π.lines
    have hFG : (((π.lines.countP fun C => decide (d < C.card ∧ ℓ ∉ C)) : ℕ) : ℝ) ≤ F * t := by
      have h1 : (d : ℝ) * F ≤ 2 * n * G := by exact_mod_cast hℓ
      have h2 : (((π.lines.countP fun C => decide (d < C.card ∧ ℓ ∉ C)) : ℕ) : ℝ) = F - G := by
        rw [hFdef, hGdef, ← hsplit]
        push_cast
        ring
      have h3 : (F : ℝ) * d / (2 * n) ≤ G := by
        rw [div_le_iff₀ hn0]
        linarith
      rw [h2, ht]
      have : (F : ℝ) * (1 - d / (2 * n)) = F - F * d / (2 * n) := by ring
      rw [this]
      linarith
    -- the branch `ℓ := 1`
    obtain ⟨π₁, -, hc₁⟩ := π.exists_restrict_width (Restriction.ofLit ℓ)
    have hF₁ : (((π₁.lines.countP fun C => decide (d < C.card)) : ℕ) : ℝ) * t ^ b' < 1 := by
      have h1 : (π₁.lines.countP fun C => decide (d < C.card)) ≤
          π.lines.countP fun C => decide (d < C.card ∧ ℓ ∉ C) := by
        refine (hc₁ d).trans (List.countP_mono_left fun C _ h => ?_)
        simp only [decide_eq_true_eq] at h ⊢
        exact ⟨h.2, fun hmem => h.1 ⟨ℓ, hmem, (Literal.satBy_ofLit_iff ℓ ℓ).mpr rfl⟩⟩
      calc (((π₁.lines.countP fun C => decide (d < C.card)) : ℕ) : ℝ) * t ^ b'
          ≤ (((π.lines.countP fun C => decide (d < C.card ∧ ℓ ∉ C)) : ℕ) : ℝ) * t ^ b' :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast h1) (pow_nonneg ht0 _)
        _ ≤ F * t * t ^ b' := mul_le_mul_of_nonneg_right hFG (pow_nonneg ht0 _)
        _ = F * t ^ (b' + 1) := by ring
        _ < 1 := hF
    have hk₁ : (Φ.restrict (Restriction.ofLit ℓ)).vars.card ≤ k := by
      calc (Φ.restrict (Restriction.ofLit ℓ)).vars.card
          ≤ (Φ.vars.erase ℓ.var).card :=
            Finset.card_le_card (CNF.vars_restrict_ofLit_subset ℓ Φ)
        _ = Φ.vars.card - 1 := Finset.card_erase_of_mem hvar
        _ ≤ k := by omega
    obtain ⟨π₁', hπ₁'⟩ := ih _ hk₁ b' π₁ hF₁
    obtain ⟨D, hD, δ, hδ⟩ := π₁'.exists_lift_width {ℓᶜ} (by
      intro C _ l _ hf
      rw [Literal.falsifiedBy_ofLit_iff] at hf
      exact Finset.mem_singleton.mpr hf)
    have hδw : δ.width ≤ Φ.width + d + (b' + 1) := by
      have := CNF.width_restrict_le (Restriction.ofLit ℓ) Φ
      rw [Finset.card_singleton] at hδ
      omega
    rcases Finset.subset_singleton_iff.mp hD with rfl | rfl
    · exact ⟨δ, hδw⟩
    -- the branch `ℓ := 0`
    obtain ⟨π₀, -, hc₀⟩ := π.exists_restrict_width (Restriction.ofLit ℓᶜ)
    have hF₀ : (((π₀.lines.countP fun C => decide (d < C.card)) : ℕ) : ℝ) * t ^ (b' + 1) < 1 := by
      have h1 : (π₀.lines.countP fun C => decide (d < C.card)) ≤ F := by
        refine (hc₀ d).trans (List.countP_mono_left fun C _ h => ?_)
        simp only [decide_eq_true_eq] at h ⊢
        exact h.2
      calc (((π₀.lines.countP fun C => decide (d < C.card)) : ℕ) : ℝ) * t ^ (b' + 1)
          ≤ (F : ℝ) * t ^ (b' + 1) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast h1) (pow_nonneg ht0 _)
        _ < 1 := hF
    have hk₀ : (Φ.restrict (Restriction.ofLit ℓᶜ)).vars.card ≤ k := by
      calc (Φ.restrict (Restriction.ofLit ℓᶜ)).vars.card
          ≤ (Φ.vars.erase ℓᶜ.var).card :=
            Finset.card_le_card (CNF.vars_restrict_ofLit_subset ℓᶜ Φ)
        _ = Φ.vars.card - 1 := Finset.card_erase_of_mem (by simpa using hvar)
        _ ≤ k := by omega
    obtain ⟨π₀', hπ₀'⟩ := ih _ hk₀ (b' + 1) π₀ hF₀
    obtain ⟨π', hπ'⟩ := Refutation.exists_of_unit δ π₀'
    refine ⟨π', hπ'.trans ?_⟩
    have := CNF.width_restrict_le (Restriction.ofLit ℓᶜ) Φ
    exact max_le (max_le (by omega) hδw) (by omega)
  intro k
  induction k with
  | zero =>
    intro Φ hk b π hF
    by_cases hF0 : (π.lines.countP fun C => decide (d < C.card)) = 0
    · exact ⟨π, (π.width_le_of_countP_eq_zero hF0).trans (by omega)⟩
    · exfalso
      obtain ⟨C, hC, hp⟩ := List.countP_pos_iff.mp (Nat.pos_of_ne_zero hF0)
      simp only [decide_eq_true_eq] at hp
      obtain ⟨l, hl⟩ := Finset.card_pos.mp (by omega : 0 < C.card)
      have : l.var ∈ Φ.vars := π.vars_subset hC (Clause.mem_vars.mpr ⟨l, hl, rfl⟩)
      have := Finset.card_pos.mpr ⟨l.var, this⟩
      omega
  | succ k ih => exact step k ih

end Fat

/-! ### The theorem -/

/-- **The size–width tradeoff** (Theorem [thm:bw]) as a proposition: there is an absolute
constant `c > 0` such that for every CNF `Φ` over a finite variable type `V` and every
refutation `π` of `Φ`, some refutation of `Φ` has width at most `w(Φ) + √(c |V| log |π|)`.

Paper: Theorem [thm:bw]. -/
def BWTradeoff : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (V : Type) [Fintype V] [DecidableEq V] (Φ : CNF V) (π : Refutation Φ),
    ∃ π' : Refutation Φ,
      (π'.width : ℝ) ≤ Φ.width + Real.sqrt (c * Fintype.card V * Real.log π.size)

/-- **The size–width tradeoff** (Theorem [thm:bw]), with the constant `c = 32`: a refutation
of size `S` of a CNF over `N` variables can be replaced by one of width at most
`w(Φ) + √(32 N log S)`.

Paper: Theorem [thm:bw]. -/
theorem bwTradeoff : BWTradeoff := by
  refine ⟨32, by norm_num, ?_⟩
  intro V _ _ Φ π
  set n := Fintype.card V with hn
  set S := π.size with hS
  have hS1 : 1 ≤ S := π.size_pos
  have hwidth2n : π.width ≤ 2 * n := π.width_le fun D _ => by
    calc D.card ≤ (Literal.ofVars (Finset.univ : Finset V)).card :=
          Finset.card_le_card (Clause.subset_ofVars (Finset.subset_univ _))
      _ ≤ 2 * n := by simpa using Literal.card_ofVars_le (Finset.univ : Finset V)
  by_cases hB : (2 * n : ℝ) ≤ Real.sqrt (32 * n * Real.log S)
  · refine ⟨π, ?_⟩
    calc (π.width : ℝ) ≤ 2 * n := by exact_mod_cast hwidth2n
      _ ≤ Real.sqrt (32 * n * Real.log S) := hB
      _ ≤ Φ.width + Real.sqrt (32 * n * Real.log S) := le_add_of_nonneg_left (Nat.cast_nonneg _)
  rw [not_le] at hB
  have hn1 : 1 ≤ n := by
    by_contra h
    have h0 : n = 0 := by omega
    rw [h0] at hB
    simp only [Nat.cast_zero, mul_zero, zero_mul] at hB
    exact absurd hB (not_lt.mpr (Real.sqrt_nonneg _))
  rcases Nat.eq_or_lt_of_le hS1 with hS1' | hS2
  · refine ⟨π, ?_⟩
    have hw : π.width = 0 := by
      have hlen : π.lines.length = 1 := hS1'.symm
      obtain ⟨C, hC⟩ := List.length_eq_one_iff.mp hlen
      have hC0 : C = ∅ := by
        have := π.getLast?_lines
        rw [hC] at this
        simpa using this
      subst hC0
      simp [Derivation.width, hC]
    rw [hw]
    push_cast
    positivity
  have hlogS : 0 < Real.log S := Real.log_pos (by exact_mod_cast hS2)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  set x : ℝ := 2 * n * Real.log S with hx
  have hxpos : 0 < x := by positivity
  set d : ℕ := ⌈Real.sqrt x⌉₊ with hd
  set b : ℕ := ⌊x / d⌋₊ + 1 with hb
  have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxpos
  have hd_pos : 0 < d := by
    rw [hd]
    exact Nat.ceil_pos.mpr hsqrt_pos
  have hd_pos' : (0 : ℝ) < d := by exact_mod_cast hd_pos
  have hd_ge : Real.sqrt x ≤ d := Nat.le_ceil _
  have hd_lt : (d : ℝ) < Real.sqrt x + 1 := Nat.ceil_lt_add_one (Real.sqrt_nonneg _)
  have hx_lt : x < ((n : ℝ) / 2) ^ 2 := by
    have h1 : 32 * n * Real.log S < (2 * n) ^ 2 := (Real.sqrt_lt' (by positivity)).mp hB
    have h3 : ((n : ℝ) / 2) ^ 2 = n ^ 2 / 4 := by ring
    rw [h3, hx]
    linarith
  have hsqrt_lt : Real.sqrt x < n / 2 := (Real.sqrt_lt' (by positivity)).mpr hx_lt
  have hdn : d ≤ 2 * n := by
    have : (d : ℝ) ≤ 2 * n := by linarith
    exact_mod_cast this
  obtain ⟨π', hπ'⟩ := exists_width_le_of_fat hd_pos hdn Φ.vars.card Φ le_rfl b π (by
    set t : ℝ := 1 - (d : ℝ) / (2 * n) with ht
    have hF_le : (((π.lines.countP fun C => decide (d < C.card)) : ℕ) : ℝ) ≤ S := by
      rw [hS]
      exact_mod_cast List.countP_le_length
    have ht0 : 0 ≤ t := by
      rw [ht, sub_nonneg, div_le_one (by positivity)]
      exact_mod_cast hdn
    have ht_exp : t ≤ Real.exp (-((d : ℝ) / (2 * n))) := by
      have := Real.add_one_le_exp (-((d : ℝ) / (2 * n)))
      rw [ht]
      linarith
    have hpow : t ^ b ≤ Real.exp (-((d : ℝ) / (2 * n))) ^ b := pow_le_pow_left₀ ht0 ht_exp b
    rw [← Real.exp_nat_mul] at hpow
    have hbd : Real.log S < b * ((d : ℝ) / (2 * n)) := by
      have hb_gt : x / d < b := by
        rw [hb]
        push_cast
        exact Nat.lt_floor_add_one _
      rw [div_lt_iff₀ hd_pos'] at hb_gt
      rw [hx] at hb_gt
      rw [mul_div_assoc', lt_div_iff₀ (by positivity)]
      linarith
    have hSpos : (0 : ℝ) < S := by exact_mod_cast hS1
    calc (((π.lines.countP fun C => decide (d < C.card)) : ℕ) : ℝ) * t ^ b
        ≤ S * Real.exp (b * -((d : ℝ) / (2 * n))) :=
          mul_le_mul hF_le hpow (pow_nonneg ht0 _) (Nat.cast_nonneg _)
      _ < (S : ℝ) * (S : ℝ)⁻¹ := by
          apply mul_lt_mul_of_pos_left _ hSpos
          rw [show (b : ℝ) * -((d : ℝ) / (2 * n)) = -(b * (d / (2 * n))) by ring, Real.exp_neg]
          have : (S : ℝ) = Real.exp (Real.log S) := (Real.exp_log hSpos).symm
          conv_rhs => rw [this]
          exact inv_strictAnti₀ (Real.exp_pos _) (Real.exp_lt_exp.mpr hbd)
      _ = 1 := mul_inv_cancel₀ hSpos.ne')
  refine ⟨π', ?_⟩
  have hb_le : (b : ℝ) ≤ x / d + 1 := by
    rw [hb]
    push_cast
    have := Nat.floor_le (a := x / d) (by positivity)
    linarith
  have hxd : x / d ≤ Real.sqrt x := by
    rw [div_le_iff₀ hd_pos']
    calc x = Real.sqrt x * Real.sqrt x := (Real.mul_self_sqrt hxpos.le).symm
      _ ≤ Real.sqrt x * d := mul_le_mul_of_nonneg_left hd_ge (Real.sqrt_nonneg _)
  have hsq32 : Real.sqrt (32 * n * Real.log S) = 4 * Real.sqrt x := by
    rw [show (32 : ℝ) * n * Real.log S = 4 ^ 2 * x by rw [hx]; ring, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  have hx1 : 1 ≤ Real.sqrt x := by
    rw [Real.le_sqrt (by norm_num) hxpos.le, one_pow, hx]
    have hlog2 : Real.log 2 ≤ Real.log S := Real.log_le_log (by norm_num) (by exact_mod_cast hS2)
    have := Real.log_two_gt_d9
    nlinarith
  calc (π'.width : ℝ) ≤ Φ.width + d + b := by exact_mod_cast hπ'
    _ ≤ Φ.width + Real.sqrt (32 * n * Real.log S) := by linarith

end AssocLB
