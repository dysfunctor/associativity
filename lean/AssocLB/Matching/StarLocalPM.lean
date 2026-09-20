/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/
import AssocLB.Resolution.Completeness
import AssocLB.Matching.Expander

/-!
# Star-local perfect matching

Paper: Section 5 (Star-local perfect matching): Definition [def:pm] (perfect-matching CNF),
Definition [def:star-local-ext] (star-local extension) and Lemma [lem:star-local-derivations]
(local consequences have constant-size derivations).

## Main definitions

* `StarFun G w`: a Boolean function of the edges at the vertex `w`, a function of the
  assignments to the star `E(w)`.
* `SPMVar G`: the variables, the edge variables `X_e` (`SPM.X`) and the extension variables
  `Z_{w,f}` (`SPM.Z`).
* `SPM.exactOne G w`: `ExactOne(X_{E(w)})`, the clause `⋁_{e ∈ E(w)} X_e` (`SPM.atLeastOne`)
  and the clauses `¬X_e ∨ ¬X_f` (`SPM.atMostOne`); `PM G`, the perfect-matching CNF.
* `SPM.defClauses G w f`: `Def(Z_{w,f})`, the clauses expressing `Z_{w,f} = f((X_e)_{e ∈ E(w)})`;
  `SPM.vertexClauses G w`: the clauses `F_w` associated with `w`; `SPM G`: the star-local
  extension `SPM(G) = ⋀_w F_w`.

## Main results

* `SPM.sat_exactOne_iff`, `SPM.sat_defClauses_iff`, `SPM.sat_SPM_iff`: the semantics of the
  clauses, exactly one selected edge at every vertex and every extension variable equal to
  its function.
* `SPM.extend G β`: the extension of an edge assignment by the defining functions; every
  clause of `Def(Z_{w,f})` holds under it (`SPM.sat_defClauses_extend`). `PM(G) ⊆ SPM(G)`
  (`SPM.PM_subset_SPM`), and `PM(G)` mentions only edge variables (`SPM.mem_vars_PM`).
* `SPM.width_SPM_le`: every clause of `SPM(G)` has width at most `Δ + 1` when the maximum
  degree is at most `Δ`.
* `SPM.unsatisfiable`: `SPM(G)` is unsatisfiable when `|U| > |V|`, since the selected edges
  would match `U` injectively into `V`.
* `SPM.card_SPMVar_le`: `SPM(G)` has at most `(|U| + |V|) (Δ + 2^{2^Δ})` variables.
* `SPM.exists_derivation_localCNF`: Lemma [lem:star-local-derivations]. A nontautological
  clause implied by the clauses `⋀_{w ∈ W} F_w` (`SPM.localCNF G W`) has a subclause with a
  derivation from them of size at most `2 ^ (2 |W| (Δ + 2^{2^Δ}))`.

## Design notes

* The variable type is `E ⊕ Σ w, StarFun G w`, so that the equality and finiteness instances
  come from Mathlib; `X` and `Z` are the two injections.
* `Def(Z_{w,f})` is the truth-table clause set, one clause per pattern of values of the edges at
  `w`, as for gates in `AssocLB.Multiplier.Circuit`.

Theorem [thm:star-local-hard] (the star-local extension remains hard) is proved in
`AssocLB.Matching.StarLocalHard`.
-/

namespace AssocLB

variable {U V E : Type*} (G : Bipartite U V E) [Fintype U] [Fintype V] [Fintype E]
  [DecidableEq U] [DecidableEq V] [DecidableEq E]

/-- A Boolean function of the edges at the vertex `w`: a function of the assignments to the
star `E(w)`.

Paper: Definition [def:star-local-ext]. -/
abbrev StarFun (w : U ⊕ V) : Type _ := ({e // e ∈ G.star w} → Bool) → Bool

/-- The variables of `SPM(G)`: the edge variables `X_e` and the extension variables `Z_{w,f}`.

Paper: Definitions [def:pm] and [def:star-local-ext]. -/
abbrev SPMVar : Type _ := E ⊕ Σ w : U ⊕ V, StarFun G w

/- The instances are spelled out: the nested search through `Sum`, `Sigma` and the function
types of `StarFun` exceeds the pending-instance depth of the default configuration. -/

instance instDecidableEqStarFun (w : U ⊕ V) : DecidableEq (StarFun G w) := inferInstance

instance instFintypeStarFun (w : U ⊕ V) : Fintype (StarFun G w) := inferInstance

instance instDecidableEqSPMVar : DecidableEq (SPMVar G) := inferInstance

instance instFintypeSPMVar : Fintype (SPMVar G) := inferInstance

namespace SPM

/-- The edge variable `X_e`. -/
abbrev X (e : E) : SPMVar G := Sum.inl e

/-- The extension variable `Z_{w,f}`. -/
abbrev Z (w : U ⊕ V) (f : StarFun G w) : SPMVar G := Sum.inr ⟨w, f⟩

/-- The clause `⋁_{e ∈ E(w)} X_e`. -/
def atLeastOne (w : U ⊕ V) : Clause (SPMVar G) :=
  (G.star w).image fun e => Literal.pos (X G e)

/-- The clauses `¬X_e ∨ ¬X_f` for distinct `e, f ∈ E(w)`. -/
def atMostOne (w : U ⊕ V) : CNF (SPMVar G) :=
  ((G.star w ×ˢ G.star w).filter fun p => p.1 ≠ p.2).image fun p =>
    {Literal.neg (X G p.1), Literal.neg (X G p.2)}

/-- `ExactOne(X_{E(w)})`: exactly one edge at `w` is selected.

Paper: Definition [def:pm]. -/
def exactOne (w : U ⊕ V) : CNF (SPMVar G) := insert (atLeastOne G w) (atMostOne G w)

/-- The clause of `Def(Z_{w,f})` for the pattern `σ` of values of the edges at `w`: if the
edges take the values `σ`, then `Z_{w,f}` takes the value `f σ`. -/
def defClause (w : U ⊕ V) (f : StarFun G w) (σ : {e // e ∈ G.star w} → Bool) :
    Clause (SPMVar G) :=
  (Finset.univ.image fun e : {e // e ∈ G.star w} => (⟨X G e, !σ e⟩ : Literal (SPMVar G))) ∪
    {⟨Z G w f, f σ⟩}

/-- `Def(Z_{w,f})`: the clauses expressing `Z_{w,f} = f((X_e)_{e ∈ E(w)})`.

Paper: Definition [def:star-local-ext]. -/
def defClauses (w : U ⊕ V) (f : StarFun G w) : CNF (SPMVar G) :=
  Finset.univ.image (defClause G w f)

/-- The clauses `F_w` of `SPM(G)` associated with the vertex `w`.

Paper: Lemma [lem:star-local-derivations]. -/
def vertexClauses (w : U ⊕ V) : CNF (SPMVar G) :=
  exactOne G w ∪ Finset.univ.biUnion fun f => defClauses G w f

end SPM

/-- The exact-one perfect-matching CNF `PM(G)`.

Paper: Definition [def:pm]. -/
def PM : CNF (SPMVar G) := Finset.univ.biUnion fun w => SPM.exactOne G w

/-- The star-local extension `SPM(G)` of the perfect-matching principle.

Paper: Definition [def:star-local-ext]. -/
def SPM : CNF (SPMVar G) := Finset.univ.biUnion fun w => SPM.vertexClauses G w

namespace SPM

variable (α : SPMVar G → Bool)

/-! ### Semantics -/

omit [Fintype U] [Fintype V] in
theorem sat_atLeastOne_iff (w : U ⊕ V) :
    Clause.Sat α (atLeastOne G w) ↔ ∃ e ∈ G.star w, α (X G e) = true := by
  simp [atLeastOne, Clause.Sat]

omit [Fintype U] [Fintype V] in
theorem sat_atMostOne_iff (w : U ⊕ V) :
    CNF.Sat α (atMostOne G w) ↔
      ∀ e ∈ G.star w, ∀ f ∈ G.star w, e ≠ f → α (X G e) = false ∨ α (X G f) = false := by
  constructor
  · intro h e he f hf hne
    have hmem : (e, f) ∈ (G.star w ×ˢ G.star w).filter fun p => p.1 ≠ p.2 :=
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨he, hf⟩, hne⟩
    have := h _ (Finset.mem_image_of_mem _ hmem)
    simpa [Clause.Sat] using this
  · intro h C hC
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hC
    rw [Finset.mem_filter, Finset.mem_product] at hp
    rcases h p.1 hp.1.1 p.2 hp.1.2 hp.2 with h1 | h1 <;> simp [Clause.Sat, h1]

omit [Fintype U] [Fintype V] in
/-- `ExactOne(X_{E(w)})` is satisfied exactly when one edge at `w` is selected. -/
theorem sat_exactOne_iff (w : U ⊕ V) :
    CNF.Sat α (exactOne G w) ↔
      ∃ e ∈ G.star w, α (X G e) = true ∧ ∀ f ∈ G.star w, α (X G f) = true → f = e := by
  rw [exactOne, CNF.Sat, Finset.forall_mem_insert, ← CNF.Sat, sat_atMostOne_iff,
    sat_atLeastOne_iff]
  constructor
  · rintro ⟨⟨e, he, hα⟩, hmost⟩
    refine ⟨e, he, hα, fun f hf hαf => ?_⟩
    by_contra hne
    rcases hmost e he f hf (Ne.symm hne) with h | h
    · rw [h] at hα
      exact Bool.false_ne_true hα
    · rw [h] at hαf
      exact Bool.false_ne_true hαf
  · rintro ⟨e, he, hα, huniq⟩
    refine ⟨⟨e, he, hα⟩, fun e₁ h₁ e₂ h₂ hne => ?_⟩
    by_contra hcon
    rw [not_or] at hcon
    have h₁' := huniq e₁ h₁ (by simpa using hcon.1)
    have h₂' := huniq e₂ h₂ (by simpa using hcon.2)
    exact hne (h₁'.trans h₂'.symm)

omit [Fintype U] [Fintype V] in
/-- `Def(Z_{w,f})` is satisfied exactly when `Z_{w,f}` takes the value of `f` at the edges. -/
theorem sat_defClauses_iff (w : U ⊕ V) (f : StarFun G w) :
    CNF.Sat α (defClauses G w f) ↔ α (Z G w f) = f fun e => α (X G e) := by
  constructor
  · intro h
    obtain ⟨l, hl, hs⟩ := h _ (Finset.mem_image_of_mem (defClause G w f)
      (Finset.mem_univ fun e : {e // e ∈ G.star w} => α (X G e)))
    simp only [defClause, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_singleton] at hl
    rcases hl with ⟨e, rfl⟩ | rfl
    · exact absurd hs (by simp [Literal.Sat])
    · exact hs
  · intro h C hC
    obtain ⟨σ, -, rfl⟩ := Finset.mem_image.mp hC
    by_cases hσ : (fun e : {e // e ∈ G.star w} => α (X G e)) = σ
    · refine ⟨⟨Z G w f, f σ⟩, Finset.mem_union_right _ (Finset.mem_singleton_self _), ?_⟩
      change α (Z G w f) = f σ
      rw [h, hσ]
    · obtain ⟨e, he⟩ := Function.ne_iff.mp hσ
      refine ⟨⟨X G e, !σ e⟩,
        Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ e)), ?_⟩
      simpa [Literal.Sat, Bool.eq_not] using he

omit [Fintype U] [Fintype V] in
theorem sat_vertexClauses_iff (w : U ⊕ V) :
    CNF.Sat α (vertexClauses G w) ↔
      CNF.Sat α (exactOne G w) ∧ ∀ f : StarFun G w, α (Z G w f) = f fun e => α (X G e) := by
  simp only [vertexClauses, CNF.sat_union_iff, CNF.sat_biUnion_iff, Finset.mem_univ,
    true_implies, sat_defClauses_iff]

/-- The semantics of `SPM(G)`: exactly one selected edge at every vertex, and every extension
variable equal to its function of the edges. -/
theorem sat_SPM_iff :
    CNF.Sat α (SPM G) ↔ ∀ w, CNF.Sat α (exactOne G w) ∧
      ∀ f : StarFun G w, α (Z G w f) = f fun e => α (X G e) := by
  simp only [SPM, CNF.sat_biUnion_iff, Finset.mem_univ, true_implies, sat_vertexClauses_iff]

theorem exactOne_subset_SPM (w : U ⊕ V) : exactOne G w ⊆ SPM G := fun _ hC =>
  Finset.mem_biUnion.mpr ⟨w, Finset.mem_univ w, Finset.mem_union_left _ hC⟩

omit [Fintype U] [Fintype V] [DecidableEq E] in
/-- The extension of an edge assignment `β` to all variables of `SPM(G)`: the edge variable
`X_e` takes the value `β e`, and the extension variable `Z_{w,f}` the value `f((β e)_{e ∈ E(w)})`
of its defining function. A clause `C` is satisfied by `extend G β` exactly when the paper's
`Ĉ`, obtained by replacing each extension variable by its defining function, is satisfied by
`β`.

Paper: proofs of Lemma [lem:width-transfer] and Theorem [thm:star-local-hard]. -/
def extend (β : E → Bool) : SPMVar G → Bool
  | Sum.inl e => β e
  | Sum.inr ⟨_, f⟩ => f fun e => β e

omit [Fintype U] [Fintype V] [DecidableEq E] in
@[simp] theorem extend_X (β : E → Bool) (e : E) : extend G β (X G e) = β e := rfl

omit [Fintype U] [Fintype V] [DecidableEq E] in
@[simp] theorem extend_Z (β : E → Bool) (w : U ⊕ V) (f : StarFun G w) :
    extend G β (Z G w f) = f fun e => β e := rfl

omit [Fintype U] [Fintype V] in
/-- Every clause of `Def(Z_{w,f})` holds under an extended assignment. -/
theorem sat_defClauses_extend (β : E → Bool) (w : U ⊕ V) (f : StarFun G w) :
    CNF.Sat (extend G β) (defClauses G w f) :=
  (sat_defClauses_iff G _ w f).mpr rfl

/-- `PM(G)` is contained in `SPM(G)`. -/
theorem PM_subset_SPM : PM G ⊆ SPM G := fun C hC => by
  obtain ⟨w, -, hC⟩ := Finset.mem_biUnion.mp hC
  exact exactOne_subset_SPM G w hC

/-- Every variable of `PM(G)` is an edge variable. -/
theorem mem_vars_PM {x : SPMVar G} (hx : x ∈ (PM G).vars) : ∃ e, x = X G e := by
  obtain ⟨C, hC, l, hl, rfl⟩ := CNF.mem_vars.mp hx
  obtain ⟨w, -, hC⟩ := Finset.mem_biUnion.mp hC
  rw [exactOne, Finset.mem_insert] at hC
  rcases hC with rfl | hC
  · obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp hl
    exact ⟨e, rfl⟩
  · obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hC
    rcases Finset.mem_insert.mp hl with rfl | hl
    · exact ⟨p.1, rfl⟩
    · rw [Finset.mem_singleton] at hl
      subst hl
      exact ⟨p.2, rfl⟩

/-! ### Width -/

/-- Every clause of `SPM(G)` has width at most `Δ + 1` when the maximum degree is at most `Δ`. -/
theorem width_SPM_le {Δ : ℕ} (hΔ : G.MaxDegreeLE Δ) : (SPM G).width ≤ Δ + 1 := by
  refine Finset.sup_le fun C hC => ?_
  obtain ⟨w, -, hC⟩ := Finset.mem_biUnion.mp hC
  rw [vertexClauses, Finset.mem_union] at hC
  rcases hC with hC | hC
  · rw [exactOne, Finset.mem_insert] at hC
    rcases hC with rfl | hC
    · exact (Finset.card_image_le.trans (hΔ w)).trans (Nat.le_succ _)
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hC
      rw [Finset.mem_filter, Finset.mem_product] at hp
      have h2 : 2 ≤ G.degree w :=
        Finset.one_lt_card_iff.mpr ⟨p.1, p.2, hp.1.1, hp.1.2, hp.2⟩
      exact Finset.card_le_two.trans (by have := hΔ w; omega)
  · obtain ⟨f, -, hC⟩ := Finset.mem_biUnion.mp hC
    obtain ⟨σ, -, rfl⟩ := Finset.mem_image.mp hC
    calc (defClause G w f σ).card
        ≤ (Finset.univ.image fun e : {e // e ∈ G.star w} =>
            (⟨X G e, !σ e⟩ : Literal (SPMVar G))).card + 1 :=
          (Finset.card_union_le _ _).trans (Nat.add_le_add_left (Finset.card_singleton _).le _)
      _ ≤ (G.star w).card + 1 :=
          Nat.add_le_add_right (Finset.card_image_le.trans_eq
            (Finset.card_univ.trans (Fintype.card_coe _))) 1
      _ ≤ Δ + 1 := Nat.add_le_add_right (hΔ w) 1

/-! ### Unsatisfiability -/

/-- `SPM(G)` is unsatisfiable when `|U| > |V|`: the selected edges would match `U` injectively
into `V`. -/
theorem unsatisfiable (hcard : Fintype.card V < Fintype.card U) : (SPM G).Unsatisfiable := by
  rintro ⟨α, hα⟩
  have hsat : ∀ w, CNF.Sat α (exactOne G w) := fun w => hα.subset (exactOne_subset_SPM G w)
  choose sel hsel using fun u : U => (sat_exactOne_iff G α (.inl u)).mp (hsat (.inl u))
  have hinj : Function.Injective fun u => G.right (sel u) := by
    intro u u' h
    obtain ⟨v, -, -, huniq⟩ := (sat_exactOne_iff G α (.inr (G.right (sel u)))).mp (hsat _)
    have h1 := huniq (sel u) (by simp) (hsel u).2.1
    have h2 := huniq (sel u') (by simpa using h.symm) (hsel u').2.1
    have hu := (G.mem_star_inl).mp (hsel u).1
    have hu' := (G.mem_star_inl).mp (hsel u').1
    rw [← hu, ← hu', h1, h2]
  exact absurd (Fintype.card_le_of_injective _ hinj) (not_le.mpr hcard)

/-! ### Local consequences -/

omit [Fintype U] [Fintype V] in
/-- The clauses `⋀_{w ∈ W} F_w` associated with the vertices of `W`.

Paper: Lemma [lem:star-local-derivations]. -/
def localCNF (W : Finset (U ⊕ V)) : CNF (SPMVar G) := W.biUnion fun w => vertexClauses G w

-- Sanity check: the local CNF of all vertices is `SPM(G)` itself.
example : localCNF G Finset.univ = SPM G := rfl

theorem localCNF_subset_SPM (W : Finset (U ⊕ V)) : localCNF G W ⊆ SPM G :=
  Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.subset_univ W)

omit [Fintype U] [Fintype V] in
/-- The variables of the star of `w`: `X_e` for `e ∈ E(w)` and `Z_{w,f}` for every `f`. -/
def starVars (w : U ⊕ V) : Finset (SPMVar G) :=
  (G.star w).image (X G) ∪ Finset.univ.image (Z G w)

omit [Fintype U] [Fintype V] in
/-- The clauses `F_w` mention only the variables of the star of `w`. -/
theorem vars_vertexClauses_subset (w : U ⊕ V) : (vertexClauses G w).vars ⊆ starVars G w := by
  intro v hv
  obtain ⟨C, hC, l, hl, rfl⟩ := CNF.mem_vars.mp hv
  rw [vertexClauses, Finset.mem_union] at hC
  rcases hC with hC | hC
  · refine Finset.mem_union_left _ ?_
    rw [exactOne, Finset.mem_insert] at hC
    rcases hC with rfl | hC
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hl
      exact Finset.mem_image.mpr ⟨e, he, rfl⟩
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hC
      rw [Finset.mem_filter, Finset.mem_product] at hp
      rcases Finset.mem_insert.mp hl with rfl | hl
      · exact Finset.mem_image.mpr ⟨p.1, hp.1.1, rfl⟩
      · rw [Finset.mem_singleton] at hl
        subst hl
        exact Finset.mem_image.mpr ⟨p.2, hp.1.2, rfl⟩
  · obtain ⟨f, -, hC⟩ := Finset.mem_biUnion.mp hC
    obtain ⟨σ, -, rfl⟩ := Finset.mem_image.mp hC
    rw [defClause, Finset.mem_union] at hl
    rcases hl with hl | hl
    · obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp hl
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, e.2, rfl⟩)
    · rw [Finset.mem_singleton] at hl
      subst hl
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨f, Finset.mem_univ _, rfl⟩)

omit [Fintype U] [Fintype V] in
/-- A star of degree at most `Δ` has at most `Δ + 2^{2^Δ}` variables. -/
theorem card_starVars_le {Δ : ℕ} (hΔ : G.MaxDegreeLE Δ) (w : U ⊕ V) :
    (starVars G w).card ≤ Δ + 2 ^ 2 ^ Δ := by
  refine (Finset.card_union_le _ _).trans (Nat.add_le_add ?_ ?_)
  · exact Finset.card_image_le.trans (hΔ w)
  · refine Finset.card_image_le.trans ?_
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
    exact Nat.pow_le_pow_right two_pos (Nat.pow_le_pow_right two_pos (hΔ w))

/-- `SPM(G)` has at most `(|U| + |V|) (Δ + 2^{2^Δ})` variables. -/
theorem card_SPMVar_le {Δ : ℕ} (hΔ : G.MaxDegreeLE Δ) :
    Fintype.card (SPMVar G) ≤ (Fintype.card U + Fintype.card V) * (Δ + 2 ^ 2 ^ Δ) := by
  have hsub : (Finset.univ : Finset (SPMVar G)) ⊆ Finset.univ.biUnion (starVars G) := by
    intro x _
    rcases x with e | ⟨w, f⟩
    · exact Finset.mem_biUnion.mpr ⟨Sum.inl (G.left e), Finset.mem_univ _,
        Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, G.mem_star_inl.mpr rfl, rfl⟩)⟩
    · exact Finset.mem_biUnion.mpr ⟨w, Finset.mem_univ _,
        Finset.mem_union_right _ (Finset.mem_image.mpr ⟨f, Finset.mem_univ _, rfl⟩)⟩
  calc Fintype.card (SPMVar G) = (Finset.univ : Finset (SPMVar G)).card := Finset.card_univ.symm
    _ ≤ (Finset.univ.biUnion (starVars G)).card := Finset.card_le_card hsub
    _ ≤ ∑ w, (starVars G w).card := Finset.card_biUnion_le
    _ ≤ (Finset.univ : Finset (U ⊕ V)).card • (Δ + 2 ^ 2 ^ Δ) :=
        Finset.sum_le_card_nsmul _ _ _ fun w _ => card_starVars_le G hΔ w
    _ = (Fintype.card U + Fintype.card V) * (Δ + 2 ^ 2 ^ Δ) := by
        rw [smul_eq_mul, Finset.card_univ, Fintype.card_sum]

omit [Fintype U] [Fintype V] in
theorem vars_localCNF_subset (W : Finset (U ⊕ V)) :
    (localCNF G W).vars ⊆ W.biUnion (starVars G) := by
  intro v hv
  obtain ⟨C, hC, hl⟩ := CNF.mem_vars.mp hv
  obtain ⟨w, hw, hC⟩ := Finset.mem_biUnion.mp hC
  exact Finset.mem_biUnion.mpr
    ⟨w, hw, vars_vertexClauses_subset G w (CNF.mem_vars.mpr ⟨C, hC, hl⟩)⟩

omit [Fintype U] [Fintype V] in
/-- The clauses `⋀_{w ∈ W} F_w` mention at most `|W| (Δ + 2^{2^Δ})` variables. -/
theorem card_vars_localCNF_le {Δ : ℕ} (hΔ : G.MaxDegreeLE Δ) (W : Finset (U ⊕ V)) :
    (localCNF G W).vars.card ≤ W.card * (Δ + 2 ^ 2 ^ Δ) :=
  calc (localCNF G W).vars.card ≤ (W.biUnion (starVars G)).card :=
        Finset.card_le_card (vars_localCNF_subset G W)
    _ ≤ ∑ w ∈ W, (starVars G w).card := Finset.card_biUnion_le
    _ ≤ W.card • (Δ + 2 ^ 2 ^ Δ) :=
        Finset.sum_le_card_nsmul _ _ _ fun w _ => card_starVars_le G hΔ w
    _ = W.card * (Δ + 2 ^ 2 ^ Δ) := smul_eq_mul _ _

omit [Fintype U] [Fintype V] in
/-- **Local consequences have constant-size derivations.** A nontautological clause implied by
the clauses `⋀_{w ∈ W} F_w` has a subclause with a derivation from them of size at most
`2 ^ (2 |W| (Δ + 2^{2^Δ}))`, a bound depending only on `|W|` and `Δ`.

The paper assumes in addition that `C` mentions only the variables of the stars of `W`; the
bound holds without this assumption, since every clause of a derivation from `⋀_{w ∈ W} F_w`
mentions only those variables.

Paper: Lemma [lem:star-local-derivations]. -/
theorem exists_derivation_localCNF {Δ : ℕ} (hΔ : G.MaxDegreeLE Δ) (W : Finset (U ⊕ V))
    {C : Clause (SPMVar G)} (h : (localCNF G W).Implies C) (hC : ¬ C.IsTautology) :
    ∃ D ⊆ C, ∃ π : Derivation (localCNF G W) D,
      π.size ≤ 2 ^ (2 * (W.card * (Δ + 2 ^ 2 ^ Δ))) := by
  obtain ⟨D, hD, π, hπ⟩ := h.exists_derivation_size_le hC
  exact ⟨D, hD, π, hπ.trans (Nat.pow_le_pow_right two_pos
    (Nat.mul_le_mul_left 2 (card_vars_localCNF_le G hΔ W)))⟩

end SPM

end AssocLB
