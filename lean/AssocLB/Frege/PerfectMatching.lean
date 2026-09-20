/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/
import AssocLB.LowerBound

/-!
# Perfect matching over the edge variables

Paper: Definition [def:pm] (the perfect-matching CNF `PM(H)`), as used in Section 9, where the
extension variables `Z_{w,f}` of Section 5 "are no longer needed": the Frege reduction
substitutes a constant-size formula for each wire directly, so the target of Lemma
[lem:frege-transfer] and the formula of Theorem [thm:hastad] are `PM(H)` over the edge
variables alone.

## Main definitions

* `SPM.projX G`: the substitution forgetting the extension variables, `X_e ↦ X_e` and
  `Z_{w,f} ↦ 0`.
* `EdgePM.exactOne G w`: `ExactOne(X_{E(w)})` over the edge variables, the image of
  `SPM.exactOne G w` under `SPM.projX G`; `EdgePM.localCNF G W`: the `ExactOne` clauses at
  the vertices of `W`.
* `EdgePM G`: the perfect-matching CNF `PM(G)` over the edge variables `E`.

## Main results

* `EdgePM.sat_exactOne_iff`: `ExactOne(X_{E(w)})` is satisfied exactly when the edge assignment
  selects exactly one edge at `w` (`ExactOneAt`).
* `EdgePM.card_exactOne_le`, `EdgePM.width_exactOne_le`, `EdgePM.vars_exactOne_subset`: at a
  vertex of degree at most `Δ` there are at most `Δ² + 1` clauses, of width at most `Δ`, over
  the edges of the star.
* `EdgePM.unsatisfiable`: `PM(G)` is unsatisfiable when `|U| > |V|`.

## Design notes

* `PM G` of `AssocLB.Matching.StarLocalPM` is a CNF over `SPMVar G = E ⊕ Σ w, StarFun G w`,
  the variable type of the star-local extension, in which the extension variables do not
  occur. Håstad's theorem is about `PM(Grid_t)` over its own variables, so, to import it
  faithfully, `EdgePM G` is the same CNF over `E`. It is obtained by substitution rather than
  by redefining the clauses, so that the semantics of `SPM.exactOne` transfers through
  `CNF.sat_subst_iff`.
* `ExactOneAt` is defined in `AssocLB.LowerBound`, hence the import.
-/

namespace AssocLB

namespace SPM

variable {U V E : Type*} (G : Bipartite U V E) [Fintype E] [DecidableEq U] [DecidableEq V]

/-- The substitution forgetting the extension variables: `X_e ↦ X_e`, `Z_{w,f} ↦ 0`. -/
def projX : Subst (SPMVar G) E := fun x =>
  match x with
  | .inl e => .lit (.pos e)
  | .inr _ => .const false

@[simp] theorem projX_X (e : E) : projX G (X G e) = .lit (.pos e) := rfl

@[simp] theorem projX_Z (w : U ⊕ V) (f : StarFun G w) : projX G (Z G w f) = .const false := rfl

/-- The pullback of an edge assignment along `projX` agrees with it on the edge variables. -/
theorem pullback_projX_X (β : E → Bool) (e : E) : (projX G).pullback β (X G e) = β e := by
  cases hb : β e <;> simp [Subst.pullback, LitConst.eval, Literal.Sat, hb]

end SPM

variable {U V E : Type*} (G : Bipartite U V E) [Fintype U] [Fintype V] [Fintype E]
  [DecidableEq U] [DecidableEq V] [DecidableEq E]

namespace EdgePM

/-- `ExactOne(X_{E(w)})` over the edge variables.

Paper: Definition [def:pm]. -/
def exactOne (w : U ⊕ V) : CNF E := (SPM.exactOne G w).subst (SPM.projX G)

/-- The `ExactOne` clauses at the vertices of `W`. -/
def localCNF (W : Finset (U ⊕ V)) : CNF E := W.biUnion fun w => exactOne G w

end EdgePM

/-- The perfect-matching CNF `PM(G)` over the edge variables: exactly one edge is selected at
every vertex.

Paper: Definition [def:pm]; Section 9. -/
def EdgePM : CNF E := Finset.univ.biUnion fun w => EdgePM.exactOne G w

omit [Fintype U] [Fintype V] [DecidableEq E] in
/-- `β` selects exactly one edge at `w` if and only if some selected edge at `w` is the only
one. -/
theorem exactOneAt_iff (β : E → Bool) (w : U ⊕ V) :
    ExactOneAt G β w ↔ ∃ e ∈ G.star w, β e = true ∧ ∀ f ∈ G.star w, β f = true → f = e := by
  rw [ExactOneAt, Finset.card_eq_one]
  constructor
  · rintro ⟨e, he⟩
    have he' : e ∈ (G.star w).filter fun e => β e = true := by
      rw [he]
      exact Finset.mem_singleton_self e
    rw [Finset.mem_filter] at he'
    refine ⟨e, he'.1, he'.2, fun f hf hβf => ?_⟩
    have hf' : f ∈ (G.star w).filter fun e => β e = true := Finset.mem_filter.mpr ⟨hf, hβf⟩
    rw [he] at hf'
    exact Finset.mem_singleton.mp hf'
  · rintro ⟨e, he, hβe, huniq⟩
    refine ⟨e, Finset.ext fun f => ?_⟩
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hf, hβf⟩
      exact huniq f hf hβf
    · rintro rfl
      exact ⟨he, hβe⟩

namespace EdgePM

variable (β : E → Bool)

omit [Fintype U] [Fintype V] in
/-- `ExactOne(X_{E(w)})` holds exactly when `β` selects one edge at `w`. -/
theorem sat_exactOne_iff (w : U ⊕ V) : CNF.Sat β (exactOne G w) ↔ ExactOneAt G β w := by
  rw [exactOne, CNF.sat_subst_iff, SPM.sat_exactOne_iff, exactOneAt_iff]
  simp only [SPM.pullback_projX_X]

theorem sat_EdgePM_iff : CNF.Sat β (EdgePM G) ↔ ∀ w, ExactOneAt G β w := by
  rw [EdgePM, CNF.sat_biUnion_iff]
  simp only [Finset.mem_univ, true_implies, sat_exactOne_iff]

omit [Fintype U] [Fintype V] in
theorem sat_localCNF_iff (W : Finset (U ⊕ V)) :
    CNF.Sat β (localCNF G W) ↔ ∀ w ∈ W, ExactOneAt G β w := by
  rw [localCNF, CNF.sat_biUnion_iff]
  simp only [sat_exactOne_iff]

theorem exactOne_subset (w : U ⊕ V) : exactOne G w ⊆ EdgePM G := fun _ hC =>
  Finset.mem_biUnion.mpr ⟨w, Finset.mem_univ _, hC⟩

theorem localCNF_subset (W : Finset (U ⊕ V)) : localCNF G W ⊆ EdgePM G := by
  intro C hC
  obtain ⟨w, -, hC⟩ := Finset.mem_biUnion.mp hC
  exact exactOne_subset G w hC

omit [Fintype U] [Fintype V] in
/-- The variables of `ExactOne(X_{E(w)})` are the edges at `w`. -/
theorem vars_exactOne_subset (w : U ⊕ V) : (exactOne G w).vars ⊆ G.star w := by
  intro e he
  obtain ⟨D, hD, m, hm, rfl⟩ := CNF.mem_vars.mp he
  obtain ⟨C, hC, -, rfl⟩ := CNF.mem_subst.mp hD
  obtain ⟨l, hl, hlm⟩ := Clause.mem_subst.mp hm
  have hCv : C ∈ SPM.vertexClauses G w := by
    rw [SPM.vertexClauses]
    exact Finset.mem_union_left _ hC
  have hv : l.var ∈ SPM.starVars G w :=
    SPM.vars_vertexClauses_subset G w (CNF.mem_vars.mpr ⟨C, hCv, l, hl, rfl⟩)
  rw [SPM.starVars, Finset.mem_union] at hv
  rcases hv with hv | hv
  · -- the variable is an edge variable `X_{e'}`, which `projX` keeps
    obtain ⟨e', he', hXe⟩ := Finset.mem_image.mp hv
    rcases Literal.eq_pos_or_eq_neg l with hl' | hl'
    · rw [hl', ← hXe, Literal.subst_pos, SPM.projX_X] at hlm
      obtain rfl := LitConst.lit.inj hlm
      simpa using he'
    · rw [hl', ← hXe, Literal.subst_neg, SPM.projX_X, LitConst.compl_lit, Literal.compl_pos] at hlm
      obtain rfl := LitConst.lit.inj hlm
      simpa using he'
  · -- the variable is an extension variable, which `projX` sends to a constant
    obtain ⟨f, -, hZ⟩ := Finset.mem_image.mp hv
    rcases Literal.eq_pos_or_eq_neg l with hl' | hl'
    · rw [hl', ← hZ, Literal.subst_pos, SPM.projX_Z] at hlm
      cases hlm
    · rw [hl', ← hZ, Literal.subst_neg, SPM.projX_Z, LitConst.compl_const] at hlm
      cases hlm

omit [Fintype U] [Fintype V] in
/-- At a vertex of degree at most `Δ` there are at most `Δ² + 1` clauses. -/
theorem card_exactOne_le {Δ : ℕ} (hΔ : G.MaxDegreeLE Δ) (w : U ⊕ V) :
    (exactOne G w).card ≤ Δ ^ 2 + 1 := by
  have hdeg : (G.star w).card ≤ Δ := hΔ w
  calc (exactOne G w).card ≤ (SPM.exactOne G w).card := by
        unfold exactOne CNF.subst
        exact Finset.card_image_le.trans (Finset.card_filter_le _ _)
    _ ≤ (SPM.atMostOne G w).card + 1 := Finset.card_insert_le _ _
    _ ≤ (G.star w ×ˢ G.star w).card + 1 := by
        unfold SPM.atMostOne
        exact Nat.add_le_add_right (Finset.card_image_le.trans (Finset.card_filter_le _ _)) 1
    _ ≤ Δ ^ 2 + 1 := by
        rw [Finset.card_product, sq]
        exact Nat.add_le_add_right (Nat.mul_le_mul hdeg hdeg) 1

omit [Fintype U] [Fintype V] in
/-- The clauses at a vertex of degree at most `Δ` have width at most `Δ`. -/
theorem width_exactOne_le {Δ : ℕ} (hΔ : G.MaxDegreeLE Δ) (w : U ⊕ V) :
    (exactOne G w).width ≤ Δ := by
  refine (CNF.width_subst_le _ _).trans ?_
  rw [CNF.width, Finset.sup_le_iff]
  intro C hC
  rw [SPM.exactOne, Finset.mem_insert] at hC
  rcases hC with rfl | hC
  · exact Finset.card_image_le.trans (hΔ w)
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hC
    rw [Finset.mem_filter, Finset.mem_product] at hp
    have hpair : ({p.1, p.2} : Finset E) ⊆ G.star w := by
      intro e he
      rw [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl
      · exact hp.1.1
      · exact hp.1.2
    have h2 := Finset.card_le_card hpair
    rw [Finset.card_pair hp.2] at h2
    exact Finset.card_le_two.trans (h2.trans (hΔ w))

/-- `PM(G)` is unsatisfiable when `|U| > |V|`.

Paper: Section 5, after Definition [def:pm]. -/
theorem unsatisfiable (hcard : Fintype.card V < Fintype.card U) : (EdgePM G).Unsatisfiable := by
  rintro ⟨β, hβ⟩
  rw [sat_EdgePM_iff] at hβ
  -- the selected edge at each vertex
  have hsel : ∀ w, ∃ e ∈ G.star w, β e = true ∧ ∀ f ∈ G.star w, β f = true → f = e :=
    fun w => (exactOneAt_iff G β w).mp (hβ w)
  choose sel hsel_mem hsel_true hsel_uniq using hsel
  -- selecting edges matches `U` injectively into `V`
  have hf : Function.Injective fun u => G.right (sel (Sum.inl u)) := by
    intro u u' h
    have h1 : sel (Sum.inl u) ∈ G.star (Sum.inr (G.right (sel (Sum.inl u)))) :=
      G.mem_star_inr.mpr rfl
    have h2 : sel (Sum.inl u') ∈ G.star (Sum.inr (G.right (sel (Sum.inl u)))) :=
      G.mem_star_inr.mpr h.symm
    have heq : sel (Sum.inl u) = sel (Sum.inl u') :=
      (hsel_uniq _ _ h1 (hsel_true _)).trans (hsel_uniq _ _ h2 (hsel_true _)).symm
    calc u = G.left (sel (Sum.inl u)) := (G.mem_star_inl.mp (hsel_mem (Sum.inl u))).symm
      _ = G.left (sel (Sum.inl u')) := by rw [heq]
      _ = u' := G.mem_star_inl.mp (hsel_mem (Sum.inl u'))
  exact absurd (Fintype.card_le_of_injective _ hf) (not_le.mpr hcard)

end EdgePM

end AssocLB
