/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/
import AssocLB.Frege.Substitution

/-!
# Local consequences have constant-size Frege derivations

Paper: Section 9.1 (Bounded-depth Frege systems), Lemma [lem:frege-local-derivations]: if a
set of clauses over `k` variables implies a formula `G`, then `G` has a derivation from them
whose depth and size depend only on `k` and `|G|`. This is the Frege analogue of Lemma
[lem:star-local-derivations], and follows from implicational completeness.

## Main results

* `FregeSystem.exists_local_derivation`: the finiteness argument in general. For all `k`, `c`
  and `s` there are `D` and `S` such that a formula `G` of size at most `s` implied by at most
  `c` formulas of size at most `s`, all over at most `k` variables, has a derivation from them
  of depth at most `D` and size at most `S`.
* `FregeSystem.exists_local_derivation_cnf`: Lemma [lem:frege-local-derivations]. For all `k`
  and `s` there are `D` and `S` such that a formula `G` of size at most `s` implied by a CNF
  `Φ`, both over at most `k` variables, has a derivation from `Φ.toFormulas` of depth at most
  `D` and size at most `S`.

## Auxiliary definitions

* `Formula.finsetSizeLE k s`: a finite set containing every formula over `Fin k` of size at
  most `s`.
* `Formula.renameTo X hk`, `Formula.renameBack X k`: for `X` a set of at most `k` variables,
  the renaming of the variables of `X` to `Fin k` and its inverse, as substitutions by
  variables (variables outside their domains map to `⊥`); `Formula.subst_renameTo_renameBack`
  is the round trip on formulas over `X`.

## Design notes

* The paper's "depend only on `k` and `|G|`" is the order of quantifiers `∀ k s, ∃ D S, ∀ …`,
  with the variable type quantified inside.
* The proof renames the at most `k` variables to `Fin k` (a substitution by variables, Lemma
  [lem:frege-substitution]), applies completeness to each of the finitely many pairs of a set
  of at most `c` formulas of size at most `s` and a formula of size at most `s` over `Fin k`,
  and takes the maximum. The version for sets of formulas is proved first, because renaming a
  clause does not commute with `Clause.toFormula`: the order of `Finset.toList` is arbitrary,
  so the images of clause formulas are formulas, not clause formulas, of the renamed clauses.
  The CNF version follows since a CNF over `k` variables has at most `2^{2k}` clauses, each of
  which is a formula of size at most `3k + 1`.
-/

namespace AssocLB

namespace Formula

/-! ### Finitely many formulas of bounded size -/

/-- A finite set containing every formula over `Fin k` of size at most `s`. -/
def finsetSizeLE (k : ℕ) : ℕ → Finset (Formula (Fin k))
  | 0 => ∅
  | s + 1 =>
    insert bot (Finset.univ.image var) ∪ (finsetSizeLE k s).image neg ∪
      ((finsetSizeLE k s ×ˢ finsetSizeLE k s).image fun p => or p.1 p.2)

/-- Every formula over `Fin k` of size at most `s` lies in `finsetSizeLE k s`. -/
theorem mem_finsetSizeLE_of_size_le {k : ℕ} {F : Formula (Fin k)} :
    ∀ {s : ℕ}, F.size ≤ s → F ∈ finsetSizeLE k s := by
  induction F with
  | var v =>
    intro s hs
    obtain ⟨s, rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by simp at hs; omega⟩
    simp [finsetSizeLE]
  | bot =>
    intro s hs
    obtain ⟨s, rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by simp at hs; omega⟩
    simp [finsetSizeLE]
  | neg F ih =>
    intro s hs
    obtain ⟨s, rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by simp at hs; omega⟩
    simp only [finsetSizeLE, Finset.mem_union]
    exact Or.inl (Or.inr (Finset.mem_image_of_mem _ (ih (by simp at hs; omega))))
  | or F G ihF ihG =>
    intro s hs
    obtain ⟨s, rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by simp at hs; omega⟩
    simp only [finsetSizeLE, Finset.mem_union]
    refine Or.inr (Finset.mem_image.mpr ⟨(F, G), Finset.mem_product.mpr ⟨ihF ?_, ihG ?_⟩, rfl⟩)
    · simp at hs
      omega
    · simp at hs
      omega

/-! ### Renaming variables to `Fin k` -/

variable {V : Type*} [DecidableEq V]

/-- The renaming of the variables of `X` to `Fin k`, for `|X| ≤ k`: the `i`-th element of `X`
maps to the variable `i`, and the variables outside `X` map to `⊥`. -/
noncomputable def renameTo (X : Finset V) {k : ℕ} (hk : X.card ≤ k) : V → Formula (Fin k) :=
  fun v => if h : v ∈ X then var (Fin.castLE hk (X.equivFin ⟨v, h⟩)) else bot

/-- The inverse renaming: the variable `i < |X|` maps to the `i`-th element of `X`, and the
other variables map to `⊥`. -/
noncomputable def renameBack (X : Finset V) (k : ℕ) : Fin k → Formula V :=
  fun i => if h : i.val < X.card then var (X.equivFin.symm ⟨i.val, h⟩).1 else bot

theorem size_renameTo_le (X : Finset V) {k : ℕ} (hk : X.card ≤ k) (v : V) :
    (renameTo X hk v).size ≤ 1 := by
  unfold renameTo
  split <;> simp

omit [DecidableEq V] in
theorem size_renameBack_le (X : Finset V) (k : ℕ) (i : Fin k) : (renameBack X k i).size ≤ 1 := by
  unfold renameBack
  split <;> simp

omit [DecidableEq V] in
theorem depth_renameBack_le (X : Finset V) (k : ℕ) (i : Fin k) :
    (renameBack X k i).depth ≤ 0 := by
  unfold renameBack
  split <;> simp

/-- Renaming a variable of `X` and renaming back gives the variable. -/
theorem renameTo_subst_renameBack {X : Finset V} {k : ℕ} (hk : X.card ≤ k) {v : V} (hv : v ∈ X) :
    (renameTo X hk v).subst (renameBack X k) = var v := by
  simp [renameTo, renameBack, hv]

/-- Renaming a formula over `X` and renaming back gives the formula. -/
theorem subst_renameTo_renameBack {X : Finset V} {k : ℕ} (hk : X.card ≤ k) {F : Formula V}
    (hF : F.vars ⊆ X) : (F.subst (renameTo X hk)).subst (renameBack X k) = F := by
  rw [subst_subst]
  exact (subst_congr fun v hv => renameTo_subst_renameBack hk (hF hv)).trans (subst_var_eq F)

end Formula

namespace FregeSystem

variable (𝓕 : FregeSystem)

/-- **Constant-size derivations of local consequences, for sets of formulas.** For all `k`,
`c` and `s` there are `D` and `S` such that whenever at most `c` formulas of size at most `s`
over a set `X` of at most `k` variables imply a formula `G` of size at most `s` over `X`, the
formula `G` has a derivation from them of depth at most `D` and size at most `S`. -/
theorem exists_local_derivation (k c s : ℕ) :
    ∃ D S : ℕ, ∀ (V : Type) [DecidableEq V] (X : Finset V) (Γ : Finset (Formula V))
      (G : Formula V), X.card ≤ k → Γ.card ≤ c → (∀ F ∈ Γ, F.vars ⊆ X ∧ F.size ≤ s) →
      G.vars ⊆ X → G.size ≤ s → Formula.Implies (↑Γ) G →
      ∃ δ : 𝓕.Derivation (↑Γ) G, δ.depth ≤ D ∧ δ.size ≤ S := by
  classical
  -- the admissible pairs over `Fin k`, and the depth and size of a derivation for each
  let P : Finset (Finset (Formula (Fin k)) × Formula (Fin k)) :=
    ((Formula.finsetSizeLE k s).powerset.filter fun Γ' => Γ'.card ≤ c) ×ˢ
      Formula.finsetSizeLE k s
  let dep : Finset (Formula (Fin k)) × Formula (Fin k) → ℕ := fun p =>
    if h : Formula.Implies (↑p.1) p.2 then (Classical.choice (𝓕.complete k p.1 p.2 h)).depth
    else 0
  let sz : Finset (Formula (Fin k)) × Formula (Fin k) → ℕ := fun p =>
    if h : Formula.Implies (↑p.1) p.2 then (Classical.choice (𝓕.complete k p.1 p.2 h)).size
    else 0
  refine ⟨P.sup dep + 1, P.sup sz, fun V _ X Γ G hX hΓc hΓ hG hGs himp => ?_⟩
  -- rename the variables of `X` to `Fin k`
  have hren : ∀ v, (Formula.renameTo X hX v).size ≤ 1 := Formula.size_renameTo_le X hX
  have hΓ' : Γ.image (Formula.subst (Formula.renameTo X hX)) ∈
      (Formula.finsetSizeLE k s).powerset.filter fun Γ' => Γ'.card ≤ c := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨fun F' hF' => ?_, Finset.card_image_le.trans hΓc⟩
    obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hF'
    exact Formula.mem_finsetSizeLE_of_size_le
      ((Formula.size_subst_le le_rfl hren F).trans (by simpa using (hΓ F hF).2))
  have hG' : G.subst (Formula.renameTo X hX) ∈ Formula.finsetSizeLE k s :=
    Formula.mem_finsetSizeLE_of_size_le
      ((Formula.size_subst_le le_rfl hren G).trans (by simpa using hGs))
  have hpair : (Γ.image (Formula.subst (Formula.renameTo X hX)),
      G.subst (Formula.renameTo X hX)) ∈ P :=
    Finset.mem_product.mpr ⟨hΓ', hG'⟩
  have himp' : Formula.Implies (↑(Γ.image (Formula.subst (Formula.renameTo X hX))))
      (G.subst (Formula.renameTo X hX)) := by
    rw [Finset.coe_image]
    exact himp.subst _
  -- the chosen derivation over `Fin k`
  obtain ⟨δ', hδ'd, hδ's⟩ : ∃ δ' : 𝓕.Derivation
      (↑(Γ.image (Formula.subst (Formula.renameTo X hX)))) (G.subst (Formula.renameTo X hX)),
      δ'.depth ≤ P.sup dep ∧ δ'.size ≤ P.sup sz := by
    refine ⟨Classical.choice (𝓕.complete k _ _ himp'), ?_, ?_⟩
    · have := Finset.le_sup (f := dep) hpair
      simpa [dep, dif_pos himp'] using this
    · have := Finset.le_sup (f := sz) hpair
      simpa [sz, dif_pos himp'] using this
  -- rename back
  refine ⟨((δ'.subst (Formula.renameBack X k)).mono ?_).copy
    (Formula.subst_renameTo_renameBack hX hG), ?_, ?_⟩
  · rintro F ⟨F₁, hF₁, rfl⟩
    obtain ⟨F₀, hF₀, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hF₁)
    rw [Formula.subst_renameTo_renameBack hX (hΓ F₀ hF₀).1]
    exact Finset.mem_coe.mpr hF₀
  · change (δ'.subst (Formula.renameBack X k)).depth ≤ P.sup dep + 1
    have := δ'.depth_subst_le (Formula.depth_renameBack_le X k)
    omega
  · change (δ'.subst (Formula.renameBack X k)).size ≤ P.sup sz
    have := δ'.size_subst_le le_rfl (Formula.size_renameBack_le X k)
    omega

/-- **Local consequences have constant-size Frege derivations.** For all `k` and `s` there are
`D` and `S` such that whenever a CNF `Φ` over a set `X` of at most `k` variables implies a
formula `G` of size at most `s` over `X`, the formula `G` has a derivation from the formulas
of `Φ` of depth at most `D` and size at most `S`.

Paper: Lemma [lem:frege-local-derivations]. -/
theorem exists_local_derivation_cnf (k s : ℕ) :
    ∃ D S : ℕ, ∀ (V : Type) [DecidableEq V] (X : Finset V) (Φ : CNF V) (G : Formula V),
      X.card ≤ k → Φ.vars ⊆ X → G.vars ⊆ X → G.size ≤ s → (∀ α, Φ.Sat α → G.eval α = true) →
      ∃ δ : 𝓕.Derivation Φ.toFormulas G, δ.depth ≤ D ∧ δ.size ≤ S := by
  obtain ⟨D, S, h⟩ := 𝓕.exists_local_derivation k (2 ^ (2 * k)) (max (6 * k + 1) s)
  refine ⟨D, S, fun V _ X Φ G hX hΦ hG hGs himp => ?_⟩
  have hC : ∀ C ∈ Φ, C.vars ⊆ X := fun C hC =>
    (Finset.subset_biUnion_of_mem Clause.vars hC).trans hΦ
  obtain ⟨δ, hd, hs⟩ := h V X (Φ.image Clause.toFormula) G hX
    (Finset.card_image_le.trans ((Clause.card_le_of_vars_subset hC).trans
      (Nat.pow_le_pow_right two_pos (by omega))))
    (fun F hF => by
      obtain ⟨C, hCΦ, rfl⟩ := Finset.mem_image.mp hF
      refine ⟨by rw [Clause.vars_toFormula]; exact hC C hCΦ, ?_⟩
      have h1 : C.card ≤ 2 * X.card :=
        (Finset.card_le_card (Clause.subset_ofVars (hC C hCΦ))).trans (Literal.card_ofVars_le X)
      have h2 := Clause.size_toFormula_le C
      omega)
    hG (hGs.trans (le_max_right _ _))
    (by rw [Finset.coe_image]; exact (CNF.implies_toFormulas_iff Φ G).mpr himp)
  refine ⟨δ.mono (by rw [Finset.coe_image]; exact subset_rfl), ?_, ?_⟩
  · change δ.depth ≤ D
    exact hd
  · change δ.size ≤ S
    exact hs

end FregeSystem

end AssocLB
