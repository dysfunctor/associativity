/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/
import AssocLB.Reduction.Outline
import AssocLB.Reduction.Locality
import AssocLB.Matching.StarLocalHard
import AssocLB.Matching.ISSGraphs
import AssocLB.Multiplier.ArrayStripLocal
import AssocLB.Multiplier.WallaceStripLocal

/-!
# Lower bound for `Assoc_n`

Paper: Section 8 (Lower bound for `Assoc_n`): Lemma [lem:local-soundness] (local soundness),
Lemma [lem:reduction] (reduction from perfect matching) and Theorem
[thm:main] (lower bound for multiplier associativity).

## Main definitions

* `ExactOneAt H β w`: the edge assignment `β` selects exactly one edge at `w`.
* `restrictFn H F w`: a function of edge assignments restricted to the star `E(w)`, as a
  Boolean function of the edges at `w`.
* `Assoc.sigma I M₁ M₂`: the substitution `σ` of Lemma [lem:reduction]: a variable fixed by
  `ρ` or computing a constant maps to that constant, and every other variable, a function `f`
  of a single star `E(w)`, maps to the extension variable `Z_{w,f}`.
* `reductionConst Δ w`: the constant `2^(2 · 2Δw · (Δ + 2^{2^Δ}))` bounding the size of the
  derivation of a restricted, substituted clause of width at most `w`.

## Main results

* `Assoc.sat_propagate_of_exactOne_supp`: Lemma [lem:local-soundness].
* `Assoc.pullback_sigma_eq`: under the defining clauses of the extension variables on the
  support of `C`, the substituted values agree with the propagated values on the variables
  of `C`.
* `Assoc.exists_refutation_SPM`: Lemma [lem:reduction], a refutation of `Assoc_n` yields a
  refutation of `SPM(H)` of size at most `(reductionConst Δ w + 1)` times as large.
* `main_explicit`: Theorem [thm:main] in explicit form. For a strip-local family of
  encodings, assuming Theorem [thm:iss-graphs] and the size–width tradeoff, there are `c > 0`
  and `m₀` such that for every `m ≥ m₀` and every `n ≥ n₀(m) = O(m⁴ log m)`, every
  resolution refutation of `Assoc_n` has size at least `exp(c m)`.
* `main`: Theorem [thm:main] in asymptotic form, size `2^{Ω((n / log n)^{1/4})}`, for any
  strip-local family, with Theorems [thm:iss-graphs] and [thm:bw] as explicit hypotheses.
  Both are theorems (`issGraphs`, `bwTradeoff`), so `main M hM issGraphs bwTradeoff` is the
  unconditional bound for every strip-local family `M`; `main_arrayMul`, `main_wallaceMul`
  are its instances for the array multiplier and the Wallace-tree multiplier.

## Design notes

* The paper maps the unset input bits `y_{j(e)}` to `X_e` and edge-local wires to the literals
  they compute; here every non-constant variable maps to an extension variable `Z_{w,f}`,
  which is sound since `Def(Z_{w,f})` forces `Z_{w,f}` to the same value. Constant variables
  must map to constants: their star is arbitrary and need not lie in the support.
* Lemma [lem:local-soundness] modifies the edge assignment outside the support to select one
  edge at every vertex of one side; this needs a vertex without edges not to exist, which the
  expanders provide (`ExpanderGraph.exists_edge_left`, `ExpanderGraph.exists_edge_right`).
* The size bound of Lemma [lem:reduction] counts only the initial clauses the refutation uses,
  by `Refutation.reduce`, which gives the paper's constant factor.
-/

namespace AssocLB

/-! ### Exactly one edge at a vertex -/

section ExactOne

variable {U V E : Type*} (H : Bipartite U V E) [Fintype E] [DecidableEq U] [DecidableEq V]

/-- The edge assignment `β` selects exactly one edge at `w`. -/
def ExactOneAt (β : E → Bool) (w : U ⊕ V) : Prop :=
  ((H.star w).filter fun e => β e = true).card = 1

variable {H}

/-- An assignment satisfying `ExactOne(X_{E(w)})` selects exactly one edge at `w`. -/
theorem exactOneAt_of_sat_exactOne [DecidableEq E] {α : SPMVar H → Bool} {w : U ⊕ V}
    (h : CNF.Sat α (SPM.exactOne H w)) : ExactOneAt H (fun e => α (SPM.X H e)) w := by
  obtain ⟨e, he, hαe, huniq⟩ := (SPM.sat_exactOne_iff H α w).mp h
  refine Finset.card_eq_one.mpr ⟨e, Finset.ext fun f => ?_⟩
  rw [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hf, hαf⟩
    exact huniq f hf hαf
  · rintro rfl
    exact ⟨he, hαe⟩

/-- The restriction of a function of edge assignments to the star `E(w)`, as a Boolean function
of the edges at `w`. -/
def restrictFn [DecidableEq E] (F : (E → Bool) → Bool) (w : U ⊕ V) : StarFun H w :=
  fun τ => F fun e => if h : e ∈ H.star w then τ ⟨e, h⟩ else false

/-- A function of the star `E(w)` is recovered from its restriction. -/
theorem restrictFn_apply [DecidableEq E] {w : U ⊕ V} {F : (E → Bool) → Bool}
    (h : StarLocalFn H w F)
    (β : E → Bool) : restrictFn (H := H) F w (fun e => β e) = F β :=
  h _ _ fun e he => by rw [dif_pos he]

end ExactOne

namespace Assoc

variable {U V E : Type*} {H : Bipartite U V E} {g K n₀ : ℕ} (I : IndexMaps H g K n₀)
  [Fintype U] [Fintype V] [Fintype E] [DecidableEq U] [DecidableEq V] [DecidableEq E] {n : ℕ}
  (M₁ : MulEncoding n) (M₂ : MulEncoding (2 * n))

/-! ### Lemma [lem:local-soundness] -/

omit [DecidableEq E] in
/-- The miter clause is satisfied by `ρ`, which sets `e_K = 1`. -/
theorem satBy_miterClause (hn : n₀ ≤ n) :
    (miterClause n M₁.Wire M₂.Wire).SatBy (rho I M₁ M₂) := by
  have hK : K < 2 * (2 * n) := by have := I.K_lt; omega
  refine ⟨Literal.pos (.e ⟨K, hK⟩), ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨⟨K, hK⟩, Finset.mem_univ _, rfl⟩
  · change rho I M₁ M₂ (.e ⟨K, hK⟩) = some true
    rw [rho_e, if_pos rfl]

/-- The propagated assignments of two edge assignments agreeing on the edges the variables of
`C` depend on agree on the variables of `C`. -/
theorem propagate_eq_on_vars {C : Clause (AssocVar n M₁.Wire M₂.Wire)} {β β' : E → Bool}
    (h : ∀ q ∈ C.vars, ∀ e ∈ deps (valFn I M₁ M₂ q), β e = β' e) :
    ∀ q ∈ C.vars, propagate I M₁ M₂ β q = propagate I M₁ M₂ β' q :=
  fun q hq => eq_of_agree_on_deps (valFn I M₁ M₂ q) β β' (h q hq)

/-- **Local soundness.** If the edge assignment `β` selects exactly
one edge at every vertex of the support of a clause `C` of `Assoc_n↾ρ`, then the propagated
assignment `β̄` satisfies `C`.

Paper: Lemma [lem:local-soundness]. -/
theorem sat_propagate_of_exactOne_supp (hn : n₀ ≤ n) (hg : 1 ≤ g)
    (hsp : (inputXY I M₁ M₂).IsSparse g) (hsp' : (inputYZ I M₁ M₂).IsSparse g)
    (hsp₁ : (inputXY_Z I M₁ M₂).IsSparse g) (hsp₂ : (inputX_YZ I M₁ M₂).IsSparse g)
    (hcard : Fintype.card U = Fintype.card V + 1) (hU : ∀ u, ∃ e, H.left e = u)
    (hV : ∀ v, ∃ e, H.right e = v) {C : Clause (AssocVar n M₁.Wire M₂.Wire)}
    (hC : C ∈ (Assoc M₁ M₂).restrict (rho I M₁ M₂)) {β : E → Bool}
    (hβ : ∀ w ∈ supp I M₁ M₂ C, ExactOneAt H β w) : Clause.Sat (propagate I M₁ M₂ β) C := by
  obtain ⟨C₀, hC₀, hsurv, rfl⟩ := CNF.mem_restrict.mp hC
  have hext := propagate_extends I M₁ M₂ β
  simp only [Assoc, Finset.mem_union, Finset.mem_singleton] at hC₀
  rcases hC₀ with ((((h | h) | h) | h) | h) | h
  · -- the inner copy `xy`: modify `β` outside the support to select one edge at every `v`
    choose sel hsel using hV
    let β' : E → Bool := fun e =>
      if Sum.inr (H.right e) ∈ supp I M₁ M₂ (C₀.restrict (rho I M₁ M₂)) then β e
      else decide (e = sel (H.right e))
    have hβ' : ∀ v, ((H.star (Sum.inr v)).filter fun e => β' e = true).card = 1 := by
      intro v
      by_cases hv : Sum.inr v ∈ supp I M₁ M₂ (C₀.restrict (rho I M₁ M₂))
      · rw [← hβ _ hv]
        apply congrArg Finset.card
        apply Finset.filter_congr
        intro e he
        rw [H.mem_star_inr] at he
        simp only [β', he, hv, if_true]
      · refine Finset.card_eq_one.mpr ⟨sel v, Finset.ext fun e => ?_⟩
        rw [Finset.mem_filter, Finset.mem_singleton, H.mem_star_inr]
        constructor
        · rintro ⟨he, hβe⟩
          simp only [β', he, hv, if_false, decide_eq_true_eq] at hβe
          exact hβe
        · rintro rfl
          simp [β', hsel, hv]
    have hsat : Clause.Sat (propagate I M₁ M₂ β') (C₀.restrict (rho I M₁ M₂)) :=
      (Clause.sat_restrict_iff_of_extends (propagate_extends I M₁ M₂ β') C₀).mpr
        (sat_xy_copy_of_exactOne I M₁ M₂ β' hn hg hsp hβ' C₀ h)
    refine (Clause.sat_congr (propagate_eq_on_vars I M₁ M₂ fun q hq e he => ?_)).mpr hsat
    have := (mem_supp_of_depends I M₁ M₂ hq he).2
    simp only [β', this, if_true]
  · -- the inner copy `yz`
    choose sel hsel using hU
    let β' : E → Bool := fun e =>
      if Sum.inl (H.left e) ∈ supp I M₁ M₂ (C₀.restrict (rho I M₁ M₂)) then β e
      else decide (e = sel (H.left e))
    have hβ' : ∀ u, ((H.star (Sum.inl u)).filter fun e => β' e = true).card = 1 := by
      intro u
      by_cases hu : Sum.inl u ∈ supp I M₁ M₂ (C₀.restrict (rho I M₁ M₂))
      · rw [← hβ _ hu]
        apply congrArg Finset.card
        apply Finset.filter_congr
        intro e he
        rw [H.mem_star_inl] at he
        simp only [β', he, hu, if_true]
      · refine Finset.card_eq_one.mpr ⟨sel u, Finset.ext fun e => ?_⟩
        rw [Finset.mem_filter, Finset.mem_singleton, H.mem_star_inl]
        constructor
        · rintro ⟨he, hβe⟩
          simp only [β', he, hu, if_false, decide_eq_true_eq] at hβe
          exact hβe
        · rintro rfl
          simp [β', hsel, hu]
    have hsat : Clause.Sat (propagate I M₁ M₂ β') (C₀.restrict (rho I M₁ M₂)) :=
      (Clause.sat_restrict_iff_of_extends (propagate_extends I M₁ M₂ β') C₀).mpr
        (sat_yz_copy_of_exactOne I M₁ M₂ β' hn hg hsp' hβ' C₀ h)
    refine (Clause.sat_congr (propagate_eq_on_vars I M₁ M₂ fun q hq e he => ?_)).mpr hsat
    have := (mem_supp_of_depends I M₁ M₂ hq he).1
    simp only [β', this, if_true]
  · -- the outer copy `(xy)z`
    exact (Clause.sat_restrict_iff_of_extends hext C₀).mpr (sat_xy_z_copy I M₁ M₂ β C₀ h)
  · -- the outer copy `x(yz)`
    exact (Clause.sat_restrict_iff_of_extends hext C₀).mpr (sat_x_yz_copy I M₁ M₂ β C₀ h)
  · -- the clauses defining the miter variables
    exact (Clause.sat_restrict_iff_of_extends hext C₀).mpr
      (sat_miter I M₁ M₂ β hn hg hsp₁ hsp₂ hcard C₀ h)
  · -- the miter clause does not survive `ρ`
    exact absurd (h ▸ satBy_miterClause I M₁ M₂ hn) hsurv

/-! ### The substitution `σ` -/

open Classical in
/-- **The substitution `σ`** of Lemma [lem:reduction]: a variable fixed by `ρ` maps to its
value; a variable computing a constant under `ρ` maps to that constant; every other variable,
a function `f` of a single star `E(w)`, maps to the extension variable `Z_{w,f}`.

Paper: Lemma [lem:reduction]. -/
noncomputable def sigma : Subst (AssocVar n M₁.Wire M₂.Wire) (SPMVar H) := fun q =>
  match rho I M₁ M₂ q with
  | some b => .const b
  | none =>
    if ∀ β, valFn I M₁ M₂ q β = valFn I M₁ M₂ q fun _ => false then
      .const (valFn I M₁ M₂ q fun _ => false)
    else if h : ∃ w, StarLocalFn H w (valFn I M₁ M₂ q) then
      .lit (.pos (SPM.Z H h.choose (restrictFn (H := H) (valFn I M₁ M₂ q) h.choose)))
    else .const false

/-- The star assigned by `σ` to a non-constant variable lies in the support of every clause
containing the variable. -/
theorem choose_mem_supp {q : AssocVar n M₁.Wire M₂.Wire}
    (hc : ¬ ∀ β, valFn I M₁ M₂ q β = valFn I M₁ M₂ q fun _ => false)
    (h : ∃ w, StarLocalFn H w (valFn I M₁ M₂ q)) {C : Clause (AssocVar n M₁.Wire M₂.Wire)}
    (hq : q ∈ C.vars) : h.choose ∈ supp I M₁ M₂ C := by
  have hne : (deps (valFn I M₁ M₂ q)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    apply hc
    intro β
    apply eq_of_agree_on_deps
    intro e he
    rw [hempty] at he
    exact absurd he (Finset.notMem_empty _)
  obtain ⟨e, he⟩ := hne
  have hstar : e ∈ H.star h.choose := h.choose_spec.deps_subset he
  refine (mem_supp I M₁ M₂).mpr ⟨q, hq, e, he, ?_⟩
  cases hw : h.choose with
  | inl u =>
    rw [hw, H.mem_star_inl] at hstar
    simp [Bipartite.ends, hstar]
  | inr v =>
    rw [hw, H.mem_star_inr] at hstar
    simp [Bipartite.ends, hstar]

/-- Under the defining clauses of the extension variables at the vertices of the support of
`C`, the values substituted by `σ` agree with the propagated values on the variables of `C`. -/
theorem pullback_sigma_eq (hloc : ∀ q, ∃ w, StarLocalFn H w (valFn I M₁ M₂ q))
    {C : Clause (AssocVar n M₁.Wire M₂.Wire)} {α : SPMVar H → Bool}
    (hα : ∀ w ∈ supp I M₁ M₂ C, ∀ f : StarFun H w,
      α (SPM.Z H w f) = f fun e => α (SPM.X H e))
    {q : AssocVar n M₁.Wire M₂.Wire} (hq : q ∈ C.vars) :
    (sigma I M₁ M₂).pullback α q = propagate I M₁ M₂ (fun e => α (SPM.X H e)) q := by
  rw [Subst.pullback_apply]
  unfold sigma
  cases hrho : rho I M₁ M₂ q with
  | some b =>
    simp only [LitConst.eval_const]
    exact (propagate_extends I M₁ M₂ _ q b hrho).symm
  | none =>
    simp only
    split_ifs with hc h
    · rw [LitConst.eval_const]
      exact (hc (fun e => α (SPM.X H e))).symm
    · simp only [LitConst.eval_lit, Literal.sat_pos_iff, Bool.decide_eq_true]
      rw [hα _ (choose_mem_supp I M₁ M₂ hc h hq),
        restrictFn_apply h.choose_spec (fun e => α (SPM.X H e))]
      rfl
    · exact absurd (hloc q) h

/-! ### Lemma [lem:reduction] -/

/-- The constant `2^(2 · 2Δw · (Δ + 2^{2^Δ}))` bounding the size of the derivation from
`SPM(H)` of a subclause of a restricted, substituted clause of width at most `w`. -/
def reductionConst (Δ w : ℕ) : ℕ := 2 ^ (2 * (2 * Δ * w * (Δ + 2 ^ 2 ^ Δ)))

/-- **Reduction from perfect matching.** Under the hypotheses of Section 8 (strip-local
encodings, `n₀ ≤ n`, a width `g ≥ 1` with the induced input restrictions `g`-sparse,
`|U| = |V| + 1`, no isolated vertices, maximum degree `Δ`, and clauses of `Assoc_n` other than
the miter clause of width at most `w`), a refutation of `Assoc_n` of size `s` yields a
refutation of `SPM(H)` of size at most `(reductionConst Δ w + 1) s`.

Paper: Lemma [lem:reduction]. -/
theorem exists_refutation_SPM [Nonempty U] [Nonempty V] (hM₁ : M₁.WiresStripLocal)
    (hM₂ : M₂.WiresStripLocal) (hn : n₀ ≤ n) (hg : 1 ≤ g) (hsp : (inputXY I M₁ M₂).IsSparse g)
    (hsp' : (inputYZ I M₁ M₂).IsSparse g) (hsp₁ : (inputXY_Z I M₁ M₂).IsSparse g)
    (hsp₂ : (inputX_YZ I M₁ M₂).IsSparse g) (hcard : Fintype.card U = Fintype.card V + 1)
    (hU : ∀ u, ∃ e, H.left e = u) (hV : ∀ v, ∃ e, H.right e = v) {Δ : ℕ}
    (hΔ : H.MaxDegreeLE Δ) {w : ℕ}
    (hw : ∀ C ∈ Assoc M₁ M₂, C ≠ miterClause n M₁.Wire M₂.Wire → C.card ≤ w)
    (π : Refutation (Assoc M₁ M₂)) :
    ∃ π' : Refutation (SPM H), π'.size ≤ (reductionConst Δ w + 1) * π.size := by
  have hloc := exists_starLocalFn_valFn I M₁ M₂ hM₁ hM₂ hn hg hsp hsp' hsp₁ hsp₂
  refine π.reduce (rho I M₁ M₂) (sigma I M₁ M₂) fun C hC => ?_
  obtain ⟨C₀, hC₀, hsurvσ, rfl⟩ := CNF.mem_subst.mp hC
  -- the clauses of the support imply the restricted, substituted clause
  have himpl : (SPM.localCNF H (supp I M₁ M₂ C₀)).Implies (C₀.subst (sigma I M₁ M₂)) := by
    intro α hα
    rw [SPM.localCNF, CNF.sat_biUnion_iff] at hα
    have hα' : ∀ w ∈ supp I M₁ M₂ C₀, CNF.Sat α (SPM.exactOne H w) ∧
        ∀ f : StarFun H w, α (SPM.Z H w f) = f fun e => α (SPM.X H e) := fun w hw =>
      (SPM.sat_vertexClauses_iff H α w).mp (hα w hw)
    have hβ : ∀ w ∈ supp I M₁ M₂ C₀, ExactOneAt H (fun e => α (SPM.X H e)) w := fun w hw =>
      exactOneAt_of_sat_exactOne (hα' w hw).1
    have hsat := sat_propagate_of_exactOne_supp I M₁ M₂ hn hg hsp hsp' hsp₁ hsp₂ hcard hU hV
      hC₀ hβ
    rw [Clause.sat_subst_iff hsurvσ.1]
    exact (Clause.sat_congr fun q hq =>
      pullback_sigma_eq I M₁ M₂ hloc (fun w hw => (hα' w hw).2) hq).mpr hsat
  -- the width of the restricted clause
  have hwidth : C₀.card ≤ w := by
    obtain ⟨C₁, hC₁, hsurv, rfl⟩ := CNF.mem_restrict.mp hC₀
    refine (Finset.card_le_card (C₁.restrict_subset _)).trans (hw C₁ hC₁ fun h => hsurv ?_)
    rw [h]
    exact satBy_miterClause I M₁ M₂ hn
  obtain ⟨D, hD, δ, hδ⟩ := SPM.exists_derivation_localCNF H hΔ (supp I M₁ M₂ C₀) himpl
    (CNF.not_isTautology_of_mem_subst hC)
  refine ⟨D, hD, δ.mono (SPM.localCNF_subset_SPM H _), ?_⟩
  rw [Derivation.size_mono]
  refine hδ.trans (Nat.pow_le_pow_right two_pos (Nat.mul_le_mul_left 2 ?_))
  refine Nat.mul_le_mul_right _ ((card_supp_le I M₁ M₂ hΔ hloc C₀).trans ?_)
  exact Nat.mul_le_mul_left _ hwidth

end Assoc

/-! ### Theorem [thm:main] -/

/-- **Lower bound for multiplier associativity**, in explicit form. Let `M` be a strip-local
family of multiplier encodings, and take Theorem [thm:iss-graphs] and the size–width
tradeoff as hypotheses (both are theorems, `issGraphs` and `bwTradeoff`). Then there are
`c > 0` and `m₀` such that for every `m ≥ m₀` and every
`n ≥ n₀(m) = 4K = O(m⁴ log m)`, every resolution refutation of `Assoc_n` has size at least
`exp(c m)`; the paper's `2^{Ω((n / log n)^{1/4})}` follows by choosing `m` of order
`(n / log n)^{1/4}`.

Paper: Theorem [thm:main]. -/
theorem main_explicit (M : ∀ n, MulEncoding n) (hM : StripLocal M) (hISS : ISSGraphs)
    (hBW : BWTradeoff) :
    ∃ (c : ℝ) (m₀ : ℕ), 0 < c ∧ ∀ m ≥ m₀, ∀ n, indexN₀ m (stripWidth m) ≤ n →
      ∀ π : Refutation (Assoc (M n) (M (2 * n))), c * m ≤ Real.log π.size := by
  obtain ⟨⟨k, hk⟩, hloc⟩ := hM
  obtain ⟨Δ, Γ, ε, hΓ, hε, m₁, hex⟩ := hISS
  obtain ⟨c₂, hc₂, m₂, hsize⟩ :=
    SPM.exists_size_bound hBW (Δ := Δ) (by linarith : (1 : ℝ) ≤ Γ) hε
  set K' : ℕ := Assoc.reductionConst Δ (max k 3) with hK'
  set L : ℝ := Real.log ((K' : ℝ) + 1) with hL
  refine ⟨c₂ / 2, max (max m₁ m₂) (max (⌈1 / ε⌉₊ + 1) (⌈2 * L / c₂⌉₊ + 1)), by positivity,
    fun m hm n hn π => ?_⟩
  have hm₁ : m₁ ≤ m := le_of_max_le_left (le_of_max_le_left hm)
  have hm₂ : m₂ ≤ m := le_of_max_le_right (le_of_max_le_left hm)
  have hm1 : 1 ≤ m := by omega
  have hεm : 1 ≤ ε * m := by
    have h1 : (1 / ε : ℝ) ≤ ⌈1 / ε⌉₊ := Nat.le_ceil _
    have h2 : ((⌈1 / ε⌉₊ : ℕ) : ℝ) ≤ m := by exact_mod_cast (show ⌈1 / ε⌉₊ ≤ m by omega)
    have h3 := (div_le_iff₀ hε).mp (h1.trans h2)
    linarith
  have hLm : 2 * L ≤ c₂ * m := by
    have h1 : (2 * L / c₂ : ℝ) ≤ ⌈2 * L / c₂⌉₊ := Nat.le_ceil _
    have h2 : ((⌈2 * L / c₂⌉₊ : ℕ) : ℝ) ≤ m := by
      exact_mod_cast (show ⌈2 * L / c₂⌉₊ ≤ m by omega)
    have h3 := (div_le_iff₀ hc₂).mp (h1.trans h2)
    linarith
  obtain ⟨H⟩ := hex m hm₁
  have hg : 1 ≤ stripWidth m := stripWidth_pos m
  have hg2 : m + 2 ≤ 2 ^ (stripWidth m - 1) :=
    le_trans (by omega) (two_mul_le_two_pow_stripWidth m)
  obtain ⟨I⟩ := exists_indexMaps H.G H.simple hm1 H.card_U H.card_V (stripWidth_pos m)
  have : Nonempty H.U := Fintype.card_pos_iff.mp (by rw [H.card_U]; omega)
  have : Nonempty H.V := Fintype.card_pos_iff.mp (by rw [H.card_V]; omega)
  have hU' : Fintype.card H.U ≤ m + 1 := H.card_U.le
  have hV' : Fintype.card H.V ≤ m + 1 := by rw [H.card_V]; omega
  have hcard : Fintype.card H.U = Fintype.card H.V + 1 := by rw [H.card_U, H.card_V]
  have hw : ∀ C ∈ Assoc (M n) (M (2 * n)),
      C ≠ Assoc.miterClause n (M n).Wire (M (2 * n)).Wire → C.card ≤ max k 3 := fun C hC hne =>
    (Assoc.card_le_of_ne_miterClause _ _ hC hne).trans
      (max_le_max (max_le (hk n) (hk (2 * n))) le_rfl)
  obtain ⟨π', hπ'⟩ := Assoc.exists_refutation_SPM I (M n) (M (2 * n)) (hloc n) (hloc (2 * n))
    hn hg (Assoc.isSparse_inputXY I _ _ H.simple hU' hg2)
    (Assoc.isSparse_inputYZ I _ _ H.simple hV' hg2) (Assoc.isSparse_inputXY_Z I _ _ hV' hg2)
    (Assoc.isSparse_inputX_YZ I _ _ hU' hg2) hcard (H.exists_edge_left (by linarith) hεm)
    H.exists_edge_right H.maxDegreeLE hw π
  have h1 := hsize m hm₂ H π'
  have h2 : Real.log π'.size ≤ L + Real.log π.size := by
    have hpos : (0 : ℝ) < π'.size := by exact_mod_cast π'.size_pos
    have hle : (π'.size : ℝ) ≤ ((K' : ℝ) + 1) * π.size := by exact_mod_cast hπ'
    have hs : (0 : ℝ) < π.size := by exact_mod_cast π.size_pos
    calc Real.log π'.size ≤ Real.log (((K' : ℝ) + 1) * π.size) := Real.log_le_log hpos hle
      _ = L + Real.log π.size := Real.log_mul (by positivity) hs.ne'
  linarith

/-- **Lower bound for multiplier associativity.** For a strip-local family of multiplier
encodings, given Theorem [thm:iss-graphs] and the size–width tradeoff, there are `c > 0` and
`n₁` such that for every `n ≥ n₁`, every resolution refutation of `Assoc_n` has size at least
`exp(c (n / log n)^{1/4})`, the paper's `2^{Ω((n / log n)^{1/4})}`. The parameter is
`m = ⌊(n / log n)^{1/4} / 20⌋`, for which `n₀(m) ≤ 16896 g m⁴ ≤ n` since `g ≤ 5 log n`.
Both hypotheses are theorems (`issGraphs`, `bwTradeoff`), so the bound holds unconditionally
for every strip-local family.

Paper: Theorem [thm:main]. -/
theorem main (M : ∀ n, MulEncoding n) (hM : StripLocal M) (hISS : ISSGraphs) (hBW : BWTradeoff) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₁ : ℕ, ∀ n ≥ n₁, ∀ π : Refutation (Assoc (M n) (M (2 * n))),
      c * ((n : ℝ) / Real.log n) ^ ((1 : ℝ) / 4) ≤ Real.log π.size := by
  obtain ⟨c₀, m₀, hc₀, hmain⟩ := main_explicit M hM hISS hBW
  set A : ℝ := (20 * ((m₀ : ℝ) + 2)) ^ 4 with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨c₀ / 40, by positivity, max 3 ⌈4 * A ^ 2⌉₊, fun n hn π => ?_⟩
  have hn3 : 3 ≤ n := le_of_max_le_left hn
  have hnA : ⌈4 * A ^ 2⌉₊ ≤ n := le_of_max_le_right hn
  have hn3' : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog1 : 1 ≤ Real.log n := by
    rw [← Real.log_exp 1]
    refine Real.log_le_log (Real.exp_pos 1) ?_
    have := Real.exp_one_lt_d9
    linarith
  set t : ℝ := ((n : ℝ) / Real.log n) ^ ((1 : ℝ) / 4) with ht
  have hbase : (0 : ℝ) ≤ (n : ℝ) / Real.log n := by positivity
  have ht0 : 0 ≤ t := Real.rpow_nonneg hbase _
  have ht4 : t ^ 4 = (n : ℝ) / Real.log n := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hbase]
    norm_num
  -- `log n ≤ 2√n`, hence `n / log n ≥ √n / 2 ≥ A` once `n ≥ 4A²`
  have hlogsqrt : Real.log n ≤ 2 * Real.sqrt n := by
    have := Real.log_le_rpow_div hn0.le (by norm_num : (0 : ℝ) < 1 / 2)
    rw [Real.sqrt_eq_rpow]
    linarith
  have hnA' : 4 * A ^ 2 ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hnA)
  have hsqrt : 2 * A ≤ Real.sqrt n := by
    rw [show 2 * A = Real.sqrt ((2 * A) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have htA : A ≤ t ^ 4 := by
    rw [ht4, le_div_iff₀ (by linarith)]
    calc A * Real.log n ≤ A * (2 * Real.sqrt n) := mul_le_mul_of_nonneg_left hlogsqrt hA0
      _ = 2 * A * Real.sqrt n := by ring
      _ ≤ Real.sqrt n * Real.sqrt n := mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg _)
      _ = n := Real.mul_self_sqrt hn0.le
  have ht20 : 20 * ((m₀ : ℝ) + 2) ≤ t :=
    (pow_le_pow_iff_left₀ (by positivity) ht0 (by norm_num : (4 : ℕ) ≠ 0)).mp htA
  -- the parameter `m`
  set m : ℕ := ⌊t / 20⌋₊ with hm
  have hm_le : (m : ℝ) ≤ t / 20 := Nat.floor_le (by positivity)
  have hm_ge : t / 20 - 1 ≤ m := by
    have := Nat.lt_floor_add_one (t / 20)
    linarith
  have hm₀ : m₀ + 1 ≤ m := by
    have : ((m₀ + 1 : ℕ) : ℝ) ≤ m := by
      push_cast
      linarith
    exact_mod_cast this
  have hm1 : 1 ≤ m := by omega
  -- `t ≤ n`, so `m + 2 ≤ n`
  have htn : t ≤ n := by
    rcases le_or_gt t 1 with h | h
    · linarith
    · calc t ≤ t ^ 4 := le_self_pow₀ h.le (by norm_num)
        _ = (n : ℝ) / Real.log n := ht4
        _ ≤ n := div_le_self hn0.le hlog1
  have hmn : (m : ℝ) + 2 ≤ n := by linarith
  -- the strip width is at most `5 log n`
  have hg : (stripWidth m : ℝ) ≤ 5 * Real.log n := by
    have hm2 : 1 < m + 2 := by omega
    have hpow := Nat.pow_pred_clog_lt_self one_lt_two hm2
    have hclog1 : 0 < Nat.clog 2 (m + 2) := Nat.clog_pos one_lt_two hm2
    have h1 : ((2 ^ (Nat.clog 2 (m + 2)).pred : ℕ) : ℝ) < ((m + 2 : ℕ) : ℝ) := by
      exact_mod_cast hpow
    push_cast at h1
    have h2 := Real.log_lt_log (by positivity) (h1.trans_le hmn)
    rw [Real.log_pow] at h2
    have hp : (((Nat.clog 2 (m + 2)).pred : ℕ) : ℝ) = (Nat.clog 2 (m + 2) : ℝ) - 1 := by
      rw [Nat.pred_eq_sub_one, Nat.cast_sub hclog1, Nat.cast_one]
    rw [hp] at h2
    have hlog2 : (1 : ℝ) / 2 < Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    have h3 : ((Nat.clog 2 (m + 2) : ℝ) - 1) * (1 / 2) ≤
        ((Nat.clog 2 (m + 2) : ℝ) - 1) * Real.log 2 :=
      mul_le_mul_of_nonneg_left hlog2.le (by linarith)
    unfold stripWidth
    push_cast
    linarith
  -- `n₀(m) ≤ n`
  have hn₀ : indexN₀ m (stripWidth m) ≤ n := by
    have h1 : ((indexN₀ m (stripWidth m) : ℕ) : ℝ) ≤
        16896 * (stripWidth m : ℝ) * (m : ℝ) ^ 4 := by
      exact_mod_cast indexN₀_le m (stripWidth m) hm1
    have hm4 : (m : ℝ) ^ 4 ≤ (t / 20) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hm_le 4
    have hlt : Real.log n * t ^ 4 = n := by
      rw [ht4]
      field_simp
    have key : ((indexN₀ m (stripWidth m) : ℕ) : ℝ) ≤ n := by
      calc ((indexN₀ m (stripWidth m) : ℕ) : ℝ)
          ≤ 16896 * (stripWidth m : ℝ) * (m : ℝ) ^ 4 := h1
        _ ≤ 16896 * (5 * Real.log n) * (t / 20) ^ 4 :=
            mul_le_mul (mul_le_mul_of_nonneg_left hg (by norm_num)) hm4 (by positivity)
              (by positivity)
        _ = (16896 * 5 / 160000) * (Real.log n * t ^ 4) := by ring
        _ = (16896 * 5 / 160000) * n := by rw [hlt]
        _ ≤ 1 * n := mul_le_mul_of_nonneg_right (by norm_num) hn0.le
        _ = n := one_mul _
    exact_mod_cast key
  have h := hmain m (by omega) n hn₀ π
  have hm40 : t / 40 ≤ m := by linarith
  calc c₀ / 40 * t = c₀ * (t / 40) := by ring
    _ ≤ c₀ * m := mul_le_mul_of_nonneg_left hm40 hc₀.le
    _ ≤ Real.log π.size := h

/-- **Theorem [thm:main] for the array multiplier**, by Proposition [prop:array-strip-local],
the expander graphs `issGraphs` and the size–width tradeoff `bwTradeoff`: every resolution
refutation of `Assoc_n` has size `2^{Ω((n / log n)^{1/4})}`. -/
theorem main_arrayMul :
    ∃ c : ℝ, 0 < c ∧ ∃ n₁ : ℕ, ∀ n ≥ n₁,
      ∀ π : Refutation (Assoc (arrayMul n) (arrayMul (2 * n))),
        c * ((n : ℝ) / Real.log n) ^ ((1 : ℝ) / 4) ≤ Real.log π.size :=
  main arrayMul arrayMul_stripLocal issGraphs bwTradeoff

/-- **Theorem [thm:main] for the Wallace-tree multiplier** with a carry-lookahead adder, by
Proposition [prop:wallace-strip-local], the expander graphs `issGraphs` and the size–width
tradeoff `bwTradeoff`. -/
theorem main_wallaceMul :
    ∃ c : ℝ, 0 < c ∧ ∃ n₁ : ℕ, ∀ n ≥ n₁,
      ∀ π : Refutation (Assoc (wallaceMul n) (wallaceMul (2 * n))),
        c * ((n : ℝ) / Real.log n) ^ ((1 : ℝ) / 4) ≤ Real.log π.size :=
  main wallaceMul wallaceMul_stripLocal issGraphs bwTradeoff

end AssocLB
