/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/
import AssocLB.Frege.LocalDerivations
import AssocLB.Frege.PerfectMatching

/-!
# Reduction from `PM(H)` in bounded-depth Frege

Paper: Section 9.3 (Reduction and lower bound), Lemma [lem:frege-transfer] (reduction from
`PM(H)`): there are constants `d₀` and `s₀` such that a depth-`d` Frege refutation `π` of
`Assoc_n` yields a depth-`(d + d₀)` Frege refutation of `PM(H)` of size at most `s₀ |π|`. The
proof follows the three steps of the resolution reduction (Lemma [lem:reduction]).

## Main definitions

* `Assoc.sigmaF I M₁ M₂`: the formula substitution `σ` of the "DNF substitution" step: a
  variable fixed by `ρ` maps to its constant, a variable computing a constant under `ρ` to that
  constant, and every other variable, a function `f` of a single star `E(w)`, to the canonical
  DNF of `f` over the edges of `w`.

## Main results

* `FregeSystem.exists_derivation_toFormula_subst_of_satBy`: "Application of `ρ`", satisfied
  clauses. If `ρ` satisfies `C`, then `C^ρ` has a derivation from no premises of constant
  depth and size linear in `|C^ρ|` (it is a weakening of `¬⊥`).
* `FregeSystem.exists_derivation_toFormula_subst_of_survives`: "Application of `ρ`", surviving
  clauses. If `C` survives `ρ` and has width at most `w`, then `C^ρ` has a derivation from
  `C↾ρ` of depth and size bounded in terms of `w` (it is a weakening of `C↾ρ`). This is an
  instance of Lemma [lem:frege-local-derivations] in its form for sets of formulas
  (`FregeSystem.exists_local_derivation`): one premise over the at most `w` variables of `C`.
* `FregeSystem.exists_refutation_restrict`: the restriction step for any CNF whose surviving
  clauses have bounded width: a refutation of `Φ` yields a refutation of `Φ↾ρ` of depth larger
  by a constant and size larger by a constant factor.
* `Assoc.depth_sigmaF_le`, `Assoc.size_sigmaF_le`, `Assoc.eval_sigmaF`, `Assoc.vars_sigmaF_subset`:
  `σ` has depth at most `3` and constant size, `σ(q)` computes the propagated value of `q`,
  and its variables lie in the stars of the support of any clause containing `q`.
* `Assoc.implies_toFormula_subst_sigmaF`: "Local derivations", the `ExactOne` clauses at the
  support of a clause `C` of `Assoc_n↾ρ` imply `C^σ`, by Lemma [lem:local-soundness].
* `FregeSystem.frege_transfer`: Lemma [lem:frege-transfer].

## Design notes

* The constants `d₀`, `s₀` depend on the Frege system, on `Δ` and on the width bound `w` of the
  encoding, and on nothing else: the statement is `∃ d₀ s₀, ∀ (graph, index maps, encodings,
  refutation), …`, with the standing hypotheses of Section 8 as in `Assoc.exists_refutation_SPM`.
* As in the resolution reduction, `σ` maps every non-constant variable to a formula of its
  star function (the paper distinguishes edge variables, edge-local and star-local wires; all
  are functions of a single star), and constant variables to constants, so that the variables
  of `C^σ` lie in the stars of the support of `C` (`Assoc.choose_mem_supp`).
* `ρ` is applied as the formula substitution `Restriction.toFormulaSubst`, so the restricted
  clauses `Assoc_n↾ρ` (the input of Lemma [lem:local-soundness]) have to be reconnected to the
  substituted formulas `Assoc_n^ρ`; this is the restriction step, whose only non-constant case
  is the miter clause, satisfied by `ρ`, handled by weakening along a balanced disjunction.
* The size bound of the restriction step is per initial formula, `s₀ |C^ρ|`, and is summed by
  `Frege.Refutation.compose`, which gives the constant factor of the paper.
-/

namespace AssocLB

namespace FregeSystem

variable (𝓕 : FregeSystem)

/-- **Application of `ρ`, satisfied clauses.** If `ρ` satisfies `C`, then `C^ρ` is a weakening of
`¬⊥`: it has a derivation from no premises of constant depth and of size linear in `|C^ρ|`,
with constants depending only on the system.

Paper: proof of Lemma [lem:frege-transfer], "Application of `ρ`". -/
theorem exists_derivation_toFormula_subst_of_satBy :
    ∃ d₀ s₀ : ℕ, ∀ (V : Type) [DecidableEq V] (ρ : Restriction V) (C : Clause V), C.SatBy ρ →
      ∃ δ : 𝓕.Derivation (∅ : Set (Formula V)) (C.toFormula.subst ρ.toFormulaSubst),
        δ.depth ≤ d₀ ∧ δ.size ≤ s₀ * (C.toFormula.subst ρ.toFormulaSubst).size := by
  obtain ⟨d₁, s₁, h₁⟩ := 𝓕.exists_derivation_top
  obtain ⟨d₂, s₂, h₂⟩ := 𝓕.exists_derivation_orBalanced_of_mem
  refine ⟨max d₁ (d₂ + 2), s₁ + 5 * s₂, fun V _ ρ C hC => ?_⟩
  -- the substituted clause formula is the balanced disjunction of the substituted literals
  obtain ⟨L, hL⟩ : ∃ L : List (Formula V),
      L = (C.toList.map Literal.toFormula).map (Formula.subst ρ.toFormulaSubst) := ⟨_, rfl⟩
  have hCL : C.toFormula.subst ρ.toFormulaSubst = Formula.orBalanced L := by
    rw [Clause.toFormula, Formula.subst_orBalanced, hL]
  rw [hCL]
  -- its disjuncts are literals under `ρ`: size at most `4`, depth at most `1`
  have hb : ∀ F ∈ L, F.size ≤ 4 := by
    intro F hF
    rw [hL] at hF
    obtain ⟨F₁, hF₁, rfl⟩ := List.mem_map.mp hF
    obtain ⟨l, -, rfl⟩ := List.mem_map.mp hF₁
    have h1 := Formula.size_subst_le (k := 2) (by norm_num) (Restriction.size_toFormulaSubst_le ρ)
      l.toFormula
    have h2 := Literal.size_toFormula_le l
    omega
  have hdepth : (Formula.orBalanced L).depth ≤ 2 := by
    refine Formula.depth_orBalanced_le fun F hF => ?_
    rw [hL] at hF
    obtain ⟨F₁, hF₁, rfl⟩ := List.mem_map.mp hF
    obtain ⟨l, -, rfl⟩ := List.mem_map.mp hF₁
    have h1 := Formula.depthFrom_le_depth_add_one (some true)
      (l.toFormula.subst ρ.toFormulaSubst)
    have h2 := Formula.depth_subst_le (s := 0) (fun v => (Restriction.depth_toFormulaSubst ρ v).le)
      l.toFormula
    have h3 := Literal.depth_toFormula l
    omega
  have htop : Formula.top ∈ L := by
    rw [hL]
    exact Restriction.exists_top_mem_of_satBy hC
  -- derive `¬⊥`, then weaken it along the path to its leaf
  obtain ⟨δ₁, hd₁, hs₁⟩ := h₁ V
  obtain ⟨δ₂, hd₂, hs₂⟩ := h₂ V 4 L Formula.top hb htop
  obtain ⟨δ, hδd, hδs⟩ := δ₁.exists_trans_le δ₂ (d := max d₁ (d₂ + 2)) (by omega) (by omega)
  refine ⟨δ, hδd, ?_⟩
  have h1 := Nat.mul_le_mul_left s₁ (Formula.size_pos (Formula.orBalanced L))
  nlinarith

/-- **Application of `ρ`, surviving clauses.** If `C` survives `ρ` and has width at most `w`,
then `C^ρ` is a weakening of `C↾ρ`: it has a derivation from `C↾ρ` of depth and size bounded
in terms of `w` and the system.

Paper: proof of Lemma [lem:frege-transfer], "Application of `ρ`". -/
theorem exists_derivation_toFormula_subst_of_survives (w : ℕ) :
    ∃ D S : ℕ, ∀ (V : Type) [DecidableEq V] (ρ : Restriction V) (C : Clause V),
      C.card ≤ w → C.Survives ρ →
      ∃ δ : 𝓕.Derivation {(C.restrict ρ).toFormula} (C.toFormula.subst ρ.toFormulaSubst),
        δ.depth ≤ D ∧ δ.size ≤ S := by
  obtain ⟨D, S, h⟩ := 𝓕.exists_local_derivation w 1 (6 * w + 2)
  refine ⟨D, S, fun V _ ρ C hw hsurv => ?_⟩
  have hρs : ∀ v, (ρ.toFormulaSubst v).size ≤ 2 := Restriction.size_toFormulaSubst_le ρ
  have hρv : ∀ v, (ρ.toFormulaSubst v).vars ⊆ {v} := by
    intro v
    unfold Restriction.toFormulaSubst
    split
    · rename_i b _
      cases b <;> simp
    · simp
  -- the variables of `C↾ρ` and of `C^ρ` are among those of `C`
  have hvars : (C.toFormula.subst ρ.toFormulaSubst).vars ⊆ C.vars := by
    refine (Formula.vars_subst_subset _ _).trans (Finset.biUnion_subset.mpr fun v hv => ?_)
    rw [Clause.vars_toFormula] at hv
    exact (hρv v).trans (Finset.singleton_subset_iff.mpr hv)
  -- `C↾ρ` implies `C^ρ`: an assignment satisfying `C↾ρ` agrees with its pullback along `ρ`
  -- on the variables of `C↾ρ`, which `ρ` leaves unassigned, and the pullback extends `ρ`
  have himp : Formula.Implies (↑({(C.restrict ρ).toFormula} : Finset (Formula V)))
      (C.toFormula.subst ρ.toFormulaSubst) := by
    intro α hα
    have h1 : Clause.Sat α (C.restrict ρ) :=
      (Clause.eval_toFormula_eq_true_iff α _).mp (hα _ (by simp))
    have hext : ρ.Extends fun v => (ρ.toFormulaSubst v).eval α := fun v b hb => by
      change (ρ.toFormulaSubst v).eval α = b
      rw [Restriction.toFormulaSubst_of_eq_some hb, Formula.eval_const]
    rw [Formula.eval_subst, Clause.eval_toFormula_eq_true_iff,
      ← Clause.sat_restrict_iff_of_extends hext]
    refine (Clause.sat_congr fun v hv => ?_).mp h1
    obtain ⟨l, hl, rfl⟩ := Clause.mem_vars.mp hv
    rw [Restriction.toFormulaSubst_of_eq_none (Clause.eq_none_of_mem_restrict hsurv hl),
      Formula.eval_var]
  obtain ⟨δ, hd, hs⟩ := h V C.vars {(C.restrict ρ).toFormula} (C.toFormula.subst ρ.toFormulaSubst)
    (Finset.card_image_le.trans hw) (Finset.card_singleton _).le
    (fun F hF => by
      rw [Finset.mem_singleton] at hF
      subst hF
      refine ⟨?_, ?_⟩
      · rw [Clause.vars_toFormula]
        exact Finset.image_subset_image (Clause.restrict_subset ρ C)
      · have h1 := Clause.size_toFormula_le (C.restrict ρ)
        have h2 := Finset.card_le_card (Clause.restrict_subset ρ C)
        omega)
    hvars
    ((Formula.size_subst_le (by norm_num) hρs _).trans (by
      have := Clause.size_toFormula_le C
      omega))
    himp
  refine ⟨δ.mono (by simp), ?_, ?_⟩
  · change δ.depth ≤ D
    exact hd
  · change δ.size ≤ S
    exact hs

/-- **The restriction step.** For a CNF `Φ` whose clauses surviving `ρ` have width at most `w`,
a refutation of `Φ` yields a refutation of `Φ↾ρ` of depth larger by a constant and size larger
by a constant factor, with constants depending only on `w` and the system: substitute `ρ`
(Lemma [lem:frege-substitution]) and derive each initial formula `C^ρ` from `Φ↾ρ`.

Paper: proof of Lemma [lem:frege-transfer], "Application of `ρ`". -/
theorem exists_refutation_restrict (w : ℕ) :
    ∃ d₀ s₀ : ℕ, ∀ (V : Type) [DecidableEq V] (Φ : CNF V) (ρ : Restriction V),
      (∀ C ∈ Φ, C.Survives ρ → C.card ≤ w) →
      ∀ π : 𝓕.Refutation Φ.toFormulas,
        ∃ π' : 𝓕.Refutation (Φ.restrict ρ).toFormulas,
          π'.depth ≤ π.depth + d₀ ∧ π'.size ≤ s₀ * π.size := by
  obtain ⟨d₁, s₁, h₁⟩ := 𝓕.exists_derivation_toFormula_subst_of_satBy
  obtain ⟨d₂, s₂, h₂⟩ := 𝓕.exists_derivation_toFormula_subst_of_survives w
  refine ⟨max d₁ d₂ + 1, 2 * (s₁ + s₂ + 1), fun V _ Φ ρ hw π => ?_⟩
  -- substitute `ρ`
  obtain ⟨π₁, hπ₁d, hπ₁s⟩ : ∃ π₁ : 𝓕.Refutation (Formula.subst ρ.toFormulaSubst '' Φ.toFormulas),
      π₁.depth ≤ π.depth + 0 + 1 ∧ π₁.size ≤ 2 * π.size :=
    ⟨π.subst ρ.toFormulaSubst, π.depth_subst_le fun v => (Restriction.depth_toFormulaSubst ρ v).le,
      π.size_subst_le (by norm_num) (Restriction.size_toFormulaSubst_le ρ)⟩
  -- derive each initial formula `C^ρ` from `Φ↾ρ`
  obtain ⟨π', hπ's, hπ'd⟩ := π₁.compose (Γ' := (Φ.restrict ρ).toFormulas) (K := s₁ + s₂)
    (D := max d₁ d₂) fun F _ hF => by
      obtain ⟨F₀, hF₀, rfl⟩ := hF
      obtain ⟨C, hC, rfl⟩ := CNF.mem_toFormulas.mp hF₀
      by_cases hsat : C.SatBy ρ
      · obtain ⟨δ, hd, hs⟩ := h₁ V ρ C hsat
        refine ⟨δ.mono (Set.empty_subset _), ?_, ?_⟩
        · change δ.size ≤ _
          exact hs.trans (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
        · change δ.depth ≤ _
          exact hd.trans (le_max_left _ _)
      · obtain ⟨δ, hd, hs⟩ := h₂ V ρ C (hw C hC hsat) hsat
        refine ⟨δ.mono ?_, ?_, ?_⟩
        · rw [Set.singleton_subset_iff]
          exact CNF.toFormula_mem_toFormulas (CNF.mem_restrict.mpr ⟨C, hC, hsat, rfl⟩)
        · change δ.size ≤ _
          exact hs.trans ((Nat.le_mul_of_pos_right _ (Formula.size_pos _)).trans
            (Nat.mul_le_mul_right _ (Nat.le_add_left _ _)))
        · change δ.depth ≤ _
          exact hd.trans (le_max_right _ _)
  refine ⟨π', ?_, ?_⟩
  · omega
  · calc π'.size ≤ (s₁ + s₂ + 1) * π₁.size := hπ's
      _ ≤ (s₁ + s₂ + 1) * (2 * π.size) := Nat.mul_le_mul_left _ hπ₁s
      _ = 2 * (s₁ + s₂ + 1) * π.size := by ring

end FregeSystem

namespace Assoc

variable {U V E : Type*} {H : Bipartite U V E} {g K n₀ : ℕ} (I : IndexMaps H g K n₀)
  [Fintype U] [Fintype V] [Fintype E] [DecidableEq U] [DecidableEq V] [DecidableEq E] {n : ℕ}
  (M₁ : MulEncoding n) (M₂ : MulEncoding (2 * n))

/-! ### The formula substitution `σ` -/

open Classical in
/-- **The formula substitution `σ`** of Lemma [lem:frege-transfer]: a variable fixed by `ρ` maps
to its constant; a variable computing a constant under `ρ` maps to that constant; every other
variable, a function `f` of a single star `E(w)`, maps to the canonical DNF of `f` over the
edges of `w`.

Paper: proof of Lemma [lem:frege-transfer], "DNF substitution". -/
noncomputable def sigmaF : AssocVar n M₁.Wire M₂.Wire → Formula E := fun q =>
  match rho I M₁ M₂ q with
  | some b => Formula.const b
  | none =>
    if ∀ β, valFn I M₁ M₂ q β = valFn I M₁ M₂ q fun _ => false then
      Formula.const (valFn I M₁ M₂ q fun _ => false)
    else if h : ∃ w, StarLocalFn H w (valFn I M₁ M₂ q) then
      Formula.dnf (H.star h.choose) (restrictFn (H := H) (valFn I M₁ M₂ q) h.choose)
    else Formula.bot

/-- `σ` has depth at most `3`. -/
theorem depth_sigmaF_le (q : AssocVar n M₁.Wire M₂.Wire) : (sigmaF I M₁ M₂ q).depth ≤ 3 := by
  unfold sigmaF
  cases rho I M₁ M₂ q with
  | some b => simp
  | none =>
    simp only
    split_ifs
    · simp
    · exact Formula.depth_dnf_le _ _
    · simp

/-- `σ` has size at most `2^Δ (3Δ + 3) + 1`, the size bound of a DNF over a star. -/
theorem size_sigmaF_le {Δ : ℕ} (hΔ : H.MaxDegreeLE Δ) (q : AssocVar n M₁.Wire M₂.Wire) :
    (sigmaF I M₁ M₂ q).size ≤ 2 ^ Δ * (3 * Δ + 3) + 1 := by
  have h3 : 1 * 3 ≤ 2 ^ Δ * (3 * Δ + 3) := Nat.mul_le_mul Nat.one_le_two_pow (by omega)
  unfold sigmaF
  cases rho I M₁ M₂ q with
  | some b => exact (Formula.size_const_le _).trans (by omega)
  | none =>
    simp only
    split_ifs with hc h
    · exact (Formula.size_const_le _).trans (by omega)
    · refine (Formula.size_dnf_le _ _).trans ?_
      have hd : (H.star h.choose).card ≤ Δ := hΔ _
      exact Nat.add_le_add_right
        (Nat.mul_le_mul (Nat.pow_le_pow_right two_pos hd) (by omega)) 1
    · simp only [Formula.size_bot]
      omega

/-- `σ(q)` computes the propagated value of `q`: `β(σ(q)) = β̄(q)`. -/
theorem eval_sigmaF (hloc : ∀ q, ∃ w, StarLocalFn H w (valFn I M₁ M₂ q)) (β : E → Bool)
    (q : AssocVar n M₁.Wire M₂.Wire) : (sigmaF I M₁ M₂ q).eval β = propagate I M₁ M₂ β q := by
  unfold sigmaF
  cases hrho : rho I M₁ M₂ q with
  | some b =>
    simp only [Formula.eval_const]
    exact (propagate_extends I M₁ M₂ β q b hrho).symm
  | none =>
    simp only
    split_ifs with hc h
    · rw [Formula.eval_const]
      exact (hc β).symm
    · rw [Formula.eval_dnf, restrictFn_apply h.choose_spec]
      rfl
    · exact absurd (hloc q) h

/-- The variables of `σ(q)` lie in the stars of the support of any clause containing `q`. -/
theorem vars_sigmaF_subset {C : Clause (AssocVar n M₁.Wire M₂.Wire)}
    {q : AssocVar n M₁.Wire M₂.Wire} (hq : q ∈ C.vars) :
    (sigmaF I M₁ M₂ q).vars ⊆ (supp I M₁ M₂ C).biUnion H.star := by
  unfold sigmaF
  cases rho I M₁ M₂ q with
  | some b => cases b <;> simp
  | none =>
    simp only
    split_ifs with hc h
    · cases valFn I M₁ M₂ q fun _ => false <;> simp
    · exact (Formula.vars_dnf_subset _ _).trans
        (Finset.subset_biUnion_of_mem H.star (choose_mem_supp I M₁ M₂ hc h hq))
    · simp

/-! ### Local derivations -/

/-- **The `ExactOne` clauses at the support imply the substituted clause.** For a clause `C` of
`Assoc_n↾ρ`, the clauses `ExactOne(X_{E(w)})` for `w ∈ supp(C)` imply `C^σ`: an edge
assignment satisfying them propagates to an assignment satisfying `C` (Lemma
[lem:local-soundness]), and `σ` maps each variable of `C` to a formula computing its
propagated value.

Paper: proof of Lemma [lem:frege-transfer], "Local derivations". -/
theorem implies_toFormula_subst_sigmaF (hM₁ : M₁.WiresStripLocal) (hM₂ : M₂.WiresStripLocal)
    [Nonempty U] [Nonempty V] (hn : n₀ ≤ n) (hg : 1 ≤ g)
    (hsp : (inputXY I M₁ M₂).IsSparse g) (hsp' : (inputYZ I M₁ M₂).IsSparse g)
    (hsp₁ : (inputXY_Z I M₁ M₂).IsSparse g) (hsp₂ : (inputX_YZ I M₁ M₂).IsSparse g)
    (hcard : Fintype.card U = Fintype.card V + 1) (hU : ∀ u, ∃ e, H.left e = u)
    (hV : ∀ v, ∃ e, H.right e = v) {C : Clause (AssocVar n M₁.Wire M₂.Wire)}
    (hC : C ∈ (Assoc M₁ M₂).restrict (rho I M₁ M₂)) :
    ∀ β : E → Bool, CNF.Sat β (EdgePM.localCNF H (supp I M₁ M₂ C)) →
      (C.toFormula.subst (sigmaF I M₁ M₂)).eval β = true := by
  intro β hβ
  rw [EdgePM.sat_localCNF_iff] at hβ
  have hloc := exists_starLocalFn_valFn I M₁ M₂ hM₁ hM₂ hn hg hsp hsp' hsp₁ hsp₂
  have hsat := sat_propagate_of_exactOne_supp I M₁ M₂ hn hg hsp hsp' hsp₁ hsp₂ hcard hU hV hC hβ
  rw [Formula.eval_subst, Clause.eval_toFormula_eq_true_iff]
  have : (fun q => (sigmaF I M₁ M₂ q).eval β) = propagate I M₁ M₂ β :=
    funext fun q => eval_sigmaF I M₁ M₂ hloc β q
  rwa [this]

end Assoc

namespace FregeSystem

/-- **Reduction from `PM(H)`.** For a Frege system, a maximum degree `Δ` and a width bound `w`
there are constants `d₀` and `s₀` such that under the hypotheses of Section 8 (strip-local
encodings, `n₀ ≤ n`, a width `g ≥ 1` with the induced input restrictions `g`-sparse,
`|U| = |V| + 1`, no isolated vertices, maximum degree at most `Δ`, and clauses of `Assoc_n`
other than the miter clause of width at most `w`), every Frege refutation `π` of `Assoc_n`
yields a Frege refutation of `PM(H)` of depth at most `depth(π) + d₀` and size at most
`s₀ |π|`.

Paper: Lemma [lem:frege-transfer]. -/
theorem frege_transfer (𝓕 : FregeSystem) (Δ w : ℕ) :
    ∃ d₀ s₀ : ℕ, ∀ (U V E : Type) [Fintype U] [Fintype V] [Fintype E] [DecidableEq U]
      [DecidableEq V] [DecidableEq E] [Nonempty U] [Nonempty V] (H : Bipartite U V E)
      (g K n₀ n : ℕ) (I : IndexMaps H g K n₀) (M₁ : MulEncoding n) (M₂ : MulEncoding (2 * n)),
      M₁.WiresStripLocal → M₂.WiresStripLocal → n₀ ≤ n → 1 ≤ g →
      (Assoc.inputXY I M₁ M₂).IsSparse g → (Assoc.inputYZ I M₁ M₂).IsSparse g →
      (Assoc.inputXY_Z I M₁ M₂).IsSparse g → (Assoc.inputX_YZ I M₁ M₂).IsSparse g →
      Fintype.card U = Fintype.card V + 1 → (∀ u, ∃ e, H.left e = u) →
      (∀ v, ∃ e, H.right e = v) → H.MaxDegreeLE Δ →
      (∀ C ∈ Assoc M₁ M₂, C ≠ Assoc.miterClause n M₁.Wire M₂.Wire → C.card ≤ w) →
      ∀ π : 𝓕.Refutation (Assoc M₁ M₂).toFormulas,
        ∃ π' : 𝓕.Refutation (EdgePM H).toFormulas,
          π'.depth ≤ π.depth + d₀ ∧ π'.size ≤ s₀ * π.size := by
  -- the constants: the restriction step, the size of `σ`, and the local derivations
  obtain ⟨d₁, s₁, h₁⟩ := 𝓕.exists_refutation_restrict w
  obtain ⟨D₃, S₃, h₃⟩ :=
    𝓕.exists_local_derivation_cnf (2 * Δ * w * Δ) ((2 ^ Δ * (3 * Δ + 3) + 1) * (3 * w + 1))
  refine ⟨max (d₁ + 4) D₃, (S₃ + 1) * ((2 ^ Δ * (3 * Δ + 3) + 1) * s₁), ?_⟩
  intro U V E _ _ _ _ _ _ _ _ H g K n₀ n I M₁ M₂ hM₁ hM₂ hn hg hsp hsp' hsp₁ hsp₂ hcard hU hV hΔ
    hw π
  have hloc := Assoc.exists_starLocalFn_valFn I M₁ M₂ hM₁ hM₂ hn hg hsp hsp' hsp₁ hsp₂
  have hmiter : ∀ C ∈ Assoc M₁ M₂, C.Survives (Assoc.rho I M₁ M₂) → C.card ≤ w :=
    fun C hC hsurv => hw C hC fun h => hsurv (by
      rw [h]
      exact Assoc.satBy_miterClause I M₁ M₂ hn)
  -- Step 1: apply `ρ`
  obtain ⟨π₁, hπ₁d, hπ₁s⟩ := h₁ _ (Assoc M₁ M₂) (Assoc.rho I M₁ M₂) hmiter π
  -- Step 2: the DNF substitution `σ`
  have hB : 1 ≤ 2 ^ Δ * (3 * Δ + 3) + 1 := Nat.le_add_left 1 _
  obtain ⟨π₂, hπ₂d, hπ₂s⟩ : ∃ π₂ : 𝓕.Refutation (Formula.subst (Assoc.sigmaF I M₁ M₂) ''
      ((Assoc M₁ M₂).restrict (Assoc.rho I M₁ M₂)).toFormulas),
      π₂.depth ≤ π₁.depth + 3 + 1 ∧ π₂.size ≤ (2 ^ Δ * (3 * Δ + 3) + 1) * π₁.size :=
    ⟨π₁.subst (Assoc.sigmaF I M₁ M₂), π₁.depth_subst_le (Assoc.depth_sigmaF_le I M₁ M₂),
      π₁.size_subst_le hB (Assoc.size_sigmaF_le I M₁ M₂ hΔ)⟩
  -- Step 3: derive each initial formula `C^σ` from the `ExactOne` clauses at the support of `C`
  obtain ⟨π₃, hπ₃s, hπ₃d⟩ := π₂.compose (Γ' := (EdgePM H).toFormulas) (K := S₃) (D := D₃)
    fun F _ hF => by
      obtain ⟨F₀, hF₀, rfl⟩ := hF
      obtain ⟨C, hC, rfl⟩ := CNF.mem_toFormulas.mp hF₀
      -- the width of `C`
      have hwidth : C.card ≤ w := by
        obtain ⟨C₁, hC₁, hsurv, rfl⟩ := CNF.mem_restrict.mp hC
        exact (Finset.card_le_card (Clause.restrict_subset _ C₁)).trans (hmiter C₁ hC₁ hsurv)
      -- the edge variables of the stars of the support of `C`
      have hX : ((Assoc.supp I M₁ M₂ C).biUnion H.star).card ≤ 2 * Δ * w * Δ := by
        refine Finset.card_biUnion_le.trans ?_
        refine (Finset.sum_le_card_nsmul _ _ Δ fun x _ => hΔ x).trans ?_
        rw [smul_eq_mul]
        exact Nat.mul_le_mul_right Δ
          ((Assoc.card_supp_le I M₁ M₂ hΔ hloc C).trans (Nat.mul_le_mul_left _ hwidth))
      have hΦ : (EdgePM.localCNF H (Assoc.supp I M₁ M₂ C)).vars ⊆
          (Assoc.supp I M₁ M₂ C).biUnion H.star := by
        intro v hv
        obtain ⟨D, hD, l, hl, rfl⟩ := CNF.mem_vars.mp hv
        obtain ⟨x, hx, hD⟩ := Finset.mem_biUnion.mp hD
        exact Finset.mem_biUnion.mpr
          ⟨x, hx, EdgePM.vars_exactOne_subset H x (CNF.mem_vars.mpr ⟨D, hD, l, hl, rfl⟩)⟩
      have hG : (C.toFormula.subst (Assoc.sigmaF I M₁ M₂)).vars ⊆
          (Assoc.supp I M₁ M₂ C).biUnion H.star := by
        refine (Formula.vars_subst_subset _ _).trans (Finset.biUnion_subset.mpr fun q hq => ?_)
        rw [Clause.vars_toFormula] at hq
        exact Assoc.vars_sigmaF_subset I M₁ M₂ hq
      have hGs : (C.toFormula.subst (Assoc.sigmaF I M₁ M₂)).size ≤
          (2 ^ Δ * (3 * Δ + 3) + 1) * (3 * w + 1) := by
        refine (Formula.size_subst_le hB (Assoc.size_sigmaF_le I M₁ M₂ hΔ) _).trans
          (Nat.mul_le_mul_left _ ?_)
        have := Clause.size_toFormula_le C
        omega
      obtain ⟨δ, hd, hs⟩ := h₃ E _ (EdgePM.localCNF H (Assoc.supp I M₁ M₂ C)) _ hX hΦ hG hGs
        (Assoc.implies_toFormula_subst_sigmaF I M₁ M₂ hM₁ hM₂ hn hg hsp hsp' hsp₁ hsp₂ hcard hU hV
          hC)
      refine ⟨δ.mono (CNF.toFormulas_mono (EdgePM.localCNF_subset H _)), ?_, ?_⟩
      · change δ.size ≤ _
        exact hs.trans (Nat.le_mul_of_pos_right _ (Formula.size_pos _))
      · change δ.depth ≤ _
        exact hd
  refine ⟨π₃, ?_, ?_⟩
  · omega
  · calc π₃.size ≤ (S₃ + 1) * π₂.size := hπ₃s
      _ ≤ (S₃ + 1) * ((2 ^ Δ * (3 * Δ + 3) + 1) * π₁.size) := Nat.mul_le_mul_left _ hπ₂s
      _ ≤ (S₃ + 1) * ((2 ^ Δ * (3 * Δ + 3) + 1) * (s₁ * π.size)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hπ₁s)
      _ = (S₃ + 1) * ((2 ^ Δ * (3 * Δ + 3) + 1) * s₁) * π.size := by ring

end FregeSystem

end AssocLB
