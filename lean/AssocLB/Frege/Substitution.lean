/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/
import AssocLB.Resolution.Substitution
import AssocLB.Frege.System

/-!
# The Frege substitution lemma

Paper: Section 9.1 (Bounded-depth Frege systems), paragraph "Formula substitutions" and Lemma
[lem:frege-substitution] (Frege substitution lemma); restrictions read as formula
substitutions; the weakening step of the proof of Lemma [lem:frege-transfer].

## Main definitions

* `Restriction.toFormulaSubst ρ`: the restriction `ρ` as a formula substitution, mapping each
  assigned variable to its constant and each unassigned variable to itself. This is how `ρ`
  is applied in Lemma [lem:frege-transfer], "which does not simplify away constants".
* `Frege.Derivation.subst π σ`: the substituted derivation `π^σ`, a derivation of `G^σ` from
  `Γ^σ`.

## Main results

* `Frege.Derivation.depth_subst_le`, `Frege.Derivation.size_subst_le`: Lemma
  [lem:frege-substitution], `depth(π^σ) ≤ depth(π) + depth(σ) + 1` and `|π^σ| ≤ |σ| |π|`.
* `FregeSystem.exists_weakening_left`, `FregeSystem.exists_weakening_right`: the weakening
  step, `G ∨ F` (or `F ∨ G`) has a derivation from `G` of size `O(|G| + |F|)` and depth
  `O(1) + max(depth G, depth F)`, with constants depending only on the system. It is a fixed
  derivation of `p ∨ q` from `p`, obtained from completeness, substituted.
* `FregeSystem.exists_derivation_orBalanced_of_mem`: weakening along a path of a balanced
  disjunction. When the disjuncts have size at most `b`, `⋁ L` has a derivation from any
  `G ∈ L` of size at most `s₀ (b + 1) |⋁ L|` and depth at most `depth(⋁ L) + d₀`.
* `FregeSystem.exists_derivation_top`: `¬⊥` has a derivation from no premises of constant size.

## Design notes

* `π^σ` is defined, not merely shown to exist, as the substituted sequence: Frege rules are
  closed under substitution, so `π^σ` is literally a derivation, without the case analysis
  that the resolution substitution lemma needs. Its `IsDerivation` proof is a proof field of
  the definition.
* The depth and size of a substitution are the hypotheses `∀ x, (σ x).depth ≤ s` and
  `∀ x, (σ x).size ≤ k`, see `AssocLB.Frege.Formula`.
* The weakening constants are existential (`∃ d₀ s₀, ∀ V G F, …`): they come from one
  derivation provided by completeness, whose size is not computed. Every constant of Section
  9 is of this form.
* The balanced weakening is what gives the linear size bound for the miter clause in Lemma
  [lem:frege-transfer]; see the design notes of `AssocLB.Frege.Formula` on `orBalanced`. The
  bound needs the disjuncts to have bounded size: the derivation weakens `G` into the subtrees
  along the path from the root to `G`, and each weakening costs the size of the subtree. The
  subtrees halve in number of disjuncts, so for disjuncts of size at most `b` their sizes form
  a geometric series, but a single large disjunct on the path would be paid for once per level.
  In the application the disjuncts are literals and constants, of size at most `4`.
-/

namespace AssocLB

variable {V V' : Type*}

/-! ### Restrictions as formula substitutions -/

/-- A restriction as a formula substitution: an assigned variable maps to its constant, an
unassigned variable to itself. Applying it does not simplify constants away.

Paper: proof of Lemma [lem:frege-transfer], "Application of `ρ`". -/
def Restriction.toFormulaSubst (ρ : Restriction V) : V → Formula V := fun v =>
  match ρ v with
  | some b => Formula.const b
  | none => Formula.var v

namespace Restriction

theorem toFormulaSubst_of_eq_some {ρ : Restriction V} {v : V} {b : Bool} (h : ρ v = some b) :
    ρ.toFormulaSubst v = Formula.const b := by
  simp [toFormulaSubst, h]

theorem toFormulaSubst_of_eq_none {ρ : Restriction V} {v : V} (h : ρ v = none) :
    ρ.toFormulaSubst v = Formula.var v := by
  simp [toFormulaSubst, h]

theorem depth_toFormulaSubst (ρ : Restriction V) (v : V) : (ρ.toFormulaSubst v).depth = 0 := by
  unfold toFormulaSubst
  split <;> simp

theorem size_toFormulaSubst_le (ρ : Restriction V) (v : V) : (ρ.toFormulaSubst v).size ≤ 2 := by
  unfold toFormulaSubst
  split
  · exact Formula.size_const_le _
  · simp

-- Sanity check: under an assignment extending `ρ`, `F^ρ` evaluates like `F`.
example {ρ : Restriction V} {α : V → Bool} (hα : ρ.Extends α) (F : Formula V) :
    (F.subst ρ.toFormulaSubst).eval α = F.eval α := by
  rw [Formula.eval_subst]
  congr 1
  funext v
  rcases h : ρ v with _ | b
  · rw [toFormulaSubst_of_eq_none h, Formula.eval_var]
  · rw [toFormulaSubst_of_eq_some h, Formula.eval_const, hα v b h]

/-- The formula of a clause satisfied by `ρ` has `¬⊥` among its disjuncts after substituting
`ρ`: the satisfied literal becomes `¬⊥`. -/
theorem exists_top_mem_of_satBy {ρ : Restriction V} {C : Clause V} (h : C.SatBy ρ) :
    Formula.top ∈ (C.toList.map Literal.toFormula).map (Formula.subst ρ.toFormulaSubst) := by
  obtain ⟨l, hl, hs⟩ := h
  refine List.mem_map.mpr ⟨l.toFormula, List.mem_map.mpr ⟨l, Finset.mem_toList.mpr hl, rfl⟩, ?_⟩
  rcases l with ⟨v, _ | _⟩
  · simp only [Literal.SatBy] at hs
    simp [Literal.toFormula, toFormulaSubst_of_eq_some hs]
  · simp only [Literal.SatBy] at hs
    simp [Literal.toFormula, toFormulaSubst_of_eq_some hs]

end Restriction

namespace Frege

variable [DecidableEq V] [DecidableEq V'] {R : List FregeRule}

/-- Substituting a derivation sequence: initial formulas map to initial formulas of `Γ^σ`, and
rule instances to rule instances, since Frege rules are closed under substitution. -/
theorem IsDerivation.subst {Γ : Set (Formula V)} {S : Finset (Formula V)} {π : List (Formula V)}
    (h : IsDerivation R Γ S π) (σ : V → Formula V') :
    IsDerivation R (Formula.subst σ '' Γ) (S.image (Formula.subst σ))
      (π.map (Formula.subst σ)) := by
  induction π generalizing S with
  | nil => trivial
  | cons F π ih =>
    obtain ⟨hF, hπ⟩ := h
    refine ⟨?_, ?_⟩
    · rcases hF with hF | ⟨r, hr, τ, hprem, rfl⟩
      · exact Or.inl (Set.mem_image_of_mem _ hF)
      · refine Or.inr ⟨r, hr, fun i => (τ i).subst σ, fun P hP => ?_, ?_⟩
        · rw [← Formula.subst_subst]
          exact Finset.mem_image_of_mem _ (hprem P hP)
        · rw [Formula.subst_subst]
    · have := ih hπ
      rwa [Finset.image_insert] at this

/-- **The substituted derivation `π^σ`.** Each line is substituted; initial formulas map to
initial formulas of `Γ^σ`, and rule instances to rule instances, since Frege rules are closed
under substitution.

Paper: Section 9.1, "Formula substitutions"; Lemma [lem:frege-substitution]. -/
def Derivation.subst {Γ : Set (Formula V)} {G : Formula V} (π : Derivation R Γ G)
    (σ : V → Formula V') : Derivation R (Formula.subst σ '' Γ) (G.subst σ) where
  lines := π.lines.map (Formula.subst σ)
  isDerivation := by
    have := π.isDerivation.subst σ
    rwa [Finset.image_empty] at this
  getLast?_lines := by
    rw [List.getLast?_map, π.getLast?_lines, Option.map_some]

@[simp] theorem Derivation.lines_subst {Γ : Set (Formula V)} {G : Formula V}
    (π : Derivation R Γ G) (σ : V → Formula V') :
    (π.subst σ).lines = π.lines.map (Formula.subst σ) := rfl

/-- `depth(π^σ) ≤ depth(π) + depth(σ) + 1`.

Paper: Lemma [lem:frege-substitution]. -/
theorem Derivation.depth_subst_le {Γ : Set (Formula V)} {G : Formula V} (π : Derivation R Γ G)
    {σ : V → Formula V'} {s : ℕ} (hσ : ∀ x, (σ x).depth ≤ s) :
    (π.subst σ).depth ≤ π.depth + s + 1 := by
  rw [Derivation.depth_le_iff]
  intro F' hF'
  rw [Derivation.lines_subst] at hF'
  obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hF'
  have h₁ := Formula.depth_subst_le hσ F
  have h₂ := π.depth_le_depth hF
  omega

/-- `|π^σ| ≤ |σ| |π|`.

Paper: Lemma [lem:frege-substitution]. -/
theorem Derivation.size_subst_le {Γ : Set (Formula V)} {G : Formula V} (π : Derivation R Γ G)
    {σ : V → Formula V'} {k : ℕ} (hk : 1 ≤ k) (hσ : ∀ x, (σ x).size ≤ k) :
    (π.subst σ).size ≤ k * π.size := by
  unfold Derivation.size
  rw [Derivation.lines_subst, List.map_map, ← List.sum_map_mul_left]
  exact List.sum_le_sum fun F _ => Formula.size_subst_le hk hσ F

/-- A refutation substitutes to a refutation: `⊥^σ = ⊥`. -/
def Refutation.subst {Γ : Set (Formula V)} (π : Refutation R Γ) (σ : V → Formula V') :
    Refutation R (Formula.subst σ '' Γ) :=
  Derivation.subst π σ

end Frege

namespace FregeSystem

variable (𝓕 : FregeSystem)

/-- `¬⊥` has a derivation from no premises, of constant size and depth. -/
theorem exists_derivation_top :
    ∃ d₀ s₀ : ℕ, ∀ (V : Type) [DecidableEq V],
      ∃ δ : 𝓕.Derivation (∅ : Set (Formula V)) Formula.top, δ.depth ≤ d₀ ∧ δ.size ≤ s₀ := by
  obtain ⟨δ₀⟩ := 𝓕.complete 0 ∅ Formula.top fun _ _ => rfl
  refine ⟨δ₀.depth + 1, δ₀.size, fun V _ => ?_⟩
  refine ⟨((δ₀.subst (Fin.elim0 : Fin 0 → Formula V)).mono (by simp)).copy (by simp), ?_, ?_⟩
  · change (δ₀.subst (Fin.elim0 : Fin 0 → Formula V)).depth ≤ δ₀.depth + 1
    have := δ₀.depth_subst_le (σ := (Fin.elim0 : Fin 0 → Formula V)) (s := 0) fun x => x.elim0
    omega
  · change (δ₀.subst (Fin.elim0 : Fin 0 → Formula V)).size ≤ δ₀.size
    have := δ₀.size_subst_le (σ := (Fin.elim0 : Fin 0 → Formula V)) (k := 1) le_rfl
      fun x => x.elim0
    omega

/-- **Weakening, general form.** A two-variable formula `H` implied by `p₀` gives, for all `G`
and `F`, a derivation of `H^{[G, F]}` from `G` of size `O(|G| + |F|)` and depth
`O(1) + max(depth G, depth F)`: take the derivation of `H` from `p₀` given by completeness and
substitute. The constants depend only on the system and on `H`. -/
private theorem exists_weakening_aux (H : Formula (Fin 2))
    (hH : Formula.Implies (↑({Formula.var 0} : Finset (Formula (Fin 2)))) H) :
    ∃ d₀ s₀ : ℕ, ∀ (V : Type) [DecidableEq V] (G F : Formula V),
      ∃ δ : 𝓕.Derivation {G} (H.subst ![G, F]),
        δ.depth ≤ max G.depth F.depth + d₀ ∧ δ.size ≤ s₀ * (G.size + F.size) := by
  obtain ⟨δ₀⟩ := 𝓕.complete 2 {Formula.var 0} H hH
  refine ⟨δ₀.depth + 1, δ₀.size, fun V _ G F => ?_⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : Fin 2 → Formula V, σ = ![G, F] := ⟨_, rfl⟩
  have hσd : ∀ x, (σ x).depth ≤ max G.depth F.depth :=
    Fin.forall_fin_two.mpr ⟨by simp [hσ], by simp [hσ]⟩
  have hσs : ∀ x, (σ x).size ≤ G.size + F.size :=
    Fin.forall_fin_two.mpr ⟨by simp [hσ], by simp [hσ]⟩
  refine ⟨((δ₀.subst σ).mono (by simp [hσ])).copy (by rw [hσ]), ?_, ?_⟩
  · rw [Frege.Derivation.depth_copy, Frege.Derivation.depth_mono]
    have := δ₀.depth_subst_le hσd
    omega
  · rw [Frege.Derivation.size_copy, Frege.Derivation.size_mono, Nat.mul_comm]
    exact δ₀.size_subst_le (by have := G.size_pos; omega) hσs

/-- **Weakening on the right.** `G ∨ F` has a derivation from `G` of size `O(|G| + |F|)` and
depth `O(1) + max(depth G, depth F)`, with constants depending only on the system: a fixed
derivation of `p ∨ q` from `p`, substituted.

Paper: proof of Lemma [lem:frege-transfer], "Application of `ρ`". -/
theorem exists_weakening_right :
    ∃ d₀ s₀ : ℕ, ∀ (V : Type) [DecidableEq V] (G F : Formula V),
      ∃ δ : 𝓕.Derivation {G} (Formula.or G F),
        δ.depth ≤ max G.depth F.depth + d₀ ∧ δ.size ≤ s₀ * (G.size + F.size) := by
  obtain ⟨d₀, s₀, h⟩ := 𝓕.exists_weakening_aux (Formula.or (Formula.var 0) (Formula.var 1))
    fun α hα => by
      have h0 : α 0 = true := hα (Formula.var 0) (by simp)
      simp [h0]
  exact ⟨d₀, s₀, fun V _ G F => by simpa using h V G F⟩

/-- **Weakening on the left.** `F ∨ G` has a derivation from `G` of size `O(|G| + |F|)` and
depth `O(1) + max(depth G, depth F)`.

Paper: proof of Lemma [lem:frege-transfer], "Application of `ρ`". -/
theorem exists_weakening_left :
    ∃ d₀ s₀ : ℕ, ∀ (V : Type) [DecidableEq V] (G F : Formula V),
      ∃ δ : 𝓕.Derivation {G} (Formula.or F G),
        δ.depth ≤ max G.depth F.depth + d₀ ∧ δ.size ≤ s₀ * (G.size + F.size) := by
  obtain ⟨d₀, s₀, h⟩ := 𝓕.exists_weakening_aux (Formula.or (Formula.var 1) (Formula.var 0))
    fun α hα => by
      have h0 : α 0 = true := hα (Formula.var 0) (by simp)
      simp [h0]
  exact ⟨d₀, s₀, fun V _ G F => by simpa using h V G F⟩

/-- **Weakening along a path.** A balanced disjunction of formulas of size at most `b` has a
derivation from any one of its disjuncts of size at most `s₀ (b + 1)` times the size of the
disjunction and of depth larger by a constant: weaken the disjunct into the subtrees along the
path from it to the root, whose sizes form a geometric series since they halve in number of
disjuncts. The constants `d₀`, `s₀` depend only on the system.

The proof uses the invariant `|δ| + K (b + 1) ≤ K (b + 1) (2 |L|)` with `K = 2 (s₁ + s₂) + 1`,
where `s₁`, `s₂` are the size constants of the two weakening derivations: a half of `L` has at
most `(|L| + 1) / 2` disjuncts, and the disjunction of `L` has at most `(b + 1) |L|` symbols
besides its root. -/
theorem exists_derivation_orBalanced_of_mem :
    ∃ d₀ s₀ : ℕ, ∀ (V : Type) [DecidableEq V] (b : ℕ) (L : List (Formula V)) (G : Formula V),
      (∀ F ∈ L, F.size ≤ b) → G ∈ L →
      ∃ δ : 𝓕.Derivation {G} (Formula.orBalanced L),
        δ.depth ≤ (Formula.orBalanced L).depth + d₀ ∧
          δ.size ≤ s₀ * (b + 1) * (Formula.orBalanced L).size := by
  obtain ⟨d₁, s₁, h₁⟩ := 𝓕.exists_weakening_right
  obtain ⟨d₂, s₂, h₂⟩ := 𝓕.exists_weakening_left
  obtain ⟨K, hK⟩ : ∃ K, K = 2 * (s₁ + s₂) + 1 := ⟨_, rfl⟩
  refine ⟨max d₁ d₂, 2 * K, fun V _ b L G hb hG => ?_⟩
  suffices h : ∃ δ : 𝓕.Derivation {G} (Formula.orBalanced L),
      δ.depth ≤ (Formula.orBalanced L).depth + max d₁ d₂ ∧
        δ.size + K * (b + 1) ≤ K * (b + 1) * (2 * L.length) by
    obtain ⟨δ, hd, hs⟩ := h
    refine ⟨δ, hd, ?_⟩
    have hlen := Formula.length_le_size_orBalanced L
    nlinarith [Nat.mul_le_mul_left (K * (b + 1)) hlen]
  induction L using Formula.orBalanced.induct with
  | case1 => simp at hG
  | case2 F =>
    rw [List.mem_singleton] at hG
    subst hG
    refine ⟨(Frege.Derivation.single (Set.mem_singleton _)).copy
      (Formula.orBalanced_singleton _).symm, by simp, ?_⟩
    have := hb _ List.mem_cons_self
    simp only [Frege.Derivation.size_copy, Frege.Derivation.size_single, List.length_singleton]
    subst hK
    nlinarith
  | case3 F₁ F₂ L ih₁ ih₂ =>
    -- the two halves and their lengths
    have hn2 : 2 ≤ (F₁ :: F₂ :: L).length := by simp
    have h2t : 2 * ((F₁ :: F₂ :: L).take ((L.length + 2) / 2)).length ≤
        (F₁ :: F₂ :: L).length + 1 := by
      simp only [List.length_take, List.length_cons]
      omega
    have h2u : 2 * ((F₁ :: F₂ :: L).drop ((L.length + 2) / 2)).length ≤
        (F₁ :: F₂ :: L).length + 1 := by
      simp only [List.length_drop, List.length_cons]
      omega
    have hAB := Formula.size_orBalanced_le_of_forall_size_le hb
    rw [Formula.orBalanced.eq_3, Formula.size_or] at hAB
    rw [Formula.orBalanced.eq_3]
    set A := Formula.orBalanced ((F₁ :: F₂ :: L).take ((L.length + 2) / 2)) with hA
    set B := Formula.orBalanced ((F₁ :: F₂ :: L).drop ((L.length + 2) / 2)) with hB
    set n := (F₁ :: F₂ :: L).length with hn
    have hAd : A.depth ≤ (Formula.or A B).depth := by
      rw [Formula.depth_or]
      exact (Formula.depth_le_depthFrom _ _).trans (le_max_left _ _)
    have hBd : B.depth ≤ (Formula.or A B).depth := by
      rw [Formula.depth_or]
      exact (Formula.depth_le_depthFrom _ _).trans (le_max_right _ _)
    have p1 := Nat.mul_le_mul_left (s₁ * (b + 1)) hn2
    have p2 := Nat.mul_le_mul_left (s₂ * (b + 1)) (Nat.one_le_of_lt hn2)
    rw [← List.take_append_drop ((L.length + 2) / 2) (F₁ :: F₂ :: L), List.mem_append] at hG
    rcases hG with hG | hG
    · -- `G` lies in the first half: weaken on the right
      obtain ⟨δ₁, hd₁, hs₁⟩ := ih₁ (fun F hF => hb F (List.mem_of_mem_take hF)) hG
      obtain ⟨δ₂, hd₂, hs₂⟩ := h₁ V A B
      obtain ⟨δ, hδd, hδs⟩ := δ₁.exists_trans_le δ₂
        (d := (Formula.or A B).depth + max d₁ d₂) (by omega) (by omega)
      refine ⟨δ, hδd, ?_⟩
      · have e1 := Nat.mul_le_mul_left (K * (b + 1)) h2t
        have e2 : δ₂.size ≤ s₁ * ((b + 1) * n) :=
          hs₂.trans (Nat.mul_le_mul_left s₁ (by omega))
        subst hK
        nlinarith
    · -- `G` lies in the second half: weaken on the left
      obtain ⟨δ₁, hd₁, hs₁⟩ := ih₂ (fun F hF => hb F (List.mem_of_mem_drop hF)) hG
      obtain ⟨δ₂, hd₂, hs₂⟩ := h₂ V B A
      obtain ⟨δ, hδd, hδs⟩ := δ₁.exists_trans_le δ₂
        (d := (Formula.or A B).depth + max d₁ d₂) (by omega) (by omega)
      refine ⟨δ, hδd, ?_⟩
      · have e1 := Nat.mul_le_mul_left (K * (b + 1)) h2u
        have e2 : δ₂.size ≤ s₂ * ((b + 1) * n) :=
          hs₂.trans (Nat.mul_le_mul_left s₂ (by omega))
        subst hK
        nlinarith

end FregeSystem

end AssocLB
