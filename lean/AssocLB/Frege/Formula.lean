/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/
import AssocLB.Resolution.Basic

/-!
# Frege formulas

Paper: Section 9.1 (Bounded-depth Frege systems), paragraph "Formulas and depth", and the
formulas-level part of paragraph "Formula substitutions". Also the canonical DNF of a Boolean
function used in the proof of Lemma [lem:frege-transfer].

## Main definitions

* `Formula V`: formulas over the variables `V`, built from variables and the constant `⊥` by
  negation and binary disjunction. `Formula.const b` is `⊥` or `¬⊥`, and `Formula.top` is
  `¬⊥`.
* `Formula.eval α F`: the value of `F` under the assignment `α : V → Bool`;
  `Formula.Implies Γ G`: every assignment satisfying all formulas of `Γ` satisfies `G`.
* `Formula.depth F`: the maximum number of alternations between `∨` and `¬` on a path from the
  root to a leaf; `Formula.depthFrom p F` is the depth of `F` below a parent connective `p`.
  A literal has depth `0`, a clause depth at most `1`, a DNF depth at most `3`.
* `Formula.size F`: the number of symbols; `Formula.vars F`: the variables occurring in `F`.
* `Formula.subst σ F`: the formula substitution `F^σ`, replacing every variable `x` by the
  formula `σ x`.
* `Formula.orBalanced L`: the balanced disjunction of a list of formulas.
* `Literal.toFormula`, `Clause.toFormula`, `CNF.toFormulas`: literals and clauses read as
  formulas, and the set of formulas of a CNF.
* `Formula.term X τ`, `Formula.dnf X f`: the term of an assignment `τ` to the variables `X` and
  the canonical DNF of a Boolean function `f` of the variables `X`.

## Main results

* `Formula.eval_subst`, `Formula.subst_subst`: `F^σ` evaluates like `F` under `α ∘ σ`, and
  substitutions compose.
* `Formula.depth_subst_le`, `Formula.size_subst_le`: `depth(F^σ) ≤ depth(F) + depth(σ) + 1`
  and `|F^σ| ≤ |σ| |F|`, the formula-level content of Lemma [lem:frege-substitution].
* `Clause.eval_toFormula`, `Clause.depth_toFormula_le`, `Clause.size_toFormula_le`: the formula
  of a clause evaluates like the clause, has depth at most `1` and size `O(|C|)`.
* `Formula.eval_dnf`, `Formula.depth_dnf_le`, `Formula.size_dnf_le`: the canonical DNF computes
  `f`, has depth at most `3` and size depending only on `|X|`.

## Design notes

* Disjunction is binary. Håstad's formulas have disjunctions of unbounded arity, but with depth
  measured by alternations a nest of binary disjunctions counts as one disjunction, so the
  depth of a formula is that of its flattened form, and its size is within a factor of two.
  In exchange, the weakening step of Lemma [lem:frege-transfer] (deriving `G ∨ F` from `G`) is
  literally one substituted instance of a fixed derivation, and rule instances need no
  flattening convention.
* The constants are `⊥` and `¬⊥`, following Håstad; `⊥` is a leaf of depth `0`. Substituting a
  constant for a variable can raise the depth by one (`x ∨ y` becomes `¬⊥ ∨ y`), which is the
  `+ 1` of Lemma [lem:frege-substitution].
* `depthFrom p F` carries the connective of the parent (`none` at the root, `some true` below
  `∨`, `some false` below `¬`) and adds one at each node whose connective differs from its
  parent's, so `depth F ≤ depthFrom p F ≤ depth F + 1`.
* The formula of a clause is the *balanced* disjunction of its literals in the order of
  `Finset.toList`. Balance is what makes the size accounting of Lemma [lem:frege-transfer]
  linear: the miter clause has width `4n` and is satisfied by `ρ`, so its image under `ρ` is a
  disjunction with `¬⊥` at one leaf, derived from `¬⊥` by weakening along the path to that
  leaf, and in a balanced tree of disjuncts of bounded size (literals and constants here) the
  subtrees along the path have geometrically decreasing sizes
  (`FregeSystem.exists_derivation_orBalanced_of_mem`). In a right-nested disjunction the same
  derivation would be quadratic. The order of
  `Finset.toList` is arbitrary but fixed, so `C.toFormula` is a function of the clause; the
  arguments that need order-independence (Lemma [lem:frege-local-derivations] and the
  restriction step of Lemma [lem:frege-transfer]) quantify over finitely many patterns of
  lists rather than over clauses.
* Substitutions are total functions `V → Formula V'`. Their depth and size are hypotheses
  `∀ x, (σ x).depth ≤ s` and `∀ x, (σ x).size ≤ k` rather than maxima over a possibly infinite
  `V`.
* Conjunctions are `¬(¬F₁ ∨ ¬F₂)`, as in the paper; the term of `τ` is the conjunction of the
  literals `v` (if `τ v`) or `¬v` (otherwise) over `v ∈ X`, written as the negation of the
  balanced disjunction of the complementary literals.
-/

namespace AssocLB

/-- A Frege formula over the variables `V`: variables, the constant `⊥`, negation and binary
disjunction.

Paper: Section 9.1, "Formulas and depth". -/
inductive Formula (V : Type*)
  /-- The variable `v`. -/
  | var (v : V) : Formula V
  /-- The constant `⊥`. -/
  | bot : Formula V
  /-- The negation `¬F`. -/
  | neg (F : Formula V) : Formula V
  /-- The disjunction `F ∨ G`. -/
  | or (F G : Formula V) : Formula V
  deriving DecidableEq

namespace Formula

variable {V V' : Type*}

/-- The constant `b`: `⊥` for `false` and `¬⊥` for `true`.

Paper: Section 9.1, "Formulas and depth" (constants). -/
def const : Bool → Formula V
  | false => bot
  | true => neg bot

/-- The constant `⊤ = ¬⊥`. -/
abbrev top : Formula V := neg bot

@[simp] theorem const_false : (const false : Formula V) = bot := rfl

@[simp] theorem const_true : (const true : Formula V) = top := rfl

/-! ### Semantics -/

/-- The value of a formula under an assignment. -/
def eval (α : V → Bool) : Formula V → Bool
  | var v => α v
  | bot => false
  | neg F => !F.eval α
  | or F G => F.eval α || G.eval α

@[simp] theorem eval_var (α : V → Bool) (v : V) : (var v).eval α = α v := rfl

@[simp] theorem eval_bot (α : V → Bool) : (bot : Formula V).eval α = false := rfl

@[simp] theorem eval_neg (α : V → Bool) (F : Formula V) : (neg F).eval α = !F.eval α := rfl

@[simp] theorem eval_or (α : V → Bool) (F G : Formula V) :
    (or F G).eval α = (F.eval α || G.eval α) := rfl

@[simp] theorem eval_const (α : V → Bool) (b : Bool) : (const b : Formula V).eval α = b := by
  cases b <;> rfl

@[simp] theorem eval_top (α : V → Bool) : (top : Formula V).eval α = true := rfl

/-- `Formula.Implies Γ G`: every assignment satisfying all formulas of `Γ` satisfies `G`.

Paper: Section 9.1, "Frege systems" (`Γ` implies `G`). -/
def Implies (Γ : Set (Formula V)) (G : Formula V) : Prop :=
  ∀ α : V → Bool, (∀ F ∈ Γ, F.eval α = true) → G.eval α = true

theorem implies_of_mem {Γ : Set (Formula V)} {G : Formula V} (h : G ∈ Γ) : Implies Γ G :=
  fun _ hα => hα G h

theorem Implies.mono {Γ Γ' : Set (Formula V)} {G : Formula V} (h : Implies Γ G) (hΓ : Γ ⊆ Γ') :
    Implies Γ' G :=
  fun α hα => h α fun F hF => hα F (hΓ hF)

/-! ### Depth and size -/

/-- The depth of `F` below a parent connective `p`: `none` at the root, `some true` below a
disjunction, `some false` below a negation. One is added at each node whose connective differs
from its parent's; leaves contribute nothing. -/
def depthFrom : Option Bool → Formula V → ℕ
  | _, var _ => 0
  | _, bot => 0
  | p, neg F => (if p = some true then 1 else 0) + depthFrom (some false) F
  | p, or F G =>
      (if p = some false then 1 else 0) + max (depthFrom (some true) F) (depthFrom (some true) G)

/-- The depth of a formula: the maximum number of alternations between `∨` and `¬` on a path
from the root to a leaf. A literal has depth `0`, a clause at most `1`, a DNF at most `3`.

Paper: Section 9.1, "Formulas and depth". -/
def depth (F : Formula V) : ℕ := depthFrom none F

@[simp] theorem depth_var (v : V) : (var v).depth = 0 := rfl

@[simp] theorem depth_bot : (bot : Formula V).depth = 0 := rfl

@[simp] theorem depth_neg_var (v : V) : (neg (var v)).depth = 0 := rfl

@[simp] theorem depth_top : (top : Formula V).depth = 0 := rfl

@[simp] theorem depth_const (b : Bool) : (const b : Formula V).depth = 0 := by cases b <;> rfl

/-- The depth of a disjunction is the maximum of the depths of its disjuncts seen from a
disjunction; nesting disjunctions does not increase the depth. -/
theorem depth_or (F G : Formula V) :
    (or F G).depth = max (depthFrom (some true) F) (depthFrom (some true) G) := by
  simp [depth, depthFrom]

theorem depth_le_depthFrom (p : Option Bool) (F : Formula V) : F.depth ≤ depthFrom p F := by
  cases F <;> simp [depth, depthFrom]

theorem depthFrom_le_depth_add_one (p : Option Bool) (F : Formula V) :
    depthFrom p F ≤ F.depth + 1 := by
  cases F <;> simp only [depth, depthFrom] <;> (try split_ifs) <;> omega

theorem depth_neg_le (F : Formula V) : (neg F).depth ≤ F.depth + 1 := by
  have := depthFrom_le_depth_add_one (some false) F
  simpa [depth, depthFrom] using this

theorem depth_or_le (F G : Formula V) : (or F G).depth ≤ max F.depth G.depth + 1 := by
  rw [depth_or]
  have h₁ := depthFrom_le_depth_add_one (some true) F
  have h₂ := depthFrom_le_depth_add_one (some true) G
  omega

/-- The size of a formula: its number of symbols.

Paper: Section 9.1, "Formulas and depth". -/
def size : Formula V → ℕ
  | var _ => 1
  | bot => 1
  | neg F => F.size + 1
  | or F G => F.size + G.size + 1

@[simp] theorem size_var (v : V) : (var v).size = 1 := rfl

@[simp] theorem size_bot : (bot : Formula V).size = 1 := rfl

@[simp] theorem size_neg (F : Formula V) : (neg F).size = F.size + 1 := rfl

@[simp] theorem size_or (F G : Formula V) : (or F G).size = F.size + G.size + 1 := rfl

theorem size_pos (F : Formula V) : 0 < F.size := by
  cases F <;> simp [size]

theorem size_const_le (b : Bool) : (const b : Formula V).size ≤ 2 := by
  cases b <;> simp [size]

/-- The variables occurring in a formula. -/
def vars [DecidableEq V] : Formula V → Finset V
  | var v => {v}
  | bot => ∅
  | neg F => F.vars
  | or F G => F.vars ∪ G.vars

@[simp] theorem vars_var [DecidableEq V] (v : V) : (var v).vars = {v} := rfl

@[simp] theorem vars_bot [DecidableEq V] : (bot : Formula V).vars = ∅ := rfl

@[simp] theorem vars_neg [DecidableEq V] (F : Formula V) : (neg F).vars = F.vars := rfl

@[simp] theorem vars_or [DecidableEq V] (F G : Formula V) : (or F G).vars = F.vars ∪ G.vars :=
  rfl

/-- The value of a formula depends only on the values of its variables. -/
theorem eval_congr [DecidableEq V] {α α' : V → Bool} {F : Formula V}
    (h : ∀ v ∈ F.vars, α v = α' v) : F.eval α = F.eval α' := by
  induction F with
  | var v => exact h v (by simp)
  | bot => rfl
  | neg F ih =>
    simp only [eval_neg]
    rw [ih (by simpa using h)]
  | or F G ihF ihG =>
    simp only [eval_or]
    rw [ihF fun v hv => h v (by simp [hv]), ihG fun v hv => h v (by simp [hv])]

/-- A formula has at most as many variables as symbols. -/
theorem card_vars_le_size [DecidableEq V] (F : Formula V) : F.vars.card ≤ F.size := by
  induction F with
  | var v => simp
  | bot => simp
  | neg F ih =>
    simp only [vars_neg, size_neg]
    omega
  | or F G ihF ihG =>
    have := Finset.card_union_le F.vars G.vars
    simp only [vars_or, size_or]
    omega

/-! ### Substitutions -/

/-- The formula substitution `F^σ`: every variable `x` is replaced by the formula `σ x`.

Paper: Section 9.1, "Formula substitutions". -/
def subst (σ : V → Formula V') : Formula V → Formula V'
  | var v => σ v
  | bot => bot
  | neg F => neg (F.subst σ)
  | or F G => or (F.subst σ) (G.subst σ)

@[simp] theorem subst_var (σ : V → Formula V') (v : V) : (var v).subst σ = σ v := rfl

@[simp] theorem subst_bot (σ : V → Formula V') : (bot : Formula V).subst σ = bot := rfl

@[simp] theorem subst_neg (σ : V → Formula V') (F : Formula V) :
    (neg F).subst σ = neg (F.subst σ) := rfl

@[simp] theorem subst_or (σ : V → Formula V') (F G : Formula V) :
    (or F G).subst σ = or (F.subst σ) (G.subst σ) := rfl

@[simp] theorem subst_const (σ : V → Formula V') (b : Bool) :
    (const b : Formula V).subst σ = const b := by
  cases b <;> rfl

/-- `F^σ` evaluates under `α` as `F` evaluates under `x ↦ eval α (σ x)`. -/
theorem eval_subst (σ : V → Formula V') (α : V' → Bool) (F : Formula V) :
    (F.subst σ).eval α = F.eval fun v => (σ v).eval α := by
  induction F with
  | var v => rfl
  | bot => rfl
  | neg F ih => simp only [subst_neg, eval_neg, ih]
  | or F G ihF ihG => simp only [subst_or, eval_or, ihF, ihG]

/-- Substitutions compose. -/
theorem subst_subst {V'' : Type*} (σ : V → Formula V') (τ : V' → Formula V'') (F : Formula V) :
    (F.subst σ).subst τ = F.subst fun v => (σ v).subst τ := by
  induction F with
  | var v => rfl
  | bot => rfl
  | neg F ih => simp only [subst_neg, ih]
  | or F G ihF ihG => simp only [subst_or, ihF, ihG]

/-- The identity substitution. -/
@[simp] theorem subst_var_eq (F : Formula V) : F.subst var = F := by
  induction F with
  | var v => rfl
  | bot => rfl
  | neg F ih => simp only [subst_neg, ih]
  | or F G ihF ihG => simp only [subst_or, ihF, ihG]

/-- `depth(F^σ) ≤ depth(F) + depth(σ) + 1`: the extra one is a possible alternation where
`σ x` is substituted.

Paper: Lemma [lem:frege-substitution], depth. -/
theorem depthFrom_subst_le {σ : V → Formula V'} {s : ℕ} (hσ : ∀ x, (σ x).depth ≤ s)
    (F : Formula V) (p : Option Bool) : depthFrom p (F.subst σ) ≤ depthFrom p F + s + 1 := by
  induction F generalizing p with
  | var v =>
    have h₁ := depthFrom_le_depth_add_one p (σ v)
    have h₂ := hσ v
    simp only [subst_var, depthFrom]
    omega
  | bot => simp [depthFrom]
  | neg F ih =>
    have := ih (some false)
    simp only [subst_neg, depthFrom]
    omega
  | or F G ihF ihG =>
    have h₁ := ihF (some true)
    have h₂ := ihG (some true)
    simp only [subst_or, depthFrom]
    omega

theorem depth_subst_le {σ : V → Formula V'} {s : ℕ} (hσ : ∀ x, (σ x).depth ≤ s) (F : Formula V) :
    (F.subst σ).depth ≤ F.depth + s + 1 :=
  depthFrom_subst_le hσ F none

/-- `|F^σ| ≤ |σ| |F|`.

Paper: Lemma [lem:frege-substitution], size. -/
theorem size_subst_le {σ : V → Formula V'} {k : ℕ} (hk : 1 ≤ k) (hσ : ∀ x, (σ x).size ≤ k)
    (F : Formula V) : (F.subst σ).size ≤ k * F.size := by
  induction F with
  | var v => simpa using hσ v
  | bot => simpa using hk
  | neg F ih =>
    simp only [subst_neg, size_neg, Nat.mul_add, Nat.mul_one]
    omega
  | or F G ihF ihG =>
    simp only [subst_or, size_or, Nat.mul_add, Nat.mul_one]
    omega

/-- Substitutions agreeing on the variables of `F` give the same `F^σ`. -/
theorem subst_congr [DecidableEq V] {σ τ : V → Formula V'} {F : Formula V}
    (h : ∀ v ∈ F.vars, σ v = τ v) : F.subst σ = F.subst τ := by
  induction F with
  | var v => exact h v (by simp)
  | bot => rfl
  | neg F ih =>
    simp only [subst_neg]
    rw [ih (by simpa using h)]
  | or F G ihF ihG =>
    simp only [subst_or]
    rw [ihF fun v hv => h v (by simp [hv]), ihG fun v hv => h v (by simp [hv])]

/-- Implication is preserved by substitution. -/
theorem Implies.subst {Γ : Set (Formula V)} {G : Formula V} (h : Implies Γ G)
    (σ : V → Formula V') : Implies (subst σ '' Γ) (G.subst σ) := by
  intro α hα
  rw [eval_subst]
  refine h _ fun F hF => ?_
  rw [← eval_subst]
  exact hα _ (Set.mem_image_of_mem _ hF)

/-- The variables of `F^σ` are the variables of the images of the variables of `F`. -/
theorem vars_subst_subset [DecidableEq V] [DecidableEq V'] (σ : V → Formula V') (F : Formula V) :
    (F.subst σ).vars ⊆ F.vars.biUnion fun v => (σ v).vars := by
  induction F with
  | var v => simp
  | bot => simp
  | neg F ih => simpa using ih
  | or F G ihF ihG =>
    simp only [subst_or, vars_or]
    exact Finset.union_subset
      (ihF.trans (Finset.biUnion_subset_biUnion_of_subset_left _ Finset.subset_union_left))
      (ihG.trans (Finset.biUnion_subset_biUnion_of_subset_left _ Finset.subset_union_right))

/-! ### Balanced disjunctions -/

/-- The balanced disjunction of a list of formulas: `⊥` for the empty list, the formula itself
for a singleton, and otherwise the disjunction of the balanced disjunctions of the two halves.
-/
def orBalanced : List (Formula V) → Formula V
  | [] => bot
  | [F] => F
  | F :: G :: L =>
      or (orBalanced ((F :: G :: L).take ((L.length + 2) / 2)))
        (orBalanced ((F :: G :: L).drop ((L.length + 2) / 2)))
termination_by L => L.length
decreasing_by
  all_goals simp_wf
  all_goals omega

@[simp] theorem orBalanced_nil : orBalanced ([] : List (Formula V)) = bot := by
  simp [orBalanced]

@[simp] theorem orBalanced_singleton (F : Formula V) : orBalanced [F] = F := by
  simp [orBalanced]

/-- A balanced disjunction is true when one of its disjuncts is. -/
theorem eval_orBalanced (α : V → Bool) (L : List (Formula V)) :
    (orBalanced L).eval α = L.any fun F => F.eval α := by
  induction L using orBalanced.induct with
  | case1 => simp
  | case2 F => simp
  | case3 F G L ih₁ ih₂ =>
    rw [orBalanced.eq_3, eval_or, ih₁, ih₂, ← List.any_append, List.take_append_drop]

/-- Seen from a disjunction, a balanced disjunction is no deeper than its disjuncts seen from a
disjunction: nesting disjunctions adds no alternation. -/
theorem depthFrom_orBalanced_le {d : ℕ} {L : List (Formula V)}
    (h : ∀ F ∈ L, depthFrom (some true) F ≤ d) : depthFrom (some true) (orBalanced L) ≤ d := by
  induction L using orBalanced.induct with
  | case1 => simp [depthFrom]
  | case2 F => simpa using h F (List.mem_singleton_self F)
  | case3 F G L ih₁ ih₂ =>
    have h₁ := ih₁ fun F hF => h F (List.mem_of_mem_take hF)
    have h₂ := ih₂ fun F hF => h F (List.mem_of_mem_drop hF)
    rw [orBalanced.eq_3]
    simp only [depthFrom, Option.some.injEq, Bool.true_eq_false, if_false, zero_add]
    omega

/-- The depth of a balanced disjunction is bounded by the depths of its disjuncts seen from a
disjunction. -/
theorem depth_orBalanced_le {d : ℕ} {L : List (Formula V)}
    (h : ∀ F ∈ L, depthFrom (some true) F ≤ d) : (orBalanced L).depth ≤ d :=
  (depth_le_depthFrom _ _).trans (depthFrom_orBalanced_le h)

/-- A nonempty balanced disjunction has exactly one internal node fewer than disjuncts. -/
theorem size_orBalanced_add_one_le {L : List (Formula V)} (h : L ≠ []) :
    (orBalanced L).size + 1 ≤ (L.map size).sum + L.length := by
  induction L using orBalanced.induct with
  | case1 => exact absurd rfl h
  | case2 F => simp
  | case3 F G L ih₁ ih₂ =>
    have ht : (F :: G :: L).take ((L.length + 2) / 2) ≠ [] := by
      intro hc
      have := congrArg List.length hc
      simp only [List.length_take, List.length_cons, List.length_nil] at this
      omega
    have hd : (F :: G :: L).drop ((L.length + 2) / 2) ≠ [] := by
      intro hc
      have := congrArg List.length hc
      simp only [List.length_drop, List.length_cons, List.length_nil] at this
      omega
    have h₁ := ih₁ ht
    have h₂ := ih₂ hd
    have hsum : (((F :: G :: L).take ((L.length + 2) / 2)).map size).sum +
        (((F :: G :: L).drop ((L.length + 2) / 2)).map size).sum =
          ((F :: G :: L).map size).sum := by
      rw [← List.sum_append, ← List.map_append, List.take_append_drop]
    rw [orBalanced.eq_3, size_or]
    simp only [List.length_take, List.length_drop, List.length_cons] at h₁ h₂ ⊢
    omega

/-- A balanced disjunction has one internal node fewer than disjuncts (and `⊥` alone when there
are none). -/
theorem size_orBalanced_le (L : List (Formula V)) :
    (orBalanced L).size ≤ (L.map size).sum + L.length + 1 := by
  rcases L with _ | ⟨F, L⟩
  · simp
  · have := size_orBalanced_add_one_le (List.cons_ne_nil F L)
    omega

theorem size_le_size_orBalanced {L : List (Formula V)} {F : Formula V} (h : F ∈ L) :
    F.size ≤ (orBalanced L).size := by
  induction L using orBalanced.induct with
  | case1 => simp at h
  | case2 G =>
    rw [List.mem_singleton] at h
    subst h
    simp
  | case3 F₁ F₂ L ih₁ ih₂ =>
    rw [orBalanced.eq_3, size_or]
    rw [← List.take_append_drop ((L.length + 2) / 2) (F₁ :: F₂ :: L), List.mem_append] at h
    rcases h with h | h
    · exact (ih₁ h).trans (by omega)
    · exact (ih₂ h).trans (by omega)

/-- A balanced disjunction has at least as many symbols as disjuncts. -/
theorem length_le_size_orBalanced (L : List (Formula V)) : L.length ≤ (orBalanced L).size := by
  induction L using orBalanced.induct with
  | case1 => simp
  | case2 F =>
    have := F.size_pos
    simp only [List.length_singleton, orBalanced_singleton]
    omega
  | case3 F G L ih₁ ih₂ =>
    rw [orBalanced.eq_3, size_or]
    simp only [List.length_take, List.length_drop, List.length_cons] at ih₁ ih₂ ⊢
    omega

/-- A balanced disjunction of formulas of size at most `b` has size at most `(b + 1) |L| + 1`. -/
theorem size_orBalanced_le_of_forall_size_le {b : ℕ} {L : List (Formula V)}
    (hb : ∀ F ∈ L, F.size ≤ b) : (orBalanced L).size ≤ (b + 1) * L.length + 1 := by
  refine (size_orBalanced_le L).trans ?_
  have h := List.sum_le_card_nsmul (L.map size) b fun x hx => by
    obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hx
    exact hb F hF
  rw [List.length_map, smul_eq_mul] at h
  nlinarith

theorem mem_foldr_union [DecidableEq V] {v : V} (L : List (Formula V)) :
    v ∈ L.foldr (fun F s => F.vars ∪ s) ∅ ↔ ∃ F ∈ L, v ∈ F.vars := by
  induction L with
  | nil => simp
  | cons F L ih => simp [ih]

theorem foldr_union_append [DecidableEq V] (L₁ L₂ : List (Formula V)) :
    (L₁ ++ L₂).foldr (fun F s => F.vars ∪ s) ∅ =
      L₁.foldr (fun F s => F.vars ∪ s) ∅ ∪ L₂.foldr (fun F s => F.vars ∪ s) ∅ := by
  induction L₁ with
  | nil => simp
  | cons F L₁ ih => simp [ih, Finset.union_assoc]

theorem vars_orBalanced [DecidableEq V] (L : List (Formula V)) :
    (orBalanced L).vars = L.foldr (fun F s => F.vars ∪ s) ∅ := by
  induction L using orBalanced.induct with
  | case1 => simp
  | case2 F => simp
  | case3 F G L ih₁ ih₂ =>
    rw [orBalanced.eq_3, vars_or, ih₁, ih₂, ← foldr_union_append, List.take_append_drop]

/-- A variable occurs in a balanced disjunction exactly when it occurs in one of the
disjuncts. -/
theorem mem_vars_orBalanced [DecidableEq V] {v : V} {L : List (Formula V)} :
    v ∈ (orBalanced L).vars ↔ ∃ F ∈ L, v ∈ F.vars := by
  rw [vars_orBalanced, mem_foldr_union]

/-- Substitution commutes with balanced disjunction. -/
theorem subst_orBalanced (σ : V → Formula V') (L : List (Formula V)) :
    (orBalanced L).subst σ = orBalanced (L.map (subst σ)) := by
  induction L using orBalanced.induct with
  | case1 => simp
  | case2 F => simp
  | case3 F G L ih₁ ih₂ =>
    rw [orBalanced.eq_3, subst_or, ih₁, ih₂, List.map_cons, List.map_cons, orBalanced.eq_3,
      List.length_map, ← List.map_cons, ← List.map_cons, List.map_take, List.map_drop]

end Formula

/-! ### Literals and clauses as formulas -/

namespace Literal

variable {V : Type*}

/-- A literal as a formula: `v` or `¬v`.

Paper: Section 9.1, "Formulas and depth" (a literal has depth `0`). -/
def toFormula : Literal V → Formula V
  | ⟨v, true⟩ => .var v
  | ⟨v, false⟩ => .neg (.var v)

@[simp] theorem toFormula_pos (v : V) : (pos v).toFormula = .var v := rfl

@[simp] theorem toFormula_neg (v : V) : (neg v).toFormula = .neg (.var v) := rfl

theorem eval_toFormula (α : V → Bool) (l : Literal V) : l.toFormula.eval α = decide (l.Sat α) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  rcases l with ⟨v, _ | _⟩ <;> simp [toFormula, Literal.Sat]

theorem depth_toFormula (l : Literal V) : l.toFormula.depth = 0 := by
  rcases l with ⟨v, _ | _⟩ <;> rfl

theorem depthFrom_toFormula_le (l : Literal V) : Formula.depthFrom (some true) l.toFormula ≤ 1 := by
  rcases l with ⟨v, _ | _⟩ <;> simp [toFormula, Formula.depthFrom]

theorem size_toFormula_le (l : Literal V) : l.toFormula.size ≤ 2 := by
  rcases l with ⟨v, _ | _⟩ <;> simp [toFormula, Formula.size]

@[simp] theorem vars_toFormula [DecidableEq V] (l : Literal V) : l.toFormula.vars = {l.var} := by
  rcases l with ⟨v, _ | _⟩ <;> rfl

end Literal

namespace Clause

variable {V : Type*}

/-- A clause as a formula: the balanced disjunction of its literals, in the order of
`Finset.toList`.

Paper: Section 9.1, "Formulas and depth" (a clause has depth at most `1`). -/
noncomputable def toFormula (C : Clause V) : Formula V :=
  Formula.orBalanced (C.toList.map Literal.toFormula)

theorem eval_toFormula (α : V → Bool) (C : Clause V) : C.toFormula.eval α = decide (C.Sat α) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, toFormula, Formula.eval_orBalanced, List.any_eq_true]
  simp [Literal.eval_toFormula, Clause.Sat]

theorem eval_toFormula_eq_true_iff (α : V → Bool) (C : Clause V) :
    C.toFormula.eval α = true ↔ C.Sat α := by
  rw [eval_toFormula, decide_eq_true_eq]

theorem depth_toFormula_le (C : Clause V) : C.toFormula.depth ≤ 1 := by
  unfold toFormula
  exact Formula.depth_orBalanced_le fun F hF => by
    obtain ⟨l, -, rfl⟩ := List.mem_map.mp hF
    exact Literal.depthFrom_toFormula_le l

/-- The formula of a clause has at most `3 |C| + 1` symbols. -/
theorem size_toFormula_le (C : Clause V) : C.toFormula.size ≤ 3 * C.card + 1 := by
  unfold toFormula
  refine (Formula.size_orBalanced_le _).trans ?_
  have h := List.sum_le_card_nsmul ((C.toList.map Literal.toFormula).map Formula.size) 2 (by
    intro x hx
    obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hx
    obtain ⟨l, -, rfl⟩ := List.mem_map.mp hF
    exact Literal.size_toFormula_le l)
  simp only [List.length_map, Finset.length_toList, smul_eq_mul] at h ⊢
  omega

theorem vars_toFormula [DecidableEq V] (C : Clause V) : C.toFormula.vars = C.vars := by
  ext v
  rw [toFormula, Formula.mem_vars_orBalanced, Clause.mem_vars]
  simp only [List.mem_map, Finset.mem_toList, Literal.vars_toFormula, Finset.mem_singleton,
    exists_exists_and_eq_and]
  exact ⟨fun ⟨l, hl, h⟩ => ⟨l, hl, h.symm⟩, fun ⟨l, hl, h⟩ => ⟨l, hl, h.symm⟩⟩

@[simp] theorem toFormula_empty : (∅ : Clause V).toFormula = Formula.bot := by
  simp [toFormula]

end Clause

namespace CNF

variable {V : Type*}

/-- The formulas of a CNF: the formulas of its clauses.

Paper: Section 9.1, "Frege systems" (a refutation of a set of clauses). -/
noncomputable def toFormulas (Φ : CNF V) : Set (Formula V) :=
  Clause.toFormula '' (↑Φ : Set (Clause V))

theorem mem_toFormulas {Φ : CNF V} {F : Formula V} :
    F ∈ Φ.toFormulas ↔ ∃ C ∈ Φ, C.toFormula = F := by
  simp [toFormulas]

theorem toFormula_mem_toFormulas {Φ : CNF V} {C : Clause V} (h : C ∈ Φ) :
    C.toFormula ∈ Φ.toFormulas :=
  mem_toFormulas.mpr ⟨C, h, rfl⟩

theorem toFormulas_mono {Φ Φ' : CNF V} (h : Φ ⊆ Φ') : Φ.toFormulas ⊆ Φ'.toFormulas :=
  Set.image_mono h

/-- An assignment satisfies a CNF exactly when it satisfies its formulas. -/
theorem sat_iff_forall_eval (α : V → Bool) (Φ : CNF V) :
    Φ.Sat α ↔ ∀ F ∈ Φ.toFormulas, F.eval α = true := by
  constructor
  · intro h F hF
    obtain ⟨C, hC, rfl⟩ := mem_toFormulas.mp hF
    exact (Clause.eval_toFormula_eq_true_iff α C).mpr (h C hC)
  · intro h C hC
    exact (Clause.eval_toFormula_eq_true_iff α C).mp (h _ (toFormula_mem_toFormulas hC))

/-- A formula is implied by the formulas of a CNF exactly when it is implied by the CNF. -/
theorem implies_toFormulas_iff (Φ : CNF V) (G : Formula V) :
    Formula.Implies Φ.toFormulas G ↔ ∀ α, Φ.Sat α → G.eval α = true := by
  constructor
  · intro h α hα
    exact h α ((sat_iff_forall_eval α Φ).mp hα)
  · intro h α hα
    exact h α ((sat_iff_forall_eval α Φ).mpr hα)

end CNF

/-! ### Canonical DNFs -/

namespace Formula

variable {V : Type*}

/-- The term of the assignment `τ` to the variables `X`: the conjunction over `v ∈ X` of `v` if
`τ v` and of `¬v` otherwise, written as `¬ ⋁_{v ∈ X} (¬v or v)`. -/
noncomputable def term (X : Finset V) (τ : {v // v ∈ X} → Bool) : Formula V :=
  neg (orBalanced (X.attach.toList.map fun v => if τ v then neg (var v.1) else var v.1))

/-- The term of `τ` is true under `α` exactly when `α` agrees with `τ` on `X`. -/
theorem eval_term (X : Finset V) (τ : {v // v ∈ X} → Bool) (α : V → Bool) :
    (term X τ).eval α = decide (∀ v : {v // v ∈ X}, α v.1 = τ v) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, term, eval_neg, Bool.not_eq_true', eval_orBalanced,
    List.any_eq_false]
  simp only [List.forall_mem_map, Finset.mem_toList, Finset.mem_attach, true_implies]
  refine forall_congr' fun v => ?_
  split_ifs with h <;> simp [h]

/-- Seen from a disjunction, a term has depth at most `3`. -/
theorem depthFrom_term_le (X : Finset V) (τ : {v // v ∈ X} → Bool) :
    depthFrom (some true) (term X τ) ≤ 3 := by
  have h₁ : (orBalanced (X.attach.toList.map fun v =>
      if τ v then neg (var v.1) else var v.1)).depth ≤ 1 :=
    depth_orBalanced_le fun F hF => by
      obtain ⟨v, -, rfl⟩ := List.mem_map.mp hF
      split_ifs <;> simp [depthFrom]
  have h₂ := depthFrom_le_depth_add_one (some false)
    (orBalanced (X.attach.toList.map fun v => if τ v then neg (var v.1) else var v.1))
  rw [term]
  simp only [depthFrom, if_true]
  omega

/-- A term over `X` has size at most `3 |X| + 2`. -/
theorem size_term_le (X : Finset V) (τ : {v // v ∈ X} → Bool) :
    (term X τ).size ≤ 3 * X.card + 2 := by
  rw [term, size_neg]
  have h := size_orBalanced_le (X.attach.toList.map fun v =>
    if τ v then neg (var v.1) else var v.1)
  have hsum := List.sum_le_card_nsmul ((X.attach.toList.map fun v =>
    if τ v then neg (var v.1) else var v.1).map size) 2 (by
      intro x hx
      obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hx
      obtain ⟨v, -, rfl⟩ := List.mem_map.mp hF
      split_ifs <;> simp)
  simp only [List.length_map, Finset.length_toList, Finset.card_attach, smul_eq_mul] at h hsum
  omega

variable [DecidableEq V]

/-- The canonical DNF of a Boolean function `f` of the variables `X`: the disjunction of the
terms of the satisfying assignments of `f`.

Paper: proof of Lemma [lem:frege-transfer], "DNF substitution". -/
noncomputable def dnf (X : Finset V) (f : ({v // v ∈ X} → Bool) → Bool) : Formula V :=
  orBalanced ((Finset.univ.filter fun τ => f τ = true).toList.map (term X))

/-- The canonical DNF of `f` computes `f`. -/
theorem eval_dnf (X : Finset V) (f : ({v // v ∈ X} → Bool) → Bool) (α : V → Bool) :
    (dnf X f).eval α = f fun v => α v.1 := by
  rw [Bool.eq_iff_iff, dnf, eval_orBalanced, List.any_eq_true]
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and,
    exists_exists_and_eq_and, eval_term, decide_eq_true_eq]
  constructor
  · rintro ⟨τ, hτ, h⟩
    have : (fun v : {v // v ∈ X} => α v.1) = τ := funext h
    rwa [this]
  · intro h
    exact ⟨_, h, fun v => rfl⟩

/-- The canonical DNF has depth at most `3`. -/
theorem depth_dnf_le (X : Finset V) (f : ({v // v ∈ X} → Bool) → Bool) : (dnf X f).depth ≤ 3 := by
  unfold dnf
  exact depth_orBalanced_le fun F hF => by
    obtain ⟨τ, -, rfl⟩ := List.mem_map.mp hF
    exact depthFrom_term_le X τ

/-- The canonical DNF of a function of `|X|` variables has size at most
`2^{|X|} (3 |X| + 3) + 1`. -/
theorem size_dnf_le (X : Finset V) (f : ({v // v ∈ X} → Bool) → Bool) :
    (dnf X f).size ≤ 2 ^ X.card * (3 * X.card + 3) + 1 := by
  unfold dnf
  set L := (Finset.univ.filter fun τ => f τ = true).toList.map (term X) with hL
  have hlen : L.length ≤ 2 ^ X.card := by
    rw [hL, List.length_map, Finset.length_toList]
    refine (Finset.card_filter_le _ _).trans ?_
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
  have hsum : (L.map size).sum ≤ L.length * (3 * X.card + 2) := by
    have := List.sum_le_card_nsmul (L.map size) (3 * X.card + 2) (by
      intro x hx
      obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hx
      rw [hL] at hF
      obtain ⟨τ, -, rfl⟩ := List.mem_map.mp hF
      exact size_term_le X τ)
    rwa [List.length_map, smul_eq_mul] at this
  refine (size_orBalanced_le L).trans ?_
  have := Nat.mul_le_mul_right (3 * X.card + 3) hlen
  nlinarith

/-- The variables of the canonical DNF lie in `X`. -/
theorem vars_dnf_subset (X : Finset V) (f : ({v // v ∈ X} → Bool) → Bool) : (dnf X f).vars ⊆ X := by
  intro v hv
  rw [dnf, mem_vars_orBalanced] at hv
  obtain ⟨F, hF, hv⟩ := hv
  obtain ⟨τ, -, rfl⟩ := List.mem_map.mp hF
  rw [term, vars_neg, mem_vars_orBalanced] at hv
  obtain ⟨G, hG, hv⟩ := hv
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp hG
  have : v = w.1 := by
    split_ifs at hv <;> simpa using hv
  exact this ▸ w.2

end Formula

end AssocLB
