/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/
import AssocLB.Resolution.Substitution

/-!
# Overview of the reduction

Paper: Section 6 (Overview of the reduction), Section 6.1 (Reduction of star-local perfect
matching to `Assoc_n`): the three steps Restrict, Substitute and Compose that turn a refutation
of `Assoc_n` into a refutation of `SPM(H)` with a constant-factor increase in size.

## Main results

* `Refutation.compose`: the Compose step. If `Ψ` has a refutation `π` and every initial clause
  of `π` has a subclause with a derivation from `Φ` of size at most `K`, then `Φ` has a
  refutation of size at most `(K + 1) |π|`.
* `Refutation.reduce`: the reduction, abstractly. A refutation of `Φ` of size `s`, a
  restriction `ρ` (Restrict) and a substitution `σ` into the variables of `Ψ` (Substitute) such
  that every clause of `(Φ↾ρ)^σ` has a subclause derivable from `Ψ` in at most `K` steps yield
  a refutation of `Ψ` of size at most `(K + 1) s`.

## Design notes

* Section 6 of the paper contains no definitions of its own: the restriction `ρ` and the
  substitution `σ` are constructed in Sections 7 and 8, where `Refutation.reduce` is
  instantiated with `Φ = Assoc_n`, `Ψ = SPM(H)` and the constant `K` of Lemma
  [lem:star-local-derivations] (Lemma [lem:reduction]).
* The composed refutation only derives the initial clauses that the given refutation uses,
  which gives the constant-factor bound `(K + 1) s` of the paper rather than a bound involving
  the number of clauses of `Φ`.
* The clauses of `(Φ↾ρ)^σ` are never tautologies (`CNF.not_isTautology_of_mem_subst`), since
  tautological images are discarded, so Lemma [lem:star-local-derivations] applies to each of
  them.
-/

namespace AssocLB

variable {V V' : Type*} [DecidableEq V]

/-- **The Compose step.** If `Ψ` has a refutation `π` and every initial clause of `π` has a
subclause with a derivation from `Φ` of size at most `K`, then `Φ` has a refutation of size at
most `(K + 1) |π|`: derive the subclauses first, then run `π` on them.

Paper: Section 6.1, Compose. -/
theorem Refutation.compose {Ψ Φ : CNF V} (π : Refutation Ψ) {K : ℕ}
    (h : ∀ C ∈ π.lines, C ∈ Ψ → ∃ D ⊆ C, ∃ δ : Derivation Φ D, δ.size ≤ K) :
    ∃ π' : Refutation Φ, π'.size ≤ (K + 1) * π.size := by
  classical
  -- derivations of subclauses of the initial clauses that `π` uses
  obtain ⟨π₀, hπ₀, hlen₀, hsub⟩ := exists_isDerivation_concat
    (π.lines.filter fun C => decide (C ∈ Ψ)) fun C hC => by
      rw [List.mem_filter, decide_eq_true_eq] at hC
      exact h C hC.1 hC.2
  -- `π` runs on these subclauses
  obtain ⟨π₁, hπ₁⟩ := π.of_subclauses (Φ := π₀.toFinset) fun C hC hCΨ => by
    obtain ⟨D, hD, hDC⟩ := hsub C (List.mem_filter.mpr ⟨hC, by simpa using hCΨ⟩)
    exact ⟨D, List.mem_toFinset.mpr hD, hDC⟩
  -- its initial-clause steps are already derived
  obtain ⟨π₂, hπ₂, hlen₂, hmem⟩ := (π₁.isDerivation.mono_acc
    (Finset.empty_subset _)).exists_of_initial_mem_acc (Φ := Φ) fun _ _ hC => hC
  have hfull : IsDerivation Φ ∅ (π₀ ++ π₂) :=
    hπ₀.append (by rwa [Finset.empty_union])
  have hbot : (∅ : Clause V) ∈ π₀ ++ π₂ := by
    rcases hmem ∅ π₁.mem_lines with h0 | h0
    · exact List.mem_append_left _ (List.mem_toFinset.mp h0)
    · exact List.mem_append_right _ h0
  obtain ⟨π', hπ'⟩ := Derivation.exists_of_mem hfull hbot
  refine ⟨π', hπ'.trans ?_⟩
  have hF : (π.lines.filter fun C => decide (C ∈ Ψ)).length ≤ π.size :=
    List.length_filter_le _ _
  have hKF : K * (π.lines.filter fun C => decide (C ∈ Ψ)).length ≤ K * π.size :=
    Nat.mul_le_mul_left K hF
  have hlen₁ : π₂.length ≤ π.size := hlen₂.trans hπ₁
  rw [List.length_append, Nat.succ_mul]
  omega

/-- **The reduction, abstractly.** A refutation `π` of `Φ` of size `s`, a restriction `ρ`
(Restrict) and a substitution `σ` into the variables of `Ψ` (Substitute) such that every
clause of `(Φ↾ρ)^σ` has a subclause derivable from `Ψ` in at most `K` steps (Compose) yield a
refutation of `Ψ` of size at most `(K + 1) s`.

Paper: Section 6.1; instantiated in Lemma [lem:reduction]. -/
theorem Refutation.reduce [DecidableEq V'] {Φ : CNF V} (π : Refutation Φ) (ρ : Restriction V)
    (σ : Subst V V') {Ψ : CNF V'} {K : ℕ}
    (h : ∀ C ∈ (Φ.restrict ρ).subst σ, ∃ D ⊆ C, ∃ δ : Derivation Ψ D, δ.size ≤ K) :
    ∃ π' : Refutation Ψ, π'.size ≤ (K + 1) * π.size := by
  obtain ⟨π₁, hπ₁⟩ := π.restrict ρ
  obtain ⟨π₂, hπ₂⟩ := π₁.subst σ
  obtain ⟨π₃, hπ₃⟩ := π₂.compose fun C _ hC => h C hC
  exact ⟨π₃, hπ₃.trans (Nat.mul_le_mul_left _ (hπ₂.trans hπ₁))⟩

end AssocLB
