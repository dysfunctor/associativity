/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/
import AssocLB.Resolution.WidthTransfer
import AssocLB.Matching.ISSWidth

/-!
# The star-local extension remains hard

Paper: Section 5, Theorem [thm:star-local-hard]: for the expanders of Theorem [thm:iss-graphs],
every resolution refutation of `SPM(H)` has width `Ω(m)` and size `2^{Ω(m)}`. As in the paper,
the width lower bound for `PM(H)` of Itsykson et al. (`PM.width_lower_bound`) is carried over
to `SPM(H)` by the width transfer lemma, Lemma [lem:width-transfer] (`width_transfer`):
`SPM(H)` extends `PM(H)` by the variables `Z_{w,f} = f(X_{E(w)})`, each a function of at most
`Δ` edge variables. The size bound then follows from the size–width tradeoff.

## Main results

* `SPM.exists_refutation_PM`: Lemma [lem:width-transfer] for `SPM(G)` over `PM(G)`: a
  refutation of `SPM(G)` of width `w` yields one of `PM(G)` of width at most `2Δw`.
* `SPM.width_lower_bound`: every refutation of `SPM(H)` has width `w` with `Γ (εm) / 2 < 2Δ w`,
  for an expander graph `H` with `Γ ≥ 1` and `εm ≥ 2`.
* `SPM.exists_width_bound`: the same as a bound `Ω(m)`.
* `SPM.exists_size_bound`: assuming the size–width tradeoff `BWTradeoff`, every refutation has
  size `exp(Ω(m))`.
* `SPM.star_local_hard`: Theorem [thm:star-local-hard], with `ISSGraphs` and `BWTradeoff` as
  explicit hypotheses; both are theorems (`issGraphs`, `bwTradeoff`).

## Design notes

* `SPM.defFun` packages the defining functions `Z_{w,f} ↦ f((X_e)_{e ∈ E(w)})` as functions of
  edge assignments, so that `SPM.extend G β = extendBy (defFun G) β`; the support of `Z_{w,f}`
  is the star `E(w)`, of size at most `Δ`.
* The width bounds are stated for `Γ ≥ 1`, which is all the argument uses; Theorem
  [thm:iss-graphs] provides `Γ > 2`.
* The size bound uses Theorem [thm:bw] in the form `BWTradeoff` of
  `AssocLB.Resolution.SizeWidth`, taken as an explicit hypothesis and proved there
  (`bwTradeoff`); `SPM(H)` has width at most `Δ + 1` and at most `(2m + 1)(Δ + 2^{2^Δ})`
  variables.
-/

namespace AssocLB

variable {U V E : Type*} (G : Bipartite U V E) [Fintype U] [Fintype V] [Fintype E]
  [DecidableEq U] [DecidableEq V] [DecidableEq E]

namespace SPM

/-! ### `SPM(G)` as a local extension of `PM(G)` -/

omit [Fintype U] [Fintype V] [DecidableEq E] in
/-- The defining function of the extension variable `Z_{w,f}`, as a function of edge
assignments: `β ↦ f((β e)_{e ∈ E(w)})`. -/
def defFun (z : Σ w : U ⊕ V, StarFun G w) (β : E → Bool) : Bool := z.2 fun e => β e

omit [Fintype U] [Fintype V] [DecidableEq E] in
theorem extend_eq_extendBy (β : E → Bool) : extend G β = extendBy (defFun G) β := by
  funext x
  rcases x with e | ⟨w, f⟩ <;> rfl

omit [Fintype U] [Fintype V] [DecidableEq E] in
/-- `Z_{w,f}` depends only on the edges at `w`. -/
theorem defFun_congr (z : Σ w : U ⊕ V, StarFun G w) {β β' : E → Bool}
    (h : ∀ e ∈ G.star z.1, β e = β' e) : defFun G z β = defFun G z β' := by
  obtain ⟨w, f⟩ := z
  change f (fun e => β e) = f (fun e => β' e)
  congr 1
  funext e
  exact h e e.2

/-- **Lemma [lem:width-transfer] for `SPM(G)`.** `SPM(G)` extends `PM(G)` by the variables
`Z_{w,f} = f(X_{E(w)})`, each a function of the at most `Δ` edge variables at `w`, so a
refutation of `SPM(G)` of width `w` yields a refutation of `PM(G)` of width at most `2Δw`. -/
theorem exists_refutation_PM {Δ : ℕ} (hΔ : G.MaxDegreeLE Δ) (hΔ1 : 1 ≤ Δ)
    (π : Refutation (SPM G)) : ∃ π' : Refutation (PM G), π'.width ≤ 2 * Δ * π.width := by
  refine width_transfer (f := defFun G) (S := fun z => G.star z.1) hΔ1 (fun z => hΔ z.1)
    (fun z β β' h => defFun_congr G z h) ?_ ?_ π
  · intro C hC l hl
    obtain ⟨e, he⟩ := mem_vars_PM G (CNF.mem_vars.mpr ⟨C, hC, l, hl, rfl⟩)
    exact ⟨e, he⟩
  · intro C hC
    obtain ⟨w, -, hC⟩ := Finset.mem_biUnion.mp hC
    rw [vertexClauses, Finset.mem_union] at hC
    rcases hC with hC | hC
    · exact Or.inl (Finset.mem_biUnion.mpr ⟨w, Finset.mem_univ _, hC⟩)
    · obtain ⟨f, -, hC⟩ := Finset.mem_biUnion.mp hC
      refine Or.inr fun β => ?_
      rw [← extend_eq_extendBy]
      exact sat_defClauses_extend G β w f C hC

/-! ### The width lower bound -/

/-- **The star-local extension remains hard (width).** For an expander graph `H` with `Γ ≥ 1`
and `εm ≥ 2`, every resolution refutation of `SPM(H)` has width `w` with `Γ (εm) / 2 < 2Δ w`:
the width bound `Γ (εm) / 2 < w'` of Itsykson et al. for `PM(H)` (`PM.width_lower_bound`),
transferred by Lemma [lem:width-transfer] (`exists_refutation_PM`).

Paper: Theorem [thm:star-local-hard], the width bound; `Γ > 2` there. -/
theorem width_lower_bound {Δ : ℕ} {Γ ε : ℝ} {m : ℕ} (H : ExpanderGraph Δ Γ ε m) (hΓ : 1 ≤ Γ)
    (hr : 2 ≤ ε * m) (π : Refutation (SPM H.G)) : Γ * (ε * m) / 2 < 2 * Δ * π.width := by
  -- `V` is nonempty, so some vertex has an edge and `Δ ≥ 1`
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp only [Nat.cast_zero, mul_zero] at hr
      linarith
    · exact hm
  have hΔ1 : 1 ≤ Δ := by
    obtain ⟨v⟩ : Nonempty H.V := Fintype.card_pos_iff.mp (by rw [H.card_V]; exact hm)
    obtain ⟨e, -⟩ := H.exists_edge_right v
    have h1 : 1 ≤ H.G.degree (Sum.inl (H.G.left e)) :=
      Finset.card_pos.mpr ⟨e, H.G.mem_star_inl.mpr rfl⟩
    exact h1.trans (H.maxDegreeLE _)
  obtain ⟨π', hπ'⟩ := exists_refutation_PM H.G H.maxDegreeLE hΔ1 π
  have h1 := PM.width_lower_bound H hΓ hr π'
  have h2 : (π'.width : ℝ) ≤ 2 * Δ * π.width := by exact_mod_cast hπ'
  linarith

/-- Theorem [thm:star-local-hard], the width bound, in the form `Ω(m)`: for constants `Γ ≥ 1`
and `ε > 0` there are `c > 0` and `m₀` such that for every `m ≥ m₀`, every refutation of
`SPM(H)` for an expander graph `H` with parameter `m` has width at least `c m`.

Paper: Theorem [thm:star-local-hard]. -/
theorem exists_width_bound {Δ : ℕ} {Γ ε : ℝ} (hΓ : 1 ≤ Γ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ H : ExpanderGraph Δ Γ ε m,
      ∀ π : Refutation (SPM H.G), c * m ≤ π.width := by
  refine ⟨Γ * ε / (4 * (Δ + 1)), by positivity, ⌈2 / ε⌉₊, fun m hm H π => ?_⟩
  have hr : 2 ≤ ε * m := by
    have h1 : (⌈2 / ε⌉₊ : ℝ) ≤ m := Nat.cast_le.mpr hm
    have h3 : 2 / ε ≤ m := (Nat.le_ceil _).trans h1
    rw [div_le_iff₀ hε] at h3
    linarith
  have h1 := width_lower_bound H hΓ hr π
  have hw : (0 : ℝ) ≤ π.width := Nat.cast_nonneg _
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith

/-! ### The size lower bound -/

/-- **The star-local extension remains hard (size).** Assuming the size–width tradeoff, for
constants `Γ ≥ 1` and `ε > 0` there are `c > 0` and `m₀` such that for every `m ≥ m₀`, every
refutation of `SPM(H)` for an expander graph `H` with parameter `m` has size at least
`exp(c m)`, stated as `c m ≤ log |π|`.

Paper: Theorem [thm:star-local-hard], the size bound `2^{Ω(m)}`, via Theorem [thm:bw]. -/
theorem exists_size_bound (hBW : BWTradeoff) {Δ : ℕ} {Γ ε : ℝ} (hΓ : 1 ≤ Γ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ H : ExpanderGraph Δ Γ ε m,
      ∀ π : Refutation (SPM H.G), c * m ≤ Real.log π.size := by
  obtain ⟨c₀, hc₀, hBW⟩ := hBW
  obtain ⟨a, ha, m₁, hwidth⟩ := exists_width_bound (Δ := Δ) hΓ hε
  have hK : (1 : ℝ) ≤ ((Δ + 2 ^ 2 ^ Δ : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ Δ + 2 ^ 2 ^ Δ by have := Nat.one_le_two_pow (n := 2 ^ Δ); omega)
  have hKpos : (0 : ℝ) < ((Δ + 2 ^ 2 ^ Δ : ℕ) : ℝ) := by linarith
  have hden : (0 : ℝ) < 12 * c₀ * ((Δ + 2 ^ 2 ^ Δ : ℕ) : ℝ) :=
    mul_pos (mul_pos (by norm_num) hc₀) hKpos
  refine ⟨a ^ 2 / (12 * c₀ * ((Δ + 2 ^ 2 ^ Δ : ℕ) : ℝ)), div_pos (pow_pos ha 2) hden,
    max m₁ (⌈2 * (Δ + 1) / a⌉₊ + 1), fun m hm H π => ?_⟩
  have hm₁ : m₁ ≤ m := le_of_max_le_left hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have ham : 2 * (Δ + 1) ≤ a * m := by
    have h1 : (2 * (Δ + 1) / a : ℝ) ≤ ⌈2 * (Δ + 1) / a⌉₊ := Nat.le_ceil _
    have h2 : ((⌈2 * (Δ + 1) / a⌉₊ : ℕ) : ℝ) ≤ m := by
      exact_mod_cast (show ⌈2 * (Δ + 1) / a⌉₊ ≤ m by omega)
    have h3 := (div_le_iff₀ ha).mp (h1.trans h2)
    linarith
  obtain ⟨π', hπ'⟩ := hBW (SPMVar H.G) (SPM H.G) π
  have hw₁ : a * m ≤ π'.width := hwidth m hm₁ H π'
  have hwΦ : ((SPM H.G).width : ℝ) ≤ Δ + 1 := by
    exact_mod_cast width_SPM_le H.G H.maxDegreeLE
  have hN : (Fintype.card (SPMVar H.G) : ℝ) ≤ 3 * m * ((Δ + 2 ^ 2 ^ Δ : ℕ) : ℝ) := by
    have h1 := card_SPMVar_le H.G H.maxDegreeLE
    rw [H.card_U, H.card_V] at h1
    have h2 : (m + 1 + m) * (Δ + 2 ^ 2 ^ Δ) ≤ 3 * m * (Δ + 2 ^ 2 ^ Δ) :=
      Nat.mul_le_mul_right _ (by omega)
    exact_mod_cast h1.trans h2
  have hs1 : (1 : ℝ) ≤ π.size := by exact_mod_cast π.size_pos
  have hlog : 0 ≤ Real.log π.size := Real.log_nonneg hs1
  have hsq : a * m / 2 ≤ Real.sqrt (c₀ * Fintype.card (SPMVar H.G) * Real.log π.size) := by
    linarith
  rw [Real.le_sqrt (by positivity) (mul_nonneg (mul_nonneg hc₀.le (Nat.cast_nonneg _)) hlog)]
    at hsq
  have h2 : c₀ * Fintype.card (SPMVar H.G) * Real.log π.size ≤
      c₀ * (3 * m * ((Δ + 2 ^ 2 ^ Δ : ℕ) : ℝ)) * Real.log π.size :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN hc₀.le) hlog
  have h3 : a ^ 2 * m * m ≤ (12 * c₀ * ((Δ + 2 ^ 2 ^ Δ : ℕ) : ℝ) * Real.log π.size) * m := by
    calc a ^ 2 * m * m = 4 * (a * m / 2) ^ 2 := by ring
      _ ≤ 4 * (c₀ * Fintype.card (SPMVar H.G) * Real.log π.size) := by linarith
      _ ≤ 4 * (c₀ * (3 * m * ((Δ + 2 ^ 2 ^ Δ : ℕ) : ℝ)) * Real.log π.size) := by linarith
      _ = (12 * c₀ * ((Δ + 2 ^ 2 ^ Δ : ℕ) : ℝ) * Real.log π.size) * m := by ring
  have h4 : a ^ 2 * m ≤ 12 * c₀ * ((Δ + 2 ^ 2 ^ Δ : ℕ) : ℝ) * Real.log π.size :=
    le_of_mul_le_mul_right h3 (by linarith)
  rw [div_mul_eq_mul_div, div_le_iff₀ hden]
  linarith

/-- **Theorem [thm:star-local-hard].** Given Theorem [thm:iss-graphs] (`ISSGraphs`) and the
size–width tradeoff (`BWTradeoff`), both of which are theorems (`issGraphs`, `bwTradeoff`): for
the constants `Δ`, `Γ > 2` and `ε > 0` of Theorem [thm:iss-graphs] there are `c > 0` and `m₀`
such that for every `m ≥ m₀` an expander graph with parameter `m` exists, and every resolution
refutation of `SPM(H)` for such a graph `H` has width at least `c m` and size at least
`exp(c m)`. -/
theorem star_local_hard (hISS : ISSGraphs) (hBW : BWTradeoff) :
    ∃ (Δ : ℕ) (Γ ε : ℝ), 2 < Γ ∧ 0 < ε ∧ ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀,
      Nonempty (ExpanderGraph Δ Γ ε m) ∧ ∀ H : ExpanderGraph Δ Γ ε m,
        ∀ π : Refutation (SPM H.G), c * m ≤ π.width ∧ c * m ≤ Real.log π.size := by
  obtain ⟨Δ, Γ, ε, hΓ, hε, m₀, hex⟩ := hISS
  obtain ⟨c₁, hc₁, m₁, h₁⟩ := exists_width_bound (Δ := Δ) (by linarith : 1 ≤ Γ) hε
  obtain ⟨c₂, hc₂, m₂, h₂⟩ := exists_size_bound hBW (Δ := Δ) (by linarith : 1 ≤ Γ) hε
  refine ⟨Δ, Γ, ε, hΓ, hε, min c₁ c₂, lt_min hc₁ hc₂, max m₀ (max m₁ m₂), fun m hm => ?_⟩
  have hm₀ : m₀ ≤ m := le_of_max_le_left hm
  have hm₁ : m₁ ≤ m := le_of_max_le_left (le_of_max_le_right hm)
  have hm₂ : m₂ ≤ m := le_of_max_le_right (le_of_max_le_right hm)
  refine ⟨hex m hm₀, fun H π => ⟨?_, ?_⟩⟩
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _)).trans
      (h₁ m hm₁ H π)
  · exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg _)).trans
      (h₂ m hm₂ H π)

end SPM

end AssocLB
