/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/
import Mathlib

/-!
# Bipartite graphs, matchings and boundary expansion

Paper: Section 2 (Preliminaries), paragraph "Bipartite graphs and matchings"; Section 5,
Definition [def:boundary-expander] (boundary expander) and Theorem [thm:iss-graphs] (the
expanders of Itsykson et al.).

## Main definitions

* `Bipartite U V E`: a bipartite graph `G = (U, V, E)`, each edge `e` having a left endpoint
  `u_e` and a right endpoint `v_e`. Vertices are the elements of `U ⊕ V`.
* `Bipartite.star G w`: the star `E(w)`, the edges at `w`; `Bipartite.degree`;
  `Bipartite.MaxDegreeLE G Δ`.
* `Bipartite.IsMatching G M`, `Bipartite.Covers G M A`: matchings, and matchings covering a
  vertex set. `Bipartite.IsSimple G`: no two edges have the same endpoints.
* `Bipartite.neighbors G S`: the neighbors `N(S) ⊆ V` of `S ⊆ U`; `Bipartite.boundary G S`: the
  boundary `δ(S)`, the vertices of `V` with exactly one edge from `S`;
  `Bipartite.IsBoundaryExpander G r Γ`: Definition [def:boundary-expander].
* `ExpanderGraph Δ Γ ε m`: a graph as in Theorem [thm:iss-graphs] for the parameter `m`, and
  `ISSGraphs`, the theorem itself as a proposition, proved in `AssocLB.Matching.ISSGraphs`
  (`issGraphs`).

## Main results

* `Bipartite.IsBoundaryExpander.card_le_card_neighbors`: boundary expansion with `Γ ≥ 1` gives
  Hall's condition for the sets of size at most `r`.
* `Bipartite.exists_matching_covers`: when `|U| = |V| + 1` and a matching covers `V`, every
  `S ⊆ U` satisfying Hall's condition is covered together with `V` by a single matching. This
  is the case of Lemma 3.1 of Itsykson et al. used in the proof of Theorem
  [thm:star-local-hard]; it is proved by Hall's theorem for `V` with one added dummy vertex
  adjacent to `U ∖ S`.

## Design notes

* Edges form a type `E` with endpoint maps, so parallel edges are not excluded in general;
  `ExpanderGraph` requires simplicity, as the paper's graphs are simple and the index maps of
  Lemma [lem:indices] need it. The boundary counts edges from `S` rather than neighbors, which
  agrees with the paper's definition for simple graphs.
* The expansion constant `Γ` and the threshold `r` are real numbers, since Theorem
  [thm:iss-graphs] provides a real `Γ > 2` and the threshold `εm`.
* Theorem [thm:iss-graphs] is a probabilistic existence result, proved by counting in
  `AssocLB.Matching.ISSGraphs` (`issGraphs`). The main theorem takes `ISSGraphs` as an explicit
  hypothesis, which `issGraphs` discharges. Hall's theorem is taken from Mathlib
  (`Finset.all_card_le_biUnion_card_iff_exists_injective`) when needed.
-/

namespace AssocLB

/-- A bipartite graph `G = (U, V, E)`: every edge `e` has a left endpoint `u_e ∈ U` and a right
endpoint `v_e ∈ V`.

Paper: Section 2, "Bipartite graphs and matchings". -/
structure Bipartite (U V E : Type*) where
  /-- The left endpoint `u_e`. -/
  left : E → U
  /-- The right endpoint `v_e`. -/
  right : E → V

namespace Bipartite

variable {U V E : Type*} (G : Bipartite U V E) [Fintype E] [DecidableEq U] [DecidableEq V]

/-- The endpoints of an edge, as vertices of `U ⊕ V`. -/
def ends (e : E) : Finset (U ⊕ V) := {Sum.inl (G.left e), Sum.inr (G.right e)}

/-- The star `E(w)` of a vertex: the edges incident to it. -/
def star : U ⊕ V → Finset E
  | .inl u => Finset.univ.filter fun e => G.left e = u
  | .inr v => Finset.univ.filter fun e => G.right e = v

@[simp] theorem mem_star_inl {u : U} {e : E} : e ∈ G.star (.inl u) ↔ G.left e = u := by
  simp [star]

@[simp] theorem mem_star_inr {v : V} {e : E} : e ∈ G.star (.inr v) ↔ G.right e = v := by
  simp [star]

/-- The degree `|E(w)|` of a vertex. -/
def degree (w : U ⊕ V) : ℕ := (G.star w).card

/-- The maximum degree is at most `Δ`. -/
def MaxDegreeLE (Δ : ℕ) : Prop := ∀ w, G.degree w ≤ Δ

instance [Fintype U] [Fintype V] (Δ : ℕ) : Decidable (G.MaxDegreeLE Δ) :=
  inferInstanceAs (Decidable (∀ w, G.degree w ≤ Δ))

/-- A matching: a set of pairwise disjoint edges. -/
def IsMatching (M : Finset E) : Prop :=
  ∀ e ∈ M, ∀ f ∈ M, e ≠ f → G.left e ≠ G.left f ∧ G.right e ≠ G.right f

/-- The matching `M` covers the vertex set `A`: every vertex of `A` is an endpoint of an edge
of `M`. -/
def Covers (M : Finset E) (A : Finset (U ⊕ V)) : Prop := ∀ w ∈ A, ∃ e ∈ M, w ∈ G.ends e

/-- `G` is simple: no two edges have the same pair of endpoints. -/
def IsSimple : Prop := ∀ e f, G.left e = G.left f → G.right e = G.right f → e = f

variable {G} in
/-- In a simple graph, the degree of a vertex of `U` is at most `|V|`. -/
theorem IsSimple.degree_inl_le [Fintype V] (h : G.IsSimple) (u : U) :
    G.degree (Sum.inl u) ≤ Fintype.card V := by
  refine (Finset.card_le_card_of_injOn G.right (fun e _ => Finset.mem_univ _) ?_).trans
    Finset.card_univ.le
  intro e he f hf hef
  exact h e f ((G.mem_star_inl.mp he).trans (G.mem_star_inl.mp hf).symm) hef

variable {G} in
/-- In a simple graph, the degree of a vertex of `V` is at most `|U|`. -/
theorem IsSimple.degree_inr_le [Fintype U] (h : G.IsSimple) (v : V) :
    G.degree (Sum.inr v) ≤ Fintype.card U := by
  refine (Finset.card_le_card_of_injOn G.left (fun e _ => Finset.mem_univ _) ?_).trans
    Finset.card_univ.le
  intro e he f hf hef
  exact h e f hef ((G.mem_star_inr.mp he).trans (G.mem_star_inr.mp hf).symm)

variable [Fintype V]

/-- The edges from `S ⊆ U` into the vertex `v`. -/
def edgesTo (S : Finset U) (v : V) : Finset E :=
  Finset.univ.filter fun e => G.left e ∈ S ∧ G.right e = v

/-- The neighbors `N(S) ⊆ V` of a set `S ⊆ U`. -/
def neighbors (S : Finset U) : Finset V := Finset.univ.filter fun v => (G.edgesTo S v).Nonempty

/-- The boundary `δ(S)` of `S ⊆ U`: the vertices of `V` with exactly one edge from `S`.

Paper: Definition [def:boundary-expander]. -/
def boundary (S : Finset U) : Finset V := Finset.univ.filter fun v => (G.edgesTo S v).card = 1

/-- A boundary vertex is a neighbor. -/
theorem boundary_subset_neighbors (S : Finset U) : G.boundary S ⊆ G.neighbors S := by
  intro v hv
  rw [boundary, Finset.mem_filter] at hv
  rw [neighbors, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, Finset.card_pos.mp (by omega)⟩

/-- `G` is an `(r, Γ)`-boundary expander: every `S ⊆ U` with `|S| ≤ r` has `|δ(S)| ≥ Γ |S|`.

Paper: Definition [def:boundary-expander]. -/
def IsBoundaryExpander (r Γ : ℝ) : Prop :=
  ∀ S : Finset U, (S.card : ℝ) ≤ r → Γ * S.card ≤ (G.boundary S).card

variable {G} in
/-- Boundary expansion with `Γ ≥ 1` gives Hall's condition `|N(S)| ≥ |S|` for `|S| ≤ r`. -/
theorem IsBoundaryExpander.card_le_card_neighbors {r Γ : ℝ} (h : G.IsBoundaryExpander r Γ)
    (hΓ : 1 ≤ Γ) {S : Finset U} (hS : (S.card : ℝ) ≤ r) : S.card ≤ (G.neighbors S).card := by
  have h1 : (S.card : ℝ) ≤ Γ * S.card := le_mul_of_one_le_left (Nat.cast_nonneg _) hΓ
  have h2 : ((G.boundary S).card : ℝ) ≤ (G.neighbors S).card := by
    exact_mod_cast Finset.card_le_card (G.boundary_subset_neighbors S)
  exact_mod_cast h1.trans ((h S hS).trans h2)

/-! ### A matching covering a small set and all of `V` -/

/-- The neighbors in `U` of a vertex `v ∈ V`. -/
def leftNeighbors (v : V) : Finset U := (G.star (Sum.inr v)).image G.left

variable [Fintype U]

/-- When `|U| = |V| + 1` and some matching covers `V`, every `S ⊆ U` satisfying Hall's
condition is covered together with `V` by a single matching. This is the case of the
Mendelsohn–Dulmage theorem (Lemma 3.1 of Itsykson et al.) used in Theorem
[thm:star-local-hard].

The proof applies Hall's theorem (`Finset.all_card_le_biUnion_card_iff_exists_injective`) to
`V` together with one dummy vertex adjacent to `U ∖ S`: an injection from `Option V` into `U`
along the edges is a bijection, and the vertices of `S` are then matched to vertices of `V`. -/
theorem exists_matching_covers (hcard : Fintype.card U = Fintype.card V + 1)
    (hV : ∃ M, G.IsMatching M ∧ G.Covers M (Finset.univ.image Sum.inr)) {S : Finset U}
    (hS : ∀ S' ⊆ S, S'.card ≤ (G.neighbors S').card) :
    ∃ M, G.IsMatching M ∧ G.Covers M (S.image Sum.inl ∪ Finset.univ.image Sum.inr) := by
  classical
  obtain ⟨M₀, hM₀, hcov⟩ := hV
  have hpart : ∀ v : V, ∃ e ∈ M₀, G.right e = v := by
    intro v
    obtain ⟨e, he, hv⟩ := hcov (Sum.inr v) (Finset.mem_image_of_mem _ (Finset.mem_univ v))
    refine ⟨e, he, ?_⟩
    simp only [ends, Finset.mem_insert, Finset.mem_singleton, reduceCtorEq, false_or,
      Sum.inr.injEq] at hv
    exact hv.symm
  choose p hpM hpr using hpart
  have hpinj : Function.Injective fun v => G.left (p v) := by
    intro v v' h
    by_contra hne
    have hpne : p v ≠ p v' := fun h' => hne
      (calc v = G.right (p v) := (hpr v).symm
        _ = G.right (p v') := by rw [h']
        _ = v' := hpr v')
    exact (hM₀ _ (hpM v) _ (hpM v') hpne).1 h
  let t : Option V → Finset U := fun o => o.elim Sᶜ G.leftNeighbors
  have hhall : ∀ s : Finset (Option V), s.card ≤ (s.biUnion t).card := by
    intro s
    have hsub : (s.eraseNone.image fun v => G.left (p v)) ⊆ s.biUnion t := by
      intro u hu
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
      refine Finset.mem_biUnion.mpr ⟨some v, Finset.mem_eraseNone.mp hv, ?_⟩
      exact Finset.mem_image.mpr ⟨p v, G.mem_star_inr.mpr (hpr v), rfl⟩
    have hY : s.eraseNone.card ≤ (s.biUnion t).card :=
      (Finset.card_image_of_injective _ hpinj).symm.le.trans (Finset.card_le_card hsub)
    by_cases hn : none ∈ s
    · have hs : s.card = s.eraseNone.card + 1 := by
        rw [Finset.card_eraseNone_of_mem hn]
        have := Finset.card_pos.mpr ⟨_, hn⟩
        omega
      set Y := s.eraseNone with hYdef
      set S' := S.filter fun u => u ∉ Y.biUnion G.leftNeighbors with hS'def
      have h1 : S'ᶜ ⊆ s.biUnion t := by
        intro u hu
        rw [Finset.mem_compl, hS'def, Finset.mem_filter, not_and, not_not] at hu
        by_cases huS : u ∈ S
        · obtain ⟨v, hv, hvu⟩ := Finset.mem_biUnion.mp (hu huS)
          exact Finset.mem_biUnion.mpr ⟨some v, Finset.mem_eraseNone.mp hv, hvu⟩
        · exact Finset.mem_biUnion.mpr ⟨none, hn, Finset.mem_compl.mpr huS⟩
      have h2 : Disjoint (G.neighbors S') Y := by
        rw [Finset.disjoint_left]
        intro v hv hvY
        obtain ⟨e, he⟩ := (Finset.mem_filter.mp hv).2
        obtain ⟨hleft, hright⟩ := (Finset.mem_filter.mp he).2
        refine (Finset.mem_filter.mp hleft).2 ?_
        exact Finset.mem_biUnion.mpr
          ⟨v, hvY, Finset.mem_image.mpr ⟨e, G.mem_star_inr.mpr hright, rfl⟩⟩
      have h3 : S'.card ≤ (G.neighbors S').card := hS S' (Finset.filter_subset _ _)
      have h4 : (G.neighbors S').card + Y.card ≤ Fintype.card V := by
        rw [← Finset.card_union_of_disjoint h2]
        exact Finset.card_le_univ _
      have h5 : S'ᶜ.card + S'.card = Fintype.card U := Finset.card_compl_add_card S'
      have h6 := Finset.card_le_card h1
      omega
    · rw [Finset.card_eraseNone_of_not_mem hn] at hY
      exact hY
  obtain ⟨g, hginj, hg⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hhall
  have hedge : ∀ v : V, ∃ e, G.right e = v ∧ G.left e = g (some v) := by
    intro v
    have hv := hg (some v)
    simp only [t, Option.elim] at hv
    obtain ⟨e, he, hle⟩ := Finset.mem_image.mp hv
    exact ⟨e, G.mem_star_inr.mp he, hle⟩
  choose q hqr hql using hedge
  have hbij : Function.Bijective g :=
    (Fintype.bijective_iff_injective_and_card g).mpr
      ⟨hginj, by rw [Fintype.card_option, hcard]⟩
  refine ⟨Finset.univ.image q, ?_, ?_⟩
  · intro e he f hf hef
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨v', -, rfl⟩ := Finset.mem_image.mp hf
    have hvv : v ≠ v' := fun h => hef (h ▸ rfl)
    refine ⟨?_, ?_⟩
    · rw [hql, hql]
      exact fun h => hvv (Option.some_injective _ (hginj h))
    · rw [hqr, hqr]
      exact hvv
  · intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨o, rfl⟩ := hbij.2 u
      rcases o with _ | v
      · exfalso
        have h0 := hg none
        simp only [t, Option.elim, Finset.mem_compl] at h0
        exact h0 hu
      · exact ⟨q v, Finset.mem_image_of_mem _ (Finset.mem_univ v), by simp [ends, hql v]⟩
    · obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hw
      exact ⟨q v, Finset.mem_image_of_mem _ (Finset.mem_univ v), by simp [ends, hqr v]⟩

end Bipartite

/-- A bipartite expander as in Theorem [thm:iss-graphs] for the parameter `m`: a simple graph
with `|U| = m + 1`, `|V| = m`, maximum degree at most `Δ`, an `(εm, Γ)`-boundary expander,
with a matching covering `V`. -/
structure ExpanderGraph (Δ : ℕ) (Γ ε : ℝ) (m : ℕ) where
  /-- The left vertices. -/
  U : Type
  /-- The right vertices. -/
  V : Type
  /-- The edges. -/
  E : Type
  [fintypeU : Fintype U]
  [fintypeV : Fintype V]
  [fintypeE : Fintype E]
  [decEqU : DecidableEq U]
  [decEqV : DecidableEq V]
  [decEqE : DecidableEq E]
  /-- The graph. -/
  G : Bipartite U V E
  simple : G.IsSimple
  card_U : Fintype.card U = m + 1
  card_V : Fintype.card V = m
  maxDegreeLE : G.MaxDegreeLE Δ
  isBoundaryExpander : G.IsBoundaryExpander (ε * m) Γ
  exists_matching : ∃ M, G.IsMatching M ∧ G.Covers M (Finset.univ.image Sum.inr)

attribute [instance] ExpanderGraph.fintypeU ExpanderGraph.fintypeV ExpanderGraph.fintypeE
  ExpanderGraph.decEqU ExpanderGraph.decEqV ExpanderGraph.decEqE

namespace ExpanderGraph

variable {Δ : ℕ} {Γ ε : ℝ} {m : ℕ} (H : ExpanderGraph Δ Γ ε m)

/-- Every vertex of `V` has an edge, from the matching covering `V`. -/
theorem exists_edge_right (v : H.V) : ∃ e, H.G.right e = v := by
  obtain ⟨M, -, hcov⟩ := H.exists_matching
  obtain ⟨e, -, he⟩ := hcov (Sum.inr v) (Finset.mem_image_of_mem _ (Finset.mem_univ v))
  simp only [Bipartite.ends, Finset.mem_insert, Finset.mem_singleton, reduceCtorEq, false_or,
    Sum.inr.injEq] at he
  exact ⟨e, he.symm⟩

/-- Every vertex of `U` has an edge, from expansion, once `εm ≥ 1`. -/
theorem exists_edge_left (hΓ : 0 < Γ) (hεm : 1 ≤ ε * m) (u : H.U) : ∃ e, H.G.left e = u := by
  have h := H.isBoundaryExpander {u} (by rw [Finset.card_singleton]; exact_mod_cast hεm)
  rw [Finset.card_singleton, Nat.cast_one, mul_one] at h
  have hpos : 0 < (H.G.boundary {u}).card := by
    have : (0 : ℝ) < (H.G.boundary {u}).card := lt_of_lt_of_le hΓ h
    exact_mod_cast this
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
  rw [Bipartite.boundary, Finset.mem_filter] at hv
  obtain ⟨e, he⟩ := Finset.card_pos.mp (by omega : 0 < (H.G.edgesTo {u} v).card)
  rw [Bipartite.edgesTo, Finset.mem_filter, Finset.mem_singleton] at he
  exact ⟨e, he.2.1⟩

end ExpanderGraph

/-- Theorem [thm:iss-graphs] as a proposition: there are absolute constants `Δ`, `Γ > 2` and
`ε > 0` such that for every sufficiently large `m` an expander graph with parameter `m`
exists. It is a probabilistic existence result, proved in `AssocLB.Matching.ISSGraphs`
(`issGraphs`). -/
def ISSGraphs : Prop :=
  ∃ (Δ : ℕ) (Γ ε : ℝ), 2 < Γ ∧ 0 < ε ∧ ∃ m₀, ∀ m ≥ m₀, Nonempty (ExpanderGraph Δ Γ ε m)

end AssocLB
