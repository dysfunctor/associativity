/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/
import AssocLB.Matching.Expander

/-!
# Existence of the expander graphs

Paper: Theorem [thm:iss-graphs] (Itsykson, Slabodkin and Sokolov): there are absolute
constants `Δ`, `Γ > 2` and `ε > 0` such that for every sufficiently large `m` there is a
bipartite graph with `|U| = m + 1` and `|V| = m`, of maximum degree at most `Δ`, that is an
`(εm, Γ)`-boundary expander and has a matching covering `V`.

## Main definitions

* `ISS.graph σ`: the bipartite graph on `U = Fin (m+1)` and `V = Fin m` determined by seven
  permutations `σ 0, …, σ 6` of `Fin (m+1)`: `u` and `v` are adjacent when some `σ i` maps
  `v` (as an element of `Fin (m+1)`) to `u`. Every vertex has degree at most `7`, and `σ 0`
  gives a matching covering `V`.
* `ISS.Good ε σ`: no set `S ⊆ U` with `1 ≤ |S| ≤ εm` has all its neighbors inside a set of
  `5|S| - 1` vertices of `V`.
* `ISS.Bad ε m`: the tuples that are not good, as a union over `S` and `T`.

## Main results

* `ISS.isBoundaryExpander_of_good`: a good tuple gives an `(εm, 3)`-boundary expander for
  `ε ≤ 1/5`: if `|N(S)| ≥ 5|S|` then, since `S` sends at most `7|S|` edges, at least `3|S|`
  neighbors receive exactly one edge.
* `ISS.card_permBad_le`: the number of permutations mapping every `v ∉ T` outside `S` is at
  most `C(|T|+1, |S|) |S|! (m+1-|S|)!`, by counting the possible preimages `σ⁻¹(S)`.
* `ISS.card_bad_lt`: for `ε = 10⁻⁸` the bad tuples are fewer than all tuples, by a union
  bound; hence `ISS.exists_good` and `issGraphs : ISSGraphs`, with `Δ = 7`, `Γ = 3` and
  `ε = 10⁻⁸`.

## Design notes

* The probabilistic argument of the paper's source is carried out as counting over the
  finite sample space of tuples of permutations. Multiple edges between the same pair of
  vertices are merged: the edge type is the set of adjacent pairs, so the graph is simple and
  the degree bounds hold trivially; a vertex `v` with exactly one index `i` such that
  `σ i v ∈ S` has exactly one neighbor in `S`.
* The constants are not optimized: `C(n, k) ≤ (en/k)^k`, `e ≤ 3`, and the union bound sums
  to at most `1/9`.
-/

namespace AssocLB

namespace ISS

variable {m : ℕ}

/-! ### The random graph -/

/-- A tuple of seven permutations of `Fin (m+1)`. -/
abbrev Tuple (m : ℕ) := Fin 7 → Equiv.Perm (Fin (m + 1))

/-- `u` and `v` are adjacent: some permutation maps `v` to `u`. -/
def Adj (σ : Tuple m) (u : Fin (m + 1)) (v : Fin m) : Prop := ∃ i, σ i (Fin.castSucc v) = u

instance (σ : Tuple m) (u : Fin (m + 1)) (v : Fin m) : Decidable (Adj σ u v) :=
  inferInstanceAs (Decidable (∃ i : Fin 7, σ i (Fin.castSucc v) = u))

/-- The edges: the adjacent pairs. -/
def Edge (σ : Tuple m) : Type := {p : Fin (m + 1) × Fin m // Adj σ p.1 p.2}

instance (σ : Tuple m) : Fintype (Edge σ) := Subtype.fintype _

instance (σ : Tuple m) : DecidableEq (Edge σ) := Subtype.instDecidableEq

/-- The bipartite graph of a tuple. -/
def graph (σ : Tuple m) : Bipartite (Fin (m + 1)) (Fin m) (Edge σ) where
  left p := p.1.1
  right p := p.1.2

theorem graph_simple (σ : Tuple m) : (graph σ).IsSimple := by
  intro e f h1 h2
  exact Subtype.ext (Prod.ext h1 h2)

/-- The index of a permutation witnessing an edge. -/
noncomputable def idx {σ : Tuple m} (e : Edge σ) : Fin 7 := e.2.choose

theorem idx_spec {σ : Tuple m} (e : Edge σ) : σ (idx e) (Fin.castSucc e.1.2) = e.1.1 :=
  e.2.choose_spec

/-- Every vertex has degree at most `7`. -/
theorem maxDegreeLE (σ : Tuple m) : (graph σ).MaxDegreeLE 7 := by
  intro w
  have key : ∀ A : Finset (Edge σ), (∀ e ∈ A, ∀ f ∈ A, idx e = idx f → e = f) → A.card ≤ 7 := by
    intro A hA
    calc A.card ≤ (Finset.univ : Finset (Fin 7)).card :=
          Finset.card_le_card_of_injOn idx (fun _ _ => Finset.mem_univ _)
            fun e he f hf h => hA e he f hf h
      _ = 7 := by simp
  cases w with
  | inl u =>
    refine key _ fun e he f hf h => ?_
    rw [Bipartite.mem_star_inl] at he hf
    change e.1.1 = u at he
    change f.1.1 = u at hf
    have h1 : σ (idx e) (Fin.castSucc e.1.2) = σ (idx e) (Fin.castSucc f.1.2) := by
      rw [idx_spec, h, idx_spec, he, hf]
    have h2 := Fin.castSucc_injective m ((σ (idx e)).injective h1)
    exact Subtype.ext (Prod.ext (he.trans hf.symm) h2)
  | inr v =>
    refine key _ fun e he f hf h => ?_
    rw [Bipartite.mem_star_inr] at he hf
    change e.1.2 = v at he
    change f.1.2 = v at hf
    have h1 : e.1.1 = f.1.1 := by
      rw [← idx_spec e, ← idx_spec f, he, hf, h]
    exact Subtype.ext (Prod.ext h1 (by rw [he, hf]))

/-- The matching given by `σ 0`. -/
def matching (σ : Tuple m) : Finset (Edge σ) :=
  Finset.univ.filter fun e => σ 0 (Fin.castSucc e.1.2) = e.1.1

theorem isMatching (σ : Tuple m) : (graph σ).IsMatching (matching σ) := by
  intro e he f hf hne
  rw [matching, Finset.mem_filter] at he hf
  constructor
  · intro h
    change e.1.1 = f.1.1 at h
    apply hne
    have h2 := Fin.castSucc_injective m ((σ 0).injective (he.2.trans (h.trans hf.2.symm)))
    exact Subtype.ext (Prod.ext h h2)
  · intro h
    change e.1.2 = f.1.2 at h
    apply hne
    have h1 : e.1.1 = f.1.1 := by rw [← he.2, ← hf.2, h]
    exact Subtype.ext (Prod.ext h1 h)

theorem matching_covers (σ : Tuple m) :
    (graph σ).Covers (matching σ) (Finset.univ.image Sum.inr) := by
  intro w hw
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hw
  refine ⟨⟨(σ 0 (Fin.castSucc v), v), 0, rfl⟩, ?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  · simp [Bipartite.ends, graph]

/-! ### Expansion of good tuples -/

/-- A tuple is good for `ε` if no set `S ⊆ U` with `1 ≤ |S| ≤ εm` has all its neighbors in
a set of `5|S| - 1` right vertices. -/
def Good (ε : ℝ) (σ : Tuple m) : Prop :=
  ∀ S : Finset (Fin (m + 1)), 1 ≤ S.card → (S.card : ℝ) ≤ ε * m →
    ∀ T : Finset (Fin m), T.card = 5 * S.card - 1 → ∃ v ∉ T, ∃ i, σ i (Fin.castSucc v) ∈ S

/-- The number of indices `i` with `σ i v ∈ S`. -/
def cnt (σ : Tuple m) (S : Finset (Fin (m + 1))) (v : Fin m) : ℕ :=
  (Finset.univ.filter fun i => σ i (Fin.castSucc v) ∈ S).card

/-- `S` sends at most `7|S|` edges, counted with multiplicity. -/
theorem sum_cnt_le (σ : Tuple m) (S : Finset (Fin (m + 1))) :
    ∑ v, cnt σ S v ≤ 7 * S.card := by
  unfold cnt
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  have : ∀ i : Fin 7, (∑ v : Fin m, if σ i (Fin.castSucc v) ∈ S then 1 else 0) ≤ S.card := by
    intro i
    rw [← Finset.card_filter]
    refine Finset.card_le_card_of_injOn (fun v => σ i (Fin.castSucc v)) ?_ ?_
    · intro v hv
      simpa using hv
    · intro v _ v' _ h
      exact Fin.castSucc_injective m ((σ i).injective h)
  calc (∑ i : Fin 7, ∑ v : Fin m, if σ i (Fin.castSucc v) ∈ S then 1 else 0)
      ≤ ∑ _i : Fin 7, S.card := Finset.sum_le_sum fun i _ => this i
    _ = 7 * S.card := by simp

/-- A vertex with exactly one index `i` such that `σ i v ∈ S` is a boundary vertex. -/
theorem mem_boundary_of_cnt_eq_one (σ : Tuple m) (S : Finset (Fin (m + 1))) {v : Fin m}
    (hv : cnt σ S v = 1) : v ∈ (graph σ).boundary S := by
  obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.mp hv
  have hmem : ∀ i, σ i (Fin.castSucc v) ∈ S ↔ i = i₀ := by
    intro i
    rw [← Finset.mem_singleton, ← hi₀, Finset.mem_filter]
    simp
  rw [Bipartite.boundary, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [Finset.card_eq_one]
  have hadj : Adj σ (σ i₀ (Fin.castSucc v)) v := ⟨i₀, rfl⟩
  refine ⟨⟨(σ i₀ (Fin.castSucc v), v), hadj⟩, Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hmem i₀).mpr rfl, rfl⟩
  · intro e he
    obtain ⟨-, he1, he2⟩ := Finset.mem_filter.mp he
    change e.1.1 ∈ S at he1
    change e.1.2 = v at he2
    obtain ⟨i, hi⟩ := e.2
    rw [he2] at hi
    rw [← hi, hmem] at he1
    subst he1
    exact Subtype.ext (Prod.ext hi.symm he2)

/-- **Good tuples are boundary expanders**: for `ε ≤ 1/5`, a good tuple is an
`(εm, 3)`-boundary expander. -/
theorem isBoundaryExpander_of_good {ε : ℝ} (hε : ε ≤ 1 / 5) {σ : Tuple m} (hσ : Good ε σ) :
    (graph σ).IsBoundaryExpander (ε * m) 3 := by
  intro S hS
  rcases Nat.eq_zero_or_pos S.card with h0 | hpos
  · rw [h0]
    simp
  set s := S.card with hs
  have hsm : 5 * s ≤ m := by
    have h1 : (5 * s : ℝ) ≤ 5 * (ε * m) := by linarith
    have h2 : (5 * (ε * m) : ℝ) ≤ m := by nlinarith [Nat.cast_nonneg (α := ℝ) m]
    exact_mod_cast h1.trans h2
  -- the neighbors
  set N : Finset (Fin m) := Finset.univ.filter fun v => 1 ≤ cnt σ S v with hN
  have hNcard : 5 * s ≤ N.card := by
    by_contra h
    rw [not_le] at h
    obtain ⟨T, hNT, -, hT⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ N)
      (show N.card ≤ 5 * s - 1 by omega) (show 5 * s - 1 ≤ Finset.univ.card by simp; omega)
    obtain ⟨v, hvT, i, hi⟩ := hσ S hpos hS T hT
    apply hvT
    apply hNT
    rw [hN, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [cnt]
    exact Finset.card_pos.mpr ⟨i, by simpa using hi⟩
  -- the boundary
  set B : Finset (Fin m) := Finset.univ.filter fun v => cnt σ S v = 1 with hB
  have hBsub : B ⊆ (graph σ).boundary S := fun v hv =>
    mem_boundary_of_cnt_eq_one σ S ((Finset.mem_filter.mp hv).2)
  have hBN : (Finset.filter (fun v => cnt σ S v = 1) N) = B := by
    ext v
    simp only [hN, hB, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨by omega, h⟩
  have hBN' : B.card ≤ N.card := by
    refine Finset.card_le_card fun v hv => ?_
    rw [hB, Finset.mem_filter] at hv
    rw [hN, Finset.mem_filter]
    exact ⟨hv.1, by omega⟩
  have hmemN : ∀ v ∈ N, 1 ≤ cnt σ S v := fun v hv => (Finset.mem_filter.mp hv).2
  clear_value N B
  have hsum : ∑ v, cnt σ S v ≤ 7 * s := sum_cnt_le σ S
  have hlow : 2 * N.card ≤ ∑ v, cnt σ S v + B.card := by
    have h1 : ∑ v ∈ N, (if cnt σ S v = 1 then 1 else 2) ≤ ∑ v ∈ N, cnt σ S v := by
      refine Finset.sum_le_sum fun v hv => ?_
      have := hmemN v hv
      split_ifs with h
      · omega
      · omega
    have h2 : ∑ v ∈ N, (if cnt σ S v = 1 then 1 else 2) = 2 * N.card - B.card := by
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul, hBN]
      have hcard : (Finset.filter (fun v => ¬ cnt σ S v = 1) N).card = N.card - B.card := by
        have := Finset.card_filter_add_card_filter_not (s := N) (p := fun v => cnt σ S v = 1)
        rw [hBN] at this
        omega
      rw [hcard]
      omega
    have h3 : ∑ v ∈ N, cnt σ S v ≤ ∑ v, cnt σ S v :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => Nat.zero_le _
    omega
  have hfinal : 3 * s ≤ ((graph σ).boundary S).card := by
    have := Finset.card_le_card hBsub
    omega
  exact_mod_cast hfinal

/-! ### Counting the bad tuples -/

/-- The permutations mapping every `v ∉ T` outside `S`. -/
def PermBad (S : Finset (Fin (m + 1))) (T : Finset (Fin m)) : Finset (Equiv.Perm (Fin (m + 1))) :=
  Finset.univ.filter fun τ => ∀ v ∉ T, τ (Fin.castSucc v) ∉ S

/-- The tuples all of whose permutations map every `v ∉ T` outside `S`. -/
def BadAt (S : Finset (Fin (m + 1))) (T : Finset (Fin m)) : Finset (Tuple m) :=
  Finset.univ.filter fun σ => ∀ i, ∀ v ∉ T, σ i (Fin.castSucc v) ∉ S

theorem card_badAt (S : Finset (Fin (m + 1))) (T : Finset (Fin m)) :
    (BadAt S T).card = (PermBad S T).card ^ 7 := by
  have : BadAt S T = Fintype.piFinset fun _ : Fin 7 => PermBad S T := by
    ext σ
    simp [BadAt, PermBad, Fintype.mem_piFinset]
  rw [this, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The permutations with a given preimage `A` of `S` are at most `|S|! (m+1-|S|)!`. -/
theorem card_fiber_le (S A : Finset (Fin (m + 1))) (hA : A.card = S.card) :
    (Finset.univ.filter fun τ : Equiv.Perm (Fin (m + 1)) => S.image τ.symm = A).card ≤
      S.card.factorial * (m + 1 - S.card).factorial := by
  set F := Finset.univ.filter fun τ : Equiv.Perm (Fin (m + 1)) => S.image τ.symm = A with hF
  have hmem : ∀ τ ∈ F, ∀ a, a ∈ A ↔ τ a ∈ S := by
    intro τ hτ a
    rw [hF, Finset.mem_filter] at hτ
    rw [← hτ.2, Finset.mem_image]
    constructor
    · rintro ⟨u, hu, rfl⟩
      simpa using hu
    · intro h
      exact ⟨τ a, h, by simp⟩
  let f : F → (A ↪ S) × ({x // x ∉ A} ↪ {x // x ∉ S}) := fun τ =>
    (⟨fun a => ⟨τ.1 a, (hmem τ.1 τ.2 a).mp a.2⟩,
        fun a b h => Subtype.ext (τ.1.injective (congrArg Subtype.val h))⟩,
      ⟨fun a => ⟨τ.1 a, fun h => a.2 ((hmem τ.1 τ.2 a).mpr h)⟩,
        fun a b h => Subtype.ext (τ.1.injective (congrArg Subtype.val h))⟩)
  have hf : Function.Injective f := by
    intro τ τ' h
    apply Subtype.ext
    apply Equiv.ext
    intro a
    by_cases ha : a ∈ A
    · have := congrArg (fun p => ((p.1 ⟨a, ha⟩ : S) : Fin (m + 1))) h
      exact this
    · have := congrArg (fun p => ((p.2 ⟨a, ha⟩ : {x // x ∉ S}) : Fin (m + 1))) h
      exact this
  have hcard := Fintype.card_le_of_injective f hf
  rw [Fintype.card_coe, Fintype.card_prod, Fintype.card_embedding_eq, Fintype.card_embedding_eq,
    Fintype.card_coe, Fintype.card_coe, hA, Nat.descFactorial_self,
    Fintype.card_subtype_compl, Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_coe,
    Fintype.card_fin, hA, Nat.descFactorial_self] at hcard
  exact hcard

/-- **Counting one bad event.** The permutations mapping every `v ∉ T` outside `S` number at
most `C(|T| + 1, |S|) |S|! (m + 1 - |S|)!`: the preimage of `S` is a subset of size `|S|` of
`T ∪ {last}`, and for each such preimage there are at most `|S|! (m+1-|S|)!` permutations. -/
theorem card_permBad_le (S : Finset (Fin (m + 1))) (T : Finset (Fin m)) :
    (PermBad S T).card ≤
      (T.card + 1).choose S.card * (S.card.factorial * (m + 1 - S.card).factorial) := by
  set T' : Finset (Fin (m + 1)) :=
    insert (Fin.last m) (T.map ⟨Fin.castSucc, Fin.castSucc_injective m⟩) with hT'
  have hT'card : T'.card = T.card + 1 := by
    rw [hT', Finset.card_insert_of_notMem, Finset.card_map]
    rw [Finset.mem_map]
    rintro ⟨v, -, hv⟩
    exact (Fin.castSucc_lt_last v).ne hv
  have hsub : PermBad S T ⊆ (T'.powersetCard S.card).biUnion fun A =>
      Finset.univ.filter fun τ : Equiv.Perm (Fin (m + 1)) => S.image τ.symm = A := by
    intro τ hτ
    rw [PermBad, Finset.mem_filter] at hτ
    rw [Finset.mem_biUnion]
    refine ⟨S.image τ.symm, ?_, by simp⟩
    rw [Finset.mem_powersetCard]
    refine ⟨?_, Finset.card_image_of_injective _ τ.symm.injective⟩
    intro a ha
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
    by_cases hlast : τ.symm u = Fin.last m
    · rw [hlast, hT']
      exact Finset.mem_insert_self _ _
    · obtain ⟨v, hv⟩ := Fin.exists_castSucc_eq.mpr hlast
      rw [hT', Finset.mem_insert, Finset.mem_map]
      refine Or.inr ⟨v, ?_, hv⟩
      by_contra hvT
      apply hτ.2 v hvT
      rw [hv]
      simpa using hu
  calc (PermBad S T).card
      ≤ ((T'.powersetCard S.card).biUnion fun A =>
          Finset.univ.filter fun τ : Equiv.Perm (Fin (m + 1)) => S.image τ.symm = A).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ A ∈ T'.powersetCard S.card,
          (Finset.univ.filter fun τ : Equiv.Perm (Fin (m + 1)) => S.image τ.symm = A).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _A ∈ T'.powersetCard S.card, S.card.factorial * (m + 1 - S.card).factorial :=
        Finset.sum_le_sum fun A hA =>
          card_fiber_le S A (Finset.mem_powersetCard.mp hA).2
    _ = (T.card + 1).choose S.card * (S.card.factorial * (m + 1 - S.card).factorial) := by
        rw [Finset.sum_const, smul_eq_mul, Finset.card_powersetCard, hT'card]

/-- The bad tuples for `ε`: those with a set `S`, `1 ≤ |S| ≤ εm`, and a set `T` of
`5|S| - 1` right vertices such that every permutation maps every `v ∉ T` outside `S`. -/
noncomputable def Bad (ε : ℝ) (m : ℕ) : Finset (Tuple m) :=
  (Finset.Icc 1 ⌊ε * m⌋₊).biUnion fun s =>
    ((Finset.univ : Finset (Fin (m + 1))).powersetCard s).biUnion fun S =>
      ((Finset.univ : Finset (Fin m)).powersetCard (5 * s - 1)).biUnion fun T => BadAt S T

theorem good_of_notMem_bad {ε : ℝ} {σ : Tuple m} (hσ : σ ∉ Bad ε m) : Good ε σ := by
  intro S hS1 hSε T hT
  by_contra h
  apply hσ
  simp only [Bad, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_powersetCard]
  refine ⟨S.card, ⟨hS1, Nat.le_floor hSε⟩, S, ⟨Finset.subset_univ _, rfl⟩, T,
    ⟨Finset.subset_univ _, hT⟩, ?_⟩
  simp only [BadAt, Finset.mem_filter, Finset.mem_univ, true_and]
  intro i v hv hi
  exact h ⟨v, hv, i, hi⟩

theorem card_bad_le (ε : ℝ) (m : ℕ) :
    (Bad ε m).card ≤ ∑ s ∈ Finset.Icc 1 ⌊ε * m⌋₊, (m + 1).choose s * (m.choose (5 * s - 1) *
      ((5 * s).choose s * (s.factorial * (m + 1 - s).factorial)) ^ 7) := by
  refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun s hs => ?_)
  have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hs).1
  refine Finset.card_biUnion_le.trans ?_
  calc ∑ S ∈ (Finset.univ : Finset (Fin (m + 1))).powersetCard s,
        (((Finset.univ : Finset (Fin m)).powersetCard (5 * s - 1)).biUnion fun T =>
          BadAt S T).card
      ≤ ∑ _S ∈ (Finset.univ : Finset (Fin (m + 1))).powersetCard s, m.choose (5 * s - 1) *
          ((5 * s).choose s * (s.factorial * (m + 1 - s).factorial)) ^ 7 := by
        refine Finset.sum_le_sum fun S hS => ?_
        rw [Finset.mem_powersetCard] at hS
        refine Finset.card_biUnion_le.trans ?_
        calc ∑ T ∈ (Finset.univ : Finset (Fin m)).powersetCard (5 * s - 1), (BadAt S T).card
            ≤ ∑ _T ∈ (Finset.univ : Finset (Fin m)).powersetCard (5 * s - 1),
                ((5 * s).choose s * (s.factorial * (m + 1 - s).factorial)) ^ 7 := by
              refine Finset.sum_le_sum fun T hT => ?_
              rw [Finset.mem_powersetCard] at hT
              rw [card_badAt]
              refine Nat.pow_le_pow_left ?_ 7
              have := card_permBad_le S T
              rw [hT.2, hS.2] at this
              rwa [show 5 * s - 1 + 1 = 5 * s by omega] at this
          _ = _ := by
              rw [Finset.sum_const, smul_eq_mul, Finset.card_powersetCard, Finset.card_univ,
                Fintype.card_fin]
    _ = _ := by
        rw [Finset.sum_const, smul_eq_mul, Finset.card_powersetCard, Finset.card_univ,
          Fintype.card_fin]

/-! ### The union bound -/

/-- `C(n, k) ≤ (e n / k)^k`. -/
theorem choose_le_exp_pow (n k : ℕ) (hk : 0 < k) :
    (n.choose k : ℝ) ≤ (Real.exp 1 * n / k) ^ k := by
  have h1 : (n.choose k : ℝ) ≤ (n : ℝ) ^ k / k.factorial := Nat.choose_le_pow_div k n
  have h2 : (k : ℝ) ^ k / k.factorial ≤ Real.exp k :=
    Real.pow_div_factorial_le_exp (k : ℝ) (Nat.cast_nonneg k) k
  have hk' : (0 : ℝ) < (k : ℝ) ^ k := by positivity
  have hfact : (0 : ℝ) < k.factorial := by positivity
  have h3 : (1 : ℝ) / k.factorial ≤ Real.exp k / (k : ℝ) ^ k := by
    rw [div_le_div_iff₀ hfact hk', one_mul]
    rw [div_le_iff₀ hfact] at h2
    linarith
  calc (n.choose k : ℝ) ≤ (n : ℝ) ^ k / k.factorial := h1
    _ = (n : ℝ) ^ k * (1 / k.factorial) := by ring
    _ ≤ (n : ℝ) ^ k * (Real.exp k / (k : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = (Real.exp 1 * n / k) ^ k := by
        rw [← Real.exp_one_pow, div_pow, mul_pow]
        field_simp

/-- The per-size term of the union bound is at most `(1/10)^s ((m+1)!)^7` for `ε = 10⁻⁸`
and `1 ≤ s ≤ εm`. -/
theorem term_le (m s : ℕ) (hs1 : 1 ≤ s) (hsm : (s : ℝ) ≤ (1 / 10 ^ 8) * m) :
    (((m + 1).choose s * (m.choose (5 * s - 1) *
      ((5 * s).choose s * (s.factorial * (m + 1 - s).factorial)) ^ 7) : ℕ) : ℝ) ≤
      (1 / 10) ^ s * ((m + 1).factorial : ℝ) ^ 7 := by
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  have hsm' : 5 * s ≤ m := by
    have : (5 * s : ℝ) ≤ m := by linarith
    exact_mod_cast this
  have he : Real.exp 1 ≤ 3 := by
    have := Real.exp_one_lt_d9
    linarith
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  have he1 : (1 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  -- the factorials: `(m+1)! = (m+1)_s (m+1-s)!` and `C(5s, s) s! = (5s)_s ≤ (5s)^s`
  have hfact : ((m + 1).factorial : ℝ) = ((m + 1).descFactorial s : ℝ) * (m + 1 - s).factorial := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    have := Nat.choose_mul_factorial_mul_factorial (show s ≤ m + 1 by omega)
    rw [← this]
    push_cast
    ring
  have hdesc : ((5 * s).choose s * s.factorial : ℝ) ≤ ((5 * s : ℕ) : ℝ) ^ s := by
    have h := Nat.descFactorial_le_pow (5 * s) s
    rw [Nat.descFactorial_eq_factorial_mul_choose] at h
    exact_mod_cast (by rw [mul_comm] at h; exact h : (5 * s).choose s * s.factorial ≤ (5 * s) ^ s)
  have hdesc2 : (((m + 1) : ℝ) / 2) ^ s ≤ ((m + 1).descFactorial s : ℝ) := by
    have h := Nat.pow_sub_le_descFactorial (m + 1) s
    have h2 : (((m + 1) : ℝ) / 2) ≤ ((m + 1 + 1 - s : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      linarith
    calc (((m + 1) : ℝ) / 2) ^ s ≤ ((m + 1 + 1 - s : ℕ) : ℝ) ^ s :=
          pow_le_pow_left₀ (by positivity) h2 s
      _ ≤ _ := by exact_mod_cast h
  -- the binomial coefficients
  have hc1 : ((m + 1).choose s : ℝ) ≤ (Real.exp 1 * (m + 1) / s) ^ s := by
    have := choose_le_exp_pow (m + 1) s hs1
    push_cast at this
    exact this
  have hc2 : (m.choose (5 * s - 1) : ℝ) ≤ (Real.exp 1 * (m + 1) / (4 * s)) ^ (5 * s) := by
    have h1 := choose_le_exp_pow m (5 * s - 1) (by omega)
    have hbase : Real.exp 1 * m / ((5 * s - 1 : ℕ) : ℝ) ≤ Real.exp 1 * (m + 1) / (4 * s) := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      rw [div_le_div_iff₀ (by linarith) (by positivity)]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) he0.le) (by linarith)
        (by positivity) (by positivity)
    have hbase1 : (1 : ℝ) ≤ Real.exp 1 * (m + 1) / (4 * s) := by
      rw [le_div_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_right he1 (by positivity : (0 : ℝ) ≤ (m : ℝ) + 1)
      linarith
    calc (m.choose (5 * s - 1) : ℝ)
        ≤ (Real.exp 1 * m / ((5 * s - 1 : ℕ) : ℝ)) ^ (5 * s - 1) := h1
      _ ≤ (Real.exp 1 * (m + 1) / (4 * s)) ^ (5 * s - 1) :=
          pow_le_pow_left₀ (by positivity) hbase _
      _ ≤ (Real.exp 1 * (m + 1) / (4 * s)) ^ (5 * s) :=
          pow_le_pow_right₀ hbase1 (by omega)
  -- assemble
  have hpos : (0 : ℝ) ≤ ((m + 1 - s).factorial : ℝ) ^ 7 := by positivity
  have key : ((m + 1).choose s : ℝ) * (m.choose (5 * s - 1) : ℝ) *
      ((5 * s).choose s * s.factorial : ℝ) ^ 7 ≤
      (1 / 10) ^ s * ((m + 1).descFactorial s : ℝ) ^ 7 := by
    have hB : ((((m + 1) : ℝ) / 2) ^ s) ^ 7 ≤ ((m + 1).descFactorial s : ℝ) ^ 7 :=
      pow_le_pow_left₀ (by positivity) hdesc2 7
    have hbase : Real.exp 1 * ((m : ℝ) + 1) / s * (Real.exp 1 * ((m : ℝ) + 1) / (4 * s)) ^ 5 *
        (((5 * s : ℕ) : ℝ)) ^ 7 ≤ (1 / 10) * (((m : ℝ) + 1) / 2) ^ 7 := by
      have hL : Real.exp 1 * ((m : ℝ) + 1) / s * (Real.exp 1 * ((m : ℝ) + 1) / (4 * s)) ^ 5 *
          (((5 * s : ℕ) : ℝ)) ^ 7 = Real.exp 1 ^ 6 * (5 ^ 7 / 4 ^ 5) * (((m : ℝ) + 1) ^ 6 * s) := by
        push_cast
        field_simp
      have hR : (1 / 10 : ℝ) * (((m : ℝ) + 1) / 2) ^ 7 =
          (1 / 10 / 2 ^ 7) * (((m : ℝ) + 1) ^ 6 * ((m : ℝ) + 1)) := by ring
      rw [hL, hR]
      have h6 : Real.exp 1 ^ 6 ≤ 3 ^ 6 := pow_le_pow_left₀ he0.le he 6
      have hsm1 : (s : ℝ) ≤ (1 / 10 ^ 8) * ((m : ℝ) + 1) := by linarith
      have hm6 : (0 : ℝ) ≤ ((m : ℝ) + 1) ^ 6 := by positivity
      calc Real.exp 1 ^ 6 * (5 ^ 7 / 4 ^ 5) * (((m : ℝ) + 1) ^ 6 * s)
          ≤ 3 ^ 6 * (5 ^ 7 / 4 ^ 5) * (((m : ℝ) + 1) ^ 6 * ((1 / 10 ^ 8) * ((m : ℝ) + 1))) :=
            mul_le_mul (mul_le_mul_of_nonneg_right h6 (by norm_num))
              (mul_le_mul_of_nonneg_left hsm1 hm6) (by positivity) (by positivity)
        _ = (3 ^ 6 * (5 ^ 7 / 4 ^ 5) / 10 ^ 8) * (((m : ℝ) + 1) ^ 6 * ((m : ℝ) + 1)) := by ring
        _ ≤ (1 / 10 / 2 ^ 7) * (((m : ℝ) + 1) ^ 6 * ((m : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    calc ((m + 1).choose s : ℝ) * (m.choose (5 * s - 1) : ℝ) *
          ((5 * s).choose s * s.factorial : ℝ) ^ 7
        ≤ (Real.exp 1 * (m + 1) / s) ^ s * (Real.exp 1 * (m + 1) / (4 * s)) ^ (5 * s) *
            (((5 * s : ℕ) : ℝ) ^ s) ^ 7 := by
          gcongr
      _ = (Real.exp 1 * ((m : ℝ) + 1) / s * (Real.exp 1 * ((m : ℝ) + 1) / (4 * s)) ^ 5 *
            (((5 * s : ℕ) : ℝ)) ^ 7) ^ s := by
          rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm s 7]
      _ ≤ ((1 / 10) * (((m : ℝ) + 1) / 2) ^ 7) ^ s :=
          pow_le_pow_left₀ (by positivity) hbase s
      _ = (1 / 10) ^ s * ((((m + 1) : ℝ) / 2) ^ s) ^ 7 := by
          rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm 7 s]
      _ ≤ (1 / 10) ^ s * ((m + 1).descFactorial s : ℝ) ^ 7 :=
          mul_le_mul_of_nonneg_left hB (by positivity)
  have hN : (((m + 1).choose s * (m.choose (5 * s - 1) *
      ((5 * s).choose s * (s.factorial * (m + 1 - s).factorial)) ^ 7) : ℕ) : ℝ) =
      ((m + 1).choose s : ℝ) * (m.choose (5 * s - 1) : ℝ) *
        ((5 * s).choose s * s.factorial : ℝ) ^ 7 * ((m + 1 - s).factorial : ℝ) ^ 7 := by
    push_cast
    ring
  rw [hN, hfact, mul_pow (((m + 1).descFactorial s : ℕ) : ℝ) (((m + 1 - s).factorial : ℕ) : ℝ) 7]
  calc ((m + 1).choose s : ℝ) * (m.choose (5 * s - 1) : ℝ) *
        ((5 * s).choose s * s.factorial : ℝ) ^ 7 * ((m + 1 - s).factorial : ℝ) ^ 7
      ≤ (1 / 10) ^ s * ((m + 1).descFactorial s : ℝ) ^ 7 * ((m + 1 - s).factorial : ℝ) ^ 7 :=
        mul_le_mul_of_nonneg_right key hpos
    _ = (1 / 10) ^ s * (((m + 1).descFactorial s : ℝ) ^ 7 * ((m + 1 - s).factorial : ℝ) ^ 7) := by
        ring

/-- **The union bound**: for `ε = 10⁻⁸`, fewer than all tuples are bad. -/
theorem card_bad_lt (m : ℕ) : (Bad (1 / 10 ^ 8) m).card < Fintype.card (Tuple m) := by
  have hΩ : (Fintype.card (Tuple m) : ℝ) = ((m + 1).factorial : ℝ) ^ 7 := by
    rw [Fintype.card_fun, Fintype.card_perm, Fintype.card_fin, Fintype.card_fin]
    push_cast
    ring
  have hle : ((Bad (1 / 10 ^ 8) m).card : ℝ) ≤
      (∑ s ∈ Finset.Icc 1 ⌊(1 / 10 ^ 8 : ℝ) * m⌋₊, (1 / 10 : ℝ) ^ s) *
        ((m + 1).factorial : ℝ) ^ 7 := by
    calc ((Bad (1 / 10 ^ 8) m).card : ℝ)
        ≤ ((∑ s ∈ Finset.Icc 1 ⌊(1 / 10 ^ 8 : ℝ) * m⌋₊, (m + 1).choose s * (m.choose (5 * s - 1) *
            ((5 * s).choose s * (s.factorial * (m + 1 - s).factorial)) ^ 7) : ℕ) : ℝ) :=
          Nat.cast_le.mpr (card_bad_le (1 / 10 ^ 8) m)
      _ = ∑ s ∈ Finset.Icc 1 ⌊(1 / 10 ^ 8 : ℝ) * m⌋₊,
            (((m + 1).choose s * (m.choose (5 * s - 1) *
              ((5 * s).choose s * (s.factorial * (m + 1 - s).factorial)) ^ 7) : ℕ) : ℝ) :=
          Nat.cast_sum _ _
      _ ≤ ∑ s ∈ Finset.Icc 1 ⌊(1 / 10 ^ 8 : ℝ) * m⌋₊,
            (1 / 10 : ℝ) ^ s * ((m + 1).factorial : ℝ) ^ 7 := by
          refine Finset.sum_le_sum fun s hs => ?_
          rw [Finset.mem_Icc] at hs
          exact term_le m s hs.1 ((Nat.le_floor_iff (by positivity)).mp hs.2)
      _ = _ := by rw [Finset.sum_mul]
  have hgeom : (∑ s ∈ Finset.Icc 1 ⌊(1 / 10 ^ 8 : ℝ) * m⌋₊, (1 / 10 : ℝ) ^ s) ≤ 1 / 9 := by
    have hIcc : Finset.Icc 1 ⌊(1 / 10 ^ 8 : ℝ) * m⌋₊ =
        Finset.Ico 1 (⌊(1 / 10 ^ 8 : ℝ) * m⌋₊ + 1) := by
      ext s
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hIcc]
    calc (∑ s ∈ Finset.Ico 1 (⌊(1 / 10 ^ 8 : ℝ) * m⌋₊ + 1), (1 / 10 : ℝ) ^ s)
        ≤ (1 / 10 : ℝ) ^ 1 / (1 - 1 / 10) := geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)
      _ = 1 / 9 := by norm_num
  have hpos : (0 : ℝ) < ((m + 1).factorial : ℝ) ^ 7 := by positivity
  have : ((Bad (1 / 10 ^ 8) m).card : ℝ) < (Fintype.card (Tuple m) : ℝ) := by
    rw [hΩ]
    calc ((Bad (1 / 10 ^ 8) m).card : ℝ)
        ≤ (∑ s ∈ Finset.Icc 1 ⌊(1 / 10 ^ 8 : ℝ) * m⌋₊, (1 / 10 : ℝ) ^ s) *
            ((m + 1).factorial : ℝ) ^ 7 := hle
      _ ≤ (1 / 9) * ((m + 1).factorial : ℝ) ^ 7 := mul_le_mul_of_nonneg_right hgeom hpos.le
      _ < ((m + 1).factorial : ℝ) ^ 7 := by linarith
  exact_mod_cast this

/-- **A good tuple exists** for every `m`. -/
theorem exists_good (m : ℕ) : ∃ σ : Tuple m, Good (1 / 10 ^ 8) σ := by
  obtain ⟨σ, -, hσ⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show (Bad (1 / 10 ^ 8) m).card < (Finset.univ : Finset (Tuple m)).card by
      rw [Finset.card_univ]; exact card_bad_lt m)
  exact ⟨σ, good_of_notMem_bad hσ⟩

end ISS

/-- **Theorem [thm:iss-graphs].** The expander graphs exist, with `Δ = 7`, `Γ = 3` and
`ε = 10⁻⁸`, for every `m`. -/
theorem issGraphs : ISSGraphs := by
  refine ⟨7, 3, 1 / 10 ^ 8, by norm_num, by norm_num, 0, fun m _ => ?_⟩
  obtain ⟨σ, hσ⟩ := ISS.exists_good m
  exact ⟨{ U := Fin (m + 1)
           V := Fin m
           E := ISS.Edge σ
           G := ISS.graph σ
           simple := ISS.graph_simple σ
           card_U := Fintype.card_fin _
           card_V := Fintype.card_fin _
           maxDegreeLE := ISS.maxDegreeLE σ
           isBoundaryExpander := ISS.isBoundaryExpander_of_good (by norm_num) hσ
           exists_matching := ⟨ISS.matching σ, ISS.isMatching σ, ISS.matching_covers σ⟩ }⟩

end AssocLB
