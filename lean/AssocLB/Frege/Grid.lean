/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/
import AssocLB.Matching.Expander

/-!
# The odd grid

Paper: Section 9.2 (The odd grid): the grid `Grid_t` on `[1,t]²` for odd `t ≥ 3`, coloured as
a chessboard, is a bipartite graph `H = (U, V, E)` with `U` the white and `V` the black
vertices, `|U| = (t² + 1)/2 = m + 1`, `|V| = (t² − 1)/2 = m`, and maximum degree at most `4`,
so it satisfies the standing assumptions of Sections 5–8.

## Main definitions

* `Grid.Vertex t`: the vertices `Fin t × Fin t`, the paper's `[1,t]²` shifted to start at `0`.
* `Grid.IsWhite p`: `i + j` is even; `Grid.White t`, `Grid.Black t`: the white and the black
  vertices.
* `Grid.Adj p q`: the vertices agree in one coordinate and differ by `1` in the other.
* `Grid.Edge t`: an edge, an adjacent pair of a white and a black vertex.
* `grid t`: the grid as a bipartite graph `Bipartite (Grid.White t) (Grid.Black t) (Grid.Edge t)`.

## Main results

* `Grid.isWhite_iff_of_adj`, `Grid.not_isWhite_of_adj`: adjacent vertices have different
  colours, so every edge joins a white vertex to a black one.
* `Grid.card_white`, `Grid.card_black`: `|U| = (t² + 1)/2` and `|V| = (t² − 1)/2` for odd `t`;
  `Grid.card_white_eq_card_black_add_one`. The vertices are counted in row-major order: under
  `finProdFinEquiv`, the vertex `(i, j)` has index `j + t i`, whose parity is that of `i + j`
  when `t` is odd (`Grid.isWhite_iff_even_finProdFinEquiv`), so the white vertices are the
  even indices below `t²` and the black ones the odd indices (`Grid.count_even`).
* `Grid.card_filter_adj_le`: a vertex has at most four neighbours.
* `Grid.grid_isSimple`, `Grid.grid_maxDegreeLE`: the grid is simple with maximum degree at
  most `4`.
* `Grid.exists_edge_left`, `Grid.exists_edge_right`: every vertex has an edge when `t ≥ 2`, as
  Lemma [lem:local-soundness] requires.

## Design notes

* An edge is an ordered pair (white endpoint, black endpoint) with the adjacency proof, so
  every geometric edge appears exactly once and the graph is simple by construction; the
  colouring of the endpoints is `Grid.not_isWhite_of_adj`.
* The shift from `[1,t]` to `[0,t)` preserves the parity of `i + j`, so the colouring is the
  paper's, with `(0,0)` white.
* The reduction needs only `|U| = m + 1`, `|V| = m`, simplicity, maximum degree `Δ = 4` and the
  existence of an edge at every vertex (`Assoc.exists_refutation_SPM` and its Frege analogue);
  no expansion or matching property of the grid is used, those being replaced by Theorem
  [thm:hastad].
-/

namespace AssocLB

namespace Grid

/-- The vertices of the grid: `[0,t)²`, the paper's `[1,t]²`.

Paper: Section 9.2. -/
abbrev Vertex (t : ℕ) := Fin t × Fin t

variable {t : ℕ}

/-- A vertex `(i, j)` is white if `i + j` is even.

Paper: Section 9.2. -/
def IsWhite (p : Vertex t) : Prop := Even (p.1.val + p.2.val)

instance : DecidablePred (IsWhite (t := t)) := fun p =>
  inferInstanceAs (Decidable (Even (p.1.val + p.2.val)))

/-- The white vertices, the side `U`. -/
abbrev White (t : ℕ) := {p : Vertex t // IsWhite p}

/-- The black vertices, the side `V`. -/
abbrev Black (t : ℕ) := {p : Vertex t // ¬ IsWhite p}

/-- Two vertices are adjacent if they agree in one coordinate and differ by `1` in the other.

Paper: Section 9.2. -/
def Adj (p q : Vertex t) : Prop :=
  (p.1 = q.1 ∧ (p.2.val + 1 = q.2.val ∨ q.2.val + 1 = p.2.val)) ∨
    (p.2 = q.2 ∧ (p.1.val + 1 = q.1.val ∨ q.1.val + 1 = p.1.val))

instance : DecidableRel (Adj (t := t)) := fun p q =>
  inferInstanceAs (Decidable ((p.1 = q.1 ∧ (p.2.val + 1 = q.2.val ∨ q.2.val + 1 = p.2.val)) ∨
    (p.2 = q.2 ∧ (p.1.val + 1 = q.1.val ∨ q.1.val + 1 = p.1.val))))

theorem adj_comm (p q : Vertex t) : Adj p q ↔ Adj q p := by
  unfold Adj
  constructor <;> rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
    first
    | exact Or.inl ⟨h1.symm, h2.symm⟩
    | exact Or.inr ⟨h1.symm, h2.symm⟩

/-- Adjacent vertices have different colours. -/
theorem isWhite_iff_of_adj {p q : Vertex t} (h : Adj p q) : IsWhite p ↔ ¬ IsWhite q := by
  unfold IsWhite
  rw [Nat.even_iff, Nat.even_iff]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> have := congrArg Fin.val h1 <;> omega

/-- Adjacent vertices have different colours. -/
theorem not_isWhite_of_adj {p q : Vertex t} (h : Adj p q) (hp : IsWhite p) : ¬ IsWhite q :=
  (isWhite_iff_of_adj h).mp hp

/-- A vertex has at most four neighbours: `(i ± 1, j)` and `(i, j ± 1)`. -/
theorem card_filter_adj_le (p : Vertex t) :
    ((Finset.univ : Finset (Vertex t)).filter (Adj p)).card ≤ 4 := by
  refine (Finset.card_le_card_of_injOn (fun q : Vertex t => (q.1.val, q.2.val))
    (t := {(p.1.val + 1, p.2.val), (p.1.val - 1, p.2.val), (p.1.val, p.2.val + 1),
      (p.1.val, p.2.val - 1)}) ?_ ?_).trans Finset.card_le_four
  · intro q hq
    rw [Finset.mem_coe, Finset.mem_filter] at hq
    obtain ⟨-, hq⟩ := hq
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff,
      Prod.mk.injEq]
    rcases hq with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> have := congrArg Fin.val h1 <;> omega
  · intro q _ q' _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)

/-- An edge of the grid: an adjacent pair of a white and a black vertex. -/
abbrev Edge (t : ℕ) := {e : White t × Black t // Adj e.1.1 e.2.1}

end Grid

/-- The odd grid `Grid_t` as a bipartite graph, with `U` the white and `V` the black vertices.

Paper: Section 9.2. -/
def grid (t : ℕ) : Bipartite (Grid.White t) (Grid.Black t) (Grid.Edge t) where
  left e := e.1.1
  right e := e.1.2

namespace Grid

variable {t : ℕ}

@[simp] theorem grid_left (e : Edge t) : (grid t).left e = e.1.1 := rfl

@[simp] theorem grid_right (e : Edge t) : (grid t).right e = e.1.2 := rfl

/-! ### Counting the vertices -/

/-- The number of even naturals below `n` is `(n + 1) / 2`. -/
theorem count_even (n : ℕ) : Nat.count Even n = (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.count_succ, ih]
    split_ifs with h
    all_goals
      rw [Nat.even_iff] at h
      omega

/-- The elements of `Fin n` with even value number `(n + 1) / 2`. -/
theorem card_fin_even (n : ℕ) : Fintype.card {k : Fin n // Even k.val} = (n + 1) / 2 := by
  rw [Fintype.card_subtype, ← count_even, Nat.count_eq_card_filter_range, ← Nat.Iio_eq_range,
    ← Fin.map_valEmbedding_univ, Finset.filter_map, Finset.card_map]
  rfl

/-- The elements of `Fin n` with odd value number `n / 2`: the complement of the even ones. -/
theorem card_fin_not_even (n : ℕ) : Fintype.card {k : Fin n // ¬ Even k.val} = n / 2 := by
  rw [Fintype.card_subtype_compl, card_fin_even, Fintype.card_fin]
  omega

/-- In row-major order the vertex `(i, j)` has index `j + t i`, whose parity is that of `i + j`
when `t` is odd: a vertex is white exactly when its index is even. -/
theorem isWhite_iff_even_finProdFinEquiv (ht : Odd t) (p : Vertex t) :
    IsWhite p ↔ Even (finProdFinEquiv p).val := by
  rw [IsWhite, finProdFinEquiv_apply_val, Nat.even_add, Nat.even_add, Nat.even_mul]
  have := Nat.not_even_iff_odd.mpr ht
  tauto

/-- The white vertices are the even indices in row-major order. -/
def whiteEquiv (ht : Odd t) : White t ≃ {k : Fin (t * t) // Even k.val} :=
  Equiv.subtypeEquiv finProdFinEquiv (isWhite_iff_even_finProdFinEquiv ht)

/-- The black vertices are the odd indices in row-major order. -/
def blackEquiv (ht : Odd t) : Black t ≃ {k : Fin (t * t) // ¬ Even k.val} :=
  Equiv.subtypeEquiv finProdFinEquiv fun p => not_congr (isWhite_iff_even_finProdFinEquiv ht p)

/-- The number of white vertices of the odd grid is `(t² + 1)/2`.

Paper: Section 9.2. -/
theorem card_white (ht : Odd t) : Fintype.card (White t) = (t ^ 2 + 1) / 2 := by
  rw [Fintype.card_congr (whiteEquiv ht), card_fin_even, sq]

/-- The number of black vertices of the odd grid is `(t² − 1)/2`.

Paper: Section 9.2. -/
theorem card_black (ht : Odd t) : Fintype.card (Black t) = (t ^ 2 - 1) / 2 := by
  rw [Fintype.card_congr (blackEquiv ht), card_fin_not_even, sq]
  have := Nat.odd_iff.mp (Nat.odd_mul.mpr ⟨ht, ht⟩)
  omega

/-- The odd grid has one more white vertex than black vertices: `|U| = |V| + 1`. -/
theorem card_white_eq_card_black_add_one (ht : Odd t) :
    Fintype.card (White t) = Fintype.card (Black t) + 1 := by
  rw [card_white ht, card_black ht]
  have := Nat.odd_iff.mp (ht.pow (n := 2))
  omega

/-! ### Simplicity, degree and edges at every vertex -/

/-- The grid is simple. -/
theorem grid_isSimple : (grid t).IsSimple := fun _ _ h1 h2 => Subtype.ext (Prod.ext h1 h2)

/-- Every vertex of the grid has degree at most `4`.

Paper: Section 9.2. -/
theorem grid_maxDegreeLE : (grid t).MaxDegreeLE 4 := by
  rintro (u | v)
  · -- the edges at a white vertex inject into its neighbours via their black endpoints
    refine (Finset.card_le_card_of_injOn (fun e : Edge t => e.1.2.1) ?_ ?_).trans
      (card_filter_adj_le u.1)
    · intro e he
      rw [Finset.mem_coe, (grid t).mem_star_inl] at he
      rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [← he]
      exact e.2
    · intro e he e' he' h
      rw [Finset.mem_coe, (grid t).mem_star_inl] at he he'
      exact Subtype.ext (Prod.ext (he.trans he'.symm) (Subtype.ext h))
  · -- the edges at a black vertex inject into its neighbours via their white endpoints
    refine (Finset.card_le_card_of_injOn (fun e : Edge t => e.1.1.1) ?_ ?_).trans
      (card_filter_adj_le v.1)
    · intro e he
      rw [Finset.mem_coe, (grid t).mem_star_inr] at he
      rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [← he]
      exact (adj_comm _ _).mp e.2
    · intro e he e' he' h
      rw [Finset.mem_coe, (grid t).mem_star_inr] at he he'
      exact Subtype.ext (Prod.ext (Subtype.ext h) (he.trans he'.symm))

/-- Every white vertex has an edge once `t ≥ 2`: the vertex to its right, or to its left in the
last column. -/
theorem exists_edge_left (ht : 2 ≤ t) (u : White t) : ∃ e, (grid t).left e = u := by
  obtain ⟨⟨i, j⟩, hu⟩ := u
  by_cases hj : j.val + 1 < t
  · have hadj : Adj (i, j) (i, ⟨j.val + 1, hj⟩) := Or.inl ⟨rfl, Or.inl rfl⟩
    exact ⟨⟨(⟨(i, j), hu⟩, ⟨_, not_isWhite_of_adj hadj hu⟩), hadj⟩, rfl⟩
  · have hj1 : 1 ≤ j.val := by
      have := j.is_lt
      omega
    have hadj : Adj (i, j) (i, ⟨j.val - 1, by omega⟩) :=
      Or.inl ⟨rfl, Or.inr (show j.val - 1 + 1 = j.val by omega)⟩
    exact ⟨⟨(⟨(i, j), hu⟩, ⟨_, not_isWhite_of_adj hadj hu⟩), hadj⟩, rfl⟩

/-- Every black vertex has an edge once `t ≥ 2`: the vertex to its right, or to its left in the
last column. -/
theorem exists_edge_right (ht : 2 ≤ t) (v : Black t) : ∃ e, (grid t).right e = v := by
  obtain ⟨⟨i, j⟩, hv⟩ := v
  by_cases hj : j.val + 1 < t
  · have hadj : Adj (i, ⟨j.val + 1, hj⟩) (i, j) := Or.inl ⟨rfl, Or.inr rfl⟩
    exact ⟨⟨(⟨_, (isWhite_iff_of_adj hadj).mpr hv⟩, ⟨(i, j), hv⟩), hadj⟩, rfl⟩
  · have hj1 : 1 ≤ j.val := by
      have := j.is_lt
      omega
    have hadj : Adj (i, ⟨j.val - 1, by omega⟩) (i, j) :=
      Or.inl ⟨rfl, Or.inl (show j.val - 1 + 1 = j.val by omega)⟩
    exact ⟨⟨(⟨_, (isWhite_iff_of_adj hadj).mpr hv⟩, ⟨(i, j), hv⟩), hadj⟩, rfl⟩

end Grid

end AssocLB
