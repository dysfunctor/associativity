/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/
import AssocLB.Multiplier.StripLocal
import AssocLB.Matching.Expander

/-!
# Index maps

Paper: Section 7.1 (Construction of the index maps `i(u)`, `j(e)`, `k(v)`): Definition
[def:columns] (columns of pairs and triples), Lemma [lem:golomb] (directed Golomb ruler) and
Lemma [lem:indices] (construction of index maps).

## Main definitions

* `stripWidth m`: the strip width `g = ⌈log(m+2)⌉ + 2`.
* `IsGolombRuler s`: every nonzero directed difference of marks determines its ordered pair.
* `IndexMaps H g K n₀`: maps `i : U → ℕ`, `j : E → ℕ`, `k : V → ℕ` with the properties of
  Lemma [lem:indices]: distinct positions (i), strip alignment (ii), the common column `K` of
  the incident triples and the outer collision pattern (iv). The inner collision pattern (iii)
  and (iv)(a) are derived: `IndexMaps.colXY_eq_colXYv_iff`, `IndexMaps.colXY_nonincident`,
  `IndexMaps.colYZ_eq_colYZu_iff`, `IndexMaps.colYZ_nonincident`,
  `IndexMaps.colOuter_eq_K_iff`.
* `IndexMaps.colXY`, `IndexMaps.colYZ`, `IndexMaps.colOuter`: Definition [def:columns];
  `IndexMaps.colXYv v = K - k v` and `IndexMaps.colYZu u = K - i u`, the columns `col_xy(v)`
  and `col_yz(u)` of the incident pairs.
* `indexK m g = 2g(B+1)R` and `indexN₀ m g = 4K` with `R = 32m²` and `B = 2R + 1`.

## Main results

* `exists_golombRuler`: Lemma [lem:golomb], by the Erdős–Turán construction
  `s_r = 2pr + (r² mod p)` for a prime `m + 1 < p ≤ 2(m + 1)` (Bertrand's postulate).
* `exists_indexMaps`: Lemma [lem:indices]; `indexN₀_le : n₀ ≤ 16896 g m⁴`, the paper's
  `n₀ = O(m⁴ log m)` for `g = O(log m)`.
* `IndexMaps.strip_at_col`: the arithmetic of the strip at a column that is a multiple of `g`
  and at most `K`, used for both inner copies in Section 8.

## Design notes

* `IndexMaps` records the properties the rest of the argument uses rather than the concrete
  maps; the paper notes that only the properties of Lemma [lem:indices] are used afterwards.
  Its fields are (i), (ii), the bounds `i u ≤ K`, `k v ≤ K`, `g ∣ K`, the common incident
  column (`incident_col`) and (iv) as `colOuter_eq_iff`, `i_diff_unique`, `k_diff_unique`.
* Differences are taken in `ℤ`. The construction needs the graph to be simple, as `j` is a
  function of the endpoints of an edge; `ExpanderGraph.simple` provides this.
* The width `g` is a parameter with `0 < g`; the construction does not depend on its value,
  and `stripWidth m` is used only in Section 7.2.
-/

namespace AssocLB

/-! ### The strip width -/

/-- The strip width `g = ⌈log(m+2)⌉ + 2`.

Paper: Lemma [lem:indices]. -/
def stripWidth (m : ℕ) : ℕ := Nat.clog 2 (m + 2) + 2

theorem stripWidth_pos (m : ℕ) : 0 < stripWidth m := by
  unfold stripWidth
  omega

/-- `2(m+2) ≤ 2^(g-1)`: a strip of width `g` can count `m + 1` partial products. -/
theorem two_mul_le_two_pow_stripWidth (m : ℕ) : 2 * (m + 2) ≤ 2 ^ (stripWidth m - 1) := by
  have h : m + 2 ≤ 2 ^ Nat.clog 2 (m + 2) := Nat.le_pow_clog one_lt_two _
  have h' : stripWidth m - 1 = Nat.clog 2 (m + 2) + 1 := by
    unfold stripWidth
    omega
  rw [h', Nat.pow_succ]
  omega

/-! ### The directed Golomb ruler -/

/-- A directed Golomb ruler: every nonzero directed difference `s a - s b` determines the
ordered pair `(a, b)`.

Paper: Lemma [lem:golomb]. -/
def IsGolombRuler {ι : Type*} (s : ι → ℕ) : Prop :=
  ∀ a b c d, (s a : ℤ) - s b = s c - s d → (s a : ℤ) - s b ≠ 0 → a = c ∧ b = d

/-- **Directed Golomb ruler.** For `m ≥ 1` there are `m + 1` distinct marks below `32m²`
forming a directed Golomb ruler: the Erdős–Turán marks `s_r = 2pr + (r² mod p)` for a prime
`m + 1 < p ≤ 2(m + 1)`.

Paper: Lemma [lem:golomb]. -/
theorem exists_golombRuler (m : ℕ) (hm : 1 ≤ m) :
    ∃ s : Fin (m + 1) → ℕ, Function.Injective s ∧ (∀ r, s r < 32 * m ^ 2) ∧ IsGolombRuler s := by
  obtain ⟨p, hp, hmp, hp2⟩ := Nat.exists_prime_lt_and_le_two_mul (m + 1) (by omega)
  have := Fact.mk hp
  have hp3 : 3 ≤ p := by omega
  -- the residues `τ r = r² mod p`, kept opaque
  obtain ⟨τ, hτ_def⟩ : ∃ τ : ℕ → ℕ, ∀ r, τ r = r * r % p := ⟨_, fun _ => rfl⟩
  have hτ : ∀ r : ℕ, τ r < p := fun r => by rw [hτ_def]; exact Nat.mod_lt _ hp.pos
  have hτcast : ∀ r : ℕ, ((τ r : ℕ) : ZMod p) = (r : ZMod p) * r := fun r => by
    rw [hτ_def, ZMod.natCast_mod, Nat.cast_mul]
  -- the key computation: equal differences of marks force equal differences of indices
  -- and of the residues
  have key : ∀ a b c d : Fin (m + 1),
      ((2 * p * a + τ a : ℕ) : ℤ) - (2 * p * b + τ b : ℕ) =
        ((2 * p * c + τ c : ℕ) : ℤ) - (2 * p * d + τ d : ℕ) →
      ((a : ℕ) : ℤ) - (b : ℕ) = (c : ℕ) - (d : ℕ) ∧
        ((τ a : ℕ) : ℤ) - (τ b : ℕ) = ((τ c : ℕ) : ℤ) - (τ d : ℕ) := by
    intro a b c d h
    have ha : ((τ a : ℕ) : ℤ) < p := by exact_mod_cast hτ a
    have hb : ((τ b : ℕ) : ℤ) < p := by exact_mod_cast hτ b
    have hc : ((τ c : ℕ) : ℤ) < p := by exact_mod_cast hτ c
    have hd : ((τ d : ℕ) : ℤ) < p := by exact_mod_cast hτ d
    push_cast at h
    have hdvd : (2 * (p : ℤ)) ∣ (((τ c : ℕ) : ℤ) - (τ d : ℕ)) - (((τ a : ℕ) : ℤ) - (τ b : ℕ)) :=
      ⟨(((a : ℕ) : ℤ) - (b : ℕ)) - ((c : ℕ) - (d : ℕ)), by linarith⟩
    have hzero := Int.eq_zero_of_abs_lt_dvd hdvd (abs_lt.mpr ⟨by linarith, by linarith⟩)
    have hp0 : (2 * (p : ℤ)) ≠ 0 := by positivity
    refine ⟨?_, by linarith⟩
    have hmul : (2 * (p : ℤ)) * ((((a : ℕ) : ℤ) - (b : ℕ)) - ((c : ℕ) - (d : ℕ))) = 0 := by
      linarith
    have := (mul_eq_zero.mp hmul).resolve_left hp0
    linarith
  refine ⟨fun r => 2 * p * r + τ r, ?_, ?_, ?_⟩
  · -- injectivity
    intro a b hab
    have hab' : 2 * p * (a : ℕ) + τ a = 2 * p * (b : ℕ) + τ b := hab
    have h := (key a b b b (by rw [hab'])).1
    exact Fin.ext (by exact_mod_cast sub_eq_zero.mp (by linarith : ((a : ℕ) : ℤ) - (b : ℕ) = 0))
  · -- range
    intro r
    change 2 * p * (r : ℕ) + τ r < 32 * m ^ 2
    have h1 : (r : ℕ) ≤ m := Fin.is_le r
    have h2 := hτ r
    nlinarith
  · -- the Golomb property
    intro a b c d h hne
    obtain ⟨h₁, h₂⟩ := key a b c d h
    have hab : (a : ℕ) ≠ b := by
      intro hab'
      apply hne
      rw [Fin.ext hab']
      ring
    have ha : ((a : ℕ) : ℤ) ≤ m := by exact_mod_cast Fin.is_le a
    have hb : ((b : ℕ) : ℤ) ≤ m := by exact_mod_cast Fin.is_le b
    -- pass to `ZMod p`
    have hA : ((a : ℕ) : ZMod p) - (b : ℕ) = (c : ℕ) - (d : ℕ) := by
      have := congrArg (Int.cast : ℤ → ZMod p) h₁
      push_cast at this
      exact this
    have hT : ((a : ℕ) : ZMod p) * a - (b : ℕ) * b = (c : ℕ) * c - (d : ℕ) * d := by
      have := congrArg (Int.cast : ℤ → ZMod p) h₂
      rw [Int.cast_sub, Int.cast_sub, Int.cast_natCast, Int.cast_natCast, Int.cast_natCast,
        Int.cast_natCast, hτcast, hτcast, hτcast, hτcast] at this
      exact this
    have hH : ((a : ℕ) : ZMod p) - (b : ℕ) ≠ 0 := by
      intro h0
      have h0' : ((((a : ℕ) : ℤ) - (b : ℕ) : ℤ) : ZMod p) = 0 := by
        push_cast
        exact h0
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0'
      have := Int.eq_zero_of_abs_lt_dvd h0' (abs_lt.mpr ⟨by linarith, by linarith⟩)
      exact hab (by exact_mod_cast sub_eq_zero.mp this)
    have hprod : (((a : ℕ) : ZMod p) - (b : ℕ)) * ((a : ℕ) + (b : ℕ)) =
        (((a : ℕ) : ZMod p) - (b : ℕ)) * ((c : ℕ) + (d : ℕ)) := by
      linear_combination hT - (((c : ℕ) : ZMod p) + (d : ℕ)) * hA
    have hsum : ((a : ℕ) : ZMod p) + (b : ℕ) = (c : ℕ) + (d : ℕ) := mul_left_cancel₀ hH hprod
    have h2A : (2 : ZMod p) * (a : ℕ) = 2 * (c : ℕ) := by linear_combination hsum + hA
    have h2 : (2 : ZMod p) ≠ 0 := by
      intro h0
      have h0' : ((2 : ℤ) : ZMod p) = 0 := by exact_mod_cast h0
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0'
      have := Int.le_of_dvd (by norm_num) h0'
      linarith
    have hAC : ((a : ℕ) : ZMod p) = (c : ℕ) := mul_left_cancel₀ h2 h2A
    have hBD : ((b : ℕ) : ZMod p) = (d : ℕ) := by linear_combination hAC - hA
    have hac : (a : ℕ) = c := by
      have := (ZMod.natCast_eq_natCast_iff' (a : ℕ) (c : ℕ) p).mp hAC
      rwa [Nat.mod_eq_of_lt (by have := Fin.is_le a; omega),
        Nat.mod_eq_of_lt (by have := Fin.is_le c; omega)] at this
    have hbd : (b : ℕ) = d := by
      have := (ZMod.natCast_eq_natCast_iff' (b : ℕ) (d : ℕ) p).mp hBD
      rwa [Nat.mod_eq_of_lt (by have := Fin.is_le b; omega),
        Nat.mod_eq_of_lt (by have := Fin.is_le d; omega)] at this
    exact ⟨Fin.ext hac, Fin.ext hbd⟩

/-- **Base-`B` uniqueness.** With `B = 2R + 1`, a two-digit value `a + B b` with `|a| < R`
determines its digits.

Paper: proof of Lemma [lem:indices]. -/
theorem baseB_unique {R : ℕ} {a a' b b' : ℤ} (ha : |a| < R) (ha' : |a'| < R)
    (h : a + (2 * R + 1) * b = a' + (2 * R + 1) * b') : a = a' ∧ b = b' := by
  have hdvd : (2 * (R : ℤ) + 1) ∣ a - a' := ⟨b' - b, by linarith⟩
  have h0 : a - a' = 0 := by
    refine Int.eq_zero_of_abs_lt_dvd hdvd ?_
    rw [abs_lt] at ha ha' ⊢
    constructor <;> linarith
  refine ⟨sub_eq_zero.mp h0, ?_⟩
  have hmul : (2 * (R : ℤ) + 1) * (b - b') = 0 := by linarith
  rcases mul_eq_zero.mp hmul with h1 | h1
  · exfalso
    have : (0 : ℤ) < 2 * (R : ℤ) + 1 := by positivity
    linarith
  · linarith

/-! ### Index maps -/

/-- Index maps as in Lemma [lem:indices]: maps `i : U → ℕ`, `j : E → ℕ`, `k : V → ℕ` to bit
positions of `x`, `y`, `z`, with (i) distinct positions, (ii) strip alignment for the width
`g` within `[0, n₀)`, the common column `K` of the incident triples `(u_e, e, v_e)`, and (iv)
the outer collision pattern: the column `i u + j e + k v` is determined, injectively, by the
difference pair `(i u - i u_e, k v - k v_e)`, and a nonzero difference determines its ordered
pair of vertices. The inner collision pattern (iii) follows; see `IndexMaps.colXY_nonincident`
and `IndexMaps.colXY_eq_colXYv_iff`.

Paper: Lemma [lem:indices]. -/
structure IndexMaps {U V E : Type*} (H : Bipartite U V E) (g K n₀ : ℕ) where
  /-- The `x`-position `i(u)` of the vertex `u ∈ U`. -/
  i : U → ℕ
  /-- The `y`-position `j(e)` of the edge `e`. -/
  j : E → ℕ
  /-- The `z`-position `k(v)` of the vertex `v ∈ V`. -/
  k : V → ℕ
  /-- (i) Distinct positions. -/
  i_injective : Function.Injective i
  j_injective : Function.Injective j
  k_injective : Function.Injective k
  /-- The positions lie in `[0, n₀)`. -/
  i_lt : ∀ u, i u < n₀
  j_lt : ∀ e, j e < n₀
  k_lt : ∀ v, k v < n₀
  /-- (ii) Strip alignment: the positions, hence the columns, are multiples of `g`. -/
  g_dvd_i : ∀ u, g ∣ i u
  g_dvd_j : ∀ e, g ∣ j e
  g_dvd_k : ∀ v, g ∣ k v
  g_dvd_K : g ∣ K
  g_dvd_n₀ : g ∣ n₀
  /-- (ii) The columns lie in `[0, n₀)`. -/
  colXY_lt : ∀ u e, i u + j e < n₀
  colYZ_lt : ∀ e v, j e + k v < n₀
  colOuter_lt : ∀ u e v, i u + j e + k v < n₀
  /-- The positions of the vertices lie below `K`, so that `K - k v` and `K - i u` are the
  columns `col_xy(v)` and `col_yz(u)`; `K` itself lies in `[0, n₀)`. -/
  i_le_K : ∀ u, i u ≤ K
  k_le_K : ∀ v, k v ≤ K
  K_lt : K < n₀
  /-- The columns `col_xy(v) + k(v')` and `i(u') + col_yz(u)` of the outer partial products
  with a constant inner factor lie in `[0, n₀)`. -/
  K_add_i_lt : ∀ u, K + i u < n₀
  K_add_k_lt : ∀ v, K + k v < n₀
  /-- (iv)(a) Every incident triple `(u_e, e, v_e)` lies in the column `K`. -/
  incident_col : ∀ e, i (H.left e) + j e + k (H.right e) = K
  /-- (iv) The column of a triple is determined, injectively, by its difference pair. -/
  colOuter_eq_iff : ∀ u e v u' e' v', i u + j e + k v = i u' + j e' + k v' ↔
    ((i u : ℤ) - i (H.left e) = i u' - i (H.left e') ∧
      (k v : ℤ) - k (H.right e) = k v' - k (H.right e'))
  /-- (iv)(b) A nonzero difference of `x`-positions determines its ordered pair of vertices. -/
  i_diff_unique : ∀ u e u' e', (i u : ℤ) - i (H.left e) = i u' - i (H.left e') →
    (i u : ℤ) - i (H.left e) ≠ 0 → u = u' ∧ H.left e = H.left e'
  /-- (iv)(b) A nonzero difference of `z`-positions determines its ordered pair of vertices. -/
  k_diff_unique : ∀ v e v' e', (k v : ℤ) - k (H.right e) = k v' - k (H.right e') →
    (k v : ℤ) - k (H.right e) ≠ 0 → v = v' ∧ H.right e = H.right e'

namespace IndexMaps

variable {U V E : Type*} {H : Bipartite U V E} {g K n₀ : ℕ} (I : IndexMaps H g K n₀)

/-! #### Columns -/

/-- The column `col_xy(u, e) = i(u) + j(e)` of the partial product `x_{i(u)} y_{j(e)}`.

Paper: Definition [def:columns]. -/
def colXY (u : U) (e : E) : ℕ := I.i u + I.j e

/-- The column `col_yz(e, v) = j(e) + k(v)` of the partial product `y_{j(e)} z_{k(v)}`.

Paper: Definition [def:columns]. -/
def colYZ (e : E) (v : V) : ℕ := I.j e + I.k v

/-- The column `i(u) + j(e) + k(v)` of the outer partial products of the triple `(u, e, v)`,
the same in `(xy)z` and in `x(yz)`.

Paper: Definition [def:columns]. -/
def colOuter (u : U) (e : E) (v : V) : ℕ := I.i u + I.j e + I.k v

/-- The column `col_xy(v) = K - k(v)` shared by the incident pairs `(u_e, e)`, `e ∈ E(v)`.

Paper: Lemma [lem:indices] (iii)(a). -/
def colXYv (v : V) : ℕ := K - I.k v

/-- The column `col_yz(u) = K - i(u)` shared by the incident pairs `(e, v_e)`, `e ∈ E(u)`.

Paper: Lemma [lem:indices] (iii)(b). -/
def colYZu (u : U) : ℕ := K - I.i u

theorem colOuter_eq (u : U) (e : E) (v : V) : I.colOuter u e v = I.colXY u e + I.k v := rfl

theorem colOuter_eq' (u : U) (e : E) (v : V) : I.colOuter u e v = I.i u + I.colYZ e v := by
  unfold colOuter colYZ
  omega

theorem g_dvd_colXY (u : U) (e : E) : g ∣ I.colXY u e := Nat.dvd_add (I.g_dvd_i u) (I.g_dvd_j e)

theorem g_dvd_colYZ (e : E) (v : V) : g ∣ I.colYZ e v := Nat.dvd_add (I.g_dvd_j e) (I.g_dvd_k v)

theorem g_dvd_colOuter (u : U) (e : E) (v : V) : g ∣ I.colOuter u e v :=
  Nat.dvd_add (I.g_dvd_colXY u e) (I.g_dvd_k v)

theorem g_dvd_colXYv (v : V) : g ∣ I.colXYv v := Nat.dvd_sub I.g_dvd_K (I.g_dvd_k v)

theorem g_dvd_colYZu (u : U) : g ∣ I.colYZu u := Nat.dvd_sub I.g_dvd_K (I.g_dvd_i u)

theorem colXYv_le (v : V) : I.colXYv v ≤ K := Nat.sub_le _ _

theorem colYZu_le (u : U) : I.colYZu u ≤ K := Nat.sub_le _ _

include I in
/-- Arithmetic of the strip at a column `col` that is a multiple of `g` and at most `K`: the
whole strip `[col, col + g)` lies below `n₀`, and for `k < g` the column `col + k` has quotient
`col / g` and remainder `k`, hence lies in the strip numbered `col / g`. -/
theorem strip_at_col (hg : 1 ≤ g) {col k : ℕ} (hdvd : g ∣ col) (hcol : col ≤ K) (hk : k < g) :
    col + g ≤ n₀ ∧ (col + k) / g * g = col ∧ (col + k) % g = k ∧
      InStrip g (col / g) (col + k) := by
  obtain ⟨a, ha⟩ := hdvd
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 : col / g < n₀ / g :=
      Nat.div_lt_div_of_lt_of_dvd I.g_dvd_n₀ (lt_of_le_of_lt hcol I.K_lt)
    have h2 := Nat.mul_le_mul_right g h1
    rwa [Nat.div_mul_cancel I.g_dvd_n₀, Nat.succ_mul, Nat.div_mul_cancel ⟨a, ha⟩] at h2
  · rw [ha, Nat.mul_add_div hg, Nat.div_eq_of_lt hk, Nat.add_zero, Nat.mul_comm]
  · rw [ha, Nat.mul_add_mod, Nat.mod_eq_of_lt hk]
  · rw [ha, Nat.mul_div_cancel_left a hg]
    exact ⟨by rw [Nat.mul_comm]; omega, by rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]; omega⟩

/-- (iii)(a) Distinct vertices of `V` have distinct columns `col_xy(v)`. -/
theorem colXYv_injective : Function.Injective I.colXYv := by
  intro v v' h
  have h1 := I.k_le_K v
  have h2 := I.k_le_K v'
  exact I.k_injective (by unfold colXYv at h; omega)

/-- (iii)(b) Distinct vertices of `U` have distinct columns `col_yz(u)`. -/
theorem colYZu_injective : Function.Injective I.colYZu := by
  intro u u' h
  have h1 := I.i_le_K u
  have h2 := I.i_le_K u'
  exact I.i_injective (by unfold colYZu at h; omega)

/-! #### The collision patterns -/

/-- (iv)(a) The triples in the column `K` are exactly the incident triples `(u_e, e, v_e)`. -/
theorem colOuter_eq_K_iff (u : U) (e : E) (v : V) :
    I.colOuter u e v = K ↔ u = H.left e ∧ v = H.right e := by
  have h := I.colOuter_eq_iff u e v (H.left e) e (H.right e)
  rw [I.incident_col e] at h
  rw [colOuter, h, sub_self, sub_self, sub_eq_zero, sub_eq_zero, Nat.cast_inj, Nat.cast_inj,
    I.i_injective.eq_iff, I.k_injective.eq_iff]

/-- (iii)(a) The pairs `(u, e)` in the column `col_xy(v)` are exactly the incident pairs
`(u_e, e)` with `e ∈ E(v)`. -/
theorem colXY_eq_colXYv_iff (u : U) (e : E) (v : V) :
    I.colXY u e = I.colXYv v ↔ u = H.left e ∧ H.right e = v := by
  have hK := I.k_le_K v
  have h := I.colOuter_eq_K_iff u e v
  rw [colOuter_eq] at h
  constructor
  · intro hc
    have : I.colOuter u e v = K := by rw [colOuter_eq, hc]; unfold colXYv; omega
    obtain ⟨h1, h2⟩ := (I.colOuter_eq_K_iff u e v).mp this
    exact ⟨h1, h2.symm⟩
  · rintro ⟨h1, h2⟩
    have := h.mpr ⟨h1, h2.symm⟩
    unfold colXYv
    omega

/-- (iii)(a) The incident pair `(u_e, e)` lies in the column `col_xy(v_e)`. -/
theorem colXY_incident (e : E) : I.colXY (H.left e) e = I.colXYv (H.right e) :=
  (I.colXY_eq_colXYv_iff _ _ _).mpr ⟨rfl, rfl⟩

/-- (iii)(b) The pairs `(e, v)` in the column `col_yz(u)` are exactly the incident pairs
`(e, v_e)` with `e ∈ E(u)`. -/
theorem colYZ_eq_colYZu_iff (e : E) (v : V) (u : U) :
    I.colYZ e v = I.colYZu u ↔ v = H.right e ∧ H.left e = u := by
  have hK := I.i_le_K u
  have h := I.colOuter_eq_K_iff u e v
  rw [colOuter_eq'] at h
  constructor
  · intro hc
    have : I.colOuter u e v = K := by rw [colOuter_eq', hc]; unfold colYZu; omega
    obtain ⟨h1, h2⟩ := (I.colOuter_eq_K_iff u e v).mp this
    exact ⟨h2, h1.symm⟩
  · rintro ⟨h1, h2⟩
    have := h.mpr ⟨h2.symm, h1⟩
    unfold colYZu
    omega

/-- (iii)(b) The incident pair `(e, v_e)` lies in the column `col_yz(u_e)`. -/
theorem colYZ_incident (e : E) : I.colYZ e (H.right e) = I.colYZu (H.left e) :=
  (I.colYZ_eq_colYZu_iff _ _ _).mpr ⟨rfl, rfl⟩

/-- (iii)(a) A non-incident pair `(u, e)`, `u ≠ u_e`, occupies its own column. -/
theorem colXY_nonincident {u : U} {e : E} (hu : u ≠ H.left e) {u' : U} {e' : E}
    (h : I.colXY u e = I.colXY u' e') : u = u' ∧ e = e' := by
  have hc : I.colOuter u e (H.right e) = I.colOuter u' e' (H.right e) := by
    rw [colOuter_eq, colOuter_eq, h]
  obtain ⟨h1, h2⟩ := (I.colOuter_eq_iff _ _ _ _ _ _).mp hc
  have hre : H.right e = H.right e' := I.k_injective (by
    have := sub_eq_zero.mp (by linarith : (I.k (H.right e') : ℤ) - I.k (H.right e) = 0)
    exact_mod_cast this.symm)
  have hne : (I.i u : ℤ) - I.i (H.left e) ≠ 0 := by
    intro h0
    exact hu (I.i_injective (by exact_mod_cast sub_eq_zero.mp h0))
  obtain ⟨huu, hle⟩ := I.i_diff_unique u e u' e' h1 hne
  refine ⟨huu, I.j_injective ?_⟩
  have h3 := I.incident_col e
  have h4 := I.incident_col e'
  rw [hle, hre] at h3
  omega

/-- (iii)(b) A non-incident pair `(e, v)`, `v ≠ v_e`, occupies its own column. -/
theorem colYZ_nonincident {e : E} {v : V} (hv : v ≠ H.right e) {e' : E} {v' : V}
    (h : I.colYZ e v = I.colYZ e' v') : e = e' ∧ v = v' := by
  have hc : I.colOuter (H.left e) e v = I.colOuter (H.left e) e' v' := by
    rw [colOuter_eq', colOuter_eq', h]
  obtain ⟨h1, h2⟩ := (I.colOuter_eq_iff _ _ _ _ _ _).mp hc
  have hle : H.left e = H.left e' := I.i_injective (by
    have := sub_eq_zero.mp (by linarith : (I.i (H.left e') : ℤ) - I.i (H.left e) = 0)
    exact_mod_cast this.symm)
  have hne : (I.k v : ℤ) - I.k (H.right e) ≠ 0 := by
    intro h0
    exact hv (I.k_injective (by exact_mod_cast sub_eq_zero.mp h0))
  obtain ⟨hvv, hre⟩ := I.k_diff_unique v e v' e' h2 hne
  refine ⟨I.j_injective ?_, hvv⟩
  have h3 := I.incident_col e
  have h4 := I.incident_col e'
  rw [hle, hre] at h3
  omega

end IndexMaps

/-! ### Construction of the index maps -/

/-- `R = 32m²`, the range of the Golomb ruler. -/
def indexR (m : ℕ) : ℕ := 32 * m ^ 2

/-- `B = 2R + 1`, the base of the two-digit encoding of difference pairs. -/
def indexB (m : ℕ) : ℕ := 2 * indexR m + 1

/-- `K = 2g(B+1)R`, the column of the incident triples. -/
def indexK (m g : ℕ) : ℕ := 2 * g * (indexB m + 1) * indexR m

/-- `n₀ = 4K`, the number of input bits used by the construction. -/
def indexN₀ (m g : ℕ) : ℕ := 4 * indexK m g

/-- `n₀ ≤ 16896 g m⁴`: the paper's `n₀ = O(m⁴ log m)` for `g = O(log m)`. -/
theorem indexN₀_le (m g : ℕ) (hm : 1 ≤ m) : indexN₀ m g ≤ 16896 * g * m ^ 4 := by
  unfold indexN₀ indexK indexB indexR
  have h : m ^ 2 ≤ m ^ 4 := Nat.pow_le_pow_right hm (by norm_num)
  nlinarith [Nat.mul_le_mul_left g h]

/-- **Construction of index maps.** For a simple bipartite graph with `|U| = m + 1` and
`|V| = m`, `m ≥ 1`, and any width `g ≥ 1`, index maps with the properties of Lemma
[lem:indices] exist for `K = 2g(B+1)R` and `n₀ = 4K`: with a directed Golomb ruler `s` and
injections of `U` and `V` into its marks, `i(u) = g s_u`, `k(v) = gB s_v` and
`j(e) = K - i(u_e) - k(v_e)`.

Paper: Lemma [lem:indices]. -/
theorem exists_indexMaps {U V E : Type*} [Fintype U] [Fintype V] (H : Bipartite U V E)
    (hs : H.IsSimple) {m : ℕ} (hm : 1 ≤ m) (hU : Fintype.card U = m + 1)
    (hV : Fintype.card V = m) {g : ℕ} (hg : 0 < g) :
    Nonempty (IndexMaps H g (indexK m g) (indexN₀ m g)) := by
  obtain ⟨s, hs_inj, hs_lt, hs_gol⟩ := exists_golombRuler m hm
  let σU : U ≃ Fin (m + 1) := Fintype.equivFinOfCardEq hU
  obtain ⟨σV⟩ : Nonempty (V ↪ Fin (m + 1)) :=
    Function.Embedding.nonempty_of_card_le (by rw [hV, Fintype.card_fin]; omega)
  -- the parameters
  set R := indexR m with hR
  set B := indexB m with hB
  set K := indexK m g with hK
  have hRpos : 0 < R := by
    rw [hR, indexR]
    have : 0 < m := hm
    positivity
  have hB' : B = 2 * R + 1 := rfl
  have hBpos : 0 < B := by rw [hB']; omega
  have hK' : K = 2 * g * (B + 1) * R := rfl
  have hn₀ : indexN₀ m g = 4 * K := rfl
  have hBZ : (B : ℤ) = 2 * (R : ℤ) + 1 := by rw [hB']; push_cast; ring
  -- the marks of the vertices
  let sU : U → ℕ := fun u => s (σU u)
  let sV : V → ℕ := fun v => s (σV v)
  have hsU_lt : ∀ u, sU u < R := fun u => hs_lt _
  have hsV_lt : ∀ v, sV v < R := fun v => hs_lt _
  have hsU_inj : Function.Injective sU := hs_inj.comp σU.injective
  have hsV_inj : Function.Injective sV := hs_inj.comp σV.injective
  have hdU : ∀ u u', |(sU u : ℤ) - sU u'| < R := fun u u' => by
    have h1 : (sU u : ℤ) < R := by exact_mod_cast hsU_lt u
    have h2 : (sU u' : ℤ) < R := by exact_mod_cast hsU_lt u'
    have h3 : (0 : ℤ) ≤ sU u := Nat.cast_nonneg _
    have h4 : (0 : ℤ) ≤ sU u' := Nat.cast_nonneg _
    rw [abs_lt]
    constructor <;> linarith
  -- the maps
  let i : U → ℕ := fun u => g * sU u
  let k : V → ℕ := fun v => g * B * sV v
  have hi_lt : ∀ u, i u < g * R := fun u => Nat.mul_lt_mul_of_pos_left (hsU_lt u) hg
  have hk_lt : ∀ v, k v < g * B * R := fun v =>
    Nat.mul_lt_mul_of_pos_left (hsV_lt v) (Nat.mul_pos hg hBpos)
  have hsum : g * R + g * B * R = g * (B + 1) * R := by ring
  have hK2 : g * (B + 1) * R + g * (B + 1) * R = K := by rw [hK']; ring
  have hik : ∀ u v, i u + k v < g * (B + 1) * R := fun u v => by
    have := hi_lt u
    have := hk_lt v
    omega
  let j : E → ℕ := fun e => K - (i (H.left e) + k (H.right e))
  have hj : ∀ e, i (H.left e) + k (H.right e) + j e = K := fun e =>
    Nat.add_sub_cancel' (by have := hik (H.left e) (H.right e); omega)
  have hj_le : ∀ e, j e ≤ K := fun e => Nat.sub_le _ _
  have hiZ : ∀ u, (i u : ℤ) = g * sU u := fun u => by simp [i]
  have hkZ : ∀ v, (k v : ℤ) = g * B * sV v := fun v => by simp [k]
  have hcol : ∀ u e v, ((i u + j e + k v : ℕ) : ℤ) =
      K + ((i u : ℤ) - i (H.left e)) + ((k v : ℤ) - k (H.right e)) := fun u e v => by
    have := hj e
    omega
  have hgZ : (g : ℤ) ≠ 0 := by positivity
  have hgBZ : (g : ℤ) * B ≠ 0 := by
    have : (0 : ℤ) < B := by rw [hBZ]; positivity
    positivity
  -- the difference pairs in terms of the marks
  have hdiffU : ∀ u u', (i u : ℤ) - i u' = g * ((sU u : ℤ) - sU u') := fun u u' => by
    rw [hiZ, hiZ]; ring
  have hdiffV : ∀ v v', (k v : ℤ) - k v' = g * B * ((sV v : ℤ) - sV v') := fun v v' => by
    rw [hkZ, hkZ]; ring
  refine ⟨⟨i, j, k, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- `i` injective
    intro u u' h
    exact hsU_inj (Nat.eq_of_mul_eq_mul_left hg h)
  · -- `j` injective
    intro e e' h
    have h1 := hj e
    have h2 := hj e'
    have h3 : i (H.left e) + k (H.right e) = i (H.left e') + k (H.right e') := by omega
    have h4 : ((sU (H.left e) : ℤ)) + (2 * R + 1) * (sV (H.right e)) =
        (sU (H.left e') : ℤ) + (2 * R + 1) * (sV (H.right e')) := by
      have h5 : ((i (H.left e) + k (H.right e) : ℕ) : ℤ) =
          ((i (H.left e') + k (H.right e') : ℕ) : ℤ) := by exact_mod_cast h3
      push_cast at h5
      rw [hiZ, hiZ, hkZ, hkZ, hBZ] at h5
      apply mul_left_cancel₀ hgZ
      linear_combination h5
    have h6 : (0 : ℤ) ≤ sU (H.left e) := Nat.cast_nonneg _
    obtain ⟨h7, h8⟩ := baseB_unique (R := R) (by
        have := hsU_lt (H.left e)
        rw [abs_lt]; constructor <;> [linarith; exact_mod_cast this]) (by
        have := hsU_lt (H.left e')
        have : (0 : ℤ) ≤ sU (H.left e') := Nat.cast_nonneg _
        rw [abs_lt]; constructor <;> [linarith; exact_mod_cast ‹sU (H.left e') < R›]) h4
    exact hs e e' (hsU_inj (by exact_mod_cast h7)) (hsV_inj (by exact_mod_cast h8))
  · -- `k` injective
    intro v v' h
    exact hsV_inj (Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hg hBpos) h)
  · -- `i u < n₀`
    intro u
    have := hi_lt u
    rw [hn₀]
    omega
  · -- `j e < n₀`
    intro e
    have := hj_le e
    have : 0 < K := by rw [hK']; positivity
    rw [hn₀]
    omega
  · -- `k v < n₀`
    intro v
    have := hk_lt v
    rw [hn₀]
    omega
  · -- `g ∣ i u`
    exact fun u => ⟨sU u, rfl⟩
  · -- `g ∣ j e`
    intro e
    refine Nat.dvd_sub ⟨2 * (B + 1) * R, by rw [hK']; ring⟩ (Nat.dvd_add ⟨sU _, rfl⟩ ?_)
    exact ⟨B * sV _, by simp only [k]; ring⟩
  · -- `g ∣ k v`
    exact fun v => ⟨B * sV v, by simp only [k]; ring⟩
  · -- `g ∣ K`
    exact ⟨2 * (B + 1) * R, by rw [hK']; ring⟩
  · -- `g ∣ n₀`
    exact ⟨8 * (B + 1) * R, by rw [hn₀, hK']; ring⟩
  · -- `i u + j e < n₀`
    intro u e
    have := hi_lt u
    have := hj_le e
    rw [hn₀]
    omega
  · -- `j e + k v < n₀`
    intro e v
    have := hk_lt v
    have := hj_le e
    rw [hn₀]
    omega
  · -- `i u + j e + k v < n₀`
    intro u e v
    have := hi_lt u
    have := hk_lt v
    have := hj_le e
    rw [hn₀]
    omega
  · -- `i u ≤ K`
    intro u
    have := hi_lt u
    omega
  · -- `k v ≤ K`
    intro v
    have := hk_lt v
    omega
  · -- `K < n₀`
    have : 0 < K := by rw [hK']; positivity
    rw [hn₀]
    omega
  · -- `K + i u < n₀`
    intro u
    have := hi_lt u
    have : 0 < K := by rw [hK']; positivity
    rw [hn₀]
    omega
  · -- `K + k v < n₀`
    intro v
    have := hk_lt v
    have : 0 < K := by rw [hK']; positivity
    rw [hn₀]
    omega
  · -- the incident triples lie in column `K`
    intro e
    have := hj e
    omega
  · -- the outer collision pattern
    intro u e v u' e' v'
    rw [← Nat.cast_inj (R := ℤ), hcol, hcol, hdiffU, hdiffU, hdiffV, hdiffV]
    constructor
    · intro h
      have h4 : ((sU u : ℤ) - sU (H.left e)) + (2 * R + 1) * ((sV v : ℤ) - sV (H.right e)) =
          ((sU u' : ℤ) - sU (H.left e')) +
            (2 * R + 1) * ((sV v' : ℤ) - sV (H.right e')) := by
        rw [← hBZ]
        apply mul_left_cancel₀ hgZ
        linear_combination h
      obtain ⟨h5, h6⟩ := baseB_unique (R := R) (hdU _ _) (hdU _ _) h4
      exact ⟨by rw [h5], by rw [h6]⟩
    · rintro ⟨h1, h2⟩
      rw [h1, h2]
  · -- a nonzero `i`-difference determines its pair
    intro u e u' e' h hne
    rw [hdiffU, hdiffU] at h
    rw [hdiffU] at hne
    have h1 : (sU u : ℤ) - sU (H.left e) = sU u' - sU (H.left e') := mul_left_cancel₀ hgZ h
    have h2 : (sU u : ℤ) - sU (H.left e) ≠ 0 := by
      intro h0
      exact hne (by rw [h0, mul_zero])
    obtain ⟨h3, h4⟩ := hs_gol (σU u) (σU (H.left e)) (σU u') (σU (H.left e')) h1 h2
    exact ⟨σU.injective h3, σU.injective h4⟩
  · -- a nonzero `k`-difference determines its pair
    intro v e v' e' h hne
    rw [hdiffV, hdiffV] at h
    rw [hdiffV] at hne
    have h1 : (sV v : ℤ) - sV (H.right e) = sV v' - sV (H.right e') := mul_left_cancel₀ hgBZ h
    have h2 : (sV v : ℤ) - sV (H.right e) ≠ 0 := by
      intro h0
      exact hne (by rw [h0, mul_zero])
    obtain ⟨h3, h4⟩ := hs_gol (σV v) (σV (H.right e)) (σV v') (σV (H.right e')) h1 h2
    exact ⟨σV.injective h3, σV.injective h4⟩

end AssocLB
