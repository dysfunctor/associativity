/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/
import AssocLB.Reduction.Propagation

/-!
# Locality after restriction

Paper: Section 8 (Lower bound for `Assoc_n`): Definition [def:edge-star-local] (edge- and
star-local wires), Definition [def:support] (support of a restricted clause) and Lemma
[lem:locality] (locality): under `ρ`, every variable of `Assoc_n` computes a Boolean function
of the edge variables of a single star. Also the consequence, used in the proofs of Lemmas
[lem:reduction] and [lem:frege-transfer], that every restricted clause has a support of
constant size.

## Main definitions

* `StarLocalFn H w F`: the function `F` of edge assignments depends only on the edges of the
  star `E(w)`. A variable is constant, edge-local or star-local in the paper's sense exactly
  when its value function is star-local at some vertex (Definition [def:edge-star-local]).
* `Depends F e`, `deps F`: the edges `F` depends on, in the sense that flipping the edge
  changes the value for some assignment; `eq_of_agree_on_deps`: `F` is a function of `deps F`.
* `Assoc.valFn I M₁ M₂ q`: the value of the variable `q` under `ρ` as a function of the edge
  assignment, `β ↦ β̄ q`.
* `Assoc.supp I M₁ M₂ C`: the support of a clause, the endpoints of the edges its variables
  depend on (Definition [def:support]).

## Main results

* `MulEncoding.exists_starLocalFn_wire`: under a sparse restriction of a strip-local encoding,
  if the partial products of every strip are functions of a single star, so is every wire.
* `Assoc.exists_star_pp_xy`, `Assoc.exists_star_pp_yz`, `Assoc.exists_star_pp_outer`: under
  `ρ`, the partial products of every strip of the four multipliers are functions of a single
  star; for the outer multipliers, of the same star for both.
* `Assoc.exists_starLocalFn_valFn`: Lemma [lem:locality], every variable of `Assoc_n` is a
  function of a single star under `ρ`.
* `Assoc.card_supp_le`: the support of a clause `C` has at most `2Δ|C|` vertices.

## Design notes

* The paper distinguishes constant, edge-local and star-local wires; here all three are
  instances of `StarLocalFn` (a constant is star-local at every vertex, an edge-local wire at
  either endpoint of its edge), which is what the reduction uses.
* The output bits of the outer multipliers are read off the strip counts
  (`MulEncoding.fn_out_eq_testBit_ppCount`) rather than strip-locality, since the abstract
  Definition [def:strip-local] does not tie an output bit to the strip containing its column;
  this is what makes the miter variables star-local.
-/

namespace AssocLB

/-! ### Functions of a single star -/

section StarLocalFn

variable {U V E : Type*} (H : Bipartite U V E) [Fintype E] [DecidableEq U] [DecidableEq V]

/-- `F` depends only on the edges of the star `E(w)`: assignments agreeing on `E(w)` give the
same value.

Paper: Definition [def:edge-star-local]. -/
def StarLocalFn (w : U ⊕ V) {α : Type*} (F : (E → Bool) → α) : Prop :=
  ∀ β β' : E → Bool, (∀ e ∈ H.star w, β e = β' e) → F β = F β'

variable {H}

theorem StarLocalFn.const (w : U ⊕ V) {α : Type*} (a : α) :
    StarLocalFn H w (fun _ : E → Bool => a) := fun _ _ _ => rfl

theorem StarLocalFn.comp {w : U ⊕ V} {α α' : Type*} {F : (E → Bool) → α} (f : α → α')
    (h : StarLocalFn H w F) : StarLocalFn H w (fun β => f (F β)) := fun β β' hβ => by
  dsimp only
  rw [h β β' hβ]

theorem StarLocalFn.comp₂ {w : U ⊕ V} {α α' α'' : Type*} {F : (E → Bool) → α}
    {G : (E → Bool) → α'} (f : α → α' → α'') (hF : StarLocalFn H w F) (hG : StarLocalFn H w G) :
    StarLocalFn H w (fun β => f (F β) (G β)) := fun β β' hβ => by
  dsimp only
  rw [hF β β' hβ, hG β β' hβ]

theorem StarLocalFn.congr {w : U ⊕ V} {α : Type*} {F G : (E → Bool) → α}
    (h : StarLocalFn H w F) (hFG : ∀ β, F β = G β) : StarLocalFn H w G := fun β β' hβ => by
  rw [← hFG, ← hFG]
  exact h β β' hβ

/-- The projection to an edge is a function of the star of its left endpoint. -/
theorem StarLocalFn.proj_left (e : E) : StarLocalFn H (Sum.inl (H.left e)) fun β => β e :=
  fun _ _ hβ => hβ e (H.mem_star_inl.mpr rfl)

/-- The projection to an edge is a function of the star of its right endpoint. -/
theorem StarLocalFn.proj_right (e : E) : StarLocalFn H (Sum.inr (H.right e)) fun β => β e :=
  fun _ _ hβ => hβ e (H.mem_star_inr.mpr rfl)

/-- The projection to an edge of the star `E(w)` is a function of that star. -/
theorem StarLocalFn.proj {w : U ⊕ V} {e : E} (he : e ∈ H.star w) :
    StarLocalFn H w fun β => β e :=
  fun _ _ hβ => hβ e he

end StarLocalFn

/-! ### Dependence on edges -/

section Depends

variable {E : Type*}

/-- `F` depends on the edge `e`: flipping `e` changes the value for some assignment. -/
def Depends [DecidableEq E] (F : (E → Bool) → Bool) (e : E) : Prop :=
  ∃ β : E → Bool, F (Function.update β e (!β e)) ≠ F β

open Classical in
/-- The edges `F` depends on. -/
noncomputable def deps [Fintype E] [DecidableEq E] (F : (E → Bool) → Bool) : Finset E :=
  Finset.univ.filter (Depends F)

open Classical in
theorem mem_deps [Fintype E] [DecidableEq E] {F : (E → Bool) → Bool} {e : E} :
    e ∈ deps F ↔ Depends F e := by
  unfold deps
  exact ⟨fun h => (Finset.mem_filter.mp h).2,
    fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩

/-- A function takes the same value on assignments agreeing on the edges it depends on. -/
theorem eq_of_agree_on_deps [Fintype E] [DecidableEq E] (F : (E → Bool) → Bool) :
    ∀ β β' : E → Bool, (∀ e ∈ deps F, β e = β' e) → F β = F β' := by
  suffices h : ∀ (k : ℕ) (β β' : E → Bool),
      (Finset.univ.filter fun e => β e ≠ β' e).card ≤ k →
      (∀ e ∈ deps F, β e = β' e) → F β = F β' from
    fun β β' hβ => h _ β β' le_rfl hβ
  intro k
  induction k with
  | zero =>
    intro β β' hcard _
    have hβ' : β = β' := by
      funext e
      by_contra hne
      have hmem : e ∈ Finset.univ.filter fun e => β e ≠ β' e :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
      have := Finset.card_pos.mpr ⟨e, hmem⟩
      omega
    rw [hβ']
  | succ k ih =>
    intro β β' hcard hβ
    by_cases hD : (Finset.univ.filter fun e => β e ≠ β' e) = ∅
    · have hβ' : β = β' := by
        funext e
        by_contra hne
        have hmem : e ∈ Finset.univ.filter fun e => β e ≠ β' e :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
        rw [hD] at hmem
        exact Finset.notMem_empty _ hmem
      rw [hβ']
    · obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hD
      have hne : β e ≠ β' e := (Finset.mem_filter.mp he).2
      have hnd : e ∉ deps F := fun h => hne (hβ e h)
      have hflip : ∀ γ : E → Bool, F (Function.update γ e (!γ e)) = F γ := by
        intro γ
        by_contra h
        exact hnd (mem_deps.mpr ⟨γ, h⟩)
      have h1 : F β = F (Function.update β e (β' e)) := by
        rw [show β' e = !β e from Bool.eq_not_iff.mpr hne.symm]
        exact (hflip β).symm
      have h2 : (Finset.univ.filter fun e' => Function.update β e (β' e) e' ≠ β' e').card ≤ k := by
        have hsub : (Finset.univ.filter fun e' => Function.update β e (β' e) e' ≠ β' e') ⊆
            (Finset.univ.filter fun e => β e ≠ β' e).erase e := by
          intro e' he'
          rw [Finset.mem_filter] at he'
          rw [Finset.mem_erase, Finset.mem_filter]
          have hne' : e' ≠ e := by
            rintro rfl
            exact he'.2 (Function.update_self _ _ _)
          rw [Function.update_of_ne hne'] at he'
          exact ⟨hne', Finset.mem_univ _, he'.2⟩
        have := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem he] at this
        omega
      rw [h1]
      refine ih _ β' h2 fun e' he' => ?_
      have hne' : e' ≠ e := fun h : e' = e => hnd (h ▸ he')
      rw [Function.update_of_ne hne']
      exact hβ e' he'

/-- A function of the star `E(w)` depends only on edges of `E(w)`. -/
theorem StarLocalFn.deps_subset {U V : Type*} [Fintype E] [DecidableEq E] [DecidableEq U]
    [DecidableEq V] {H : Bipartite U V E} {w : U ⊕ V} {F : (E → Bool) → Bool}
    (h : StarLocalFn H w F) : deps F ⊆ H.star w := by
  intro e he
  rw [mem_deps] at he
  obtain ⟨β, hβ⟩ := he
  by_contra hne
  apply hβ
  apply h
  intro e' he'
  have hne' : e' ≠ e := fun h : e' = e => hne (h ▸ he')
  rw [Function.update_of_ne hne']

end Depends

/-! ### Strips -/

/-- A column that is a multiple of `g` and lies in the strip `b` is the base column of the
strip. -/
theorem eq_of_inStrip_of_dvd {g : ℕ} (hg : 0 < g) {b c : ℕ} (h : InStrip g b c) (hc : g ∣ c) :
    c = b * g := by
  obtain ⟨a, rfl⟩ := hc
  obtain ⟨h1, h2⟩ := h
  rw [Nat.mul_comm g a] at h1 h2 ⊢
  have h3 : b ≤ a := Nat.le_of_mul_le_mul_right h1 hg
  have h4 : a < b + 1 := Nat.lt_of_mul_lt_mul_right h2
  have : a = b := by omega
  rw [this]

/-! ### Strip-locality transfers to stars -/

section Transfer

variable {U V E : Type*} {H : Bipartite U V E} [Fintype E] [DecidableEq U] [DecidableEq V]

/-- Under a sparse restriction of a strip-local encoding, if the partial products of every
strip are functions of a single star, so is every wire. -/
theorem MulEncoding.exists_starLocalFn_wire {N : ℕ} (M : MulEncoding N) (hM : M.WiresStripLocal)
    {g : ℕ} (hg : 1 ≤ g) {ρ : InputRestriction N} (hρ : ρ.IsSparse g)
    (X Y : (E → Bool) → Bits N) (hext : ∀ β, ρ.Extends (X β) (Y β))
    (hpp : ∀ b, ∃ w, ∀ i j : Fin N, InStrip g b (i + j) →
      StarLocalFn H w fun β => partialProduct (X β) (Y β) i j) (w : M.Wire) :
    ∃ w', StarLocalFn H w' fun β => M.fn w (X β) (Y β) := by
  obtain ⟨b, hb⟩ := hM g hg ρ hρ w
  obtain ⟨w', hw'⟩ := hpp b
  exact ⟨w', fun β β' hβ => hb (X β) (Y β) (X β') (Y β') (hext β) (hext β')
    fun i j hij => hw' i j hij β β' hβ⟩

/-- If the partial products of a column are functions of a single star, so is its count. -/
theorem starLocalFn_ppCount {N : ℕ} (X Y : (E → Bool) → Bits N) {w : U ⊕ V} {c : ℕ}
    (hpp : ∀ i j : Fin N, (i : ℕ) + j = c →
      StarLocalFn H w fun β => partialProduct (X β) (Y β) i j) :
    StarLocalFn H w fun β => ppCount (X β) (Y β) c := by
  intro β β' hβ
  unfold ppCount
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro p _
  constructor
  · rintro ⟨hc, hp⟩
    have h := hpp p.1 p.2 hc β β' hβ
    dsimp only at h
    exact ⟨hc, by rw [← h]; exact hp⟩
  · rintro ⟨hc, hp⟩
    have h := hpp p.1 p.2 hc β β' hβ
    dsimp only at h
    exact ⟨hc, by rw [h]; exact hp⟩

end Transfer

namespace Assoc

variable {U V E : Type*} {H : Bipartite U V E} {g K n₀ : ℕ} (I : IndexMaps H g K n₀)
  [Fintype U] [Fintype V] [Fintype E] [DecidableEq U] [DecidableEq V] {n : ℕ}
  (M₁ : MulEncoding n) (M₂ : MulEncoding (2 * n))

/-! ### The partial products of the inner multipliers -/

omit [Fintype V] in
/-- The partial product `x_i y_j` of `xy` is a function of the star `E(w)` provided every
edge `e` with `x_i = x_{i(u)}` and `y_j = y_{j(e)}` lies in `E(w)`. -/
theorem starLocalFn_pp_xy {w : U ⊕ V} {i j : Fin n}
    (h : ∀ u e, I.i u = i → I.j e = j → e ∈ H.star w) :
    StarLocalFn H w fun β => partialProduct (xBits I n) (yBits I n β) i j := by
  intro β β' hβ
  simp only [partialProduct]
  cases hx : xBits I n i with
  | false => rfl
  | true =>
    obtain ⟨u, hu⟩ := (xBits_eq_true_iff I i).mp hx
    simp only [Bool.true_and, yBits, decide_eq_decide]
    constructor
    · rintro ⟨e, he, hβe⟩
      exact ⟨e, he, by rw [← hβ e (h u e hu he)]; exact hβe⟩
    · rintro ⟨e, he, hβe⟩
      exact ⟨e, he, by rw [hβ e (h u e hu he)]; exact hβe⟩

omit [Fintype U] in
/-- The partial product `y_i z_j` of `yz` is a function of the star `E(w)` provided every
edge `e` with `y_i = y_{j(e)}` and `z_j = z_{k(v)}` lies in `E(w)`. -/
theorem starLocalFn_pp_yz {w : U ⊕ V} {i j : Fin n}
    (h : ∀ e v, I.j e = i → I.k v = j → e ∈ H.star w) :
    StarLocalFn H w fun β => partialProduct (yBits I n β) (zBits I n) i j := by
  intro β β' hβ
  simp only [partialProduct]
  cases hz : zBits I n j with
  | false => simp
  | true =>
    obtain ⟨v, hv⟩ := (zBits_eq_true_iff I j).mp hz
    simp only [Bool.and_true, yBits, decide_eq_decide]
    constructor
    · rintro ⟨e, he, hβe⟩
      exact ⟨e, he, by rw [← hβ e (h e v he hv)]; exact hβe⟩
    · rintro ⟨e, he, hβe⟩
      exact ⟨e, he, by rw [hβ e (h e v he hv)]; exact hβe⟩

omit [Fintype V] in
/-- The partial products of every strip of `xy` are functions of a single star: the star of
`v` for the strip at `col_xy(v)`, the star of `v_e` for the strip of a non-incident pair
`(u, e)`, and any star otherwise. -/
theorem exists_star_pp_xy [Nonempty V] (hg : 0 < g) (b : ℕ) :
    ∃ w, ∀ i j : Fin n, InStrip g b (i + j) →
      StarLocalFn H w fun β => partialProduct (xBits I n) (yBits I n β) i j := by
  by_cases hv : ∃ v, I.colXYv v = b * g
  · obtain ⟨v, hv⟩ := hv
    refine ⟨Sum.inr v, fun i j hij => starLocalFn_pp_xy I fun u e hu he => ?_⟩
    have hcol : I.colXY u e = b * g :=
      eq_of_inStrip_of_dvd hg (by change InStrip g b (I.i u + I.j e); rw [hu, he]; exact hij)
        (I.g_dvd_colXY u e)
    rw [← hv] at hcol
    exact H.mem_star_inr.mpr ((I.colXY_eq_colXYv_iff u e v).mp hcol).2
  · by_cases hne : ∃ u e, u ≠ H.left e ∧ I.colXY u e = b * g
    · obtain ⟨u₀, e₀, hne₀, hcol₀⟩ := hne
      refine ⟨Sum.inr (H.right e₀), fun i j hij => starLocalFn_pp_xy I fun u e hu he => ?_⟩
      have hcol : I.colXY u e = b * g :=
        eq_of_inStrip_of_dvd hg (by change InStrip g b (I.i u + I.j e); rw [hu, he]; exact hij)
          (I.g_dvd_colXY u e)
      obtain ⟨rfl, rfl⟩ := I.colXY_nonincident hne₀ (hcol₀.trans hcol.symm)
      exact H.mem_star_inr.mpr rfl
    · refine ⟨Sum.inr (Classical.arbitrary V),
        fun i j hij => starLocalFn_pp_xy I fun u e hu he => ?_⟩
      exfalso
      have hcol : I.colXY u e = b * g :=
        eq_of_inStrip_of_dvd hg (by change InStrip g b (I.i u + I.j e); rw [hu, he]; exact hij)
          (I.g_dvd_colXY u e)
      by_cases hue : u = H.left e
      · subst hue
        exact hv ⟨H.right e, (I.colXY_incident e).symm.trans hcol⟩
      · exact hne ⟨u, e, hue, hcol⟩

omit [Fintype U] in
/-- The partial products of every strip of `yz` are functions of a single star. -/
theorem exists_star_pp_yz [Nonempty U] (hg : 0 < g) (b : ℕ) :
    ∃ w, ∀ i j : Fin n, InStrip g b (i + j) →
      StarLocalFn H w fun β => partialProduct (yBits I n β) (zBits I n) i j := by
  by_cases hu : ∃ u, I.colYZu u = b * g
  · obtain ⟨u, hu⟩ := hu
    refine ⟨Sum.inl u, fun i j hij => starLocalFn_pp_yz I fun e v he hv => ?_⟩
    have hcol : I.colYZ e v = b * g :=
      eq_of_inStrip_of_dvd hg (by change InStrip g b (I.j e + I.k v); rw [he, hv]; exact hij)
        (I.g_dvd_colYZ e v)
    rw [← hu] at hcol
    exact H.mem_star_inl.mpr ((I.colYZ_eq_colYZu_iff e v u).mp hcol).2
  · by_cases hne : ∃ e v, v ≠ H.right e ∧ I.colYZ e v = b * g
    · obtain ⟨e₀, v₀, hne₀, hcol₀⟩ := hne
      refine ⟨Sum.inl (H.left e₀), fun i j hij => starLocalFn_pp_yz I fun e v he hv => ?_⟩
      have hcol : I.colYZ e v = b * g :=
        eq_of_inStrip_of_dvd hg (by change InStrip g b (I.j e + I.k v); rw [he, hv]; exact hij)
          (I.g_dvd_colYZ e v)
      obtain ⟨rfl, rfl⟩ := I.colYZ_nonincident hne₀ (hcol₀.trans hcol.symm)
      exact H.mem_star_inl.mpr rfl
    · refine ⟨Sum.inl (Classical.arbitrary U),
        fun i j hij => starLocalFn_pp_yz I fun e v he hv => ?_⟩
      exfalso
      have hcol : I.colYZ e v = b * g :=
        eq_of_inStrip_of_dvd hg (by change InStrip g b (I.j e + I.k v); rw [he, hv]; exact hij)
          (I.g_dvd_colYZ e v)
      by_cases hve : v = H.right e
      · subst hve
        exact hu ⟨H.left e, (I.colYZ_incident e).symm.trans hcol⟩
      · exact hne ⟨e, v, hve, hcol⟩

/-! ### The partial products of the outer multipliers -/

omit [Fintype V] [DecidableEq U] [DecidableEq V] in
/-- The column of a non-incident pair `(u, e)` of `xy` holds one partial product, `β e`. -/
theorem ppCount_xy_colXY_nonincident (β : E → Bool) (hn : n₀ ≤ n) {u : U} {e : E}
    (hue : u ≠ H.left e) :
    ppCount (xBits I n) (yBits I n β) (I.colXY u e) = (β e).toNat := by
  have hle := ppCount_xy_le_one I (n := n) β (c := I.colXY u e)
    fun v hv => hue ((I.colXY_eq_colXYv_iff u e v).mp hv.symm).1
  cases hβ : β e with
  | true =>
    refine le_antisymm hle ?_
    unfold ppCount
    refine Finset.card_pos.mpr ⟨(⟨I.i u, lt_of_lt_of_le (I.i_lt u) hn⟩,
      ⟨I.j e, lt_of_lt_of_le (I.j_lt e) hn⟩), ?_⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, rfl, ?_⟩
    simp only [partialProduct]
    rw [xBits_i I hn, yBits_j I hn, hβ]
    rfl
  | false =>
    unfold ppCount
    change _ = 0
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨-, hc, hpp⟩ := hp
    simp only [partialProduct, Bool.and_eq_true] at hpp
    obtain ⟨u', hu'⟩ := (xBits_eq_true_iff I _).mp hpp.1
    obtain ⟨e', he', hβ'⟩ := (yBits_eq_true_iff I β _).mp hpp.2
    have hcol : I.colXY u e = I.colXY u' e' := by
      change I.i u + I.j e = I.i u' + I.j e'
      rw [hu', he', hc]
      rfl
    obtain ⟨rfl, rfl⟩ := I.colXY_nonincident hue hcol
    rw [hβ] at hβ'
    exact Bool.false_ne_true hβ'

omit [Fintype U] [DecidableEq U] [DecidableEq V] in
/-- The column of a non-incident pair `(e, v)` of `yz` holds one partial product, `β e`. -/
theorem ppCount_yz_colYZ_nonincident (β : E → Bool) (hn : n₀ ≤ n) {e : E} {v : V}
    (hve : v ≠ H.right e) :
    ppCount (yBits I n β) (zBits I n) (I.colYZ e v) = (β e).toNat := by
  have hle := ppCount_yz_le_one I (n := n) β (c := I.colYZ e v)
    fun u hu => hve ((I.colYZ_eq_colYZu_iff e v u).mp hu.symm).1
  cases hβ : β e with
  | true =>
    refine le_antisymm hle ?_
    unfold ppCount
    refine Finset.card_pos.mpr ⟨(⟨I.j e, lt_of_lt_of_le (I.j_lt e) hn⟩,
      ⟨I.k v, lt_of_lt_of_le (I.k_lt v) hn⟩), ?_⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, rfl, ?_⟩
    simp only [partialProduct]
    rw [yBits_j I hn, zBits_k I hn, hβ]
    rfl
  | false =>
    unfold ppCount
    change _ = 0
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨-, hc, hpp⟩ := hp
    simp only [partialProduct, Bool.and_eq_true] at hpp
    obtain ⟨e', he', hβ'⟩ := (yBits_eq_true_iff I β _).mp hpp.1
    obtain ⟨v', hv'⟩ := (zBits_eq_true_iff I _).mp hpp.2
    have hcol : I.colYZ e v = I.colYZ e' v' := by
      change I.j e + I.k v = I.j e' + I.k v'
      rw [he', hv', hc]
      rfl
    obtain ⟨rfl, rfl⟩ := I.colYZ_nonincident hve hcol
    rw [hβ] at hβ'
    exact Bool.false_ne_true hβ'

/-- The output bit of `xy` at the column of a non-incident pair `(u, e)` is `β e`. -/
theorem xyOutBits_nonincident (hn : n₀ ≤ n) (hg : 1 ≤ g) (hsp : (inputXY I M₁ M₂).IsSparse g)
    (β : E → Bool) {u : U} {e : E} (hue : u ≠ H.left e) (c : Fin (2 * n))
    (hc : (c : ℕ) = I.colXY u e) : xyOutBits I M₁ β c = β e := by
  rw [xyOutBits_of_eq_none I M₁ β (by rw [hc]; exact I.xyOut_colXY_of_ne hue),
    fn_out_xy_eq I M₁ M₂ β hn hg hsp c, hc, Nat.div_mul_cancel (I.g_dvd_colXY u e),
    Nat.mod_eq_zero_of_dvd (I.g_dvd_colXY u e), ppCount_xy_colXY_nonincident I β hn hue,
    Nat.testBit_zero]
  cases β e <;> simp

/-- The output bit of `yz` at the column of a non-incident pair `(e, v)` is `β e`. -/
theorem yzOutBits_nonincident (hn : n₀ ≤ n) (hg : 1 ≤ g) (hsp : (inputYZ I M₁ M₂).IsSparse g)
    (β : E → Bool) {e : E} {v : V} (hve : v ≠ H.right e) (c : Fin (2 * n))
    (hc : (c : ℕ) = I.colYZ e v) : yzOutBits I M₁ β c = β e := by
  rw [yzOutBits_of_eq_none I M₁ β (by rw [hc]; exact I.yzOut_colYZ_of_ne hve),
    fn_out_yz_eq I M₁ M₂ β hn hg hsp c, hc, Nat.div_mul_cancel (I.g_dvd_colYZ e v),
    Nat.mod_eq_zero_of_dvd (I.g_dvd_colYZ e v), ppCount_yz_colYZ_nonincident I β hn hve,
    Nat.testBit_zero]
  cases β e <;> simp

/-- A partial product of `(xy)z` is a function of the star `E(w)` provided the edge of every
non-incident pair at its first factor lies in `E(w)`, when its second factor is a `1`. -/
theorem starLocalFn_pp_xy_z (hn : n₀ ≤ n) (hg : 1 ≤ g) (hsp : (inputXY I M₁ M₂).IsSparse g)
    {w : U ⊕ V} {c₁ c₂ : Fin (2 * n)}
    (h : Bits.zeroExtend (zBits I n) (2 * n) c₂ = true →
      ∀ u e, u ≠ H.left e → I.colXY u e = c₁ → e ∈ H.star w) :
    StarLocalFn H w fun β =>
      partialProduct (xyOutBits I M₁ β) (Bits.zeroExtend (zBits I n) (2 * n)) c₁ c₂ := by
  cases hz : Bits.zeroExtend (zBits I n) (2 * n) c₂ with
  | false => exact fun β β' _ => by simp [partialProduct, hz]
  | true =>
    cases hout : I.xyOut c₁ with
    | some b =>
      exact fun β β' _ => by
        simp only [partialProduct, xyOutBits_of_eq_some I M₁ β hout,
          xyOutBits_of_eq_some I M₁ β' hout]
    | none =>
      obtain ⟨-, u, e, hue, hcol⟩ := (I.xyOut_eq_none_iff c₁).mp hout
      intro β β' hβ
      simp only [partialProduct, xyOutBits_nonincident I M₁ M₂ hn hg hsp β hue c₁ hcol.symm,
        xyOutBits_nonincident I M₁ M₂ hn hg hsp β' hue c₁ hcol.symm,
        hβ e (h hz u e hue hcol)]

/-- A partial product of `x(yz)` is a function of the star `E(w)` provided the edge of every
non-incident pair at its second factor lies in `E(w)`, when its first factor is a `1`. -/
theorem starLocalFn_pp_x_yz (hn : n₀ ≤ n) (hg : 1 ≤ g) (hsp : (inputYZ I M₁ M₂).IsSparse g)
    {w : U ⊕ V} {c₁ c₂ : Fin (2 * n)}
    (h : Bits.zeroExtend (xBits I n) (2 * n) c₁ = true →
      ∀ e v, v ≠ H.right e → I.colYZ e v = c₂ → e ∈ H.star w) :
    StarLocalFn H w fun β =>
      partialProduct (Bits.zeroExtend (xBits I n) (2 * n)) (yzOutBits I M₁ β) c₁ c₂ := by
  cases hx : Bits.zeroExtend (xBits I n) (2 * n) c₁ with
  | false => exact fun β β' _ => by simp [partialProduct, hx]
  | true =>
    cases hout : I.yzOut c₂ with
    | some b =>
      exact fun β β' _ => by
        simp only [partialProduct, yzOutBits_of_eq_some I M₁ β hout,
          yzOutBits_of_eq_some I M₁ β' hout]
    | none =>
      obtain ⟨-, e, v, hve, hcol⟩ := (I.yzOut_eq_none_iff c₂).mp hout
      intro β β' hβ
      simp only [partialProduct, yzOutBits_nonincident I M₁ M₂ hn hg hsp β hve c₂ hcol.symm,
        yzOutBits_nonincident I M₁ M₂ hn hg hsp β' hve c₂ hcol.symm,
        hβ e (h hx e v hve hcol)]

/-- The partial products of every strip of the outer multipliers are functions of a single
star, the same for both multipliers: by the outer collision pattern, the non-constant partial
products in a strip come from edges of one star. -/
theorem exists_star_pp_outer [Nonempty V] (hn : n₀ ≤ n) (hg : 1 ≤ g)
    (hsp : (inputXY I M₁ M₂).IsSparse g) (hsp' : (inputYZ I M₁ M₂).IsSparse g) (b : ℕ) :
    ∃ w, (∀ c₁ c₂ : Fin (2 * n), InStrip g b (c₁ + c₂) → StarLocalFn H w fun β =>
        partialProduct (xyOutBits I M₁ β) (Bits.zeroExtend (zBits I n) (2 * n)) c₁ c₂) ∧
      ∀ c₁ c₂ : Fin (2 * n), InStrip g b (c₁ + c₂) → StarLocalFn H w fun β =>
        partialProduct (Bits.zeroExtend (xBits I n) (2 * n)) (yzOutBits I M₁ β) c₁ c₂ := by
  have key₁ : ∀ (c₁ c₂ : Fin (2 * n)), InStrip g b (c₁ + c₂) →
      Bits.zeroExtend (zBits I n) (2 * n) c₂ = true →
      ∀ u e, u ≠ H.left e → I.colXY u e = c₁ → ∃ v, I.colOuter u e v = b * g := by
    intro c₁ c₂ hij hz u e _ hcol
    simp only [Bits.zeroExtend] at hz
    split_ifs at hz with hlt
    obtain ⟨v, hv⟩ := (zBits_eq_true_iff I _).mp hz
    have hv' : I.k v = c₂ := hv
    refine ⟨v, eq_of_inStrip_of_dvd hg ?_ (I.g_dvd_colOuter u e v)⟩
    rw [I.colOuter_eq, hcol, hv']
    exact hij
  have key₂ : ∀ (c₁ c₂ : Fin (2 * n)), InStrip g b (c₁ + c₂) →
      Bits.zeroExtend (xBits I n) (2 * n) c₁ = true →
      ∀ e v, v ≠ H.right e → I.colYZ e v = c₂ → ∃ u, I.colOuter u e v = b * g := by
    intro c₁ c₂ hij hx e v _ hcol
    simp only [Bits.zeroExtend] at hx
    split_ifs at hx with hlt
    obtain ⟨u, hu⟩ := (xBits_eq_true_iff I _).mp hx
    have hu' : I.i u = c₁ := hu
    refine ⟨u, eq_of_inStrip_of_dvd hg ?_ (I.g_dvd_colOuter u e v)⟩
    rw [I.colOuter_eq', hcol, hu']
    exact hij
  by_cases h₁ : ∃ u e v, u ≠ H.left e ∧ I.colOuter u e v = b * g
  · obtain ⟨u₀, e₀, v₀, hu₀, hcol₀⟩ := h₁
    have hne : (I.i u₀ : ℤ) - I.i (H.left e₀) ≠ 0 := fun h =>
      hu₀ (I.i_injective (by exact_mod_cast sub_eq_zero.mp h))
    refine ⟨Sum.inl (H.left e₀),
      fun c₁ c₂ hij => starLocalFn_pp_xy_z I M₁ M₂ hn hg hsp fun hz u e hue hcol => ?_,
      fun c₁ c₂ hij => starLocalFn_pp_x_yz I M₁ M₂ hn hg hsp' fun hx e v hve hcol => ?_⟩
    · obtain ⟨v, hcol'⟩ := key₁ c₁ c₂ hij hz u e hue hcol
      obtain ⟨hd, -⟩ := (I.colOuter_eq_iff u₀ e₀ v₀ u e v).mp (hcol₀.trans hcol'.symm)
      obtain ⟨-, hle⟩ := I.i_diff_unique u₀ e₀ u e hd hne
      rw [hle]
      exact H.mem_star_inl.mpr rfl
    · obtain ⟨u, hcol'⟩ := key₂ c₁ c₂ hij hx e v hve hcol
      obtain ⟨hd, -⟩ := (I.colOuter_eq_iff u₀ e₀ v₀ u e v).mp (hcol₀.trans hcol'.symm)
      obtain ⟨-, hle⟩ := I.i_diff_unique u₀ e₀ u e hd hne
      rw [hle]
      exact H.mem_star_inl.mpr rfl
  · by_cases h₂ : ∃ u e v, v ≠ H.right e ∧ I.colOuter u e v = b * g
    · obtain ⟨u₀, e₀, v₀, hv₀, hcol₀⟩ := h₂
      have hne : (I.k v₀ : ℤ) - I.k (H.right e₀) ≠ 0 := fun h =>
        hv₀ (I.k_injective (by exact_mod_cast sub_eq_zero.mp h))
      refine ⟨Sum.inr (H.right e₀),
        fun c₁ c₂ hij => starLocalFn_pp_xy_z I M₁ M₂ hn hg hsp fun hz u e hue hcol => ?_,
        fun c₁ c₂ hij => starLocalFn_pp_x_yz I M₁ M₂ hn hg hsp' fun hx e v hve hcol => ?_⟩
      · exfalso
        obtain ⟨v, hcol'⟩ := key₁ c₁ c₂ hij hz u e hue hcol
        exact h₁ ⟨u, e, v, hue, hcol'⟩
      · obtain ⟨u, hcol'⟩ := key₂ c₁ c₂ hij hx e v hve hcol
        obtain ⟨-, hd⟩ := (I.colOuter_eq_iff u₀ e₀ v₀ u e v).mp (hcol₀.trans hcol'.symm)
        obtain ⟨-, hre⟩ := I.k_diff_unique v₀ e₀ v e hd hne
        rw [hre]
        exact H.mem_star_inr.mpr rfl
    · refine ⟨Sum.inr (Classical.arbitrary V),
        fun c₁ c₂ hij => starLocalFn_pp_xy_z I M₁ M₂ hn hg hsp fun hz u e hue hcol => ?_,
        fun c₁ c₂ hij => starLocalFn_pp_x_yz I M₁ M₂ hn hg hsp' fun hx e v hve hcol => ?_⟩
      · exfalso
        obtain ⟨v, hcol'⟩ := key₁ c₁ c₂ hij hz u e hue hcol
        exact h₁ ⟨u, e, v, hue, hcol'⟩
      · exfalso
        obtain ⟨u, hcol'⟩ := key₂ c₁ c₂ hij hx e v hve hcol
        exact h₂ ⟨u, e, v, hve, hcol'⟩

/-- The output bit of `(xy)z` at a column of the strip `b` is a function of the star of the
strip's partial products. -/
theorem starLocalFn_out_xy_z (hn : n₀ ≤ n) (hg : 1 ≤ g) (hsp : (inputXY_Z I M₁ M₂).IsSparse g)
    {b : ℕ} {w : U ⊕ V}
    (hw : ∀ c₁ c₂ : Fin (2 * n), InStrip g b (c₁ + c₂) → StarLocalFn H w fun β =>
      partialProduct (xyOutBits I M₁ β) (Bits.zeroExtend (zBits I n) (2 * n)) c₁ c₂)
    (c : Fin (2 * (2 * n))) (hc : (c : ℕ) / g = b) :
    StarLocalFn H w fun β =>
      M₂.fn (M₂.out c) (xyOutBits I M₁ β) (Bits.zeroExtend (zBits I n) (2 * n)) := by
  refine StarLocalFn.congr ?_ fun β => (fn_out_xy_z_eq I M₁ M₂ β hn hg hsp c).symm
  refine StarLocalFn.comp (fun N : ℕ => N.testBit (c % g)) ?_
  refine starLocalFn_ppCount (fun β => xyOutBits I M₁ β)
    (fun _ => Bits.zeroExtend (zBits I n) (2 * n)) fun c₁ c₂ hc' => hw c₁ c₂ ?_
  rw [hc', ← hc]
  exact (inStrip_iff hg).mpr (Nat.mul_div_cancel _ hg).symm

/-- The output bit of `x(yz)` at a column of the strip `b` is a function of the star of the
strip's partial products. -/
theorem starLocalFn_out_x_yz (hn : n₀ ≤ n) (hg : 1 ≤ g) (hsp : (inputX_YZ I M₁ M₂).IsSparse g)
    {b : ℕ} {w : U ⊕ V}
    (hw : ∀ c₁ c₂ : Fin (2 * n), InStrip g b (c₁ + c₂) → StarLocalFn H w fun β =>
      partialProduct (Bits.zeroExtend (xBits I n) (2 * n)) (yzOutBits I M₁ β) c₁ c₂)
    (c : Fin (2 * (2 * n))) (hc : (c : ℕ) / g = b) :
    StarLocalFn H w fun β =>
      M₂.fn (M₂.out c) (Bits.zeroExtend (xBits I n) (2 * n)) (yzOutBits I M₁ β) := by
  refine StarLocalFn.congr ?_ fun β => (fn_out_x_yz_eq I M₁ M₂ β hn hg hsp c).symm
  refine StarLocalFn.comp (fun N : ℕ => N.testBit (c % g)) ?_
  refine starLocalFn_ppCount (fun _ => Bits.zeroExtend (xBits I n) (2 * n))
    (fun β => yzOutBits I M₁ β) fun c₁ c₂ hc' => hw c₁ c₂ ?_
  rw [hc', ← hc]
  exact (inStrip_iff hg).mpr (Nat.mul_div_cancel _ hg).symm

/-! ### Lemma [lem:locality]: every variable is a function of a single star -/

/-- The value of the variable `q` under `ρ` as a function of the edge assignment: `β ↦ β̄ q`. -/
noncomputable def valFn (q : AssocVar n M₁.Wire M₂.Wire) : (E → Bool) → Bool :=
  fun β => propagate I M₁ M₂ β q

/-- **Lemma [lem:locality].** Under `ρ`, every variable of `Assoc_n` computes a Boolean
function of the edge variables of a single star. -/
theorem exists_starLocalFn_valFn [Nonempty U] [Nonempty V] (hM₁ : M₁.WiresStripLocal)
    (hM₂ : M₂.WiresStripLocal) (hn : n₀ ≤ n) (hg : 1 ≤ g) (hsp : (inputXY I M₁ M₂).IsSparse g)
    (hsp' : (inputYZ I M₁ M₂).IsSparse g) (hsp₁ : (inputXY_Z I M₁ M₂).IsSparse g)
    (hsp₂ : (inputX_YZ I M₁ M₂).IsSparse g) (q : AssocVar n M₁.Wire M₂.Wire) :
    ∃ w, StarLocalFn H w (valFn I M₁ M₂ q) := by
  cases q with
  | x i => exact ⟨Sum.inr (Classical.arbitrary V), StarLocalFn.const _ _⟩
  | y j =>
    by_cases hj : ∃ e, I.j e = j
    · obtain ⟨e, he⟩ := hj
      refine ⟨Sum.inr (H.right e), fun β β' hβ => ?_⟩
      simp only [valFn, propagate_y, yBits, decide_eq_decide]
      constructor
      · rintro ⟨e', he', hβ'⟩
        obtain rfl := I.j_injective (he'.trans he.symm)
        exact ⟨e', he', by rw [← hβ e' (H.mem_star_inr.mpr rfl)]; exact hβ'⟩
      · rintro ⟨e', he', hβ'⟩
        obtain rfl := I.j_injective (he'.trans he.symm)
        exact ⟨e', he', by rw [hβ e' (H.mem_star_inr.mpr rfl)]; exact hβ'⟩
    · refine ⟨Sum.inr (Classical.arbitrary V), fun β β' _ => ?_⟩
      simp only [valFn, propagate_y, yBits, decide_eq_decide]
      constructor <;> rintro ⟨e, he, -⟩ <;> exact absurd ⟨e, he⟩ hj
  | z k => exact ⟨Sum.inr (Classical.arbitrary V), StarLocalFn.const _ _⟩
  | xy w =>
    cases hrho : rho I M₁ M₂ (.xy w) with
    | some b =>
      exact ⟨Sum.inr (Classical.arbitrary V), fun β β' _ => by
        simp only [valFn, propagate, hrho, Option.getD_some]⟩
    | none =>
      obtain ⟨w', hw'⟩ := M₁.exists_starLocalFn_wire (H := H) hM₁ hg hsp (fun _ => xBits I n)
        (yBits I n) (fun β => extends_inputXY I M₁ M₂ β) (exists_star_pp_xy I hg) w
      exact ⟨w', fun β β' hβ => by
        simp only [valFn, propagate, hrho, Option.getD_none]
        exact hw' β β' hβ⟩
  | yz w =>
    cases hrho : rho I M₁ M₂ (.yz w) with
    | some b =>
      exact ⟨Sum.inr (Classical.arbitrary V), fun β β' _ => by
        simp only [valFn, propagate, hrho, Option.getD_some]⟩
    | none =>
      obtain ⟨w', hw'⟩ := M₁.exists_starLocalFn_wire (H := H) hM₁ hg hsp' (yBits I n)
        (fun _ => zBits I n) (fun β => extends_inputYZ I M₁ M₂ β) (exists_star_pp_yz I hg) w
      exact ⟨w', fun β β' hβ => by
        simp only [valFn, propagate, hrho, Option.getD_none]
        exact hw' β β' hβ⟩
  | xy_z w =>
    obtain ⟨w', hw'⟩ := M₂.exists_starLocalFn_wire (H := H) hM₂ hg hsp₁
      (fun β => xyOutBits I M₁ β) (fun _ => Bits.zeroExtend (zBits I n) (2 * n))
      (fun β => extends_inputXY_Z I M₁ M₂ β)
      (fun b => (exists_star_pp_outer I M₁ M₂ hn hg hsp hsp' b).imp fun _ h => h.1) w
    exact ⟨w', hw'⟩
  | x_yz w =>
    obtain ⟨w', hw'⟩ := M₂.exists_starLocalFn_wire (H := H) hM₂ hg hsp₂
      (fun _ => Bits.zeroExtend (xBits I n) (2 * n)) (fun β => yzOutBits I M₁ β)
      (fun β => extends_inputX_YZ I M₁ M₂ β)
      (fun b => (exists_star_pp_outer I M₁ M₂ hn hg hsp hsp' b).imp fun _ h => h.2) w
    exact ⟨w', hw'⟩
  | e i =>
    by_cases hi : (i : ℕ) = K
    · exact ⟨Sum.inr (Classical.arbitrary V), fun β β' _ => by
        simp only [valFn, propagate_e, if_pos hi]⟩
    · obtain ⟨w, h1, h2⟩ := exists_star_pp_outer I M₁ M₂ hn hg hsp hsp' ((i : ℕ) / g)
      refine ⟨w, fun β β' hβ => ?_⟩
      have h1' := starLocalFn_out_xy_z I M₁ M₂ hn hg hsp₁ h1 i rfl β β' hβ
      have h2' := starLocalFn_out_x_yz I M₁ M₂ hn hg hsp₂ h2 i rfl β β' hβ
      dsimp only at h1' h2'
      simp only [valFn, propagate_e, if_neg hi]
      rw [h1', h2']

/-! ### The support of a restricted clause -/

variable [DecidableEq E]

/-- The support of a clause: the endpoints of the edges its variables depend on.

Paper: Definition [def:support]. -/
noncomputable def supp (C : Clause (AssocVar n M₁.Wire M₂.Wire)) : Finset (U ⊕ V) :=
  C.vars.biUnion fun q => (deps (valFn I M₁ M₂ q)).biUnion H.ends

theorem mem_supp {C : Clause (AssocVar n M₁.Wire M₂.Wire)} {w : U ⊕ V} :
    w ∈ supp I M₁ M₂ C ↔ ∃ q ∈ C.vars, ∃ e ∈ deps (valFn I M₁ M₂ q), w ∈ H.ends e := by
  simp [supp]

/-- The endpoints of an edge a variable of `C` depends on lie in the support of `C`. -/
theorem mem_supp_of_depends {C : Clause (AssocVar n M₁.Wire M₂.Wire)}
    {q : AssocVar n M₁.Wire M₂.Wire} (hq : q ∈ C.vars) {e : E}
    (he : e ∈ deps (valFn I M₁ M₂ q)) :
    Sum.inl (H.left e) ∈ supp I M₁ M₂ C ∧ Sum.inr (H.right e) ∈ supp I M₁ M₂ C :=
  ⟨(mem_supp I M₁ M₂).mpr ⟨q, hq, e, he, by simp [Bipartite.ends]⟩,
    (mem_supp I M₁ M₂).mpr ⟨q, hq, e, he, by simp [Bipartite.ends]⟩⟩

/-- **The support has constant size.** If every variable is a function of a single star and
the maximum degree is at most `Δ`, then the support of `C` has at most `2Δ|C|` vertices.

Paper: the support bound in the proofs of Lemma [lem:reduction] and Lemma
[lem:frege-transfer], from Lemma [lem:locality] and the constant width of `C`. -/
theorem card_supp_le {Δ : ℕ} (hΔ : H.MaxDegreeLE Δ)
    (hloc : ∀ q, ∃ w, StarLocalFn H w (valFn I M₁ M₂ q))
    (C : Clause (AssocVar n M₁.Wire M₂.Wire)) : (supp I M₁ M₂ C).card ≤ 2 * Δ * C.card := by
  have hq : ∀ q, ((deps (valFn I M₁ M₂ q)).biUnion H.ends).card ≤ 2 * Δ := by
    intro q
    obtain ⟨w, hw⟩ := hloc q
    calc ((deps (valFn I M₁ M₂ q)).biUnion H.ends).card
        ≤ ∑ e ∈ deps (valFn I M₁ M₂ q), (H.ends e).card := Finset.card_biUnion_le
      _ ≤ ∑ _e ∈ deps (valFn I M₁ M₂ q), 2 := Finset.sum_le_sum fun e _ => Finset.card_le_two
      _ = (deps (valFn I M₁ M₂ q)).card * 2 := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ Δ * 2 :=
          Nat.mul_le_mul_right _ ((Finset.card_le_card hw.deps_subset).trans (hΔ w))
      _ = 2 * Δ := Nat.mul_comm _ _
  calc (supp I M₁ M₂ C).card
      ≤ ∑ q ∈ C.vars, ((deps (valFn I M₁ M₂ q)).biUnion H.ends).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _q ∈ C.vars, 2 * Δ := Finset.sum_le_sum fun q _ => hq q
    _ = C.vars.card * (2 * Δ) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ C.card * (2 * Δ) := Nat.mul_le_mul_right _ Finset.card_image_le
    _ = 2 * Δ * C.card := Nat.mul_comm _ _

end Assoc

end AssocLB
