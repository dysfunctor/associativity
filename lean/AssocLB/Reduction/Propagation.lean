/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/
import AssocLB.Reduction.Restriction

/-!
# The propagated assignment

Paper: Section 8 (Lower bound for `Assoc_n`): Definition [def:propagation] (propagated
assignment), Lemma [lem:inner-pm] (inner multipliers impose perfect matching), and the miter
case of the proof of Lemma [lem:local-soundness] (local soundness); and from Section 7.2,
Lemma [lem:rho-outer-outputs] (`ρ` forces disagreement), which the miter case cites.

## Main definitions

* `Assoc.xBits`, `Assoc.yBits`, `Assoc.zBits`: the input bit-vectors under `ρ` for an edge
  assignment `β`: `x` and `z` as fixed by `ρ`, and `y` with `y_{j(e)} = β e`.
* `Assoc.xyOutBits`, `Assoc.yzOutBits`: the output bits of the inner multipliers as inputs of
  the outer ones: the value fixed by `ρ` where there is one, the computed output bit otherwise.
* `Assoc.propagate I M₁ M₂ β`: the propagated assignment `β̄`, extending `ρ` and giving every
  other variable the value of its Boolean function at `β` (Definition [def:propagation]).

## Main results

* `Assoc.propagate_extends`: `β̄` extends `ρ`.
* `Assoc.sat_xy_z_copy`, `Assoc.sat_x_yz_copy`: `β̄` satisfies the outer multiplier copies.
* `Assoc.sat_xy_copy_of_exactOne`, `Assoc.sat_yz_copy_of_exactOne`: the forward direction of
  Lemma [lem:inner-pm], if `β` selects exactly one edge at every `v ∈ V` then `β̄` satisfies
  the inner copy `xy`, and symmetrically for `yz` and `U`.
* `Assoc.sat_restrict_xy_copy_iff`, `Assoc.sat_restrict_yz_copy_iff`: Lemma [lem:inner-pm],
  `β̄` satisfies the restricted inner copy `xy↾ρ` iff `β` selects exactly one edge at every
  `v ∈ V`, and `yz↾ρ` iff it selects exactly one edge at every `u ∈ U`.
* `Assoc.ppCount_xy_z_K`, `Assoc.ppCount_x_yz_K`, `Assoc.e_K_consistent`, `Assoc.sat_miter`:
  Lemma [lem:rho-outer-outputs] and the miter case of Lemma [lem:local-soundness], the strips
  at `K` of the outer multipliers output `|V|` and `|U|`, so `e_K = 1` is consistent with its
  defining clauses, and `β̄` satisfies the miter clauses.

## Design notes

* The paper defines `β̄` as extending `ρ` and setting each remaining variable to the value of
  its function. Here `β̄` is defined by evaluating the multipliers on the inputs determined by
  `ρ` and `β`, with the values of `ρ` overriding the inner multiplier outputs and the miter
  bit `e_K`; it extends `ρ` by construction, and the inner copies are satisfied exactly when
  the overrides agree with the computed outputs, which is Lemma [lem:inner-pm].
* The output bits are read off Observation [obs:strip-counts] in the form
  `MulEncoding.fn_out_eq_testBit_ppCount`; the hypotheses `n₀ ≤ n`, `1 ≤ g` and the sparsity
  of the induced input restrictions (Lemma [lem:rho-g-sparse]) are parameters.
-/

namespace AssocLB

variable {U V E : Type*} {H : Bipartite U V E} {g K n₀ : ℕ} (I : IndexMaps H g K n₀)

namespace Assoc

/-! ### The input bit-vectors under `ρ` -/

section XBits

variable [Fintype U]

/-- The bits of `x` under `ρ`: `1` at the positions `i(u)`, `0` elsewhere. -/
def xBits (n : ℕ) : Bits n := fun i => decide (∃ u, I.i u = i)

theorem xBits_eq_true_iff {n : ℕ} (i : Fin n) : xBits I n i = true ↔ ∃ u, I.i u = i := by
  simp [xBits]

theorem xBits_i {n : ℕ} (hn : n₀ ≤ n) (u : U) :
    xBits I n ⟨I.i u, lt_of_lt_of_le (I.i_lt u) hn⟩ = true :=
  (xBits_eq_true_iff I _).mpr ⟨u, rfl⟩

end XBits

section YBits

variable [Fintype E]

/-- The bits of `y` under `ρ` and the edge assignment `β`: `y_{j(e)} = β e`, `0` elsewhere. -/
def yBits (n : ℕ) (β : E → Bool) : Bits n := fun j => decide (∃ e, I.j e = j ∧ β e = true)

theorem yBits_eq_true_iff {n : ℕ} (β : E → Bool) (j : Fin n) :
    yBits I n β j = true ↔ ∃ e, I.j e = j ∧ β e = true := by
  simp [yBits]

theorem yBits_j {n : ℕ} (hn : n₀ ≤ n) (β : E → Bool) (e : E) :
    yBits I n β ⟨I.j e, lt_of_lt_of_le (I.j_lt e) hn⟩ = β e := by
  simp only [yBits, I.j_injective.eq_iff, exists_eq_left]
  cases β e <;> simp

end YBits

section ZBits

variable [Fintype V]

/-- The bits of `z` under `ρ`: `1` at the positions `k(v)`, `0` elsewhere. -/
def zBits (n : ℕ) : Bits n := fun k => decide (∃ v, I.k v = k)

theorem zBits_eq_true_iff {n : ℕ} (k : Fin n) : zBits I n k = true ↔ ∃ v, I.k v = k := by
  simp [zBits]

theorem zBits_k {n : ℕ} (hn : n₀ ≤ n) (v : V) :
    zBits I n ⟨I.k v, lt_of_lt_of_le (I.k_lt v) hn⟩ = true :=
  (zBits_eq_true_iff I _).mpr ⟨v, rfl⟩

end ZBits

section Propagation

variable [Fintype U] [Fintype V] [Fintype E] [DecidableEq U] [DecidableEq V] {n : ℕ}
  (M₁ : MulEncoding n) (M₂ : MulEncoding (2 * n)) (β : E → Bool)

/-- The input bit-vectors of `xy` extend the restriction of its inputs induced by `ρ`. -/
theorem extends_inputXY : (inputXY I M₁ M₂).Extends (xBits I n) (yBits I n β) := by
  refine ⟨fun i b hb => ?_, fun j b hb => ?_⟩
  · rw [inputXY_x] at hb
    simp only [IndexMaps.xIn, Option.some.injEq] at hb
    exact hb
  · rw [inputXY_y] at hb
    cases b with
    | true => exact absurd hb (I.yIn_ne_some_true j)
    | false =>
      have h := (I.yIn_eq_some_false_iff j).mp hb
      simp only [yBits, decide_eq_false_iff_not, not_exists, not_and]
      exact fun e he _ => h ⟨e, he⟩

/-- The input bit-vectors of `yz` extend the restriction of its inputs induced by `ρ`. -/
theorem extends_inputYZ : (inputYZ I M₁ M₂).Extends (yBits I n β) (zBits I n) := by
  refine ⟨fun i b hb => ?_, fun k b hb => ?_⟩
  · rw [inputYZ_x] at hb
    cases b with
    | true => exact absurd hb (I.yIn_ne_some_true i)
    | false =>
      have h := (I.yIn_eq_some_false_iff i).mp hb
      simp only [yBits, decide_eq_false_iff_not, not_exists, not_and]
      exact fun e he _ => h ⟨e, he⟩
  · rw [inputYZ_y] at hb
    simp only [IndexMaps.zIn, Option.some.injEq] at hb
    exact hb

/-- The output bits of `xy` as inputs of `(xy)z`: the value fixed by `ρ` where there is one,
the computed output bit otherwise. -/
def xyOutBits : Bits (2 * n) := fun c =>
  (I.xyOut c).getD (M₁.fn (M₁.out c) (xBits I n) (yBits I n β))

/-- The output bits of `yz` as inputs of `x(yz)`: the value fixed by `ρ` where there is one,
the computed output bit otherwise. -/
def yzOutBits : Bits (2 * n) := fun c =>
  (I.yzOut c).getD (M₁.fn (M₁.out c) (yBits I n β) (zBits I n))

omit [DecidableEq V] in
theorem xyOutBits_of_eq_some {c : Fin (2 * n)} {b : Bool} (h : I.xyOut c = some b) :
    xyOutBits I M₁ β c = b := by
  simp [xyOutBits, h]

omit [DecidableEq V] in
theorem xyOutBits_of_eq_none {c : Fin (2 * n)} (h : I.xyOut c = none) :
    xyOutBits I M₁ β c = M₁.fn (M₁.out c) (xBits I n) (yBits I n β) := by
  simp [xyOutBits, h]

omit [DecidableEq U] in
theorem yzOutBits_of_eq_some {c : Fin (2 * n)} {b : Bool} (h : I.yzOut c = some b) :
    yzOutBits I M₁ β c = b := by
  simp [yzOutBits, h]

omit [DecidableEq U] in
theorem yzOutBits_of_eq_none {c : Fin (2 * n)} (h : I.yzOut c = none) :
    yzOutBits I M₁ β c = M₁.fn (M₁.out c) (yBits I n β) (zBits I n) := by
  simp [yzOutBits, h]

/-- The input bit-vectors of `(xy)z` extend the restriction of its inputs induced by `ρ`. -/
theorem extends_inputXY_Z :
    (inputXY_Z I M₁ M₂).Extends (xyOutBits I M₁ β) (Bits.zeroExtend (zBits I n) (2 * n)) := by
  refine ⟨fun c b hb => ?_, fun c b hb => ?_⟩
  · rw [inputXY_Z_x] at hb
    exact xyOutBits_of_eq_some I M₁ β hb
  · by_cases hc : (c : ℕ) < n
    · rw [inputXY_Z_y_of_lt I M₁ M₂ hc] at hb
      simp only [IndexMaps.zIn, Option.some.injEq] at hb
      simp only [Bits.zeroExtend, dif_pos hc]
      exact hb
    · rw [inputXY_Z_y_of_le I M₁ M₂ (not_lt.mp hc), Option.some.injEq] at hb
      simp only [Bits.zeroExtend, dif_neg hc]
      exact hb

/-- The input bit-vectors of `x(yz)` extend the restriction of its inputs induced by `ρ`. -/
theorem extends_inputX_YZ :
    (inputX_YZ I M₁ M₂).Extends (Bits.zeroExtend (xBits I n) (2 * n)) (yzOutBits I M₁ β) := by
  refine ⟨fun c b hb => ?_, fun c b hb => ?_⟩
  · by_cases hc : (c : ℕ) < n
    · rw [inputX_YZ_x_of_lt I M₁ M₂ hc] at hb
      simp only [IndexMaps.xIn, Option.some.injEq] at hb
      simp only [Bits.zeroExtend, dif_pos hc]
      exact hb
    · rw [inputX_YZ_x_of_le I M₁ M₂ (not_lt.mp hc), Option.some.injEq] at hb
      simp only [Bits.zeroExtend, dif_neg hc]
      exact hb
  · rw [inputX_YZ_y] at hb
    exact yzOutBits_of_eq_some I M₁ β hb

/-! ### The propagated assignment -/

/-- **The propagated assignment** `β̄` of an edge assignment `β`: the inputs `x`, `z` as fixed by
`ρ` and `y_{j(e)} = β e`; every wire of the inner multipliers takes the value fixed by `ρ` if
there is one and the value of its function otherwise; every wire of the outer multipliers takes
the value of its function of the inner outputs so determined; the miter bit `e_K` is `1` and
every other miter bit is the exclusive or of the outer outputs.

Paper: Definition [def:propagation]. -/
noncomputable def propagate : AssocVar n M₁.Wire M₂.Wire → Bool
  | .x i => xBits I n i
  | .y j => yBits I n β j
  | .z k => zBits I n k
  | .xy w => (rho I M₁ M₂ (.xy w)).getD (M₁.fn w (xBits I n) (yBits I n β))
  | .yz w => (rho I M₁ M₂ (.yz w)).getD (M₁.fn w (yBits I n β) (zBits I n))
  | .xy_z w => M₂.fn w (xyOutBits I M₁ β) (Bits.zeroExtend (zBits I n) (2 * n))
  | .x_yz w => M₂.fn w (Bits.zeroExtend (xBits I n) (2 * n)) (yzOutBits I M₁ β)
  | .e i => if (i : ℕ) = K then true else
      M₂.fn (M₂.out i) (xyOutBits I M₁ β) (Bits.zeroExtend (zBits I n) (2 * n)) ^^
        M₂.fn (M₂.out i) (Bits.zeroExtend (xBits I n) (2 * n)) (yzOutBits I M₁ β)

@[simp] theorem propagate_x (i : Fin n) : propagate I M₁ M₂ β (.x i) = xBits I n i := rfl

@[simp] theorem propagate_y (j : Fin n) : propagate I M₁ M₂ β (.y j) = yBits I n β j := rfl

@[simp] theorem propagate_z (k : Fin n) : propagate I M₁ M₂ β (.z k) = zBits I n k := rfl

@[simp] theorem propagate_xy_z (w : M₂.Wire) :
    propagate I M₁ M₂ β (.xy_z w) =
      M₂.fn w (xyOutBits I M₁ β) (Bits.zeroExtend (zBits I n) (2 * n)) := rfl

@[simp] theorem propagate_x_yz (w : M₂.Wire) :
    propagate I M₁ M₂ β (.x_yz w) =
      M₂.fn w (Bits.zeroExtend (xBits I n) (2 * n)) (yzOutBits I M₁ β) := rfl

theorem propagate_e (i : Fin (2 * (2 * n))) :
    propagate I M₁ M₂ β (.e i) = if (i : ℕ) = K then true else
      M₂.fn (M₂.out i) (xyOutBits I M₁ β) (Bits.zeroExtend (zBits I n) (2 * n)) ^^
        M₂.fn (M₂.out i) (Bits.zeroExtend (xBits I n) (2 * n)) (yzOutBits I M₁ β) := rfl

theorem propagate_xy_out (c : Fin (2 * n)) :
    propagate I M₁ M₂ β (.xy (M₁.out c)) = xyOutBits I M₁ β c := by
  simp only [propagate, rho_xy_out]
  rfl

theorem propagate_yz_out (c : Fin (2 * n)) :
    propagate I M₁ M₂ β (.yz (M₁.out c)) = yzOutBits I M₁ β c := by
  simp only [propagate, rho_yz_out]
  rfl

theorem propagate_xy_of_not_out {w : M₁.Wire} (hw : ∀ c, M₁.out c ≠ w) :
    propagate I M₁ M₂ β (.xy w) = M₁.fn w (xBits I n) (yBits I n β) := by
  simp only [propagate, rho_xy_of_not_out I M₁ M₂ hw, Option.getD_none]

theorem propagate_yz_of_not_out {w : M₁.Wire} (hw : ∀ c, M₁.out c ≠ w) :
    propagate I M₁ M₂ β (.yz w) = M₁.fn w (yBits I n β) (zBits I n) := by
  simp only [propagate, rho_yz_of_not_out I M₁ M₂ hw, Option.getD_none]

/-- `β̄` extends `ρ`. -/
theorem propagate_extends : (rho I M₁ M₂).Extends (propagate I M₁ M₂ β) := by
  intro v b hb
  cases v with
  | x i => exact (extends_inputXY I M₁ M₂ β).1 i b (by rw [inputXY_x]; exact hb)
  | y j => exact (extends_inputXY I M₁ M₂ β).2 j b (by rw [inputXY_y]; exact hb)
  | z k => exact (extends_inputYZ I M₁ M₂ β).2 k b (by rw [inputYZ_y]; exact hb)
  | xy w => simp only [propagate, hb, Option.getD_some]
  | yz w => simp only [propagate, hb, Option.getD_some]
  | xy_z w => exact absurd hb (by simp)
  | x_yz w => exact absurd hb (by simp)
  | e i =>
    rw [rho_e] at hb
    split_ifs at hb with hi
    simp only [Option.some.injEq] at hb
    simp only [propagate, if_pos hi]
    exact hb

/-! ### The four copies and the miter under `β̄` -/

/-- The copy `xy` is satisfied by `β̄` iff the output bits fixed by `ρ` agree with the
computed product. -/
theorem sat_xy_copy_iff :
    CNF.Sat (propagate I M₁ M₂ β) (M₁.cnf.subst (substXY M₁ M₂)) ↔
      ∀ (c : Fin (2 * n)) (b : Bool), I.xyOut c = some b →
        M₁.fn (M₁.out c) (xBits I n) (yBits I n β) = b := by
  rw [CNF.sat_subst_iff, M₁.sat_iff]
  have hx : (substXY M₁ M₂).pullback (propagate I M₁ M₂ β) ∘ MulVar.x = xBits I n := by
    rw [pullback_substXY_comp_x]
    rfl
  have hy : (substXY M₁ M₂).pullback (propagate I M₁ M₂ β) ∘ MulVar.y = yBits I n β := by
    rw [pullback_substXY_comp_y]
    rfl
  simp only [pullback_substXY_wire, hx, hy]
  constructor
  · intro h c b hb
    have := h (M₁.out c)
    rw [propagate_xy_out, xyOutBits_of_eq_some I M₁ β hb] at this
    exact this.symm
  · intro h w
    by_cases hw : ∃ c, M₁.out c = w
    · obtain ⟨c, rfl⟩ := hw
      rw [propagate_xy_out]
      cases hc : I.xyOut c with
      | none => exact xyOutBits_of_eq_none I M₁ β hc
      | some b =>
        rw [xyOutBits_of_eq_some I M₁ β hc]
        exact (h c b hc).symm
    · exact propagate_xy_of_not_out I M₁ M₂ β fun c hc => hw ⟨c, hc⟩

/-- The copy `yz` is satisfied by `β̄` iff the output bits fixed by `ρ` agree with the
computed product. -/
theorem sat_yz_copy_iff :
    CNF.Sat (propagate I M₁ M₂ β) (M₁.cnf.subst (substYZ M₁ M₂)) ↔
      ∀ (c : Fin (2 * n)) (b : Bool), I.yzOut c = some b →
        M₁.fn (M₁.out c) (yBits I n β) (zBits I n) = b := by
  rw [CNF.sat_subst_iff, M₁.sat_iff]
  have hx : (substYZ M₁ M₂).pullback (propagate I M₁ M₂ β) ∘ MulVar.x = yBits I n β := by
    rw [pullback_substYZ_comp_x]
    rfl
  have hy : (substYZ M₁ M₂).pullback (propagate I M₁ M₂ β) ∘ MulVar.y = zBits I n := by
    rw [pullback_substYZ_comp_y]
    rfl
  simp only [pullback_substYZ_wire, hx, hy]
  constructor
  · intro h c b hb
    have := h (M₁.out c)
    rw [propagate_yz_out, yzOutBits_of_eq_some I M₁ β hb] at this
    exact this.symm
  · intro h w
    by_cases hw : ∃ c, M₁.out c = w
    · obtain ⟨c, rfl⟩ := hw
      rw [propagate_yz_out]
      cases hc : I.yzOut c with
      | none => exact yzOutBits_of_eq_none I M₁ β hc
      | some b =>
        rw [yzOutBits_of_eq_some I M₁ β hc]
        exact (h c b hc).symm
    · exact propagate_yz_of_not_out I M₁ M₂ β fun c hc => hw ⟨c, hc⟩

/-- `β̄` satisfies the copy `(xy)z`: `ρ` assigns none of its wires. -/
theorem sat_xy_z_copy : CNF.Sat (propagate I M₁ M₂ β) (M₂.cnf.subst (substXY_Z M₁ M₂)) := by
  rw [CNF.sat_subst_iff, M₂.sat_iff]
  intro w
  rw [pullback_substXY_Z_wire, pullback_substXY_Z_comp_x, pullback_substXY_Z_comp_y]
  have h1 : (fun i => propagate I M₁ M₂ β (.xy (M₁.out i))) = xyOutBits I M₁ β :=
    funext fun i => propagate_xy_out I M₁ M₂ β i
  rw [h1]
  rfl

/-- `β̄` satisfies the copy `x(yz)`: `ρ` assigns none of its wires. -/
theorem sat_x_yz_copy : CNF.Sat (propagate I M₁ M₂ β) (M₂.cnf.subst (substX_YZ M₁ M₂)) := by
  rw [CNF.sat_subst_iff, M₂.sat_iff]
  intro w
  rw [pullback_substX_YZ_wire, pullback_substX_YZ_comp_x, pullback_substX_YZ_comp_y]
  have h1 : (fun i => propagate I M₁ M₂ β (.yz (M₁.out i))) = yzOutBits I M₁ β :=
    funext fun i => propagate_yz_out I M₁ M₂ β i
  rw [h1]
  rfl

/-- `β̄` satisfies the clauses defining the miter variables provided `e_K = 1` is consistent
with the outer outputs at column `K`. -/
theorem sat_miter_of_e_K
    (hK : ∀ i : Fin (2 * (2 * n)), (i : ℕ) = K →
      (M₂.fn (M₂.out i) (xyOutBits I M₁ β) (Bits.zeroExtend (zBits I n) (2 * n)) ^^
        M₂.fn (M₂.out i) (Bits.zeroExtend (xBits I n) (2 * n)) (yzOutBits I M₁ β)) = true) :
    CNF.Sat (propagate I M₁ M₂ β) (miter M₁ M₂) := by
  rw [sat_miter_iff]
  intro i
  simp only [propagate_xy_z, propagate_x_yz, propagate_e]
  split_ifs with hi
  · exact (hK i hi).symm
  · rfl

/-! ### Output bits as bits of strip counts -/

/-- Every output bit of `xy` under `β̄` is a bit of the count of its strip. -/
theorem fn_out_xy_eq (hn : n₀ ≤ n) (hg : 1 ≤ g) (hsp : (inputXY I M₁ M₂).IsSparse g)
    (c : Fin (2 * n)) :
    M₁.fn (M₁.out c) (xBits I n) (yBits I n β) =
      (ppCount (xBits I n) (yBits I n β) (c / g * g)).testBit (c % g) := by
  refine M₁.fn_out_eq_testBit_ppCount hg hsp (extends_inputXY I M₁ M₂ β) I.g_dvd_n₀ (by omega)
    (fun c' hc' => ?_) c
  obtain ⟨p, hp⟩ := hc'
  rw [InputRestriction.mem_liveInColumn, not_forcedZero_inputXY_iff] at hp
  obtain ⟨hc, ⟨u, hu⟩, ⟨e, he⟩⟩ := hp
  rw [← hc, ← hu, ← he]
  exact I.colXY_lt u e

/-- Every output bit of `yz` under `β̄` is a bit of the count of its strip. -/
theorem fn_out_yz_eq (hn : n₀ ≤ n) (hg : 1 ≤ g) (hsp : (inputYZ I M₁ M₂).IsSparse g)
    (c : Fin (2 * n)) :
    M₁.fn (M₁.out c) (yBits I n β) (zBits I n) =
      (ppCount (yBits I n β) (zBits I n) (c / g * g)).testBit (c % g) := by
  refine M₁.fn_out_eq_testBit_ppCount hg hsp (extends_inputYZ I M₁ M₂ β) I.g_dvd_n₀ (by omega)
    (fun c' hc' => ?_) c
  obtain ⟨p, hp⟩ := hc'
  rw [InputRestriction.mem_liveInColumn, not_forcedZero_inputYZ_iff] at hp
  obtain ⟨hc, ⟨e, he⟩, ⟨v, hv⟩⟩ := hp
  rw [← hc, ← he, ← hv]
  exact I.colYZ_lt e v

/-- Every output bit of `(xy)z` under `β̄` is a bit of the count of its strip. -/
theorem fn_out_xy_z_eq (hn : n₀ ≤ n) (hg : 1 ≤ g) (hsp : (inputXY_Z I M₁ M₂).IsSparse g)
    (c : Fin (2 * (2 * n))) :
    M₂.fn (M₂.out c) (xyOutBits I M₁ β) (Bits.zeroExtend (zBits I n) (2 * n)) =
      (ppCount (xyOutBits I M₁ β) (Bits.zeroExtend (zBits I n) (2 * n))
        (c / g * g)).testBit (c % g) := by
  refine M₂.fn_out_eq_testBit_ppCount hg hsp (extends_inputXY_Z I M₁ M₂ β) I.g_dvd_n₀
    (by omega) (fun c' hc' => ?_) c
  obtain ⟨p, hp⟩ := hc'
  rw [InputRestriction.mem_liveInColumn, not_forcedZero_inputXY_Z_iff] at hp
  obtain ⟨hc, h1, -, v, hv⟩ := hp
  rw [Ne, IndexMaps.xyOut_eq_some_false_iff, not_and_or, not_not, not_not] at h1
  rw [← hc, ← hv]
  rcases h1 with ⟨v', hv'⟩ | ⟨u, e, -, hue⟩
  · rw [← hv']
    exact lt_of_le_of_lt (Nat.add_le_add_right (I.colXYv_le v') _) (I.K_add_k_lt v)
  · rw [← hue]
    exact I.colOuter_lt u e v

/-- Every output bit of `x(yz)` under `β̄` is a bit of the count of its strip. -/
theorem fn_out_x_yz_eq (hn : n₀ ≤ n) (hg : 1 ≤ g) (hsp : (inputX_YZ I M₁ M₂).IsSparse g)
    (c : Fin (2 * (2 * n))) :
    M₂.fn (M₂.out c) (Bits.zeroExtend (xBits I n) (2 * n)) (yzOutBits I M₁ β) =
      (ppCount (Bits.zeroExtend (xBits I n) (2 * n)) (yzOutBits I M₁ β)
        (c / g * g)).testBit (c % g) := by
  refine M₂.fn_out_eq_testBit_ppCount hg hsp (extends_inputX_YZ I M₁ M₂ β) I.g_dvd_n₀
    (by omega) (fun c' hc' => ?_) c
  obtain ⟨p, hp⟩ := hc'
  rw [InputRestriction.mem_liveInColumn, not_forcedZero_inputX_YZ_iff] at hp
  obtain ⟨hc, ⟨-, u, hu⟩, h2⟩ := hp
  rw [Ne, IndexMaps.yzOut_eq_some_false_iff, not_and_or, not_not, not_not] at h2
  rw [← hc, ← hu]
  rcases h2 with ⟨u', hu'⟩ | ⟨e, v, -, hev⟩
  · rw [← hu']
    exact lt_of_le_of_lt (Nat.add_le_add_left (I.colYZu_le u') _)
      (by have := I.K_add_i_lt u; omega)
  · rw [← hev, ← I.colOuter_eq']
    exact I.colOuter_lt u e v

/-! ### The strip counts of the inner multipliers -/

omit [Fintype V] in
/-- The column `col_xy(v)` of `xy` holds one partial product `x_{i(u_e)} y_{j(e)} = β e` for
each edge `e ∈ E(v)`, so its count is the number of selected edges at `v`. -/
theorem ppCount_xy_colXYv (hn : n₀ ≤ n) (v : V) :
    ppCount (xBits I n) (yBits I n β) (I.colXYv v) =
      ((H.star (Sum.inr v)).filter fun e => β e = true).card := by
  unfold ppCount
  symm
  refine Finset.card_bij (fun e _ => (⟨I.i (H.left e), lt_of_lt_of_le (I.i_lt _) hn⟩,
    ⟨I.j e, lt_of_lt_of_le (I.j_lt _) hn⟩)) ?_ ?_ ?_
  · intro e he
    rw [Finset.mem_filter, H.mem_star_inr] at he
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · change I.i (H.left e) + I.j e = I.colXYv v
      rw [← he.1]
      exact I.colXY_incident e
    · simp only [partialProduct]
      rw [xBits_i I hn, yBits_j I hn, he.2]
      rfl
  · intro e _ e' _ h
    simp only [Prod.mk.injEq, Fin.mk.injEq] at h
    exact I.j_injective h.2
  · intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨-, hc, hpp⟩ := hp
    simp only [partialProduct, Bool.and_eq_true] at hpp
    obtain ⟨hx, hy⟩ := hpp
    obtain ⟨u, hu⟩ := (xBits_eq_true_iff I _).mp hx
    obtain ⟨e, he, hβe⟩ := (yBits_eq_true_iff I β _).mp hy
    have hcol : I.colXY u e = I.colXYv v := by
      change I.i u + I.j e = _
      rw [hu, he]
      exact hc
    obtain ⟨rfl, rfl⟩ := (I.colXY_eq_colXYv_iff u e v).mp hcol
    refine ⟨e, ?_, ?_⟩
    · rw [Finset.mem_filter, H.mem_star_inr]
      exact ⟨rfl, hβe⟩
    · exact Prod.ext (Fin.ext hu) (Fin.ext he)

omit [Fintype U] in
/-- The column `col_yz(u)` of `yz` holds one partial product `y_{j(e)} z_{k(v_e)} = β e` for
each edge `e ∈ E(u)`, so its count is the number of selected edges at `u`. -/
theorem ppCount_yz_colYZu (hn : n₀ ≤ n) (u : U) :
    ppCount (yBits I n β) (zBits I n) (I.colYZu u) =
      ((H.star (Sum.inl u)).filter fun e => β e = true).card := by
  unfold ppCount
  symm
  refine Finset.card_bij (fun e _ => (⟨I.j e, lt_of_lt_of_le (I.j_lt _) hn⟩,
    ⟨I.k (H.right e), lt_of_lt_of_le (I.k_lt _) hn⟩)) ?_ ?_ ?_
  · intro e he
    rw [Finset.mem_filter, H.mem_star_inl] at he
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · change I.j e + I.k (H.right e) = I.colYZu u
      rw [← he.1]
      exact I.colYZ_incident e
    · simp only [partialProduct]
      rw [yBits_j I hn, zBits_k I hn, he.2]
      rfl
  · intro e _ e' _ h
    simp only [Prod.mk.injEq, Fin.mk.injEq] at h
    exact I.j_injective h.1
  · intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨-, hc, hpp⟩ := hp
    simp only [partialProduct, Bool.and_eq_true] at hpp
    obtain ⟨hy, hz⟩ := hpp
    obtain ⟨e, he, hβe⟩ := (yBits_eq_true_iff I β _).mp hy
    obtain ⟨v, hv⟩ := (zBits_eq_true_iff I _).mp hz
    have hcol : I.colYZ e v = I.colYZu u := by
      change I.j e + I.k v = _
      rw [he, hv]
      exact hc
    obtain ⟨rfl, rfl⟩ := (I.colYZ_eq_colYZu_iff e v u).mp hcol
    refine ⟨e, ?_, ?_⟩
    · rw [Finset.mem_filter, H.mem_star_inl]
      exact ⟨rfl, hβe⟩
    · exact Prod.ext (Fin.ext he) (Fin.ext hv)

omit [Fintype V] [DecidableEq U] [DecidableEq V] in
/-- Every column of `xy` other than the columns `col_xy(v)` has count at most `1`. -/
theorem ppCount_xy_le_one {c : ℕ} (hc : ∀ v, I.colXYv v ≠ c) :
    ppCount (xBits I n) (yBits I n β) c ≤ 1 := by
  unfold ppCount
  refine Finset.card_le_one.mpr fun p hp p' hp' => ?_
  rw [Finset.mem_filter] at hp hp'
  obtain ⟨-, hpc, hpp⟩ := hp
  obtain ⟨-, hpc', hpp'⟩ := hp'
  simp only [partialProduct, Bool.and_eq_true] at hpp hpp'
  obtain ⟨u, hu⟩ := (xBits_eq_true_iff I _).mp hpp.1
  obtain ⟨e, he, -⟩ := (yBits_eq_true_iff I β _).mp hpp.2
  obtain ⟨u', hu'⟩ := (xBits_eq_true_iff I _).mp hpp'.1
  obtain ⟨e', he', -⟩ := (yBits_eq_true_iff I β _).mp hpp'.2
  have hu_ne : u ≠ H.left e := by
    rintro rfl
    refine hc (H.right e) ((I.colXY_incident e).symm.trans ?_)
    change I.i (H.left e) + I.j e = c
    rw [hu, he]
    exact hpc
  have hcol : I.colXY u e = I.colXY u' e' := by
    change I.i u + I.j e = I.i u' + I.j e'
    rw [hu, he, hu', he', hpc, hpc']
  obtain ⟨rfl, rfl⟩ := I.colXY_nonincident hu_ne hcol
  exact Prod.ext (Fin.ext (hu.symm.trans hu')) (Fin.ext (he.symm.trans he'))

omit [Fintype U] [DecidableEq U] [DecidableEq V] in
/-- Every column of `yz` other than the columns `col_yz(u)` has count at most `1`. -/
theorem ppCount_yz_le_one {c : ℕ} (hc : ∀ u, I.colYZu u ≠ c) :
    ppCount (yBits I n β) (zBits I n) c ≤ 1 := by
  unfold ppCount
  refine Finset.card_le_one.mpr fun p hp p' hp' => ?_
  rw [Finset.mem_filter] at hp hp'
  obtain ⟨-, hpc, hpp⟩ := hp
  obtain ⟨-, hpc', hpp'⟩ := hp'
  simp only [partialProduct, Bool.and_eq_true] at hpp hpp'
  obtain ⟨e, he, -⟩ := (yBits_eq_true_iff I β _).mp hpp.1
  obtain ⟨v, hv⟩ := (zBits_eq_true_iff I _).mp hpp.2
  obtain ⟨e', he', -⟩ := (yBits_eq_true_iff I β _).mp hpp'.1
  obtain ⟨v', hv'⟩ := (zBits_eq_true_iff I _).mp hpp'.2
  have hv_ne : v ≠ H.right e := by
    rintro rfl
    refine hc (H.left e) ((I.colYZ_incident e).symm.trans ?_)
    change I.j e + I.k (H.right e) = c
    rw [he, hv]
    exact hpc
  have hcol : I.colYZ e v = I.colYZ e' v' := by
    change I.j e + I.k v = I.j e' + I.k v'
    rw [he, hv, he', hv', hpc, hpc']
  obtain ⟨rfl, rfl⟩ := I.colYZ_nonincident hv_ne hcol
  exact Prod.ext (Fin.ext (he.symm.trans he')) (Fin.ext (hv.symm.trans hv'))

/-! ### Lemma [lem:inner-pm]: the inner multipliers impose the exact-one constraints

The forward direction, `sat_xy_copy_of_exactOne`, is what the inner-multiplier case of
Lemma [lem:local-soundness] uses. -/

/-- If `β` selects exactly one edge at every `v ∈ V`, then `β̄` satisfies the copy `xy`. -/
theorem sat_xy_copy_of_exactOne (hn : n₀ ≤ n) (hg : 1 ≤ g) (hsp : (inputXY I M₁ M₂).IsSparse g)
    (hβ : ∀ v, ((H.star (Sum.inr v)).filter fun e => β e = true).card = 1) :
    CNF.Sat (propagate I M₁ M₂ β) (M₁.cnf.subst (substXY M₁ M₂)) := by
  rw [sat_xy_copy_iff]
  intro c b hb
  rw [fn_out_xy_eq I M₁ M₂ β hn hg hsp c]
  by_cases hcb : (c : ℕ) = (c : ℕ) / g * g
  · -- `c` is the base of its strip
    have hcmod : (c : ℕ) % g = 0 := by
      rw [hcb]
      exact Nat.mul_mod_left _ _
    rw [hcmod]
    by_cases hv : ∃ v, I.colXYv v = (c : ℕ) / g * g
    · obtain ⟨v, hv⟩ := hv
      rw [← hv, ppCount_xy_colXYv I β hn v, hβ v]
      have hout : I.xyOut c = some true := by
        rw [hcb, ← hv]
        exact I.xyOut_colXYv v
      rw [hout, Option.some.injEq] at hb
      rw [← hb]
      simp
    · have hv' : ∀ v, I.colXYv v ≠ (c : ℕ) / g * g := fun v h => hv ⟨v, h⟩
      have hb' : b = false := by
        cases b with
        | false => rfl
        | true =>
          obtain ⟨v, hv⟩ := (I.xyOut_eq_some_true_iff c).mp hb
          exact absurd (hv.trans hcb) (hv' v)
      subst hb'
      have h0 : ppCount (xBits I n) (yBits I n β) ((c : ℕ) / g * g) = 0 := by
        refine Nat.eq_zero_of_le_zero
          ((ppCount_le_card_liveInColumn _ (extends_inputXY I M₁ M₂ β) _).trans (le_of_eq ?_))
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro p hp
        rw [InputRestriction.mem_liveInColumn, not_forcedZero_inputXY_iff] at hp
        obtain ⟨hc, ⟨u, hu⟩, ⟨e, he⟩⟩ := hp
        have hcol : I.colXY u e = (c : ℕ) / g * g := by
          change I.i u + I.j e = _
          rw [hu, he, hc]
        by_cases hue : u = H.left e
        · subst hue
          exact hv' (H.right e) ((I.colXY_incident e).symm.trans hcol)
        · have := I.xyOut_colXY_of_ne hue
          rw [hcol, ← hcb, hb] at this
          exact absurd this (by simp)
      rw [h0, Nat.zero_testBit]
  · -- `c` is not the base of its strip: a higher bit of a count at most `1`
    have hcmod : (c : ℕ) % g ≠ 0 := by
      intro h
      apply hcb
      have := Nat.div_add_mod (c : ℕ) g
      rw [h, Nat.add_zero, Nat.mul_comm] at this
      exact this.symm
    have hb' : b = false := by
      cases b with
      | false => rfl
      | true =>
        obtain ⟨v, hv⟩ := (I.xyOut_eq_some_true_iff c).mp hb
        refine absurd (Nat.mod_eq_zero_of_dvd ?_) hcmod
        rw [← hv]
        exact I.g_dvd_colXYv v
    subst hb'
    have hcnt : ppCount (xBits I n) (yBits I n β) ((c : ℕ) / g * g) ≤ 1 := by
      by_cases hv : ∃ v, I.colXYv v = (c : ℕ) / g * g
      · obtain ⟨v, hv⟩ := hv
        rw [← hv, ppCount_xy_colXYv I β hn v, hβ v]
      · exact ppCount_xy_le_one I β fun v h => hv ⟨v, h⟩
    apply Nat.testBit_eq_false_of_lt
    calc ppCount (xBits I n) (yBits I n β) ((c : ℕ) / g * g) ≤ 1 := hcnt
      _ < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ ((c : ℕ) % g) :=
          Nat.pow_le_pow_right two_pos (Nat.one_le_iff_ne_zero.mpr hcmod)

/-- If `β` selects exactly one edge at every `u ∈ U`, then `β̄` satisfies the copy `yz`. -/
theorem sat_yz_copy_of_exactOne (hn : n₀ ≤ n) (hg : 1 ≤ g) (hsp : (inputYZ I M₁ M₂).IsSparse g)
    (hβ : ∀ u, ((H.star (Sum.inl u)).filter fun e => β e = true).card = 1) :
    CNF.Sat (propagate I M₁ M₂ β) (M₁.cnf.subst (substYZ M₁ M₂)) := by
  rw [sat_yz_copy_iff]
  intro c b hb
  rw [fn_out_yz_eq I M₁ M₂ β hn hg hsp c]
  by_cases hcb : (c : ℕ) = (c : ℕ) / g * g
  · have hcmod : (c : ℕ) % g = 0 := by
      rw [hcb]
      exact Nat.mul_mod_left _ _
    rw [hcmod]
    by_cases hu : ∃ u, I.colYZu u = (c : ℕ) / g * g
    · obtain ⟨u, hu⟩ := hu
      rw [← hu, ppCount_yz_colYZu I β hn u, hβ u]
      have hout : I.yzOut c = some true := by
        rw [hcb, ← hu]
        exact I.yzOut_colYZu u
      rw [hout, Option.some.injEq] at hb
      rw [← hb]
      simp
    · have hu' : ∀ u, I.colYZu u ≠ (c : ℕ) / g * g := fun u h => hu ⟨u, h⟩
      have hb' : b = false := by
        cases b with
        | false => rfl
        | true =>
          obtain ⟨u, hu⟩ := (I.yzOut_eq_some_true_iff c).mp hb
          exact absurd (hu.trans hcb) (hu' u)
      subst hb'
      have h0 : ppCount (yBits I n β) (zBits I n) ((c : ℕ) / g * g) = 0 := by
        refine Nat.eq_zero_of_le_zero
          ((ppCount_le_card_liveInColumn _ (extends_inputYZ I M₁ M₂ β) _).trans (le_of_eq ?_))
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro p hp
        rw [InputRestriction.mem_liveInColumn, not_forcedZero_inputYZ_iff] at hp
        obtain ⟨hc, ⟨e, he⟩, ⟨v, hv⟩⟩ := hp
        have hcol : I.colYZ e v = (c : ℕ) / g * g := by
          change I.j e + I.k v = _
          rw [he, hv, hc]
        by_cases hve : v = H.right e
        · subst hve
          exact hu' (H.left e) ((I.colYZ_incident e).symm.trans hcol)
        · have := I.yzOut_colYZ_of_ne hve
          rw [hcol, ← hcb, hb] at this
          exact absurd this (by simp)
      rw [h0, Nat.zero_testBit]
  · have hcmod : (c : ℕ) % g ≠ 0 := by
      intro h
      apply hcb
      have := Nat.div_add_mod (c : ℕ) g
      rw [h, Nat.add_zero, Nat.mul_comm] at this
      exact this.symm
    have hb' : b = false := by
      cases b with
      | false => rfl
      | true =>
        obtain ⟨u, hu⟩ := (I.yzOut_eq_some_true_iff c).mp hb
        refine absurd (Nat.mod_eq_zero_of_dvd ?_) hcmod
        rw [← hu]
        exact I.g_dvd_colYZu u
    subst hb'
    have hcnt : ppCount (yBits I n β) (zBits I n) ((c : ℕ) / g * g) ≤ 1 := by
      by_cases hu : ∃ u, I.colYZu u = (c : ℕ) / g * g
      · obtain ⟨u, hu⟩ := hu
        rw [← hu, ppCount_yz_colYZu I β hn u, hβ u]
      · exact ppCount_yz_le_one I β fun u h => hu ⟨u, h⟩
    apply Nat.testBit_eq_false_of_lt
    calc ppCount (yBits I n β) (zBits I n) ((c : ℕ) / g * g) ≤ 1 := hcnt
      _ < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ ((c : ℕ) % g) :=
          Nat.pow_le_pow_right two_pos (Nat.one_le_iff_ne_zero.mpr hcmod)

/-- A number below `2^g` whose bit `0` is set and whose bits `1, …, g-1` are clear is `1`. -/
theorem eq_one_of_testBit {N g : ℕ} (hg : 1 ≤ g) (hN : N < 2 ^ g)
    (hbit : ∀ k, k < g → N.testBit k = decide (k = 0)) : N = 1 := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < g
  · rw [hbit k hk, Bool.eq_iff_iff, Nat.testBit_one_eq_true_iff_self_eq_zero, decide_eq_true_iff]
  · rw [Nat.testBit_eq_false_of_lt (hN.trans_le (Nat.pow_le_pow_right two_pos (not_lt.mp hk))),
      Nat.testBit_eq_false_of_lt]
    calc 1 < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right two_pos (by omega)

/-- If `β̄` satisfies the copy `xy`, then `β` selects exactly one edge at every `v ∈ V`. -/
theorem exactOne_of_sat_xy_copy (hn : n₀ ≤ n) (hg : 1 ≤ g) (hsp : (inputXY I M₁ M₂).IsSparse g)
    (h : CNF.Sat (propagate I M₁ M₂ β) (M₁.cnf.subst (substXY M₁ M₂))) (v : V) :
    ((H.star (Sum.inr v)).filter fun e => β e = true).card = 1 := by
  rw [sat_xy_copy_iff] at h
  rw [← ppCount_xy_colXYv I β hn v]
  refine eq_one_of_testBit hg (hsp.ppCount_lt (extends_inputXY I M₁ M₂ β) _) fun k hk => ?_
  obtain ⟨hstrip, hc1', hc2', hin⟩ :=
    I.strip_at_col hg (I.g_dvd_colXYv v) (I.colXYv_le v) hk
  let c : Fin (2 * n) := ⟨I.colXYv v + k, by omega⟩
  have hc1 : (c : ℕ) / g * g = I.colXYv v := hc1'
  have hc2 : (c : ℕ) % g = k := hc2'
  have hfn := fn_out_xy_eq I M₁ M₂ β hn hg hsp c
  rw [hc1, hc2] at hfn
  by_cases hk0 : k = 0
  · subst hk0
    have hout : I.xyOut c = some true := by
      change I.xyOut (I.colXYv v + 0) = some true
      rw [Nat.add_zero]
      exact I.xyOut_colXYv v
    rw [← hfn, h c true hout]
    rfl
  · have hout : I.xyOut c = some false := by
      refine I.xyOut_eq_some_false_of_inStrip (v := v) hg hin ?_
      change I.colXYv v + k ≠ I.colXYv v
      omega
    rw [← hfn, h c false hout]
    simp [hk0]

/-- If `β̄` satisfies the copy `yz`, then `β` selects exactly one edge at every `u ∈ U`. -/
theorem exactOne_of_sat_yz_copy (hn : n₀ ≤ n) (hg : 1 ≤ g) (hsp : (inputYZ I M₁ M₂).IsSparse g)
    (h : CNF.Sat (propagate I M₁ M₂ β) (M₁.cnf.subst (substYZ M₁ M₂))) (u : U) :
    ((H.star (Sum.inl u)).filter fun e => β e = true).card = 1 := by
  rw [sat_yz_copy_iff] at h
  rw [← ppCount_yz_colYZu I β hn u]
  refine eq_one_of_testBit hg (hsp.ppCount_lt (extends_inputYZ I M₁ M₂ β) _) fun k hk => ?_
  obtain ⟨hstrip, hc1', hc2', hin⟩ :=
    I.strip_at_col hg (I.g_dvd_colYZu u) (I.colYZu_le u) hk
  let c : Fin (2 * n) := ⟨I.colYZu u + k, by omega⟩
  have hc1 : (c : ℕ) / g * g = I.colYZu u := hc1'
  have hc2 : (c : ℕ) % g = k := hc2'
  have hfn := fn_out_yz_eq I M₁ M₂ β hn hg hsp c
  rw [hc1, hc2] at hfn
  by_cases hk0 : k = 0
  · subst hk0
    have hout : I.yzOut c = some true := by
      change I.yzOut (I.colYZu u + 0) = some true
      rw [Nat.add_zero]
      exact I.yzOut_colYZu u
    rw [← hfn, h c true hout]
    rfl
  · have hout : I.yzOut c = some false := by
      refine I.yzOut_eq_some_false_of_inStrip (u := u) hg hin ?_
      change I.colYZu u + k ≠ I.colYZu u
      omega
    rw [← hfn, h c false hout]
    simp [hk0]

/-- **Lemma [lem:inner-pm]** for `xy`: `β̄` satisfies `xy↾ρ` iff `β` selects exactly one edge
at every `v ∈ V`. -/
theorem sat_restrict_xy_copy_iff (hn : n₀ ≤ n) (hg : 1 ≤ g)
    (hsp : (inputXY I M₁ M₂).IsSparse g) :
    CNF.Sat (propagate I M₁ M₂ β) ((M₁.cnf.subst (substXY M₁ M₂)).restrict (rho I M₁ M₂)) ↔
      ∀ v, ((H.star (Sum.inr v)).filter fun e => β e = true).card = 1 := by
  rw [CNF.sat_restrict_iff_of_extends (propagate_extends I M₁ M₂ β)]
  exact ⟨exactOne_of_sat_xy_copy I M₁ M₂ β hn hg hsp,
    sat_xy_copy_of_exactOne I M₁ M₂ β hn hg hsp⟩

/-- **Lemma [lem:inner-pm]** for `yz`: `β̄` satisfies `yz↾ρ` iff `β` selects exactly one edge
at every `u ∈ U`. -/
theorem sat_restrict_yz_copy_iff (hn : n₀ ≤ n) (hg : 1 ≤ g)
    (hsp : (inputYZ I M₁ M₂).IsSparse g) :
    CNF.Sat (propagate I M₁ M₂ β) ((M₁.cnf.subst (substYZ M₁ M₂)).restrict (rho I M₁ M₂)) ↔
      ∀ u, ((H.star (Sum.inl u)).filter fun e => β e = true).card = 1 := by
  rw [CNF.sat_restrict_iff_of_extends (propagate_extends I M₁ M₂ β)]
  exact ⟨exactOne_of_sat_yz_copy I M₁ M₂ β hn hg hsp,
    sat_yz_copy_of_exactOne I M₁ M₂ β hn hg hsp⟩

/-! ### The outer strips at `K` and the miter bit `e_K`

Lemma [lem:rho-outer-outputs] (`ρ` forces disagreement) and the miter case of
Lemma [lem:local-soundness], which cites it. -/

omit [DecidableEq V] in
/-- The column `K` of `(xy)z` holds exactly one partial product evaluating to `1` for each
`v ∈ V`: the output bit of `xy` at `col_xy(v)`, fixed to `1`, times `z_{k(v)} = 1`. -/
theorem ppCount_xy_z_K (hn : n₀ ≤ n) :
    ppCount (xyOutBits I M₁ β) (Bits.zeroExtend (zBits I n) (2 * n)) K = Fintype.card V := by
  have h1 : ∀ v, I.colXYv v < 2 * n := fun v =>
    lt_of_le_of_lt (I.colXYv_le v) (by have := I.K_lt; omega)
  have h2 : ∀ v, I.k v < 2 * n := fun v => lt_of_lt_of_le (I.k_lt v) (by omega)
  unfold ppCount
  rw [← Finset.card_univ]
  symm
  refine Finset.card_bij (fun v _ => (⟨I.colXYv v, h1 v⟩, ⟨I.k v, h2 v⟩)) ?_ ?_ ?_
  · intro v _
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · change I.colXYv v + I.k v = K
      have := I.k_le_K v
      unfold IndexMaps.colXYv
      omega
    · simp only [partialProduct]
      rw [xyOutBits_of_eq_some I M₁ β (I.xyOut_colXYv v)]
      simp only [Bool.true_and, Bits.zeroExtend, dif_pos (lt_of_lt_of_le (I.k_lt v) hn)]
      exact zBits_k I hn v
  · intro v _ v' _ h
    simp only [Prod.mk.injEq, Fin.mk.injEq] at h
    exact I.k_injective h.2
  · intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨-, hc, hpp⟩ := hp
    simp only [partialProduct, Bool.and_eq_true] at hpp
    obtain ⟨-, hz⟩ := hpp
    simp only [Bits.zeroExtend] at hz
    split_ifs at hz with hlt
    obtain ⟨v, hv⟩ := (zBits_eq_true_iff I _).mp hz
    have hv' : I.k v = p.2 := hv
    refine ⟨v, Finset.mem_univ _, ?_⟩
    apply Prod.ext
    · apply Fin.ext
      change I.colXYv v = p.1
      unfold IndexMaps.colXYv
      omega
    · exact Fin.ext hv'

omit [DecidableEq U] in
/-- The column `K` of `x(yz)` holds exactly one partial product evaluating to `1` for each
`u ∈ U`: `x_{i(u)} = 1` times the output bit of `yz` at `col_yz(u)`, fixed to `1`. -/
theorem ppCount_x_yz_K (hn : n₀ ≤ n) :
    ppCount (Bits.zeroExtend (xBits I n) (2 * n)) (yzOutBits I M₁ β) K = Fintype.card U := by
  have h1 : ∀ u, I.i u < 2 * n := fun u => lt_of_lt_of_le (I.i_lt u) (by omega)
  have h2 : ∀ u, I.colYZu u < 2 * n := fun u =>
    lt_of_le_of_lt (I.colYZu_le u) (by have := I.K_lt; omega)
  unfold ppCount
  rw [← Finset.card_univ]
  symm
  refine Finset.card_bij (fun u _ => (⟨I.i u, h1 u⟩, ⟨I.colYZu u, h2 u⟩)) ?_ ?_ ?_
  · intro u _
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · change I.i u + I.colYZu u = K
      have := I.i_le_K u
      unfold IndexMaps.colYZu
      omega
    · simp only [partialProduct]
      rw [yzOutBits_of_eq_some I M₁ β (I.yzOut_colYZu u)]
      simp only [Bool.and_true, Bits.zeroExtend, dif_pos (lt_of_lt_of_le (I.i_lt u) hn)]
      exact xBits_i I hn u
  · intro u _ u' _ h
    simp only [Prod.mk.injEq, Fin.mk.injEq] at h
    exact I.i_injective h.1
  · intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨-, hc, hpp⟩ := hp
    simp only [partialProduct, Bool.and_eq_true] at hpp
    obtain ⟨hx, -⟩ := hpp
    simp only [Bits.zeroExtend] at hx
    split_ifs at hx with hlt
    obtain ⟨u, hu⟩ := (xBits_eq_true_iff I _).mp hx
    have hu' : I.i u = p.1 := hu
    refine ⟨u, Finset.mem_univ _, ?_⟩
    apply Prod.ext
    · exact Fin.ext hu'
    · apply Fin.ext
      change I.colYZu u = p.2
      unfold IndexMaps.colYZu
      omega

/-- **The miter bit `e_K` is consistent.** The outer outputs at column `K` are the low bits of
`|V|` and of `|U| = |V| + 1`, which differ, so `e_K = 1` is consistent with its defining clauses.

Paper: Lemma [lem:rho-outer-outputs] (`ρ` forces disagreement), as used in the miter case of
Lemma [lem:local-soundness]. -/
theorem e_K_consistent (hn : n₀ ≤ n) (hg : 1 ≤ g) (hsp₁ : (inputXY_Z I M₁ M₂).IsSparse g)
    (hsp₂ : (inputX_YZ I M₁ M₂).IsSparse g) (hcard : Fintype.card U = Fintype.card V + 1)
    (i : Fin (2 * (2 * n))) (hi : (i : ℕ) = K) :
    (M₂.fn (M₂.out i) (xyOutBits I M₁ β) (Bits.zeroExtend (zBits I n) (2 * n)) ^^
      M₂.fn (M₂.out i) (Bits.zeroExtend (xBits I n) (2 * n)) (yzOutBits I M₁ β)) = true := by
  rw [fn_out_xy_z_eq I M₁ M₂ β hn hg hsp₁, fn_out_x_yz_eq I M₁ M₂ β hn hg hsp₂, hi,
    Nat.div_mul_cancel I.g_dvd_K, Nat.mod_eq_zero_of_dvd I.g_dvd_K, ppCount_xy_z_K I M₁ β hn,
    ppCount_x_yz_K I M₁ β hn, hcard, Nat.testBit_zero, Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one (Fintype.card V) with h | h <;> simp [h, Nat.add_mod]

/-- `β̄` satisfies the clauses defining the miter variables. -/
theorem sat_miter (hn : n₀ ≤ n) (hg : 1 ≤ g) (hsp₁ : (inputXY_Z I M₁ M₂).IsSparse g)
    (hsp₂ : (inputX_YZ I M₁ M₂).IsSparse g) (hcard : Fintype.card U = Fintype.card V + 1) :
    CNF.Sat (propagate I M₁ M₂ β) (miter M₁ M₂) :=
  sat_miter_of_e_K I M₁ M₂ β fun i hi => e_K_consistent I M₁ M₂ β hn hg hsp₁ hsp₂ hcard i hi

end Propagation

end Assoc

end AssocLB
