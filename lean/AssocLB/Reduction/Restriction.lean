/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/
import AssocLB.Reduction.IndexMaps
import AssocLB.Multiplier.Assoc

/-!
# The restriction `ρ`

Paper: Section 7.2 (The restriction `ρ`): Definition [def:rho] and Lemma [lem:rho-g-sparse]
(`ρ` is a `g`-sparse restriction).

## Main definitions

* `IndexMaps.xIn`, `IndexMaps.yIn`, `IndexMaps.zIn`: the values of the input bits under `ρ`:
  `x_{i(u)} = 1`, `z_{k(v)} = 1`, `y_{j(e)}` unset, every other bit `0`
  (Definition [def:rho](a)).
* `IndexMaps.xyOut`, `IndexMaps.yzOut`: the values of the output bits of the inner
  multipliers: the strip at `col_xy(v)` outputs `1`, the bit at `col_xy(u, e)` of a
  non-incident pair is unset, every other bit is `0`; symmetrically for `yz`
  (Definition [def:rho](b)).
* `Assoc.rho I M₁ M₂`: the restriction `ρ` of `Assoc_n`, which also sets the miter bit
  `e_K = 1` (Definition [def:rho](c)) and leaves every other wire unset.
* `Assoc.inputXY`, `Assoc.inputYZ`, `Assoc.inputXY_Z`, `Assoc.inputX_YZ`: the restrictions
  of the input bit-vectors of the four multipliers induced by `ρ`, the pullbacks of `ρ` along
  the four substitutions of `Assoc` (`InputRestriction.ofRestriction`, `Restriction.comap`).

## Main results

* `Assoc.mem_liveInColumn_inputXY_colXYv`, `Assoc.card_liveInColumn_inputXY_le_one`, and the
  symmetric statements for `yz`: Lemma [lem:rho-g-sparse](i), the column `col_xy(v)` holds
  exactly the partial products `x_{i(u_e)} y_{j(e)}`, `e ∈ E(v)`, and every other column
  holds at most one partial product not forced to `0`.
* `Assoc.isSparse_inputXY`, `Assoc.isSparse_inputYZ`, `Assoc.isSparse_inputXY_Z`,
  `Assoc.isSparse_inputX_YZ`: Lemma [lem:rho-g-sparse](ii), for a simple graph with
  `|U|, |V| ≤ m + 1` and a width `g` with `m + 2 ≤ 2^(g-1)`.
* `IndexMaps.xyOut_eq_some_false_of_inStrip`: within the strip of `col_xy(v)`, the output
  bits other than the base are `0`, so the strip outputs `1` in binary.

## Design notes

* `ρ` is defined on `AssocVar n W₁ W₂` by cases; positions are compared as natural numbers,
  so the definition does not need `n₀ ≤ n`, which enters only when a position is used as an
  index of `Fin n`. The output-bit values are functions of the column, and `ρ` on a wire of
  an inner multiplier looks up whether the wire is an output bit (by choice; the output map
  is injective, so the column is unique, `Assoc.rho_xy_out`).
* The width `g` is a parameter; the paper's `g = ⌈log(m+2)⌉ + 2` (`stripWidth m`) satisfies
  `m + 2 ≤ 2^(g-1)` by `two_mul_le_two_pow_stripWidth`.
-/

namespace AssocLB

variable {U V E : Type*} {H : Bipartite U V E} {g K n₀ : ℕ} (I : IndexMaps H g K n₀)

namespace IndexMaps

/-! ### The values of the input bits -/

section X

variable [Fintype U]

/-- The value of `x_i` under `ρ`: `1` at the positions `i(u)`, `0` elsewhere.

Paper: Definition [def:rho](a). -/
def xIn (i : ℕ) : Option Bool := some (decide (∃ u, I.i u = i))

theorem xIn_eq_some_false_iff (i : ℕ) : I.xIn i = some false ↔ ¬ ∃ u, I.i u = i := by
  simp [xIn]

theorem xIn_eq_some_true_iff (i : ℕ) : I.xIn i = some true ↔ ∃ u, I.i u = i := by
  simp [xIn]

theorem xIn_ne_none (i : ℕ) : I.xIn i ≠ none := by
  simp [xIn]

end X

section Y

variable [Fintype E]

/-- The value of `y_j` under `ρ`: unset at the positions `j(e)`, `0` elsewhere.

Paper: Definition [def:rho](a). -/
def yIn (j : ℕ) : Option Bool := if ∃ e, I.j e = j then none else some false

theorem yIn_eq_none_iff (j : ℕ) : I.yIn j = none ↔ ∃ e, I.j e = j := by
  unfold yIn
  split_ifs with h <;> simp [h]

theorem yIn_eq_some_false_iff (j : ℕ) : I.yIn j = some false ↔ ¬ ∃ e, I.j e = j := by
  unfold yIn
  split_ifs with h <;> simp [h]

theorem yIn_ne_some_true (j : ℕ) : I.yIn j ≠ some true := by
  unfold yIn
  split_ifs <;> simp

end Y

section Z

variable [Fintype V]

/-- The value of `z_k` under `ρ`: `1` at the positions `k(v)`, `0` elsewhere.

Paper: Definition [def:rho](a). -/
def zIn (k : ℕ) : Option Bool := some (decide (∃ v, I.k v = k))

theorem zIn_eq_some_false_iff (k : ℕ) : I.zIn k = some false ↔ ¬ ∃ v, I.k v = k := by
  simp [zIn]

theorem zIn_eq_some_true_iff (k : ℕ) : I.zIn k = some true ↔ ∃ v, I.k v = k := by
  simp [zIn]

theorem zIn_ne_none (k : ℕ) : I.zIn k ≠ none := by
  simp [zIn]

end Z

/-! ### The values of the inner multiplier outputs -/

section XYOut

variable [Fintype U] [Fintype V] [Fintype E] [DecidableEq U]

/-- The value under `ρ` of the output bit of `xy` at column `c`: `1` at the base `col_xy(v)`
of the strip of a vertex `v ∈ V`, unset at the column `col_xy(u, e)` of a non-incident pair,
and `0` otherwise.

Paper: Definition [def:rho](b). -/
def xyOut (c : ℕ) : Option Bool :=
  if ∃ v, I.colXYv v = c then some true
  else if ∃ u e, u ≠ H.left e ∧ I.colXY u e = c then none
  else some false

theorem xyOut_eq_some_false_iff (c : ℕ) :
    I.xyOut c = some false ↔
      (¬ ∃ v, I.colXYv v = c) ∧ ¬ ∃ u e, u ≠ H.left e ∧ I.colXY u e = c := by
  unfold xyOut
  split_ifs with h1 h2 <;> simp [*]

theorem xyOut_eq_some_true_iff (c : ℕ) : I.xyOut c = some true ↔ ∃ v, I.colXYv v = c := by
  unfold xyOut
  split_ifs with h1 h2 <;> simp [*]

theorem xyOut_eq_none_iff (c : ℕ) :
    I.xyOut c = none ↔ (¬ ∃ v, I.colXYv v = c) ∧ ∃ u e, u ≠ H.left e ∧ I.colXY u e = c := by
  unfold xyOut
  split_ifs with h1 h2 <;> simp [*]

theorem xyOut_colXYv (v : V) : I.xyOut (I.colXYv v) = some true := by
  unfold xyOut
  rw [if_pos ⟨v, rfl⟩]

theorem xyOut_colXY_of_ne {u : U} {e : E} (hu : u ≠ H.left e) :
    I.xyOut (I.colXY u e) = none := by
  unfold xyOut
  rw [if_neg, if_pos ⟨u, e, hu, rfl⟩]
  rintro ⟨v, hv⟩
  exact hu ((I.colXY_eq_colXYv_iff u e v).mp hv.symm).1

/-- Every output bit of `xy` not set to `0` lies in a `g`-column. -/
theorem g_dvd_of_xyOut_ne {c : ℕ} (hc : I.xyOut c ≠ some false) : g ∣ c := by
  rw [Ne, xyOut_eq_some_false_iff, not_and_or, not_not, not_not] at hc
  rcases hc with ⟨v, rfl⟩ | ⟨u, e, -, rfl⟩
  · exact I.g_dvd_colXYv v
  · exact I.g_dvd_colXY u e

/-- Within the strip of `col_xy(v)`, the output bits of `xy` other than the base are `0`: the
strip outputs `1` in binary. -/
theorem xyOut_eq_some_false_of_inStrip (hg : 0 < g) {v : V} {c : ℕ}
    (hc : InStrip g (I.colXYv v / g) c) (hne : c ≠ I.colXYv v) : I.xyOut c = some false := by
  by_contra h
  apply hne
  obtain ⟨a, rfl⟩ := I.g_dvd_of_xyOut_ne h
  obtain ⟨b, hb⟩ := I.g_dvd_colXYv v
  rw [inStrip_iff hg, hb, Nat.mul_div_cancel_left _ hg, Nat.mul_div_cancel_left _ hg] at hc
  rw [hb, hc]

end XYOut

section YZOut

variable [Fintype U] [Fintype V] [Fintype E] [DecidableEq V]

/-- The value under `ρ` of the output bit of `yz` at column `c`: `1` at the base `col_yz(u)`
of the strip of a vertex `u ∈ U`, unset at the column `col_yz(e, v)` of a non-incident pair,
and `0` otherwise.

Paper: Definition [def:rho](b). -/
def yzOut (c : ℕ) : Option Bool :=
  if ∃ u, I.colYZu u = c then some true
  else if ∃ e v, v ≠ H.right e ∧ I.colYZ e v = c then none
  else some false

theorem yzOut_eq_some_false_iff (c : ℕ) :
    I.yzOut c = some false ↔
      (¬ ∃ u, I.colYZu u = c) ∧ ¬ ∃ e v, v ≠ H.right e ∧ I.colYZ e v = c := by
  unfold yzOut
  split_ifs with h1 h2 <;> simp [*]

theorem yzOut_eq_some_true_iff (c : ℕ) : I.yzOut c = some true ↔ ∃ u, I.colYZu u = c := by
  unfold yzOut
  split_ifs with h1 h2 <;> simp [*]

theorem yzOut_eq_none_iff (c : ℕ) :
    I.yzOut c = none ↔ (¬ ∃ u, I.colYZu u = c) ∧ ∃ e v, v ≠ H.right e ∧ I.colYZ e v = c := by
  unfold yzOut
  split_ifs with h1 h2 <;> simp [*]

theorem yzOut_colYZu (u : U) : I.yzOut (I.colYZu u) = some true := by
  unfold yzOut
  rw [if_pos ⟨u, rfl⟩]

theorem yzOut_colYZ_of_ne {e : E} {v : V} (hv : v ≠ H.right e) :
    I.yzOut (I.colYZ e v) = none := by
  unfold yzOut
  rw [if_neg, if_pos ⟨e, v, hv, rfl⟩]
  rintro ⟨u, hu⟩
  exact hv ((I.colYZ_eq_colYZu_iff e v u).mp hu.symm).1

/-- Every output bit of `yz` not set to `0` lies in a `g`-column. -/
theorem g_dvd_of_yzOut_ne {c : ℕ} (hc : I.yzOut c ≠ some false) : g ∣ c := by
  rw [Ne, yzOut_eq_some_false_iff, not_and_or, not_not, not_not] at hc
  rcases hc with ⟨u, rfl⟩ | ⟨e, v, -, rfl⟩
  · exact I.g_dvd_colYZu u
  · exact I.g_dvd_colYZ e v

/-- Within the strip of `col_yz(u)`, the output bits of `yz` other than the base are `0`: the
strip outputs `1` in binary. -/
theorem yzOut_eq_some_false_of_inStrip (hg : 0 < g) {u : U} {c : ℕ}
    (hc : InStrip g (I.colYZu u / g) c) (hne : c ≠ I.colYZu u) : I.yzOut c = some false := by
  by_contra h
  apply hne
  obtain ⟨a, rfl⟩ := I.g_dvd_of_yzOut_ne h
  obtain ⟨b, hb⟩ := I.g_dvd_colYZu u
  rw [inStrip_iff hg, hb, Nat.mul_div_cancel_left _ hg, Nat.mul_div_cancel_left _ hg] at hc
  rw [hb, hc]

end YZOut

end IndexMaps

/-! ### Restrictions of the inputs of an encoding -/

namespace InputRestriction

/-- The restriction of the input bit-vectors read off a restriction of the variables of an
encoding. -/
def ofRestriction {n : ℕ} {W : Type*} (ρ : Restriction (MulVar n W)) : InputRestriction n :=
  ⟨fun i => ρ (.x i), fun j => ρ (.y j)⟩

@[simp] theorem ofRestriction_x {n : ℕ} {W : Type*} (ρ : Restriction (MulVar n W))
    (i : Fin n) : (ofRestriction ρ).x i = ρ (.x i) := rfl

@[simp] theorem ofRestriction_y {n : ℕ} {W : Type*} (ρ : Restriction (MulVar n W))
    (j : Fin n) : (ofRestriction ρ).y j = ρ (.y j) := rfl

-- Sanity check: the inputs of an assignment extending `ρ` extend the input restriction read
-- off `ρ`.
example {n : ℕ} {W : Type*} {ρ : Restriction (MulVar n W)} {α : MulVar n W → Bool}
    (h : ρ.Extends α) : (ofRestriction ρ).Extends (α ∘ MulVar.x) (α ∘ MulVar.y) :=
  ⟨fun _ _ hb => h _ _ hb, fun _ _ hb => h _ _ hb⟩

end InputRestriction

namespace Assoc

variable [Fintype U] [Fintype V] [Fintype E] [DecidableEq U] [DecidableEq V]
  {n : ℕ} (M₁ : MulEncoding n) (M₂ : MulEncoding (2 * n))

/-! ### The restriction `ρ` -/

/-- The restriction `ρ` of `Assoc_n`: (a) the input bits `x_{i(u)} = 1`, `z_{k(v)} = 1`,
`y_{j(e)}` unset and every other input bit `0`; (b) the output bits of the inner multipliers
as in `IndexMaps.xyOut` and `IndexMaps.yzOut`; (c) the miter bit `e_K = 1`. Every other
variable is unset.

Paper: Definition [def:rho]. -/
noncomputable def rho : Restriction (AssocVar n M₁.Wire M₂.Wire)
  | .x i => I.xIn i
  | .y j => I.yIn j
  | .z k => I.zIn k
  | .xy w => if h : ∃ c, M₁.out c = w then I.xyOut h.choose else none
  | .yz w => if h : ∃ c, M₁.out c = w then I.yzOut h.choose else none
  | .xy_z _ => none
  | .x_yz _ => none
  | .e i => if (i : ℕ) = K then some true else none

@[simp] theorem rho_x (i : Fin n) : rho I M₁ M₂ (.x i) = I.xIn i := rfl

@[simp] theorem rho_y (j : Fin n) : rho I M₁ M₂ (.y j) = I.yIn j := rfl

@[simp] theorem rho_z (k : Fin n) : rho I M₁ M₂ (.z k) = I.zIn k := rfl

/-- `ρ` on the output bit of `xy` at column `c`. -/
theorem rho_xy_out (c : Fin (2 * n)) : rho I M₁ M₂ (.xy (M₁.out c)) = I.xyOut c := by
  have h : ∃ c', M₁.out c' = M₁.out c := ⟨c, rfl⟩
  simp only [rho, dif_pos h]
  rw [M₁.out_injective h.choose_spec]

/-- `ρ` on the output bit of `yz` at column `c`. -/
theorem rho_yz_out (c : Fin (2 * n)) : rho I M₁ M₂ (.yz (M₁.out c)) = I.yzOut c := by
  have h : ∃ c', M₁.out c' = M₁.out c := ⟨c, rfl⟩
  simp only [rho, dif_pos h]
  rw [M₁.out_injective h.choose_spec]

/-- `ρ` leaves the wires of `xy` other than the output bits unset. -/
theorem rho_xy_of_not_out {w : M₁.Wire} (hw : ∀ c, M₁.out c ≠ w) :
    rho I M₁ M₂ (.xy w) = none := by
  simp only [rho]
  rw [dif_neg]
  rintro ⟨c, hc⟩
  exact hw c hc

/-- `ρ` leaves the wires of `yz` other than the output bits unset. -/
theorem rho_yz_of_not_out {w : M₁.Wire} (hw : ∀ c, M₁.out c ≠ w) :
    rho I M₁ M₂ (.yz w) = none := by
  simp only [rho]
  rw [dif_neg]
  rintro ⟨c, hc⟩
  exact hw c hc

@[simp] theorem rho_xy_z (w : M₂.Wire) : rho I M₁ M₂ (.xy_z w) = none := rfl

@[simp] theorem rho_x_yz (w : M₂.Wire) : rho I M₁ M₂ (.x_yz w) = none := rfl

theorem rho_e (i : Fin (2 * (2 * n))) :
    rho I M₁ M₂ (.e i) = if (i : ℕ) = K then some true else none := rfl

/-! ### The induced restrictions of the four multipliers' inputs -/

/-- The restriction of the inputs of the copy `xy` induced by `ρ`. -/
noncomputable def inputXY : InputRestriction n :=
  .ofRestriction ((rho I M₁ M₂).comap (substXY M₁ M₂))

/-- The restriction of the inputs of the copy `yz` induced by `ρ`. -/
noncomputable def inputYZ : InputRestriction n :=
  .ofRestriction ((rho I M₁ M₂).comap (substYZ M₁ M₂))

/-- The restriction of the inputs of the copy `(xy)z` induced by `ρ`: the output bits of `xy`
and the zero-padded `z`. -/
noncomputable def inputXY_Z : InputRestriction (2 * n) :=
  .ofRestriction ((rho I M₁ M₂).comap (substXY_Z M₁ M₂))

/-- The restriction of the inputs of the copy `x(yz)` induced by `ρ`: the zero-padded `x` and
the output bits of `yz`. -/
noncomputable def inputX_YZ : InputRestriction (2 * n) :=
  .ofRestriction ((rho I M₁ M₂).comap (substX_YZ M₁ M₂))

@[simp] theorem inputXY_x (i : Fin n) : (inputXY I M₁ M₂).x i = I.xIn i := by
  simp [inputXY, substXY]

@[simp] theorem inputXY_y (j : Fin n) : (inputXY I M₁ M₂).y j = I.yIn j := by
  simp [inputXY, substXY]

@[simp] theorem inputYZ_x (i : Fin n) : (inputYZ I M₁ M₂).x i = I.yIn i := by
  simp [inputYZ, substYZ]

@[simp] theorem inputYZ_y (j : Fin n) : (inputYZ I M₁ M₂).y j = I.zIn j := by
  simp [inputYZ, substYZ]

@[simp] theorem inputXY_Z_x (c : Fin (2 * n)) : (inputXY_Z I M₁ M₂).x c = I.xyOut c := by
  simp [inputXY_Z, substXY_Z, rho_xy_out]

theorem inputXY_Z_y_of_lt {c : Fin (2 * n)} (hc : (c : ℕ) < n) :
    (inputXY_Z I M₁ M₂).y c = I.zIn c := by
  simp [inputXY_Z, substXY_Z, hc]

theorem inputXY_Z_y_of_le {c : Fin (2 * n)} (hc : n ≤ c) :
    (inputXY_Z I M₁ M₂).y c = some false := by
  simp [inputXY_Z, substXY_Z, not_lt.mpr hc]

theorem inputX_YZ_x_of_lt {c : Fin (2 * n)} (hc : (c : ℕ) < n) :
    (inputX_YZ I M₁ M₂).x c = I.xIn c := by
  simp [inputX_YZ, substX_YZ, hc]

theorem inputX_YZ_x_of_le {c : Fin (2 * n)} (hc : n ≤ c) :
    (inputX_YZ I M₁ M₂).x c = some false := by
  simp [inputX_YZ, substX_YZ, not_lt.mpr hc]

@[simp] theorem inputX_YZ_y (c : Fin (2 * n)) : (inputX_YZ I M₁ M₂).y c = I.yzOut c := by
  simp [inputX_YZ, substX_YZ, rho_yz_out]

/-! ### The live partial products of the inner multipliers -/

/-- A partial product of `xy` is not forced to `0` exactly when it is `x_{i(u)} y_{j(e)}` for
a vertex `u` and an edge `e`. -/
theorem not_forcedZero_inputXY_iff (i j : Fin n) :
    ¬ (inputXY I M₁ M₂).ForcedZero i j ↔ (∃ u, I.i u = i) ∧ ∃ e, I.j e = j := by
  rw [InputRestriction.ForcedZero, inputXY_x, inputXY_y, not_or, IndexMaps.xIn_eq_some_false_iff,
    IndexMaps.yIn_eq_some_false_iff, not_not, not_not]

/-- A partial product of `yz` is not forced to `0` exactly when it is `y_{j(e)} z_{k(v)}` for
an edge `e` and a vertex `v`. -/
theorem not_forcedZero_inputYZ_iff (i j : Fin n) :
    ¬ (inputYZ I M₁ M₂).ForcedZero i j ↔ (∃ e, I.j e = i) ∧ ∃ v, I.k v = j := by
  rw [InputRestriction.ForcedZero, inputYZ_x, inputYZ_y, not_or, IndexMaps.yIn_eq_some_false_iff,
    IndexMaps.zIn_eq_some_false_iff, not_not, not_not]

/-- **Lemma [lem:rho-g-sparse](i).** The column `col_xy(v)` of `xy` holds exactly the partial
products `x_{i(u_e)} y_{j(e)}`, `e ∈ E(v)`. -/
theorem mem_liveInColumn_inputXY_colXYv (v : V) (p : Fin n × Fin n) :
    p ∈ (inputXY I M₁ M₂).liveInColumn (I.colXYv v) ↔
      ∃ e, H.right e = v ∧ (p.1 : ℕ) = I.i (H.left e) ∧ (p.2 : ℕ) = I.j e := by
  rw [InputRestriction.mem_liveInColumn, not_forcedZero_inputXY_iff]
  constructor
  · rintro ⟨hc, ⟨u, hu⟩, ⟨e, he⟩⟩
    have hcol : I.colXY u e = I.colXYv v := by
      change I.i u + I.j e = _
      rw [hu, he]
      exact hc
    obtain ⟨rfl, rfl⟩ := (I.colXY_eq_colXYv_iff u e v).mp hcol
    exact ⟨e, rfl, hu.symm, he.symm⟩
  · rintro ⟨e, rfl, h1, h2⟩
    refine ⟨?_, ⟨_, h1.symm⟩, ⟨_, h2.symm⟩⟩
    rw [h1, h2]
    exact I.colXY_incident e

/-- **Lemma [lem:rho-g-sparse](i).** The column `col_yz(u)` of `yz` holds exactly the partial
products `y_{j(e)} z_{k(v_e)}`, `e ∈ E(u)`. -/
theorem mem_liveInColumn_inputYZ_colYZu (u : U) (p : Fin n × Fin n) :
    p ∈ (inputYZ I M₁ M₂).liveInColumn (I.colYZu u) ↔
      ∃ e, H.left e = u ∧ (p.1 : ℕ) = I.j e ∧ (p.2 : ℕ) = I.k (H.right e) := by
  rw [InputRestriction.mem_liveInColumn, not_forcedZero_inputYZ_iff]
  constructor
  · rintro ⟨hc, ⟨e, he⟩, ⟨v, hv⟩⟩
    have hcol : I.colYZ e v = I.colYZu u := by
      change I.j e + I.k v = _
      rw [he, hv]
      exact hc
    obtain ⟨rfl, rfl⟩ := (I.colYZ_eq_colYZu_iff e v u).mp hcol
    exact ⟨e, rfl, he.symm, hv.symm⟩
  · rintro ⟨e, rfl, h1, h2⟩
    refine ⟨?_, ⟨_, h1.symm⟩, ⟨_, h2.symm⟩⟩
    rw [h1, h2]
    exact I.colYZ_incident e

/-- **Lemma [lem:rho-g-sparse](i).** Every column of `xy` other than the columns `col_xy(v)`
holds at most one partial product not forced to `0`. -/
theorem card_liveInColumn_inputXY_le_one {c : ℕ} (hc : ∀ v, I.colXYv v ≠ c) :
    ((inputXY I M₁ M₂).liveInColumn c).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun p hp p' hp' => ?_
  rw [InputRestriction.mem_liveInColumn, not_forcedZero_inputXY_iff] at hp hp'
  obtain ⟨hpc, ⟨u, hu⟩, ⟨e, he⟩⟩ := hp
  obtain ⟨hpc', ⟨u', hu'⟩, ⟨e', he'⟩⟩ := hp'
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

/-- **Lemma [lem:rho-g-sparse](i).** Every column of `yz` other than the columns `col_yz(u)`
holds at most one partial product not forced to `0`. -/
theorem card_liveInColumn_inputYZ_le_one {c : ℕ} (hc : ∀ u, I.colYZu u ≠ c) :
    ((inputYZ I M₁ M₂).liveInColumn c).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun p hp p' hp' => ?_
  rw [InputRestriction.mem_liveInColumn, not_forcedZero_inputYZ_iff] at hp hp'
  obtain ⟨hpc, ⟨e, he⟩, ⟨v, hv⟩⟩ := hp
  obtain ⟨hpc', ⟨e', he'⟩, ⟨v', hv'⟩⟩ := hp'
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

/-! ### `ρ` is `g`-sparse -/

/-- **Lemma [lem:rho-g-sparse](ii)** for `xy`: for a simple graph with `|U| ≤ m + 1` and
`m + 2 ≤ 2^(g-1)`, the induced restriction of the inputs of `xy` is `g`-sparse. -/
theorem isSparse_inputXY {m : ℕ} (hs : H.IsSimple) (hU : Fintype.card U ≤ m + 1)
    (hg : m + 2 ≤ 2 ^ (g - 1)) : (inputXY I M₁ M₂).IsSparse g := by
  refine ⟨fun i j hij => ?_, fun c => ?_⟩
  · obtain ⟨⟨u, hu⟩, ⟨e, he⟩⟩ := (not_forcedZero_inputXY_iff I M₁ M₂ i j).mp hij
    rw [← hu, ← he]
    exact I.g_dvd_colXY u e
  · by_cases hc : ∃ v, I.colXYv v = c
    · obtain ⟨v, rfl⟩ := hc
      calc ((inputXY I M₁ M₂).liveInColumn (I.colXYv v)).card
          ≤ ((H.star (Sum.inr v)).image fun e => I.j e).card := by
            refine Finset.card_le_card_of_injOn (fun p => (p.2 : ℕ)) ?_ ?_
            · intro p hp
              obtain ⟨e, he, -, h2⟩ :=
                (mem_liveInColumn_inputXY_colXYv I M₁ M₂ v p).mp (Finset.mem_coe.mp hp)
              exact Finset.mem_coe.mpr
                (Finset.mem_image.mpr ⟨e, H.mem_star_inr.mpr he, h2.symm⟩)
            · intro p hp p' hp' h
              have h1 := ((InputRestriction.mem_liveInColumn _).mp (Finset.mem_coe.mp hp)).1
              have h2 := ((InputRestriction.mem_liveInColumn _).mp (Finset.mem_coe.mp hp')).1
              simp only at h
              exact Prod.ext (Fin.ext (by omega)) (Fin.ext h)
        _ ≤ (H.star (Sum.inr v)).card := Finset.card_image_le
        _ ≤ Fintype.card U := hs.degree_inr_le v
        _ < 2 ^ (g - 1) := by omega
    · have hc' : ∀ v, I.colXYv v ≠ c := fun v hv => hc ⟨v, hv⟩
      exact lt_of_le_of_lt (card_liveInColumn_inputXY_le_one I M₁ M₂ hc') (by omega)

/-- **Lemma [lem:rho-g-sparse](ii)** for `yz`: for a simple graph with `|V| ≤ m + 1` and
`m + 2 ≤ 2^(g-1)`, the induced restriction of the inputs of `yz` is `g`-sparse. -/
theorem isSparse_inputYZ {m : ℕ} (hs : H.IsSimple) (hV : Fintype.card V ≤ m + 1)
    (hg : m + 2 ≤ 2 ^ (g - 1)) : (inputYZ I M₁ M₂).IsSparse g := by
  refine ⟨fun i j hij => ?_, fun c => ?_⟩
  · obtain ⟨⟨e, he⟩, ⟨v, hv⟩⟩ := (not_forcedZero_inputYZ_iff I M₁ M₂ i j).mp hij
    rw [← he, ← hv]
    exact I.g_dvd_colYZ e v
  · by_cases hc : ∃ u, I.colYZu u = c
    · obtain ⟨u, rfl⟩ := hc
      calc ((inputYZ I M₁ M₂).liveInColumn (I.colYZu u)).card
          ≤ ((H.star (Sum.inl u)).image fun e => I.j e).card := by
            refine Finset.card_le_card_of_injOn (fun p => (p.1 : ℕ)) ?_ ?_
            · intro p hp
              obtain ⟨e, he, h1, -⟩ :=
                (mem_liveInColumn_inputYZ_colYZu I M₁ M₂ u p).mp (Finset.mem_coe.mp hp)
              exact Finset.mem_coe.mpr
                (Finset.mem_image.mpr ⟨e, H.mem_star_inl.mpr he, h1.symm⟩)
            · intro p hp p' hp' h
              have h1 := ((InputRestriction.mem_liveInColumn _).mp (Finset.mem_coe.mp hp)).1
              have h2 := ((InputRestriction.mem_liveInColumn _).mp (Finset.mem_coe.mp hp')).1
              simp only at h
              exact Prod.ext (Fin.ext h) (Fin.ext (by omega))
        _ ≤ (H.star (Sum.inl u)).card := Finset.card_image_le
        _ ≤ Fintype.card V := hs.degree_inl_le u
        _ < 2 ^ (g - 1) := by omega
    · have hc' : ∀ u, I.colYZu u ≠ c := fun u hu => hc ⟨u, hu⟩
      exact lt_of_le_of_lt (card_liveInColumn_inputYZ_le_one I M₁ M₂ hc') (by omega)

/-- A partial product of `(xy)z` is not forced to `0` exactly when its first factor is an
output bit of `xy` not set to `0` and its second factor is a bit `z_{k(v)}`. -/
theorem not_forcedZero_inputXY_Z_iff (c₁ c₂ : Fin (2 * n)) :
    ¬ (inputXY_Z I M₁ M₂).ForcedZero c₁ c₂ ↔
      I.xyOut c₁ ≠ some false ∧ (c₂ : ℕ) < n ∧ ∃ v, I.k v = c₂ := by
  rw [InputRestriction.ForcedZero, inputXY_Z_x, not_or]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    by_cases hc : (c₂ : ℕ) < n
    · rw [inputXY_Z_y_of_lt I M₁ M₂ hc, IndexMaps.zIn_eq_some_false_iff, not_not] at h2
      exact ⟨hc, h2⟩
    · exact absurd (inputXY_Z_y_of_le I M₁ M₂ (not_lt.mp hc)) h2
  · rintro ⟨h1, hc, v, hv⟩
    refine ⟨h1, ?_⟩
    rw [inputXY_Z_y_of_lt I M₁ M₂ hc, IndexMaps.zIn_eq_some_false_iff, not_not]
    exact ⟨v, hv⟩

/-- A partial product of `x(yz)` is not forced to `0` exactly when its first factor is a bit
`x_{i(u)}` and its second factor is an output bit of `yz` not set to `0`. -/
theorem not_forcedZero_inputX_YZ_iff (c₁ c₂ : Fin (2 * n)) :
    ¬ (inputX_YZ I M₁ M₂).ForcedZero c₁ c₂ ↔
      ((c₁ : ℕ) < n ∧ ∃ u, I.i u = c₁) ∧ I.yzOut c₂ ≠ some false := by
  rw [InputRestriction.ForcedZero, inputX_YZ_y, not_or]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    by_cases hc : (c₁ : ℕ) < n
    · rw [inputX_YZ_x_of_lt I M₁ M₂ hc, IndexMaps.xIn_eq_some_false_iff, not_not] at h1
      exact ⟨hc, h1⟩
    · exact absurd (inputX_YZ_x_of_le I M₁ M₂ (not_lt.mp hc)) h1
  · rintro ⟨⟨hc, u, hu⟩, h2⟩
    refine ⟨?_, h2⟩
    rw [inputX_YZ_x_of_lt I M₁ M₂ hc, IndexMaps.xIn_eq_some_false_iff, not_not]
    exact ⟨u, hu⟩

/-- **Lemma [lem:rho-g-sparse](ii)** for `(xy)z`: with `|V| ≤ m + 1` and `m + 2 ≤ 2^(g-1)`,
the induced restriction of the inputs of `(xy)z` is `g`-sparse; each column holds at most
`|V|` partial products not forced to `0`, one for each factor `z_{k(v)}`. -/
theorem isSparse_inputXY_Z {m : ℕ} (hV : Fintype.card V ≤ m + 1) (hg : m + 2 ≤ 2 ^ (g - 1)) :
    (inputXY_Z I M₁ M₂).IsSparse g := by
  refine ⟨fun c₁ c₂ h => ?_, fun c => ?_⟩
  · obtain ⟨h1, -, v, hv⟩ := (not_forcedZero_inputXY_Z_iff I M₁ M₂ c₁ c₂).mp h
    rw [← hv]
    exact Nat.dvd_add (I.g_dvd_of_xyOut_ne h1) (I.g_dvd_k v)
  · calc ((inputXY_Z I M₁ M₂).liveInColumn c).card
        ≤ (Finset.univ.image fun v => I.k v).card := by
          refine Finset.card_le_card_of_injOn (fun p => (p.2 : ℕ)) ?_ ?_
          · intro p hp
            obtain ⟨-, -, v, hv⟩ := (not_forcedZero_inputXY_Z_iff I M₁ M₂ p.1 p.2).mp
              ((InputRestriction.mem_liveInColumn _).mp (Finset.mem_coe.mp hp)).2
            exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨v, Finset.mem_univ _, hv⟩)
          · intro p hp p' hp' h
            have h1 := ((InputRestriction.mem_liveInColumn _).mp (Finset.mem_coe.mp hp)).1
            have h2 := ((InputRestriction.mem_liveInColumn _).mp (Finset.mem_coe.mp hp')).1
            simp only at h
            exact Prod.ext (Fin.ext (by omega)) (Fin.ext h)
      _ ≤ Fintype.card V := Finset.card_image_le.trans Finset.card_univ.le
      _ < 2 ^ (g - 1) := by omega

/-- **Lemma [lem:rho-g-sparse](ii)** for `x(yz)`: with `|U| ≤ m + 1` and `m + 2 ≤ 2^(g-1)`,
the induced restriction of the inputs of `x(yz)` is `g`-sparse; each column holds at most
`|U|` partial products not forced to `0`, one for each factor `x_{i(u)}`. -/
theorem isSparse_inputX_YZ {m : ℕ} (hU : Fintype.card U ≤ m + 1) (hg : m + 2 ≤ 2 ^ (g - 1)) :
    (inputX_YZ I M₁ M₂).IsSparse g := by
  refine ⟨fun c₁ c₂ h => ?_, fun c => ?_⟩
  · obtain ⟨⟨-, u, hu⟩, h2⟩ := (not_forcedZero_inputX_YZ_iff I M₁ M₂ c₁ c₂).mp h
    rw [← hu]
    exact Nat.dvd_add (I.g_dvd_i u) (I.g_dvd_of_yzOut_ne h2)
  · calc ((inputX_YZ I M₁ M₂).liveInColumn c).card
        ≤ (Finset.univ.image fun u => I.i u).card := by
          refine Finset.card_le_card_of_injOn (fun p => (p.1 : ℕ)) ?_ ?_
          · intro p hp
            obtain ⟨⟨-, u, hu⟩, -⟩ := (not_forcedZero_inputX_YZ_iff I M₁ M₂ p.1 p.2).mp
              ((InputRestriction.mem_liveInColumn _).mp (Finset.mem_coe.mp hp)).2
            exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨u, Finset.mem_univ _, hu⟩)
          · intro p hp p' hp' h
            have h1 := ((InputRestriction.mem_liveInColumn _).mp (Finset.mem_coe.mp hp)).1
            have h2 := ((InputRestriction.mem_liveInColumn _).mp (Finset.mem_coe.mp hp')).1
            simp only at h
            exact Prod.ext (Fin.ext h) (Fin.ext (by omega))
      _ ≤ Fintype.card U := Finset.card_image_le.trans Finset.card_univ.le
      _ < 2 ^ (g - 1) := by omega

end Assoc

end AssocLB
