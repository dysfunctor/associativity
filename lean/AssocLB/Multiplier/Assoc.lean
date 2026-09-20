/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/
import AssocLB.Resolution.Substitution
import AssocLB.Multiplier.Circuit

/-!
# The associativity formula

Paper: Section 3 (The associativity formula), Definition [def:assoc] (full-product
associativity miter).

## Main definitions

* `AssocVar n W₁ W₂`: the variables of `Assoc_n`: the bits of the three `n`-bit inputs `x`, `y`,
  `z`; the wires of the four multipliers, `xy` and `yz` (inner, with wires `W₁`) and `xy_z` and
  `x_yz` (outer, with wires `W₂`), each named after its output as in the paper; and the miter
  variables `e i`.
* `Assoc M₁ M₂`, for an exact `n`-bit encoding `M₁` and an exact `2n`-bit encoding `M₂`: the CNF
  consisting of the four multiplier copies, made by substitution (`Assoc.substXY`,
  `Assoc.substYZ`, `Assoc.substXY_Z`, `Assoc.substX_YZ`), the clauses defining the miter
  variables `e_i ↔ ((xy)z)_i ⊕ (x(yz))_i` (`Assoc.miter`), and the clause `e_0 ∨ ⋯ ∨ e_{4n-1}`
  (`Assoc.miterClause`).

## Main results

* `Assoc.unsatisfiable`: `Assoc_n` is unsatisfiable. Under a satisfying assignment the four
  copies compute `xy`, `yz`, `(xy)z` and `x(yz)` by exactness, the two outer outputs represent
  the same integer by associativity of multiplication and are therefore equal as bit-vectors,
  so every miter variable is `0`, contradicting the miter clause.
* `Assoc.card_le_of_ne_miterClause`: every clause other than the miter clause has width at most
  the larger width of the two encodings, or `3`; `Assoc.card_miterClause`: the miter clause
  has width `4n`.

## Design notes

* The four copies are images of the encodings under substitutions (`CNF.subst`): the inner
  copies under injective renamings, the outer copies under renamings that also send the high
  `n` bits of the padded inputs `x` and `z` to the constant `0`. So the zero-padding of the
  paper is substitution by a constant, and, as always with `CNF.subst`, clauses satisfied by
  that constant disappear and its falsified literals are removed. Tautological clauses of the
  encodings, if any, are dropped as well; they are satisfied by every assignment.
* The miter variables are the outputs of XOR gates over the two outer outputs, with the
  Tseitin clauses of `Gate.xor2`. Their index type is `Fin (2 * (2 * n))`, the length of the
  outer outputs, which is the paper's `4n`.
* The encodings for the widths `n` and `2n` are separate parameters `M₁` and `M₂`, so that a
  family `M : ∀ n, MulEncoding n` gives `Assoc (M n) (M (2 * n))`.
-/

namespace AssocLB

/-- The variables of the associativity formula `Assoc_n`: the input bits, the wires of the four
multipliers, named after their outputs, and the miter variables.

Paper: Definition [def:assoc]. -/
inductive AssocVar (n : ℕ) (W₁ W₂ : Type)
  /-- The bit `x_i` of the input `x`. -/
  | x (i : Fin n)
  /-- The bit `y_i` of the input `y`. -/
  | y (i : Fin n)
  /-- The bit `z_i` of the input `z`. -/
  | z (i : Fin n)
  /-- A wire of the inner multiplier `xy`. -/
  | xy (w : W₁)
  /-- A wire of the inner multiplier `yz`. -/
  | yz (w : W₁)
  /-- A wire of the outer multiplier `(xy)z`. -/
  | xy_z (w : W₂)
  /-- A wire of the outer multiplier `x(yz)`. -/
  | x_yz (w : W₂)
  /-- The miter variable `e_i`. -/
  | e (i : Fin (2 * (2 * n)))
  deriving DecidableEq

namespace Assoc

variable {n : ℕ} (M₁ : MulEncoding n) (M₂ : MulEncoding (2 * n))

/-- The substitution embedding the inner multiplier `xy = Mul_n(x, y; xy)`. -/
def substXY : Subst (MulVar n M₁.Wire) (AssocVar n M₁.Wire M₂.Wire)
  | .x i => .lit (.pos (.x i))
  | .y j => .lit (.pos (.y j))
  | .wire w => .lit (.pos (.xy w))

/-- The substitution embedding the inner multiplier `yz = Mul_n(y, z; yz)`. -/
def substYZ : Subst (MulVar n M₁.Wire) (AssocVar n M₁.Wire M₂.Wire)
  | .x i => .lit (.pos (.y i))
  | .y j => .lit (.pos (.z j))
  | .wire w => .lit (.pos (.yz w))

/-- The substitution embedding the outer multiplier `(xy)z = Mul_{2n}(xy, z; (xy)z)`: its first
input is the output of `xy`, its second is the input `z` zero-padded to `2n` bits. -/
def substXY_Z : Subst (MulVar (2 * n) M₂.Wire) (AssocVar n M₁.Wire M₂.Wire)
  | .x i => .lit (.pos (.xy (M₁.out i)))
  | .y j => if h : (j : ℕ) < n then .lit (.pos (.z ⟨j, h⟩)) else .const false
  | .wire w => .lit (.pos (.xy_z w))

/-- The substitution embedding the outer multiplier `x(yz) = Mul_{2n}(x, yz; x(yz))`: its first
input is the input `x` zero-padded to `2n` bits, its second is the output of `yz`. -/
def substX_YZ : Subst (MulVar (2 * n) M₂.Wire) (AssocVar n M₁.Wire M₂.Wire)
  | .x i => if h : (i : ℕ) < n then .lit (.pos (.x ⟨i, h⟩)) else .const false
  | .y j => .lit (.pos (.yz (M₁.out j)))
  | .wire w => .lit (.pos (.x_yz w))

/-- The clauses defining the miter variables, `e_i ↔ ((xy)z)_i ⊕ (x(yz))_i`. -/
def miter : CNF (AssocVar n M₁.Wire M₂.Wire) :=
  Finset.univ.biUnion fun i : Fin (2 * (2 * n)) =>
    (Gate.xor2 (AssocVar.xy_z (M₂.out i)) (AssocVar.x_yz (M₂.out i))).clauses (AssocVar.e i)

/-- The miter clause `e_0 ∨ ⋯ ∨ e_{4n-1}`. -/
def miterClause (n : ℕ) (W₁ W₂ : Type) [DecidableEq W₁] [DecidableEq W₂] :
    Clause (AssocVar n W₁ W₂) :=
  Finset.univ.image fun i : Fin (2 * (2 * n)) => Literal.pos (AssocVar.e i)

end Assoc

/-- The associativity formula `Assoc_n`: the four multiplier copies, the clauses defining the
miter variables, and the miter clause.

Paper: Definition [def:assoc]. -/
def Assoc {n : ℕ} (M₁ : MulEncoding n) (M₂ : MulEncoding (2 * n)) :
    CNF (AssocVar n M₁.Wire M₂.Wire) :=
  M₁.cnf.subst (Assoc.substXY M₁ M₂) ∪ M₁.cnf.subst (Assoc.substYZ M₁ M₂) ∪
    M₂.cnf.subst (Assoc.substXY_Z M₁ M₂) ∪ M₂.cnf.subst (Assoc.substX_YZ M₁ M₂) ∪
    Assoc.miter M₁ M₂ ∪ {Assoc.miterClause n M₁.Wire M₂.Wire}

namespace Assoc

variable {n : ℕ} (M₁ : MulEncoding n) (M₂ : MulEncoding (2 * n))
  (α : AssocVar n M₁.Wire M₂.Wire → Bool)

/-! ### The values of the substituted variables -/

@[simp] theorem pullback_substXY_x (i : Fin n) :
    (substXY M₁ M₂).pullback α (.x i) = α (.x i) := by
  simp [substXY]

@[simp] theorem pullback_substXY_y (j : Fin n) :
    (substXY M₁ M₂).pullback α (.y j) = α (.y j) := by
  simp [substXY]

@[simp] theorem pullback_substXY_wire (w : M₁.Wire) :
    (substXY M₁ M₂).pullback α (.wire w) = α (.xy w) := by
  simp [substXY]

@[simp] theorem pullback_substYZ_x (i : Fin n) :
    (substYZ M₁ M₂).pullback α (.x i) = α (.y i) := by
  simp [substYZ]

@[simp] theorem pullback_substYZ_y (j : Fin n) :
    (substYZ M₁ M₂).pullback α (.y j) = α (.z j) := by
  simp [substYZ]

@[simp] theorem pullback_substYZ_wire (w : M₁.Wire) :
    (substYZ M₁ M₂).pullback α (.wire w) = α (.yz w) := by
  simp [substYZ]

@[simp] theorem pullback_substXY_Z_x (i : Fin (2 * n)) :
    (substXY_Z M₁ M₂).pullback α (.x i) = α (.xy (M₁.out i)) := by
  simp [substXY_Z]

@[simp] theorem pullback_substXY_Z_y (j : Fin (2 * n)) :
    (substXY_Z M₁ M₂).pullback α (.y j) = Bits.zeroExtend (α ∘ AssocVar.z) (2 * n) j := by
  simp only [Subst.pullback_apply, substXY_Z, Bits.zeroExtend]
  split_ifs <;> simp

@[simp] theorem pullback_substXY_Z_wire (w : M₂.Wire) :
    (substXY_Z M₁ M₂).pullback α (.wire w) = α (.xy_z w) := by
  simp [substXY_Z]

@[simp] theorem pullback_substX_YZ_x (i : Fin (2 * n)) :
    (substX_YZ M₁ M₂).pullback α (.x i) = Bits.zeroExtend (α ∘ AssocVar.x) (2 * n) i := by
  simp only [Subst.pullback_apply, substX_YZ, Bits.zeroExtend]
  split_ifs <;> simp

@[simp] theorem pullback_substX_YZ_y (j : Fin (2 * n)) :
    (substX_YZ M₁ M₂).pullback α (.y j) = α (.yz (M₁.out j)) := by
  simp [substX_YZ]

@[simp] theorem pullback_substX_YZ_wire (w : M₂.Wire) :
    (substX_YZ M₁ M₂).pullback α (.wire w) = α (.x_yz w) := by
  simp [substX_YZ]

theorem pullback_substXY_comp_x : (substXY M₁ M₂).pullback α ∘ MulVar.x = α ∘ AssocVar.x :=
  funext fun i => pullback_substXY_x M₁ M₂ α i

theorem pullback_substXY_comp_y : (substXY M₁ M₂).pullback α ∘ MulVar.y = α ∘ AssocVar.y :=
  funext fun j => pullback_substXY_y M₁ M₂ α j

theorem pullback_substXY_out :
    (fun i => (substXY M₁ M₂).pullback α (.wire (M₁.out i))) = fun i => α (.xy (M₁.out i)) :=
  funext fun i => pullback_substXY_wire M₁ M₂ α (M₁.out i)

theorem pullback_substYZ_comp_x : (substYZ M₁ M₂).pullback α ∘ MulVar.x = α ∘ AssocVar.y :=
  funext fun i => pullback_substYZ_x M₁ M₂ α i

theorem pullback_substYZ_comp_y : (substYZ M₁ M₂).pullback α ∘ MulVar.y = α ∘ AssocVar.z :=
  funext fun j => pullback_substYZ_y M₁ M₂ α j

theorem pullback_substYZ_out :
    (fun i => (substYZ M₁ M₂).pullback α (.wire (M₁.out i))) = fun i => α (.yz (M₁.out i)) :=
  funext fun i => pullback_substYZ_wire M₁ M₂ α (M₁.out i)

theorem pullback_substXY_Z_comp_x :
    (substXY_Z M₁ M₂).pullback α ∘ MulVar.x = fun i => α (.xy (M₁.out i)) :=
  funext fun i => pullback_substXY_Z_x M₁ M₂ α i

theorem pullback_substXY_Z_comp_y :
    (substXY_Z M₁ M₂).pullback α ∘ MulVar.y = Bits.zeroExtend (α ∘ AssocVar.z) (2 * n) :=
  funext fun j => pullback_substXY_Z_y M₁ M₂ α j

theorem pullback_substXY_Z_out :
    (fun i => (substXY_Z M₁ M₂).pullback α (.wire (M₂.out i))) =
      fun i => α (.xy_z (M₂.out i)) :=
  funext fun i => pullback_substXY_Z_wire M₁ M₂ α (M₂.out i)

theorem pullback_substX_YZ_comp_x :
    (substX_YZ M₁ M₂).pullback α ∘ MulVar.x = Bits.zeroExtend (α ∘ AssocVar.x) (2 * n) :=
  funext fun i => pullback_substX_YZ_x M₁ M₂ α i

theorem pullback_substX_YZ_comp_y :
    (substX_YZ M₁ M₂).pullback α ∘ MulVar.y = fun j => α (.yz (M₁.out j)) :=
  funext fun j => pullback_substX_YZ_y M₁ M₂ α j

theorem pullback_substX_YZ_out :
    (fun i => (substX_YZ M₁ M₂).pullback α (.wire (M₂.out i))) =
      fun i => α (.x_yz (M₂.out i)) :=
  funext fun i => pullback_substX_YZ_wire M₁ M₂ α (M₂.out i)

/-! ### The products computed by the four copies -/

/-- Under an assignment satisfying the copy `xy`, its output represents `x · y`. -/
theorem toNat_xy_of_sat {α : AssocVar n M₁.Wire M₂.Wire → Bool}
    (h : CNF.Sat α (M₁.cnf.subst (substXY M₁ M₂))) :
    Bits.toNat (fun i => α (.xy (M₁.out i))) =
      Bits.toNat (α ∘ AssocVar.x) * Bits.toNat (α ∘ AssocVar.y) := by
  have := M₁.toNat_out_of_sat ((CNF.sat_subst_iff _ _ _).mp h)
  rwa [pullback_substXY_out, pullback_substXY_comp_x, pullback_substXY_comp_y] at this

/-- Under an assignment satisfying the copy `yz`, its output represents `y · z`. -/
theorem toNat_yz_of_sat {α : AssocVar n M₁.Wire M₂.Wire → Bool}
    (h : CNF.Sat α (M₁.cnf.subst (substYZ M₁ M₂))) :
    Bits.toNat (fun i => α (.yz (M₁.out i))) =
      Bits.toNat (α ∘ AssocVar.y) * Bits.toNat (α ∘ AssocVar.z) := by
  have := M₁.toNat_out_of_sat ((CNF.sat_subst_iff _ _ _).mp h)
  rwa [pullback_substYZ_out, pullback_substYZ_comp_x, pullback_substYZ_comp_y] at this

/-- Under an assignment satisfying the copy `(xy)z`, its output represents `xy · z`. -/
theorem toNat_xy_z_of_sat {α : AssocVar n M₁.Wire M₂.Wire → Bool}
    (h : CNF.Sat α (M₂.cnf.subst (substXY_Z M₁ M₂))) :
    Bits.toNat (fun i => α (.xy_z (M₂.out i))) =
      Bits.toNat (fun i => α (.xy (M₁.out i))) * Bits.toNat (α ∘ AssocVar.z) := by
  have := M₂.toNat_out_of_sat ((CNF.sat_subst_iff _ _ _).mp h)
  rwa [pullback_substXY_Z_out, pullback_substXY_Z_comp_x, pullback_substXY_Z_comp_y,
    Bits.toNat_zeroExtend _ (by omega : n ≤ 2 * n)] at this

/-- Under an assignment satisfying the copy `x(yz)`, its output represents `x · yz`. -/
theorem toNat_x_yz_of_sat {α : AssocVar n M₁.Wire M₂.Wire → Bool}
    (h : CNF.Sat α (M₂.cnf.subst (substX_YZ M₁ M₂))) :
    Bits.toNat (fun i => α (.x_yz (M₂.out i))) =
      Bits.toNat (α ∘ AssocVar.x) * Bits.toNat (fun i => α (.yz (M₁.out i))) := by
  have := M₂.toNat_out_of_sat ((CNF.sat_subst_iff _ _ _).mp h)
  rwa [pullback_substX_YZ_out, pullback_substX_YZ_comp_x, pullback_substX_YZ_comp_y,
    Bits.toNat_zeroExtend _ (by omega : n ≤ 2 * n)] at this

/-! ### The miter -/

theorem sat_miter_iff :
    CNF.Sat α (miter M₁ M₂) ↔
      ∀ i, α (.e i) = (α (.xy_z (M₂.out i)) ^^ α (.x_yz (M₂.out i))) := by
  simp only [miter, CNF.sat_biUnion_iff, Finset.mem_univ, true_implies, Gate.sat_clauses_iff,
    Gate.fn_xor2_comp]

theorem sat_miterClause_iff :
    Clause.Sat α (miterClause n M₁.Wire M₂.Wire) ↔ ∃ i, α (.e i) = true := by
  simp [miterClause, Clause.Sat]

theorem card_miterClause : (miterClause n M₁.Wire M₂.Wire).card = 2 * (2 * n) := by
  rw [miterClause, Finset.card_image_of_injective _ fun i j h => by simpa [Literal.pos] using h,
    Finset.card_univ, Fintype.card_fin]

/-! ### The formula -/

theorem sat_iff :
    CNF.Sat α (Assoc M₁ M₂) ↔
      CNF.Sat α (M₁.cnf.subst (substXY M₁ M₂)) ∧ CNF.Sat α (M₁.cnf.subst (substYZ M₁ M₂)) ∧
        CNF.Sat α (M₂.cnf.subst (substXY_Z M₁ M₂)) ∧
        CNF.Sat α (M₂.cnf.subst (substX_YZ M₁ M₂)) ∧
        CNF.Sat α (miter M₁ M₂) ∧ Clause.Sat α (miterClause n M₁.Wire M₂.Wire) := by
  simp only [Assoc, CNF.sat_union_iff, CNF.sat_singleton_iff, and_assoc]

/-- **`Assoc_n` is unsatisfiable.**

Paper: Definition [def:assoc]. -/
theorem unsatisfiable : (Assoc M₁ M₂).Unsatisfiable := by
  rintro ⟨α, hα⟩
  obtain ⟨hxy, hyz, hxy_z, hx_yz, hm, hc⟩ := (sat_iff M₁ M₂ α).mp hα
  have heq : (fun i => α (.xy_z (M₂.out i))) = fun i => α (.x_yz (M₂.out i)) := by
    apply Bits.toNat_injective
    rw [toNat_xy_z_of_sat M₁ M₂ hxy_z, toNat_x_yz_of_sat M₁ M₂ hx_yz, toNat_xy_of_sat M₁ M₂ hxy,
      toNat_yz_of_sat M₁ M₂ hyz, Nat.mul_assoc]
  obtain ⟨i, hi⟩ := (sat_miterClause_iff M₁ M₂ α).mp hc
  have hi' : α (.xy_z (M₂.out i)) = α (.x_yz (M₂.out i)) := congrFun heq i
  have := (sat_miter_iff M₁ M₂ α).mp hm i
  rw [hi', Bool.xor_self] at this
  rw [this] at hi
  exact Bool.false_ne_true hi

/-- Every clause of `Assoc_n` other than the miter clause has width at most the larger width of
the two encodings, or `3`. -/
theorem card_le_of_ne_miterClause {C : Clause (AssocVar n M₁.Wire M₂.Wire)}
    (hC : C ∈ Assoc M₁ M₂) (hne : C ≠ miterClause n M₁.Wire M₂.Wire) :
    C.card ≤ max (max M₁.cnf.width M₂.cnf.width) 3 := by
  simp only [Assoc, Finset.mem_union, Finset.mem_singleton] at hC
  rcases hC with ((((h | h) | h) | h) | h) | h
  · exact ((CNF.card_le_width h).trans (CNF.width_subst_le _ _)).trans
      (le_max_of_le_left (le_max_left _ _))
  · exact ((CNF.card_le_width h).trans (CNF.width_subst_le _ _)).trans
      (le_max_of_le_left (le_max_left _ _))
  · exact ((CNF.card_le_width h).trans (CNF.width_subst_le _ _)).trans
      (le_max_of_le_left (le_max_right _ _))
  · exact ((CNF.card_le_width h).trans (CNF.width_subst_le _ _)).trans
      (le_max_of_le_left (le_max_right _ _))
  · obtain ⟨i, -, hC⟩ := Finset.mem_biUnion.mp h
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hC
    exact (Gate.card_clause_le _ _ b).trans (le_max_right _ _)
  · exact absurd h hne

end Assoc

end AssocLB
