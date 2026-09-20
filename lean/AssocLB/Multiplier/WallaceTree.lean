/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/
import AssocLB.Multiplier.Circuit
import AssocLB.Multiplier.StripLocal
import AssocLB.Multiplier.CarryLookahead

/-!
# The Wallace-tree multiplier

Paper: Appendix (Wallace-tree multipliers are strip-local), Definition [def:cla]
(carry-lookahead adder), Definition [def:wallace] (Wallace-tree multiplier) and Observation
[obs:wallace-exact] (the Wallace-tree multiplier is an exact encoding).

## Main definitions

* `wallaceRows n ℓ`: the number of rows of layer `ℓ`, `n` for the partial products and then
  `⌈2N/3⌉`; `wallaceLayers n`: the number `ℓ_max` of adder layers, the first layer with at most
  two rows.
* `claLevels n`, `claWidth n = 4^claLevels n ≥ 2n`: the number of levels and the width of the
  final carry-lookahead adder.
* `WWire n`: the wires: the constant `zero`; the layer variables `t ℓ i j` (layer, column,
  row); and the wires of the carry-lookahead adder: the bit signals `p i`, `q i`, the group
  pairs `P ℓ m`, `Q ℓ m` of the block `m` at level `ℓ + 1`, the carries `c i` and the sum
  bits `s i`.
* `WWire.circuit n`: the circuit. Layer `0` holds the partial products, column `i` in the rows
  `j ≤ i` as `x_{i-j} ∧ y_j`. Layer `ℓ + 1` is obtained by partitioning the rows of layer `ℓ`
  into sets of three: the adder of the `k`-th set of column `i` puts its sum bit in row `2k`
  of column `i` and its carry bit in row `2k + 1` of column `i + 1`; nonexistent variables are
  the constant `0`, so an adder with constant inputs is a half adder or a wire. The final two
  rows are added by the carry-lookahead adder: level-`0` pairs `(p_i, q_i)`, level-`(ℓ+1)`
  group pairs from four level-`ℓ` pairs, the carry into a position from the pairs of the
  preceding sub-blocks of its block and the carry into the block, and sum bits `p_i ⊕ c_i`.
* `wallaceMul n`: the Wallace-tree multiplier as an exact multiplier encoding.

## Main results

* `WWire.Wint_succ`: the weighted sum of a column interval changes from one layer to the next
  only by the carries entering and leaving the interval (Definition [def:wallace]: "every adder
  has the same total weight of inputs and outputs").
* `WWire.Wint_eq`: every layer has the weighted sum `x · y`; `WWire.tv_eq_false_of_rows`: the
  rows beyond `wallaceRows n ℓ` are `0`.
* `WWire.eval_c`, `WWire.eval_s`: the carry-lookahead adder computes the carries and sum bits of
  the addition of the final two rows; `WWire.toNat_out`: the output is the product.

## Design notes

* Addresses `(ℓ, i, j)` range over `ℓ ≤ ℓ_max`, `i < 2n`, `j < 2n`; addresses without a real
  variable are wires computing `0`, which realizes the paper's convention that nonexistent
  variables are the constant `0`. Row `j` of column `i` in layer `0` holds `x_{i-j} ∧ y_j`
  whenever both indices are in range, for all columns; the paper re-indexes the rows of the
  columns `i ≥ n` to start at `0`, which only renames rows.
* Sums go to even rows and carries to odd rows of the next layer, one fixed choice of the
  order in which the paper "appends" them to a subcolumn.
* The adder is padded with zero inputs to the width `4^h ≥ 2n`; the carry into a position `i`
  is computed at the level where `i` is an interior block boundary, from the 4-adic valuation
  of `i`. The group pairs are addressed by `(ℓ, m)` with `m < 4^h` for every level; the blocks
  `m ≥ 4^(h-ℓ-1)` do not exist and are wires computing `0`. Gates of fan-in up to `9` (the
  level circuitry) are used, so clauses have width at most `10`.
-/

namespace AssocLB

/-! ### Rows, layers and the width of the final adder -/

/-- The number of rows of layer `ℓ`: `n` rows of partial products, then `⌈2N/3⌉`. -/
def wallaceRows (n : ℕ) : ℕ → ℕ
  | 0 => n
  | ℓ + 1 => (2 * wallaceRows n ℓ + 2) / 3

theorem wallaceRows_succ (n ℓ : ℕ) : wallaceRows n (ℓ + 1) = (2 * wallaceRows n ℓ + 2) / 3 := rfl

theorem exists_wallaceRows_le_two (n : ℕ) : ∃ ℓ, wallaceRows n ℓ ≤ 2 := by
  suffices h : ∀ k ℓ, wallaceRows n ℓ ≤ k → ∃ ℓ', wallaceRows n ℓ' ≤ 2 from h n 0 le_rfl
  intro k
  induction k with
  | zero => exact fun ℓ h => ⟨ℓ, by omega⟩
  | succ k ih =>
    intro ℓ h
    by_cases h2 : wallaceRows n ℓ ≤ 2
    · exact ⟨ℓ, h2⟩
    · exact ih (ℓ + 1) (by rw [wallaceRows_succ]; omega)

/-- The number of adder layers `ℓ_max`: the first layer with at most two rows. -/
def wallaceLayers (n : ℕ) : ℕ := Nat.find (exists_wallaceRows_le_two n)

theorem wallaceRows_wallaceLayers_le (n : ℕ) : wallaceRows n (wallaceLayers n) ≤ 2 :=
  Nat.find_spec (exists_wallaceRows_le_two n)

/-- The number of levels of the carry-lookahead adder, `⌈log₄(2n)⌉`. -/
def claLevels (n : ℕ) : ℕ := Nat.clog 4 (2 * n)

/-- The width `4^h ≥ 2n` of the carry-lookahead adder. -/
def claWidth (n : ℕ) : ℕ := 4 ^ claLevels n

theorem two_mul_le_claWidth (n : ℕ) : 2 * n ≤ claWidth n := Nat.le_pow_clog (by norm_num) _

theorem claWidth_pos (n : ℕ) : 0 < claWidth n := by
  unfold claWidth
  positivity

/-! ### The 4-adic valuation -/

/-- The exponent of the largest power of `4` dividing `i` (`0` for `i = 0`). -/
def val4 (i : ℕ) : ℕ := if h : 0 < i ∧ i % 4 = 0 then val4 (i / 4) + 1 else 0
termination_by i
decreasing_by omega

theorem pow_val4_dvd (i : ℕ) : 4 ^ val4 i ∣ i := by
  refine Nat.strong_induction_on i ?_
  intro i ih
  rw [val4]
  split_ifs with h
  · have h4 : 4 * (i / 4) = i := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h.2)
    calc 4 ^ (val4 (i / 4) + 1) = 4 * 4 ^ val4 (i / 4) := pow_succ' 4 _
      _ ∣ 4 * (i / 4) := mul_dvd_mul_left 4 (ih (i / 4) (by omega))
      _ = i := h4
  · simp

theorem div_pow_val4_mod (i : ℕ) (hi : 0 < i) : (i / 4 ^ val4 i) % 4 ≠ 0 := by
  refine Nat.strong_induction_on i ?_ hi
  intro i ih hi
  rw [val4]
  split_ifs with h
  · rw [pow_succ', ← Nat.div_div_eq_div_mul]
    exact ih (i / 4) (by omega) (by omega)
  · rw [pow_zero, Nat.div_one]
    exact fun h0 => h ⟨hi, h0⟩

theorem val4_lt {i h : ℕ} (hi : 0 < i) (hW : i < 4 ^ h) : val4 i < h := by
  by_contra hle
  rw [not_lt] at hle
  have h1 := Nat.le_of_dvd hi (pow_val4_dvd i)
  have h2 : 4 ^ h ≤ 4 ^ val4 i := Nat.pow_le_pow_right (by norm_num) hle
  omega

/-- The sub-block index `r ∈ {1, 2, 3}` of a position `i > 0` in its block. -/
def claR (i : ℕ) : ℕ := (i / 4 ^ val4 i) % 4

/-- The block index `m` of a position `i` at the level of its 4-adic valuation. -/
def claM (i : ℕ) : ℕ := (i / 4 ^ val4 i) / 4

theorem claR_pos {i : ℕ} (hi : 0 < i) : 0 < claR i :=
  Nat.pos_of_ne_zero (div_pow_val4_mod i hi)

theorem claR_lt (i : ℕ) : claR i < 4 := Nat.mod_lt _ (by norm_num)

/-- The decomposition `i = (4m + r) 4^v`. -/
theorem claM_R_eq (i : ℕ) : (4 * claM i + claR i) * 4 ^ val4 i = i := by
  unfold claM claR
  rw [Nat.div_add_mod, Nat.div_mul_cancel (pow_val4_dvd i)]

/-! ### Gates with many inputs -/

namespace Gate

variable {V : Type*}

/-- The AND of `r` inputs `ps 0, …, ps (r-1)`: the group propagate of a block from the
propagates of its sub-blocks. -/
def allN (r : ℕ) (ps : ℕ → V) : Gate V :=
  ⟨r, fun k => ps k, fun v => allProp (fun t => if h : t < r then v ⟨t, h⟩ else false) 0 r⟩

/-- The carry-fold gate with inputs `ps 0, …, ps (r-1), qs 0, …, qs (r-1), cin`: the carry out
of `r` consecutive sub-blocks with the pairs `(ps t, qs t)` from the carry-in `cin`, by the
recurrence `c ↦ q ⊕ (p ∧ c)`. -/
def carryFold (r : ℕ) (ps qs : ℕ → V) (cin : V) : Gate V :=
  ⟨2 * r + 1,
    fun k => if (k : ℕ) < r then ps k else if (k : ℕ) < 2 * r then qs (k - r) else cin,
    fun v => foldCarry (fun t => if h : t < r then v ⟨t, by omega⟩ else false)
      (fun t => if h : t < r then v ⟨r + t, by omega⟩ else false) 0 r (v ⟨2 * r, by omega⟩)⟩

theorem fn_allN (r : ℕ) (ps : ℕ → V) (β : V → Bool) :
    (allN r ps).fn (fun k => β ((allN r ps).inputs k)) = allProp (fun t => β (ps t)) 0 r := by
  simp only [allN]
  apply allProp_congr
  intro t _ ht
  simp [show t < r by omega]

theorem fn_carryFold (r : ℕ) (ps qs : ℕ → V) (cin : V) (β : V → Bool) :
    (carryFold r ps qs cin).fn (fun k => β ((carryFold r ps qs cin).inputs k)) =
      foldCarry (fun t => β (ps t)) (fun t => β (qs t)) 0 r (β cin) := by
  simp only [carryFold]
  have hc : β ((fun k : Fin (2 * r + 1) =>
      if (k : ℕ) < r then ps k else if (k : ℕ) < 2 * r then qs (k - r) else cin)
      ⟨2 * r, by omega⟩) = β cin := by
    simp [show ¬ (2 * r < r) by omega]
  rw [hc]
  apply foldCarry_congr
  intro t _ ht
  have ht' : t < r := by omega
  have h2 : r + t < 2 * r := by omega
  constructor
  · simp [ht']
  · simp [ht', h2]

theorem inputs_allN (r : ℕ) (ps : ℕ → V) (k : Fin (allN r ps).arity) :
    (allN r ps).inputs k = ps k := rfl

theorem inputs_carryFold (r : ℕ) (ps qs : ℕ → V) (cin : V)
    (k : Fin (carryFold r ps qs cin).arity) :
    (∃ t, t < r ∧ (carryFold r ps qs cin).inputs k = ps t) ∨
      (∃ t, t < r ∧ (carryFold r ps qs cin).inputs k = qs t) ∨
        (carryFold r ps qs cin).inputs k = cin := by
  simp only [carryFold]
  split_ifs with h1 h2
  · exact Or.inl ⟨k, h1, rfl⟩
  · exact Or.inr (Or.inl ⟨k - r, by omega, rfl⟩)
  · exact Or.inr (Or.inr rfl)

end Gate

/-! ### The wires -/

/-- The wires of the `n`-bit Wallace-tree multiplier. -/
inductive WWire (n : ℕ)
  /-- The constant `0`. -/
  | zero
  /-- The layer variable `t_{ℓ,i,j}`: layer `ℓ`, column `i`, row `j`. -/
  | t (ℓ : Fin (wallaceLayers n + 1)) (i : Fin (2 * n)) (j : Fin (2 * n))
  /-- The propagate signal `p_i` of the final adder. -/
  | p (i : Fin (claWidth n))
  /-- The generate signal `q_i` of the final adder. -/
  | q (i : Fin (claWidth n))
  /-- The group propagate of the block `m` at level `ℓ + 1`. -/
  | P (ℓ : Fin (claLevels n)) (m : Fin (claWidth n))
  /-- The group generate of the block `m` at level `ℓ + 1`. -/
  | Q (ℓ : Fin (claLevels n)) (m : Fin (claWidth n))
  /-- The carry into position `i` of the final adder. -/
  | c (i : Fin (claWidth n))
  /-- The sum bit at position `i` of the final adder. -/
  | s (i : Fin (claWidth n))
  deriving DecidableEq, Fintype

namespace WWire

variable {n : ℕ}

/-- The layer variable at the address `(ℓ, i, j)`, or the constant `0` out of range. -/
def tVar (ℓ i j : ℕ) : MulVar n (WWire n) :=
  if h : ℓ < wallaceLayers n + 1 ∧ i < 2 * n ∧ j < 2 * n then
    .wire (.t ⟨ℓ, h.1⟩ ⟨i, h.2.1⟩ ⟨j, h.2.2⟩)
  else .wire .zero

/-- The signal `p_i`, or `0` out of range. -/
def pVar (i : ℕ) : MulVar n (WWire n) :=
  if h : i < claWidth n then .wire (.p ⟨i, h⟩) else .wire .zero

/-- The signal `q_i`, or `0` out of range. -/
def qVar (i : ℕ) : MulVar n (WWire n) :=
  if h : i < claWidth n then .wire (.q ⟨i, h⟩) else .wire .zero

/-- The carry `c_i`, or `0` out of range. -/
def cVar (i : ℕ) : MulVar n (WWire n) :=
  if h : i < claWidth n then .wire (.c ⟨i, h⟩) else .wire .zero

/-- The group propagate of the block `m` at level `ℓ`: the signal `p_m` at level `0`. -/
def PVar : ℕ → ℕ → MulVar n (WWire n)
  | 0, m => pVar m
  | ℓ + 1, m =>
    if h : ℓ < claLevels n ∧ m < claWidth n then .wire (.P ⟨ℓ, h.1⟩ ⟨m, h.2⟩) else .wire .zero

/-- The group generate of the block `m` at level `ℓ`: the signal `q_m` at level `0`. -/
def QVar : ℕ → ℕ → MulVar n (WWire n)
  | 0, m => qVar m
  | ℓ + 1, m =>
    if h : ℓ < claLevels n ∧ m < claWidth n then .wire (.Q ⟨ℓ, h.1⟩ ⟨m, h.2⟩) else .wire .zero

/-- The first summand of the final adder: row `0` of the last layer. -/
def aVar (i : ℕ) : MulVar n (WWire n) := tVar (wallaceLayers n) i 0

/-- The second summand of the final adder: row `1` of the last layer. -/
def bVar (i : ℕ) : MulVar n (WWire n) := tVar (wallaceLayers n) i 1

/-- The partial product in column `i`, row `j` of layer `0`: `x_{i-j} ∧ y_j` when both indices
are in range. -/
def ppPair (n : ℕ) (i j : ℕ) : Option (Fin n × Fin n) :=
  if h : j ≤ i ∧ i - j < n ∧ j < n then some (⟨i - j, h.2.1⟩, ⟨j, h.2.2⟩) else none

/-- The gate of a layer-`0` variable: an AND gate, or the constant `0`. -/
def ppGate (i j : ℕ) : Gate (MulVar n (WWire n)) :=
  match ppPair n i j with
  | some (a, b) => Gate.and2 (.x a) (.y b)
  | none => Gate.const false

theorem ppGate_inputs_ne_wire (i j : ℕ) (k : Fin (ppGate (n := n) i j).arity) (w : WWire n) :
    (ppGate i j).inputs k ≠ MulVar.wire w := by
  revert k
  unfold ppGate
  generalize ppPair n i j = o
  rcases o with _ | ⟨a, b⟩
  · intro k
    exact k.elim0
  · intro k
    rcases Gate.inputs_and2 _ _ k with hk | hk <;> rw [hk] <;> simp

theorem fn_ppGate (i j : ℕ) (β : MulVar n (WWire n) → Bool) :
    (ppGate i j).fn (fun k => β ((ppGate i j).inputs k)) =
      match ppPair n i j with
      | some (a, b) => β (.x a) && β (.y b)
      | none => false := by
  unfold ppGate
  generalize ppPair n i j = o
  rcases o with _ | ⟨a, b⟩ <;> simp [Gate.and2, Gate.const]

/-- The sum gate of the `k`-th set of three rows of column `i` in layer `ℓ`. -/
def sumGate (ℓ i k : ℕ) : Gate (MulVar n (WWire n)) :=
  Gate.xor3 (tVar ℓ i (3 * k)) (tVar ℓ i (3 * k + 1)) (tVar ℓ i (3 * k + 2))

/-- The carry gate of the `k`-th set of three rows of column `i` in layer `ℓ`. -/
def carryGate (ℓ i k : ℕ) : Gate (MulVar n (WWire n)) :=
  Gate.maj3 (tVar ℓ i (3 * k)) (tVar ℓ i (3 * k + 1)) (tVar ℓ i (3 * k + 2))

/-- The gate of the layer variable `(ℓ, i, j)`: a partial product in layer `0`; in layer
`ℓ + 1`, row `2k` is the sum of the `k`-th set of column `i` and row `2k + 1` the carry of the
`k`-th set of column `i - 1`. -/
def layerGate : ℕ → ℕ → ℕ → Gate (MulVar n (WWire n))
  | 0, i, j => ppGate i j
  | ℓ + 1, i, j =>
    if j % 2 = 0 then sumGate ℓ i (j / 2)
    else if i = 0 then Gate.const false else carryGate ℓ (i - 1) (j / 2)

/-- The gate of the carry `c_i`: for `i = (4m + r) 4^v > 0`, the carry out of the sub-blocks
`4m, …, 4m + r - 1` at level `v` from the carry into the block, `c_{4m·4^v}`. -/
def cGate (i : ℕ) : Gate (MulVar n (WWire n)) :=
  if i = 0 then Gate.const false
  else Gate.carryFold (claR i) (fun t => PVar (val4 i) (4 * claM i + t))
    (fun t => QVar (val4 i) (4 * claM i + t)) (cVar (4 * claM i * 4 ^ val4 i))

/-- The gate of each wire. -/
def gate : WWire n → Gate (MulVar n (WWire n))
  | .zero => Gate.const false
  | .t ℓ i j => layerGate ℓ i j
  | .p i => Gate.xor2 (aVar i) (bVar i)
  | .q i => Gate.and2 (aVar i) (bVar i)
  | .P ℓ m =>
    if (m : ℕ) < 4 ^ (claLevels n - (ℓ + 1)) then Gate.allN 4 fun t => PVar ℓ (4 * m + t)
    else Gate.const false
  | .Q ℓ m =>
    if (m : ℕ) < 4 ^ (claLevels n - (ℓ + 1)) then
      Gate.carryFold 4 (fun t => PVar ℓ (4 * m + t)) (fun t => QVar ℓ (4 * m + t)) (.wire .zero)
    else Gate.const false
  | .c i => cGate i
  | .s i => Gate.xor2 (pVar i) (cVar i)

/-- A rank decreasing along gate inputs: layers in order, then the adder level by level, then
the carries in order of position, then the sum bits. -/
def rank : WWire n → ℕ
  | .zero => 0
  | .t ℓ _ _ => ℓ + 1
  | .p _ => wallaceLayers n + 2
  | .q _ => wallaceLayers n + 2
  | .P ℓ _ => wallaceLayers n + 3 + ℓ
  | .Q ℓ _ => wallaceLayers n + 3 + ℓ
  | .c i => wallaceLayers n + 3 + claLevels n + i
  | .s _ => wallaceLayers n + 4 + claLevels n + claWidth n

theorem rank_le_of_tVar {ℓ i j : ℕ} {w : WWire n} (h : tVar ℓ i j = .wire w) :
    rank w ≤ ℓ + 1 := by
  unfold tVar at h
  split_ifs at h <;> cases h <;> simp [rank]

theorem rank_le_of_pVar {i : ℕ} {w : WWire n} (h : pVar i = .wire w) :
    rank w ≤ wallaceLayers n + 2 := by
  unfold pVar at h
  split_ifs at h <;> cases h <;> simp [rank]

theorem rank_le_of_qVar {i : ℕ} {w : WWire n} (h : qVar i = .wire w) :
    rank w ≤ wallaceLayers n + 2 := by
  unfold qVar at h
  split_ifs at h <;> cases h <;> simp [rank]

theorem rank_le_of_cVar {i : ℕ} {w : WWire n} (h : cVar i = .wire w) :
    rank w ≤ wallaceLayers n + 3 + claLevels n + i := by
  unfold cVar at h
  split_ifs at h <;> cases h <;> simp [rank]

theorem rank_le_of_PVar {ℓ m : ℕ} {w : WWire n} (h : PVar ℓ m = .wire w) :
    rank w ≤ wallaceLayers n + 2 + ℓ := by
  cases ℓ with
  | zero => have := rank_le_of_pVar h; omega
  | succ ℓ =>
    rw [PVar] at h
    split_ifs at h <;> cases h
    · change wallaceLayers n + 3 + ℓ ≤ _
      omega
    · exact Nat.zero_le _

theorem rank_le_of_QVar {ℓ m : ℕ} {w : WWire n} (h : QVar ℓ m = .wire w) :
    rank w ≤ wallaceLayers n + 2 + ℓ := by
  cases ℓ with
  | zero => have := rank_le_of_qVar h; omega
  | succ ℓ =>
    rw [QVar] at h
    split_ifs at h <;> cases h
    · change wallaceLayers n + 3 + ℓ ≤ _
      omega
    · exact Nat.zero_le _

theorem rank_lt (w : WWire n) (k : Fin (gate w).arity) (w' : WWire n)
    (h : (gate w).inputs k = MulVar.wire w') : rank w' < rank w := by
  revert k w' h
  suffices H : ∀ (G : Gate (MulVar n (WWire n))), gate w = G →
      ∀ (k : Fin G.arity) (w' : WWire n), G.inputs k = MulVar.wire w' → rank w' < rank w from
    H _ rfl
  intro G hG
  cases w with
  | zero =>
    subst hG
    intro k
    exact k.elim0
  | t ℓ i j =>
    rcases ℓ with ⟨ℓ, hℓ⟩
    cases ℓ with
    | zero =>
      rw [show gate (t ⟨0, hℓ⟩ i j) = ppGate i j from rfl] at hG
      subst hG
      intro k w' h
      exact absurd h (ppGate_inputs_ne_wire i j k w')
    | succ ℓ =>
      rw [show gate (t ⟨ℓ + 1, hℓ⟩ i j) = (if (j : ℕ) % 2 = 0 then sumGate ℓ i (j / 2)
        else if (i : ℕ) = 0 then Gate.const false else carryGate ℓ (i - 1) (j / 2)) from rfl] at hG
      split_ifs at hG with h1 h2 <;> subst hG <;> intro k w' h
      · unfold sumGate at h
        rcases Gate.inputs_xor3 _ _ _ k with hk | hk | hk <;> rw [hk] at h <;>
          have := rank_le_of_tVar h <;> change rank w' < ℓ + 1 + 1 <;> omega
      · exact k.elim0
      · unfold carryGate at h
        rcases Gate.inputs_maj3 _ _ _ k with hk | hk | hk <;> rw [hk] at h <;>
          have := rank_le_of_tVar h <;> change rank w' < ℓ + 1 + 1 <;> omega
  | p i =>
    rw [show gate (p i) = Gate.xor2 (aVar i) (bVar i) from rfl] at hG
    subst hG
    intro k w' h
    rcases Gate.inputs_xor2 _ _ k with hk | hk <;> rw [hk] at h <;>
      have := rank_le_of_tVar h <;> change rank w' < wallaceLayers n + 2 <;> omega
  | q i =>
    rw [show gate (q i) = Gate.and2 (aVar i) (bVar i) from rfl] at hG
    subst hG
    intro k w' h
    rcases Gate.inputs_and2 _ _ k with hk | hk <;> rw [hk] at h <;>
      have := rank_le_of_tVar h <;> change rank w' < wallaceLayers n + 2 <;> omega
  | P ℓ m =>
    rw [show gate (P ℓ m) = (if (m : ℕ) < 4 ^ (claLevels n - (ℓ + 1)) then
      Gate.allN 4 (fun t => PVar ℓ (4 * m + t)) else Gate.const false) from rfl] at hG
    split_ifs at hG <;> subst hG <;> intro k w' h
    · rw [Gate.inputs_allN] at h
      have := rank_le_of_PVar h
      change rank w' < wallaceLayers n + 3 + ℓ
      omega
    · exact k.elim0
  | Q ℓ m =>
    rw [show gate (Q ℓ m) = (if (m : ℕ) < 4 ^ (claLevels n - (ℓ + 1)) then
      Gate.carryFold 4 (fun t => PVar ℓ (4 * m + t)) (fun t => QVar ℓ (4 * m + t)) (.wire .zero)
      else Gate.const false) from rfl] at hG
    split_ifs at hG <;> subst hG <;> intro k w' h
    · change rank w' < wallaceLayers n + 3 + ℓ
      rcases Gate.inputs_carryFold _ _ _ _ k with ⟨t, -, hk⟩ | ⟨t, -, hk⟩ | hk <;> rw [hk] at h
      · have := rank_le_of_PVar h
        omega
      · have := rank_le_of_QVar h
        omega
      · cases h
        simp [rank]
    · exact k.elim0
  | c i =>
    rw [show gate (c i) = cGate i from rfl] at hG
    unfold cGate at hG
    split_ifs at hG with hi <;> subst hG <;> intro k w' h
    · exact k.elim0
    · have hi' : 0 < (i : ℕ) := Nat.pos_of_ne_zero hi
      have hv : val4 i < claLevels n := val4_lt hi' i.isLt
      have hlt : 4 * claM i * 4 ^ val4 i < i := by
        have h1 := claM_R_eq i
        rw [Nat.add_mul] at h1
        have h2 : 0 < claR i * 4 ^ val4 i := Nat.mul_pos (claR_pos hi') (by positivity)
        omega
      change rank w' < wallaceLayers n + 3 + claLevels n + i
      rcases Gate.inputs_carryFold _ _ _ _ k with ⟨t, -, hk⟩ | ⟨t, -, hk⟩ | hk <;> rw [hk] at h
      · have := rank_le_of_PVar h
        omega
      · have := rank_le_of_QVar h
        omega
      · have := rank_le_of_cVar h
        omega
  | s i =>
    rw [show gate (s i) = Gate.xor2 (pVar i) (cVar i) from rfl] at hG
    subst hG
    intro k w' h
    change rank w' < wallaceLayers n + 4 + claLevels n + claWidth n
    rcases Gate.inputs_xor2 _ _ k with hk | hk <;> rw [hk] at h
    · have := rank_le_of_pVar h
      omega
    · have := rank_le_of_cVar h
      have := i.isLt
      omega

/-- The Wallace-tree multiplier circuit for `n`-bit inputs. -/
def circuit (n : ℕ) : MulCircuit n (WWire n) where
  gate := gate
  rank := rank
  rank_lt := rank_lt

@[simp] theorem circuit_gate (w : WWire n) : (circuit n).gate w = gate w := rfl

/-! ### Evaluation of the layers -/

variable (x y : Bits n)

/-- The value of the address `(ℓ, i, j)`: the layer variable, or `0` out of range. -/
def tv (ℓ i j : ℕ) : Bool :=
  (circuit n).toCircuit.evalAssign (MulVar.ofInputs x y) (tVar ℓ i j)

@[simp] theorem eval_zero : (circuit n).eval x y .zero = false := by
  rw [MulCircuit.eval_eq]
  rfl

theorem tv_of_not {ℓ i j : ℕ} (h : ¬ (ℓ < wallaceLayers n + 1 ∧ i < 2 * n ∧ j < 2 * n)) :
    tv x y ℓ i j = false := by
  rw [tv, tVar, dif_neg h, MulCircuit.evalAssign_wire, eval_zero]

theorem tv_eq_eval {ℓ i j : ℕ} (h : ℓ < wallaceLayers n + 1 ∧ i < 2 * n ∧ j < 2 * n) :
    tv x y ℓ i j = (circuit n).eval x y (.t ⟨ℓ, h.1⟩ ⟨i, h.2.1⟩ ⟨j, h.2.2⟩) := by
  rw [tv, tVar, dif_pos h, MulCircuit.evalAssign_wire]

/-- The value of the partial product in column `i`, row `j` of layer `0`. -/
def ppVal (i j : ℕ) : Bool :=
  match ppPair n i j with
  | some (a, b) => x a && y b
  | none => false

theorem ppPair_eq_some_iff {i j : ℕ} {a b : Fin n} :
    ppPair n i j = some (a, b) ↔ j ≤ i ∧ (a : ℕ) = i - j ∧ (b : ℕ) = j := by
  unfold ppPair
  split_ifs with h
  · simp only [Option.some.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨h.1, rfl, rfl⟩
    · rintro ⟨-, h1, h2⟩
      exact ⟨Fin.ext h1.symm, Fin.ext h2.symm⟩
  · simp only [false_iff, not_and]
    intro hji h1 h2
    exact h ⟨hji, h1 ▸ a.isLt, h2 ▸ b.isLt⟩

/-- Layer `0` holds the partial products. -/
theorem tv_zero (i j : ℕ) : tv x y 0 i j = ppVal x y i j := by
  by_cases h : 0 < wallaceLayers n + 1 ∧ i < 2 * n ∧ j < 2 * n
  · rw [tv_eq_eval x y h, MulCircuit.eval_eq]
    change (ppGate i j).fn (fun k => (circuit n).toCircuit.evalAssign (MulVar.ofInputs x y)
      ((ppGate i j).inputs k)) = _
    rw [fn_ppGate]
    unfold ppVal
    generalize ppPair n i j = o
    rcases o with _ | ⟨a, b⟩ <;> simp
  · rw [tv_of_not x y h]
    unfold ppVal ppPair
    split_ifs with h' <;> simp
    omega

/-- Row `2k` of column `i` in layer `ℓ + 1` is the sum of the `k`-th set of column `i`. -/
theorem tv_succ_even {ℓ i k : ℕ} (hℓ : ℓ < wallaceLayers n) (hi : i < 2 * n) (hk : 2 * k < 2 * n) :
    tv x y (ℓ + 1) i (2 * k) =
      FullAdder.sum (tv x y ℓ i (3 * k)) (tv x y ℓ i (3 * k + 1)) (tv x y ℓ i (3 * k + 2)) := by
  rw [tv_eq_eval x y ⟨by omega, hi, hk⟩, MulCircuit.eval_eq]
  have h1 : 2 * k % 2 = 0 := by omega
  have h2 : 2 * k / 2 = k := by omega
  change (layerGate (ℓ + 1) i (2 * k)).fn (fun k' => (circuit n).toCircuit.evalAssign
    (MulVar.ofInputs x y) ((layerGate (ℓ + 1) i (2 * k)).inputs k')) = _
  rw [layerGate, if_pos h1, h2]
  simp [sumGate, Gate.xor3, tv]

/-- Row `2k + 1` of column `i + 1` in layer `ℓ + 1` is the carry of the `k`-th set of column
`i`. -/
theorem tv_succ_odd {ℓ i k : ℕ} (hℓ : ℓ < wallaceLayers n) (hi : i + 1 < 2 * n)
    (hk : 2 * k + 1 < 2 * n) :
    tv x y (ℓ + 1) (i + 1) (2 * k + 1) =
      FullAdder.carry (tv x y ℓ i (3 * k)) (tv x y ℓ i (3 * k + 1)) (tv x y ℓ i (3 * k + 2)) := by
  rw [tv_eq_eval x y ⟨by omega, hi, hk⟩, MulCircuit.eval_eq]
  have h1 : (2 * k + 1) % 2 ≠ 0 := by omega
  have h2 : (2 * k + 1) / 2 = k := by omega
  change (layerGate (ℓ + 1) (i + 1) (2 * k + 1)).fn (fun k' => (circuit n).toCircuit.evalAssign
    (MulVar.ofInputs x y) ((layerGate (ℓ + 1) (i + 1) (2 * k + 1)).inputs k')) = _
  rw [layerGate, if_neg h1, if_neg (Nat.succ_ne_zero i), h2, Nat.add_sub_cancel]
  simp [carryGate, Gate.maj3, tv]

/-- Column `0` receives no carries. -/
theorem tv_succ_odd_zero {ℓ k : ℕ} (hℓ : ℓ < wallaceLayers n) (hn : 0 < 2 * n)
    (hk : 2 * k + 1 < 2 * n) : tv x y (ℓ + 1) 0 (2 * k + 1) = false := by
  rw [tv_eq_eval x y ⟨by omega, hn, hk⟩, MulCircuit.eval_eq]
  have h1 : (2 * k + 1) % 2 ≠ 0 := by omega
  change (layerGate (ℓ + 1) 0 (2 * k + 1)).fn (fun k' => (circuit n).toCircuit.evalAssign
    (MulVar.ofInputs x y) ((layerGate (ℓ + 1) 0 (2 * k + 1)).inputs k')) = _
  rw [layerGate, if_neg h1, if_pos rfl]
  rfl

/-! ### Weights -/

/-- The number of ones in column `i` of layer `ℓ`. -/
def colW (ℓ i : ℕ) : ℕ := ∑ j ∈ Finset.range (2 * n), (tv x y ℓ i j).toNat

/-- The carry of the `k`-th set of column `i` in layer `ℓ`, into column `i + 1`. -/
def chunkCarry (ℓ i k : ℕ) : Bool :=
  FullAdder.carry (tv x y ℓ i (3 * k)) (tv x y ℓ i (3 * k + 1)) (tv x y ℓ i (3 * k + 2))

/-- The number of carries entering column `i` from layer `ℓ`. -/
def cinW (ℓ i : ℕ) : ℕ :=
  if i = 0 then 0 else ∑ k ∈ Finset.range n, (chunkCarry x y ℓ (i - 1) k).toNat

@[simp] theorem cinW_zero (ℓ : ℕ) : cinW x y ℓ 0 = 0 := rfl

theorem cinW_succ (ℓ i : ℕ) :
    cinW x y ℓ (i + 1) = ∑ k ∈ Finset.range n, (chunkCarry x y ℓ i k).toNat := by
  simp [cinW]

omit x y in
theorem sum_range_three_mul (f : ℕ → ℕ) (m : ℕ) :
    ∑ j ∈ Finset.range (3 * m), f j =
      ∑ k ∈ Finset.range m, (f (3 * k) + f (3 * k + 1) + f (3 * k + 2)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 3 * (m + 1) = 3 * m + 1 + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

omit x y in
theorem sum_range_two_mul (f : ℕ → ℕ) (m : ℕ) :
    ∑ j ∈ Finset.range (2 * m), f j = ∑ k ∈ Finset.range m, (f (2 * k) + f (2 * k + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    ring

/-- The ones of a column of layer `ℓ`, counted set by set: each set of three rows is the sum
bit plus twice the carry bit of its adder. -/
theorem colW_eq_chunks (ℓ i : ℕ) :
    colW x y ℓ i = ∑ k ∈ Finset.range n,
      ((FullAdder.sum (tv x y ℓ i (3 * k)) (tv x y ℓ i (3 * k + 1))
        (tv x y ℓ i (3 * k + 2))).toNat + 2 * (chunkCarry x y ℓ i k).toNat) := by
  have h3 : ∑ j ∈ Finset.range (2 * n), (tv x y ℓ i j).toNat =
      ∑ j ∈ Finset.range (3 * n), (tv x y ℓ i j).toNat := by
    symm
    rw [← Finset.sum_range_add_sum_Ico _ (show 2 * n ≤ 3 * n by omega)]
    rw [Finset.sum_eq_zero (s := Finset.Ico (2 * n) (3 * n)) fun j hj => ?_, add_zero]
    rw [Finset.mem_Ico] at hj
    rw [tv_of_not x y (by omega)]
    rfl
  rw [colW, h3, sum_range_three_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [chunkCarry, FullAdder.toNat_sum_add_two_mul_toNat_carry]

/-- The ones of a column of layer `ℓ + 1`: the sums of its sets and the carries from the
previous column. -/
theorem colW_succ {ℓ i : ℕ} (hℓ : ℓ < wallaceLayers n) (hi : i < 2 * n) :
    colW x y (ℓ + 1) i = (∑ k ∈ Finset.range n,
      (FullAdder.sum (tv x y ℓ i (3 * k)) (tv x y ℓ i (3 * k + 1))
        (tv x y ℓ i (3 * k + 2))).toNat) + cinW x y ℓ i := by
  rw [colW, sum_range_two_mul, Finset.sum_add_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [tv_succ_even x y hℓ hi (by rw [Finset.mem_range] at hk; omega)]
  · cases i with
    | zero =>
      rw [cinW_zero]
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [tv_succ_odd_zero x y hℓ hi (by rw [Finset.mem_range] at hk; omega)]
      rfl
    | succ i =>
      rw [cinW_succ]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [tv_succ_odd x y hℓ hi (by rw [Finset.mem_range] at hk; omega)]
      rfl

/-- The column identity: the ones of a column in the next layer plus twice the carries leaving
it equal its ones plus the carries entering it. -/
theorem colW_succ_add {ℓ i : ℕ} (hℓ : ℓ < wallaceLayers n) (hi : i < 2 * n) :
    colW x y (ℓ + 1) i + 2 * cinW x y ℓ (i + 1) = colW x y ℓ i + cinW x y ℓ i := by
  rw [colW_succ x y hℓ hi, colW_eq_chunks x y ℓ i, cinW_succ, Finset.sum_add_distrib,
    Finset.mul_sum]
  ring

/-- The weighted sum of the columns `lo, …, hi - 1` of layer `ℓ`. -/
def Wint (ℓ lo hi : ℕ) : ℕ := ∑ i ∈ Finset.Ico lo hi, colW x y ℓ i * 2 ^ i

/-- **The weight of a column interval** changes from one layer to the next only by the carries
leaving it at the top and entering it at the bottom. -/
theorem Wint_succ {ℓ : ℕ} (hℓ : ℓ < wallaceLayers n) {lo hi : ℕ} (hlo : lo ≤ hi)
    (hhi : hi ≤ 2 * n) :
    Wint x y (ℓ + 1) lo hi + cinW x y ℓ hi * 2 ^ hi =
      Wint x y ℓ lo hi + cinW x y ℓ lo * 2 ^ lo := by
  induction hi, hlo using Nat.le_induction with
  | base => simp [Wint]
  | succ hi hlo ih =>
    have ih' := ih (by omega)
    have hcol := colW_succ_add x y hℓ (i := hi) (by omega)
    unfold Wint at ih' ⊢
    rw [Finset.sum_Ico_succ_top hlo, Finset.sum_Ico_succ_top hlo, pow_succ]
    zify at ih' hcol ⊢
    linear_combination ih' + (2 : ℤ) ^ hi * hcol

/-- The ones of a column of layer `0` are its partial products evaluating to `1`. -/
theorem colW_zero (i : ℕ) : colW x y 0 i = ppCount x y i := by
  unfold colW ppCount
  simp only [tv_zero]
  rw [Finset.card_filter]
  have h1 : ∑ j ∈ Finset.range (2 * n), (ppVal x y i j).toNat =
      ∑ j ∈ Finset.range (2 * n), if ppVal x y i j = true then 1 else 0 :=
    Finset.sum_congr rfl fun j _ => by cases ppVal x y i j <;> simp
  rw [h1, ← Finset.card_filter, ← Finset.card_filter]
  symm
  refine Finset.card_bij (fun q _ => (q.2 : ℕ)) ?_ ?_ ?_
  · intro q hq
    rw [Finset.mem_filter] at hq
    obtain ⟨-, hc, hpp⟩ := hq
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by have := q.2.isLt; omega, ?_⟩
    have hpair : ppPair n i q.2 = some (q.1, q.2) :=
      ppPair_eq_some_iff.mpr ⟨by omega, by omega, rfl⟩
    rw [ppVal, hpair]
    exact hpp
  · intro q hq q' hq' h
    have hc := (Finset.mem_filter.mp hq).2.1
    have hc' := (Finset.mem_filter.mp hq').2.1
    ext
    · omega
    · exact h
  · intro j hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨-, hpp⟩ := hj
    unfold ppVal at hpp
    rcases hpair : ppPair n i j with _ | ⟨a, b⟩
    · rw [hpair] at hpp
      exact absurd hpp Bool.false_ne_true
    · rw [hpair] at hpp
      obtain ⟨hji, ha, hb⟩ := ppPair_eq_some_iff.mp hpair
      refine ⟨(a, b), ?_, hb⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by change (a : ℕ) + b = i; omega, hpp⟩

/-- The weighted sum of layer `0` is the product. -/
theorem Wint_zero : Wint x y 0 0 (2 * n) = Bits.toNat x * Bits.toNat y := by
  rw [Wint, Bits.toNat_mul_toNat_eq_sum_ppCount, Finset.range_eq_Ico]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [colW_zero]

/-- **Every layer has the weighted sum `x · y`**, and no carry leaves the top column. -/
theorem Wint_eq : ∀ ℓ, ℓ ≤ wallaceLayers n →
    Wint x y ℓ 0 (2 * n) = Bits.toNat x * Bits.toNat y ∧
      (ℓ < wallaceLayers n → cinW x y ℓ (2 * n) = 0) := by
  have hlt : Bits.toNat x * Bits.toNat y < 2 ^ (2 * n) := by
    rw [two_mul, pow_add]
    exact Nat.mul_lt_mul'' (Bits.toNat_lt x) (Bits.toNat_lt y)
  intro ℓ
  induction ℓ with
  | zero =>
    intro _
    refine ⟨Wint_zero x y, fun h0 => ?_⟩
    have := Wint_succ x y h0 (Nat.zero_le (2 * n)) le_rfl
    rw [Wint_zero, cinW_zero, zero_mul, add_zero] at this
    rcases Nat.eq_zero_or_pos (cinW x y 0 (2 * n)) with h | h
    · exact h
    · exfalso
      have := Nat.le_mul_of_pos_left (2 ^ (2 * n)) h
      omega
  | succ ℓ ih =>
    intro hℓ
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hstep := Wint_succ x y (by omega : ℓ < wallaceLayers n) (Nat.zero_le (2 * n)) le_rfl
    rw [ih1, ih2 (by omega), zero_mul, add_zero, cinW_zero, zero_mul, add_zero] at hstep
    refine ⟨hstep, fun h0 => ?_⟩
    have := Wint_succ x y h0 (Nat.zero_le (2 * n)) le_rfl
    rw [hstep, cinW_zero, zero_mul, add_zero] at this
    rcases Nat.eq_zero_or_pos (cinW x y (ℓ + 1) (2 * n)) with h | h
    · exact h
    · exfalso
      have := Nat.le_mul_of_pos_left (2 ^ (2 * n)) h
      omega

/-- The column identity for every column: beyond the top column all quantities vanish. -/
theorem colW_succ_add' {ℓ : ℕ} (hℓ : ℓ < wallaceLayers n) (i : ℕ) :
    colW x y (ℓ + 1) i + 2 * cinW x y ℓ (i + 1) = colW x y ℓ i + cinW x y ℓ i := by
  rcases lt_or_ge i (2 * n) with hi | hi
  · exact colW_succ_add x y hℓ hi
  have hcol : ∀ ℓ', colW x y ℓ' i = 0 := fun ℓ' => by
    unfold colW
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [tv_of_not x y (by omega)]
    rfl
  have hcin : cinW x y ℓ (i + 1) = 0 := by
    rw [cinW_succ]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [chunkCarry, tv_of_not x y (by omega), tv_of_not x y (by omega), tv_of_not x y (by omega)]
    rfl
  rw [hcol, hcol, hcin]
  rcases Nat.eq_or_lt_of_le hi with h | h
  · rw [← h, (Wint_eq x y ℓ hℓ.le).2 hℓ]
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    have hcin' : cinW x y ℓ (i' + 1) = 0 := by
      rw [cinW_succ]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [chunkCarry, tv_of_not x y (by omega), tv_of_not x y (by omega),
        tv_of_not x y (by omega)]
      rfl
    rw [hcin']

/-- The weight of a column interval, for every interval. -/
theorem Wint_succ' {ℓ : ℕ} (hℓ : ℓ < wallaceLayers n) {lo hi : ℕ} (hlo : lo ≤ hi) :
    Wint x y (ℓ + 1) lo hi + cinW x y ℓ hi * 2 ^ hi =
      Wint x y ℓ lo hi + cinW x y ℓ lo * 2 ^ lo := by
  induction hi, hlo using Nat.le_induction with
  | base => simp [Wint]
  | succ hi hlo ih =>
    have hcol := colW_succ_add' x y hℓ hi
    unfold Wint at ih ⊢
    rw [Finset.sum_Ico_succ_top hlo, Finset.sum_Ico_succ_top hlo, pow_succ]
    zify at ih hcol ⊢
    linear_combination ih + (2 : ℤ) ^ hi * hcol

/-! ### The rows shrink -/

/-- The rows beyond `wallaceRows n ℓ` of layer `ℓ` are `0`. -/
theorem tv_eq_false_of_rows : ∀ ℓ, ℓ ≤ wallaceLayers n → ∀ i j, wallaceRows n ℓ ≤ j →
    tv x y ℓ i j = false := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro _ i j hj
    change n ≤ j at hj
    rw [tv_zero]
    unfold ppVal ppPair
    split_ifs with h
    · exfalso
      exact absurd h.2.2 (by omega)
    · rfl
  | succ ℓ ih =>
    intro hℓ i j hj
    by_cases hb : i < 2 * n ∧ j < 2 * n
    · rw [wallaceRows_succ] at hj
      rcases Nat.even_or_odd' j with ⟨k, rfl | rfl⟩
      · rw [tv_succ_even x y (by omega) hb.1 hb.2]
        have hN : wallaceRows n ℓ ≤ 3 * k := by omega
        rw [ih (by omega) i (3 * k) hN, ih (by omega) i (3 * k + 1) (by omega),
          ih (by omega) i (3 * k + 2) (by omega)]
        rfl
      · cases i with
        | zero => exact tv_succ_odd_zero x y (by omega) hb.1 hb.2
        | succ i =>
          rw [tv_succ_odd x y (by omega) hb.1 hb.2]
          have hN : wallaceRows n ℓ ≤ 3 * k + 1 := by omega
          rw [ih (by omega) i (3 * k + 1) hN, ih (by omega) i (3 * k + 2) (by omega)]
          cases tv x y ℓ i (3 * k) <;> rfl
    · exact tv_of_not x y (by omega)

/-- In the last layer only the rows `0` and `1` are nonzero. -/
theorem tv_last (i j : ℕ) (hj : 2 ≤ j) : tv x y (wallaceLayers n) i j = false :=
  tv_eq_false_of_rows x y _ le_rfl i j ((wallaceRows_wallaceLayers_le n).trans hj)

/-- The first summand of the final adder, as a bit sequence. -/
def aVal (i : ℕ) : Bool := tv x y (wallaceLayers n) i 0

/-- The second summand of the final adder, as a bit sequence. -/
def bVal (i : ℕ) : Bool := tv x y (wallaceLayers n) i 1

theorem aVal_of_le {i : ℕ} (hi : 2 * n ≤ i) : aVal x y i = false :=
  tv_of_not x y (by omega)

theorem bVal_of_le {i : ℕ} (hi : 2 * n ≤ i) : bVal x y i = false :=
  tv_of_not x y (by omega)

/-- The ones of a column of the last layer are its two summand bits. -/
theorem colW_last (i : ℕ) (hi : i < 2 * n) :
    colW x y (wallaceLayers n) i = (aVal x y i).toNat + (bVal x y i).toNat := by
  unfold colW
  rw [← Finset.sum_range_add_sum_Ico _ (show 2 ≤ 2 * n by omega),
    Finset.sum_eq_zero (s := Finset.Ico 2 (2 * n)) fun j hj => ?_, add_zero]
  · simp [Finset.sum_range_succ, aVal, bVal]
  · rw [Finset.mem_Ico] at hj
    rw [tv_last x y i j hj.1]
    rfl

/-- The two summands of the final adder represent the product. -/
theorem toNat_aVal_add_bVal :
    ∑ i ∈ Finset.range (2 * n), ((aVal x y i).toNat + (bVal x y i).toNat) * 2 ^ i =
      Bits.toNat x * Bits.toNat y := by
  rw [← (Wint_eq x y _ le_rfl).1, Wint, Finset.range_eq_Ico]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_Ico] at hi
  rw [colW_last x y i hi.2]

/-! ### The carry-lookahead adder -/

/-- The propagate signals of the final addition. -/
def pSig : ℕ → Bool := CLA.prop (aVal x y) (bVal x y)

/-- The generate signals of the final addition. -/
def qSig : ℕ → Bool := CLA.gen (aVal x y) (bVal x y)

theorem evalAssign_aVar (i : ℕ) :
    (circuit n).toCircuit.evalAssign (MulVar.ofInputs x y) (aVar i) = aVal x y i := rfl

theorem evalAssign_bVar (i : ℕ) :
    (circuit n).toCircuit.evalAssign (MulVar.ofInputs x y) (bVar i) = bVal x y i := rfl

theorem eval_p (i : Fin (claWidth n)) : (circuit n).eval x y (.p i) = pSig x y i := by
  rw [MulCircuit.eval_eq]
  change (Gate.xor2 (aVar i) (bVar i)).fn (fun k => (circuit n).toCircuit.evalAssign
    (MulVar.ofInputs x y) ((Gate.xor2 (aVar i) (bVar i)).inputs k)) = _
  simp [Gate.xor2, evalAssign_aVar, evalAssign_bVar, pSig, CLA.prop]

theorem eval_q (i : Fin (claWidth n)) : (circuit n).eval x y (.q i) = qSig x y i := by
  rw [MulCircuit.eval_eq]
  change (Gate.and2 (aVar i) (bVar i)).fn (fun k => (circuit n).toCircuit.evalAssign
    (MulVar.ofInputs x y) ((Gate.and2 (aVar i) (bVar i)).inputs k)) = _
  simp [Gate.and2, evalAssign_aVar, evalAssign_bVar, qSig, CLA.gen]

theorem pSig_of_le {i : ℕ} (hi : claWidth n ≤ i) : pSig x y i = false := by
  have := two_mul_le_claWidth n
  change CLA.prop (aVal x y) (bVal x y) i = false
  rw [CLA.prop, aVal_of_le x y (by omega : 2 * n ≤ i), bVal_of_le x y (by omega : 2 * n ≤ i)]
  rfl

theorem qSig_of_le {i : ℕ} (hi : claWidth n ≤ i) : qSig x y i = false := by
  have := two_mul_le_claWidth n
  change CLA.gen (aVal x y) (bVal x y) i = false
  rw [CLA.gen, aVal_of_le x y (by omega : 2 * n ≤ i), bVal_of_le x y (by omega : 2 * n ≤ i)]
  rfl

theorem evalAssign_pVar (i : ℕ) :
    (circuit n).toCircuit.evalAssign (MulVar.ofInputs x y) (pVar i) = pSig x y i := by
  unfold pVar
  split_ifs with h
  · simp [eval_p]
  · simp [pSig_of_le x y (not_lt.mp h)]

theorem evalAssign_qVar (i : ℕ) :
    (circuit n).toCircuit.evalAssign (MulVar.ofInputs x y) (qVar i) = qSig x y i := by
  unfold qVar
  split_ifs with h
  · simp [eval_q]
  · simp [qSig_of_le x y (not_lt.mp h)]

/-- The group pairs: the block `m` at level `ℓ` covers the positions `m 4^ℓ, …, (m+1) 4^ℓ - 1`,
and its pair is the group propagate and generate of that interval. -/
theorem evalAssign_PVar_QVar : ∀ ℓ, ℓ ≤ claLevels n → ∀ m, m < 4 ^ (claLevels n - ℓ) →
    (circuit n).toCircuit.evalAssign (MulVar.ofInputs x y) (PVar ℓ m) =
        allProp (pSig x y) (m * 4 ^ ℓ) (4 ^ ℓ) ∧
      (circuit n).toCircuit.evalAssign (MulVar.ofInputs x y) (QVar ℓ m) =
        foldCarry (pSig x y) (qSig x y) (m * 4 ^ ℓ) (4 ^ ℓ) false := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro _ m _
    simp only [PVar, QVar, pow_zero, mul_one, allProp_one, foldCarry_one, Bool.and_false,
      Bool.xor_false]
    exact ⟨evalAssign_pVar x y m, evalAssign_qVar x y m⟩
  | succ ℓ ih =>
    intro hℓ m hm
    have hℓ' : ℓ < claLevels n := by omega
    have hmW : m < claWidth n := by
      unfold claWidth
      exact lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hsub : ∀ t, t < 4 → 4 * m + t < 4 ^ (claLevels n - ℓ) := by
      intro t ht
      have : claLevels n - ℓ = (claLevels n - (ℓ + 1)) + 1 := by omega
      rw [this, pow_succ]
      omega
    have hpos : ∀ t, (4 * m + t) * 4 ^ ℓ = m * (4 * 4 ^ ℓ) + t * 4 ^ ℓ := by
      intro t
      ring
    have hP : (circuit n).toCircuit.evalAssign (MulVar.ofInputs x y) (PVar (ℓ + 1) m) =
        allProp (pSig x y) (m * 4 ^ (ℓ + 1)) (4 ^ (ℓ + 1)) := by
      rw [PVar, dif_pos (And.intro hℓ' hmW), MulCircuit.evalAssign_wire, MulCircuit.eval_eq,
        circuit_gate, show gate (P ⟨ℓ, hℓ'⟩ ⟨m, hmW⟩) = (if m < 4 ^ (claLevels n - (ℓ + 1)) then
          Gate.allN 4 (fun t => PVar ℓ (4 * m + t)) else Gate.const false) from rfl, if_pos hm,
        Gate.fn_allN]
      rw [show 4 ^ (ℓ + 1) = 4 * 4 ^ ℓ from pow_succ' 4 ℓ, ← allProp_blocks]
      apply allProp_congr
      intro t _ ht
      rw [Nat.zero_add] at ht
      show (circuit n).toCircuit.evalAssign (MulVar.ofInputs x y) (PVar ℓ (4 * m + t)) =
        allProp (pSig x y) (m * (4 * 4 ^ ℓ) + t * 4 ^ ℓ) (4 ^ ℓ)
      rw [(ih (by omega) (4 * m + t) (hsub t ht)).1, hpos]
    have hQ : (circuit n).toCircuit.evalAssign (MulVar.ofInputs x y) (QVar (ℓ + 1) m) =
        foldCarry (pSig x y) (qSig x y) (m * 4 ^ (ℓ + 1)) (4 ^ (ℓ + 1)) false := by
      rw [QVar, dif_pos (And.intro hℓ' hmW), MulCircuit.evalAssign_wire, MulCircuit.eval_eq,
        circuit_gate, show gate (Q ⟨ℓ, hℓ'⟩ ⟨m, hmW⟩) = (if m < 4 ^ (claLevels n - (ℓ + 1)) then
          Gate.carryFold 4 (fun t => PVar ℓ (4 * m + t)) (fun t => QVar ℓ (4 * m + t))
            (.wire .zero) else Gate.const false) from rfl, if_pos hm,
        Gate.fn_carryFold, MulCircuit.evalAssign_wire, eval_zero]
      rw [show 4 ^ (ℓ + 1) = 4 * 4 ^ ℓ from pow_succ' 4 ℓ, ← foldCarry_blocks]
      apply foldCarry_congr
      intro t _ ht
      rw [Nat.zero_add] at ht
      show (circuit n).toCircuit.evalAssign (MulVar.ofInputs x y) (PVar ℓ (4 * m + t)) =
          allProp (pSig x y) (m * (4 * 4 ^ ℓ) + t * 4 ^ ℓ) (4 ^ ℓ) ∧
        (circuit n).toCircuit.evalAssign (MulVar.ofInputs x y) (QVar ℓ (4 * m + t)) =
          foldCarry (pSig x y) (qSig x y) (m * (4 * 4 ^ ℓ) + t * 4 ^ ℓ) (4 ^ ℓ) false
      rw [(ih (by omega) (4 * m + t) (hsub t ht)).1, (ih (by omega) (4 * m + t) (hsub t ht)).2,
        hpos]
      exact ⟨rfl, rfl⟩
    exact ⟨hP, hQ⟩

/-- A real group propagate wire: the group propagate of its interval. -/
theorem eval_P (ℓ : Fin (claLevels n)) (m : Fin (claWidth n))
    (hm : (m : ℕ) < 4 ^ (claLevels n - (ℓ + 1))) :
    (circuit n).eval x y (.P ℓ m) =
      allProp (pSig x y) (m * 4 ^ ((ℓ : ℕ) + 1)) (4 ^ ((ℓ : ℕ) + 1)) := by
  have := (evalAssign_PVar_QVar x y (ℓ + 1) ℓ.isLt m hm).1
  rwa [PVar, dif_pos (And.intro ℓ.isLt m.isLt), MulCircuit.evalAssign_wire] at this

/-- A real group generate wire: the group generate of its interval. -/
theorem eval_Q (ℓ : Fin (claLevels n)) (m : Fin (claWidth n))
    (hm : (m : ℕ) < 4 ^ (claLevels n - (ℓ + 1))) :
    (circuit n).eval x y (.Q ℓ m) =
      foldCarry (pSig x y) (qSig x y) (m * 4 ^ ((ℓ : ℕ) + 1)) (4 ^ ((ℓ : ℕ) + 1)) false := by
  have := (evalAssign_PVar_QVar x y (ℓ + 1) ℓ.isLt m hm).2
  rwa [QVar, dif_pos (And.intro ℓ.isLt m.isLt), MulCircuit.evalAssign_wire] at this

/-- A nonexistent group propagate wire computes `0`. -/
theorem eval_P_of_not (ℓ : Fin (claLevels n)) (m : Fin (claWidth n))
    (hm : ¬ (m : ℕ) < 4 ^ (claLevels n - (ℓ + 1))) : (circuit n).eval x y (.P ℓ m) = false := by
  rw [MulCircuit.eval_eq, circuit_gate, show gate (P ℓ m) =
    (if (m : ℕ) < 4 ^ (claLevels n - (ℓ + 1)) then Gate.allN 4 (fun t => PVar ℓ (4 * m + t))
      else Gate.const false) from rfl, if_neg hm]
  rfl

/-- A nonexistent group generate wire computes `0`. -/
theorem eval_Q_of_not (ℓ : Fin (claLevels n)) (m : Fin (claWidth n))
    (hm : ¬ (m : ℕ) < 4 ^ (claLevels n - (ℓ + 1))) : (circuit n).eval x y (.Q ℓ m) = false := by
  rw [MulCircuit.eval_eq, circuit_gate, show gate (Q ℓ m) =
    (if (m : ℕ) < 4 ^ (claLevels n - (ℓ + 1)) then Gate.carryFold 4 (fun t => PVar ℓ (4 * m + t))
      (fun t => QVar ℓ (4 * m + t)) (.wire .zero) else Gate.const false) from rfl, if_neg hm]
  rfl

/-- The carries: `c_i` is the carry into position `i` of the final addition. -/
theorem evalAssign_cVar : ∀ i, i < claWidth n →
    (circuit n).toCircuit.evalAssign (MulVar.ofInputs x y) (cVar i) =
      CLA.carry (aVal x y) (bVal x y) i := by
  intro i
  refine Nat.strong_induction_on i ?_
  intro i ih hi
  rw [cVar, dif_pos hi, MulCircuit.evalAssign_wire, MulCircuit.eval_eq, circuit_gate,
    show gate (c ⟨i, hi⟩) = cGate i from rfl]
  by_cases h0 : i = 0
  · subst h0
    rw [cGate, if_pos rfl]
    rfl
  · rw [cGate, if_neg h0, Gate.fn_carryFold]
    have hi' : 0 < i := Nat.pos_of_ne_zero h0
    have hv : val4 i < claLevels n := val4_lt hi' hi
    have hdec := claM_R_eq i
    have hsum : 4 * claM i * 4 ^ val4 i + claR i * 4 ^ val4 i = i := by
      rw [← Nat.add_mul]
      exact hdec
    have hlt : 4 * claM i * 4 ^ val4 i < i := by
      have h2 : 0 < claR i * 4 ^ val4 i := Nat.mul_pos (claR_pos hi') (by positivity)
      omega
    have hblock : 4 * claM i + claR i < 4 ^ (claLevels n - val4 i) := by
      have h1 : (4 * claM i + claR i) * 4 ^ val4 i <
          4 ^ (claLevels n - val4 i) * 4 ^ val4 i := by
        rw [hdec, ← pow_add, Nat.sub_add_cancel hv.le]
        exact hi
      exact Nat.lt_of_mul_lt_mul_right h1
    rw [ih _ hlt (by omega)]
    rw [foldCarry_congr _ _
      (p' := fun t => allProp (pSig x y) (4 * claM i * 4 ^ val4 i + t * 4 ^ val4 i) (4 ^ val4 i))
      (q' := fun t => foldCarry (pSig x y) (qSig x y) (4 * claM i * 4 ^ val4 i + t * 4 ^ val4 i)
        (4 ^ val4 i) false) 0 (claR i) _ ?_, foldCarry_blocks, pSig, qSig,
      ← CLA.carry_eq_foldCarry, hsum]
    intro t _ ht
    rw [Nat.zero_add] at ht
    have hpos : (4 * claM i + t) * 4 ^ val4 i = 4 * claM i * 4 ^ val4 i + t * 4 ^ val4 i := by
      ring
    obtain ⟨hP, hQ⟩ := evalAssign_PVar_QVar x y (val4 i) hv.le (4 * claM i + t) (by omega)
    rw [hpos] at hP hQ
    exact ⟨hP, hQ⟩

theorem eval_c (i : Fin (claWidth n)) :
    (circuit n).eval x y (.c i) = CLA.carry (aVal x y) (bVal x y) i := by
  have := evalAssign_cVar x y i i.isLt
  rwa [cVar, dif_pos i.isLt, MulCircuit.evalAssign_wire] at this

/-- The sum bits: `s_i` is the bit `i` of the final addition. -/
theorem eval_s (i : Fin (claWidth n)) :
    (circuit n).eval x y (.s i) = CLA.sumBit (aVal x y) (bVal x y) i := by
  rw [MulCircuit.eval_eq]
  change (Gate.xor2 (pVar i) (cVar i)).fn (fun k => (circuit n).toCircuit.evalAssign
    (MulVar.ofInputs x y) ((Gate.xor2 (pVar i) (cVar i)).inputs k)) = _
  simp only [Gate.xor2]
  rw [CLA.sumBit_eq]
  simp [evalAssign_pVar, evalAssign_cVar x y i i.isLt, pSig]

/-! ### The output -/

/-- The output bits: the sum bits `s_0, …, s_{2n-1}` of the final adder. -/
def out (n : ℕ) (i : Fin (2 * n)) : WWire n :=
  .s ⟨i, lt_of_lt_of_le i.isLt (two_mul_le_claWidth n)⟩

theorem out_injective (n : ℕ) : Function.Injective (out n) := by
  intro i j h
  simp only [out, WWire.s.injEq, Fin.mk.injEq] at h
  exact Fin.ext h

/-- **The output represents the product.** Paper: Observation [obs:wallace-exact]. -/
theorem toNat_out :
    Bits.toNat (fun i => (circuit n).eval x y (out n i)) = Bits.toNat x * Bits.toNat y := by
  have hprod := toNat_aVal_add_bVal x y
  have hlt : Bits.toNat x * Bits.toNat y < 2 ^ (2 * n) := by
    rw [two_mul, pow_add]
    exact Nat.mul_lt_mul'' (Bits.toNat_lt x) (Bits.toNat_lt y)
  have hW := two_mul_le_claWidth n
  have hsum := CLA.toNat_sumBit (aVal x y) (bVal x y) (claWidth n)
  have htail : ∑ i ∈ Finset.range (claWidth n), ((aVal x y i).toNat + (bVal x y i).toNat) * 2 ^ i =
      Bits.toNat x * Bits.toNat y := by
    rw [← Finset.sum_range_add_sum_Ico _ hW, hprod,
      Finset.sum_eq_zero (s := Finset.Ico (2 * n) (claWidth n)) fun i hi => ?_, add_zero]
    rw [Finset.mem_Ico] at hi
    rw [aVal_of_le x y hi.1, bVal_of_le x y hi.1]
    simp
  rw [htail] at hsum
  have hW2 : 2 ^ (2 * n) ≤ 2 ^ claWidth n := Nat.pow_le_pow_right (by norm_num) hW
  have hcarry : (CLA.carry (aVal x y) (bVal x y) (claWidth n)).toNat = 0 := by
    cases h : CLA.carry (aVal x y) (bVal x y) (claWidth n)
    · rfl
    · exfalso
      rw [h, Bool.toNat_true, one_mul] at hsum
      omega
  rw [hcarry, zero_mul, add_zero, ← Finset.sum_range_add_sum_Ico _ hW] at hsum
  have hdvd : 2 ^ (2 * n) ∣ ∑ i ∈ Finset.Ico (2 * n) (claWidth n),
      (CLA.sumBit (aVal x y) (bVal x y) i).toNat * 2 ^ i := by
    refine Finset.dvd_sum fun i hi => ?_
    rw [Finset.mem_Ico] at hi
    exact Dvd.dvd.mul_left (pow_dvd_pow 2 hi.1) _
  have htail2 : ∑ i ∈ Finset.Ico (2 * n) (claWidth n),
      (CLA.sumBit (aVal x y) (bVal x y) i).toNat * 2 ^ i = 0 := by
    obtain ⟨T, hT⟩ := hdvd
    rw [hT] at hsum ⊢
    rcases Nat.eq_zero_or_pos T with h | h
    · rw [h, mul_zero]
    · exfalso
      have := Nat.le_mul_of_pos_right (2 ^ (2 * n)) h
      omega
  rw [htail2, add_zero] at hsum
  rw [← hsum, Bits.toNat,
    ← Fin.sum_univ_eq_sum_range (fun i => (CLA.sumBit (aVal x y) (bVal x y) i).toNat * 2 ^ i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [out, eval_s]

end WWire

/-- **The Wallace-tree multiplier** with a carry-lookahead adder, as an exact multiplier
encoding. Paper: Definition [def:wallace], Observation [obs:wallace-exact]. -/
def wallaceMul (n : ℕ) : MulEncoding n :=
  MulEncoding.ofMulCircuit (WWire.circuit n) (WWire.out n) (WWire.out_injective n)
    WWire.toNat_out

end AssocLB
