/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/
import AssocLB.Multiplier.WallaceTree

/-!
# Wallace-tree multipliers are strip-local

Paper: Appendix, Lemma [lem:wallace-tree-local] (Wallace-tree strip-locality), Lemma
[lem:cla-local] (carry-lookahead adder strip-locality) and Proposition
[prop:wallace-strip-local].

## Main results

* `foldCarry_local`: the interval argument of Lemma [lem:cla-local]: if two signal pairs vanish
  at every top column and agree on the strip of the last position of an interval, then the
  group propagate and generate of the interval agree.
* `WWire.strip_zero`: under a `g`-sparse restriction, no carry enters a strip and every
  strip's weighted sum stays below `2^(g-1) · 2^(bg)` in every layer (the induction of Lemma
  [lem:wallace-tree-local]); `WWire.tv_top_eq_false`: every layer variable in the top column
  of a strip is `0`.
* `WWire.tv_congr`: every layer variable is a function of the partial products of its strip.
* `WWire.eval_local`: every wire is a function of the partial products of the strip
  `WWire.stripOf g w`.
* `wallaceMul_stripLocal`: the Wallace-tree multiplier is strip-local, Proposition
  [prop:wallace-strip-local].

## Design notes

* The paper's `(P_I, Q_I)` for an interval `I = [a, i]` are `allProp p a (i + 1 - a)` and
  `foldCarry p q a (i + 1 - a) false`; the carry `c_i` is `foldCarry p q 0 i false`
  (`CLA.carry_eq`), which is how the carry wires are related to intervals here. The
  top-column argument uses `allProp_of_zero_at` and `foldCarry_of_zero_at` at the highest top
  column below the end of the interval.
* Strip-locality of a wire is proved directly from the wire's semantics rather than by
  induction on the circuit, so no separate treatment of "constant" wires is needed: a wire
  whose value does not depend on the inputs is local to every strip.
-/

namespace AssocLB

/-! ### Locality of the carry-lookahead folds -/

/-- **Carry-lookahead locality** (the interval argument of Lemma [lem:cla-local]). If two
signal pairs vanish at every top column `s` (`g ∣ s + 1`) and agree on the strip `b`
containing the last position of the interval `[lo, lo + r)`, then the group propagate and the
group generate of the interval agree. -/
theorem foldCarry_local {g : ℕ} {p q p' q' : ℕ → Bool}
    (hz : ∀ s, g ∣ s + 1 → p s = false ∧ q s = false)
    (hz' : ∀ s, g ∣ s + 1 → p' s = false ∧ q' s = false)
    {lo r : ℕ} (hr : 1 ≤ r) {b : ℕ} (hb : InStrip g b (lo + r - 1))
    (hagree : ∀ t, InStrip g b t → p t = p' t ∧ q t = q' t) :
    allProp p lo r = allProp p' lo r ∧ foldCarry p q lo r false = foldCarry p' q' lo r false := by
  obtain ⟨hb1, hb2⟩ := hb
  rw [add_one_mul] at hb2
  rcases le_or_gt (b * g) lo with hlo | hlo
  · have hin : ∀ t, lo ≤ t → t < lo + r → InStrip g b t := fun t h1 h2 =>
      ⟨by omega, by rw [add_one_mul]; omega⟩
    exact ⟨allProp_congr p lo r fun t h1 h2 => (hagree t (hin t h1 h2)).1,
      foldCarry_congr p q lo r false fun t h1 h2 => hagree t (hin t h1 h2)⟩
  · have hs : g ∣ (b * g - 1) + 1 := by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ b * g)]
      exact Dvd.intro_left b rfl
    have hrange : lo ≤ b * g - 1 ∧ b * g - 1 < lo + r := ⟨by omega, by omega⟩
    obtain ⟨hp, hq⟩ := hz _ hs
    obtain ⟨hp', hq'⟩ := hz' _ hs
    refine ⟨?_, ?_⟩
    · rw [allProp_of_zero_at p hrange hp, allProp_of_zero_at p' hrange hp']
    · rw [foldCarry_of_zero_at p q hrange hp hq, foldCarry_of_zero_at p' q' hrange hp' hq']
      have hin : ∀ t, b * g - 1 + 1 ≤ t → t < b * g - 1 + 1 + (lo + r - (b * g - 1 + 1)) →
          InStrip g b t := fun t h1 h2 => ⟨by omega, by rw [add_one_mul]; omega⟩
      exact foldCarry_congr p q _ _ false fun t h1 h2 => hagree t (hin t h1 h2)

namespace WWire

variable {n : ℕ} (x y : Bits n)

/-! ### The Wallace tree under a sparse restriction -/

/-- Under a `g`-sparse restriction, a column that is not a multiple of `g` holds no partial
product evaluating to `1`. -/
theorem colW_zero_of_not_dvd {g : ℕ} {ρ : InputRestriction n} (hρ : ρ.IsSparse g)
    (hxy : ρ.Extends x y) {c : ℕ} (hc : ¬ g ∣ c) : colW x y 0 c = 0 := by
  rw [colW_zero]
  by_contra h
  exact hc (hρ.dvd_of_ppCount_ne_zero hxy h)

/-- Under a `g`-sparse restriction, every column holds fewer than `2^(g-1)` partial products
evaluating to `1`. -/
theorem colW_zero_lt {g : ℕ} {ρ : InputRestriction n} (hρ : ρ.IsSparse g)
    (hxy : ρ.Extends x y) (c : ℕ) : colW x y 0 c < 2 ^ (g - 1) := by
  rw [colW_zero]
  exact lt_of_le_of_lt (ppCount_le_card_liveInColumn ρ hxy c) (hρ.2 c)

/-- The weight of a strip in layer `0` is below `2^(g-1) · 2^(bg)`: all its partial products
lie in the base column. -/
theorem Wint_zero_strip {g : ℕ} (hg : 1 ≤ g) {ρ : InputRestriction n} (hρ : ρ.IsSparse g)
    (hxy : ρ.Extends x y) (b : ℕ) :
    Wint x y 0 (b * g) ((b + 1) * g) < 2 ^ (g - 1) * 2 ^ (b * g) := by
  unfold Wint
  rw [Finset.sum_eq_single (b * g)]
  · exact Nat.mul_lt_mul_of_pos_right (colW_zero_lt x y hρ hxy _) (by positivity)
  · intro c hc hne
    rw [Finset.mem_Ico, add_one_mul] at hc
    rw [colW_zero_of_not_dvd x y hρ hxy, zero_mul]
    rintro ⟨k, rfl⟩
    have hbk : b ≤ k :=
      Nat.le_of_mul_le_mul_right (by rw [mul_comm k g]; exact hc.1) (by omega)
    have hkb : k < b + 1 :=
      Nat.lt_of_mul_lt_mul_right
        (show k * g < (b + 1) * g by rw [mul_comm k g, add_one_mul]; exact hc.2)
    exact hne (by rw [show k = b by omega, mul_comm])
  · intro h
    exact absurd (Finset.mem_Ico.mpr ⟨le_rfl, by rw [add_one_mul]; omega⟩) h

/-- If no carry enters the strip with base `bg`, its weight stays below `2^(g-1) · 2^(bg)` in
every layer. -/
theorem strip_weight {g : ℕ} (hg : 1 ≤ g) {ρ : InputRestriction n} (hρ : ρ.IsSparse g)
    (hxy : ρ.Extends x y) (b : ℕ) (hb : ∀ ℓ, ℓ < wallaceLayers n → cinW x y ℓ (b * g) = 0) :
    ∀ ℓ, ℓ ≤ wallaceLayers n →
      Wint x y ℓ (b * g) ((b + 1) * g) < 2 ^ (g - 1) * 2 ^ (b * g) := by
  intro ℓ
  induction ℓ with
  | zero => exact fun _ => Wint_zero_strip x y hg hρ hxy b
  | succ ℓ ih =>
    intro hℓ
    have h2 := Wint_succ' x y (by omega : ℓ < wallaceLayers n)
      (show b * g ≤ (b + 1) * g by rw [add_one_mul]; omega)
    rw [hb ℓ (by omega), zero_mul, add_zero] at h2
    omega

/-- If the weight of a strip is below `2^(g-1) · 2^(bg) = 2^((b+1)g - 1)`, its top column is
`0`. -/
theorem tv_top_eq_false_of_weight {g : ℕ} (hg : 1 ≤ g) {ℓ b : ℕ}
    (hw : Wint x y ℓ (b * g) ((b + 1) * g) < 2 ^ (g - 1) * 2 ^ (b * g)) (j : ℕ) :
    tv x y ℓ ((b + 1) * g - 1) j = false := by
  have hmem : (b + 1) * g - 1 ∈ Finset.Ico (b * g) ((b + 1) * g) := by
    rw [Finset.mem_Ico, add_one_mul]
    omega
  unfold Wint at hw
  have hle : colW x y ℓ ((b + 1) * g - 1) * 2 ^ ((b + 1) * g - 1) ≤
      ∑ i ∈ Finset.Ico (b * g) ((b + 1) * g), colW x y ℓ i * 2 ^ i :=
    Finset.single_le_sum (f := fun i => colW x y ℓ i * 2 ^ i) (fun _ _ => Nat.zero_le _) hmem
  have hpow : 2 ^ (g - 1) * 2 ^ (b * g) = 2 ^ ((b + 1) * g - 1) := by
    rw [← pow_add, add_one_mul]
    congr 1
    omega
  rw [hpow] at hw
  have hcol : colW x y ℓ ((b + 1) * g - 1) = 0 := by
    by_contra h
    have : 1 * 2 ^ ((b + 1) * g - 1) ≤ colW x y ℓ ((b + 1) * g - 1) * 2 ^ ((b + 1) * g - 1) :=
      Nat.mul_le_mul_right _ (Nat.one_le_iff_ne_zero.mpr h)
    omega
  unfold colW at hcol
  rcases lt_or_ge j (2 * n) with hj | hj
  · have := (Finset.sum_eq_zero_iff.mp hcol) j (Finset.mem_range.mpr hj)
    cases h : tv x y ℓ ((b + 1) * g - 1) j
    · rfl
    · rw [h] at this
      exact absurd this (by simp)
  · exact tv_of_not x y (by omega)

/-- If the weight of a strip is below `2^(g-1) · 2^(bg)`, no carry leaves it. -/
theorem cinW_top {g : ℕ} (hg : 1 ≤ g) {ℓ b : ℕ}
    (hw : Wint x y ℓ (b * g) ((b + 1) * g) < 2 ^ (g - 1) * 2 ^ (b * g)) :
    cinW x y ℓ ((b + 1) * g) = 0 := by
  have h1 : (b + 1) * g = ((b + 1) * g - 1) + 1 := by
    rw [add_one_mul]
    omega
  rw [h1, cinW_succ]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [chunkCarry, tv_top_eq_false_of_weight x y hg hw, tv_top_eq_false_of_weight x y hg hw,
    tv_top_eq_false_of_weight x y hg hw]
  rfl

/-- **The strip induction** of Lemma [lem:wallace-tree-local]: under a `g`-sparse restriction,
no carry enters any strip, and every strip's weight stays below `2^(g-1) · 2^(bg)` in every
layer. -/
theorem strip_zero {g : ℕ} (hg : 1 ≤ g) {ρ : InputRestriction n} (hρ : ρ.IsSparse g)
    (hxy : ρ.Extends x y) : ∀ b, (∀ ℓ, ℓ < wallaceLayers n → cinW x y ℓ (b * g) = 0) ∧
      ∀ ℓ, ℓ ≤ wallaceLayers n →
        Wint x y ℓ (b * g) ((b + 1) * g) < 2 ^ (g - 1) * 2 ^ (b * g) := by
  intro b
  induction b with
  | zero =>
    have hcin : ∀ ℓ, ℓ < wallaceLayers n → cinW x y ℓ (0 * g) = 0 := fun ℓ _ => by
      rw [Nat.zero_mul, cinW_zero]
    exact ⟨hcin, strip_weight x y hg hρ hxy 0 hcin⟩
  | succ b ih =>
    have hcin : ∀ ℓ, ℓ < wallaceLayers n → cinW x y ℓ ((b + 1) * g) = 0 := fun ℓ hℓ =>
      cinW_top x y hg (ih.2 ℓ hℓ.le)
    exact ⟨hcin, strip_weight x y hg hρ hxy (b + 1) hcin⟩

/-- **Top columns are `0`** (Lemma [lem:wallace-tree-local]): under a `g`-sparse restriction,
every layer variable in a top column `c` (`g ∣ c + 1`) is `0`. -/
theorem tv_top_eq_false {g : ℕ} (hg : 1 ≤ g) {ρ : InputRestriction n} (hρ : ρ.IsSparse g)
    (hxy : ρ.Extends x y) {ℓ : ℕ} (hℓ : ℓ ≤ wallaceLayers n) {c : ℕ} (hc : g ∣ c + 1) (j : ℕ) :
    tv x y ℓ c j = false := by
  obtain ⟨k, hk⟩ := hc
  have hk1 : k ≠ 0 := by
    rintro rfl
    omega
  obtain ⟨b, rfl⟩ : ∃ b, k = b + 1 := ⟨k - 1, by omega⟩
  have hc : c = (b + 1) * g - 1 := by
    rw [mul_comm] at hk
    omega
  rw [hc]
  exact tv_top_eq_false_of_weight x y hg ((strip_zero x y hg hρ hxy b).2 ℓ hℓ) j

/-- **Layer variables are strip-local** (Lemma [lem:wallace-tree-local]): two extensions of a
`g`-sparse restriction agreeing on the partial products of the strip `b` agree on every layer
variable in the columns of the strip. -/
theorem tv_congr {g : ℕ} (hg : 1 ≤ g) {ρ : InputRestriction n} (hρ : ρ.IsSparse g)
    {x' y' : Bits n} (hxy : ρ.Extends x y) (hxy' : ρ.Extends x' y') {b : ℕ}
    (hagree : ∀ i j : Fin n, InStrip g b ((i : ℕ) + j) →
      partialProduct x y i j = partialProduct x' y' i j) :
    ∀ ℓ, ℓ ≤ wallaceLayers n → ∀ i, InStrip g b i → ∀ j, tv x y ℓ i j = tv x' y' ℓ i j := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro _ i hi j
    rw [tv_zero, tv_zero]
    unfold ppVal
    rcases hpair : ppPair n i j with _ | ⟨a, b'⟩
    · rfl
    · obtain ⟨hji, ha, hb'⟩ := ppPair_eq_some_iff.mp hpair
      have hab : (a : ℕ) + b' = i := by omega
      exact hagree a b' (hab ▸ hi)
  | succ ℓ ih =>
    intro hℓ i hi j
    by_cases hb : i < 2 * n ∧ j < 2 * n
    · rcases Nat.even_or_odd' j with ⟨k, rfl | rfl⟩
      · rw [tv_succ_even x y (by omega) hb.1 hb.2, tv_succ_even x' y' (by omega) hb.1 hb.2,
          ih (by omega) i hi, ih (by omega) i hi, ih (by omega) i hi]
      · cases i with
        | zero =>
          rw [tv_succ_odd_zero x y (by omega) hb.1 hb.2,
            tv_succ_odd_zero x' y' (by omega) hb.1 hb.2]
        | succ i =>
          rw [tv_succ_odd x y (by omega) hb.1 hb.2, tv_succ_odd x' y' (by omega) hb.1 hb.2]
          by_cases hi' : InStrip g b i
          · rw [ih (by omega) i hi', ih (by omega) i hi', ih (by omega) i hi']
          · have hdvd : g ∣ i + 1 := by
              obtain ⟨h1, h2⟩ := hi
              have : i + 1 = b * g := by
                by_contra hne
                exact hi' ⟨by omega, by rw [add_one_mul] at h2 ⊢; omega⟩
              rw [this]
              exact Dvd.intro_left b rfl
            rw [tv_top_eq_false x y hg hρ hxy (by omega) hdvd,
              tv_top_eq_false x y hg hρ hxy (by omega) hdvd,
              tv_top_eq_false x y hg hρ hxy (by omega) hdvd,
              tv_top_eq_false x' y' hg hρ hxy' (by omega) hdvd,
              tv_top_eq_false x' y' hg hρ hxy' (by omega) hdvd,
              tv_top_eq_false x' y' hg hρ hxy' (by omega) hdvd]
    · rw [tv_of_not x y (by omega), tv_of_not x' y' (by omega)]

/-! ### The carry-lookahead adder under a sparse restriction -/

/-- The signals of the final adder vanish at every top column. -/
theorem pSig_top {g : ℕ} (hg : 1 ≤ g) {ρ : InputRestriction n} (hρ : ρ.IsSparse g)
    (hxy : ρ.Extends x y) {c : ℕ} (hc : g ∣ c + 1) :
    pSig x y c = false ∧ qSig x y c = false := by
  have h0 := tv_top_eq_false x y hg hρ hxy le_rfl hc 0
  have h1 := tv_top_eq_false x y hg hρ hxy le_rfl hc 1
  simp [pSig, qSig, CLA.prop, CLA.gen, aVal, bVal, h0, h1]

/-- The signals of the final adder in the columns of a strip are functions of the partial
products of that strip. -/
theorem pSig_congr {g : ℕ} (hg : 1 ≤ g) {ρ : InputRestriction n} (hρ : ρ.IsSparse g)
    {x' y' : Bits n} (hxy : ρ.Extends x y) (hxy' : ρ.Extends x' y') {b : ℕ}
    (hagree : ∀ i j : Fin n, InStrip g b ((i : ℕ) + j) →
      partialProduct x y i j = partialProduct x' y' i j) {t : ℕ} (ht : InStrip g b t) :
    pSig x y t = pSig x' y' t ∧ qSig x y t = qSig x' y' t := by
  have h0 := tv_congr x y hg hρ hxy hxy' hagree _ le_rfl t ht 0
  have h1 := tv_congr x y hg hρ hxy hxy' hagree _ le_rfl t ht 1
  simp [pSig, qSig, CLA.prop, CLA.gen, aVal, bVal, h0, h1]

/-! ### Strip-locality of every wire -/

/-- The strip to which a wire is local: its column for layer variables, bit signals and sum
bits; the strip of the last position of its interval for group pairs; the strip of the
position below it for carries (the carry `c_i` is `0` when `i - 1` is a top column). -/
def stripOf (g : ℕ) : WWire n → ℕ
  | .zero => 0
  | .t _ i _ => i / g
  | .p i => i / g
  | .q i => i / g
  | .P ℓ m => (m * 4 ^ ((ℓ : ℕ) + 1) + 4 ^ ((ℓ : ℕ) + 1) - 1) / g
  | .Q ℓ m => (m * 4 ^ ((ℓ : ℕ) + 1) + 4 ^ ((ℓ : ℕ) + 1) - 1) / g
  | .c i => (i - 1) / g
  | .s i => i / g

/-- **Every wire is strip-local** (Lemmas [lem:wallace-tree-local] and [lem:cla-local]): two
extensions of a `g`-sparse restriction agreeing on the partial products of the strip
`stripOf g w` give the wire `w` the same value. -/
theorem eval_local {g : ℕ} (hg : 1 ≤ g) {ρ : InputRestriction n} (hρ : ρ.IsSparse g)
    {x' y' : Bits n} (hxy : ρ.Extends x y) (hxy' : ρ.Extends x' y') (w : WWire n)
    (hagree : ∀ i j : Fin n, InStrip g (stripOf g w) ((i : ℕ) + j) →
      partialProduct x y i j = partialProduct x' y' i j) :
    (circuit n).eval x y w = (circuit n).eval x' y' w := by
  have hin : ∀ c, InStrip g (c / g) c := fun c => (inStrip_iff (by omega)).mpr rfl
  have hz : ∀ s, g ∣ s + 1 → pSig x y s = false ∧ qSig x y s = false :=
    fun s hs => pSig_top x y hg hρ hxy hs
  have hz' : ∀ s, g ∣ s + 1 → pSig x' y' s = false ∧ qSig x' y' s = false :=
    fun s hs => pSig_top x' y' hg hρ hxy' hs
  cases w with
  | zero => rw [eval_zero, eval_zero]
  | t ℓ i j =>
    rw [← tv_eq_eval x y ⟨ℓ.isLt, i.isLt, j.isLt⟩, ← tv_eq_eval x' y' ⟨ℓ.isLt, i.isLt, j.isLt⟩]
    exact tv_congr x y hg hρ hxy hxy' hagree ℓ (by omega) i (hin i) j
  | p i =>
    rw [eval_p, eval_p]
    exact (pSig_congr x y hg hρ hxy hxy' hagree (hin i)).1
  | q i =>
    rw [eval_q, eval_q]
    exact (pSig_congr x y hg hρ hxy hxy' hagree (hin i)).2
  | P ℓ m =>
    by_cases hm : (m : ℕ) < 4 ^ (claLevels n - (ℓ + 1))
    · rw [eval_P x y ℓ m hm, eval_P x' y' ℓ m hm]
      exact (foldCarry_local hz hz' (Nat.one_le_pow _ _ (by norm_num)) (hin _)
        fun t ht => pSig_congr x y hg hρ hxy hxy' hagree ht).1
    · rw [eval_P_of_not x y ℓ m hm, eval_P_of_not x' y' ℓ m hm]
  | Q ℓ m =>
    by_cases hm : (m : ℕ) < 4 ^ (claLevels n - (ℓ + 1))
    · rw [eval_Q x y ℓ m hm, eval_Q x' y' ℓ m hm]
      exact (foldCarry_local hz hz' (Nat.one_le_pow _ _ (by norm_num)) (hin _)
        fun t ht => pSig_congr x y hg hρ hxy hxy' hagree ht).2
    · rw [eval_Q_of_not x y ℓ m hm, eval_Q_of_not x' y' ℓ m hm]
  | c i =>
    rw [eval_c, eval_c, CLA.carry_eq, CLA.carry_eq]
    rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | hpos
    · rw [h0]
      rfl
    · have hb : InStrip g (stripOf g (c i)) (0 + i - 1) := by
        rw [Nat.zero_add]
        exact hin _
      exact (foldCarry_local hz hz' hpos hb
        fun t ht => pSig_congr x y hg hρ hxy hxy' hagree ht).2
  | s i =>
    rw [eval_s, eval_s, CLA.sumBit_eq, CLA.sumBit_eq]
    have hp := (pSig_congr x y hg hρ hxy hxy' hagree (hin i)).1
    have hc : CLA.carry (aVal x y) (bVal x y) i = CLA.carry (aVal x' y') (bVal x' y') i := by
      rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | hpos
      · rw [h0]
        rfl
      · by_cases hdvd : g ∣ (i : ℕ)
        · obtain ⟨i', hi'⟩ : ∃ i', (i : ℕ) = i' + 1 := ⟨i - 1, by omega⟩
          rw [hi', CLA.carry_succ_eq, CLA.carry_succ_eq]
          have h1 := pSig_top x y hg hρ hxy (c := i') (by rw [← hi']; exact hdvd)
          have h2 := pSig_top x' y' hg hρ hxy' (c := i') (by rw [← hi']; exact hdvd)
          change (qSig x y i' ^^ (pSig x y i' && _)) = (qSig x' y' i' ^^ (pSig x' y' i' && _))
          rw [h1.1, h1.2, h2.1, h2.2]
          rfl
        · rw [CLA.carry_eq, CLA.carry_eq]
          have hb : InStrip g (stripOf g (s i)) (0 + i - 1) := by
            change (i : ℕ) / g * g ≤ 0 + i - 1 ∧ 0 + i - 1 < ((i : ℕ) / g + 1) * g
            have h := Nat.div_add_mod (i : ℕ) g
            have hmodlt := Nat.mod_lt (i : ℕ) (by omega : g > 0)
            rw [mul_comm] at h
            rw [add_one_mul]
            omega
          exact (foldCarry_local hz hz' hpos hb
            fun t ht => pSig_congr x y hg hρ hxy hxy' hagree ht).2
    change (pSig x y i ^^ CLA.carry (aVal x y) (bVal x y) i) =
      (pSig x' y' i ^^ CLA.carry (aVal x' y') (bVal x' y') i)
    rw [hp, hc]

omit x y in
/-- The wires of the `n`-bit Wallace-tree multiplier are strip-local. -/
theorem wiresStripLocal (n : ℕ) : (wallaceMul n).WiresStripLocal := by
  intro g hg ρ hρ w
  refine ⟨stripOf g w, ?_⟩
  intro x y x' y' hxy hxy' hagree
  exact eval_local x y hg hρ hxy hxy' w hagree

omit x y in
/-- Every gate of the Wallace-tree multiplier has fan-in at most `9`. -/
theorem arity_le (w : WWire n) : (gate w).arity ≤ 9 := by
  cases w with
  | zero => exact Nat.zero_le _
  | t ℓ i j =>
    rcases ℓ with ⟨ℓ, hℓ⟩
    cases ℓ with
    | zero =>
      change (ppGate (n := n) i j).arity ≤ 9
      unfold ppGate
      generalize ppPair n i j = o
      rcases o with _ | ⟨a, b⟩ <;> simp [Gate.and2, Gate.const]
    | succ ℓ =>
      change (layerGate (ℓ + 1) i j).arity ≤ 9
      rw [layerGate]
      split_ifs <;> simp [sumGate, carryGate, Gate.xor3, Gate.maj3, Gate.const]
  | p i =>
    change (Gate.xor2 (aVar (n := n) i) (bVar i)).arity ≤ 9
    simp [Gate.xor2]
  | q i =>
    change (Gate.and2 (aVar (n := n) i) (bVar i)).arity ≤ 9
    simp [Gate.and2]
  | P ℓ m =>
    change (if (m : ℕ) < 4 ^ (claLevels n - (ℓ + 1)) then
      Gate.allN 4 (fun t => PVar (n := n) ℓ (4 * m + t)) else Gate.const false).arity ≤ 9
    split_ifs <;> simp [Gate.allN, Gate.const]
  | Q ℓ m =>
    change (if (m : ℕ) < 4 ^ (claLevels n - (ℓ + 1)) then
      Gate.carryFold 4 (fun t => PVar (n := n) ℓ (4 * m + t)) (fun t => QVar ℓ (4 * m + t))
        (.wire .zero) else Gate.const false).arity ≤ 9
    split_ifs <;> simp [Gate.carryFold, Gate.const]
  | c i =>
    change (cGate (n := n) i).arity ≤ 9
    unfold cGate
    split_ifs
    · simp [Gate.const]
    · simp only [Gate.carryFold]
      have := claR_lt (i : ℕ)
      omega
  | s i =>
    change (Gate.xor2 (pVar (n := n) i) (cVar i)).arity ≤ 9
    simp [Gate.xor2]

end WWire

/-- **The Wallace-tree multiplier is strip-local.**

Paper: Proposition [prop:wallace-strip-local]. -/
theorem wallaceMul_stripLocal : StripLocal wallaceMul :=
  ⟨⟨10, fun n => MulEncoding.width_ofMulCircuit_le (WWire.circuit n) (WWire.out n)
    (WWire.out_injective n) WWire.toNat_out 9 WWire.arity_le⟩, fun n => WWire.wiresStripLocal n⟩

end AssocLB
