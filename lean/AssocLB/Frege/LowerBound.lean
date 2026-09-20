/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/
import AssocLB.Frege.Transfer
import AssocLB.Frege.Hastad

/-!
# Bounded-depth Frege lower bound for `Assoc_n`

Paper: Section 9.3 (Reduction and lower bound), Theorem [thm:frege] (bounded-depth Frege lower
bound): for a strip-local multiplier encoding there is a constant `γ > 0` such that for all
sufficiently large `n` and all `d ≤ γ log n / log log n`, every depth-`d` Frege refutation of
`Assoc_n` has size at least `exp(n^{γ/d})`.

## Main results

* `frege_main`: Theorem [thm:frege], for any Frege system `𝓕` satisfying Håstad's lower bound
  `HastadGridPM 𝓕` and any strip-local family of encodings.
* `frege_main_arrayMul`, `frege_main_wallaceMul`: its instances for the array multiplier and
  the Wallace-tree multiplier.

## Design notes

* The theorem takes Håstad's lower bound as the explicit hypothesis `HastadGridPM 𝓕`, which is
  not proved in this library (see `AssocLB.Frege.Hastad`); it is otherwise unconditional, with
  Lemma [lem:indices] (`exists_indexMaps`), the grid (`AssocLB.Frege.Grid`) and Lemma
  [lem:frege-transfer] (`FregeSystem.frege_transfer`) as ingredients, following the paper's
  proof, with an explicit choice of the grid side: `r = ⌊n^{1/40}⌋₊`, taken as the largest
  natural with `r^40 ≤ n` so that the estimates stay in `ℕ`, and `t = 2 ⌊r/2⌋ + 1`, so
  that `t` is odd with `r ≤ t ≤ r + 1`, `n^{1/80} ≤ t` and `n₀(t) = indexN₀ ((t² − 1)/2) g ≤ n`
  for `n ≥ 3^40` (polynomial inequalities in `r`), and `γ = c / (160 (1 + d₀))`. The paper
  takes the largest odd `t` with `n₀(t) ≤ n`, hence `t ≥ n^{1/9}` and `γ = c / (18 (1 + d₀))`;
  the theorem asserts only the existence of `γ`, and the smaller `t` simplifies the estimates.
  The threshold `n₁ = max (3^40) ⌈exp s₀⌉₊` also makes `log n ≥ log s₀ + 1`, which absorbs the
  size factor `s₀` of the reduction.
* "Depth `d` refutation" is `π.depth ≤ d`; depths range over `d ≥ 1` as in `HastadGridPM`.
* Remarks [rem:frege-vs-res] (comparison with Theorem [thm:main]) and [rem:frege-lines] (the
  number of lines) are not formalized.
-/

namespace AssocLB

/-- **Bounded-depth Frege lower bound**, for a Frege system `𝓕` satisfying Håstad's lower bound
and a strip-local family `M` of multiplier encodings: there is `γ > 0` such that for all
sufficiently large `n` and all depths `1 ≤ d ≤ γ log n / log log n`, every refutation of
`Assoc_n` in `𝓕` of depth at most `d` has size at least `exp(n^{γ/d})`, stated as
`n^{γ/d} ≤ log |π|`.

Paper: Theorem [thm:frege]. -/
theorem frege_main (𝓕 : FregeSystem) (hH : HastadGridPM 𝓕) (M : ∀ n, MulEncoding n)
    (hM : StripLocal M) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ n₁ : ℕ, ∀ n ≥ n₁, ∀ d : ℕ, 1 ≤ d →
      (d : ℝ) ≤ γ * Real.log n / Real.log (Real.log n) →
      ∀ π : 𝓕.Refutation (Assoc (M n) (M (2 * n))).toFormulas, π.depth ≤ d →
        (n : ℝ) ^ (γ / (d : ℝ)) ≤ Real.log π.size := by
  obtain ⟨c, hc, hH⟩ := hH
  obtain ⟨⟨k, hk⟩, hloc⟩ := hM
  obtain ⟨d₀, s₀, htrans⟩ := 𝓕.frege_transfer 4 (max k 3)
  -- Lemma [lem:frege-transfer] for the odd grid, in explicit form
  have hgrid : ∀ t : ℕ, Odd t → 3 ≤ t → ∀ m : ℕ, m = (t ^ 2 - 1) / 2 → ∀ n : ℕ,
      indexN₀ m (stripWidth m) ≤ n →
      ∀ π : 𝓕.Refutation (Assoc (M n) (M (2 * n))).toFormulas,
        ∃ π' : 𝓕.Refutation (EdgePM (grid t)).toFormulas,
          π'.depth ≤ π.depth + d₀ ∧ π'.size ≤ s₀ * π.size := by
    intro t ht ht3 m hm n hn π
    subst hm
    have ht2 : 9 ≤ t ^ 2 := by
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ t ^ 2 := Nat.pow_le_pow_left ht3 2
    have hm1 : 1 ≤ (t ^ 2 - 1) / 2 := by omega
    have hU : Fintype.card (Grid.White t) = (t ^ 2 - 1) / 2 + 1 := by
      rw [Grid.card_white ht]
      omega
    have hV : Fintype.card (Grid.Black t) = (t ^ 2 - 1) / 2 := Grid.card_black ht
    obtain ⟨I⟩ := exists_indexMaps (grid t) Grid.grid_isSimple hm1 hU hV (stripWidth_pos _)
    have : Nonempty (Grid.White t) := Fintype.card_pos_iff.mp (by rw [hU]; omega)
    have : Nonempty (Grid.Black t) := Fintype.card_pos_iff.mp (by rw [hV]; omega)
    have hg2 : (t ^ 2 - 1) / 2 + 2 ≤ 2 ^ (stripWidth ((t ^ 2 - 1) / 2) - 1) :=
      le_trans (by omega) (two_mul_le_two_pow_stripWidth _)
    have hw : ∀ C ∈ Assoc (M n) (M (2 * n)),
        C ≠ Assoc.miterClause n (M n).Wire (M (2 * n)).Wire → C.card ≤ max k 3 :=
      fun C hC hne => (Assoc.card_le_of_ne_miterClause _ _ hC hne).trans
        (max_le_max (max_le (hk n) (hk (2 * n))) le_rfl)
    exact htrans _ _ _ (grid t) _ _ _ n I (M n) (M (2 * n)) (hloc n) (hloc (2 * n)) hn
      (stripWidth_pos _) (Assoc.isSparse_inputXY I _ _ Grid.grid_isSimple hU.le hg2)
      (Assoc.isSparse_inputYZ I _ _ Grid.grid_isSimple (by omega) hg2)
      (Assoc.isSparse_inputXY_Z I _ _ (by omega) hg2) (Assoc.isSparse_inputX_YZ I _ _ hU.le hg2)
      (Grid.card_white_eq_card_black_add_one ht) (Grid.exists_edge_left (by omega))
      (Grid.exists_edge_right (by omega)) Grid.grid_maxDegreeLE hw π
  -- the constant `γ` and the threshold
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = c / (160 * (1 + d₀)) := ⟨_, rfl⟩
  have hγ0 : 0 < γ := by
    rw [hγ]
    positivity
  refine ⟨γ, hγ0, max (3 ^ 40) ⌈Real.exp s₀⌉₊, fun n hn d hd1 hd π hπd => ?_⟩
  have hn40 : 3 ^ 40 ≤ n := le_of_max_le_left hn
  have hnexp : ⌈Real.exp s₀⌉₊ ≤ n := le_of_max_le_right hn
  clear hn
  have hn3 : 3 ≤ n := (by norm_num : 3 ≤ 3 ^ 40).trans hn40
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hlog3 : (1 : ℝ) < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith
  have hlog1 : 1 < Real.log n :=
    hlog3.trans_le (Real.log_le_log (by norm_num) (by exact_mod_cast hn3))
  have hlogn0 : 0 < Real.log n := by linarith
  have hlln : 0 < Real.log (Real.log n) := Real.log_pos hlog1
  -- `r = ⌊n^{1/40}⌋₊`, as the largest natural with `r^40 ≤ n`: `r^40 ≤ n < (r + 1)^40 ≤ r^80`
  obtain ⟨r, hr_def⟩ : ∃ r : ℕ, r = Nat.findGreatest (fun k => k ^ 40 ≤ n) n := ⟨_, rfl⟩
  have hr3 : 3 ≤ r := hr_def ▸ Nat.le_findGreatest hn3 hn40
  have hr40 : r ^ 40 ≤ n := by
    rw [hr_def]
    exact Nat.findGreatest_spec (P := fun k => k ^ 40 ≤ n) (m := 3) hn3 hn40
  have hrn : r < n :=
    calc r = r ^ 1 := (pow_one r).symm
      _ < r ^ 40 := Nat.pow_lt_pow_right (by omega) (by norm_num)
      _ ≤ n := hr40
  have hnr : n < (r + 1) ^ 40 :=
    not_le.mp (Nat.findGreatest_is_greatest (P := fun k => k ^ 40 ≤ n)
      (by rw [← hr_def]; omega) (by omega))
  have hr2 : 2 ≤ r := by omega
  have hrr : r + 1 ≤ r ^ 2 := by
    rw [sq]
    have := Nat.mul_le_mul_right r hr2
    omega
  have hn80 : n ≤ r ^ 80 := by
    calc n ≤ (r + 1) ^ 40 := hnr.le
      _ ≤ (r ^ 2) ^ 40 := Nat.pow_le_pow_left hrr 40
      _ = r ^ 80 := by rw [← pow_mul]
  -- the odd grid side `t = 2 ⌊r/2⌋ + 1`, with `r ≤ t ≤ r + 1`
  obtain ⟨t, ht_def⟩ : ∃ t : ℕ, t = 2 * (r / 2) + 1 := ⟨_, rfl⟩
  have ht_odd : Odd t := by
    rw [ht_def]
    exact odd_two_mul_add_one _
  have hrt : r ≤ t := by omega
  have htr : t ≤ r + 1 := by omega
  have ht3 : 3 ≤ t := by omega
  have htn : t ≤ n :=
    calc t ≤ r + 1 := htr
      _ ≤ r ^ 2 := hrr
      _ ≤ r ^ 40 := Nat.pow_le_pow_right (by omega) (by norm_num)
      _ ≤ n := hr40
  -- `n₀(t) ≤ n`
  obtain ⟨m, hm_def⟩ : ∃ m : ℕ, m = (t ^ 2 - 1) / 2 := ⟨_, rfl⟩
  have ht2 : 9 ≤ t ^ 2 := by
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ t ^ 2 := Nat.pow_le_pow_left ht3 2
  have hm_le : m ≤ 4 * r ^ 2 := by
    have h1 : t ^ 2 ≤ (2 * r) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h2 : (2 * r) ^ 2 = 4 * r ^ 2 := by ring
    omega
  have hclog : Nat.clog 2 (m + 2) ≤ m + 2 := by
    have h1 := Nat.pow_pred_clog_lt_self one_lt_two (show 1 < m + 2 by omega)
    have h2 := Nat.lt_two_pow_self (n := (Nat.clog 2 (m + 2)).pred)
    simp only [Nat.pred_eq_sub_one] at h1 h2
    omega
  have hg : stripWidth m ≤ 8 * r ^ 2 := by
    unfold stripWidth
    omega
  have hn0' : indexN₀ m (stripWidth m) ≤ n := by
    have hm1 : 1 ≤ m := by omega
    calc indexN₀ m (stripWidth m) ≤ 16896 * stripWidth m * m ^ 4 := indexN₀_le m _ hm1
      _ ≤ 16896 * (8 * r ^ 2) * (4 * r ^ 2) ^ 4 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hg) (Nat.pow_le_pow_left hm_le 4)
      _ = 34603008 * r ^ 10 := by ring
      _ ≤ r ^ 30 * r ^ 10 :=
          Nat.mul_le_mul_right _ (le_trans (by norm_num) (Nat.pow_le_pow_left hr2 30))
      _ = r ^ 40 := by rw [← pow_add]
      _ ≤ n := hr40
  -- the reduction to `PM(Grid_t)`
  obtain ⟨π', hπ'd, hπ's⟩ := hgrid t ht_odd ht3 m hm_def n hn0' π
  have hπ'depth : π'.depth ≤ d + d₀ := by omega
  -- real-number facts about `t`: `t ≥ n^{1/80}`, `log t ≥ log n / 80`, `log log t ≤ log log n`
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hlogt1 : 1 < Real.log t :=
    hlog3.trans_le (Real.log_le_log (by norm_num) (by exact_mod_cast ht3))
  have hlogt0 : 0 < Real.log t := by linarith
  have hllt : 0 < Real.log (Real.log t) := Real.log_pos hlogt1
  have hloglogt : Real.log (Real.log t) ≤ Real.log (Real.log n) :=
    Real.log_le_log hlogt0 (Real.log_le_log ht0 (by exact_mod_cast htn))
  have hnr80 : (n : ℝ) ^ (80 : ℝ)⁻¹ ≤ r := by
    have h1 : (n : ℝ) ≤ (r : ℝ) ^ (80 : ℕ) := by exact_mod_cast hn80
    have h2 := Real.rpow_le_rpow hn0.le h1 (by positivity : (0 : ℝ) ≤ (80 : ℝ)⁻¹)
    have h3 := Real.pow_rpow_inv_natCast (by positivity : (0 : ℝ) ≤ r) (by norm_num : (80 : ℕ) ≠ 0)
    rw [show ((80 : ℕ) : ℝ)⁻¹ = (80 : ℝ)⁻¹ by norm_num] at h3
    rwa [h3] at h2
  have hnt : (n : ℝ) ^ (80 : ℝ)⁻¹ ≤ t := hnr80.trans (by exact_mod_cast hrt)
  have hlogt : (80 : ℝ)⁻¹ * Real.log n ≤ Real.log t := by
    rw [← Real.log_rpow hn0]
    exact Real.log_le_log (by positivity) hnt
  -- the depth `d + d₀` is admissible for Håstad's theorem
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
  have hd1r : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hd' : (d : ℝ) * Real.log (Real.log n) ≤ γ * Real.log n := by
    rwa [le_div_iff₀ hlln] at hd
  have hd₀0 : (0 : ℝ) ≤ d₀ := Nat.cast_nonneg d₀
  have h1d₀ : (0 : ℝ) < 1 + d₀ := add_pos_of_pos_of_nonneg one_pos hd₀0
  have hdd₀ : (0 : ℝ) < d + d₀ := add_pos_of_pos_of_nonneg hd0 hd₀0
  have hdt : ((d + d₀ : ℕ) : ℝ) ≤ c * Real.log t / Real.log (Real.log t) := by
    rw [le_div_iff₀ hllt]
    push_cast
    have hdd : (d : ℝ) + d₀ ≤ (1 + d₀) * d := by
      have := mul_le_mul_of_nonneg_left hd1r (Nat.cast_nonneg d₀)
      linarith
    calc ((d : ℝ) + d₀) * Real.log (Real.log t)
        ≤ ((1 + d₀) * d) * Real.log (Real.log n) :=
          mul_le_mul hdd hloglogt hllt.le (mul_nonneg h1d₀.le hd0.le)
      _ = (1 + d₀) * (d * Real.log (Real.log n)) := by ring
      _ ≤ (1 + d₀) * (γ * Real.log n) := mul_le_mul_of_nonneg_left hd' h1d₀.le
      _ = c / 160 * Real.log n := by
          rw [hγ]
          field_simp
      _ ≤ c * ((80 : ℝ)⁻¹ * Real.log n) := by
          have := mul_pos hc hlogn0
          linarith
      _ ≤ c * Real.log t := mul_le_mul_of_nonneg_left hlogt hc.le
  -- Håstad's lower bound for `π'`
  have hHt := hH t ht_odd ht3 (d + d₀) (by omega) hdt π' hπ'depth
  push_cast at hHt
  -- the size of `π'` in terms of the size of `π`
  have hs₀ : 0 < s₀ := by
    rcases Nat.eq_zero_or_pos s₀ with h | h
    · rw [h, zero_mul] at hπ's
      have := π'.size_pos
      omega
    · exact h
  have hs₀r : (0 : ℝ) < s₀ := by exact_mod_cast hs₀
  have hπs0 : (0 : ℝ) < π.size := by exact_mod_cast π.size_pos
  have hπ's0 : (0 : ℝ) < π'.size := by exact_mod_cast π'.size_pos
  have hlogπ' : Real.log π'.size ≤ Real.log s₀ + Real.log π.size := by
    rw [← Real.log_mul hs₀r.ne' hπs0.ne']
    exact Real.log_le_log hπ's0 (by exact_mod_cast hπ's)
  -- `t^{c/(d + d₀)} ≥ n^{2γ/d} = n^{γ/d} · n^{γ/d}`, and `n^{γ/d} ≥ log n ≥ log s₀ + 1`
  have hA0 : 0 ≤ (n : ℝ) ^ (γ / d) := Real.rpow_nonneg hn0.le _
  have hexp : 2 * γ / d ≤ (80 : ℝ)⁻¹ * (c / (d + d₀)) := by
    rw [hγ]
    have e1 : 2 * (c / (160 * (1 + (d₀ : ℝ)))) / d = c / (80 * ((1 + d₀) * d)) := by
      field_simp
      ring
    have e2 : (80 : ℝ)⁻¹ * (c / (d + d₀)) = c / (80 * (d + d₀)) := by
      field_simp
    rw [e1, e2]
    apply div_le_div_of_nonneg_left hc.le (mul_pos (by norm_num) hdd₀)
    have := mul_le_mul_of_nonneg_left hd1r (Nat.cast_nonneg d₀)
    linarith
  have ht_ge : (n : ℝ) ^ (2 * γ / d) ≤ (t : ℝ) ^ (c / ((d : ℝ) + d₀)) := by
    calc (n : ℝ) ^ (2 * γ / d) ≤ (n : ℝ) ^ ((80 : ℝ)⁻¹ * (c / (d + d₀))) :=
          Real.rpow_le_rpow_of_exponent_le hn1 hexp
      _ = ((n : ℝ) ^ (80 : ℝ)⁻¹) ^ (c / ((d : ℝ) + d₀)) := Real.rpow_mul hn0.le _ _
      _ ≤ (t : ℝ) ^ (c / ((d : ℝ) + d₀)) :=
          Real.rpow_le_rpow (Real.rpow_nonneg hn0.le _) hnt (div_pos hc hdd₀).le
  have h2γ : (n : ℝ) ^ (2 * γ / d) = (n : ℝ) ^ (γ / d) * (n : ℝ) ^ (γ / d) := by
    rw [← Real.rpow_add hn0]
    congr 1
    ring
  have hlogn_le : Real.log n ≤ (n : ℝ) ^ (γ / d) := by
    have h1 : Real.log (Real.log n) ≤ Real.log n * (γ / d) := by
      have : Real.log (Real.log n) ≤ γ * Real.log n / d := by
        rw [le_div_iff₀ hd0]
        linarith [hd']
      calc Real.log (Real.log n) ≤ γ * Real.log n / d := this
        _ = Real.log n * (γ / d) := by ring
    calc Real.log n = Real.exp (Real.log (Real.log n)) := (Real.exp_log hlogn0).symm
      _ ≤ Real.exp (Real.log n * (γ / d)) := Real.exp_le_exp.mpr h1
      _ = (n : ℝ) ^ (γ / d) := (Real.rpow_def_of_pos hn0 _).symm
  have hs₀log : Real.log s₀ + 1 ≤ Real.log n := by
    have h1 : Real.log s₀ + 1 ≤ (s₀ : ℝ) := by
      have := Real.add_one_le_exp (Real.log s₀)
      rwa [Real.exp_log hs₀r] at this
    have h2 : (s₀ : ℝ) ≤ Real.log n := by
      rw [Real.le_log_iff_exp_le hn0]
      exact (Nat.le_ceil _).trans (by exact_mod_cast hnexp)
    linarith
  have hlogs₀ : 0 ≤ Real.log s₀ := Real.log_nonneg (by exact_mod_cast hs₀)
  -- assemble
  have hAL : (n : ℝ) ^ (γ / d) * Real.log n ≤ (n : ℝ) ^ (γ / d) * (n : ℝ) ^ (γ / d) :=
    mul_le_mul_of_nonneg_left hlogn_le hA0
  have hAs : (n : ℝ) ^ (γ / d) * (Real.log s₀ + 1) ≤ (n : ℝ) ^ (γ / d) * Real.log n :=
    mul_le_mul_of_nonneg_left hs₀log hA0
  have hprod : 0 ≤ ((n : ℝ) ^ (γ / d) - 1) * Real.log s₀ := mul_nonneg (by linarith) hlogs₀
  linarith [hHt, hlogπ', ht_ge, h2γ, hAL, hAs, hprod]

/-- Theorem [thm:frege] for the array multiplier (Proposition [prop:array-strip-local]). -/
theorem frege_main_arrayMul (𝓕 : FregeSystem) (hH : HastadGridPM 𝓕) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ n₁ : ℕ, ∀ n ≥ n₁, ∀ d : ℕ, 1 ≤ d →
      (d : ℝ) ≤ γ * Real.log n / Real.log (Real.log n) →
      ∀ π : 𝓕.Refutation (Assoc (arrayMul n) (arrayMul (2 * n))).toFormulas, π.depth ≤ d →
        (n : ℝ) ^ (γ / (d : ℝ)) ≤ Real.log π.size :=
  frege_main 𝓕 hH arrayMul arrayMul_stripLocal

/-- Theorem [thm:frege] for the Wallace-tree multiplier (Proposition
[prop:wallace-strip-local]). -/
theorem frege_main_wallaceMul (𝓕 : FregeSystem) (hH : HastadGridPM 𝓕) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ n₁ : ℕ, ∀ n ≥ n₁, ∀ d : ℕ, 1 ≤ d →
      (d : ℝ) ≤ γ * Real.log n / Real.log (Real.log n) →
      ∀ π : 𝓕.Refutation (Assoc (wallaceMul n) (wallaceMul (2 * n))).toFormulas, π.depth ≤ d →
        (n : ℝ) ^ (γ / (d : ℝ)) ≤ Real.log π.size :=
  frege_main 𝓕 hH wallaceMul wallaceMul_stripLocal

end AssocLB
