/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/
import AssocLB.Resolution.SizeWidth
import AssocLB.Matching.StarLocalPM

/-!
# The perfect-matching principle is wide on expanders

Paper: Section 5, proof of Theorem [thm:star-local-hard], which cites Theorem 1.1 of the full
version of Itsykson, Slabodkin and Sokolov (ECCC TR14-093): for a bipartite graph that is an
`(r, Γ)`-boundary expander and has a matching covering `V`, every resolution refutation of the
perfect-matching CNF `PM(G)` has width at least `Γ r / 2`. The paper cites this theorem; here
it is proved, following their argument, for the expander graphs of Theorem [thm:iss-graphs].

## Main definitions

* `PM.Proper G β`: an edge assignment is proper if every vertex is incident to at most one
  selected edge; `PM.SelectsAt G β w`: some edge at `w` is selected, the exact-one constraint at
  `w` for a proper assignment.
* `PM.IsWitness G S C`: `S ⊆ U ∪ V` properly implies `C`, every proper edge assignment
  satisfying the exact-one constraints at the vertices of `S` satisfies `C`; `PM.leftPart S`:
  the set `S ∩ U`; `PM.HasWitnessLE G C k`: the measure `μ(C) ≤ k`.

## Main results

* `PM.hasWitnessLE_one_of_mem`: every initial clause has `μ ≤ 1`.
* `PM.HasWitnessLE.resolvent`: semiadditivity `μ(C) ≤ μ(C₁) + μ(C₂)` for a resolvent.
* `PM.lt_card_leftPart_of_isWitness_empty`: `μ(⊥) > r`, from boundary expansion, Hall's
  theorem and the matching covering `V`.
* `PM.card_boundary_le_of_minimal`: the boundary argument, `|δ(S ∩ U)| ≤ |C| k` for a minimal
  witness `S` of `C` whose variables each depend on at most `k` vertices of `V`.
* `PM.width_lower_bound`: Theorem 1.1 of Itsykson et al. for an expander graph `H` with
  `Γ ≥ 1` and `εm ≥ 2`: every refutation of `PM(H)` has width `w` with `Γ (εm) / 2 < w`.

## Design notes

* `PM(G)` is a CNF over the variables of `SPM(G)` mentioning only the edge variables. Its
  clauses are evaluated on an edge assignment `β` through `SPM.extend G β`; the values this
  gives the extension variables are immaterial here, and reappear in the width transfer of
  `AssocLB.Matching.StarLocalHard`.
* The measure `μ(C)` is a minimum over witnesses; here it is replaced by the predicate
  `HasWitnessLE G C k`, and the minimal witness of the first clause with `μ(C) > r/2` is
  obtained from `Finset.exists_min_image`.
* The matching covering `S ∩ U` and `V` simultaneously is `Bipartite.exists_matching_covers`,
  proved by Hall's theorem with one dummy vertex; it is Lemma 3.1 of Itsykson et al.
* The bound is stated for `Γ ≥ 1`, which is all the argument uses; Theorem [thm:iss-graphs]
  provides `Γ > 2`. Its constant `Γ r / 2` is that of Itsykson et al., as each edge variable
  depends on a single vertex of `V`.
-/

namespace AssocLB

variable {U V E : Type*} (G : Bipartite U V E) [Fintype U] [Fintype V] [Fintype E]
  [DecidableEq U] [DecidableEq V] [DecidableEq E]

namespace PM

open SPM

/-! ### Proper assignments and witnesses -/

omit [Fintype U] [Fintype V] [DecidableEq E] in
/-- An edge assignment is proper if every vertex is incident to at most one selected edge.

Paper: Theorem 1.1 of Itsykson et al., cited in the proof of Theorem [thm:star-local-hard]. -/
def Proper (β : E → Bool) : Prop :=
  ∀ w, ∀ e ∈ G.star w, ∀ f ∈ G.star w, β e = true → β f = true → e = f

omit [Fintype U] [Fintype V] [DecidableEq E] in
/-- The edge assignment `β` selects an edge at `w`; for a proper assignment this is the
exact-one constraint at `w`. -/
def SelectsAt (β : E → Bool) (w : U ⊕ V) : Prop := ∃ e ∈ G.star w, β e = true

omit [Fintype U] [Fintype V] [DecidableEq E] in
/-- `S` properly implies `C`, in the terminology of Itsykson et al.: every proper edge
assignment satisfying the exact-one constraints at the vertices of `S` satisfies `C`. -/
def IsWitness (S : Finset (U ⊕ V)) (C : Clause (SPMVar G)) : Prop :=
  ∀ β, Proper G β → (∀ w ∈ S, SelectsAt G β w) → Clause.Sat (extend G β) C

omit [Fintype V] in
/-- The vertices of `U` in a vertex set `S ⊆ U ∪ V`: the set `S ∩ U`. -/
def leftPart (S : Finset (U ⊕ V)) : Finset U := Finset.univ.filter fun u => Sum.inl u ∈ S

omit [Fintype V] in
@[simp] theorem mem_leftPart {S : Finset (U ⊕ V)} {u : U} : u ∈ leftPart S ↔ Sum.inl u ∈ S := by
  simp [leftPart]

omit [Fintype V] in
theorem leftPart_union (S₁ S₂ : Finset (U ⊕ V)) :
    leftPart (S₁ ∪ S₂) = leftPart S₁ ∪ leftPart S₂ := by
  ext u
  simp

omit [Fintype V] in
theorem leftPart_erase_inl (S : Finset (U ⊕ V)) (u : U) :
    leftPart (S.erase (Sum.inl u)) = (leftPart S).erase u := by
  ext u'
  simp

omit [Fintype V] in
theorem card_leftPart_singleton_le (w : U ⊕ V) : (leftPart {w}).card ≤ 1 :=
  Finset.card_le_one.mpr fun _ ha _ hb => Sum.inl_injective
    ((Finset.mem_singleton.mp (mem_leftPart.mp ha)).trans
      (Finset.mem_singleton.mp (mem_leftPart.mp hb)).symm)

omit [Fintype V] [DecidableEq E] in
/-- `μ(C) ≤ k`: `C` has a witness `S` with `|S ∩ U| ≤ k`. -/
def HasWitnessLE (C : Clause (SPMVar G)) (k : ℕ) : Prop :=
  ∃ S, IsWitness G S C ∧ (leftPart S).card ≤ k

variable {G} in
omit [Fintype V] [DecidableEq E] in
theorem HasWitnessLE.mono {C : Clause (SPMVar G)} {k k' : ℕ} (h : HasWitnessLE G C k)
    (hk : k ≤ k') : HasWitnessLE G C k' :=
  let ⟨S, hS, hSk⟩ := h
  ⟨S, hS, hSk.trans hk⟩

/-! ### Initial clauses and resolvents -/

omit [Fintype U] [Fintype V] in
/-- A proper assignment selecting an edge at `w` satisfies `ExactOne(X_{E(w)})`. -/
theorem sat_exactOne_extend {β : E → Bool} (hβ : Proper G β) {w : U ⊕ V}
    (hw : SelectsAt G β w) : CNF.Sat (extend G β) (exactOne G w) := by
  rw [sat_exactOne_iff]
  obtain ⟨e, he, hβe⟩ := hw
  exact ⟨e, he, hβe, fun f hf hβf => hβ w f hf e he hβf hβe⟩

/-- Every initial clause has `μ ≤ 1`: a clause of `ExactOne(X_{E(w)})` has the witness `{w}`. -/
theorem hasWitnessLE_one_of_mem {C : Clause (SPMVar G)} (hC : C ∈ PM G) :
    HasWitnessLE G C 1 := by
  obtain ⟨w, -, hC⟩ := Finset.mem_biUnion.mp hC
  exact ⟨{w}, fun β hβ hw => sat_exactOne_extend G hβ (hw w (Finset.mem_singleton_self w)) C hC,
    card_leftPart_singleton_le w⟩

variable {G} in
omit [Fintype U] [Fintype V] in
/-- Soundness of resolution: the union of witnesses of the premises is a witness of the
resolvent. -/
theorem IsWitness.resolvent {S₁ S₂ : Finset (U ⊕ V)} {C C₁ C₂ : Clause (SPMVar G)}
    (h₁ : IsWitness G S₁ C₁) (h₂ : IsWitness G S₂ C₂) (h : Clause.IsResolvent C C₁ C₂) :
    IsWitness G (S₁ ∪ S₂) C := by
  obtain ⟨x, -, -, rfl⟩ := h
  intro β hβ hS
  exact (h₁ β hβ fun w hw => hS w (Finset.mem_union_left _ hw)).resolvent x
    (h₂ β hβ fun w hw => hS w (Finset.mem_union_right _ hw))

variable {G} in
omit [Fintype V] in
/-- Semiadditivity: `μ(C) ≤ μ(C₁) + μ(C₂)` for a resolvent `C` of `C₁` and `C₂`. -/
theorem HasWitnessLE.resolvent {C C₁ C₂ : Clause (SPMVar G)} {k₁ k₂ : ℕ}
    (h₁ : HasWitnessLE G C₁ k₁) (h₂ : HasWitnessLE G C₂ k₂) (h : Clause.IsResolvent C C₁ C₂) :
    HasWitnessLE G C (k₁ + k₂) := by
  obtain ⟨S₁, hS₁, hk₁⟩ := h₁
  obtain ⟨S₂, hS₂, hk₂⟩ := h₂
  refine ⟨S₁ ∪ S₂, hS₁.resolvent hS₂ h, ?_⟩
  rw [leftPart_union]
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add hk₁ hk₂)

/-! ### No small witness for the empty clause -/

omit [Fintype U] [Fintype V] [DecidableEq E] in
/-- A matching covering `A` gives a proper assignment selecting an edge at every vertex of
`A`. -/
theorem exists_proper_selectsAt_of_matching {M : Finset E} (hM : G.IsMatching M)
    {A : Finset (U ⊕ V)} (hcov : G.Covers M A) :
    ∃ β, Proper G β ∧ ∀ w ∈ A, SelectsAt G β w := by
  classical
  refine ⟨fun e => decide (e ∈ M), ?_, ?_⟩
  · intro w e he f hf hβe hβf
    simp only [decide_eq_true_eq] at hβe hβf
    by_contra hef
    obtain ⟨hl, hr⟩ := hM e hβe f hβf hef
    rcases w with u | v
    · exact hl ((G.mem_star_inl.mp he).trans (G.mem_star_inl.mp hf).symm)
    · exact hr ((G.mem_star_inr.mp he).trans (G.mem_star_inr.mp hf).symm)
  · intro w hw
    obtain ⟨e, he, hwe⟩ := hcov w hw
    refine ⟨e, ?_, by simpa using he⟩
    simp only [Bipartite.ends, Finset.mem_insert, Finset.mem_singleton] at hwe
    rcases hwe with rfl | rfl
    · exact G.mem_star_inl.mpr rfl
    · exact G.mem_star_inr.mpr rfl

omit [DecidableEq E] in
/-- **No small witness for the empty clause.** In a graph with `|U| = |V| + 1`, a matching
covering `V`, and boundary expansion with `Γ ≥ 1` up to size `r`, every witness `S` for `⊥`
has `|S ∩ U| > r`. -/
theorem lt_card_leftPart_of_isWitness_empty (hcard : Fintype.card U = Fintype.card V + 1)
    (hV : ∃ M, G.IsMatching M ∧ G.Covers M (Finset.univ.image Sum.inr)) {r Γ : ℝ}
    (hexp : G.IsBoundaryExpander r Γ) (hΓ : 1 ≤ Γ) {S : Finset (U ⊕ V)}
    (hS : IsWitness G S ∅) : r < (leftPart S).card := by
  by_contra hle
  rw [not_lt] at hle
  obtain ⟨M, hM, hcov⟩ := G.exists_matching_covers hcard hV (S := leftPart S)
    fun S' hS' => hexp.card_le_card_neighbors hΓ
      ((Nat.cast_le.mpr (Finset.card_le_card hS')).trans hle)
  have hcov' : G.Covers M S := fun w hw => hcov w (by
    rcases w with u | v
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (mem_leftPart.mpr hw))
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ v)))
  obtain ⟨β, hβ, hsel⟩ := exists_proper_selectsAt_of_matching G hM hcov'
  exact Clause.not_sat_empty _ (hS β hβ hsel)

/-! ### The boundary argument -/

omit [Fintype U] [Fintype V] [DecidableEq E] in
/-- The vertices of `V` that a variable depends on: `X_e` depends on the endpoint `v_e` of
`e`, and `Z_{w,f}` on the right endpoints of the edges at `w`. -/
def touched : SPMVar G → Finset V
  | Sum.inl e => {G.right e}
  | Sum.inr ⟨w, _⟩ => (G.star w).image G.right

omit [Fintype U] [Fintype V] [DecidableEq E] in
/-- An edge variable depends on a single vertex of `V`. -/
theorem card_touched_X (e : E) : (touched G (X G e)).card = 1 := Finset.card_singleton _

omit [Fintype U] [Fintype V] [DecidableEq E] in
/-- If two edge assignments differ only on edges at `v`, then a variable whose extended
values differ depends on `v`. -/
theorem mem_touched_of_extend_ne {β β' : E → Bool} {v : V}
    (hdiff : ∀ e, β' e ≠ β e → G.right e = v) {x : SPMVar G}
    (hx : extend G β' x ≠ extend G β x) : v ∈ touched G x := by
  rcases x with e | ⟨w, f⟩
  · exact Finset.mem_singleton.mpr (hdiff e hx).symm
  · by_contra hv
    apply hx
    change f (fun e => β' e) = f (fun e => β e)
    congr 1
    funext e
    by_contra hne
    exact hv (Finset.mem_image.mpr ⟨e, e.2, hdiff e hne⟩)

omit [DecidableEq E] in
/-- **The boundary argument.** Let `S` be a minimal witness for `C`: removing any `u ∈ S ∩ U`
destroys the witness. Then every boundary vertex of `S ∩ U` is a vertex on which some variable
of `C` depends, so `|δ(S ∩ U)| ≤ |C| k` when every variable of `C` depends on at most `k`
vertices of `V`. -/
theorem card_boundary_le_of_minimal {S : Finset (U ⊕ V)} {C : Clause (SPMVar G)}
    (hS : IsWitness G S C) (hmin : ∀ u ∈ leftPart S, ¬ IsWitness G (S.erase (Sum.inl u)) C)
    {k : ℕ} (hk : ∀ l ∈ C, (touched G l.var).card ≤ k) :
    (G.boundary (leftPart S)).card ≤ C.card * k := by
  have hsub : G.boundary (leftPart S) ⊆ C.biUnion fun l => touched G l.var := by
    intro v hv
    have hv1 : (G.edgesTo (leftPart S) v).card = 1 := (Finset.mem_filter.mp hv).2
    obtain ⟨e₀, he₀⟩ := Finset.card_eq_one.mp hv1
    have he₀mem : e₀ ∈ G.edgesTo (leftPart S) v := he₀ ▸ Finset.mem_singleton_self e₀
    obtain ⟨hu, hre₀⟩ := (Finset.mem_filter.mp he₀mem).2
    have huniq : ∀ e, G.right e = v → G.left e ∈ leftPart S → e = e₀ := by
      intro e he hl
      have hmem : e ∈ G.edgesTo (leftPart S) v :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl, he⟩
      rw [he₀] at hmem
      exact Finset.mem_singleton.mp hmem
    -- minimality at `u = G.left e₀`
    have hnot : ∃ β, Proper G β ∧ (∀ w ∈ S.erase (Sum.inl (G.left e₀)), SelectsAt G β w) ∧
        ¬ Clause.Sat (extend G β) C := by
      by_contra h
      exact hmin _ hu fun β hβ hsel => by_contra fun hC => h ⟨β, hβ, hsel, hC⟩
    obtain ⟨β, hβ, hsel, hC⟩ := hnot
    have hnu : ¬ SelectsAt G β (Sum.inl (G.left e₀)) := by
      intro hsu
      refine hC (hS β hβ fun w hw => ?_)
      by_cases hwu : w = Sum.inl (G.left e₀)
      · exact hwu ▸ hsu
      · exact hsel w (Finset.mem_erase.mpr ⟨hwu, hw⟩)
    -- rematch `v` to `u`
    classical
    let β' : E → Bool := fun e => if G.right e = v then decide (e = e₀) else β e
    have hdiff : ∀ e, β' e ≠ β e → G.right e = v := by
      intro e he
      by_contra hne
      exact he (if_neg hne)
    have hβ'e₀ : β' e₀ = true := by simp [β', hre₀]
    have hβ'_of_right : ∀ e, G.right e = v → β' e = true → e = e₀ := by
      intro e he hb
      simpa [β', if_pos he] using hb
    have hβ'_of_ne : ∀ e, G.right e ≠ v → β' e = β e := fun e he => if_neg he
    have hβ' : Proper G β' := by
      intro w e he f hf hbe hbf
      by_cases hev : G.right e = v <;> by_cases hfv : G.right f = v
      · rw [hβ'_of_right e hev hbe, hβ'_of_right f hfv hbf]
      · exfalso
        rw [hβ'_of_right e hev hbe] at he
        rw [hβ'_of_ne f hfv] at hbf
        rcases w with u' | v'
        · refine hnu ⟨f, ?_, hbf⟩
          rw [G.mem_star_inl.mp he]
          exact hf
        · exact hfv ((G.mem_star_inr.mp hf).trans ((G.mem_star_inr.mp he).symm.trans hre₀))
      · exfalso
        rw [hβ'_of_right f hfv hbf] at hf
        rw [hβ'_of_ne e hev] at hbe
        rcases w with u' | v'
        · refine hnu ⟨e, ?_, hbe⟩
          rw [G.mem_star_inl.mp hf]
          exact he
        · exact hev ((G.mem_star_inr.mp he).trans ((G.mem_star_inr.mp hf).symm.trans hre₀))
      · rw [hβ'_of_ne e hev] at hbe
        rw [hβ'_of_ne f hfv] at hbf
        exact hβ w e he f hf hbe hbf
    have hsel' : ∀ w ∈ S, SelectsAt G β' w := by
      intro w hw
      by_cases hwu : w = Sum.inl (G.left e₀)
      · rw [hwu]
        exact ⟨e₀, G.mem_star_inl.mpr rfl, hβ'e₀⟩
      · obtain ⟨e, he, hbe⟩ := hsel w (Finset.mem_erase.mpr ⟨hwu, hw⟩)
        by_cases hev : G.right e = v
        · rcases w with u' | v'
          · exfalso
            have hl : G.left e ∈ leftPart S := by
              rw [G.mem_star_inl.mp he]
              exact mem_leftPart.mpr hw
            have hee₀ := huniq e hev hl
            exact hwu (by rw [← G.mem_star_inl.mp he, hee₀])
          · have hvv : v' = v := (G.mem_star_inr.mp he).symm.trans hev
            rw [hvv]
            exact ⟨e₀, G.mem_star_inr.mpr hre₀, hβ'e₀⟩
        · exact ⟨e, he, (hβ'_of_ne e hev).trans hbe⟩
    obtain ⟨l, hl, hsat'⟩ := hS β' hβ' hsel'
    have hnsat : ¬ Literal.Sat (extend G β) l := fun h => hC ⟨l, hl, h⟩
    refine Finset.mem_biUnion.mpr ⟨l, hl, mem_touched_of_extend_ne G hdiff fun heq => ?_⟩
    exact hnsat (by rw [Literal.Sat, ← heq]; exact hsat')
  calc (G.boundary (leftPart S)).card
      ≤ (C.biUnion fun l => touched G l.var).card := Finset.card_le_card hsub
    _ ≤ ∑ l ∈ C, (touched G l.var).card := Finset.card_biUnion_le
    _ ≤ C.card • k := Finset.sum_le_card_nsmul _ _ _ fun l hl => hk l hl
    _ = C.card * k := smul_eq_mul _ _

/-! ### The width lower bound -/

/-- **The perfect-matching principle is wide**, Theorem 1.1 of Itsykson et al. For an expander
graph `H` with `Γ ≥ 1` and `εm ≥ 2`, every resolution refutation of `PM(H)` has width more
than `Γ (εm) / 2`: the first clause of the refutation with `μ(C) > r/2`, for `r = εm`, has a
minimal witness `S` with `r/2 < |S ∩ U| ≤ r`, whose boundary has at least `Γ |S ∩ U|` vertices,
each of them the endpoint of an edge variable of `C`.

Paper: cited in the proof of Theorem [thm:star-local-hard]. -/
theorem width_lower_bound {Δ : ℕ} {Γ ε : ℝ} {m : ℕ} (H : ExpanderGraph Δ Γ ε m) (hΓ : 1 ≤ Γ)
    (hr : 2 ≤ ε * m) (π : Refutation (PM H.G)) : Γ * (ε * m) / 2 < π.width := by
  classical
  set r : ℝ := ε * m with hr_def
  set t : ℕ := ⌊r / 2⌋₊ with ht_def
  have hr0 : 0 ≤ r / 2 := by linarith
  have ht1 : 1 ≤ t := (Nat.le_floor_iff hr0).mpr (by push_cast; linarith)
  have htr : (t : ℝ) ≤ r / 2 := Nat.floor_le hr0
  have hcard : Fintype.card H.U = Fintype.card H.V + 1 := by rw [H.card_U, H.card_V]
  have hinit : ∀ C ∈ PM H.G, HasWitnessLE H.G C t := fun C hC =>
    (hasWitnessLE_one_of_mem H.G hC).mono ht1
  have hbot : ¬ HasWitnessLE H.G ∅ t := by
    rintro ⟨S, hS, hSt⟩
    have h1 := lt_card_leftPart_of_isWitness_empty H.G hcard H.exists_matching
      H.isBoundaryExpander hΓ hS
    have h2 : ((leftPart S).card : ℝ) ≤ t := Nat.cast_le.mpr hSt
    linarith
  obtain ⟨C, hCπ, hPC, C₁, -, C₂, -, hP₁, hP₂, hres⟩ :=
    π.exists_resolvent_of_not _ hinit hbot
  obtain ⟨S₀, hS₀, hk⟩ : HasWitnessLE H.G C (t + t) := hP₁.resolvent hP₂ hres
  obtain ⟨S, hSmem, hSmin⟩ := Finset.exists_min_image
    ((Finset.univ : Finset (Finset (H.U ⊕ H.V))).filter fun S => IsWitness H.G S C)
    (fun S => (leftPart S).card) ⟨S₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS₀⟩⟩
  have hSw : IsWitness H.G S C := (Finset.mem_filter.mp hSmem).2
  have hSle : (leftPart S).card ≤ t + t :=
    (hSmin S₀ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS₀⟩)).trans hk
  have hSgt : t < (leftPart S).card := by
    by_contra h
    exact hPC ⟨S, hSw, not_lt.mp h⟩
  have hmin : ∀ u ∈ leftPart S, ¬ IsWitness H.G (S.erase (Sum.inl u)) C := by
    intro u hu hw
    have h1 := hSmin _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩)
    have h2 : (leftPart (S.erase (Sum.inl u))).card < (leftPart S).card := by
      rw [leftPart_erase_inl]
      exact Finset.card_erase_lt_of_mem hu
    omega
  -- every variable of `C` is an edge variable, depending on a single vertex of `V`
  have hk1 : ∀ l ∈ C, (touched H.G l.var).card ≤ 1 := by
    intro l hl
    obtain ⟨e, he⟩ :=
      mem_vars_PM H.G (Refutation.vars_subset π hCπ (Clause.mem_vars.mpr ⟨l, hl, rfl⟩))
    rw [he, card_touched_X]
  have hbd := card_boundary_le_of_minimal H.G hSw hmin hk1
  rw [mul_one] at hbd
  have hexp := H.isBoundaryExpander (leftPart S) (by
    have h1 : ((leftPart S).card : ℝ) ≤ ((t + t : ℕ) : ℝ) := Nat.cast_le.mpr hSle
    push_cast at h1
    linarith)
  have hw : C.card ≤ π.width := π.card_le_width hCπ
  have hbd' : ((H.G.boundary (leftPart S)).card : ℝ) ≤ C.card := by exact_mod_cast hbd
  have hw' : (C.card : ℝ) ≤ π.width := by exact_mod_cast hw
  have hk' : (t : ℝ) + 1 ≤ (leftPart S).card := by exact_mod_cast hSgt
  have hfloor : r / 2 < (t : ℝ) + 1 := Nat.lt_floor_add_one _
  have hΓ0 : 0 < Γ := by linarith
  calc Γ * r / 2 = Γ * (r / 2) := by ring
    _ < Γ * (leftPart S).card := mul_lt_mul_of_pos_left (by linarith) hΓ0
    _ ≤ (H.G.boundary (leftPart S)).card := hexp
    _ ≤ C.card := hbd'
    _ ≤ π.width := hw'

end PM

end AssocLB
