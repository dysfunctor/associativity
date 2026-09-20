/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/
import AssocLB.Frege.System
import AssocLB.Frege.PerfectMatching
import AssocLB.Frege.Grid

/-!
# Håstad's lower bound for the odd grid

Paper: Section 9.2 (The odd grid), Theorem [thm:hastad] (Håstad, Theorem 5.1 of
`hastad-php`): for odd `t` and `d ≤ O(log t / log log t)`, every depth-`d` Frege refutation
of `PM(Grid_t)`, the functional onto pigeonhole principle on the odd grid, has size
`exp(Ω(t^{1/(2d−1)} (log t)^{O(1)}))`; in particular, for some `c > 0`, size at least
`exp(t^{c/d})` whenever `d ≤ c log t / log log t`.

## Main definitions

* `HastadGridPM 𝓕`: the weak form of Theorem [thm:hastad] (the display `eq:hastad-weak` of the
  paper) for the Frege system `𝓕`, as a proposition.

## Design notes

* Håstad's theorem is imported, not proved: it is the source of hardness of Section 9, as
  Theorem [thm:iss-graphs] and Theorem [thm:bw] were for Section 8, and unlike those it is not
  going to be formalized. It is stated as the proposition `HastadGridPM 𝓕` and taken as an
  explicit hypothesis by every result depending on it (`frege_main`), so that the library
  has no axioms beyond Lean's; the theorem of Section 9 is conditional on it.
* The proposition quantifies over the Frege system, as the paper notes that Håstad's argument
  applies to every Frege system. It is stated in the paper's weak form, with one constant `c`
  serving both as the depth threshold and in the exponent, which is all that Theorem
  [thm:frege] uses.
* Depth `d` ranges over `d ≥ 1`. Depth-`0` refutations do not exist (the clauses of `PM` have
  depth `1`), and excluding `d = 0` avoids the division `c / 0`.
* The refutation is of `(EdgePM (grid t)).toFormulas`, the formulas of the perfect-matching
  CNF over the edge variables of the grid, so the variable type is exactly Håstad's.
-/

namespace AssocLB

/-- **Håstad's lower bound for `PM(Grid_t)`**, weak form, for the Frege system `𝓕`: there is a
constant `c > 0` such that for every odd `t ≥ 3` and every depth `1 ≤ d ≤ c log t / log log t`,
every refutation of `PM(Grid_t)` of depth at most `d` has size at least `exp(t^{c/d})`, stated
as `t^{c/d} ≤ log |π|`.

Paper: Theorem [thm:hastad], second statement (`eq:hastad-weak`); Håstad, Theorem 5.1. -/
def HastadGridPM (𝓕 : FregeSystem) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ t : ℕ, Odd t → 3 ≤ t → ∀ d : ℕ, 1 ≤ d →
    (d : ℝ) ≤ c * Real.log t / Real.log (Real.log t) →
    ∀ π : 𝓕.Refutation (EdgePM (grid t)).toFormulas, π.depth ≤ d →
      (t : ℝ) ^ (c / (d : ℝ)) ≤ Real.log π.size

end AssocLB
