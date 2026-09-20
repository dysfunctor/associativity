# AssocLB

Lean 4 formalization, on top of Mathlib, of

> Vincent Liew, *Associativity of Multiplication Is Hard for Resolution*
> (`../associativity_lower_bound.tex`).

The paper shows that general resolution refutations of the associativity of
`n`-bit multiplication, for any strip-local multiplier encoding, require size
`2^{Ω((n / log n)^{1/4})}`.

## Status

Everything is proved. The library builds with no `sorry`, and every theorem
below depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`. The one result imported from the literature, Håstad's lower bound
for the odd grid, is a hypothesis of the Frege theorem, not an axiom.

| Result | Paper | Lean | Hypotheses |
| --- | --- | --- | --- |
| Resolution lower bound `2^{Ω((n / log n)^{1/4})}` for a strip-local family | Thm. 8.8 (Lower bound for multiplier associativity; `thm:main`) | `main` (`AssocLB/LowerBound.lean`) | `ISSGraphs`, `BWTradeoff`, both proved (`issGraphs`, `bwTradeoff`) |
| The same for the array and Wallace-tree multipliers | Thm. 8.8 (Lower bound for multiplier associativity; `thm:main`) | `main_arrayMul`, `main_wallaceMul` | none |
| Bounded-depth Frege lower bound `exp(n^{γ/d})` for depth `d ≤ γ log n / log log n` | Thm. 9.5 (Bounded-depth Frege lower bound; `thm:frege`) | `frege_main`, `frege_main_arrayMul`, `frege_main_wallaceMul` (`AssocLB/Frege/LowerBound.lean`) | `HastadGridPM 𝓕`, Håstad's Theorem 9.3 (Håstad's theorem; `thm:hastad`) (imported, not proved) |

The Frege theorem is conditional: `frege_main` takes `HastadGridPM 𝓕` as an
explicit hypothesis, as `main` takes `ISSGraphs` and `BWTradeoff`, and no
instance of `FregeSystem` is constructed, so it holds for every Frege system.
Its constant is chosen explicitly, `γ = c / (160 (1 + d₀))` where the paper has
`c / (18 (1 + d₀))`; the theorem asserts only that some `γ > 0` works. Remarks
9.6 and 9.7 are not formalized.

## Layout

The library follows the paper's sections. Each module's docstring lists the
paper items it is meant to formalize, cited by their LaTeX labels; the table
below gives each item's number in the paper with its label in parentheses.

| Module | Paper |
| --- | --- |
| `AssocLB/Resolution/Basic.lean` | §2, CNF formulas: literals, clauses, width, satisfaction |
| `AssocLB/Resolution/Derivation.lean` | §2, Resolution: the resolution rule, derivations, refutations, size, width, soundness |
| `AssocLB/Resolution/Substitution.lean` | §2, restrictions and substitutions; Lemma 2.2 (Substitution lemma; `lem:substitution`), its special case for restrictions, and the subclause observation used implicitly in Lemma 8.7 (Reduction from perfect matching; `lem:reduction`) |
| `AssocLB/Resolution/Completeness.lean` | §2, Resolution: refutational and implicational completeness |
| `AssocLB/Resolution/SizeWidth.lean` | §2, Thm. 2.1 (`thm:bw`), the Ben-Sasson–Wigderson size–width tradeoff: `bwTradeoff`, with constant `32` |
| `AssocLB/Resolution/WidthTransfer.lean` | §5, Lemma 5.5 (Width transfer; `lem:width-transfer`): `width_transfer`, a refutation of an extension by variables defined over at most `Δ` of the original variables yields a refutation of the original CNF of at most `2Δ` times the width; implicational completeness within the variables of the premises |
| `AssocLB/Multiplier/Encoding.lean` | §2, Defs. 2.3 (Exact multiplier encoding; `def:exact-encoding`), 2.4 (Partial products, columns; `def:partial-products`): bit-vectors, partial products, the full adder, exact multiplier encodings and their evaluation |
| `AssocLB/Multiplier/Circuit.lean` | §2, circuits and Tseitin encodings; exactness, used for the array multiplier, the Wallace tree and the miter |
| `AssocLB/Multiplier/ArrayMultiplier.lean` | §2, Fig. 1 (`fig:array-multiplier`): the array multiplier `arrayMul` as an exact encoding |
| `AssocLB/Multiplier/ArrayStripLocal.lean` | §4, Prop. 4.6 (`prop:array-strip-local`): the array multiplier is strip-local |
| `AssocLB/Multiplier/Assoc.lean` | §3, Def. 3.1 (Associativity miter; `def:assoc`): the associativity formula `Assoc_n` |
| `AssocLB/Multiplier/StripLocal.lean` | §4, Defs. 4.1 (`g`-strip; `def:g-strip`), 4.2 (`g`-sparse restriction; `def:g-sparse`), 4.3 (Strip-local; `def:strip-local`); Obs. 4.5 (Strips count their partial products; `obs:strip-counts`) |
| `AssocLB/Multiplier/CarryLookahead.lean` | Appendix, Def. A.1 (Carry-lookahead adder; `def:cla`): the semantics of carry-lookahead addition (group propagate/generate folds) |
| `AssocLB/Multiplier/WallaceTree.lean` | Appendix, Defs. A.1 (Carry-lookahead adder; `def:cla`), A.2 (Wallace-tree multiplier; `def:wallace`), Obs. A.3 (`obs:wallace-exact`): the Wallace-tree multiplier `wallaceMul` as an exact encoding |
| `AssocLB/Multiplier/WallaceStripLocal.lean` | Appendix, Lemmas A.4 (Wallace-tree strip-locality; `lem:wallace-tree-local`), A.5 (Carry-lookahead adder strip-locality; `lem:cla-local`), Prop. 4.7 (`prop:wallace-strip-local`): the Wallace-tree multiplier is strip-local, `wallaceMul_stripLocal` |
| `AssocLB/Matching/Expander.lean` | §2, bipartite graphs and matchings; §5, Def. 5.3 (Boundary expander; `def:boundary-expander`) and Thm. 5.4 (`thm:iss-graphs`) as the proposition `ISSGraphs` |
| `AssocLB/Matching/ISSGraphs.lean` | §5, Thm. 5.4 (`thm:iss-graphs`): `issGraphs`, existence of the expander graphs (`Δ = 7`, `Γ = 3`, `ε = 10⁻⁸`) by counting |
| `AssocLB/Matching/StarLocalPM.lean` | §5, Defs. 5.1 (Perfect-matching CNF; `def:pm`), 5.2 (Star-local extension; `def:star-local-ext`): `PM`, `SPM`; Lemma 5.7 (Local consequences have constant-size derivations; `lem:star-local-derivations`) |
| `AssocLB/Matching/ISSWidth.lean` | §5, the width lower bound `Γ r / 2` for `PM(H)` of Itsykson et al. (Theorem 1.1 of the ECCC full version), cited in the proof of Thm. 5.6 and proved here: `PM.width_lower_bound` |
| `AssocLB/Matching/StarLocalHard.lean` | §5, Thm. 5.6 (The star-local extension remains hard; `thm:star-local-hard`): the width bound by `width_transfer` from `PM.width_lower_bound`, and the size bound |
| `AssocLB/Reduction/Outline.lean` | §6, the reduction abstractly: Restrict, Substitute, Compose |
| `AssocLB/Reduction/IndexMaps.lean` | §7.1, the index maps `i(u)`, `j(e)`, `k(v)` |
| `AssocLB/Reduction/Restriction.lean` | §7.2, the restriction `ρ` |
| `AssocLB/Reduction/Propagation.lean` | §8, Def. 8.1 (Propagated assignment; `def:propagation`); Lemma 8.5 (Inner multipliers impose perfect matching; `lem:inner-pm`); the miter case of Lemma 8.6 (Local soundness; `lem:local-soundness`); also §7.2, Lemma 7.6 (`ρ` forces disagreement; `lem:rho-outer-outputs`), on which the miter case rests |
| `AssocLB/Reduction/Locality.lean` | §8, Defs. 8.2 (Edge- and star-local; `def:edge-star-local`), 8.3 (Support of a restricted clause; `def:support`), Lemma 8.4 (Locality; `lem:locality`), and the constant-size support bound used in Lemma 8.7 |
| `AssocLB/LowerBound.lean` | §8, the reduction, Lemma 8.6 (Local soundness; `lem:local-soundness`), Lemma 8.7 (Reduction from perfect matching; `lem:reduction`), and Thm. 8.8 (Lower bound for multiplier associativity; `thm:main`): `main`, `main_arrayMul`, `main_wallaceMul` |
| `AssocLB/Frege/Formula.lean` | §9.1, "Formulas and depth": `Formula`, depth, size, `F^σ`; clauses as formulas; the canonical DNF |
| `AssocLB/Frege/System.lean` | §9.1, "Frege systems": `FregeRule`, `FregeSystem`, derivations, refutations, size, depth; the cut and the Compose step |
| `AssocLB/Frege/Substitution.lean` | §9.1, "Formula substitutions", Lemma 9.1 (Frege substitution lemma; `lem:frege-substitution`); `ρ` as a formula substitution; weakening |
| `AssocLB/Frege/LocalDerivations.lean` | §9.1, Lemma 9.2 (Local consequences have constant-size Frege derivations; `lem:frege-local-derivations`) |
| `AssocLB/Frege/PerfectMatching.lean` | Def. 5.1 (Perfect-matching CNF; `def:pm`) over the edge variables: `EdgePM`, as used in §9 |
| `AssocLB/Frege/Grid.lean` | §9.2, the odd grid `grid t` and its properties |
| `AssocLB/Frege/Hastad.lean` | §9.2, Thm. 9.3 (Håstad's theorem; `thm:hastad`) as the proposition `HastadGridPM` (imported, not proved) |
| `AssocLB/Frege/Transfer.lean` | §9.3, the formula substitution `σ` and Lemma 9.4 (Reduction from `PM(H)`; `lem:frege-transfer`), `FregeSystem.frege_transfer` |
| `AssocLB/Frege/LowerBound.lean` | §9.3, Thm. 9.5 (Bounded-depth Frege lower bound; `thm:frege`): `frege_main`, conditional on `HastadGridPM` |

## Building

Requires [elan](https://github.com/leanprover/elan). The toolchain is pinned in
`lean-toolchain` (Lean v4.33.1) and Mathlib is pinned in `lakefile.toml` to the
matching release tag, so prebuilt Mathlib oleans are available.

From this directory:

    lake exe cache get   # prebuilt Mathlib oleans: on a fresh clone, and after `lake update`
    lake build

Bump the Mathlib pin only together with `lean-toolchain`, to a tag for which a
cache exists.

## License

Apache 2.0, see `LICENSE`. It covers this directory only; the paper sources in
the parent directory are not part of the Lean package.
