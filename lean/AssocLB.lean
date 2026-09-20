/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/
import AssocLB.Resolution.Basic
import AssocLB.Resolution.Derivation
import AssocLB.Resolution.Substitution
import AssocLB.Resolution.Completeness
import AssocLB.Resolution.SizeWidth
import AssocLB.Resolution.WidthTransfer
import AssocLB.Multiplier.Encoding
import AssocLB.Multiplier.Circuit
import AssocLB.Multiplier.ArrayMultiplier
import AssocLB.Multiplier.ArrayStripLocal
import AssocLB.Multiplier.CarryLookahead
import AssocLB.Multiplier.WallaceTree
import AssocLB.Multiplier.WallaceStripLocal
import AssocLB.Multiplier.Assoc
import AssocLB.Multiplier.StripLocal
import AssocLB.Matching.Expander
import AssocLB.Matching.ISSGraphs
import AssocLB.Matching.StarLocalPM
import AssocLB.Matching.ISSWidth
import AssocLB.Matching.StarLocalHard
import AssocLB.Reduction.Outline
import AssocLB.Reduction.IndexMaps
import AssocLB.Reduction.Restriction
import AssocLB.Reduction.Propagation
import AssocLB.Reduction.Locality
import AssocLB.LowerBound
import AssocLB.Frege.Formula
import AssocLB.Frege.System
import AssocLB.Frege.Substitution
import AssocLB.Frege.LocalDerivations
import AssocLB.Frege.PerfectMatching
import AssocLB.Frege.Grid
import AssocLB.Frege.Hastad
import AssocLB.Frege.Transfer
import AssocLB.Frege.LowerBound

/-!
# AssocLB

Lean 4 formalization of the paper *Associativity of Multiplication Is Hard for
Resolution* (`../associativity_lower_bound.tex`), including the bounded-depth
Frege lower bound of its Section 9 (`AssocLB.Frege.*`, conditional on Håstad's
theorem `HastadGridPM`).

This root module imports every module of the library. The layout follows the
paper's sections; see `README.md` for the correspondence.
-/
