# Associativity of Multiplication Is Hard for Resolution

[![Lean](https://github.com/dysfunctor/associativity/actions/workflows/lean.yml/badge.svg)](https://github.com/dysfunctor/associativity/actions/workflows/lean.yml)

Welcome!

**[Read the paper (PDF)](associativity_lower_bound.pdf)**

**[Proof slides (PDF)](associativity-proof-slides.pdf)**

**[Interactive applet (HTML)](https://dysfunctor.github.io/associativity/)**

This repository holds a writeup, accompanied by a Lean formalization, of an exponential lower bound on the size of general resolution refutations of multiplier associativity. Specifically, we show a size lower bound of `2^{Ω((n / log n)^{1/4})}` for associativity of `n`-bit multiplication, for a broad class of multiplier encodings. This lower bound applies, for instance, to standard array multipliers and Wallace-tree multipliers.

## Note from the author

For the surrounding context and motivation for why this result is interesting, I recommend reading the [paper](associativity_lower_bound.pdf) introduction (Section 1) and conclusion (Section 10). Long story short, it has been observed for a long time that modern SAT solvers struggle with formulas involving multiplication. This repository's lower bound is a first step towards a theoretical explanation of this empirical phenomenon. In particular, this is the first non-trivial resolution proof size lower bound for a natural formula involving multiplication.

To understand the main ideas of the proof, I recommend starting with the [proof slides (PDF)](associativity-proof-slides.pdf), then (or concurrently) reading through Sections 2-6 of the [paper](associativity_lower_bound.pdf). The [interactive applet](https://dysfunctor.github.io/associativity/) may also be helpful for visualizing the construction. Afterwards, if you are interested in the technical details, go ahead and read through the full proof (Sections 7 and 8).

## Lean formalization

The directory [`lean/`](lean) formalizes the main theorems in Lean 4 on top of
Mathlib, with no `sorry`. Start with the
[resolution lower bound](lean/AssocLB/LowerBound.lean) (`main`, Theorem 8.8) and the
[bounded-depth Frege lower bound](lean/AssocLB/Frege/LowerBound.lean)
(`frege_main`, Theorem 9.5, conditional on Håstad's theorem), follow the
[proof modules](lean/AssocLB.lean), or browse the
[correspondence with the paper](lean/README.md).

With [elan](https://github.com/leanprover/elan) installed, run from `lean/`:

```sh
lake exe cache get
lake build
```

Lean and Mathlib versions are pinned. CI builds the library on every push.
The main theorems depend only on the axioms `propext`, `Classical.choice` and
`Quot.sound`. Code: [Apache 2.0](lean/LICENSE).
