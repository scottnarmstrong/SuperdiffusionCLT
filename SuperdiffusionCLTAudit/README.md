# Comparator challenge for Theorem A

`TheoremA/Challenge.lean` restates Theorem A of Armstrong–Bou-Rabee–Kuusi, *Superdiffusive
central limit theorem for a Brownian particle in a critically-correlated incompressible random
drift* (arXiv:2404.01115), using Mathlib alone. Theorem A is the quenched superdiffusive
invariance principle, together with its quenched and annealed bounds on the mean squared
displacement.

The challenge defines everything the statement uses:

* the shells and their topology and σ-algebra;
* the standing assumptions and (J1)–(J5), including the stationary block response that
  defines `c⋆`;
* the recentred coefficient field `ν Id + k − k(0)`;
* the divergence-form Feller semigroups and their continuous-path laws;
* the heat kernel;
* path rescaling.

The theorem is stated without proof. Read this file to see what is claimed.

`TheoremA/Solution.lean` proves the same theorem from the library's
`SuperdiffusionCLT.Frozen.Section8.theoremA`. `TheoremA/SolutionBasic.lean` copies the
challenge's definitions verbatim. `TheoremA/Support/` identifies each challenge definition
with its library counterpart. `TheoremA/DESIGN.md` lists the identifications and every
presentation choice.

## Running the comparator

Build the library and the audit modules, then run
[leanprover/comparator](https://github.com/leanprover/comparator) on the configuration:

```
lake build SuperdiffusionCLTAudit
lake env <path-to>/comparator SuperdiffusionCLTAudit/TheoremA/comparator.json
```

The `lean4export`, `nanoda` and `landrun` binaries must be available, for example through
`COMPARATOR_LEAN4EXPORT`, `COMPARATOR_NANODA` and `COMPARATOR_LANDRUN`. The comparator checks
four things:

* the solution's theorem has exactly the challenge's statement;
* every definition the statement uses is the same in both;
* the proof replays in the Lean kernel and in nanoda;
* the only axioms used are `propext`, `Quot.sound` and `Classical.choice`.

A successful run ends with `Your solution is okay!`.
