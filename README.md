# SuperdiffusionCLT

A machine-checked **Lean 4** formalization of the paper

> Scott Armstrong, Ahmed Bou-Rabee and Tuomo Kuusi,
> [*Superdiffusive central limit theorem for a Brownian particle in a critically-correlated
> incompressible random drift*](https://link.springer.com/article/10.1007/s00222-026-01455-z), Invent. Math., to appear.

The paper's main results, Theorems A, B, C and D and the asymptotics of the renormalized diffusivities
(Theorem 5.1), are proved from its assumptions on the random drift, together with every result of Sections 2
to 8 that their proofs use, with no `sorry` and no axiom beyond Lean's and mathlib's standard ones. The formal
proof of Theorem A replaces the parabolic Lemmas 8.2 and 8.3 and the Nash–Aronson estimates of Appendix B by an
elliptic argument; the log-correlated Gaussian example of Appendix A is not formalized (a nondegenerate Gaussian
shell law shows that the assumptions are satisfiable, see below). The development is built on [mathlib](https://github.com/leanprover-community/mathlib4) and
on two public libraries: [CoarseGraining](https://github.com/scottnarmstrong/CoarseGraining), the
homogenization library of Armstrong and Kuusi, and
[MarkovProcess](https://github.com/scottnarmstrong/MarkovProcess), a library of continuous-time Markov
processes.

## What is proved

The paper studies a Brownian particle `dX_t = √(2ν) dB_t + f(X_t) dt` in a random, divergence-free drift
`f = ∇·k` whose stream matrix `k` is a sum of independent shells over all scales, in the critical
(marginally correlated) case, where the effective diffusivity grows like the square root of the logarithm
of the scale. The assumptions on the law `P` of the shells are the paper's (J1)–(J5); in Lean they are
`ShellLawPrefix`, `ShellLawJ1Restriction`, `ShellLawJ2`, …, `ShellLawJ5` in
[`SuperdiffusionCLT/Frozen/Assumptions`](SuperdiffusionCLT/Frozen/Assumptions). The main results are:

- **Theorem A (quenched superdiffusive invariance principle).** For `P`-almost every realization of the
  drift, the diffusion exists as a continuous Feller process with generator `∇·(ν Id + k)∇`, and
  `|log ε²|^{-1/4} ε X_{t/ε²}` converges in law, on `C([0,∞); ℝ^d)` with the topology of locally uniform
  convergence, to `√(2 c⋆^{1/2})` times a standard Brownian motion. Moreover the quenched mean square
  displacement satisfies `|t⁻¹ E⁰|X_t|² − 2 d c⋆^{1/2} (log t)^{1/2}| + t⁻¹ |E⁰X_t|² ≤ C (log t)^{1/4+δ}`
  outside an event of probability at most `C exp(−C⁻¹ (log t)^β)`, together with the corresponding
  annealed `L^p` bound.
  Lean: `SuperdiffusionCLT.Frozen.Section8.theoremA`.
- **Theorem B (quantitative homogenization).** On a smooth bounded domain, solutions of the Dirichlet
  problem for `−(2 c⋆ |log ε|)^{-1/2} ∇·(ν Id + k^ε)∇` are within `C |log ε|^{-α}` of the solutions of the
  Laplace equation with the same data, in `L^∞` and for the gradients and fluxes in `H^{-1}`, for all
  `ε ≤ 1/2` above a random minimal scale with stretched-exponential tails.
  Lean: `SuperdiffusionCLT.Frozen.Section7.superdiffusivity`.
- **Theorem C (large-scale `C^{0,γ}` estimate)** and the corresponding Liouville theorem, above a random
  minimal scale. Lean: `SuperdiffusionCLT.Frozen.Section7.large_scale_holder`.
- **Theorem D (large-scale `C^{1,γ}` estimate)**: the space of solutions of growth `1+γ` has dimension
  `1+d`, flatness at every scale, and the large-scale `C^{1,γ}` estimate.
  Lean: `SuperdiffusionCLT.Frozen.Section6.c1beta`.
- **Theorem 5.1 (asymptotics of the renormalized diffusivities)**:
  `|σ̄_m − (2 c⋆ (log 3) m)^{1/2}| ≤ C c⋆⁻¹ (log² m + Ă)` for all large `m`, where `c⋆` and `Ă` are the
  constants of assumption (J5).
  Lean: `SuperdiffusionCLT.Frozen.Section5.sigmaBar_sharp_bounds`.

Every statement in [`SuperdiffusionCLT/Frozen`](SuperdiffusionCLT/Frozen) is the formal counterpart of a
numbered result of the paper, with a docstring explaining how the printed statement is read. The
assumptions are not vacuous: `SuperdiffusionCLT.Assumptions.ShellLaw.Model.exists_nondegenerate_law_satisfying_all_shellLaws`
constructs a nondegenerate Gaussian shell law satisfying all of them.

The formalization found a few errors in the manuscript, all of them repairable without changing the main
results; they are listed in [`ERRATA.md`](ERRATA.md), whose page and equation numbers refer to the preprint
arXiv:2404.01115v3.

## Guarantees

- **No `sorry`** and no custom axiom: every main theorem depends only on `propext`, `Classical.choice` and
  `Quot.sound`.
- **Independent statement of Theorem A.**
  [`SuperdiffusionCLTAudit/TheoremA/Challenge.lean`](SuperdiffusionCLTAudit/TheoremA/Challenge.lean)
  restates Theorem A with every object rebuilt from mathlib alone, and
  [`Solution.lean`](SuperdiffusionCLTAudit/TheoremA/Solution.lean) proves that restatement from the library;
  the pair is a [leanprover/comparator](https://github.com/leanprover/comparator) configuration, which checks
  that the solution proves exactly the challenge's statement; it is accepted by both the Lean kernel and the
  independent nanoda kernel. See
  [`SuperdiffusionCLTAudit/README.md`](SuperdiffusionCLTAudit/README.md).
- **Zero warnings** under the linter options in [`lakefile.lean`](lakefile.lean).
- **Pinned toolchain**: Lean `v4.35.0-rc2`, mathlib `v4.35.0-rc2`, and the CoarseGraining and MarkovProcess
  libraries at fixed commits recorded in [`lake-manifest.json`](lake-manifest.json).
- Every file is a Lean module.

## Building

The toolchain is pinned in [`lean-toolchain`](lean-toolchain) and managed by
[elan](https://github.com/leanprover/elan).

```bash
lake exe cache get   # prebuilt mathlib
lake build
```

The two library dependencies have no olean cache and are compiled from source on the first build, as is the
project itself; expect several hours. Afterwards `import SuperdiffusionCLT` loads the whole development, and

```bash
lake env lean SuperdiffusionCLT/Meta/AxiomsAudit.lean
```

prints the axioms of every stated theorem.

## Repository layout

```
SuperdiffusionCLT/
  Frozen/        the statements of the paper's results and assumptions (one per file)
  Assumptions/   the random shells, their law, and a model satisfying all assumptions
  Probability/   concentration and Orlicz-norm tools
  Section2/ … Section8/   the paper's Sections 2 to 8
  AKHC61/        the high-contrast homogenization input (Theorem 6.1 of Armstrong–Kuusi)
  Sobolev/       Sobolev-space tools used in Sections 6 to 8
SuperdiffusionCLT.lean   the root module, importing the whole library
SuperdiffusionCLTAudit/  the comparator challenge for Theorem A and its solution
ERRATA.md                corrections to the manuscript
```

## How this was built

The Lean code was written by AI models under the close supervision of the author, mostly by Claude (Opus 5.5,
Fable 5.1 and Opus 5, with Sonnet subagents), with contributions from OpenAI models through Codex. Models,
tooling and review status are disclosed in [`formalization.yaml`](formalization.yaml), following the
[mathlib-initiative](https://github.com/mathlib-initiative/formalization.yaml) standard.

## Authors, citation, license

The Lean development is by **Scott Armstrong**. To cite it, use [`CITATION.cff`](CITATION.cff).

Apache License 2.0; see [`LICENSE`](LICENSE).
