# Theorem A challenge: design

`Challenge.lean` imports Mathlib only and restates `SuperdiffusionCLT.Frozen.Section8.theoremA`
as `SuperdiffusionCLT.StatementAudit.TheoremA.theoremA`. `SolutionBasic.lean` repeats the
challenge's definitions verbatim. `Solution.lean` proves the theorem from the library through
`Support/Bridge.lean`, `Support/ProjectionTransport.lean` and `Support/BrownianUniqueness.lean`.
Where the challenge copies a library body, the bridge is definitional (`rfl`, or a structure
rebuilt from its fields). In the other cases the bridge is a proved equivalence.

## Challenge definitions and their library counterparts

| Challenge | Library | Bridge |
|---|---|---|
| `Vec`, `Mat`, `CoeffField` | `Homogenization.Vec`, `Mat`, `CoeffField` | definitional |
| `vecNorm` | `Homogenization.Book.Ch02.vecNorm` | definitional |
| `vecNormSq` (`∑ xᵢ xᵢ`) | `Homogenization.vecNormSq` (`vecDot x x`) | definitional |
| `matrixOperatorNorm` | `Homogenization.Book.Ch02.matrixOperatorNorm` | definitional |
| `IsSignedPermutationMatrix` | `Homogenization.IsSignedPermutationMatrix` | definitional |
| `ShellField`, its topology, its σ-algebra | `Frozen.Assumptions.ShellField`, `shellFieldCompactOpenTopology`, `shellFieldBorelMeasurableSpace` | definitional |
| norm instances on `Vec d →L[ℝ] Mat d` and on second derivatives | `ShellField.shellFirstDeriv*`, `shellSecondDeriv*` | definitional |
| `ShellField.translate` | `ShellField.translate` | definitional |
| `ShellField.negate` | `ShellField.negate` (`scale (-1)`) | definitional |
| `ShellField.matVecCLM`, `conjugateCLM`, `rotateDerivCLM`, `rotateSecondDerivCLM`, `rotate` | `matVecContinuousLinearMap`, `conjugateContinuousLinearMap`, `rotateDerivativeMap`, `rotateSecondDerivativeMap`, `rotate` | definitional |
| `RegField` (a subtype) | `Homogenization.RegCoeffField` (a structure) | measurable equivalence `regEquiv` |
| `IsProbe` (a conjunction) | `Homogenization.IsProbeR` (a structure) | equivalent |
| σ-algebra on `RegField` | `instMeasurableSpaceRegCoeffField` (`pointwiseSigmaR ⊔ entryTestSigmaR`) | `comap_toLibReg` |
| translation action on `RegField` | `regCoeffFieldAddAction` (`translateReg`) | definitional through `regEquiv` |
| `RegField.ofContinuous` | `ShellField.forgetShell` | definitional through `regEquiv` |
| `RegField.restrict` | `Homogenization.restrictReg` | definitional through `regEquiv` |
| `shellMarginalLaw` | `ShellField.shellMarginalLaw` | definitional |
| `ShellLawPrefix`, `ShellLawJ2`, `ShellLawJ3`, `ShellLawJ4` | the frozen structures of the same names | rebuilt from fields |
| `ShellLawJ1Restriction` | the frozen structure | the restriction σ-algebras are equal (`shellLawJ1Restriction_lib`) |
| `UnitBall`, `derivNorm`, `secondDerivNorm`, `CubePoint`, `j3Observable` | `EuclideanUnitVector`, `matrixDerivativeNorm`, `matrixSecondDerivativeNorm`, `ShellOpenCubePoint`, `j3Observable` | definitional |
| `koopman`, `HasHorizontalGradient`, `potentialProjection` | `Probability.Stationary.koopman`, `HasHorizontalGradient`, `stationaryPotentialProjection` | `potentialProjection_eq` |
| `blockLaw` | `Section2.Cutoff.blockRegLaw` | `blockLaw_eq` (image under `regEquiv.symm`) |
| `ShellLawJ5` | the frozen structure, with `blockPotentialResponse` | `shellLawJ5_lib`, using `norm_stationaryPotentialProjection_congr` |
| `fullCoefficientRecentered` | `Section6.fullCoefficientRecentered` | definitional |
| `divForm` | `Section8.divForm` | definitional |
| `SubMarkovKernelSemigroup` | `MarkovProcess.SubMarkovKernelSemigroup` | `toLib` / `ofLib` |
| `IsConservative`, `MapsC0`, `c0KernelIntegral` | the `MarkovProcess` definitions of the same names | definitional |
| `IsDivergenceFormFeller` | `Section8.IsDivergenceFormFeller` | `isDivergenceFormFeller_iff` |
| `ContinuousPath` and its Borel σ-algebra | `MarkovProcess.ContinuousPath` and its instance | definitional |
| `OrderedTimes`, `relativeTail`, `finiteTimeKernel`, `finiteSetKernel` | `FiniteOrderedTimes`, `relativeTail`, `SubMarkovKernelSemigroup.finiteTimeKernel`, `finiteSetKernel` | `finiteSetKernel_eq` (induction) |
| `IsContinuousPathLaw` | `Section8.IsContinuousPathLaw` | `isContinuousPathLaw_iff` |
| `heatKernel` | `Section8.Brownian.heatKernel` (with `stdGaussian`, `heatKernelJoint` inlined) | definitional |
| `scalePath` | `Section8.scalePath` (with `timeScaling` inlined) | definitional |
| `theoremA` | `Frozen.Section8.theoremA` | `Solution.lean` |

## Presentation deltas

1. **Brownian motion.** The library's limit is `brownianMotion d 0`, built by `MarkovProcess`'s
   Kolmogorov construction. That construction is too long to restate. The challenge therefore
   asserts that a continuous-path law `W` of the heat kernels exists: this is the new first
   conjunct `∃ W, IsContinuousPathLaw (heatKernel d) W`. The convergence clause then holds for
   every such `W`, with limit law `W 0`. The heat kernel itself is defined explicitly, as the
   image of the product Gaussian `∏ᵢ N(0, 1)` under `z ↦ x + √t z`. Existence follows from
   `isContinuousPathLaw_brownianMotion`. Uniqueness (`W 0 = brownianMotion d 0`) is
   `eq_brownianMotion_of_isContinuousPathLaw`.
2. **The generator clause of `IsDivergenceFormFeller`.** The library writes
   `∃ hF : IsFellerKernelSemigroup, … ∃ hu : u ∈ hF.c0Semigroup.generatorDomain,
   hF.c0Semigroup.generator ⟨u, hu⟩ = v`. The challenge writes the Feller property as
   `∃ hC0 : MapsC0, (∀ f, Continuous fun t ↦ S_t f)`, and the generator clause as
   `t⁻¹ (S_t u − u) → v` in `C₀` as `t → 0⁺`. This is the definition of the generator domain
   and of the generator, so the challenge does not need the packaged `C₀` semigroup.
   Equivalence: `generator_eq_iff_tendsto`.
3. **(J5) proof arguments.** The library's `ShellLawJ5` takes `hPrefix hJ2 hJ3` and passes the
   theorems `blockRegLaw_stationary` and `memLp_originForcing_blockRegLaw` to
   `blockPotentialResponse`. The challenge's `ShellLawJ5 d P cStar K` instead quantifies over
   the translation measurability, the translation invariance of the block law, and the `L²`
   membership of the forcing. All three are propositions. Under the prefix, (J2) and (J3)
   they hold, so the two forms are equivalent. Without the prefix, (J2) and (J3) the
   challenge's form is weaker, which makes the challenge theorem stronger. The theorem keeps
   the prefix, (J2) and (J3) as hypotheses in the library's order, but they are unnamed.
4. **Regular fields as a subtype.** `RegField` is a subtype of `Vec d → Mat d`, where the
   library uses a structure. Its σ-algebra is written directly as the join of the pointwise
   σ-algebra and the entry-test σ-algebra. It equals the comap of the library's σ-algebra
   (`comap_toLibReg`). `IsProbe` is a conjunction where the library uses a structure.
5. **The stationary potential subspace** is written as the closure of the linear span of the
   horizontal gradients. The library proves that the set of gradients is already a subspace
   and closes that subspace. The two subspaces coincide by `Submodule.span_eq`.
6. **Block law and forcing.** `blockLaw` is a `Measure`, the image of `P` under
   `F ↦ ∑_{n<k≤m} jₖ`. The library uses the `ProbabilityMeasure` `blockRegLaw`. The forcing
   `a ↦ a(0) e` is written with `Matrix.mulVec` and `WithLp.toLp`. The library uses
   `matVecMul` and `HilbertVec.ofVec`, which are definitionally equal to these.
7. **Feller conservativity and semigroup.** The challenge's `SubMarkovKernelSemigroup` is the
   library's structure with the same fields, restated. `IsSubMarkovKernel` is inlined. The
   time-scaling map, `stdGaussian` and `heatKernelJoint` are inlined into `scalePath` and
   `heatKernel`. `finsetEvaluation` is inlined as `fun path t ↦ path t`.
8. **Literal forms kept for definitional equality.** The bounds of the cube `□ₙ` read
   `((0 : ℤ) : ℝ) ∓ 1/2) · 3^(n : ℤ)`, which is the library's `openCubeSet (originCube d n)`
   unfolded. The induced norms take a supremum over `Option` (the `none` value `0`), as the
   library does.
9. **Names.** Every challenge object lives in `SuperdiffusionCLT.StatementAudit.TheoremA`.
   The theorem's prefix, (J2) and (J3) binders are unnamed.
10. **Module root.** The audit library is `SuperdiffusionCLTAudit`, not `Audit`. The
    dependencies `MarkovProcess` and `CoarseGraining` each declare a library named `Audit` with
    the glob `.submodules Audit`. Lake therefore resolves every `Audit.*` import into those
    packages.

## Differences from the printed statement (arXiv:2404.01115v3)

The challenge states the theorem the library proves; where that differs from the printed Theorem A
and assumptions, the difference is a reading of the text, never a weakening of the conclusion:

1. **The process** is specified by its generator: the conclusions hold for every conservative Feller
   semigroup whose generator acts as `∇·(ν Id + k − k(0))∇` on twice continuously differentiable
   functions vanishing at infinity (with the image vanishing at infinity), and for every
   continuous-path law with these transition kernels; a separate clause asserts that such a process
   exists for almost every realization. The convergence holds for every starting point `x₀`, with
   one null set for all of them.
2. **The coefficient field** is the recentred field `ν Id + (k − k(0))`; the series for `k` itself
   does not converge, and the constant skew matrix `k(0)` does not change the operator.
3. **Constants.** `C` is chosen after `ν, c⋆, K, δ, β` and may depend on all of them, as in the
   printed `C(β, δ, c⋆, ν, Ă, d)` (here `K` is `Ă`); `C_p` depends also on `p`.
4. **Assumptions.** (J1) is stated with the σ-algebras of pointwise restrictions and non-strict
   separation at the range `3ⁿ √d`; (J3) uses a stored `C²` shell carrier (the printed assumption
   asks for `C^{1,1}_loc`) and fixes the norms of its regularity observable; the constants `c⋆` and
   `Ă` of (J5) are explicit parameters; stationarity is assumed shell by shell (equivalent to joint
   stationarity under (J2)).
5. **Integrability** of the quenched second moment is part of the conclusion, so no junk value of the
   Bochner integral enters the quantitative clauses; the event of the second clause is a set of
   samples (outer measure if it is not measurable).
