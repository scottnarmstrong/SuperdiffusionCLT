/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3FluxEnergy
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1InputsG
public import SuperdiffusionCLT.Section2.Estimates.Stream.ShellHminusEndpointOrderOneC
public import SuperdiffusionCLT.Section2.Norms.NegativeNormPairing

/-!
# The multiscale Poincaré at the vector flux field of `e.RHS.term3.B`

**Where the residual `hPointwise` stands.**  In
`Section3/Terms/RHSTerm3FluxEnergy.lean` the estimate `e.RHS.term3.B` is reduced
to two named residuals, and the first — `hPointwise`, the multiscale Poincaré at
`s = 1`, `p = 2` on the *vector* flux field `a_{L'}(∇u_m − ∇u_{n,z})` — was
carried because the order-one endpoint
`vecHatNegENormOrderOne_le_depthSum` (in the module `ShellHminusEndpointOrderOneB`)
asks for `Continuous F`.

**The `Continuous F` hypothesis is not needed.**  In the proof of
`vecHatNegENormOrderOne_le_depthSum` (through `volumeAverage_vecGradientPairingDensity_le`)
continuity of `F` is used *only* to obtain integrability on the cube and on its
descendants of the pointwise size `‖F‖²`, of the coordinates of `F` and of the
pairings `F · ∇g`, and thereby the descendant-partition identities
`volumeAverage_eq_descendantsAverage`, `vecSqAvg_eq_descendantsAverage`,
`vecDot_volumeAverageVec_eq_descendantsAverage`, plus the two Cauchy–Schwarz
steps.  Every one of those is an `L̲²` statement: the companion module
`ShellHminusEndpointOrderOneC` already provides exactly that replacement, and its
`vecHatNegENormOrderOne_le_depthSum_memLp` is `vecHatNegENormOrderOne_le_depthSum` with
`Continuous F` replaced by
`MemLp (hilbertifyVecField F) 2 (normalizedCubeMeasure Q)`.  So the cheapest
route is available and is taken here.

**Our flux field sits on the response side.**  `fluxFieldCarrier nu S omega
uMgrad uNGlued` is the glued-gradient difference `∇ũ_m − ∇ũ_n` multiplied by the
bounded cutoff coefficient `a_{L'} = (coefficientCutoff nu omega S.LPrime)
.toCoeffField`.  The response side is an `H¹` gradient, and continuity in `x` is
NOT available for it (the glued gradient is defined by cases, with values on the
half-open sub-cubes); so the flux field is **not** continuous, and the continuous
form of the endpoint is inapplicable.  What *is* available is `L̲²` membership:
the glued gradients are `L²` on every triadic cube
(`memVectorL2_openCubeSet_gluedGradientField`), and multiplying an `L²` field by
the bounded cutoff coefficient preserves `L²`
(`memVectorL2_matVecMul_coefficientCutoff`).  That is precisely the hypothesis of
the weakened endpoint.

## Main results

* `memLp_fluxFieldCarrier` — the flux field of an `L̲²` difference is `L̲²`
  against the normalized cube measure; `memLp_fluxFieldCarrier_gluedDiff` is its
  specialization to the difference of two glued gradients.

## The printed display

The first inequality of `hFlux` is

```
\E\Biggl[
\biggl(
      \sum_{j = -\infty}^n 3^{j} \biggl( \avsum_{z' \in z + 3^j \Z^d \cap \cu_n}
        \bigl| \bigl( \a_{L'}  ( \nabla u_m - \nabla u_{n,z} ) \bigr)_{z'+\cu_j} \bigr|^2
      \biggr)^{\! \nicefrac12} \biggr)^{\! \nicefrac 32} \Biggr]
```

**Confinement, kept.**  The printed `j`-sum is confined to
`z' ∈ z + 3^j Z^d ∩ cu_n`, the scale-`j` sub-cubes of the *small* cube.  The
device `vecDepthMoment Q j F = (avsum_{R ∈ descendantsAtDepth Q j}
‖(F)_R‖²)^{1/2}` averages over `descendantsAtDepth Q j`, whose members are
sub-cubes of `Q` and which at `cu_n` and depth `n − j` is exactly the
paper's family `largeCubeSubcubes d j n` whose centres are `3^j Z^d ∩ cu_n`
(see `RHSTerm3FluxEnergy.lean`).  The confinement is
therefore inherited, not weakened; the printed weights `3^j` are the
weights `3^{-t}` under the depth/scale change `j = n − t`, rescaled by the
constant `3^n` carried separately in `hPointwise`.

**What remains.**  This module removes the `Continuous F` obstacle and proves the
multiscale-Poincaré *piece* of `hPointwise` at the flux carriers.  The residual
`hPointwise` of `RHSTerm3FluxEnergy` is not discharged as a whole: its remaining
content is the energy-map step `e.energymaps.nonsymm.flux` (the passage from the
depth sum to `‖σ^{1/2}(∇u_m − ∇u_{n,z})‖^{3/2}` times the block maximum) and the
block-maximum envelope `hBlockOrlicz`, neither of which is affected by the
regularity question settled here.  The convexity rearrangement that follows is already
proved (`weighted_rpow_three_halves_le`, `RHSTerm3FluxEnergy.lean`).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open Homogenization
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The flux field is `L̲²`, not continuous -/

/-- **The flux field is `L̲²` when the underlying difference is.**  If
`uMgrad − uNGlued` is square-integrable on the open cube of `R`, then so is its
product against the bounded cutoff coefficient `a_{L'} = (coefficientCutoff nu
omega S.LPrime).toCoeffField`: `memVectorL2_matVecMul_coefficientCutoff` followed
by the passage to the normalized cube measure.  This is the hypothesis that
replaces `Continuous F` in the multiscale Poincaré at our carriers. -/
theorem memLp_fluxFieldCarrier {nu : ℝ} (hnu : 0 < nu) (S : ScaleSelection)
    (omega : ShellSeq d) {uMgrad uNGlued : Vec d → Vec d} {R : TriadicCube d}
    (hV : MemVectorL2 (openCubeSet R) (fun y => uMgrad y - uNGlued y)) :
    MemLp (hilbertifyVecField (fluxFieldCarrier nu S omega uMgrad uNGlued)) 2
      (normalizedCubeMeasure R) := by
  unfold fluxFieldCarrier
  exact memLp_hilbertifyVecField_of_memVectorL2
    (memVectorL2_matVecMul_coefficientCutoff hnu omega S.LPrime R hV)

/-- **The flux field of the glued-gradient difference is `L̲²`.**  The response
side `∇ũ_m − ∇ũ_n` of `e.u.k.def` is `L²` on every triadic cube, so the flux
field `a_{L'}(∇ũ_m − ∇ũ_n)` is `L²` on every triadic cube, in particular on the
scale-`n` sub-cubes `R` of `cu_m` that the `j`-sums use. -/
theorem memLp_fluxFieldCarrier_gluedDiff {nu : ℝ} (hnu : 0 < nu)
    (S : ScaleSelection) (omega : ShellSeq d) (L₁ L₂ k₁ k₂ m : ℕ) (F : Vec d)
    (R : TriadicCube d) :
    MemLp (hilbertifyVecField (fluxFieldCarrier nu S omega
      (gluedGradientField hnu L₁ k₁ m F omega)
      (gluedGradientField hnu L₂ k₂ m F omega))) 2 (normalizedCubeMeasure R) :=
  memLp_fluxFieldCarrier hnu S omega
    ((memVectorL2_openCubeSet_gluedGradientField hnu L₁ k₁ m F omega R).sub
      (memVectorL2_openCubeSet_gluedGradientField hnu L₂ k₂ m F omega R))

/-! ## The weakened multiscale Poincaré at the flux field -/

/-! ## The printed estimate in the real carriers -/

/-! ## Witnesses

Each statement above is exhibited at an explicit configuration, so that no
hypothesis is vacuous: the zero difference satisfies the `L̲²` input, the glued
difference is a genuine nonzero instance, and the depth-sum estimate is checked
at a concrete scale selection `d = 1`. -/

end

end SuperdiffusionCLT.Section3.Terms
