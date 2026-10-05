/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm2AnchorsConstFirst
public import SuperdiffusionCLT.Section3.Setup.DirichletResponse
public import SuperdiffusionCLT.Section3.HighContrast.BEllIndependence

/-!
# The measurability sentence of `l.RHS.term2`, and the half of it that is proved

The following sentence occurs in the proof of `l.RHS.term2`:

> Let `F_> := σ(j_r : r > ℓ)`.  The field `R` is `F_>`-measurable, while
> `∇ũ_n` is measurable with respect to `σ(j_r : r ≤ ℓ)`.

`l_RHS_term2_of_anchors_constFirst` of `RHSTerm2AnchorsConstFirst.lean` carries
that sentence as its last two binders, read on the two cube mean vectors:
`hRmeas` for `R` against `highShellSigma d S.ell`, `hTmeas` for the proxy
`∇ũ_n` against `lowShellSigma d S.ell`.

## The proxy half is proved

`gluedGradientField hnu ell n m F` is the print's `∇ũ_n`, and its cube mean on
a sub-cube `z` of the family is not the mean of a choice-built object at all:
`volumeAverageVec_gluedGradientField` of `GluedField.lean` evaluates it as

`(∇ũ_n)_{z+cu_n} = s_{ℓ,*}^{-1}(z + cu_n) F`,

the quenched coarse matrix of the cutoff field `a_ℓ = ν Id + k_ℓ` on that
cube applied to the flux slot.  The maximizer and its `Classical.choice` have
disappeared from the observable.  What is left is a measurable function of
`a_ℓ`: the coarse matrices of an admissible source are measurable for *any*
`σ`-field on the sample carrier (`measurable_sigmaStarInvCoarse_apply` of
`Section2/Annealed/Measurability.lean`, stated for an arbitrary
`MeasurableSpace Omega`), the cutoff field is admissible at every sample
(`aeLocallyUniformlyEllipticField_coefficientCutoff`), and `a_ℓ` reads only the
shells `r ≤ ℓ` (`measurable_coefficientCutoff_indexSigma` of
`Section3/HighContrast/BEllIndependence.lean`, at the index set `Set.Iic ell`,
which is `lowShellSigma d ell`).  Composing the three gives `hTmeas`.

## The field half is not

For `R = (k_{L'} − k_ℓ)^t ∇w` only the coefficient factor is available: the
increment `k_{L'} − k_ℓ` is the finite shell sum over `(ℓ, L']`, hence
`F_>`-measurable.  The
response factor `∇w` is not: `w` is a free binder of the rendered statement,
given only by `IsDirichletResponse`, and the Dirichlet response
`dirichletResponse` of `Section3/Setup/DirichletResponse.lean` is produced by
`Classical.choose`.  The cube mean of `R` *is* a well-defined function of the
sample, by the a.e. uniqueness of the response gradient, so `hRmeas` is a definite
property of the shell sequence and not an artefact of the free binder — but no
declaration here makes that function measurable, and nothing in the
definitions records how the solution of the Dirichlet problem depends on the
sample.  `hRmeas` therefore stays a hypothesis.

## Main results

* `measurable_coefficientCutoff_lowShellSigma`,
  `measurable_sigmaStarInvCoarse_coefficientCutoff_lowShellSigma`: `a_ℓ` and
  the coarse matrix `s_{ℓ,*}^{-1}` read only the shells `r ≤ ℓ`.
* `measurable_volumeAverageVec_gluedGradientField_lowShellSigma`: **`hTmeas`**,
  the proxy half of the sentence.
* `coefficientCutoff_toCoeffField_sub_eq_finiteShellIncrement`: the coefficient
  factor of `R` is the finite shell increment, which reads only the shells `r > ℓ`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open ProbabilityTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.HighContrast
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Probability
open Homogenization

noncomputable section

variable {d : ℕ}

/-! ## The two `σ`-fields of the sentence as index `σ`-fields -/

/-! ## The proxy half: `hTmeas` -/

/-- The cutoff coefficient field `a_ℓ = ν Id + k_ℓ` reads only the shells
`r ≤ ℓ`, i.e. it is measurable for `σ(j_r : r ≤ ℓ)`. -/
theorem measurable_coefficientCutoff_lowShellSigma (nu : ℝ) (ell : ℕ) :
    Measurable[lowShellSigma d ell]
      (fun omega : ShellSeq d ↦ coefficientCutoff nu omega ell) :=
  measurable_coefficientCutoff_indexSigma nu ell

/-- The quenched coarse matrix `s_{ℓ,*}^{-1}(Q)` of the cutoff field reads only
the shells `r ≤ ℓ`.  The cutoff field is admissible at every sample, so no
event is excluded. -/
theorem measurable_sigmaStarInvCoarse_coefficientCutoff_lowShellSigma [NeZero d]
    {nu : ℝ} (hnu : 0 < nu) (ell : ℕ) (Q : TriadicCube d) (i j : Fin d) :
    Measurable[lowShellSigma d ell]
      (fun omega : ShellSeq d ↦
        sigmaStarInvCoarse (openCubeSet Q)
          (coefficientCutoff nu omega ell).toCoeffField i j) :=
  @measurable_sigmaStarInvCoarse_apply d _ (ShellSeq d) (lowShellSigma d ell)
    (fun omega ↦ coefficientCutoff nu omega ell)
    (measurable_coefficientCutoff_lowShellSigma nu ell)
    (fun omega ↦ aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega ell) Q i j

/-- A matrix-valued map with measurable entries gives a measurable vector-valued
map after multiplication by a fixed vector. -/
private theorem measurable_matVecMul_of_entries {Omega : Type*} [MeasurableSpace Omega]
    {M : Omega → Mat d} (hM : ∀ i j, Measurable fun omega ↦ M omega i j) (F : Vec d) :
    Measurable fun omega ↦ matVecMul (M omega) F := by
  refine Measurable.of_eval fun i ↦ ?_
  exact Finset.measurable_sum _ fun j _ ↦ (hM i j).mul_const (F j)

/-- **The proxy half of the measurability sentence**: on
every scale-`n` sub-cube of `cu_m` the cube mean of the glued field
`∇ũ_n = ∇u_n` at cutoff level `ℓ` is measurable for `σ(j_r : r ≤ ℓ)`.

The mean is the quenched coarse matrix of `a_ℓ` on that cube applied to the
flux slot (`volumeAverageVec_gluedGradientField`), so the cube-wise maximizers
and the choice inside them are absent from the observable. -/
theorem measurable_volumeAverageVec_gluedGradientField_lowShellSigma [NeZero d]
    {nu : ℝ} (hnu : 0 < nu) (ell n m : ℕ) (F : Vec d) :
    ∀ z ∈ largeCubeSubcubes d n m,
      Measurable[lowShellSigma d ell]
        (fun omega : ShellSeq d ↦
          volumeAverageVec (openCubeSet z)
            (gluedGradientField hnu ell n m F omega)) := by
  intro z hz
  have hEq : (fun omega : ShellSeq d ↦
      volumeAverageVec (openCubeSet z) (gluedGradientField hnu ell n m F omega)) =
      fun omega : ShellSeq d ↦
        matVecMul (sigmaStarInvCoarse (openCubeSet z)
          (coefficientCutoff nu omega ell).toCoeffField) F := by
    funext omega
    exact volumeAverageVec_gluedGradientField hnu ell n m F omega hz
  rw [hEq]
  exact @measurable_matVecMul_of_entries d (ShellSeq d) (lowShellSigma d ell) _
    (fun i j ↦ measurable_sigmaStarInvCoarse_coefficientCutoff_lowShellSigma hnu ell z i j) F

/-! ## The field half: what `R` does record -/

/-- The coefficient factor of `R` is the finite shell increment: the constant
`ν Id` cancels, so `a_{L'} − a_ℓ = k_{L'} − k_ℓ` is the shell sum over
`(ℓ, L']`. -/
theorem coefficientCutoff_toCoeffField_sub_eq_finiteShellIncrement (nu : ℝ)
    (omega : ShellSeq d) {ell L : ℕ} (hlL : ell ≤ L) (x : Vec d) :
    (coefficientCutoff nu omega L).toCoeffField x -
        (coefficientCutoff nu omega ell).toCoeffField x =
      finiteShellIncrement omega ell L x := by
  rw [coefficientCutoff_toCoeffField_apply, coefficientCutoff_toCoeffField_apply,
    finiteShellIncrement_apply_eq_streamCutoff_sub omega hlL x]
  abel

end

end SuperdiffusionCLT.Section3.Terms
