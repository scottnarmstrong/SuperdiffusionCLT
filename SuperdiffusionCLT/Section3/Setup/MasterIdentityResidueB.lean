/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.ResponseMeasurabilityC
public import SuperdiffusionCLT.Section3.Setup.ResponseMeasurabilityD
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2Measurability
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1Inputs
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1InputsF
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1InputsG
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1AnchorsConstFirst
public import SuperdiffusionCLT.Section3.Terms.MaximizerCoefficientStabilityB
public import SuperdiffusionCLT.Section3.ResponseFields.RegboundsWindowB
public import SuperdiffusionCLT.Section3.ResponseFields.LpEstimates
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementLinftyLargeCube
public import SuperdiffusionCLT.Section2.Estimates.Stream.ShellHminusEndpointOrderOneC
public import SuperdiffusionCLT.Section2.Norms.NegativeNormPairing

/-!
# The three mixed-scale `hData` binders `hI1`, `hI2`, `hI3`

The three annealed integrability binders of the master identity that pair the
response gradient `∇w` against a *mixed-scale* field — the level-`ℓ` cutoff
coefficient against the glued field of level `L'` (`hI1`), the cutoff increment
`a_{L'} − a_ℓ` against the glued field shifted by `p` (`hI2`), and the level-`L'`
cutoff coefficient against the glued maximizer gradient difference (`hI3`) — are
the binders no term bound produces.  This module proves them.

Two half-obligations are involved in each.

* *Measurability in the sample.*  The integrand is a **signed** cube average of
  `∇w` against a field that is **not** the coefficient flux of the response, so
  the available carriers (which produce cube *norms* of `A∇w`) do not apply.
  The engine is `aemeasurable_volumeAverage_vecDot_grad_of_class`: the signed
  cube average of the response gradient against any field whose `L²(cu_m)`
  class is measurable in the sample is measurable.  Choice independence
  (`volumeAverage_comp_grad_response_funext`) moves the average to the canonical
  response, where it is the inner product of two measurable class functions.
  The class measurability of each second slot is then
  `measurable_matFieldMulClass_family` fed by the class measurability of
  the glued field (`measurable_gluedGradientClass`) and of the cube maximizer
  gradient (`measurable_cubeMaximizerGradientClass`).

* *Finiteness.*  Cauchy–Schwarz on the cube bounds the signed average by the
  product of the cube norms of the first and second slots; the extended integral
  of a product of nonnegative observables is bounded by the sum of their
  squares.  The first factor is the response's own second moment
  (`gradW_l2_second_moment_explicit`, through the `W^{8,2}` response
  estimate).  The second factor is a coefficient envelope times a *uniformly*
  bounded glued field: the glued field is bounded by `nu⁻¹ |F|` on every cube
  (`vecCubeLpENorm_two_sq_gluedGradientField_le`), the level-`ℓ` envelope by the
  second moment of the cutoff coefficient
  (`second_moment_coeffLinftySupBound_le`), and the increment envelope
  `(ℓ, L']` by the `Γ₂` tail of `e.kmn.Linfty`
  (`isBigOWith_gammaSigma_largeCubeIncrementSupBound`, read on the large cube
  `cu_{L'}`), which needs no relation between the level `L'` and the cube scale
  `m`.

## Main results

* `aemeasurable_volumeAverage_vecDot_grad_of_class`
* `master_residue_hI1`, `master_residue_hI2`, `master_residue_hI3`
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Setup

open MeasureTheory ProbabilityTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Probability.Stationary
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Terms
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The measurability engine -/

/-- The cube average of a pairing is the rescaled inner product of the two
`L²(U)` classes. -/
private theorem master_residue_volumeAverage_vecDot_eq_inner {U : Set (Vec d)}
    {f g : Vec d → Vec d} (hf : MemVectorL2 U f) (hg : MemVectorL2 U g) :
    volumeAverage U (fun x => vecDot (f x) (g x)) =
      (MeasureTheory.volume U).toReal⁻¹ *
        inner ℝ (toHilbertVectorL2OfVecField hf) (toHilbertVectorL2OfVecField hg) := by
  rw [inner_toHilbertVectorL2OfVecField_eq_integral, volumeAverage]

/-- **The signed cube average of the response gradient against a field whose
`L²(cu_m)` class is measurable in the sample is measurable in the sample.**

The average is moved to the canonical Dirichlet response by choice independence
(`volumeAverage_comp_grad_response_funext`), where it is a constant multiple of
the inner product of the two class functions — the gradient class of the
canonical response (`measurable_gradToHilbertVectorL2_dirichletResponse`) and
the class of the second slot. -/
theorem aemeasurable_volumeAverage_vecDot_grad_of_class [NeZero d]
    {LPrime ellPrime m : ℕ} {p : Vec d} {mu : MeasureTheory.Measure (ShellSeq d)}
    {w : ShellSeq d → H10Function (openCubeSet (originCube d (m : ℤ)))}
    (hw : ∀ omega : ShellSeq d, IsDirichletResponse omega LPrime ellPrime m p (w omega))
    {Vfield : ShellSeq d → Vec d → Vec d}
    (hVmem : ∀ omega : ShellSeq d,
      MemVectorL2 (openCubeSet (originCube d (m : ℤ))) (Vfield omega))
    (hVclass : AEMeasurable (fun omega : ShellSeq d =>
      toHilbertVectorL2OfVecField (hVmem omega)) mu) :
    AEMeasurable (fun omega : ShellSeq d =>
      volumeAverage (openCubeSet (originCube d (m : ℤ)))
        (fun x => vecDot ((w omega).toH1Function.grad x) (Vfield omega x))) mu := by
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  have hvU : openCubeSet (originCube d (m : ℤ)) ⊆
      openCubeSet (originCube d (m : ℤ)) := Set.Subset.rfl
  rw [volumeAverage_comp_grad_response_funext hvU
    (fun omega x v => vecDot v (Vfield omega x)) hw]
  have hg : ∀ omega : ShellSeq d, MemVectorL2 (openCubeSet (originCube d (m : ℤ)))
      (dirichletResponse omega LPrime ellPrime m p).toH1Function.grad :=
    fun omega => (dirichletResponse omega LPrime ellPrime m p).toH1Function.grad_memVectorL2
  have hfun : (fun omega : ShellSeq d =>
      volumeAverage (openCubeSet (originCube d (m : ℤ)))
        (fun x => vecDot ((dirichletResponse omega LPrime ellPrime m p).toH1Function.grad x)
          (Vfield omega x))) =
      fun omega : ShellSeq d =>
        (MeasureTheory.volume (openCubeSet (originCube d (m : ℤ)))).toReal⁻¹ *
          inner ℝ (toHilbertVectorL2OfVecField (hg omega))
            (toHilbertVectorL2OfVecField (hVmem omega)) := by
    funext omega
    exact master_residue_volumeAverage_vecDot_eq_inner (hg omega) (hVmem omega)
  rw [hfun]
  have hinner : AEMeasurable (fun omega : ShellSeq d =>
      inner ℝ (toHilbertVectorL2OfVecField (hg omega))
        (toHilbertVectorL2OfVecField (hVmem omega))) mu :=
    continuous_inner.measurable.comp_aemeasurable
      ((measurable_gradToHilbertVectorL2_dirichletResponse
        (LPrime := LPrime) (ellPrime := ellPrime) (m := m) (p := p)).aemeasurable.prodMk hVclass)
  exact (hinner.const_mul _)

end

end SuperdiffusionCLT.Section3.Setup
