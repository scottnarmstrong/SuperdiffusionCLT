/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Norms.NegativeNormPairing
public import SuperdiffusionCLT.Section3.ResponseFields.AprioriAssemblyB
public import SuperdiffusionCLT.Section3.ResponseFields.HhalfDilationB
public import SuperdiffusionCLT.Section3.ResponseFields.JunkBranch

/-!
# The junk branches of the a priori response clauses

`SuperdiffusionCLT/Section3/ResponseFields/AprioriAssembly.lean` and the
modules above it assemble `responseFields_apriori_orderZero` from four clauses, each of
which carries one explicit hypothesis covering the branch of the statement
on which the flux field is not measurable on the cube. This file
discharges three of those four hypotheses from
`Section3/ResponseFields/JunkBranch.lean`.

## What is proved here

* `junkL8_bridge`: the junk branch of `e.abstract.response.L8`. Both response
  gradients vanish almost everywhere, so the left-hand side is `0`.
* `junkHalf_bridge`: the junk branch of `e.abstract.response.Hhalf`, in the
  unconditional shape `HhalfDilationB.lean` asks for.
* `junkND_bridge`: the junk branch of `e.abstract.response.ND.weak`. On the
  guard `‖F₀‖_{L̲⁴(cu_M)} < ⊤` the centred flux is not measurable and both
  gradients vanish; on the guard `‖F₀‖_{Ĥ̲^{-1}(cu_M)} = 0` no measurability is
  available, and the estimate comes instead from the duality bound
  `vecCubeLpENorm_grad_sub_le_vecHatNegENorm` together with
  `vecHatNegENorm_le_add_const`, which pays for the centring with exactly the
  printed constant term `C |(F)_{cu_M}|`.

## The weak Hessian

`hess_ae_eq_zero_of_grad_ae_eq_zero` is the a.e. congruence the Hessian clause
needs: on the junk branch of the Dirichlet equation the gradient vanishes
almost everywhere, hence so does every weak Hessian witness of it, by the a.e.
uniqueness of weak partial derivatives. The junk hypothesis of the Hessian clause is
nevertheless *not* discharged here: its case split covers, beyond that branch, two cases in
which the flux itself is measurable, and neither is a junk branch. The repaired case split is
in `AprioriAssemblyE.lean`.
-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Section3
namespace ResponseFields

open Homogenization
open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The weak Hessian of a gradient that vanishes almost everywhere -/

/-- An `L²` function on an open cube is locally integrable there. -/
private theorem locallyIntegrableOn_of_memScalarL2 {Q : TriadicCube d}
    {f : Vec d → ℝ} (hf : MemScalarL2 (openCubeSet Q) f) :
    LocallyIntegrableOn f (openCubeSet Q) volume := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    instIsFiniteMeasureVolumeMeasureOnOpenCubeSet Q
  exact IntegrableOn.locallyIntegrableOn
    (show IntegrableOn f (openCubeSet Q) volume from hf.integrable (by norm_num))

/-- **A weak Hessian of an `H¹` function with an almost everywhere vanishing
gradient vanishes almost everywhere.** The zero field is a weak second
derivative of the zero gradient, and weak partial derivatives are unique almost
everywhere on an open set. -/
theorem hess_ae_eq_zero_of_grad_ae_eq_zero {Q : TriadicCube d}
    {u : H1Function (openCubeSet Q)} (H : HasWeakHessianOn (openCubeSet Q) u)
    (hu : ∀ᵐ x ∂(volume.restrict (openCubeSet Q)), u.grad x = 0) (i j : Fin d) :
    H.hess i j =ᵐ[volume.restrict (openCubeSet Q)] 0 := by
  have hzero : HasWeakPartialDerivOn (openCubeSet Q) j (fun x => u.grad x i)
      (fun _ => (0 : ℝ)) := by
    intro φ _hφ _hφc _hφs
    have hlhs : ∫ x in openCubeSet Q, u.grad x i * (fderiv ℝ φ x) (basisVec j) = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hu] with x hx
      rw [hx]
      simp
    rw [hlhs]
    simp
  exact HasWeakPartialDerivOn.ae_eq (isOpen_openCubeSet Q)
    (locallyIntegrableOn_of_memScalarL2 (H.hess_memL2 i j))
    (locallyIntegrableOn_of_memScalarL2
      (MeasureTheory.memLp_const (μ := volumeMeasureOn (openCubeSet Q)) (c := (0 : ℝ))))
    (H.weak_second i j) hzero

/-! ## Centring the hatted negative norm -/

/-- **The hatted negative norm is subadditive against a constant field.** The
pairing density of a constant field with a test field is continuous, hence
integrable on the cube, so either both pairings are honest integrals and the
average splits, or neither is and the pairing of `F` is Bochner's `0`. -/
theorem vecHatNegENorm_le_add_const {Q : TriadicCube d} (F : Vec d → Vec d) (c : Vec d) :
    vecHatNegENorm Q F ≤
      vecHatNegENorm Q (fun x => F x - c) + vecHatNegENorm Q (fun _ => c) := by
  refine vecHatNegENorm_le fun g hg => ?_
  have hdens : ∀ x : Vec d, vecGradientPairingDensity F g x
      = vecGradientPairingDensity (fun y => F y - c) g x
        + vecGradientPairingDensity (fun _ => c) g x := by
    intro x
    show (fderiv ℝ g x) (F x) = (fderiv ℝ g x) (F x - c) + (fderiv ℝ g x) c
    rw [← map_add]
    congr 1
    abel
  have hcint : IntegrableOn (vecGradientPairingDensity (fun _ => c) g) (cubeSet Q) volume :=
    vecGradientPairingDensity_integrableOn continuous_const hg.contDiff Q
  by_cases h0 : IntegrableOn (vecGradientPairingDensity (fun y => F y - c) g) (cubeSet Q) volume
  · have hsplit : volumeAverage (cubeSet Q) (vecGradientPairingDensity F g)
        = volumeAverage (cubeSet Q) (vecGradientPairingDensity (fun y => F y - c) g)
          + volumeAverage (cubeSet Q) (vecGradientPairingDensity (fun _ => c) g) := by
      simp only [volumeAverage]
      rw [setIntegral_congr_fun (measurableSet_cubeSet Q) (fun x _ => hdens x),
        integral_add h0 hcint, mul_add]
    rw [hsplit]
    exact le_trans ENNReal.ofReal_add_le
      (add_le_add (le_vecHatNegENorm _ hg) (le_vecHatNegENorm _ hg))
  · have hFnot : ¬ IntegrableOn (vecGradientPairingDensity F g) (cubeSet Q) volume := by
      intro hc
      refine h0 ?_
      have heq : vecGradientPairingDensity (fun y => F y - c) g
          = fun x => vecGradientPairingDensity F g x
              - vecGradientPairingDensity (fun _ => c) g x := by
        funext x
        rw [hdens x]
        ring
      rw [heq]
      exact hc.sub hcint
    have hzero : volumeAverage (cubeSet Q) (vecGradientPairingDensity F g) = 0 := by
      simp only [volumeAverage]
      rw [integral_undef hFnot, mul_zero]
    rw [hzero, ENNReal.ofReal_zero]
    exact zero_le

/-- The hatted negative norm of a constant field is at most the Euclidean
magnitude of the constant. -/
theorem vecHatNegENorm_const_le {Q : TriadicCube d} (c : Vec d) :
    vecHatNegENorm Q (fun _ => c) ≤ ‖HilbertVec.ofVec c‖ₑ := by
  have hmem : MemLp (hilbertifyVecField (fun _ : Vec d => c)) 2 (normalizedCubeMeasure Q) := by
    have := isProbabilityMeasure_normalizedCubeMeasure Q
    exact memLp_const _
  refine le_trans (Section2.Norms.vecHatNegENorm_le_vecCubeLpENorm hmem) ?_
  exact le_of_eq (vecCubeLpENorm_const Q (by norm_num) c)

/-! ## The junk branch of `e.abstract.response.L8` -/

/-- **The junk branch of the first conjunct of `responseFields_apriori_orderZero`**, in
the exact shape of the hypothesis `hjunk` of
`exists_responseGradientL8Clause`: a flux of finite `L̲⁸(cu_M)` size which
is not an `L̲⁸(cu_M)` field is not measurable on the cube, so both response
gradients vanish almost everywhere and the left-hand side is `0`. -/
theorem junkL8_bridge (M : ℕ) (F : Vec d → Vec d)
    (wD : H10Function (openCubeSet (originCube d (M : ℤ))))
    (wN : H1MeanZeroFunction (openCubeSet (originCube d (M : ℤ))))
    (hD : IsCubeDirichletResponse (originCube d (M : ℤ)) F wD)
    (hN : IsCubeNeumannResponse (originCube d (M : ℤ)) F wN)
    (hfin : vecCubeLpENorm (originCube d (M : ℤ)) 8 F < ⊤)
    (hmem : ¬ MemLp (hilbertifyVecField F) 8
      (normalizedCubeMeasure (originCube d (M : ℤ)))) :
    vecCubeLpENorm (originCube d (M : ℤ)) 8 wD.toH1Function.grad +
        vecCubeLpENorm (originCube d (M : ℤ)) 8 wN.toH1Function.grad ≤
      vecCubeLpENorm (originCube d (M : ℤ)) 8 F := by
  have hF := not_aestronglyMeasurable_of_not_memLp hfin hmem
  rw [vecCubeLpENorm_grad_eq_zero_of_isCubeDirichletResponse hF hD,
    vecCubeLpENorm_grad_eq_zero_of_isCubeNeumannResponse hF hN, add_zero]
  exact zero_le

/-! ## The junk branch of `e.abstract.response.ND.weak` -/

/-- **The junk branch of the fourth conjunct of `responseFields_apriori_orderZero`**, in
the exact shape of the hypothesis `hjunk` of
`exists_responseDifferenceL2Clause`.

On the first guard the centred flux has finite `L̲⁴(cu_M)` size, so failing to
be an `L̲⁴(cu_M)` field means it is not measurable on the cube; the flux itself
is then not measurable either, both response gradients vanish almost everywhere
and the left-hand side is `0`. On the second guard nothing is measurable, but
the right-hand side keeps its constant term: the duality bound gives
`‖∇w_N − ∇w_D‖_{L̲²} ≤ ‖F‖_{Ĥ̲^{-1}}`, and centring costs exactly
`|(F)_{cu_M}|`. -/
theorem junkND_bridge (M : ℕ) (F : Vec d → Vec d)
    (wD : H10Function (openCubeSet (originCube d (M : ℤ))))
    (wN : H1MeanZeroFunction (openCubeSet (originCube d (M : ℤ))))
    (hD : IsCubeDirichletResponse (originCube d (M : ℤ)) F wD)
    (hN : IsCubeNeumannResponse (originCube d (M : ℤ)) F wN)
    (hmem : ¬ MemLp (hilbertifyVecField (fun x => F x -
          volumeAverageVec (cubeSet (originCube d (M : ℤ))) F)) 4
        (normalizedCubeMeasure (originCube d (M : ℤ))))
    (hguard : vecCubeLpENorm (originCube d (M : ℤ)) 4
          (fun x => F x -
            volumeAverageVec (cubeSet (originCube d (M : ℤ))) F) < ⊤ ∨
        vecHatNegENorm (originCube d (M : ℤ))
          (fun x => F x -
            volumeAverageVec (cubeSet (originCube d (M : ℤ))) F) = 0) :
    vecCubeLpENorm (originCube d (M : ℤ)) 2
        (fun x => wN.toH1Function.grad x - wD.toH1Function.grad x) ≤
      (vecHatNegENorm (originCube d (M : ℤ))
            (fun x => F x -
              volumeAverageVec (cubeSet (originCube d (M : ℤ))) F)) ^ ((1 : ℝ) / 5) *
          (vecCubeLpENorm (originCube d (M : ℤ)) 4
            (fun x => F x -
              volumeAverageVec (cubeSet (originCube d (M : ℤ))) F)) ^ ((4 : ℝ) / 5) +
        ‖HilbertVec.ofVec (volumeAverageVec (cubeSet (originCube d (M : ℤ))) F)‖ₑ := by
  rcases hguard with hfin | hhat
  · have hF₀ := not_aestronglyMeasurable_of_not_memLp hfin hmem
    have hF : ¬ AEStronglyMeasurable F
        (volume.restrict (openCubeSet (originCube d (M : ℤ)))) := fun h =>
      hF₀ (h.sub aestronglyMeasurable_const)
    have hzero : vecCubeLpENorm (originCube d (M : ℤ)) 2
        (fun x => wN.toH1Function.grad x - wD.toH1Function.grad x) = 0 := by
      refine vecCubeLpENorm_eq_zero_of_ae_eq_zero ?_
      filter_upwards [grad_ae_eq_zero_of_isCubeDirichletResponse hF hD,
        grad_ae_eq_zero_of_isCubeNeumannResponse hF hN] with x hxD hxN
      simp [hxD, hxN]
    rw [hzero]
    exact zero_le
  · have hbound : vecHatNegENorm (originCube d (M : ℤ)) F ≤
        ‖HilbertVec.ofVec (volumeAverageVec (cubeSet (originCube d (M : ℤ))) F)‖ₑ := by
      refine le_trans (vecHatNegENorm_le_add_const F
        (volumeAverageVec (cubeSet (originCube d (M : ℤ))) F)) ?_
      rw [hhat, zero_add]
      exact vecHatNegENorm_const_le _
    rw [hhat, ENNReal.zero_rpow_of_pos (by norm_num), zero_mul, zero_add]
    exact le_trans (vecCubeLpENorm_grad_sub_le_vecHatNegENorm hN hD) hbound

/-! ## The junk branch of `e.abstract.response.Hhalf` -/

/-- **The junk branch of the third conjunct of `responseFields_apriori_orderZero`**, in
the exact shape of the hypothesis `hjunk` of
`dirichlet_hhalf_bridge`: on the branch where the flux is not
measurable against the normalized cube measure, the Dirichlet response gradient
vanishes almost everywhere on the open cube, so the `H̲^{1/2}` clause holds with
any constant. The guard `‖F‖_{H̲^{1/2}(cu_M)} < ⊤` is not used: the implication
holds unconditionally. -/
theorem junkHalf_bridge (M : ℕ) (F : Vec d → Vec d)
    (wD : H10Function (openCubeSet (originCube d (M : ℤ))))
    (hD : IsCubeDirichletResponse (originCube d (M : ℤ)) F wD)
    (hF : ¬ AEStronglyMeasurable (hilbertifyVecField F)
      (normalizedCubeMeasure (originCube d (M : ℤ)))) :
    wD.toH1Function.grad =ᵐ[volume.restrict (openCubeSet (originCube d (M : ℤ)))]
      0 := by
  have hF' : ¬ AEStronglyMeasurable F
      (volume.restrict (openCubeSet (originCube d (M : ℤ)))) := fun h =>
    hF (aestronglyMeasurable_hilbertifyVecField_normalizedCubeMeasure h)
  filter_upwards [grad_ae_eq_zero_of_isCubeDirichletResponse hF' hD] with x hx
  exact hx

/-! ## The a priori anchor with all three junk binders removed -/

end

end ResponseFields
end Section3
end SuperdiffusionCLT
