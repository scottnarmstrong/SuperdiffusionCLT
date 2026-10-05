/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Sobolev.DirichletW2pDivergence
public import Homogenization.Sobolev.Fractional.ContinuousKFunctional

/-!
# The `K`-lane packaging of a weak Hessian

In Step 2 of the proof of
`l.abstract.response.fields` the fractional estimate
`e.abstract.response.Hhalf` is obtained "by interpolating the corresponding
`L²` and `H¹` estimates". The differentiated endpoint of that interpolation is
`e.abstract.response.W28` at `p = 2` on the unit centered cube: the Dirichlet
response `w` of an `H¹` flux has `∇w ∈ H¹`, with
`‖∇²w‖_{L̲²(cu_0)} ≤ B ‖∇F‖_{L̲²(cu_0)}`.

CoarseGraining's `K`-functional lane measures the `H̲¹` endpoint through
`ContinuousKCompetitor d`, a `d`-tuple of honest `H1Function`s on the open unit
centered cube, and `continuousKGradientNorm`. The
`Sobolev.exists_cubeDirichletResponseHessianLpEstimate` produces instead a
`HasWeakHessianOn` witness together with an `L̲^p` bound on it. This module is
the translation between the two carriers.

## The packaging

`HasWeakHessianOn U u` carries, for each pair `(i, j)`, a function `hess i j`
which is in `L²(U)` and is the weak `j`-th partial derivative of `x ↦ u.grad x i`
(`HasWeakPartialDerivOn`). The five fields of `H1Function U` for the scalar
`∂_i w` are therefore already present:

* the function `x ↦ w.grad x i` is `H1Function.gradMemL2 i`;
* its candidate gradient `x ↦ fun j => H.hess i j x` is `L²` by
  `HasWeakHessianOn.hess_memL2 i j`;
* the integration-by-parts identity is `HasWeakHessianOn.weak_second i j`,
  which is literally `HasWeakGradientOn` for that pair once `j` is abstracted.

So `weakHessianCompetitor H` is a `ContinuousKCompetitor` whose field is `∇w`
*on the nose*, not merely almost everywhere, and whose competitor gradient
matrix is the weak Hessian. No hypothesis beyond the witness is needed.

## The two norms

`continuousKGradientNorm G` is the real normalized `L²` size of the Frobenius
magnitude of `G.gradient`, taken against `(unitCenteredCubeDomain d).normalizedVolume`;
the local `Section2.Norms.cubeLpENorm (originCube d 0) 2` of the same matrix
field read in `HilbertMat d` is its `ℝ≥0∞` form. The two measures are equal
(`cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure`) and
the two magnitudes are equal
(`matrixFrobeniusMagnitude_eq_norm_hilbertMat_ofMat`), so the identification is
exact.

## Main results

* `weakHessianCompetitor`, `weakHessianCompetitor_toField`,
  `weakHessianCompetitor_gradient`: the packaging.
* `continuousKGradientNorm_eq_toReal_cubeLpENorm`: the two gradient sizes.
* `memLp_competitorField`, `hasWeakJacobianOn_competitor`,
  `memLp_competitorGradientHilbertMat`: the
  `L̲²` data an `H¹` competitor supplies to the `W^{2,2}` endpoint.
-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Section3
namespace ResponseFields

open Homogenization
open MeasureTheory
open Section2.Norms
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## A weak Hessian read as a `K`-lane competitor -/

/-- **The weak Hessian of a zero-trace `H¹` function, packaged as an `H¹`
competitor for its gradient.** The `i`-th coordinate is the scalar `∂_i w`, an
honest `H1Function` on the open unit centered cube: it is square integrable
because `w` is `H¹`, its candidate gradient `j ↦ ∂_j ∂_i w` is square
integrable by `HasWeakHessianOn.hess_memL2`, and the integration-by-parts
identity is `HasWeakHessianOn.weak_second`. -/
def weakHessianCompetitor {w : H1Function (openCubeSet (originCube d 0))}
    (H : HasWeakHessianOn (openCubeSet (originCube d 0)) w) :
    ContinuousKCompetitor d where
  coord i :=
    { toFun := fun x => w.grad x i
      grad := fun x j => H.hess i j x
      memL2 := w.gradMemL2 i
      gradMemL2 := fun j => H.hess_memL2 i j
      hasWeakGradient := fun j => H.weak_second i j }

@[simp] theorem weakHessianCompetitor_toField
    {w : H1Function (openCubeSet (originCube d 0))}
    (H : HasWeakHessianOn (openCubeSet (originCube d 0)) w) :
    (weakHessianCompetitor H).toField = w.grad := rfl

@[simp] theorem weakHessianCompetitor_gradient
    {w : H1Function (openCubeSet (originCube d 0))}
    (H : HasWeakHessianOn (openCubeSet (originCube d 0)) w) (x : Vec d) :
    (weakHessianCompetitor H).gradient x = fun i j => H.hess i j x := rfl

/-! ## The gradient size of a competitor as a normalized cube norm -/

/-- **The `K`-lane gradient size is the normalized cube `L̲²` norm of the
competitor gradient matrix.** The `K`-functional measures the Frobenius
magnitude against `(unitCenteredCubeDomain d).normalizedVolume`; that measure is
`normalizedCubeMeasure (originCube d 0)` and that magnitude is the norm of the
`HilbertMat` realization. -/
theorem continuousKGradientNorm_eq_toReal_cubeLpENorm (G : ContinuousKCompetitor d) :
    continuousKGradientNorm G =
      (cubeLpENorm (originCube d 0) 2
        (fun x => HilbertMat.ofMat (G.gradient x))).toReal := by
  have h : (unitCenteredCubeDomain d).normalizedLpENorm 2
      (fun x => matrixFrobeniusMagnitude (G.gradient x)) =
      cubeLpENorm (originCube d 0) 2 (fun x => HilbertMat.ofMat (G.gradient x)) := by
    rw [BoundedMeasurableDomain.normalizedLpENorm, cubeLpENorm, unitCenteredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
      show (fun x => matrixFrobeniusMagnitude (G.gradient x)) =
          (fun x => ‖HilbertMat.ofMat (G.gradient x)‖) from
        funext fun x => matrixFrobeniusMagnitude_eq_norm_hilbertMat_ofMat _]
    refine eLpNorm_norm _ ?_
    refine MeasureTheory.MemLp.aestronglyMeasurable (p := 2) ?_
    rw [memLp_piLp_iff]
    intro i
    rw [memLp_piLp_iff]
    intro j
    simpa only [ContinuousKCompetitor.gradient_apply] using
      (G.coord i).grad_memL2_normalizedCubeMeasure j
  exact congrArg ENNReal.toReal h

/-! ## The `L̲²` data carried by an `H¹` competitor -/

/-- The field of an `H¹` competitor is square integrable on the unit centered
cube, coordinate by coordinate. -/
theorem memLp_competitorField (G : ContinuousKCompetitor d) :
    MemLp G.toField 2 (normalizedCubeMeasure (originCube d 0)) := by
  refine MemLp.of_eval (fun i => ?_)
  simpa only [ContinuousKCompetitor.toField_apply] using
    (G.coord i).memL2_normalizedCubeMeasure

/-- The coordinate weak gradients of an `H¹` competitor are a weak Jacobian of
its field. -/
theorem hasWeakJacobianOn_competitor (G : ContinuousKCompetitor d) :
    Sobolev.HasWeakJacobianOn (openCubeSet (originCube d 0)) G.toField
      (fun i => (G.coord i).grad) :=
  fun i => (G.coord i).hasWeakGradient

/-- The competitor gradient matrix is square integrable on the unit centered
cube, entry by entry. -/
theorem memLp_competitorGradientHilbertMat (G : ContinuousKCompetitor d) :
    MemLp (fun x => HilbertMat.ofMat (G.gradient x)) 2
      (normalizedCubeMeasure (originCube d 0)) := by
  rw [memLp_piLp_iff]
  intro i
  rw [memLp_piLp_iff]
  intro j
  simpa only [ContinuousKCompetitor.gradient_apply] using
    (G.coord i).grad_memL2_normalizedCubeMeasure j

end

end ResponseFields
end Section3
end SuperdiffusionCLT
