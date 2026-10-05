/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.ResponseFields.HhalfEndpoint
public import SuperdiffusionCLT.Section3.ResponseFields.JunkBranchB

/-!
# The differentiated endpoint of the `H̲^{1/2}` interpolation

In Step 2 of the proof of `l.abstract.response.fields`,
`e.abstract.response.Hhalf` is obtained by interpolating "the corresponding
`L²` and `H¹` estimates". The
`L̲²` endpoint is `Sobolev.exists_unitCubeResponseGradientL2Bound`; the
differentiated endpoint is `e.abstract.response.W28` at `p = 2` on the unit
centered cube, in the competitor form the `K`-functional lane consumes. That is
the binder `hendpoint` of `dirichlet_hhalf_bridge`, and this module discharges it.

## The route

`Sobolev.exists_cubeDirichletResponseHessianLpEstimate` at `p = 2` gives, for a
flux `F` on `cu_0` which is square integrable and carries a square integrable
weak Jacobian `DF`, and for *every* Dirichlet response `w` of `F`, a weak
Hessian witness `H` of `w` with

> `‖∇²w‖_{L̲²(cu_0)} ≤ C(d) ‖∇F‖_{L̲²(cu_0)}`.

An `H¹` competitor `G` supplies exactly those data
(`memLp_competitorField`, `hasWeakJacobianOn_competitor`,
`memLp_competitorGradientHilbertMat`), and `weakHessianCompetitor H` turns the
witness back into a competitor whose field is `∇w` on the nose
(`HhalfEndpoint.lean`). The two gradient sizes are the same quantity read in
`ℝ` and in `ℝ≥0∞` (`continuousKGradientNorm_eq_toReal_cubeLpENorm`), and the
right-hand side is finite because `G` is a competitor, so passing to
`ENNReal.toReal` keeps the inequality.

## The constant

`hhalfEndpointConst d hd` is the real value of the `ℝ≥0∞` constant of
`Sobolev.exists_cubeDirichletResponseHessianLpEstimate` at `p = 2`. It cannot
be written as a closed formula in `d`: that endpoint, and below it
CoarseGraining's scalar Poisson Hessian Calderón-Zygmund estimate, state their
constants existentially, so `Classical.choose` is the only name available. It
depends on `d` and on `hd` alone and is quantified before the competitor, the
response and the scale.

## Main results

* `hhalfEndpointConst`, `hhalfEndpointConst_nonneg`: the constant.
* `hhalf_endpoint_bridge`: the `hendpoint` binder of
  `dirichlet_hhalf_bridge`, in exact shape.
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

/-! ## The constant -/

/-- **The constant of the differentiated endpoint**: the real value of the
`ℝ≥0∞` constant of the divergence-form `W^{2,2}` estimate on the unit centered
cube. -/
def hhalfEndpointConst (d : ℕ) (hd : 2 ≤ d) : ℝ :=
  (Classical.choose (Sobolev.exists_cubeDirichletResponseHessianLpEstimate (d := d)
    hd 2 (by norm_num) (by norm_num))).toReal

theorem hhalfEndpointConst_nonneg (d : ℕ) (hd : 2 ≤ d) :
    0 ≤ hhalfEndpointConst d hd :=
  ENNReal.toReal_nonneg

/-! ## The differentiated endpoint -/

/-- **The differentiated endpoint of the interpolation of Step 2**,
in the exact shape of the `hendpoint` binder of
`dirichlet_hhalf_bridge`: for every `H¹` competitor `G` on the unit centered
cube and every Dirichlet response `w` of `G.toField` there is an `H¹`
competitor whose field is `∇w` and whose gradient size is at most
`hhalfEndpointConst d hd` times that of `G`.

This is `e.abstract.response.W28` at `p = 2` on `cu_0` with `∇w` packaged as
`d` honest `H¹` functions. Nothing is carried: the estimate is
`Sobolev.exists_cubeDirichletResponseHessianLpEstimate`, and the packaging is
`weakHessianCompetitor`. -/
theorem hhalf_endpoint_bridge (d : ℕ) (hd : 2 ≤ d) :
    ∀ (G : ContinuousKCompetitor d)
      (w : H10Function (openCubeSet (originCube d 0))),
      IsCubeDirichletResponse (originCube d 0) G.toField w →
      ∃ G' : ContinuousKCompetitor d,
        G'.toField = w.toH1Function.grad ∧
          continuousKGradientNorm G' ≤
            hhalfEndpointConst d hd * continuousKGradientNorm G := by
  obtain ⟨hCtop, hC⟩ := Classical.choose_spec
    (Sobolev.exists_cubeDirichletResponseHessianLpEstimate (d := d) hd 2
      (by norm_num) (by norm_num))
  set C := Classical.choose
    (Sobolev.exists_cubeDirichletResponseHessianLpEstimate (d := d) hd 2
      (by norm_num) (by norm_num)) with hCdef
  intro G w hw
  have hmem := memLp_competitorGradientHilbertMat G
  obtain ⟨H, -, hbound⟩ := hC 0 G.toField (fun i => (G.coord i).grad)
    (memLp_competitorField G) (hasWeakJacobianOn_competitor G) hmem hmem w hw
  refine ⟨weakHessianCompetitor H, rfl, ?_⟩
  rw [continuousKGradientNorm_eq_toReal_cubeLpENorm,
    continuousKGradientNorm_eq_toReal_cubeLpENorm]
  have hmulfin : C * cubeLpENorm (originCube d 0) 2
      (Sobolev.jacobianHilbertMat (fun i => (G.coord i).grad)) ≠ ⊤ :=
    ENNReal.mul_ne_top hCtop.ne hmem.eLpNorm_ne_top
  calc (cubeLpENorm (originCube d 0) 2
          (fun x => HilbertMat.ofMat ((weakHessianCompetitor H).gradient x))).toReal
      ≤ (C * cubeLpENorm (originCube d 0) 2
          (Sobolev.jacobianHilbertMat (fun i => (G.coord i).grad))).toReal :=
        ENNReal.toReal_mono hmulfin hbound
    _ = hhalfEndpointConst d hd * (cubeLpENorm (originCube d 0) 2
          (fun x => HilbertMat.ofMat (G.gradient x))).toReal := by
        rw [ENNReal.toReal_mul, hCdef]
        rfl

/-! ## The a priori anchor with the endpoint discharged -/

end

end ResponseFields
end Section3
end SuperdiffusionCLT
