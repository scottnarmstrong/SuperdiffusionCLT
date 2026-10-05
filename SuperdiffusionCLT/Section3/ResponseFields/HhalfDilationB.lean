/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.ResponseFields.HhalfDilation
public import SuperdiffusionCLT.Section3.ResponseFields.HarmonicInterpolationB
public import SuperdiffusionCLT.Sobolev.ResponseHalfInterpolation
public import Homogenization.Deterministic.ConstantCoefficientDirichletBesov.CenteredCubeScaleTransport

/-!
# `e.abstract.response.Hhalf` for the Dirichlet response at the scale `M`

This module treats the display `e.abstract.response.Hhalf` of the paper and Step 2
of its proof.

`Sobolev/ResponseHalfInterpolation.lean` performs the interpolation of Step 2 on
the unit centered cube `cu_0 = originCube d 0`, which is the cube carrying
CoarseGraining's `K`-functional lane. This module carries that estimate to the
cube `cu_M` of the display and puts it in the exact shape the `hHalf` binder of
`exists_dirichletHsClause` consumes.

## The three steps

1. **The dilation of the norm.** `cubeHsENorm_originCube`
   (`Section3/ResponseFields/HhalfDilation.lean`) gives
   `‖f‖_{H̲^s(cu_M)} = 3^{-sM} ‖f ∘ δ_M‖_{H̲^s(cu_0)}` with `δ_M x = 3^M x`, the
   factor `3^{-sM}` being the scale weight `cubeHsWeight (cu_M) s` in the
   definition of the norm. The same factor appears on
   both sides of the display, so it cancels.
2. **The dilation of the Dirichlet response.** The normalized pullback
   `ŵ(x) = 3^{-M} w(3^M x)` of `Homogenization.centeredCubeNormalizedPullback`
   has weak gradient `∇w ∘ δ_M`, and
   `cubeDirichletDivergenceProblem_normalizedPullback` transports the weak
   problem: `ŵ` is the Dirichlet response on `cu_0` of the pulled-back flux
   `F ∘ δ_M`. No factor appears, because the normalization of the pullback is
   exactly the one that leaves the gradient unscaled.
3. **The passage to the chosen response.** The interpolation of Step 2 is proved
   for the response `unitCubeDirichletResponse` chosen by
   `Classical.choose`; the anchor quantifies over every response. Two responses
   of the same flux have almost everywhere the same gradient
   (`grad_ae_eq_of_isCubeDirichletResponse`), and `cubeHsENorm_congr_ae` says
   that both pieces of the norm only see the field almost everywhere.

## The two inputs taken as hypotheses

* `hendpoint` is the *differentiated endpoint* of the interpolation: for an
  `H¹` flux `G` on `cu_0` the Dirichlet response is `H²` and its Hessian
  satisfies `‖∇²w‖_{L̲²(cu_0)} ≤ B ‖∇G‖_{L̲²(cu_0)}`, with `∇w` packaged as `d`
  honest `H¹` functions. This is `e.abstract.response.W28` at `p = 2` on the
  unit cube in competitor form. The estimate
  `Sobolev.exists_cubeDirichletResponseHessianLpEstimate` produces a weak
  Hessian witness `HasWeakHessianOn`, not a `ContinuousKCompetitor`; the
  packaging is done by `hhalf_endpoint_bridge`.
* `hjunk` is the branch on which the flux is not almost everywhere strongly
  measurable while `‖F‖_{H̲^{1/2}(cu_M)}` is finite. There every pairing
  `∫_{cu_M} F·∇φ` that is not integrable evaluates to Bochner's `0`, so the
  response equation forces `∇w_D = 0` almost everywhere; that implication is
  taken as the hypothesis here and proved by `junkHalf_bridge`. The statement
  carries no integrability hypothesis on `F`, so the branch is part of it.

## Main results

* `dirichletHhalfConst`, `dirichletHhalfConst_lt_top`: the constant.
* `isCubeDirichletResponse_centeredCubeNormalizedPullback`: step 2.
* `dirichlet_hhalf_bridge`: the `hHalf` binder of `exists_dirichletHsClause`.
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

/-- The interpolation order `s = 1/2` of `e.abstract.response.Hhalf`. -/
def halfFractionalOrder : FractionalOrder := ⟨1 / 2, by norm_num⟩

/-- The `L̲²` endpoint constant of the two response operators on the unit
centered cube, the `p = 2` case of `exists_cubeResponseGradientLpEstimate`. -/
def unitCubeResponseGradientL2Const (d : ℕ) (hd : 2 ≤ d) : ℝ :=
  Classical.choose (Sobolev.exists_unitCubeResponseGradientL2Bound (d := d) hd)

/-- **The constant of `e.abstract.response.Hhalf` for the Dirichlet response**,
given the constant `B` of the differentiated endpoint of the interpolation:
twice the square of CoarseGraining's `K`-functional comparison constant times
the larger of the two endpoint constants, doubled again by the two-sided
comparison between `cubeHsENorm` and `euclideanHsFullENorm`. -/
def dirichletHhalfConst (d : ℕ) (hd : 2 ≤ d) (B : ℝ) : ℝ≥0∞ :=
  2 * (continuousKEuclideanHsFullENormConstant halfFractionalOrder d ^ 2 *
    ENNReal.ofReal (max (unitCubeResponseGradientL2Const d hd) B))

theorem dirichletHhalfConst_lt_top (d : ℕ) (hd : 2 ≤ d) (B : ℝ) :
    dirichletHhalfConst d hd B < ⊤ := by
  refine ENNReal.mul_lt_top (by norm_num) (ENNReal.mul_lt_top ?_ ENNReal.ofReal_lt_top)
  exact ENNReal.pow_lt_top
    (continuousKEuclideanHsFullENormConstant_lt_top halfFractionalOrder d)

/-! ## The dilation of the Dirichlet response -/

section Transport

variable {d : ℕ}

/-- An `L̲²(cu_m)` flux, bundled in upstream's centered-cube carrier. -/
private def centeredFlux {m : ℤ} {F : Vec d → Vec d}
    (hF : MemLp (hilbertifyVecField F) 2 (normalizedCubeMeasure (originCube d m))) :
    CenteredCubeEuclideanL2Field d m where
  toField := F
  euclideanMemL2 := by
    rw [centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
    exact hF

/-- **The Dirichlet response is carried by the dilation.** The normalized
pullback `ŵ(x) = 3^{-m} w(3^m x)` of `w` is the Dirichlet response on the unit
centered cube of the pulled-back flux `F ∘ δ_m`; the normalization is exactly
the one that leaves the weak gradient unscaled, so no factor appears. -/
theorem isCubeDirichletResponse_centeredCubeNormalizedPullback {m : ℤ}
    {F : Vec d → Vec d}
    (hF : MemLp (hilbertifyVecField F) 2 (normalizedCubeMeasure (originCube d m)))
    {w : H10Function (openCubeSet (originCube d m))}
    (hw : IsCubeDirichletResponse (originCube d m) F w) :
    IsCubeDirichletResponse (originCube d 0)
      (fun x => F (centeredCubeScale m • x)) (centeredCubeNormalizedPullback w) :=
  cubeDirichletDivergenceProblem_normalizedPullback (centeredFlux hF) w hw

/-- The dilation law of `‖·‖_{H̲^s}` on the Euclidean realization of a vector
field, at the centered cubes. -/
theorem cubeHsENorm_hilbertify_originCube (m : ℤ) (s : ℝ) (F : Vec d → Vec d) :
    cubeHsENorm (originCube d m) s (hilbertifyVecField F) =
      cubeHsWeight (originCube d m) s *
        cubeHsENorm (originCube d 0) s
          (hilbertifyVecField (fun x => F (centeredCubeScale m • x))) := by
  rw [cubeHsENorm_originCube]
  rfl

/-- The same, for the weak gradient of a zero-trace function and its normalized
pullback. -/
theorem cubeHsENorm_hilbertify_grad_originCube {m : ℤ}
    (w : H10Function (openCubeSet (originCube d m))) (s : ℝ) :
    cubeHsENorm (originCube d m) s (hilbertifyVecField w.toH1Function.grad) =
      cubeHsWeight (originCube d m) s *
        cubeHsENorm (originCube d 0) s
          (hilbertifyVecField
            (centeredCubeNormalizedPullback w).toH1Function.grad) := by
  have hfun : (fun x : Vec d =>
      hilbertifyVecField w.toH1Function.grad (centeredCubeScale m • x)) =
      hilbertifyVecField (centeredCubeNormalizedPullback w).toH1Function.grad := by
    funext x
    have hx := centeredCubeNormalizedPullback_grad w x
    simp only [hilbertifyVecField, hx]
  rw [cubeHsENorm_originCube]
  exact congrArg (fun t => cubeHsWeight (originCube d m) s * t) (congrArg _ hfun)

/-- The scale weight of clause (b) never vanishes. -/
theorem cubeHsWeight_ne_zero (Q : TriadicCube d) (s : ℝ) :
    cubeHsWeight Q s ≠ 0 := by
  have hpos : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale
  exact ENNReal.ofReal_ne_zero_iff.2 (Real.rpow_pos_of_pos hpos _)

end Transport

/-! ## The `H̲^{1/2}` bridge at the scale `M` -/

/-- **`e.abstract.response.Hhalf` for the Dirichlet response at the scale `M`**,
in the exact shape of the `hHalf` binder of
`exists_dirichletHsClause`, with the constant `dirichletHhalfConst d hd B`
quantified before the scale, the flux and the response.

Two inputs are carried, and only those two.

* `hendpoint` is the differentiated endpoint of the interpolation of Step 2:
  the Dirichlet response of an `H¹` flux `G` on the unit
  centered cube has its gradient again in `H¹`, packaged as `d` honest `H¹`
  functions, with `‖∇²w‖_{L̲²(cu_0)} ≤ B ‖∇G‖_{L̲²(cu_0)}`. This is
  `e.abstract.response.W28` at `p = 2` on the unit cube in competitor form; the
  estimate `Sobolev.exists_cubeDirichletResponseHessianLpEstimate` produces a
  `HasWeakHessianOn` witness rather than a `ContinuousKCompetitor`, and
  `hhalf_endpoint_bridge` performs the packaging.
* `hjunk` is the branch on which the flux is not almost everywhere strongly
  measurable on `cu_M`. The statement carries no integrability hypothesis
  on `F`, so this branch belongs to it; on it every non-integrable
  pairing `∫_{cu_M} F·∇φ` evaluates to Bochner's `0` and the response equation
  forces `∇w_D = 0` almost everywhere.

Everything else — the dilation of the norm, the dilation of the response, the
`L̲²` endpoint, the `K`-method interpolation and the passage from the chosen
response to an arbitrary one — is proved. -/
theorem dirichlet_hhalf_bridge (d : ℕ) (hd : 2 ≤ d) (B : ℝ) (hB : 0 ≤ B)
    (hendpoint : ∀ (G : ContinuousKCompetitor d)
      (w : H10Function (openCubeSet (originCube d 0))),
      IsCubeDirichletResponse (originCube d 0) G.toField w →
      ∃ G' : ContinuousKCompetitor d,
        G'.toField = w.toH1Function.grad ∧
          continuousKGradientNorm G' ≤ B * continuousKGradientNorm G)
    (hjunk : ∀ (M : ℕ) (F : Vec d → Vec d)
      (wD : H10Function (openCubeSet (originCube d (M : ℤ)))),
      IsCubeDirichletResponse (originCube d (M : ℤ)) F wD →
      ¬ AEStronglyMeasurable (hilbertifyVecField F)
          (normalizedCubeMeasure (originCube d (M : ℤ))) →
      wD.toH1Function.grad =ᵐ[volume.restrict (openCubeSet (originCube d (M : ℤ)))]
        0) :
    ∀ (M : ℕ) (F : Vec d → Vec d)
      (wD : H10Function (openCubeSet (originCube d (M : ℤ)))),
      IsCubeDirichletResponse (originCube d (M : ℤ)) F wD →
      cubeHsENorm (originCube d (M : ℤ)) (1 / 2) (hilbertifyVecField F) < ⊤ →
      cubeHsENorm (originCube d (M : ℤ)) (1 / 2)
          (hilbertifyVecField wD.toH1Function.grad) ≤
        dirichletHhalfConst d hd B *
          cubeHsENorm (originCube d (M : ℤ)) (1 / 2) (hilbertifyVecField F) := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨hAnonneg, hA⟩ :=
    Classical.choose_spec (Sobolev.exists_unitCubeResponseGradientL2Bound (d := d) hd)
  have hL2 : ∀ H : Vec d → Vec d,
      MemLp (hilbertifyVecField H) 2 (normalizedCubeMeasure (originCube d 0)) →
      ∀ w : H10Function (openCubeSet (originCube d 0)),
        IsCubeDirichletResponse (originCube d 0) H w →
          vecCubeLpENorm (originCube d 0) 2 w.toH1Function.grad ≤
            ENNReal.ofReal (unitCubeResponseGradientL2Const d hd) *
              vecCubeLpENorm (originCube d 0) 2 H :=
    fun H hH w hw => (hA H hH).1 w hw
  have hchoice : ∀ G : ContinuousKCompetitor d,
      ∃ G' : ContinuousKCompetitor d,
        G'.toField =
            (Sobolev.unitCubeDirichletResponseGradient
              (Sobolev.competitorField G)).toField ∧
          continuousKGradientNorm G' ≤ B * continuousKGradientNorm G := by
    intro G
    exact hendpoint G (Sobolev.unitCubeDirichletResponse (Sobolev.competitorField G))
      (Sobolev.isCubeDirichletResponse_unitCubeDirichletResponse
        (Sobolev.competitorField G))
  have hunit := Sobolev.cubeHsENorm_unitCubeDirichletResponseGradient_le
    halfFractionalOrder hAnonneg hB hL2 (fun G => Classical.choose (hchoice G))
    (fun G => (Classical.choose_spec (hchoice G)).1)
    (fun G => (Classical.choose_spec (hchoice G)).2)
  intro M F wD hD hfin
  by_cases hmeas : AEStronglyMeasurable (hilbertifyVecField F)
      (normalizedCubeMeasure (originCube d (M : ℤ)))
  · have hLfin : cubeLpENorm (originCube d (M : ℤ)) 2 (hilbertifyVecField F) < ⊤ := by
      refine lt_top_iff_ne_top.2 fun htop => hfin.ne ?_
      have hle := cubeHsENorm_weighted_le (originCube d (M : ℤ)) (1 / 2)
        (hilbertifyVecField F)
      rw [htop, ENNReal.mul_top (cubeHsWeight_ne_zero (originCube d (M : ℤ)) (1 / 2))]
        at hle
      exact top_le_iff.1 hle
    have hFmem : MemLp (hilbertifyVecField F) 2
        (normalizedCubeMeasure (originCube d (M : ℤ))) := MeasureTheory.memLp_iff.mpr hLfin
    have hD0 : IsCubeDirichletResponse (originCube d 0)
        (fun x => F (centeredCubeScale (M : ℤ) • x))
        (centeredCubeNormalizedPullback wD) :=
      isCubeDirichletResponse_centeredCubeNormalizedPullback hFmem hD
    have hae := grad_ae_eq_of_isCubeDirichletResponse hD0
      (Sobolev.isCubeDirichletResponse_unitCubeDirichletResponse
        (centeredFlux hFmem).pullbackToUnit)
    have haeH : hilbertifyVecField
          (centeredCubeNormalizedPullback wD).toH1Function.grad
        =ᵐ[volume.restrict (openCubeSet (originCube d 0))]
        hilbertifyVecField
          (Sobolev.unitCubeDirichletResponse
            (centeredFlux hFmem).pullbackToUnit).toH1Function.grad := by
      filter_upwards [hae] with x hx
      simp only [hilbertifyVecField, hx]
    have hkey : cubeHsENorm (originCube d 0) (1 / 2)
        (hilbertifyVecField
          (Sobolev.unitCubeDirichletResponse
            (centeredFlux hFmem).pullbackToUnit).toH1Function.grad) ≤
        dirichletHhalfConst d hd B *
          cubeHsENorm (originCube d 0) (1 / 2)
            (hilbertifyVecField
              (fun x => F (centeredCubeScale (M : ℤ) • x))) :=
      hunit (centeredFlux hFmem).pullbackToUnit
    rw [← cubeHsENorm_congr_ae haeH] at hkey
    rw [cubeHsENorm_hilbertify_grad_originCube wD (1 / 2),
      cubeHsENorm_hilbertify_originCube (M : ℤ) (1 / 2) F]
    calc cubeHsWeight (originCube d (M : ℤ)) (1 / 2) *
          cubeHsENorm (originCube d 0) (1 / 2)
            (hilbertifyVecField
              (centeredCubeNormalizedPullback wD).toH1Function.grad)
        ≤ cubeHsWeight (originCube d (M : ℤ)) (1 / 2) *
            (dirichletHhalfConst d hd B *
              cubeHsENorm (originCube d 0) (1 / 2)
                (hilbertifyVecField
                  (fun x => F (centeredCubeScale (M : ℤ) • x)))) :=
          mul_le_mul' le_rfl hkey
      _ = dirichletHhalfConst d hd B *
            (cubeHsWeight (originCube d (M : ℤ)) (1 / 2) *
              cubeHsENorm (originCube d 0) (1 / 2)
                (hilbertifyVecField
                  (fun x => F (centeredCubeScale (M : ℤ) • x)))) := by
          rw [mul_left_comm]
  · have haeH : hilbertifyVecField wD.toH1Function.grad
        =ᵐ[volume.restrict (openCubeSet (originCube d (M : ℤ)))]
        (0 : Vec d → HilbertVec d) := by
      filter_upwards [hjunk M F wD hD hmeas] with x hx
      show HilbertVec.ofVec (wD.toH1Function.grad x) = (0 : Vec d → HilbertVec d) x
      rw [hx]
      rfl
    rw [cubeHsENorm_congr_ae haeH, cubeHsENorm_zero]
    exact zero_le

/-! ## The a priori anchor with the `H̲^{1/2}` clause discharged -/

end

end ResponseFields
end Section3
end SuperdiffusionCLT
