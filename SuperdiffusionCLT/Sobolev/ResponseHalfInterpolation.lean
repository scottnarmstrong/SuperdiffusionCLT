/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Sobolev.OperatorInterpolation
public import SuperdiffusionCLT.Section2.Norms.FractionalHs
public import SuperdiffusionCLT.Section3.ResponseFields.LpEstimates

/-!
# The `H̲^{1/2}` response bound by interpolation on the unit centered cube

display `e.abstract.response.Hhalf`, asserts with a constant `C(d) < ∞`

> `‖∇w_D‖_{H̲^{1/2}(cu_M)} + ‖∇w_N‖_{H̲^{1/2}(cu_M)} ≤ C ‖F‖_{H̲^{1/2}(cu_M)}`

for the two responses of `e.abstract.response.equations`, and Step 2 of the
proof obtains it "by interpolating the corresponding `L²`
and `H¹` estimates".

This module carries out that interpolation on the unit centered cube
`originCube d 0`, which is the cube on which CoarseGraining's `K`-functional
lane lives. Three things are done.

1. **The two fractional norms are identified.** The local
   `SuperdiffusionCLT.Section2.Norms.cubeHsENorm (originCube d 0) s`
   (the local normalized norm), and upstream's
   `Homogenization.euclideanHsFullENorm s` are the same two quantities
   combined differently: the first is `(‖·‖²_{L̲²} + [·]²)^{1/2}` and the
   second is `‖·‖_{L̲²} + [·]`. On the unit cube the scale weight `3^{-sl}` is
   `1`, the `L̲²` parts agree on the nose, and the Gagliardo parts agree on the
   nose; so the two norms differ by a factor at most `2` in either direction.

2. **The two response operators are realized as maps.** `Vec`-valued fluxes in
   `L̲²` of the unit cube have Dirichlet and mean-zero Neumann responses
   (`exists_isCubeDirichletResponse`, `exists_isCubeNeumannResponse`), unique in
   the gradient; the gradient of a chosen response is a map of the flux, and it
   is additive because the difference of two responses is the response of the
   difference.

3. **The interpolation step is applied.** With the `L̲²` endpoint of
   `exists_cubeResponseGradientLpEstimate` at `p = 2` and a competitor-level
   `H̲¹` endpoint, `continuousKFullENorm_le_of_endpoints` gives the `H̲^s`
   bound, and step 1 carries it to `cubeHsENorm`.

## The remaining input

The `H̲¹` endpoint is supplied as the hypothesis `hgrad` together with the
realization hypothesis `htransfer`: a rule assigning to each `H¹` competitor
`G` for the flux a competitor for the response gradient, whose field is the
gradient of the response of `G` and whose gradient `L̲²` size is at most `B`
times that of `G`. Its Dirichlet half is the `p = 2` case of
`SuperdiffusionCLT.Sobolev.exists_cubeDirichletResponseHessianLpEstimate`
plus the packaging of `∇w_G` as an `H¹` field; its Neumann half is upstream's
`originCubeNeumannW22CalderonZygmund_qTwo`. Neither packaging is performed
here.

## Main results

* `cubeLpENorm_hilbertify_eq_normalizedEuclideanLpENorm`,
  `cubeEuclideanGagliardoESeminorm_eq_euclideanHsESeminorm`: the two pieces of
  the norm identification.
* `cubeHsENorm_le_euclideanHsFullENorm`,
  `euclideanHsFullENorm_le_two_mul_cubeHsENorm`: the two-sided comparison.
* `unitCubeDirichletResponseGradient`: the Dirichlet solution operator on the flux
  space of the unit cube.
* `isCubeDirichletResponse_sub`: additivity of the Dirichlet response, from which
  the residual endpoint bound follows.
* `exists_unitCubeResponseGradientL2Bound`: the `L̲²` endpoint with a
  nonnegative real constant.
* `continuousKResidualNorm_unitCubeDirichletResponseGradient_le`: the residual
  half of the endpoint bound.
* `cubeHsENorm_unitCubeDirichletResponseGradient_le`: the `H̲^s` bound for the
  Dirichlet response gradient.
-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Sobolev

open Homogenization
open MeasureTheory
open Section2.Norms
open Section3.ResponseFields
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The two fractional norms on the unit centered cube -/

/-- The flux of a unit-cube Euclidean `L²` field is in `L̲²` of the cube. -/
theorem memLp_normalizedCubeMeasure_of_unitCubeField (F : UnitCubeEuclideanL2Field d) :
    MemLp (hilbertifyVecField F.toField) 2 (normalizedCubeMeasure (originCube d 0)) := by
  have h := F.euclideanMemL2
  rwa [unitCenteredCubeDomain,
    cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure] at h

/-- The normalized cube `L̲²` norm of the Euclidean realization of a vector
field is upstream's normalized Euclidean `L²` norm. -/
theorem cubeLpENorm_hilbertify_eq_normalizedEuclideanLpENorm (F : Vec d → Vec d)
    (hF : AEStronglyMeasurable (hilbertifyVecField F)
      (normalizedCubeMeasure (originCube d 0))) :
    cubeLpENorm (originCube d 0) 2 (hilbertifyVecField F) =
      (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) F := by
  unfold cubeLpENorm BoundedMeasurableDomain.normalizedEuclideanLpENorm
    BoundedMeasurableDomain.normalizedLpENorm
  rw [unitCenteredCubeDomain,
    cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
    show (fun x => euclideanNorm (F x)) = fun x => ‖hilbertifyVecField F x‖ from
      funext fun x => euclideanNorm_eq_norm_ofVec (F x)]
  exact (eLpNorm_norm _ hF).symm

private theorem enorm_euclideanGagliardoKernel_rpow_two (s : ℝ) (F : Vec d → Vec d)
    (z : Vec d × Vec d) :
    ‖euclideanGagliardoKernel s 2 (hilbertifyVecField F) z‖ₑ ^ (2 : ℝ) =
      ENNReal.ofReal (‖HilbertVec.ofVec (F z.1 - F z.2)‖ ^ 2 /
        Real.rpow (euclideanDist z.1 z.2) ((d : ℝ) + 2 * s)) := by
  have hsub : hilbertifyVecField F z.1 - hilbertifyVecField F z.2 =
      HilbertVec.ofVec (F z.1 - F z.2) := by
    exact (map_sub (HilbertVec.ofVecL d) (F z.1) (F z.2)).symm
  have hnorm : ‖euclideanGagliardoKernel s 2 (hilbertifyVecField F) z‖ =
      euclideanDist z.1 z.2 ^ (-(s + (d : ℝ) / 2)) *
        ‖HilbertVec.ofVec (F z.1 - F z.2)‖ := by
    rw [norm_euclideanGagliardoKernel]
    simp only [ENNReal.toReal_ofNat, hsub]
  rcases eq_or_lt_of_le (euclideanDist_nonneg z.1 z.2) with hzero | hpos
  · have hEq : z.1 = z.2 := euclideanDist_eq_zero_iff.1 hzero.symm
    have hz : ‖HilbertVec.ofVec (F z.1 - F z.2)‖ = 0 := by
      rw [hEq, sub_self]
      simp
    rw [← ofReal_norm, hnorm, hz, mul_zero, ENNReal.ofReal_zero,
      ENNReal.zero_rpow_of_pos (by norm_num)]
    norm_num
  · rw [← ofReal_norm, hnorm,
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    rw [Real.rpow_two, mul_pow]
    have hsq : (euclideanDist z.1 z.2 ^ (-(s + (d : ℝ) / 2))) ^ 2 =
        (euclideanDist z.1 z.2 ^ ((d : ℝ) + 2 * s))⁻¹ := by
      rw [← Real.rpow_natCast (euclideanDist z.1 z.2 ^ (-(s + (d : ℝ) / 2))) 2,
        ← Real.rpow_mul hpos.le, ← Real.rpow_neg hpos.le]
      congr 1
      push_cast
      ring
    have hrne : euclideanDist z.1 z.2 ^ ((d : ℝ) + 2 * s) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos hpos _)
    rw [hsq, show Real.rpow (euclideanDist z.1 z.2) ((d : ℝ) + 2 * s) =
        euclideanDist z.1 z.2 ^ ((d : ℝ) + 2 * s) from rfl]
    field_simp

/-- The source product measure of the Euclidean `H^s` seminorm is the
Gagliardo product measure of the unit centered cube. -/
theorem euclideanHsProductMeasure_eq_gagliardoCubeMeasure (d : ℕ) :
    euclideanHsProductMeasure d = Gagliardo.gagliardoCubeMeasure (originCube d 0) := by
  rw [euclideanHsProductMeasure, Gagliardo.gagliardoCubeMeasure, unitCenteredCubeDomain,
    cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
  rfl

/-- The local volume-normalized Gagliardo seminorm at exponent `2` on the unit
centered cube is upstream's exact Euclidean `H^s` seminorm. -/
theorem cubeEuclideanGagliardoESeminorm_eq_euclideanHsESeminorm
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) :
    cubeEuclideanGagliardoESeminorm (originCube d 0) s.1 2 (hilbertifyVecField F) =
      euclideanHsESeminorm s F := by
  rw [cubeEuclideanGagliardoESeminorm,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      (aestronglyMeasurable_euclideanGagliardoKernel
        (memLp_normalizedCubeMeasure_of_unitCubeField F).aestronglyMeasurable),
    euclideanHsESeminorm, euclideanHsEnergy,
    euclideanHsProductMeasure_eq_gagliardoCubeMeasure d]
  simp only [ENNReal.toReal_ofNat, one_div]
  exact congrArg (fun x : ℝ≥0∞ => x ^ ((2 : ℝ)⁻¹))
    (lintegral_congr fun z => enorm_euclideanGagliardoKernel_rpow_two s.1 F z)

/-- On the unit centered cube the scale weight of the normalized fractional
norm is `1`. -/
theorem cubeHsWeight_originCube_zero (s : ℝ) : cubeHsWeight (originCube d 0) s = 1 := by
  rw [cubeHsWeight, cubeScaleFactor_originCube,
    show ((3 : ℝ) ^ (0 : ℤ)) = 1 from zpow_zero 3, Real.one_rpow,
    ENNReal.ofReal_one]

/-- The local `H̲^s` norm is at most upstream's exact Euclidean `H^s` full
norm. -/
theorem cubeHsENorm_le_euclideanHsFullENorm (s : FractionalOrder)
    (F : UnitCubeEuclideanL2Field d) :
    cubeHsENorm (originCube d 0) s.1 (hilbertifyVecField F) ≤ euclideanHsFullENorm s F := by
  refine (cubeHsENorm_le_add _ _ _).trans (le_of_eq ?_)
  rw [cubeHsWeight_originCube_zero, one_mul, euclideanHsFullENorm_eq,
    cubeLpENorm_hilbertify_eq_normalizedEuclideanLpENorm _
      (memLp_normalizedCubeMeasure_of_unitCubeField F).aestronglyMeasurable,
    cubeEuclideanGagliardoESeminorm_eq_euclideanHsESeminorm]

/-- Upstream's exact Euclidean `H^s` full norm is at most twice the local
`H̲^s` norm. -/
theorem euclideanHsFullENorm_le_two_mul_cubeHsENorm (s : FractionalOrder)
    (F : UnitCubeEuclideanL2Field d) :
    euclideanHsFullENorm s F ≤
      2 * cubeHsENorm (originCube d 0) s.1 (hilbertifyVecField F) := by
  have hL : (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) F ≤
      cubeHsENorm (originCube d 0) s.1 (hilbertifyVecField F) := by
    rw [← cubeLpENorm_hilbertify_eq_normalizedEuclideanLpENorm _
      (memLp_normalizedCubeMeasure_of_unitCubeField F).aestronglyMeasurable]
    simpa only [cubeHsWeight_originCube_zero, one_mul] using
      cubeHsENorm_weighted_le (originCube d 0) s.1 (hilbertifyVecField F)
  have hG : euclideanHsESeminorm s F ≤
      cubeHsENorm (originCube d 0) s.1 (hilbertifyVecField F) := by
    rw [← cubeEuclideanGagliardoESeminorm_eq_euclideanHsESeminorm]
    exact cubeHsENorm_gagliardo_le (originCube d 0) s.1 (hilbertifyVecField F)
  rw [euclideanHsFullENorm_eq, two_mul]
  exact add_le_add hL hG

/-! ## The two response operators on the flux space of the unit cube -/

theorem vecCubeLpENorm_originCube_zero_eq_normalizedEuclideanLpENorm (X : Vec d → Vec d)
    (hX : AEStronglyMeasurable (hilbertifyVecField X)
      (normalizedCubeMeasure (originCube d 0))) :
    vecCubeLpENorm (originCube d 0) 2 X =
      (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) X :=
  cubeLpENorm_hilbertify_eq_normalizedEuclideanLpENorm X hX

private theorem hilbertifyVecField_sub (a b : Vec d → Vec d) :
    hilbertifyVecField (fun x => a x - b x) =
      fun x => hilbertifyVecField a x - hilbertifyVecField b x := by
  funext x
  exact map_sub (HilbertVec.ofVecL d) (a x) (b x)

private theorem memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure
    {Q : TriadicCube d} {H : Vec d → Vec d} (h : MemLp H 2 (normalizedCubeMeasure Q)) :
    MemVectorL2 (openCubeSet Q) H := by
  have h1 : MemLp H 2 ((cubeBoundedMeasurableDomain Q).normalizedVolume) := by
    rwa [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
  have h2 : MemLp H 2 ((cubeBoundedMeasurableDomain Q).restrictedVolume) :=
    ((cubeBoundedMeasurableDomain Q).memLp_normalizedVolume_iff 2 H).1 h1
  exact h2.mono_measure (Measure.restrict_mono (openCubeSet_subset_cubeSet Q) le_rfl)

theorem memVectorL2_of_unitCubeField (F : UnitCubeEuclideanL2Field d) :
    MemVectorL2 (openCubeSet (originCube d 0)) F.toField :=
  memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure
    (memLp_hilbertifyVecField_iff.1 (memLp_normalizedCubeMeasure_of_unitCubeField F))

/-- The weak gradient of an `H¹` function on the unit cube, as a unit-cube
Euclidean `L²` field. -/
noncomputable def unitCubeFieldOfGrad (u : H1Function (openCubeSet (originCube d 0))) :
    UnitCubeEuclideanL2Field d where
  toField := u.grad
  euclideanMemL2 := by
    rw [unitCenteredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
    exact memLp_hilbertifyVecField_iff.2
      (MemLp.of_eval (fun i : Fin d => u.grad_memL2_normalizedCubeMeasure i))

@[simp] theorem unitCubeFieldOfGrad_toField
    (u : H1Function (openCubeSet (originCube d 0))) :
    (unitCubeFieldOfGrad u).toField = u.grad := rfl

/-- An `H¹` competitor of the interpolation lane, read as a flux field. -/
noncomputable def competitorField (G : ContinuousKCompetitor d) :
    UnitCubeEuclideanL2Field d where
  toField := G.toField
  euclideanMemL2 := G.euclideanMemL2

@[simp] theorem competitorField_toField (G : ContinuousKCompetitor d) :
    (competitorField G).toField = G.toField := rfl

section Dirichlet

variable [NeZero d]

/-- A chosen Dirichlet response of the flux of a unit-cube `L²` field. -/
noncomputable def unitCubeDirichletResponse (F : UnitCubeEuclideanL2Field d) :
    H10Function (openCubeSet (originCube d 0)) :=
  Classical.choose (exists_isCubeDirichletResponse (originCube d 0)
    (memVectorL2_of_unitCubeField F))

theorem isCubeDirichletResponse_unitCubeDirichletResponse
    (F : UnitCubeEuclideanL2Field d) :
    IsCubeDirichletResponse (originCube d 0) F.toField (unitCubeDirichletResponse F) :=
  Classical.choose_spec (exists_isCubeDirichletResponse (originCube d 0)
    (memVectorL2_of_unitCubeField F))

/-- The Dirichlet response gradient as a map of the flux. -/
noncomputable def unitCubeDirichletResponseGradient (F : UnitCubeEuclideanL2Field d) :
    UnitCubeEuclideanL2Field d :=
  unitCubeFieldOfGrad (unitCubeDirichletResponse F).toH1Function

end Dirichlet

/-! ## Additivity of the responses -/

private theorem setIntegral_vecDot_sub {Q : TriadicCube d} {F G ψ : Vec d → Vec d}
    (hF : MemVectorL2 (openCubeSet Q) F) (hG : MemVectorL2 (openCubeSet Q) G)
    (hψ : MemVectorL2 (openCubeSet Q) ψ) :
    ∫ x in openCubeSet Q, vecDot (F x - G x) (ψ x) =
      (∫ x in openCubeSet Q, vecDot (F x) (ψ x)) -
        ∫ x in openCubeSet Q, vecDot (G x) (ψ x) := by
  rw [← integral_sub (integrableOn_vecDot_of_memVectorL2 hF hψ)
    (integrableOn_vecDot_of_memVectorL2 hG hψ)]
  refine setIntegral_congr_fun (measurableSet_openCubeSet Q) (fun x _ => ?_)
  simp only [vecDot, Pi.sub_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Additivity of the Dirichlet response.** The difference of the responses of
two `L̲²` fluxes is a response of the difference. -/
theorem isCubeDirichletResponse_sub {Q : TriadicCube d} {F G : Vec d → Vec d}
    (hF : MemVectorL2 (openCubeSet Q) F) (hG : MemVectorL2 (openCubeSet Q) G)
    {u v : H10Function (openCubeSet Q)}
    (hu : IsCubeDirichletResponse Q F u) (hv : IsCubeDirichletResponse Q G v) :
    IsCubeDirichletResponse Q (fun x => F x - G x) (u - v) := by
  intro φ
  have hgrad : (u - v).toH1Function.grad =
      fun x => u.toH1Function.grad x - v.toH1Function.grad x := by
    rw [show (u - v).toH1Function = u.toH1Function - v.toH1Function from rfl]
    exact H1Function.sub_grad _ _
  rw [hgrad,
    setIntegral_vecDot_sub u.toH1Function.grad_memVectorL2
      v.toH1Function.grad_memVectorL2 φ.toH1Function.grad_memVectorL2,
    setIntegral_vecDot_sub hF hG φ.toH1Function.grad_memVectorL2, hu φ, hv φ]
  ring

/-! ## The `L̲²` endpoint -/

/-- **The `L̲²` endpoint of the two response operators** on the unit centered
cube, with a nonnegative real constant depending on the dimension alone. This is
the `p = 2` case of `exists_cubeResponseGradientLpEstimate`. -/
theorem exists_unitCubeResponseGradientL2Bound (hd : 2 ≤ d) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ H : Vec d → Vec d,
        MemLp (hilbertifyVecField H) 2 (normalizedCubeMeasure (originCube d 0)) →
        (∀ w : H10Function (openCubeSet (originCube d 0)),
            IsCubeDirichletResponse (originCube d 0) H w →
              vecCubeLpENorm (originCube d 0) 2 w.toH1Function.grad ≤
                ENNReal.ofReal A * vecCubeLpENorm (originCube d 0) 2 H) ∧
        (∀ w : H1MeanZeroFunction (openCubeSet (originCube d 0)),
            IsCubeNeumannResponse (originCube d 0) H w →
              vecCubeLpENorm (originCube d 0) 2 w.toH1Function.grad ≤
                ENNReal.ofReal A * vecCubeLpENorm (originCube d 0) 2 H) := by
  obtain ⟨C, hCtop, hC⟩ :=
    exists_cubeResponseGradientLpEstimate hd 2 (by norm_num) (by norm_num)
  refine ⟨C.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro H hH
  rw [ENNReal.ofReal_toReal hCtop.ne]
  exact ⟨fun w hw => ((hC (originCube d 0) H hH).1 w hw).2,
    fun w hw => ((hC (originCube d 0) H hH).2 w hw).2⟩

/-! ## The residual endpoint bound and the interpolation instance -/

private theorem toReal_le_of_le_ofReal_mul {A : ℝ} (hA : 0 ≤ A) {E' E : ℝ≥0∞}
    (hE : E ≠ ⊤) (h : E' ≤ ENNReal.ofReal A * E) : E'.toReal ≤ A * E.toReal := by
  have hfin : ENNReal.ofReal A * E ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hE
  calc
    E'.toReal ≤ (ENNReal.ofReal A * E).toReal := ENNReal.toReal_mono hfin h
    _ = A * E.toReal := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hA]

section Dirichlet

variable [NeZero d]

/-- **The residual half of the two endpoint bounds for the Dirichlet response
operator.** The response of the flux minus the response of a competitor is the
response of their difference, so the `L̲²` endpoint bounds the residual with
the same constant. -/
theorem continuousKResidualNorm_unitCubeDirichletResponseGradient_le
    {A : ℝ} (hA : 0 ≤ A)
    (hL2 : ∀ H : Vec d → Vec d,
      MemLp (hilbertifyVecField H) 2 (normalizedCubeMeasure (originCube d 0)) →
      ∀ w : H10Function (openCubeSet (originCube d 0)),
        IsCubeDirichletResponse (originCube d 0) H w →
          vecCubeLpENorm (originCube d 0) 2 w.toH1Function.grad ≤
            ENNReal.ofReal A * vecCubeLpENorm (originCube d 0) 2 H)
    (F : UnitCubeEuclideanL2Field d) (G G' : ContinuousKCompetitor d)
    (hG' : G'.toField = (unitCubeDirichletResponseGradient (competitorField G)).toField) :
    continuousKResidualNorm (unitCubeDirichletResponseGradient F) G' ≤
      A * continuousKResidualNorm F G := by
  have hmem : MemLp (hilbertifyVecField (fun x => F.toField x - G.toField x)) 2
      (normalizedCubeMeasure (originCube d 0)) := by
    rw [hilbertifyVecField_sub]
    exact (memLp_normalizedCubeMeasure_of_unitCubeField F).sub
      (memLp_normalizedCubeMeasure_of_unitCubeField (competitorField G))
  have hdiff : IsCubeDirichletResponse (originCube d 0)
      (fun x => F.toField x - G.toField x)
      (unitCubeDirichletResponse F - unitCubeDirichletResponse (competitorField G)) :=
    isCubeDirichletResponse_sub (memVectorL2_of_unitCubeField F)
      (memVectorL2_of_unitCubeField (competitorField G))
      (isCubeDirichletResponse_unitCubeDirichletResponse F)
      (isCubeDirichletResponse_unitCubeDirichletResponse (competitorField G))
  have hbound := hL2 _ hmem _ hdiff
  have hfun : (fun x => (unitCubeDirichletResponseGradient F).toField x - G'.toField x) =
      (unitCubeDirichletResponse F -
        unitCubeDirichletResponse (competitorField G)).toH1Function.grad := by
    rw [show (unitCubeDirichletResponse F -
        unitCubeDirichletResponse (competitorField G)).toH1Function =
        (unitCubeDirichletResponse F).toH1Function -
          (unitCubeDirichletResponse (competitorField G)).toH1Function from rfl,
      H1Function.sub_grad, hG']
    rfl
  have hEne : vecCubeLpENorm (originCube d 0) 2 (fun x => F.toField x - G.toField x) ≠ ⊤ :=
    hmem.eLpNorm_ne_top
  have hres : continuousKResidualNorm (unitCubeDirichletResponseGradient F) G' =
      (vecCubeLpENorm (originCube d 0) 2
        (unitCubeDirichletResponse F -
          unitCubeDirichletResponse (competitorField G)).toH1Function.grad).toReal := by
    have hmemX : MemLp (hilbertifyVecField
        (fun x => (unitCubeDirichletResponseGradient F).toField x - G'.toField x)) 2
        (normalizedCubeMeasure (originCube d 0)) := by
      rw [hilbertifyVecField_sub]
      exact (memLp_normalizedCubeMeasure_of_unitCubeField (unitCubeDirichletResponseGradient F)).sub
        (memLp_normalizedCubeMeasure_of_unitCubeField (competitorField G'))
    rw [vecCubeLpENorm_originCube_zero_eq_normalizedEuclideanLpENorm _ (by rw [← hfun]; exact hmemX.aestronglyMeasurable), ← hfun]
    rfl
  have hsrc : continuousKResidualNorm F G =
      (vecCubeLpENorm (originCube d 0) 2 (fun x => F.toField x - G.toField x)).toReal := by
    rw [vecCubeLpENorm_originCube_zero_eq_normalizedEuclideanLpENorm _ hmem.aestronglyMeasurable]
    rfl
  rw [hres, hsrc]
  exact toReal_le_of_le_ofReal_mul hA hEne hbound

/-- **The `H̲^s` bound for the Dirichlet response gradient.** With the `L̲²`
endpoint `hL2` at constant `A` and a competitor transfer realizing the
differentiated endpoint at constant `B`, the real `K`-method gives the
fractional bound in the local normalized norm `cubeHsENorm`. At `s = 1/2` this is the Dirichlet
summand of `e.abstract.response.Hhalf` on the unit centered cube. -/
theorem cubeHsENorm_unitCubeDirichletResponseGradient_le
    (s : FractionalOrder) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hL2 : ∀ H : Vec d → Vec d,
      MemLp (hilbertifyVecField H) 2 (normalizedCubeMeasure (originCube d 0)) →
      ∀ w : H10Function (openCubeSet (originCube d 0)),
        IsCubeDirichletResponse (originCube d 0) H w →
          vecCubeLpENorm (originCube d 0) 2 w.toH1Function.grad ≤
            ENNReal.ofReal A * vecCubeLpENorm (originCube d 0) 2 H)
    (transfer : ContinuousKCompetitor d → ContinuousKCompetitor d)
    (htransfer : ∀ G : ContinuousKCompetitor d,
      (transfer G).toField = (unitCubeDirichletResponseGradient (competitorField G)).toField)
    (hgrad : ∀ G : ContinuousKCompetitor d,
      continuousKGradientNorm (transfer G) ≤ B * continuousKGradientNorm G)
    (F : UnitCubeEuclideanL2Field d) :
    cubeHsENorm (originCube d 0) s.1
        (hilbertifyVecField (unitCubeDirichletResponseGradient F).toField) ≤
      2 * (continuousKEuclideanHsFullENormConstant s d ^ 2 * ENNReal.ofReal (max A B)) *
        cubeHsENorm (originCube d 0) s.1 (hilbertifyVecField F.toField) := by
  have hl2F : (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞)
      (unitCubeDirichletResponseGradient F) ≤
      ENNReal.ofReal A *
        (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) F := by
    rw [← vecCubeLpENorm_originCube_zero_eq_normalizedEuclideanLpENorm (unitCubeDirichletResponseGradient F).toField
        (memLp_normalizedCubeMeasure_of_unitCubeField (unitCubeDirichletResponseGradient F)).aestronglyMeasurable,
      ← vecCubeLpENorm_originCube_zero_eq_normalizedEuclideanLpENorm F.toField
        (memLp_normalizedCubeMeasure_of_unitCubeField F).aestronglyMeasurable]
    exact hL2 F.toField (memLp_normalizedCubeMeasure_of_unitCubeField F) _
      (isCubeDirichletResponse_unitCubeDirichletResponse F)
  have hHs := euclideanHsFullENorm_le_of_endpoints hA hB s transfer
    (fun G => continuousKResidualNorm_unitCubeDirichletResponseGradient_le hA hL2 F G
      (transfer G) (htransfer G)) hgrad hl2F
  calc
    cubeHsENorm (originCube d 0) s.1
        (hilbertifyVecField (unitCubeDirichletResponseGradient F).toField)
        ≤ euclideanHsFullENorm s (unitCubeDirichletResponseGradient F) :=
      cubeHsENorm_le_euclideanHsFullENorm s _
    _ ≤ (continuousKEuclideanHsFullENormConstant s d ^ 2 * ENNReal.ofReal (max A B)) *
          euclideanHsFullENorm s F := hHs
    _ ≤ (continuousKEuclideanHsFullENormConstant s d ^ 2 * ENNReal.ofReal (max A B)) *
          (2 * cubeHsENorm (originCube d 0) s.1 (hilbertifyVecField F.toField)) :=
      mul_le_mul' le_rfl (euclideanHsFullENorm_le_two_mul_cubeHsENorm s F)
    _ = 2 * (continuousKEuclideanHsFullENormConstant s d ^ 2 * ENNReal.ofReal (max A B)) *
          cubeHsENorm (originCube d 0) s.1 (hilbertifyVecField F.toField) := by ring

end Dirichlet

section Neumann

end Neumann

/-! ## The two summands together -/

end

end Sobolev
end SuperdiffusionCLT
