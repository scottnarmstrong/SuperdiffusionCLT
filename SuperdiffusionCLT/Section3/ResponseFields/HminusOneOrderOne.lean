/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.ResponseFields.AprioriAssemblyC
public import SuperdiffusionCLT.Sobolev.CubeSmoothDensityH2B
public import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.EuclideanNormalized
public import Homogenization.Sobolev.Foundations.CubeCalderonZygmund.ScalarPoissonHessianTwo

/-!
# The two cube Poisson potentials of the order-one `Ĥ̲^{-1}` estimate

`Section3/ResponseFields/AprioriAssemblyC.lean` carries the first of the two
standard estimates of Step 4 of the proof of `l.abstract.response.fields`,

`3^{-M}‖v − (v)_{cu_M}‖_{L̲²(cu_M)} ≤ C‖F₀‖_{Ĥ̲^{-1}(cu_M)}`,

in the order-one hatted negative norm, as the hypothesis `hHm1`.
This module and its sibling `HminusOneOrderOneB.lean` discharge it.

## The two potentials

Write `v = u − w` for the difference of the prescribed-flux Neumann response `u`
and the Dirichlet response `w` of the same flux `G`, and `z = v − (v)_{cu_M}`.
The estimate is a duality against two Poisson problems of the cube:

* `ψ`, the mean-zero Neumann potential of `z`: `∫ ∇ψ·∇φ = ∫ z φ` for every
  mean-zero `φ ∈ H¹(cu_M)`.  Testing at `z` itself gives `∫ z² = ∫ ∇v·∇ψ`.
* `θ`, the zero-trace part of `ψ`: the Dirichlet response of the flux `−∇ψ`,
  which satisfies `∫ ∇θ·∇φ = ∫ ∇ψ·∇φ` for every `φ ∈ H¹₀(cu_M)`.  Because `z`
  is mean-zero this makes `θ` the *Dirichlet Poisson potential* of `z`, so its
  Hessian obeys the cube `H²` estimate as well; and because `v` is harmonic
  (`setIntegral_vecDot_grad_responseDifference_eq_zero`) the pairing `∫ ∇v·∇θ`
  vanishes, so `∫ z² = ∫ ∇v·(∇ψ − ∇θ)`.

`∇ψ − ∇θ` is the gradient of the harmonic part of `ψ`; the sibling module pairs
it with `G` through the order-one duality, which is what turns the display into
an `Ĥ̲^{-1}` estimate rather than an `L̲²` one.

## The inputs used here

* Existence of the mean-zero Neumann potential for an arbitrary `L̲²` datum:
  `Homogenization.meanZeroNeumannPoissonSolutionOfCoerciveEstimate`.
* The Neumann `H²` bound on an origin cube:
  `Homogenization.originCubeNeumannW22CalderonZygmund_regularity_qTwo_apply`
  (normalized Frobenius form).  The identification of its carrier with
  `cubeLpENorm Q 2 (HilbertMat.ofMat ∘ hess)` is
  `cubeLpENorm_hessianHilbertMat_eq_ofReal_frobeniusNormalizedL2` below.
* The Dirichlet `H²` bound, already in that carrier:
  `Homogenization.CubeCalderonZygmund.exists_scalarPoisson_hessianHilbertMat_normalizedCubeMeasure_le_two`.
* Solvability of the cube Dirichlet problem for an `L̲²` flux:
  `exists_isCubeDirichletResponse`; this is what produces `θ`, so no separate
  existence theorem for the Dirichlet Poisson problem is needed.
* The cube Poincaré-Wirtinger estimate with its explicit constant:
  `cubeScaleFactor_inv_mul_cubeLpENorm_subAverage_le`.

## Main results

* `cubeLpENorm_hessianHilbertMat_eq_ofReal_frobeniusNormalizedL2`: the weak
  Hessian in the Hilbert-matrix carrier of `vecHatTestH1ENorm`.
* `exists_cubeNeumannPotential`: the mean-zero Neumann potential of a mean-zero
  `L̲²` datum on an origin cube, with its gradient and Hessian bounds.
* `exists_cubeHarmonicPartPotential`: the pair `(ψ, θ)` with all four norm
  bounds and the two pairing identities the sibling module consumes.
* `volumeAverage_vecDot_sub_left`, `volumeAverage_vecDot_sub_right`: bilinearity
  of the normalized cube pairing, through its `L²` realization.
* `exists_orderOneTestPotential`: the smooth mean-zero potential admissible for
  `vecHatNegENormOrderOne` at the level `‖∇a‖_{L̲²(Q)} + 3^{scale}‖∇²a‖_{L̲²(Q)}`, up to
  a prescribed error, attached to an `H¹` function with a weak Hessian.

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

/-! ## Scalar `L̲²` pairings on a cube -/

private theorem volumeAverage_cubeSet_eq_cubeAverage''' (Q : TriadicCube d)
    (f : Vec d → ℝ) : volumeAverage (cubeSet Q) f = cubeAverage Q f := by
  rw [volumeAverage, cubeAverage, volume_cubeSet_toReal]

/-- An `L²(cu)` scalar is normalized-`L̲²` on the cube. -/
theorem memLp_two_normalizedCubeMeasure_of_memScalarL2 {Q : TriadicCube d}
    {f : Vec d → ℝ} (hf : MemScalarL2 (openCubeSet Q) f) :
    MemLp f 2 (normalizedCubeMeasure Q) := by
  rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
  exact hf.smul_measure ENNReal.ofReal_ne_top

/-- The inner product of two scalar `L²(normalizedCubeMeasure Q)` realizations is
the normalized cube average of the product, the manuscript's `⨍_Q f g`. -/
private theorem inner_toLp_scalar {Q : TriadicCube d} {a b : Vec d → ℝ}
    (ha : MemLp a 2 (normalizedCubeMeasure Q))
    (hb : MemLp b 2 (normalizedCubeMeasure Q)) :
    (inner ℝ (ha.toLp a) (hb.toLp b) : ℝ) =
      volumeAverage (cubeSet Q) (fun x => a x * b x) := by
  rw [L2.inner_def, volumeAverage_cubeSet_eq_cubeAverage''',
    cubeAverage_eq_integral_normalizedCubeMeasure]
  refine integral_congr_ae ?_
  filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with x hxa hxb
  rw [hxa, hxb]
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
  ring

private theorem norm_toLp_scalar {Q : TriadicCube d} {a : Vec d → ℝ}
    (ha : MemLp a 2 (normalizedCubeMeasure Q)) :
    ‖ha.toLp a‖ = (Section2.Norms.cubeLpENorm Q 2 a).toReal :=
  Lp.norm_toLp _ ha

/-- **`⨍_Q f² = ‖f‖²_{L̲²(Q)}`.** -/
theorem volumeAverage_mul_self_eq_sq {Q : TriadicCube d} {a : Vec d → ℝ}
    (ha : MemLp a 2 (normalizedCubeMeasure Q)) :
    volumeAverage (cubeSet Q) (fun x => a x * a x) =
      (Section2.Norms.cubeLpENorm Q 2 a).toReal ^ 2 := by
  rw [← inner_toLp_scalar ha ha, real_inner_self_eq_norm_sq, norm_toLp_scalar ha]

/-- **Cauchy-Schwarz for the normalized cube average of a scalar product.** -/
theorem abs_volumeAverage_mul_le_mul {Q : TriadicCube d} {a b : Vec d → ℝ}
    (ha : MemLp a 2 (normalizedCubeMeasure Q))
    (hb : MemLp b 2 (normalizedCubeMeasure Q)) :
    |volumeAverage (cubeSet Q) (fun x => a x * b x)| ≤
      (Section2.Norms.cubeLpENorm Q 2 a).toReal *
        (Section2.Norms.cubeLpENorm Q 2 b).toReal := by
  rw [← inner_toLp_scalar ha hb, ← norm_toLp_scalar ha, ← norm_toLp_scalar hb]
  exact abs_real_inner_le_norm _ _

/-! ## The weak Hessian in the Hilbert-matrix carrier -/

/-- The Hilbert-matrix realization of a weak Hessian is normalized-`L̲²` on the
cube. -/
theorem memLp_hessianHilbertMat (Q : TriadicCube d)
    {v : H1Function (openCubeSet Q)} (H : HasWeakHessianOn (openCubeSet Q) v) :
    MemLp (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) 2
      (normalizedCubeMeasure Q) := by
  rw [MeasureTheory.memLp_piLp_iff]
  intro i
  rw [MeasureTheory.memLp_piLp_iff]
  intro j
  simpa only [Function.comp_apply, HilbertMat.ofMat, HilbertVec.ofVec,
    PiLp.toLp_apply] using H.hess_memLp_normalizedCubeMeasure Q i j

/-- **The `L̲²(Q)` size of a weak Hessian in the Hilbert-matrix carrier is its
normalized Frobenius value.** This is the identification that lets the upstream
Neumann `H²` bound, stated in `HasWeakHessianOn.frobeniusNormalizedL2`, be read
in the carrier of `vecHatTestH1ENorm`. -/
theorem cubeLpENorm_hessianHilbertMat_eq_ofReal_frobeniusNormalizedL2
    (Q : TriadicCube d) {v : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) v) :
    Section2.Norms.cubeLpENorm Q 2
        (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) =
      ENNReal.ofReal (H.frobeniusNormalizedL2 Q) := by
  have hnorm : eLpNorm (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) 2
      (normalizedCubeMeasure Q) =
      eLpNorm H.frobeniusMagnitude 2 (normalizedCubeMeasure Q) := by
    have hm := (memLp_hessianHilbertMat Q H).aestronglyMeasurable
    have hmF : AEStronglyMeasurable H.frobeniusMagnitude (normalizedCubeMeasure Q) :=
      hm.norm.congr (ae_of_all _ fun x =>
        (matrixFrobeniusMagnitude_eq_norm_hilbertMat_ofMat _).symm)
    refine eLpNorm_congr_norm_ae hm hmF (ae_of_all _ fun x => ?_)
    rw [HasWeakHessianOn.frobeniusMagnitude, Real.norm_eq_abs,
      abs_of_nonneg (matrixFrobeniusMagnitude_nonneg (fun i j => H.hess i j x))]
    exact (matrixFrobeniusMagnitude_eq_norm_hilbertMat_ofMat _).symm
  have hfrob : H.frobeniusNormalizedL2 Q =
      (eLpNorm H.frobeniusMagnitude 2 (normalizedCubeMeasure Q)).toReal := by
    rw [HasWeakHessianOn.frobeniusNormalizedL2_eq_frobeniusMagnitudeNormalizedLpNorm]
    change (eLpNorm H.frobeniusMagnitude 2
      (cubeBoundedMeasurableDomain Q).normalizedVolume).toReal = _
    rw [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
  rw [Section2.Norms.cubeLpENorm, hnorm, hfrob,
    ENNReal.ofReal_toReal
      (H.frobeniusMagnitude_memLp_normalizedCubeMeasure Q).eLpNorm_lt_top.ne]

/-! ## Vector `L̲²` pairings, and the passage to the normalized average -/

/-- An `L²(cu)` vector field is normalized-`L̲²` on the cube. -/
theorem memLp_two_hilbertify {Q : TriadicCube d} {F : Vec d → Vec d}
    (hF : MemVectorL2 (openCubeSet Q) F) :
    MemLp (hilbertifyVecField F) 2 (normalizedCubeMeasure Q) := by
  rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
  exact (memHilbertVectorL2_hilbertifyVecField hF).smul_measure ENNReal.ofReal_ne_top

/-- **`⨍_Q |a|² = ‖a‖²_{L̲²(Q)}`.** -/
theorem volumeAverage_vecDot_self_eq_sq {Q : TriadicCube d} {a : Vec d → Vec d}
    (ha : MemLp (hilbertifyVecField a) 2 (normalizedCubeMeasure Q)) :
    volumeAverage (cubeSet Q) (fun x => vecDot (a x) (a x)) =
      (vecCubeLpENorm Q 2 a).toReal ^ 2 := by
  rw [← Section2.Norms.inner_toLp_hilbertifyVecField ha ha,
    real_inner_self_eq_norm_sq, Lp.norm_toLp]
  rw [vecCubeLpENorm, Section2.Norms.cubeLpENorm]

/-- Two integrals over the open cube that agree have the same normalized cube
average. -/
theorem volumeAverage_congr_setIntegral {Q : TriadicCube d} {f g : Vec d → ℝ}
    (h : ∫ x in openCubeSet Q, f x = ∫ x in openCubeSet Q, g x) :
    volumeAverage (cubeSet Q) f = volumeAverage (cubeSet Q) g := by
  rw [volumeAverage_cubeSet_eq_openCubeSet, volumeAverage_cubeSet_eq_openCubeSet,
    volumeAverage, volumeAverage, h]

/-! ## The mean-zero Neumann potential of a mean-zero `L̲²` datum -/

private theorem cubeScaleFactor_pos' (Q : TriadicCube d) : 0 < cubeScaleFactor Q := by
  rw [cubeScaleFactor]
  positivity

/-- **The mean-zero Neumann potential of a mean-zero `L̲²` datum on an origin
cube**, with its two norm bounds: the Poincaré-Wirtinger gradient bound, whose
constant is `3^m` times the dimensional constant of the unit centered cube, and
the Calderón-Zygmund Hessian bound of
`originCubeNeumannW22CalderonZygmund_regularity_qTwo`, read in the Hilbert-matrix
carrier through
`cubeLpENorm_hessianHilbertMat_eq_ofReal_frobeniusNormalizedL2`. -/
theorem exists_cubeNeumannPotential (m : ℤ) {z : Vec d → ℝ}
    (hz : MemLp z 2 (normalizedCubeMeasure (originCube d m)))
    (hzmean : cubeAverage (originCube d m) z = 0) :
    ∃ (ψ : H1MeanZeroFunction (openCubeSet (originCube d m)))
      (H : HasWeakHessianOn (openCubeSet (originCube d m)) ψ.toH1Function),
      (∀ φ : H1MeanZeroFunction (openCubeSet (originCube d m)),
          ∫ x in openCubeSet (originCube d m),
              vecDot (ψ.toH1Function.grad x) (φ.toH1Function.grad x) =
            ∫ x in openCubeSet (originCube d m), z x * φ.toH1Function x) ∧
        vecCubeLpENorm (originCube d m) 2 ψ.toH1Function.grad ≤
          ENNReal.ofReal ((originCubeMeanZeroH1CoerciveEstimate d 0).constant *
              cubeScaleFactor (originCube d m)) *
            Section2.Norms.cubeLpENorm (originCube d m) 2 z ∧
        Section2.Norms.cubeLpENorm (originCube d m) 2
            (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) ≤
          ENNReal.ofReal (originCubeNeumannW22CalderonZygmundConstant d) *
            Section2.Norms.cubeLpENorm (originCube d m) 2 z := by
  have hfluct : cubeFluctuation (originCube d m) z = z := by
    funext x
    show z x - cubeAverage (originCube d m) z = z x
    rw [hzmean, sub_zero]
  have W0 := meanZeroNeumannPoissonSolutionOfCoerciveEstimate (originCube d m) z hz
  have hWeq := W0.equation
  obtain ⟨H, hH⟩ :=
    originCubeNeumannW22CalderonZygmund_regularity_qTwo_apply d m z hz
      ({ w := W0.w
         equation := fun φ => by rw [hfluct]; exact hWeq φ } :
        MeanZeroNeumannPoissonSolution (originCube d m)
          (cubeFluctuation (originCube d m) z))
  have hZfin : Section2.Norms.cubeLpENorm (originCube d m) 2 z ≠ ⊤ :=
    hz.eLpNorm_lt_top.ne
  refine ⟨W0.w, H, hWeq, ?_, ?_⟩
  · -- the Poincaré-Wirtinger gradient bound
    have hgmem : MemLp (hilbertifyVecField W0.w.toH1Function.grad) 2
        (normalizedCubeMeasure (originCube d m)) :=
      memLp_two_hilbertify W0.w.toH1Function.grad_memVectorL2
    have hpmem : MemLp W0.w.toH1Function.toFun 2
        (normalizedCubeMeasure (originCube d m)) :=
      memLp_two_normalizedCubeMeasure_of_memScalarL2 W0.w.toH1Function.memL2
    have hGfin : vecCubeLpENorm (originCube d m) 2 W0.w.toH1Function.grad ≠ ⊤ :=
      hgmem.eLpNorm_lt_top.ne
    have hPfin : Section2.Norms.cubeLpENorm (originCube d m) 2
        W0.w.toH1Function.toFun ≠ ⊤ := hpmem.eLpNorm_lt_top.ne
    have hscale : 0 < cubeScaleFactor (originCube d m) := cubeScaleFactor_pos' _
    have hCP : 0 ≤ (originCubeMeanZeroH1CoerciveEstimate d 0).constant :=
      (originCubeMeanZeroH1CoerciveEstimate d 0).constant_nonneg
    have hG0 : (0 : ℝ) ≤ (vecCubeLpENorm (originCube d m) 2
      W0.w.toH1Function.grad).toReal := ENNReal.toReal_nonneg
    have hZ0 : (0 : ℝ) ≤ (Section2.Norms.cubeLpENorm (originCube d m) 2 z).toReal :=
      ENNReal.toReal_nonneg
    -- the energy identity of the Neumann problem, tested at the potential itself
    have henergy : (vecCubeLpENorm (originCube d m) 2 W0.w.toH1Function.grad).toReal ^ 2
        = volumeAverage (cubeSet (originCube d m))
          (fun x => z x * W0.w.toH1Function x) := by
      rw [← volumeAverage_vecDot_self_eq_sq hgmem]
      exact volumeAverage_congr_setIntegral (hWeq W0.w)
    -- the potential is its own mean-zero normalization
    have hsubfun : W0.w.toH1Function.subAverage.toFun = W0.w.toH1Function.toFun := by
      have hmz : ∫ x in openCubeSet (originCube d m), W0.w.toH1Function.toFun x = 0 :=
        W0.w.meanZero
      have hIA : integralAverage (openCubeSet (originCube d m))
          W0.w.toH1Function.toFun = 0 := by
        show (volume (openCubeSet (originCube d m))).toReal⁻¹ *
          ∫ x in openCubeSet (originCube d m), W0.w.toH1Function.toFun x = 0
        rw [hmz, mul_zero]
      funext x
      show W0.w.toH1Function.subAverage x = W0.w.toH1Function x
      rw [H1Function.subAverage_apply, hIA, sub_zero]
    have hpoincare := cubeScaleFactor_inv_mul_cubeLpENorm_subAverage_le
      (originCube d m) W0.w.toH1Function
    rw [hsubfun] at hpoincare
    have hreal : (cubeScaleFactor (originCube d m))⁻¹ *
        (Section2.Norms.cubeLpENorm (originCube d m) 2 W0.w.toH1Function.toFun).toReal ≤
        (originCubeMeanZeroH1CoerciveEstimate d 0).constant *
          (vecCubeLpENorm (originCube d m) 2 W0.w.toH1Function.grad).toReal := by
      rw [← ENNReal.ofReal_toReal hPfin, ← ENNReal.ofReal_toReal hGfin,
        ← ENNReal.ofReal_mul (le_of_lt (inv_pos.2 hscale)),
        ← ENNReal.ofReal_mul hCP] at hpoincare
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hpoincare
    have hP' : (Section2.Norms.cubeLpENorm (originCube d m) 2
          W0.w.toH1Function.toFun).toReal ≤
        (originCubeMeanZeroH1CoerciveEstimate d 0).constant *
          cubeScaleFactor (originCube d m) *
          (vecCubeLpENorm (originCube d m) 2 W0.w.toH1Function.grad).toReal := by
      have h1 := mul_le_mul_of_nonneg_left hreal (le_of_lt hscale)
      rw [← mul_assoc, mul_inv_cancel₀ hscale.ne', one_mul] at h1
      exact le_trans h1 (le_of_eq (by ring))
    have hCS : (vecCubeLpENorm (originCube d m) 2 W0.w.toH1Function.grad).toReal ^ 2 ≤
        (Section2.Norms.cubeLpENorm (originCube d m) 2 z).toReal *
          (Section2.Norms.cubeLpENorm (originCube d m) 2
            W0.w.toH1Function.toFun).toReal := by
      rw [henergy]
      exact le_trans (le_abs_self _) (abs_volumeAverage_mul_le_mul hz hpmem)
    have hfinal : (vecCubeLpENorm (originCube d m) 2 W0.w.toH1Function.grad).toReal ≤
        (originCubeMeanZeroH1CoerciveEstimate d 0).constant *
            cubeScaleFactor (originCube d m) *
          (Section2.Norms.cubeLpENorm (originCube d m) 2 z).toReal := by
      rcases eq_or_lt_of_le hG0 with hzero | hpos
      · rw [← hzero]
        positivity
      · refine le_of_mul_le_mul_right ?_ hpos
        calc (vecCubeLpENorm (originCube d m) 2 W0.w.toH1Function.grad).toReal *
              (vecCubeLpENorm (originCube d m) 2 W0.w.toH1Function.grad).toReal
            = (vecCubeLpENorm (originCube d m) 2 W0.w.toH1Function.grad).toReal ^ 2 := by
              ring
          _ ≤ (Section2.Norms.cubeLpENorm (originCube d m) 2 z).toReal *
                (Section2.Norms.cubeLpENorm (originCube d m) 2
                  W0.w.toH1Function.toFun).toReal := hCS
          _ ≤ (Section2.Norms.cubeLpENorm (originCube d m) 2 z).toReal *
                ((originCubeMeanZeroH1CoerciveEstimate d 0).constant *
                  cubeScaleFactor (originCube d m) *
                  (vecCubeLpENorm (originCube d m) 2
                    W0.w.toH1Function.grad).toReal) :=
              mul_le_mul_of_nonneg_left hP' hZ0
          _ = (originCubeMeanZeroH1CoerciveEstimate d 0).constant *
                cubeScaleFactor (originCube d m) *
                (Section2.Norms.cubeLpENorm (originCube d m) 2 z).toReal *
                (vecCubeLpENorm (originCube d m) 2
                  W0.w.toH1Function.grad).toReal := by ring
    rw [← ENNReal.ofReal_toReal hGfin, ← ENNReal.ofReal_toReal hZfin,
      ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hfinal
  · -- the Calderón-Zygmund Hessian bound
    have hcent : centeredCubeNormalizedL2 (originCube d m) z hz =
        (Section2.Norms.cubeLpENorm (originCube d m) 2 z).toReal := by
      rw [centeredCubeNormalizedL2_eq_cubeLpNorm, hfluct]
      exact (Section2.Norms.cubeLpENorm_toReal_eq_cubeLpNorm _ _ _).symm
    rw [hcent] at hH
    rw [cubeLpENorm_hessianHilbertMat_eq_ofReal_frobeniusNormalizedL2,
      ← ENNReal.ofReal_toReal hZfin,
      ← ENNReal.ofReal_mul (originCubeNeumannW22CalderonZygmundConstant_nonneg d)]
    exact ENNReal.ofReal_le_ofReal hH

/-! ## The dimensional constant of the cube Dirichlet `H²` estimate -/

/-- The dimensional constant of the cube Dirichlet `H²` estimate at the energy
exponent.  It is a `Classical.choose` constant of the upstream existential
`exists_scalarPoisson_hessianHilbertMat_normalizedCubeMeasure_le_two`, made total
in `d` by the value `0` in dimension zero, where that statement is vacuous. -/
def cubeDirichletHessianConst (d : ℕ) : ℝ≥0∞ :=
  if h : d = 0 then 0
  else
    haveI : NeZero d := ⟨h⟩
    (CubeCalderonZygmund.exists_scalarPoisson_hessianHilbertMat_normalizedCubeMeasure_le_two
      d).choose

theorem cubeDirichletHessianConst_lt_top (d : ℕ) : cubeDirichletHessianConst d < ⊤ := by
  by_cases h : d = 0
  · rw [cubeDirichletHessianConst, dite_eq_left h]
    exact ENNReal.zero_lt_top
  · have : NeZero d := ⟨h⟩
    rw [cubeDirichletHessianConst, dite_eq_right h]
    exact
      (CubeCalderonZygmund.exists_scalarPoisson_hessianHilbertMat_normalizedCubeMeasure_le_two
        d).choose_spec.1

/-- **The cube Dirichlet `H²` estimate at the energy exponent**, with the
constant named. -/
theorem exists_hessianHilbertMat_le_cubeDirichletHessianConst [NeZero d] (m : ℤ)
    {f : Vec d → ℝ} (hf : MemLp f 2 (normalizedCubeMeasure (originCube d m)))
    (u : H10Function (openCubeSet (originCube d m)))
    (hu : CubeDirichletWeakPoissonProblem (originCube d m) u f) :
    ∃ H : HasWeakHessianOn (openCubeSet (originCube d m)) u.toH1Function,
      Section2.Norms.cubeLpENorm (originCube d m) 2
          (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) ≤
        cubeDirichletHessianConst d *
          Section2.Norms.cubeLpENorm (originCube d m) 2 f := by
  have hd0 : d ≠ 0 := NeZero.ne d
  have hval : cubeDirichletHessianConst d =
      (CubeCalderonZygmund.exists_scalarPoisson_hessianHilbertMat_normalizedCubeMeasure_le_two
        d).choose := by
    rw [cubeDirichletHessianConst, dite_eq_right hd0]
  obtain ⟨H, _, hbound⟩ :=
    (CubeCalderonZygmund.exists_scalarPoisson_hessianHilbertMat_normalizedCubeMeasure_le_two
      d).choose_spec.2 m f hf u hu
  exact ⟨H, by rw [hval]; exact hbound⟩

/-! ## The zero-trace part of the Neumann potential -/

/-- **The Poisson potential pair of a mean-zero `L̲²` datum on an origin cube.**

`ψ` is the mean-zero Neumann potential of the datum and `θ` is the Dirichlet
response of the flux `−∇ψ`, that is, the zero-trace part of `ψ`; `∇ψ − ∇θ` is the
gradient of the harmonic part of `ψ`.  Because the datum is mean-zero, `θ` is at
the same time the Dirichlet Poisson potential of the datum, so the cube `H²`
estimate applies to it as well and no separate existence theorem for the
Dirichlet Poisson problem is needed. -/
theorem exists_cubeHarmonicPartPotential [NeZero d] (m : ℤ) {z : Vec d → ℝ}
    (hz : MemLp z 2 (normalizedCubeMeasure (originCube d m)))
    (hzmean : cubeAverage (originCube d m) z = 0) :
    ∃ (ψ : H1MeanZeroFunction (openCubeSet (originCube d m)))
      (θ : H10Function (openCubeSet (originCube d m)))
      (Hpsi : HasWeakHessianOn (openCubeSet (originCube d m)) ψ.toH1Function)
      (Hth : HasWeakHessianOn (openCubeSet (originCube d m)) θ.toH1Function),
      (∀ φ : H1MeanZeroFunction (openCubeSet (originCube d m)),
          ∫ x in openCubeSet (originCube d m),
              vecDot (ψ.toH1Function.grad x) (φ.toH1Function.grad x) =
            ∫ x in openCubeSet (originCube d m), z x * φ.toH1Function x) ∧
        (∀ φ : H10Function (openCubeSet (originCube d m)),
            ∫ x in openCubeSet (originCube d m),
                vecDot (θ.toH1Function.grad x) (φ.toH1Function.grad x) =
              ∫ x in openCubeSet (originCube d m),
                vecDot (ψ.toH1Function.grad x) (φ.toH1Function.grad x)) ∧
        vecCubeLpENorm (originCube d m) 2 ψ.toH1Function.grad ≤
          ENNReal.ofReal ((originCubeMeanZeroH1CoerciveEstimate d 0).constant *
              cubeScaleFactor (originCube d m)) *
            Section2.Norms.cubeLpENorm (originCube d m) 2 z ∧
        vecCubeLpENorm (originCube d m) 2 θ.toH1Function.grad ≤
          ENNReal.ofReal ((originCubeMeanZeroH1CoerciveEstimate d 0).constant *
              cubeScaleFactor (originCube d m)) *
            Section2.Norms.cubeLpENorm (originCube d m) 2 z ∧
        Section2.Norms.cubeLpENorm (originCube d m) 2
            (fun x => HilbertMat.ofMat (fun i j => Hpsi.hess i j x)) ≤
          ENNReal.ofReal (originCubeNeumannW22CalderonZygmundConstant d) *
            Section2.Norms.cubeLpENorm (originCube d m) 2 z ∧
        Section2.Norms.cubeLpENorm (originCube d m) 2
            (fun x => HilbertMat.ofMat (fun i j => Hth.hess i j x)) ≤
          cubeDirichletHessianConst d *
            Section2.Norms.cubeLpENorm (originCube d m) 2 z := by
  obtain ⟨ψ, Hpsi, hψeq, hψgrad, hψhess⟩ := exists_cubeNeumannPotential m hz hzmean
  -- the zero-trace part of `ψ`, as the Dirichlet response of the flux `−∇ψ`
  have hnegmem : MemVectorL2 (openCubeSet (originCube d m))
      (fun x => -ψ.toH1Function.grad x) := by
    simpa only [Pi.neg_def] using ψ.toH1Function.grad_memVectorL2.neg
  obtain ⟨θ, hθresp⟩ := exists_isCubeDirichletResponse (originCube d m) hnegmem
  have hθeq : ∀ φ : H10Function (openCubeSet (originCube d m)),
      ∫ x in openCubeSet (originCube d m),
          vecDot (θ.toH1Function.grad x) (φ.toH1Function.grad x) =
        ∫ x in openCubeSet (originCube d m),
          vecDot (ψ.toH1Function.grad x) (φ.toH1Function.grad x) := by
    intro φ
    have hpt : ∀ x : Vec d,
        vecDot (-ψ.toH1Function.grad x) (φ.toH1Function.grad x) =
          -vecDot (ψ.toH1Function.grad x) (φ.toH1Function.grad x) := by
      intro x
      simp only [vecDot, Pi.neg_apply, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hθresp φ,
      setIntegral_congr_fun (measurableSet_openCubeSet _) (fun x _ => hpt x),
      integral_neg, neg_neg]
  -- the datum has vanishing integral, so `θ` solves the Dirichlet Poisson problem
  have hzL2 : MemScalarL2 (openCubeSet (originCube d m)) z :=
    memL2On_openCubeSet_of_memLp_normalizedCubeMeasure (originCube d m) hz
  have hzint : IntegrableOn z (openCubeSet (originCube d m)) volume :=
    hzL2.integrable (by norm_num)
  have hzint0 : ∫ x in openCubeSet (originCube d m), z x = 0 := by
    have h : (cubeVolume (originCube d m))⁻¹ *
        ∫ x in cubeSet (originCube d m), z x = 0 := hzmean
    have hne : (cubeVolume (originCube d m))⁻¹ ≠ 0 :=
      inv_ne_zero (cubeVolume_pos (originCube d m)).ne'
    have h2 : ∫ x in cubeSet (originCube d m), z x = 0 := by
      rcases mul_eq_zero.1 h with h' | h'
      · exact absurd h' hne
      · exact h'
    rwa [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] at h2
  have hθpoisson : CubeDirichletWeakPoissonProblem (originCube d m) θ z := by
    intro φ
    rw [hθeq φ]
    have hmz := hψeq φ.toH1Function.toMeanZero
    rw [show (φ.toH1Function.toMeanZero).toH1Function.grad = φ.toH1Function.grad from
      funext (fun x => H1Function.toMeanZero_grad _ x)] at hmz
    rw [hmz]
    have hprod : IntegrableOn (fun x => z x * φ.toH1Function.toFun x)
        (openCubeSet (originCube d m)) volume := by
      exact hzL2.integrable_mul φ.toH1Function.memL2
    have hsplit : ∀ x : Vec d,
        z x * (φ.toH1Function.toMeanZero).toH1Function.toFun x =
          z x * φ.toH1Function.toFun x -
            integralAverage (openCubeSet (originCube d m)) φ.toH1Function.toFun * z x := by
      intro x
      rw [H1Function.toMeanZero_apply]
      ring
    rw [setIntegral_congr_fun (measurableSet_openCubeSet _) (fun x _ => hsplit x),
      integral_sub hprod (hzint.const_mul _), integral_const_mul, hzint0, mul_zero,
      sub_zero]
  obtain ⟨Hth, hθhess⟩ :=
    exists_hessianHilbertMat_le_cubeDirichletHessianConst m hz θ hθpoisson
  -- the energy comparison `‖∇θ‖ ≤ ‖∇ψ‖`
  have hgψ : MemLp (hilbertifyVecField ψ.toH1Function.grad) 2
      (normalizedCubeMeasure (originCube d m)) :=
    memLp_two_hilbertify ψ.toH1Function.grad_memVectorL2
  have hgθ : MemLp (hilbertifyVecField θ.toH1Function.grad) 2
      (normalizedCubeMeasure (originCube d m)) :=
    memLp_two_hilbertify θ.toH1Function.grad_memVectorL2
  have hψfin : vecCubeLpENorm (originCube d m) 2 ψ.toH1Function.grad ≠ ⊤ :=
    hgψ.eLpNorm_lt_top.ne
  have hθfin : vecCubeLpENorm (originCube d m) 2 θ.toH1Function.grad ≠ ⊤ :=
    hgθ.eLpNorm_lt_top.ne
  have hθnorm : vecCubeLpENorm (originCube d m) 2 θ.toH1Function.grad ≤
      vecCubeLpENorm (originCube d m) 2 ψ.toH1Function.grad := by
    have hen : (vecCubeLpENorm (originCube d m) 2 θ.toH1Function.grad).toReal ^ 2 =
        volumeAverage (cubeSet (originCube d m))
          (fun x => vecDot (ψ.toH1Function.grad x) (θ.toH1Function.grad x)) := by
      rw [← volumeAverage_vecDot_self_eq_sq hgθ]
      exact volumeAverage_congr_setIntegral (hθeq θ)
    have hCS : (vecCubeLpENorm (originCube d m) 2 θ.toH1Function.grad).toReal ^ 2 ≤
        (vecCubeLpENorm (originCube d m) 2 ψ.toH1Function.grad).toReal *
          (vecCubeLpENorm (originCube d m) 2 θ.toH1Function.grad).toReal := by
      rw [hen]
      exact le_trans (le_abs_self _)
        (Section2.Norms.abs_volumeAverage_vecDot_le_mul hgψ hgθ)
    have hreal : (vecCubeLpENorm (originCube d m) 2 θ.toH1Function.grad).toReal ≤
        (vecCubeLpENorm (originCube d m) 2 ψ.toH1Function.grad).toReal := by
      rcases eq_or_lt_of_le
        (ENNReal.toReal_nonneg :
          (0 : ℝ) ≤ (vecCubeLpENorm (originCube d m) 2 θ.toH1Function.grad).toReal)
        with hzero | hpos
      · rw [← hzero]
        exact ENNReal.toReal_nonneg
      · refine le_of_mul_le_mul_right ?_ hpos
        calc (vecCubeLpENorm (originCube d m) 2 θ.toH1Function.grad).toReal *
              (vecCubeLpENorm (originCube d m) 2 θ.toH1Function.grad).toReal
            = (vecCubeLpENorm (originCube d m) 2 θ.toH1Function.grad).toReal ^ 2 := by
              ring
          _ ≤ (vecCubeLpENorm (originCube d m) 2 ψ.toH1Function.grad).toReal *
                (vecCubeLpENorm (originCube d m) 2 θ.toH1Function.grad).toReal := hCS
    exact (ENNReal.toReal_le_toReal hθfin hψfin).1 hreal
  exact ⟨ψ, θ, Hpsi, Hth, hψeq, hθeq, hψgrad, le_trans hθnorm hψgrad, hψhess, hθhess⟩

/-! ## Bilinearity of the normalized cube pairing -/

theorem vecDot_comm' (a b : Vec d) : vecDot a b = vecDot b a := by
  simp only [vecDot]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

private theorem toLp_hilbertifyVecField_sub {Q : TriadicCube d} {a b : Vec d → Vec d}
    (ha : MemLp (hilbertifyVecField a) 2 (normalizedCubeMeasure Q))
    (hb : MemLp (hilbertifyVecField b) 2 (normalizedCubeMeasure Q))
    (hab : MemLp (hilbertifyVecField (fun x => a x - b x)) 2
      (normalizedCubeMeasure Q)) :
    hab.toLp (hilbertifyVecField (fun x => a x - b x)) =
      ha.toLp (hilbertifyVecField a) - hb.toLp (hilbertifyVecField b) := by
  rw [← MemLp.toLp_sub]
  exact MemLp.toLp_congr hab (ha.sub hb)
    (Filter.EventuallyEq.of_eq (Section2.Norms.hilbertifyVecField_sub' a b))

private theorem memLp_hilbertifyVecField_sub {Q : TriadicCube d} {a b : Vec d → Vec d}
    (ha : MemLp (hilbertifyVecField a) 2 (normalizedCubeMeasure Q))
    (hb : MemLp (hilbertifyVecField b) 2 (normalizedCubeMeasure Q)) :
    MemLp (hilbertifyVecField (fun x => a x - b x)) 2 (normalizedCubeMeasure Q) := by
  rw [Section2.Norms.hilbertifyVecField_sub']
  exact ha.sub hb

/-- **The normalized cube pairing is additive in its first argument.** -/
theorem volumeAverage_vecDot_sub_left {Q : TriadicCube d} {a b c : Vec d → Vec d}
    (ha : MemLp (hilbertifyVecField a) 2 (normalizedCubeMeasure Q))
    (hb : MemLp (hilbertifyVecField b) 2 (normalizedCubeMeasure Q))
    (hc : MemLp (hilbertifyVecField c) 2 (normalizedCubeMeasure Q)) :
    volumeAverage (cubeSet Q) (fun x => vecDot (a x - b x) (c x)) =
      volumeAverage (cubeSet Q) (fun x => vecDot (a x) (c x)) -
        volumeAverage (cubeSet Q) (fun x => vecDot (b x) (c x)) := by
  have hab := memLp_hilbertifyVecField_sub ha hb
  rw [← Section2.Norms.inner_toLp_hilbertifyVecField hab hc,
    ← Section2.Norms.inner_toLp_hilbertifyVecField ha hc,
    ← Section2.Norms.inner_toLp_hilbertifyVecField hb hc,
    toLp_hilbertifyVecField_sub ha hb hab, inner_sub_left]

/-- **The normalized cube pairing is additive in its second argument.** -/
theorem volumeAverage_vecDot_sub_right {Q : TriadicCube d} {a b c : Vec d → Vec d}
    (ha : MemLp (hilbertifyVecField a) 2 (normalizedCubeMeasure Q))
    (hb : MemLp (hilbertifyVecField b) 2 (normalizedCubeMeasure Q))
    (hc : MemLp (hilbertifyVecField c) 2 (normalizedCubeMeasure Q)) :
    volumeAverage (cubeSet Q) (fun x => vecDot (a x) (b x - c x)) =
      volumeAverage (cubeSet Q) (fun x => vecDot (a x) (b x)) -
        volumeAverage (cubeSet Q) (fun x => vecDot (a x) (c x)) := by
  have hbc := memLp_hilbertifyVecField_sub hb hc
  rw [← Section2.Norms.inner_toLp_hilbertifyVecField ha hbc,
    ← Section2.Norms.inner_toLp_hilbertifyVecField ha hb,
    ← Section2.Norms.inner_toLp_hilbertifyVecField ha hc,
    toLp_hilbertifyVecField_sub hb hc hbc, inner_sub_right]

/-! ## Smoothness of the classical Jacobian of a smooth gradient -/

private theorem contDiff_euclideanGradient_apply' {g : Vec d → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => euclideanGradient g y i) := by
  have hfd : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => fderiv ℝ g y) :=
    hg.fderiv_right (by simp)
  exact hfd.clm_apply contDiff_const

private theorem continuous_hilbertMat_euclideanGradientJacobian {g : Vec d → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    Continuous (fun x : Vec d =>
      HilbertMat.ofMat (Section2.Norms.euclideanGradientJacobian g x)) := by
  have hcont : Continuous
      (fun x : Vec d => (Section2.Norms.euclideanGradientJacobian g x : Mat d)) := by
    refine continuous_pi fun i => continuous_pi fun _ => ?_
    have h : Continuous (fun x : Vec d =>
        fderiv ℝ (fun y : Vec d => euclideanGradient g y i) x) :=
      (contDiff_euclideanGradient_apply' hg i).continuous_fderiv
        (by simp)
    exact h.clm_apply continuous_const
  exact ((HilbertMat.continuousLinearEquivMat d).symm).continuous.comp hcont

private theorem matrixFrobeniusMagnitude_sub_eq_norm (M N : Mat d) :
    matrixFrobeniusMagnitude (fun i j => M i j - N i j)
      = ‖HilbertMat.ofMat M - HilbertMat.ofMat N‖ := by
  refine (matrixFrobeniusMagnitude_eq_norm_hilbertMat_ofMat _).trans ?_
  congr 1

private theorem threePow_scale_eq_cubeScaleFactor (Q : TriadicCube d) :
    (3 : ℝ) ^ ((Q.scale : ℝ)) = cubeScaleFactor Q := by
  rw [cubeScaleFactor, Real.rpow_intCast]

/-! ## The smooth order-one test potential attached to an `H²` potential -/

/-- **The order-one test potential.** An `H¹` function on the cube carrying a
weak Hessian is approximated, in the `L̲²` gradient norm and to within `eps`, by a
smooth mean-zero potential admissible for `vecHatNegENormOrderOne` at the level
`‖∇a‖_{L̲²(Q)} + 3^{scale}‖∇²a‖_{L̲²(Q)} + (1 + 3^{scale}) eps`.  The approximants
are those of `Sobolev.exists_cubeH2MeanZeroSmoothApprox`; what is added here is
the passage from the two approximation bounds to the test-class level. -/
theorem exists_orderOneTestPotential {Q : TriadicCube d}
    {a : H1Function (openCubeSet Q)} (H : HasWeakHessianOn (openCubeSet Q) a)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ g : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ volumeAverage (cubeSet Q) g = 0 ∧
      Section2.Norms.vecHatTestH1ENorm Q g ≤
        ENNReal.ofReal ((vecCubeLpENorm Q 2 a.grad).toReal +
          cubeScaleFactor Q * (Section2.Norms.cubeLpENorm Q 2
            (fun x => HilbertMat.ofMat (fun i j => H.hess i j x))).toReal +
          (1 + cubeScaleFactor Q) * eps) ∧
      MemLp (hilbertifyVecField (euclideanGradient g)) 2 (normalizedCubeMeasure Q) ∧
      MemLp (hilbertifyVecField (fun x => euclideanGradient g x - a.grad x)) 2
        (normalizedCubeMeasure Q) ∧
      vecCubeLpENorm Q 2 (fun x => euclideanGradient g x - a.grad x) ≤
        ENNReal.ofReal eps := by
  obtain ⟨g, hgc, hgmean, hgclose, hgjac⟩ :=
    Sobolev.exists_cubeH2MeanZeroSmoothApprox H eps heps
  rw [Section2.Norms.vecGradient_eq_euclideanGradient] at hgclose hgjac
  have hAmem : MemLp (hilbertifyVecField a.grad) 2 (normalizedCubeMeasure Q) :=
    memLp_two_hilbertify a.grad_memVectorL2
  have hHmem := memLp_hessianHilbertMat Q H
  have hDmem : MemLp (hilbertifyVecField (fun x => euclideanGradient g x - a.grad x))
      2 (normalizedCubeMeasure Q) := by
    exact MeasureTheory.memLp_iff.mpr (lt_of_le_of_lt hgclose ENNReal.ofReal_lt_top)
  -- the gradient half of the level
  have hgrad : vecCubeLpENorm Q 2 (euclideanGradient g) ≤
      vecCubeLpENorm Q 2 a.grad + ENNReal.ofReal eps := by
    have heq : (fun x => (euclideanGradient g x - a.grad x) + a.grad x)
        = euclideanGradient g := by
      funext x
      funext i
      show (euclideanGradient g x i - a.grad x i) + a.grad x i = euclideanGradient g x i
      ring
    have htri := vecCubeLpENorm_add_le (Q := Q) (q := 2)
      (F := fun x => euclideanGradient g x - a.grad x) (G := a.grad) (by norm_num)
      hDmem.aestronglyMeasurable hAmem.aestronglyMeasurable
    rw [heq] at htri
    exact le_trans htri (le_trans (le_of_eq (add_comm _ _)) (add_le_add le_rfl hgclose))
  have hEmem : MemLp (hilbertifyVecField (euclideanGradient g)) 2
      (normalizedCubeMeasure Q) :=
    MeasureTheory.memLp_iff.mpr (lt_of_le_of_lt hgrad
        (ENNReal.add_lt_top.2 ⟨hAmem.eLpNorm_lt_top, ENNReal.ofReal_lt_top⟩))
  refine ⟨g, hgc, by rw [volumeAverage_cubeSet_eq_cubeAverage''', hgmean], ?_, hEmem,
    hDmem, hgclose⟩
  -- the Hessian half of the level
  have hjaceq : Section2.Norms.jacobianDistENorm Q (euclideanGradient g)
        (fun x i j => H.hess i j x) =
      Section2.Norms.cubeLpENorm Q 2 (fun x =>
        HilbertMat.ofMat (Section2.Norms.euclideanGradientJacobian g x) -
          HilbertMat.ofMat (fun i j => H.hess i j x)) := by
    unfold Section2.Norms.jacobianDistENorm
    rw [Section2.Norms.cubeLpENorm,
      Section2.Norms.cubeLpENorm]
    have hdiff := ((continuous_hilbertMat_euclideanGradientJacobian hgc).aestronglyMeasurable).sub
      hHmem.aestronglyMeasurable
    refine eLpNorm_congr_norm_ae (hdiff.norm.congr (ae_of_all _ fun x => ?_)) hdiff
      (ae_of_all _ fun x => ?_)
    · exact (matrixFrobeniusMagnitude_sub_eq_norm
        (Section2.Norms.euclideanGradientJacobian g x) (fun i j => H.hess i j x)).symm
    rw [Real.norm_eq_abs]
    exact (abs_of_nonneg (matrixFrobeniusMagnitude_nonneg _)).trans
      (matrixFrobeniusMagnitude_sub_eq_norm
        (Section2.Norms.euclideanGradientJacobian g x) (fun i j => H.hess i j x))
  have hgjac' : Section2.Norms.cubeLpENorm Q 2 (fun x =>
      HilbertMat.ofMat (Section2.Norms.euclideanGradientJacobian g x) -
        HilbertMat.ofMat (fun i j => H.hess i j x)) ≤ ENNReal.ofReal eps := by
    rw [← hjaceq]
    exact hgjac
  have hJmem : MemLp (fun x =>
      HilbertMat.ofMat (Section2.Norms.euclideanGradientJacobian g x) -
        HilbertMat.ofMat (fun i j => H.hess i j x)) 2 (normalizedCubeMeasure Q) :=
    MeasureTheory.memLp_iff.mpr (lt_of_le_of_lt hgjac' ENNReal.ofReal_lt_top)
  have hjac : Section2.Norms.cubeLpENorm Q 2
        (fun x => HilbertMat.ofMat (Section2.Norms.euclideanGradientJacobian g x)) ≤
      Section2.Norms.cubeLpENorm Q 2
          (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) +
        ENNReal.ofReal eps := by
    have heq : ((fun x =>
          HilbertMat.ofMat (Section2.Norms.euclideanGradientJacobian g x) -
            HilbertMat.ofMat (fun i j => H.hess i j x)) +
        fun x => HilbertMat.ofMat (fun i j => H.hess i j x))
        = fun x => HilbertMat.ofMat (Section2.Norms.euclideanGradientJacobian g x) := by
      funext x
      show (HilbertMat.ofMat (Section2.Norms.euclideanGradientJacobian g x) -
        HilbertMat.ofMat (fun i j => H.hess i j x)) +
          HilbertMat.ofMat (fun i j => H.hess i j x) = _
      abel
    have htri := Section2.Norms.cubeLpENorm_add_le (Q := Q) (q := 2)
      (f := fun x => HilbertMat.ofMat (Section2.Norms.euclideanGradientJacobian g x) -
        HilbertMat.ofMat (fun i j => H.hess i j x))
      (g := fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) (by norm_num)
      hJmem.aestronglyMeasurable hHmem.aestronglyMeasurable
    rw [heq] at htri
    exact le_trans htri (le_trans (le_of_eq (add_comm _ _)) (add_le_add le_rfl hgjac'))
  -- combining the two halves
  have hAfin : vecCubeLpENorm Q 2 a.grad ≠ ⊤ := hAmem.eLpNorm_lt_top.ne
  have hHfin : Section2.Norms.cubeLpENorm Q 2
      (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) ≠ ⊤ :=
    hHmem.eLpNorm_lt_top.ne
  have hsc : (0 : ℝ) ≤ cubeScaleFactor Q :=
    le_of_lt (by rw [cubeScaleFactor]; positivity)
  set A : ℝ := (vecCubeLpENorm Q 2 a.grad).toReal with hAdef
  set C : ℝ := (Section2.Norms.cubeLpENorm Q 2
    (fun x => HilbertMat.ofMat (fun i j => H.hess i j x))).toReal with hCdef
  have hA0 : (0 : ℝ) ≤ A := ENNReal.toReal_nonneg
  have hC0 : (0 : ℝ) ≤ C := ENNReal.toReal_nonneg
  have hAval : vecCubeLpENorm Q 2 a.grad = ENNReal.ofReal A :=
    (ENNReal.ofReal_toReal hAfin).symm
  have hCval : Section2.Norms.cubeLpENorm Q 2
      (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) = ENNReal.ofReal C :=
    (ENNReal.ofReal_toReal hHfin).symm
  rw [Section2.Norms.vecHatTestH1ENorm, threePow_scale_eq_cubeScaleFactor]
  refine le_trans (add_le_add hgrad (mul_le_mul' le_rfl hjac)) (le_of_eq ?_)
  rw [hAval, hCval, ← ENNReal.ofReal_add hA0 heps.le,
    ← ENNReal.ofReal_add hC0 heps.le, ← ENNReal.ofReal_mul hsc,
    ← ENNReal.ofReal_add (by linarith only [hA0, heps.le])
      (mul_nonneg hsc (by linarith only [hC0, heps.le]))]
  congr 1
  ring

end

end ResponseFields
end Section3
end SuperdiffusionCLT
