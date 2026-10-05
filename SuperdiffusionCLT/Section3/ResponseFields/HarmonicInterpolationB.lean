/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.ResponseFields.HarmonicInterpolation
public import SuperdiffusionCLT.Section3.ResponseFields.AprioriAssemblyB

/-!
# Step 3 of `l.abstract.response.fields`: Caccioppoli, and the interpolation

This file completes Step 3 of the proof: it tests the equation against
`(v − (v)_{cu_M})φ²`, obtains the printed
Caccioppoli inequality, combines it with the boundary-layer
estimates of `HarmonicInterpolation.lean` and balances in `ε`, and discharges
the hypothesis `hharm` of
`exists_responseDifferenceL2Clause` in its exact printed shape.
-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Section3
namespace ResponseFields

open Homogenization
open Homogenization.Book.Ch02
open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The squared `L̲²(Q)` norm as a cube integral -/

private theorem eLpNorm_two_sq'' {α : Type*} {E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] (ν : Measure α) (f : α → E) (hf : AEStronglyMeasurable f ν) :
    eLpNorm f 2 ν ^ (2 : ℕ) = ∫⁻ a, ‖f a‖ₑ ^ (2 : ℕ) ∂ν := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf,
    ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
  norm_num

private theorem enorm_ofVec_sq' (y : Vec d) :
    ‖HilbertVec.ofVec y‖ₑ ^ (2 : ℕ) = ENNReal.ofReal (vecDot y y) := by
  have hnorm : ‖HilbertVec.ofVec y‖ ^ (2 : ℕ) = vecDot y y := by
    rw [HilbertVec.norm_sq_eq_sum_sq]
    simp [vecDot, sq]
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), hnorm]

/-- The square of `‖F‖_{L̲²(Q)}` as the volume-normalized cube integral of
`|F|²`, for a field that is square integrable on the open cube. -/
private theorem vecCubeLpENorm_two_sq_eq_ofReal {Q : TriadicCube d} {F : Vec d → Vec d}
    (hF : MemVectorL2 (openCubeSet Q) F) :
    vecCubeLpENorm Q 2 F ^ (2 : ℕ) =
      ENNReal.ofReal ((cubeVolume Q)⁻¹ *
        ∫ x in openCubeSet Q, vecDot (F x) (F x)) := by
  have hint : IntegrableOn (fun x => vecDot (F x) (F x)) (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 hF hF
  have hvol : 0 < cubeVolume Q := cubeVolume_pos Q
  have hnn : (0 : Vec d → ℝ) ≤ᵐ[volume.restrict (openCubeSet Q)]
      fun x => vecDot (F x) (F x) :=
    Filter.Eventually.of_forall (fun x => by
      simpa [vecDot, sq] using Finset.sum_nonneg
        (fun i (_ : i ∈ Finset.univ) => mul_self_nonneg (F x i)))
  have hmeas : AEStronglyMeasurable (hilbertifyVecField F) (normalizedCubeMeasure Q) := by
    rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
    exact (memHilbertVectorL2_hilbertifyVecField hF).aestronglyMeasurable.smul_measure _
  rw [vecCubeLpENorm, Section2.Norms.cubeLpENorm, eLpNorm_two_sq'' _ _ hmeas,
    normalizedCubeMeasure, cubeMeasure, lintegral_smul_measure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  have hpt : ∀ x : Vec d, ‖hilbertifyVecField F x‖ₑ ^ (2 : ℕ) =
      ENNReal.ofReal (vecDot (F x) (F x)) := fun x => enorm_ofVec_sq' (F x)
  rw [lintegral_congr hpt,
    ← ofReal_integral_eq_lintegral_ofReal hint hnn,
    smul_eq_mul, ← ENNReal.ofReal_mul (le_of_lt (inv_pos.2 hvol))]

/-! ## The Caccioppoli inequality -/

variable {Q : TriadicCube d} {ε : ℝ}

private theorem cubeScaleFactor_pos'' (Q : TriadicCube d) : 0 < cubeScaleFactor Q := by
  simpa [cubeScaleFactor] using (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)

private theorem collarBound_nonneg (Q : TriadicCube d) (hε0 : 0 < ε) :
    (0 : ℝ) ≤ collarCutoffGradientConst d * ε⁻¹ * (cubeScaleFactor Q)⁻¹ :=
  mul_nonneg (mul_nonneg (collarCutoffGradientConst_nonneg d) (inv_pos.2 hε0).le)
    (inv_pos.2 (cubeScaleFactor_pos'' Q)).le

private theorem memVectorL2_collarCutoff_smul (Q : TriadicCube d) (hε0 : 0 < ε)
    (hεh : ε < 1 / 2) {F : Vec d → Vec d}
    (hF : MemVectorL2 (openCubeSet Q) F) :
    MemVectorL2 (openCubeSet Q) (fun x => collarCutoff Q ε x • F x) := by
  refine hF.mono
    (((collarCutoff_continuous Q hε0 hεh).measurable.aestronglyMeasurable).smul
      hF.aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun x => ?_))
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (collarCutoff_nonneg Q ε x)]
  exact mul_le_of_le_one_left (norm_nonneg _) (collarCutoff_le_one Q ε x)

private theorem memVectorL2_smul_gradCollarCutoff (Q : TriadicCube d) (hε0 : 0 < ε)
    (hεh : ε < 1 / 2) {g : Vec d → ℝ}
    (hg : MemLp g 2 (volumeMeasureOn (openCubeSet Q))) :
    MemVectorL2 (openCubeSet Q) (fun x => g x • gradCollarCutoff Q ε x) := by
  have hM := collarBound_nonneg (d := d) Q hε0
  have hbound : ∀ x : Vec d, ‖gradCollarCutoff Q ε x‖ ≤
      collarCutoffGradientConst d * ε⁻¹ * (cubeScaleFactor Q)⁻¹ := fun x =>
    le_trans (norm_le_vecNorm (gradCollarCutoff Q ε x))
      (vecNorm_gradCollarCutoff_le Q hε0 hεh x)
  refine (hg.const_mul (collarCutoffGradientConst d * ε⁻¹ *
      (cubeScaleFactor Q)⁻¹)).mono
      (hg.aestronglyMeasurable.smul
        ((gradCollarCutoff_continuous Q hε0 hεh).measurable.aestronglyMeasurable))
      (Filter.Eventually.of_forall (fun x => ?_))
  rw [norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg hM,
    mul_comm]
  exact mul_le_mul_of_nonneg_right (hbound x) (abs_nonneg (g x))

private theorem le_of_sq_le_sq'' {x y : ℝ≥0∞} (h : x ^ (2 : ℕ) ≤ y ^ (2 : ℕ)) : x ≤ y := by
  have hx : x ^ (2 : ℕ) = x ^ ((2 : ℝ)) := by
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  have hy : y ^ (2 : ℕ) = y ^ ((2 : ℝ)) := by
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  rw [hx, hy] at h
  have hh := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2)
  rwa [← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    show (2 : ℝ) * ((1 : ℝ) / 2) = 1 by norm_num,
    ENNReal.rpow_one, ENNReal.rpow_one] at hh

/-- The integrand produced by testing against `(v − (v)_{cu_M})φ²`: the weak
gradient of the test function pairs with `∇v` into `|φ∇v|² + 2 φ∇v·(v −
(v)_{cu_M})∇φ`. -/
private theorem vecDot_test_expand (Q : TriadicCube d) (hε0 : 0 < ε)
    (hεh : ε < 1 / 2) (v : H1Function (openCubeSet Q)) (x : Vec d) :
    vecDot (v.grad x)
        (fun j => collarCutoff Q ε x * collarCutoff Q ε x * v.subAverage.grad x j +
          v.subAverage.toFun x *
            (fderiv ℝ (fun y => collarCutoff Q ε y * collarCutoff Q ε y) x)
              (basisVec j)) =
      vecDot (collarCutoff Q ε x • v.grad x) (collarCutoff Q ε x • v.grad x) +
        2 * vecDot (collarCutoff Q ε x • v.grad x)
          (v.subAverage.toFun x • gradCollarCutoff Q ε x) := by
  have hdiff : DifferentiableAt ℝ (collarCutoff Q ε) x :=
    ((collarCutoff_smooth Q hε0 hεh).differentiable
      (by simp)).differentiableAt
  have hfd : ∀ j : Fin d,
      (fderiv ℝ (fun y => collarCutoff Q ε y * collarCutoff Q ε y) x) (basisVec j) =
        2 * collarCutoff Q ε x * gradCollarCutoff Q ε x j := by
    intro j
    show (fderiv ℝ (collarCutoff Q ε * collarCutoff Q ε) x) (basisVec j) =
      2 * collarCutoff Q ε x * gradCollarCutoff Q ε x j
    rw [fderiv_mul hdiff hdiff]
    simp only [add_apply, FunLike.coe_smul,
      Pi.smul_apply, smul_eq_mul, gradCollarCutoff]
    ring
  simp only [vecDot, Pi.smul_apply, smul_eq_mul, hfd, H1Function.grad_subAverage]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-- **The Caccioppoli inequality**: testing `Δv = 0` against
`(v − (v)_{cu_M})φ²` gives

> `‖φ∇v‖_{L̲²(cu_M)}² ≤ 4‖(v − (v)_{cu_M})∇φ‖_{L̲²(cu_M)}²`.

`hharm` is the weak form of `Δv = 0` in `cu_M`, tested against `H¹₀(cu_M)`. -/
theorem vecCubeLpENorm_two_collarCutoff_smul_grad_le (Q : TriadicCube d)
    (hε0 : 0 < ε) (hεh : ε < 1 / 2) (v : H1Function (openCubeSet Q))
    (hharm : ∀ φ : H10Function (openCubeSet Q),
      ∫ x in openCubeSet Q, vecDot (v.grad x) (φ.toH1Function.grad x) = 0) :
    vecCubeLpENorm Q 2 (fun x => collarCutoff Q ε x • v.grad x) ≤
      2 * vecCubeLpENorm Q 2
        (fun x => v.subAverage.toFun x • gradCollarCutoff Q ε x) := by
  classical
  have hU : IsOpenBoundedConvexDomain (openCubeSet Q) :=
    isOpenBoundedConvexDomain_openCubeSet Q
  have hψ : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => collarCutoff Q ε x * collarCutoff Q ε x) :=
    (collarCutoff_smooth Q hε0 hεh).mul (collarCutoff_smooth Q hε0 hεh)
  have hψcs : HasCompactSupport
      (fun x => collarCutoff Q ε x * collarCutoff Q ε x) :=
    (collarCutoff_hasCompactSupport Q hε0 hεh).mul_right
  have hsupp : Function.support (fun x => collarCutoff Q ε x * collarCutoff Q ε x) ⊆
      Function.support (collarCutoff Q ε) := by
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro h0
    exact hx (by rw [h0]; ring)
  have hψsub : tsupport (fun x => collarCutoff Q ε x * collarCutoff Q ε x) ⊆
      openCubeSet Q :=
    le_trans (closure_mono hsupp) (collarCutoff_tsupport_subset Q hε0 hεh)
  have hgradv : MemVectorL2 (openCubeSet Q) v.grad := v.grad_memVectorL2
  have ha : MemVectorL2 (openCubeSet Q)
      (fun x => collarCutoff Q ε x • v.grad x) :=
    memVectorL2_collarCutoff_smul Q hε0 hεh hgradv
  have hb : MemVectorL2 (openCubeSet Q)
      (fun x => v.subAverage.toFun x • gradCollarCutoff Q ε x) :=
    memVectorL2_smul_gradCollarCutoff Q hε0 hεh v.subAverage.memL2
  have haa := integrableOn_vecDot_of_memVectorL2 ha ha
  have hab := integrableOn_vecDot_of_memVectorL2 ha hb
  have hbb := integrableOn_vecDot_of_memVectorL2 hb hb
  have hW := hharm (v.subAverage.mulContDiffHasCompactSupportToH10 hU hψ hψcs hψsub)
  have hWg := WeakPoissonEquationOn.mulContDiffHasCompactSupportToH10_grad_ae
    v.subAverage hU hψ hψcs hψsub
  -- the tested identity
  have hzero : (∫ x in openCubeSet Q,
        vecDot (collarCutoff Q ε x • v.grad x) (collarCutoff Q ε x • v.grad x)) +
      2 * ∫ x in openCubeSet Q,
        vecDot (collarCutoff Q ε x • v.grad x)
          (v.subAverage.toFun x • gradCollarCutoff Q ε x) = 0 := by
    have hcongr : ∫ x in openCubeSet Q,
          vecDot (v.grad x)
            ((v.subAverage.mulContDiffHasCompactSupportToH10 hU hψ hψcs
              hψsub).toH1Function.grad x) =
        ∫ x in openCubeSet Q,
          (vecDot (collarCutoff Q ε x • v.grad x) (collarCutoff Q ε x • v.grad x) +
            2 * vecDot (collarCutoff Q ε x • v.grad x)
              (v.subAverage.toFun x • gradCollarCutoff Q ε x)) := by
      refine integral_congr_ae ?_
      filter_upwards [hWg] with x hx
      rw [hx]
      exact vecDot_test_expand Q hε0 hεh v x
    rw [hcongr, integral_add haa (hab.const_mul 2), integral_const_mul] at hW
    exact hW
  -- testing the square of `φ∇v + 2(v − (v)_{cu_M})∇φ` against itself
  have hnn : ∀ y : Vec d, (0 : ℝ) ≤ vecDot y y := by
    intro y
    simpa [vecDot] using
      Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => mul_self_nonneg (y i))
  have hptw : ∀ x : Vec d,
      vecDot (fun j => collarCutoff Q ε x * v.grad x j +
            2 * (v.subAverage.toFun x * gradCollarCutoff Q ε x j))
          (fun j => collarCutoff Q ε x * v.grad x j +
            2 * (v.subAverage.toFun x * gradCollarCutoff Q ε x j)) =
        vecDot (collarCutoff Q ε x • v.grad x) (collarCutoff Q ε x • v.grad x) +
          (4 * vecDot (collarCutoff Q ε x • v.grad x)
              (v.subAverage.toFun x • gradCollarCutoff Q ε x) +
            4 * vecDot (v.subAverage.toFun x • gradCollarCutoff Q ε x)
              (v.subAverage.toFun x • gradCollarCutoff Q ε x)) := by
    intro x
    simp only [vecDot, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hpos : (0 : ℝ) ≤ ∫ x in openCubeSet Q,
      vecDot (fun j => collarCutoff Q ε x * v.grad x j +
            2 * (v.subAverage.toFun x * gradCollarCutoff Q ε x j))
          (fun j => collarCutoff Q ε x * v.grad x j +
            2 * (v.subAverage.toFun x * gradCollarCutoff Q ε x j)) :=
    setIntegral_nonneg (measurableSet_openCubeSet Q) (fun x _ => hnn _)
  have habb : IntegrableOn (fun x =>
      4 * vecDot (collarCutoff Q ε x • v.grad x)
          (v.subAverage.toFun x • gradCollarCutoff Q ε x) +
        4 * vecDot (v.subAverage.toFun x • gradCollarCutoff Q ε x)
          (v.subAverage.toFun x • gradCollarCutoff Q ε x)) (openCubeSet Q) volume :=
    (hab.const_mul 4).add (hbb.const_mul 4)
  rw [setIntegral_congr_fun (measurableSet_openCubeSet Q) (fun x _ => hptw x),
    integral_add haa habb,
    integral_add (hab.const_mul 4) (hbb.const_mul 4), integral_const_mul,
    integral_const_mul] at hpos
  have hkey : (∫ x in openCubeSet Q,
        vecDot (collarCutoff Q ε x • v.grad x) (collarCutoff Q ε x • v.grad x)) ≤
      4 * ∫ x in openCubeSet Q,
        vecDot (v.subAverage.toFun x • gradCollarCutoff Q ε x)
          (v.subAverage.toFun x • gradCollarCutoff Q ε x) := by
    linarith only [hpos, hzero]
  -- back to the normalized norms
  have hvol : 0 < cubeVolume Q := cubeVolume_pos Q
  have hinv : (0 : ℝ) < (cubeVolume Q)⁻¹ := inv_pos.2 hvol
  have hCnn : (0 : ℝ) ≤ ∫ x in openCubeSet Q,
      vecDot (v.subAverage.toFun x • gradCollarCutoff Q ε x)
        (v.subAverage.toFun x • gradCollarCutoff Q ε x) :=
    setIntegral_nonneg (measurableSet_openCubeSet Q) (fun x _ => hnn _)
  refine le_of_sq_le_sq'' ?_
  rw [vecCubeLpENorm_two_sq_eq_ofReal ha, mul_pow, vecCubeLpENorm_two_sq_eq_ofReal hb]
  have hreal : (cubeVolume Q)⁻¹ * ∫ x in openCubeSet Q,
        vecDot (collarCutoff Q ε x • v.grad x) (collarCutoff Q ε x • v.grad x) ≤
      4 * ((cubeVolume Q)⁻¹ * ∫ x in openCubeSet Q,
        vecDot (v.subAverage.toFun x • gradCollarCutoff Q ε x)
          (v.subAverage.toFun x • gradCollarCutoff Q ε x)) := by
    nlinarith only [hkey, hinv]
  calc ENNReal.ofReal ((cubeVolume Q)⁻¹ * ∫ x in openCubeSet Q,
        vecDot (collarCutoff Q ε x • v.grad x) (collarCutoff Q ε x • v.grad x))
      ≤ ENNReal.ofReal (4 * ((cubeVolume Q)⁻¹ * ∫ x in openCubeSet Q,
          vecDot (v.subAverage.toFun x • gradCollarCutoff Q ε x)
            (v.subAverage.toFun x • gradCollarCutoff Q ε x))) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = (2 : ℝ≥0∞) ^ (2 : ℕ) * ENNReal.ofReal ((cubeVolume Q)⁻¹ *
          ∫ x in openCubeSet Q,
            vecDot (v.subAverage.toFun x • gradCollarCutoff Q ε x)
              (v.subAverage.toFun x • gradCollarCutoff Q ε x)) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
        norm_num

/-! ## The combined estimate -/

private theorem hilbertify_smul' (c : Vec d → ℝ) (F : Vec d → Vec d) (x : Vec d) :
    hilbertifyVecField (fun y => c y • F y) x = c x • hilbertifyVecField F x :=
  map_smul (HilbertVec.linearEquivVec d).symm (c x) (F x)

/-- The `L̲²(cu_M)` size of `(v − (v)_{cu_M})∇φ` is at most `Cε⁻¹` times
`3^{-M}‖v − (v)_{cu_M}‖_{L̲²(cu_M)}`, by the cutoff bound. -/
private theorem vecCubeLpENorm_two_smul_gradCollarCutoff_le (Q : TriadicCube d)
    (hε0 : 0 < ε) (hεh : ε < 1 / 2) (u : Vec d → ℝ)
    (hu : AEStronglyMeasurable u (normalizedCubeMeasure Q)) :
    vecCubeLpENorm Q 2 (fun x => u x • gradCollarCutoff Q ε x) ≤
      ENNReal.ofReal (collarCutoffGradientConst d * ε⁻¹) *
        (ENNReal.ofReal ((cubeScaleFactor Q)⁻¹) *
          Section2.Norms.cubeLpENorm Q 2 u) := by
  have hM := collarBound_nonneg (d := d) Q hε0
  have hC : (0 : ℝ) ≤ collarCutoffGradientConst d * ε⁻¹ :=
    mul_nonneg (collarCutoffGradientConst_nonneg d) (inv_pos.2 hε0).le
  have hs : (0 : ℝ) ≤ (cubeScaleFactor Q)⁻¹ :=
    (inv_pos.2 (cubeScaleFactor_pos'' Q)).le
  have hmono : vecCubeLpENorm Q 2 (fun x => u x • gradCollarCutoff Q ε x) ≤
      Section2.Norms.cubeLpENorm Q 2
        (fun x => (collarCutoffGradientConst d * ε⁻¹ * (cubeScaleFactor Q)⁻¹) * u x) := by
    have hfm : AEStronglyMeasurable
        (hilbertifyVecField (fun y => u y • gradCollarCutoff Q ε y)) (normalizedCubeMeasure Q) := by
      rw [show hilbertifyVecField (fun y => u y • gradCollarCutoff Q ε y) =
        fun x => u x • hilbertifyVecField (gradCollarCutoff Q ε) x from
          funext (hilbertify_smul' u _)]
      exact hu.smul (((HilbertVec.ofVecL d).continuous.comp
        (gradCollarCutoff_continuous Q hε0 hεh)).aestronglyMeasurable)
    refine Section2.Norms.cubeLpENorm_mono_enorm hfm (fun x => ?_)
    have hlhs : ‖hilbertifyVecField (fun y => u y • gradCollarCutoff Q ε y) x‖ =
        |u x| * vecNorm (gradCollarCutoff Q ε x) := by
      rw [hilbertify_smul' u (gradCollarCutoff Q ε) x, norm_smul, Real.norm_eq_abs]
      rfl
    rw [hlhs, Real.norm_eq_abs, abs_mul, abs_of_nonneg hM, mul_comm]
    exact mul_le_mul_of_nonneg_right
      (vecNorm_gradCollarCutoff_le Q hε0 hεh x) (abs_nonneg (u x))
  refine le_trans hmono (le_of_eq ?_)
  rw [show (fun x => (collarCutoffGradientConst d * ε⁻¹ * (cubeScaleFactor Q)⁻¹) * u x)
      = (collarCutoffGradientConst d * ε⁻¹ * (cubeScaleFactor Q)⁻¹) • u from rfl,
    Section2.Norms.cubeLpENorm_const_smul, Real.enorm_eq_ofReal hM,
    ENNReal.ofReal_mul hC, mul_assoc]

/-- **The combined estimate**: the boundary-layer splitting, the
Caccioppoli inequality and Hölder combine into
`‖∇v‖_{L̲²}² ≤ Cε⁻²A² + Cε^{1/2}B²` at every admissible collar width, with
`A = 3^{-M}‖v − (v)_{cu_M}‖_{L̲²(cu_M)}` and `B = ‖∇v‖_{L̲⁴(cu_M)}`. -/
theorem vecCubeLpENorm_two_sq_grad_le (Q : TriadicCube d) (hε0 : 0 < ε)
    (hεh : ε < 1 / 2) (v : H1Function (openCubeSet Q))
    (hharm : ∀ φ : H10Function (openCubeSet Q),
      ∫ x in openCubeSet Q, vecDot (v.grad x) (φ.toH1Function.grad x) = 0) :
    vecCubeLpENorm Q 2 v.grad ^ (2 : ℕ) ≤
      ENNReal.ofReal (4 * collarCutoffGradientConst d ^ (2 : ℕ) * (ε⁻¹) ^ (2 : ℕ)) *
          (ENNReal.ofReal ((cubeScaleFactor Q)⁻¹) *
            Section2.Norms.cubeLpENorm Q 2 v.subAverage.toFun) ^ (2 : ℕ) +
        ENNReal.ofReal ((2 * (d : ℝ)) ^ ((1 : ℝ) / 2) * ε ^ ((1 : ℝ) / 2)) *
          vecCubeLpENorm Q 4 v.grad ^ (2 : ℕ) := by
  have hgradv : MemVectorL2 (openCubeSet Q) v.grad := v.grad_memVectorL2
  have hmeas : AEStronglyMeasurable (hilbertifyVecField v.grad)
      (normalizedCubeMeasure Q) := by
    rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
    exact ((memHilbertVectorL2_hilbertifyVecField hgradv).smul_measure
      ENNReal.ofReal_ne_top).aestronglyMeasurable
  rw [vecCubeLpENorm_two_sq_split Q hε0 hεh hmeas]
  refine add_le_add ?_ ?_
  · -- the interior piece: Caccioppoli plus the cutoff bound
    have hcac := vecCubeLpENorm_two_collarCutoff_smul_grad_le Q hε0 hεh v hharm
    have hcut := vecCubeLpENorm_two_smul_gradCollarCutoff_le Q hε0 hεh
      v.subAverage.toFun (by
        rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
        exact (v.subAverage.memL2.smul_measure
          ENNReal.ofReal_ne_top).aestronglyMeasurable)
    have hchain : vecCubeLpENorm Q 2 (fun x => collarCutoff Q ε x • v.grad x) ≤
        ENNReal.ofReal (2 * (collarCutoffGradientConst d * ε⁻¹)) *
          (ENNReal.ofReal ((cubeScaleFactor Q)⁻¹) *
            Section2.Norms.cubeLpENorm Q 2 v.subAverage.toFun) := by
      refine le_trans hcac (le_trans (mul_le_mul' le_rfl hcut) (le_of_eq ?_))
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ← mul_assoc]
      norm_num
    have hval : (2 * (collarCutoffGradientConst d * ε⁻¹)) ^ (2 : ℕ)
        = 4 * collarCutoffGradientConst d ^ (2 : ℕ) * (ε⁻¹) ^ (2 : ℕ) := by ring
    have hCnn : (0 : ℝ) ≤ 2 * (collarCutoffGradientConst d * ε⁻¹) :=
      mul_nonneg (by norm_num)
        (mul_nonneg (collarCutoffGradientConst_nonneg d) (inv_pos.2 hε0).le)
    refine le_trans (pow_le_pow_left' hchain 2) (le_of_eq ?_)
    rw [mul_pow, ← ENNReal.ofReal_pow hCnn, hval]
  · -- the boundary piece: Hölder plus the collar volume
    have hholder := vecCubeLpENorm_two_collarDefect_smul_le Q hε0 hεh hmeas
    have hdefect := cubeLpENorm_four_collarDefect_le Q hε0 hεh
    refine le_trans (pow_le_pow_left' (le_trans hholder
      (mul_le_mul' hdefect le_rfl)) 2) (le_of_eq ?_)
    have hz : (0 : ℝ) ≤ 2 * (d : ℝ) * ε := by positivity
    rw [mul_pow, ← ENNReal.rpow_natCast
        (ENNReal.ofReal (2 * (d : ℝ) * ε) ^ ((1 : ℝ) / 4)) 2,
      ← ENNReal.rpow_mul, show ((1 : ℝ) / 4) * ((2 : ℕ) : ℝ) = (1 : ℝ) / 2 by norm_num,
      ENNReal.ofReal_rpow_of_nonneg hz (by norm_num),
      Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2 * (d : ℝ)) hε0.le]

/-! ## `e.abstract.harmonic.interpolation` -/

/-- The constant `C` of `e.abstract.harmonic.interpolation`,
explicit in the dimension: it is `(4C_a + C_b)^{1/2} + 1` for the two constants
of the combined estimate, `C_a = 4C_φ²` with `C_φ` the cutoff gradient
constant and `C_b = (2d)^{1/2}` the collar volume constant. -/
noncomputable def harmonicInterpolationConst (d : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((16 * collarCutoffGradientConst d ^ (2 : ℕ) +
    (2 * (d : ℝ)) ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / 2) + 1)

theorem harmonicInterpolationConst_lt_top (d : ℕ) :
    harmonicInterpolationConst d < ⊤ :=
  ENNReal.ofReal_lt_top

/-- `‖∇v‖_{L̲²(cu_M)} ≤ ‖∇v‖_{L̲⁴(cu_M)}`, the normalized cube measure being a
probability measure. This is the printed "if `A > B`, then the same conclusion
follows from `‖∇v‖_{L̲²(cu_M)} ≤ B`". -/
theorem vecCubeLpENorm_two_le_four {Q : TriadicCube d} {F : Vec d → Vec d}
    (_hF : AEStronglyMeasurable (hilbertifyVecField F) (normalizedCubeMeasure Q)) :
    vecCubeLpENorm Q 2 F ≤ vecCubeLpENorm Q 4 F := by
  have : IsProbabilityMeasure (normalizedCubeMeasure Q) :=
    isProbabilityMeasure_normalizedCubeMeasure Q
  exact eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)

/-- The degenerate case `A = 0`: if `v` agrees with its cube
average in `L̲²(cu_M)` then its weak gradient vanishes a.e., by the a.e.
uniqueness of weak gradients on an open set. -/
theorem vecCubeLpENorm_two_grad_eq_zero_of_cubeLpENorm_subAverage_eq_zero
    (Q : TriadicCube d) (v : H1Function (openCubeSet Q))
    (h : Section2.Norms.cubeLpENorm Q 2 v.subAverage.toFun = 0) :
    vecCubeLpENorm Q 2 v.grad = 0 := by
  have hne : ENNReal.ofReal ((cubeVolume Q)⁻¹) ≠ 0 := by
    simpa using (inv_pos.2 (cubeVolume_pos Q))
  have hmeasu : AEStronglyMeasurable v.subAverage.toFun
      (normalizedCubeMeasure Q) := by
    rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
    exact (v.subAverage.memL2.smul_measure
      ENNReal.ofReal_ne_top).aestronglyMeasurable
  have hzero : v.subAverage.toFun =ᵐ[normalizedCubeMeasure Q] 0 :=
    (eLpNorm_eq_zero_iff (by norm_num)).1 h
  rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet] at hzero
  have hzero' : v.subAverage.toFun =ᵐ[volume.restrict (openCubeSet Q)] 0 :=
    (Measure.ae_ennreal_smul_measure_iff hne).1 hzero
  have hzero'' : v.subAverage.toFun =ᵐ[volume.restrict (openCubeSet Q)]
      (0 : H1Function (openCubeSet Q)).toFun := by
    filter_upwards [hzero'] with x hx
    simpa using hx
  have hgrad := Homogenization.Book.Ch03.H1Function.grad_ae_eq_of_toFun_ae_eq
    (isOpen_openCubeSet Q) hzero''
  have hgv : v.grad =ᵐ[volume.restrict (openCubeSet Q)] fun _ => (0 : Vec d) := by
    filter_upwards [hgrad] with x hx
    simpa using hx
  have hgv' : hilbertifyVecField v.grad =ᵐ[normalizedCubeMeasure Q]
      hilbertifyVecField (fun _ : Vec d => (0 : Vec d)) := by
    rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
    refine (Measure.ae_ennreal_smul_measure_iff hne).2 ?_
    filter_upwards [hgv] with x hx
    rw [hilbertifyVecField, hilbertifyVecField, hx]
  rw [vecCubeLpENorm, Section2.Norms.cubeLpENorm, eLpNorm_congr_ae hgv']
  simpa [vecCubeLpENorm, Section2.Norms.cubeLpENorm] using
    (vecCubeLpENorm_zero Q 2 : vecCubeLpENorm Q 2 (fun _ : Vec d => (0 : Vec d)) = 0)

/-- **`e.abstract.harmonic.interpolation`**: for `v` harmonic
in the cube,

> `‖∇v‖_{L̲²(cu_M)} ≤ C (3^{-M}‖v − (v)_{cu_M}‖_{L̲²(cu_M)})^{1/5}
> ‖∇v‖_{L̲⁴(cu_M)}^{4/5}`,

with the explicit constant `harmonicInterpolationConst d`. `hharm` is the weak
form of `Δv = 0` in the cube, tested against `H¹₀(cu_M)`. -/
theorem vecCubeLpENorm_two_grad_le_interpolation (Q : TriadicCube d)
    (v : H1Function (openCubeSet Q))
    (hharm : ∀ φ : H10Function (openCubeSet Q),
      ∫ x in openCubeSet Q, vecDot (v.grad x) (φ.toH1Function.grad x) = 0) :
    vecCubeLpENorm Q 2 v.grad ≤
      harmonicInterpolationConst d *
        (ENNReal.ofReal ((cubeScaleFactor Q)⁻¹) *
          Section2.Norms.cubeLpENorm Q 2 v.subAverage.toFun) ^ ((1 : ℝ) / 5) *
        (vecCubeLpENorm Q 4 v.grad) ^ ((4 : ℝ) / 5) := by
  have hgradv : MemVectorL2 (openCubeSet Q) v.grad := v.grad_memVectorL2
  have hmeas : AEStronglyMeasurable (hilbertifyVecField v.grad)
      (normalizedCubeMeasure Q) := by
    rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
    exact ((memHilbertVectorL2_hilbertifyVecField hgradv).smul_measure
      ENNReal.ofReal_ne_top).aestronglyMeasurable
  rcases eq_or_ne (ENNReal.ofReal ((cubeScaleFactor Q)⁻¹) *
      Section2.Norms.cubeLpENorm Q 2 v.subAverage.toFun) 0 with hA0 | hA0
  · have hsne : ENNReal.ofReal ((cubeScaleFactor Q)⁻¹) ≠ 0 := by
      simpa using (inv_pos.2 (cubeScaleFactor_pos'' Q))
    have huz : Section2.Norms.cubeLpENorm Q 2 v.subAverage.toFun = 0 := by
      rcases mul_eq_zero.1 hA0 with h | h
      · exact absurd h hsne
      · exact h
    rw [vecCubeLpENorm_two_grad_eq_zero_of_cubeLpENorm_subAverage_eq_zero Q v huz]
    exact zero_le
  · have hCa : (0 : ℝ) ≤ 4 * collarCutoffGradientConst d ^ (2 : ℕ) := by
      have := collarCutoffGradientConst_nonneg d
      positivity
    have hCb : (0 : ℝ) ≤ (2 * (d : ℝ)) ^ ((1 : ℝ) / 2) :=
      Real.rpow_nonneg (by positivity) _
    have hmain := le_mul_rpow_fifth_mul_rpow_four_fifth hCa hCb hA0
      (vecCubeLpENorm_two_le_four hmeas)
      (fun ε hε0 hεh => vecCubeLpENorm_two_sq_grad_le Q hε0 hεh v hharm)
    rw [harmonicInterpolationConst, show (16 : ℝ) * collarCutoffGradientConst d ^ (2 : ℕ)
      = 4 * (4 * collarCutoffGradientConst d ^ (2 : ℕ)) by ring]
    exact hmain

/-! ## The bridge consumed by `exists_responseDifferenceL2Clause` -/

/-- **Step 3 of `l.abstract.response.fields` in the shape the a priori assembly
consumes**: this is `hharm` of
`exists_responseDifferenceL2Clause` verbatim, with `Cint := harmonicInterpolationConst d`. -/
theorem harmonic_interpolation_bridge (d : ℕ) :
    ∀ (M : ℕ) (v : H1Function (openCubeSet (originCube d (M : ℤ)))),
      (∀ φ : H10Function (openCubeSet (originCube d (M : ℤ))),
        ∫ x in openCubeSet (originCube d (M : ℤ)),
          vecDot (v.grad x) (φ.toH1Function.grad x) = 0) →
      vecCubeLpENorm (originCube d (M : ℤ)) 2 v.grad ≤
        harmonicInterpolationConst d *
            (ENNReal.ofReal ((cubeScaleFactor (originCube d (M : ℤ)))⁻¹) *
              Section2.Norms.cubeLpENorm (originCube d (M : ℤ)) 2
                v.subAverage.toFun) ^ ((1 : ℝ) / 5) *
            (vecCubeLpENorm (originCube d (M : ℤ)) 4 v.grad) ^ ((4 : ℝ) / 5) :=
  fun M v hv => vecCubeLpENorm_two_grad_le_interpolation (originCube d (M : ℤ)) v hv

/-! ## The a priori anchor with Step 3 discharged -/

end

end ResponseFields
end Section3
end SuperdiffusionCLT
