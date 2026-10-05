/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Norms.NegativeHatFullGradient
public import SuperdiffusionCLT.Section2.Norms.FractionalHs
public import SuperdiffusionCLT.Section3.ResponseFields.HminusOneDuality

/-!
# The order-one Hölder pairing: hatted negative norm against `L̲²`

The paper reads the order-one hatted
negative norm of a vector field as

> `‖F‖_{Ĥ̲^{-1}(U)}` is the supremum of `⨍_U F·∇g` over smooth mean-zero `g`
> with `‖∇g‖_{L̲²(U)} ≤ 1`,

and the estimates use it in the opposite direction. The first display of the
proof of `e.RHS.term3.B` pairs the centered gradient field
`∇w − (∇w)_{z+cu_n}` against the flux `a_{L'}(∇u_m − ∇u_{n,z})` and bounds the
pairing by the product of the `L̲²` energy of the first factor and the hatted
negative norm of the second; the `Ĥ̲^{-1}`/`L̲⁴` step of
`e.abstract.response.ND.weak` (the fourth clause of
`Frozen.Section3.responseFields_apriori_orderOne`) pairs the same way against the
gradient of the difference of the two responses.

The supremum defining the norm ranges over *smooth* test potentials while `∇w`
is only `L̲²`, so this direction of the estimate is a density statement rather
than an unfolding of the definition. It is proved here from the smooth
density of `H¹` on a cube in the gradient norm,
`SuperdiffusionCLT.Sobolev.exists_cubeH1SmoothGradientApprox`, exactly the
technique of `Section3/ResponseFields/HminusOneDuality.lean`; the constant
vector of the centered field is moved by the linear function `x ↦ c·x`, whose
Euclidean gradient is the constant `c`.

## The constant

**Exactly `1`.** The test class is normalized by the same
volume-normalized `L̲²(Q)` gradient norm that appears on the right of the
estimate, so the homogeneous step `⨍_Q F·∇g ≤ ‖F‖_{Ĥ̲^{-1}(Q)} ‖∇g‖_{L̲²(Q)}`
costs nothing, and the passage to a general `H¹` gradient is a limit. No
dimensional constant enters.

## Honesty of the values

**All norms are `ℝ≥0∞`-valued and `⊤` is a legitimate outcome.** An `L̲²`
membership hypothesis on the field `F` is what makes `‖F‖_{Ĥ̲^{-1}(Q)}` finite
(`vecHatNegENorm_le_vecCubeLpENorm`), so no `ENNReal.toReal` junk branch is
reached. The Bochner integral inside `volumeAverage` returns `0` on a
non-integrable density; that branch is unreachable here because both factors of
every pairing are `L²` on the cube, and the degenerate case of a field with
vanishing `L̲²` norm is settled by
`volumeAverage_vecDot_eq_zero_of_vecCubeLpENorm_eq_zero`.

## Main results

* `vecHatNegENorm_le_vecCubeLpENorm`: an `L̲²` field has a finite order-one
  hatted negative norm, bounded by its `L̲²` norm.
-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Section2
namespace Norms

open Homogenization
open Homogenization.Book.Ch02
open MeasureTheory
open SuperdiffusionCLT.Section3.ResponseFields
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Elementary rewriting -/

/-- The conjugate exponent of `2` is `2`; the hatted negative norms at `p = 2`
constrain their test fields at the exponent `2`. -/
theorem conjExponent_two : ENNReal.conjExponent 2 = 2 := by
  have h : (2 : ℝ≥0∞) - 1 = 1 := by
    rw [show (2 : ℝ≥0∞) = 1 + 1 from by norm_num,
      ENNReal.add_sub_cancel_left ENNReal.one_ne_top]
  rw [ENNReal.conjExponent, h, inv_one]
  norm_num

/-- The matrix-vector pairing `p·(A u)` is the pairing of the row vector
`p ᵥ* A` with `u`; this is the identity that turns the printed
`p · ⨍ (k_{ℓ'} − k_ℓ) ∇w` into the rank-one gradient pairing of clause (d). -/
theorem vecDot_matVecMul (p : Vec d) (A : Mat d) (u : Vec d) :
    vecDot p (matVecMul A u) = vecDot (Matrix.vecMul p A) u := by
  simp only [vecDot, matVecMul, Matrix.vecMul, dotProduct,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => by ring

/-- The gradient pairing density of `Section3/ResponseFields/Norms.lean` is the
coordinate dot product with the Euclidean gradient. -/
theorem vecGradientPairingDensity_eq_vecDot (F : Vec d → Vec d) (g : Vec d → ℝ)
    (x : Vec d) :
    vecGradientPairingDensity F g x = vecDot (F x) (euclideanGradient g x) := by
  rw [vecGradientPairingDensity_eq_sum]
  rfl

/-- The Euclidean gradient of the linear function `x ↦ c·x` is the constant
field `c`. This is what turns a centered gradient field `∇w − (∇w)_Q` back into
the gradient of an admissible potential. -/
theorem euclideanGradient_vecDot_const (c : Vec d) :
    euclideanGradient (fun x : Vec d => vecDot c x) = fun _ : Vec d => c := by
  have hd : ∀ x : Vec d, HasFDerivAt (fun y : Vec d => vecDot c y)
      (∑ j : Fin d, c j •
        (ContinuousLinearMap.proj j : (Fin d → ℝ) →L[ℝ] ℝ)) x := by
    intro x
    have hj : ∀ j : Fin d, HasFDerivAt (fun y : Vec d => c j * y j)
        (c j • (ContinuousLinearMap.proj j : (Fin d → ℝ) →L[ℝ] ℝ)) x := fun j =>
      (((ContinuousLinearMap.proj j :
        (Fin d → ℝ) →L[ℝ] ℝ).hasFDerivAt)).const_mul (c j)
    have hsum := HasFDerivAt.sum (fun j (_ : j ∈ Finset.univ) => hj j)
    have heq : (∑ j : Fin d, fun y : Vec d => c j * y j)
        = fun y : Vec d => vecDot c y := by
      funext y
      simp [vecDot, Finset.sum_apply]
    rwa [heq] at hsum
  funext x i
  have hfd : fderiv ℝ (fun y : Vec d => vecDot c y) x =
      ∑ j : Fin d, c j • (ContinuousLinearMap.proj j : (Fin d → ℝ) →L[ℝ] ℝ) :=
    (hd x).fderiv
  simp only [euclideanGradient, euclideanCoordDeriv, hfd,
    FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul, basisVec_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-! ## The `L²` realization of the normalized cube pairing -/

private theorem volumeAverage_cubeSet_eq_cubeAverage (Q : TriadicCube d)
    (f : Vec d → ℝ) : volumeAverage (cubeSet Q) f = cubeAverage Q f := by
  rw [volumeAverage, cubeAverage, volume_cubeSet_toReal]

/-- The `L²` norm of the realization of a vector field is its `L̲²(Q)` norm. -/
theorem norm_toLp_hilbertifyVecField {Q : TriadicCube d} {F : Vec d → Vec d}
    (hF : MemLp (hilbertifyVecField F) 2 (normalizedCubeMeasure Q)) :
    ‖hF.toLp (hilbertifyVecField F)‖ = (vecCubeLpENorm Q 2 F).toReal :=
  Lp.norm_toLp _ hF

/-- The `L²` inner product of two realizations is the normalized cube average
of the coordinate dot product. -/
theorem inner_toLp_hilbertifyVecField {Q : TriadicCube d} {a b : Vec d → Vec d}
    (ha : MemLp (hilbertifyVecField a) 2 (normalizedCubeMeasure Q))
    (hb : MemLp (hilbertifyVecField b) 2 (normalizedCubeMeasure Q)) :
    (inner ℝ (ha.toLp (hilbertifyVecField a))
        (hb.toLp (hilbertifyVecField b)) : ℝ) =
      volumeAverage (cubeSet Q) (fun x => vecDot (a x) (b x)) := by
  rw [L2.inner_def, volumeAverage_cubeSet_eq_cubeAverage,
    cubeAverage_eq_integral_normalizedCubeMeasure]
  refine integral_congr_ae ?_
  filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with x hxa hxb
  rw [hxa, hxb]
  exact HilbertVec.inner_def _ _

/-- **Cauchy-Schwarz for the volume-normalized cube pairing of two `L̲²`
vector fields.** -/
theorem abs_volumeAverage_vecDot_le_mul {Q : TriadicCube d} {a b : Vec d → Vec d}
    (ha : MemLp (hilbertifyVecField a) 2 (normalizedCubeMeasure Q))
    (hb : MemLp (hilbertifyVecField b) 2 (normalizedCubeMeasure Q)) :
    |volumeAverage (cubeSet Q) (fun x => vecDot (a x) (b x))| ≤
      (vecCubeLpENorm Q 2 a).toReal * (vecCubeLpENorm Q 2 b).toReal := by
  rw [← inner_toLp_hilbertifyVecField ha hb, ← norm_toLp_hilbertifyVecField ha,
    ← norm_toLp_hilbertifyVecField hb]
  exact abs_real_inner_le_norm _ _

/-! ## The `L²` membership of a smooth gradient field -/

private theorem continuous_euclideanGradient {g : Vec d → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) : Continuous (euclideanGradient g) := by
  have hfd : Continuous (fun x : Vec d => fderiv ℝ g x) :=
    hg.continuous_fderiv (by simp)
  exact continuous_pi fun i => hfd.clm_apply continuous_const

/-- The Euclidean gradient of a globally smooth function is continuous, hence
almost everywhere strongly measurable in the Euclidean carrier. -/
theorem aestronglyMeasurable_hilbertifyVecField_euclideanGradient {g : Vec d → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (mu : Measure (Vec d)) :
    AEStronglyMeasurable (hilbertifyVecField (euclideanGradient g)) mu :=
  (((HilbertVec.ofVecL d).continuous.comp
    (continuous_euclideanGradient hg)).aestronglyMeasurable)

/-- A smooth potential with a finite `L̲²(Q)` gradient norm has an `L²`
gradient field. -/
theorem memLp_hilbertifyVecField_euclideanGradient {Q : TriadicCube d} {g : Vec d → ℝ}
    (_hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hfin : vecCubeLpENorm Q 2 (euclideanGradient g) ≠ ⊤) :
    MemLp (hilbertifyVecField (euclideanGradient g)) 2
      (normalizedCubeMeasure Q) :=
  lt_of_le_of_ne le_top hfin

/-! ## Finiteness of the order-one hatted negative norm -/

/-- **The order-one hatted negative norm is dominated by the `L̲²` norm.** Every
admissible test field has `‖∇g‖_{L̲²(Q)} ≤ 1`, so Cauchy-Schwarz
bounds each pairing by `‖F‖_{L̲²(Q)}`. In particular an `L̲²` field has a finite
hatted negative norm. -/
theorem vecHatNegENorm_le_vecCubeLpENorm {Q : TriadicCube d} {F : Vec d → Vec d}
    (hF : MemLp (hilbertifyVecField F) 2 (normalizedCubeMeasure Q)) :
    vecHatNegENorm Q F ≤ vecCubeLpENorm Q 2 F := by
  refine vecHatNegENorm_le fun g hg => ?_
  have hgfin : vecCubeLpENorm Q 2 (euclideanGradient g) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hg.gradient_le_one
  have hgmem := memLp_hilbertifyVecField_euclideanGradient hg.contDiff hgfin
  have hCS := abs_volumeAverage_vecDot_le_mul hF hgmem
  have hpt : vecGradientPairingDensity F g
      = fun x : Vec d => vecDot (F x) (euclideanGradient g x) :=
    funext fun x => vecGradientPairingDensity_eq_vecDot F g x
  have hone : (vecCubeLpENorm Q 2 (euclideanGradient g)).toReal ≤ 1 := by
    have h := hg.gradient_le_one
    have := (ENNReal.toReal_le_toReal hgfin ENNReal.one_ne_top).2 h
    simpa using this
  have hFnn : (0 : ℝ) ≤ (vecCubeLpENorm Q 2 F).toReal := ENNReal.toReal_nonneg
  have hbound : volumeAverage (cubeSet Q) (vecGradientPairingDensity F g) ≤
      (vecCubeLpENorm Q 2 F).toReal := by
    rw [hpt]
    refine le_trans (le_abs_self _) (le_trans hCS ?_)
    calc (vecCubeLpENorm Q 2 F).toReal *
          (vecCubeLpENorm Q 2 (euclideanGradient g)).toReal
        ≤ (vecCubeLpENorm Q 2 F).toReal * 1 :=
          mul_le_mul_of_nonneg_left hone hFnn
      _ = (vecCubeLpENorm Q 2 F).toReal := mul_one _
  calc ENNReal.ofReal
        (volumeAverage (cubeSet Q) (vecGradientPairingDensity F g))
      ≤ ENNReal.ofReal ((vecCubeLpENorm Q 2 F).toReal) :=
        ENNReal.ofReal_le_ofReal hbound
    _ ≤ vecCubeLpENorm Q 2 F := ENNReal.ofReal_toReal_le

/-! ## The homogeneous form of the order-one pairing -/

/-- A constant factor comes out of a volume-normalized average. -/
theorem volumeAverage_const_mul (U : Set (Vec d)) (c : ℝ)
    (f : Vec d → ℝ) :
    volumeAverage U (fun x => c * f x) = c * volumeAverage U f := by
  rw [volumeAverage, volumeAverage, integral_const_mul]
  ring

/-- The Euclidean gradient of a constant multiple. -/
theorem euclideanGradient_const_mul {g : Vec d → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (c : ℝ) :
    euclideanGradient (fun y => c * g y) = fun x => c • euclideanGradient g x := by
  funext x i
  have hdiff : DifferentiableAt ℝ g x :=
    (hg.differentiable (by simp)) x
  simp only [euclideanGradient, euclideanCoordDeriv, Pi.smul_apply, smul_eq_mul]
  rw [fderiv_const_mul hdiff]
  rfl

/-- Subtracting its own cube average makes a continuous function mean zero on
the cube, in the `volumeAverage` form the test classes use. -/
theorem volumeAverage_sub_self_eq_zero (Q : TriadicCube d)
    {g : Vec d → ℝ} (hg : Continuous g) :
    volumeAverage (cubeSet Q) (fun x => g x - volumeAverage (cubeSet Q) g)
      = 0 := by
  have hint : IntegrableOn g (cubeSet Q) volume :=
    integrableOn_cubeSet_of_continuous hg Q
  have hconst : IntegrableOn
      (fun _ : Vec d => volumeAverage (cubeSet Q) g) (cubeSet Q) volume :=
    integrableOn_const (volume_cubeSet_lt_top Q).ne (by simp)
  have hvol : (volume : Measure (Vec d)).real (cubeSet Q) = cubeVolume Q := by
    rw [Measure.real_def, volume_cubeSet_toReal]
  have hne : cubeVolume Q ≠ 0 := (cubeVolume_pos Q).ne'
  rw [volumeAverage, integral_sub hint hconst, setIntegral_const, hvol,
    smul_eq_mul, volumeAverage, volume_cubeSet_toReal, mul_sub, ← mul_assoc,
    ← mul_assoc, inv_mul_cancel₀ hne, one_mul, sub_self]

/-- **A field with vanishing `L̲²(Q)` norm pairs to zero.** The junk branch of
the Bochner integral is never reached: an `L̲²`-null field vanishes almost
everywhere on the cube, so every pairing against it is the integral of an
almost everywhere zero function. -/
theorem volumeAverage_vecDot_eq_zero_of_vecCubeLpENorm_eq_zero
    {Q : TriadicCube d} {G : Vec d → Vec d}
    (_hG : AEStronglyMeasurable (hilbertifyVecField G) (normalizedCubeMeasure Q))
    (hzero : vecCubeLpENorm Q 2 G = 0) (F : Vec d → Vec d) :
    volumeAverage (cubeSet Q) (fun x => vecDot (F x) (G x)) = 0 := by
  have hae : hilbertifyVecField G =ᵐ[normalizedCubeMeasure Q] 0 :=
    (eLpNorm_eq_zero_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0)).1 hzero
  have hsmul : normalizedCubeMeasure Q =
      ENNReal.ofReal ((cubeVolume Q)⁻¹) • volume.restrict (cubeSet Q) := by
    rw [normalizedCubeMeasure, cubeMeasure]
  have hc : ENNReal.ofReal ((cubeVolume Q)⁻¹) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (inv_pos.2 (cubeVolume_pos Q))).ne'
  have hae' : hilbertifyVecField G =ᵐ[volume.restrict (cubeSet Q)] 0 := by
    rw [hsmul] at hae
    exact (Measure.ae_ennreal_smul_measure_iff hc).1 hae
  have hzero' : (fun x : Vec d => vecDot (F x) (G x))
      =ᵐ[volume.restrict (cubeSet Q)] 0 := by
    filter_upwards [hae'] with x hx
    have hgx : G x = 0 := by
      have h2 := congrArg HilbertVec.toVec hx
      simpa [hilbertifyVecField] using h2.trans (by simp)
    simp [hgx, vecDot]
  rw [volumeAverage, integral_eq_zero_of_ae hzero', mul_zero]

/-! ## The order-one pairing against an `H¹` gradient -/

/-- `MemVectorL2` on the open cube gives `L²` membership against the
normalized cube measure. -/
theorem memLp_hilbertifyVecField_of_memVectorL2 {Q : TriadicCube d}
    {F : Vec d → Vec d} (hF : MemVectorL2 (openCubeSet Q) F) :
    MemLp (hilbertifyVecField F) 2 (normalizedCubeMeasure Q) := by
  rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
  exact (memHilbertVectorL2_hilbertifyVecField hF).smul_measure
    ENNReal.ofReal_ne_top

/-- The Euclidean carrier is additive. -/
theorem hilbertifyVecField_sub' (a b : Vec d → Vec d) :
    hilbertifyVecField (fun x => a x - b x)
      = hilbertifyVecField a - hilbertifyVecField b := by
  funext x
  exact map_sub (HilbertVec.linearEquivVec d).symm _ _

/-- The centered gradient of an `H¹` function is an `L²` field on the cube. -/
theorem memLp_hilbertifyVecField_grad_sub_const {Q : TriadicCube d}
    (w : H1Function (openCubeSet Q)) (c : Vec d) :
    MemLp (hilbertifyVecField (fun x => w.grad x - c)) 2
      (normalizedCubeMeasure Q) := by
  let : IsProbabilityMeasure (normalizedCubeMeasure Q) :=
    ⟨normalizedCubeMeasure_apply_univ Q⟩
  have hw : MemLp (hilbertifyVecField w.grad) 2 (normalizedCubeMeasure Q) :=
    memLp_hilbertifyVecField_of_memVectorL2 w.grad_memVectorL2
  have hc : MemLp (hilbertifyVecField (fun _ : Vec d => c)) 2
      (normalizedCubeMeasure Q) := memLp_const _
  rw [hilbertifyVecField_sub']
  exact hw.sub hc

/-- The linear function `x ↦ c·x` is smooth. -/
theorem contDiff_vecDot_const (c : Vec d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => vecDot c x) := by
  have h : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => ∑ i : Fin d, c i * x i) :=
    ContDiff.sum fun i _ => contDiff_const.mul
      ((ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).contDiff)
  exact h

/-- Subtracting the linear function `x ↦ c·x` shifts the gradient by `c`. -/
theorem euclideanGradient_sub_vecDot_const {g : Vec d → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (c : Vec d) :
    euclideanGradient (fun x => g x - vecDot c x)
      = fun x => euclideanGradient g x - c := by
  funext x
  funext i
  have hd1 : DifferentiableAt ℝ g x :=
    hg.differentiable (by simp) x
  have hd2 : DifferentiableAt ℝ (fun y : Vec d => vecDot c y) x :=
    (contDiff_vecDot_const c).differentiable (by simp) x
  have hlin : fderiv ℝ (fun y : Vec d => vecDot c y) x (basisVec i) = c i :=
    congrFun (congrFun (euclideanGradient_vecDot_const c) x) i
  have hfd : fderiv ℝ (fun y : Vec d => g y - vecDot c y) x
      = fderiv ℝ g x - fderiv ℝ (fun y : Vec d => vecDot c y) x :=
    (hd1.hasFDerivAt.sub hd2.hasFDerivAt).fderiv
  simp only [euclideanGradient, euclideanCoordDeriv, Pi.sub_apply]
  rw [hfd, sub_apply, hlin]

/-! ## The order-one matrix pairing against a vector -/

end

end Norms
end Section2
end SuperdiffusionCLT
