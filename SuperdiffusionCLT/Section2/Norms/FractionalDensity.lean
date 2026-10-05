/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Norms.NegativeNormPairingHalf
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementHsClause
public import Homogenization.Sobolev.Foundations.WeakHessianEuclidean
public import Homogenization.Sobolev.Fractional.ContinuousInterpolation.UnitCubeGeometry

/-!
# The `H̲^s(Q)` norm of a field with a gradient in `L̲²(Q)`

The paper pairs the hatted negative
norm of the stream increment against `‖∇w‖_{H̲^{1/2}(cu_m)}`; the duality that
realizes it (`ofReal_abs_volumeAverage_matPairing_le_matHatNegENorm_mul_cubeHsENorm`)
is stated against *smooth* gradient fields, and its remaining input is the
density hypothesis `hdense`. This module supplies the comparison that density argument needs:

> for a vector field `G` on the cube with a Jacobian in `L̲²(Q)` and
> `0 < s < 1`,
> `‖G‖_{H̲^s(Q)} ≤ 3^{-sl} ‖G‖_{L̲²(Q)} + C(d,s) (3^l)^{1-s} ‖|DG|‖_{L̲²(Q)}`.

It is proved here for a globally smooth field `G`; the passage to an `L̲²`
limit of smooth fields is carried out in `FractionalDensityB`.

## The proof

The `L̲²` summand is the scale-weighted piece of the definition of the
`H̲^s` norm itself, so the content is the
Gagliardo piece `[G]_{W̲^{s,2}(Q)} ≤ C(d,s)(3^l)^{1-s} ‖|DG|‖_{L̲²(Q)}`. On a
convex domain no far-field branch is needed: with `x, y` in the cube,

* the fundamental theorem of calculus along `[y,x]` gives
  `|G(x) - G(y)| ≤ ∫_0^1 |DG(y + t(x-y))| dt · |x-y|`, and Cauchy-Schwarz on
  `[0,1]` squares this into `|x-y|² ∫_0^1 |DG(y+t(x-y))|² dt`;
* the shear `(x,y) ↦ (x-y, y)` is measure preserving, the segment point stays
  in the cube by convexity, and translation invariance collapses the
  `y`-integral to `∫_Q |DG|²`;
* what is left is `∫ min{d·3^l, d‖z‖}² ‖z‖^{-(2s+d)} dz`, the majorant
  `radialIntegrand` of the stream-increment estimates, bounded there by
  `gagliardoOscillationConst d s · a^{2-2s} b^{2s}`.

The kernel of clause (a) uses the Euclidean magnitude while `Vec d` carries the
supremum norm; the losses `‖z‖ ≤ |z| ≤ d‖z‖` enter as the factor `d`, giving
`gagliardoGradientConst d s = √(gagliardoOscillationConst d s) · d` and the
cube dependence `(3^l)^{1-s}` — recorded explicitly, not absorbed.

## Honesty of the values

All norms are `ℝ≥0∞`-valued and `⊤` is a legitimate outcome; no real-valued
conversion and no junk branch occurs.

## Main definitions

* `jacobianFrobeniusMagnitude`: `|DG(x)|`, the Frobenius magnitude of the
  classical Jacobian.
* `gagliardoGradientConst`: the dimensional constant `√(goc) · d`.

## Main results

* `vecNorm_fderiv_le`, `vecNorm_sub_le_intervalIntegral`,
  `ofReal_vecNorm_sub_sq_le`: the segment estimate.
* `shear_bound`, `lintegral_enorm_kernel_sq_le`: the double integral.
* `cubeEuclideanGagliardoESeminorm_le_of_contDiff`: the Gagliardo comparison.
-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Section2
namespace Norms

open Homogenization
open Homogenization.Book.Ch02
open MeasureTheory
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The Jacobian magnitude of a smooth vector field -/

/-- The Frobenius magnitude `|DG(x)|` of the classical Jacobian matrix of a
vector field, the pointwise quantity the `L̲²` gradient norm in the definition of
the `H̲^s` norm is taken of. -/
noncomputable def jacobianFrobeniusMagnitude (G : Vec d → Vec d) (x : Vec d) : ℝ :=
  matrixFrobeniusMagnitude (fun i j => euclideanGradient (fun y => G y i) x j)

/-- The Jacobian magnitude is nonnegative. -/
theorem jacobianFrobeniusMagnitude_nonneg (G : Vec d → Vec d) (x : Vec d) :
    0 ≤ jacobianFrobeniusMagnitude G x :=
  matrixFrobeniusMagnitude_nonneg _

/-- The Jacobian magnitude of a smooth field is continuous. -/
theorem continuous_jacobianFrobeniusMagnitude {G : Vec d → Vec d}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) : Continuous (jacobianFrobeniusMagnitude G) := by
  have hentry : ∀ i j : Fin d,
      Continuous (fun x : Vec d => euclideanGradient (fun y => G y i) x j) := by
    intro i j
    have hi : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => G y i) := contDiff_pi.mp hG i
    have hfd : Continuous (fun x : Vec d => fderiv ℝ (fun y : Vec d => G y i) x) :=
      hi.continuous_fderiv (by simp)
    exact hfd.clm_apply continuous_const
  have hsum : Continuous (fun x : Vec d =>
      ∑ i : Fin d, ∑ j : Fin d, euclideanGradient (fun y => G y i) x j ^ 2) := by
    refine continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ => ?_))
    exact (hentry i j).pow 2
  exact hsum.sqrt

private theorem vecNorm_sq_eq_sum (x : Vec d) : vecNorm x ^ 2 = ∑ i, x i ^ 2 := by
  rw [vecNorm_sq_eq_vecNormSq]
  simp [vecNormSq, vecDot, pow_two]

/-- The Frobenius magnitude of the Jacobian dominates the Euclidean operator
action: `|DG(w)v| ≤ |DG(w)| |v|`. -/
theorem vecNorm_fderiv_le {G : Vec d → Vec d} {w : Vec d}
    (hG : DifferentiableAt ℝ G w) (v : Vec d) :
    vecNorm (fderiv ℝ G w v) ≤ jacobianFrobeniusMagnitude G w * vecNorm v := by
  have hcoord : ∀ i : Fin d, (fderiv ℝ G w v) i
      = ∑ j, v j * euclideanGradient (fun y => G y i) w j := by
    intro i
    have h := (hasFDerivAt_pi'.1 hG.hasFDerivAt) i
    have hi : (fderiv ℝ G w v) i = fderiv ℝ (fun y => G y i) w v := by
      rw [h.fderiv]; rfl
    rw [hi]
    have h2 := vecGradientPairingDensity_eq_sum (fun _ : Vec d => v)
      (fun y => G y i) w
    rw [vecGradientPairingDensity] at h2
    exact h2
  have hrow : ∀ i : Fin d, ((fderiv ℝ G w v) i) ^ 2 ≤
      (∑ j, v j ^ 2) * ∑ j, euclideanGradient (fun y => G y i) w j ^ 2 := by
    intro i
    rw [hcoord i]
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => v j)
      (fun j => euclideanGradient (fun y => G y i) w j)
  have hsq : vecNorm (fderiv ℝ G w v) ^ 2 ≤
      (jacobianFrobeniusMagnitude G w * vecNorm v) ^ 2 := by
    rw [vecNorm_sq_eq_sum, mul_pow, jacobianFrobeniusMagnitude]
    erw [sq_matrixFrobeniusMagnitude]
    rw [vecNorm_sq_eq_sum]
    calc ∑ i, ((fderiv ℝ G w v) i) ^ 2
        ≤ ∑ i : Fin d, (∑ j, v j ^ 2) *
            ∑ j, euclideanGradient (fun y => G y i) w j ^ 2 :=
          Finset.sum_le_sum fun i _ => hrow i
      _ = (∑ i : Fin d, ∑ j, euclideanGradient (fun y => G y i) w j ^ 2) *
            ∑ j, v j ^ 2 := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by ring
  have h1 : (0 : ℝ) ≤ vecNorm (fderiv ℝ G w v) := vecNorm_nonneg _
  have h2 : (0 : ℝ) ≤ jacobianFrobeniusMagnitude G w * vecNorm v :=
    mul_nonneg (jacobianFrobeniusMagnitude_nonneg G w) (vecNorm_nonneg v)
  have hle := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq h1, Real.sqrt_sq h2] at hle

/-! ## The segment estimate on a convex domain -/

/-- **The fundamental theorem of calculus along the segment `[y, x]`.** For a
globally smooth vector field the Euclidean increment is at most the integral of
the Jacobian magnitude along the segment, times the Euclidean length. -/
theorem vecNorm_sub_le_intervalIntegral {G : Vec d → Vec d}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (x y : Vec d) :
    vecNorm (G x - G y) ≤
      ∫ t in (0 : ℝ)..1,
        jacobianFrobeniusMagnitude G (y + t • (x - y)) * vecNorm (x - y) := by
  set v : Vec d := x - y with hv
  set F : ℝ → HilbertVec d := fun r => HilbertVec.ofVec (G (y + r • v)) with hF
  set F' : ℝ → HilbertVec d :=
    fun t => HilbertVec.ofVecL d (fderiv ℝ G (y + t • v) v) with hF'
  have hderiv : ∀ t : ℝ, HasDerivAt F (F' t) t := by
    intro t
    have hpath : HasDerivAt (fun r : ℝ => y + r • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add y
    have hGd : HasFDerivAt G (fderiv ℝ G (y + t • v)) (y + t • v) :=
      (hG.differentiable (by simp) _).hasFDerivAt
    exact (HilbertVec.ofVecL d).hasFDerivAt.comp_hasDerivAt t
      (hGd.comp_hasDerivAt t hpath)
  have hcont : Continuous F' := by
    have hfd : Continuous (fun w : Vec d => fderiv ℝ G w) :=
      hG.continuous_fderiv (by simp)
    have hpath : Continuous (fun t : ℝ => y + t • v) := by fun_prop
    exact (HilbertVec.ofVecL d).continuous.comp
      ((hfd.comp hpath).clm_apply continuous_const)
  have hFTC : ∫ t in (0 : ℝ)..1, F' t = F 1 - F 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
      (hcont.intervalIntegrable 0 1)
  have hF1 : F 1 = HilbertVec.ofVec (G x) := by
    simp only [hF, one_smul, hv]
    congr 2
    abel
  have hF0 : F 0 = HilbertVec.ofVec (G y) := by
    simp only [hF, zero_smul, add_zero]
  have hnorm : ‖F 1 - F 0‖ = vecNorm (G x - G y) := by
    rw [hF1, hF0]
    congr 1
  have hcont2 : Continuous (fun t : ℝ =>
      jacobianFrobeniusMagnitude G (y + t • v) * vecNorm v) :=
    ((continuous_jacobianFrobeniusMagnitude hG).comp
      (by fun_prop : Continuous (fun t : ℝ => y + t • v))).mul continuous_const
  calc vecNorm (G x - G y) = ‖∫ t in (0 : ℝ)..1, F' t‖ := by rw [hFTC, hnorm]
    _ ≤ ∫ t in (0 : ℝ)..1, ‖F' t‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ t in (0 : ℝ)..1,
          jacobianFrobeniusMagnitude G (y + t • v) * vecNorm v := by
        refine intervalIntegral.integral_mono_on (by norm_num)
          (hcont.norm.intervalIntegrable 0 1) (hcont2.intervalIntegrable 0 1) ?_
        intro t _
        exact vecNorm_fderiv_le (hG.differentiable (by simp) _) v

/-! ## Cauchy-Schwarz on the unit interval -/

private theorem sq_lintegral_le_lintegral_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (hμ : μ Set.univ = 1) {φ : α → ℝ≥0∞} (hφ : AEMeasurable φ μ) :
    (∫⁻ a, φ a ∂μ) ^ (2 : ℕ) ≤ ∫⁻ a, (φ a) ^ (2 : ℕ) ∂μ := by
  have hcast : ∀ z : ℝ≥0∞, z ^ (2 : ℝ) = z ^ (2 : ℕ) := by
    intro z
    rw [← ENNReal.rpow_natCast z 2]
    norm_num
  have hone : ∫⁻ _a : α, (1 : ℝ≥0∞) ^ (2 : ℝ) ∂μ = 1 := by
    simp [hμ]
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    hφ (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one] at h
  rw [hone, ENNReal.one_rpow, mul_one] at h
  have h2 : (∫⁻ a, φ a ∂μ) ^ (2 : ℕ) ≤
      ((∫⁻ a, φ a ^ (2 : ℝ) ∂μ) ^ (1 / (2:ℝ))) ^ (2 : ℕ) := by
    exact pow_le_pow_left' h 2
  refine le_trans h2 (le_of_eq ?_)
  rw [← ENNReal.rpow_natCast ((∫⁻ a, φ a ^ (2:ℝ) ∂μ) ^ (1/(2:ℝ))) 2,
    ← ENNReal.rpow_mul]
  simp only [Nat.cast_ofNat]
  rw [show (1 / (2:ℝ)) * 2 = 1 by norm_num, ENNReal.rpow_one]
  exact lintegral_congr fun a => hcast (φ a)

/-- **The pointwise segment estimate in `ℝ≥0∞`.** -/
theorem ofReal_vecNorm_sub_sq_le {G : Vec d → Vec d}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (x y : Vec d) :
    ENNReal.ofReal (vecNorm (G x - G y) ^ 2) ≤
      ENNReal.ofReal (vecNorm (x - y) ^ 2) *
        ∫⁻ t in Set.Ioc (0 : ℝ) 1,
          ENNReal.ofReal (jacobianFrobeniusMagnitude G (y + t • (x - y)) ^ 2) := by
  set v : Vec d := x - y with hv
  set psi : ℝ → ℝ := fun t => jacobianFrobeniusMagnitude G (y + t • v) with hpsi
  have hcont : Continuous psi :=
    (continuous_jacobianFrobeniusMagnitude hG).comp
      (by fun_prop : Continuous (fun t : ℝ => y + t • v))
  have hnn : ∀ t : ℝ, 0 ≤ psi t := fun t => jacobianFrobeniusMagnitude_nonneg G _
  set A : ℝ := ∫ t in (0 : ℝ)..1, psi t with hA
  have hAnn : 0 ≤ A := by
    rw [hA]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun t _ => hnn t)
  have hseg : vecNorm (G x - G y) ≤ A * vecNorm v := by
    have h := vecNorm_sub_le_intervalIntegral hG x y
    rwa [intervalIntegral.integral_mul_const, ← hA] at h
  have hsq : vecNorm (G x - G y) ^ 2 ≤ A ^ 2 * vecNorm v ^ 2 := by
    rw [← mul_pow]
    rw [pow_two, pow_two]
    exact mul_self_le_mul_self (vecNorm_nonneg _) hseg
  have hAint : ENNReal.ofReal A = ∫⁻ t in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (psi t) := by
    rw [hA, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      ((hcont.intervalIntegrable 0 1).1)
      (Filter.Eventually.of_forall (fun t => hnn t))
  have hprob : (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) 1)) Set.univ = 1 := by
    rw [Measure.restrict_apply_univ, Real.volume_Ioc]
    norm_num
  have hCS := sq_lintegral_le_lintegral_sq hprob
    (φ := fun t => ENNReal.ofReal (psi t))
    (hcont.measurable.ennreal_ofReal.aemeasurable)
  calc ENNReal.ofReal (vecNorm (G x - G y) ^ 2)
      ≤ ENNReal.ofReal (A ^ 2 * vecNorm v ^ 2) := ENNReal.ofReal_le_ofReal hsq
    _ = ENNReal.ofReal (vecNorm v ^ 2) * ENNReal.ofReal (A ^ 2) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        ring_nf
    _ = ENNReal.ofReal (vecNorm v ^ 2) * (ENNReal.ofReal A) ^ (2 : ℕ) := by
        rw [← ENNReal.ofReal_pow hAnn]
    _ ≤ ENNReal.ofReal (vecNorm v ^ 2) *
          ∫⁻ t in Set.Ioc (0 : ℝ) 1, (ENNReal.ofReal (psi t)) ^ (2 : ℕ) := by
        rw [hAint]
        exact mul_le_mul' le_rfl hCS
    _ = ENNReal.ofReal (vecNorm v ^ 2) *
          ∫⁻ t in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (psi t ^ 2) := by
        congr 1
        exact lintegral_congr fun t => (ENNReal.ofReal_pow (hnn t) 2).symm

/-! ## Two facts about the half-open cube -/

/-- Two points of the half-open cube are at ambient distance at most the cube
side length. -/
theorem dist_le_cubeScaleFactor {Q : TriadicCube d} {x y : Vec d}
    (hx : x ∈ cubeSet Q) (hy : y ∈ cubeSet Q) : dist x y ≤ cubeScaleFactor Q := by
  have hx' := Metric.mem_closedBall.1 (cubeSet_subset_closedBall Q hx)
  have hy' := Metric.mem_closedBall.1 (cubeSet_subset_closedBall Q hy)
  have := dist_triangle x (cubeCenter Q) y
  rw [dist_comm (cubeCenter Q) y] at this
  rw [cubeScaleFactor_eq_two_mul_cubeRadius]
  linarith only [this, hx', hy']

/-- The half-open cube is convex: the segment between two of its points stays
inside it. -/
theorem mem_cubeSet_segment {Q : TriadicCube d} {y u : Vec d} {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hy : y ∈ cubeSet Q) (hyu : y + u ∈ cubeSet Q) :
    y + t • u ∈ cubeSet Q := by
  rcases eq_or_lt_of_le ht1 with heq | ht1'
  · rw [heq, one_smul]
    exact hyu
  intro i
  obtain ⟨h1, h2⟩ := hy i
  obtain ⟨h3, h4⟩ := hyu i
  have hcoord : (y + t • u) i = y i + t * u i := rfl
  have hsum : (y + u) i = y i + u i := rfl
  rw [hsum] at h3 h4
  rw [hcoord]
  constructor
  · have h5 : (0:ℝ) ≤ (1 - t) * (y i - (((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q)) :=
      mul_nonneg (by linarith only [ht1]) (by linarith only [h1])
    have h6 : (0:ℝ) ≤ t * (y i + u i - (((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q)) :=
      mul_nonneg ht0 (by linarith only [h3])
    have hid : y i + t * u i - (((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q)
        = (1 - t) * (y i - (((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q))
          + t * (y i + u i - (((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q)) := by
      ring
    linarith only [h5, h6, hid]
  · have h5 : (0:ℝ) < (1 - t) * ((((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q) - y i) :=
      mul_pos (by linarith only [ht1']) (by linarith only [h2])
    have h6 : (0:ℝ) ≤ t * ((((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q) - (y i + u i)) :=
      mul_nonneg ht0 (by linarith only [h4])
    have hid : (((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q) - (y i + t * u i)
        = (1 - t) * ((((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q) - y i)
          + t * ((((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q) - (y i + u i)) := by
      ring
    linarith only [h5, h6, hid]

/-- The explicit Euclidean magnitude is the `HilbertVec` magnitude. -/
theorem euclideanNorm_eq_vecNorm (x : Vec d) : euclideanNorm x = vecNorm x := by
  rw [← sq_eq_sq₀ (euclideanNorm_nonneg x) (vecNorm_nonneg x), euclideanNorm_sq,
    vecNorm_sq_eq_vecNormSq]

/-! ## The shear-and-translate bound -/

/-- **The shear-and-translate bound.** The double integral over `Q × Q` of a
radial weight in `x - y` against a nonnegative density evaluated at the segment
point `y + t(x - y)` is at most the total mass of the weight times the integral
of the density over `Q`: the shear `(x,y) ↦ (x-y,y)` preserves the product
measure, convexity keeps the segment point in the cube, and translation
invariance collapses the inner integral. -/
theorem shear_bound {Q : TriadicCube d} {R : Vec d → ℝ≥0∞} (hR : Measurable R)
    {Phi : Vec d → ℝ≥0∞} (hPhi : Measurable Phi) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (∫⁻ z in cubeSet Q ×ˢ cubeSet Q, R (z.1 - z.2) * Phi (z.2 + t • (z.1 - z.2))
        ∂(volume.prod volume))
      ≤ (∫⁻ u : Vec d, R u) * ∫⁻ w in cubeSet Q, Phi w := by
  classical
  set S : Set (Vec d) := cubeSet Q with hS
  have hSm : MeasurableSet S := measurableSet_cubeSet Q
  set ind : Vec d → ℝ≥0∞ := S.indicator (fun _ => (1 : ℝ≥0∞)) with hind
  have hindm : Measurable ind := measurable_const.indicator hSm
  set Psi : Vec d × Vec d → ℝ≥0∞ :=
    fun p => ind p.2 * ind (p.2 + p.1) * (R p.1 * Phi (p.2 + t • p.1)) with hPsi
  have hPsim : Measurable Psi := by
    refine ((hindm.comp measurable_snd).mul
      (hindm.comp (measurable_snd.add measurable_fst))).mul ?_
    exact (hR.comp measurable_fst).mul
      (hPhi.comp (measurable_snd.add (measurable_fst.const_smul t)))
  -- Step 1: rewrite the restricted integral through the indicator form
  have hstep1 : (∫⁻ z in S ×ˢ S, R (z.1 - z.2) * Phi (z.2 + t • (z.1 - z.2))
        ∂(volume.prod volume))
      = ∫⁻ z : Vec d × Vec d, Psi (z.1 - z.2, z.2) ∂(volume.prod volume) := by
    rw [← lintegral_indicator (hSm.prod hSm)]
    refine lintegral_congr fun z => ?_
    by_cases hz : z ∈ S ×ˢ S
    · rw [Set.indicator_of_mem hz]
      have h1 : ind z.2 = 1 := by rw [hind, Set.indicator_of_mem hz.2]
      have h2 : ind (z.2 + (z.1 - z.2)) = 1 := by
        rw [hind, Set.indicator_of_mem (by simpa using hz.1)]
      simp only [hPsi, h1, h2, one_mul]
    · rw [Set.indicator_of_notMem hz]
      have : ind z.2 * ind (z.2 + (z.1 - z.2)) = 0 := by
        by_cases h1 : z.1 ∈ S
        · have h2 : z.2 ∉ S := fun h => hz ⟨h1, h⟩
          have : ind z.2 = 0 := by rw [hind, Set.indicator_of_notMem h2]
          rw [this, zero_mul]
        · have : ind (z.2 + (z.1 - z.2)) = 0 := by
            rw [hind, Set.indicator_of_notMem (by simpa using h1)]
          rw [this, mul_zero]
      simp only [hPsi]
      rw [this, zero_mul]
  have hstep2 : (∫⁻ z : Vec d × Vec d, Psi (z.1 - z.2, z.2) ∂(volume.prod volume))
      = ∫⁻ p : Vec d × Vec d, Psi p ∂(volume.prod volume) :=
    (measurePreserving_sub_prod (volume : Measure (Vec d)) volume).lintegral_comp hPsim
  have hstep3 : (∫⁻ p : Vec d × Vec d, Psi p ∂(volume.prod volume))
      = ∫⁻ u : Vec d, ∫⁻ y : Vec d, Psi (u, y) := lintegral_prod _ hPsim.aemeasurable
  have hinner : ∀ u : Vec d, (∫⁻ y : Vec d, Psi (u, y))
      ≤ R u * ∫⁻ w in S, Phi w := by
    intro u
    have hpt : ∀ y : Vec d, Psi (u, y) ≤ R u * (ind (y + t • u) * Phi (y + t • u)) := by
      intro y
      by_cases hy : y ∈ S
      · by_cases hyu : y + u ∈ S
        · have hseg : y + t • u ∈ S := mem_cubeSet_segment ht0 ht1 hy hyu
          have h1 : ind y = 1 := by rw [hind, Set.indicator_of_mem hy]
          have h2 : ind (y + u) = 1 := by rw [hind, Set.indicator_of_mem hyu]
          have h3 : ind (y + t • u) = 1 := by rw [hind, Set.indicator_of_mem hseg]
          simp only [hPsi, h1, h2, h3, one_mul, mul_one]
          exact le_rfl
        · have h2 : ind (y + u) = 0 := by rw [hind, Set.indicator_of_notMem hyu]
          simp only [hPsi, h2, mul_zero, zero_mul]
          exact zero_le
      · have h1 : ind y = 0 := by rw [hind, Set.indicator_of_notMem hy]
        simp only [hPsi, h1, zero_mul]
        exact zero_le
    calc (∫⁻ y : Vec d, Psi (u, y))
        ≤ ∫⁻ y : Vec d, R u * (ind (y + t • u) * Phi (y + t • u)) :=
          lintegral_mono hpt
      _ = R u * ∫⁻ y : Vec d, ind (y + t • u) * Phi (y + t • u) := by
          have hm : Measurable
              (fun y : Vec d => ind (y + t • u) * Phi (y + t • u)) :=
            (hindm.comp (measurable_id.add_const (t • u))).mul
              (hPhi.comp (measurable_id.add_const (t • u)))
          rw [lintegral_const_mul _ hm]
      _ = R u * ∫⁻ w : Vec d, ind w * Phi w := by
          congr 1
          exact lintegral_add_right_eq_self (fun w => ind w * Phi w) (t • u)
      _ = R u * ∫⁻ w in S, Phi w := by
          congr 1
          rw [← lintegral_indicator hSm]
          refine lintegral_congr fun w => ?_
          by_cases hw : w ∈ S
          · rw [hind, Set.indicator_of_mem hw, one_mul, Set.indicator_of_mem hw]
          · rw [hind, Set.indicator_of_notMem hw, zero_mul,
              Set.indicator_of_notMem hw]
  rw [hstep1, hstep2, hstep3]
  calc (∫⁻ u : Vec d, ∫⁻ y : Vec d, Psi (u, y))
      ≤ ∫⁻ u : Vec d, R u * ∫⁻ w in S, Phi w := lintegral_mono hinner
    _ = (∫⁻ u : Vec d, R u) * ∫⁻ w in S, Phi w := lintegral_mul_const _ hR

/-! ## The kernel estimate on the cube -/

private theorem enorm_kernel_sq_le {Q : TriadicCube d} {s : ℝ} (hs : 0 < s)
    {G : Vec d → Vec d} (hG : ContDiff ℝ (⊤ : ℕ∞) G) {z : Vec d × Vec d}
    (hz1 : z.1 ∈ cubeSet Q) (hz2 : z.2 ∈ cubeSet Q) :
    ‖euclideanGagliardoKernel s 2 (hilbertifyVecField G) z‖ₑ ^ (2 : ℝ)
      ≤ radialIntegrand d s ((d : ℝ) * cubeScaleFactor Q) d (z.1 - z.2) *
          ∫⁻ t in Set.Ioc (0 : ℝ) 1,
            ENNReal.ofReal
              (jacobianFrobeniusMagnitude G (z.2 + t • (z.1 - z.2)) ^ 2) := by
  set u : Vec d := z.1 - z.2 with hu
  set e : ℝ := euclideanDist z.1 z.2 with he
  have heu : e = vecNorm u := by
    rw [he, euclideanDist, euclideanNorm_eq_vecNorm, hu]
  have hexp : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  have hknorm : ‖euclideanGagliardoKernel s 2 (hilbertifyVecField G) z‖
      = e ^ (-(s + (d : ℝ) / 2)) * vecNorm (G z.1 - G z.2) := by
    rw [norm_euclideanGagliardoKernel, hexp, ← he]
    rfl
  have hennorm : ‖euclideanGagliardoKernel s 2 (hilbertifyVecField G) z‖ₑ ^ (2 : ℝ)
      = ENNReal.ofReal (e ^ (-(2 * s + (d : ℝ))))
        * ENNReal.ofReal (vecNorm (G z.1 - G z.2) ^ 2) := by
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 2), hknorm]
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (euclideanDist_nonneg _ _) _)]
    congr 1
    have hrw : ∀ w : ℝ, w ^ (2 : ℝ) = w ^ 2 := by
      intro w
      rw [← Real.rpow_natCast w 2]
      norm_num
    rw [hrw, mul_pow, ← Real.rpow_natCast (e ^ (-(s + (d : ℝ) / 2))) 2,
      ← Real.rpow_mul (euclideanDist_nonneg _ _)]
    congr 2
    push_cast
    ring
  set Lt : ℝ≥0∞ := ∫⁻ t in Set.Ioc (0 : ℝ) 1,
    ENNReal.ofReal (jacobianFrobeniusMagnitude G (z.2 + t • (z.1 - z.2)) ^ 2) with hLt
  have hreal : ENNReal.ofReal (e ^ (-(2 * s + (d : ℝ))) * vecNorm u ^ 2)
      ≤ radialIntegrand d s ((d : ℝ) * cubeScaleFactor Q) d u := by
    rw [radialIntegrand]
    rcases eq_or_lt_of_le (norm_nonneg u) with hzero | hpos
    · have hu0 : u = 0 := by
        rw [← norm_eq_zero]
        exact hzero.symm
      have hvn : vecNorm u = 0 := by
        rw [hu0]
        simpa using (euclideanNorm_eq_vecNorm (0 : Vec d)).symm
      rw [hvn]
      norm_num
    · have hnle : ‖u‖ ≤ vecNorm u := by
        rw [← euclideanNorm_eq_vecNorm]
        exact norm_le_euclideanNorm u
      have hdle : vecNorm u ≤ (d : ℝ) * ‖u‖ := by
        rw [← euclideanNorm_eq_vecNorm]
        exact euclideanNorm_le_dimension_mul_norm u
      have hnonpos : -(2 * s + (d : ℝ)) ≤ 0 := by
        have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
        linarith only [hs, this]
      have h1 : e ^ (-(2 * s + (d : ℝ))) ≤ ‖u‖ ^ (-(2 * s + (d : ℝ))) := by
        rw [heu]
        exact Real.rpow_le_rpow_of_nonpos hpos hnle hnonpos
      have h2 : vecNorm u ^ 2 ≤ ((d : ℝ) * ‖u‖) ^ 2 := by
        rw [pow_two, pow_two]
        exact mul_self_le_mul_self (vecNorm_nonneg u) hdle
      have hdist : ‖u‖ ≤ cubeScaleFactor Q := by
        have h := dist_le_cubeScaleFactor hz1 hz2
        rwa [dist_eq_norm, ← hu] at h
      have hmin : min ((d : ℝ) * cubeScaleFactor Q) ((d : ℝ) * ‖u‖)
          = (d : ℝ) * ‖u‖ :=
        min_eq_right (by
          exact mul_le_mul_of_nonneg_left hdist (Nat.cast_nonneg d))
      rw [hmin]
      refine ENNReal.ofReal_le_ofReal ?_
      calc e ^ (-(2 * s + (d : ℝ))) * vecNorm u ^ 2
          ≤ ‖u‖ ^ (-(2 * s + (d : ℝ))) * ((d : ℝ) * ‖u‖) ^ 2 :=
            mul_le_mul h1 h2 (sq_nonneg _)
              (Real.rpow_nonneg (norm_nonneg u) _)
        _ = ((d : ℝ) * ‖u‖) ^ 2 * ‖u‖ ^ (-(2 * s + (d : ℝ))) := by ring
  calc ‖euclideanGagliardoKernel s 2 (hilbertifyVecField G) z‖ₑ ^ (2 : ℝ)
      = ENNReal.ofReal (e ^ (-(2 * s + (d : ℝ))))
          * ENNReal.ofReal (vecNorm (G z.1 - G z.2) ^ 2) := hennorm
    _ ≤ ENNReal.ofReal (e ^ (-(2 * s + (d : ℝ))))
          * (ENNReal.ofReal (vecNorm u ^ 2) * Lt) := by
        refine mul_le_mul' le_rfl ?_
        rw [hLt, hu]
        exact ofReal_vecNorm_sub_sq_le hG z.1 z.2
    _ = ENNReal.ofReal (e ^ (-(2 * s + (d : ℝ))) * vecNorm u ^ 2) * Lt := by
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg (euclideanDist_nonneg _ _) _),
          mul_assoc]
    _ ≤ radialIntegrand d s ((d : ℝ) * cubeScaleFactor Q) d u * Lt :=
        mul_le_mul' hreal le_rfl

/-- **The un-normalized kernel estimate.** The double integral of the squared
Gagliardo kernel of a smooth field over `Q × Q` is at most
`goc(d,s) ((d 3^l)^{2-2s} d^{2s})` times the integral of the squared Jacobian
magnitude over `Q`. -/
theorem lintegral_enorm_kernel_sq_le {Q : TriadicCube d} {s : ℝ} (hs : 0 < s)
    (hs1 : s < 1) (hd : 0 < d) {G : Vec d → Vec d} (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    (∫⁻ z in cubeSet Q ×ˢ cubeSet Q,
        ‖euclideanGagliardoKernel s 2 (hilbertifyVecField G) z‖ₑ ^ (2 : ℝ)
        ∂(volume.prod volume))
      ≤ ENNReal.ofReal (gagliardoOscillationConst d s *
            (((d : ℝ) * cubeScaleFactor Q) ^ (2 - 2 * s) * (d : ℝ) ^ (2 * s))) *
          ∫⁻ w in cubeSet Q,
            ENNReal.ofReal (jacobianFrobeniusMagnitude G w ^ 2) := by
  classical
  have hRm0 : Measurable (radialIntegrand d s ((d : ℝ) * cubeScaleFactor Q) d) := by
    unfold radialIntegrand
    fun_prop
  set R : Vec d → ℝ≥0∞ :=
    radialIntegrand d s ((d : ℝ) * cubeScaleFactor Q) d with hR
  have hRm : Measurable R := hRm0
  have hPhim0 : Measurable
      (fun w : Vec d => ENNReal.ofReal (jacobianFrobeniusMagnitude G w ^ 2)) :=
    (((continuous_jacobianFrobeniusMagnitude hG).pow 2).measurable).ennreal_ofReal
  set Phi : Vec d → ℝ≥0∞ :=
    fun w => ENNReal.ofReal (jacobianFrobeniusMagnitude G w ^ 2) with hPhi
  have hPhim : Measurable Phi := hPhim0
  set f : Vec d × Vec d → ℝ → ℝ≥0∞ :=
    fun z t => R (z.1 - z.2) * Phi (z.2 + t • (z.1 - z.2)) with hf
  have hfm : Measurable (Function.uncurry f) := by
    have h1 : Measurable (fun p : (Vec d × Vec d) × ℝ => R (p.1.1 - p.1.2)) :=
      hRm.comp ((measurable_fst.comp measurable_fst).sub
        (measurable_snd.comp measurable_fst))
    have h2 : Measurable (fun p : (Vec d × Vec d) × ℝ =>
        Phi (p.1.2 + p.2 • (p.1.1 - p.1.2))) := by
      refine hPhim.comp ((measurable_snd.comp measurable_fst).add ?_)
      exact (measurable_snd.smul
        ((measurable_fst.comp measurable_fst).sub
          (measurable_snd.comp measurable_fst)))
    exact h1.mul h2
  have hmaj : Measurable (fun z : Vec d × Vec d =>
      ∫⁻ t in Set.Ioc (0 : ℝ) 1, f z t) := by
    exact Measurable.lintegral_prod_right' (ν := volume.restrict (Set.Ioc (0:ℝ) 1)) hfm
  -- Step 1: the pointwise bound
  have hstep1 : (∫⁻ z in cubeSet Q ×ˢ cubeSet Q,
        ‖euclideanGagliardoKernel s 2 (hilbertifyVecField G) z‖ₑ ^ (2 : ℝ)
        ∂(volume.prod volume))
      ≤ ∫⁻ z in cubeSet Q ×ˢ cubeSet Q,
          (∫⁻ t in Set.Ioc (0 : ℝ) 1, f z t) ∂(volume.prod volume) := by
    refine setLIntegral_mono hmaj (fun z hz => ?_)
    have hb := enorm_kernel_sq_le (Q := Q) hs hG hz.1 hz.2
    calc ‖euclideanGagliardoKernel s 2 (hilbertifyVecField G) z‖ₑ ^ (2 : ℝ)
        ≤ R (z.1 - z.2) * ∫⁻ t in Set.Ioc (0 : ℝ) 1,
            Phi (z.2 + t • (z.1 - z.2)) := hb
      _ = ∫⁻ t in Set.Ioc (0 : ℝ) 1, f z t := by
          rw [hf]
          exact (lintegral_const_mul _
            (hPhim.comp (measurable_const.add
              (measurable_id.smul_const (z.1 - z.2))))).symm
  have hswap : (∫⁻ z in cubeSet Q ×ˢ cubeSet Q,
        (∫⁻ t in Set.Ioc (0 : ℝ) 1, f z t) ∂(volume.prod volume))
      = ∫⁻ t in Set.Ioc (0 : ℝ) 1,
          (∫⁻ z in cubeSet Q ×ˢ cubeSet Q, f z t ∂(volume.prod volume)) :=
    lintegral_lintegral_swap hfm.aemeasurable
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hLpos : (0 : ℝ) < cubeScaleFactor Q := by
    rw [cubeScaleFactor]
    positivity
  have hradial : (∫⁻ u : Vec d, R u)
      ≤ ENNReal.ofReal (gagliardoOscillationConst d s *
          (((d : ℝ) * cubeScaleFactor Q) ^ (2 - 2 * s) * (d : ℝ) ^ (2 * s))) :=
    lintegral_radialIntegrand_le d hs hs1 (mul_pos hdR hLpos) hdR
  have hinner : ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 →
      (∫⁻ z in cubeSet Q ×ˢ cubeSet Q, f z t ∂(volume.prod volume))
        ≤ ENNReal.ofReal (gagliardoOscillationConst d s *
            (((d : ℝ) * cubeScaleFactor Q) ^ (2 - 2 * s) * (d : ℝ) ^ (2 * s))) *
          ∫⁻ w in cubeSet Q, Phi w := by
    intro t ht
    exact le_trans (shear_bound hRm hPhim ht.1.le ht.2)
      (mul_le_mul' hradial le_rfl)
  calc (∫⁻ z in cubeSet Q ×ˢ cubeSet Q,
        ‖euclideanGagliardoKernel s 2 (hilbertifyVecField G) z‖ₑ ^ (2 : ℝ)
        ∂(volume.prod volume))
      ≤ ∫⁻ z in cubeSet Q ×ˢ cubeSet Q,
          (∫⁻ t in Set.Ioc (0 : ℝ) 1, f z t) ∂(volume.prod volume) := hstep1
    _ = ∫⁻ t in Set.Ioc (0 : ℝ) 1,
          (∫⁻ z in cubeSet Q ×ˢ cubeSet Q, f z t ∂(volume.prod volume)) := hswap
    _ ≤ ∫⁻ _t in Set.Ioc (0 : ℝ) 1,
          ENNReal.ofReal (gagliardoOscillationConst d s *
            (((d : ℝ) * cubeScaleFactor Q) ^ (2 - 2 * s) * (d : ℝ) ^ (2 * s))) *
            ∫⁻ w in cubeSet Q, Phi w := setLIntegral_mono measurable_const hinner
    _ = ENNReal.ofReal (gagliardoOscillationConst d s *
          (((d : ℝ) * cubeScaleFactor Q) ^ (2 - 2 * s) * (d : ℝ) ^ (2 * s))) *
          ∫⁻ w in cubeSet Q, Phi w := by
        rw [setLIntegral_const, Real.volume_Ioc]
        norm_num

/-! ## The comparison with the gradient `L̲²` norm -/

private theorem gagliardoOscillationConst_nonneg' (d : ℕ) {s : ℝ} (hs : 0 < s)
    (hs1 : s < 1) : 0 ≤ gagliardoOscillationConst d s := by
  have h1 : (2 : ℝ) ^ (2 * s - 2) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith only [hs1])
  have h2 : (2 : ℝ) ^ (-(2 * s)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith only [hs])
  have h3 : (0 : ℝ) < 1 - (2 : ℝ) ^ (2 * s - 2) := by linarith only [h1]
  have h4 : (0 : ℝ) < 1 - (2 : ℝ) ^ (-(2 * s)) := by linarith only [h2]
  rw [gagliardoOscillationConst]
  have h5 : (0 : ℝ) ≤ (2 : ℝ) ^ (2 * s) * (1 - (2 : ℝ) ^ (2 * s - 2))⁻¹ :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (inv_nonneg.2 h3.le)
  have h6 : (0 : ℝ) ≤ (1 - (2 : ℝ) ^ (-(2 * s)))⁻¹ := inv_nonneg.2 h4.le
  exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (by linarith only [h5, h6])

/-- The dimensional constant of the gradient comparison. -/
noncomputable def gagliardoGradientConst (d : ℕ) (s : ℝ) : ℝ :=
  Real.sqrt (gagliardoOscillationConst d s) * (d : ℝ)

/-- The dimensional constant is nonnegative. -/
theorem gagliardoGradientConst_nonneg (d : ℕ) (s : ℝ) :
    0 ≤ gagliardoGradientConst d s :=
  mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg d)

private theorem sqrt_const_identity {Q : TriadicCube d} {s : ℝ} (hs : 0 < s)
    (hs1 : s < 1) (hd : 0 < d) :
    Real.sqrt (gagliardoOscillationConst d s *
        (((d : ℝ) * cubeScaleFactor Q) ^ (2 - 2 * s) * (d : ℝ) ^ (2 * s)))
      = gagliardoGradientConst d s * cubeScaleFactor Q ^ (1 - s) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hLpos : (0 : ℝ) < cubeScaleFactor Q := by
    rw [cubeScaleFactor]
    positivity
  have hgoc := gagliardoOscillationConst_nonneg' d hs hs1
  have hsplit : ((d : ℝ) * cubeScaleFactor Q) ^ (2 - 2 * s) * (d : ℝ) ^ (2 * s)
      = (d : ℝ) ^ (2 : ℕ) * (cubeScaleFactor Q ^ (1 - s)) ^ (2 : ℕ) := by
    rw [Real.mul_rpow hdR.le hLpos.le]
    have hd2 : (d : ℝ) ^ (2 - 2 * s) * (d : ℝ) ^ (2 * s) = (d : ℝ) ^ (2 : ℕ) := by
      rw [← Real.rpow_add hdR, show (2 - 2 * s) + 2 * s = (2 : ℝ) by ring,
        ← Real.rpow_natCast (d : ℝ) 2]
      norm_num
    have hL2 : (cubeScaleFactor Q ^ (1 - s)) ^ (2 : ℕ)
        = cubeScaleFactor Q ^ (2 - 2 * s) := by
      rw [← Real.rpow_natCast (cubeScaleFactor Q ^ (1 - s)) 2,
        ← Real.rpow_mul hLpos.le]
      norm_num
      congr 1
      ring
    rw [hL2, ← hd2]
    ring
  rw [hsplit, gagliardoGradientConst]
  rw [show gagliardoOscillationConst d s *
      ((d : ℝ) ^ (2 : ℕ) * (cubeScaleFactor Q ^ (1 - s)) ^ (2 : ℕ))
      = (Real.sqrt (gagliardoOscillationConst d s) * (d : ℝ) *
          cubeScaleFactor Q ^ (1 - s)) ^ (2 : ℕ) by
    rw [mul_pow, mul_pow, Real.sq_sqrt hgoc]
    ring]
  exact Real.sqrt_sq (by
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hdR.le)
      (Real.rpow_nonneg hLpos.le _))

/-- **The Gagliardo seminorm of an `H¹` field is controlled by its gradient.** -/
theorem cubeEuclideanGagliardoESeminorm_le_of_contDiff {Q : TriadicCube d} {s : ℝ}
    (hs : 0 < s) (hs1 : s < 1) (hd : 0 < d) {G : Vec d → Vec d}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    cubeEuclideanGagliardoESeminorm Q s 2 (hilbertifyVecField G) ≤
      ENNReal.ofReal (gagliardoGradientConst d s * cubeScaleFactor Q ^ (1 - s)) *
        cubeLpENorm Q 2 (jacobianFrobeniusMagnitude G) := by
  classical
  set K : ℝ := gagliardoOscillationConst d s *
    (((d : ℝ) * cubeScaleFactor Q) ^ (2 - 2 * s) * (d : ℝ) ^ (2 * s)) with hK
  have hKnn : 0 ≤ K := by
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have hLpos : (0 : ℝ) < cubeScaleFactor Q := by
      rw [cubeScaleFactor]
      positivity
    rw [hK]
    exact mul_nonneg (gagliardoOscillationConst_nonneg' d hs hs1)
      (mul_nonneg (Real.rpow_nonneg (mul_pos hdR hLpos).le _)
        (Real.rpow_nonneg hdR.le _))
  have hmeas : Gagliardo.gagliardoCubeMeasure Q
      = ENNReal.ofReal (cubeVolume Q)⁻¹ •
        ((volume.prod volume).restrict (cubeSet Q ×ˢ cubeSet Q)) := by
    rw [Gagliardo.gagliardoCubeMeasure, normalizedCubeMeasure, cubeMeasure,
      Measure.prod_smul_left, Measure.prod_restrict]
  have hjac : ∀ w : Vec d,
      ‖jacobianFrobeniusMagnitude G w‖ₑ ^ (2 : ℝ)
        = ENNReal.ofReal (jacobianFrobeniusMagnitude G w ^ 2) := by
    intro w
    rw [Real.enorm_eq_ofReal_abs,
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    rw [show |jacobianFrobeniusMagnitude G w| ^ (2 : ℝ)
        = |jacobianFrobeniusMagnitude G w| ^ (2 : ℕ) by
      rw [← Real.rpow_natCast _ 2]; norm_num]
    exact sq_abs _
  have hLHS : cubeEuclideanGagliardoESeminorm Q s 2 (hilbertifyVecField G)
      = (ENNReal.ofReal (cubeVolume Q)⁻¹ *
          ∫⁻ z in cubeSet Q ×ˢ cubeSet Q,
            ‖euclideanGagliardoKernel s 2 (hilbertifyVecField G) z‖ₑ ^ (2 : ℝ)
            ∂(volume.prod volume)) ^ ((1 : ℝ) / 2) := by
    rw [cubeEuclideanGagliardoESeminorm,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
        (aestronglyMeasurable_euclideanGagliardoKernel (s := s) (f := hilbertifyVecField G)
          ((HilbertVec.ofVecL d).continuous.comp hG.continuous).aestronglyMeasurable), hmeas,
      lintegral_smul_measure, smul_eq_mul,
      show ((2 : ℝ≥0∞).toReal) = (2 : ℝ) from by norm_num]
  have hRHS : cubeLpENorm Q 2 (jacobianFrobeniusMagnitude G)
      = (ENNReal.ofReal (cubeVolume Q)⁻¹ *
          ∫⁻ w in cubeSet Q,
            ENNReal.ofReal (jacobianFrobeniusMagnitude G w ^ 2)) ^ ((1 : ℝ) / 2) := by
    rw [cubeLpENorm, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
        (continuous_jacobianFrobeniusMagnitude hG).aestronglyMeasurable,
      normalizedCubeMeasure, cubeMeasure, lintegral_smul_measure, smul_eq_mul,
      show ((2 : ℝ≥0∞).toReal) = (2 : ℝ) from by norm_num]
    congr 2
    exact lintegral_congr fun w => hjac w
  rw [hLHS, hRHS, ← sqrt_const_identity (Q := Q) hs hs1 hd, ← hK,
    Real.sqrt_eq_rpow,
    ← ENNReal.ofReal_rpow_of_nonneg hKnn (by norm_num : (0:ℝ) ≤ (1:ℝ)/2),
    ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ (1:ℝ)/2)]
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  calc ENNReal.ofReal (cubeVolume Q)⁻¹ *
        ∫⁻ z in cubeSet Q ×ˢ cubeSet Q,
          ‖euclideanGagliardoKernel s 2 (hilbertifyVecField G) z‖ₑ ^ (2 : ℝ)
          ∂(volume.prod volume)
      ≤ ENNReal.ofReal (cubeVolume Q)⁻¹ * (ENNReal.ofReal K *
          ∫⁻ w in cubeSet Q,
            ENNReal.ofReal (jacobianFrobeniusMagnitude G w ^ 2)) :=
        mul_le_mul' le_rfl (lintegral_enorm_kernel_sq_le hs hs1 hd hG)
    _ = ENNReal.ofReal K * (ENNReal.ofReal (cubeVolume Q)⁻¹ *
          ∫⁻ w in cubeSet Q,
            ENNReal.ofReal (jacobianFrobeniusMagnitude G w ^ 2)) := by ring

end

end Norms
end Section2
end SuperdiffusionCLT
