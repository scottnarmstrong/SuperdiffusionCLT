/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5
public import SuperdiffusionCLT.Frozen.Section2.CoefficientCutoff
public import SuperdiffusionCLT.Section3.ResponseFields.Definitions
public import SuperdiffusionCLT.Section3.ResponseFields.Norms
public import SuperdiffusionCLT.Section3.ResponseFields.StationaryComparison
public import SuperdiffusionCLT.Section3.ResponseFields.LpEstimates
public import SuperdiffusionCLT.Section3.ResponseFields.HminusOneDuality
public import SuperdiffusionCLT.Section2.Norms.FractionalHs
public import SuperdiffusionCLT.Section3.Setup.Scales
public import SuperdiffusionCLT.Section3.Setup.Parameters
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementLinftyLargeCube
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementCubeMomentLocality
public import Homogenization.Probability.IndependentSums.WeakOrlicz
public import Homogenization.Book.Ch02.Matrices
public import Homogenization.Book.Ch02.Block
public import Homogenization.Geometry.TriadicPartition
public import Homogenization.Geometry.CubeMeasure
public import Homogenization.Besov.Localization
public import Homogenization.Sobolev.H1.BasicLemmas
public import Homogenization.Sobolev.Foundations.CubeCoerciveH1
public import Homogenization.Sobolev.PotentialSolenoidalL2Recovery

/-!
# The second term of the right-hand side: `l.RHS.term2`

The statement `e.RHS.term2` is posed in the paper before `l.RHS.term2`.  In the
formalized statement the cubewise lattice average
`avsum_{z ∈ 3^nℤ^d ∩ cu_m}` is rendered by the carrier
`largeCubeSubcubes d S.n S.m` with the uniform weight `(card)⁻¹`, the inner
`⨍_{z+cu_n}` is `volumeAverage (openCubeSet z)`, and the glued gradient fields
`uNGlued`, `uTildeGlued` and the proxy mean `pTilde` are carried as free
binders.

## Contents

This module carries the public helper lemmas that the proof of `l.RHS.term2`
uses; the two auxiliary inputs below are taken as explicit hypotheses by the
proof of the main theorem.  The elementary identities used are taken from the
modules where they are proved (see the sections below for the exact names).

## The proof

The proof is the three-term display of the proof of `l.RHS.term2`: inside each
inner cube average,
`∇u_n − p = (∇u_n − ∇ũ_n) + (∇ũ_n − p̃) + (p̃ − p)`,
so the pairing splits into three pieces which are estimated separately.

* Pieces 1 and 3 (the `∇u_n − ∇ũ_n` and `p̃ − p` pieces) are Cauchy-Schwarz
  against the transported field `R = (k_{L'} − k_ℓ) ∇w` in `ω` and in the cube,
  and are closed against the first displayed input `hRbounds` and the first
  summand of `hProxyError`.  The transport of the cutoff difference into
  `R` uses that `(k_{L'} − k_ℓ)(x)` is a finite sum of skew-symmetric shell
  matrices (`finiteShellIncrement_skew`), so `ᵗ(k_{L'} − k_ℓ) = −(k_{L'} − k_ℓ)`
  and the pairing density `∇w · (k_{L'} − k_ℓ)(∇u_n − p)` equals
  `−(k_{L'} − k_ℓ) ∇w · (∇u_n − p)`.
* Piece 2 (the `∇ũ_n − p̃` piece) is step `l.RHS.term2#independence-decoupling`:
  the expectation of the pairing of the proxy with `p̃`
  equals the expectation of the *centered* pairing, i.e. of the pairing of
  `R − (R)_{z+cu_n}` with `∇ũ_n − (∇ũ_n)_{z+cu_n}`.  That step is the explicit
  hypothesis `hDecouple` below, in its exact mathematical shape.
  The centered pairing is then Cauchy-Schwarz in the cube and in `ω` against
  the per-cube Poincaré bound `l.RHS.term2#poincare-per-cube`:
  `(R − (R)_{z+cu_n})` is controlled by `3^n ∇R` through the coercive estimate
  `scaledTranslatedCubeMeanZeroH1CoerciveEstimate`, and `∇R` enters through
  the second summand of `hRbounds`, while `∇ũ_n − (∇ũ_n)_{z+cu_n}` is
  controlled by `∇ũ_n − p̃` through the triangle inequality, Jensen's
  inequality for the cube average and the second displayed input
  `hProxyEnergy`.
* The closing arithmetic uses the duality `|p| σ̄_{L',*}^{1/2}(cu_n) = 1` of
  `e.Sec3.p.q.def` (proved from `vecNormSq_testVector` and `sigmaBarStarInvSqrt_pos`)
  and `ν ≤ 1`.

## The two auxiliary inputs

The three displayed inputs `hRbounds`, `hProxyError`, `hProxyEnergy` are those
of the statement; the glued fields are free binders, so the proof needs two
further inputs in their exact mathematical shapes, documented here:

* `hDecouple`, step `l.RHS.term2#independence-decoupling`:
  for every sub-cube `z` of the large cube, the expectation of the pairing of
  the proxy field `∇ũ_n` with `p̃` equals the expectation of the pairing of the
  centered fields `(∇w − (∇w · (k_{L'} − k_ℓ))_{z+cu_n})` and
  `(∇ũ_n − (∇ũ_n)_{z+cu_n})`.
* `hMeas`: the measurability facts that make the expectation arguments of the
  proof meaningful.  The integrand of the displayed conclusion depends on the
  free binders `w`, `uNGlued`, `uTildeGlued`, so no measurability in `ω` or in
  `y` is available from the type of the statement; the proof needs (a) the
  components of the weak gradient field `DR` of `R` to be strongly measurable
  in `y` (so that the per-cube H¹ structure needed by the coercive estimate
  exists), (b) the transported field to be strongly measurable in `y`, and
  (c) the four cube-norm functions of `ω` and the three per-cube pairing
  functions of `ω` to be measurable (so that the Cauchy-Schwarz steps in `ω`
  are instances of the Hölder inequality for the lower integral).  In
  the intended construction every one of these holds: the fields are
  measurable functions of the sample `ω` and of the point, and the norms are
  measurable by composition.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The cutoff difference and its skew symmetry -/

/-- The difference of the two cutoffs `(k_{L'} − k_ℓ)(x)` is the finite shell
increment over the interval `(ℓ, L']`. -/
theorem coefficientCutoff_sub_apply (omega : ShellSeq d) (nu : ℝ)
    (ell LPrime : ℕ) (h : ell < LPrime) (x : Vec d) :
    (coefficientCutoff nu omega LPrime).toCoeffField x -
        (coefficientCutoff nu omega ell).toCoeffField x =
      (finiteShellIncrement omega ell LPrime).toCoeffField x := by
  simp only [RegCoeffField.toCoeffField_apply]
  have hS1 : streamCutoff omega LPrime x =
      ∑ n ∈ Finset.range (LPrime + 1), shellReg omega n x := by
    simp only [streamCutoff, RegCoeffField.finset_sum_apply]
  have hS2 : streamCutoff omega ell x =
      ∑ n ∈ Finset.range (ell + 1), shellReg omega n x := by
    simp only [streamCutoff, RegCoeffField.finset_sum_apply]
  rw [show coefficientCutoff nu omega LPrime x =
        RegCoeffField.constRegCoeffField (nu • (1 : Mat d)) x +
          streamCutoff omega LPrime x from rfl,
    show coefficientCutoff nu omega ell x =
        RegCoeffField.constRegCoeffField (nu • (1 : Mat d)) x +
          streamCutoff omega ell x from rfl,
    hS1, hS2, finiteShellIncrement_apply]
  have hsplit : Finset.range (LPrime + 1) = Finset.range (ell + 1) ∪
      Finset.Ioc ell LPrime := by
    ext n
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.range (ell + 1)) (Finset.Ioc ell LPrime) := by
    rw [Finset.disjoint_iff_inter_eq_empty, Finset.eq_empty_iff_forall_notMem]
    intro n hn
    rw [Finset.mem_inter, Finset.mem_range, Finset.mem_Ioc] at hn
    omega
  rw [hsplit, Finset.sum_union hdisj]
  show (RegCoeffField.constRegCoeffField (nu • (1 : Mat d))).toFun x +
        ((∑ n ∈ Finset.range (ell + 1), (shellReg omega n).toFun x) +
          ∑ n ∈ Finset.Ioc ell LPrime, (shellReg omega n).toFun x) -
        ((RegCoeffField.constRegCoeffField (nu • (1 : Mat d))).toFun x +
          ∑ n ∈ Finset.range (ell + 1), (shellReg omega n).toFun x) =
      ∑ n ∈ Finset.Ioc ell LPrime, (shellReg omega n).toFun x
  abel

/-! ## Algebra of the ambient carriers

The elementary identities `vecDot_add_right`, `vecDot_add_left`,
`vecDot_neg_left`, `vecDot_neg_right`, `matVecMul_neg` (the negated-vector
form) and the transpose transport `vecDot x (matVecMul (matTranspose A) y) =
vecDot (matVecMul A x) y` are proved in `Homogenization.Ambient.BlockMatrix`
(imported above); the negated-matrix form `matVecMul (-A) x = -matVecMul A x`
is proved there as `neg_matVecMul`.  The anti-symmetry transport
`vecDot g (matVecMul M u) = -vecDot (matVecMul M g) u` for
`matTranspose M = -M` is
`SuperdiffusionCLT.Section2.CoarseGraining.vecDot_matVecMul_swap_of_skew`,
and `matTranspose ((finiteShellIncrement omega n m).toCoeffField x) =
-(finiteShellIncrement omega n m).toCoeffField x` is `finiteShellIncrement_skew`
(up to `RegCoeffField.toCoeffField_apply`, which is defeq).  No duplicate
copies are restated here. -/

/-- The matrix-vector pairing `g · (A u)` is the pairing of the row vector
`g ᵥ* A` with `u`. -/
theorem vecDot_matVecMul_vecMul (g : Vec d) (A : Mat d) (u : Vec d) :
    vecDot g (matVecMul A u) = vecDot (Matrix.vecMul g A) u := by
  simp only [vecDot, matVecMul, Matrix.vecMul, dotProduct, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The pairing with a matrix product transports the transpose to the other
slot (`A` in the middle slot form). -/
theorem vecDot_matVecMul_transpose (x : Vec d) (A : Mat d) (y : Vec d) :
    vecDot x (matVecMul A y) = vecDot (matVecMul (matTranspose A) x) y := by
  have h : Matrix.vecMul x A = matVecMul (matTranspose A) x := by
    funext i
    simp only [Matrix.vecMul, dotProduct, matVecMul, matTranspose, Matrix.transpose_apply]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [vecDot_matVecMul_vecMul, h]

/-! ## The sub-cube family of the large cube -/

/-- The normalized average over `cu_l` is the plain average of the normalized
averages over the scale-`n` sub-cubes `z`, `z ∈ largeCubeSubcubes d n l`. -/
theorem volumeAverage_avsum_openCubeSet {n l : ℕ} {f : Vec d → ℝ}
    (hf : ∀ R ∈ largeCubeSubcubes d n l, IntegrableOn f (openCubeSet R)) :
    volumeAverage (openCubeSet (originCube d (l : ℤ))) f =
      ((largeCubeSubcubes d n l).card : ℝ)⁻¹ *
        ∑ R ∈ largeCubeSubcubes d n l, volumeAverage (openCubeSet R) f := by
  have hsub : ∀ R ∈ largeCubeSubcubes d n l, IntegrableOn f (cubeSet R) := fun R hR =>
    (hf R hR).congr_set_ae (cubeSet_ae_eq_openCubeSet R)
  have hpart : volumeAverage (cubeSet (originCube d (l : ℤ))) f =
      ((largeCubeSubcubes d n l).card : ℝ)⁻¹ *
        ∑ R ∈ largeCubeSubcubes d n l, volumeAverage (cubeSet R) f := by
    rw [show largeCubeSubcubes d n l =
      descendantsAtDepth (originCube d (l : ℤ)) (l - n) from rfl]
    exact volumeAverage_cubeSet_eq_inv_card_mul_sum_descendants (originCube d (l : ℤ)) (l - n) hsub
  have hL : volumeAverage (openCubeSet (originCube d (l : ℤ))) f =
      volumeAverage (cubeSet (originCube d (l : ℤ))) f :=
    (volumeAverage_cubeSet_eq_openCubeSet (originCube d (l : ℤ)) f).symm
  rw [hL, hpart]
  refine congrArg (fun t => ((largeCubeSubcubes d n l).card : ℝ)⁻¹ * t) ?_
  exact Finset.sum_congr rfl fun R _ => volumeAverage_cubeSet_eq_openCubeSet R f

/-! ## `L²` membership on the open cube -/

theorem memVectorL2_mono {U V : Set (Vec d)} {F : Vec d → Vec d} (hVU : V ⊆ U)
    (hF : MemVectorL2 U F) : MemVectorL2 V F :=
  hF.mono_measure (MeasureTheory.Measure.restrict_mono_set volume hVU)

/-- The scalar components of a vector `L²` field are scalar `L²` functions. -/
theorem memL2On_component_of_memVectorL2 {U : Set (Vec d)} {F : Vec d → Vec d}
    (hF : MemVectorL2 U F) (i : Fin d) : MemL2On U (fun x => (F x) i) := by
  let T : (Fin d → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  exact T.comp_memLp' hF

theorem memVectorL2_sub_const {Q : TriadicCube d} {F : Vec d → Vec d} (c : Vec d)
    (hF : MemVectorL2 (openCubeSet Q) F) : MemVectorL2 (openCubeSet Q) (fun x => F x - c) :=
  hF.sub (memVectorL2_const c)

/-! ## Measurability on the normalized cube measure -/

theorem aestronglyMeasurable_hilbertifyVecField_of_memVectorL2
    {Q : TriadicCube d} {F : Vec d → Vec d} (hF : MemVectorL2 (openCubeSet Q) F) :
    AEStronglyMeasurable (hilbertifyVecField F) (normalizedCubeMeasure Q) := by
  have h : AEStronglyMeasurable (hilbertifyVecField F) (volume.restrict (openCubeSet Q)) :=
    (memHilbertVectorL2_hilbertifyVecField hF).aestronglyMeasurable
  rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
  exact h.smul_measure (ENNReal.ofReal ((cubeVolume Q)⁻¹))

/-! ## Cube-average algebra -/

theorem volumeAverage_openCubeSet_eq_integral_normalizedCubeMeasure
    (Q : TriadicCube d) (f : Vec d → ℝ) :
    volumeAverage (openCubeSet Q) f = ∫ x, f x ∂normalizedCubeMeasure Q := by
  rw [integral_normalizedCubeMeasure_eq, ← volume_openCubeSet_toReal]
  rfl

theorem volumeAverage_add' {U : Set (Vec d)} {f g : Vec d → ℝ}
    (hf : IntegrableOn f U volume) (hg : IntegrableOn g U volume) :
    volumeAverage U (fun y => f y + g y) = volumeAverage U f + volumeAverage U g := by
  simp only [volumeAverage]
  rw [MeasureTheory.integral_add hf hg]
  ring

/-- Pulling a constant vector out of a normalized average. -/
theorem volumeAverage_vecDot_const_left {U : Set (Vec d)} (c : Vec d)
    {F : Vec d → Vec d} (hF : ∀ i, IntegrableOn (fun y => F y i) U volume) :
    volumeAverage U (fun y => vecDot c (F y)) = vecDot c (volumeAverageVec U F) := by
  have hint : ∫ y in U, (∑ i, c i * F y i) ∂volume
      = ∑ i, c i * ∫ y in U, F y i ∂volume := by
    rw [MeasureTheory.integral_finsetSum _ (fun i _ => (hF i).const_mul (c i))]
    exact Finset.sum_congr rfl fun i _ => MeasureTheory.integral_const_mul _ _
  show (volume U).toReal⁻¹ * ∫ y in U, (∑ i, c i * F y i) ∂volume
      = ∑ i, c i * volumeAverage U (fun y => F y i)
  rw [hint, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by
    simp only [volumeAverage]
    ring

theorem vecDot_sub_left' (x y z : Vec d) :
    vecDot (x - y) z = vecDot x z - vecDot y z := by
  simp only [vecDot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- The add-and-subtract step on a single cube: the normalized average of the
pairing `g · F` splits into the pairing of the centered field `g − (g)_U`
against `F` plus the pairing of the two cube averages. -/
theorem volumeAverage_vecDot_split {U : Set (Vec d)} (g F : Vec d → Vec d)
    (hgF : IntegrableOn (fun y => vecDot (g y) (F y)) U volume)
    (hF : ∀ i, IntegrableOn (fun y => F y i) U volume) :
    volumeAverage U (fun y => vecDot (g y) (F y)) =
      volumeAverage U (fun y => vecDot (g y - volumeAverageVec U g) (F y)) +
        vecDot (volumeAverageVec U g) (volumeAverageVec U F) := by
  set c : Vec d := volumeAverageVec U g with hc
  have hcF : IntegrableOn (fun y => vecDot c (F y)) U volume := by
    have : (fun y => vecDot c (F y)) = fun y => ∑ i, c i * F y i := rfl
    rw [this]
    exact MeasureTheory.integrable_finsetSum _ (fun i _ => (hF i).const_mul (c i))
  have hsplit : ∀ y : Vec d,
      vecDot (g y) (F y) = vecDot (g y - c) (F y) + vecDot c (F y) := by
    intro y
    rw [vecDot_sub_left']
    ring
  have hcenter : IntegrableOn (fun y => vecDot (g y - c) (F y)) U volume := by
    have heq : (fun y => vecDot (g y - c) (F y))
        = fun y => vecDot (g y) (F y) - vecDot c (F y) := by
      funext y; rw [vecDot_sub_left']
    rw [heq]
    exact hgF.sub hcF
  calc volumeAverage U (fun y => vecDot (g y) (F y))
      = volumeAverage U (fun y => vecDot (g y - c) (F y) + vecDot c (F y)) := by
        exact congrArg (volumeAverage U) (funext hsplit)
    _ = volumeAverage U (fun y => vecDot (g y - c) (F y))
          + volumeAverage U (fun y => vecDot c (F y)) := volumeAverage_add' hcenter hcF
    _ = volumeAverage U (fun y => vecDot (g y - c) (F y)) + vecDot c (volumeAverageVec U F) := by
        rw [volumeAverage_vecDot_const_left c hF]

/-! ## Cauchy-Schwarz on the open cube -/

theorem ofReal_volumeAverage_openCubeSet_vecDot_le {Q : TriadicCube d}
    {a b : Vec d → Vec d}
    (ha : MemVectorL2 (openCubeSet Q) a) (hb : MemVectorL2 (openCubeSet Q) b) :
    ENNReal.ofReal (volumeAverage (openCubeSet Q) (fun x => vecDot (a x) (b x))) ≤
      vecCubeLpENorm Q 2 a * vecCubeLpENorm Q 2 b := by
  have hma : AEStronglyMeasurable (hilbertifyVecField a) (normalizedCubeMeasure Q) :=
    aestronglyMeasurable_hilbertifyVecField_of_memVectorL2 ha
  have hmb : AEStronglyMeasurable (hilbertifyVecField b) (normalizedCubeMeasure Q) :=
    aestronglyMeasurable_hilbertifyVecField_of_memVectorL2 hb
  have hbound : ENNReal.ofReal
      (∫ x, vecDot (a x) (b x) ∂normalizedCubeMeasure Q) ≤
      ∫⁻ x, ‖vecDot (a x) (b x)‖ₑ ∂normalizedCubeMeasure Q := by
    by_cases hint : Integrable (fun x => vecDot (a x) (b x)) (normalizedCubeMeasure Q)
    · calc ENNReal.ofReal (∫ x, vecDot (a x) (b x) ∂normalizedCubeMeasure Q)
        ≤ ENNReal.ofReal (∫ x, ‖vecDot (a x) (b x)‖ ∂normalizedCubeMeasure Q) :=
          ENNReal.ofReal_le_ofReal
            (le_trans (le_abs_self _)
              (norm_integral_le_integral_norm (fun x => vecDot (a x) (b x))))
      _ = ∫⁻ x, ‖vecDot (a x) (b x)‖ₑ ∂normalizedCubeMeasure Q :=
          ofReal_integral_norm_eq_lintegral_enorm hint
    · rw [integral_undef hint]
      simp
  have hptr : ∀ x : Vec d, ‖vecDot (a x) (b x)‖ₑ ≤
      ‖hilbertifyVecField a x‖ₑ * ‖hilbertifyVecField b x‖ₑ := by
    intro x
    have h : |vecDot (a x) (b x)| ≤
        ‖hilbertifyVecField a x‖ * ‖hilbertifyVecField b x‖ := by
      simpa [hilbertifyVecField, HilbertVec.inner_def] using
        abs_real_inner_le_norm (hilbertifyVecField a x) (hilbertifyVecField b x)
    calc ‖vecDot (a x) (b x)‖ₑ = ENNReal.ofReal |vecDot (a x) (b x)| :=
          Real.enorm_eq_ofReal_abs _
      _ ≤ ENNReal.ofReal (‖hilbertifyVecField a x‖ * ‖hilbertifyVecField b x‖) :=
          ENNReal.ofReal_le_ofReal h
      _ = ‖hilbertifyVecField a x‖ₑ * ‖hilbertifyVecField b x‖ₑ := by
          rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm,
            ofReal_norm]
  rw [volumeAverage_openCubeSet_eq_integral_normalizedCubeMeasure]
  calc ENNReal.ofReal (∫ x, vecDot (a x) (b x) ∂normalizedCubeMeasure Q)
      ≤ ∫⁻ x, ‖vecDot (a x) (b x)‖ₑ ∂normalizedCubeMeasure Q := hbound
    _ ≤ ∫⁻ x, ‖hilbertifyVecField a x‖ₑ * ‖hilbertifyVecField b x‖ₑ
          ∂normalizedCubeMeasure Q := lintegral_mono hptr
    _ ≤ (∫⁻ x, ‖hilbertifyVecField a x‖ₑ ^ (2 : ℝ) ∂normalizedCubeMeasure Q) ^
            (1 / (2 : ℝ)) *
          (∫⁻ x, ‖hilbertifyVecField b x‖ₑ ^ (2 : ℝ) ∂normalizedCubeMeasure Q) ^
            (1 / (2 : ℝ)) :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq (normalizedCubeMeasure Q)
          Real.HolderConjugate.two_two hma.enorm hmb.enorm
    _ = vecCubeLpENorm Q 2 a * vecCubeLpENorm Q 2 b := by
        rw [vecCubeLpENorm, vecCubeLpENorm, Section2.Norms.cubeLpENorm,
          Section2.Norms.cubeLpENorm,
          eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hma,
          eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hmb]
        norm_num

/-- The absolute form of the Cauchy-Schwarz bound. -/
theorem abs_volumeAverage_openCubeSet_vecDot_le {Q : TriadicCube d}
    {a b : Vec d → Vec d}
    (ha : MemVectorL2 (openCubeSet Q) a) (hb : MemVectorL2 (openCubeSet Q) b)
    (ha' : vecCubeLpENorm Q 2 a ≠ ⊤) (hb' : vecCubeLpENorm Q 2 b ≠ ⊤) :
    |volumeAverage (openCubeSet Q) (fun x => vecDot (a x) (b x))| ≤
      (vecCubeLpENorm Q 2 a).toReal * (vecCubeLpENorm Q 2 b).toReal := by
  have hB : ENNReal.ofReal (volumeAverage (openCubeSet Q) (fun x => vecDot (a x) (b x))) ≤
      vecCubeLpENorm Q 2 a * vecCubeLpENorm Q 2 b :=
    ofReal_volumeAverage_openCubeSet_vecDot_le ha hb
  have hna : MemVectorL2 (openCubeSet Q) (fun x => -a x) := ha.neg
  have hB' : ENNReal.ofReal
      (volumeAverage (openCubeSet Q) (fun x => vecDot (-a x) (b x))) ≤
      vecCubeLpENorm Q 2 a * vecCubeLpENorm Q 2 b := by
    have h := ofReal_volumeAverage_openCubeSet_vecDot_le hna hb
    rw [show vecCubeLpENorm Q 2 (fun x : Vec d => -a x) = vecCubeLpENorm Q 2 a from
      vecCubeLpENorm_neg Q 2 a] at h
    exact h
  have hflip : volumeAverage (openCubeSet Q) (fun x => vecDot (-a x) (b x)) =
      -(volumeAverage (openCubeSet Q) (fun x => vecDot (a x) (b x))) := by
    have h1 : volumeAverage (openCubeSet Q) (fun x => vecDot (-a x) (b x)) =
        volumeAverage (openCubeSet Q) (fun x => -vecDot (a x) (b x)) :=
      congrArg (volumeAverage (openCubeSet Q))
        (funext fun x => vecDot_neg_left (a x) (b x))
    rw [h1]
    simp only [volumeAverage, integral_neg, mul_neg]
  have htop : vecCubeLpENorm Q 2 a * vecCubeLpENorm Q 2 b ≠ ⊤ :=
    ENNReal.mul_ne_top ha' hb'
  have hrhs : 0 ≤ (vecCubeLpENorm Q 2 a).toReal * (vecCubeLpENorm Q 2 b).toReal := by
    positivity
  rw [abs_le]
  constructor
  · -- `-rhs ≤ X`
    rcases le_total 0 (volumeAverage (openCubeSet Q) (fun x => vecDot (a x) (b x))) with
      hsign | hsign
    · exact le_trans (neg_nonpos.2 hrhs) hsign
    · have hpos0 : 0 ≤ -(volumeAverage (openCubeSet Q) (fun x => vecDot (a x) (b x))) :=
        neg_nonneg.2 hsign
      rw [hflip] at hB'
      have hstep : -(volumeAverage (openCubeSet Q) (fun x => vecDot (a x) (b x))) ≤
          (vecCubeLpENorm Q 2 a).toReal * (vecCubeLpENorm Q 2 b).toReal := by
        calc -(volumeAverage (openCubeSet Q) (fun x => vecDot (a x) (b x))) =
            (ENNReal.ofReal (-(volumeAverage (openCubeSet Q)
              (fun x => vecDot (a x) (b x))))).toReal := (ENNReal.toReal_ofReal hpos0).symm
          _ ≤ (vecCubeLpENorm Q 2 a * vecCubeLpENorm Q 2 b).toReal :=
              (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top htop).2 hB'
          _ = (vecCubeLpENorm Q 2 a).toReal * (vecCubeLpENorm Q 2 b).toReal :=
              ENNReal.toReal_mul
      have hstep' := neg_le_neg hstep
      rwa [neg_neg] at hstep'
  · -- `X ≤ rhs`
    rcases le_total 0 (volumeAverage (openCubeSet Q) (fun x => vecDot (a x) (b x))) with
      hsign | hsign
    · calc volumeAverage (openCubeSet Q) (fun x => vecDot (a x) (b x)) =
          (ENNReal.ofReal (volumeAverage (openCubeSet Q)
            (fun x => vecDot (a x) (b x)))).toReal := (ENNReal.toReal_ofReal hsign).symm
      _ ≤ (vecCubeLpENorm Q 2 a * vecCubeLpENorm Q 2 b).toReal :=
          (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top htop).2 hB
      _ = (vecCubeLpENorm Q 2 a).toReal * (vecCubeLpENorm Q 2 b).toReal :=
          ENNReal.toReal_mul
    · exact le_trans hsign hrhs

/-! ## Norm algebra on the cubes -/

theorem vecCubeLpENorm_const_sq (Q : TriadicCube d) (v : Vec d) :
    (vecCubeLpENorm Q 2 (fun _ : Vec d => v)) ^ (2 : ℕ) = ENNReal.ofReal (vecNormSq v) := by
  rw [vecCubeLpENorm_two_sq Q _ aestronglyMeasurable_const, lintegral_const,
    normalizedCubeMeasure_apply_univ, mul_one]
  exact enorm_ofVec_sq v

theorem aestronglyMeasurable_normalizedCubeMeasure_iff {E : Type*} [NormedAddCommGroup E]
    (R : TriadicCube d) (f : Vec d → E) :
    AEStronglyMeasurable f (normalizedCubeMeasure R) ↔
      AEStronglyMeasurable f (volume.restrict (cubeSet R)) := by
  have hc0 : ENNReal.ofReal ((cubeVolume R)⁻¹) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (inv_pos.2 (cubeVolume_pos R))).ne'
  have hr : volume.restrict (openCubeSet R) = volume.restrict (cubeSet R) :=
    Measure.restrict_congr_set (cubeSet_ae_eq_openCubeSet R).symm
  rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet, hr]
  constructor
  · intro h
    have h' := h.smul_measure (ENNReal.ofReal ((cubeVolume R)⁻¹))⁻¹
    rwa [smul_smul, ENNReal.inv_mul_cancel hc0 ENNReal.ofReal_ne_top, one_smul] at h'
  · intro h
    exact h.smul_measure _

/-- The squared normalized cube norm of a field is the plain average of the
squared normalized cube norms over the sub-cubes at depth `j`. -/
theorem cubeLpENorm_two_sq_eq_inv_card_mul_sum {E : Type*} [NormedAddCommGroup E]
    {Q : TriadicCube d} (j : ℕ) (f : Vec d → E) :
    (Section2.Norms.cubeLpENorm Q 2 f) ^ (2 : ℕ) =
      ENNReal.ofReal (((descendantsAtDepth Q j).card : ℝ)⁻¹) *
        ∑ R ∈ descendantsAtDepth Q j, (Section2.Norms.cubeLpENorm R 2 f) ^ (2 : ℕ) := by
  classical
  have hcardpos : (0 : ℝ) < ((descendantsAtDepth Q j).card : ℝ) := by
    exact_mod_cast Finset.card_pos.2 (descendantsAtDepth_nonempty Q j)
  have hdisj : Set.PairwiseDisjoint
      (descendantsAtDepth Q j : Set (TriadicCube d))
      (fun z : TriadicCube d => cubeSet z) := pairwiseDisjoint_descendantsAtDepth Q j
  have hmeas : ∀ R ∈ descendantsAtDepth Q j, MeasurableSet (cubeSet R) :=
    fun R _ => measurableSet_cubeSet R
  have hcv : ∀ R ∈ descendantsAtDepth Q j,
      ((descendantsAtDepth Q j).card : ℝ) * cubeVolume R = cubeVolume Q := by
    intro R hR
    rw [cubeVolume_eq_card_mul_cubeVolume_of_mem_descendantsAtDepth hR]
  have hprod : ∀ R ∈ descendantsAtDepth Q j,
      (cubeVolume Q)⁻¹ * cubeVolume R = ((descendantsAtDepth Q j).card : ℝ)⁻¹ := by
    intro R hR
    have h1 := hcv R hR
    have h2 : ((descendantsAtDepth Q j).card : ℝ)⁻¹ * cubeVolume Q = cubeVolume R := by
      rw [← h1, inv_mul_cancel_left₀ (ne_of_gt hcardpos)]
    have h3 : cubeVolume Q ≠ 0 := by
      rw [← h1]
      exact mul_ne_zero (ne_of_gt hcardpos) (ne_of_gt (cubeVolume_pos R))
    calc (cubeVolume Q)⁻¹ * cubeVolume R
        = (cubeVolume Q)⁻¹ *
            (((descendantsAtDepth Q j).card : ℝ)⁻¹ * cubeVolume Q) := by rw [h2]
      _ = ((descendantsAtDepth Q j).card : ℝ)⁻¹ * ((cubeVolume Q)⁻¹ * cubeVolume Q) := by ring
      _ = ((descendantsAtDepth Q j).card : ℝ)⁻¹ := by rw [inv_mul_cancel₀ h3, mul_one]
  have hofreal : ∀ R ∈ descendantsAtDepth Q j, ENNReal.ofReal ((cubeVolume Q)⁻¹) *
      ENNReal.ofReal (cubeVolume R) =
        ENNReal.ofReal (((descendantsAtDepth Q j).card : ℝ)⁻¹) := by
    intro R hR
    rw [← ENNReal.ofReal_mul (le_of_lt (inv_pos.2 (cubeVolume_pos Q))), hprod R hR]
  have hset : cubeSet Q = ⋃ R ∈ descendantsAtDepth Q j, cubeSet R :=
    cubeSet_eq_iUnion_descendantsAtDepth Q j
  by_cases hfQ : AEStronglyMeasurable f (normalizedCubeMeasure Q)
  swap
  · have hex : ∃ R ∈ descendantsAtDepth Q j,
        ¬ AEStronglyMeasurable f (normalizedCubeMeasure R) := by
      by_contra hcon
      push Not at hcon
      apply hfQ
      rw [aestronglyMeasurable_normalizedCubeMeasure_iff, hset]
      have hU : AEStronglyMeasurable f (volume.restrict
          (⋃ R : {R // R ∈ descendantsAtDepth Q j}, cubeSet R.1)) :=
        aestronglyMeasurable_iUnion_iff.mpr fun R =>
          (aestronglyMeasurable_normalizedCubeMeasure_iff R.1 f).1 (hcon R.1 R.2)
      have hEq : (⋃ R : {R // R ∈ descendantsAtDepth Q j}, cubeSet R.1) =
          ⋃ R ∈ descendantsAtDepth Q j, cubeSet R := by
        ext x
        simp
      rwa [hEq] at hU
    obtain ⟨R, hR, hRm⟩ := hex
    have hRtop : (Section2.Norms.cubeLpENorm R 2 f) ^ (2 : ℕ) = ⊤ := by
      rw [Section2.Norms.cubeLpENorm, eLpNorm_of_not_aestronglyMeasurable hRm]
      simp
    have hQtop : (Section2.Norms.cubeLpENorm Q 2 f) ^ (2 : ℕ) = ⊤ := by
      rw [Section2.Norms.cubeLpENorm, eLpNorm_of_not_aestronglyMeasurable hfQ]
      simp
    have hsumtop : ∑ R ∈ descendantsAtDepth Q j,
        (Section2.Norms.cubeLpENorm R 2 f) ^ (2 : ℕ) = ⊤ :=
      ENNReal.sum_eq_top.2 ⟨R, hR, hRtop⟩
    rw [hQtop, hsumtop]
    have hne : ENNReal.ofReal (((descendantsAtDepth Q j).card : ℝ)⁻¹) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (inv_pos.2 hcardpos)).ne'
    simp [hne]
  have hfR : ∀ R ∈ descendantsAtDepth Q j,
      AEStronglyMeasurable f (normalizedCubeMeasure R) := by
    intro R hR
    rw [aestronglyMeasurable_normalizedCubeMeasure_iff]
    have hQ := (aestronglyMeasurable_normalizedCubeMeasure_iff Q f).1 hfQ
    refine hQ.mono_set ?_
    rw [hset]
    exact Set.subset_biUnion_of_mem (u := fun R => cubeSet R) hR
  have hpercube : ∀ R ∈ descendantsAtDepth Q j,
      ∫⁻ x, ‖f x‖ₑ ^ (2 : ℕ) ∂(volume.restrict (cubeSet R)) =
        ENNReal.ofReal (cubeVolume R) * (Section2.Norms.cubeLpENorm R 2 f) ^ (2 : ℕ) := by
    intro R hR
    have hpos : 0 < cubeVolume R := cubeVolume_pos R
    have h2 : ENNReal.ofReal (cubeVolume R) * ENNReal.ofReal ((cubeVolume R)⁻¹) = 1 := by
      rw [mul_comm, ← ENNReal.ofReal_mul (le_of_lt (inv_pos.2 hpos)),
        inv_mul_cancel₀ (ne_of_gt hpos), ENNReal.ofReal_one]
    have h1 : (Section2.Norms.cubeLpENorm R 2 f) ^ (2 : ℕ) =
        ENNReal.ofReal ((cubeVolume R)⁻¹) *
          ∫⁻ x, ‖f x‖ₑ ^ (2 : ℕ) ∂(volume.restrict (cubeSet R)) := by
      rw [Section2.Norms.cubeLpENorm, eLpNorm_two_sq _ _ (hfR R hR),
        normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet, lintegral_smul_measure,
        smul_eq_mul, Measure.restrict_congr_set (cubeSet_ae_eq_openCubeSet R)]
    rw [h1, ← mul_assoc, h2, one_mul]
  rw [Section2.Norms.cubeLpENorm, eLpNorm_two_sq _ _ hfQ,
    normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet, lintegral_smul_measure,
    smul_eq_mul, ← Measure.restrict_congr_set (cubeSet_ae_eq_openCubeSet Q),
    hset, lintegral_biUnion_finset hdisj hmeas]
  have hstep : ENNReal.ofReal ((cubeVolume Q)⁻¹) *
      ∑ R ∈ descendantsAtDepth Q j,
        ∫⁻ x, ‖f x‖ₑ ^ (2 : ℕ) ∂(volume.restrict (cubeSet R)) =
      ENNReal.ofReal (((descendantsAtDepth Q j).card : ℝ)⁻¹) *
        ∑ R ∈ descendantsAtDepth Q j, (Section2.Norms.cubeLpENorm R 2 f) ^ (2 : ℕ) := by
    have hsum1 : ∑ R ∈ descendantsAtDepth Q j,
        ∫⁻ x, ‖f x‖ₑ ^ (2 : ℕ) ∂(volume.restrict (cubeSet R)) =
      ∑ R ∈ descendantsAtDepth Q j, ENNReal.ofReal (cubeVolume R) *
        (Section2.Norms.cubeLpENorm R 2 f) ^ (2 : ℕ) :=
      Finset.sum_congr rfl fun R hR => hpercube R hR
    rw [hsum1,
      Finset.mul_sum (f := fun R : TriadicCube d => ENNReal.ofReal (cubeVolume R) *
        (Section2.Norms.cubeLpENorm R 2 f) ^ (2 : ℕ)),
      Finset.mul_sum (f := fun R : TriadicCube d =>
        (Section2.Norms.cubeLpENorm R 2 f) ^ (2 : ℕ))]
    exact Finset.sum_congr rfl fun R hR => by
      rw [← mul_assoc, hofreal R hR]
  exact hstep

end