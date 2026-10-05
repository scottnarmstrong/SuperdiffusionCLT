/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Sobolev.CubeSmoothDensityH2
public import SuperdiffusionCLT.Section2.Norms.FractionalDensityB

/-!
# Smooth `H²` density on a cube, and the order-`s` pairing duality it discharges

The fractional Hölder duality of the paper is reduced, in `Section2/Norms/FractionalDensityB.lean`,
to one explicit hypothesis `hH2`: for the field `G` and a matrix field `J` playing the role of
its weak Jacobian, smooth `g` with

`‖∇g - G‖_{L̲²(Q)} ≤ ε` and `‖∇²g - J‖_{L̲²(Q)} ≤ ε`.

This module discharges `hH2` for `G = ∇w` the weak gradient of an `H¹` function
carrying a weak Hessian `H`, with `J = H`. Nothing is hypothesised: the
approximants are the convex-approximation smoothings of `w` of
`Sobolev/CubeSmoothDensityH2.lean`, and the two transported identities

`∂_i(S_t w) = (1 - t) S_t(∂_i w)`, `∂_j∂_i(S_t w) = (1 - t)² S_t(H_{ij})`,

both valid at every point of the open cube, turn the two required convergences
into the single weighted `L²` convergence
`tendsto_eLpNorm_smul_cubeH2Smoothing_sub` applied coordinate by coordinate.

## From coordinates to the two carriers

The two norms of `hH2` are Euclidean, not coordinatewise: `vecCubeLpENorm Q 2`
measures the Euclidean magnitude of a vector field and `jacobianDistENorm Q`
the Frobenius magnitude of a matrix field. Both are dominated by the
corresponding sums of coordinate `L̲²(Q)` norms — `‖v‖ ≤ ∑ᵢ |vᵢ|` and, upstream,
`matrixFrobeniusMagnitude_le_sum_abs` — so the finitely many coordinate
convergences suffice; `cubeLpENorm_le_sum_abs` is the packaged form.

## The mean-zero question

The test class the duality is proved against does not constrain the potential:
the `hdense` binder of `Section2/Norms/NegativeNormPairingHalf.lean` asks only
for `ContDiff` and the two norm bounds, so no mean-zero normalization is needed
to consume `hH2`. The mean-zero variant is recorded anyway, for the
`Ĥ̲^{-1}(U)` test class of the paper, which does normalize its potentials;
subtracting a constant changes neither the gradient nor the Hessian.

## Main results

* `exists_cubeH2SmoothApprox`: the `H²` smooth approximation on the cube.
* `exists_cubeH2MeanZeroSmoothApprox`: the same with `cubeAverage Q g = 0`.
* `hH2_of_hasWeakHessianOn`: the same, in the exact shape of the `hH2` binder
  of `Section2/Norms/FractionalDensityB.lean`.
* `pairing_le_of_hasWeakHessianOn`: `pairing_le_of_hessianDensity` with both
  `hJm` and `hH2` discharged, i.e. the `hDual` binder of
  the term-4 statement of Section 3 for a Dirichlet-type gradient field.
-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Sobolev

open Homogenization
open Homogenization.Book.Ch02
open MeasureTheory
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section3.ResponseFields
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The normalized measure against the restricted volume -/

private theorem normalizedCubeMeasure_eq_smul_restrict (Q : TriadicCube d) :
    normalizedCubeMeasure Q
      = ENNReal.ofReal ((cubeVolume Q)⁻¹) • volume.restrict (openCubeSet Q) := by
  rw [normalizedCubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]

private theorem cubeLpENorm_eq_const_mul_eLpNorm (Q : TriadicCube d) {E : Type*}
    [NormedAddCommGroup E] (f : Vec d → E) :
    cubeLpENorm Q 2 f
      = ENNReal.ofReal ((cubeVolume Q)⁻¹) ^ (1 / (2 : ℝ≥0∞)).toReal *
        eLpNorm f 2 (volume.restrict (openCubeSet Q)) := by
  rw [cubeLpENorm, normalizedCubeMeasure_eq_smul_restrict Q,
    eLpNorm_smul_measure_of_ne_zero
      (ENNReal.ofReal_pos.2 (inv_pos.2 (cubeVolume_pos Q))).ne', smul_eq_mul]

/-- A sequence of fields whose `L²` norms on the open cube vanish also has
vanishing normalized `L̲²(Q)` norms: the two differ by one finite factor. -/
private theorem tendsto_cubeLpENorm_of_tendsto_eLpNorm (Q : TriadicCube d)
    {E : Type*} [NormedAddCommGroup E] {f : ℕ → Vec d → E}
    (h : Filter.Tendsto (fun n : ℕ => eLpNorm (f n) 2 (volume.restrict (openCubeSet Q)))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n : ℕ => cubeLpENorm Q 2 (f n)) Filter.atTop (nhds 0) := by
  have hK : ENNReal.ofReal ((cubeVolume Q)⁻¹) ^ (1 / (2 : ℝ≥0∞)).toReal ≠ ⊤ :=
    (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top).ne
  have hmul := ENNReal.Tendsto.const_mul h (Or.inr hK)
  rw [mul_zero] at hmul
  simpa only [cubeLpENorm_eq_const_mul_eLpNorm Q] using hmul

/-! ## Euclidean magnitudes against coordinate sums -/

private theorem norm_hilbertVec_ofVec_le_sum_abs (v : Vec d) :
    ‖HilbertVec.ofVec v‖ ≤ ∑ i : Fin d, |v i| := by
  have hnn : (0 : ℝ) ≤ ∑ i : Fin d, |v i| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hsq : ‖HilbertVec.ofVec v‖ ^ 2 ≤ (∑ i : Fin d, |v i|) ^ 2 := by
    rw [HilbertVec.norm_sq_eq_sum_sq]
    have hcoord : ∀ i : Fin d, (HilbertVec.ofVec v) i ^ 2 = |v i| ^ 2 := by
      intro i
      rw [sq_abs]
    rw [Finset.sum_congr rfl (fun i _ => hcoord i)]
    simpa [pow_two] using
      Finset.sum_sq_le_sq_sum_of_nonneg (s := (Finset.univ : Finset (Fin d)))
        (f := fun i => |v i|) (by intro _ _; exact abs_nonneg _)
  calc ‖HilbertVec.ofVec v‖
      = Real.sqrt (‖HilbertVec.ofVec v‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((∑ i : Fin d, |v i|) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ∑ i : Fin d, |v i| := Real.sqrt_sq hnn

/-- **Coordinate domination of a normalized `L̲²(Q)` norm.** If the pointwise
magnitude of `f` is at most the sum of the absolute values of finitely many
scalar fields, then the `L̲²(Q)` norm of `f` is at most the sum of theirs. -/
private theorem cubeLpENorm_le_sum_abs {Q : TriadicCube d} {ι : Type*} [Fintype ι]
    {E : Type*} [NormedAddCommGroup E] {f : Vec d → E} {h : ι → Vec d → ℝ}
    (hf : AEStronglyMeasurable f (normalizedCubeMeasure Q))
    (hmeas : ∀ p : ι, AEStronglyMeasurable (h p) (normalizedCubeMeasure Q))
    (hpt : ∀ x : Vec d, ‖f x‖ ≤ ∑ p : ι, |h p x|) :
    cubeLpENorm Q 2 f ≤ ∑ p : ι, cubeLpENorm Q 2 (h p) := by
  have hstep : cubeLpENorm Q 2 f ≤ cubeLpENorm Q 2 (fun x => ∑ p : ι, |h p x|) := by
    refine cubeLpENorm_mono_enorm hf (fun x => ?_)
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)]
    exact hpt x
  refine hstep.trans ?_
  have hfun : (fun x : Vec d => ∑ p : ι, |h p x|)
      = ∑ p : ι, fun x : Vec d => |h p x| := by
    funext x
    simp only [Finset.sum_apply]
  rw [cubeLpENorm, hfun]
  refine le_trans (eLpNorm_sum_le (by norm_num)) ?_
  refine Finset.sum_le_sum (fun p _ => ?_)
  rw [cubeLpENorm]
  exact eLpNorm_mono_enorm
    (by simpa only [Real.norm_eq_abs] using (hmeas p).norm) (fun x => by simp)

/-! ## The approximating sequence -/

/-- The `n`-th smooth approximant of `w`: the convex-approximation smoothing at
scale `1/(n + 2)`. -/
private def cubeH2Approx (Q : TriadicCube d) (w : H1Function (openCubeSet Q))
    (n : ℕ) : Vec d → ℝ :=
  cubeH2Smoothing Q w.toFun (cubeH2SmoothingScale n)

private theorem contDiff_cubeH2Approx (Q : TriadicCube d)
    (w : H1Function (openCubeSet Q)) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (cubeH2Approx Q w n) :=
  contDiff_cubeH2Smoothing w.memL2 (cubeH2SmoothingScale_pos n)

/-- The gradient field of `Section2/Norms/NegativeHatFullGradient.lean` is the Euclidean
gradient of `CoarseGraining`: `Pi.single i 1` is `basisVec i`. Rewriting with
this identity keeps the two spellings syntactically apart, so that no unifier
ever has to reduce a `fderiv` to compare them. -/
private theorem vecGradient_eq_euclideanGradient (g : Vec d → ℝ) :
    vecGradient g = euclideanGradient g := rfl

private theorem contDiff_euclideanGradient_apply {g : Vec d → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => euclideanGradient g x i) :=
  contDiff_pi.mp (contDiff_vecGradient hg) i

/-! ## The two coefficient sequences -/

private theorem tendsto_one_sub_cubeH2SmoothingScale :
    Filter.Tendsto (fun n : ℕ => 1 - cubeH2SmoothingScale n) Filter.atTop (nhds 1) := by
  simpa using (tendsto_const_nhds (x := (1 : ℝ)) (f := Filter.atTop (α := ℕ))).sub
    tendsto_cubeH2SmoothingScale_zero

private theorem abs_one_sub_cubeH2SmoothingScale_le (n : ℕ) :
    |1 - cubeH2SmoothingScale n| ≤ 1 := by
  have h0 := cubeH2SmoothingScale_pos n
  have h1 := cubeH2SmoothingScale_lt_one n
  rw [abs_of_nonneg (by linarith only [h1])]
  linarith only [h0]

private theorem tendsto_one_sub_cubeH2SmoothingScale_sq :
    Filter.Tendsto (fun n : ℕ => (1 - cubeH2SmoothingScale n) ^ 2) Filter.atTop
      (nhds 1) := by
  simpa using tendsto_one_sub_cubeH2SmoothingScale.pow 2

private theorem abs_one_sub_cubeH2SmoothingScale_sq_le (n : ℕ) :
    |(1 - cubeH2SmoothingScale n) ^ 2| ≤ 1 := by
  have h0 := cubeH2SmoothingScale_pos n
  have h1 := cubeH2SmoothingScale_lt_one n
  have hb : (0 : ℝ) ≤ 1 - cubeH2SmoothingScale n := by linarith only [h1]
  have hle : 1 - cubeH2SmoothingScale n ≤ 1 := by linarith only [h0]
  rw [abs_of_nonneg (by positivity)]
  exact pow_le_one₀ hb hle

/-! ## Coordinate convergence -/

private theorem tendsto_cubeLpENorm_grad_component (Q : TriadicCube d)
    (w : H1Function (openCubeSet Q)) (i : Fin d) :
    Filter.Tendsto
      (fun n : ℕ => cubeLpENorm Q 2
        (fun x => euclideanGradient (cubeH2Approx Q w n) x i - w.grad x i))
      Filter.atTop (nhds 0) := by
  refine tendsto_cubeLpENorm_of_tendsto_eLpNorm Q ?_
  have hcongr : ∀ n : ℕ,
      eLpNorm (fun x => euclideanGradient (cubeH2Approx Q w n) x i - w.grad x i) 2
          (volume.restrict (openCubeSet Q))
        = eLpNorm (fun x => (1 - cubeH2SmoothingScale n) *
            cubeH2Smoothing Q (fun y => w.grad y i) (cubeH2SmoothingScale n) x -
            w.grad x i) 2 (volume.restrict (openCubeSet Q)) := by
    intro n
    refine eLpNorm_congr_ae ?_
    filter_upwards [ae_restrict_mem (isOpen_openCubeSet Q).measurableSet] with x hx
    have heq : euclideanGradient
          (cubeH2Smoothing Q w.toFun (cubeH2SmoothingScale n)) x i
        = (1 - cubeH2SmoothingScale n) *
          cubeH2Smoothing Q (fun y => w.grad y i) (cubeH2SmoothingScale n) x :=
      eqOn_euclideanGradient_cubeH2Smoothing w (cubeH2SmoothingScale_pos n)
        (cubeH2SmoothingScale_lt_one n) i hx
    simp only [cubeH2Approx]
    rw [heq]
  simp only [hcongr]
  exact tendsto_eLpNorm_smul_cubeH2Smoothing_sub Q (w.grad_memL2 i)
    tendsto_one_sub_cubeH2SmoothingScale abs_one_sub_cubeH2SmoothingScale_le

private theorem tendsto_cubeLpENorm_hess_component (Q : TriadicCube d)
    {w : H1Function (openCubeSet Q)} (H : HasWeakHessianOn (openCubeSet Q) w)
    (i j : Fin d) :
    Filter.Tendsto
      (fun n : ℕ => cubeLpENorm Q 2
        (fun x => euclideanGradient
          (fun y => euclideanGradient (cubeH2Approx Q w n) y i) x j - H.hess i j x))
      Filter.atTop (nhds 0) := by
  refine tendsto_cubeLpENorm_of_tendsto_eLpNorm Q ?_
  have hcongr : ∀ n : ℕ,
      eLpNorm (fun x => euclideanGradient
          (fun y => euclideanGradient (cubeH2Approx Q w n) y i) x j - H.hess i j x) 2
          (volume.restrict (openCubeSet Q))
        = eLpNorm (fun x => (1 - cubeH2SmoothingScale n) ^ 2 *
            cubeH2Smoothing Q (H.hess i j) (cubeH2SmoothingScale n) x -
            H.hess i j x) 2 (volume.restrict (openCubeSet Q)) := by
    intro n
    refine eLpNorm_congr_ae ?_
    filter_upwards [ae_restrict_mem (isOpen_openCubeSet Q).measurableSet] with x hx
    have heq : euclideanGradient
          (fun y => euclideanGradient
            (cubeH2Smoothing Q w.toFun (cubeH2SmoothingScale n)) y i) x j
        = (1 - cubeH2SmoothingScale n) ^ 2 *
          cubeH2Smoothing Q (H.hess i j) (cubeH2SmoothingScale n) x :=
      eqOn_euclideanGradient_euclideanGradient_cubeH2Smoothing H
        (cubeH2SmoothingScale_pos n) (cubeH2SmoothingScale_lt_one n) i j hx
    simp only [cubeH2Approx]
    rw [heq]
  simp only [hcongr]
  exact tendsto_eLpNorm_smul_cubeH2Smoothing_sub Q (H.hess_memL2 i j)
    tendsto_one_sub_cubeH2SmoothingScale_sq abs_one_sub_cubeH2SmoothingScale_sq_le

/-! ## The `H²` smooth approximation -/

/-- **Smooth `H²` density on a cube.** For an `H¹` function `w` on the interior
of a triadic cube carrying a weak Hessian `H`, and every `ε > 0`, there is a
globally smooth `g` on `Vec d` whose gradient is within `ε` of the weak gradient
of `w` in the Euclidean `L̲²(Q)` norm and whose classical Hessian is within `ε`
of `H` in the Frobenius `L̲²(Q)` distance. -/
theorem exists_cubeH2SmoothApprox {Q : TriadicCube d}
    {w : H1Function (openCubeSet Q)} (H : HasWeakHessianOn (openCubeSet Q) w)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ g : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧
      vecCubeLpENorm Q 2 (fun x => vecGradient g x - w.grad x) ≤
        ENNReal.ofReal eps ∧
      jacobianDistENorm Q (vecGradient g) (fun x i j => H.hess i j x) ≤
        ENNReal.ofReal eps := by
  have hs1 : Filter.Tendsto
      (fun n : ℕ => ∑ i : Fin d, cubeLpENorm Q 2
        (fun x => euclideanGradient (cubeH2Approx Q w n) x i - w.grad x i))
      Filter.atTop (nhds 0) := by
    have h := tendsto_finsetSum (Finset.univ : Finset (Fin d))
      (fun i (_ : i ∈ Finset.univ) => tendsto_cubeLpENorm_grad_component Q w i)
    simpa using h
  have hs2 : Filter.Tendsto
      (fun n : ℕ => ∑ p : Fin d × Fin d, cubeLpENorm Q 2
        (fun x => euclideanGradient
          (fun y => euclideanGradient (cubeH2Approx Q w n) y p.1) x p.2 -
            H.hess p.1 p.2 x)) Filter.atTop (nhds 0) := by
    have h := tendsto_finsetSum (Finset.univ : Finset (Fin d × Fin d))
      (fun p (_ : p ∈ Finset.univ) =>
        tendsto_cubeLpENorm_hess_component Q H p.1 p.2)
    simpa using h
  have htot := hs1.add hs2
  rw [add_zero] at htot
  obtain ⟨n, hn⟩ := ((tendsto_order.1 htot).2 (ENNReal.ofReal eps)
    (ENNReal.ofReal_pos.2 heps)).exists
  refine ⟨cubeH2Approx Q w n, contDiff_cubeH2Approx Q w n, ?_, ?_⟩
  · have hmeas : ∀ i : Fin d, AEStronglyMeasurable
        (fun x => euclideanGradient (cubeH2Approx Q w n) x i - w.grad x i)
        (normalizedCubeMeasure Q) := fun i =>
      ((contDiff_euclideanGradient_apply (contDiff_cubeH2Approx Q w n)
          i).continuous.aestronglyMeasurable).sub
        (w.grad_memL2_normalizedCubeMeasure i).aestronglyMeasurable
    have hpt : ∀ x : Vec d,
        ‖hilbertifyVecField
            (fun y => euclideanGradient (cubeH2Approx Q w n) y - w.grad y) x‖
          ≤ ∑ i : Fin d,
              |euclideanGradient (cubeH2Approx Q w n) x i - w.grad x i| :=
      fun x => norm_hilbertVec_ofVec_le_sum_abs _
    have hb := cubeLpENorm_le_sum_abs (Q := Q)
      (f := hilbertifyVecField
        (fun y => euclideanGradient (cubeH2Approx Q w n) y - w.grad y))
      (h := fun (i : Fin d) (x : Vec d) =>
        euclideanGradient (cubeH2Approx Q w n) x i - w.grad x i)
      ((HilbertVec.ofVecL d).continuous.comp_aestronglyMeasurable
        (aemeasurable_pi_iff.mpr fun i => (hmeas i).aemeasurable).aestronglyMeasurable) hmeas hpt
    rw [vecGradient_eq_euclideanGradient, vecCubeLpENorm]
    exact le_trans hb (le_trans le_self_add (le_of_lt hn))
  · have hmeas : ∀ p : Fin d × Fin d, AEStronglyMeasurable
        (fun x => euclideanGradient
          (fun y => euclideanGradient (cubeH2Approx Q w n) y p.1) x p.2 -
            H.hess p.1 p.2 x) (normalizedCubeMeasure Q) := fun p =>
      ((contDiff_euclideanGradient_apply
          (contDiff_euclideanGradient_apply (contDiff_cubeH2Approx Q w n) p.1)
          p.2).continuous.aestronglyMeasurable).sub
        (H.hess_memLp_normalizedCubeMeasure Q p.1 p.2).aestronglyMeasurable
    have hpt : ∀ x : Vec d,
        ‖matrixFrobeniusMagnitude (fun i j =>
            euclideanGradient
              (fun y => euclideanGradient (cubeH2Approx Q w n) y i) x j -
              H.hess i j x)‖
          ≤ ∑ p : Fin d × Fin d,
              |euclideanGradient
                (fun y => euclideanGradient (cubeH2Approx Q w n) y p.1) x p.2 -
                  H.hess p.1 p.2 x| := by
      intro x
      rw [Real.norm_eq_abs]
      erw [abs_of_nonneg (matrixFrobeniusMagnitude_nonneg _)]
      simp only [Fintype.sum_prod_type]
      exact matrixFrobeniusMagnitude_le_sum_abs _
    have hb := cubeLpENorm_le_sum_abs (Q := Q)
      (f := fun x => matrixFrobeniusMagnitude (fun i j =>
        euclideanGradient
          (fun y => euclideanGradient (cubeH2Approx Q w n) y i) x j -
          H.hess i j x))
      (h := fun (p : Fin d × Fin d) (x : Vec d) => euclideanGradient
        (fun y => euclideanGradient (cubeH2Approx Q w n) y p.1) x p.2 -
          H.hess p.1 p.2 x)
      (by
        unfold matrixFrobeniusMagnitude
        exact Real.continuous_sqrt.comp_aestronglyMeasurable
          (Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
            Finset.aestronglyMeasurable_fun_sum _ fun j _ => (hmeas (i, j)).pow 2))
      hmeas hpt
    rw [vecGradient_eq_euclideanGradient]
    unfold jacobianDistENorm
    exact le_trans hb (le_trans le_add_self (le_of_lt hn))

/-! ## The mean-zero variant -/

private theorem vecGradient_sub_const (g : Vec d → ℝ) (c : ℝ) :
    vecGradient (fun x => g x - c) = vecGradient g := by
  funext x i
  simp [vecGradient, fderiv_sub_const]

private theorem cubeAverage_sub_self_eq_zero' (Q : TriadicCube d) {g : Vec d → ℝ}
    (hg : Continuous g) : cubeAverage Q (fun x => g x - cubeAverage Q g) = 0 := by
  have hint : IntegrableOn g (cubeSet Q) volume :=
    (hg.continuousOn.integrableOn_compact
      ((isBounded_cubeSet Q).isCompact_closure)).mono_set subset_closure
  have hconst : IntegrableOn (fun _ : Vec d => cubeAverage Q g) (cubeSet Q) volume :=
    integrableOn_const (volume_cubeSet_lt_top Q).ne (by simp)
  have hvol : (volume : Measure (Vec d)).real (cubeSet Q) = cubeVolume Q := by
    rw [Measure.real_def, volume_cubeSet_toReal]
  have hne : cubeVolume Q ≠ 0 := (cubeVolume_pos Q).ne'
  rw [cubeAverage, integral_sub hint hconst, setIntegral_const, hvol, smul_eq_mul,
    cubeAverage, ← mul_assoc, mul_inv_cancel₀ hne, one_mul, sub_self, mul_zero]

/-- **The mean-zero variant.** Subtracting its cube average from the
approximant changes neither its gradient nor its Hessian, so the same
approximation is available inside the mean-zero potential class of the paper. The
`hdense` binder that `hH2` feeds does not require this normalization; it is recorded for the
`Ĥ̲^{-1}(U)` test class of the paper, which does. -/
theorem exists_cubeH2MeanZeroSmoothApprox {Q : TriadicCube d}
    {w : H1Function (openCubeSet Q)} (H : HasWeakHessianOn (openCubeSet Q) w)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ g : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ cubeAverage Q g = 0 ∧
      vecCubeLpENorm Q 2 (fun x => vecGradient g x - w.grad x) ≤
        ENNReal.ofReal eps ∧
      jacobianDistENorm Q (vecGradient g) (fun x i j => H.hess i j x) ≤
        ENNReal.ofReal eps := by
  obtain ⟨g, hgsmooth, hgclose, hgjac⟩ := exists_cubeH2SmoothApprox H eps heps
  refine ⟨fun x => g x - cubeAverage Q g, hgsmooth.sub contDiff_const,
    cubeAverage_sub_self_eq_zero' Q hgsmooth.continuous, ?_, ?_⟩
  · rw [vecGradient_sub_const]
    exact hgclose
  · rw [vecGradient_sub_const]
    exact hgjac

/-! ## The hypothesis `hH2`, discharged -/

/-- **The `hH2` binder of `Section2/Norms/FractionalDensityB.lean`, discharged**
for the gradient field of an `H¹` function carrying a weak Hessian, with the
weak Hessian in the role of the weak Jacobian. -/
theorem hH2_of_hasWeakHessianOn {Q : TriadicCube d}
    {w : H1Function (openCubeSet Q)} (H : HasWeakHessianOn (openCubeSet Q) w) :
    ∀ eps : ℝ, 0 < eps → ∃ g : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧
      vecCubeLpENorm Q 2 (fun x => vecGradient g x - w.grad x) ≤
        ENNReal.ofReal eps ∧
      jacobianDistENorm Q (vecGradient g) (fun x i j => H.hess i j x) ≤
        ENNReal.ofReal eps :=
  fun eps heps => exists_cubeH2SmoothApprox H eps heps

/-! ## The term-4 duality, with no density hypothesis -/

/-- **The duality in the shape `l.RHS.term4` consumes, for a gradient field
with a weak Hessian.** This is `pairing_le_of_hessianDensity` with both its
matrix-measurability binder `hJm` and its density binder `hH2` discharged: the
field is `∇w` for an `H¹` function `w` on the interior of the cube, and `J` is
any weak Hessian witness of `w`. -/
theorem pairing_le_of_hasWeakHessianOn {Q : TriadicCube d} {s : ℝ} (hs : 0 < s)
    (hs1 : s < 1) (hd : 0 < d) {M : Vec d → Mat d} (p : Vec d)
    {w : H1Function (openCubeSet Q)} (H : HasWeakHessianOn (openCubeSet Q) w)
    (hrow : ∀ u : Vec d,
      MemLp (hilbertifyVecField (fun x => Matrix.vecMul u (M x))) 2
        (normalizedCubeMeasure Q))
    (hG : MemLp (hilbertifyVecField w.grad) 2 (normalizedCubeMeasure Q))
    (hMfin : matHatNegENorm Q s 2 M ≠ ⊤)
    (hGfin : cubeHsENorm Q s (hilbertifyVecField w.grad) ≠ ⊤) :
    |volumeAverage (openCubeSet Q)
        (fun y => vecDot p (matVecMul (M y) (w.grad y)))| ≤
      (matHatNegENorm Q s 2 M).toReal *
        (cubeHsENorm Q s (hilbertifyVecField w.grad)).toReal * vecNorm p := by
  refine pairing_le_of_hessianDensity hs hs1 hd p hrow hG hMfin hGfin
    (fun i j => (H.hess_memLp_normalizedCubeMeasure Q i j).aestronglyMeasurable)
    (hH2_of_hasWeakHessianOn H)

end

end Sobolev
end SuperdiffusionCLT
