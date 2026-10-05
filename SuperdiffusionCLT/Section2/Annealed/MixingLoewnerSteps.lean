/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.MixingStepEnvelope
public import SuperdiffusionCLT.Section2.Annealed.Symmetry

/-!
# The two Step-E Loewner statements of the mixing block

The mixing anchor `sigmaStarInv_mixing_minscale_of_anchors_midpoint`
carries two Step data whose
conclusion types are matrix-Loewner statements:

* `hStepE` — **the descendant average of the coarse matrices** `s^-1_{L,*}(R)`
  over the depth-`(n - h)` descendants `R` of `cu_n` is Loewner-dominated by the
  annealed block `shom^-1_{m,*}(cu_h)` plus a `Gamma_2` fluctuation times the
  identity, the amplitude being
  `CFluc * nu^(-2) * 3^(-((n - h)/4))`;
* `hStepD` — **the annealed blocks at two cutoffs `m <= l` at one cube** `cu_h`
  are Loewner-comparable, with a `Gamma_2` correction of amplitude
  `CDet * nu^(-2) * 3^(-((m - h)/2))`.

Neither is an instance of the Loewner statement about `sigmaBarStarInv`
(`matLoewnerLE_sigmaBarStarInv_originCube`), which compares *cube scales at one fixed
cutoff*, and the Step-E machinery of `MixingStepEnvelope` is *entry-level*, for a
shell-separated sublattice, not for the descendant average as a matrix.

This module isolates the exact analytic content of the two targets.

## Step D

At an origin cube, under the isotropy law `ShellLawJ4`, the two annealed blocks
are **scalar matrices** (`sigmaBarStarInv_originCube_eq_smul_one`,
`Symmetry.lean`), so the `hStepD` Loewner statement follows from the purely
scalar inequality

> `shom^-1_{m,*}(cu_h) <= shom^-1_{l,*}(cu_h) + CDet * nu^(-2) * 3^(-((m - h)/2))`

(`stepD_exists_of_scalar_gap`), with the explicit witness
`Y := max 0 (shom^-1_{m,*}(cu_h) - shom^-1_{l,*}(cu_h))`. Conversely, `IsBigO` is a *tail*
relation — a positive deterministic excess would force the tail event
`{|Y| > A}` to be all of `Omega`, against `measureReal univ = 1 > exp(-1)`.
So `hStepD` carries **no probability content**; its whole content is the
deterministic cutoff comparison, which is not a consequence of Loewner monotonicity (the cutoff
increment `a_l - a_m = finiteShellIncrement` is not sign-definite, so the
pointwise Loewner monotonicity of the coefficient field does not apply).

## Step E

`hStepE` reduces to the single
operator-norm `Gamma_2` concentration of the fluctuation matrix
`D omega - shom^-1_{m,*}(cu_h)` at exactly the same amplitude. The reduction is
the deterministic operator-norm sandwich `M <= ||M||_op . 1`
(`matLoewnerLE_matrixOperatorNorm_smul_one`, `matLoewnerLE_add_operatorNorm_sub`) added to the
annealed block, with
the measurability of `omega |-> ||D omega - shom^-1||_op` from the continuity of
`matrixOperatorNorm` and the entrywise measurability of the descendant average.
The Step-E reduction needs only `0 < nu` (for the ellipticity of the cutoff
field), not `ShellLawJ4`; the Step-D reduction needs `ShellLawJ4` for the
scalarization of the two blocks.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Annealed

open Homogenization MeasureTheory
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## The operator-norm Loewner sandwich of a fixed perturbation -/

/-- **The Loewner sandwich of a matrix around a fixed reference.**  For any two
real matrices `D`, `S` there holds
`D <= S + ||D - S||_op . 1` in the Loewner order.  The quadratic form of a sum
splits (`add_matVecMul`, `vecDot_add_right`) and the perturbation is dominated
by its own operator norm (`matLoewnerLE_matrixOperatorNorm_smul_one`); this is
the deterministic Loewner step of `hStepE`, with the reference `S` the annealed
block and the perturbation the centred descendant average. -/
theorem matLoewnerLE_add_operatorNorm_sub {d : ℕ} (D S : Homogenization.Mat d) :
    Homogenization.MatLoewnerLE D
      (S + Homogenization.Book.Ch02.matrixOperatorNorm (D - S) •
        (1 : Homogenization.Mat d)) := by
  refine SuperdiffusionCLT.Section2.Localization.matLoewnerLE_of_quad_le (fun y => ?_)
  have hsplit : D = S + (D - S) := by abel
  have hmat : Homogenization.matVecMul D y =
      Homogenization.matVecMul S y + Homogenization.matVecMul (D - S) y := by
    conv_lhs => rw [hsplit]
    rw [Homogenization.add_matVecMul]
  have h1 : Homogenization.vecDot y (Homogenization.matVecMul D y) =
      Homogenization.vecDot y (Homogenization.matVecMul S y) +
        Homogenization.vecDot y (Homogenization.matVecMul (D - S) y) := by
    have h := congrArg (Homogenization.vecDot y) hmat
    rwa [Homogenization.vecDot_add_right] at h
  have h2 : Homogenization.vecDot y (Homogenization.matVecMul
        (S + Homogenization.Book.Ch02.matrixOperatorNorm (D - S) •
          (1 : Homogenization.Mat d)) y) =
      Homogenization.vecDot y (Homogenization.matVecMul S y) +
        Homogenization.vecDot y (Homogenization.matVecMul
          (Homogenization.Book.Ch02.matrixOperatorNorm (D - S) •
            (1 : Homogenization.Mat d)) y) := by
    rw [Homogenization.add_matVecMul, Homogenization.vecDot_add_right]
  have hnorm : Homogenization.vecDot y (Homogenization.matVecMul (D - S) y) ≤
      Homogenization.vecDot y (Homogenization.matVecMul
        (Homogenization.Book.Ch02.matrixOperatorNorm (D - S) •
          (1 : Homogenization.Mat d)) y) := by
    have h := SuperdiffusionCLT.Section2.Localization.matLoewnerLE_matrixOperatorNorm_smul_one
      (M := D - S) y
    linarith only [h]
  rw [h1, h2]
  linarith only [hnorm]

/-! ## Step D: the annealed blocks at two cutoffs at one origin cube -/

/-- **`hStepD` from the scalar cutoff comparison.**  If the two scalar annealed
blocks at the cube `cu_h` satisfy
`shom^-1_{m,*}(cu_h) <= shom^-1_{l,*}(cu_h) + A`, then the `hStepD` conclusion
holds with the explicit witness
`Y := max 0 (shom^-1_{m,*}(cu_h) - shom^-1_{l,*}(cu_h))`: it is measurable and
constant, hence `Gamma_2` at amplitude `max 0 (gap) <= A` (using `A >= 0`), and
the per-`omega` Loewner comparison is the scalar matrix comparison. -/
theorem stepD_exists_of_scalar_gap [NeZero d] {nu A : ℝ} (hnu : 0 < nu) (hA : 0 ≤ A)
    (P : ProbabilityMeasure (ShellSeq d)) (hJ4 : ShellLawJ4 d P) {h m l : ℕ}
    (hgap : sigmaBarStarInvScalar nu m P
        (Homogenization.cubeSet (Homogenization.originCube d (h : ℤ))) ≤
      sigmaBarStarInvScalar nu l P
        (Homogenization.cubeSet (Homogenization.originCube d (h : ℤ))) + A) :
    ∃ Y : ShellSeq d → ℝ, Measurable Y ∧
      IsBigO P.toMeasure (gammaSigma 2) Y A ∧
      ∀ ω : ShellSeq d,
        Homogenization.MatLoewnerLE
          (sigmaBarStarInv nu m P (Homogenization.cubeSet (Homogenization.originCube d (h : ℤ))))
          (sigmaBarStarInv nu l P (Homogenization.cubeSet (Homogenization.originCube d (h : ℤ))) +
            Y ω • (1 : Homogenization.Mat d)) := by
  set c : ℝ := sigmaBarStarInvScalar nu m P
      (Homogenization.cubeSet (Homogenization.originCube d (h : ℤ))) -
    sigmaBarStarInvScalar nu l P
      (Homogenization.cubeSet (Homogenization.originCube d (h : ℤ))) with hc
  have hcA : c ≤ A := by rw [hc]; linarith only [hgap]
  refine ⟨fun _ => max 0 c, measurable_const, ?_, ?_⟩
  · exact (isBigO_gammaSigma_const_apply (mu := P.toMeasure) (c := max 0 c) (sigma := 2)
      (le_max_left 0 c)).mono_scale (max_le hA hcA)
  · intro ω
    show Homogenization.MatLoewnerLE
      (sigmaBarStarInv nu m P (Homogenization.cubeSet (Homogenization.originCube d (h : ℤ))))
      (sigmaBarStarInv nu l P (Homogenization.cubeSet (Homogenization.originCube d (h : ℤ))) +
        (max 0 c) • (1 : Homogenization.Mat d))
    rw [sigmaBarStarInv_originCube_eq_smul_one hnu m hJ4 (h : ℤ),
        sigmaBarStarInv_originCube_eq_smul_one hnu l hJ4 (h : ℤ), ← add_smul]
    refine Homogenization.Book.Ch04.matLoewnerLE_smul_one_of_scalar_le ?_
    have h1 : c ≤ max 0 c := le_max_right 0 c
    rw [hc] at h1
    linarith only [h1]

/-! ## Step E: the descendant average as a matrix -/

/-- **Measurability of an entry of the coarse matrix on a cube.**  Each entry of
`s^-1_{L,*}(R)` is measurable in the source, by the entrywise measurability of
`s_*^{-1}` on the cube (`measurable_sigmaStarInvCoarse_apply`) and the identity
of the coarse matrix on `cubeSet R` and on `openCubeSet R`. -/
theorem measurable_entry_sigmaStarInvCoarse_cubeSet [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (m : ℕ) (R : Homogenization.TriadicCube d) (i j : Fin d) :
    Measurable (fun ω : ShellSeq d =>
      sigmaStarInvCoarse (Homogenization.cubeSet R)
        (coefficientCutoff nu ω m).toCoeffField i j) := by
  have hEq : (fun ω : ShellSeq d => sigmaStarInvCoarse (Homogenization.cubeSet R)
        (coefficientCutoff nu ω m).toCoeffField i j) =
      fun ω : ShellSeq d => sigmaStarInvCoarse (Homogenization.openCubeSet R)
        (coefficientCutoff nu ω m).toFun i j := by
    funext ω
    exact congrArg (fun M : Homogenization.Mat d => M i j)
      (SuperdiffusionCLT.Section3.Terms.sigmaStarInvCoarse_cubeSet_eq_openCubeSet R _)
  rw [hEq]
  exact measurable_sigmaStarInvCoarse_apply (measurable_coefficientCutoff nu m)
    (fun ω => aeLocallyUniformlyEllipticField_coefficientCutoff hnu ω m) R i j

/-- **Measurability of an entry of the descendant average.**  The descendant
average is the finset average of the coarse-matrix entries over the depth-`(n-h)`
descendants of `cu_n`, each of which is measurable
(`measurable_entry_sigmaStarInvCoarse_cubeSet`); the average is a finite sum
against the constant `card^{-1}`. -/
theorem measurable_descendantsAverageMat_entry [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (m n h : ℕ) (i j : Fin d) :
    Measurable (fun ω : ShellSeq d =>
      Homogenization.descendantsAverageMat (Homogenization.originCube d (n : ℤ)) (n - h)
        (fun R => sigmaStarInvCoarse (Homogenization.cubeSet R)
          (coefficientCutoff nu ω m).toCoeffField) i j) := by
  have hgoal : (fun ω : ShellSeq d =>
        Homogenization.descendantsAverageMat (Homogenization.originCube d (n : ℤ)) (n - h)
          (fun R => sigmaStarInvCoarse (Homogenization.cubeSet R)
            (coefficientCutoff nu ω m).toCoeffField) i j) =
      fun ω : ShellSeq d =>
        (((Homogenization.descendantsAtDepth (Homogenization.originCube d (n : ℤ))
            (n - h)).card : ℝ)⁻¹) *
          (Homogenization.descendantsAtDepth (Homogenization.originCube d (n : ℤ))
            (n - h)).sum
            (fun R => sigmaStarInvCoarse (Homogenization.cubeSet R)
              (coefficientCutoff nu ω m).toCoeffField i j) := by
    funext ω
    simp only [Homogenization.descendantsAverageMat, Homogenization.descendantsAverage]
  rw [hgoal]
  exact measurable_const.mul
    (Finset.measurable_sum _ (fun R _ => measurable_entry_sigmaStarInvCoarse_cubeSet hnu m R i j))

/-- **Measurability of the operator norm of the Step-E fluctuation.**  The
fluctuation matrix `D omega - shom^-1_{m,*}(cu_h)` is measurable entrywise
(`measurable_descendantsAverageMat_entry` and a constant), so its operator norm
is measurable by the continuity of `matrixOperatorNorm`. -/
theorem measurable_matrixOperatorNorm_fluctuation [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (m : ℕ) (P : ProbabilityMeasure (ShellSeq d)) (n h : ℕ) :
    Measurable (fun ω : ShellSeq d => Homogenization.Book.Ch02.matrixOperatorNorm
      (Homogenization.descendantsAverageMat (Homogenization.originCube d (n : ℤ)) (n - h)
          (fun R => sigmaStarInvCoarse (Homogenization.cubeSet R)
            (coefficientCutoff nu ω m).toCoeffField)
        - sigmaBarStarInv nu m P
          (Homogenization.cubeSet (Homogenization.originCube d (h : ℤ))))) := by
  refine SuperdiffusionCLT.Frozen.Assumptions.ShellField.continuous_matrixOperatorNorm.measurable.comp ?_
  refine measurable_pi_iff.mpr (fun i => measurable_pi_iff.mpr (fun j => ?_))
  simp only [Matrix.sub_apply]
  exact (measurable_descendantsAverageMat_entry hnu m n h i j).sub measurable_const

end

end SuperdiffusionCLT.Section2.Annealed
