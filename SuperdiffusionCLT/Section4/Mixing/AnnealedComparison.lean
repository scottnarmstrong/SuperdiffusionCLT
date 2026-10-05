/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.Symmetry
public import SuperdiffusionCLT.Section3.Terms.TranslatedBlocks

/-!
# The block-diagonal-scalar bilinear bridge, and the annealed comparison step

`e.homs.defs.U` (proved for the marginal annealed matrices in
`SuperdiffusionCLT.Section2.Annealed.Symmetry`) says that on an origin
cube `cu_n` the annealed matrix `bfAhom_m(cu_n)` is block diagonal with
*scalar* blocks `σ̄_m(cu_n) • Id` and `σ̄_{m,*}^{-1}(cu_n) • Id`. This file
records the direct consequence for the bilinear-form reading of the
sandwich convention used throughout
`Frozen.Section4.mixing_below_cutoff`: the quadratic form
`blockVecDot p (blockMatVecMul (annealedBlockMatrix ...) p)` reduces to the
explicit real-number expression
`σ̄_m(cu_n) * vecNormSq p.1 + σ̄_{m,*}^{-1}(cu_n) * vecNormSq p.2`
(`mixMain_annealedBilinear_eq`). Every later bilinear-sandwich manipulation in
this development (`p.mixing.P.three.prime#annealed-comparison`,
`#invert-B`, `#convert-to-L-normalization`) reduces, via this bridge, to
ordinary real-number algebra on the two annealed scalars — no matrix
square root or matrix inverse is ever computed as a Lean operation.

`Section4/Mixing/InvertB.lean` uses this bridge, applied at the two scales
`ℓ` and `L`, to reduce the sandwich-form annealed-comparison hypothesis and
the `#invert-B` conclusion to ordinary real-number algebra on the annealed
scalars.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

open Homogenization
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Annealed
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## Elementary block-vector algebra -/

/-- `matVecMul` of a scalar matrix `c • 1` is scalar multiplication of the
vector. -/
private theorem mixMain_matVecMul_smul_one (c : ℝ) (x : Vec d) :
    matVecMul (c • (1 : Mat d)) x = c • x := by
  funext i
  simp only [matVecMul, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, Pi.smul_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji.symm]
  · intro hi
    simp at hi

/-- `matVecMul` of the zero matrix is the zero vector. -/
private theorem mixMain_matVecMul_zero (x : Vec d) :
    matVecMul (0 : Mat d) x = 0 := by
  funext i
  simp [matVecMul]

/-- `vecDot x (c • x) = c * vecNormSq x`. -/
private theorem mixMain_vecDot_smul_self (c : ℝ) (x : Vec d) :
    vecDot x (c • x) = c * vecNormSq x := by
  simp only [vecDot, vecNormSq, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-! ## The bilinear-to-scalar bridge -/

/-- The bilinear-form value of a block-diagonal-scalar `BlockMat d`. Public:
reused directly in `Section4/Mixing/InvertB.lean` to unfold the sandwich-form
hypotheses there without redoing this computation. -/
theorem mixMain_blockDiagScalar_bilinear_eq {A : BlockMat d}
    (hUR : A.upperRight = 0) (hLL : A.lowerLeft = 0)
    {s t : ℝ} (hUL : A.upperLeft = s • (1 : Mat d))
    (hLR : A.lowerRight = t • (1 : Mat d)) (p : BlockVec d) :
    blockVecDot p (blockMatVecMul A p) = s * vecNormSq p.1 + t * vecNormSq p.2 := by
  have hmv : blockMatVecMul A p = (s • p.1, t • p.2) := by
    unfold blockMatVecMul
    rw [hUR, hLL, hUL, hLR, mixMain_matVecMul_smul_one, mixMain_matVecMul_smul_one,
      mixMain_matVecMul_zero, mixMain_matVecMul_zero]
    simp
  rw [hmv]
  show vecDot p.1 (s • p.1) + vecDot p.2 (t • p.2) = _
  rw [mixMain_vecDot_smul_self, mixMain_vecDot_smul_self]

/-- `vecDot x (c • y) = c * vecDot x y`, the two-vector generalization of
`mixMain_vecDot_smul_self`. -/
private theorem mixMain_vecDot_smul_right (c : ℝ) (x y : Vec d) :
    vecDot x (c • y) = c * vecDot x y := by
  simp only [vecDot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The bilinear cross-term value of a block-diagonal-scalar `BlockMat d`:
the two-vector generalization of `mixMain_blockDiagScalar_bilinear_eq`, used
to unfold sandwich-form hypotheses `2 * blockVecDot p (blockMatVecMul H q) ≤
...` at general (not necessarily equal) `p, q`. -/
theorem mixMain_blockDiagScalar_bilinear_cross_eq {A : BlockMat d}
    (hUR : A.upperRight = 0) (hLL : A.lowerLeft = 0)
    {s t : ℝ} (hUL : A.upperLeft = s • (1 : Mat d))
    (hLR : A.lowerRight = t • (1 : Mat d)) (p q : BlockVec d) :
    blockVecDot p (blockMatVecMul A q) = s * vecDot p.1 q.1 + t * vecDot p.2 q.2 := by
  have hmv : blockMatVecMul A q = (s • q.1, t • q.2) := by
    unfold blockMatVecMul
    rw [hUR, hLL, hUL, hLR, mixMain_matVecMul_smul_one, mixMain_matVecMul_smul_one,
      mixMain_matVecMul_zero, mixMain_matVecMul_zero]
    simp
  rw [hmv]
  show vecDot p.1 (s • q.1) + vecDot p.2 (t • q.2) = _
  rw [mixMain_vecDot_smul_right, mixMain_vecDot_smul_right]

/-! ## The expectation step of `#annealed-comparison`, the moment half

The paper's "taking expectations in the preceding display... gives" step
needs, for each `O_{Γσ}(A)`-controlled amplitude `X` appearing in
`combine-terms-bound`'s conclusion, a bound `E[|X|] ≤ C(σ)·A`. This is
already in the `CoarseGraining` dependency as
`Homogenization.IndependentSums.integral_abs_rpow_le_of_isBigO_gammaSigma`
(specialized here to the first moment `p = 1`, `C(σ) = gammaMomentConst σ`,
`Homogenization/Probability/IndependentSums/GammaSigma/Basic.lean`). -/

/-- **The moment half of the `#annealed-comparison` expectation step.** If `X
= O_{Γσ}(A)` (`A > 0`, `σ > 0`) under a probability measure, `E[|X|] ≤
gammaMomentConst σ · A`. -/
theorem mixMain_integral_abs_le_of_isBigO_gammaSigma {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : Ω → ℝ} {A σ : ℝ} (hσ : 0 < σ) (hA : 0 < A)
    (hXm : AEMeasurable X μ) (hX : Homogenization.IndependentSums.IsBigO μ (Homogenization.IndependentSums.gammaSigma σ) X A) :
    ∫ ω, |X ω| ∂μ ≤ Homogenization.IndependentSums.gammaMomentConst σ * A := by
  have h :=
    Homogenization.IndependentSums.integral_abs_rpow_le_of_isBigO_gammaSigma
      (μ := μ) (X := X) (K := A) (σ := σ) (p := 1) hσ hA le_rfl hXm hX
  simpa using h

/-- **The moment half, three-term sum form.** The shape actually needed to
process `combine-terms-bound`'s `X1+X2+X3` (or the gauge-term hypothesis's
`X1g+X2g+X3g`): each amplitude contributes its own `gammaMomentConst`-scaled
bound to `E[|X1|+|X2|+|X3|]`, hence (by the triangle inequality twice) to a bound on
`E[X1+X2+X3]` itself. -/
theorem mixMain_integral_sum3_le_of_isBigO_gammaSigma {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X1 X2 X3 : Ω → ℝ} {A1 A2 A3 σ1 σ2 σ3 : ℝ}
    (hσ1 : 0 < σ1) (hσ2 : 0 < σ2) (hσ3 : 0 < σ3) (hA1 : 0 < A1) (hA2 : 0 < A2) (hA3 : 0 < A3)
    (hX1m : AEMeasurable X1 μ) (hX2m : AEMeasurable X2 μ) (hX3m : AEMeasurable X3 μ)
    (hX1 : Homogenization.IndependentSums.IsBigO μ (Homogenization.IndependentSums.gammaSigma σ1) X1 A1)
    (hX2 : Homogenization.IndependentSums.IsBigO μ (Homogenization.IndependentSums.gammaSigma σ2) X2 A2)
    (hX3 : Homogenization.IndependentSums.IsBigO μ (Homogenization.IndependentSums.gammaSigma σ3) X3 A3)
    (hInt1 : MeasureTheory.Integrable X1 μ) (hInt2 : MeasureTheory.Integrable X2 μ)
    (hInt3 : MeasureTheory.Integrable X3 μ) :
    ∫ ω, (X1 ω + X2 ω + X3 ω) ∂μ ≤
      Homogenization.IndependentSums.gammaMomentConst σ1 * A1 +
        Homogenization.IndependentSums.gammaMomentConst σ2 * A2 +
        Homogenization.IndependentSums.gammaMomentConst σ3 * A3 := by
  have h1 := mixMain_integral_abs_le_of_isBigO_gammaSigma hσ1 hA1 hX1m hX1
  have h2 := mixMain_integral_abs_le_of_isBigO_gammaSigma hσ2 hA2 hX2m hX2
  have h3 := mixMain_integral_abs_le_of_isBigO_gammaSigma hσ3 hA3 hX3m hX3
  have hle1 : ∫ ω, X1 ω ∂μ ≤ ∫ ω, |X1 ω| ∂μ :=
    MeasureTheory.integral_mono hInt1 hInt1.abs (fun ω => le_abs_self (X1 ω))
  have hle2 : ∫ ω, X2 ω ∂μ ≤ ∫ ω, |X2 ω| ∂μ :=
    MeasureTheory.integral_mono hInt2 hInt2.abs (fun ω => le_abs_self (X2 ω))
  have hle3 : ∫ ω, X3 ω ∂μ ≤ ∫ ω, |X3 ω| ∂μ :=
    MeasureTheory.integral_mono hInt3 hInt3.abs (fun ω => le_abs_self (X3 ω))
  have hsum : ∫ ω, (X1 ω + X2 ω + X3 ω) ∂μ =
      ∫ ω, X1 ω ∂μ + ∫ ω, X2 ω ∂μ + ∫ ω, X3 ω ∂μ := by
    have step1 : ∫ ω, (X1 ω + X2 ω + X3 ω) ∂μ = ∫ ω, (X1 ω + X2 ω) ∂μ + ∫ ω, X3 ω ∂μ :=
      MeasureTheory.integral_add (f := fun ω => X1 ω + X2 ω) (g := X3) (hInt1.add hInt2) hInt3
    have step2 : ∫ ω, (X1 ω + X2 ω) ∂μ = ∫ ω, X1 ω ∂μ + ∫ ω, X2 ω ∂μ :=
      MeasureTheory.integral_add (f := X1) (g := X2) hInt1 hInt2
    rw [step1, step2]
  rw [hsum]
  linarith only [h1, h2, h3, hle1, hle2, hle3]

/-- **The annealed bilinear bridge.** On an origin cube `cu_n`, the annealed
quadratic form `p ↦ blockVecDot p (blockMatVecMul (annealedBlockMatrix ...) p)`
equals the explicit real-number expression in the two annealed scalars
`σ̄_m(cu_n)` and `σ̄_{m,*}^{-1}(cu_n)`, `e.homs.defs.U`. -/
theorem mixMain_annealedBilinear_eq [NeZero d] {nu : ℝ} (hnu : 0 < nu) (m : ℕ)
    {P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)}
    (hJ4 : ShellLawJ4 d P) (n : ℤ) (p : BlockVec d) :
    blockVecDot p
        (blockMatVecMul (annealedBlockMatrix nu m P (cubeSet (originCube d n))) p) =
      sigmaBarScalar nu m P (cubeSet (originCube d n)) * vecNormSq p.1 +
        sigmaBarStarInvScalar nu m P (cubeSet (originCube d n)) * vecNormSq p.2 :=
  mixMain_blockDiagScalar_bilinear_eq
    (annealedBlockMatrix_originCube_upperRight_eq_zero hnu m hJ4 n)
    (annealedBlockMatrix_originCube_lowerLeft_eq_zero hnu m hJ4 n)
    (annealedBlockMatrix_originCube_upperLeft_eq_sigmaBar hnu m hJ4 n |>.trans
      (sigmaBar_originCube_eq_smul_one hnu m hJ4 n))
    (sigmaBarStarInv_originCube_eq_smul_one hnu m hJ4 n) p

/-! ## Stationarity: `E[bfA_L(z+cu_n)] = bfAhom_L(cu_n)` for every translate `z`

The other half `#annealed-comparison`'s expectation step needs ("using stationarity"):
`annealedBlockMatrix` is *defined* as an expectation
at the origin cube, so the fact needed is that the same expectation, read at
any scale-`n` translate `z`, gives the same answer. This is exactly
`Section3.Terms.integral_of_translationCovariant` (the general tool proved
for the `l.RHS.term3` block-concentration package,
`Section3/Terms/BlockConcentrationInputs.lean`'s
`integral_translatedCoarseBlock_apply` is the same argument specialized to
the upper-left block only) applied to all four `BlockMat` blocks via the
translation-covariance identity `translatedBlockMat_eq_originCube`. -/

section Stationarity

open SuperdiffusionCLT.Section2.Cutoff (ShellSeq)
open SuperdiffusionCLT.Frozen.Section2 (coefficientCutoff)

private theorem mixMain_coarseBlockMatrix_covariant [NeZero d] (nu : ℝ) (L : ℕ)
    (omega : ShellSeq d) (Q : Homogenization.TriadicCube d) :
    coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega L).toCoeffField =
      coarseBlockMatrix (cubeSet (originCube d Q.scale))
        (coefficientCutoff nu
            (ShellField.translateSequence (Homogenization.triadicCubeShift Q) omega) L).toCoeffField := by
  rw [← SuperdiffusionCLT.Section3.Terms.translatedBlockMat_eq_cubeSet,
    ← SuperdiffusionCLT.Section3.Terms.translatedBlockMat_eq_cubeSet]
  exact SuperdiffusionCLT.Section3.Terms.translatedBlockMat_eq_originCube nu L omega Q

variable [NeZero d] {nu : ℝ} (hnu : 0 < nu) {P : MeasureTheory.ProbabilityMeasure (ShellSeq d)}
  (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
  (hJ4 : ShellLawJ4 d P) (L nn : ℕ) {z : Homogenization.TriadicCube d}

include hnu hPrefix hJ2 hJ3 hJ4

/-- **`E[b_L(z+cu_n)] = bBar_L(cu_n)` for every scale-`n` translate `z`.** -/
theorem mixMain_integral_coarseBlockMatrix_upperLeft_eq (hz : z.scale = (nn : ℤ)) (i j : Fin d) :
    ∫ omega : ShellSeq d, (coarseBlockMatrix (cubeSet z)
        (coefficientCutoff nu omega L).toCoeffField).upperLeft i j ∂P.toMeasure =
      (annealedBlockMatrix nu L P (cubeSet (originCube d (nn : ℤ)))).upperLeft i j := by
  have hcov : ∀ omega : ShellSeq d, (coarseBlockMatrix (cubeSet z)
        (coefficientCutoff nu omega L).toCoeffField).upperLeft i j =
      (coarseBlockMatrix (cubeSet (originCube d z.scale))
          (coefficientCutoff nu
              (ShellField.translateSequence (Homogenization.triadicCubeShift z) omega) L).toCoeffField
        ).upperLeft i j := fun omega =>
    congrFun (congrFun (congrArg BlockMat.upperLeft
      (mixMain_coarseBlockMatrix_covariant nu L omega z)) i) j
  have hmeas := (integrable_coarseBlockMatrix_upperLeft_apply hnu L (originCube d z.scale)
    hPrefix hJ2 hJ3 hJ4 i j).aestronglyMeasurable
  have h := SuperdiffusionCLT.Section3.Terms.integral_of_translationCovariant
    (P := P) hPrefix hJ2
    (F := fun omega Q => (coarseBlockMatrix (cubeSet Q)
      (coefficientCutoff nu omega L).toCoeffField).upperLeft i j) hcov hmeas
  rw [hz] at h
  exact h

/-- **`E[b_L^{ur}(z+cu_n)] = bfAhom_L(cu_n).upperRight` for every scale-`n`
translate `z`.** -/
theorem mixMain_integral_coarseBlockMatrix_upperRight_eq (hz : z.scale = (nn : ℤ)) (i j : Fin d) :
    ∫ omega : ShellSeq d, (coarseBlockMatrix (cubeSet z)
        (coefficientCutoff nu omega L).toCoeffField).upperRight i j ∂P.toMeasure =
      (annealedBlockMatrix nu L P (cubeSet (originCube d (nn : ℤ)))).upperRight i j := by
  have hcov : ∀ omega : ShellSeq d, (coarseBlockMatrix (cubeSet z)
        (coefficientCutoff nu omega L).toCoeffField).upperRight i j =
      (coarseBlockMatrix (cubeSet (originCube d z.scale))
          (coefficientCutoff nu
              (ShellField.translateSequence (Homogenization.triadicCubeShift z) omega) L).toCoeffField
        ).upperRight i j := fun omega =>
    congrFun (congrFun (congrArg BlockMat.upperRight
      (mixMain_coarseBlockMatrix_covariant nu L omega z)) i) j
  have hmeas := (integrable_coarseBlockMatrix_upperRight_apply hnu L (originCube d z.scale)
    hPrefix hJ2 hJ3 hJ4 i j).aestronglyMeasurable
  have h := SuperdiffusionCLT.Section3.Terms.integral_of_translationCovariant
    (P := P) hPrefix hJ2
    (F := fun omega Q => (coarseBlockMatrix (cubeSet Q)
      (coefficientCutoff nu omega L).toCoeffField).upperRight i j) hcov hmeas
  rw [hz] at h
  exact h

/-- **`E[b_L^{ll}(z+cu_n)] = bfAhom_L(cu_n).lowerLeft` for every scale-`n`
translate `z`.** -/
theorem mixMain_integral_coarseBlockMatrix_lowerLeft_eq (hz : z.scale = (nn : ℤ)) (i j : Fin d) :
    ∫ omega : ShellSeq d, (coarseBlockMatrix (cubeSet z)
        (coefficientCutoff nu omega L).toCoeffField).lowerLeft i j ∂P.toMeasure =
      (annealedBlockMatrix nu L P (cubeSet (originCube d (nn : ℤ)))).lowerLeft i j := by
  have hcov : ∀ omega : ShellSeq d, (coarseBlockMatrix (cubeSet z)
        (coefficientCutoff nu omega L).toCoeffField).lowerLeft i j =
      (coarseBlockMatrix (cubeSet (originCube d z.scale))
          (coefficientCutoff nu
              (ShellField.translateSequence (Homogenization.triadicCubeShift z) omega) L).toCoeffField
        ).lowerLeft i j := fun omega =>
    congrFun (congrFun (congrArg BlockMat.lowerLeft
      (mixMain_coarseBlockMatrix_covariant nu L omega z)) i) j
  have hmeas := (integrable_coarseBlockMatrix_lowerLeft_apply hnu L (originCube d z.scale)
    hPrefix hJ2 hJ3 hJ4 i j).aestronglyMeasurable
  have h := SuperdiffusionCLT.Section3.Terms.integral_of_translationCovariant
    (P := P) hPrefix hJ2
    (F := fun omega Q => (coarseBlockMatrix (cubeSet Q)
      (coefficientCutoff nu omega L).toCoeffField).lowerLeft i j) hcov hmeas
  rw [hz] at h
  exact h

/-- **`E[b_L^{lr}(z+cu_n)] = bfAhom_L(cu_n).lowerRight` for every scale-`n`
translate `z`.** -/
theorem mixMain_integral_coarseBlockMatrix_lowerRight_eq (hz : z.scale = (nn : ℤ)) (i j : Fin d) :
    ∫ omega : ShellSeq d, (coarseBlockMatrix (cubeSet z)
        (coefficientCutoff nu omega L).toCoeffField).lowerRight i j ∂P.toMeasure =
      (annealedBlockMatrix nu L P (cubeSet (originCube d (nn : ℤ)))).lowerRight i j := by
  have hcov : ∀ omega : ShellSeq d, (coarseBlockMatrix (cubeSet z)
        (coefficientCutoff nu omega L).toCoeffField).lowerRight i j =
      (coarseBlockMatrix (cubeSet (originCube d z.scale))
          (coefficientCutoff nu
              (ShellField.translateSequence (Homogenization.triadicCubeShift z) omega) L).toCoeffField
        ).lowerRight i j := fun omega =>
    congrFun (congrFun (congrArg BlockMat.lowerRight
      (mixMain_coarseBlockMatrix_covariant nu L omega z)) i) j
  have hmeas := (integrable_coarseBlockMatrix_lowerRight_apply hnu L (originCube d z.scale)
    hPrefix hJ2 hJ3 hJ4 i j).aestronglyMeasurable
  have h := SuperdiffusionCLT.Section3.Terms.integral_of_translationCovariant
    (P := P) hPrefix hJ2
    (F := fun omega Q => (coarseBlockMatrix (cubeSet Q)
      (coefficientCutoff nu omega L).toCoeffField).lowerRight i j) hcov hmeas
  rw [hz] at h
  exact h

end Stationarity

end

end SuperdiffusionCLT.Section4.Mixing
