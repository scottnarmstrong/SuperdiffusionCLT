/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Probability.OrliczProduct
public import SuperdiffusionCLT.Section2.Annealed.Integrability
public import SuperdiffusionCLT.Section2.Annealed.MixingAnchorAssembly
public import SuperdiffusionCLT.Section2.Annealed.Symmetry
public import SuperdiffusionCLT.Section2.Localization.LoewnerMinAlgebra
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3InputsE
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3LocAnchor

/-!
# The balanced conjunct `e.refined.localization.twoo` from the one-sided conjunct

The main statement `sigmaStarInv_mixing_minscale` (the printed lemma `l.mixing.minscale` of the
paper) has a conclusion with one existential constant `C` and two conjuncts.  The first,
`e.sstarL.quenched.lb`, is supplied by the assembly
`sigmaStarInv_mixing_minscale_of_anchors_midpoint`; the second,
`e.refined.localization.twoo`, is the relative bilinear bound

`2 p·H q ≤ (X₁ + X₂) (p·s_{L,*}(cu_n) p + q·s_{L,*}(cu_n) q)`

with `H = (k_L − k_ℓ)_{cu_n}` the averaged stream increment on `cu_n`, in the sandwich reading
of the bound.  The conjunct is not used anywhere below `l.RHS.term3`.  It is assembled with the
first conjunct directly, and not through a hypothesis stated *without* the `nu ≤ 1` binder of
its own
conclusion, since such a hypothesis would be strictly stronger than the conjunct 2 and could
not be filled by a proof of the conjunct.

## What this module does

It closes the conjunct from the *one-sided* conjunct, with no new probability
theory.  The printed proof multiplies the two available estimates:

* Step G, `isBigO_gammaSigma_matrixOperatorNorm_streamIncrementAverage`,
  `|H| = O_{Γ₂}(C (L−ℓ)^{1/2})` in operator norm;
* the one-sided conjunct, `s_{L,*}^{-1}(cu_n) ≤ σ̄_{L,*}^{-1}(cu_h) + X ω · Id`
  with `X = O_{Γ₂}(C ν^{-2} 3^{-(n-h)/4})`.

The deterministic half is the matrix algebra of the multiplication step, which
needs no symmetry of `H`: the operator-norm sandwich (proved as
`matLoewnerLE_matrixOperatorNorm_smul_one`), the identity
`‖ξ‖² ≤ ‖s_{L,*}^{-1}‖ · ξ · s_{L,*}(cu_n) ξ` for a left-inverse pair
(proved as
`Book.Ch02.vecNormSq_le_matrixOperatorNorm_mul_vecDot_matVecMul_of_posSemidef_of_leftInverse`),
and the resulting bilinear bound

`2 p·H q ≤ ‖H‖ · M · (p·s_{L,*}(cu_n) p + q·s_{L,*}(cu_n) q)`

at `M = σ̄_{L,*}^{-1}(cu_h) + |X ω|`.  The two Orlicz witnesses are then
`X₁ ω = ‖H ω‖ · σ̄_{L,*}^{-1}(cu_h)` (`Γ₂`, the proved Step G) and
`X₂ ω = ‖H ω‖ · |X ω|` (`Γ₂ · Γ₂ → Γ₁` by the proved product rule
`isBigO_gammaSigma_mul`).

## Main results

* `mixing_minscale_conjunct2_of_conjunct1`: the balanced conjunct, verbatim,
  from the one-sided conjunct at its own constant.
* `mixingConjunct2Const`: the constant of the balanced conjunct, and the auxiliary estimates
  `mixingConj2_bilinear_le` and `mixingAmpConst_nonneg` behind it.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Annealed

open Homogenization MeasureTheory
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Section2.CoarseGraining
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Localization
open SuperdiffusionCLT.Section3.Terms

noncomputable section

variable {d : ℕ}

/-! ## The deterministic matrix algebra of the multiplication step -/

/-- A Loewner comparison between two scalar multiples of the identity. -/
theorem mixingConj2_smul_one_le_smul_one {c c' : ℝ} (h : c ≤ c') :
    MatLoewnerLE (c • (1 : Mat d)) (c' • (1 : Mat d)) := by
  refine matLoewnerLE_of_quad_le fun y => ?_
  rw [quad_smul, quad_one, quad_smul, quad_one]
  exact mul_le_mul_of_nonneg_right h (vecNormSq_nonneg y)

/-- **`‖ξ‖² ≤ M · ξ · A ξ`** from a positive-semidefinite left inverse `B` of
`A` with `‖B‖ ≤ M`.  This is the proved
`vecNormSq_le_matrixOperatorNorm_mul_vecDot_matVecMul_of_posSemidef_of_leftInverse`
composed with the operator-norm bound.  No symmetry of `A` is used. -/
theorem mixingConj2_vecNormSq_le_mul_quad {A B : Mat d} (hB : B.PosSemidef)
    (hleft : ∀ ξ : Vec d, matVecMul B (matVecMul A ξ) = ξ) {M : ℝ}
    (hM : matrixOperatorNorm B ≤ M) (ξ : Vec d) :
    vecNormSq ξ ≤ M * vecDot ξ (matVecMul A ξ) := by
  have hquad : 0 ≤ vecDot ξ (matVecMul A ξ) := by
    have h := hB.dotProduct_mulVec_nonneg (matVecMul A ξ)
    have h' : 0 ≤ vecDot (matVecMul A ξ) (matVecMul B (matVecMul A ξ)) := by
      simpa only [dotProduct, Matrix.mulVec, vecDot, matVecMul, RCLike.star_def, star_trivial,
        conj_trivial] using h
    rw [hleft ξ] at h'
    rw [vecDot_comm] at h'
    exact h'
  exact
    (vecNormSq_le_matrixOperatorNorm_mul_vecDot_matVecMul_of_posSemidef_of_leftInverse
      hB hleft ξ).trans (mul_le_mul_of_nonneg_right hM hquad)

/-- **The bilinear form of the multiplication step.**  If `B` is a
positive-semidefinite left inverse of `A` with `‖B‖ ≤ M`, then for every matrix
`H` and all `p, q`

`2 p·H q ≤ ‖H‖ · M · (p·A p + q·A q)`.

This is the square-root-free form of `|A^{-1/2} H A^{-1/2}| ≤ M` of the
sandwich form. -/
theorem mixingConj2_bilinear_le {H A B : Mat d} {M : ℝ} (hB : B.PosSemidef)
    (hleft : ∀ ξ : Vec d, matVecMul B (matVecMul A ξ) = ξ)
    (hM : matrixOperatorNorm B ≤ M) (p q : Vec d) :
    2 * vecDot p (matVecMul H q) ≤
      matrixOperatorNorm H * M *
        (vecDot p (matVecMul A p) + vecDot q (matVecMul A q)) := by
  have hp := mixingConj2_vecNormSq_le_mul_quad hB hleft hM p
  have hq := mixingConj2_vecNormSq_le_mul_quad hB hleft hM q
  have hHnn : 0 ≤ matrixOperatorNorm H := matrixOperatorNorm_nonneg H
  have hstep1 : 2 * vecDot p (matVecMul H q) ≤
      matrixOperatorNorm H * (2 * (vecNorm p * vecNorm q)) := by
    have hcs : vecDot p (matVecMul H q) ≤ vecNorm p * vecNorm (matVecMul H q) :=
      le_trans (le_abs_self _) (abs_vecDot_le_vecNorm_mul_vecNorm p (matVecMul H q))
    have hHq : vecNorm (matVecMul H q) ≤ matrixOperatorNorm H * vecNorm q :=
      vecNorm_matVecMul_le_matrixOperatorNorm_mul_vecNorm H q
    have h1 : vecDot p (matVecMul H q) ≤
        vecNorm p * (matrixOperatorNorm H * vecNorm q) :=
      hcs.trans (mul_le_mul_of_nonneg_left hHq (vecNorm_nonneg p))
    calc 2 * vecDot p (matVecMul H q)
        ≤ 2 * (vecNorm p * (matrixOperatorNorm H * vecNorm q)) := by
          linarith only [h1]
      _ = matrixOperatorNorm H * (2 * (vecNorm p * vecNorm q)) := by ring
  have hstep2 : 2 * (vecNorm p * vecNorm q) ≤ vecNormSq p + vecNormSq q := by
    have h := sq_nonneg (vecNorm p - vecNorm q)
    have hp2 := vecNorm_sq_eq_vecNormSq p
    have hq2 := vecNorm_sq_eq_vecNormSq q
    nlinarith only [h, hp2, hq2]
  have hstep3 : vecNormSq p + vecNormSq q ≤
      M * (vecDot p (matVecMul A p) + vecDot q (matVecMul A q)) := by
    have h := add_le_add hp hq
    have heq : M * vecDot p (matVecMul A p) + M * vecDot q (matVecMul A q) =
        M * (vecDot p (matVecMul A p) + vecDot q (matVecMul A q)) := by ring
    linarith only [h, heq]
  calc 2 * vecDot p (matVecMul H q)
      ≤ matrixOperatorNorm H * (2 * (vecNorm p * vecNorm q)) := hstep1
    _ ≤ matrixOperatorNorm H *
          (M * (vecDot p (matVecMul A p) + vecDot q (matVecMul A q))) :=
        mul_le_mul_of_nonneg_left (hstep2.trans hstep3) hHnn
    _ = matrixOperatorNorm H * M *
          (vecDot p (matVecMul A p) + vecDot q (matVecMul A q)) := by ring

/-! ## The carriers: invertibility of the cutoff starred inverse -/

/-- **`s_{L,*}^{-1}(cu_n)` is invertible at the cutoff coefficient.**  The
Chapter 2 nondegeneracy `isUnit_det_sigmaStarInvCoarse` on the open-cube
carrier, transported to the half-open cube of the statement. -/
theorem isUnit_det_sigmaStarInvCoarse_cutoffCube [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (L : ℕ) (omega : ShellSeq d) (Q : TriadicCube d) :
    IsUnit (Homogenization.sigmaStarInvCoarse (cubeSet Q)
      (coefficientCutoff nu omega L).toCoeffField).det := by
  rw [SuperdiffusionCLT.Section3.Terms.sigmaStarInvCoarse_cubeSet_eq_openCubeSet]
  have h := Book.Ch02.isUnit_det_sigmaStarInvCoarse (Book.Ch02.cubeDomain Q)
    ((Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
      (coefficientCutoff nu omega L)
      (aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega L)).coeffOn Q)
  rwa [← sigmaStarInvCoarse_toCoeffField,
    Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField_coeffOn_toCoeffField,
    Book.Ch02.cubeDomain_coe] at h

/-- **`s_{L,*}^{-1}(cu_n)` inverts `s_{L,*}(cu_n)`.** -/
theorem sigmaStarInvCoarse_mul_sigmaStarCoarse_cubeSet {Q : TriadicCube d}
    {a : CoeffField d} (hdet : IsUnit (Homogenization.sigmaStarInvCoarse (cubeSet Q) a).det) :
    Homogenization.sigmaStarInvCoarse (cubeSet Q) a *
      Homogenization.sigmaStarCoarse (cubeSet Q) a = 1 := by
  simpa only [Homogenization.sigmaStarCoarse] using
    Matrix.mul_nonsing_inv (Homogenization.sigmaStarInvCoarse (cubeSet Q) a) hdet

/-- **The left-inverse identity on vectors**: `s_{L,*}^{-1}(cu_n)` recovers `ξ`
from `s_{L,*}(cu_n) ξ`. -/
theorem matVecMul_sigmaStarInvCoarse_sigmaStarCoarse_cubeSet {Q : TriadicCube d}
    {a : CoeffField d} (hdet : IsUnit (Homogenization.sigmaStarInvCoarse (cubeSet Q) a).det)
    (ξ : Vec d) :
    matVecMul (Homogenization.sigmaStarInvCoarse (cubeSet Q) a)
      (matVecMul (Homogenization.sigmaStarCoarse (cubeSet Q) a) ξ) = ξ := by
  rw [matVecMul_mul, sigmaStarInvCoarse_mul_sigmaStarCoarse_cubeSet hdet]
  funext k
  simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]

/-! ## The constant of the balanced conjunct -/

/-- The constant of the balanced conjunct as a function of the one-sided
conjunct's constant `CM`: it dominates the Step-G amplitude
`streamIncrementNormConst d` (the `X₁` clause) and the product amplitude
`orliczProductConst 2 2 * streamIncrementNormConst d * CM` (the `X₂` clause). -/
def mixingConjunct2Const (d : ℕ) (CM : ℝ) : ℝ :=
  max (streamIncrementNormConst d)
    (orliczProductConst 2 2 * streamIncrementNormConst d * CM)

/-- **The mixing amplitude constant is nonnegative.**  This discharges the sign
hypothesis `0 ≤ CM` of the statements below from the constant domination
`mixingAmpConst CL CFluc CDet ≤ CM` together with the positivity of the three
packaging constants, in one line. -/
theorem mixingAmpConst_nonneg {CL CFluc CDet : ℝ} (hCL : 0 < CL) (hCFluc : 0 < CFluc)
    (hCDet : 0 < CDet) : 0 ≤ mixingAmpConst CL CFluc CDet := by
  have hg := Homogenization.IndependentSums.two_le_gammaGrowthConst (2 : ℝ)
  have hX : 0 < Homogenization.IndependentSums.gammaGrowthConst 2 ^ (12 : ℝ) :=
    Real.rpow_pos_of_pos (lt_of_lt_of_le (by norm_num) hg) _
  unfold mixingAmpConst Homogenization.IndependentSums.gammaTriangleConst
  positivity

/-! ## The balanced conjunct from the one-sided conjunct -/

/-- **`e.refined.localization.twoo` from `e.sstarL.quenched.lb`.**  The
balanced conjunct of `l.mixing.minscale`, at the constant
`mixingConjunct2Const d CM` determined by the one-sided conjunct's own constant
`CM`, from that conjunct carried verbatim as its own named hypothesis.

Nothing new from probability theory enters: the `Γ₂` amplitude of `X₁` is the
proved Step G, the `Γ₁` amplitude of `X₂` is the proved product rule applied to
Step G and to the one-sided conjunct's `Γ₂` variable, and the deterministic
content is the matrix algebra of `mixingConj2_bilinear_le`.

The one-sided hypothesis `hOne` carries `ShellLawJ4` besides
`ShellLawJ1Restriction`, `J2` and `J3`: the corrected Step-E at the printed intermediate
scale `(n + h + 1) / 2` needs all five `J`-binders
(`isBigO_gammaSigma_descendantAverage_entry_of_colorPartition`), and this binder is where the
chain hands them to the one-sided conjunct. -/
theorem mixing_minscale_conjunct2_of_conjunct1 (d : ℕ) [NeZero d] {CM : ℝ} (hCM : 0 ≤ CM)
    (hOne : ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ P : ProbabilityMeasure (ShellSeq d),
          ShellLawPrefix d P → ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P →
          ShellLawJ4 d P →
          ∀ h n L : ℕ, h < n → n ≤ L →
            ∃ X : ShellSeq d → ℝ, Measurable X ∧
              IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2) X
                (CM * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4))) ∧
              ∀ omega : ShellSeq d,
                MatLoewnerLE
                  (Homogenization.sigmaStarInvCoarse (cubeSet (originCube d (n : ℤ)))
                    (coefficientCutoff nu omega L).toCoeffField)
                  (sigmaBarStarInv nu L P (cubeSet (originCube d (h : ℤ))) +
                    X omega • (1 : Mat d))) :
    ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
      ∀ P : ProbabilityMeasure (ShellSeq d),
        ShellLawPrefix d P → ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P →
        ShellLawJ4 d P →
        ∀ h n l L : ℕ, h < n → n < l → l < L →
          ∃ X1 X2 : ShellSeq d → ℝ,
            Measurable X1 ∧
            IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2) X1
              (mixingConjunct2Const d CM * ((L - l : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
                sigmaBarStarInvScalar nu L P (cubeSet (originCube d (h : ℤ)))) ∧
            Measurable X2 ∧
            IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 1) X2
              (mixingConjunct2Const d CM * nu ^ (-(2 : ℝ)) *
                ((L - l : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
                (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4))) ∧
            ∀ (omega : ShellSeq d) (p q : Vec d),
              2 * vecDot p (matVecMul
                  (volumeAverageMat (cubeSet (originCube d (n : ℤ)))
                    (fun y => finiteShellIncrement omega l L y)) q) ≤
                (X1 omega + X2 omega) *
                  (vecDot p (matVecMul
                    (Homogenization.sigmaStarCoarse (cubeSet (originCube d (n : ℤ)))
                      (coefficientCutoff nu omega L).toCoeffField) p) +
                   vecDot q (matVecMul
                    (Homogenization.sigmaStarCoarse (cubeSet (originCube d (n : ℤ)))
                      (coefficientCutoff nu omega L).toCoeffField) q)) := by
  intro nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 h n l L hhn hnl hlL
  -- the one-sided conjunct at the triple `h < n ≤ L`
  obtain ⟨X, hXmeas, hXbigO, hXloew⟩ :=
    hOne nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 h n L hhn (le_of_lt (lt_trans hnl hlL))
  -- the carriers of the bilinear form
  let Hfun : ShellSeq d → Mat d := fun omega =>
    volumeAverageMat (cubeSet (originCube d (n : ℤ)))
      (fun y => finiteShellIncrement omega l L y)
  let sc : ℝ := sigmaBarStarInvScalar nu L P (cubeSet (originCube d (h : ℤ)))
  let X1 : ShellSeq d → ℝ := fun omega => matrixOperatorNorm (Hfun omega) * sc
  let X2 : ShellSeq d → ℝ := fun omega => matrixOperatorNorm (Hfun omega) * |X omega|
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hsc : 0 ≤ sc :=
    (sigmaBarStarInvScalar_pos_cutoff hnu L hPrefix hJ2 hJ3 hJ4 (h : ℤ)).le
  have hr : 0 ≤ ((L - l : ℕ) : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hnu2nn : 0 ≤ nu ^ (-(2 : ℝ)) := Real.rpow_nonneg hnu.le _
  have h3nn : 0 ≤ (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4)) :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
  have hCH : 0 ≤ streamIncrementNormConst d := (streamIncrementNormConst_pos hd).le
  -- the proved Step G, in the carrier
  have hG : IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d => matrixOperatorNorm (Hfun omega))
      (streamIncrementNormConst d * Real.sqrt ((L - l : ℕ) : ℝ)) :=
    isBigO_gammaSigma_matrixOperatorNorm_streamIncrementAverage (d := d)
      hPrefix hJ2 hJ3 hJ4 (nn := n) (l := l) (L := L) (le_of_lt hnl) hlL
  have hHmeas : Measurable Hfun :=
    measurable_volumeAverageMat_finiteShellIncrement (d := d) l L (originCube d (n : ℤ))
  have hHnorm : Measurable (fun omega : ShellSeq d => matrixOperatorNorm (Hfun omega)) :=
    SuperdiffusionCLT.Frozen.Assumptions.ShellField.continuous_matrixOperatorNorm.measurable.comp
      hHmeas
  have hsqrt : Real.sqrt ((L - l : ℕ) : ℝ) = ((L - l : ℕ) : ℝ) ^ ((1 : ℝ) / 2) :=
    (Real.sqrt_eq_rpow _)
  rw [hsqrt] at hG
  refine ⟨X1, X2, ?_, ?_, ?_, ?_, ?_⟩
  · exact hHnorm.mul measurable_const
  · -- `X₁`: the Step-G `Γ₂` amplitude, at the constant of the conjunct
    have hcm := hG.const_mul hsc
    refine (hcm.of_abs_le fun omega => ?_).mono_scale ?_
    · have h1 : |X1 omega| = matrixOperatorNorm (Hfun omega) * sc := by
        have hz : X1 omega = matrixOperatorNorm (Hfun omega) * sc := rfl
        rw [hz]
        exact abs_of_nonneg (mul_nonneg (matrixOperatorNorm_nonneg _) hsc)
      have h2 : |sc * matrixOperatorNorm (Hfun omega)|
          = matrixOperatorNorm (Hfun omega) * sc := by
        rw [abs_of_nonneg (mul_nonneg hsc (matrixOperatorNorm_nonneg _))]
        ring
      rw [h1, h2]
    · have hle : streamIncrementNormConst d ≤ mixingConjunct2Const d CM :=
        le_max_left _ _
      calc sc * (streamIncrementNormConst d * ((L - l : ℕ) : ℝ) ^ ((1 : ℝ) / 2))
          = sc * streamIncrementNormConst d * ((L - l : ℕ) : ℝ) ^ ((1 : ℝ) / 2) := by
            ring
        _ ≤ sc * mixingConjunct2Const d CM * ((L - l : ℕ) : ℝ) ^ ((1 : ℝ) / 2) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hsc) hr
        _ = mixingConjunct2Const d CM * ((L - l : ℕ) : ℝ) ^ ((1 : ℝ) / 2) * sc := by
            ring
  · exact hHnorm.mul (continuous_abs.measurable.comp hXmeas)
  · -- `X₂`: the product rule `Γ₂ · Γ₂ → Γ₁`
    have hA2 : 0 ≤ CM * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4)) :=
      mul_nonneg (mul_nonneg hCM hnu2nn) h3nn
    have hA1 : 0 ≤ streamIncrementNormConst d * ((L - l : ℕ) : ℝ) ^ ((1 : ℝ) / 2) :=
      mul_nonneg hCH hr
    have hprod := isBigO_gammaSigma_mul (mu := P.toMeasure)
      (X₁ := fun omega : ShellSeq d => matrixOperatorNorm (Hfun omega)) (X₂ := X)
      (A₁ := streamIncrementNormConst d * ((L - l : ℕ) : ℝ) ^ ((1 : ℝ) / 2))
      (A₂ := CM * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4)))
      (σ₁ := (2 : ℝ)) (σ₂ := (2 : ℝ)) (by norm_num) (by norm_num) hA1 hA2 hG hXbigO
    rw [show (2 : ℝ) * 2 / ((2 : ℝ) + 2) = 1 from by norm_num] at hprod
    refine (hprod.of_abs_le fun omega => ?_).mono_scale ?_
    · have h1 : |X2 omega| = matrixOperatorNorm (Hfun omega) * |X omega| := by
        have hz : X2 omega = matrixOperatorNorm (Hfun omega) * |X omega| := rfl
        rw [hz]
        exact abs_of_nonneg (mul_nonneg (matrixOperatorNorm_nonneg _) (abs_nonneg _))
      have h2 : |matrixOperatorNorm (Hfun omega) * X omega|
          = matrixOperatorNorm (Hfun omega) * |X omega| := by
        rw [abs_mul, abs_of_nonneg (matrixOperatorNorm_nonneg _)]
      rw [h1, h2]
    · have hle : orliczProductConst 2 2 * streamIncrementNormConst d * CM ≤
          mixingConjunct2Const d CM := le_max_right _ _
      calc orliczProductConst 2 2 *
            ((streamIncrementNormConst d * ((L - l : ℕ) : ℝ) ^ ((1 : ℝ) / 2)) *
              (CM * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4))))
          = orliczProductConst 2 2 * streamIncrementNormConst d * CM *
              ((L - l : ℕ) : ℝ) ^ ((1 : ℝ) / 2) * nu ^ (-(2 : ℝ)) *
              (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4)) := by ring
        _ ≤ mixingConjunct2Const d CM * ((L - l : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
              nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hle hr) hnu2nn) h3nn
        _ = mixingConjunct2Const d CM * nu ^ (-(2 : ℝ)) *
              ((L - l : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
              (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4)) := by ring
  · -- the bilinear form, pointwise in the sample
    intro omega p q
    have hpsd : (Homogenization.sigmaStarInvCoarse (cubeSet (originCube d (n : ℤ)))
        (coefficientCutoff nu omega L).toCoeffField).PosSemidef :=
      posSemidef_sigmaStarInvCoarse_cutoffCube hnu L omega (originCube d (n : ℤ))
    have hunit := isUnit_det_sigmaStarInvCoarse_cutoffCube hnu L omega (originCube d (n : ℤ))
    have hleft := matVecMul_sigmaStarInvCoarse_sigmaStarCoarse_cubeSet
      (Q := originCube d (n : ℤ)) hunit
    -- the one-sided conjunct, scalarized and capped at `sc + |X omega|`
    have h1 := hXloew omega
    rw [sigmaBarStarInv_originCube_eq_smul_one hnu L hJ4 (h : ℤ)] at h1
    have h2 : MatLoewnerLE
        (Homogenization.sigmaStarInvCoarse (cubeSet (originCube d (n : ℤ)))
          (coefficientCutoff nu omega L).toCoeffField)
        ((sc + X omega) • (1 : Mat d)) := by
      simpa only [add_smul] using h1
    have h3 : MatLoewnerLE ((sc + X omega) • (1 : Mat d))
        ((sc + |X omega|) • (1 : Mat d)) :=
      mixingConj2_smul_one_le_smul_one (add_le_add (le_refl sc) (le_abs_self (X omega)))
    have hM0 : 0 ≤ sc + |X omega| := add_nonneg hsc (abs_nonneg _)
    have hnorm := matrixOperatorNorm_le_of_matLoewnerLE_of_posSemidef hpsd
      (Matrix.PosSemidef.one.smul hM0) (h2.trans h3)
    rw [matrixOperatorNorm_smul_one_eq_of_nonneg hM0] at hnorm
    have hbil := mixingConj2_bilinear_le (H := Hfun omega)
      (A := Homogenization.sigmaStarCoarse (cubeSet (originCube d (n : ℤ)))
        (coefficientCutoff nu omega L).toCoeffField)
      (B := Homogenization.sigmaStarInvCoarse (cubeSet (originCube d (n : ℤ)))
        (coefficientCutoff nu omega L).toCoeffField)
      hpsd hleft hnorm p q
    have heq : X1 omega + X2 omega = matrixOperatorNorm (Hfun omega) * (sc + |X omega|) := by
      have hz1 : X1 omega = matrixOperatorNorm (Hfun omega) * sc := rfl
      have hz2 : X2 omega = matrixOperatorNorm (Hfun omega) * |X omega| := rfl
      rw [hz1, hz2]
      ring
    rw [heq]
    exact hbil

/-! ## The balanced conjunct from the localization anchor -/

/-! ## The main statement from the two conjuncts, both discharged -/

end

end SuperdiffusionCLT.Section2.Annealed
