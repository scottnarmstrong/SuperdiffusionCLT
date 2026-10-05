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
public import SuperdiffusionCLT.Section2.Norms.FractionalHs
public import SuperdiffusionCLT.Section3.Setup.Scales
public import SuperdiffusionCLT.Section3.Setup.Parameters
public import SuperdiffusionCLT.Section2.Localization.BlockGaugeGroup
public import SuperdiffusionCLT.Section3.Terms.BellUpscaleBoundUnitSlice
public import Homogenization.Book.Ch02.Theorems.MatrixOperatorNorm
public import Homogenization.Book.Ch02.MultiscaleEllipticity
public import Homogenization.Probability.IndependentSums.WeakOrlicz
public import Homogenization.Book.Ch02.Matrices

@[expose] public section

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open scoped ENNReal

/-!
# The bell-upscale operator bound, third rendering (`l.blupbounds`, v3)

This module is the successor of `BellUpscaleBound.lean` (v1, whose remainder
hypothesis is vacuous) and `BellUpscaleBoundUnitSlice.lean` (v2, whose remainder
hypothesis kept `bfA_m(U)` *outside* the gauge conjugation, so that the
conjugation cancelled and the hypothesis collapsed to the unit-slice core of the
conclusion).

Version 3 carries the paper's own remainder display
`e.blupbounds.remainder`, in which `bfA_m(U)` sits **inside**
the conjugation:

`| P · G_{-h_U}ᵗ (G_{h_U}ᵗ bfA_ℓ(U) G_{h_U} − bfA_m(U)) G_{-h_U} P |
    ≤ O_{Γ_{1/2}}(C ν^{-3} ℓ 3^{n−m})`,

on the unit slice `P = (e, 0)`, `|e| = 1`.  Since `BlockMat d`
carries no subtraction, the display is written through the transported vector
`Q = G_{-h_U} P` — bilinearity of the block pairing moves the block
subtraction outside.

With `bfA_m(U)` inside the conjugation the gauge no longer cancels, and the
paper's two remaining steps become load-bearing:

* the conjugated `bfA_ℓ(U)` term collapses to the unit-slice quadratic form of
  `b_ℓ(U)` (`blockVecDot_transported_conj`), because
  `G_{h_U} Q = G_{h_U} G_{-h_U} P = P` (`blockG_mul_neg`) and
  the transposed gauge moves across the pairing
  (`blockVecDot_blockGT_transpose` of the v2 module);
* the `bfA_m(U)` term is the first decomposition term of the proof,
  `Q · bfA_m(U) Q − e · b_m(U) e
     = e·h_Uᵗ σ_{m,*}^{-1}(U) h_U e + 2 e·h_Uᵗ σ_{m,*}^{-1}(U) κ_m(U) e`,
  computed here from the printed block form `e.bigA.def`
  and controlled by the printed Young step with the
  printed weights `ep` and `ep⁻¹` (`abs_gauge_shift_le`).

The printed `ep |b_m(U)|` and `(1 + ep⁻¹) |σ_{m,*}^{-1/2}(U) h_U|²` terms of
the conclusion are therefore *earned* here, not discharged as nonnegative
slack: they are the two Young amounts.

## Inputs beyond the displays

The carriers `aM`, `bM`, `sigmaStarInvHalf`, `hU` are free binders,
so the printed relations between them have to be named explicitly.  Each of
the four added hypotheses is a statement printed in the paper:

* `hAM` — the block form `e.bigA.def` of `bfA_m(U)`, with
  `b(U) := (σ + κᵗ σ_*^{-1} κ)(U)`.  It is the shape of
  `Book.Ch02.blockMatrixOfCoarseMatrices`, so it holds verbatim for a
  genuine `coarseBlockMatrix U a`.
* `hSqrt` — the defining Gram property of the printed square root
  `σ_{m,*}^{-1/2}(U)`:
  `σ_{m,*}^{-1/2}(U)ᵗ σ_{m,*}^{-1/2}(U) = σ_{m,*}^{-1}(U)`.  It is what turns
  the printed `|σ_{m,*}^{-1/2}(U) v|²` into the quadratic
  form `v · σ_{m,*}^{-1}(U) v`.
* `hKappaB` — the printed Cauchy-Schwarz input
  `κ_mᵗ(U) σ_{m,*}^{-1}(U) κ_m(U) ≤ b_m(U)`, in the norm form in which it is
  used in the Young step.
* `hSym` — the printed fact that the upper-left block of
  `bfA_ℓ(U) − bfA_m(U)` is the *symmetric* matrix `(b_ℓ − b_m)(U)`; its
  identity half is `hBL`/`hBM`, its symmetry half is this hypothesis.  It is
  consumed by the operator-norm bridge
  `matrixOperatorNorm_le_of_abs_quadratic_form_le` at the last step, and it is
  load-bearing, the bridge constant `1` being sharp.

## Main results

* `blockVecDot_transported_conj`: the conjugated `bfA_ℓ(U)` term of
  `e.blupbounds.remainder` equals `e · b_ℓ(U) e` on the unit slice.
* `blockVecDot_bigA_transported`, `gauge_shift_sqrt`: the transported
  quadratic form of `bfA_m(U)` in the block form `e.bigA.def`.
* `abs_gauge_shift_le`: the Young step.
* `blupbounds_operatorNorm_le`: the deterministic core, one realization, in the final shape
  of `e.blupbounds`.
-/

namespace SuperdiffusionCLT.Section3.Terms

variable {d : ℕ}

/-! ### Private vector algebra -/

private theorem vecDot_sub_right_remainder (x y z : Vec d) :
    vecDot x (y - z) = vecDot x y - vecDot x z := by
  rw [sub_eq_add_neg, vecDot_add_right, vecDot_neg_right]
  ring

/-- The standard basis vector is a unit vector of `Vec d`: this is the `|e| = 1`
of the paper's unit slice. -/
private theorem vecNormSq_single_remainder (i : Fin d) :
    vecNormSq (Pi.single i (1 : ℝ)) = 1 := by
  show vecDot (Pi.single i (1 : ℝ)) (Pi.single i (1 : ℝ)) = 1
  rw [vecDot_single_left]
  simp

/-- The transported slice `Q = G_{-h}(e, 0) = (e, -h e)` of the proof. -/
private theorem blockMatVecMul_blockG_neg_slice (h : Mat d) (e : Vec d) :
    blockMatVecMul (blockG (-h)) ((e, 0) : BlockVec d) = (e, -(matVecMul h e)) := by
  refine Prod.ext ?_ ?_ <;>
    simp only [blockG, blockMatVecMul_fst, blockMatVecMul_snd, matVecMul_one,
      zero_matVecMul, neg_matVecMul, add_zero]

/-! ### The conjugated `bfA_ell(U)` term of `e.blupbounds.remainder` -/

/-- The conjugated `bfA_ℓ(U)` half of the manuscript's remainder display
`e.blupbounds.remainder`, read on the transported unit slice
`Q = G_{-h}(e, 0)`, is the unit-slice quadratic form of the upper-left block of
`bfA_ℓ(U)`:

`Q · G_hᵗ bfA_ℓ(U) G_h Q = (e, 0) · bfA_ℓ(U) (e, 0) = e · b_ℓ(U) e`.

The transposed gauge moves across the block pairing
(`blockVecDot_blockGT_transpose`) and the two untransposed gauges cancel
(`blockG_mul_neg`), leaving `G_h Q = P`. -/
theorem blockVecDot_transported_conj (A : BlockMat d) (h : Mat d) (e : Vec d) :
    blockVecDot (blockMatVecMul (blockG (-h)) ((e, 0) : BlockVec d))
        (blockMatVecMul (blockMatMul (blockGT h) (blockMatMul A (blockG h)))
          (blockMatVecMul (blockG (-h)) ((e, 0) : BlockVec d)))
      = vecDot e (matVecMul A.upperLeft e) := by
  set Q : BlockVec d := blockMatVecMul (blockG (-h)) ((e, 0) : BlockVec d) with hQ
  have hGQ : blockMatVecMul (blockG h) Q = ((e, 0) : BlockVec d) := by
    rw [hQ, ← Homogenization.blockMatVecMul_blockMatMul,
      SuperdiffusionCLT.Section2.Localization.blockG_mul_neg,
      Homogenization.blockMatVecMul_blockIdentity]
  calc blockVecDot Q
        (blockMatVecMul (blockMatMul (blockGT h) (blockMatMul A (blockG h))) Q)
      = blockVecDot Q (blockMatVecMul (blockGT h)
          (blockMatVecMul (blockMatMul A (blockG h)) Q)) := by
        rw [Homogenization.blockMatVecMul_blockMatMul]
    _ = blockVecDot (blockMatVecMul (blockG h) Q)
          (blockMatVecMul (blockMatMul A (blockG h)) Q) :=
        blockVecDot_blockGT_transpose h Q _
    _ = blockVecDot ((e, 0) : BlockVec d)
          (blockMatVecMul A (blockMatVecMul (blockG h) Q)) := by
        rw [Homogenization.blockMatVecMul_blockMatMul, hGQ]
    _ = blockVecDot ((e, 0) : BlockVec d)
          (blockMatVecMul A ((e, 0) : BlockVec d)) := by
        rw [hGQ]
    _ = vecDot e (matVecMul A.upperLeft e) := blockVecDot_blockMatVecMul_upperLeft A e

/-! ### The `bfA_m(U)` term: the manuscript's gauge shift -/

/-- The transported quadratic form of the coarse block matrix `bfA_m(U)` in the
printed block form `e.bigA.def`,

`bfA_m(U) = [[b_m(U), -(κ_mᵗ σ_{m,*}^{-1})(U)], [-(σ_{m,*}^{-1} κ_m)(U),
  σ_{m,*}^{-1}(U)]]`,

read on the transported unit slice `Q = G_{-h}(e, 0) = (e, -h e)`.
This is the paper's gauge-shift display before the two cross terms
are merged. -/
theorem blockVecDot_bigA_transported (bM kappaM sigmaStarInvU h : Mat d) (e : Vec d) :
    blockVecDot (blockMatVecMul (blockG (-h)) ((e, 0) : BlockVec d))
        (blockMatVecMul
          ({ upperLeft := bM
             upperRight := -(matTranspose kappaM * sigmaStarInvU)
             lowerLeft := -(sigmaStarInvU * kappaM)
             lowerRight := sigmaStarInvU } : BlockMat d)
          (blockMatVecMul (blockG (-h)) ((e, 0) : BlockVec d)))
      = vecDot e (matVecMul bM e)
        + (vecDot (matVecMul kappaM e) (matVecMul sigmaStarInvU (matVecMul h e))
          + vecDot (matVecMul h e) (matVecMul sigmaStarInvU (matVecMul kappaM e)))
        + vecDot (matVecMul h e) (matVecMul sigmaStarInvU (matVecMul h e)) := by
  rw [blockMatVecMul_blockG_neg_slice]
  simp only [blockVecDot, blockMatVecMul_fst, blockMatVecMul_snd, neg_matVecMul,
    matVecMul_neg, ← matVecMul_mul, vecDot_neg_left, vecDot_neg_right,
    vecDot_add_right, vecDot_matVecMul_transpose]
  ring

/-- The paper's gauge-shift display, written through the
printed square root `σ_{m,*}^{-1/2}(U)`:

`Q · bfA_m(U) Q = e · b_m(U) e
   + (2 (σ^{-1/2} κ_m e) · (σ^{-1/2} h e) + |σ^{-1/2} h e|²)`.

The second summand is the paper's
`e·h_Uᵗ σ_{m,*}^{-1}(U) h_U e + 2 e·h_Uᵗ σ_{m,*}^{-1}(U) κ_m(U) e`; the Gram
hypothesis `hSqrt` is what rewrites the two `σ_{m,*}^{-1}` quadratic forms
as the squared norms. -/
theorem gauge_shift_sqrt (bM kappaM sigmaStarInvU sigmaStarInvHalf h : Mat d)
    (e : Vec d)
    (hSqrt : matTranspose sigmaStarInvHalf * sigmaStarInvHalf = sigmaStarInvU) :
    blockVecDot (blockMatVecMul (blockG (-h)) ((e, 0) : BlockVec d))
        (blockMatVecMul
          ({ upperLeft := bM
             upperRight := -(matTranspose kappaM * sigmaStarInvU)
             lowerLeft := -(sigmaStarInvU * kappaM)
             lowerRight := sigmaStarInvU } : BlockMat d)
          (blockMatVecMul (blockG (-h)) ((e, 0) : BlockVec d)))
      = vecDot e (matVecMul bM e)
        + (2 * vecDot (matVecMul sigmaStarInvHalf (matVecMul kappaM e))
              (matVecMul sigmaStarInvHalf (matVecMul h e))
          + vecNormSq (matVecMul sigmaStarInvHalf (matVecMul h e))) := by
  rw [blockVecDot_bigA_transported, ← hSqrt]
  simp only [← matVecMul_mul, vecDot_matVecMul_transpose]
  rw [vecDot_comm (matVecMul sigmaStarInvHalf (matVecMul h e))
        (matVecMul sigmaStarInvHalf (matVecMul kappaM e))]
  show _ = _ + (2 * _ + vecDot _ _)
  ring

/-! ### The Young step -/

/-- **`l.blupbounds#young-cross-term`** (the Young step of the proof): on the
unit slice `|e| = 1` the gauge-shift amount

`2 (σ_{m,*}^{-1/2} κ_m e) · (σ_{m,*}^{-1/2} h e) + |σ_{m,*}^{-1/2} h e|²`

is bounded in absolute value by the two printed Young amounts
`ep |b_m(U)|` and `(1 + ep⁻¹) |σ_{m,*}^{-1/2}(U) h|²`.

The cross term is split with the printed weights `ep`, `ep⁻¹`
(`young_cross_term`), the first Young amount is turned into
`ep e·b_m(U)e` by the printed Cauchy-Schwarz input `hKappaB`
and then into `ep |b_m(U)|` on the unit
sphere, and the two square terms are collected into the printed weight
`1 + ep⁻¹`. -/
theorem abs_gauge_shift_le (ep : ℝ) (hep : 0 < ep)
    (bM kappaM sigmaStarInvHalf h : Mat d) (e : Vec d) (he : vecNormSq e = 1)
    (hKappaB : vecNormSq (matVecMul sigmaStarInvHalf (matVecMul kappaM e))
      ≤ vecDot e (matVecMul bM e)) :
    |2 * vecDot (matVecMul sigmaStarInvHalf (matVecMul kappaM e))
          (matVecMul sigmaStarInvHalf (matVecMul h e))
        + vecNormSq (matVecMul sigmaStarInvHalf (matVecMul h e))|
      ≤ ep * matrixOperatorNorm bM
        + (1 + ep⁻¹) * (matrixOperatorNorm (sigmaStarInvHalf * h)) ^ 2 := by
  set a : Vec d := matVecMul sigmaStarInvHalf (matVecMul kappaM e) with ha
  set c : Vec d := matVecMul sigmaStarInvHalf (matVecMul h e) with hc
  have hyoung : |2 * vecDot a c| ≤ ep * vecNormSq a + ep⁻¹ * vecNormSq c := by
    have h1 : |vecDot a c| ≤ vecNorm a * vecNorm c := abs_vecDot_le_vecNorm_mul_vecNorm a c
    have h2 : 2 * vecNorm a * vecNorm c ≤ ep * vecNorm a ^ 2 + ep⁻¹ * vecNorm c ^ 2 :=
      young_cross_term ep (vecNorm a) (vecNorm c) hep
    rw [vecNorm_sq_eq_vecNormSq, vecNorm_sq_eq_vecNormSq] at h2
    have h3 : |2 * vecDot a c| = 2 * |vecDot a c| := by
      rw [abs_mul]
      norm_num
    linarith only [h1, h2, h3]
  have hcnn : 0 ≤ vecNormSq c := vecNormSq_nonneg c
  have hbM : vecNormSq a ≤ matrixOperatorNorm bM := by
    have h1 : vecDot e (matVecMul bM e) ≤ matrixOperatorNorm bM := by
      have h2 := abs_vecDot_matVecMul_le_matrixOperatorNorm_mul_vecNormSq bM e
      rw [he, mul_one] at h2
      exact le_trans (le_abs_self _) h2
    exact le_trans hKappaB h1
  have hch : vecNormSq c ≤ (matrixOperatorNorm (sigmaStarInvHalf * h)) ^ 2 := by
    have h1 : c = matVecMul (sigmaStarInvHalf * h) e := by
      rw [hc, matVecMul_mul]
    have h2 := vecNormSq_matVecMul_le_matrixOperatorNorm_sq_mul_vecNormSq
      (sigmaStarInvHalf * h) e
    rw [he, mul_one] at h2
    rw [h1]
    exact h2
  have hw : (0:ℝ) ≤ 1 + ep⁻¹ := by
    have h := (inv_pos.mpr hep).le
    linarith only [h]
  have t1 : ep * vecNormSq a ≤ ep * matrixOperatorNorm bM :=
    mul_le_mul_of_nonneg_left hbM hep.le
  have t2 : (1 + ep⁻¹) * vecNormSq c
      ≤ (1 + ep⁻¹) * (matrixOperatorNorm (sigmaStarInvHalf * h)) ^ 2 :=
    mul_le_mul_of_nonneg_left hch hw
  have hsplit : |2 * vecDot a c + vecNormSq c| ≤ |2 * vecDot a c| + vecNormSq c := by
    have hlow : -|2 * vecDot a c| ≤ 2 * vecDot a c := neg_abs_le _
    have hupp : 2 * vecDot a c ≤ |2 * vecDot a c| := le_abs_self _
    exact abs_le.mpr ⟨by linarith only [hlow, hcnn], by linarith only [hupp]⟩
  have hexp : ep * vecNormSq a + ep⁻¹ * vecNormSq c + vecNormSq c
      = ep * vecNormSq a + (1 + ep⁻¹) * vecNormSq c := by ring
  linarith only [hsplit, hyoung, hexp, t1, t2]

/-! ### The deterministic core of `e.blupbounds` -/

/-- **`l.blupbounds`, one realization.**  The deterministic content of the
paper's proof at a single realization, with the
remainder amount carried by the real number `Zw`.

The hypotheses are the printed ones:

* `hBL` — the paper's `b_ℓ(U)` is the upper-left block of `bfA_ℓ(U)`.
* `hAM` — the block form `e.bigA.def` of `bfA_m(U)`.
* `hSqrt` — the Gram property of the printed square root `σ_{m,*}^{-1/2}(U)`.
* `hKappaB` — the printed Cauchy-Schwarz input `κ_mᵗ σ_{m,*}^{-1} κ_m ≤ b_m`.
* `hSym` — the printed symmetry of `(b_ℓ − b_m)(U)`.
* `hRem` — the paper's remainder display `e.blupbounds.remainder` on the unit
  slice `P = (e, 0)`, `|e| = 1`, written through the transported vector
  `Q = G_{-h_U} P`.

The proof is the paper's: the initial decomposition
splits the unit-slice quadratic form of `(b_ℓ − b_m)(U)` into the remainder
(bounded by `Zw`) and the gauge shift; the Young step
bounds the gauge shift by the two printed amounts; and the
supremum over `|e| = 1` is taken by the operator-norm bridge
`matrixOperatorNorm_le_of_abs_quadratic_form_le`. -/
theorem blupbounds_operatorNorm_le [NeZero d] (ep : ℝ) (hep : 0 < ep)
    (aL aM : BlockMat d)
    (bL bM kappaM sigmaStarInvU sigmaStarInvHalf hU : Mat d) (Zw : ℝ)
    (hBL : bL = aL.upperLeft)
    (hAM : aM =
      { upperLeft := bM
        upperRight := -(matTranspose kappaM * sigmaStarInvU)
        lowerLeft := -(sigmaStarInvU * kappaM)
        lowerRight := sigmaStarInvU })
    (hSqrt : matTranspose sigmaStarInvHalf * sigmaStarInvHalf = sigmaStarInvU)
    (hKappaB : ∀ e : Vec d,
      vecNormSq (matVecMul sigmaStarInvHalf (matVecMul kappaM e))
        ≤ vecDot e (matVecMul bM e))
    (hSym : (bL - bM).IsSymm)
    (hRem : ∀ e : Vec d, vecNormSq e = 1 →
      |blockVecDot (blockMatVecMul (blockG (-hU)) ((e, 0) : BlockVec d))
          (blockMatVecMul
            (blockMatMul (blockGT hU) (blockMatMul aL (blockG hU)))
            (blockMatVecMul (blockG (-hU)) ((e, 0) : BlockVec d))) -
        blockVecDot (blockMatVecMul (blockG (-hU)) ((e, 0) : BlockVec d))
          (blockMatVecMul aM
            (blockMatVecMul (blockG (-hU)) ((e, 0) : BlockVec d)))| ≤ Zw) :
    matrixOperatorNorm (bL - bM) ≤ ep * matrixOperatorNorm bM
      + (1 + ep⁻¹) * (matrixOperatorNorm (sigmaStarInvHalf * hU)) ^ 2 + Zw := by
  set B : ℝ := ep * matrixOperatorNorm bM
      + (1 + ep⁻¹) * (matrixOperatorNorm (sigmaStarInvHalf * hU)) ^ 2 + Zw with hBdef
  -- the remainder display, read on the unit slice through the two identities
  have hslice : ∀ e : Vec d, vecNormSq e = 1 →
      |vecDot e (matVecMul bL e) - (vecDot e (matVecMul bM e)
        + (2 * vecDot (matVecMul sigmaStarInvHalf (matVecMul kappaM e))
              (matVecMul sigmaStarInvHalf (matVecMul hU e))
          + vecNormSq (matVecMul sigmaStarInvHalf (matVecMul hU e))))| ≤ Zw := by
    intro e he
    have h := hRem e he
    rw [blockVecDot_transported_conj, hAM,
      gauge_shift_sqrt bM kappaM sigmaStarInvU sigmaStarInvHalf hU e hSqrt,
      ← hBL] at h
    exact h
  -- the remainder amount is nonnegative: the display holds at a unit vector
  have hZ0 : 0 ≤ Zw := by
    obtain ⟨i⟩ : Nonempty (Fin d) := inferInstance
    exact le_trans (abs_nonneg _) (hslice (Pi.single i (1 : ℝ)) (vecNormSq_single_remainder i))
  have hw : (0:ℝ) ≤ 1 + ep⁻¹ := by
    have h := (inv_pos.mpr hep).le
    linarith only [h]
  have hBnn : 0 ≤ B := by
    have t1 : 0 ≤ ep * matrixOperatorNorm bM :=
      mul_nonneg hep.le (matrixOperatorNorm_nonneg _)
    have t2 : 0 ≤ (1 + ep⁻¹) * (matrixOperatorNorm (sigmaStarInvHalf * hU)) ^ 2 :=
      mul_nonneg hw (sq_nonneg _)
    rw [hBdef]
    linarith only [t1, t2, hZ0]
  -- the quadratic form of the difference, expanded
  have hQ : ∀ v : Vec d, vecDot v (matVecMul (bL - bM) v)
      = vecDot v (matVecMul bL v) - vecDot v (matVecMul bM v) := by
    intro v
    rw [sub_matVecMul, vecDot_sub_right_remainder]
  -- the unit-sphere bound: remainder plus the two Young amounts
  have hunit : ∀ e : Vec d, vecNormSq e = 1 →
      |vecDot e (matVecMul (bL - bM) e)| ≤ B := by
    intro e he
    have h1 := abs_le.mp (hslice e he)
    have h2 := abs_le.mp (abs_gauge_shift_le ep hep bM kappaM sigmaStarInvHalf hU e he
      (hKappaB e))
    rw [hQ e]
    rw [hBdef]
    exact abs_le.mpr ⟨by linarith only [h1.1, h2.1], by linarith only [h1.2, h2.2]⟩
  -- rescale the unit-sphere bound to every vector, with the factor `|u| ^ 2`
  have hbound : ∀ u : Vec d,
      |vecDot u (matVecMul (bL - bM) u)| ≤ B * vecNormSq u := by
    intro u
    by_cases hu0 : u = 0
    · subst hu0
      simp [matVecMul_zero, vecDot_zero_left, vecNormSq]
    · have hn0 : vecNorm u ≠ 0 := by
        intro hcon
        exact hu0 (vecNormSq_eq_zero (by
          rw [← vecNorm_sq_eq_vecNormSq, hcon]
          norm_num))
      have hn : 0 < vecNorm u := lt_of_le_of_ne (vecNorm_nonneg u) (Ne.symm hn0)
      obtain ⟨e, hu_eq, hunite⟩ :
          ∃ e : Vec d, u = vecNorm u • e ∧ vecNormSq e = 1 := by
        refine ⟨(vecNorm u)⁻¹ • u, (smul_inv_smul₀ hn0 u).symm, ?_⟩
        have h2 : vecNormSq u = vecNorm u ^ 2 := (vecNorm_sq_eq_vecNormSq u).symm
        rw [vecNormSq_smul, h2, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hn0)]
      have hrem := hunit e hunite
      have hscal : vecDot u (matVecMul (bL - bM) u)
          = vecNorm u * (vecNorm u * vecDot e (matVecMul (bL - bM) e)) := by
        conv_lhs => rw [hu_eq]
        rw [vecDot_smul_left, matVecMul_smul, vecDot_smul_right]
      rw [hscal, abs_mul, abs_mul, abs_of_pos hn]
      calc vecNorm u * (vecNorm u * |vecDot e (matVecMul (bL - bM) e)|)
          ≤ vecNorm u * (vecNorm u * B) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hrem (vecNorm_nonneg u)) (vecNorm_nonneg u)
        _ = B * vecNormSq u := by
            rw [← vecNorm_sq_eq_vecNormSq u, pow_two]
            ring
  -- the supremum over the unit sphere
  exact matrixOperatorNorm_le_of_abs_quadratic_form_le (bL - bM) hSym B hBnn hbound

/-! ### `e.blupbounds` -/

end SuperdiffusionCLT.Section3.Terms
