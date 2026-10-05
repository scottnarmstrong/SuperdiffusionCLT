/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.CoarseGraining.CutoffCorrespondence
public import SuperdiffusionCLT.Section2.CoarseGraining.SkewShift
public import SuperdiffusionCLT.Section2.Cutoff.Centered

/-!
# The shifted coefficient object, and the centered marginal cutoff

`SuperdiffusionCLT.Section2.CoarseGraining.SkewShift` proves
`e.commute.k0` for any two Chapter 2 coefficient objects `a`, `b` on the same
domain with `b = a + k_0` pointwise and `k_0` constant anti-symmetric. This
module supplies the canonical such `b`, and applies it to the manuscript's
centered representative of the infrared cutoff.

Building `b` is not free. `Homogenization.IsEllipticMatrix lam Lam A` is the
two-sided condition `lam |xi|^2 <= xi . A xi` **and**
`Lam^{-1} |xi|^2 <= xi . A^{-1} xi`. A constant anti-symmetric shift leaves the
first alone, because it leaves the symmetric part alone, but it does move the
inverse, so the upper constant must be enlarged. No new hypothesis is needed:
every constant matrix is bounded, and the Frobenius sum of `k_0` supplies the
enlargement.

The marginal instance is the manuscript's centered field
`a^U = nu Id + (k_L - (k_L)_U)` of the proof of `l.cutoff.approximation`, whose
average `(k_L)_U` is anti-symmetric because `k_L` is. So `s(U)` and `s_*(U)` of the
centered representative are those of `a_L`, and `k(U)` drops by `(k_L)_U`. This is the
identity behind the fact that the stream matrix is canonical
only modulo a constant anti-symmetric matrix, and the coarse-grained
diffusivities do not see the choice.

## Main results

* `isEllipticMatrix_add_const_skew`: ellipticity of `A + k_0`.
* `addConstSkewCoeffOn`: the Chapter 2 coefficient object of `a + k_0`.
* `coarseBlockMatrix_addConstSkewCoeffOn`: `e.commute.coarse.grained.k0` for the literal
  shifted field.
* `centeredCoefficientCutoff_toCoeffField`: the centered cutoff field is the
  cutoff field shifted by the constant anti-symmetric matrix `-(k_L)_U`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.CoarseGraining

open Homogenization
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## The shifted coefficient object

`IsEllipticMatrix lam Lam A` is two sided: besides `lam |ξ|² ≤ ξ·Aξ` it also
demands `Lam⁻¹ |ξ|² ≤ ξ·A⁻¹ξ`. A constant anti-symmetric shift leaves the first
condition untouched, because it leaves the symmetric part untouched, but it
does move the inverse; the upper constant must therefore be enlarged. Since
every constant matrix is bounded, no extra hypothesis is needed: the
Frobenius sum of `k₀` supplies the enlargement. -/

private theorem vecNormSq_matVecMul_le_frobenius (K : Mat d) (x : Vec d) :
    vecNormSq (matVecMul K x) ≤ (∑ i, ∑ j, K i j ^ 2) * vecNormSq x := by
  have hrow : ∀ i : Fin d, matVecMul K x i ^ 2 ≤ (∑ j, K i j ^ 2) * vecNormSq x := by
    intro i
    have hns : vecNormSq (fun j => K i j) = ∑ j, K i j ^ 2 := by
      simp [vecNormSq, vecDot, pow_two]
    have hdot : matVecMul K x i = vecDot (fun j => K i j) x := rfl
    rw [hdot, ← hns]
    exact sq_vecDot_le_vecNormSq_mul_vecNormSq (fun j => K i j) x
  calc
    vecNormSq (matVecMul K x) = ∑ i, matVecMul K x i ^ 2 := by
      simp [vecNormSq, vecDot, pow_two]
    _ ≤ ∑ i, (∑ j, K i j ^ 2) * vecNormSq x := Finset.sum_le_sum fun i _ => hrow i
    _ = (∑ i, ∑ j, K i j ^ 2) * vecNormSq x := by rw [Finset.sum_mul]

theorem frobenius_nonneg (K : Mat d) : (0 : ℝ) ≤ ∑ i, ∑ j, K i j ^ 2 :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- A coercivity bound together with an operator bound gives the two-sided
`IsEllipticMatrix` package. -/
private theorem isEllipticMatrix_of_lower_of_normSq_bound {lam B : ℝ} {A : Mat d}
    (hlam : 0 < lam) (hlamB : lam ^ 2 ≤ B)
    (hlower : ∀ ξ : Vec d, lam * vecNormSq ξ ≤ vecDot ξ (matVecMul A ξ))
    (hbd : ∀ ξ : Vec d, vecNormSq (matVecMul A ξ) ≤ B * vecNormSq ξ) :
    IsEllipticMatrix lam (B / lam) A := by
  have hB : 0 < B := lt_of_lt_of_le (pow_pos hlam 2) hlamB
  have hinj : Function.Injective (fun xi : Vec d => matVecMul A xi) := by
    intro xi zeta hxi
    have hw : matVecMul A (xi - zeta) = 0 := by
      rw [sub_eq_add_neg, matVecMul_add, matVecMul_neg, ← sub_eq_add_neg,
        sub_eq_zero]
      exact hxi
    have hle : lam * vecNormSq (xi - zeta) ≤ 0 := by
      have h := hlower (xi - zeta)
      rwa [hw, vecDot_zero_right] at h
    have hsq : vecNormSq (xi - zeta) = 0 := by
      have hge : (0 : ℝ) ≤ vecNormSq (xi - zeta) := vecNormSq_nonneg _
      have hle' : vecNormSq (xi - zeta) ≤ 0 :=
        nonpos_of_mul_nonpos_right hle hlam
      linarith only [hge, hle']
    exact sub_eq_zero.mp (vecNormSq_eq_zero hsq)
  have hdet : IsUnit A.det :=
    A.isUnit_iff_isUnit_det.mp (Matrix.mulVec_injective_iff_isUnit.mp hinj)
  have hlamLam : lam ≤ B / lam := by
    rw [le_div_iff₀ hlam, ← pow_two]
    exact hlamB
  refine ⟨hlam, hlamLam, hlower, fun xi => ?_⟩
  set eta : Vec d := matVecMul A⁻¹ xi with hetadef
  have hAeta : matVecMul A eta = xi := by
    rw [hetadef, matVecMul_mul, Matrix.mul_nonsing_inv A hdet]
    exact Matrix.one_mulVec xi
  have hpair : lam * vecNormSq eta ≤ vecDot xi eta := by
    have h := hlower eta
    rwa [hAeta, vecDot_comm eta xi] at h
  have hnorm : vecNormSq xi ≤ B * vecNormSq eta := by
    have h := hbd eta
    rwa [hAeta] at h
  rw [inv_div]
  calc lam / B * vecNormSq xi ≤ lam / B * (B * vecNormSq eta) :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = lam * vecNormSq eta := by field_simp
    _ ≤ vecDot xi eta := hpair

/-- Adding a constant anti-symmetric matrix keeps the lower ellipticity
constant and enlarges the upper one by the Frobenius sum of the shift. -/
theorem isEllipticMatrix_add_const_skew {lam Lam : ℝ} {A k0 : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (hk0 : matTranspose k0 = -k0) :
    IsEllipticMatrix lam
      (2 * (Lam ^ 2 + ∑ i, ∑ j, k0 i j ^ 2) / lam) (A + k0) := by
  have hlam : 0 < lam := hA.1
  have hlamLam : lam ≤ Lam := hA.2.1
  have hlower : ∀ ξ : Vec d, lam * vecNormSq ξ ≤ vecDot ξ (matVecMul A ξ) :=
    hA.2.2.1
  have hF : (0 : ℝ) ≤ ∑ i, ∑ j, k0 i j ^ 2 := frobenius_nonneg k0
  have hsplit : ∀ ξ : Vec d,
      matVecMul (A + k0) ξ = matVecMul A ξ + matVecMul k0 ξ :=
    fun ξ => add_matVecMul A k0 ξ
  refine isEllipticMatrix_of_lower_of_normSq_bound hlam ?_ ?_ ?_
  · have hsq : lam ^ 2 ≤ Lam ^ 2 := pow_le_pow_left₀ hlam.le hlamLam 2
    have hLamsq : (0 : ℝ) ≤ Lam ^ 2 := sq_nonneg Lam
    linarith only [hsq, hLamsq, hF]
  · intro ξ
    rw [hsplit ξ, vecDot_add_right, vecDot_matVecMul_self_of_skew hk0 ξ, add_zero]
    exact hlower ξ
  · intro ξ
    have hAbd : vecNormSq (matVecMul A ξ) ≤ Lam ^ 2 * vecNormSq ξ :=
      vecNormSq_matVecMul_le_of_isEllipticMatrix hA ξ
    have hkbd : vecNormSq (matVecMul k0 ξ) ≤ (∑ i, ∑ j, k0 i j ^ 2) * vecNormSq ξ :=
      vecNormSq_matVecMul_le_frobenius k0 ξ
    have htri := vecNormSq_add_le (matVecMul A ξ) (matVecMul k0 ξ)
    rw [hsplit ξ]
    linarith only [hAbd, hkbd, htri]

/-- The Chapter 2 coefficient object of `a + k₀` for a constant anti-symmetric
`k₀`: the same lower constant, the enlarged upper constant of
`isEllipticMatrix_add_const_skew`, and the same measurability data. -/
noncomputable def addConstSkewCoeffOn {U : Book.Ch02.Domain d}
    (a : Book.Ch02.CoeffOn U) {k0 : Mat d} (hk0 : matTranspose k0 = -k0) :
    Book.Ch02.CoeffOn U where
  toCoeffField := fun x => a.toCoeffField x + k0
  lam := a.lam
  Lam := 2 * (a.Lam ^ 2 + ∑ i, ∑ j, k0 i j ^ 2) / a.lam
  lam_pos := a.lam_pos
  lam_le_Lam := by
    have hlam : 0 < a.lam := a.lam_pos
    have hsq : a.lam ^ 2 ≤ a.Lam ^ 2 :=
      pow_le_pow_left₀ hlam.le a.lam_le_Lam 2
    have hLamsq : (0 : ℝ) ≤ a.Lam ^ 2 := sq_nonneg a.Lam
    have hF : (0 : ℝ) ≤ ∑ i, ∑ j, k0 i j ^ 2 := frobenius_nonneg k0
    rw [le_div_iff₀ hlam, ← pow_two]
    linarith only [hsq, hLamsq, hF]
  aeStronglyMeasurable := by
    classical
    intro i j
    have hEq : (fun x : Vec d =>
        restrictCoeffField (U : Set (Vec d))
          (fun y => a.toCoeffField y + k0) x i j) =
        fun x : Vec d =>
          restrictCoeffField (U : Set (Vec d)) a.toCoeffField x i j +
            Set.indicator (U : Set (Vec d)) (fun _ : Vec d => k0 i j) x := by
      funext x
      by_cases hx : x ∈ (U : Set (Vec d)) <;>
        simp [restrictCoeffField, Set.indicator, hx]
    rw [hEq]
    exact (a.aeStronglyMeasurable i j).add
      ((measurable_const.indicator U.measurableSet).aestronglyMeasurable)
  aeElliptic :=
    a.aeElliptic.mono fun _ hx => isEllipticMatrix_add_const_skew hx hk0

@[simp] theorem addConstSkewCoeffOn_toCoeffField {U : Book.Ch02.Domain d}
    (a : Book.Ch02.CoeffOn U) {k0 : Mat d} (hk0 : matTranspose k0 = -k0) :
    (addConstSkewCoeffOn a hk0).toCoeffField = fun x => a.toCoeffField x + k0 :=
  rfl

/-! ### `e.commute.k0` for the literal shifted field -/

section Literal

variable {U : Book.Ch02.Domain d} (a : Book.Ch02.CoeffOn U) {k0 : Mat d}

/-- `bfA(U; a + k₀) = G_{-k₀}^t bfA(U; a) G_{-k₀}` for the literal shifted
field. -/
theorem coarseBlockMatrix_addConstSkewCoeffOn (hk0 : matTranspose k0 = -k0) :
    Book.Ch02.coarseBlockMatrix U (addConstSkewCoeffOn a hk0) =
      Book.Ch02.blockMatMul
        (Book.Ch02.blockMatTranspose (Book.Ch02.blockG (-k0)))
        (Book.Ch02.blockMatMul (Book.Ch02.coarseBlockMatrix U a)
          (Book.Ch02.blockG (-k0))) :=
  coarseBlockMatrix_add_const_skew hk0 (fun _ => rfl)

end Literal

/-! ## The centered representative of the marginal infrared cutoff -/

section CenteredCutoff

/-- The volume average of the cutoff stream matrix over `U` is anti-symmetric,
so its negative is an admissible constant anti-symmetric shift. -/
theorem matTranspose_neg_volumeAverageMat_streamCutoff (omega : ShellSeq d)
    (L : ℕ) (U : Set (Vec d)) :
    matTranspose (-volumeAverageMat U (streamCutoff omega L)) =
      -(-volumeAverageMat U (streamCutoff omega L)) := by
  have h := matTranspose_volumeAverageMat U (fun y => streamCutoff omega L y)
    fun y i k => streamCutoff_skew_entry omega L y i k
  rw [matTranspose, Matrix.transpose_neg, ← matTranspose, h]

/-- The centered cutoff coefficient field is the cutoff coefficient field
shifted by the constant anti-symmetric matrix `-(k_L)_U`. -/
theorem centeredCoefficientCutoff_toCoeffField (nu : ℝ) (omega : ShellSeq d)
    (L : ℕ) (U : Set (Vec d)) :
    (centeredCoefficientCutoff nu omega L U).toCoeffField =
      fun x => (coefficientCutoff nu omega L).toCoeffField x +
        -volumeAverageMat U (streamCutoff omega L) := by
  funext x
  simp only [RegCoeffField.toCoeffField_apply,
    centeredCoefficientCutoff_eq_coefficientCutoff_sub, sub_eq_add_neg]

variable (U : Book.Ch02.Domain d) {nu C : ℝ} (hnu : 0 < nu) (omega : ShellSeq d)
  (L : ℕ)
  (hentry : ∀ x ∈ (U : Set (Vec d)), ∀ i j,
    |(coefficientCutoff nu omega L).toCoeffField x i j| ≤ C)

include hnu hentry

end CenteredCutoff

end

end SuperdiffusionCLT.Section2.CoarseGraining
