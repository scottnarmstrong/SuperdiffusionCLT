/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.CoarseGraining.Correspondence
public import SuperdiffusionCLT.Section2.Cutoff.CoefficientCutoffAPI

/-!
# The marginal cutoff field as a Chapter 2 coefficient object

The cutoff `a_L = nu Id + k_L` of the paper is a `RegCoeffField d`, and its symmetric part is
the constant `nu Id` (`symmPart_coefficientCutoff`). The coarse-grained
matrices of Section 2.1 are already defined for it on the raw carrier, but the
Chapter 2 theorems collected in
`SuperdiffusionCLT.Section2.CoarseGraining.Correspondence` are stated for
a `CoeffOn U`, which bundles quantitative ellipticity constants.

Those constants are not part of the definition of `a_L`; supplying them is a
separate step, carried out here from an entry bound for `a_L` on the domain,
which is what the `L^infinity` shell envelopes of Section 2 provide. The lower
constant is the molecular diffusivity `nu`, available for free from the
anti-symmetry of the shells; the upper constant is the entry bound converted to
the inverse-side bound of `IsEllipticMatrix`.

## Main results

* `isEllipticMatrix_of_symmPart_eq_smul_one`: a matrix whose symmetric part is
  `nu Id` and whose entries are bounded by `C` is elliptic with constants
  `nu` and `(d^2 C^2 + nu^2)/nu`.
* `abs_coefficientCutoff_entry_le`: an entry bound for `k_L` gives one for
  `a_L`.
* `coefficientCutoffCoeffOn`: the Chapter 2 coefficient object of `a_L`.
* `sigmaStarCoarse_coefficientCutoff_posDef`,
  `sigmaStarCoarse_le_sigmaCoarse_coefficientCutoff`,
  `bCoarse_coefficientCutoff_posDef`: the Section 2.1-2.2 vocabulary of `a_L`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.CoarseGraining

open Homogenization
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## Ellipticity from an entry bound -/

private theorem matVecMul_one (x : Vec d) : matVecMul (1 : Mat d) x = x := by
  funext k
  simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]

private theorem vecNormSq_matVecMul_le_entrySumSq (A : Mat d) (x : Vec d) :
    vecNormSq (matVecMul A x) ≤ (∑ i, ∑ j, A i j ^ 2) * vecNormSq x := by
  have hrow : ∀ i : Fin d, matVecMul A x i ^ 2 ≤ (∑ j, A i j ^ 2) * vecNormSq x := by
    intro i
    have hcs := sq_vecDot_le_vecNormSq_mul_vecNormSq (fun j => A i j) x
    have hns : vecNormSq (fun j => A i j) = ∑ j, A i j ^ 2 := by
      simp [vecNormSq, vecDot, pow_two]
    have hdot : matVecMul A x i = vecDot (fun j => A i j) x := rfl
    rw [hdot, ← hns]
    exact hcs
  calc
    vecNormSq (matVecMul A x) = ∑ i, matVecMul A x i ^ 2 := by
      simp [vecNormSq, vecDot, pow_two]
    _ ≤ ∑ i, (∑ j, A i j ^ 2) * vecNormSq x := Finset.sum_le_sum fun i _ => hrow i
    _ = (∑ i, ∑ j, A i j ^ 2) * vecNormSq x := by rw [Finset.sum_mul]

private theorem entrySumSq_le (A : Mat d) {C : ℝ} (hentry : ∀ i j, |A i j| ≤ C) :
    (∑ i, ∑ j, A i j ^ 2) ≤ (d : ℝ) * (d : ℝ) * C ^ 2 := by
  calc
    (∑ i, ∑ j, A i j ^ 2) ≤ ∑ _i : Fin d, ∑ _j : Fin d, C ^ 2 := by
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
      calc A i j ^ 2 = |A i j| ^ 2 := (sq_abs (A i j)).symm
        _ ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hentry i j) 2
    _ = (d : ℝ) * (d : ℝ) * C ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

theorem isEllipticMatrix_of_symmPart_eq_smul_one {A : Mat d} {nu C : ℝ}
    (hnu : 0 < nu) (hsymm : symmPart A = nu • (1 : Mat d))
    (hentry : ∀ i j, |A i j| ≤ C) :
    IsEllipticMatrix nu (((d : ℝ) * (d : ℝ) * C ^ 2 + nu ^ 2) / nu) A := by
  set B : ℝ := (d : ℝ) * (d : ℝ) * C ^ 2 + nu ^ 2 with hBdef
  have hfrob : (0 : ℝ) ≤ (d : ℝ) * (d : ℝ) * C ^ 2 := by positivity
  have hB : 0 < B := by
    rw [hBdef]
    exact add_pos_of_nonneg_of_pos hfrob (pow_pos hnu 2)
  have hco : ∀ xi : Vec d, vecDot xi (matVecMul A xi) = nu * vecNormSq xi := by
    intro xi
    rw [← vecDot_matVecMul_symmPart, hsymm, smul_matVecMul, matVecMul_one,
      vecDot_smul_right]
    rfl
  have hbd : ∀ eta : Vec d, vecNormSq (matVecMul A eta) ≤ B * vecNormSq eta := by
    intro eta
    refine (vecNormSq_matVecMul_le_entrySumSq A eta).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (vecNormSq_nonneg eta)
    exact (entrySumSq_le A hentry).trans (by rw [hBdef]; linarith only [sq_nonneg nu])
  have hinj : Function.Injective (fun xi : Vec d => matVecMul A xi) := by
    intro xi zeta hxi
    have hw : matVecMul A (xi - zeta) = 0 := by
      rw [sub_eq_add_neg, matVecMul_add, matVecMul_neg, ← sub_eq_add_neg, sub_eq_zero]
      exact hxi
    have hzero : nu * vecNormSq (xi - zeta) = 0 := by
      rw [← hco (xi - zeta), hw, vecDot_zero_right]
    have hsq : vecNormSq (xi - zeta) = 0 := by
      rcases mul_eq_zero.mp hzero with h | h
      · exact absurd h hnu.ne'
      · exact h
    exact sub_eq_zero.mp (vecNormSq_eq_zero hsq)
  have hdet : IsUnit A.det :=
    A.isUnit_iff_isUnit_det.mp (Matrix.mulVec_injective_iff_isUnit.mp hinj)
  refine ⟨hnu, ?_, fun xi => (hco xi).ge, fun xi => ?_⟩
  · rw [le_div_iff₀ hnu, ← pow_two, hBdef]
    linarith only [hfrob]
  · set eta : Vec d := matVecMul A⁻¹ xi with hetadef
    have hAeta : matVecMul A eta = xi := by
      rw [hetadef, matVecMul_mul, Matrix.mul_nonsing_inv A hdet]
      exact Matrix.one_mulVec xi
    have hpair : vecDot xi (matVecMul A⁻¹ xi) = nu * vecNormSq eta := by
      rw [← hetadef, ← hAeta, vecDot_comm, hco eta]
    have hnorm : vecNormSq xi ≤ B * vecNormSq eta := by
      have h := hbd eta
      rwa [hAeta] at h
    rw [hpair, inv_div]
    calc nu / B * vecNormSq xi ≤ nu / B * (B * vecNormSq eta) := by
          exact mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ = nu * vecNormSq eta := by field_simp

theorem abs_coefficientCutoff_entry_le {nu C : ℝ} (hnu : 0 ≤ nu)
    (omega : ShellSeq d) (L : ℕ) (x : Vec d)
    (h : ∀ i j, |streamCutoff omega L x i j| ≤ C) (i j : Fin d) :
    |(coefficientCutoff nu omega L).toCoeffField x i j| ≤ nu + C := by
  have hone : |nu * (1 : Mat d) i j| ≤ nu := by
    by_cases hij : i = j
    · subst hij
      simp [abs_of_nonneg hnu]
    · simpa [Matrix.one_apply, hij] using hnu
  calc |(coefficientCutoff nu omega L).toCoeffField x i j|
      = |nu * (1 : Mat d) i j + streamCutoff omega L x i j| := by
        simp only [coefficientCutoff_toCoeffField_apply, Matrix.add_apply,
          Matrix.smul_apply, smul_eq_mul]
    _ ≤ |nu * (1 : Mat d) i j| + |streamCutoff omega L x i j| := abs_add_le _ _
    _ ≤ nu + C := add_le_add hone (h i j)

/-- The Chapter 2 coefficient object of the marginal cutoff field
`a_L = nu Id + k_L` on a domain `U`, built from an entry bound for `a_L` on
`U`. The lower ellipticity constant is the molecular diffusivity `nu`; the
upper one is the entry bound converted to the inverse-side bound. -/
noncomputable def coefficientCutoffCoeffOn (U : Book.Ch02.Domain d) {nu C : ℝ}
    (hnu : 0 < nu) (omega : ShellSeq d) (L : ℕ)
    (hentry : ∀ x ∈ (U : Set (Vec d)), ∀ i j,
      |(coefficientCutoff nu omega L).toCoeffField x i j| ≤ C) :
    Book.Ch02.CoeffOn U where
  toCoeffField := (coefficientCutoff nu omega L).toCoeffField
  lam := nu
  Lam := ((d : ℝ) * (d : ℝ) * C ^ 2 + nu ^ 2) / nu
  lam_pos := hnu
  lam_le_Lam := by
    rw [le_div_iff₀ hnu, ← pow_two]
    linarith only [show (0 : ℝ) ≤ (d : ℝ) * (d : ℝ) * C ^ 2 by positivity]
  aeStronglyMeasurable := by
    classical
    intro i j
    have hEq : (fun x : Vec d =>
        restrictCoeffField (U : Set (Vec d))
          (coefficientCutoff nu omega L).toCoeffField x i j) =
        fun x : Vec d => if x ∈ (U : Set (Vec d))
          then (coefficientCutoff nu omega L).toCoeffField x i j else 0 := by
      funext x
      by_cases hx : x ∈ (U : Set (Vec d)) <;> simp [restrictCoeffField, hx]
    rw [hEq]
    exact (((coefficientCutoff nu omega L).entry_measurable i j).ite
      U.measurableSet measurable_const).aestronglyMeasurable
  aeElliptic := by
    filter_upwards [MeasureTheory.ae_restrict_mem U.measurableSet] with x hx
    exact isEllipticMatrix_of_symmPart_eq_smul_one hnu
      (symmPart_coefficientCutoff nu omega L x) (hentry x hx)

@[simp] theorem coefficientCutoffCoeffOn_toCoeffField (U : Book.Ch02.Domain d)
    {nu C : ℝ} (hnu : 0 < nu) (omega : ShellSeq d) (L : ℕ)
    (hentry : ∀ x ∈ (U : Set (Vec d)), ∀ i j,
      |(coefficientCutoff nu omega L).toCoeffField x i j| ≤ C) :
    (coefficientCutoffCoeffOn U hnu omega L hentry).toCoeffField =
      (coefficientCutoff nu omega L).toCoeffField :=
  rfl

/-! ### The Section 2.1-2.2 vocabulary of the cutoff field

Every theorem of this module applies to `a_L` through
`coefficientCutoffCoeffOn`. The following are the instances a Section 3
consumer quotes directly. -/

/-- `s_*(U; a_L)` is positive definite. -/
theorem sigmaStarCoarse_coefficientCutoff_posDef (U : Book.Ch02.Domain d)
    {nu C : ℝ} (hnu : 0 < nu) (omega : ShellSeq d) (L : ℕ)
    (hentry : ∀ x ∈ (U : Set (Vec d)), ∀ i j,
      |(coefficientCutoff nu omega L).toCoeffField x i j| ≤ C) :
    (Homogenization.sigmaStarCoarse (U : Set (Vec d))
      (coefficientCutoff nu omega L).toCoeffField).PosDef :=
  sigmaStarCoarse_posDef U (coefficientCutoffCoeffOn U hnu omega L hentry)

/-- `s_*(U; a_L) <= s(U; a_L)`. -/
theorem sigmaStarCoarse_le_sigmaCoarse_coefficientCutoff (U : Book.Ch02.Domain d)
    {nu C : ℝ} (hnu : 0 < nu) (omega : ShellSeq d) (L : ℕ)
    (hentry : ∀ x ∈ (U : Set (Vec d)), ∀ i j,
      |(coefficientCutoff nu omega L).toCoeffField x i j| ≤ C) :
    MatLoewnerLE
      (Homogenization.sigmaStarCoarse (U : Set (Vec d))
        (coefficientCutoff nu omega L).toCoeffField)
      (Homogenization.sigmaCoarse (U : Set (Vec d))
        (coefficientCutoff nu omega L).toCoeffField) :=
  sigmaStarCoarse_le_sigmaCoarse U (coefficientCutoffCoeffOn U hnu omega L hentry)

/-- `b(U; a_L)` is positive definite, so `b^{-1}(U; a_L)` is well defined. -/
theorem bCoarse_coefficientCutoff_posDef (U : Book.Ch02.Domain d)
    {nu C : ℝ} (hnu : 0 < nu) (omega : ShellSeq d) (L : ℕ)
    (hentry : ∀ x ∈ (U : Set (Vec d)), ∀ i j,
      |(coefficientCutoff nu omega L).toCoeffField x i j| ≤ C) :
    (Homogenization.bCoarse
      (Homogenization.sigmaCoarse (U : Set (Vec d))
        (coefficientCutoff nu omega L).toCoeffField)
      (Homogenization.sigmaStarCoarse (U : Set (Vec d))
        (coefficientCutoff nu omega L).toCoeffField)
      (Homogenization.kappaCoarse (U : Set (Vec d))
        (coefficientCutoff nu omega L).toCoeffField)).PosDef :=
  bCoarse_posDef U (coefficientCutoffCoeffOn U hnu omega L hentry)

end

end SuperdiffusionCLT.Section2.CoarseGraining
