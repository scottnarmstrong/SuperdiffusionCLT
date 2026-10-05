/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.NewMixing.Splitting
public import Homogenization.Internal.Ch02.DoubledResponse.ScalarMaximizers

/-!
# Item 5, part 1: ellipticity of the shifted marginal field `a_L + h_0`

The passage from the `T_3`/`T_0` energy
bound to the doubled response `bfJ`, via `e.Jaas.matform` and
`e.mathcal.E.bfJ.scalar.max`. This file supplies the ellipticity
witness the `CoarseGraining` scalar-maximizer machinery
(`Homogenization.Internal.Ch02.DoubledResponse.ScalarMaximizers`) needs for
the field `a_L + h_0` (`newMixParam_aLplusH0`, `ParamStatement.lean`), built
from the pointwise ellipticity of `a_L`
(`newMixParam_isEllipticFieldOn_coefficientCutoff`, `Splitting.lean`) and the
skew-shift ellipticity lemma
(`isEllipticMatrix_add_const_skew`, `Section2/CoarseGraining/SkewShiftCutoff.lean`).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.NewMixing

open Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

/-- **Everywhere** (not just a.e.) ellipticity of the shifted field
`a_L + h_0` on any Chapter 2 domain `U`: the lower constant `nu` is
unchanged, and the upper constant is `a_L`'s own upper constant enlarged by
the Frobenius sum of `h_0`, via `isEllipticMatrix_add_const_skew`. -/
theorem newMixAsm_isEllipticFieldOn_aLplusH0 {d : ℕ} [NeZero d]
    {nu : ℝ} (hnu : 0 < nu) (omega : ShellSeq d) (L : ℕ)
    (h0 : Mat d) (hh0 : matTranspose h0 = -h0) (U : Domain d) :
    IsEllipticFieldOn nu
      (2 * ((((d : ℝ) * (d : ℝ) * (newMixParam_entryBound U nu omega L) ^ 2 + nu ^ 2) / nu) ^ 2
              + ∑ i, ∑ j, h0 i j ^ 2) / nu)
      (U : Set (Vec d))
      (fun x => (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField
        x + h0) := by
  have hEllA := newMixParam_isEllipticFieldOn_coefficientCutoff hnu omega L U
  refine ⟨?_, ?_⟩
  · classical
    refine Measurable.of_eval (fun i => Measurable.of_eval (fun j => ?_))
    have heq : (fun x : Vec d => if x ∈ (U : Set (Vec d)) then
          ((SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField x +
              h0) i j
        else 0) =
        (fun x : Vec d => (if x ∈ (U : Set (Vec d)) then
              (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField x
                i j
            else 0) +
          (if x ∈ (U : Set (Vec d)) then h0 i j else 0)) := by
      funext x
      by_cases hx : x ∈ (U : Set (Vec d)) <;> simp [hx, Matrix.add_apply]
    rw [heq]
    exact (Homogenization.RegCoeffField.entry_measurable
        (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L) i j).ite
        U.measurableSet measurable_const |>.add
      (measurable_const.ite U.measurableSet measurable_const)
  · intro x hx
    exact SuperdiffusionCLT.Section2.CoarseGraining.isEllipticMatrix_add_const_skew
      (hEllA.2 x hx) hh0

/-- The specialization of `newMixAsm_isEllipticFieldOn_aLplusH0` to the exact
domain and ellipticity constants `newMixParam_aLplusH0` itself carries
(`.lam`, `.Lam` built by `addConstSkewCoeffOn`/`coefficientCutoffCoeffOn`),
ready to feed the `CoarseGraining` scalar-maximizer machinery, which needs
`IsEllipticFieldOn a.lam a.Lam U a.toCoeffField` exactly. -/
theorem newMixAsm_isEllipticFieldOn_aLplusH0' {d : ℕ} [NeZero d]
    {nu : ℝ} (hnu : 0 < nu) (omega : ShellSeq d) (L m : ℕ)
    (h0 : Mat d) (hh0 : matTranspose h0 = -h0) :
    IsEllipticFieldOn (newMixParam_aLplusH0 nu hnu omega L m h0 hh0).lam
      (newMixParam_aLplusH0 nu hnu omega L m h0 hh0).Lam
      ((cubeDomain (originCube d (m : ℤ))) : Set (Vec d))
      (newMixParam_aLplusH0 nu hnu omega L m h0 hh0).toCoeffField :=
  newMixAsm_isEllipticFieldOn_aLplusH0 hnu omega L h0 hh0
    (cubeDomain (originCube d (m : ℤ)))

/-! ## The scalar-max passage (`e.Jaas.matform`, `e.mathcal.E.bfJ.scalar.max`) -/

open SuperdiffusionCLT.Section2.Carriers (blockVecNorm blockVecNorm_sq)

/-- Homogeneity of `responseJ` at the rescaled-unit-vector shape
`(shom_r^{-1/2} e, shom_r^{1/2} e)`: a ball-wide bound `≤ R` sharpens to the
exact quadratic bound `≤ ‖e‖² R` at every `e` in the ball, not just the unit
sphere. Pure algebra from `responseJ_smul`; no ellipticity needed. -/
theorem newMixAsm_responseJ_le_vecNormSq_mul {d : ℕ} [NeZero d] {U : Domain d} {a : CoeffOn U}
    {shomr R : ℝ}
    (hJ : ∀ e : Vec d, vecNormSq e ≤ 1 →
      responseJ U a (shomr ^ (-(1 : ℝ) / 2) • e) (shomr ^ ((1 : ℝ) / 2) • e) ≤ R) :
    ∀ e : Vec d, vecNormSq e ≤ 1 →
      responseJ U a (shomr ^ (-(1 : ℝ) / 2) • e) (shomr ^ ((1 : ℝ) / 2) • e) ≤
        vecNormSq e * R := by
  intro e he
  rcases eq_or_ne e 0 with rfl | hne
  · have hz : responseJ U a (0 : Vec d) (0 : Vec d) = 0 := by
      have h0 := responseJ_smul (U := U) (a := a) (0 : ℝ) (0 : Vec d) (0 : Vec d)
      simpa using h0
    have hz0 : vecNormSq (0 : Vec d) = 0 := by simp [vecNormSq, vecDot]
    simp only [smul_zero, hz]
    rw [hz0]
    simp
  · have hvpos : 0 < vecNormSq e := by
      have hne0 : vecNormSq e ≠ 0 := fun h => hne (vecNormSq_eq_zero_iff.mp h)
      exact lt_of_le_of_ne (vecNormSq_nonneg e) (Ne.symm hne0)
    obtain ⟨t, ht0, ht2⟩ : ∃ t : ℝ, 0 < t ∧ t ^ 2 = vecNormSq e :=
      ⟨Real.sqrt (vecNormSq e), Real.sqrt_pos.mpr hvpos, Real.sq_sqrt (vecNormSq_nonneg e)⟩
    have htne : t ≠ 0 := ht0.ne'
    obtain ⟨e', he'e⟩ : ∃ e' : Vec d, t • e' = e :=
      ⟨t⁻¹ • e, by rw [smul_smul, mul_inv_cancel₀ htne, one_smul]⟩
    have hnorme' : vecNormSq e' = 1 := by
      have h1 : t ^ 2 * vecNormSq e' = vecNormSq e := by rw [← vecNormSq_smul, he'e]
      rw [ht2] at h1
      have h2 : vecNormSq e * vecNormSq e' = vecNormSq e * 1 := by rw [h1, mul_one]
      exact mul_left_cancel₀ hvpos.ne' h2
    have hJe' := hJ e' (le_of_eq hnorme')
    have hcomm1 : shomr ^ (-(1 : ℝ) / 2) • e = t • (shomr ^ (-(1 : ℝ) / 2) • e') := by
      rw [← he'e, smul_smul, smul_smul, mul_comm (shomr ^ (-(1 : ℝ) / 2)) t]
    have hcomm2 : shomr ^ ((1 : ℝ) / 2) • e = t • (shomr ^ ((1 : ℝ) / 2) • e') := by
      rw [← he'e, smul_smul, smul_smul, mul_comm (shomr ^ ((1 : ℝ) / 2)) t]
    rw [hcomm1, hcomm2, responseJ_smul t, ht2]
    exact mul_le_mul_of_nonneg_left hJe' (vecNormSq_nonneg e)

/-- **The scalar-max passage** (`e.Jaas.matform` + `e.mathcal.E.bfJ.scalar.max`):
if the scalar response `J` (at the field
`a_L + h_0`) and its adjoint `J^*` (at the transposed field) are both bounded
by the SAME `R` at every rescaled `e` in the unit ball, then the doubled
response `bfJ` is bounded by `R` at every rescaled unit block vector
`eta`. -/
theorem newMixAsm_doubledResponseJ_le_of_scalar_bounds {d : ℕ} [NeZero d]
    {nu shomr : ℝ} (hnu : 0 < nu)
    (omega : ShellSeq d) (L m : ℕ)
    (h0 : Mat d) (hh0 : matTranspose h0 = -h0) {R : ℝ}
    (hJ : ∀ e : Vec d, vecNormSq e ≤ 1 →
      responseJ (cubeDomain (originCube d (m : ℤ)))
          (newMixParam_aLplusH0 nu hnu omega L m h0 hh0)
          (shomr ^ (-(1 : ℝ) / 2) • e) (shomr ^ ((1 : ℝ) / 2) • e) ≤ R)
    (hJstar : ∀ e : Vec d, vecNormSq e ≤ 1 →
      responseJ (cubeDomain (originCube d (m : ℤ)))
          (newMixParam_aLplusH0 nu hnu omega L m h0 hh0).transpose
          (shomr ^ (-(1 : ℝ) / 2) • e) (shomr ^ ((1 : ℝ) / 2) • e) ≤ R)
    (eta : BlockVec d) (heta : blockVecNorm eta = 1) :
    doubledResponseJ (cubeDomain (originCube d (m : ℤ)))
        (newMixParam_aLplusH0 nu hnu omega L m h0 hh0)
        (shomr ^ (-(1 : ℝ) / 2) • eta.1, shomr ^ ((1 : ℝ) / 2) • eta.2)
        (shomr ^ ((1 : ℝ) / 2) • eta.1, shomr ^ (-(1 : ℝ) / 2) • eta.2) ≤ R := by
  have hEll : IsEllipticFieldOn (newMixParam_aLplusH0 nu hnu omega L m h0 hh0).lam
      (newMixParam_aLplusH0 nu hnu omega L m h0 hh0).Lam
      ((cubeDomain (originCube d (m : ℤ))) : Set (Vec d))
      (newMixParam_aLplusH0 nu hnu omega L m h0 hh0).toCoeffField :=
    newMixAsm_isEllipticFieldOn_aLplusH0' hnu omega L m h0 hh0
  have hkey := Homogenization.Internal.Ch02.BookCh02.doubled_response_by_scalar_of_isEllipticFieldOn
    (cubeDomain (originCube d (m : ℤ))) (newMixParam_aLplusH0 nu hnu omega L m h0 hh0) hEll
    (shomr ^ (-(1 : ℝ) / 2) • eta.1) (shomr ^ (-(1 : ℝ) / 2) • eta.2)
    (shomr ^ ((1 : ℝ) / 2) • eta.2) (shomr ^ ((1 : ℝ) / 2) • eta.1)
  have hsqrt2ne : (Real.sqrt 2 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hsqrt2sq : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  -- `e1`, `e2` are introduced opaquely (via `obtain`, not `set`) so that later
  -- rewrites by `he1eq`/`he2eq` cannot loop back through their own definitions.
  obtain ⟨e1, he1eq⟩ : ∃ e1 : Vec d, eta.1 - eta.2 = Real.sqrt 2 • e1 :=
    ⟨(Real.sqrt 2)⁻¹ • (eta.1 - eta.2), by rw [smul_smul, mul_inv_cancel₀ hsqrt2ne, one_smul]⟩
  obtain ⟨e2, he2eq⟩ : ∃ e2 : Vec d, eta.1 + eta.2 = Real.sqrt 2 • e2 :=
    ⟨(Real.sqrt 2)⁻¹ • (eta.1 + eta.2), by rw [smul_smul, mul_inv_cancel₀ hsqrt2ne, one_smul]⟩
  -- the exact parallelogram identity
  have hpara : vecNormSq (eta.1 + eta.2) + vecNormSq (eta.1 - eta.2) =
      2 * vecNormSq eta.1 + 2 * vecNormSq eta.2 := by
    have hsum : vecNormSq (eta.1 + eta.2) = ∑ i, (eta.1 i + eta.2 i) ^ 2 := by
      simp [vecNormSq, vecDot, pow_two]
    have hdiff : vecNormSq (eta.1 - eta.2) = ∑ i, (eta.1 i - eta.2 i) ^ 2 := by
      simp [vecNormSq, vecDot, pow_two]
    have hx : vecNormSq eta.1 = ∑ i, eta.1 i ^ 2 := by simp [vecNormSq, vecDot, pow_two]
    have hy : vecNormSq eta.2 = ∑ i, eta.2 i ^ 2 := by simp [vecNormSq, vecDot, pow_two]
    rw [hsum, hdiff, hx, hy, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hetanorm : vecNormSq eta.1 + vecNormSq eta.2 = 1 := by
    have hsq : blockVecNorm eta ^ 2 = blockVecDot eta eta := blockVecNorm_sq eta
    rw [heta, one_pow] at hsq
    have heq : blockVecDot eta eta = vecNormSq eta.1 + vecNormSq eta.2 := rfl
    rw [heq] at hsq
    exact hsq.symm
  have hsum12 : vecNormSq e1 + vecNormSq e2 = 1 := by
    have h1 : vecNormSq (eta.1 - eta.2) = 2 * vecNormSq e1 := by
      rw [he1eq, vecNormSq_smul, hsqrt2sq]
    have h2 : vecNormSq (eta.1 + eta.2) = 2 * vecNormSq e2 := by
      rw [he2eq, vecNormSq_smul, hsqrt2sq]
    nlinarith only [hpara, hetanorm, h1, h2]
  have he1le : vecNormSq e1 ≤ 1 := by nlinarith only [hsum12, vecNormSq_nonneg e2]
  have he2le : vecNormSq e2 ≤ 1 := by nlinarith only [hsum12, vecNormSq_nonneg e1]
  have hb1 := newMixAsm_responseJ_le_vecNormSq_mul
    (U := cubeDomain (originCube d (m : ℤ)))
    (a := newMixParam_aLplusH0 nu hnu omega L m h0 hh0) hJ e1 he1le
  have hb2 := newMixAsm_responseJ_le_vecNormSq_mul
    (U := cubeDomain (originCube d (m : ℤ)))
    (a := (newMixParam_aLplusH0 nu hnu omega L m h0 hh0).transpose) hJstar e2 he2le
  have hcomm1 : shomr ^ (-(1 : ℝ) / 2) • eta.1 - shomr ^ (-(1 : ℝ) / 2) • eta.2 =
      Real.sqrt 2 • (shomr ^ (-(1 : ℝ) / 2) • e1) := by
    rw [← smul_sub, he1eq, smul_smul, smul_smul, mul_comm (shomr ^ (-(1 : ℝ) / 2)) (Real.sqrt 2)]
  have hcomm2 : shomr ^ ((1 : ℝ) / 2) • eta.1 - shomr ^ ((1 : ℝ) / 2) • eta.2 =
      Real.sqrt 2 • (shomr ^ ((1 : ℝ) / 2) • e1) := by
    rw [← smul_sub, he1eq, smul_smul, smul_smul, mul_comm (shomr ^ ((1 : ℝ) / 2)) (Real.sqrt 2)]
  have hcomm3 : shomr ^ (-(1 : ℝ) / 2) • eta.2 + shomr ^ (-(1 : ℝ) / 2) • eta.1 =
      Real.sqrt 2 • (shomr ^ (-(1 : ℝ) / 2) • e2) := by
    rw [← smul_add, add_comm eta.2 eta.1, he2eq, smul_smul, smul_smul,
      mul_comm (shomr ^ (-(1 : ℝ) / 2)) (Real.sqrt 2)]
  have hcomm4 : shomr ^ ((1 : ℝ) / 2) • eta.1 + shomr ^ ((1 : ℝ) / 2) • eta.2 =
      Real.sqrt 2 • (shomr ^ ((1 : ℝ) / 2) • e2) := by
    rw [← smul_add, he2eq, smul_smul, smul_smul, mul_comm (shomr ^ ((1 : ℝ) / 2)) (Real.sqrt 2)]
  rw [hcomm1, hcomm2, hcomm3, hcomm4, responseJ_smul (Real.sqrt 2), responseJ_smul (Real.sqrt 2),
    hsqrt2sq] at hkey
  have hsumR : vecNormSq e1 * R + vecNormSq e2 * R = R := by
    rw [← add_mul, hsum12, one_mul]
  linarith only [hkey, hb1, hb2, hsumR]

end
end SuperdiffusionCLT.Section4.NewMixing
