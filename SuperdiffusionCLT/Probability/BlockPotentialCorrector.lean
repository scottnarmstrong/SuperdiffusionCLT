/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Ambient.CoefficientFieldHilbert
public import Homogenization.Book.Ch02.Theorems.MatrixOperatorNorm
public import SuperdiffusionCLT.Assumptions.ShellLaw.BlockStationarity
public import SuperdiffusionCLT.Assumptions.ShellLaw.J3OriginConsequences
public import SuperdiffusionCLT.Probability.StationaryProjection

/-!
# The stationary response of a finite shell block

The paper evaluates the field `grad Delta⁻¹ (div F)` at the spatial origin
for the forcing `F = (sum of the shells in a finite block) e`. This file builds
the Hilbert-space realization of that response over the law of the block.

The sample space is the regular-coefficient carrier `RegCoeffField d` of the CoarseGraining
library, acted on by its `translateReg`; the block law is `blockRegLaw`, stationary by
`blockRegLaw_stationary`. The forcing is the matrix-vector product at the origin,
square integrable by the J3 tail, and the response is its orthogonal
projection onto the stationary potential subspace.

## Sign convention

`grad Delta⁻¹ div` is realized by the *positive* orthogonal projection onto the
stationary potential subspace: if `w` solves `Delta w = div F` then
`grad Delta⁻¹ (div F) = grad w`, and `F - grad w` is divergence free, so `grad w`
is the potential part of `F`. A development that instead normalizes its corrector
by `-Delta w = div F` obtains the negative of this element; the two differ by a
sign and have the same norm.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Cutoff

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open scoped BigOperators

noncomputable section

variable {d : ℕ} {P : ProbabilityMeasure (ℕ → ShellField d)}

/-! ## The real translation action on the regular-coefficient carrier -/

/-- The spatial translation of the CoarseGraining library is the additive action
`(z +ᵥ a)(x) = a (x + z)` on regular coefficient fields. -/
noncomputable instance regCoeffFieldAddAction :
    AddAction (Vec d) (RegCoeffField d) where
  vadd := translateReg
  zero_vadd a := by
    refine RegCoeffField.ext fun x ↦ ?_
    change a (x + 0) = a x
    rw [add_zero]
  add_vadd z w a := by
    refine RegCoeffField.ext fun x ↦ ?_
    change a (x + (z + w)) = a (x + z + w)
    rw [add_assoc]

/-- Fixed-shift measurability of the translation action is exactly the proved
measurability of `translateReg` in the CoarseGraining library. -/
instance regCoeffFieldMeasurableConstVAdd :
    MeasurableConstVAdd (Vec d) (RegCoeffField d) where
  measurable_const_vadd z := by
    change Measurable (translateReg (d := d) z)
    exact measurable_translateReg z

/-! ## The origin forcing -/

private def matVecMulLinear (e : Vec d) : Mat d →ₗ[ℝ] Vec d where
  toFun A := matVecMul A e
  map_add' A B := by
    funext i
    change ∑ j, (A i j + B i j) * e j =
      (∑ j, A i j * e j) + ∑ j, B i j * e j
    simp_rw [add_mul]
    exact Finset.sum_add_distrib
  map_smul' c A := by
    funext i
    change ∑ j, (c * A i j) * e j = c * ∑ j, A i j * e j
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [mul_assoc]

/-- The forcing `a e` of the paper evaluated at the spatial origin, promoted to
the Euclidean Hilbert carrier of the CoarseGraining library. -/
def originForcing (e : Vec d) (a : RegCoeffField d) : HilbertVec d :=
  HilbertVec.ofVec (matVecMul (a 0) e)

theorem measurable_originForcing (e : Vec d) :
    Measurable (originForcing (d := d) e) := by
  have hEval : Measurable (fun a : RegCoeffField d ↦ a 0) :=
    measurable_matrix_of_entries fun i j ↦ measurable_apply_entry 0 i j
  change Measurable
    (fun a : RegCoeffField d ↦ HilbertVec.ofVec (matVecMul (a 0) e))
  exact (HilbertVec.ofVecL d).continuous.measurable.comp
    ((matVecMulLinear e).continuous_of_finiteDimensional.measurable.comp hEval)

theorem norm_sq_originForcing (e : Vec d) (a : RegCoeffField d) :
    ‖originForcing e a‖ ^ 2 =
      vecDot (matVecMul (a 0) e) (matVecMul (a 0) e) :=
  HilbertVec.norm_sq_ofVec _

/-- For a unit direction the origin forcing is bounded by the Euclidean operator
norm of the coefficient matrix at the origin. -/
theorem norm_originForcing_le_matrixOperatorNorm (e : Vec d)
    (a : RegCoeffField d) (he : Book.Ch02.vecNorm e = 1) :
    ‖originForcing e a‖ ≤ Book.Ch02.matrixOperatorNorm (a 0) := by
  have hnorm : ‖originForcing e a‖ = Book.Ch02.vecNorm (matVecMul (a 0) e) := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (Book.Ch02.vecNorm_nonneg _),
      norm_sq_originForcing, Book.Ch02.vecNorm_sq_eq_vecNormSq]
    rfl
  rw [hnorm]
  calc
    Book.Ch02.vecNorm (matVecMul (a 0) e) ≤
        Book.Ch02.matrixOperatorNorm (a 0) * Book.Ch02.vecNorm e :=
      Book.Ch02.vecNorm_matVecMul_le_matrixOperatorNorm_mul_vecNorm _ _
    _ = Book.Ch02.matrixOperatorNorm (a 0) := by rw [he, mul_one]

/-! ## Square integrability of the block forcing -/

private theorem matrixOperatorNorm_add_le (A B : Mat d) :
    Book.Ch02.matrixOperatorNorm (A + B) ≤
      Book.Ch02.matrixOperatorNorm A + Book.Ch02.matrixOperatorNorm B := by
  simpa only [add_sub_cancel_left] using
    Book.Ch02.matrixOperatorNorm_le_matrixOperatorNorm_add_matrixOperatorNorm_sub
      (A + B) A

private theorem matrixOperatorNorm_finset_sum_le {ι : Type*} (s : Finset ι)
    (A : ι → Mat d) :
    Book.Ch02.matrixOperatorNorm (∑ i ∈ s, A i) ≤
      ∑ i ∈ s, Book.Ch02.matrixOperatorNorm (A i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (matrixOperatorNorm_add_le _ _).trans (add_le_add le_rfl ih)

/-- The J3 Gaussian tail makes the origin forcing of a finite shell block square
integrable for the block law. -/
theorem memLp_originForcing_blockRegLaw (hJ3 : ShellLawJ3 d P) (n m : ℕ)
    (e : Vec d) (he : Book.Ch02.vecNorm e = 1) :
    MemLp (originForcing (d := d) e) 2 (blockRegLaw P n m).toMeasure := by
  have hXmem : MemLp
      (fun omega : ShellSeq d ↦
        ∑ k ∈ Finset.Ioc n m,
          Book.Ch02.matrixOperatorNorm ((omega k) 0)) 2 P.toMeasure :=
    memLp_finsetSum (μ := P.toMeasure) (p := 2) (Finset.Ioc n m)
      (fun k _ ↦ hJ3.memLp_two_matrixOperatorNorm_zero_coordinate k)
  have hpull : MemLp
      (fun omega : ShellSeq d ↦
        originForcing e (finiteShellIncrement omega n m)) 2 P.toMeasure := by
    refine hXmem.mono' ?_ (Filter.Eventually.of_forall fun omega ↦ ?_)
    · exact ((measurable_originForcing e).comp
        (measurable_finiteShellIncrement n m)).aestronglyMeasurable
    · calc
        ‖originForcing e (finiteShellIncrement omega n m)‖ ≤
            Book.Ch02.matrixOperatorNorm (finiteShellIncrement omega n m 0) :=
          norm_originForcing_le_matrixOperatorNorm e _ he
        _ = Book.Ch02.matrixOperatorNorm
              (∑ k ∈ Finset.Ioc n m, shellReg omega k 0) := by
          rw [finiteShellIncrement_apply]
        _ ≤ ∑ k ∈ Finset.Ioc n m,
              Book.Ch02.matrixOperatorNorm (shellReg omega k 0) :=
          matrixOperatorNorm_finset_sum_le _ _
        _ = ∑ k ∈ Finset.Ioc n m,
              Book.Ch02.matrixOperatorNorm ((omega k) 0) := rfl
  rw [blockRegLaw_toMeasure]
  exact (memLp_map_measure_iff (measurable_originForcing e).aestronglyMeasurable
    (measurable_finiteShellIncrement (d := d) n m).aemeasurable).mpr hpull

/-- The canonical `L²` element represented by the block origin forcing. -/
def blockForcingL2 (P : ProbabilityMeasure (ℕ → ShellField d)) (n m : ℕ)
    (e : Vec d)
    (hmem : MemLp (originForcing (d := d) e) 2 (blockRegLaw P n m).toMeasure) :
    SuperdiffusionCLT.Probability.Stationary.VectorL2 d
      (blockRegLaw P n m).toMeasure :=
  hmem.toLp (originForcing e)

theorem coeFn_blockForcingL2 (P : ProbabilityMeasure (ℕ → ShellField d))
    (n m : ℕ) (e : Vec d)
    (hmem : MemLp (originForcing (d := d) e) 2 (blockRegLaw P n m).toMeasure) :
    (blockForcingL2 P n m e hmem : RegCoeffField d → HilbertVec d) =ᵐ[
      (blockRegLaw P n m).toMeasure] originForcing e :=
  hmem.coeFn_toLp

/-! ## The stationary potential response -/

/-- Translation invariance of the block law, packaged for the stationary
projection. -/
theorem blockRegLaw_vaddInvariant (P : ProbabilityMeasure (ℕ → ShellField d))
    (n m : ℕ)
    (hstat : ∀ z : Vec d,
      Measure.map (translateReg z) (blockRegLaw P n m).toMeasure =
        (blockRegLaw P n m).toMeasure) :
    VAddInvariantMeasure (Vec d) (RegCoeffField d)
      (blockRegLaw P n m).toMeasure where
  measure_preimage_vadd z s hs := by
    change (blockRegLaw P n m).toMeasure ((translateReg z) ⁻¹' s) =
      (blockRegLaw P n m).toMeasure s
    rw [← Measure.map_apply (measurable_translateReg z) hs]
    exact congrArg (fun ν : Measure (RegCoeffField d) ↦ ν s) (hstat z)

/-- The manuscript's response `grad Delta⁻¹ (div F)` for the block forcing
`F = (sum of the shells in `(n, m]`) e`: the orthogonal projection of the forcing
onto the stationary potential subspace, with the positive sign of the literal
expression `grad Delta⁻¹ div`. -/
def blockPotentialResponse (P : ProbabilityMeasure (ℕ → ShellField d))
    (n m : ℕ)
    (hstat : ∀ z : Vec d,
      Measure.map (translateReg z) (blockRegLaw P n m).toMeasure =
        (blockRegLaw P n m).toMeasure)
    (e : Vec d)
    (hmem : MemLp (originForcing (d := d) e) 2 (blockRegLaw P n m).toMeasure) :
    SuperdiffusionCLT.Probability.Stationary.VectorL2 d
      (blockRegLaw P n m).toMeasure := by
  haveI := blockRegLaw_vaddInvariant P n m hstat
  exact SuperdiffusionCLT.Probability.Stationary.stationaryPotentialProjection
    (blockForcingL2 P n m e hmem)

end

end SuperdiffusionCLT.Section2.Cutoff
