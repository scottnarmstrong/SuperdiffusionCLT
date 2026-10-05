/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.LimitLocSandwich

/-!
# The matrix sandwich on descendant cubes

`LimitLocSandwich.lean` and the earlier limit-localization estimates
are stated on the single cube `originCube d n`. The multiscale response of
`mathcalE_bounds` uses every descendant cube `R` of `originCube d n`, and the
only property of `R` used in the arguments is `cubeSet R ⊆ cubeSet (originCube d n)`.
This module restates those three steps on an arbitrary triadic cube `R` with
that containment: the sandwich bound `M_L` comes from the same uniform field
estimate on `cubeSet (originCube d m)`, so it does not depend on `R`.

## Main results

* `srootL4_coeffOnCube`: the `Book.Ch02.CoeffOn` bundle on an arbitrary cube.
* `srootL4_coarseBlockMatrix_sandwich_cube`: the two-sided Loewner sandwich on
  every `R` with `cubeSet R ⊆ cubeSet (originCube d n)`, with one sequence `M_L`.
* `srootL4_quadForm_two_sided`: the scalar form of that sandwich at a block vector.
* `srootL4_tendsto_sandwichFactor`: the sandwich factor `nu⁻¹ M + nu⁻¹² M²` tends to `0`
  when `M` does.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

open Homogenization MeasureTheory Filter
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Carriers
open SuperdiffusionCLT.Frozen.Assumptions
open scoped Matrix.Norms.Elementwise

noncomputable section

open Classical in
/-- The `Book.Ch02.CoeffOn` bundle on `cubeDomain R` of a field that is everywhere
elliptic on `cubeSet R`. -/
def srootL4_coeffOnCube {d : ℕ} (R : TriadicCube d) {nu Lam : ℝ}
    (hnu : 0 < nu) (hnuLam : nu ≤ Lam) (a : Homogenization.CoeffField d)
    (hEll : Homogenization.IsEllipticFieldOn nu Lam (Homogenization.cubeSet R) a) :
    Homogenization.Book.Ch02.CoeffOn (Homogenization.Book.Ch02.cubeDomain R) where
  toCoeffField := a
  lam := nu
  Lam := Lam
  lam_pos := hnu
  lam_le_Lam := hnuLam
  aeStronglyMeasurable := by
    classical
    intro i j
    have hEll' := hEll.mono (measurableSet_openCubeSet R) (openCubeSet_subset_cubeSet R)
    have hmeas : Measurable (fun x : Vec d =>
        if x ∈ (Homogenization.Book.Ch02.cubeDomain R : Set (Vec d))
        then a x i j else 0) := by
      have h1 : Measurable (fun x : Vec d => fun i j : Fin d =>
          if x ∈ Homogenization.openCubeSet R then a x i j else 0) := hEll'.1
      have h2 := (measurable_pi_apply i).comp h1
      exact (measurable_pi_apply j).comp h2
    have heq : (fun x : Vec d => restrictCoeffField
        (Homogenization.Book.Ch02.cubeDomain R : Set (Vec d)) a x i j) =
        fun x : Vec d =>
          if x ∈ (Homogenization.Book.Ch02.cubeDomain R : Set (Vec d))
          then a x i j else 0 := by
      funext x
      by_cases hx : x ∈ (Homogenization.Book.Ch02.cubeDomain R : Set (Vec d))
      · simp only [restrictCoeffField, hx, ite_true]
      · simp only [restrictCoeffField, hx, ite_false, Matrix.zero_apply]
    rw [heq]
    exact hmeas.aestronglyMeasurable
  aeElliptic := by
    have hEll' := hEll.mono (measurableSet_openCubeSet R) (openCubeSet_subset_cubeSet R)
    filter_upwards [MeasureTheory.ae_restrict_mem
      (Homogenization.Book.Ch02.cubeDomain R).measurableSet] with x hx
    exact hEll'.2 x hx

/-- `nu ≤ Lam` extracted from `IsEllipticFieldOn` at one point of the cube. -/
theorem srootL4_nu_le_Lam_cube {d : ℕ} {nu Lam : ℝ} (R : TriadicCube d)
    {a : Homogenization.CoeffField d}
    (hEll : Homogenization.IsEllipticFieldOn nu Lam (Homogenization.cubeSet R) a) :
    nu ≤ Lam := by
  obtain ⟨x0, hx0⟩ := (Homogenization.Book.Ch02.cubeDomain R).nonempty
  exact (hEll.2 x0 (openCubeSet_subset_cubeSet R hx0)).2.1

/-- Ellipticity of the shifted cutoff field on every sub-cube of `cubeSet (originCube d n)`. -/
theorem srootL4_exists_ellipticOn_field_cube {d : ℕ} [NeZero d] (nu : ℝ) (hnu : 0 < nu)
    (omega : ShellSeq d) (L m n : ℕ) (k : Fin d → ℤ)
    (hk : (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
          cubeSet (originCube d (n : ℤ)) ⊆ cubeSet (originCube d (m : ℤ)))
    (R : TriadicCube d) (hRn : cubeSet R ⊆ cubeSet (originCube d (n : ℤ))) :
    ∃ Lam : ℝ, nu ≤ Lam ∧
      IsEllipticFieldOn nu Lam (cubeSet R) (srootE_field nu omega L m n k) := by
  obtain ⟨Lam, hLam⟩ := srootL3_isEllipticFieldOn_srootE_field nu hnu omega L m n k hk
  have h := hLam.mono (measurableSet_cubeSet R) hRn
  exact ⟨Lam, srootL4_nu_le_Lam_cube R h, h⟩

/-- Ellipticity of the shifted limiting field on every sub-cube of `cubeSet (originCube d n)`. -/
theorem srootL4_exists_ellipticOn_limField_cube {d : ℕ} (nu : ℝ) (hnu : 0 < nu)
    (omega : ShellSeq d) (m n : ℕ) (k : Fin d → ℤ)
    (hk : (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
          cubeSet (originCube d (n : ℤ)) ⊆ cubeSet (originCube d (m : ℤ)))
    (hsum : Summable fun j : ℕ => shellDerivLinftyNorm (cubeSet (originCube d (m : ℤ))) (omega j))
    (R : TriadicCube d) (hRn : cubeSet R ⊆ cubeSet (originCube d (n : ℤ))) :
    ∃ Lam : ℝ, nu ≤ Lam ∧
      IsEllipticFieldOn nu Lam (cubeSet R) (srootE_limField nu omega m n k) := by
  obtain ⟨Lam, hLam⟩ := srootL4_isEllipticFieldOn_srootE_limField nu hnu omega m n k hk hsum
  have h := hLam.mono (measurableSet_cubeSet R) hRn
  exact ⟨Lam, srootL4_nu_le_Lam_cube R h, h⟩

/-- **The Loewner sandwich on every sub-cube, a.s.**, with one sequence `M_L`. -/
theorem srootL4_coarseBlockMatrix_sandwich_cube {d : ℕ} [NeZero d] (nu : ℝ) (hnu : 0 < nu)
    {P : MeasureTheory.ProbabilityMeasure (ShellSeq d)} (hJ3 : ShellLawJ3 d P)
    (m n : ℕ) (k : Fin d → ℤ)
    (hk : (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
          cubeSet (originCube d (n : ℤ)) ⊆ cubeSet (originCube d (m : ℤ))) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure,
      ∃ M : ℕ → ℝ, (∀ L : ℕ, 0 ≤ M L) ∧ Filter.Tendsto M Filter.atTop (nhds 0) ∧
        ∀ (L : ℕ) (R : TriadicCube d), cubeSet R ⊆ cubeSet (originCube d (n : ℤ)) →
          Homogenization.BlockMatLoewnerLE
              ((-(nu⁻¹ * M L + nu⁻¹ ^ 2 * (M L) ^ 2)) •
                Homogenization.coarseBlockMatrix (openCubeSet R)
                  (srootE_limField nu omega m n k))
              (Homogenization.ofFullBlockMat
                (Homogenization.toFullBlockMat
                    (Homogenization.coarseBlockMatrix (openCubeSet R)
                      (srootE_field nu omega L m n k)) -
                  Homogenization.toFullBlockMat
                    (Homogenization.coarseBlockMatrix (openCubeSet R)
                      (srootE_limField nu omega m n k)))) ∧
            Homogenization.BlockMatLoewnerLE
              (Homogenization.ofFullBlockMat
                (Homogenization.toFullBlockMat
                    (Homogenization.coarseBlockMatrix (openCubeSet R)
                      (srootE_field nu omega L m n k)) -
                  Homogenization.toFullBlockMat
                    (Homogenization.coarseBlockMatrix (openCubeSet R)
                      (srootE_limField nu omega m n k))))
              ((nu⁻¹ * M L + nu⁻¹ ^ 2 * (M L) ^ 2) •
                Homogenization.coarseBlockMatrix (openCubeSet R)
                  (srootE_limField nu omega m n k)) := by
  classical
  have hUsub : cubeSet (originCube d (m : ℤ)) ⊆ openCubeSet (originCube d (m + 1 : ℤ)) :=
    srootL_cubeSet_subset_openCubeSet_succ m
  filter_upwards [srootL2_tendsto_uniformOn_centeredStreamCutoff_centeredStreamField
      (P := P) hJ3 m,
    SuperdiffusionCLT.Section2.Cutoff.eventually_summable_shellDerivLinftyNorm
      (P := P) hJ3 (m := m + 1) (U := cubeSet (originCube d (m : ℤ))) hUsub]
    with omega hbound hsum
  obtain ⟨bound, hbound0, hboundLe, hboundTendsto⟩ := hbound
  refine ⟨fun L => (d : ℝ) * bound L, fun L => mul_nonneg (Nat.cast_nonneg d) (hbound0 L),
    ?_, fun L R hRn => ?_⟩
  · simpa using hboundTendsto.const_mul (d : ℝ)
  · let U : Homogenization.Book.Ch02.Domain d := Homogenization.Book.Ch02.cubeDomain R
    have hMnonneg : (0 : ℝ) ≤ (d : ℝ) * bound L := mul_nonneg (Nat.cast_nonneg d) (hbound0 L)
    have hsRaw : ∀ᵐ x ∂(volumeMeasureOn (U : Set (Vec d))),
        symmPart (srootE_limField nu omega m n k x) = nu • (1 : Mat d) :=
      Filter.Eventually.of_forall (fun x =>
        symmPart_smul_one_add_of_skew
          (centeredStreamField_skew omega (cubeSet (originCube d (m : ℤ))) _))
    have hbRaw : ∀ᵐ x ∂(volumeMeasureOn (U : Set (Vec d))),
        srootE_field nu omega L m n k x =
          srootE_limField nu omega m n k x + srootL4_hField nu omega L m n k x := by
      refine Filter.Eventually.of_forall (fun x => ?_)
      have heq : srootL4_hField nu omega L m n k x =
          srootE_field nu omega L m n k x - srootE_limField nu omega m n k x := rfl
      rw [heq]; abel
    have hskew : ∀ᵐ x ∂(volumeMeasureOn (U : Set (Vec d))),
        matTranspose (srootL4_hField nu omega L m n k x) = -srootL4_hField nu omega L m n k x :=
      Filter.Eventually.of_forall (srootL4_hField_skew nu omega L m n k)
    have hnorm : ∀ᵐ x ∂(volumeMeasureOn (U : Set (Vec d))), ∀ w : Vec d,
        vecNormSq (matVecMul (srootL4_hField nu omega L m n k x) w) ≤
          ((d : ℝ) * bound L) ^ 2 * vecNormSq w := by
      filter_upwards [MeasureTheory.ae_restrict_mem U.measurableSet] with x hx w
      have hxm : (fun l => (3 : ℝ) ^ ((n : ℤ) - 3) * (k l : ℝ)) + x ∈
          cubeSet (originCube d (m : ℤ)) :=
        hk ⟨x, hRn (openCubeSet_subset_cubeSet R hx), rfl⟩
      have hentry : ∀ i j : Fin d, |srootL4_hField nu omega L m n k x i j| ≤ bound L := by
        intro i j
        rw [srootL4_hField_eq]
        have hac : ∀ A B : Mat d, |(A - B) i j| = |(B - A) i j| := by
          intro A B
          rw [Matrix.sub_apply, Matrix.sub_apply, abs_sub_comm]
        rw [hac]
        calc |(centeredStreamField omega (cubeSet (originCube d (m : ℤ)))
                  ((fun l => (3 : ℝ) ^ ((n : ℤ) - 3) * (k l : ℝ)) + x) -
                centeredStreamCutoff omega L (cubeSet (originCube d (m : ℤ)))
                  ((fun l => (3 : ℝ) ^ ((n : ℤ) - 3) * (k l : ℝ)) + x)) i j|
            ≤ ‖centeredStreamField omega (cubeSet (originCube d (m : ℤ)))
                  ((fun l => (3 : ℝ) ^ ((n : ℤ) - 3) * (k l : ℝ)) + x) -
                centeredStreamCutoff omega L (cubeSet (originCube d (m : ℤ)))
                  ((fun l => (3 : ℝ) ^ ((n : ℤ) - 3) * (k l : ℝ)) + x)‖ := by
              rw [← Real.norm_eq_abs]
              exact Matrix.norm_entry_le_entrywise_sup_norm _
          _ ≤ bound L := hboundLe L _ hxm
      have hop : Homogenization.Book.Ch02.matrixOperatorNorm
          (srootL4_hField nu omega L m n k x) ≤ (d : ℝ) * bound L :=
        SuperdiffusionCLT.Section2.Estimates.Stream.matrixOperatorNorm_le_of_entry_bound
          _ (hbound0 L) hentry
      have hopnn : (0 : ℝ) ≤
          Homogenization.Book.Ch02.matrixOperatorNorm (srootL4_hField nu omega L m n k x) :=
        Homogenization.Book.Ch02.matrixOperatorNorm_nonneg _
      have hsq : Homogenization.Book.Ch02.matrixOperatorNorm
            (srootL4_hField nu omega L m n k x) ^ 2 ≤ ((d : ℝ) * bound L) ^ 2 :=
        pow_le_pow_left₀ hopnn hop 2
      have hwnn : (0 : ℝ) ≤ vecNormSq w := Homogenization.vecNormSq_nonneg w
      have hmul : Homogenization.Book.Ch02.matrixOperatorNorm
            (srootL4_hField nu omega L m n k x) ^ 2 * vecNormSq w ≤
          ((d : ℝ) * bound L) ^ 2 * vecNormSq w :=
        mul_le_mul_of_nonneg_right hsq hwnn
      have hstep : vecNormSq (matVecMul (srootL4_hField nu omega L m n k x) w) ≤
          Homogenization.Book.Ch02.matrixOperatorNorm
              (srootL4_hField nu omega L m n k x) ^ 2 * vecNormSq w :=
        Homogenization.Book.Ch02.vecNormSq_matVecMul_le_matrixOperatorNorm_sq_mul_vecNormSq
          (srootL4_hField nu omega L m n k x) w
      exact hstep.trans hmul
    obtain ⟨LamA, hnuA, hEllA⟩ :=
      srootL4_exists_ellipticOn_limField_cube nu hnu omega m n k hk hsum R hRn
    obtain ⟨LamB, hnuB, hEllB⟩ :=
      srootL4_exists_ellipticOn_field_cube nu hnu omega L m n k hk R hRn
    let aCoeff : Homogenization.Book.Ch02.CoeffOn U :=
      srootL4_coeffOnCube R hnu hnuA (srootE_limField nu omega m n k) hEllA
    let bCoeff : Homogenization.Book.Ch02.CoeffOn U :=
      srootL4_coeffOnCube R hnu hnuB (srootE_field nu omega L m n k) hEllB
    have haToC : aCoeff.toCoeffField = srootE_limField nu omega m n k := rfl
    have hbToC : bCoeff.toCoeffField = srootE_field nu omega L m n k := rfl
    have hs : ∀ᵐ x ∂(volumeMeasureOn (U : Set (Vec d))),
        symmPart (aCoeff.toCoeffField x) = nu • (1 : Mat d) := by
      rw [haToC]; exact hsRaw
    have hb : ∀ᵐ x ∂(volumeMeasureOn (U : Set (Vec d))),
        bCoeff.toCoeffField x = aCoeff.toCoeffField x + srootL4_hField nu omega L m n k x := by
      rw [haToC, hbToC]; exact hbRaw
    have hντ := SuperdiffusionCLT.Section2.Localization.coarseBlockMatrix_localization_scalar_two_sided
      (U := U) (a := aCoeff) (b := bCoeff) (h := srootL4_hField nu omega L m n k)
      hnu hMnonneg hs hb hskew hnorm
    have hconv := SuperdiffusionCLT.Section2.Localization.coarseBlockMatrix_toCoeffField U aCoeff
    have hconvB := SuperdiffusionCLT.Section2.Localization.coarseBlockMatrix_toCoeffField U bCoeff
    rw [haToC] at hconv
    rw [hbToC] at hconvB
    simp only [U, Homogenization.Book.Ch02.cubeDomain_coe] at hconv hconvB
    simp only [U] at hντ
    rw [← hconv, ← hconvB] at hντ
    exact hντ

/-- The scalar (fixed block vector) two-sided bound extracted from `BlockMatLoewnerLE`. -/
theorem srootL4_quadForm_two_sided {d : ℕ} {D : ℝ} {AL Ainf : BlockMat d}
    (h1 : Homogenization.BlockMatLoewnerLE ((-D) • Ainf)
        (Homogenization.ofFullBlockMat
          (Homogenization.toFullBlockMat AL - Homogenization.toFullBlockMat Ainf)))
    (h2 : Homogenization.BlockMatLoewnerLE
        (Homogenization.ofFullBlockMat
          (Homogenization.toFullBlockMat AL - Homogenization.toFullBlockMat Ainf))
        (D • Ainf))
    (X : BlockVec d) :
    (1 - D) * blockVecDot X (blockMatVecMul Ainf X) ≤ blockVecDot X (blockMatVecMul AL X) ∧
      blockVecDot X (blockMatVecMul AL X) ≤ (1 + D) * blockVecDot X (blockMatVecMul Ainf X) := by
  have hdiff : blockVecDot X
      (blockMatVecMul (Homogenization.ofFullBlockMat
        (Homogenization.toFullBlockMat AL - Homogenization.toFullBlockMat Ainf)) X) =
      blockVecDot X (blockMatVecMul AL X) - blockVecDot X (blockMatVecMul Ainf X) :=
    blockVecDot_blockMatVecMul_ofFullBlockMat_sub AL Ainf X
  have hh1 := h1 X
  have hh2 := h2 X
  rw [blockMatVecMul_blockSMul, blockVecDot_smul_right, hdiff] at hh1
  rw [hdiff, blockMatVecMul_blockSMul, blockVecDot_smul_right] at hh2
  constructor
  · nlinarith only [hh1]
  · nlinarith only [hh2]

/-- `D_M := nu⁻¹ M + nu⁻¹² M²` tends to `0` when `M` does. -/
theorem srootL4_tendsto_sandwichFactor {M : ℕ → ℝ} (nu : ℝ)
    (hM : Filter.Tendsto M Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun L => nu⁻¹ * M L + nu⁻¹ ^ 2 * (M L) ^ 2) Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun L => nu⁻¹ * M L) Filter.atTop (nhds 0) := by
    simpa using hM.const_mul nu⁻¹
  have h2 : Filter.Tendsto (fun L => nu⁻¹ ^ 2 * (M L) ^ 2) Filter.atTop (nhds 0) := by
    have hmul := (hM.mul hM).const_mul (nu⁻¹ ^ 2)
    have heq : (fun L : ℕ => nu⁻¹ ^ 2 * (M L * M L)) = fun L => nu⁻¹ ^ 2 * (M L) ^ 2 := by
      funext L; ring
    rw [heq] at hmul
    have hz : nu⁻¹ ^ 2 * ((0 : ℝ) * 0) = 0 := by ring
    rwa [hz] at hmul
  simpa using h1.add h2

end

end SuperdiffusionCLT.Section4.MinimalScales
