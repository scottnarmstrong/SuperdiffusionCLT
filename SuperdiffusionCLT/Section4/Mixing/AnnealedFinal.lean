/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.Mixing.TermsCombined
public import SuperdiffusionCLT.Section4.Mixing.AnnealedComparison
public import SuperdiffusionCLT.Section3.HighContrast.BEllParameters

/-!
# `p.mixing.P.three.prime#annealed-comparison`, final composition

This file proves `mixFin_annealedComparison`: from `mixTerms_combineTermsBound`'s
quenched three-witness bound (`Section4/Mixing/TermsCombined.lean`), take
expectations and use stationarity to get the deterministic sandwich bound on
`bfAhom_L(cu_n) - bfAhom_ell(cu_n)`, the annealed-comparison step of the proof of
`p.mixing.P.three.prime`, in the bilinear-sandwich reading established
by `Section4/Mixing/InvertB.lean` (whose `hsand` hypothesis this theorem's
conclusion is built to supply directly).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

open Homogenization
open Homogenization.IndependentSums
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff (ShellSeq)
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2 (coefficientCutoff)
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## Integrability from a `Gamma_sigma` tail bound -/

/-- **A measurable `O_{Gamma_sigma}(A)` random variable (`A > 0`) is
integrable.** Integrability is
not automatic from `IsBigO` alone, but follows from the library's absolute
`p`-th moment growth at `p = 1`. -/
theorem mixFin_integrable_of_isBigO_gammaSigma {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : Ω → ℝ} {A σ : ℝ} (hσ : 0 < σ) (hA : 0 < A)
    (hXm : Measurable X) (hX : IsBigO μ (gammaSigma σ) X A) :
    MeasureTheory.Integrable X μ := by
  have hXO : IsBigOWith μ (gammaSigma σ) (fun ω => |X ω|) A := hX
  have hXabsm : Measurable (fun ω => |X ω|) := continuous_abs.measurable.comp hXm
  have hInt := integrable_rpow_of_isBigOWith_gammaSigma (μ := μ) (Y := fun ω => |X ω|)
    (K := A) (σ := σ) (p := 1) hσ hA le_rfl (fun ω => abs_nonneg (X ω))
    hXabsm.aemeasurable hXO
  have hEq : (fun ω => |X ω| ^ (1 : ℝ)) = fun ω => |X ω| := by
    funext ω
    exact Real.rpow_one _
  rw [hEq] at hInt
  have hNorm : (fun ω => |X ω|) = fun ω => ‖X ω‖ := by
    funext ω
    exact (Real.norm_eq_abs (X ω)).symm
  rw [hNorm] at hInt
  exact (MeasureTheory.integrable_norm_iff hXm.aestronglyMeasurable).mp hInt

/-! ## The entrywise linearity-under-the-integral swap, bilinear form -/

/-- The bilinear expansion of a quadratic-form sum, generalizing the private
`vecDot_matVecMul_eq_sum` of `Section3/Terms/BlockConcentrationInputs.lean` to
two (possibly distinct) test vectors `e`, `f`. -/
private theorem mixFin_vecDot_matVecMul_eq_sum (e f : Vec d) (M : Mat d) :
    vecDot e (matVecMul M f) = ∑ i, ∑ j, e i * (M i j * f j) := by
  rw [vecDot]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [matVecMul, Finset.mul_sum]

/-- **The entrywise `integral_finsetSum` swap, bilinear form** (an
ingredient of the annealed comparison): for fixed test vectors `e`, `f` and an
entrywise-integrable random matrix `M`, expectation commutes with the bilinear
form `vecDot e (matVecMul (M ·) f)`. -/
theorem mixFin_integral_vecDot_matVecMul {P : MeasureTheory.ProbabilityMeasure (ShellSeq d)}
    (e f : Vec d) {M : ShellSeq d → Mat d}
    (hM : ∀ i j, MeasureTheory.Integrable (fun omega : ShellSeq d => M omega i j) P.toMeasure) :
    ∫ omega : ShellSeq d, vecDot e (matVecMul (M omega) f) ∂P.toMeasure =
      vecDot e (matVecMul (fun i j => ∫ omega : ShellSeq d, M omega i j ∂P.toMeasure) f) := by
  have heq : (fun omega : ShellSeq d => vecDot e (matVecMul (M omega) f)) =
      fun omega : ShellSeq d => ∑ i, ∑ j, e i * (M omega i j * f j) :=
    funext fun omega => mixFin_vecDot_matVecMul_eq_sum e f (M omega)
  rw [heq]
  refine Eq.trans ?_ (mixFin_vecDot_matVecMul_eq_sum e f _).symm
  rw [MeasureTheory.integral_finsetSum _ fun i _ =>
      MeasureTheory.integrable_finsetSum _ fun j _ => ((hM i j).mul_const (f j)).const_mul (e i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MeasureTheory.integral_finsetSum _ fun j _ => ((hM i j).mul_const (f j)).const_mul (e i)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const]

/-- The integrability companion of `mixFin_integral_vecDot_matVecMul`. -/
theorem mixFin_integrable_vecDot_matVecMul {P : MeasureTheory.ProbabilityMeasure (ShellSeq d)}
    (e f : Vec d) {M : ShellSeq d → Mat d}
    (hM : ∀ i j, MeasureTheory.Integrable (fun omega : ShellSeq d => M omega i j) P.toMeasure) :
    MeasureTheory.Integrable (fun omega : ShellSeq d => vecDot e (matVecMul (M omega) f)) P.toMeasure := by
  have heq : (fun omega : ShellSeq d => vecDot e (matVecMul (M omega) f)) =
      fun omega : ShellSeq d => ∑ i, ∑ j, e i * (M omega i j * f j) :=
    funext fun omega => mixFin_vecDot_matVecMul_eq_sum e f (M omega)
  rw [heq]
  exact MeasureTheory.integrable_finsetSum _ fun i _ =>
    MeasureTheory.integrable_finsetSum _ fun j _ => ((hM i j).mul_const (f j)).const_mul (e i)

/-- `Integrable.add`, restated with a pointwise (not `Pi.add`) target type so
it composes with `MeasureTheory.integral_add` under `rw` without a
higher-order matching mismatch. -/
private theorem mixFin_integrable_add' {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} {f g : Ω → ℝ}
    (hf : MeasureTheory.Integrable f μ) (hg : MeasureTheory.Integrable g μ) :
    MeasureTheory.Integrable (fun a => f a + g a) μ :=
  hf.add hg

/-! ## The block decomposition of the bilinear form -/

/-- The bilinear value of a `BlockMat d` splits into its four block bilinear
values. Pure algebra: no measure theory. -/
private theorem mixFin_blockVecDot_blockMatVecMul_eq (A : BlockMat d) (p q : BlockVec d) :
    blockVecDot p (blockMatVecMul A q) =
      vecDot p.1 (matVecMul A.upperLeft q.1) + vecDot p.1 (matVecMul A.upperRight q.2) +
        (vecDot p.2 (matVecMul A.lowerLeft q.1) + vecDot p.2 (matVecMul A.lowerRight q.2)) := by
  rcases p with ⟨p1, p2⟩
  rcases q with ⟨q1, q2⟩
  show vecDot p1 (matVecMul A.upperLeft q1 + matVecMul A.upperRight q2) +
      vecDot p2 (matVecMul A.lowerLeft q1 + matVecMul A.lowerRight q2) =
    vecDot p1 (matVecMul A.upperLeft q1) + vecDot p1 (matVecMul A.upperRight q2) +
      (vecDot p2 (matVecMul A.lowerLeft q1) + vecDot p2 (matVecMul A.lowerRight q2))
  rw [vecDot_add_right, vecDot_add_right]

/-! ## The full block-bilinear stationarity identity -/

/-- **`E[blockVecDot p (blockMatVecMul (bfA_L(z+cu_n)) q)] = blockVecDot p
(blockMatVecMul (bfAhom_L(cu_n)) q)` for every scale-`n` translate `z`.** The
bilinear (arbitrary `p`, `q`, arbitrary block, not just the diagonal quadratic
form) generalization of `AnnealedComparison.lean`'s four entrywise
`mixMain_integral_coarseBlockMatrix_*_eq` facts, combined via
`mixFin_integral_vecDot_matVecMul` (linearity of the expectation) and the
integrability facts of `Section2/Annealed/Integrability.lean`. -/
theorem mixFin_integral_blockVecDot_coarseBlockMatrix_eq [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : MeasureTheory.ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (L nn : ℕ)
    {z : TriadicCube d} (hz : z.scale = (nn : ℤ)) (p q : BlockVec d) :
    ∫ omega : ShellSeq d, blockVecDot p (blockMatVecMul
        (coarseBlockMatrix (cubeSet z) (coefficientCutoff nu omega L).toCoeffField) q)
      ∂P.toMeasure =
      blockVecDot p
        (blockMatVecMul (annealedBlockMatrix nu L P (cubeSet (originCube d (nn : ℤ)))) q) := by
  have hULint : ∀ i j, MeasureTheory.Integrable
      (fun omega : ShellSeq d => (coarseBlockMatrix (cubeSet z)
        (coefficientCutoff nu omega L).toCoeffField).upperLeft i j) P.toMeasure :=
    fun i j => integrable_coarseBlockMatrix_upperLeft_apply hnu L z hPrefix hJ2 hJ3 hJ4 i j
  have hURint : ∀ i j, MeasureTheory.Integrable
      (fun omega : ShellSeq d => (coarseBlockMatrix (cubeSet z)
        (coefficientCutoff nu omega L).toCoeffField).upperRight i j) P.toMeasure :=
    fun i j => integrable_coarseBlockMatrix_upperRight_apply hnu L z hPrefix hJ2 hJ3 hJ4 i j
  have hLLint : ∀ i j, MeasureTheory.Integrable
      (fun omega : ShellSeq d => (coarseBlockMatrix (cubeSet z)
        (coefficientCutoff nu omega L).toCoeffField).lowerLeft i j) P.toMeasure :=
    fun i j => integrable_coarseBlockMatrix_lowerLeft_apply hnu L z hPrefix hJ2 hJ3 hJ4 i j
  have hLRint : ∀ i j, MeasureTheory.Integrable
      (fun omega : ShellSeq d => (coarseBlockMatrix (cubeSet z)
        (coefficientCutoff nu omega L).toCoeffField).lowerRight i j) P.toMeasure :=
    fun i j => integrable_coarseBlockMatrix_lowerRight_apply hnu L z hPrefix hJ2 hJ3 hJ4 i j
  have heq : (fun omega : ShellSeq d => blockVecDot p (blockMatVecMul
        (coarseBlockMatrix (cubeSet z) (coefficientCutoff nu omega L).toCoeffField) q)) =
      fun omega : ShellSeq d =>
        vecDot p.1 (matVecMul (coarseBlockMatrix (cubeSet z)
          (coefficientCutoff nu omega L).toCoeffField).upperLeft q.1) +
          vecDot p.1 (matVecMul (coarseBlockMatrix (cubeSet z)
            (coefficientCutoff nu omega L).toCoeffField).upperRight q.2) +
          (vecDot p.2 (matVecMul (coarseBlockMatrix (cubeSet z)
              (coefficientCutoff nu omega L).toCoeffField).lowerLeft q.1) +
            vecDot p.2 (matVecMul (coarseBlockMatrix (cubeSet z)
              (coefficientCutoff nu omega L).toCoeffField).lowerRight q.2)) :=
    funext fun omega => mixFin_blockVecDot_blockMatVecMul_eq _ p q
  rw [heq]
  have hstep :
      ∫ omega : ShellSeq d,
          (vecDot p.1 (matVecMul (coarseBlockMatrix (cubeSet z)
              (coefficientCutoff nu omega L).toCoeffField).upperLeft q.1) +
            vecDot p.1 (matVecMul (coarseBlockMatrix (cubeSet z)
                (coefficientCutoff nu omega L).toCoeffField).upperRight q.2) +
            (vecDot p.2 (matVecMul (coarseBlockMatrix (cubeSet z)
                  (coefficientCutoff nu omega L).toCoeffField).lowerLeft q.1) +
              vecDot p.2 (matVecMul (coarseBlockMatrix (cubeSet z)
                  (coefficientCutoff nu omega L).toCoeffField).lowerRight q.2))) ∂P.toMeasure =
        (∫ omega : ShellSeq d, vecDot p.1 (matVecMul (coarseBlockMatrix (cubeSet z)
              (coefficientCutoff nu omega L).toCoeffField).upperLeft q.1) ∂P.toMeasure +
            ∫ omega : ShellSeq d, vecDot p.1 (matVecMul (coarseBlockMatrix (cubeSet z)
                (coefficientCutoff nu omega L).toCoeffField).upperRight q.2) ∂P.toMeasure) +
          (∫ omega : ShellSeq d, vecDot p.2 (matVecMul (coarseBlockMatrix (cubeSet z)
                (coefficientCutoff nu omega L).toCoeffField).lowerLeft q.1) ∂P.toMeasure +
            ∫ omega : ShellSeq d, vecDot p.2 (matVecMul (coarseBlockMatrix (cubeSet z)
                (coefficientCutoff nu omega L).toCoeffField).lowerRight q.2) ∂P.toMeasure) := by
    have h1 := MeasureTheory.integral_add (mixFin_integrable_vecDot_matVecMul p.1 q.1 hULint)
      (mixFin_integrable_vecDot_matVecMul p.1 q.2 hURint)
    have h2 := MeasureTheory.integral_add (mixFin_integrable_vecDot_matVecMul p.2 q.1 hLLint)
      (mixFin_integrable_vecDot_matVecMul p.2 q.2 hLRint)
    have h3 := MeasureTheory.integral_add
      (mixFin_integrable_add' (mixFin_integrable_vecDot_matVecMul p.1 q.1 hULint)
        (mixFin_integrable_vecDot_matVecMul p.1 q.2 hURint))
      (mixFin_integrable_add' (mixFin_integrable_vecDot_matVecMul p.2 q.1 hLLint)
        (mixFin_integrable_vecDot_matVecMul p.2 q.2 hLRint))
    rw [h3, h1, h2]
  rw [hstep, mixFin_integral_vecDot_matVecMul p.1 q.1 hULint,
    mixFin_integral_vecDot_matVecMul p.1 q.2 hURint,
    mixFin_integral_vecDot_matVecMul p.2 q.1 hLLint,
    mixFin_integral_vecDot_matVecMul p.2 q.2 hLRint]
  have hUL : (fun i j => ∫ omega : ShellSeq d, (coarseBlockMatrix (cubeSet z)
        (coefficientCutoff nu omega L).toCoeffField).upperLeft i j ∂P.toMeasure) =
      (annealedBlockMatrix nu L P (cubeSet (originCube d (nn : ℤ)))).upperLeft := by
    funext i j
    exact mixMain_integral_coarseBlockMatrix_upperLeft_eq hnu hPrefix hJ2 hJ3 hJ4 L nn hz i j
  have hUR : (fun i j => ∫ omega : ShellSeq d, (coarseBlockMatrix (cubeSet z)
        (coefficientCutoff nu omega L).toCoeffField).upperRight i j ∂P.toMeasure) =
      (annealedBlockMatrix nu L P (cubeSet (originCube d (nn : ℤ)))).upperRight := by
    funext i j
    exact mixMain_integral_coarseBlockMatrix_upperRight_eq hnu hPrefix hJ2 hJ3 hJ4 L nn hz i j
  have hLL : (fun i j => ∫ omega : ShellSeq d, (coarseBlockMatrix (cubeSet z)
        (coefficientCutoff nu omega L).toCoeffField).lowerLeft i j ∂P.toMeasure) =
      (annealedBlockMatrix nu L P (cubeSet (originCube d (nn : ℤ)))).lowerLeft := by
    funext i j
    exact mixMain_integral_coarseBlockMatrix_lowerLeft_eq hnu hPrefix hJ2 hJ3 hJ4 L nn hz i j
  have hLR : (fun i j => ∫ omega : ShellSeq d, (coarseBlockMatrix (cubeSet z)
        (coefficientCutoff nu omega L).toCoeffField).lowerRight i j ∂P.toMeasure) =
      (annealedBlockMatrix nu L P (cubeSet (originCube d (nn : ℤ)))).lowerRight := by
    funext i j
    exact mixMain_integral_coarseBlockMatrix_lowerRight_eq hnu hPrefix hJ2 hJ3 hJ4 L nn hz i j
  rw [hUL, hUR, hLL, hLR, mixFin_blockVecDot_blockMatVecMul_eq]

/-! ## Averaging over the descendant cubes -/

/-- Every scale-`(m-n)`-depth descendant of `cu_m` has scale `n`. -/
private theorem mixFin_scale_eq_of_mem_descendantsAtDepth {n m : ℕ} (hnm : n ≤ m)
    {R : TriadicCube d} (hR : R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n)) :
    R.scale = (n : ℤ) := by
  have h := scale_eq_sub_of_mem_descendantsAtDepth hR
  have hoscale : (originCube d (m : ℤ)).scale = (m : ℤ) := rfl
  rw [hoscale] at h
  omega

/-- The integrability of a single summand, reused by every averaging step
below. -/
private theorem mixFin_integrable_blockVecDot_coarseBlockMatrix [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) {P : MeasureTheory.ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (L : ℕ) (R : TriadicCube d) (p q : BlockVec d) :
    MeasureTheory.Integrable (fun omega : ShellSeq d => blockVecDot p (blockMatVecMul
        (coarseBlockMatrix (cubeSet R) (coefficientCutoff nu omega L).toCoeffField) q))
      P.toMeasure := by
  have hUL := integrable_coarseBlockMatrix_upperLeft_apply hnu L R hPrefix hJ2 hJ3 hJ4
  have hUR := integrable_coarseBlockMatrix_upperRight_apply hnu L R hPrefix hJ2 hJ3 hJ4
  have hLL := integrable_coarseBlockMatrix_lowerLeft_apply hnu L R hPrefix hJ2 hJ3 hJ4
  have hLR := integrable_coarseBlockMatrix_lowerRight_apply hnu L R hPrefix hJ2 hJ3 hJ4
  have heq : (fun omega : ShellSeq d => blockVecDot p (blockMatVecMul
        (coarseBlockMatrix (cubeSet R) (coefficientCutoff nu omega L).toCoeffField) q)) =
      fun omega : ShellSeq d =>
        (vecDot p.1 (matVecMul (coarseBlockMatrix (cubeSet R)
            (coefficientCutoff nu omega L).toCoeffField).upperLeft q.1) +
          vecDot p.1 (matVecMul (coarseBlockMatrix (cubeSet R)
              (coefficientCutoff nu omega L).toCoeffField).upperRight q.2)) +
          (vecDot p.2 (matVecMul (coarseBlockMatrix (cubeSet R)
                (coefficientCutoff nu omega L).toCoeffField).lowerLeft q.1) +
            vecDot p.2 (matVecMul (coarseBlockMatrix (cubeSet R)
                (coefficientCutoff nu omega L).toCoeffField).lowerRight q.2)) :=
    funext fun omega => mixFin_blockVecDot_blockMatVecMul_eq _ p q
  rw [heq]
  exact mixFin_integrable_add'
    (mixFin_integrable_add' (mixFin_integrable_vecDot_matVecMul p.1 q.1 hUL)
      (mixFin_integrable_vecDot_matVecMul p.1 q.2 hUR))
    (mixFin_integrable_add' (mixFin_integrable_vecDot_matVecMul p.2 q.1 hLL)
      (mixFin_integrable_vecDot_matVecMul p.2 q.2 hLR))

/-- The integrability of the whole averaged sum. -/
private theorem mixFin_integrable_avg_coarseBlockMatrix [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : MeasureTheory.ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (L n m : ℕ)
    (p q : BlockVec d) :
    MeasureTheory.Integrable (fun omega : ShellSeq d =>
        ((descendantsAtDepth (originCube d (m : ℤ)) (m - n)).card : ℝ)⁻¹ *
          ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n),
            blockVecDot p (blockMatVecMul
              (coarseBlockMatrix (cubeSet R) (coefficientCutoff nu omega L).toCoeffField) q))
      P.toMeasure :=
  MeasureTheory.Integrable.const_mul
    (MeasureTheory.integrable_finsetSum _ fun R _hR =>
      mixFin_integrable_blockVecDot_coarseBlockMatrix hnu hPrefix hJ2 hJ3 hJ4 L R p q) _

/-- **The average over the descendant cubes of the stationarity identity.**
Averaging `mixFin_integral_blockVecDot_coarseBlockMatrix_eq` over the
scale-`n` descendants of `cu_m`, using that every descendant gives the same
(deterministic) value. -/
theorem mixFin_integral_avg_coarseBlockMatrix_eq [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : MeasureTheory.ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (L n m : ℕ)
    (hnm : n ≤ m) (p q : BlockVec d) :
    ∫ omega : ShellSeq d,
        ((descendantsAtDepth (originCube d (m : ℤ)) (m - n)).card : ℝ)⁻¹ *
          ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n),
            blockVecDot p (blockMatVecMul
              (coarseBlockMatrix (cubeSet R) (coefficientCutoff nu omega L).toCoeffField) q)
      ∂P.toMeasure =
      blockVecDot p
        (blockMatVecMul (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) q) := by
  set s := descendantsAtDepth (originCube d (m : ℤ)) (m - n) with hs_def
  have hs : s.Nonempty := descendantsAtDepth_nonempty _ _
  have hcard_ne : (s.card : ℝ) ≠ 0 := by
    have : 0 < s.card := Finset.card_pos.mpr hs
    exact_mod_cast this.ne'
  have hRint : ∀ R ∈ s, MeasureTheory.Integrable
      (fun omega : ShellSeq d => blockVecDot p (blockMatVecMul
        (coarseBlockMatrix (cubeSet R) (coefficientCutoff nu omega L).toCoeffField) q))
      P.toMeasure :=
    fun R _hR => mixFin_integrable_blockVecDot_coarseBlockMatrix hnu hPrefix hJ2 hJ3 hJ4 L R p q
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_finsetSum s hRint]
  have hconst : ∀ R ∈ s,
      ∫ omega : ShellSeq d, blockVecDot p (blockMatVecMul
          (coarseBlockMatrix (cubeSet R) (coefficientCutoff nu omega L).toCoeffField) q)
        ∂P.toMeasure =
      blockVecDot p
        (blockMatVecMul (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) q) := by
    intro R hR
    exact mixFin_integral_blockVecDot_coarseBlockMatrix_eq hnu hPrefix hJ2 hJ3 hJ4 L n
      (mixFin_scale_eq_of_mem_descendantsAtDepth hnm hR) p q
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ hcard_ne, one_mul]

/-! ## Connecting to `mixTerms_reassembled`, and the annealed comparison -/

/-- The pointwise (in `omega`) averaged form of `mixTerms_reassembled`'s
bilinear value: `mixTerms_reassembled` is *by definition*
`ofFullBlockMat (toFullBlockMat (bfA_L(R)) - toFullBlockMat (bfAhom_ell(cu_n)))`,
so `mixTerms_blockVecDot_ofFullBlockMat_sub_bilinear` (`DecomposeInstance.lean`)
splits its bilinear value at each `R`, and the second term is
constant in `R`. -/
private theorem mixFin_avg_reassembled_eq (nu : ℝ) (omega : ShellSeq d) (ell L n m : ℕ)
    (P : MeasureTheory.ProbabilityMeasure (ShellSeq d)) (p q : BlockVec d) :
    ((descendantsAtDepth (originCube d (m : ℤ)) (m - n)).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n),
          blockVecDot p (blockMatVecMul (mixTerms_reassembled nu omega ell L P (n : ℤ) R) q) =
      ((descendantsAtDepth (originCube d (m : ℤ)) (m - n)).card : ℝ)⁻¹ *
          ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n),
            blockVecDot p (blockMatVecMul
              (coarseBlockMatrix (cubeSet R) (coefficientCutoff nu omega L).toCoeffField) q) -
        blockVecDot p (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) q) := by
  set s := descendantsAtDepth (originCube d (m : ℤ)) (m - n) with hs_def
  have hs : s.Nonempty := descendantsAtDepth_nonempty _ _
  have hcard_ne : (s.card : ℝ) ≠ 0 := by
    have : 0 < s.card := Finset.card_pos.mpr hs
    exact_mod_cast this.ne'
  have hpt : ∀ R ∈ s,
      blockVecDot p (blockMatVecMul (mixTerms_reassembled nu omega ell L P (n : ℤ) R) q) =
        blockVecDot p (blockMatVecMul
            (coarseBlockMatrix (cubeSet R) (coefficientCutoff nu omega L).toCoeffField) q) -
          blockVecDot p (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) q) := by
    intro R _
    rw [mixTerms_reassembled, mixTerms_blockVecDot_ofFullBlockMat_sub_bilinear]
  rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_sub,
    ← mul_assoc, inv_mul_cancel₀ hcard_ne, one_mul]

/-- The integral of `mixFin_avg_reassembled_eq`: expectation and stationarity
turn the averaged `mixTerms_reassembled` bilinear value into the deterministic
difference of the two annealed bilinear values. -/
theorem mixFin_integral_avg_reassembled_eq [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : MeasureTheory.ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (ell L n m : ℕ)
    (hnm : n ≤ m) (p q : BlockVec d) :
    ∫ omega : ShellSeq d,
        ((descendantsAtDepth (originCube d (m : ℤ)) (m - n)).card : ℝ)⁻¹ *
          ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n),
            blockVecDot p (blockMatVecMul (mixTerms_reassembled nu omega ell L P (n : ℤ) R) q)
      ∂P.toMeasure =
      blockVecDot p
          (blockMatVecMul (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) q) -
        blockVecDot p (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) q) := by
  have heq : (fun omega : ShellSeq d =>
        ((descendantsAtDepth (originCube d (m : ℤ)) (m - n)).card : ℝ)⁻¹ *
          ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n),
            blockVecDot p (blockMatVecMul (mixTerms_reassembled nu omega ell L P (n : ℤ) R) q)) =
      fun omega : ShellSeq d =>
        (((descendantsAtDepth (originCube d (m : ℤ)) (m - n)).card : ℝ)⁻¹ *
            ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n),
              blockVecDot p (blockMatVecMul
                (coarseBlockMatrix (cubeSet R) (coefficientCutoff nu omega L).toCoeffField) q)) -
          blockVecDot p (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) q) :=
    funext fun omega => mixFin_avg_reassembled_eq nu omega ell L n m P p q
  rw [heq, MeasureTheory.integral_sub (mixFin_integrable_avg_coarseBlockMatrix hnu hPrefix hJ2 hJ3 hJ4 L n m p q)
    (MeasureTheory.integrable_const _),
    mixFin_integral_avg_coarseBlockMatrix_eq hnu hPrefix hJ2 hJ3 hJ4 L n m hnm p q,
    MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul]

/-! ## The final composition: `p.mixing.P.three.prime#annealed-comparison` -/

/-- **`p.mixing.P.three.prime#annealed-comparison`**, final
composition. From `mixTerms_combineTermsBound`'s quenched three-witness bound
(`Section4/Mixing/TermsCombined.lean`), taking expectations (using
`mixFin_integral_avg_reassembled_eq`, i.e. linearity and integrability) and bounding the
resulting deterministic amplitude by its `gammaMomentConst`-scaled first moment
(`mixMain_integral_sum3_le_of_isBigO_gammaSigma`, `AnnealedComparison.lean`)
against the nonnegative quadratic form
`blockVecDot p (blockMatVecMul (bfAhom_ell(cu_n)) p) + blockVecDot q (...) q`
(from `mixMain_annealedBilinear_eq` and the scalar positivity facts `sigmaBarSeq_pos`,
`sigmaBarStarInvSeq_pos`) gives the deterministic sandwich bound on
`bfAhom_L(cu_n) - bfAhom_ell(cu_n)`, in the bilinear-sandwich reading
`Section4/Mixing/InvertB.lean`'s `hsand` consumes (with `H := bfAhom_L(cu_n) - bfAhom_ell(cu_n)`,
`A := bfAhom_ell(cu_n)`, `t` the amplitude below).

Beyond `mixTerms_combineTermsBound`'s own hypotheses this carries the standing
shell laws `hnu, hPrefix, hJ2, hJ3, hJ4` (needed for stationarity and for the
scalar positivity facts), `hnm : n ≤ m` (so the descendant cubes of `cu_m` at
depth `m - n` have scale exactly `n`), and `hLell : ell < L` (so the two
`Gamma`-witness amplitudes inherited from `hGaugeBound` are strictly positive,
as `integrable_rpow_of_isBigOWith_gammaSigma` needs). -/
theorem mixFin_annealedComparison [NeZero d] {C : ℝ} (hC : 1 ≤ C) (nu : ℝ) (hnu : 0 < nu)
    {P : MeasureTheory.ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (ell L n m : ℕ) (hm : 1 ≤ m) (hnm : n ≤ m) (hLell : ell < L)
    (hLocBound :
      ∃ X3loc : ShellSeq d → ℝ,
        Measurable X3loc ∧
          IsBigO P.toMeasure (gammaSigma ((1 : ℝ) / 3)) X3loc (C * (m : ℝ) ^ (-(5000 : ℝ))) ∧
          ∀ (omega : ShellSeq d) (p q : BlockVec d),
            2 *
                (((descendantsAtDepth (originCube d (m : ℤ)) (m - n)).card : ℝ)⁻¹ *
                  ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n),
                    blockVecDot p
                      (blockMatVecMul (mixTerms_localizationTermMatrix nu omega ell L P (n : ℤ) R) q)) ≤
              X3loc omega *
                (blockVecDot p (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) p) +
                  blockVecDot q (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) q)))
    (hGaugeBound :
      ∃ X1g X2g X3g : ShellSeq d → ℝ,
        Measurable X1g ∧
          IsBigO P.toMeasure (gammaSigma 2) X1g
            (C * ((L - ell : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
              (sigmaBarStarScalar nu L P (cubeSet (originCube d (n : ℤ)))) ^ (-(1 : ℝ))) ∧
        Measurable X2g ∧
          IsBigO P.toMeasure (gammaSigma 1) X2g
            (C * ((L - ell : ℕ) : ℝ) *
              (sigmaBarStarScalar nu L P (cubeSet (originCube d (n : ℤ)))) ^ (-(2 : ℝ))) ∧
        Measurable X3g ∧
          IsBigO P.toMeasure (gammaSigma ((1 : ℝ) / 3)) X3g (C * (m : ℝ) ^ (-(5000 : ℝ))) ∧
          ∀ (omega : ShellSeq d) (p q : BlockVec d),
            2 *
                (((descendantsAtDepth (originCube d (m : ℤ)) (m - n)).card : ℝ)⁻¹ *
                  ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n),
                    blockVecDot p (blockMatVecMul (mixTerms_gaugeTermMatrix nu omega ell L P (n : ℤ) R) q)) ≤
              (X1g omega + X2g omega + X3g omega) *
                (blockVecDot p (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) p) +
                  blockVecDot q (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) q))) :
    ∀ p q : BlockVec d,
      2 * (blockVecDot p (blockMatVecMul (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) q) -
             blockVecDot p (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) q)) ≤
        (gammaMomentConst 2 *
              (C * ((L - ell : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
                (sigmaBarStarScalar nu L P (cubeSet (originCube d (n : ℤ)))) ^ (-(1 : ℝ))) +
            gammaMomentConst 1 *
              (C * ((L - ell : ℕ) : ℝ) *
                (sigmaBarStarScalar nu L P (cubeSet (originCube d (n : ℤ)))) ^ (-(2 : ℝ))) +
            gammaMomentConst ((1 : ℝ) / 3) *
              (gammaTriangleConst ((1 : ℝ) / 3) * (2 * (C * (m : ℝ) ^ (-(5000 : ℝ)))))) *
          (blockVecDot p (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) p) +
            blockVecDot q (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) q)) := by
  intro p q
  obtain ⟨X1, X2, X3, hX1M, hX1O, hX2M, hX2O, hX3M, hX3O, hQuenched⟩ :=
    mixTerms_combineTermsBound hC nu P ell L n m hm hLocBound hGaugeBound
  have hLellR : (0 : ℝ) < ((L - ell : ℕ) : ℝ) := by
    have hpos : 0 < L - ell := by omega
    exact_mod_cast hpos
  have hsigmaLpos : 0 < sigmaBarStarScalar nu L P (cubeSet (originCube d (n : ℤ))) :=
    SuperdiffusionCLT.Section3.HighContrast.sigmaBarStarScalar_pos hnu L hPrefix hJ2 hJ3 hJ4 (n : ℤ)
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hA1pos : 0 <
      C * ((L - ell : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
        (sigmaBarStarScalar nu L P (cubeSet (originCube d (n : ℤ)))) ^ (-(1 : ℝ)) :=
    mul_pos (mul_pos hCpos (Real.rpow_pos_of_pos hLellR _)) (Real.rpow_pos_of_pos hsigmaLpos _)
  have hA2pos : 0 <
      C * ((L - ell : ℕ) : ℝ) * (sigmaBarStarScalar nu L P (cubeSet (originCube d (n : ℤ)))) ^ (-(2 : ℝ)) :=
    mul_pos (mul_pos hCpos hLellR) (Real.rpow_pos_of_pos hsigmaLpos _)
  have hA3pos : 0 < gammaTriangleConst ((1 : ℝ) / 3) * (2 * (C * (m : ℝ) ^ (-(5000 : ℝ)))) :=
    mul_pos gammaTriangleConst_pos (mul_pos two_pos (mul_pos hCpos (Real.rpow_pos_of_pos hmR _)))
  have hInt1 : MeasureTheory.Integrable X1 P.toMeasure :=
    mixFin_integrable_of_isBigO_gammaSigma (by norm_num) hA1pos hX1M hX1O
  have hInt2 : MeasureTheory.Integrable X2 P.toMeasure :=
    mixFin_integrable_of_isBigO_gammaSigma (by norm_num) hA2pos hX2M hX2O
  have hInt3 : MeasureTheory.Integrable X3 P.toMeasure :=
    mixFin_integrable_of_isBigO_gammaSigma (by norm_num) hA3pos hX3M hX3O
  have hellpos_s : 0 ≤ sigmaBarScalar nu ell P (cubeSet (originCube d (n : ℤ))) :=
    (sigmaBarSeq_pos hnu ell hPrefix hJ2 hJ3 hJ4 n).le
  have hellpos_si : 0 ≤ sigmaBarStarInvScalar nu ell P (cubeSet (originCube d (n : ℤ))) :=
    (sigmaBarStarInvSeq_pos hnu ell hPrefix hJ2 hJ3 hJ4 n).le
  have hQp := mixMain_annealedBilinear_eq hnu ell hJ4 (n : ℤ) p
  have hQq := mixMain_annealedBilinear_eq hnu ell hJ4 (n : ℤ) q
  have hCtot_nonneg : 0 ≤ blockVecDot p (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) p) +
      blockVecDot q (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) q) := by
    rw [show (mixTerms_Aell nu ell P (n : ℤ) : BlockMat d) =
        annealedBlockMatrix nu ell P (cubeSet (originCube d (n : ℤ))) from rfl, hQp, hQq]
    nlinarith only [mul_nonneg hellpos_s (vecNormSq_nonneg p.1), mul_nonneg hellpos_si (vecNormSq_nonneg p.2),
      mul_nonneg hellpos_s (vecNormSq_nonneg q.1), mul_nonneg hellpos_si (vecNormSq_nonneg q.2)]
  set F : ShellSeq d → ℝ := fun omega =>
      ((descendantsAtDepth (originCube d (m : ℤ)) (m - n)).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n),
          blockVecDot p (blockMatVecMul (mixTerms_reassembled nu omega ell L P (n : ℤ) R) q) with hF_def
  set Ctot : ℝ := blockVecDot p (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) p) +
      blockVecDot q (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) q) with hCtot_def
  have hFbound : ∀ omega : ShellSeq d, 2 * F omega ≤ (X1 omega + X2 omega + X3 omega) * Ctot :=
    fun omega => hQuenched omega p q
  have hFint : MeasureTheory.Integrable F P.toMeasure := by
    have heqF : F = fun omega =>
        (((descendantsAtDepth (originCube d (m : ℤ)) (m - n)).card : ℝ)⁻¹ *
            ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n),
              blockVecDot p (blockMatVecMul
                (coarseBlockMatrix (cubeSet R) (coefficientCutoff nu omega L).toCoeffField) q)) -
          blockVecDot p (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) q) :=
      funext fun omega => mixFin_avg_reassembled_eq nu omega ell L n m P p q
    rw [heqF]
    exact (mixFin_integrable_avg_coarseBlockMatrix hnu hPrefix hJ2 hJ3 hJ4 L n m p q).sub
      (MeasureTheory.integrable_const _)
  have hXsum_int : MeasureTheory.Integrable (fun omega => X1 omega + X2 omega + X3 omega) P.toMeasure :=
    mixFin_integrable_add' (mixFin_integrable_add' hInt1 hInt2) hInt3
  have hmono : ∫ omega : ShellSeq d, 2 * F omega ∂P.toMeasure ≤
      ∫ omega : ShellSeq d, (X1 omega + X2 omega + X3 omega) * Ctot ∂P.toMeasure :=
    MeasureTheory.integral_mono (hFint.const_mul 2) (hXsum_int.mul_const Ctot) hFbound
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const] at hmono
  have hFeq : ∫ omega : ShellSeq d, F omega ∂P.toMeasure =
      blockVecDot p (blockMatVecMul (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) q) -
        blockVecDot p (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) q) :=
    mixFin_integral_avg_reassembled_eq hnu hPrefix hJ2 hJ3 hJ4 ell L n m hnm p q
  rw [hFeq] at hmono
  have hsum3 : ∫ omega : ShellSeq d, (X1 omega + X2 omega + X3 omega) ∂P.toMeasure ≤
      gammaMomentConst 2 *
          (C * ((L - ell : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
            (sigmaBarStarScalar nu L P (cubeSet (originCube d (n : ℤ)))) ^ (-(1 : ℝ))) +
        gammaMomentConst 1 *
            (C * ((L - ell : ℕ) : ℝ) *
              (sigmaBarStarScalar nu L P (cubeSet (originCube d (n : ℤ)))) ^ (-(2 : ℝ))) +
        gammaMomentConst ((1 : ℝ) / 3) *
          (gammaTriangleConst ((1 : ℝ) / 3) * (2 * (C * (m : ℝ) ^ (-(5000 : ℝ))))) :=
    mixMain_integral_sum3_le_of_isBigO_gammaSigma (by norm_num) (by norm_num) (by norm_num)
      hA1pos hA2pos hA3pos hX1M.aemeasurable hX2M.aemeasurable hX3M.aemeasurable hX1O hX2O hX3O
      hInt1 hInt2 hInt3
  have hscaled : (∫ omega : ShellSeq d, (X1 omega + X2 omega + X3 omega) ∂P.toMeasure) * Ctot ≤
      (gammaMomentConst 2 *
            (C * ((L - ell : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
              (sigmaBarStarScalar nu L P (cubeSet (originCube d (n : ℤ)))) ^ (-(1 : ℝ))) +
          gammaMomentConst 1 *
              (C * ((L - ell : ℕ) : ℝ) *
                (sigmaBarStarScalar nu L P (cubeSet (originCube d (n : ℤ)))) ^ (-(2 : ℝ))) +
          gammaMomentConst ((1 : ℝ) / 3) *
            (gammaTriangleConst ((1 : ℝ) / 3) * (2 * (C * (m : ℝ) ^ (-(5000 : ℝ)))))) * Ctot :=
    mul_le_mul_of_nonneg_right hsum3 hCtot_nonneg
  linarith only [hmono, hscaled]
