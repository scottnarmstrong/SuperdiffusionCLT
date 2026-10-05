/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.BlockConcentrationInputs
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3StepsB

/-!
# The Hoelder-pair inputs of `e.RHS.term3.A`: the carrier `bHalfDiff`, the two
Cauchy-Schwarz steps, and the stationarity of the `b`-factor

The second block of inputs of the proof of `e.RHS.term3.A`.  After the two insertion
steps (`_hInsertCS` and `_hInsertDiff` of the reduction, carried in
`RHSTerm3OscCgB`), the printed proof consumes the Hoelder-pair display

`(E[avsum_{z,z'} |b_{L'}^{1/2}(z+cu_n)((∇w)_{z+cu_n} - (∇w)_{z'+cu_k})|²])^(1/2) ≤
  (E[avsum |(∇w)_{z+cu_n} - (∇w)_{z'+cu_k}|⁴])^(1/4) (E[|b_{L'}(cu_n)|²])^(1/4)`,

at the free binders `bHalfDiff` (the matrix square root of the coarse block
applied to the difference of the two cube averages) and `bNormSq` (the square
of the coarse-block norm).  This module proves that step at the carriers:

* `translatedBlockHalfWeightDiff` — the carrier `bHalfDiff`, the block at the
  *second* (small) cube applied to the difference of the two `∇w` cube
  averages, with its operator-norm bridge `translatedBlockHalfWeightDiff_le`
  (`|b^{1/2}x|² ≤ |b||x|²`, the analogue of `translatedBlockHalfWeight_le`).
* `integral_mul_le_rpow_mul_rpow`, `avsum_mul_le_sqrt_mul_sqrt`,
  `avsum_integral_mul_le_sqrt_mul_sqrt` — the two Cauchy-Schwarz steps
  (one Bochner integral, the finite average, and the two
  combined), at the Hoelder exponent pair `2, 2`.
* `integral_translatedBlockNorm_sq` — the stationarity of the second moment of
  the coarse-block norm across equal-scale translates (the squared-norm
  analogue of `integral_of_translationCovariant`).
* `memLp_two_translatedBlockNorm` — the `L²(P)` membership of the coarse-block
  norm, from its `Γ₁` envelope
  `isBigO_gammaSigma_translatedBlockNorm_envelope` read through the moment
  lemma `Homogenization.IndependentSums.hasGammaMomentGrowthWith_of_isBigO_gammaSigma`.
* `holderPair_translatedBlockHalfWeightDiff` — the Hoelder pair itself, the
  exact shape of the binder `_hHolderPair` at `bHalfDiff :=
  translatedBlockHalfWeightDiff` and `bNormSq omega := translatedBlockNorm
  omega zc ^ 2`: the carrier bound feeds the first Cauchy-Schwarz step, the
  second step reads the two averages, and the `b`-factor collapses to a single
  integral by stationarity.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open Homogenization
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal
open scoped MatrixOrder

noncomputable section

variable {d : ℕ}

/-! ## The carrier `bHalfDiff` and the operator-norm bridge -/

/-- **`|b_L^{1/2}(z + cu_n)((∇w)_{z+cu_n} - (∇w)_{z'+cu_k})|²`**, the carrier
`bHalfDiff` of the Hoelder-pair step of `e.RHS.term3.A`: the matrix square root
of the coarse block `b_L(z + cu_n)` at the *second* cube `z` applied to the
difference of the two `∇w` cube averages.  It is the analogue of the
carrier `translatedBlockHalfWeight` with the single cube average replaced by
the difference of the two. -/
def translatedBlockHalfWeightDiff (nu : ℝ) (L : ℕ) {U : Set (Vec d)}
    (w : ShellSeq d → H10Function U) (omega : ShellSeq d) (z' z : TriadicCube d) : ℝ :=
  vecNormSq (matVecMul (CFC.sqrt (translatedCoarseBlock nu L omega z))
    (volumeAverageVec (openCubeSet z) ((w omega).toH1Function.grad) -
      volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad)))

/-- The carrier is nonnegative. -/
theorem translatedBlockHalfWeightDiff_nonneg {nu : ℝ} (L : ℕ) {U : Set (Vec d)}
    (w : ShellSeq d → H10Function U) (omega : ShellSeq d) (z' z : TriadicCube d) :
    0 ≤ translatedBlockHalfWeightDiff nu L w omega z' z :=
  Homogenization.vecNormSq_nonneg (matVecMul (CFC.sqrt (translatedCoarseBlock nu L omega z))
    (volumeAverageVec (openCubeSet z) ((w omega).toH1Function.grad) -
      volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad)))

/-- **The operator-norm bridge for the difference carrier**: `|b^{1/2}x|² ≤
|b||x|²` — the analogue of `translatedBlockHalfWeight_le`, from the
quadratic-form bridge
`SuperdiffusionCLT.Section2.Localization.vecNormSq_sqrt_matVecMul_le`
through the positive semidefiniteness of the coarse block. -/
theorem translatedBlockHalfWeightDiff_le [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ)
    {U : Set (Vec d)} (w : ShellSeq d → H10Function U)
    (omega : ShellSeq d) (z' z : TriadicCube d) :
    translatedBlockHalfWeightDiff nu L w omega z' z ≤
      translatedBlockNorm nu L omega z *
        vecNormSq (volumeAverageVec (openCubeSet z) ((w omega).toH1Function.grad) -
          volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad)) := by
  show vecNormSq (matVecMul (CFC.sqrt (translatedCoarseBlock nu L omega z))
      (volumeAverageVec (openCubeSet z) ((w omega).toH1Function.grad) -
        volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad))) ≤
    Book.Ch02.matrixOperatorNorm (translatedCoarseBlock nu L omega z) *
      vecNormSq (volumeAverageVec (openCubeSet z) ((w omega).toH1Function.grad) -
        volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad))
  exact SuperdiffusionCLT.Section2.Localization.vecNormSq_sqrt_matVecMul_le
    (posSemidef_translatedCoarseBlock hnu L omega z) _

/-! ## The two Cauchy-Schwarz steps, in the square-root spelling -/

/-- Cauchy-Schwarz for one Bochner integral, at the exponent pair `2, 2`: for
nonnegative `A`, `B` in `L²`, `∫ A * B ≤ (∫ A²)^(1/2) (∫ B²)^(1/2)`. -/
theorem integral_mul_le_rpow_mul_rpow {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {A B : Omega → ℝ}
    (hAnn : ∀ omega, 0 ≤ A omega) (hBnn : ∀ omega, 0 ≤ B omega)
    (hA : MemLp A (ENNReal.ofReal (2 : ℝ)) mu)
    (hB : MemLp B (ENNReal.ofReal (2 : ℝ)) mu) :
    ∫ omega, A omega * B omega ∂mu ≤
      (∫ omega, A omega ^ (2 : ℝ) ∂mu) ^ ((1 : ℝ) / 2) *
        (∫ omega, B omega ^ (2 : ℝ) ∂mu) ^ ((1 : ℝ) / 2) := by
  have hconj : Real.HolderConjugate (2 : ℝ) (2 : ℝ) :=
    ⟨by norm_num, by norm_num, by norm_num⟩
  exact MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := mu) (f := A) (g := B) hconj
    (Filter.Eventually.of_forall hAnn) (Filter.Eventually.of_forall hBnn) hA hB

/-- Cauchy-Schwarz for the plain average over a finite family, in the
square-root spelling. -/
theorem avsum_mul_le_sqrt_mul_sqrt {iota : Type*} (s : Finset iota) (hs : s.Nonempty)
    (a b : iota → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    ((s.card : ℝ))⁻¹ * ∑ i ∈ s, a i ^ ((1 : ℝ) / 2) * b i ^ ((1 : ℝ) / 2) ≤
      (((s.card : ℝ))⁻¹ * ∑ i ∈ s, a i) ^ ((1 : ℝ) / 2) *
        (((s.card : ℝ))⁻¹ * ∑ i ∈ s, b i) ^ ((1 : ℝ) / 2) := by
  classical
  have hcard : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hs
  have hinvnn : (0 : ℝ) ≤ ((s.card : ℝ))⁻¹ := le_of_lt (inv_pos.2 hcard)
  have hconj : Real.HolderConjugate (2 : ℝ) (2 : ℝ) :=
    ⟨by norm_num, by norm_num, by norm_num⟩
  have hmain := Real.inner_le_Lp_mul_Lq_of_nonneg (s := s)
    (f := fun i => a i ^ ((1 : ℝ) / 2)) (g := fun i => b i ^ ((1 : ℝ) / 2)) hconj
    (fun i _ => Real.rpow_nonneg (ha i) _) (fun i _ => Real.rpow_nonneg (hb i) _)
  have hA : ∀ i : iota, (a i ^ ((1 : ℝ) / 2)) ^ (2 : ℝ) = a i := by
    intro i
    rw [← Real.rpow_mul (ha i)]
    norm_num
  have hB : ∀ i : iota, (b i ^ ((1 : ℝ) / 2)) ^ (2 : ℝ) = b i := by
    intro i
    rw [← Real.rpow_mul (hb i)]
    norm_num
  simp only [hA, hB] at hmain
  have hexp : (1 : ℝ) / (2 : ℝ) = (1 : ℝ) / 2 := rfl
  rw [hexp] at hmain
  have hsa : (0 : ℝ) ≤ ∑ i ∈ s, a i := Finset.sum_nonneg fun i _ => ha i
  have hsb : (0 : ℝ) ≤ ∑ i ∈ s, b i := Finset.sum_nonneg fun i _ => hb i
  have hstep := mul_le_mul_of_nonneg_left hmain hinvnn
  refine hstep.trans_eq ?_
  rw [Real.mul_rpow hinvnn hsa, Real.mul_rpow hinvnn hsb]
  have hsplit : ((s.card : ℝ))⁻¹ ^ ((1 : ℝ) / 2) * ((s.card : ℝ))⁻¹ ^ ((1 : ℝ) / 2) =
      ((s.card : ℝ))⁻¹ := by
    rw [← Real.rpow_add (inv_pos.2 hcard)]
    norm_num
  calc ((s.card : ℝ))⁻¹ * ((∑ i ∈ s, a i) ^ ((1 : ℝ) / 2) * (∑ i ∈ s, b i) ^ ((1 : ℝ) / 2))
      = (((s.card : ℝ))⁻¹ ^ ((1 : ℝ) / 2) * ((s.card : ℝ))⁻¹ ^ ((1 : ℝ) / 2)) *
        ((∑ i ∈ s, a i) ^ ((1 : ℝ) / 2) * (∑ i ∈ s, b i) ^ ((1 : ℝ) / 2)) := by
        rw [hsplit]
    _ = ((s.card : ℝ))⁻¹ ^ ((1 : ℝ) / 2) * (∑ i ∈ s, a i) ^ ((1 : ℝ) / 2) *
        (((s.card : ℝ))⁻¹ ^ ((1 : ℝ) / 2) * (∑ i ∈ s, b i) ^ ((1 : ℝ) / 2)) := by
        ring

/-- The two Cauchy-Schwarz steps combined: over the finite family and the
measure space at once. -/
theorem avsum_integral_mul_le_sqrt_mul_sqrt {iota : Type*} (s : Finset iota)
    (hs : s.Nonempty) {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    (f g : iota → Omega → ℝ)
    (hf : ∀ i omega, 0 ≤ f i omega) (hg : ∀ i omega, 0 ≤ g i omega)
    (hMf : ∀ i ∈ s, MemLp (f i) (ENNReal.ofReal (2 : ℝ)) mu)
    (hMg : ∀ i ∈ s, MemLp (g i) (ENNReal.ofReal (2 : ℝ)) mu) :
    ((s.card : ℝ))⁻¹ * ∑ i ∈ s, ∫ omega, f i omega * g i omega ∂mu ≤
      (((s.card : ℝ))⁻¹ * ∑ i ∈ s, ∫ omega, f i omega ^ (2 : ℝ) ∂mu) ^ ((1 : ℝ) / 2) *
        (((s.card : ℝ))⁻¹ * ∑ i ∈ s, ∫ omega, g i omega ^ (2 : ℝ) ∂mu) ^ ((1 : ℝ) / 2) := by
  classical
  have hinvnn : (0 : ℝ) ≤ ((s.card : ℝ))⁻¹ := inv_nonneg.2 (Nat.cast_nonneg (s.card))
  calc ((s.card : ℝ))⁻¹ * ∑ i ∈ s, ∫ omega, f i omega * g i omega ∂mu
      ≤ ((s.card : ℝ))⁻¹ * ∑ i ∈ s,
          (∫ omega, f i omega ^ (2 : ℝ) ∂mu) ^ ((1 : ℝ) / 2) *
            (∫ omega, g i omega ^ (2 : ℝ) ∂mu) ^ ((1 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun i hi =>
            integral_mul_le_rpow_mul_rpow
              (fun omega => hf i omega) (fun omega => hg i omega) (hMf i hi) (hMg i hi))
          hinvnn
    _ ≤ (((s.card : ℝ))⁻¹ * ∑ i ∈ s, ∫ omega, f i omega ^ (2 : ℝ) ∂mu) ^ ((1 : ℝ) / 2) *
        (((s.card : ℝ))⁻¹ * ∑ i ∈ s, ∫ omega, g i omega ^ (2 : ℝ) ∂mu) ^ ((1 : ℝ) / 2) :=
        avsum_mul_le_sqrt_mul_sqrt s hs
          (fun i => ∫ omega, f i omega ^ (2 : ℝ) ∂mu)
          (fun i => ∫ omega, g i omega ^ (2 : ℝ) ∂mu)
          (fun i => MeasureTheory.integral_nonneg fun omega =>
            Real.rpow_nonneg (hf i omega) (2 : ℝ))
          (fun i => MeasureTheory.integral_nonneg fun omega =>
            Real.rpow_nonneg (hg i omega) (2 : ℝ))

/-- The dominance corollary of the two Cauchy-Schwarz steps: a carrier
pointwise dominated by `g i * h i` inherits the product estimate. -/
theorem avsum_integral_le_sqrt_sqrt_mul_sqrt_sqrt {iota : Type*} (s : Finset iota)
    (hs : s.Nonempty) {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {f g h : iota → Omega → ℝ}
    (hdom : ∀ i ∈ s, ∫ omega, f i omega ∂mu ≤ ∫ omega, g i omega * h i omega ∂mu)
    (hMg : ∀ i ∈ s, MemLp (g i) (ENNReal.ofReal (2 : ℝ)) mu)
    (hMh : ∀ i ∈ s, MemLp (h i) (ENNReal.ofReal (2 : ℝ)) mu)
    (hg : ∀ i omega, 0 ≤ g i omega) (hh : ∀ i omega, 0 ≤ h i omega) :
    ((s.card : ℝ))⁻¹ * ∑ i ∈ s, ∫ omega, f i omega ∂mu ≤
      (((s.card : ℝ))⁻¹ * ∑ i ∈ s, ∫ omega, g i omega ^ (2 : ℝ) ∂mu) ^ ((1 : ℝ) / 2) *
        (((s.card : ℝ))⁻¹ * ∑ i ∈ s, ∫ omega, h i omega ^ (2 : ℝ) ∂mu) ^ ((1 : ℝ) / 2) := by
  classical
  have hinvnn : (0 : ℝ) ≤ ((s.card : ℝ))⁻¹ := inv_nonneg.2 (Nat.cast_nonneg (s.card))
  refine (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => hdom i hi) hinvnn).trans ?_
  exact avsum_integral_mul_le_sqrt_mul_sqrt s hs g h
    (fun i omega => hg i omega) (fun i omega => hh i omega) hMg hMh

/-! ## Stationarity of the second moment of the coarse block -/

/-- The squared coarse-block norm is measurable in the shell sequence. -/
theorem measurable_translatedBlockNorm_sq [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ)
    (z : TriadicCube d) :
    Measurable fun omega : ShellSeq d => translatedBlockNorm nu L omega z ^ (2 : ℝ) :=
  (Real.continuous_rpow_const (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)).measurable.comp
    (measurable_translatedBlockNorm hnu L z)

/-- The squared coarse-block norm is translation covariant: the pointwise
companion of `translatedBlockNorm_eq_originCube`. -/
theorem translatedBlockNorm_sq_covariant (nu : ℝ) (L : ℕ) (omega : ShellSeq d)
    (Q : TriadicCube d) :
    translatedBlockNorm nu L omega Q ^ (2 : ℝ) =
      translatedBlockNorm nu L
        (ShellField.translateSequence (triadicCubeShift Q) omega)
        (originCube d Q.scale) ^ (2 : ℝ) := by
  rw [translatedBlockNorm_eq_originCube (nu := nu) (L := L) (omega := omega) (Q := Q)]

/-- The annealed second moment of `|b_L|` on a cube equals its second moment on
the origin cube of the same scale, through the measure-preserving shell
translation (`integral_translateObservable_eq`). -/
theorem integral_translatedBlockNorm_sq_originCube [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (L : ℕ) (Q : TriadicCube d) :
    ∫ omega : ShellSeq d, translatedBlockNorm nu L omega Q ^ (2 : ℝ) ∂P.toMeasure =
      ∫ omega : ShellSeq d,
        translatedBlockNorm nu L omega (originCube d Q.scale) ^ (2 : ℝ) ∂P.toMeasure := by
  have hYmeas : AEStronglyMeasurable
      (fun omega : ShellSeq d =>
        translatedBlockNorm nu L omega (originCube d Q.scale) ^ (2 : ℝ)) P.toMeasure :=
    (measurable_translatedBlockNorm_sq hnu L (originCube d Q.scale)).aestronglyMeasurable
  have heq : (fun omega : ShellSeq d => translatedBlockNorm nu L omega Q ^ (2 : ℝ)) =
      translateObservable (fun omega : ShellSeq d =>
        translatedBlockNorm nu L omega (originCube d Q.scale) ^ (2 : ℝ)) Q := by
    funext omega
    show translatedBlockNorm nu L omega Q ^ (2 : ℝ) =
      translatedBlockNorm nu L
        (ShellField.translateSequence (triadicCubeShift Q) omega)
        (originCube d Q.scale) ^ (2 : ℝ)
    exact translatedBlockNorm_sq_covariant nu L omega Q
  rw [heq]
  exact integral_translateObservable_eq hPrefix hJ2 hYmeas Q

/-- **The second moment of the coarse-block norm does not depend on the
translate**: for equal-scale cubes the annealed second moment of `|b_L|` is the
same integral, through the stationarity of the carrier
(`translatedBlockNorm_eq_originCube`) and the measure-preserving shell
translation. -/
theorem integral_translatedBlockNorm_sq [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (L : ℕ) {z Q : TriadicCube d}
    (hQ : Q.scale = z.scale) :
    ∫ omega : ShellSeq d, translatedBlockNorm nu L omega Q ^ (2 : ℝ) ∂P.toMeasure =
      ∫ omega : ShellSeq d, translatedBlockNorm nu L omega z ^ (2 : ℝ) ∂P.toMeasure := by
  have h1 : ∫ omega : ShellSeq d, translatedBlockNorm nu L omega Q ^ (2 : ℝ)
        ∂P.toMeasure =
      ∫ omega : ShellSeq d,
        translatedBlockNorm nu L omega (originCube d z.scale) ^ (2 : ℝ) ∂P.toMeasure := by
    rw [integral_translatedBlockNorm_sq_originCube hnu hPrefix hJ2 L Q, hQ]
  have h2 : ∫ omega : ShellSeq d, translatedBlockNorm nu L omega z ^ (2 : ℝ)
        ∂P.toMeasure =
      ∫ omega : ShellSeq d,
        translatedBlockNorm nu L omega (originCube d z.scale) ^ (2 : ℝ) ∂P.toMeasure :=
    integral_translatedBlockNorm_sq_originCube hnu hPrefix hJ2 L z
  exact h1.trans h2.symm

/-- **The coarse block norm is in `L²(P)`** on every translated cube: the
`Γ₁` envelope `isBigO_gammaSigma_translatedBlockNorm_envelope` read at
the exponent `2` through the moment lemma
`Homogenization.IndependentSums.hasGammaMomentGrowthWith_of_isBigO_gammaSigma`. -/
theorem memLp_two_translatedBlockNorm_core [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (L : ℕ) (z : TriadicCube d) :
    MemLp (fun omega : ShellSeq d => translatedBlockNorm nu L omega z) 2 P.toMeasure := by
  have hK : (0 : ℝ) < envelopeUpperScalar d nu L :=
    SuperdiffusionCLT.Section2.Annealed.envelopeUpperScalar_pos hnu d L
  have hbig := isBigO_gammaSigma_translatedBlockNorm_envelope hnu hPrefix hJ2 hJ3 hJ4 L z
  have hgrowth := Homogenization.IndependentSums.hasGammaMomentGrowthWith_of_isBigO_gammaSigma
    (μ := P.toMeasure) (show (0 : ℝ) < 1 by norm_num) hK
    (measurable_translatedBlockNorm hnu L z).aemeasurable hbig
  obtain ⟨hint, -⟩ := hgrowth (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)
  have hint' : Integrable (fun omega : ShellSeq d =>
      translatedBlockNorm nu L omega z ^ (2 : ℕ)) P.toMeasure := by
    refine hint.congr (Filter.Eventually.of_forall fun omega => ?_)
    show |translatedBlockNorm nu L omega z| ^ ((2 : ℕ) : ℝ) =
      translatedBlockNorm nu L omega z ^ (2 : ℕ)
    have hznn : (0 : ℝ) ≤ translatedBlockNorm nu L omega z :=
      Homogenization.Book.Ch02.matrixOperatorNorm_nonneg _
    rw [Real.rpow_natCast, abs_of_nonneg hznn]
  exact (MeasureTheory.memLp_two_iff_integrable_sq
    (measurable_translatedBlockNorm hnu L z).aestronglyMeasurable).2 hint'

/-- The `L²(P)` membership at the `ENNReal.ofReal` exponent `2`, the form the
Cauchy-Schwarz steps and the binder idiom of the reduction read. -/
theorem memLp_two_translatedBlockNorm [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (L : ℕ) (z : TriadicCube d) :
    MemLp (fun omega : ShellSeq d => translatedBlockNorm nu L omega z)
      (ENNReal.ofReal (2 : ℝ)) P.toMeasure := by
  simpa using memLp_two_translatedBlockNorm_core hnu hPrefix hJ2 hJ3 hJ4 L z

/-! ## The Hoelder pair of `e.RHS.term3.A` -/

/-- The `MemLp` exponent bridge: `ENNReal.ofReal 2` is the exponent `2`. -/
private theorem memLp_ofReal_two {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {f : Omega → ℝ} (h : MemLp f (ENNReal.ofReal (2 : ℝ)) mu) :
    MemLp f 2 mu := by simpa using h

/-- The exponent half-step: a domination of `A` by the product of the square
roots of two nonnegative observables gives the domination at the fourth roots. -/
private theorem sqrt_le_quarter_mul_quarter {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hC : 0 ≤ C) (h : A ≤ B ^ ((1 : ℝ) / 2) * C ^ ((1 : ℝ) / 2)) :
    A ^ ((1 : ℝ) / 2) ≤ B ^ ((1 : ℝ) / 4) * C ^ ((1 : ℝ) / 4) := by
  have hexp2 : ((1 : ℝ) / 2) * ((1 : ℝ) / 2) = (1 : ℝ) / 4 := by norm_num
  have hrpow := Real.rpow_le_rpow hA h (show (0 : ℝ) ≤ (1 : ℝ) / 2 by norm_num)
  have hkey : (B ^ ((1 : ℝ) / 2) * C ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / 2)
      = B ^ ((1 : ℝ) / 4) * C ^ ((1 : ℝ) / 4) := by
    rw [← Real.mul_rpow (z := (1 : ℝ) / 2) hB hC,
      ← Real.rpow_mul (mul_nonneg hB hC) ((1 : ℝ) / 2) ((1 : ℝ) / 2), hexp2,
      Real.mul_rpow (z := (1 : ℝ) / 4) hB hC]
  exact hrpow.trans_eq hkey

/-- The integral-domination step of the Hoelder pair: the carrier
`translatedBlockHalfWeightDiff` is dominated by the product of the difference
carrier and the coarse-block norm, so its integral is dominated by theirs. -/
theorem integral_translatedBlockHalfWeightDiff_le [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (L : ℕ) {U : Set (Vec d)}
    {P : ProbabilityMeasure (ShellSeq d)} (w : ShellSeq d → H10Function U)
    {z' z : TriadicCube d}
    (hMemD : MemLp (fun omega : ShellSeq d =>
        vecNormSq (volumeAverageVec (openCubeSet z) ((w omega).toH1Function.grad) -
            volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad)))
      (ENNReal.ofReal (2 : ℝ)) P.toMeasure)
    (hMemb : MemLp (fun omega : ShellSeq d => translatedBlockNorm nu L omega z)
      (ENNReal.ofReal (2 : ℝ)) P.toMeasure)
    (hXmeas : AEMeasurable (fun omega : ShellSeq d =>
        translatedBlockHalfWeightDiff nu L w omega z' z) P.toMeasure) :
    Integrable (fun omega : ShellSeq d => translatedBlockHalfWeightDiff nu L w omega z' z)
      P.toMeasure ∧
    ∫ omega : ShellSeq d, translatedBlockHalfWeightDiff nu L w omega z' z ∂P.toMeasure ≤
      ∫ omega : ShellSeq d,
        vecNormSq (volumeAverageVec (openCubeSet z) ((w omega).toH1Function.grad) -
            volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad)) *
          translatedBlockNorm nu L omega z ∂P.toMeasure := by
  have hprodint : Integrable (fun omega : ShellSeq d =>
      vecNormSq (volumeAverageVec (openCubeSet z) ((w omega).toH1Function.grad) -
          volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad)) *
        translatedBlockNorm nu L omega z) P.toMeasure :=
    (memLp_ofReal_two hMemD).integrable_mul (memLp_ofReal_two hMemb)
  have hdom : ∀ omega : ShellSeq d, translatedBlockHalfWeightDiff nu L w omega z' z ≤
      vecNormSq (volumeAverageVec (openCubeSet z) ((w omega).toH1Function.grad) -
          volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad)) *
        translatedBlockNorm nu L omega z := fun omega =>
    (translatedBlockHalfWeightDiff_le hnu L w omega z' z).trans_eq
      (mul_comm (translatedBlockNorm nu L omega z)
        (vecNormSq (volumeAverageVec (openCubeSet z) ((w omega).toH1Function.grad) -
          volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad))))
  have hintX : Integrable (fun omega : ShellSeq d =>
      translatedBlockHalfWeightDiff nu L w omega z' z) P.toMeasure := by
    refine Integrable.mono' hprodint hXmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun omega => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (translatedBlockHalfWeightDiff_nonneg L w omega z' z)]
    exact hdom omega
  exact ⟨hintX, MeasureTheory.integral_mono hintX hprodint hdom⟩

/-- **The Hoelder pair of `e.RHS.term3.A`**, the exact shape of the
binder `_hHolderPair` of the reduction at the carriers
`bHalfDiff := translatedBlockHalfWeightDiff` and
`bNormSq omega := translatedBlockNorm omega zc ^ 2`:

`(avsum_{z,z'} ∫ |b^{1/2}((∇w)_z - (∇w)_{z'})|²)^(1/2) ≤
  (avsum ∫ |(∇w)_z - (∇w)_{z'}|⁴)^(1/4) (∫ |b_{L'}(cu_n)|²)^(1/4)`.

The carrier bound `translatedBlockHalfWeightDiff_le` feeds the first
Cauchy-Schwarz step (`avsum_integral_le_sqrt_sqrt_mul_sqrt_sqrt`), the second
step is the exponent-pair `2, 2` Hölder, and the `b`-factor collapses to a
single integral by the stationarity
`integral_translatedBlockNorm_sq` (every second member of the double lattice
has scale `n`, the scale of `zc`).  The measurability inputs on the `∇w` side
are standing hypotheses, matching the binder idiom of the reduction. -/
theorem holderPair_translatedBlockHalfWeightDiff [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (L : ℕ) {U : Set (Vec d)} (w : ShellSeq d → H10Function U)
    {n k m : ℕ} (hnk : n ≤ k) (hkm : k ≤ m) {zc : TriadicCube d}
    (hzc : zc.scale = ((n : ℕ) : ℤ))
    (hMemDiff : ∀ q ∈ coarsePairs d n k m,
      MemLp (fun omega : ShellSeq d =>
        vecNormSq (volumeAverageVec (openCubeSet q.2) ((w omega).toH1Function.grad) -
            volumeAverageVec (openCubeSet q.1) ((w omega).toH1Function.grad)))
        (ENNReal.ofReal (2 : ℝ)) P.toMeasure)
    (hXmeas : ∀ q ∈ coarsePairs d n k m,
      AEMeasurable (fun omega : ShellSeq d =>
        translatedBlockHalfWeightDiff nu L w omega q.1 q.2) P.toMeasure) :
    (((coarsePairs d n k m).card : ℝ)⁻¹ *
        ∑ q ∈ coarsePairs d n k m,
          ∫ omega : ShellSeq d, translatedBlockHalfWeightDiff nu L w omega q.1 q.2
            ∂P.toMeasure) ^ ((1 : ℝ) / 2) ≤
      (((coarsePairs d n k m).card : ℝ)⁻¹ * ∑ q ∈ coarsePairs d n k m,
          ∫ omega : ShellSeq d,
            vecNormSq (volumeAverageVec (openCubeSet q.2) ((w omega).toH1Function.grad) -
                volumeAverageVec (openCubeSet q.1) ((w omega).toH1Function.grad)) ^ (2 : ℝ)
            ∂P.toMeasure) ^ ((1 : ℝ) / 4) *
        (∫ omega : ShellSeq d, translatedBlockNorm nu L omega zc ^ (2 : ℝ)
          ∂P.toMeasure) ^ ((1 : ℝ) / 4) := by
  classical
  -- the `b`-factor: stationarity collapses the average to a single integral
  have hBavg : ((coarsePairs d n k m).card : ℝ)⁻¹ *
      ∑ q ∈ coarsePairs d n k m,
        ∫ omega : ShellSeq d, translatedBlockNorm nu L omega q.2 ^ (2 : ℝ)
          ∂P.toMeasure
      = ∫ omega : ShellSeq d, translatedBlockNorm nu L omega zc ^ (2 : ℝ)
          ∂P.toMeasure := by
    rw [avsum_coarsePairs_snd hnk hkm
      (fun z => ∫ omega : ShellSeq d, translatedBlockNorm nu L omega z ^ (2 : ℝ)
        ∂P.toMeasure)]
    have hconst : ∀ z ∈ largeCubeSubcubes d n m,
        ∫ omega : ShellSeq d, translatedBlockNorm nu L omega z ^ (2 : ℝ) ∂P.toMeasure
        = ∫ omega : ShellSeq d, translatedBlockNorm nu L omega zc ^ (2 : ℝ)
            ∂P.toMeasure := fun z hz =>
      integral_translatedBlockNorm_sq hnu hPrefix hJ2 L
        ((SuperdiffusionCLT.Section2.Estimates.Stream.scale_of_mem_largeCubeSubcubes
          (le_trans hnk hkm) hz).trans hzc.symm)
    have hcard : ((largeCubeSubcubes d n m).card : ℝ) ≠ 0 :=
      by exact_mod_cast ne_of_gt (Finset.card_pos.2 (largeCubeSubcubes_nonempty d n m))
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ hcard, one_mul]
  -- the two Cauchy-Schwarz steps, at the double lattice
  have hmain := avsum_integral_le_sqrt_sqrt_mul_sqrt_sqrt
    (s := coarsePairs d n k m) (mu := P.toMeasure)
    (f := fun q omega => translatedBlockHalfWeightDiff nu L w omega q.1 q.2)
    (g := fun q omega =>
      vecNormSq (volumeAverageVec (openCubeSet q.2) ((w omega).toH1Function.grad) -
        volumeAverageVec (openCubeSet q.1) ((w omega).toH1Function.grad)))
    (h := fun q omega => translatedBlockNorm nu L omega q.2)
    (coarsePairs_nonempty d n k m)
    (fun q hq =>
      (integral_translatedBlockHalfWeightDiff_le hnu L w
        (z := q.2) (z' := q.1) (hMemDiff q hq)
        (memLp_two_translatedBlockNorm hnu hPrefix hJ2 hJ3 hJ4 L q.2)
        (hXmeas q hq)).2)
    hMemDiff
    (fun q _ => memLp_two_translatedBlockNorm hnu hPrefix hJ2 hJ3 hJ4 L q.2)
    (fun i omega => Homogenization.vecNormSq_nonneg
      (volumeAverageVec (openCubeSet i.2) ((w omega).toH1Function.grad) -
        volumeAverageVec (openCubeSet i.1) ((w omega).toH1Function.grad)))
    (fun i omega => Homogenization.Book.Ch02.matrixOperatorNorm_nonneg
      (translatedCoarseBlock nu L omega i.2))
  -- the three averages are nonnegative
  have hXnn2 : (0 : ℝ) ≤ ((coarsePairs d n k m).card : ℝ)⁻¹ *
      ∑ q ∈ coarsePairs d n k m,
        ∫ omega : ShellSeq d, translatedBlockHalfWeightDiff nu L w omega q.1 q.2
          ∂P.toMeasure := by
    refine mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (Finset.sum_nonneg fun q hq => ?_)
    exact MeasureTheory.integral_nonneg fun omega =>
      translatedBlockHalfWeightDiff_nonneg L w omega q.1 q.2
  have hDnn2 : (0 : ℝ) ≤ ((coarsePairs d n k m).card : ℝ)⁻¹ *
      ∑ q ∈ coarsePairs d n k m,
        ∫ omega : ShellSeq d,
          vecNormSq (volumeAverageVec (openCubeSet q.2) ((w omega).toH1Function.grad) -
              volumeAverageVec (openCubeSet q.1) ((w omega).toH1Function.grad)) ^ (2 : ℝ)
          ∂P.toMeasure := by
    refine mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (Finset.sum_nonneg fun q hq => ?_)
    exact MeasureTheory.integral_nonneg fun omega =>
      Real.rpow_nonneg (Homogenization.vecNormSq_nonneg
        (volumeAverageVec (openCubeSet q.2) ((w omega).toH1Function.grad) -
          volumeAverageVec (openCubeSet q.1) ((w omega).toH1Function.grad))) (2 : ℝ)
  have hBnn2 : (0 : ℝ) ≤ ((coarsePairs d n k m).card : ℝ)⁻¹ *
      ∑ q ∈ coarsePairs d n k m,
        ∫ omega : ShellSeq d, translatedBlockNorm nu L omega q.2 ^ (2 : ℝ)
          ∂P.toMeasure := by
    refine mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (Finset.sum_nonneg fun q hq => ?_)
    exact MeasureTheory.integral_nonneg fun omega =>
      Real.rpow_nonneg (Homogenization.Book.Ch02.matrixOperatorNorm_nonneg
        (translatedCoarseBlock nu L omega q.2)) (2 : ℝ)
  -- the exponent half-step and the stationarity of the `b`-factor
  have hstep := sqrt_le_quarter_mul_quarter hXnn2 hDnn2 hBnn2 hmain
  rw [← hBavg]
  exact hstep

end

end SuperdiffusionCLT.Section3.Terms