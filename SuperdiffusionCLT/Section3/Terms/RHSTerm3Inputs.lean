/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.TranslatedBlocks
public import SuperdiffusionCLT.Section3.Setup.CrudeBounds
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3StepsD

/-!
# The carriers of `l.RHS.term3#averaged-quadratic-tail` and its one-sided input

Step 3 of the proof of `e.RHS.term3`.  `averaged_quadratic_tail`
(`RHSTerm3StepsD`) is stated for two free real-valued
binders `quad` and `streamSq`, because the quenched objects it reads live on the
translated cubes `z + cu_n`.  This module supplies the two carriers and
discharges the hypotheses of that step which can be reached.

## The carriers

The printed quantity averaged in the proof is

`(k_ℓ − k_{L'})_{z+cu_n}ᵗ σ_{L',*}^{-1}(z+cu_n) (k_ℓ − k_{L'})_{z+cu_n}`,

the quadratic form of the coarse matrix `σ_{L',*}^{-1}` on the translated cube
at the coarse average of the stream increment.  Tested at the unit direction
`e` of `e.Sec3.p.q.def` this is the scalar

* `translatedStreamQuadForm`, `quad_z = v · σ_{L',*}^{-1}(z+cu_n) v`, and
* `translatedStreamNormSq`, `streamSq_z = |v|²`,

with `v = (k_ℓ − k_{L'})_{z+cu_n} e` the
`streamIncrementCubeVec`, whose translation covariance is
`volumeAverageMat_cubeSet_finiteShellIncrement_translate` and whose coarse
matrix is `sigmaStarInvCoarse` on `cubeSet z`, the carrier in which
`mixing_minscale_onesided_translated` states the transported Loewner bound.

## What is discharged

* `hquadNonneg`, `hstreamNonneg`, `hquadMeas`, `hstreamMeas`, `hXmeas`: the
  positive semidefiniteness of `σ_{L',*}^{-1}` on a triadic cube and the
  measurability of the two carriers, both proved.
* `hOneSided` **and** `hXtail`: the one-sided part `e.sstarL.quenched.lb` of
  `l.mixing.minscale`, transported to the translate by
  `mixing_minscale_onesided_translated` and *tested* at `v`.  This is the step
  the paper performs in the sentence "the one-sided part of
  Lemma `l.mixing.minscale`, applied on each translate with local lower scale
  `m − 2h` and local cube scale `n`"; the conclusion of the statement
  `sigmaStarInv_mixing_minscale` on `cu_n`
  enters as an explicit hypothesis in its exact shape.
* `hStreamTail`: the `Γ₁` envelope of `translatedStreamNormSq`, transported from `cu_n` to
  every translate by `isBigO_gammaSigma_of_translationCovariant`.  Its value on
  `cu_n` is the balanced part `e.refined.localization.twoo` of the same
  statement and stays an explicit hypothesis, for the reason recorded in the
  docstring of `isBigO_gammaSigma_translatedStreamNormSq`.

## References

* `Frozen/Section2/MixingMinscale.lean` (`sigmaStarInv_mixing_minscale`).
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
open SuperdiffusionCLT.Section3.Setup

noncomputable section

variable {d : ℕ}

/-! ## The half-open and the open realization of the coarse matrix -/

/-- The half-open and the open realization of a triadic cube give the same
coarse matrix `s_{L,*}^{-1}`.  Both entry formulas of `sigmaStarInvCoarse` are
values of `ResponseJ` at the two cubes, and those agree by
`responseJ_cubeSet_eq_openCubeSet_of_triadicCube`; no ellipticity or coarse
data is needed.  This is the bridge between the carrier in which
`l.mixing.minscale` is stated (`cubeSet`) and the carrier in which the Chapter 2
positivity and the measurability engine work (`openCubeSet`). -/
theorem sigmaStarInvCoarse_cubeSet_eq_openCubeSet [NeZero d] (Q : TriadicCube d)
    (a : CoeffField d) :
    sigmaStarInvCoarse (cubeSet Q) a = sigmaStarInvCoarse (openCubeSet Q) a := by
  funext i j
  by_cases h : i = j
  · subst h
    rw [sigmaStarInvCoarse_apply_same, sigmaStarInvCoarse_apply_same,
      responseJ_cubeSet_eq_openCubeSet_of_triadicCube]
  · rw [sigmaStarInvCoarse_apply_of_ne _ _ h, sigmaStarInvCoarse_apply_of_ne _ _ h,
      responseJ_cubeSet_eq_openCubeSet_of_triadicCube,
      responseJ_cubeSet_eq_openCubeSet_of_triadicCube,
      responseJ_cubeSet_eq_openCubeSet_of_triadicCube]

/-- **`s_{L,*}^{-1}(z + cu_n)` is positive semidefinite.**  On the open cube this
is the Chapter 2 `sigmaStarInvCoarse_posDef` at the coefficient object of the
cutoff field, which the unconditional admissibility `l.ell.adm` supplies; the
half-open spelling follows by `sigmaStarInvCoarse_cubeSet_eq_openCubeSet`. -/
theorem posSemidef_sigmaStarInvCoarse_cutoffCube [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (L : ℕ) (omega : ShellSeq d) (Q : TriadicCube d) :
    (sigmaStarInvCoarse (cubeSet Q)
      (coefficientCutoff nu omega L).toCoeffField).PosSemidef := by
  rw [sigmaStarInvCoarse_cubeSet_eq_openCubeSet]
  have h := Book.Ch02.sigmaStarInvCoarse_posDef (Book.Ch02.cubeDomain Q)
    ((Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
      (coefficientCutoff nu omega L)
      (aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega L)).coeffOn Q)
  rw [← SuperdiffusionCLT.Section2.CoarseGraining.sigmaStarInvCoarse_toCoeffField,
    Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField_coeffOn_toCoeffField,
    Book.Ch02.cubeDomain_coe] at h
  exact h.posSemidef

/-! ## Elementary matrix-vector algebra -/

private theorem matVecMul_add_mat (A B : Mat d) (x : Vec d) :
    matVecMul (A + B) x = matVecMul A x + matVecMul B x := by
  funext i
  simp only [matVecMul, Matrix.add_apply, Pi.add_apply, add_mul]
  exact Finset.sum_add_distrib

private theorem vecDot_add_right (x y z : Vec d) :
    vecDot x (y + z) = vecDot x y + vecDot x z := by
  simp only [vecDot, Pi.add_apply, mul_add]
  exact Finset.sum_add_distrib

private theorem measurable_matVecMul_apply {Omega : Type*} [MeasurableSpace Omega]
    {M : Omega → Mat d} (hM : ∀ i j, Measurable fun omega => M omega i j)
    (x : Vec d) (i : Fin d) :
    Measurable fun omega => matVecMul (M omega) x i := by
  simp only [matVecMul]
  exact Finset.measurable_sum _ fun j _ => (hM i j).mul measurable_const

private theorem measurable_vecDot_matVecMul {Omega : Type*} [MeasurableSpace Omega]
    {M : Omega → Mat d} {v : Omega → Vec d}
    (hM : ∀ i j, Measurable fun omega => M omega i j)
    (hv : ∀ i, Measurable fun omega => v omega i) :
    Measurable fun omega => vecDot (v omega) (matVecMul (M omega) (v omega)) := by
  simp only [vecDot, matVecMul]
  exact Finset.measurable_sum _ fun i _ =>
    (hv i).mul (Finset.measurable_sum _ fun j _ => (hM i j).mul (hv j))

private theorem measurable_vecNormSq_of_apply {Omega : Type*} [MeasurableSpace Omega]
    {v : Omega → Vec d} (hv : ∀ i, Measurable fun omega => v omega i) :
    Measurable fun omega => vecNormSq (v omega) := by
  simp only [vecNormSq, vecDot]
  exact Finset.measurable_sum _ fun i _ => (hv i).mul (hv i)

/-! ## The carriers `translatedStreamQuadForm` and `translatedStreamNormSq` -/

/-- **`(k_l − k_L)_{z + cu_n} e`**, the coarse average of the finite stream
increment on the translated cube `z + cu_n` applied to the direction `e`.  This
is the vector the quadratic form of `s_{L,*}^{-1}(z + cu_n)` is tested at in the
printed display. -/
def streamIncrementCubeVec (l L : ℕ) (e : Vec d) (omega : ShellSeq d)
    (z : TriadicCube d) : Vec d :=
  matVecMul (volumeAverageMat (cubeSet z) (fun y => finiteShellIncrement omega l L y)) e

/-- **`translatedStreamQuadForm`**, the carrier of the free binder `quad` of
`averaged_quadratic_tail`: the quadratic form of the coarse matrix
`s_{L,*}^{-1}(z + cu_n)` at `(k_l − k_L)_{z+cu_n} e`. -/
def translatedStreamQuadForm (nu : ℝ) (l L : ℕ) (e : Vec d) (omega : ShellSeq d)
    (z : TriadicCube d) : ℝ :=
  vecDot (streamIncrementCubeVec l L e omega z)
    (matVecMul (sigmaStarInvCoarse (cubeSet z) (coefficientCutoff nu omega L).toCoeffField)
      (streamIncrementCubeVec l L e omega z))

/-- **`translatedStreamNormSq`**, the carrier of the free binder `streamSq` of
`averaged_quadratic_tail`: the squared norm of `(k_l − k_L)_{z+cu_n} e`. -/
def translatedStreamNormSq (l L : ℕ) (e : Vec d) (omega : ShellSeq d)
    (z : TriadicCube d) : ℝ :=
  vecNormSq (streamIncrementCubeVec l L e omega z)

/-- **`X_z`**, the carrier of the free binder `Xdev` of
`averaged_quadratic_tail`: the `Γ₂` deviation of the one-sided part of
`l.mixing.minscale` read on the translated cube, i.e. the deviation on `cu_n`
evaluated at the translated shell sequence. -/
def translatedDeviation (X : ShellSeq d → ℝ) (omega : ShellSeq d)
    (z : TriadicCube d) : ℝ :=
  translateObservable X z omega

/-! ## Sign and measurability -/

theorem translatedStreamNormSq_nonneg (l L : ℕ) (e : Vec d) (omega : ShellSeq d)
    (z : TriadicCube d) : 0 ≤ translatedStreamNormSq l L e omega z :=
  vecNormSq_nonneg _

/-- **`0 ≤ quad_z`**, the hypothesis `hquadNonneg` of `averaged_quadratic_tail`:
the coarse matrix `s_{L,*}^{-1}(z + cu_n)` is positive semidefinite. -/
theorem translatedStreamQuadForm_nonneg [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (l L : ℕ) (e : Vec d) (omega : ShellSeq d) (z : TriadicCube d) :
    0 ≤ translatedStreamQuadForm nu l L e omega z := by
  have h := (posSemidef_sigmaStarInvCoarse_cutoffCube hnu L omega z).dotProduct_mulVec_nonneg
    (streamIncrementCubeVec l L e omega z)
  simpa only [translatedStreamQuadForm, dotProduct, Matrix.mulVec, vecDot, matVecMul,
    RCLike.star_def, conj_trivial, star_trivial] using h

/-- Each entry of the coarse average of the stream increment on a triadic cube
is a measurable observable of the shell sequence. -/
theorem measurable_volumeAverageMat_finiteShellIncrement (l L : ℕ) (z : TriadicCube d) :
    Measurable fun omega : ShellSeq d =>
      volumeAverageMat (cubeSet z) (fun y => finiteShellIncrement omega l L y) :=
  measurable_volumeAverageMat_of_isBounded (isBounded_cubeSet z) (measurableSet_cubeSet z)
    (measurable_finiteShellIncrement l L)

theorem measurable_streamIncrementCubeVec_apply (l L : ℕ) (e : Vec d)
    (z : TriadicCube d) (i : Fin d) :
    Measurable fun omega : ShellSeq d => streamIncrementCubeVec l L e omega z i :=
  measurable_matVecMul_apply
    (fun r c => ((measurable_pi_apply c).comp
      ((measurable_pi_apply r).comp
        (measurable_volumeAverageMat_finiteShellIncrement l L z)))) e i

/-- **`hstreamMeas`** of `averaged_quadratic_tail` for this carrier. -/
theorem measurable_translatedStreamNormSq (l L : ℕ) (e : Vec d) (z : TriadicCube d) :
    Measurable fun omega : ShellSeq d => translatedStreamNormSq l L e omega z :=
  measurable_vecNormSq_of_apply (measurable_streamIncrementCubeVec_apply l L e z)

/-- **`hquadMeas`** of `averaged_quadratic_tail` for this carrier. -/
theorem measurable_translatedStreamQuadForm [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (l L : ℕ) (e : Vec d) (z : TriadicCube d) :
    Measurable fun omega : ShellSeq d => translatedStreamQuadForm nu l L e omega z := by
  refine measurable_vecDot_matVecMul (fun i j => ?_)
    (measurable_streamIncrementCubeVec_apply l L e z)
  have h : (fun omega : ShellSeq d =>
      sigmaStarInvCoarse (cubeSet z) (coefficientCutoff nu omega L).toCoeffField i j) =
      fun omega : ShellSeq d =>
        sigmaStarInvCoarse (openCubeSet z) (coefficientCutoff nu omega L).toFun i j := by
    funext omega
    rw [sigmaStarInvCoarse_cubeSet_eq_openCubeSet]
    rfl
  rw [h]
  exact measurable_sigmaStarInvCoarse_apply (measurable_coefficientCutoff nu L)
    (fun omega => aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega L) z i j

/-! ## Translation covariance and the transported `Γ₁` envelope -/

/-- **`(k_l − k_L)_{z+cu_n} e` is translation covariant**, the lemma
`volumeAverageMat_cubeSet_finiteShellIncrement_translate` read on the tested
vector. -/
theorem streamIncrementCubeVec_eq_originCube (l L : ℕ) (e : Vec d)
    (omega : ShellSeq d) (Q : TriadicCube d) :
    streamIncrementCubeVec l L e omega Q =
      streamIncrementCubeVec l L e
        (ShellField.translateSequence (triadicCubeShift Q) omega)
        (originCube d Q.scale) := by
  rw [streamIncrementCubeVec, streamIncrementCubeVec,
    volumeAverageMat_cubeSet_finiteShellIncrement_translate omega l L Q]

theorem translatedStreamNormSq_eq_originCube (l L : ℕ) (e : Vec d)
    (omega : ShellSeq d) (Q : TriadicCube d) :
    translatedStreamNormSq l L e omega Q =
      translatedStreamNormSq l L e
        (ShellField.translateSequence (triadicCubeShift Q) omega)
        (originCube d Q.scale) :=
  congrArg vecNormSq (streamIncrementCubeVec_eq_originCube l L e omega Q)

/-- **The `Γ_σ` envelope of `translatedStreamNormSq` transports from `cu_n` to every
translate.**  This is the printed sentence *"the estimates from Subsection
`ss.localization` are used on the translated cube `U`; stationarity gives the
same `O_{Γ_σ}` bounds as on `cu_n`"* for the carrier
`translatedStreamNormSq`.

The value on the centred cube is the amplitude that the balanced part
`e.refined.localization.twoo` of `l.mixing.minscale` supplies, and it stays an
explicit hypothesis: that conjunct is a *relative* bilinear bound
`2 p·(k_l−k_L)_{cu_n} q ≤ (X₁+X₂)(p·s_{L,*}(cu_n)p + q·s_{L,*}(cu_n)q)` in the
`s_{L,*}` metric, whose passage to the absolute squared norm `|(k_l−k_L)e|²`
needs an upper bound on `|s_{L,*}(cu_n)|`, which is exactly the quantity the
localization subsection is estimating and is not available at this surface. -/
theorem isBigO_gammaSigma_translatedStreamNormSq
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (l L : ℕ) (e : Vec d) {Q : TriadicCube d} {A sigma : ℝ}
    (hbig : IsBigO P.toMeasure (gammaSigma sigma)
      (fun omega : ShellSeq d =>
        translatedStreamNormSq l L e omega (originCube d Q.scale)) A) :
    IsBigO P.toMeasure (gammaSigma sigma)
      (fun omega : ShellSeq d => translatedStreamNormSq l L e omega Q) A :=
  isBigO_gammaSigma_of_translationCovariant hPrefix hJ2
    (fun omega => translatedStreamNormSq_eq_originCube l L e omega Q)
    (measurable_translatedStreamNormSq l L e (originCube d Q.scale)) hbig

/-! ## `hOneSided` and `hXtail` from the one-sided part of `l.mixing.minscale` -/

/-- **`hOneSided` and `hXtail` of `averaged_quadratic_tail`**: *"the one-sided part of Lemma
`l.mixing.minscale`, applied on each translate with local lower scale `m − 2h`
and local cube scale `n`, gives
`s_{L',*}^{-1}(z+cu_n) ≤ shom_{L',*}^{-1}(cu_{m−2h})Id + O_{Γ₂}(Cν⁻²3^{−(n−(m−2h))/4}Id)`"*,
tested at the coarse average of the stream increment.

`hquenched` together with `hXmeas` and `hXtail` is the conclusion of the
statement `sigmaStarInv_mixing_minscale`
(`Frozen/Section2/MixingMinscale.lean`), conjunct `e.sstarL.quenched.lb`, in its
exact shape on the centred cube `cu_n`; the transport to the translate
`Q` is `mixing_minscale_onesided_translated`, and the testing at
`streamIncrementCubeVec` is proved here: the scalar reduction
`sigmaBarStarInv_originCube_eq_smul_one` turns the matrix
`shom_{L,*}^{-1}(cu_{m−2h})` into the scalar `sigmaBarStarInvSeq`, and the
Loewner order is the quadratic-form order. -/
theorem oneSided_translatedStreamQuadForm [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ4 : ShellLawJ4 d P)
    {hh nn l L : ℕ} {X : ShellSeq d → ℝ} {A : ℝ} (e : Vec d)
    (hXmeas : Measurable X)
    (hXtail : IsBigO P.toMeasure (gammaSigma 2) X A)
    (hquenched : ∀ omega : ShellSeq d,
      MatLoewnerLE
        (sigmaStarInvCoarse (cubeSet (originCube d (nn : ℤ)))
          (coefficientCutoff nu omega L).toCoeffField)
        (sigmaBarStarInv nu L P (cubeSet (originCube d (hh : ℤ))) +
          X omega • (1 : Mat d)))
    {Q : TriadicCube d} (hQ : Q.scale = (nn : ℤ)) :
    (∀ omega : ShellSeq d,
        translatedStreamQuadForm nu l L e omega Q ≤
          (sigmaBarStarInvSeq nu L P hh + translatedDeviation X omega Q) *
            translatedStreamNormSq l L e omega Q) ∧
      Measurable (fun omega : ShellSeq d => translatedDeviation X omega Q) ∧
      IsBigO P.toMeasure (gammaSigma 2)
        (fun omega : ShellSeq d => translatedDeviation X omega Q) A := by
  obtain ⟨hmeas, hbig, hloew⟩ :=
    mixing_minscale_onesided_translated hPrefix hJ2 hXmeas hXtail hquenched hQ
  refine ⟨fun omega => ?_, hmeas, hbig⟩
  set v : Vec d := streamIncrementCubeVec l L e omega Q with hv
  have hL := hloew omega v
  rw [sigmaBarStarInv_originCube_eq_smul_one hnu L hJ4 (hh : ℤ)] at hL
  have hexp : vecDot v (matVecMul
      (sigmaBarStarInvScalar nu L P (cubeSet (originCube d (hh : ℤ))) • (1 : Mat d) +
        translateObservable X Q omega • (1 : Mat d)) v) =
      (sigmaBarStarInvSeq nu L P hh + translatedDeviation X omega Q) * vecNormSq v := by
    rw [matVecMul_add_mat, vecDot_add_right,
      show (sigmaBarStarInvScalar nu L P (cubeSet (originCube d (hh : ℤ))) • (1 : Mat d)) =
        scalarMatrix (d := d)
          (sigmaBarStarInvScalar nu L P (cubeSet (originCube d (hh : ℤ)))) from rfl,
      show (translateObservable X Q omega • (1 : Mat d)) =
        scalarMatrix (d := d) (translateObservable X Q omega) from rfl,
      matVecMul_scalarMatrix, matVecMul_scalarMatrix, vecDot_smul_right,
      vecDot_smul_right]
    simp only [vecNormSq, translatedDeviation, sigmaBarStarInvSeq]
    ring
  rw [hexp] at hL
  have hfinal : vecDot v (matVecMul
      (sigmaStarInvCoarse (cubeSet Q) (coefficientCutoff nu omega L).toCoeffField) v) ≤
      (sigmaBarStarInvSeq nu L P hh + translatedDeviation X omega Q) * vecNormSq v := by
    linarith only [hL]
  simpa only [translatedStreamQuadForm, translatedStreamNormSq, hv] using hfinal

/-! ## `l.RHS.term3#averaged-quadratic-tail` with the carriers -/

theorem quadTailConstMain_nonneg {Cb Cw Cpig : ℝ} (hCb : 0 ≤ Cb) (hCw : 0 ≤ Cw)
    (hCpig : 0 ≤ Cpig) : 0 ≤ quadTailConstMain Cb Cw Cpig := by
  have hg : (0 : ℝ) < IndependentSums.gammaMomentConst 1 :=
    IndependentSums.gammaMomentConst_pos one_pos
  have h2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  rw [quadTailConstMain]
  positivity

theorem quadTailConstError_nonneg {Cms Cb Cw : ℝ} (hCms : 0 ≤ Cms) (hCb : 0 ≤ Cb)
    (hCw : 0 ≤ Cw) : 0 ≤ quadTailConstError Cms Cb Cw := by
  have hg1 : (0 : ℝ) < IndependentSums.gammaMomentConst 1 :=
    IndependentSums.gammaMomentConst_pos one_pos
  have hg2 : (0 : ℝ) < IndependentSums.gammaMomentConst 2 :=
    IndependentSums.gammaMomentConst_pos two_pos
  have h2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  rw [quadTailConstError]
  positivity

/-- **`l.RHS.term3#averaged-quadratic-tail` at these carriers.**  This is
`averaged_quadratic_tail` applied at
`quad = translatedStreamQuadForm`, `streamSq = translatedStreamNormSq`,
`Xdev = translatedDeviation X`, with every reachable hypothesis discharged:

* `hquadNonneg`, `hstreamNonneg`, `hquadMeas`, `hstreamMeas`, `hXmeas` — proved;
* `hOneSided`, `hXtail` — `oneSided_translatedStreamQuadForm`, i.e. the
  one-sided conjunct of the statement `sigmaStarInv_mixing_minscale` in its
  exact shape on the centred cube (`hquenched`, `hXmeasCentred`, `hXtailCentred`),
  transported to every translate;
* `hStreamTail` — `isBigO_gammaSigma_translatedStreamNormSq`, i.e. the balanced
  conjunct's envelope on `cu_n` (`hStreamTailCentred`) transported;
* `hsigmaNonneg`, `hsigmaMinus`, `hcrude` — proved
  (`sigmaBarStarInvSeq_pos`, `sigmaBarStarInvSeq_le_nuInv`);
* `hell` — `e.scales.ordering`.

What is left explicit is `hWL4` (`e.nablaw.Lt`, supplied by
`RHSTerm3InputsB`), `hPigeon` (the printed `e.pigeon.scalar`
over the pigeonhole range given by the paper; a free binder at this
surface, derived from the cutoff localization
together with the pigeonhole scalar of `e.pigeon.matrix` — not an
output of the averaged gauged comparison `localization_average`) and the scale
bookkeeping `hScaleId`, `hKlog`. -/
theorem averaged_quadratic_tail_translated [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (hSorder : ScalesOrdering S)
    (D : Finset (TriadicCube d)) (hDne : D.Nonempty)
    (hDscale : ∀ z ∈ D, z.scale = (S.n : ℤ)) (e : Vec d)
    {X : ShellSeq d → ℝ} {WL4 Klog Cms Cb Cw Cpig : ℝ}
    (hCms : 0 < Cms) (hCb : 0 < Cb) (hCw : 0 ≤ Cw)
    (hXmeasCentred : Measurable X)
    (hXtailCentred : IsBigO P.toMeasure (gammaSigma 2) X
      (Cms * nu ^ (-(2 : ℝ)) *
        (3 : ℝ) ^ (-(((S.n - (S.m - 2 * S.h) : ℕ) : ℝ) / 4))))
    (hquenched : ∀ omega : ShellSeq d,
      MatLoewnerLE
        (sigmaStarInvCoarse (cubeSet (originCube d (S.n : ℤ)))
          (coefficientCutoff nu omega S.LPrime).toCoeffField)
        (sigmaBarStarInv nu S.LPrime P
            (cubeSet (originCube d ((S.m - 2 * S.h : ℕ) : ℤ))) +
          X omega • (1 : Mat d)))
    (hStreamTailCentred : IsBigO P.toMeasure (gammaSigma 1)
      (fun omega : ShellSeq d =>
        translatedStreamNormSq S.ell S.LPrime e omega (originCube d (S.n : ℤ)))
      (Cb * ((S.LPrime - S.ell : ℕ) : ℝ)))
    (hWL4nonneg : 0 ≤ WL4)
    (hWL4 : WL4 ^ ((1 : ℝ) / 2) ≤
      Cw * ((S.LPrime - S.ell : ℕ) : ℝ) * sigmaBarStarInvSeq nu S.LPrime P S.n)
    (hPigeon : sigmaBarStarInvSeq nu S.LPrime P (S.m - 2 * S.h) ≤
      Cpig * sigmaBarStarInvSeq nu S.LPrime P S.n)
    (hScaleId : (((S.n - (S.m - 2 * S.h) : ℕ)) : ℝ) = ((S.h : ℕ) : ℝ) - 2 * Klog)
    (hKlog : 4 * Klog ≤ ((S.h : ℕ) : ℝ)) :
    Real.sqrt (∫ omega, |((D.card : ℝ))⁻¹ *
          ∑ z ∈ D, translatedStreamQuadForm nu S.ell S.LPrime e omega z| ^ 2
        ∂P.toMeasure) * WL4 ^ ((1 : ℝ) / 2) ≤
      quadTailConstMain Cb Cw Cpig * ((S.LPrime - S.ell : ℕ) : ℝ) ^ 2 *
          sigmaBarStarInvSeq nu S.LPrime P S.n ^ 2 +
        quadTailConstError Cms Cb Cw * nu ^ (-(3 : ℝ)) *
          ((S.LPrime - S.ell : ℕ) : ℝ) ^ 2 * (3 : ℝ) ^ (-((S.h : ℕ) : ℝ) / 8) := by
  have hXtail' : IsBigO P.toMeasure (gammaSigma 2) X
      (Cms * nu ^ (-(2 : ℝ)) *
        (3 : ℝ) ^ (-(((S.n - (S.m - 2 * S.h) : ℕ) : ℝ)) / 4)) := by
    rwa [neg_div]
  refine averaged_quadratic_tail hnu P S D hDne
    (translatedStreamQuadForm nu S.ell S.LPrime e)
    (translatedStreamNormSq S.ell S.LPrime e) (translatedDeviation X)
    hCms hCb hCw ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hWL4nonneg hWL4 ?_ ?_ ?_ hPigeon hScaleId hKlog
  · have h1 := hSorder.ell_lt_ellPrime
    have h2 := hSorder.ellPrime_lt_m
    have h3 := hSorder.m_lt_LPrime
    omega
  · exact fun omega z => translatedStreamQuadForm_nonneg hnu S.ell S.LPrime e omega z
  · exact fun omega z => translatedStreamNormSq_nonneg S.ell S.LPrime e omega z
  · exact fun z => measurable_translatedStreamQuadForm hnu S.ell S.LPrime e z
  · exact fun z => measurable_translatedStreamNormSq S.ell S.LPrime e z
  · exact fun z => measurable_translateObservable hXmeasCentred z
  · exact fun omega z hz => (oneSided_translatedStreamQuadForm (l := S.ell) hnu hPrefix hJ2
      hJ4 e hXmeasCentred hXtail' hquenched (hDscale z hz)).1 omega
  · exact fun z hz => (oneSided_translatedStreamQuadForm (l := S.ell) hnu hPrefix hJ2 hJ4 e
      hXmeasCentred hXtail' hquenched (hDscale z hz)).2.2
  · intro z hz
    refine isBigO_gammaSigma_translatedStreamNormSq hPrefix hJ2 S.ell S.LPrime e ?_
    rw [hDscale z hz]
    exact hStreamTailCentred
  · exact le_of_lt (sigmaBarStarInvSeq_pos hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n)
  · exact le_of_lt (sigmaBarStarInvSeq_pos hnu S.LPrime hPrefix hJ2 hJ3 hJ4 (S.m - 2 * S.h))
  · exact sigmaBarStarInvSeq_le_nuInv hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n

/-- **`hDisp3` of `e.bL.to.bhomell` from the conclusion of
`averaged_quadratic_tail`**: the
display of the averaged quadratic tail enters `e.bL.to.bhomell` multiplied by
the Hölder-split coefficient `C0`, with the two constants
`C3a = C0·Cmain` and `C3b = C0·Cerr`. -/
theorem disp3_of_quadTail {C0 quadMoment W M E nu3 LL sg e3 : ℝ} (hC0 : 0 ≤ C0)
    (h : quadMoment * W ≤ M * LL ^ 2 * sg ^ 2 + E * nu3 * LL ^ 2 * e3) :
    C0 * (quadMoment * W) ≤
      C0 * M * (LL ^ 2 * sg ^ 2) + C0 * E * nu3 * LL ^ 2 * e3 := by
  calc C0 * (quadMoment * W) ≤ C0 * (M * LL ^ 2 * sg ^ 2 + E * nu3 * LL ^ 2 * e3) :=
        mul_le_mul_of_nonneg_left h hC0
    _ = C0 * M * (LL ^ 2 * sg ^ 2) + C0 * E * nu3 * LL ^ 2 * e3 := by ring

end

end SuperdiffusionCLT.Section3.Terms
