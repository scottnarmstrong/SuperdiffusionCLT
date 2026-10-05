/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.GluedField
public import SuperdiffusionCLT.Section2.Localization.PsdSqrtQuadratic
public import SuperdiffusionCLT.Section2.Annealed.Integrability
public import SuperdiffusionCLT.Section2.Annealed.EnvelopeEllipticity

/-!
# The coarse blocks on the translated cubes `z + cu_n`, and stationarity

Step 3 of the proof of `l.RHS.term3` reads the coarse-grained matrices of the
cutoff coefficient on the translated cubes `z + cu_n`, `z ∈ 3^n ℤ^d ∩ cu_k`, and uses on
each of them the estimates that Subsection `ss.localization` proves on the centred cube
`cu_n`: *"the estimates from Subsection `ss.localization` are used on the
translated cube `U`; stationarity gives the same `O_{Γ_σ}` bounds as on
`cu_n`"*.

This module supplies the two halves of that sentence.

* **The carriers.**  `translatedCoarseBlock nu L omega z` is `b_L(z + cu_n)`,
  the upper-left block of `bfA_L(z + cu_n)`; `translatedBlockNorm`
  is `|b_L(z + cu_n)|` and `translatedBlockHalfWeight` is
  `|b_L^{1/2}(z + cu_n)(∇w)_{z'+cu_k}|²`.  These are exactly the free binders
  `bLnorm` and `bHalfW` of the Hoelder split of the term-3 steps, and
  `translatedBlockHalfWeight_le` discharges the operator-norm bridge
  `hbHalfLe` for them.
* **The stationarity transfer.**  Every one of the quenched objects above is
  *translation covariant*: its value on `z + cu_n` for the shell sequence
  `omega` is its value on `cu_n` for the translated shell sequence
  `translateSequence (triadicCubeShift z) omega` — this is the deterministic
  half, proved from `CoarseGraining`'s `CoarseGraining/Translation.lean`
  exactly as `sigmaStarInvCoarse_openCubeSet_coefficientCutoff` of
  `Section3/Terms/GluedField.lean` is proved.  The law of the shell sequence is
  invariant under that translation (`ShellField.map_translateSequence_eq`, i.e.
  `ShellLawPrefix` and `ShellLawJ2`), and a weak-Orlicz tail bound is
  invariant under a measure-preserving map, so a `Γ_σ` bound on `cu_n`
  transports verbatim to `z + cu_n`.

## Main definitions

* `translatedBlockMat`, `translatedCoarseBlock`, `translatedBlockNorm`,
  `translatedBlockHalfWeight`: the coarse blocks on `z + cu_n` and the two
  carriers `bLnorm`, `bHalfW`.
* `translateObservable`: the observable `X` of the centred cube read at the
  translated shell sequence, the transported random variable of the sentence
  above.

## Main results

* `isBigO_gammaSigma_comp_measurePreserving`: a weak-Orlicz `Γ_σ` bound is
  invariant under a measure-preserving map.
* `measurePreserving_translateSequence`,
  `isBigO_gammaSigma_translateObservable`: the instance for the lattice
  translation of the shell sequence.
* `translatedBlockMat_eq_originCube`, `translatedCoarseBlock_eq_originCube`,
  `translatedBlockNorm_eq_originCube`, `sigmaStarInvCoarse_cubeSet_translate`,
  `volumeAverageMat_cubeSet_finiteShellIncrement_translate`: the deterministic
  covariance of the quenched objects the term-3 steps read on `z + cu_n`.
* `mixing_minscale_onesided_translated`: the one-sided conjunct of
  `l.mixing.minscale` that `averaged_quadratic_tail` consumes, transported from
  `cu_n` to `z + cu_n`.
* `posSemidef_translatedCoarseBlock`, `translatedBlockHalfWeight_le`: the
  operator-norm bridge `hbHalfLe` for these carriers.
* `translatedBlockNorm_le_envelope`,
  `isBigO_gammaSigma_translatedBlockNorm_envelope`: `|b_L(z + cu_n)| =
  O_{Γ₁}(bfE_L)` on every translated cube, the printed `Γ₁` envelope of the
  coarse block, read off from the norm form of `e.Enaught.vs.A.and.Ahom`.
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
open SuperdiffusionCLT.Section2.Localization
open scoped MatrixOrder

noncomputable section

variable {d : ℕ}

/-! ## The coarse blocks on a translated cube -/

/-- **`bfA_L(z + cu_n)`**, the doubled coarse-grained matrix of the cutoff
coefficient `a_L` on the translated triadic cube `z`. -/
def translatedBlockMat (nu : ℝ) (L : ℕ) (omega : ShellSeq d) (z : TriadicCube d) :
    BlockMat d :=
  coarseBlockMatrix (openCubeSet z) (coefficientCutoff nu omega L).toCoeffField

/-- **`b_L(z + cu_n)`**, the upper-left block of `bfA_L(z + cu_n)`. -/
def translatedCoarseBlock (nu : ℝ) (L : ℕ) (omega : ShellSeq d) (z : TriadicCube d) :
    Mat d :=
  (translatedBlockMat nu L omega z).upperLeft

/-- **`|b_L(z + cu_n)|`**, the carrier `bLnorm` of the Hoelder split. -/
def translatedBlockNorm (nu : ℝ) (L : ℕ) (omega : ShellSeq d) (z : TriadicCube d) : ℝ :=
  Book.Ch02.matrixOperatorNorm (translatedCoarseBlock nu L omega z)

/-- **`|b_L^{1/2}(z + cu_n)(∇w)_{z'+cu_k}|²`**, the carrier `bHalfW` of
the Hoelder split. -/
def translatedBlockHalfWeight (nu : ℝ) (L : ℕ) {U : Set (Vec d)}
    (w : ShellSeq d → H10Function U) (omega : ShellSeq d) (z' z : TriadicCube d) : ℝ :=
  vecNormSq (matVecMul (CFC.sqrt (translatedCoarseBlock nu L omega z))
    (volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad)))

/-- The coarse block is positive semidefinite: it is the Chapter 2 `bCoarse` of
the cutoff coefficient on the cube, which the unconditional admissibility
`l.ell.adm` of the cutoff field supplies. -/
theorem posSemidef_translatedCoarseBlock [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ)
    (omega : ShellSeq d) (z : TriadicCube d) :
    Matrix.PosSemidef (translatedCoarseBlock nu L omega z) := by
  rw [translatedCoarseBlock, translatedBlockMat,
    ← coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube z,
    show coarseBlockMatrix (cubeSet z) (coefficientCutoff nu omega L).toCoeffField =
      Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain z)
        ((Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
            (coefficientCutoff nu omega L)
            (aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega L)).coeffOn z) from
      Book.Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
        (aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega L) z,
    Book.Ch02.coarseBlockMatrix_upperLeft]
  exact Book.Ch02.bCoarse_posSemidef _ _

/-- **The operator-norm bridge `hbHalfLe`** for the
carriers: `|b^{1/2}v|² = v·(bv) ≤ |b||v|²` on every translated cube. -/
theorem translatedBlockHalfWeight_le [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ)
    {U : Set (Vec d)} (w : ShellSeq d → H10Function U)
    (omega : ShellSeq d) (z' z : TriadicCube d) :
    translatedBlockHalfWeight nu L w omega z' z ≤
      vecNormSq (volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad)) *
        translatedBlockNorm nu L omega z := by
  show vecNormSq (matVecMul (CFC.sqrt (translatedCoarseBlock nu L omega z))
      (volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad))) ≤
    vecNormSq (volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad)) *
      Book.Ch02.matrixOperatorNorm (translatedCoarseBlock nu L omega z)
  exact psdSqrtQuadratic_hbHalfLe U (fun omega z => translatedCoarseBlock nu L omega z)
    (fun omega z => posSemidef_translatedCoarseBlock hnu L omega z) w omega z' z

/-- The half-open and the open realization of a triadic cube give the same
coarse block matrix: `CoarseGraining`'s measurability and integrability engine
works on `cubeSet`, the Chapter 2 vocabulary on its open core. -/
theorem translatedBlockMat_eq_cubeSet [NeZero d] (nu : ℝ) (L : ℕ) (omega : ShellSeq d)
    (z : TriadicCube d) :
    translatedBlockMat nu L omega z =
      coarseBlockMatrix (cubeSet z) (coefficientCutoff nu omega L).toCoeffField :=
  (coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube z
    (coefficientCutoff nu omega L).toCoeffField).symm

/-- The entries of `b_L(z + cu_n)` in the half-open spelling. -/
theorem translatedCoarseBlock_apply [NeZero d] (nu : ℝ) (L : ℕ) (omega : ShellSeq d)
    (z : TriadicCube d) (i j : Fin d) :
    translatedCoarseBlock nu L omega z i j =
      (coarseBlockMatrix (cubeSet z)
        (coefficientCutoff nu omega L).toFun).upperLeft i j := by
  rw [translatedCoarseBlock, translatedBlockMat_eq_cubeSet]
  rfl

/-! ## The deterministic half: translation covariance of the quenched objects

Every quenched object the term-3 steps read on `z + cu_n` is the same object
read on `cu_{Q.scale}` for the translated shell sequence.  Each proof is the
one of `sigmaStarInvCoarse_openCubeSet_coefficientCutoff`
(`Section3/Terms/GluedField.lean`): rewrite the cube as a translate of the
centred cube at its scale, move the translation onto the coefficient field with
`CoarseGraining`'s `CoarseGraining/Translation.lean`, and identify the
translated cutoff field with the cutoff field of the translated sequence
(`translateReg_coefficientCutoff`). -/

section Covariance

variable (nu : ℝ) (L : ℕ) (omega : ShellSeq d) (Q : TriadicCube d)

/-- **`bfA_L(z + cu_n)` is translation covariant.** -/
theorem translatedBlockMat_eq_originCube :
    translatedBlockMat nu L omega Q =
      translatedBlockMat nu L
        (ShellField.translateSequence (triadicCubeShift Q) omega)
        (originCube d Q.scale) := by
  rw [translatedBlockMat, translatedBlockMat,
    openCubeSet_eq_translateSet_originCube_of_triadicCube Q,
    coarseBlockMatrix_translateSet_eq_translateCoeffField,
    ← translateReg_coefficientCutoff nu (triadicCubeShift Q) omega L]
  rfl

/-- **`b_L(z + cu_n)` is translation covariant.** -/
theorem translatedCoarseBlock_eq_originCube :
    translatedCoarseBlock nu L omega Q =
      translatedCoarseBlock nu L
        (ShellField.translateSequence (triadicCubeShift Q) omega)
        (originCube d Q.scale) :=
  congrArg BlockMat.upperLeft (translatedBlockMat_eq_originCube nu L omega Q)

/-- **`|b_L(z + cu_n)|` is translation covariant.** -/
theorem translatedBlockNorm_eq_originCube :
    translatedBlockNorm nu L omega Q =
      translatedBlockNorm nu L
        (ShellField.translateSequence (triadicCubeShift Q) omega)
        (originCube d Q.scale) :=
  congrArg Book.Ch02.matrixOperatorNorm (translatedCoarseBlock_eq_originCube nu L omega Q)

/-- **`s_{L,*}^{-1}(z + cu_n)` is translation covariant**, on the half-open
realization used by `l.mixing.minscale`. -/
theorem sigmaStarInvCoarse_cubeSet_translate :
    sigmaStarInvCoarse (cubeSet Q) (coefficientCutoff nu omega L).toCoeffField =
      sigmaStarInvCoarse (cubeSet (originCube d Q.scale))
        (coefficientCutoff nu
          (ShellField.translateSequence (triadicCubeShift Q) omega) L).toCoeffField := by
  rw [cubeSet_eq_translateSet_originCube_of_triadicCube Q,
    sigmaStarInvCoarse_translateSet_eq_translateCoeffField,
    ← translateReg_coefficientCutoff nu (triadicCubeShift Q) omega L]
  rfl

end Covariance

/-- Translating the finite stream increment translates the underlying shell
sequence: the analogue of `translateReg_coefficientCutoff` for `k_l - k_L`. -/
theorem translateReg_finiteShellIncrement (z : Vec d) (omega : ShellSeq d) (l L : ℕ) :
    translateReg z (finiteShellIncrement omega l L) =
      finiteShellIncrement (ShellField.translateSequence z omega) l L := by
  refine RegCoeffField.ext fun x ↦ ?_
  rw [translateReg_apply, finiteShellIncrement_apply, finiteShellIncrement_apply]
  exact Finset.sum_congr rfl fun k _ ↦ rfl

/-- **`(k_l - k_L)_{z + cu_n}` is translation covariant**: the cube average of
the finite stream increment on `z + cu_n` is its average on `cu_{Q.scale}` for
the translated shell sequence. -/
theorem volumeAverageMat_cubeSet_finiteShellIncrement_translate
    (omega : ShellSeq d) (l L : ℕ) (Q : TriadicCube d) :
    volumeAverageMat (cubeSet Q) (fun y => finiteShellIncrement omega l L y) =
      volumeAverageMat (cubeSet (originCube d Q.scale))
        (fun y => finiteShellIncrement
          (ShellField.translateSequence (triadicCubeShift Q) omega) l L y) := by
  funext i j
  rw [volumeAverageMat, volumeAverageMat,
    cubeSet_eq_translateSet_originCube_of_triadicCube Q,
    Book.Ch01.volumeAverage_translateSet_eq_comp_addRight]
  refine congrArg (volumeAverage (cubeSet (originCube d Q.scale))) ?_
  funext x
  exact congrFun (congrFun (congrArg (fun a : RegCoeffField d => a.toFun x)
    (translateReg_finiteShellIncrement (triadicCubeShift Q) omega l L)) i) j

/-! ## The probabilistic half: `Γ_σ` bounds are invariant under a
measure-preserving map -/

/-- **A weak-Orlicz `Γ_σ` bound is invariant under a measure-preserving map.**
The tail event of `X ∘ T` is the `T`-preimage of the tail event of `X`, and a
measure-preserving map does not change the measure of a preimage. -/
theorem isBigO_gammaSigma_comp_measurePreserving {Omega Omega' : Type*}
    [MeasurableSpace Omega] [MeasurableSpace Omega']
    {mu : Measure Omega} {mu' : Measure Omega'} {T : Omega → Omega'}
    (hT : MeasurePreserving T mu mu') {X : Omega' → ℝ} (hX : Measurable X)
    {A sigma : ℝ} (hbig : IsBigO mu' (gammaSigma sigma) X A) :
    IsBigO mu (gammaSigma sigma) (fun omega => X (T omega)) A := by
  rw [isBigO_gammaSigma_iff]
  intro t ht
  have hset : absTailEvent (fun omega => X (T omega)) (A * t) =
      T ⁻¹' absTailEvent X (A * t) := rfl
  have hmeas : MeasurableSet (absTailEvent X (A * t)) := by
    exact
      measurableSet_lt measurable_const (continuous_abs.measurable.comp hX)
  have hpre := hT.measure_preimage hmeas.nullMeasurableSet
  have hreal : mu.real (T ⁻¹' absTailEvent X (A * t)) =
      mu'.real (absTailEvent X (A * t)) := by
    simp only [Measure.real, hpre]
  rw [hset, hreal]
  exact (isBigO_gammaSigma_iff.1 hbig) ht

section Transfer

variable {P : ProbabilityMeasure (ShellSeq d)}

/-- **The lattice translation of the shell sequence preserves the shell law**,
`ShellField.vaddInvariantMeasure` read as a measure-preserving map: this is the
`ShellLawPrefix` together with `ShellLawJ2`. -/
theorem measurePreserving_translateSequence (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (z : Vec d) :
    MeasurePreserving (ShellField.translateSequence z) P.toMeasure P.toMeasure :=
  ⟨ShellField.measurable_translateSequence z,
    ShellField.map_translateSequence_eq hPrefix hJ2 z⟩

/-- **The observable of the centred cube read on the translated cube.**  This is
the random variable the printed sentence *"stationarity gives the same
`O_{Γ_σ}` bounds as on `cu_n`"* produces on `z + cu_n` from
the one `ss.localization` produces on `cu_n`. -/
def translateObservable (X : ShellSeq d → ℝ) (Q : TriadicCube d) : ShellSeq d → ℝ :=
  fun omega => X (ShellField.translateSequence (triadicCubeShift Q) omega)

theorem measurable_translateObservable {X : ShellSeq d → ℝ} (hX : Measurable X)
    (Q : TriadicCube d) : Measurable (translateObservable X Q) :=
  hX.comp (ShellField.measurable_translateSequence (triadicCubeShift Q))

/-- **The transported variable carries the same `Γ_σ` amplitude.** -/
theorem isBigO_gammaSigma_translateObservable (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) {X : ShellSeq d → ℝ} (hX : Measurable X) {A sigma : ℝ}
    (hbig : IsBigO P.toMeasure (gammaSigma sigma) X A) (Q : TriadicCube d) :
    IsBigO P.toMeasure (gammaSigma sigma) (translateObservable X Q) A :=
  isBigO_gammaSigma_comp_measurePreserving
    (measurePreserving_translateSequence hPrefix hJ2 (triadicCubeShift Q)) hX hbig

/-- **The translated-localization bridge for a translation-covariant family.**
If the quenched quantity `F` on the cube `Q` is the quantity on the centred cube
of the same scale for the translated shell sequence, then the `O_{Γ_σ}` bound on
`cu_{Q.scale}` is the same bound on `Q`. -/
theorem isBigO_gammaSigma_of_translationCovariant (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) {F : ShellSeq d → TriadicCube d → ℝ} {Q : TriadicCube d}
    {A sigma : ℝ}
    (hcov : ∀ omega : ShellSeq d, F omega Q =
      F (ShellField.translateSequence (triadicCubeShift Q) omega) (originCube d Q.scale))
    (hmeas : Measurable fun omega : ShellSeq d => F omega (originCube d Q.scale))
    (hbig : IsBigO P.toMeasure (gammaSigma sigma)
      (fun omega : ShellSeq d => F omega (originCube d Q.scale)) A) :
    IsBigO P.toMeasure (gammaSigma sigma) (fun omega : ShellSeq d => F omega Q) A := by
  have h := isBigO_gammaSigma_translateObservable hPrefix hJ2 hmeas hbig Q
  have heq : (fun omega : ShellSeq d => F omega Q) =
      translateObservable (fun omega : ShellSeq d => F omega (originCube d Q.scale)) Q :=
    funext hcov
  rw [heq]
  exact h

/-- **`|b_L(z + cu_n)| = O_{Γ_σ}(A)` from `|b_L(cu_n)| = O_{Γ_σ}(A)`.**  This is
the instance of the bridge that `block_concentration` and the Hoelder split use:
the `l.bfAm.ellip` envelope of the coarse block on the centred cube is the same
envelope on every translate. -/
theorem isBigO_gammaSigma_translatedBlockNorm (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (nu : ℝ) (L : ℕ) {Q : TriadicCube d} {A sigma : ℝ}
    (hmeas : Measurable fun omega : ShellSeq d =>
      translatedBlockNorm nu L omega (originCube d Q.scale))
    (hbig : IsBigO P.toMeasure (gammaSigma sigma)
      (fun omega : ShellSeq d => translatedBlockNorm nu L omega (originCube d Q.scale)) A) :
    IsBigO P.toMeasure (gammaSigma sigma)
      (fun omega : ShellSeq d => translatedBlockNorm nu L omega Q) A :=
  isBigO_gammaSigma_of_translationCovariant hPrefix hJ2
    (fun omega => translatedBlockNorm_eq_originCube nu L omega Q) hmeas hbig

end Transfer

/-! ## `l.mixing.minscale` on the translated cubes

`averaged_quadratic_tail` (`Section3/Terms/RHSTerm3StepsD.lean`) consumes two
conjuncts of the anchor `sigmaStarInv_mixing_minscale`
(`Frozen/Section2/MixingMinscale.lean`), both printed on the centred cube
`cu_n`, *on each translate* `z + cu_n`:

* `e.sstarL.quenched.lb`, the one-sided bound
  `s_{L,*}^{-1}(cu_n) ≤ shom_{L,*}^{-1}(cu_h) Id + X Id` with
  `X = O_{Γ₂}(C ν^{-2} 3^{-(n-h)/4})`, which produces the hypotheses
  `hOneSided`/`hXtail`;
* `e.refined.localization.twoo`, the balanced bound on the cube average of
  `k_l - k_L` in the `s_{L,*}` metric, which produces `hStreamTail`.

The two theorems below take the anchor's conclusion on `cu_n` as an explicit
hypothesis, in its exact printed shape, and return the same conclusion on an
arbitrary triadic cube of scale `n`, with the transported variables
`translateObservable`.  Nothing else is assumed: the quenched half is the
covariance proved above and the tail half is the measure-preserving invariance.
-/

section MixingMinscale

variable {P : ProbabilityMeasure (ShellSeq d)}

/-- **`e.sstarL.quenched.lb` on a translated cube.** -/
theorem mixing_minscale_onesided_translated (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) {nu : ℝ} {hh nn L : ℕ} {X : ShellSeq d → ℝ} {A : ℝ}
    (hXmeas : Measurable X)
    (hXtail : IsBigO P.toMeasure (gammaSigma 2) X A)
    (hquenched : ∀ omega : ShellSeq d,
      MatLoewnerLE
        (sigmaStarInvCoarse (cubeSet (originCube d (nn : ℤ)))
          (coefficientCutoff nu omega L).toCoeffField)
        (sigmaBarStarInv nu L P (cubeSet (originCube d (hh : ℤ))) +
          X omega • (1 : Mat d)))
    {Q : TriadicCube d} (hQ : Q.scale = (nn : ℤ)) :
    Measurable (translateObservable X Q) ∧
      IsBigO P.toMeasure (gammaSigma 2) (translateObservable X Q) A ∧
      ∀ omega : ShellSeq d,
        MatLoewnerLE
          (sigmaStarInvCoarse (cubeSet Q) (coefficientCutoff nu omega L).toCoeffField)
          (sigmaBarStarInv nu L P (cubeSet (originCube d (hh : ℤ))) +
            translateObservable X Q omega • (1 : Mat d)) := by
  refine ⟨measurable_translateObservable hXmeas Q,
    isBigO_gammaSigma_translateObservable hPrefix hJ2 hXmeas hXtail Q, fun omega => ?_⟩
  have hcov := sigmaStarInvCoarse_cubeSet_translate nu L omega Q
  rw [hQ] at hcov
  rw [hcov]
  exact hquenched (ShellField.translateSequence (triadicCubeShift Q) omega)

end MixingMinscale

/-! ## Expectations on a translated cube

The same invariance moves a *Bochner integral* from the translated cube to the
centred one; this is the step `integral_sigmaStarInvCoarse_openCubeSet_eq` of
`Section3/Terms/GluedField.lean` performs for `s_{L,*}^{-1}`, isolated here for
an arbitrary observable so that the centring `E[Y_z] = 0` of
`l.RHS.term3#block-concentration` can use it. -/

section Expectations

variable {P : ProbabilityMeasure (ShellSeq d)}

/-- The transported observable is integrable when the original one is. -/
theorem integrable_translateObservable (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) {X : ShellSeq d → ℝ} (hX : Integrable X P.toMeasure)
    (Q : TriadicCube d) : Integrable (translateObservable X Q) P.toMeasure := by
  have hmap : Measure.map
      (ShellField.translateSequence (triadicCubeShift Q)) P.toMeasure = P.toMeasure :=
    ShellField.map_translateSequence_eq hPrefix hJ2 (triadicCubeShift Q)
  have hX' : AEStronglyMeasurable X (Measure.map
      (ShellField.translateSequence (triadicCubeShift Q)) P.toMeasure) := by
    rw [hmap]; exact hX.aestronglyMeasurable
  refine (integrable_map_measure hX'
    (ShellField.measurable_translateSequence (triadicCubeShift Q)).aemeasurable).1 ?_
  rw [hmap]; exact hX

/-- **The expectation is unchanged by the lattice translation.** -/
theorem integral_translateObservable_eq (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) {X : ShellSeq d → ℝ}
    (hX : AEStronglyMeasurable X P.toMeasure) (Q : TriadicCube d) :
    ∫ omega : ShellSeq d, translateObservable X Q omega ∂P.toMeasure =
      ∫ omega : ShellSeq d, X omega ∂P.toMeasure := by
  have hmap : Measure.map
      (ShellField.translateSequence (triadicCubeShift Q)) P.toMeasure = P.toMeasure :=
    ShellField.map_translateSequence_eq hPrefix hJ2 (triadicCubeShift Q)
  have hX' : AEStronglyMeasurable X (Measure.map
      (ShellField.translateSequence (triadicCubeShift Q)) P.toMeasure) := by
    rw [hmap]; exact hX
  calc ∫ omega : ShellSeq d, translateObservable X Q omega ∂P.toMeasure
      = ∫ omega : ShellSeq d, X omega
          ∂(Measure.map (ShellField.translateSequence (triadicCubeShift Q)) P.toMeasure) :=
        (integral_map
          (ShellField.measurable_translateSequence (triadicCubeShift Q)).aemeasurable hX').symm
    _ = ∫ omega : ShellSeq d, X omega ∂P.toMeasure := by rw [hmap]

/-- **The expectation of a translation-covariant quenched quantity does not
depend on the translate** (stationarity). -/
theorem integral_of_translationCovariant (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) {F : ShellSeq d → TriadicCube d → ℝ} {Q : TriadicCube d}
    (hcov : ∀ omega : ShellSeq d, F omega Q =
      F (ShellField.translateSequence (triadicCubeShift Q) omega) (originCube d Q.scale))
    (hmeas : AEStronglyMeasurable
      (fun omega : ShellSeq d => F omega (originCube d Q.scale)) P.toMeasure) :
    ∫ omega : ShellSeq d, F omega Q ∂P.toMeasure =
      ∫ omega : ShellSeq d, F omega (originCube d Q.scale) ∂P.toMeasure := by
  have heq : (fun omega : ShellSeq d => F omega Q) =
      translateObservable (fun omega : ShellSeq d => F omega (originCube d Q.scale)) Q :=
    funext hcov
  rw [heq]
  exact integral_translateObservable_eq hPrefix hJ2 hmeas Q

end Expectations

/-! ## The `Γ₁` envelope of the coarse block on a translated cube

`e.Enaught.vs.A.and.Ahom` holds on every bounded domain in
the normalized form `|bfE_L^{-1/2} bfA_L(U) bfE_L^{-1/2}| = O_{Γ₁}(1)`
(`isBigOWith_gammaSigma_blockMatrixOperatorNorm_envelopeRescale`).  Undoing the
normalization on the upper-left block turns it into the envelope of `b_L(U)`
itself at the amplitude `envelopeUpperScalar d nu L`, the printed
`nu + 2C nu⁻¹(1 ∨ L)` of `e.Enaught.mixing` — the `Cℓν⁻¹` the block
concentration step uses. -/

section Envelope

variable [NeZero d] {nu : ℝ}

/-- The pointwise half: `|b_L(z + cu_n)| ≤ bfE_L · (the random factor of
`e.Enaught.vs.A.and.Ahom`)`. -/
theorem translatedBlockNorm_le_envelope (hnu : 0 < nu) (L : ℕ) (omega : ShellSeq d)
    (z : TriadicCube d) :
    translatedBlockNorm nu L omega z ≤
      envelopeUpperScalar d nu L *
        envelopeRatioOn L ((Book.Ch02.cubeDomain z : Book.Ch02.Domain d) : Set (Vec d))
          omega := by
  have hc : 0 < envelopeUpperScalar d nu L := envelopeUpperScalar_pos hnu d L
  set U : Book.Ch02.Domain d := Book.Ch02.cubeDomain z with hU
  set c : ℝ := envelopeUpperScalar d nu L with hcdef
  set rho : ℝ := envelopeRatioOn L (U : Set (Vec d)) omega with hrhodef
  have hrho : 1 ≤ rho := one_le_envelopeRatioOn L (U : Set (Vec d)) omega
  set M : BlockMat d :=
    coarseBlockMatrix (U : Set (Vec d)) (coefficientCutoff nu omega L).toCoeffField with hM
  have hcoe : (U : Set (Vec d)) = openCubeSet z := Book.Ch02.cubeDomain_coe z
  have hMeq : M = translatedBlockMat nu L omega z := by
    rw [hM, hcoe, translatedBlockMat]
  have hUL : MatLoewnerLE (envelopeRescale d nu L M).upperLeft
      (rho • Book.Ch02.blockIdentity d).upperLeft :=
    Book.Ch04.matLoewnerLE_upperLeft_of_blockMatLoewnerLE
      (blockMatLoewnerLE_envelopeRescale_coarseBlockMatrix_domain U hnu omega L)
  have hRHS : (rho • Book.Ch02.blockIdentity d).upperLeft = rho • (1 : Mat d) := rfl
  have hLHS : (envelopeRescale d nu L M).upperLeft =
      ((Real.sqrt c)⁻¹ * (Real.sqrt c)⁻¹) • M.upperLeft := by
    rw [envelopeRescale_eq]
  have hinv : c * ((Real.sqrt c)⁻¹ * (Real.sqrt c)⁻¹) = 1 := by
    have hr : Real.sqrt c ≠ 0 := (Real.sqrt_pos.2 hc).ne'
    have hrr : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc.le
    calc c * ((Real.sqrt c)⁻¹ * (Real.sqrt c)⁻¹)
        = (Real.sqrt c * Real.sqrt c) * ((Real.sqrt c)⁻¹ * (Real.sqrt c)⁻¹) := by rw [hrr]
      _ = 1 := by field_simp
  have hquad : ∀ (a : ℝ) (A : Mat d) (x : Vec d),
      vecDot x (matVecMul (a • A) x) = a * vecDot x (matVecMul A x) := by
    intro a A x
    rw [smul_matVecMul, vecDot_smul_right]
  have hone : ∀ (a : ℝ) (x : Vec d),
      vecDot x (matVecMul (a • (1 : Mat d)) x) = a * vecNormSq x := by
    intro a x
    rw [hquad]
    refine congrArg (fun t : ℝ => a * t) ?_
    show vecDot x (matVecMul (1 : Mat d) x) = vecDot x x
    refine congrArg (fun v : Vec d => vecDot x v) ?_
    funext i
    simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]
  have hLoew : MatLoewnerLE M.upperLeft ((c * rho) • (1 : Mat d)) := by
    intro x
    have h := hUL x
    rw [hLHS, hRHS, hquad, hone] at h
    rw [hone]
    have hq : (Real.sqrt c)⁻¹ * (Real.sqrt c)⁻¹ * vecDot x (matVecMul M.upperLeft x) ≤
        rho * vecNormSq x := by linarith only [h]
    have hmul := mul_le_mul_of_nonneg_left hq hc.le
    have hid : c * ((Real.sqrt c)⁻¹ * (Real.sqrt c)⁻¹ *
        vecDot x (matVecMul M.upperLeft x)) = vecDot x (matVecMul M.upperLeft x) := by
      rw [← mul_assoc, hinv, one_mul]
    have hrewr : c * (rho * vecNormSq x) = c * rho * vecNormSq x := by ring
    linarith only [hmul, hid, hrewr]
  have hPSD : Matrix.PosSemidef M.upperLeft := by
    rw [hMeq]
    exact posSemidef_translatedCoarseBlock hnu L omega z
  have hcr : (0 : ℝ) ≤ c * rho := mul_nonneg hc.le (le_trans zero_le_one hrho)
  have hPSD2 : Matrix.PosSemidef ((c * rho) • (1 : Mat d)) := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · show Matrix.conjTranspose ((c * rho) • (1 : Mat d)) = (c * rho) • (1 : Mat d)
      simp
    · intro x
      have heq : star x ⬝ᵥ Matrix.mulVec ((c * rho) • (1 : Mat d)) x =
          vecDot x (matVecMul ((c * rho) • (1 : Mat d)) x) := by
        simp only [Homogenization.vecDot, Homogenization.matVecMul, dotProduct,
          Matrix.mulVec, star_trivial]
      rw [heq, hone]
      exact mul_nonneg hcr (vecNormSq_nonneg x)
  have hnorm := Book.Ch02.matrixOperatorNorm_le_of_matLoewnerLE_of_posSemidef hPSD hPSD2 hLoew
  rw [Book.Ch02.matrixOperatorNorm_smul_one_eq_of_nonneg hcr] at hnorm
  rw [translatedBlockNorm, translatedCoarseBlock, ← hMeq]
  exact hnorm

variable {P : ProbabilityMeasure (ShellSeq d)}

/-- **`|b_L(z + cu_n)| = O_{Γ₁}(bfE_L)` on every translated cube.**  This is the
hypothesis `hYtail` of `block_concentration` at its source, discharged from the
norm form of `e.Enaught.vs.A.and.Ahom`. -/
theorem isBigO_gammaSigma_translatedBlockNorm_envelope (hnu : 0 < nu)
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (L : ℕ) (z : TriadicCube d) :
    IsBigO P.toMeasure (gammaSigma 1)
      (fun omega : ShellSeq d => translatedBlockNorm nu L omega z)
      (envelopeUpperScalar d nu L) := by
  have hc : 0 < envelopeUpperScalar d nu L := envelopeUpperScalar_pos hnu d L
  have hratio := isBigOWith_gammaSigma_envelopeRatioOn (P := P) hPrefix hJ2 hJ3 hJ4 L
    (volume_domain_ne_zero (Book.Ch02.cubeDomain z))
    (volume_domain_ne_top (Book.Ch02.cubeDomain z))
  have hscaled := hratio.const_mul (c := envelopeUpperScalar d nu L) hc.le
  rw [mul_one] at hscaled
  refine hscaled.of_le fun omega => ?_
  have hnn : 0 ≤ translatedBlockNorm nu L omega z :=
    Book.Ch02.matrixOperatorNorm_nonneg _
  rw [abs_of_nonneg hnn]
  exact translatedBlockNorm_le_envelope hnu L omega z

end Envelope

end

end SuperdiffusionCLT.Section3.Terms
