/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.SigmaBarComparison.NearAdditivityB
public import SuperdiffusionCLT.Section2.Localization.LocalizationDisplayE
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementMoreoverBlockB

/-!
# `e.localization.ml` at `U := cu_n`, `m := ell`

By `e.localization.ml`: applying Lemma `l.localization.A`
(`SuperdiffusionCLT.Frozen.Section2.coarseBlockMatrix_localization`)
with `ĥ := k_L - k_ell - (k_L-k_ell)_U` and `â := a_ell + ĥ = a_L - (k_L-k_ell)_U`,
then using `e.commute.coarse.grained.k0`
(`SuperdiffusionCLT.Section2.CoarseGraining.coarseBlockMatrix_addConstSkewCoeffOn`),
gives the deterministic quadratic-form comparison of `bfA_L(U)` against the
gauge-conjugated `bfA_ell(U)`.

This is proved, at general `l ≤ L` and general cube `R`, as
`SuperdiffusionCLT.Section2.Localization.localization_display_e_hpoint`
(`Section2/Localization/LocalizationDisplayE.lean`): it performs exactly the
`l.localization.A` + `e.commute.coarse.grained.k0` combination described above, via
`coarseBlockMatrix_localization_scalar_two_sided`
(`BlockPerturbation.lean`) and `coarseBlockMatrix_addConstSkewCoeffOn`
(`SkewShiftCutoff.lean`), with no
probabilistic or analytic estimate as a premise. `sbNear_localizationML` below
is its specialization to `l := ell`, `R := originCube d n`, matched to this
development's own gauge carrier `sbIndep_hMat` via
`sbNear_hMat_eq_localizationGaugeAverage`.

## What this gives, precisely

For every `Pvec`, `|localizationT1CubeError nu ell L (originCube d n) Pvec omega|
≤ localizationDz nu ell L (originCube d n) omega * localizationB nu ell L
(originCube d n) Pvec omega`, where
`localizationT1CubeError` is the quadratic form of
`G_h^t bfA_L(cu_n) G_h - bfA_ell(cu_n)` at `G_{-h}Pvec` (`h := sbIndep_hMat ell
L n omega`) and `localizationB` is the quadratic form of `bfA_ell(cu_n)` at the
same vector. This is the two-sided sandwich form of `e.localization.ml`, not yet the
additive `σ̄` display of the near-additivity step.

## What the near-additivity display further needs

Turning this into the near-additivity display (`hNearAdd`) needs, beyond what is here:

* **Block-extracting `σ̄`, not just `sigmaCoarse`.** `sigmaBarSeq`/`sigmaBar`
  (`Section2/Annealed/Blocks.lean`) are defined with a *Schur-complement*
  correction, `sigmaBar := bBar - kappaBar^t·sigmaBarStarInv·kappaBar` (`bBar`,
  `kappaBar` themselves expectations of the raw coarse blocks), and **not**
  simply `E[(coarseBlockMatrix R field).upperLeft]`. Reading `sbIndep_quadTerm`/
  `sbIndep_crossTerm`/`sigmaBarSeq nu L P n − sigmaBarSeq nu ell P n` off
  `localizationT1CubeError`/`localizationB`'s raw-block quadratic forms
  therefore needs an account of that correction.
* **The expectation step and the `L^{-99}` tail.** `localizationDz`/
  `localizationB` are random (depend on `omega`); the near-additivity display
  needs `E[|Error|] ≤ Cnear·L^{-99}`, via a moment/Orlicz bound on
  `localizationDz` (the same `O_{Γ1}(Cν⁻²3^{-(ell-n)})` tail that
  the *lattice-averaged* `T1` pipeline establishes for `localizationDz`) combined with a
  Cauchy-Schwarz-type bound on
  `E[localizationB]` and the `e.L.vs.Lnaught` absorption
  (`lNaught_sstar_lower`, used in
  `sbIndep_absorption_le_eighth`) to reach the specific witness gap
  `ell − n ≥ 200 log L`.

These steps are carried out in `NearAdditivityD.lean` through `NearAdditivityD5.lean`,
which prove `sbNear_nearAdd`, the `hNearAdd` input of `sbNear_goodNB`
(`NearAdditivityD6.lean`).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.SigmaBarComparison

open MeasureTheory Homogenization
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## The gauge carrier: `sbIndep_hMat` is `localizationGaugeAverage` -/

omit [NeZero d] in
theorem sbNear_hMat_eq_localizationGaugeAverage (ell L n : ℕ) (omega : ShellSeq d) :
    sbIndep_hMat (d := d) ell L n omega =
      SuperdiffusionCLT.Section2.Localization.localizationGaugeAverage ell L
        (originCube d (n : ℤ)) omega := by
  show volumeAverageMat (openCubeSet (originCube d (n : ℤ)))
      (fun y => finiteShellIncrement omega ell L y) =
    volumeAverageMat (cubeSet (originCube d (n : ℤ)))
      (fun y => finiteShellIncrement omega ell L y)
  exact (SuperdiffusionCLT.Section2.Estimates.Stream.volumeAverageMat_cubeSet_eq_openCubeSet
    (originCube d (n : ℤ)) _).symm

/-! ## `e.localization.ml` at `U := cu_n`, `m := ell` -/

/-- **`e.localization.ml`**, specialized to `l := ell`,
`R := originCube d n`: the deterministic quadratic-form sandwich of
`l.localization.A` + `e.commute.coarse.grained.k0`, matched to this
development's own gauge carrier via `sbNear_hMat_eq_localizationGaugeAverage`.
A direct specialization of
`SuperdiffusionCLT.Section2.Localization.localization_display_e_hpoint`. -/
theorem sbNear_localizationML {nu : ℝ} (hnu : 0 < nu) {ell L : ℕ} (hellL : ell ≤ L)
    (n : ℕ) (Pvec : BlockVec d) (omega : ShellSeq d) :
    |SuperdiffusionCLT.Section2.Localization.localizationT1CubeError nu ell L
        (originCube d (n : ℤ)) Pvec omega| ≤
      SuperdiffusionCLT.Section2.Localization.localizationDz nu ell L
          (originCube d (n : ℤ)) omega *
        SuperdiffusionCLT.Section2.Localization.localizationB nu ell L
          (originCube d (n : ℤ)) Pvec omega :=
  SuperdiffusionCLT.Section2.Localization.localization_display_e_hpoint hnu hellL
    (originCube d (n : ℤ)) Pvec omega

end

end SuperdiffusionCLT.Section4.SigmaBarComparison
