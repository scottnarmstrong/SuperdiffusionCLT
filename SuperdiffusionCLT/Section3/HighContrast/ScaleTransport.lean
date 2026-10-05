/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.HighContrast.CutoffLinftyEnvelope
public import SuperdiffusionCLT.Section3.HighContrast.ScaleTransportArithmetic

/-!
# The scale bookkeeping of the high-contrast entry bound

`Section3/HighContrast/StructuralLaw.lean` applies `CoarseGraining`'s
high-contrast entry theorem to `rebasedCutoffLaw nu m P`, the cutoff law dilated
by `3 ^ (m + triadicOffset d)`, and reaches the bound at that law's own entry
scale. The paper needs it at the cutoff field's own cubes: the proof of
`l.b.ell.homogenization` uses the step
`shom_k(cu_n) <= 2 shom_{k,*}(cu_n)` under the scale separation
`n - k >= C_0 log^2(nu^{-1} k)`.

## Transporting a scale of the rebased law to a scale of the cutoff law

Scale `j` of the rebased law is scale `j + m + triadicOffset d` of the cutoff
law. `CoarseGraining` states this shift for the annealed block matrix
(`Book.Ch04.annealedBlockMatrixAtScale_restrictionScaleNormalizedLaw`), and the
whole annealed algebra is built from that matrix, so it transports to `shom` and
`shom_*` and hence to `sigmaBarScalar` and `sigmaBarStarScalar` of
`Section2/Annealed/Symmetry.lean`.

The transport is stated for the annealed matrices, not for
`Book.Ch05.thetaAtScale` of the cutoff law: that quantity is typed to consume a
`Book.Ch04.RestrictionStructuralLaw`, whose `unit_range` field fails for a field
of range `3 ^ m sqrt d >= sqrt 2`, so no term of that type can be produced and
carrying it as a hypothesis would make the conclusion vacuous. The annealed
matrices are defined for every law and are exactly the manuscript's
`shom_k(cu_n)` and `shom_{k,*}(cu_n)`.

Scope note: the cube index is always `m + triadicOffset d + j` with `j : ℕ`, so
the bound below is stated for cube indices `n >= m + t_d` only. For the assembly
of `l.b.ell.homogenization` this is harmless, since there `n - m >= C_0 (1 +
log^2(nu^{-1} L)) >= t_d`; no declaration here covers `m < n < m + t_d`.

## The entry constant is uniform in the law

The entry constant of the three theorems below is quantified **before** `nu`,
`m` and `P`, in the shape `exists C, 0 < C and forall nu forall m forall P`,
exactly as in the upstream
`Book.Ch05.Section55.annealedPerturbativeEntry_homogenizationScale`: a consumer
assembling the manuscript's `l.b.ell.homogenization` needs one constant
`C_0(d)` that does not depend on the cutoff level, the cutoff index or the
measure.

## The initial-scale contrast and the threshold

`Book.Ch05.annealedEntryScale` is defined through
`widetildeThetaAtScale (rebasedCutoffLaw nu m P) 0`, the product of the two
unit-cube ellipticity moment roots. The moment bounds of
`Section3/HighContrast/EllipticityMoments.lean` give
`lambda_{s,1}(cu_0; a_m)^{-1} <= 2 nu^{-1}` unconditionally and
`Lambda_{s,1}(cu_0; a_m) <= nu + 2 nu^{-1} S ^ 2` for a uniform bound `S` on
`|k_m|` over the rebasing cube, and the `Gamma_2` moment bound
`abs_moment_le_of_isBigO_gammaSigma_two` turns the envelope amplitude `A` into
the moment bound: `widetildeTheta_0 <= 4 (1 + Gamma(xi + 1)) (1 + 2 nu^{-2})
(1 + A ^ 2)`. With the envelope of
`Section3/HighContrast/CutoffLinftyEnvelope.lean` the amplitude satisfies
`A <= cutoffLargeCubeAmpConst d * (1 + m)`, so `cutoffContrastBound` is of size
`C(d, xi) nu^{-2} m ^ 2`: the "contrast bounded by a dimensional polynomial in
`nu^{-1} k`" of the paper. The entry scale is a sum of two ceilings, both
governed by `log (2 + widetildeTheta_0)`, so a bound `widetildeTheta_0 <= B`
gives `annealedEntryScale <= entryScaleLogSqConst xi C sigma * log^2 (2 + B)`,
the printed threshold. The constants `entryScaleLogSqConst`,
`cutoffLargeCubeAmpConst` and `cutoffContrastBound` and the two comparison
lemmas `annealedEntryScale_le_mul_logSq`, `cutoffLargeCubeAmp_le`,
`cutoffContrastBound_nonneg` live in the module
`Section3/HighContrast/ScaleTransportArithmetic.lean`, which this module
imports.

The entry theorem bounds the contrast at one scale only, but `CoarseGraining`
supplies the companion statement
`Book.Ch05.Section54.GoodScale.thetaAtScale_mono_of_P4`: under `(P4)` the
contrast is non-increasing in the scale, so the bound at the entry scale
propagates to every larger scale and no new obligation is needed.

## Main definitions

None; the three explicit constants of the bookkeeping are in
`Section3/HighContrast/ScaleTransportArithmetic.lean`.

## Main results

* `annealedSigmaAtScale_rebasedCutoffLaw` and its starred companion: the scale
  shift of the two annealed diagonal blocks.
* `sigmaBarScalar_originCube_eq_barSigmaAtScale` and its starred companion: the
  manuscript scalars at `cu_{m + t_d + j}` are the structural-law scalars of the
  rebased law at `j`.
* `sigmaBarScalar_le_mul_sigmaBarStarScalar_of_quantitativeEllipticity` and its
  two specializations: the entry bound at the cutoff field's own cubes, with the
  entry constant uniform in `nu`, `m` and `P`.
* `lambdaInvMomentAtScale_zero_rebasedCutoffLaw_le`,
  `LambdaMomentAtScale_zero_rebasedCutoffLaw_le`,
  `widetildeThetaAtScale_zero_rebasedCutoffLaw_le` and its two specializations:
  the initial-scale contrast polynomial.
* `annealedEntryScale_rebasedCutoffLaw_le`: the threshold comparison.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.HighContrast

open Homogenization MeasureTheory ProbabilityTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Probability

noncomputable section

variable {d : ℕ}

/-! ## The scale shift of the annealed diagonal blocks

`CoarseGraining` proves the shift for the full annealed block matrix; the two
diagonal blocks are built from it by the same algebra at every set. -/

/-- **The scale shift of the annealed conductivity.** Scale `j` of the triadic
scale normalization by `3 ^ k` is scale `k + j` of the original law. -/
theorem annealedSigmaAtScale_restrictionScaleNormalizedLaw [NeZero d]
    {P : Book.Ch04.RestrictionCoeffLaw d} (hP : Book.Ch04.RestrictionLawCarrier P)
    (k j : ℕ) :
    Book.Ch04.annealedSigmaAtScale (Book.Ch04.restrictionScaleNormalizedLaw k P) (j : ℤ)
      = Book.Ch04.annealedSigmaAtScale P ((k + j : ℕ) : ℤ) := by
  have h := Book.Ch04.annealedBlockMatrixAtScale_restrictionScaleNormalizedLaw hP k j
  simp only [Book.Ch04.annealedBlockMatrixAtScale] at h
  simp only [Book.Ch04.annealedSigmaAtScale, Book.Ch04.annealedSigma, Book.Ch04.annealedB,
    Book.Ch04.annealedKappa, Book.Ch04.annealedSigmaStar, Book.Ch04.annealedSigmaStarInv,
    Book.Ch04.annealedSigmaStarInvKappaMean, h]

/-- **The scale shift of the annealed starred matrix.** -/
theorem annealedSigmaStarAtScale_restrictionScaleNormalizedLaw [NeZero d]
    {P : Book.Ch04.RestrictionCoeffLaw d} (hP : Book.Ch04.RestrictionLawCarrier P)
    (k j : ℕ) :
    Book.Ch04.annealedSigmaStarAtScale (Book.Ch04.restrictionScaleNormalizedLaw k P) (j : ℤ)
      = Book.Ch04.annealedSigmaStarAtScale P ((k + j : ℕ) : ℤ) := by
  have h := Book.Ch04.annealedBlockMatrixAtScale_restrictionScaleNormalizedLaw hP k j
  simp only [Book.Ch04.annealedBlockMatrixAtScale] at h
  simp only [Book.Ch04.annealedSigmaStarAtScale, Book.Ch04.annealedSigmaStar,
    Book.Ch04.annealedSigmaStarInv, h]

/-- The annealed conductivity of the rebased cutoff law at scale `j` is the
annealed conductivity of the cutoff law at scale `j + m + triadicOffset d`. -/
theorem annealedSigmaAtScale_rebasedCutoffLaw [NeZero d] {nu : ℝ} (hnu : 0 < nu) (m : ℕ)
    (P : ProbabilityMeasure (ShellSeq d)) (j : ℕ) :
    Book.Ch04.annealedSigmaAtScale (rebasedCutoffLaw nu m P) (j : ℤ)
      = Book.Ch04.annealedSigmaAtScale (cutoffLaw (d := d) nu m P)
          ((m + triadicOffset d + j : ℕ) : ℤ) :=
  annealedSigmaAtScale_restrictionScaleNormalizedLaw
    (restrictionLawCarrier_cutoffLaw hnu m P) (m + triadicOffset d) j

/-- The annealed starred matrix of the rebased cutoff law at scale `j` is the
annealed starred matrix of the cutoff law at scale `j + m + triadicOffset d`. -/
theorem annealedSigmaStarAtScale_rebasedCutoffLaw [NeZero d] {nu : ℝ} (hnu : 0 < nu) (m : ℕ)
    (P : ProbabilityMeasure (ShellSeq d)) (j : ℕ) :
    Book.Ch04.annealedSigmaStarAtScale (rebasedCutoffLaw nu m P) (j : ℤ)
      = Book.Ch04.annealedSigmaStarAtScale (cutoffLaw (d := d) nu m P)
          ((m + triadicOffset d + j : ℕ) : ℤ) :=
  annealedSigmaStarAtScale_restrictionScaleNormalizedLaw
    (restrictionLawCarrier_cutoffLaw hnu m P) (m + triadicOffset d) j

/-- Reading the scalar off a scalar matrix. -/
private theorem smul_one_apply_zero_zero [NeZero d] (c : ℝ) :
    (c • (1 : Mat d)) 0 0 = c := by
  simp

/-- **The manuscript scalar `shom_m(cu_{m + t_d + j})` is `CoarseGraining`'s
structural-law scalar of the rebased law at scale `j`.** -/
theorem sigmaBarScalar_originCube_eq_barSigmaAtScale [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {m : ℕ} {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ4 : ShellLawJ4 d P)
    (hrange : CutoffRangeDependence nu m P) (j : ℕ) :
    sigmaBarScalar nu m P (cubeSet (originCube d ((m + triadicOffset d + j : ℕ) : ℤ)))
      = (restrictionLawCarrier_rebasedCutoffLaw hnu m P).barSigmaAtScale
          (restrictionStructuralLaw_rebasedCutoffLaw hPrefix hJ2 hJ4 hrange) (j : ℤ) := by
  have hbar :=
    (restrictionLawCarrier_rebasedCutoffLaw hnu m P).annealedSigmaAtScale_eq_barSigmaAtScale
      (restrictionStructuralLaw_rebasedCutoffLaw hPrefix hJ2 hJ4 hrange) (j : ℤ)
  rw [sigmaBarScalar, sigmaBar_eq_ch04 hnu m P (originCube d ((m + triadicOffset d + j : ℕ) : ℤ))]
  show Book.Ch04.annealedSigmaAtScale (cutoffLaw (d := d) nu m P)
      ((m + triadicOffset d + j : ℕ) : ℤ) 0 0 = _
  rw [← annealedSigmaAtScale_rebasedCutoffLaw hnu m P j, hbar, smul_one_apply_zero_zero]

/-- **The manuscript scalar `shom_{m,*}(cu_{m + t_d + j})` is `CoarseGraining`'s
structural-law starred scalar of the rebased law at scale `j`.** -/
theorem sigmaBarStarScalar_originCube_eq_barSigmaStarAtScale [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {m : ℕ} {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ4 : ShellLawJ4 d P)
    (hrange : CutoffRangeDependence nu m P) (j : ℕ) :
    sigmaBarStarScalar nu m P (cubeSet (originCube d ((m + triadicOffset d + j : ℕ) : ℤ)))
      = (restrictionLawCarrier_rebasedCutoffLaw hnu m P).barSigmaStarAtScale
          (restrictionStructuralLaw_rebasedCutoffLaw hPrefix hJ2 hJ4 hrange) (j : ℤ) := by
  have hbar :=
    (restrictionLawCarrier_rebasedCutoffLaw hnu m P).annealedSigmaStarAtScale_eq_barSigmaStarAtScale
      (restrictionStructuralLaw_rebasedCutoffLaw hPrefix hJ2 hJ4 hrange) (j : ℤ)
  rw [sigmaBarStarScalar,
    sigmaBarStar_eq_ch04 hnu m P (originCube d ((m + triadicOffset d + j : ℕ) : ℤ))]
  show Book.Ch04.annealedSigmaStarAtScale (cutoffLaw (d := d) nu m P)
      ((m + triadicOffset d + j : ℕ) : ℤ) 0 0 = _
  rw [← annealedSigmaStarAtScale_rebasedCutoffLaw hnu m P j, hbar, smul_one_apply_zero_zero]

/-! ## The entry bound at the cutoff field's own cubes

Under `(P4)` the contrast is non-increasing in the scale, so the entry bound
holds at every larger scale, and the two scalar identities above read it on the
cutoff field's own cubes. -/

/-- **The high-contrast entry bound at the cutoff field's own cubes.** For every
scale `j` beyond `CoarseGraining`'s entry scale of the rebased law,
`shom_m(cu_{m + t_d + j}) <= (1 + sigma) shom_{m,*}(cu_{m + t_d + j})`: the step
of the paper, with the manuscript's `cu_n`
written as `n = m + triadicOffset d + j`, so `n - m = triadicOffset d + j`.
The entry constant is chosen from the parameter record **before** `nu`, `m` and
`P`, exactly as in the entry theorem, so it is uniform in the law. -/
theorem sigmaBarScalar_le_mul_sigmaBarStarScalar_of_quantitativeEllipticity [NeZero d]
    (params : Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (nu : ℝ) (_hnu : 0 < nu) (m : ℕ) (P : ProbabilityMeasure (ShellSeq d))
        (_hPrefix : ShellLawPrefix d P) (_hJ2 : ShellLawJ2 d P) (_hJ4 : ShellLawJ4 d P)
        (_hrange : CutoffRangeDependence nu m P)
        (hmom : CutoffEllipticityMoments nu m P params.sUpper params.sLower params.xi),
        ∀ sigma : ℝ, 0 < sigma → sigma ≤ (1 / 2 : ℝ) →
          ∀ j : ℕ,
            Book.Ch05.annealedEntryScale (rebasedCutoffLaw nu m P)
                (quantitativeCoarseGrainedEllipticity_rebasedCutoffLaw nu m P params hmom)
                C sigma ≤ j →
            sigmaBarScalar nu m P
                (cubeSet (originCube d ((m + triadicOffset d + j : ℕ) : ℤ))) ≤
              (1 + sigma) * sigmaBarStarScalar nu m P
                (cubeSet (originCube d ((m + triadicOffset d + j : ℕ) : ℤ))) := by
  obtain ⟨C, hC, hentry⟩ :=
    Book.Ch05.Section55.annealedPerturbativeEntry_homogenizationScale (d := d) params
  refine ⟨C, hC, fun nu hnu m P hPrefix hJ2 hJ4 hrange hmom sigma hsigma hsigma' j hj ↦ ?_⟩
  set hcar := restrictionLawCarrier_rebasedCutoffLaw hnu m P with hcar_def
  set hstr := restrictionStructuralLaw_rebasedCutoffLaw hPrefix hJ2 hJ4 hrange with hstr_def
  set hP4 := quantitativeCoarseGrainedEllipticity_rebasedCutoffLaw nu m P params hmom with hP4_def
  have hmono : Book.Ch05.thetaAtScale hcar hstr (j : ℤ) ≤ 1 + sigma :=
    le_trans
      (Book.Ch05.Section54.GoodScale.thetaAtScale_mono_of_P4 hcar hstr hP4 hj)
      (hentry hcar hstr hP4 rfl sigma hsigma hsigma')
  have hstar : 0 < hcar.barSigmaStarAtScale hstr (j : ℤ) :=
    Book.Ch05.Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4 hcar hstr hP4 j
  have hdiv : hcar.barSigmaAtScale hstr (j : ℤ) / hcar.barSigmaStarAtScale hstr (j : ℤ)
      ≤ 1 + sigma := by
    rw [div_eq_mul_inv]
    exact hmono
  rw [sigmaBarScalar_originCube_eq_barSigmaAtScale hnu hPrefix hJ2 hJ4 hrange j,
    sigmaBarStarScalar_originCube_eq_barSigmaStarAtScale hnu hPrefix hJ2 hJ4 hrange j]
  exact (div_le_iff₀ hstar).1 hdiv

/-- **The high-contrast entry bound at the cutoff field's own cubes**, with the
two ellipticity moment obligations discharged by the `L^infinity`
envelope of `Section3/HighContrast/CutoffLinftyEnvelope.lean`: only the range of
dependence of the cutoff law remains open. The entry constant is chosen before
`nu`, `m` and `P`, so it is uniform in the law. -/
theorem sigmaBarScalar_le_mul_sigmaBarStarScalar [NeZero d]
    (params : Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (nu : ℝ) (hnu : 0 < nu) (m : ℕ) (P : ProbabilityMeasure (ShellSeq d))
        (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
        (hJ4 : ShellLawJ4 d P) (_hrange : CutoffRangeDependence nu m P),
        ∀ sigma : ℝ, 0 < sigma → sigma ≤ (1 / 2 : ℝ) →
          ∀ j : ℕ,
            Book.Ch05.annealedEntryScale (rebasedCutoffLaw nu m P)
                (quantitativeCoarseGrainedEllipticity_rebasedCutoffLaw_of_largeCubeLinfty
                  params hnu (cutoffLargeCubeLinfty hPrefix hJ2 hJ3 hJ4 m))
                C sigma ≤ j →
            sigmaBarScalar nu m P
                (cubeSet (originCube d ((m + triadicOffset d + j : ℕ) : ℤ))) ≤
              (1 + sigma) * sigmaBarStarScalar nu m P
                (cubeSet (originCube d ((m + triadicOffset d + j : ℕ) : ℤ))) := by
  obtain ⟨C, hC, hb⟩ :=
    sigmaBarScalar_le_mul_sigmaBarStarScalar_of_quantitativeEllipticity params
  exact ⟨C, hC, fun nu hnu m P hPrefix hJ2 hJ3 hJ4 hrange ↦
    hb nu hnu m P hPrefix hJ2 hJ4 hrange
      (cutoffEllipticityMoments_of_largeCubeLinfty hnu
        (cutoffLargeCubeLinfty hPrefix hJ2 hJ3 hJ4 m) params.sUpper_pos params.sLower_pos
        params.xi)⟩


/-! ## The initial-scale contrast of the rebased cutoff law

The lower moment root is bounded unconditionally by the deterministic bound of
`Section3/HighContrast/EllipticityMoments.lean`; the upper one needs the
`Gamma_2` moment bound of `l.moments.gamma.psi`. -/

/-- An integral against the rebased cutoff law is bounded by the integral of a
dominating observable of the sample. -/
private theorem integral_rebasedCutoffLaw_le {nu : ℝ} {m : ℕ}
    {P : ProbabilityMeasure (ShellSeq d)} {X : RegCoeffField d → ℝ} {g : ShellSeq d → ℝ}
    (hX : AEStronglyMeasurable X (rebasedCutoffLaw nu m P))
    (hXnn : ∀ a : RegCoeffField d, 0 ≤ X a)
    (hg : Integrable g P.toMeasure)
    (hbound : ∀ omega : ShellSeq d,
      X (rescaleReg (d := d) (m + triadicOffset d) (coefficientCutoff nu omega m)) ≤ g omega) :
    ∫ a, X a ∂(rebasedCutoffLaw nu m P) ≤ ∫ omega, g omega ∂P.toMeasure := by
  have hmeas : Measurable (fun omega : ShellSeq d ↦
      rescaleReg (d := d) (m + triadicOffset d) (coefficientCutoff nu omega m)) :=
    (measurable_rescaleReg (d := d) (m + triadicOffset d)).comp
      (measurable_coefficientCutoff nu m)
  rw [rebasedCutoffLaw_eq_map_shellSeq] at hX ⊢
  rw [integral_map hmeas.aemeasurable hX]
  have hcomp : AEStronglyMeasurable
      (fun omega : ShellSeq d ↦
        X (rescaleReg (d := d) (m + triadicOffset d) (coefficientCutoff nu omega m)))
      P.toMeasure := hX.comp_aemeasurable hmeas.aemeasurable
  refine integral_mono ?_ hg fun omega ↦ hbound omega
  refine hg.mono' hcomp (Filter.Eventually.of_forall fun omega ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (hXnn _)]
  exact hbound omega

/-- Cancellation of the moment root of a constant. -/
private theorem pow_rpow_inv_natCast {c : ℝ} (hc : 0 ≤ c) {xi : ℕ} (hxi : 0 < xi) :
    (c ^ xi) ^ (1 / (xi : ℝ)) = c := by
  have hne : ((xi : ℝ)) ≠ 0 := Nat.cast_ne_zero.2 hxi.ne'
  rw [← Real.rpow_natCast c xi, ← Real.rpow_mul hc, mul_one_div, div_self hne, Real.rpow_one]

/-- **The lower unit-cube moment root of the rebased cutoff law.** The
reciprocal lower observable is bounded by `2 nu^{-1}` pointwise. -/
theorem lambdaInvMomentAtScale_zero_rebasedCutoffLaw_le [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (m : ℕ) (P : ProbabilityMeasure (ShellSeq d)) {sLower : ℝ} (hsLower : 0 < sLower)
    {xi : ℕ} (hxi : 0 < xi) :
    Book.Ch04.lambdaInvMomentAtScale (rebasedCutoffLaw nu m P) (0 : ℤ) sLower xi ≤ 2 * nu⁻¹ := by
  have hcarrier := restrictionLawCarrier_rebasedCutoffLaw hnu m P
  have : IsProbabilityMeasure (rebasedCutoffLaw nu m P) := hcarrier.isProbability
  have hnn : ∀ a : RegCoeffField d,
      (0 : ℝ) ≤ (Book.Ch04.lambdaSqCoeffField (originCube d (0 : ℤ)) sLower (.finite 1) a)⁻¹ :=
    fun a ↦ inv_nonneg.2 (Book.Ch04.lambdaSqCoeffField_finite_nonneg _ _ hsLower le_rfl)
  have hint := integrable_lambdaSqCoeffField_inv_pow_rebasedCutoffLaw hnu m P hsLower xi
  have hcbound : (0 : ℝ) ≤ 2 * nu⁻¹ := by positivity
  have hmono : ∫ a, (Book.Ch04.lambdaSqCoeffField (originCube d (0 : ℤ)) sLower (.finite 1) a)⁻¹
        ^ xi ∂(rebasedCutoffLaw nu m P) ≤ (2 * nu⁻¹) ^ xi := by
    have := integral_rebasedCutoffLaw_le
      (X := fun a : RegCoeffField d ↦
        (Book.Ch04.lambdaSqCoeffField (originCube d (0 : ℤ)) sLower (.finite 1) a)⁻¹ ^ xi)
      (g := fun _ : ShellSeq d ↦ (2 * nu⁻¹) ^ xi) hint.aestronglyMeasurable
      (fun a ↦ pow_nonneg (hnn a) xi) (integrable_const _)
      (fun omega ↦ pow_le_pow_left₀ (hnn _)
        (lambdaSqCoeffField_inv_rebasedCutoff_le hnu omega m hsLower) xi)
    simpa using this
  have hnonneg : (0 : ℝ) ≤ ∫ a, (Book.Ch04.lambdaSqCoeffField (originCube d (0 : ℤ)) sLower
      (.finite 1) a)⁻¹ ^ xi ∂(rebasedCutoffLaw nu m P) :=
    integral_nonneg fun a ↦ pow_nonneg (hnn a) xi
  calc Book.Ch04.lambdaInvMomentAtScale (rebasedCutoffLaw nu m P) (0 : ℤ) sLower xi
      = (∫ a, (Book.Ch04.lambdaSqCoeffField (originCube d (0 : ℤ)) sLower (.finite 1) a)⁻¹
          ^ xi ∂(rebasedCutoffLaw nu m P)) ^ (1 / (xi : ℝ)) := rfl
    _ ≤ ((2 * nu⁻¹) ^ xi) ^ (1 / (xi : ℝ)) :=
        Real.rpow_le_rpow hnonneg hmono (by positivity)
    _ = 2 * nu⁻¹ := pow_rpow_inv_natCast hcbound hxi


/-- The deterministic upper bound, raised to the moment exponent and split into
a constant and a pure power of the envelope. -/
private theorem cutoffUpperPoly_pow_le {nu : ℝ} (hnu : 0 < nu) (S : ℝ) (xi : ℕ) :
    (nu + 2 * nu⁻¹ * S ^ 2) ^ xi ≤ (nu + 2 * nu⁻¹) ^ xi * (1 + (S ^ 2) ^ xi) := by
  have hmax : (1 : ℝ) ≤ max 1 (S ^ 2) := le_max_left _ _
  have hsq : S ^ 2 ≤ max 1 (S ^ 2) := le_max_right _ _
  have hbase : nu + 2 * nu⁻¹ * S ^ 2 ≤ (nu + 2 * nu⁻¹) * max 1 (S ^ 2) := by
    have h1 : nu ≤ nu * max 1 (S ^ 2) := le_mul_of_one_le_right hnu.le hmax
    have h2 : 2 * nu⁻¹ * S ^ 2 ≤ 2 * nu⁻¹ * max 1 (S ^ 2) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    linarith only [h1, h2]
  have hb0 : (0 : ℝ) ≤ nu + 2 * nu⁻¹ * S ^ 2 := by positivity
  have hmaxpow : (max 1 (S ^ 2)) ^ xi ≤ 1 + (S ^ 2) ^ xi := by
    rcases le_total (S ^ 2) 1 with h | h
    · rw [max_eq_left h, one_pow]
      have hnn : (0 : ℝ) ≤ (S ^ 2) ^ xi := by positivity
      linarith only [hnn]
    · rw [max_eq_right h]
      have hone : (0 : ℝ) ≤ (1 : ℝ) := zero_le_one
      linarith only [hone]
  calc (nu + 2 * nu⁻¹ * S ^ 2) ^ xi
      ≤ ((nu + 2 * nu⁻¹) * max 1 (S ^ 2)) ^ xi := pow_le_pow_left₀ hb0 hbase xi
    _ = (nu + 2 * nu⁻¹) ^ xi * (max 1 (S ^ 2)) ^ xi := mul_pow _ _ _
    _ ≤ (nu + 2 * nu⁻¹) ^ xi * (1 + (S ^ 2) ^ xi) :=
        mul_le_mul_of_nonneg_left hmaxpow (by positivity)

/-- **The upper unit-cube moment root of the rebased cutoff law.** The upper
observable is bounded by `nu + 2 nu^{-1} S ^ 2` for any uniform bound `S` on
`|k_m|` over the rebasing cube, and the `Gamma_2` moment bound of
`l.moments.gamma.psi` turns the amplitude `A` into a bound. -/
theorem LambdaMomentAtScale_zero_rebasedCutoffLaw_le [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {m : ℕ} {P : ProbabilityMeasure (ShellSeq d)} {S : ShellSeq d → ℝ} {A : ℝ}
    (hA : 0 < A) (hSm : AEMeasurable S P.toMeasure)
    (hStail : IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2) S A)
    (hSbound : ∀ (omega : ShellSeq d) (x : Vec d),
      x ∈ openCubeSet (originCube d ((m + triadicOffset d : ℕ) : ℤ)) →
        Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ≤ S omega)
    {sUpper : ℝ} (hsUpper : 0 < sUpper) {xi : ℕ} (hxi : 0 < xi) :
    Book.Ch04.LambdaMomentAtScale (rebasedCutoffLaw nu m P) (0 : ℤ) sUpper xi ≤
      2 * (1 + Real.Gamma ((xi : ℝ) + 1)) * ((nu + 2 * nu⁻¹) * (1 + A ^ 2)) := by
  have hcarrier := restrictionLawCarrier_rebasedCutoffLaw hnu m P
  have : IsProbabilityMeasure (rebasedCutoffLaw nu m P) := hcarrier.isProbability
  set K : ℝ := 1 + Real.Gamma ((xi : ℝ) + 1) with hK_def
  have hK1 : (1 : ℝ) ≤ K := by
    have := Real.Gamma_nonneg_of_nonneg (by positivity : (0 : ℝ) ≤ (xi : ℝ) + 1)
    rw [hK_def]; linarith only [this]
  -- the envelope moment, rewritten from the rpow form of the printed lemma
  have hcast : ∀ omega : ShellSeq d, |S omega| ^ (((2 * xi : ℕ) : ℝ)) = (S omega ^ 2) ^ xi := by
    intro omega
    rw [Real.rpow_natCast, pow_mul, sq_abs]
  have hGamma : (((2 * xi : ℕ) : ℝ)) / 2 + 1 = (xi : ℝ) + 1 := by push_cast; ring
  have hAcast : A ^ (((2 * xi : ℕ) : ℝ)) = (A ^ 2) ^ xi := by
    rw [Real.rpow_natCast, pow_mul]
  have hSint : Integrable (fun omega : ShellSeq d ↦ (S omega ^ 2) ^ xi) P.toMeasure :=
    (integrable_abs_rpow_of_isBigO_gammaSigma_two hA hSm hStail (2 * xi)).congr
      (Filter.Eventually.of_forall hcast)
  have hSmom : ∫ omega, (S omega ^ 2) ^ xi ∂P.toMeasure ≤ (A ^ 2) ^ xi * K := by
    have hraw := abs_moment_le_of_isBigO_gammaSigma_two hA hSm hStail (2 * xi)
    rw [hGamma, hAcast] at hraw
    calc ∫ omega, (S omega ^ 2) ^ xi ∂P.toMeasure
        = ∫ omega, |S omega| ^ (((2 * xi : ℕ) : ℝ)) ∂P.toMeasure :=
          integral_congr_ae (Filter.Eventually.of_forall fun omega ↦ (hcast omega).symm)
      _ ≤ (A ^ 2) ^ xi * K := hraw
  -- the dominated integral bound
  have hmeas : AEStronglyMeasurable (fun a : RegCoeffField d ↦
      Book.Ch04.LambdaSqCoeffField (originCube d (0 : ℤ)) sUpper (.finite 1) a ^ xi)
      (rebasedCutoffLaw nu m P) :=
    ((hcarrier.aemeasurable_LambdaSqCoeffField_finite_one
      (originCube d (0 : ℤ)) hsUpper).pow_const xi).aestronglyMeasurable
  have hgint : Integrable
      (fun omega : ShellSeq d ↦ (nu + 2 * nu⁻¹) ^ xi * (1 + (S omega ^ 2) ^ xi)) P.toMeasure :=
    ((integrable_const (1 : ℝ)).add hSint).const_mul _
  have hLnn : ∀ a : RegCoeffField d,
      (0 : ℝ) ≤ Book.Ch04.LambdaSqCoeffField (originCube d (0 : ℤ)) sUpper (.finite 1) a ^ xi :=
    fun a ↦ pow_nonneg (Book.Ch04.LambdaSqCoeffField_finite_nonneg _ _ hsUpper le_rfl) xi
  have hstep : ∫ a, Book.Ch04.LambdaSqCoeffField (originCube d (0 : ℤ)) sUpper (.finite 1) a ^ xi
      ∂(rebasedCutoffLaw nu m P) ≤
      ∫ omega, (nu + 2 * nu⁻¹) ^ xi * (1 + (S omega ^ 2) ^ xi) ∂P.toMeasure := by
    refine integral_rebasedCutoffLaw_le hmeas hLnn hgint fun omega ↦ ?_
    have hnn : (0 : ℝ) ≤ Book.Ch04.LambdaSqCoeffField (originCube d (0 : ℤ)) sUpper
        (.finite 1) (rescaleReg (d := d) (m + triadicOffset d)
          (coefficientCutoff nu omega m)) :=
      Book.Ch04.LambdaSqCoeffField_finite_nonneg _ _ hsUpper le_rfl
    refine le_trans (pow_le_pow_left₀ hnn
      (LambdaSqCoeffField_rebasedCutoff_le hnu omega m
        (fun x hx ↦ hSbound omega x hx) hsUpper) xi) ?_
    exact cutoffUpperPoly_pow_le hnu (S omega) xi
  have hgval : ∫ omega, (nu + 2 * nu⁻¹) ^ xi * (1 + (S omega ^ 2) ^ xi) ∂P.toMeasure
      = (nu + 2 * nu⁻¹) ^ xi * (1 + ∫ omega, (S omega ^ 2) ^ xi ∂P.toMeasure) := by
    rw [integral_const_mul, integral_add (integrable_const (1 : ℝ)) hSint]
    simp
  -- the algebra of the two constants
  have hone_le : (1 : ℝ) ≤ (1 + A ^ 2) ^ xi :=
    one_le_pow₀ (by linarith only [sq_nonneg A])
  have hAle : (A ^ 2) ^ xi ≤ (1 + A ^ 2) ^ xi :=
    pow_le_pow_left₀ (by positivity) (by linarith only [zero_le_one (α := ℝ)]) xi
  have hKv : (1 : ℝ) ≤ K * (1 + A ^ 2) ^ xi := by
    have := mul_le_mul hK1 hone_le zero_le_one (by linarith only [hK1])
    linarith only [this]
  have hprod : (A ^ 2) ^ xi * K ≤ K * (1 + A ^ 2) ^ xi := by
    have := mul_le_mul_of_nonneg_right hAle (by linarith only [hK1] : (0 : ℝ) ≤ K)
    linarith only [this]
  have hcombine : (nu + 2 * nu⁻¹) ^ xi * (1 + ∫ omega, (S omega ^ 2) ^ xi ∂P.toMeasure) ≤
      2 * K * ((nu + 2 * nu⁻¹) * (1 + A ^ 2)) ^ xi := by
    have hinner : 1 + ∫ omega, (S omega ^ 2) ^ xi ∂P.toMeasure ≤
        2 * K * (1 + A ^ 2) ^ xi := by
      have := hSmom
      linarith only [this, hKv, hprod]
    calc (nu + 2 * nu⁻¹) ^ xi * (1 + ∫ omega, (S omega ^ 2) ^ xi ∂P.toMeasure)
        ≤ (nu + 2 * nu⁻¹) ^ xi * (2 * K * (1 + A ^ 2) ^ xi) :=
          mul_le_mul_of_nonneg_left hinner (by positivity)
      _ = 2 * K * ((nu + 2 * nu⁻¹) ^ xi * (1 + A ^ 2) ^ xi) := by ring
      _ = 2 * K * ((nu + 2 * nu⁻¹) * (1 + A ^ 2)) ^ xi := by rw [mul_pow]
  -- the moment root
  have hYnn : (0 : ℝ) ≤ (nu + 2 * nu⁻¹) * (1 + A ^ 2) := by positivity
  have hMnn : (1 : ℝ) ≤ 2 * K := by linarith only [hK1]
  have hIntnn : (0 : ℝ) ≤ ∫ a, Book.Ch04.LambdaSqCoeffField (originCube d (0 : ℤ)) sUpper
      (.finite 1) a ^ xi ∂(rebasedCutoffLaw nu m P) := integral_nonneg hLnn
  have hfinal : ∫ a, Book.Ch04.LambdaSqCoeffField (originCube d (0 : ℤ)) sUpper (.finite 1) a
      ^ xi ∂(rebasedCutoffLaw nu m P) ≤
      2 * K * ((nu + 2 * nu⁻¹) * (1 + A ^ 2)) ^ xi := by
    rw [hgval] at hstep
    exact le_trans hstep hcombine
  calc Book.Ch04.LambdaMomentAtScale (rebasedCutoffLaw nu m P) (0 : ℤ) sUpper xi
      = (∫ a, Book.Ch04.LambdaSqCoeffField (originCube d (0 : ℤ)) sUpper (.finite 1) a ^ xi
          ∂(rebasedCutoffLaw nu m P)) ^ (1 / (xi : ℝ)) := rfl
    _ ≤ (2 * K * ((nu + 2 * nu⁻¹) * (1 + A ^ 2)) ^ xi) ^ (1 / (xi : ℝ)) :=
        Real.rpow_le_rpow hIntnn hfinal (by positivity)
    _ = (2 * K) ^ (1 / (xi : ℝ)) *
          (((nu + 2 * nu⁻¹) * (1 + A ^ 2)) ^ xi) ^ (1 / (xi : ℝ)) :=
        Real.mul_rpow (by linarith only [hMnn]) (by positivity)
    _ = (2 * K) ^ (1 / (xi : ℝ)) * ((nu + 2 * nu⁻¹) * (1 + A ^ 2)) := by
        rw [pow_rpow_inv_natCast hYnn hxi]
    _ ≤ (2 * K) * ((nu + 2 * nu⁻¹) * (1 + A ^ 2)) := by
        refine mul_le_mul_of_nonneg_right ?_ hYnn
        have hle : (1 / (xi : ℝ)) ≤ 1 := by
          rw [div_le_one (by exact_mod_cast hxi)]
          exact_mod_cast hxi
        simpa using Real.rpow_le_rpow_of_exponent_le hMnn hle


/-- **The initial-scale contrast of the rebased cutoff law.** The quantity
through which `Book.Ch05.annealedEntryScale` is defined is bounded by an explicit
polynomial in `nu^{-1}` and in the amplitude `A` of the `Gamma_2` envelope of
`|k_m|` on the rebasing cube: the "contrast bounded by a dimensional polynomial
in `nu^{-1} k`" of the paper. -/
theorem widetildeThetaAtScale_zero_rebasedCutoffLaw_le [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {m : ℕ} {P : ProbabilityMeasure (ShellSeq d)} {S : ShellSeq d → ℝ} {A : ℝ}
    (hA : 0 < A) (hSm : AEMeasurable S P.toMeasure)
    (hStail : IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2) S A)
    (hSbound : ∀ (omega : ShellSeq d) (x : Vec d),
      x ∈ openCubeSet (originCube d ((m + triadicOffset d : ℕ) : ℤ)) →
        Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ≤ S omega)
    {sUpper sLower : ℝ} (hsUpper : 0 < sUpper) (hsLower : 0 < sLower)
    {xi : ℕ} (hxi : 0 < xi) :
    Book.Ch04.widetildeThetaAtScale (rebasedCutoffLaw nu m P) (0 : ℤ) sUpper sLower xi ≤
      4 * (1 + Real.Gamma ((xi : ℝ) + 1)) * (1 + 2 * nu⁻¹ ^ 2) * (1 + A ^ 2) := by
  have hupper := LambdaMomentAtScale_zero_rebasedCutoffLaw_le hnu hA hSm hStail hSbound
    hsUpper hxi
  have hlower := lambdaInvMomentAtScale_zero_rebasedCutoffLaw_le hnu m P hsLower hxi
  have hun : 0 ≤ Book.Ch04.LambdaMomentAtScale (rebasedCutoffLaw nu m P) (0 : ℤ) sUpper xi :=
    Book.Ch04.LambdaMomentAtScale_nonneg _ _ xi hsUpper
  have hln : 0 ≤ Book.Ch04.lambdaInvMomentAtScale (rebasedCutoffLaw nu m P) (0 : ℤ) sLower xi :=
    Book.Ch04.lambdaInvMomentAtScale_nonneg _ _ xi hsLower
  have hrhs : (0 : ℝ) ≤ 2 * (1 + Real.Gamma ((xi : ℝ) + 1)) * ((nu + 2 * nu⁻¹) * (1 + A ^ 2)) :=
    le_trans hun hupper
  have hstep :
      Book.Ch04.LambdaMomentAtScale (rebasedCutoffLaw nu m P) (0 : ℤ) sUpper xi *
          Book.Ch04.lambdaInvMomentAtScale (rebasedCutoffLaw nu m P) (0 : ℤ) sLower xi ≤
        (2 * (1 + Real.Gamma ((xi : ℝ) + 1)) * ((nu + 2 * nu⁻¹) * (1 + A ^ 2))) *
          (2 * nu⁻¹) :=
    mul_le_mul hupper hlower hln hrhs
  have hnu0 : nu ≠ 0 := hnu.ne'
  have hid : (2 * (1 + Real.Gamma ((xi : ℝ) + 1)) * ((nu + 2 * nu⁻¹) * (1 + A ^ 2))) *
      (2 * nu⁻¹) = 4 * (1 + Real.Gamma ((xi : ℝ) + 1)) * (1 + 2 * nu⁻¹ ^ 2) * (1 + A ^ 2) := by
    field_simp
    ring
  rw [Book.Ch04.widetildeThetaAtScale, ← hid]
  exact hstep

/-- **The initial-scale contrast**, with the envelope supplied by
`Section3/HighContrast/CutoffLinftyEnvelope.lean`. -/
theorem widetildeThetaAtScale_zero_rebasedCutoffLaw_le_cutoffLargeCubeAmp [NeZero d]
    (params : Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d)
    {nu : ℝ} (hnu : 0 < nu) {m : ℕ} {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) :
    Book.Ch05.widetildeThetaAtScale (rebasedCutoffLaw nu m P) (0 : ℤ)
        (quantitativeCoarseGrainedEllipticity_rebasedCutoffLaw_of_largeCubeLinfty params hnu
          (cutoffLargeCubeLinfty hPrefix hJ2 hJ3 hJ4 m)) ≤
      4 * (1 + Real.Gamma ((params.xi : ℝ) + 1)) * (1 + 2 * nu⁻¹ ^ 2) *
        (1 + cutoffLargeCubeAmp d m ^ 2) :=
  widetildeThetaAtScale_zero_rebasedCutoffLaw_le hnu (cutoffLargeCubeAmp_pos hPrefix m)
    (measurable_cutoffLargeCubeSupBound m).aemeasurable
    (isBigO_gammaSigma_cutoffLargeCubeSupBound hPrefix hJ2 hJ3 hJ4 m)
    (fun omega _ hx ↦ matrixOperatorNorm_streamCutoff_le_cubes omega m hx)
    params.sUpper_pos params.sLower_pos params.xi_pos


/-! ## The initial-scale contrast is bounded by the dimensional polynomial -/

/-- **The initial-scale contrast is bounded by the dimensional polynomial.** -/
theorem widetildeThetaAtScale_zero_rebasedCutoffLaw_le_cutoffContrastBound [NeZero d]
    (params : Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d)
    {nu : ℝ} (hnu : 0 < nu) {m : ℕ} {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) :
    Book.Ch05.widetildeThetaAtScale (rebasedCutoffLaw nu m P) (0 : ℤ)
        (quantitativeCoarseGrainedEllipticity_rebasedCutoffLaw_of_largeCubeLinfty params hnu
          (cutoffLargeCubeLinfty hPrefix hJ2 hJ3 hJ4 m)) ≤
      cutoffContrastBound d params.xi nu m := by
  have hstep := widetildeThetaAtScale_zero_rebasedCutoffLaw_le_cutoffLargeCubeAmp (m := m)
    params hnu hPrefix hJ2 hJ3 hJ4
  have hamp := cutoffLargeCubeAmp_le (lt_of_lt_of_le (by norm_num) hPrefix.dimension) m
  have hampnn : 0 ≤ cutoffLargeCubeAmp d m := (cutoffLargeCubeAmp_pos hPrefix m).le
  have hG : (0 : ℝ) ≤ Real.Gamma ((params.xi : ℝ) + 1) :=
    Real.Gamma_nonneg_of_nonneg (by positivity)
  have hsq : cutoffLargeCubeAmp d m ^ (2 : ℕ) ≤
      (cutoffLargeCubeAmpConst d * (1 + (m : ℝ))) ^ (2 : ℕ) :=
    pow_le_pow_left₀ hampnn hamp 2
  have hcoef : (0 : ℝ) ≤ 4 * (1 + Real.Gamma ((params.xi : ℝ) + 1)) *
      (1 + 2 * nu⁻¹ ^ (2 : ℕ)) := by
    have h1 : (0 : ℝ) ≤ 4 * (1 + Real.Gamma ((params.xi : ℝ) + 1)) := by linarith only [hG]
    have h2 : (0 : ℝ) ≤ 1 + 2 * nu⁻¹ ^ (2 : ℕ) := by positivity
    exact mul_nonneg h1 h2
  refine le_trans hstep ?_
  rw [cutoffContrastBound]
  exact mul_le_mul_of_nonneg_left (by linarith only [hsq]) hcoef

/-- **The entry scale of the rebased cutoff law is dominated by
`C_0 log^2 (2 + poly(nu^{-1} m))`**, the printed threshold
`C_0 log^2 (nu^{-1} k)` of the paper. -/
theorem annealedEntryScale_rebasedCutoffLaw_le [NeZero d]
    (params : Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d)
    {nu : ℝ} (hnu : 0 < nu) {m : ℕ} {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) {C : ℝ} (hC : 0 < C) (sigma : ℝ) :
    ((Book.Ch05.annealedEntryScale (rebasedCutoffLaw nu m P)
        (quantitativeCoarseGrainedEllipticity_rebasedCutoffLaw_of_largeCubeLinfty params hnu
          (cutoffLargeCubeLinfty hPrefix hJ2 hJ3 hJ4 m)) C sigma : ℕ) : ℝ) ≤
      entryScaleLogSqConst params.xi C sigma *
        Real.log (2 + cutoffContrastBound d params.xi nu m) ^ (2 : ℕ) :=
  annealedEntryScale_le_mul_logSq _ hC (cutoffContrastBound_nonneg d params.xi nu m)
    (widetildeThetaAtScale_zero_rebasedCutoffLaw_le_cutoffContrastBound params hnu hPrefix
      hJ2 hJ3 hJ4)

/-- **The high-contrast entry bound under the printed threshold.** For every
scale separation `j` beyond `C_0 log^2 (2 + poly(nu^{-1} m))` — the manuscript's
`n - k >= C_0 log^2(nu^{-1} k)` of the paper — the two annealed diagonal blocks
of the cutoff field on `cu_{m + t_d + j}` satisfy
`shom_m <= (1 + sigma) shom_{m,*}`. Only the range of
dependence of the cutoff law remains open. The entry constant is chosen before
`nu`, `m` and `P`, so it is uniform in the law: the shape the assembly of
`l.b.ell.homogenization` consumes. -/
theorem sigmaBarScalar_le_mul_sigmaBarStarScalar_of_logSq_le [NeZero d]
    (params : Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (nu : ℝ) (_hnu : 0 < nu) (m : ℕ) (P : ProbabilityMeasure (ShellSeq d))
        (_hPrefix : ShellLawPrefix d P) (_hJ2 : ShellLawJ2 d P) (_hJ3 : ShellLawJ3 d P)
        (_hJ4 : ShellLawJ4 d P) (_hrange : CutoffRangeDependence nu m P),
        ∀ sigma : ℝ, 0 < sigma → sigma ≤ (1 / 2 : ℝ) →
          ∀ j : ℕ,
            entryScaleLogSqConst params.xi C sigma *
                Real.log (2 + cutoffContrastBound d params.xi nu m) ^ (2 : ℕ) ≤ (j : ℝ) →
            sigmaBarScalar nu m P
                (cubeSet (originCube d ((m + triadicOffset d + j : ℕ) : ℤ))) ≤
              (1 + sigma) * sigmaBarStarScalar nu m P
                (cubeSet (originCube d ((m + triadicOffset d + j : ℕ) : ℤ))) := by
  obtain ⟨C, hC, hbound⟩ := sigmaBarScalar_le_mul_sigmaBarStarScalar params
  refine ⟨C, hC, fun nu hnu m P hPrefix hJ2 hJ3 hJ4 hrange sigma hsigma hsigma' j hj ↦
    hbound nu hnu m P hPrefix hJ2 hJ3 hJ4 hrange sigma hsigma hsigma' j ?_⟩
  have hle := annealedEntryScale_rebasedCutoffLaw_le (m := m) params hnu hPrefix hJ2 hJ3 hJ4
    hC sigma
  exact_mod_cast le_trans hle hj


end

end SuperdiffusionCLT.Section3.HighContrast
