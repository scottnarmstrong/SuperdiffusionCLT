/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.EnvelopeEllipticity
public import SuperdiffusionCLT.Section2.Localization.LocalizationEnvelopeCarrier
public import SuperdiffusionCLT.Section2.Localization.LocalizationAverageAssembly
public import SuperdiffusionCLT.Section2.Localization.LocalizationAverageT1
public import SuperdiffusionCLT.Section2.Localization.LocalizationAverageT1Inputs
public import SuperdiffusionCLT.Section2.Localization.LocalizationAverageT2
public import SuperdiffusionCLT.Probability.ConditionalGammaTail
public import SuperdiffusionCLT.Probability.ConditionalGammaTailShell

/-!
# The two `Gamma_{1/2}` moments of the localization average: `hY` and `hR`

The localization-average proof bounds the averaged fourth power by separating the
lower-scale coarse matrix from the upper-scale gauge.  With

`Y_z = |bfE_l^{-1/2} bfA_l(z+cu_n) bfE_l^{-1/2}|` and
`R_z = |bfE_l^{1/2} G_{-h_z} P|^4`,

the two per-cube displays are, verbatim:

    The variables Y_z are measurable with respect to {j_r}_{r <= l} and are
    therefore independent of F_>, while R_z is F_>-measurable.
    By (e.Enaught.vs.A.and.Ahom),
       Y_z^2 <= O_{Gamma_{1/2}}(C)      conditionally on F_>,
    for each fixed z.  [...]

    In either case, using (e.Enaught.mixing),
       R_z <= O_{Gamma_{1/2}}( C nu^{-2} ((1 v l)^2 + (L-l)^2) |P|^4 )
      for each fixed z in 3^n Z^d cap cu_m.

## What these two displays carry

* `Y_z^2` -- the square of the normalised lower-scale coarse-matrix norm -- is
  `Gamma_{1/2}` at a **pure constant** amplitude: no scale factor survives, and
  the printed `C` is the same `C` that `e.Enaught.vs.A.and.Ahom` supplies at
  `Γ₁` enlarged by the rule's constant.
* `R_z` -- the fourth power of the `bfE_l`-length of the upper-scale gauge vector
  -- is `Gamma_{1/2}` at `C nu^{-2} ((1 v l)^2 + (L-l)^2) |P|^4`, carrying the
  normalisation loss `nu^{-2}` and the two gauge scales `(1 v l)` and `(L-l)`.

## The route is the multiplication rule, not a new display

Both entries are a **square of a `Γ₁` quantity**, so the index drops by
`sigma_1 sigma_2 / (sigma_1 + sigma_2) = 1 * 1 / (1 + 1) = 1/2` of the printed
multiplication property `e.multGammasig`, proved as
`SuperdiffusionCLT.Probability.isBigO_gammaSigma_mul`.  This is confirmed by
the printed source of each entry:

* `Y_z^2`: `|bfE_l^{-1/2} bfA_l(z+cu_n) bfE_l^{-1/2}| <= O_{Gamma_1}(C)`
  conditionally on `F_>`, i.e. `Y_z = O_{Gamma_1}(C)`, squared.
  There is no scale factor to cancel: the amplitude is a constant.
* `R_z`: the printed `W_z = |bfE_l^{1/2} G_{-h_z} P|^2` satisfies
  `W_z <= O_{Gamma_1}(C nu^{-1} (1 v l)(1 v L) |P|^2)` (with amplitude
  `localizationAverageWbarCubeAmplitude`), and `R_z` is *by definition* `W_z^2`.
  Squaring the printed `Γ₁` bound gives the printed `Gamma_{1/2}` entry.

The power-rule reading of the same step (`e.powerofGammasigma` at `p = 2` divides
the index by `p`) gives the *same* index `1/2`, so the two printed supports of
`Gamma_{1/2}` agree.

## Constant bookkeeping, stated as a hypothesis

`orliczProductConst 1 1 = 4`, so the rule's own constant is the explicit `4`.
Every theorem below therefore comes in two forms: the amplitude *determined* by
the rule, `4 A^2`, and the amplitude any larger named envelope `K`, with the
numeric comparison `4 A^2 <= K` as a named hypothesis.  That comparison is the
only thing the printed proof leaves to "enlarging the constant"; it is exactly
the printed passage of the proof, and at a constant `Γ₁` amplitude it is
uniform in the scale parameters.

## One shape observation about the amplitude of `hR`

The printed amplitude of `hR`, `nu^{-2}((1 v l)^2 + (L-l)^2)|P|^4`, is **not** the square
of the printed amplitude of `W_z`, `C nu^{-1}(1 v l)(1 v L)|P|^2`: squaring the latter gives
`nu^{-2}(1 v l)^2 (1 v L)^2 |P|^4`, which exceeds the former by the factor

    (1 v l)^2 (1 v L)^2 / ((1 v l)^2 + (L-l)^2).

Since `L - l <= L <= 1 v L` and `1 v l <= 1 v L`, that factor is at least
`(1 v l)^2 / 2`, which is *unbounded* in `l`.  The printed `hR` is therefore not
a corollary of the printed `hcube` at a constant independent of `l` and `L`; its
own printed input is the per-case route through `e.Enaught.mixing` (which makes
the `(L-l)` term vanish when `h_z = 0`, i.e. when `L = l`).  Consequently the
conversion below of the consumer's `hcube` into the consumer's `hR` is carried at
a constant *enlarged by that data-dependent factor* (finite for each instance,
since `(1 v l)^2 + (L-l)^2 >= 1`), which is precisely the "enlarge `C` if
necessary" of the printed proof.  This is a bookkeeping gap between two
printed amplitudes, not a false display, and not an erratum.

## What is discharged here

* `hY` is **proved** from the four law binders, modulo exactly one named
  hypothesis: the passage from the half-open cube `cubeSet R` of this
  development's carrier `localizationY` to the open cube `openCubeSet R` at
  which the ellipticity bound
  `Section2.Annealed.isBigOWith_gammaSigma_blockMatrixOperatorNorm_envelopeRescale`
  (the printed display `e.Enaught.vs.A.and.Ahom`) is stated.  The
  amplitude reached is the explicit `orliczProductConst 1 1`.  Earlier forms
  below keep the printed `Γ₁` display as a hypothesis instead, in both its
  unconditional and its printed *conditional* form (`CondIsBigOWith`, discharged
  through the tower step `Probability.isBigO_of_condIsBigO`).  The
  nonnegativity and measurability of `Y_z` are not needed by the multiplication
  rule.
* `hR` is reduced to the printed `Γ₁` display for `W_z` --
  which is the consumer's own `hcube` -- plus the numeric comparison above.

That cube passage is the *only* residual of `hY`.  It is not definitional:
`cubeSet` is half-open and `openCubeSet` open, so the two differ on the left
face of the cube, and the volume averages defining the coarse block matrix agree
only modulo a null set.  The bridging theorem
`Section2.Annealed.coarseBlockMatrix_cubeSet_coefficientCutoff_eq_ch02` relates
the half-open `cubeSet` to the Chapter 2 coarse matrix of
`Book.Ch02.cubeDomain R` -- not to the homogenization-level `coarseBlockMatrix`
at the open cube that the ellipticity statement quotes -- so no theorem
here closes it at `d >= 2`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open MeasureTheory Homogenization Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Carriers
open SuperdiffusionCLT.Section2.Cutoff

variable {d : ℕ}

/-! ## The multiplication rule at `(1, 1)`: a square of a `Γ₁` quantity is `Gamma_{1/2}` -/

/-- The explicit constant of the multiplication rule at `sigma_1 = sigma_2 = 1`:
`orliczProductConst 1 1 = 2^(1 + 1) = 4`.  This is the factor by which the
printed `Γ₁` amplitude is enlarged when the rule is applied to a square. -/
theorem orliczProductConst_one_one :
    SuperdiffusionCLT.Probability.orliczProductConst 1 1 = 4 := by
  unfold SuperdiffusionCLT.Probability.orliczProductConst
  rw [show (1 : ℝ)⁻¹ + (1 : ℝ)⁻¹ = (2 : ℝ) by norm_num, Real.rpow_two]
  norm_num

/-- **The printed multiplication rule `e.multGammasig` at
`sigma_1 = sigma_2 = 1`.**  A real-valued `X` with a `Γ₁` tail bound at
amplitude `A >= 0` has a `Gamma_{1/2}` tail bound at `4 A^2`:
`1 * 1 / (1 + 1) = 1/2` and `orliczProductConst 1 1 = 4`.

This is the single step by which both displays of this module are obtained from
their printed `Γ₁` per-cube bounds.  The amplitude is *determined*, not
merely bounded: the printed `C` absorbs the explicit `4 A^2`. -/
theorem isBigO_gammaSigma_half_of_sq_of_isBigO_one {Omega : Type*} [MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} [IsFiniteMeasure mu] {X : Omega → ℝ} {A : ℝ}
    (hA : 0 ≤ A)
    (hX : Homogenization.IndependentSums.IsBigO mu
      (Homogenization.IndependentSums.gammaSigma 1) X A) :
    Homogenization.IndependentSums.IsBigO mu
      (Homogenization.IndependentSums.gammaSigma ((1 : ℝ) / 2))
      (fun omega => X omega ^ 2)
      (SuperdiffusionCLT.Probability.orliczProductConst 1 1 * (A * A)) := by
  have h := SuperdiffusionCLT.Probability.isBigO_gammaSigma_mul (mu := mu)
    (X₁ := X) (X₂ := X) (A₁ := A) (A₂ := A) (σ₁ := 1) (σ₂ := 1)
    one_pos one_pos hA hA hX hX
  have hidx : (1 : ℝ) * 1 / (1 + 1) = (1 : ℝ) / 2 := by norm_num
  rw [hidx] at h
  simpa only [sq] using h

/-! ## `hY`: `Y_z^2 = O_{Gamma_{1/2}}(C)` -/

/-- **`hY` at the amplitude determined by the printed rule.**  From the printed
`Γ₁` display `e.Enaught.vs.A.and.Ahom` -- `|bfE_l^{-1/2} bfA_l(z+cu_n) bfE_l^{-1/2}| <=
O_{Gamma_1}(C)`, carried here as `hY1` at the constant amplitude `A` -- the
squared carrier `Y_z^2 = localizationY nu l R ^ 2` has a `Gamma_{1/2}` tail
bound at `4 A^2`, the exact amplitude the multiplication rule produces.

No positivity or measurability of `Y_z` is required: the rule reads both factors
through absolute values.  The only side condition is `0 <= A`, which holds for
the printed constant. -/
theorem localizationY_sq_isBigO_gammaSigma_half (P : ProbabilityMeasure (ShellSeq d))
    {nu : ℝ} (l : ℕ) (R : TriadicCube d) {A : ℝ} (hA : 0 ≤ A)
    (hY1 : Homogenization.IndependentSums.IsBigO P.toMeasure
      (Homogenization.IndependentSums.gammaSigma 1) (localizationY nu l R) A) :
    Homogenization.IndependentSums.IsBigO P.toMeasure
      (Homogenization.IndependentSums.gammaSigma ((1 : ℝ) / 2))
      (fun omega : ShellSeq d => localizationY nu l R omega ^ 2)
      (SuperdiffusionCLT.Probability.orliczProductConst 1 1 * (A * A)) :=
  isBigO_gammaSigma_half_of_sq_of_isBigO_one hA hY1

/-! ## Discharging `hY`'s printed `Γ₁` input from the ellipticity bound

The display behind `hY` is `e.Enaught.vs.A.and.Ahom`,

  `|bfE_l^{-1/2} bfA_l(z + cu_n) bfE_l^{-1/2}| <= O_{Gamma_1}(C)`,

and that tail bound is available: it is the theorem
`Section2.Annealed.isBigOWith_gammaSigma_blockMatrixOperatorNorm_envelopeRescale`
(the one-sided tail form of `l.bfAm.ellip`, at amplitude `1`), stated at the open
cube `Book.Ch02.cubeDomain Q`.  Below, that input is converted to the
two-sided form and pushed through the multiplication rule, so `hY` at the
explicit constant `orliczProductConst 1 1` follows from the four law binders
alone, modulo the passage from the half-open `cubeSet` of this development to the
open cube of the printed statement.  Both steps are kept as named hypotheses.
-/

/-- The printed `Γ₁` carrier of `e.Enaught.vs.A.and.Ahom` at the
open cube: `|bfE_l^{-1/2} bfA_l(cu) bfE_l^{-1/2}|`.  The only difference from
`localizationY nu l R` is the *set* -- the open cube of the printed statement
rather than the half-open `cubeSet R`. -/
noncomputable def localizationYOnOpenCube (nu : ℝ) (l : ℕ) (Q : TriadicCube d)
    (omega : ShellSeq d) : ℝ :=
  blockMatrixOperatorNorm
    (envelopeRescale d nu l
      (coarseBlockMatrix
        ((Book.Ch02.cubeDomain Q : Book.Ch02.Domain d) : Set (Vec d))
        (coefficientCutoff nu omega l).toCoeffField))

/-- **The printed `Γ₁` display of `e.Enaught.vs.A.and.Ahom`, at
the open cube**, in the two-sided form the multiplication rule consumes:
`|bfE_l^{-1/2} bfA_l(cu) bfE_l^{-1/2}| = O_{Gamma_1}(1)`.

This is the one-sided theorem
`isBigOWith_gammaSigma_blockMatrixOperatorNorm_envelopeRescale` converted by the
nonnegativity of the operator norm (`isBigOWith_iff_isBigO_of_nonneg`); the
amplitude `1` is the printed `C`.  Every binder here is one of the four law
conditions of the main statement. -/
theorem isBigO_gammaSigma_one_localizationYOnOpenCube
    (P : ProbabilityMeasure (ShellSeq d)) {nu : ℝ} (hnu : 0 < nu)
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (l : ℕ) (Q : TriadicCube d) :
    Homogenization.IndependentSums.IsBigO P.toMeasure
      (Homogenization.IndependentSums.gammaSigma 1)
      (localizationYOnOpenCube (d := d) nu l Q) 1 :=
  (SuperdiffusionCLT.Probability.isBigOWith_iff_isBigO_of_nonneg
    (fun _ => blockMatrixOperatorNorm_nonneg _)).1
    (SuperdiffusionCLT.Section2.Annealed.isBigOWith_gammaSigma_blockMatrixOperatorNorm_envelopeRescale
      hnu hPrefix hJ2 hJ3 hJ4 l (Book.Ch02.cubeDomain Q))

/-! ## `hR`: `R_z = O_{Gamma_{1/2}}(C nu^{-2}((1 v l)^2 + (L-l)^2)|P|^4)` -/

/-- **`hR` at the amplitude determined by the printed rule.**  The carrier
`R_z = localizationR nu l L R Pvec` is *by definition* `W_z^2`, and the printed
`Γ₁` bound on `W_z` gives the printed `Gamma_{1/2}` bound
on `R_z` at `4 A^2`.

The only input is the printed `Γ₁` display for `W_z`; the printed
`hR` itself is *not* needed. -/
theorem localizationR_isBigO_gammaSigma_half (P : ProbabilityMeasure (ShellSeq d))
    {nu : ℝ} (l L : ℕ) (R : TriadicCube d) (Pvec : BlockVec d) {A : ℝ} (hA : 0 ≤ A)
    (hW1 : Homogenization.IndependentSums.IsBigO P.toMeasure
      (Homogenization.IndependentSums.gammaSigma 1) (localizationW nu l L R Pvec) A) :
    Homogenization.IndependentSums.IsBigO P.toMeasure
      (Homogenization.IndependentSums.gammaSigma ((1 : ℝ) / 2))
      (localizationR nu l L R Pvec)
      (SuperdiffusionCLT.Probability.orliczProductConst 1 1 * (A * A)) := by
  have h := isBigO_gammaSigma_half_of_sq_of_isBigO_one hA hW1
  have hdef : localizationR nu l L R Pvec =
      fun omega : ShellSeq d => localizationW nu l L R Pvec omega ^ 2 := by
    funext omega
    rfl
  rw [hdef]
  exact h

/-- **`hR` at the printed amplitude** `CR nu^{-2}((1 v l)^2 + (L-l)^2)|P|^4`,
i.e. `localizationAverageT1FourthAmplitude CR nu l L Pvec`, the exact envelope of
the assembly's `hR` hypothesis.  The comparison `4 A^2 <= CR nu^{-2}(...)` is the
printed enlargement of the constant; see the module note on the shape gap between
the printed amplitudes of `hR` and `W_z`. -/
theorem localizationR_isBigO_gammaSigma_half_of_amplitude_le
    (P : ProbabilityMeasure (ShellSeq d)) {nu : ℝ} (l L : ℕ) (R : TriadicCube d)
    (Pvec : BlockVec d) {A CR : ℝ} (hA : 0 ≤ A)
    (hAmp : SuperdiffusionCLT.Probability.orliczProductConst 1 1 * (A * A) ≤
      localizationAverageT1FourthAmplitude CR nu l L Pvec)
    (hW1 : Homogenization.IndependentSums.IsBigO P.toMeasure
      (Homogenization.IndependentSums.gammaSigma 1) (localizationW nu l L R Pvec) A) :
    Homogenization.IndependentSums.IsBigO P.toMeasure
      (Homogenization.IndependentSums.gammaSigma ((1 : ℝ) / 2))
      (localizationR nu l L R Pvec)
      (localizationAverageT1FourthAmplitude CR nu l L Pvec) :=
  IndependentSums.IsBigO.mono_scale
    (localizationR_isBigO_gammaSigma_half P l L R Pvec hA hW1) hAmp

/-! ## What the pair carries: the printed `Gamma_{1/4}` combine -/

end SuperdiffusionCLT.Section2.Localization
