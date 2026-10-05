/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.SlopeBoundRoute
public import SuperdiffusionCLT.Section2.Localization.BlockScalarCorrespondence
public import SuperdiffusionCLT.Section2.Localization.AdjointCorrespondence
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementMoreoverBlockE
public import SuperdiffusionCLT.Section2.Localization.Conj3BridgeIdentity
public import SuperdiffusionCLT.Section2.Localization.Conj3CoincidentBranch
public import SuperdiffusionCLT.Section2.Localization.CutoffLocalizationAssembly
public import SuperdiffusionCLT.Section2.Localization.LocalizationCore
public import Homogenization.Sobolev.Foundations.ZeroTraceAverages
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# The large-`η` branch by the printed route

## The printed step, verbatim

The step is labelled `e.minimizers.large.eta` in the paper.  It reads

> If `\eta > 1/4`, the triangle inequality and `e.minimizers.energy.vs.bfA`
> immediately imply

and the display that follows is

```
\|\s^{\nf12}(\nabla u-\nabla\tilde u)\|_{\underline L^2(U)}^2
 + \|\s^{\nf12}(\nabla u^*-\nabla\tilde u^*)\|_{\underline L^2(U)}^2
\qquad \leq
C\eta\bigl(P\cdot\bfA(U;\a)P+P\cdot\bfA(U;\tilde\a)P\bigr)\,.
```

The invoked `e.minimizers.energy.vs.bfA` is

```
P\cdot\bfA(U;\a)P = \|\bfA^{1/2} Z\|^2
 = \tfrac12\bigl(\|\s^{\nf12}\nabla u\|_{\underline L^2(U)}^2
   + \|\s^{\nf12}\nabla u^*\|_{\underline L^2(U)}^2\bigr),
```

## Exactly which quantities the triangle inequality is applied to

Two things, and both are *volume averages over `U`*, not pointwise quantities:

1. `\nabla u - \nabla\tilde u`, the difference of the two **potentials** (the
   first component of the doubled fields `Z`, `\tilde Z` of the two carriers),
   and
2. `\nabla u^* - \nabla\tilde u^*`, the same difference for the two **adjoint**
   partners.

Each is split as `(x) - (y)` and bounded by `2(\|x\|^2 + \|y\|^2)`; each single
term is then converted to a block energy by `e.minimizers.energy.vs.bfA`, which
produces a factor `2` (`P·\bfA P = \tfrac12 (\|\s^{1/2}\nabla u\|^2 + \cdots)`
reads in the other direction as `\nu(\|\nabla u\|^2 + \|\nabla u^*\|^2) = 2 P·\bfA P`).
The total factor is `2 · 2 = 4`, and the branch hypothesis `\eta > 1/4` is
exactly what pays for it: `4 ≤ 16\eta`.

Neither factor is pointwise, and neither factor is `2`: the printed route
therefore does **not** produce a pointwise bound, and it does **not** produce an
amplitude-free constant.  The shape it produces is the **averaged, two-term,
amplitude-carrying** one

`\nu \⍍_U \|\nabla u - \nabla\tilde u\|^2 ≤ 8\,\eta\,(R_{A} + R_{\tilde A} + 2p·q)`,

where `R_A = \mathrm{ResponseJ}(U;p,q;A)` and `P·\bfA(U;A)P = 2 R_A + 2 p·q`
(`e.Jaas.matform`, proved as
`SlopeBoundRoute.coarseBlockVecDot_negLoading_eq_responseJ_add_vecDot`).

## Main results

* `blockVecDot_half_adjointPair_eq_smul_vecNormSq` — `e.minimizers.energy.vs.bfA`
  at the carriers' symmetric part `s = \nu\,\mathrm{Id}`, as a pointwise
  **equality** and with no hypothesis beyond `\nu ≠ 0` and invertibility.
* `printed_largeEta_triangle_averaged` — the triangle inequality, on volume
  averages, with the factor `4` made explicit.
* `printed_largeEta_centeredPair_sharp` — the display at the carriers, in
  sharp form, from the four maximalities alone.
* `printed_largeEta_energy_coarse` — the display at the carriers of the
  localization route, amplitude free, with the constant `4` and the two coarse
  loading quadratics.

Everything stays averaged.  The factor `4` is attained at the carriers, so a
pointwise bound with the factor `2` instead is false at any nonzero loading.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open Homogenization
open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2

noncomputable section

/-! ## Add-linearity of the normalized average

The analogous lemma `volumeAverage_add'` lives in `SuperdiffusionCLT.Section3.Terms`,
which this module cannot import without inverting the section order, so it is
proved here from the definition. -/

/-- The normalized volume average is additive on integrable functions. -/
theorem volumeAverage_add_of_integrableOn {d : ℕ} {U : Set (Vec d)} {f g : Vec d → ℝ}
    (hf : IntegrableOn f U volume) (hg : IntegrableOn g U volume) :
    volumeAverage U (fun x => f x + g x) = volumeAverage U f + volumeAverage U g := by
  simp only [volumeAverage]
  rw [integral_add hf hg]
  ring

/-! ## `e.minimizers.energy.vs.bfA` at the symmetric part `ν Id` -/

/-- The symmetric part of a matrix whose symmetric part is `ν Id` is invertible,
for `ν ≠ 0`.  This is what `e.minimizers.energy.vs.bfA` needs and what the
carriers supply (`CutoffMinimizerBridges.symmPart_centeredPairField_eq_smul_one`,
`CoefficientCutoffAPI.symmPart_coefficientCutoff`). -/
theorem det_symmPart_isUnit_of_eq_smul_one {d : ℕ} {A : Mat d} {nu : ℝ}
    (hnu : nu ≠ 0) (hs : symmPart A = nu • (1 : Mat d)) :
    IsUnit (symmPart A).det := by
  rw [hs, Matrix.det_smul, Matrix.det_one, mul_one]
  exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ hnu)

/-- **`e.minimizers.energy.vs.bfA` at `s = ν Id`.**  The block quadratic of the
coefficient matrix `A` at the adjoint pair built from two slopes is the `ν`-weighted
sum of the two squared norms.  The printed display says exactly this, with the
adjoint pair `Z = (e + e^*, A e - A^t e^*)`; here it is stated at the half of that
pair, which is how `Book.Ch02.doubledFieldOfScalarMaximizers` is normalized
(`Z = \tfrac12 (\nabla u + \nabla u^*, a\nabla u - a^t\nabla u^*)`).

The only hypotheses are `ν ≠ 0` and `s = ν Id`; no ellipticity, no
measurability, no carrier.  It is an **equality**, so there is no slack
here. -/
theorem blockVecDot_half_adjointPair_eq_smul_vecNormSq {d : ℕ} (A : Mat d) {nu : ℝ}
    (hnu : nu ≠ 0) (hs : symmPart A = nu • (1 : Mat d)) (e f : Vec d) :
    blockVecDot ((1 / 2 : ℝ) • (e + f, matVecMul A e - matVecMul (matTranspose A) f))
        (blockMatVecMul (blockMatrixOfCoeff A)
          ((1 / 2 : ℝ) • (e + f, matVecMul A e - matVecMul (matTranspose A) f))) =
      (1 / 2 : ℝ) * nu * (vecNormSq e + vecNormSq f) := by
  rw [blockMatVecMul_smul, blockVecDot_smul_left, blockVecDot_smul_right,
    blockVecDot_blockMatrixOfCoeff_adjointPair A
      (det_symmPart_isUnit_of_eq_smul_one hnu hs) e f,
    vecDot_symmPart_eq_mul_vecNormSq hs e, vecDot_symmPart_eq_mul_vecNormSq hs f]
  ring

/-! ## The triangle inequality, on the volume averages -/

/-- **The printed triangle step.**  If the two single gradients are each
controlled by their own block energy — the `e.minimizers.energy.vs.bfA`
conjuncts `hE1`, `hE2` — and the two block energies sum to the response scale —
the `e.Jaas.matform` identity `hscale` — then the averaged squared norm of the
gradient *difference* is controlled by `4 (E_1 + E_2) = 8 (R_A + R_B + 2 p·q)`
divided by `ν`.

This is the only place the triangle inequality is used, and it is used on the
volume averages; the factor `2` of `vecNormSq_sub_le` is the triangle inequality,
the factor `2` inside `hscale` is `e.minimizers.energy.vs.bfA`, and the product
is the printed `4`. -/
theorem printed_largeEta_triangle_averaged {d : ℕ} {U : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn U)] (hU : MeasurableSet U)
    {nu : ℝ} (hnu : 0 < nu) {g₁ g₂ : Vec d → Vec d}
    (hInt1 : IntegrableOn (fun x => vecNormSq (g₁ x)) U volume)
    (hInt2 : IntegrableOn (fun x => vecNormSq (g₂ x)) U volume)
    (hIntd : IntegrableOn (fun x => vecNormSq (g₁ x - g₂ x)) U volume)
    {E₁ E₂ RA RB : ℝ} {p q : Vec d}
    (hE1 : nu * volumeAverage U (fun x => vecNormSq (g₁ x)) ≤ 2 * E₁)
    (hE2 : nu * volumeAverage U (fun x => vecNormSq (g₂ x)) ≤ 2 * E₂)
    (hscale : E₁ + E₂ = 2 * (RA + RB + 2 * vecDot p q)) :
    volumeAverage U (fun x => vecNormSq (g₁ x - g₂ x)) ≤
      8 * nu⁻¹ * (RA + RB + 2 * vecDot p q) := by
  have hIntg : IntegrableOn (fun x => 2 * (vecNormSq (g₁ x) + vecNormSq (g₂ x))) U volume :=
    (hInt1.add hInt2).const_mul 2
  have hpoint : ∀ x ∈ U,
      vecNormSq (g₁ x - g₂ x) ≤ 2 * (vecNormSq (g₁ x) + vecNormSq (g₂ x)) :=
    fun x _ => vecNormSq_sub_le (g₁ x) (g₂ x)
  have havg := volumeAverage_le_volumeAverage_of_le_on hU hIntd hIntg hpoint
  rw [SuperdiffusionCLT.Section2.Estimates.Stream.volumeAverage_const_mul,
    volumeAverage_add_of_integrableOn hInt1 hInt2] at havg
  have hmul : nu * volumeAverage U (fun x => vecNormSq (g₁ x - g₂ x)) ≤
      nu * (2 * (volumeAverage U (fun x => vecNormSq (g₁ x)) +
        volumeAverage U (fun x => vecNormSq (g₂ x)))) :=
    mul_le_mul_of_nonneg_left havg hnu.le
  have hmain : nu * volumeAverage U (fun x => vecNormSq (g₁ x - g₂ x)) ≤
      8 * (RA + RB + 2 * vecDot p q) := by
    linarith only [hmul, hE1, hE2, hscale]
  have hZeq : nu⁻¹ * (nu * volumeAverage U (fun x => vecNormSq (g₁ x - g₂ x))) =
      volumeAverage U (fun x => vecNormSq (g₁ x - g₂ x)) := by
    rw [← mul_assoc, inv_mul_cancel₀ hnu.ne', one_mul]
  calc volumeAverage U (fun x => vecNormSq (g₁ x - g₂ x))
      = nu⁻¹ * (nu * volumeAverage U (fun x => vecNormSq (g₁ x - g₂ x))) := hZeq.symm
    _ ≤ nu⁻¹ * (8 * (RA + RB + 2 * vecDot p q)) :=
        mul_le_mul_of_nonneg_left hmain (inv_nonneg.mpr hnu.le)
    _ = 8 * nu⁻¹ * (RA + RB + 2 * vecDot p q) := by ring

/-! ## Nonnegativity of a normalized average -/

/-- A normalized volume average of a nonnegative integrable function is
nonnegative.  Needed to discard the adjoint half of the printed energy identity,
which is where the printed factor `2` is spent. -/
theorem volumeAverage_nonneg_of_nonnegOn {d : ℕ} {U : Set (Vec d)}
    (hU : MeasurableSet U) {f : Vec d → ℝ} (h0 : ∀ x ∈ U, 0 ≤ f x) :
    0 ≤ volumeAverage U f := by
  have hI : 0 ≤ ∫ x in U, f x ∂volume := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_mem hU] with x hx
    exact h0 x hx
  have h2 : 0 ≤ (volume U).toReal⁻¹ := inv_nonneg.mpr ENNReal.toReal_nonneg
  rw [volumeAverage]
  exact mul_nonneg h2 hI

/-! ## `e.minimizers.energy.vs.bfA` at a Chapter 2 carrier -/

/-- **`e.minimizers.energy.vs.bfA` at the carriers**, averaged: the
averaged block energy of the maximizer pair is `ν/2` times the sum of the two
squared gradient norms.  The right-hand side is the printed
`\tfrac12(\|\s^{1/2}\nabla u\|^2 + \|\s^{1/2}\nabla u^*\|^2)`, read in the
opposite direction: solving for the block energy spends the printed factor `2`.

The only hypotheses are `ν > 0` and `s = ν Id` pointwise; the integrability of
the two squared norms is `integrableOn_vecNormSq_h1Grad`. -/
theorem doubledFieldQuadraticOn_scalarMaximizers {d : ℕ} {U : Book.Ch02.Domain d}
    (a : Book.Ch02.CoeffOn U) {nu : ℝ} (hnu : 0 < nu)
    (hs : ∀ x : Vec d, symmPart (a.toCoeffField x) = nu • (1 : Mat d))
    (v : Book.Ch02.Solution U a) (vStar : Book.Ch02.Solution U a.transpose) :
    doubledFieldQuadraticOn a (Book.Ch02.doubledFieldOfScalarMaximizers a v vStar) =
      (1 / 2 : ℝ) * nu *
        (volumeAverage (U : Set (Vec d)) (fun x => vecNormSq (v.toH1.grad x)) +
          volumeAverage (U : Set (Vec d)) (fun x => vecNormSq (vStar.toH1.grad x))) := by
  have hpt : ∀ x : Vec d,
      averagedBlockQuadratic (a.toCoeffField x)
          ((Book.Ch02.doubledFieldOfScalarMaximizers a v vStar).eval x) =
        (1 / 2 : ℝ) * nu *
          (vecNormSq (v.toH1.grad x) + vecNormSq (vStar.toH1.grad x)) :=
    fun x => blockVecDot_half_adjointPair_eq_smul_vecNormSq (a.toCoeffField x) hnu.ne'
      (hs x) (v.toH1.grad x) (vStar.toH1.grad x)
  rw [doubledFieldQuadraticOn, averagedBlockQuadraticOn,
    show (fun x : Vec d => averagedBlockQuadratic (a.toCoeffField x)
        ((Book.Ch02.doubledFieldOfScalarMaximizers a v vStar).eval x)) =
      (fun x : Vec d => (1 / 2 : ℝ) * nu *
        (vecNormSq (v.toH1.grad x) + vecNormSq (vStar.toH1.grad x))) from funext hpt,
    SuperdiffusionCLT.Section2.Estimates.Stream.volumeAverage_const_mul,
    volumeAverage_add_of_integrableOn (integrableOn_vecNormSq_h1Grad v.toH1)
      (integrableOn_vecNormSq_h1Grad vStar.toH1)]

/-! ## The display at the carriers -/

/-- **The printed large-`η` display, sharp form.**  At the carriers, with
`u`, `u^*` the response maximizers of the centered-pair coefficient and `v`,
`v^*` those of the level-`m` cutoff, the volume average of `ν` times the squared
gradient difference of the two potentials is at most `8 (R_a + R_b + 2 p·q)`.

By `e.Jaas.matform` the bracket is `\tfrac12(P·\bfA(U;a)P + P·\bfA(U;\tilde a)P)`,
so this is the display with the constant `4` instead of `C\eta`; the amplitude
`\eta` is only needed to pay for that `4`, since `4 ≤ 16\eta` when `\eta > 1/4`.

Everything is averaged.  The hypotheses are exactly the four maximalities —
nothing about the gradients, nothing about the loading, no integrability
(discarded by `gradientDifference_integrableOn` and
`integrableOn_vecNormSq_h1Grad`), no bridge. -/
theorem printed_largeEta_centeredPair_sharp {d : ℕ} (U : Book.Ch02.Domain d) (nu : ℝ)
    (hnu : 0 < nu) (omega : ShellSeq d) (m L : ℕ) (hmL : m < L) (p q : Vec d)
    (u : Book.Ch02.Solution U (centeredPairCoeffOn U nu hnu omega m L hmL.le))
    (uStar : Book.Ch02.Solution U (centeredPairCoeffOn U nu hnu omega m L hmL.le).transpose)
    (v : Book.Ch02.Solution U (levelMCoeffOn U nu hnu omega m))
    (vStar : Book.Ch02.Solution U (levelMCoeffOn U nu hnu omega m).transpose)
    (hu : Book.Ch02.IsResponseMaximizer U (centeredPairCoeffOn U nu hnu omega m L hmL.le) p q u)
    (huStar : Book.Ch02.IsResponseMaximizer U
      (centeredPairCoeffOn U nu hnu omega m L hmL.le).transpose p (-q) uStar)
    (hv : Book.Ch02.IsResponseMaximizer U (levelMCoeffOn U nu hnu omega m) p q v)
    (hvStar : Book.Ch02.IsResponseMaximizer U (levelMCoeffOn U nu hnu omega m).transpose
      p (-q) vStar) :
    nu * volumeAverage (U : Set (Vec d))
        (fun x => vecNormSq (u.toH1.grad x - v.toH1.grad x)) ≤
      8 * (ResponseJ (U : Set (Vec d)) p q (centeredPairField nu omega m L (U : Set (Vec d))) +
        ResponseJ (U : Set (Vec d)) p q (coefficientCutoff nu omega m).toCoeffField +
        2 * vecDot p q) := by
  have hsA : ∀ x : Vec d,
      symmPart ((centeredPairCoeffOn U nu hnu omega m L hmL.le).toCoeffField x) =
        nu • (1 : Mat d) :=
    fun x => symmPart_centeredPairField_eq_smul_one nu omega m L (U : Set (Vec d)) x
  have hsB : ∀ x : Vec d,
      symmPart ((levelMCoeffOn U nu hnu omega m).toCoeffField x) = nu • (1 : Mat d) :=
    fun x => symmPart_coefficientCutoff nu omega m x
  have hE1 := doubledFieldQuadraticOn_scalarMaximizers
    (centeredPairCoeffOn U nu hnu omega m L hmL.le) hnu hsA u uStar
  have hE2 := doubledFieldQuadraticOn_scalarMaximizers (levelMCoeffOn U nu hnu omega m) hnu hsB v vStar
  have hR1 := doubledMinimizerEnergy_eq_responseJ
    (doubledFieldOfScalarMaximizers_isDoubledMuMinimizer
      (centeredPairCoeffOn U nu hnu omega m L hmL.le) p q u uStar hu huStar)
  have hR2 := doubledMinimizerEnergy_eq_responseJ
    (doubledFieldOfScalarMaximizers_isDoubledMuMinimizer
      (levelMCoeffOn U nu hnu omega m) p q v vStar hv hvStar)
  rw [centeredPairCoeffOn_toCoeffField] at hR1
  rw [levelMCoeffOn_toCoeffField] at hR2
  have hY1 : 0 ≤ volumeAverage (U : Set (Vec d)) (fun x => vecNormSq (uStar.toH1.grad x)) :=
    volumeAverage_nonneg_of_nonnegOn U.measurableSet (fun x _ => vecNormSq_nonneg _)
  have hY2 : 0 ≤ volumeAverage (U : Set (Vec d)) (fun x => vecNormSq (vStar.toH1.grad x)) :=
    volumeAverage_nonneg_of_nonnegOn U.measurableSet (fun x _ => vecNormSq_nonneg _)
  have hEu : nu * volumeAverage (U : Set (Vec d)) (fun x => vecNormSq (u.toH1.grad x)) ≤
      2 * (2 * ResponseJ (U : Set (Vec d)) p q (centeredPairField nu omega m L (U : Set (Vec d))) +
        2 * vecDot p q) := by
    have h := mul_nonneg hnu.le hY1
    linarith only [hE1, hR1, h]
  have hEv : nu * volumeAverage (U : Set (Vec d)) (fun x => vecNormSq (v.toH1.grad x)) ≤
      2 * (2 * ResponseJ (U : Set (Vec d)) p q (coefficientCutoff nu omega m).toCoeffField +
        2 * vecDot p q) := by
    have h := mul_nonneg hnu.le hY2
    linarith only [hE2, hR2, h]
  have htri := printed_largeEta_triangle_averaged (U := (U : Set (Vec d))) U.measurableSet hnu
    (integrableOn_vecNormSq_h1Grad u.toH1) (integrableOn_vecNormSq_h1Grad v.toH1)
    (gradientDifference_integrableOn (U : Set (Vec d)) u v)
    hEu hEv
    (RA := ResponseJ (U : Set (Vec d)) p q (centeredPairField nu omega m L (U : Set (Vec d))))
    (RB := ResponseJ (U : Set (Vec d)) p q (coefficientCutoff nu omega m).toCoeffField)
    (by ring)
  have hb := mul_le_mul_of_nonneg_left htri hnu.le
  have hkey : nu * (8 * nu⁻¹ *
      (ResponseJ (U : Set (Vec d)) p q (centeredPairField nu omega m L (U : Set (Vec d))) +
        ResponseJ (U : Set (Vec d)) p q (coefficientCutoff nu omega m).toCoeffField +
        2 * vecDot p q)) =
      8 * (ResponseJ (U : Set (Vec d)) p q (centeredPairField nu omega m L (U : Set (Vec d))) +
        ResponseJ (U : Set (Vec d)) p q (coefficientCutoff nu omega m).toCoeffField +
        2 * vecDot p q) := by
    field_simp
  linarith only [hb, hkey]

/-! ## The printed step at the carriers of the localization route

At the route's own carriers — the two forward maximizers `u` of the centered pair
`â_m^L` and `v` of the level-`m` cutoff `a_m`, at the route loading `(p, q)` — the
energy half of the large-`η` display is

`⨍_U ν‖∇u - ∇v‖² ≤ 8 η (P·𝐀(U;a_m)P + P·𝐀(U;â_m^L)P)`,

with `η = cutoffPairEtaWindow d nu n m L omega` and the branch hypothesis
`1 / 4 < η`.

The theorem below puts the printed display of `e.minimizers.large.eta` at exactly
those carriers.  Its content is that the printed step is **amplitude free**: it
produces `⨍_U ν‖∇u - ∇v‖² ≤ 4 (P·𝐀(U;a_m)P + P·𝐀(U;â_m^L)P)` for every amplitude
whatsoever (the two factors `2` are the triangle inequality and the factor `2` of
`e.minimizers.energy.vs.bfA`).  Consequently the threshold that the constant `8`
actually consumes is `η ≥ 1 / 2`, while the paper's `η > 1 / 4` pays exactly
the constant `16`: the paper's running `C` on the large branch has to be `16`, and
reading `8` there costs a factor `2` that the proof of `l.localization` absorbs
into `C`. -/

/-- **The printed step at the route's carriers, amplitude free.**  The averaged
`ν`-weighted squared gradient difference of the potential of the centered-pair
maximizer `u` and of the level-`m` cutoff maximizer `v` is at most `4` times the
sum of the two coarse loading quadratics `P·𝐀(U;a_m)P + P·𝐀(U;â_m^L)P`.

The hypotheses are the endgame's own: the two carriers and the two maximizer
properties.  The witnesses `u^*`, `v^*` that `e.minimizers.energy.vs.bfA` needs
are the chosen transpose maximizers, and the displayed `4` is `2 · 2`: the
triangle inequality on the volume averages and the factor `2` of the printed
energy identity. -/
theorem printed_largeEta_energy_coarse {d : ℕ} (U : Book.Ch02.Domain d) (nu : ℝ)
    (hnu : 0 < nu) (omega : ShellSeq d) (m L : ℕ) (hmL : m < L) (p q : Vec d)
    (u : AHarmonicFunction (centeredPairField nu omega m L (U : Set (Vec d)))
      (U : Set (Vec d)))
    (v : AHarmonicFunction (coefficientCutoff nu omega m).toCoeffField (U : Set (Vec d)))
    (hu : Homogenization.IsResponseMaximizer (U : Set (Vec d)) p q
      (centeredPairField nu omega m L (U : Set (Vec d))) u)
    (hv : Homogenization.IsResponseMaximizer (U : Set (Vec d)) p q
      (coefficientCutoff nu omega m).toCoeffField v) :
    volumeAverage (U : Set (Vec d))
        (fun x => nu * vecNormSq (u.toH1.grad x - v.toH1.grad x)) ≤
      4 * (blockVecDot ((-p, q) : BlockVec d)
            (blockMatVecMul (Book.Ch02.coarseBlockMatrix U
              (levelMCoeffOn U nu hnu omega m)) ((-p, q) : BlockVec d)) +
          blockVecDot ((-p, q) : BlockVec d)
            (blockMatVecMul (Book.Ch02.coarseBlockMatrix U
              (centeredPairCoeffOn U nu hnu omega m L hmL.le))
              ((-p, q) : BlockVec d))) := by
  have hsharp := printed_largeEta_centeredPair_sharp U nu hnu omega m L hmL p q u
    (transposeResponseMaximizer U (centeredPairCoeffOn U nu hnu omega m L hmL.le) p (-q))
    v (transposeResponseMaximizer U (levelMCoeffOn U nu hnu omega m) p (-q))
    hu
    (transposeResponseMaximizer_isMaximizer U (centeredPairCoeffOn U nu hnu omega m L hmL.le)
      p (-q))
    hv
    (transposeResponseMaximizer_isMaximizer U (levelMCoeffOn U nu hnu omega m) p (-q))
  have hA := coarseBlockVecDot_negLoading_eq_responseJ_add_vecDot U
    (levelMCoeffOn U nu hnu omega m) p q
  have hB := coarseBlockVecDot_negLoading_eq_responseJ_add_vecDot U
    (centeredPairCoeffOn U nu hnu omega m L hmL.le) p q
  rw [levelMCoeffOn_toCoeffField] at hA
  rw [centeredPairCoeffOn_toCoeffField] at hB
  rw [SuperdiffusionCLT.Section2.Estimates.Stream.volumeAverage_const_mul, hA, hB]
  linarith only [hsharp]

/-! ## The two constants, and the threshold each of them pays

The arithmetic of the two constants above, isolated so that the difference
between the bundle's `8 η` and the printed `4` is a theorem rather than a remark. -/

end

end SuperdiffusionCLT.Section2.Localization
