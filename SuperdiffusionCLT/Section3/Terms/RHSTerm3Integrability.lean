/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3AnchorsConstFirst
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3MemFluxB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3QuadZc
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3SideConditionsB

/-!
# The two `P`-integrability side conditions of term 3

The final assembly of `e.RHS.term3` carries two sample-side
integrability residues beyond the five printed steps: `hPair`, the
`P`-integrability of the very left-hand side of the conclusion, and
`_hbHalfInt`, the half-weight carrier on the printed range of `e.bL.to.bhomell`:
`z'` a sub-cube of `cu_m` and `z` a sub-cube of `z'`.

This module discharges `hPair` from the statement's own binders.  The
left-hand side is the cube mean over `cu_m` of the pairing of the response
gradient with the cutoff flux of the glued-field difference; Cauchy-Schwarz on
the cube (`Section2.Norms.abs_volumeAverage_vecDot_le_mul`) bounds it by the
product of the two normalized cube norms, and the extended integral of that
product is finite because each factor has a finite annealed second moment:

* the flux factor is dominated by the `L^∞(cu_m)` coefficient envelope times
  the deterministic energy of the glued-field difference
  (`vecCubeLpENorm_gluedGradientField_diff_subcube_B`), so its second moment is
  the second moment of `coeffLinftySupBound nu S.LPrime S.m`, which is finite at
  the enlarged cutoff (`integrable_coeffLinftySupBound_sq_at_B`);
* the response-gradient factor is dominated by the `Γ₂` envelope of
  `e.nablaw.Lt` (`l_w_basic_regbounds_window`) through the exponent downgrade
  `‖·‖_{L̲²} ≤ ‖·‖_{L̲^8}` on the probability measure of the cube, so its second
  moment is finite by `integrable_abs_rpow_of_isBigO_gammaSigma_two`.

Both factors are measurable in the sample for the same reason: the response
gradient is `⍍`-equivalent to the canonical Dirichlet response
(`grad_ae_eq_dirichletResponse`), whose gradient class is measurable
(`measurable_gradToHilbertVectorL2_dirichletResponse`), and the flux class is the
difference of two measurable glued-field classes
(`aemeasurable_toHilbertVectorL2OfVecField_pairingField_of_gluedClass`).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory ProbabilityTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

noncomputable section

/-! ## The abstract pairing lemma -/

/-- `a * b ≤ a² + b²` for extended nonnegative reals, the `AM-GM` step that
turns the Cauchy-Schwarz product under the integral sign into a sum of two
second moments. -/
private theorem mul_le_sq_add_sq_final (a b : ℝ≥0∞) :
    a * b ≤ a ^ (2 : ℕ) + b ^ (2 : ℕ) := by
  rcases le_total a b with h | h
  · calc a * b ≤ b * b := mul_le_mul' h le_rfl
      _ = b ^ (2 : ℕ) := (pow_two b).symm
      _ ≤ a ^ (2 : ℕ) + b ^ (2 : ℕ) := le_add_self
  · calc a * b ≤ a * a := mul_le_mul' le_rfl h
      _ = a ^ (2 : ℕ) := (pow_two a).symm
      _ ≤ a ^ (2 : ℕ) + b ^ (2 : ℕ) := le_self_add

/-- **The cube mean of the pairing of two annealed-`L²` fields is integrable in
the sample.**  Measurability is the inner product of the two `L²(cu_m)` classes
(`Section3.Setup.volumeAverage_vecDot_eq_inner`); the bound is Cauchy-Schwarz on
the cube (`Section2.Norms.abs_volumeAverage_vecDot_le_mul`); and finiteness is
the two annealed squared cube norms, through `a * b ≤ a² + b²` on `ℝ≥0∞`. -/
theorem integrable_volumeAverage_pairing_final {d : ℕ} [NeZero d]
    {P : ProbabilityMeasure (ShellSeq d)} {Q : TriadicCube d}
    {Rf gf : ShellSeq d → Vec d → Vec d}
    (hRL2 : ∀ omega : ShellSeq d, MemVectorL2 (openCubeSet Q) (Rf omega))
    (hRclass : AEMeasurable (fun omega : ShellSeq d =>
      toHilbertVectorL2OfVecField (hRL2 omega)) P.toMeasure)
    (hGL2 : ∀ omega : ShellSeq d, MemVectorL2 (openCubeSet Q) (gf omega))
    (hGclass : AEMeasurable (fun omega : ShellSeq d =>
      toHilbertVectorL2OfVecField (hGL2 omega)) P.toMeasure)
    (hfinR : (∫⁻ omega : ShellSeq d,
      vecCubeLpENorm Q 2 (Rf omega) ^ (2 : ℕ) ∂P.toMeasure) ≠ ⊤)
    (hfinG : (∫⁻ omega : ShellSeq d,
      vecCubeLpENorm Q 2 (gf omega) ^ (2 : ℕ) ∂P.toMeasure) ≠ ⊤) :
    Integrable (fun omega : ShellSeq d =>
      volumeAverage (openCubeSet Q) (fun y => vecDot (Rf omega y) (gf omega y)))
      P.toMeasure := by
  classical
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  have hRmeas : AEMeasurable (fun omega : ShellSeq d =>
      vecCubeLpENorm Q 2 (Rf omega)) P.toMeasure := by
    have heq : (fun omega : ShellSeq d => vecCubeLpENorm Q 2 (Rf omega)) =
        fun omega : ShellSeq d =>
          ENNReal.ofReal ((cubeVolume Q)⁻¹) ^ ((1 : ENNReal) / 2).toReal *
            ‖toHilbertVectorL2OfVecField (hRL2 omega)‖ₑ := by
      funext omega
      exact vecCubeLpENorm_eq_enorm_toHilbertVectorL2OfVecField (hRL2 omega)
    rw [heq]
    exact (measurable_enorm.comp_aemeasurable hRclass).const_mul _
  have hcs : ∀ omega : ShellSeq d,
      |volumeAverage (openCubeSet Q) (fun y => vecDot (Rf omega y) (gf omega y))| ≤
        (vecCubeLpENorm Q 2 (Rf omega)).toReal *
          (vecCubeLpENorm Q 2 (gf omega)).toReal := by
    intro omega
    rw [← volumeAverage_cubeSet_eq_openCubeSet Q
      (fun x => vecDot (Rf omega x) (gf omega x))]
    exact SuperdiffusionCLT.Section2.Norms.abs_volumeAverage_vecDot_le_mul
      (SuperdiffusionCLT.Section2.Norms.memLp_hilbertifyVecField_of_memVectorL2
        (hRL2 omega))
      (SuperdiffusionCLT.Section2.Norms.memLp_hilbertifyVecField_of_memVectorL2
        (hGL2 omega))
  have hbound : ∀ omega : ShellSeq d,
      ‖volumeAverage (openCubeSet Q) (fun y => vecDot (Rf omega y) (gf omega y))‖ₑ ≤
        vecCubeLpENorm Q 2 (Rf omega) ^ (2 : ℕ) +
          vecCubeLpENorm Q 2 (gf omega) ^ (2 : ℕ) := by
    intro omega
    have h0 : ‖volumeAverage (openCubeSet Q)
        (fun y => vecDot (Rf omega y) (gf omega y))‖ₑ =
        ENNReal.ofReal |volumeAverage (openCubeSet Q)
          (fun y => vecDot (Rf omega y) (gf omega y))| := by
      rw [← ofReal_norm, Real.norm_eq_abs]
    have h1 := hcs omega
    have hxf : vecCubeLpENorm Q 2 (Rf omega) ≠ ⊤ :=
      (SuperdiffusionCLT.Section2.Norms.memLp_hilbertifyVecField_of_memVectorL2
        (hRL2 omega)).eLpNorm_lt_top.ne
    have hyf : vecCubeLpENorm Q 2 (gf omega) ≠ ⊤ :=
      (SuperdiffusionCLT.Section2.Norms.memLp_hilbertifyVecField_of_memVectorL2
        (hGL2 omega)).eLpNorm_lt_top.ne
    have h2 : ENNReal.ofReal ((vecCubeLpENorm Q 2 (Rf omega)).toReal *
        (vecCubeLpENorm Q 2 (gf omega)).toReal) =
        vecCubeLpENorm Q 2 (Rf omega) * vecCubeLpENorm Q 2 (gf omega) := by
      rw [ENNReal.ofReal_mul (vecCubeLpENorm Q 2 (Rf omega)).toReal_nonneg,
        ENNReal.ofReal_toReal hxf, ENNReal.ofReal_toReal hyf]
    refine le_trans (le_trans (le_of_eq h0) ?_) (mul_le_sq_add_sq_final _ _)
    refine le_trans (ENNReal.ofReal_le_ofReal h1) ?_
    rw [h2]
  have hmeas : AEMeasurable (fun omega : ShellSeq d =>
      volumeAverage (openCubeSet Q) (fun y => vecDot (Rf omega y) (gf omega y)))
      P.toMeasure := by
    have hfun : (fun omega : ShellSeq d =>
        volumeAverage (openCubeSet Q) (fun y => vecDot (Rf omega y) (gf omega y))) =
      fun omega : ShellSeq d => (MeasureTheory.volume (openCubeSet Q)).toReal⁻¹ *
        inner ℝ (toHilbertVectorL2OfVecField (hRL2 omega))
          (toHilbertVectorL2OfVecField (hGL2 omega)) := by
      funext omega
      exact volumeAverage_vecDot_eq_inner (hRL2 omega) (hGL2 omega)
    rw [hfun]
    exact (continuous_inner.measurable.comp_aemeasurable
      (hRclass.prodMk hGclass)).const_mul _
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_def]
  refine lt_of_le_of_lt (lintegral_mono hbound) ?_
  have hNR : (∫⁻ omega : ShellSeq d,
      vecCubeLpENorm Q 2 (Rf omega) ^ (2 : ℕ) ∂P.toMeasure) < ⊤ :=
    lt_of_le_of_ne le_top hfinR
  have hNG : (∫⁻ omega : ShellSeq d,
      vecCubeLpENorm Q 2 (gf omega) ^ (2 : ℕ) ∂P.toMeasure) < ⊤ :=
    lt_of_le_of_ne le_top hfinG
  rw [lintegral_add_left' (hRmeas.pow_const 2)]
  exact ENNReal.add_lt_top.2 ⟨hNR, hNG⟩

end

end SuperdiffusionCLT.Section3.Terms
