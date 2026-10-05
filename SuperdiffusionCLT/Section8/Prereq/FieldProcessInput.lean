/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.FieldRegularityC
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.LocalizedTailData
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementMoreoverBlockB

/-!
# The marginal field as the coefficient of the whole-space process

The model-specific input of the whole-space construction is read off the recentred stream
`k - k(0) = fullStreamRecentered omega`.  Almost surely it is continuous, skew, `C¹`, and its
gradient grows at most logarithmically (`FieldRegularityC`).  This file packages exactly those
properties as `FieldInputData`, produces the analytic coefficient datum of the whole-space
exhaustion for the coefficient `nu Id + k`, and splits it as `a = nu Id + ks + kl` with the rough
part `ks = 0` and the smooth part `kl = k`.  The local constants of the split are the
logarithmic bounds on the divergence of `k` and the explicit freezing radius coming from the
Lipschitz modulus of `k` on unit balls.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization Homogenization.Book.Ch02 MeasureTheory Filter Topology
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Carriers
open SuperdiffusionCLT.Section6
open scoped Matrix.Norms.Elementwise

noncomputable section

/-- The properties of a skew field `k` that the whole-space process construction for the
coefficient `nu Id + k` consumes: skewness, `C¹` regularity and logarithmic growth of the
gradient. -/
structure FieldInputData (d : ℕ) (nu : ℝ) (k : Vec d → Mat d) where
  two_le : 2 ≤ d
  nu_pos : 0 < nu
  skew : ∀ y, matTranspose (k y) = -k y
  contDiff : ContDiff ℝ 1 k
  gradConst : ℝ
  gradConst_nonneg : 0 ≤ gradConst
  grad_le : ∀ y, ‖fderiv ℝ k y‖ ≤ gradConst * (1 + Real.log (2 + ‖y‖))

variable {d : ℕ}

theorem fieldInput_matTranspose_recentered (omega : ShellSeq d) (y : Vec d) :
    matTranspose (fullStreamRecentered omega y) = -fullStreamRecentered omega y := by
  ext i j
  simp only [matTranspose, Matrix.transpose_apply, Matrix.neg_apply]
  exact fullStreamRecentered_skew_entry omega y j i

/-- **Almost surely the recentred stream carries the process input.** -/
theorem fieldInput_ae_data {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) {nu : ℝ} (hnu : 0 < nu) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure,
      Nonempty (FieldInputData d nu (fullStreamRecentered omega)) := by
  filter_upwards [ae_contDiff_fullStreamRecentered hJ3, ae_fderiv_fullStreamRecentered hJ3,
    fieldReg_ae_log_growth_fullStreamDeriv hPrefix hJ3] with omega h1 h2 h3
  obtain ⟨C, hC0, hC⟩ := h3
  refine ⟨⟨hPrefix.dimension, hnu, fieldInput_matTranspose_recentered omega, h1, C, hC0,
    fun y => ?_⟩⟩
  rw [h2]
  exact hC y

namespace FieldInputData

variable {nu : ℝ} {k : Vec d → Mat d}

theorem continuous (D : FieldInputData d nu k) : Continuous k :=
  D.contDiff.continuous

theorem contDiff_entry (D : FieldInputData d nu k) (p q : Fin d) :
    ContDiff ℝ 1 fun y => k y p q :=
  contDiff_pi.mp (contDiff_pi.mp D.contDiff p) q

end FieldInputData

/-! ## The analytic datum of the whole-space exhaustion -/

variable [NeZero d]

/-- The whole-space analytic coefficient `nu Id + k` of the marginal field. -/
def FieldInputData.analyticData {nu : ℝ} {k : Vec d → Mat d} (D : FieldInputData d nu k) :
    DivergenceForm.WholeSpaceAnalyticData d where
  a := fun y => nu • (1 : Mat d) + k y
  nu := nu
  hnu := D.nu_pos
  hsymm := fun y =>
    DivergenceForm.Decay.symmPart_scalar_add_skew rfl (D.skew y)
  hskewContinuous := by
    have h : (fun y => nu • (1 : Mat d) + k y - nu • (1 : Mat d)) = k := by
      funext y
      abel
    rw [h]
    exact D.continuous.continuousOn
  hd := D.two_le
  hameas := (continuous_const.add D.continuous).measurable

/-- **Almost-sure ellipticity and boundedness of the coefficient on every exhaustion cube.**
Almost surely `fullCoefficientRecentered nu omega` is measurable, and on the cube
`(-3^m, 3^m)^d` it is elliptic with lower constant `nu` and a finite upper constant. -/
theorem fieldInput_ae_cube_elliptic {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) {nu : ℝ} (hnu : 0 < nu) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure,
      Measurable (fullCoefficientRecentered nu omega) ∧
        ∀ m : ℕ, ∃ Lam : ℝ, IsEllipticFieldOn nu Lam (DivergenceForm.wholeSpaceCube d m)
          (fullCoefficientRecentered nu omega) := by
  filter_upwards [fieldInput_ae_data hPrefix hJ3 hnu] with omega hD
  obtain ⟨D⟩ := hD
  exact ⟨D.analyticData.hameas, fun m => ⟨_, D.analyticData.cubeEllipticity m⟩⟩

/-! ## Satisfiability witnesses -/

/-- The zero skew field carries the input data. -/
example (hd : 2 ≤ d) : Nonempty (FieldInputData d 1 (fun _ : Vec d => (0 : Mat d))) :=
  ⟨{ two_le := hd
     nu_pos := one_pos
     skew := fun _ => by simp [matTranspose]
     contDiff := contDiff_const
     gradConst := 0
     gradConst_nonneg := le_rfl
     grad_le := fun y => by simp }⟩

/-- The almost-sure statements hold for the law concentrated on the zero shell sequence. -/
example (hd : 2 ≤ d) {nu : ℝ} (hnu : 0 < nu) :
    ∀ᵐ omega : ShellSeq d ∂(SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw d).toMeasure,
      Nonempty (FieldInputData d nu (fullStreamRecentered omega)) :=
  fieldInput_ae_data (SuperdiffusionCLT.Assumptions.ShellLaw.shellLawPrefix_diracZeroLaw hd)
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ3_diracZeroLaw hnu

example (hd : 2 ≤ d) {nu : ℝ} (hnu : 0 < nu) :
    ∀ᵐ omega : ShellSeq d ∂(SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw d).toMeasure,
      Measurable (fullCoefficientRecentered nu omega) ∧
        ∀ m : ℕ, ∃ Lam : ℝ, IsEllipticFieldOn nu Lam (DivergenceForm.wholeSpaceCube d m)
          (fullCoefficientRecentered nu omega) :=
  fieldInput_ae_cube_elliptic
    (SuperdiffusionCLT.Assumptions.ShellLaw.shellLawPrefix_diracZeroLaw hd)
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ3_diracZeroLaw hnu

end

end SuperdiffusionCLT.Section8
