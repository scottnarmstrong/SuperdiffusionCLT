/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.NearShiftLocalBase
public import SuperdiffusionCLT.Section4.MinimalScales.NearTransCube
public import SuperdiffusionCLT.AKHC61.Tails.CFSTranslate
public import SuperdiffusionCLT.Assumptions.ShellLaw.BlockStationarity

/-!
# Uniform-in-`h0` local base at every descendant cube

(a) `srootNS_translateCoeffField_aLplusH0`: translation covariance of
`newMixParam_aLplusH0 … h0 hh0` for an arbitrary constant skew shift `h0` (the constant
shift commutes with translation).

(b) `srootNS_localBase_translateCube_le`: the conclusion of `srootNS_localBase_le` at every
cube `R` of scale `nn`, with witnesses `X_i ∘ translateSequence z_R`; the statement is still
uniform in `h0` after the witnesses.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

open MeasureTheory
open Homogenization.IndependentSums

noncomputable section

private theorem srootNS_translateCoeffField_toCoeffField {d : ℕ} (z : Homogenization.Vec d)
    (a : Homogenization.RegCoeffField d) :
    Homogenization.translateCoeffField z a.toCoeffField =
      (Homogenization.translateReg z a).toCoeffField := by
  funext x
  show a.toFun (fun i => x i + z i) = a.toFun (x + z)
  rfl

private theorem srootNS_aLplusH0_toCoeffField {d : ℕ} [NeZero d] (nu : ℝ) (hnu : 0 < nu)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (L m : ℕ)
    (h0 : Homogenization.Mat d) (hh0 : Homogenization.matTranspose h0 = -h0) :
    (SuperdiffusionCLT.Section4.NewMixing.newMixParam_aLplusH0 nu hnu omega L m h0 hh0).toCoeffField =
      fun x => (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField x + h0 := by
  funext x
  simp [SuperdiffusionCLT.Section4.NewMixing.newMixParam_aLplusH0,
    SuperdiffusionCLT.Section2.CoarseGraining.addConstSkewCoeffOn_toCoeffField,
    SuperdiffusionCLT.Section2.CoarseGraining.coefficientCutoffCoeffOn_toCoeffField]

/-- Translation covariance of `newMixParam_aLplusH0` for an arbitrary skew shift `h0`. -/
theorem srootNS_translateCoeffField_aLplusH0 {d : ℕ} [NeZero d] (nu : ℝ) (hnu : 0 < nu)
    (z : Homogenization.Vec d) (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
    (L m : ℕ) (h0 : Homogenization.Mat d) (hh0 : Homogenization.matTranspose h0 = -h0) :
    Homogenization.translateCoeffField z
        (SuperdiffusionCLT.Section4.NewMixing.newMixParam_aLplusH0 nu hnu omega L m
            h0 hh0).toCoeffField =
      (SuperdiffusionCLT.Section4.NewMixing.newMixParam_aLplusH0 nu hnu
          (SuperdiffusionCLT.Frozen.Assumptions.ShellField.translateSequence z omega) L m
          h0 hh0).toCoeffField := by
  have hcut :
      Homogenization.translateCoeffField z
          (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField =
        (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu
            (SuperdiffusionCLT.Frozen.Assumptions.ShellField.translateSequence z omega)
            L).toCoeffField := by
    rw [srootNS_translateCoeffField_toCoeffField,
      SuperdiffusionCLT.Section2.Annealed.translateReg_coefficientCutoff]
  rw [srootNS_aLplusH0_toCoeffField, srootNS_aLplusH0_toCoeffField]
  funext x
  have := congrFun hcut x
  simpa only [Homogenization.translateCoeffField, Homogenization.RegCoeffField.toCoeffField_apply, Section2.Cutoff.coefficientCutoff_apply, Section2.Cutoff.streamCutoff_apply, Frozen.Assumptions.ShellField.translateSequence_apply, Frozen.Assumptions.ShellField.translate_apply, add_left_inj, add_right_inj] using
    congrArg (fun M : Homogenization.Mat d => M + h0) this

private theorem srootNS_eq_translateCube_index_originCube {d : ℕ} {R : Homogenization.TriadicCube d}
    {nn : ℕ} (hR : R.scale = (nn : ℤ)) :
    R = Homogenization.translateCube R.index (Homogenization.originCube d (nn : ℤ)) := by
  cases R with
  | mk rs ri =>
      simp only at hR
      subst hR
      simp [Homogenization.translateCube, Homogenization.originCube]

/-- The uniform-in-`h0` local base at every cube `R` of scale `nn`. -/
theorem srootNS_localBase_translateCube_le (d : ℕ) [NeZero d]
    (hParam :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu cStar nondeg : ℝ) (hnu : 0 < nu) (_hnu1 : nu ≤ 1),
        ∀ (P : MeasureTheory.ProbabilityMeasure
              (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
          (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
          (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
          (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar nondeg hPrefix hJ2 hJ3 →
          ∀ alpha M K : ℝ, 0 ≤ alpha → alpha < 1 → 1 ≤ M → 1 ≤ K →
            ∀ L m r : ℕ,
              SuperdiffusionCLT.Frozen.Section4.lNaught C (C * (M + K)) alpha cStar nu nondeg ≤
                (L : ℝ) →
              SuperdiffusionCLT.Frozen.Section4.lNaught C (C * (M + K)) alpha cStar nu nondeg ≤
                (m : ℝ) →
              (L : ℝ) - M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (m : ℝ) →
              |(L : ℝ) - (r : ℝ)| ≤ K * Real.log (L : ℝ) →
              ∃ X1 X2 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                Measurable X1 ∧
                Homogenization.IndependentSums.IsBigO P.toMeasure
                    (Homogenization.IndependentSums.gammaSigma 1) X1
                    (C * (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu r P) ^
                        (-(2 : ℝ)) *
                      (max 0 ((L : ℝ) - (m : ℝ)) + K * Real.log (L : ℝ))) ∧
                Measurable X2 ∧
                Homogenization.IndependentSums.IsBigO P.toMeasure
                    (Homogenization.IndependentSums.gammaSigma ((1 : ℝ) / 3)) X2
                    (C * (m : ℝ) ^ (-(5000 : ℝ))) ∧
                ∀ (h0 : Homogenization.Mat d) (hh0 : Homogenization.matTranspose h0 = -h0),
                  ∀ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
                    ∀ eta : Homogenization.BlockVec d,
                      SuperdiffusionCLT.Section2.Carriers.blockVecNorm eta = 1 →
                        Homogenization.Book.Ch02.doubledResponseJ
                          (Homogenization.Book.Ch02.cubeDomain
                            (Homogenization.originCube d (m : ℤ)))
                          (SuperdiffusionCLT.Section4.NewMixing.newMixParam_aLplusH0 nu hnu omega L m h0 hh0)
                          (SuperdiffusionCLT.Section4.NewMixing.newMixParam_bfAhomPow nu r P (-(1 : ℝ) / 2) eta)
                          (SuperdiffusionCLT.Section4.NewMixing.newMixParam_bfAhomPow nu r P ((1 : ℝ) / 2) eta) ≤
                        C * (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu r P) ^
                            (-(2 : ℝ)) *
                            ((Homogenization.Book.Ch02.matrixOperatorNorm h0) ^ 2 +
                              max 0 ((L : ℝ) - (m : ℝ)) +
                              K * Real.log (L : ℝ) ^ (2 : ℝ)) +
                          X1 omega +
                          (1 + (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu r P) ^
                                (-(1 : ℝ)) *
                              (Homogenization.Book.Ch02.matrixOperatorNorm h0) ^ 2) * X2 omega) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu cStar nondeg : ℝ) (hnu : 0 < nu) (_hnu1 : nu ≤ 1),
        ∀ (P : MeasureTheory.ProbabilityMeasure
              (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
          (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
          (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
          (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar nondeg hPrefix hJ2 hJ3 →
          ∀ K : ℝ, 1 ≤ K →
            ∀ m nn mp : ℕ,
              SuperdiffusionCLT.Frozen.Section4.lNaught C (C * (K + K)) (1 / 2) cStar nu nondeg ≤
                (mp : ℝ) →
              SuperdiffusionCLT.Frozen.Section4.lNaught C (C * (K + K)) (1 / 2) cStar nu nondeg ≤
                (nn : ℝ) →
              (mp : ℝ) - K * (mp : ℝ) ^ ((1 : ℝ) / 2) * Real.log (mp : ℝ) ^ (3 : ℝ) ≤ (nn : ℝ) →
              |(mp : ℝ) - (m : ℝ)| ≤ K * Real.log (mp : ℝ) →
              ∀ R : Homogenization.TriadicCube d, R.scale = (nn : ℤ) →
              ∃ X1 X2 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                Measurable X1 ∧
                Homogenization.IndependentSums.IsBigO P.toMeasure
                    (Homogenization.IndependentSums.gammaSigma 1) X1
                    (C * (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) ^
                        (-(2 : ℝ)) *
                      (max 0 ((mp : ℝ) - (nn : ℝ)) + K * Real.log (mp : ℝ))) ∧
                Measurable X2 ∧
                Homogenization.IndependentSums.IsBigO P.toMeasure
                    (Homogenization.IndependentSums.gammaSigma ((1 : ℝ) / 3)) X2
                    (C * (nn : ℝ) ^ (-(5000 : ℝ))) ∧
                  ∀ (h0 : Homogenization.Mat d) (hh0 : Homogenization.matTranspose h0 = -h0),
                  ∀ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
                    Homogenization.normalizedBlockResponseMax R
                        (SuperdiffusionCLT.Section4.NewMixing.newMixParam_aLplusH0
                            nu hnu omega mp nn h0 hh0).toCoeffField
                        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P •
                            (1 : Homogenization.Mat d)) ≤
                      C * (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) ^
                          (-(2 : ℝ)) *
                          ((Homogenization.Book.Ch02.matrixOperatorNorm h0) ^ 2 +
                            max 0 ((mp : ℝ) - (nn : ℝ)) + K * Real.log (mp : ℝ) ^ (2 : ℝ)) +
                        X1 omega +
                        (1 + (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) ^
                              (-(1 : ℝ)) *
                            (Homogenization.Book.Ch02.matrixOperatorNorm h0) ^ 2) * X2 omega := by
  obtain ⟨C, hC1, hBase⟩ := srootNS_localBase_le d hParam
  refine ⟨C, hC1, ?_⟩
  intro nu cStar nondeg hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 K hK m nn mp hL1 hL2 hL3 hL4 R hRscale
  obtain ⟨X1, X2, hX1m, hX1O, hX2m, hX2O, hbound⟩ :=
    hBase nu cStar nondeg hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 K hK m nn mp hL1 hL2 hL3 hL4
  set z : Homogenization.Vec d :=
    fun i => (R.index i : ℝ) * Homogenization.cubeScaleFactor (Homogenization.originCube d (nn : ℤ))
    with hzdef
  have hzmeas :=
    SuperdiffusionCLT.Frozen.Assumptions.ShellField.measurable_translateSequence (d := d) z
  have hzmap :=
    SuperdiffusionCLT.Frozen.Assumptions.ShellField.map_translateSequence_eq hPrefix hJ2 z
  refine ⟨fun omega => X1 (SuperdiffusionCLT.Frozen.Assumptions.ShellField.translateSequence z omega),
    fun omega => X2 (SuperdiffusionCLT.Frozen.Assumptions.ShellField.translateSequence z omega),
    hX1m.comp hzmeas,
    SuperdiffusionCLT.AKHC61.Tails.akhcCfsT_isBigO_comp_of_measurePreserving hzmeas hzmap hX1m hX1O,
    hX2m.comp hzmeas,
    SuperdiffusionCLT.AKHC61.Tails.akhcCfsT_isBigO_comp_of_measurePreserving hzmeas hzmap hX2m hX2O,
    ?_⟩
  intro h0 hh0 omega
  have hReq : R = Homogenization.translateCube R.index (Homogenization.originCube d (nn : ℤ)) :=
    srootNS_eq_translateCube_index_originCube hRscale
  have hstep1 :
      Homogenization.normalizedBlockResponseMax R
          (SuperdiffusionCLT.Section4.NewMixing.newMixParam_aLplusH0
              nu hnu omega mp nn h0 hh0).toCoeffField
          (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P •
              (1 : Homogenization.Mat d)) =
        Homogenization.normalizedBlockResponseMax (Homogenization.originCube d (nn : ℤ))
          (Homogenization.translateCoeffField z
            (SuperdiffusionCLT.Section4.NewMixing.newMixParam_aLplusH0
                nu hnu omega mp nn h0 hh0).toCoeffField)
          (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P •
              (1 : Homogenization.Mat d)) := by
    conv_lhs => rw [hReq]
    exact srootN3_normalizedBlockResponseMax_translateCube_eq (Homogenization.originCube d (nn : ℤ))
      (SuperdiffusionCLT.Section4.NewMixing.newMixParam_aLplusH0
          nu hnu omega mp nn h0 hh0).toCoeffField
      (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P • (1 : Homogenization.Mat d))
      R.index
  rw [hstep1, srootNS_translateCoeffField_aLplusH0 nu hnu z omega mp nn h0 hh0]
  exact hbound h0 hh0 (SuperdiffusionCLT.Frozen.Assumptions.ShellField.translateSequence z omega)

end

end SuperdiffusionCLT.Section4.MinimalScales
