/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.NearShiftTrans
public import SuperdiffusionCLT.Section4.MinimalScales.NearShiftField

/-!
# The centered field on descendant cubes

`srootE_field nu ω L m n k` is the translate by `z = 3^{n-3} k` of `a_L + h_0`, with
`h_0 = srootNS_h0 m L ω`. The uniform-in-`h0` local base transfers to this field on every cube
`R` of scale `nn`: the field is `a_L + h_0` for the translated sequence `θ_z ω`, so the base
bound is applied at `θ_z ω`, and the witnesses are precomposed with `θ_z`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

open MeasureTheory
open Homogenization.IndependentSums

noncomputable section

private theorem srootNSG_aLplusH0_toCoeffField {d : ℕ} [NeZero d] (nu : ℝ) (hnu : 0 < nu)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (L m m' : ℕ)
    (h0 : Homogenization.Mat d) (hh0 : Homogenization.matTranspose h0 = -h0) :
    (SuperdiffusionCLT.Section4.NewMixing.newMixParam_aLplusH0 nu hnu omega L m h0 hh0).toCoeffField =
      (SuperdiffusionCLT.Section4.NewMixing.newMixParam_aLplusH0 nu hnu omega L m' h0 hh0).toCoeffField := by
  funext x
  simp [SuperdiffusionCLT.Section4.NewMixing.newMixParam_aLplusH0,
    SuperdiffusionCLT.Section2.CoarseGraining.addConstSkewCoeffOn_toCoeffField,
    SuperdiffusionCLT.Section2.CoarseGraining.coefficientCutoffCoeffOn_toCoeffField]

/-- The uniform-in-`h0` local base for `srootE_field` at every cube `R` of scale `nn`. -/
theorem srootNS_localBase_translateZ_le (d : ℕ) [NeZero d]
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
      ∀ (nu cStar nondeg : ℝ) (_hnu : 0 < nu) (_hnu1 : nu ≤ 1),
        ∀ (P : MeasureTheory.ProbabilityMeasure
              (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
          (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
          (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
          (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar nondeg hPrefix hJ2 hJ3 →
          ∀ K : ℝ, 1 ≤ K →
            ∀ m nn mp n : ℕ, ∀ k : Fin d → ℤ,
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
                  ∀ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
                    Homogenization.normalizedBlockResponseMax R
                        (srootE_field nu omega mp m n k)
                        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P •
                            (1 : Homogenization.Mat d)) ≤
                      C * (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) ^
                          (-(2 : ℝ)) *
                          ((Homogenization.Book.Ch02.matrixOperatorNorm (srootNS_h0 m mp omega)) ^ 2 +
                            max 0 ((mp : ℝ) - (nn : ℝ)) + K * Real.log (mp : ℝ) ^ (2 : ℝ)) +
                        X1 omega +
                        (1 + (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) ^
                              (-(1 : ℝ)) *
                            (Homogenization.Book.Ch02.matrixOperatorNorm (srootNS_h0 m mp omega)) ^ 2) *
                          X2 omega := by
  obtain ⟨C, hC1, hBase⟩ := srootNS_localBase_translateCube_le d hParam
  refine ⟨C, hC1, ?_⟩
  intro nu cStar nondeg hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 K hK m nn mp n k hL1 hL2 hL3 hL4 R hRscale
  obtain ⟨X1, X2, hX1m, hX1O, hX2m, hX2O, hbound⟩ :=
    hBase nu cStar nondeg hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 K hK m nn mp hL1 hL2 hL3 hL4 R hRscale
  set z : Homogenization.Vec d := fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ) with hzdef
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
  intro omega
  have hfield : srootE_field nu omega mp m n k =
      (SuperdiffusionCLT.Section4.NewMixing.newMixParam_aLplusH0 nu hnu
        (SuperdiffusionCLT.Frozen.Assumptions.ShellField.translateSequence z omega) mp nn
        (srootNS_h0 m mp omega) (srootNS_h0_skew m mp omega)).toCoeffField := by
    rw [srootNS_srootE_field_eq_aLplusH0 nu hnu omega mp m n k,
      srootNS_translateCoeffField_aLplusH0 nu hnu z omega mp m _ _,
      srootNSG_aLplusH0_toCoeffField nu hnu _ mp m nn]
  rw [hfield]
  exact hbound (srootNS_h0 m mp omega) (srootNS_h0_skew m mp omega)
    (SuperdiffusionCLT.Frozen.Assumptions.ShellField.translateSequence z omega)

end

end SuperdiffusionCLT.Section4.MinimalScales
