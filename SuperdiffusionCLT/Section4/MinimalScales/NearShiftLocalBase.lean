/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.NearLocalBridge
public import SuperdiffusionCLT.Section4.NewMixing.ParamStatement
public import SuperdiffusionCLT.Section4.NewMixing.AssemblyScalarMax
public import Homogenization.Book.Ch02.Theorems.DeterministicIdentities

/-!
# `e.new.mixing.attempt.local.base` at the origin cube, uniform in the skew shift

Variant of the near-local base estimate whose `hParam` is the uniform-in-`h0` form of
`l.new.mixing.parameterized`: the witnesses `X1`, `X2` do not depend on `h0`, the
`Γ_{1/3}` amplitude is `C m^{-5000}`, and the factor `1 + σ⁻¹‖h0‖²` multiplies `X2`
pathwise. The conclusion is the same: the witnesses are chosen before `h0`, and the
bound holds for every skew `h0`, at the cutoff field `newMixParam_aLplusH0 … h0 hh0`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

open MeasureTheory
open Homogenization.IndependentSums

noncomputable section

/-- Uniform-in-`h0` origin-cube local base. -/
theorem srootNS_localBase_le (d : ℕ) [NeZero d]
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
                    Homogenization.normalizedBlockResponseMax (Homogenization.originCube d (nn : ℤ))
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
  obtain ⟨C, hC1, hP⟩ := hParam
  refine ⟨C, hC1, ?_⟩
  intro nu cStar nondeg hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 K hK m nn mp hL1 hL2 hL3 hL4
  obtain ⟨X1, X2, hX1m, hX1O, hX2m, hX2O, hbfJ⟩ :=
    hP nu cStar nondeg hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 (1 / 2) K K
      (by norm_num) (by norm_num) hK hK mp nn m hL1 hL2 hL3 hL4
  refine ⟨X1, X2, hX1m, hX1O, hX2m, hX2O, ?_⟩
  intro h0 hh0 omega
  have hEllA :
      Homogenization.IsEllipticFieldOn
        (SuperdiffusionCLT.Section4.NewMixing.newMixParam_aLplusH0
            nu hnu omega mp nn h0 hh0).lam
        (SuperdiffusionCLT.Section4.NewMixing.newMixParam_aLplusH0
            nu hnu omega mp nn h0 hh0).Lam
        (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d (nn : ℤ)) :
          Set (Homogenization.Vec d))
        (SuperdiffusionCLT.Section4.NewMixing.newMixParam_aLplusH0
            nu hnu omega mp nn h0 hh0).toCoeffField :=
    SuperdiffusionCLT.Section4.NewMixing.newMixAsm_isEllipticFieldOn_aLplusH0
      hnu omega mp h0 hh0
      (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d (nn : ℤ)))
  have hbd :
      ∀ eta : Homogenization.BlockVec d,
        SuperdiffusionCLT.Section2.Carriers.blockVecNorm eta = 1 →
          Homogenization.BlockJ (Homogenization.cubeSet (Homogenization.originCube d (nn : ℤ)))
              ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) ^
                  (-(1 : ℝ) / 2) • eta.1,
                (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) ^
                  ((1 : ℝ) / 2) • eta.2)
              ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) ^
                  ((1 : ℝ) / 2) • eta.1,
                (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) ^
                  (-(1 : ℝ) / 2) • eta.2)
              (SuperdiffusionCLT.Section4.NewMixing.newMixParam_aLplusH0
                  nu hnu omega mp nn h0 hh0).toCoeffField ≤
            C * (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) ^
                (-(2 : ℝ)) *
                ((Homogenization.Book.Ch02.matrixOperatorNorm h0) ^ 2 +
                  max 0 ((mp : ℝ) - (nn : ℝ)) + K * Real.log (mp : ℝ) ^ (2 : ℝ)) +
              X1 omega +
              (1 + (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) ^
                    (-(1 : ℝ)) *
                  (Homogenization.Book.Ch02.matrixOperatorNorm h0) ^ 2) * X2 omega := by
    intro eta heta
    have hkey := hbfJ h0 hh0 omega eta heta
    have hbridge :=
      Homogenization.Book.Ch02.doubledResponseJ_eq_BlockJ_of_isEllipticFieldOn
        (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d (nn : ℤ)))
        (SuperdiffusionCLT.Section4.NewMixing.newMixParam_aLplusH0
            nu hnu omega mp nn h0 hh0)
        hEllA
        (SuperdiffusionCLT.Section4.NewMixing.newMixParam_bfAhomPow nu m P (-(1 : ℝ) / 2) eta)
        (SuperdiffusionCLT.Section4.NewMixing.newMixParam_bfAhomPow nu m P ((1 : ℝ) / 2) eta)
    rw [hbridge, Homogenization.Book.Ch02.cubeDomain_coe,
      ← Homogenization.BlockJ_cubeSet_eq_openCubeSet_of_triadicCube] at hkey
    simp only [SuperdiffusionCLT.Section4.NewMixing.newMixParam_bfAhomPow] at hkey
    norm_num at hkey ⊢
    exact hkey
  have hσ : 0 < SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P :=
    SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite_pos hnu m hPrefix hJ2 hJ3 hJ4
  exact SuperdiffusionCLT.Section4.MinimalScales.srootN_normalizedBlockResponseMax_le_of_forall_probe
    (Homogenization.originCube d (nn : ℤ))
    (SuperdiffusionCLT.Section4.NewMixing.newMixParam_aLplusH0
        nu hnu omega mp nn h0 hh0).toCoeffField
    hσ hbd

end

end SuperdiffusionCLT.Section4.MinimalScales
