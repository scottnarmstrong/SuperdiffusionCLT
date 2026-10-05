/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.Step2.StepTwo

/-!
# The core theorem of AK.HC Theorem 6.1 in proof-native parameters (package F1)

Theorem `t.weaker.P3` of [AK] and its proof.

`akhcF1_core` takes the root binders for the cutoff law, the Step 3 rate data `σ, U, C_s, κ`,
the `ω`-smallness `ω_m²·Υ₁ ≤ δσ²` (`akhcStep2_Upsilon1`, `akhcStep2_delta`) and the explicit
Step 2 requirement `akhcStep2_m0Req` on `m₀`. It closes Step 2 (`akhcStep2_step_two`) and returns
`Θ_n - 1 ≤ U ω_m² + C_s 3^{-κ(n-m-4m₀)}` for `n ≥ m + 4m₀`. Its hypothesis `hStep3` is
discharged by `akhcStep3_decay`. The statement it
serves is `akhc_weakerP3`, proved by `akhc_weakerP3_port`.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.Core

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.AKHC61.ParamsProofNative

noncomputable section

section CoreTheorem

variable {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ) (P : ProbabilityMeasure (ShellSeq d))
  (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ4 : ShellLawJ4 d P) (hd : 2 ≤ d)
  (gamma H D : ℝ) (m2 : ℕ) (PsiS : ℝ → ℝ) (KPsiS pPsiS : ℝ)
  (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1) (hH : 1 ≤ H) (hDnn : 0 ≤ D)
  (hPsiSMono : MonotoneOn PsiS (Set.Ici 0)) (hPsiSOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ PsiS t)
  (hKPsiS : 1 ≤ KPsiS) (hpPsiS : 2 < pPsiS)
  (hGrowthP2 : ∀ p : ℝ, 2 ≤ p → p ≤ pPsiS → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
    s ^ p ≤ KPsiS ^ (3 * ⌈p⌉₊ ^ 2) * (PsiS (t * s) / PsiS t))
  (hP2 : ∀ j : ℕ, m2 ≤ j → ∃ X : ShellSeq d → ℝ, Measurable X ∧
      Homogenization.IndependentSums.IsBigO P.toMeasure PsiS X (H * (j : ℝ) ^ D) ∧
      ∀ (omega : ShellSeq d) (Q : Homogenization.TriadicCube d),
        Q.scale ≤ (j : ℤ) →
        Homogenization.cubeCenter Q ∈
            Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)) →
          Homogenization.BlockMatLoewnerLE
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q)
              (coefficientCutoff nu omega L).toCoeffField)
            ((1 + (3 : ℝ) ^ (-(gamma * ((Q.scale : ℝ) - (j : ℝ)))) * X omega) •
              SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                (Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)))))
  (beta L1 L2 : ℝ) (m3 : ℕ) (omegaSeq : ℕ → ℝ) (Psi : ℝ → ℝ) (KPsi pPsi : ℝ)
  (hbeta0 : 0 ≤ beta) (hL1 : 1 ≤ L1) (hL2 : 1 ≤ L2) (homega : ∀ k' : ℕ, 0 < omegaSeq k')
  (homegaAnti : Antitone omegaSeq)
  (hPsiOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ Psi t) (hKPsi : 1 ≤ KPsi) (hpPsi : (d : ℝ) < pPsi)
  (hGrowthPsi : ∀ p : ℝ, 1 < p → p ≤ pPsi → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
      s ^ p ≤ KPsi ^ (3 * ⌈p⌉₊ ^ 2) * (Psi (t * s) / Psi t))
  (hP3 : ∀ j n : ℕ, m3 ≤ n → beta * (j : ℝ) < (n : ℝ) →
      (n : ℝ) < (j : ℝ) - L1 * Real.log (L2 * (n : ℝ)) →
      ∃ X : ShellSeq d → ℝ, Measurable X ∧
        Homogenization.IndependentSums.IsBigO P.toMeasure Psi X (omegaSeq n) ∧
        ∀ (omega : ShellSeq d) (p q : Homogenization.BlockVec d),
          2 *
              (((Homogenization.descendantsAtDepth
                      (Homogenization.originCube d (j : ℤ)) (j - n)).card : ℝ)⁻¹ *
                ∑ R ∈ Homogenization.descendantsAtDepth
                    (Homogenization.originCube d (j : ℤ)) (j - n),
                  Homogenization.blockVecDot p
                    (Homogenization.blockMatVecMul
                      (Homogenization.ofFullBlockMat
                        (Homogenization.toFullBlockMat
                            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet R)
                              (coefficientCutoff nu omega L).toCoeffField) -
                          Homogenization.toFullBlockMat
                            (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                              (Homogenization.cubeSet
                                (Homogenization.originCube d (n : ℤ))))))
                      q)) ≤
            X omega *
              (Homogenization.blockVecDot p
                  (Homogenization.blockMatVecMul
                    (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                      (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)))) p) +
                Homogenization.blockVecDot q
                  (Homogenization.blockMatVecMul
                    (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                      (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)))) q)))

include hnu hPrefix hJ2 hJ4 hd hgamma0 hgamma1 hH hDnn hPsiSMono hPsiSOne hKPsiS hpPsiS
  hGrowthP2 hP2 hbeta0 hL1 hL2 homega homegaAnti hPsiOne hKPsi hpPsi hGrowthPsi hP3

/-- **The core theorem (F1)**, in proof-native parameters. For every `m ≥ max{m₂, m₃}` and `m₀`
with `ω_m²·Υ₁ ≤ δσ²` and `akhcStep2_m0Req … m m₀`: Step 2 holds, `Θ_n ≤ 1 + σ` for every
`n ≥ m + 3m₀`, and, given Step 3 (`hStep3`), `Θ_n - 1 ≤ U ω_m² + C_s 3^{-κ(n-m-4m₀)}` for every
`n ≥ m + 4m₀`. -/
theorem akhcF1_core {m m0 : ℕ} (hm : max m2 m3 ≤ m) {sigma : ℝ} (hsigma0 : 0 < sigma)
    (hsigma1 : sigma < 1) (U Cs kappa : ℝ)
    (hOmega : omegaSeq m ^ 2 * akhcStep2_Upsilon1 d gamma pPsi pPsiS KPsi ≤
      akhcStep2_delta d gamma pPsi pPsiS * sigma ^ 2)
    (hm0 : akhcStep2_m0Req d gamma pPsi pPsiS L1 L2 H D KPsiS beta sigma
      (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P 0) m m0)
    (hStep3 : SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P (m + 3 * m0) ≤
        1 + sigma →
      ∀ n : ℕ, m + 4 * m0 ≤ n →
        SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P n - 1 ≤
          U * omegaSeq m ^ 2 + Cs * (3 : ℝ) ^ (-(kappa * ((n : ℝ) - (m : ℝ) - 4 * (m0 : ℝ))))) :
    (∀ n : ℕ, m + 3 * m0 ≤ n →
        SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P n ≤ 1 + sigma) ∧
      ∀ n : ℕ, m + 4 * m0 ≤ n →
        SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P n - 1 ≤
          U * omegaSeq m ^ 2 + Cs * (3 : ℝ) ^ (-(kappa * ((n : ℝ) - (m : ℝ) - 4 * (m0 : ℝ)))) := by
  have h2 := SuperdiffusionCLT.AKHC61.Step2.akhcStep2_step_two hnu L P hPrefix hJ2 hJ4 hd gamma
    H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hDnn hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowthP2 hP2
    beta L1 L2 m3 omegaSeq Psi KPsi pPsi hbeta0 hL1 hL2 homega homegaAnti hPsiOne hKPsi hpPsi
    hGrowthPsi hP3 hm hsigma0 hsigma1 hOmega hm0
  refine ⟨fun n hn => ?_, hStep3 h2⟩
  have hanti := SuperdiffusionCLT.AKHC61.Carrier.akhc_antitone_thetaCutoff_of_P2 hnu hPrefix
    hJ2 hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hDnn hPsiSMono hPsiSOne hKPsiS
    hpPsiS hGrowthP2 hP2 hn
  exact hanti.trans h2

end CoreTheorem

end

end SuperdiffusionCLT.AKHC61.Core
