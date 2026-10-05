/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.Carrier.ScalarBlocks

/-!
Stage 4 (task `sc3`), item (2) of the remaining Step-3 assembly: **`1 ≤ Θ_{L,0}`**,
i.e. `1 ≤ thetaCutoff nu L P 0`. Needed for `M0ThresholdB.lean`'s
`homogBelowM0_monotone_in_Theta0`, which lets a caller replace the *proved
upper bound* on `Θ₀` (`ThetaLmThetaZero.lean`'s `homogBelow_thetaCutoff_zero_le`)
inside `homogBelowM0_threshold_corrected`'s conclusion by the *actual* `Θ₀`,
since the whole left side is monotone increasing in `Θ₀` only once `Θ₀ ≥ 1`
(so both logs' arguments stay `≥ 1`).

Package A2's `akhc_one_le_thetaCutoff_of_P2`
(`AKHC61/Carrier/ScalarBlocks.lean`, node 60) proves exactly `1 ≤ thetaCutoff
nu L P n` for every `n`, from only `0 < nu`, `ShellLawJ4`, and the (P2')
existence clause — no `ShellLawPrefix`/`ShellLawJ2`/`ShellLawJ3` needed. The
(P2') clause it wants is *syntactically* the same `∀ j, m2 ≤ j → ∃ X, ...`
block `homogBelow_P2prime_verified` (`ThetaLmP2Prime.lean`) already produces
(and that `ThetaLmAssemblyAKHCApp.lean`'s `hexistsPsiS` already carries), so
this lemma is a thin wrapper taking that same witness tuple. -/

@[expose] public section

namespace SuperdiffusionCLT.Section4.HomogBelow

open Homogenization MeasureTheory

/-- **`1 ≤ Θ_{L,0}`, from the (P2') witness alone** (no `ShellLawPrefix`,
`ShellLawJ2`, `ShellLawJ3`). -/
theorem homogBelow_one_le_thetaCutoff_zero
    {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)}
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    {L : ℕ}
    {gamma H D : ℝ} {m2 : ℕ} {PsiS : ℝ → ℝ} {KPsiS pPsiS : ℝ}
    (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1) (hH1 : 1 ≤ H) (hD0 : 0 ≤ D)
    (hPsiSMono : MonotoneOn PsiS (Set.Ici 0)) (hPsiSge1 : ∀ t : ℝ, 0 ≤ t → 1 ≤ PsiS t)
    (hKPsiS1 : 1 ≤ KPsiS) (hpPsiS2 : 2 < pPsiS)
    (hgrowthPsiS : ∀ p : ℝ, 2 ≤ p → p ≤ pPsiS → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
      s ^ p ≤ KPsiS ^ (3 * ⌈p⌉₊ ^ 2) * (PsiS (t * s) / PsiS t))
    (hexistsPsiS : ∀ j : ℕ, m2 ≤ j →
      ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
        Measurable X ∧
        Homogenization.IndependentSums.IsBigO P.toMeasure PsiS X (H * (j : ℝ) ^ D) ∧
        ∀ (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
          (Q : Homogenization.TriadicCube d), Q.scale ≤ (j : ℤ) →
          Homogenization.cubeCenter Q ∈
              Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)) →
            Homogenization.BlockMatLoewnerLE
              (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q)
                (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu
                    omega L).toCoeffField)
              ((1 + (3 : ℝ) ^ (-(gamma * ((Q.scale : ℝ) - (j : ℝ)))) * X omega) •
                SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                  (Homogenization.cubeSet (Homogenization.originCube d (j : ℤ))))) :
    1 ≤ SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P 0 :=
  SuperdiffusionCLT.AKHC61.Carrier.akhc_one_le_thetaCutoff_of_P2
    hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH1 hD0 hPsiSMono hPsiSge1
    hKPsiS1 hpPsiS2 hgrowthPsiS hexistsPsiS 0

end SuperdiffusionCLT.Section4.HomogBelow
