/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.Step2.OneStepB
public import SuperdiffusionCLT.AKHC61.Step2.LaunchB
public import SuperdiffusionCLT.AKHC61.WeakNorms.PrimeI
public import SuperdiffusionCLT.AKHC61.Tails.CFS
public import SuperdiffusionCLT.AKHC61.Tails.MaximalMomentC
public import Homogenization.Book.Ch02.MultiscaleEllipticity

/-!
# Tools for the hypotheses of the one-step recursion

This file supplies two reusable tools for the analytic hypotheses (`hV`, `hVsmall`, `hMsmall`,
`hT1small`, `hT2small`) of the elaborate route of the one-step bound (node 40):

* `akhcOneC_rpow_neg_le_of_log_le`, a clean, general, fully proved decay tool: `3^{-cL} ≤ ε`
  whenever `c > 0`, `ε > 0` and `log(1/ε) ≤ cL log 3`. It is used to discharge the smallness
  hypotheses `hT1small`, `hT2small` once `L` is large enough.
* `akhcOneC_sigmaBar_sandwich_window` extends node 28's `δ₁`-sandwich from the single pair
  `(k-2L, k)` to every `n ∈ [k-2L, k]` by antitonicity alone (package A2, no new hypothesis).
  Composing that with node 30 (`akhcLaunch_variance_HC_prime`, `Step2/LaunchB.lean`) and the
  operator-norm bridge `akhcPrime_integral_fl_le_relFrob` (`WeakNorms/PrimeI.lean`) proves `hV` at
  any *single* `n` for which the `(P3′)` window is strict at the fixed inner scale `j := k - 2L`.

At the window's own left endpoint `n = k - 2L + 1`, `j := k - 2L` is the *only* legal inner
scale, and the window strictness `j < n - L₁ log(L₂ j)` becomes `L₁ log(L₂(k-2L)) < 1`, which
**fails** for every sufficiently deep iteration, since `k - 2L → ∞` while `L₁, L₂ ≥ 1` are
fixed. So `hV` over the full window `Finset.Icc (k-2L+1) k` cannot be discharged via the
`(P3′)`/C4 route; the window must lose at least its innermost scale, which is why
`Step2/ElaborateLag.lean` applies package C6 at lag `L` instead of `2L`.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.Step2

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.AKHC61.Carrier
open SuperdiffusionCLT.AKHC61.WeakNorms
open SuperdiffusionCLT.AKHC61.Params

noncomputable section

/-! ## A general exponential-smallness tool -/

/-- **The general decay tool.** `3^{-cL} ≤ ε` whenever `c > 0`, `ε > 0`, and `L` is large enough
that `log(1/ε) ≤ cL log 3`. Pure `log`/`rpow` algebra. -/
theorem akhcOneC_rpow_neg_le_of_log_le {c L eps : ℝ} (_hc : 0 < c) (heps : 0 < eps)
    (hbound : Real.log (1 / eps) ≤ c * L * Real.log 3) :
    (3 : ℝ) ^ (-(c * L)) ≤ eps := by
  have h0 : Real.log (1 / eps) = -Real.log eps := by rw [one_div, Real.log_inv]
  have h1 : Real.log eps = -Real.log (1 / eps) := by linarith only [h0]
  have hgoal_log : Real.log ((3 : ℝ) ^ (-(c * L))) ≤ Real.log eps := by
    rw [Real.log_rpow (by norm_num : (0 : ℝ) < 3), h1]
    linarith only [hbound]
  exact (Real.log_le_log_iff (by positivity) heps).mp hgoal_log

/-! ## The `δ₁`-sandwich extends from `(k-2L,k)` to the whole scale window -/

section SandwichWindow

variable {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ) (P : ProbabilityMeasure (ShellSeq d))
  (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ4 : ShellLawJ4 d P)
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

include hnu hPrefix hJ2 hJ4 hgamma0 hgamma1 hH hDnn hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowthP2 hP2

/-- **The `δ₁`-sandwich extends from the dichotomy's own pair `(k-2L,k)` to every scale between
them.** Given `σ̄_{kbase} ≤ (1+δ₁)σ̄_{ktop}` (from unpacking node 28's `hblock` via
`akhc_blockMatLoewnerLE_annealedBlockMatrix_smul_iff`, `Carrier/ScalarBlocksB.lean`),
antitonicity of `n ↦ σ̄_n` and `n ↦ σ̄*⁻¹_n` (package A2, `akhc_antitone_sigmaBarSeq_of_P2` /
`akhc_antitone_sigmaBarStarInvSeq_of_P2`, `Carrier/ScalarBlocks.lean`) gives the *same* sandwich at
every `n ∈ [kbase,ktop]`, since `σ̄_n` (resp. `σ̄*⁻¹_n`) lies between `σ̄_{ktop}` and `σ̄_{kbase}`. No
new hypothesis beyond `hnu`, `Prefix`, `J2`, `J4` and `(P2′)`. Composed with node 30
(`akhcLaunch_variance_HC_prime`, `Step2/LaunchB.lean`, which takes exactly these sandwich bounds
as its `hAleJ`/`hBleJ`/`hAleN`/`hBleN`) and the operator-norm bridge
`akhcPrime_integral_fl_le_relFrob` (`WeakNorms/PrimeI.lean`), this is what discharges `hV` at any
single window point `n` for which the `(P3′)` window is strict at the fixed inner scale
`kbase = k - 2L` (the strictness itself fails at the window's left endpoint, see above). -/
theorem akhcOneC_sigmaBar_sandwich_window
    {kbase ktop n : ℕ} (hbn : kbase ≤ n) (_hnk : n ≤ ktop) {delta1 : ℝ}
    (hAle : sigmaBarSeq nu L P kbase ≤ (1 + delta1) * sigmaBarSeq nu L P ktop)
    (hBle : sigmaBarStarInvSeq nu L P kbase ≤ (1 + delta1) * sigmaBarStarInvSeq nu L P ktop) :
    sigmaBarSeq nu L P n ≤ (1 + delta1) * sigmaBarSeq nu L P ktop ∧
      sigmaBarStarInvSeq nu L P n ≤ (1 + delta1) * sigmaBarStarInvSeq nu L P ktop := by
  have hanti_a := akhc_antitone_sigmaBarSeq_of_P2 hnu hPrefix hJ2 hJ4 gamma H D m2 PsiS KPsiS
    pPsiS hgamma0 hgamma1 hH hDnn hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowthP2 hP2
  have hanti_b := akhc_antitone_sigmaBarStarInvSeq_of_P2 hnu hPrefix hJ2 gamma H D m2 PsiS KPsiS
    pPsiS hgamma0 hgamma1 hH hDnn hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowthP2 hP2
  exact ⟨le_trans (hanti_a hbn) hAle, le_trans (hanti_b hbn) hBle⟩

end SandwichWindow

section ClosedAssembly

variable {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ) (P : ProbabilityMeasure (ShellSeq d))
  (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ4 : ShellLawJ4 d P)
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

include hnu hPrefix hJ2 hJ4 hgamma0 hgamma1 hH hDnn hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowthP2 hP2

end ClosedAssembly

end

end SuperdiffusionCLT.AKHC61.Step2
