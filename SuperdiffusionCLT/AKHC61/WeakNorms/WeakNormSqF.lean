/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.WeakNorms.WeakNormSqE
public import SuperdiffusionCLT.AKHC61.Response.JUpperBound

/-!
# Squared weak norms, part F: package B2's `J`-upper bound with every hypothesis discharged

`akhc_jUpperBound_of_cutoffLaw` (`AKHC61/Response/JUpperBound.lean`) carries `hGradSq` and
`hFluxSq`. Parts A–E prove both from the root's binders at every scale `m ≥ max(m₂, 1)`; this
file composes them. The result carries only root binders (`0 < ν`, `ShellLawPrefix`,
`ShellLawJ2`, `ShellLawJ4`, V3's (P2′) clause) and the scale range `m₂ ≤ m`, `0 < m`,
`0 ≤ k ≤ m`.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.WeakNorms

noncomputable section

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed

/-- **Node 43 (`e.divcurl.conclusion.pre`) at the cutoff law, hypothesis-free up to the root's
binders.** CG's normalized-cutoff `J`-upper bound at `s = t = ½`, with `hParent`, `hJ` (package
B2) and `hGradSq`, `hFluxSq` (parts A–E) all discharged. -/
theorem akhcWNSq_jUpperBound_of_cutoffLaw
    (d : ℕ) [NeZero d] {nu : ℝ} (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d)) (L : ℕ)
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ4 : ShellLawJ4 d P)
    (gamma H D : ℝ) (m2 : ℕ) (PsiS : ℝ → ℝ) (KPsiS pPsiS : ℝ)
    (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1) (hH : 1 ≤ H) (hD : 0 ≤ D)
    (hPsiSMono : MonotoneOn PsiS (Set.Ici 0)) (hPsiSOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ PsiS t)
    (hKPsiS : 1 ≤ KPsiS) (hpPsiS : 2 < pPsiS)
    (hGrowth : ∀ p : ℝ, 2 ≤ p → p ≤ pPsiS → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
      s ^ p ≤ KPsiS ^ (3 * ⌈p⌉₊ ^ 2) * (PsiS (t * s) / PsiS t))
    -- (P2') `a.ellipticity.weaker`, copied verbatim from
    -- `SuperdiffusionCLT.Frozen.Section4.akhc_weakerP3`.
    (hP2 : ∀ j : ℕ, m2 ≤ j →
      ∃ X : ShellSeq d → ℝ, Measurable X ∧
        Homogenization.IndependentSums.IsBigO P.toMeasure PsiS X (H * (j : ℝ) ^ D) ∧
        ∀ (omega : ShellSeq d) (Q : Homogenization.TriadicCube d),
          Q.scale ≤ (j : ℤ) →
          Homogenization.cubeCenter Q ∈
              Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)) →
            Homogenization.BlockMatLoewnerLE
              (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q)
                (coefficientCutoff nu omega L).toCoeffField)
              ((1 + (3 : ℝ) ^ (-(gamma * ((Q.scale : ℝ) - (j : ℝ)))) * X omega) •
                annealedBlockMatrix nu L P
                  (Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)))))
    {m : ℕ} (hm2 : m2 ≤ m) (hm : 0 < m) {k : ℤ} (hk_nonneg : 0 ≤ k) (hkm : k ≤ (m : ℤ))
    (p q p0 q0 : Homogenization.Vec d) :
    let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
    let j : ℕ := Int.toNat ((m : ℤ) - k)
    Homogenization.Book.Ch04.expectedResponseJCubeSet (cutoffLaw (d := d) nu L P) Q p q -
        (1 / 2 : ℝ) * Homogenization.vecDot p0 q0 ≤
      Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.jUpperWeakNormManuscriptExpectedRHSAtScale
        (cutoffLaw (d := d) nu L P) (m : ℤ) k (1 / 2 : ℝ) (1 / 2 : ℝ)
        (1 + Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffBound Q)
        (Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffOscillationConstant Q)
        (Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffScaleSep Q j)
        (Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffDualBound Q (1 / 2 : ℝ))
        (Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffDualBound Q (1 / 2 : ℝ))
        (Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffProductCoeff Q
          (1 / 2 : ℝ) (1 / 2 : ℝ))
        p q p0 q0 :=
  SuperdiffusionCLT.AKHC61.Response.akhc_jUpperBound_of_cutoffLaw d hnu P L hPrefix hJ2
    gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth
    hP2 hk_nonneg hkm p q p0 q0
    (akhcWNSq_integrable_gradientWeakNorm_sq hnu hPrefix hJ2 hJ4 gamma H D m2 PsiS KPsiS pPsiS
      hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hm2 hm p q p0)
    (akhcWNSq_integrable_fluxWeakNorm_sq hnu hPrefix hJ2 hJ4 gamma H D m2 PsiS KPsiS pPsiS
      hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hm2 hm p q q0)

end

end SuperdiffusionCLT.AKHC61.WeakNorms
