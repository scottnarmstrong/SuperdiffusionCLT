/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.Step3.Recursion

/-!
# Package E3, continued: the Step 3 recursion closes (nodes 51, 52, 58)

Continues `Step3/Recursion.lean` (read its docstring first). This file carries the final
assembly, which instantiates B2 (`akhcWNSq_jUpperBound_of_cutoffLaw`) directly.

## Main results

* `akhcRec_dropBound_of_P2`: the Step 3 drop-bound premise
  `(1/4)·F m ≤ (4·C'²+1/4)·(F(m-Lstep) − F m) + source`, closed from `B1`, `B2`, the
  `Recursion.lean` `EJ`/`τ` bounds, and weighted AM-GM (`δ := 1/(4·C')`), given the numeric
  window `Cosc·scaleSep ≤ 1/4` and `hWeakPrime` carrying **only** the two weak-norm summands of
  `B2`'s route-W bound (not the additivity-defect or oscillation terms, which are discharged
  here from `Recursion.lean`'s own lemmas).

## What is *not* needed by this route

E2 (`Step3/VarianceAgain.lean`, `akhcVA_variance_again_prime`) is **not** called
by this assembly: the quadratic-looking `(Θ̂_k−1)²` term in E2's own bound is consumed inside
`l.weaknorms.prime` (C6)'s own (not-yet-built) construction, not by this top-level recursion,
which turns out to be purely linear in `F(m-Lstep) − F m` once `EJ_k`/`EJ_m` are bounded sharply.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.Step3

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.AKHC61.Carrier
open SuperdiffusionCLT.AKHC61.Response

noncomputable section

/-! ## Part 6: the assembly — the drop-bound premise closes

Bounding `EJ_k` by a *fixed* constant (from `Θ ≤ 2`) would make the crude (`δ = 1`) AM-GM bound
on the additivity term reintroduce a self-referential coefficient `≥ 1/2` on `F m`, exceeding
the `1/4` budget `B1`'s identity supplies. This is avoided in two ways: (1) `EJ_k` is bounded by
`akhcRec_expectedJ_atK_le_of_P2`, which is proportional to `F(k), F(m)` (genuinely small), not
`O(1)`; (2) the AM-GM weight `δ` is chosen as `1/(4·C')` rather than `1`, which is what actually
drives the self-reference coefficient down to exactly `1/4` — matching the budget precisely, no
window slack needed beyond `Cosc·scaleSep ≤ 1/4`. -/

section Assembly

variable {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
  (P : ProbabilityMeasure (ShellSeq d)) (L : ℕ)
  (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ4 : ShellLawJ4 d P)
  (gamma H D : ℝ) (m2 : ℕ) (PsiS : ℝ → ℝ) (KPsiS pPsiS : ℝ)
  (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1) (hH : 1 ≤ H) (hD : 0 ≤ D)
  (hPsiSMono : MonotoneOn PsiS (Set.Ici 0)) (hPsiSOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ PsiS t)
  (hKPsiS : 1 ≤ KPsiS) (hpPsiS : 2 < pPsiS)
  (hGrowth : ∀ p : ℝ, 2 ≤ p → p ≤ pPsiS → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
    s ^ p ≤ KPsiS ^ (3 * ⌈p⌉₊ ^ 2) * (PsiS (t * s) / PsiS t))
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
              SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                (Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)))))

include hnu hPrefix hJ2 hJ4 hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2

/-- **The Step 3 drop-bound premise, closed.** For `m2 ≤ m`, `0 < m`, `Lstep ≤ m`, and the
numeric window `Cosc(cu_m)·scaleSep(cu_m, Lstep) ≤ 1/4` (a parameter constraint on the fixed
shift `Lstep`, exactly analogous to CoarseGraining's own `C ≤ (m-k : ℝ)` gap hypothesis in
`scalar_contraction_recursion_from_assembly` — not a proof-step hypothesis), together with
`hWeakPrime` carrying **only** the two weak-norm summands of B2's route-W bound (the linear
`E[gradWeak]`/`E[fluxWeak]` terms and the product `√E[gradWeak²]·√E[fluxWeak²]` term — *not* the
additivity-defect or oscillation terms, which this theorem discharges itself from `B1`, the
antitonicity of `sigmaBarSeq`/`sigmaBarStarInvSeq`, and weighted AM-GM), the drop-bound premise
`(1/4)·F m ≤ (4·C'²+1/4)·(F(m-Lstep) - F m) + source` holds, `C' := 1 + section53CutoffBound
(cu_m)`, `F n := Θ_n - 1`. -/
theorem akhcRec_dropBound_of_P2 {m Lstep : ℕ} (hm2 : m2 ≤ m) (hm0 : 0 < m) (hLstep : Lstep ≤ m)
    (e : Vec d) (he : vecNormSq e = 1)
    (hScaleSep :
      Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffOscillationConstant
          (Homogenization.originCube d (m : ℤ)) *
        Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffScaleSep
          (Homogenization.originCube d (m : ℤ)) Lstep ≤ (1 / 4 : ℝ))
    {source : ℝ} (hsource0 : 0 ≤ source)
    (hWeakPrime :
      let Q := Homogenization.originCube d (m : ℤ)
      let p := akhc_specialP nu L P m e
      let q := akhc_specialQ nu L P m e
      let p0 := (sigmaBarStarInvSeq nu L P m) • q - p
      let q0 := q - (sigmaBarSeq nu L P m) • p
      let Cprime := 1 + Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffBound Q
      let Cosc := Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffOscillationConstant Q
      let scaleSep := Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffScaleSep Q Lstep
      let BφS := Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffDualBound Q (1 / 2 : ℝ)
      let BφT := Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffDualBound Q (1 / 2 : ℝ)
      let Cprod := Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffProductCoeff Q
        (1 / 2 : ℝ) (1 / 2 : ℝ)
      let τ := Homogenization.Book.Ch05.tauAtScale (cutoffLaw (d := d) nu L P) (m : ℤ)
        ((m - Lstep : ℕ) : ℤ) p q
      let EJk := Homogenization.Book.Ch04.expectedResponseJCubeSet (cutoffLaw (d := d) nu L P)
        (Homogenization.originCube d ((m - Lstep : ℕ) : ℤ)) p q
      let EJm := Homogenization.Book.Ch04.expectedResponseJCubeSet (cutoffLaw (d := d) nu L P) Q p q
      Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.jUpperWeakNormManuscriptExpectedRHSAtScale
          (cutoffLaw (d := d) nu L P) (m : ℤ) ((m - Lstep : ℕ) : ℤ) (1 / 2 : ℝ) (1 / 2 : ℝ)
          Cprime Cosc scaleSep BφS BφT Cprod p q p0 q0 -
        (2 * Cprime * (Real.sqrt τ * Real.sqrt EJk) + Cosc * scaleSep * EJm) ≤ source) :
    (1 / 4 : ℝ) * (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1) ≤
      (4 * (1 + Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffBound
            (Homogenization.originCube d (m : ℤ))) ^ 2 + 1 / 4) *
        ((SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P (m - Lstep) - 1) -
          (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1)) + source := by
  set Q := Homogenization.originCube d (m : ℤ) with hQ_def
  set p := akhc_specialP nu L P m e with hp_def
  set q := akhc_specialQ nu L P m e with hq_def
  set p0 := (sigmaBarStarInvSeq nu L P m) • q - p with hp0_def
  set q0 := q - (sigmaBarSeq nu L P m) • p with hq0_def
  set Cprime := 1 + Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffBound Q
    with hCprime_def
  set Cosc := Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffOscillationConstant Q
    with hCosc_def
  set scaleSep := Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffScaleSep Q Lstep
    with hscaleSep_def
  set BφS := Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffDualBound Q (1 / 2 : ℝ)
    with hBφS_def
  set BφT := Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffDualBound Q (1 / 2 : ℝ)
    with hBφT_def
  set Cprod := Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffProductCoeff Q
    (1 / 2 : ℝ) (1 / 2 : ℝ) with hCprod_def
  -- Step 1: `j = Lstep` after the natural/integer cast.
  have hjcast : ((m : ℤ) - ((m - Lstep : ℕ) : ℤ)) = (Lstep : ℤ) := by
    have := Nat.cast_sub hLstep (R := ℤ)
    omega
  have hjnat : Int.toNat ((m : ℤ) - ((m - Lstep : ℕ) : ℤ)) = Lstep := by
    rw [hjcast]; simp
  -- Step 2: `Cprime > 0`.
  have hCbound_nonneg :
      0 ≤ Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffBound Q :=
    Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffBound_nonneg Q
  have hCprime_pos : 0 < Cprime := by rw [hCprime_def]; linarith only [hCbound_nonneg]
  -- Step 3: B1's identity and B2's div-curl bound, combined via the centering-term match.
  have hB1 := SuperdiffusionCLT.AKHC61.Response.akhc_thetaCutoff_sub_one_eq_two_centeredResponse_special
    hnu P L gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS
    hGrowth hP2 hJ4 m e he
  have hB2 := SuperdiffusionCLT.AKHC61.WeakNorms.akhcWNSq_jUpperBound_of_cutoffLaw d hnu P L
    hPrefix hJ2 hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS
    hpPsiS hGrowth hP2 (m := m) hm2 hm0 (k := ((m - Lstep : ℕ) : ℤ))
    (by positivity) (by omega) p q p0 q0
  rw [hjnat] at hB2
  have hcentering :
      (1 / 2 : ℝ) * vecDot p0 q0 =
        akhc_centeringTerm (sigmaBarStarInvSeq nu L P m) (sigmaBarSeq nu L P m) p q := by
    rw [hp0_def, hq0_def, akhc_centeringTerm]
  have hFm_le_RHS :
      (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1) / 2 ≤
        Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.jUpperWeakNormManuscriptExpectedRHSAtScale
          (cutoffLaw (d := d) nu L P) (m : ℤ) ((m - Lstep : ℕ) : ℤ) (1 / 2 : ℝ) (1 / 2 : ℝ)
          Cprime Cosc scaleSep BφS BφT Cprod p q p0 q0 := by
    have hEq : Homogenization.Book.Ch04.expectedResponseJCubeSet (cutoffLaw (d := d) nu L P) Q p q -
        akhc_centeringTerm (sigmaBarStarInvSeq nu L P m) (sigmaBarSeq nu L P m) p q =
        (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1) / 2 := by linarith only [hB1]
    rw [← hEq, ← hcentering]
    exact hB2
  clear hB1 hB2 hcentering
  -- Step 4: the two controlled terms (additivity defect and oscillation).
  have htau : Homogenization.Book.Ch05.tauAtScale (cutoffLaw (d := d) nu L P) (m : ℤ)
      ((m - Lstep : ℕ) : ℤ) p q ≤
      SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P (m - Lstep) -
        SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m := by
    have hτeq : Homogenization.Book.Ch05.tauAtScale (cutoffLaw (d := d) nu L P) (m : ℤ)
        ((m - Lstep : ℕ) : ℤ) p q =
        Homogenization.Book.Ch04.expectedResponseJCubeSet (cutoffLaw (d := d) nu L P)
            (Homogenization.originCube d ((m - Lstep : ℕ) : ℤ)) p q -
          Homogenization.Book.Ch04.expectedResponseJCubeSet (cutoffLaw (d := d) nu L P) Q p q := rfl
    rw [hτeq, hp_def, hq_def]
    exact akhcRec_tau_le_of_P2 hnu P L hPrefix hJ2 hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0
      hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 (Nat.sub_le m Lstep) e he
  have hEJk : Homogenization.Book.Ch04.expectedResponseJCubeSet (cutoffLaw (d := d) nu L P)
      (Homogenization.originCube d ((m - Lstep : ℕ) : ℤ)) p q ≤
      (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P (m - Lstep) -
          SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m) +
        (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1) / 2 := by
    rw [hp_def, hq_def]
    exact akhcRec_expectedJ_atK_le_of_P2 hnu P L hPrefix hJ2 hJ4 gamma H D m2 PsiS KPsiS pPsiS
      hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 (Nat.sub_le m Lstep) e he
  have hEJm : Homogenization.Book.Ch04.expectedResponseJCubeSet (cutoffLaw (d := d) nu L P) Q p q ≤
      (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1) / 2 := by
    rw [hQ_def, hp_def, hq_def]
    exact akhcRec_expectedJ_atM_le_half_of_P2 hnu P L gamma H D m2 PsiS KPsiS pPsiS hgamma0
      hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hJ4 m e he
  -- Step 5: `F(m-Lstep) - F m ≥ 0` from antitonicity (`F n := Θ_n - 1`).
  have hFkFm_nonneg :
      (0 : ℝ) ≤
        (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P (m - Lstep) - 1) -
          (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1) := by
    have hanti := akhc_antitone_thetaCutoff_of_P2 hnu hPrefix hJ2 hJ4 gamma H D m2 PsiS KPsiS pPsiS
      hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 (Nat.sub_le m Lstep)
    linarith only [hanti]
  have hFm_nonneg' : (0 : ℝ) ≤ SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1 := by
    have h1le := akhc_one_le_thetaCutoff_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0
      hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 m
    linarith only [h1le]
  -- Step 6: the additivity-defect term via `akhcRec_sqrt_mul_sqrt_le_of_le` + weighted AM-GM.
  have htau' :
      Homogenization.Book.Ch05.tauAtScale (cutoffLaw (d := d) nu L P) (m : ℤ)
          ((m - Lstep : ℕ) : ℤ) p q ≤
        (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P (m - Lstep) - 1) -
          (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1) := by
    linarith only [htau]
  have hEJk' : Homogenization.Book.Ch04.expectedResponseJCubeSet (cutoffLaw (d := d) nu L P)
      (Homogenization.originCube d ((m - Lstep : ℕ) : ℤ)) p q ≤
      ((SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P (m - Lstep) - 1) -
          (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1)) +
        (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1) / 2 := by
    linarith only [hEJk]
  have hsqrt_mono :
      2 * Real.sqrt (Homogenization.Book.Ch05.tauAtScale (cutoffLaw (d := d) nu L P) (m : ℤ)
            ((m - Lstep : ℕ) : ℤ) p q) *
          Real.sqrt (Homogenization.Book.Ch04.expectedResponseJCubeSet
              (cutoffLaw (d := d) nu L P) (Homogenization.originCube d ((m - Lstep : ℕ) : ℤ)) p q) ≤
      2 * Real.sqrt ((SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P (m - Lstep) - 1) -
            (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1)) *
        Real.sqrt (((SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P (m - Lstep) - 1) -
              (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1)) +
            (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1) / 2) :=
    akhcRec_sqrt_mul_sqrt_le_of_le htau' hEJk'
  have hamgm := akhcRec_weighted_amgm hFkFm_nonneg
    (by linarith only [hFkFm_nonneg, hFm_nonneg'] :
      (0:ℝ) ≤
        ((SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P (m - Lstep) - 1) -
            (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1)) +
          (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1) / 2)
    (show (0:ℝ) < 1 / (4 * Cprime) by positivity)
  -- `hamgm : 2 * √(Fk-Fm) * √((Fk-Fm)+Fm/2) ≤ (Fk-Fm)/(1/(4Cprime)) + (1/(4Cprime))*((Fk-Fm)+Fm/2)`
  have htauTerm_le :
      2 * Cprime * (Real.sqrt (Homogenization.Book.Ch05.tauAtScale (cutoffLaw (d := d) nu L P)
              (m : ℤ) ((m - Lstep : ℕ) : ℤ) p q) *
          Real.sqrt (Homogenization.Book.Ch04.expectedResponseJCubeSet
              (cutoffLaw (d := d) nu L P) (Homogenization.originCube d ((m - Lstep : ℕ) : ℤ)) p q)) ≤
      4 * Cprime ^ 2 *
          ((SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P (m - Lstep) - 1) -
            (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1)) +
        (1 / 4 : ℝ) *
          (((SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P (m - Lstep) - 1) -
                (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1)) +
              (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1) / 2) := by
    have hstep :
        2 * Cprime * (Real.sqrt (Homogenization.Book.Ch05.tauAtScale
                (cutoffLaw (d := d) nu L P) (m : ℤ) ((m - Lstep : ℕ) : ℤ) p q) *
            Real.sqrt (Homogenization.Book.Ch04.expectedResponseJCubeSet
                (cutoffLaw (d := d) nu L P) (Homogenization.originCube d ((m - Lstep : ℕ) : ℤ)) p q))
        ≤ Cprime *
          (2 * Real.sqrt ((SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P (m - Lstep) - 1) -
                (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1)) *
            Real.sqrt (((SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P (m - Lstep) - 1) -
                  (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1)) +
                (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1) / 2)) := by
      have hmul := mul_le_mul_of_nonneg_left hsqrt_mono hCprime_pos.le
      linarith only [hmul]
    have hδeq : Cprime * (1 / (4 * Cprime)) = (1 / 4 : ℝ) := by field_simp
    have hCdiv : Cprime *
        (((SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P (m - Lstep) - 1) -
            (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1)) /
          (1 / (4 * Cprime))) =
        4 * Cprime ^ 2 *
          ((SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P (m - Lstep) - 1) -
            (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1)) := by
      rw [div_eq_mul_inv, one_div, inv_inv]
      ring
    have hCscaled := mul_le_mul_of_nonneg_left hamgm hCprime_pos.le
    rw [mul_add, hCdiv] at hCscaled
    have hCscaled2 :
        Cprime * ((1 / (4 * Cprime)) *
            (((SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P (m - Lstep) - 1) -
                  (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1)) +
                (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1) / 2)) =
          (1 / 4 : ℝ) *
            (((SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P (m - Lstep) - 1) -
                  (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1)) +
                (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1) / 2) := by
      rw [← mul_assoc, hδeq]
    rw [hCscaled2] at hCscaled
    linarith only [hstep, hCscaled]
  -- Step 7: the oscillation term.
  have hCosc_nonneg : 0 ≤ Cosc := by
    rw [hCosc_def]
    exact Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffOscillationConstant_nonneg Q
  have hscaleSep_nonneg : 0 ≤ scaleSep := by
    rw [hscaleSep_def]
    unfold Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffScaleSep
    exact div_nonneg (Homogenization.cubeScaleFactor_nonneg Q) (by positivity)
  have hOscScaleSep_nonneg : 0 ≤ Cosc * scaleSep := mul_nonneg hCosc_nonneg hscaleSep_nonneg
  have hoscTerm_le :
      Cosc * scaleSep *
          Homogenization.Book.Ch04.expectedResponseJCubeSet (cutoffLaw (d := d) nu L P) Q p q ≤
        (1 / 4 : ℝ) * ((SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1) / 2) := by
    have h1 : Cosc * scaleSep *
        Homogenization.Book.Ch04.expectedResponseJCubeSet (cutoffLaw (d := d) nu L P) Q p q ≤
        Cosc * scaleSep * ((SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1) / 2) :=
      mul_le_mul_of_nonneg_left hEJm hOscScaleSep_nonneg
    have h2 : Cosc * scaleSep *
        ((SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1) / 2) ≤
        (1 / 4 : ℝ) * ((SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1) / 2) := by
      have hFm_nonneg : (0:ℝ) ≤ (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1) / 2 := by
        have h1le := akhc_one_le_thetaCutoff_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0
          hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 m
        linarith only [h1le]
      exact mul_le_mul_of_nonneg_right hScaleSep hFm_nonneg
    linarith only [h1, h2]
  -- Step 8: assemble.
  have hWeakPrime' := hWeakPrime
  dsimp only at hWeakPrime'
  have hsource0' : (0 : ℝ) ≤ source := hsource0
  linarith only [hFm_le_RHS, hWeakPrime', htauTerm_le, hoscTerm_le, hsource0']

end Assembly

end

end SuperdiffusionCLT.AKHC61.Step3
