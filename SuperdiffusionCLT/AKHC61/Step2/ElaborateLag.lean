/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.Params.ConstantsProofNative

/-!
# Node 40 at lag `L`: the elaborate route with every analytic input discharged (package F1)

Proof of `t.weaker.P3` of [AK], Step 2.

Applying package C6 at lag `ell := 2L` would make its variance hypothesis `hV` range over
`[k-2L+1, k]`, where the innermost `L₁ log(L₂ k)` scales are unreachable by `(P3′)` from the
pigeon scale `k - 2L`. The source itself uses only `j ≥ k-2L`, `j + L/4 ≤ n ≤ k`. This file
applies C6 at `ell := L` instead: the pigeon sandwich at `L` follows from the one at `2L` by
antitonicity, and
every `n ∈ [k-L+1, k]` is reached from `j := k-2L`.

Throughout, the pigeonhole lag is a separate natural number `Lp`, not the cutoff index `L` of
the law (package D1's dichotomy conflates the two; see `Step2/StepTwo.lean`). The prose above
writes `L` for `Lp`.

`akhcStep2_routeElaborate` then discharges all of C6's analytic inputs:

* `hV`, `hVsmall`: node 30 (`akhcLaunch_variance_HC_prime`, at `p_Ψ := η`) through the bridge
  `akhcPrime_integral_fl_le_relFrob`, with `c_V := akhcStep2_cV d`;
* `hwin`: `k0 := k - L + ⌈L₁ log(L₂ k)⌉ + 1`;
* `hMsmall`, `hT1small`, `hT2small`: from four scalar smallness facts about `L` and `ω`
  (`hLwin`, `hT1`, `hMt`, `hOm`), which `Params/ConstantsProofNative.lean` derives from `L ≥ L_req`.
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
open SuperdiffusionCLT.AKHC61.ParamsProofNative

noncomputable section

/-- `log(L₂ j) ≤ log(L₂ k)` for `j ≤ k`, `1 ≤ L₂`, `1 ≤ k` (also at `j = 0`, where `log 0 = 0`). -/
theorem akhcStep2_log_mono {L2 : ℝ} (hL2 : 1 ≤ L2) {j k : ℕ} (hjk : j ≤ k) (hk : 1 ≤ k) :
    Real.log (L2 * (j : ℝ)) ≤ Real.log (L2 * (k : ℝ)) := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hLk : 1 ≤ L2 * (k : ℝ) := by nlinarith only [hL2, hk1]
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    simp only [Nat.cast_zero, mul_zero, Real.log_zero]
    exact Real.log_nonneg hLk
  · have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have hjkR : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hjk
    exact Real.log_le_log (by nlinarith only [hL2, hj1]) (by nlinarith only [hL2, hjkR])

private theorem akhcStep2_Kst_nonneg (d : ℕ) (sp rho : ℝ) : 0 ≤ akhcPrime_Kst d sp rho := by
  unfold akhcPrime_Kst akhcWeakC2_maximizerConst
  refine mul_nonneg (by norm_num) ?_
  refine add_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) ?_
  · exact mul_nonneg (by norm_num) (sq_nonneg _)
  · exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _))
      (sq_nonneg _)
  · exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _))
      (sq_nonneg _)
  · exact mul_nonneg (by norm_num) (sq_nonneg _)

private theorem akhcStep2_Vsmall (d : ℕ) {A1 om d1 : ℝ} (hA1 : 0 ≤ A1) (hd10 : 0 ≤ d1)
    (hd11 : d1 ≤ 1) (hA1om : 16 * (3 + 6 * (d : ℝ)) * (d : ℝ) ^ 2 * A1 * om ^ 2 ≤ d1) :
    (3 + 6 * (d : ℝ)) * ((1 + d1) ^ 2 * ((2 * (d : ℝ)) ^ 2 * A1 * om ^ 2)) +
      51 * (d : ℝ) ^ 2 * (2 * (d : ℝ) * d1 + (2 * (d : ℝ) * d1) ^ 2) ≤ akhcStep2_cV d * d1 := by
  have hdR : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h36 : (0 : ℝ) ≤ 3 + 6 * (d : ℝ) := by linarith only [hdR]
  have hom0 : 0 ≤ om ^ 2 := sq_nonneg _
  have hsq : (1 + d1) ^ 2 ≤ 4 := by nlinarith only [hd10, hd11]
  have hX : 0 ≤ (2 * (d : ℝ)) ^ 2 * A1 * om ^ 2 :=
    mul_nonneg (mul_nonneg (sq_nonneg _) hA1) hom0
  have hfirst : (3 + 6 * (d : ℝ)) * ((1 + d1) ^ 2 * ((2 * (d : ℝ)) ^ 2 * A1 *
      om ^ 2)) ≤ d1 := by
    have h1 : (1 + d1) ^ 2 * ((2 * (d : ℝ)) ^ 2 * A1 * om ^ 2) ≤
        4 * ((2 * (d : ℝ)) ^ 2 * A1 * om ^ 2) :=
      mul_le_mul_of_nonneg_right hsq hX
    have h2 := mul_le_mul_of_nonneg_left h1 h36
    have heq : (3 + 6 * (d : ℝ)) * (4 * ((2 * (d : ℝ)) ^ 2 * A1 *
        om ^ 2)) =
        16 * (3 + 6 * (d : ℝ)) * (d : ℝ) ^ 2 * A1 * om ^ 2 := by ring
    linarith only [h2, heq, hA1om]
  have hsecond : 51 * (d : ℝ) ^ 2 * (2 * (d : ℝ) * d1 + (2 * (d : ℝ) * d1) ^ 2) ≤
      51 * (d : ℝ) ^ 2 * (2 * d + 4 * (d : ℝ) ^ 2) * d1 := by
    have hdd : d1 ^ 2 ≤ d1 := by nlinarith only [hd10, hd11]
    have hd2 : (0 : ℝ) ≤ (d : ℝ) ^ 2 := sq_nonneg _
    have h4 : 4 * (d : ℝ) ^ 2 * d1 ^ 2 ≤ 4 * (d : ℝ) ^ 2 * d1 :=
      mul_le_mul_of_nonneg_left hdd (mul_nonneg (by norm_num) hd2)
    have heq1 : (2 * (d : ℝ) * d1 + (2 * (d : ℝ) * d1) ^ 2) =
        2 * (d : ℝ) * d1 + 4 * (d : ℝ) ^ 2 * d1 ^ 2 := by ring
    have heq2 : 51 * (d : ℝ) ^ 2 * (2 * d + 4 * (d : ℝ) ^ 2) * d1 =
        51 * (d : ℝ) ^ 2 * (2 * (d : ℝ) * d1 + 4 * (d : ℝ) ^ 2 * d1) := by ring
    rw [heq1, heq2]
    exact mul_le_mul_of_nonneg_left (by linarith only [h4]) (mul_nonneg (by norm_num) hd2)
  have hcV : akhcStep2_cV d * d1 = d1 + 51 * (d : ℝ) ^ 2 * (2 * d + 4 * (d : ℝ) ^ 2) * d1 := by
    unfold akhcStep2_cV; ring
  rw [hcV]
  linarith only [hfirst, hsecond]

private theorem akhcStep2_Msecond (d : ℕ) {eta rho KPsi A1 B1 omK omL d1 Ups : ℝ} (hA1 : 0 ≤ A1)
    (hB1 : 0 ≤ B1)
    (hB1def : B1 = (eta / (eta - 2)) * KPsi ^ (3 * ⌈eta⌉₊ ^ 2) *
      KPsi ^ (2 * (3 * (⌈eta⌉₊ : ℝ) ^ 2) / eta) *
      (1 - (3 : ℝ) ^ (-(2 * rho - 2 * (d : ℝ) / eta)))⁻¹)
    (hsq : omL ^ 2 ≤ omK ^ 2)
    (hUps : Ups = 16 * (3 + 6 * (d : ℝ)) * (d : ℝ) ^ 2 * A1 + 2 * B1)
    (hOm : omK ^ 2 * Ups ≤ d1) :
    (eta / (eta - 2)) * KPsi ^ (3 * ⌈eta⌉₊ ^ 2) *
      KPsi ^ (2 * (3 * (⌈eta⌉₊ : ℝ) ^ 2) / eta) * omL ^ 2 *
      (1 - (3 : ℝ) ^ (-(2 * rho - 2 * (d : ℝ) / eta)))⁻¹ ≤ d1 / 2 := by
  have hdR : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h36 : (0 : ℝ) ≤ 3 + 6 * (d : ℝ) := by linarith only [hdR]
  have heq : (eta / (eta - 2)) * KPsi ^ (3 * ⌈eta⌉₊ ^ 2) *
      KPsi ^ (2 * (3 * (⌈eta⌉₊ : ℝ) ^ 2) / eta) * omL ^ 2 *
      (1 - (3 : ℝ) ^ (-(2 * rho - 2 * (d : ℝ) / eta)))⁻¹ = B1 * omL ^ 2 := by
    rw [hB1def]; ring
  have hA1nn : 0 ≤ 16 * (3 + 6 * (d : ℝ)) * (d : ℝ) ^ 2 * A1 * omK ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h36) (sq_nonneg _)) hA1)
      (sq_nonneg _)
  have heq2 : omK ^ 2 * Ups =
      16 * (3 + 6 * (d : ℝ)) * (d : ℝ) ^ 2 * A1 * omK ^ 2 + 2 * (B1 * omK ^ 2) := by
    rw [hUps]; ring
  have hBmono := mul_le_mul_of_nonneg_left hsq hB1
  rw [heq]
  linarith only [hOm, heq2, hA1nn, hBmono]

private theorem akhcStep2_Mpre {H KPsiS D : ℝ} (k : ℕ) (hH : 1 ≤ H) (hKPsiS : 1 ≤ KPsiS) :
    0 ≤ 3 * KPsiS ^ 36 * (H * (k : ℝ) ^ D) ^ (2 : ℝ) := by
  have h1 : 0 ≤ (H * (k : ℝ) ^ D) ^ (2 : ℝ) :=
    Real.rpow_nonneg (mul_nonneg (zero_le_one.trans hH)
      (Real.rpow_nonneg (Nat.cast_nonneg k) D)) _
  exact mul_nonneg (mul_nonneg zero_le_three (pow_nonneg (zero_le_one.trans hKPsiS) _)) h1

section RouteElaborateAtLag

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

omit homegaAnti in
/-- **Node 30 in C6's `hV` form, over the window `[k-L+1, k]`.** From the `2L`-pigeon sandwich
and the `(P3′)` window at the fixed inner scale `k - 2L`. -/
theorem akhcStep2_hV {k Lp : ℕ} (hLpos : 1 ≤ Lp) (hk2L : 2 * Lp ≤ k) (hm3 : m3 ≤ k - 2 * Lp)
    (hbetaw : beta * (k : ℝ) < ((k - 2 * Lp : ℕ) : ℝ))
    (hLwin : 2 * (L1 * Real.log (L2 * (k : ℝ))) + 4 ≤ (Lp : ℝ))
    {delta1 : ℝ}
    (hAle : sigmaBarSeq nu L P (k - 2 * Lp) ≤ (1 + delta1) * sigmaBarSeq nu L P k)
    (hBle : sigmaBarStarInvSeq nu L P (k - 2 * Lp) ≤ (1 + delta1) * sigmaBarStarInvSeq nu L P k) :
    ∀ n ∈ Finset.Icc (((k - Lp : ℕ) : ℤ) + 1) (k : ℤ),
      ∫ a, SuperdiffusionCLT.AKHC61.Response.akhcFullBlockNormalizedFluctuationAtScale
          nu L P (k : ℤ) (originCube d n) a
        ∂(SuperdiffusionCLT.Section2.Annealed.cutoffLaw (d := d) nu L P) ≤
      (3 + 6 * (d : ℝ)) * ((1 + delta1) ^ 2 *
          ((2 * (d : ℝ)) ^ 2 *
            ((SuperdiffusionCLT.AKHC61.Params.akhcEta d pPsi /
                (SuperdiffusionCLT.AKHC61.Params.akhcEta d pPsi - 2)) *
              KPsi ^ (3 * ⌈SuperdiffusionCLT.AKHC61.Params.akhcEta d pPsi⌉₊ ^ 2)) *
            omegaSeq (k - 2 * Lp) ^ 2)) +
        51 * (d : ℝ) ^ 2 * (2 * (d : ℝ) * delta1 + (2 * (d : ℝ) * delta1) ^ 2) := by
  intro n hn
  obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.1 hn
  have hn0 : 0 ≤ n := by omega
  obtain ⟨nn, rfl⟩ : ∃ nn : ℕ, n = (nn : ℤ) := ⟨n.toNat, (Int.toNat_of_nonneg hn0).symm⟩
  have hnk : nn ≤ k := by exact_mod_cast hn2
  have hnlo : k - Lp + 1 ≤ nn := by omega
  have hk1 : 1 ≤ k := by omega
  have hjn : k - 2 * Lp ≤ nn := by omega
  have hbridge := akhcPrime_integral_fl_le_relFrob hnu P L gamma H D m2 PsiS KPsiS pPsiS hgamma0
    hgamma1 hH hDnn hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowthP2 hP2 hJ4 k nn
  have heta : SuperdiffusionCLT.AKHC61.Params.akhcEta d pPsi = min ((d : ℝ) + 1) pPsi := rfl
  have hpEta : (d : ℝ) < SuperdiffusionCLT.AKHC61.Params.akhcEta d pPsi := by
    rw [heta]; exact lt_min (by linarith only) hpPsi
  have hGrowthEta : ∀ p : ℝ, 1 < p → p ≤ SuperdiffusionCLT.AKHC61.Params.akhcEta d pPsi →
      ∀ t s : ℝ, 1 ≤ t → 1 ≤ s → s ^ p ≤ KPsi ^ (3 * ⌈p⌉₊ ^ 2) * (Psi (t * s) / Psi t) :=
    fun p hp1 hp2 => hGrowthPsi p hp1 (hp2.trans (min_le_right _ _))
  have hwin1 : beta * (nn : ℝ) < ((k - 2 * Lp : ℕ) : ℝ) := by
    have hnkR : (nn : ℝ) ≤ (k : ℝ) := by exact_mod_cast hnk
    have := mul_le_mul_of_nonneg_left hnkR hbeta0
    linarith only [this, hbetaw]
  have hwin2 : ((k - 2 * Lp : ℕ) : ℝ) < (nn : ℝ) - L1 * Real.log (L2 * ((k - 2 * Lp : ℕ) : ℝ)) := by
    have hlog := akhcStep2_log_mono hL2 (Nat.sub_le k (2 * Lp)) hk1
    have hlogk0 : 0 ≤ Real.log (L2 * (k : ℝ)) := by
      have hk1R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
      exact Real.log_nonneg (by nlinarith only [hL2, hk1R])
    have hL1log := mul_le_mul_of_nonneg_left hlog (by linarith only [hL1] : (0 : ℝ) ≤ L1)
    have hL1logk0 : 0 ≤ L1 * Real.log (L2 * (k : ℝ)) :=
      mul_nonneg (by linarith only [hL1]) hlogk0
    have hgap : (((k - 2 * Lp : ℕ) : ℝ)) + (Lp : ℝ) + 1 ≤ (nn : ℝ) := by
      have : k - 2 * Lp + Lp + 1 ≤ nn := by omega
      exact_mod_cast this
    linarith only [hgap, hL1log, hL1logk0, hLwin]
  have hsand := akhcOneC_sigmaBar_sandwich_window hnu L P hPrefix hJ2 hJ4 gamma H D m2 PsiS
    KPsiS pPsiS hgamma0 hgamma1 hH hDnn hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowthP2 hP2 hjn hnk
    hAle hBle
  have hsandJ := akhcOneC_sigmaBar_sandwich_window hnu L P hPrefix hJ2 hJ4 gamma H D m2 PsiS
    KPsiS pPsiS hgamma0 hgamma1 hH hDnn hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowthP2 hP2
    (le_refl (k - 2 * Lp)) (Nat.sub_le k (2 * Lp)) hAle hBle
  have h30 := akhcLaunch_variance_HC_prime hnu L P hPrefix hJ2 hJ4 hd gamma H D m2 PsiS KPsiS
    pPsiS hgamma0 hgamma1 hH hDnn hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowthP2 hP2 beta L1 L2 m3
    omegaSeq Psi KPsi (SuperdiffusionCLT.AKHC61.Params.akhcEta d pPsi) homega hPsiOne hKPsi
    hpEta hGrowthEta hP3 (ktop := k) (j := k - 2 * Lp) (n := nn) (Nat.sub_le k (2 * Lp)) hnk hjn
    hm3 hwin1 hwin2 hsandJ.1 hsandJ.2 hsand.1 hsand.2
  exact hbridge.trans h30

/-- **Node 40 at lag `L`, analytic inputs discharged.** Dichotomy alternative (a) (the `2L`-pigeon
sandwich `hblock` at a witness `k`) gives the one-step bound `Θ_{m+N′} ≤ 1 + ¼σΘ_m`, with the
proof-native `s′, ρ, η, c_V, K_w` of `Params/ConstantsProofNative.lean`. The remaining inputs are scalar
facts about `L`, `ω`, `δ` (discharged from `L ≥ L_req` and the `ω`-smallness in
`Step2/StepTwo.lean`) and the window facts `hm3`, `hbetaw`. -/
theorem akhcStep2_routeElaborate {m k Lp : ℕ} (hLpos : 1 ≤ Lp) (hmk : m ≤ k) (hk2 : m2 ≤ k)
    (hk2L : 2 * Lp ≤ k) (hm3 : m3 ≤ k - 2 * Lp)
    (hbetaw : beta * (k : ℝ) < ((k - 2 * Lp : ℕ) : ℝ))
    (hLwin : 2 * (L1 * Real.log (L2 * (k : ℝ))) + 4 ≤ (Lp : ℝ))
    {sigma delta : ℝ} (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) (hdelta0 : 0 ≤ delta)
    (hsmall : delta * sigma ^ 2 ≤ 1)
    (hkN : k ≤ m + akhcLaunchNprimeNat Lp delta sigma)
    (hblock : Homogenization.BlockMatLoewnerLE
        (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
          (cubeSet (originCube d ((k - 2 * Lp : ℕ) : ℤ))))
        ((1 + delta * sigma ^ 2) • SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix
          nu L P (cubeSet (originCube d (k : ℤ)))))
    (hT1 : (3 : ℝ) ^ (-((1 - 2 * akhcStep2_sPrime d gamma pPsi pPsiS) * (Lp : ℝ))) ≤
      delta * sigma ^ 2)
    (hT2 : (3 : ℝ) ^ (-(Lp : ℝ)) ≤ delta * sigma ^ 2)
    (hMt : 3 * KPsiS ^ 36 * (H * (k : ℝ) ^ D) ^ (2 : ℝ) *
        (3 : ℝ) ^ (-((SuperdiffusionCLT.AKHC61.Params.akhcRho d gamma pPsi pPsiS - gamma) *
          (Lp : ℝ))) / (min 3 pPsiS - 2) ≤ delta * sigma ^ 2 / 2)
    (hOm : omegaSeq (k - 2 * Lp) ^ 2 * akhcStep2_Upsilon1 d gamma pPsi pPsiS KPsi ≤
      delta * sigma ^ 2)
    (hdelta_le : delta ≤ akhcOneDelta0 d (akhcStep2_Kw d gamma pPsi pPsiS))
    (e : Vec d) (he : vecNormSq e = 1) :
    SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P
        (m + akhcLaunchNprimeNat Lp delta sigma) ≤
      1 + 1 / 4 * sigma * SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m := by
  obtain ⟨hlo, hhi, hgap, hgammarho, heta2, hetaPsi, hcpos⟩ :=
    akhcStep2_ranges hd hgamma0 hgamma1 hpPsi hpPsiS
  set sp := akhcStep2_sPrime d gamma pPsi pPsiS with hspdef
  set rho := SuperdiffusionCLT.AKHC61.Params.akhcRho d gamma pPsi pPsiS with hrhodef
  set eta := SuperdiffusionCLT.AKHC61.Params.akhcEta d pPsi with hetadef
  set d1 := delta * sigma ^ 2 with hd1def
  have hd10 : 0 ≤ d1 := mul_nonneg hdelta0 (sq_nonneg sigma)
  have hk1 : 1 ≤ k := by omega
  -- the pigeon sandwich at `2L`, and at `L` by antitonicity
  have hPig2 := (akhc_blockMatLoewnerLE_annealedBlockMatrix_smul_iff hnu L hJ4
    ((k - 2 * Lp : ℕ) : ℤ) (k : ℤ) (1 + d1)).1 hblock
  have hAle : sigmaBarSeq nu L P (k - 2 * Lp) ≤ (1 + d1) * sigmaBarSeq nu L P k := hPig2.1
  have hBle : sigmaBarStarInvSeq nu L P (k - 2 * Lp) ≤ (1 + d1) * sigmaBarStarInvSeq nu L P k :=
    hPig2.2
  have hsandL := akhcOneC_sigmaBar_sandwich_window hnu L P hPrefix hJ2 hJ4 gamma H D m2 PsiS
    KPsiS pPsiS hgamma0 hgamma1 hH hDnn hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowthP2 hP2
    (show k - 2 * Lp ≤ k - Lp by omega) (Nat.sub_le k Lp) hAle hBle
  have hPigeonL := (akhc_blockMatLoewnerLE_annealedBlockMatrix_smul_iff hnu L hJ4
    ((k - Lp : ℕ) : ℤ) (k : ℤ) (1 + d1)).2 ⟨hsandL.1, hsandL.2⟩
  -- the variance input
  have heta2' : 0 < eta - 2 := by linarith only [heta2]
  have hetaq : 0 ≤ eta / (eta - 2) := div_nonneg (by linarith only [heta2]) heta2'.le
  set A1 : ℝ := (eta / (eta - 2)) * KPsi ^ (3 * ⌈eta⌉₊ ^ 2) with hA1def
  have hA1 : 0 ≤ A1 := mul_nonneg hetaq (pow_nonneg (by linarith only [hKPsi]) _)
  set V : ℝ := (3 + 6 * (d : ℝ)) * ((1 + d1) ^ 2 * ((2 * (d : ℝ)) ^ 2 * A1 *
      omegaSeq (k - 2 * Lp) ^ 2)) +
    51 * (d : ℝ) ^ 2 * (2 * (d : ℝ) * d1 + (2 * (d : ℝ) * d1) ^ 2) with hVdef
  have hV := akhcStep2_hV hnu L P hPrefix hJ2 hJ4 hd gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1
    hH hDnn hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowthP2 hP2 beta L1 L2 m3 omegaSeq Psi KPsi pPsi
    hbeta0 hL1 hL2 homega hPsiOne hKPsi hpPsi hGrowthPsi hP3 (Lp := Lp) hLpos hk2L hm3 hbetaw hLwin hAle hBle
  have hdR : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h36 : (0 : ℝ) ≤ 3 + 6 * (d : ℝ) := by linarith only [hdR]
  have hV0 : 0 ≤ V := by
    rw [hVdef]
    exact add_nonneg (mul_nonneg h36 (mul_nonneg (sq_nonneg _)
      (mul_nonneg (mul_nonneg (sq_nonneg _) hA1) (sq_nonneg _))))
      (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
        (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hdR) hd10) (sq_nonneg _)))
  set B1 : ℝ := (eta / (eta - 2)) * KPsi ^ (3 * ⌈eta⌉₊ ^ 2) *
      KPsi ^ (2 * (3 * (⌈eta⌉₊ : ℝ) ^ 2) / eta) *
      (1 - (3 : ℝ) ^ (-(2 * rho - 2 * (d : ℝ) / eta)))⁻¹ with hB1def
  have h3lt : (3 : ℝ) ^ (-(2 * rho - 2 * (d : ℝ) / eta)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hcpos])
  have hB1 : 0 ≤ B1 := by
    have hinv : 0 ≤ (1 - (3 : ℝ) ^ (-(2 * rho - 2 * (d : ℝ) / eta)))⁻¹ :=
      inv_nonneg.2 (by linarith only [h3lt])
    have hK0 : (0 : ℝ) ≤ KPsi := by linarith only [hKPsi]
    exact mul_nonneg (mul_nonneg (mul_nonneg hetaq (pow_nonneg hK0 _))
      (Real.rpow_nonneg hK0 _)) hinv
  have hUps : akhcStep2_Upsilon1 d gamma pPsi pPsiS KPsi =
      16 * (3 + 6 * (d : ℝ)) * (d : ℝ) ^ 2 * A1 + 2 * B1 := rfl
  have hom0 : 0 ≤ omegaSeq (k - 2 * Lp) ^ 2 := sq_nonneg _
  have hA1om : 16 * (3 + 6 * (d : ℝ)) * (d : ℝ) ^ 2 * A1 * omegaSeq (k - 2 * Lp) ^ 2 ≤ d1 := by
    have h2 : 0 ≤ 2 * B1 * omegaSeq (k - 2 * Lp) ^ 2 := mul_nonneg (by linarith only [hB1]) hom0
    have heq : omegaSeq (k - 2 * Lp) ^ 2 * akhcStep2_Upsilon1 d gamma pPsi pPsiS KPsi =
        16 * (3 + 6 * (d : ℝ)) * (d : ℝ) ^ 2 * A1 * omegaSeq (k - 2 * Lp) ^ 2 +
          2 * B1 * omegaSeq (k - 2 * Lp) ^ 2 := by rw [hUps]; ring
    linarith only [hOm, heq, h2]
  have hd11 : d1 ≤ 1 := hsmall
  have hVsmall : V ≤ akhcStep2_cV d * d1 := by
    rw [hVdef]
    exact akhcStep2_Vsmall d hA1 hd10 hd11 hA1om
  -- the inner scale `k0`
  set w : ℕ := ⌈L1 * Real.log (L2 * (k : ℝ))⌉₊ + 1 with hwdef
  have hlogk0 : 0 ≤ L1 * Real.log (L2 * (k : ℝ)) := by
    have hk1R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    exact mul_nonneg (by linarith only [hL1]) (Real.log_nonneg (by nlinarith only [hL2, hk1R]))
  have hwup : (w : ℝ) ≤ L1 * Real.log (L2 * (k : ℝ)) + 2 := by
    rw [hwdef]; push_cast
    have := Nat.ceil_lt_add_one hlogk0
    linarith only [this]
  have hwlo : L1 * Real.log (L2 * (k : ℝ)) + 1 ≤ (w : ℝ) := by
    rw [hwdef]; push_cast
    have := Nat.le_ceil (L1 * Real.log (L2 * (k : ℝ)))
    linarith only [this]
  have hwL : w ≤ Lp := by
    have : (w : ℝ) ≤ (Lp : ℝ) := by linarith only [hwup, hLwin, hlogk0]
    exact_mod_cast this
  have hLk : Lp ≤ k := by omega
  set k0 : ℕ := k - Lp + w with hk0def
  have hk0k : k0 ≤ k := by omega
  have hk0R : (k0 : ℝ) = (k : ℝ) - (Lp : ℝ) + (w : ℝ) := by
    rw [hk0def]; push_cast [Nat.cast_sub hLk]; ring
  have hkLR : ((k - Lp : ℕ) : ℝ) = (k : ℝ) - (Lp : ℝ) := by push_cast [Nat.cast_sub hLk]; ring
  have hwin : ((k - Lp : ℕ) : ℝ) < (k0 : ℝ) - L1 * Real.log (L2 * ((k - Lp : ℕ) : ℝ)) := by
    have hlog := akhcStep2_log_mono hL2 (Nat.sub_le k Lp) hk1
    have hL1log := mul_le_mul_of_nonneg_left hlog (by linarith only [hL1] : (0 : ℝ) ≤ L1)
    rw [hk0R, hkLR]
    rw [hkLR] at hL1log
    linarith only [hL1log, hwlo]
  have hm3L : m3 ≤ k - Lp := by omega
  have hbeta : beta * (k : ℝ) < ((k - Lp : ℕ) : ℝ) := by
    have : ((k - 2 * Lp : ℕ) : ℝ) ≤ ((k - Lp : ℕ) : ℝ) := by
      have h : k - 2 * Lp ≤ k - Lp := by omega
      exact_mod_cast h
    linarith only [this, hbetaw]
  -- `hMsmall`
  have hmin : 0 < min (3 : ℝ) pPsiS - 2 := by
    have : (2 : ℝ) < min (3 : ℝ) pPsiS := lt_min (by norm_num) hpPsiS
    linarith only [this]
  have hrg : 0 < rho - gamma := by
    have hr1 := akhcStep2_rhoPrime_lt_one hd hgamma1 hpPsi hpPsiS
    have hgr' := akhcStep2_gamma_le_rhoPrime d gamma pPsi pPsiS
    have hrho : rho = (1 + SuperdiffusionCLT.AKHC61.Params.akhcRhoPrime d gamma pPsi pPsiS) / 2 :=
      rfl
    rw [hrho]; linarith only [hr1, hgr']
  have hexp : -2 * (rho - gamma) * ((k : ℝ) - ((k0 : ℝ) - 1)) ≤ -((rho - gamma) * (Lp : ℝ)) := by
    rw [hk0R]
    have h1 : (Lp : ℝ) ≤ 2 * ((Lp : ℝ) - (w : ℝ) + 1) := by linarith only [hwup, hLwin]
    have h2 := mul_le_mul_of_nonneg_left h1 hrg.le
    have heq : -2 * (rho - gamma) * ((k : ℝ) - ((k : ℝ) - (Lp : ℝ) + (w : ℝ) - 1)) =
        -((rho - gamma) * (2 * ((Lp : ℝ) - (w : ℝ) + 1))) := by ring
    rw [heq]
    linarith only [h2]
  have hpre : 0 ≤ 3 * KPsiS ^ 36 * (H * (k : ℝ) ^ D) ^ (2 : ℝ) :=
    akhcStep2_Mpre k hH hKPsiS
  have hMfirst : 3 * KPsiS ^ 36 * (H * (k : ℝ) ^ D) ^ (2 : ℝ) *
      (3 : ℝ) ^ (-2 * (rho - gamma) * ((k : ℝ) - ((k0 : ℝ) - 1))) / (min 3 pPsiS - 2) ≤
      d1 / 2 := by
    have hr := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexp
    have h1 := mul_le_mul_of_nonneg_left hr hpre
    have h2 := div_le_div_of_nonneg_right h1 hmin.le
    exact h2.trans hMt
  have hMsecond : (eta / (eta - 2)) * KPsi ^ (3 * ⌈eta⌉₊ ^ 2) *
      KPsi ^ (2 * (3 * (⌈eta⌉₊ : ℝ) ^ 2) / eta) * omegaSeq (k - Lp) ^ 2 *
      (1 - (3 : ℝ) ^ (-(2 * rho - 2 * (d : ℝ) / eta)))⁻¹ ≤ d1 / 2 :=
    akhcStep2_Msecond d hA1 hB1 hB1def
      (pow_le_pow_left₀ (homega _).le (homegaAnti (show k - 2 * Lp ≤ k - Lp by omega)) 2) hUps hOm
  have hMsmall := add_le_add hMfirst hMsecond
  rw [add_halves] at hMsmall
  -- the two tails
  have hT1small : Real.rpow (3 : ℝ) (-(1 / 2 - sp) * (Lp : ℝ)) ^ 2 ≤ d1 := by
    show ((3 : ℝ) ^ (-(1 / 2 - sp) * (Lp : ℝ))) ^ 2 ≤ d1
    rw [sq, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    have heq : -(1 / 2 - sp) * (Lp : ℝ) + -(1 / 2 - sp) * (Lp : ℝ) = -((1 - 2 * sp) * (Lp : ℝ)) := by
      ring
    rw [heq]; exact hT1
  have hT2small : Real.rpow (3 : ℝ) (-(Lp : ℝ)) ≤ d1 := hT2
  -- C6
  have hcore := akhcPrime_step2_thetaBound hnu P L gamma H D m2 PsiS KPsiS pPsiS
    hgamma0 hgamma1 hH hDnn hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowthP2 hP2 hJ4 hPrefix hJ2
    beta L1 L2 m3 omegaSeq Psi KPsi pPsi hbeta0 hL1 hL2 homega hPsiOne hKPsi hGrowthPsi hP3
    (m := m) (k := k) (ell := Lp) (k0 := k0) hmk hLpos hLk hk2 hk0k hm3L hbeta hwin
    hlo hhi hgap hgammarho heta2 hetaPsi hcpos delta sigma hdelta0 hsigma0.le hsmall
    hPigeonL e he hV0 (akhcStep2_cV_nonneg d) hVsmall hV hMsmall hT1small hT2small
  -- absorption
  have hKst0 : 0 ≤ akhcPrime_Kst d sp rho := akhcStep2_Kst_nonneg d sp rho
  have hKw : akhcStep2_Kw d gamma pPsi pPsiS = akhcPrime_Kst d sp rho * (akhcStep2_cV d + 5) := rfl
  have hKw0 : 0 ≤ akhcPrime_Kst d sp rho * (akhcStep2_cV d + 5) :=
    mul_nonneg hKst0 (add_nonneg (akhcStep2_cV_nonneg d) (by norm_num))
  have hB1' : (1 : ℝ) ≤ 1 + Real.sqrt (akhcPrime_Kst d sp rho * (akhcStep2_cV d + 5)) +
      akhcPrime_Kst d sp rho * (akhcStep2_cV d + 5) := by
    have hsq := Real.sqrt_nonneg (akhcPrime_Kst d sp rho * (akhcStep2_cV d + 5))
    linarith only [hKw0, hsq]
  have hC4 := akhcOne_JBconst_ge_four d
  have hT2' : ((3 : ℝ) ^ Lp)⁻¹ ≤ d1 := by
    have heq : (3 : ℝ) ^ (-(Lp : ℝ)) = ((3 : ℝ) ^ Lp)⁻¹ := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
    rwa [heq] at hT2
  have htpos : (0 : ℝ) ≤ ((3 : ℝ) ^ Lp)⁻¹ := inv_nonneg.2 (pow_nonneg zero_le_three _)
  rw [hKw] at hdelta_le
  have habsorb := akhcOne_absorb hC4 hB1' hsigma0 hsigma1 hdelta0 htpos hT2' hdelta_le
  have hthetam0 : 0 ≤ SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m :=
    le_trans zero_le_one
      (akhc_one_le_thetaCutoff_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH
        hDnn hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowthP2 hP2 m)
  have hscaled := mul_le_mul_of_nonneg_right habsorb hthetam0
  have hkbound : SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P k ≤
      1 + 1 / 4 * sigma * SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m := by
    have h1 := hcore.trans hscaled
    linarith only [h1]
  have hanti : SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P
      (m + akhcLaunchNprimeNat Lp delta sigma) ≤
      SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P k :=
    akhc_antitone_thetaCutoff_of_P2 hnu hPrefix hJ2 hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0
      hgamma1 hH hDnn hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowthP2 hP2 hkN
  linarith only [hanti, hkbound]

end RouteElaborateAtLag

end

end SuperdiffusionCLT.AKHC61.Step2
