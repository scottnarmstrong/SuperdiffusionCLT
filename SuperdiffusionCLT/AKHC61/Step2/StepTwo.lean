/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.Step2.ElaborateLag

/-!
# Step 2 of AK.HC Theorem 6.1 closed in proof-native parameters (package F1)

Proof of `t.weaker.P3` of [AK], Step 2: `Θ_{m+3m₀} ≤ 1 + σ`.

**A separate pigeon step `Lp`.** A pigeon dichotomy built on package D1 (`Step2/Launch.lean`)
and D3 (`Step2/OneStep.lean`) would use the *cutoff index* `L` of the law
(`coefficientCutoff nu ω L`) also as the pigeonhole lag `h = 2L` and in the horizon
`akhcLaunchNprimeNat L δ σ`. The cutoff `L` is an arbitrary root binder, while the lag must be at
least `L_req` (`Params/ConstantsProofNative.lean`), so such statements cannot be used for Step 2 in
general. `akhcStep2_pigeon_dichotomy` below is the same argument with
the lag `Lp` a separate natural number.

## Main results

* `akhcStep2_pigeon_dichotomy`: node 27 with lag `Lp`.
* `akhcStep2_step_two`: `Θ_{m+3m₀} ≤ 1 + σ` from the root binders, `0 < σ < 1`, the port's
  `ω`-smallness `ω_m²·Υ₁ ≤ δσ²` and `akhcStep2_m0Req`.
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

/-- The port's `Υ₁` is nonnegative. -/
theorem akhcStep2_Upsilon1_nonneg {d : ℕ} (hd : 2 ≤ d) {gamma pPsi pPsiS KPsi : ℝ}
    (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1) (hpPsi : (d : ℝ) < pPsi) (hpPsiS : 2 < pPsiS)
    (hKPsi : 1 ≤ KPsi) : 0 ≤ akhcStep2_Upsilon1 d gamma pPsi pPsiS KPsi := by
  obtain ⟨-, -, -, -, heta2, -, hcpos⟩ := akhcStep2_ranges hd hgamma0 hgamma1 hpPsi hpPsiS
  have hetaq : 0 ≤ SuperdiffusionCLT.AKHC61.Params.akhcEta d pPsi /
      (SuperdiffusionCLT.AKHC61.Params.akhcEta d pPsi - 2) :=
    div_nonneg (by linarith only [heta2]) (by linarith only [heta2])
  have h3lt : (3 : ℝ) ^ (-(2 * SuperdiffusionCLT.AKHC61.Params.akhcRho d gamma pPsi pPsiS -
      2 * (d : ℝ) / SuperdiffusionCLT.AKHC61.Params.akhcEta d pPsi)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hcpos])
  have hinv : 0 ≤ (1 - (3 : ℝ) ^ (-(2 * SuperdiffusionCLT.AKHC61.Params.akhcRho d gamma pPsi
      pPsiS - 2 * (d : ℝ) / SuperdiffusionCLT.AKHC61.Params.akhcEta d pPsi)))⁻¹ :=
    inv_nonneg.2 (by linarith only [h3lt])
  unfold akhcStep2_Upsilon1
  have hK0 : (0 : ℝ) ≤ KPsi := by linarith only [hKPsi]
  positivity

section StepTwo

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

omit hd hbeta0 hL1 hL2 homega homegaAnti hPsiOne hKPsi hpPsi hGrowthPsi hP3 in
/-- **Node 27 with a separate lag `Lp`**: the pigeonhole lag `h = 2Lp` and horizon
`akhcLaunchNprimeNat Lp δ σ` are decoupled from the cutoff index `L` of the law. -/
theorem akhcStep2_pigeon_dichotomy (Lp m1 : ℕ) {sigma delta : ℝ} (hsigma0 : 0 < sigma)
    (hsigma1 : sigma < 1) (hdelta0 : 0 < delta) (hdelta_small : delta ≤ (6400 : ℝ)⁻¹) :
    (∃ k : ℕ, m1 + 2 * Lp ≤ k ∧ k ≤ m1 + akhcLaunchNprimeNat Lp delta sigma ∧
      BlockMatLoewnerLE
        (annealedBlockMatrix nu L P (cubeSet (originCube d ((k - 2 * Lp : ℕ) : ℤ))))
        ((1 + delta * sigma ^ 2) •
          annealedBlockMatrix nu L P (cubeSet (originCube d (k : ℤ))))) ∨
    SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P
        (m1 + akhcLaunchNprimeNat Lp delta sigma) ≤
      (sigma / 4) * SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m1 := by
  set delta1 : ℝ := delta * sigma ^ 2 with hdelta1_def
  set sigma1 : ℝ := sigma / 4 with hsigma1_def
  have hsigma2_lt_one : sigma ^ 2 < 1 := by nlinarith only [hsigma0, hsigma1]
  have hdelta1_pos : 0 < delta1 := by rw [hdelta1_def]; positivity
  have hsigma1_pos : 0 < sigma1 := by rw [hsigma1_def]; positivity
  have hdelta1_le : delta1 ≤ 1 / 2 := by
    rw [hdelta1_def]
    have h1 : delta * sigma ^ 2 ≤ delta * 1 :=
      mul_le_mul_of_nonneg_left hsigma2_lt_one.le hdelta0.le
    have h3 : delta ≤ (1 : ℝ) / 2 := by linarith only [hdelta_small]
    linarith only [h1, h3]
  have hsigma1_le : sigma1 ≤ 1 / 2 := by rw [hsigma1_def]; linarith only [hsigma1]
  set a : ℕ → Fin 1 → ℝ :=
    fun n _ => SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P n with ha_def
  have hpos : ∀ n i, 0 < a n i := by
    intro n i
    rw [ha_def]
    have h := akhc_one_le_thetaCutoff_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0
      hgamma1 hH hDnn hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowthP2 hP2 n
    linarith only [h]
  have hmono : ∀ n i, a (n + 1) i ≤ a n i := by
    intro n i
    rw [ha_def]
    exact akhc_antitone_thetaCutoff_of_P2 hnu hPrefix hJ2 hJ4 gamma H D m2 PsiS KPsiS pPsiS
      hgamma0 hgamma1 hH hDnn hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowthP2 hP2 (Nat.le_succ n)
  have hceq : (2 : ℝ) * ((1 : ℕ) : ℝ) * delta1⁻¹ * |Real.log sigma1| =
      2 / (sigma ^ 2 * delta) * |Real.log (sigma / 4)| := by
    rw [hdelta1_def, hsigma1_def, Nat.cast_one, div_eq_mul_inv]
    ring
  have hhorizon : 2 * Lp * Nat.ceil (2 * ((1 : ℕ) : ℝ) * delta1⁻¹ * |Real.log sigma1|) ≤
      akhcLaunchNprimeNat Lp delta sigma := by
    rw [hceq]
    unfold akhcLaunchNprimeNat
    exact le_refl _
  have hdich := akhcPigeon_main a hdelta1_pos hdelta1_le
    hsigma1_pos hsigma1_le hpos hmono (m₁ := m1) (h := 2 * Lp)
    (N := akhcLaunchNprimeNat Lp delta sigma) hhorizon
  rcases hdich with ⟨k, hk1, hk2, hk3⟩ | hcontract
  · left
    refine ⟨k, hk1, hk2, ?_⟩
    have hjk : k - 2 * Lp ≤ k := Nat.sub_le k (2 * Lp)
    have hThetaK : a (k - 2 * Lp) 0 ≤ (1 + delta1) * a k 0 := hk3 0
    rw [ha_def] at hThetaK
    exact akhcLaunch_pigeonSandwich_block hnu L P hPrefix hJ2 hJ4 gamma H D m2 PsiS KPsiS
      pPsiS hgamma0 hgamma1 hH hDnn hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowthP2 hP2 hjk hThetaK
  · right
    unfold akhcPigeon_thetaPow at hcontract
    rw [Fin.prod_univ_one, Fin.prod_univ_one, pow_one] at hcontract
    rw [ha_def] at hcontract
    exact hcontract

/-- **Step 2 closed in proof-native parameters** (`e.prime.step.one`, from the
iteration start `m + m₀`): `Θ_{m+3m₀} ≤ 1 + σ`. Every analytic input of node 40 is discharged;
the only inputs beyond the root binders are `0 < σ < 1` (fixed by Step 3), the port's
`ω`-smallness at `m` and the explicit `m₀` requirement `akhcStep2_m0Req`. -/
theorem akhcStep2_step_two {m m0 : ℕ} (hm : max m2 m3 ≤ m) {sigma : ℝ} (hsigma0 : 0 < sigma)
    (hsigma1 : sigma < 1)
    (hOmega : omegaSeq m ^ 2 * akhcStep2_Upsilon1 d gamma pPsi pPsiS KPsi ≤
      akhcStep2_delta d gamma pPsi pPsiS * sigma ^ 2)
    (hm0 : akhcStep2_m0Req d gamma pPsi pPsiS L1 L2 H D KPsiS beta sigma
      (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P 0) m m0) :
    SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P (m + 3 * m0) ≤ 1 + sigma := by
  set delta := akhcStep2_delta d gamma pPsi pPsiS with hdeltadef
  set Y := delta * sigma ^ 2 with hYdef
  set Lp := akhcStep2_Lreq d gamma pPsi pPsiS L1 L2 H D KPsiS Y (m + 3 * m0) with hLpdef
  set N := akhcLaunchNprimeNat Lp delta sigma with hNdef
  set Θ := fun n : ℕ => SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P n with hΘdef
  set nit := ⌈Real.log (3 * Θ 0)⌉₊ with hnitdef
  obtain ⟨hnN, hbetaLp⟩ := hm0
  have hdelta0 : 0 < delta := akhcStep2_delta_pos d gamma pPsi pPsiS
  have hdelta64 : delta ≤ (6400 : ℝ)⁻¹ := akhcStep2_delta_le d gamma pPsi pPsiS
  have hY : 0 < Y := by rw [hYdef]; positivity
  have hY1 : Y ≤ 1 := by
    have hs2 : sigma ^ 2 ≤ 1 := by nlinarith only [hsigma0, hsigma1]
    have := mul_le_mul hdelta64 hs2 (sq_nonneg sigma) (by norm_num)
    rw [hYdef]; linarith only [this]
  have hT1 := akhcStep2_T1_of_Lreq hd hgamma0 hgamma1 hpPsi hpPsiS hY (le_refl Lp)
  have hT2 := akhcStep2_T2_of_Lreq hd hgamma0 hgamma1 hpPsi hpPsiS hY (le_refl Lp)
  have hWtop := akhcStep2_window_of_Lreq (d := d) (gamma := gamma) (pPsi := pPsi) (pPsiS := pPsiS)
    (le_refl Lp)
  have hMtop := akhcStep2_Mtail_of_Lreq hd hgamma0 hgamma1 hpPsi hpPsiS hY hH hKPsiS (le_refl Lp)
  have hLp1 : 1 ≤ Lp := by rw [hLpdef]; unfold akhcStep2_Lreq; omega
  have hLpR : (1 : ℝ) ≤ (Lp : ℝ) := by exact_mod_cast hLp1
  have hbpos : 0 < (1 - beta) * (m0 : ℝ) := by linarith only [hbetaLp, hLpR]
  have hm0pos : 0 < m0 := by
    rcases Nat.eq_zero_or_pos m0 with h | h
    · rw [h, Nat.cast_zero, mul_zero] at hbpos; exact absurd hbpos (lt_irrefl 0)
    · exact h
  have hm0R : (0 : ℝ) < (m0 : ℝ) := by exact_mod_cast hm0pos
  have h1beta : 0 < 1 - beta := by
    by_contra hcon
    have : (1 - beta) * (m0 : ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hcon) hm0R.le
    linarith only [this, hbpos]
  have hUps0 := akhcStep2_Upsilon1_nonneg hd hgamma0 hgamma1 hpPsi hpPsiS hKPsi
  have hantiΘ : ∀ {i j : ℕ}, i ≤ j → Θ j ≤ Θ i := fun hij =>
    akhc_antitone_thetaCutoff_of_P2 hnu hPrefix hJ2 hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0
      hgamma1 hH hDnn hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowthP2 hP2 hij
  have hΘ1 : ∀ n, 1 ≤ Θ n := fun n =>
    akhc_one_le_thetaCutoff_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hDnn
      hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowthP2 hP2 n
  set e : Vec d := Pi.single (0 : Fin d) (1 : ℝ) with hedef
  have he : vecNormSq e = 1 := by simp [hedef, vecNormSq, vecDot, Pi.single_apply]
  have hm2m : m2 ≤ m := le_trans (le_max_left _ _) hm
  have hm3m : m3 ≤ m := le_trans (le_max_right _ _) hm
  -- the iteration
  set a : ℕ → ℝ := fun j => Θ (m + m0 + j * N) with hadef
  have ha0 : 1 ≤ a 0 := hΘ1 _
  have hn : Real.log (3 * a 0) ≤ (nit : ℝ) := by
    have h1 : a 0 ≤ Θ 0 := hantiΘ (Nat.zero_le _)
    have h2 : Real.log (3 * a 0) ≤ Real.log (3 * Θ 0) :=
      Real.log_le_log (by linarith only [ha0]) (by linarith only [h1])
    exact h2.trans (Nat.le_ceil _)
  have hrec : ∀ j : ℕ, j < nit → a (j + 1) ≤ 1 + sigma / 4 * a j := by
    intro j hj
    set b := m + m0 + j * N with hbdef
    have hab : a (j + 1) = Θ (b + N) := by
      simp only [hadef, hbdef]; congr 1; ring
    have haj : a j = Θ b := rfl
    rw [hab, haj]
    have hjN : (j + 1) * N ≤ m0 := le_trans (Nat.mul_le_mul_right N hj) hnN
    rcases akhcStep2_pigeon_dichotomy hnu L P hPrefix hJ2 hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0
        hgamma1 hH hDnn hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowthP2 hP2 Lp b hsigma0 hsigma1
        hdelta0 hdelta64 with ⟨k, hk1, hk2, hblock⟩ | hcontract
    · have hkK : k ≤ m + 3 * m0 := by
        have : j * N + N = (j + 1) * N := by ring
        omega
      have hk1' : 1 ≤ k := by omega
      have hbk : b ≤ k := by omega
      have hkm0 : m0 ≤ k := by omega
      have hk2L : 2 * Lp ≤ k := by omega
      have hbetaw : beta * (k : ℝ) < ((k - 2 * Lp : ℕ) : ℝ) := by
        have hkR : (m0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkm0
        have h1 := mul_le_mul_of_nonneg_left hkR h1beta.le
        have hcast : ((k - 2 * Lp : ℕ) : ℝ) = (k : ℝ) - 2 * (Lp : ℝ) := by
          push_cast [Nat.cast_sub hk2L]; ring
        rw [hcast]
        linarith only [h1, hbetaLp]
      have hLwin : 2 * (L1 * Real.log (L2 * (k : ℝ))) + 4 ≤ (Lp : ℝ) := by
        have hlog := akhcStep2_log_mono hL2 hkK (show 1 ≤ m + 3 * m0 by omega)
        have := mul_le_mul_of_nonneg_left hlog (by linarith only [hL1] : (0 : ℝ) ≤ L1)
        linarith only [this, hWtop]
      have hMt : 3 * KPsiS ^ 36 * (H * (k : ℝ) ^ D) ^ (2 : ℝ) *
          (3 : ℝ) ^ (-((SuperdiffusionCLT.AKHC61.Params.akhcRho d gamma pPsi pPsiS - gamma) *
            (Lp : ℝ))) / (min 3 pPsiS - 2) ≤ delta * sigma ^ 2 / 2 := by
        have hkKR : (k : ℝ) ≤ ((m + 3 * m0 : ℕ) : ℝ) := by exact_mod_cast hkK
        have hpowk : (k : ℝ) ^ D ≤ ((m + 3 * m0 : ℕ) : ℝ) ^ D :=
          Real.rpow_le_rpow (Nat.cast_nonneg k) hkKR hDnn
        have hHk : H * (k : ℝ) ^ D ≤ H * ((m + 3 * m0 : ℕ) : ℝ) ^ D :=
          mul_le_mul_of_nonneg_left hpowk (by linarith only [hH])
        have hsq : (H * (k : ℝ) ^ D) ^ (2 : ℝ) ≤ (H * ((m + 3 * m0 : ℕ) : ℝ) ^ D) ^ (2 : ℝ) :=
          Real.rpow_le_rpow (mul_nonneg (by linarith only [hH])
            (Real.rpow_nonneg (Nat.cast_nonneg k) D)) hHk (by norm_num)
        have hmin : 0 < min (3 : ℝ) pPsiS - 2 := by
          have : (2 : ℝ) < min (3 : ℝ) pPsiS := lt_min (by norm_num) hpPsiS
          linarith only [this]
        have hc : 0 ≤ 3 * KPsiS ^ 36 * (3 : ℝ) ^ (-((SuperdiffusionCLT.AKHC61.Params.akhcRho d
            gamma pPsi pPsiS - gamma) * (Lp : ℝ))) / (min 3 pPsiS - 2) := by positivity
        have h1 := mul_le_mul_of_nonneg_left hsq hc
        have heq1 : ∀ X : ℝ, 3 * KPsiS ^ 36 * X * (3 : ℝ) ^ (-((SuperdiffusionCLT.AKHC61.Params.akhcRho
            d gamma pPsi pPsiS - gamma) * (Lp : ℝ))) / (min 3 pPsiS - 2) =
            3 * KPsiS ^ 36 * (3 : ℝ) ^ (-((SuperdiffusionCLT.AKHC61.Params.akhcRho d gamma pPsi
              pPsiS - gamma) * (Lp : ℝ))) / (min 3 pPsiS - 2) * X := fun X => by ring
        rw [heq1]
        rw [heq1] at hMtop
        exact h1.trans hMtop
      have hOm : omegaSeq (k - 2 * Lp) ^ 2 * akhcStep2_Upsilon1 d gamma pPsi pPsiS KPsi ≤
          delta * sigma ^ 2 := by
        have hanti : omegaSeq (k - 2 * Lp) ≤ omegaSeq m := homegaAnti (by omega)
        have hsq : omegaSeq (k - 2 * Lp) ^ 2 ≤ omegaSeq m ^ 2 :=
          pow_le_pow_left₀ (homega _).le hanti 2
        exact (mul_le_mul_of_nonneg_right hsq hUps0).trans hOmega
      have hstep := akhcStep2_routeElaborate hnu L P hPrefix hJ2 hJ4 hd gamma H D m2 PsiS KPsiS pPsiS
        hgamma0 hgamma1 hH hDnn hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowthP2 hP2 beta L1 L2 m3
        omegaSeq Psi KPsi pPsi hbeta0 hL1 hL2 homega homegaAnti hPsiOne hKPsi hpPsi hGrowthPsi hP3
        (m := b) (k := k) (Lp := Lp) hLp1 hbk (le_trans hm2m (by omega)) hk2L
        (le_trans hm3m (by omega)) hbetaw hLwin hsigma0 hsigma1 hdelta0.le hY1 hk2 hblock hT1 hT2
        hMt hOm (akhcStep2_delta_le_delta0 d gamma pPsi pPsiS) e he
      have heq : 1 + 1 / 4 * sigma * Θ b = 1 + sigma / 4 * Θ b := by ring
      rw [← heq]
      exact hstep
    · have hΘb := hΘ1 b
      have : 0 ≤ sigma / 4 * Θ b := by positivity
      linarith only [hcontract, this]
  have hiter := SuperdiffusionCLT.AKHC61.Step2.akhcOne_iterate_bound hsigma0 hsigma1 ha0 hn hrec
  have hnN' : nit * N ≤ m0 := hnN
  have hfin : Θ (m + 3 * m0) ≤ a nit := hantiΘ (by omega)
  exact hfin.trans hiter

end StepTwo

end

end SuperdiffusionCLT.AKHC61.Step2
