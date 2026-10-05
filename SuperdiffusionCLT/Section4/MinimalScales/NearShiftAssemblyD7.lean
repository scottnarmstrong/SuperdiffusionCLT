/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.NearShiftAssemblyD6
public import SuperdiffusionCLT.Section4.MinimalScales.NearShiftAssemblyB
public import SuperdiffusionCLT.Section4.MinimalScales.NearShiftAssemblyB2
public import SuperdiffusionCLT.Section4.MinimalScales.NearSkewMaxE
public import SuperdiffusionCLT.Section3.HighContrast.RangeDependenceRestriction
public import SuperdiffusionCLT.Section4.MinimalScales.NearShiftAssemblyD7Aux

/-!
# The near-scale bound `hNear`

`srootNS_hNear`: the statement of the `hNear` hypothesis of `srootE_mathcalE_bounds_of_inputs`
(with the uniform-in-`h0` parameterized mixing bound as its premise), proved from the
local base (`srootNS_caseA_pathwise`), the tail comparison (`srootNS_caseB_pathwise`), the skew
maximum (`srootNS_skewMax`), the crude cap (`srootNS_response_le_crude`) and the packaging
`srootNSD_assemble`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

open MeasureTheory
open Homogenization.IndependentSums

noncomputable section

theorem srootNS_hNear (d : ℕ) [NeZero d] :
    (
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
                              (Homogenization.Book.Ch02.matrixOperatorNorm h0) ^ 2) * X2 omega) →
      ∀ C0 : ℝ, 1 ≤ C0 → ∃ A : ℝ, 1 ≤ A ∧ ∀ C1 : ℝ, A ≤ C1 →
      ∀ (nu cStar nondeg : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : MeasureTheory.ProbabilityMeasure
              (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
          (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
          (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
          (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar nondeg
              hPrefix hJ2 hJ3 →
          ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ K : ℝ, C1 ≤ K → ∀ m n : ℕ,
            SuperdiffusionCLT.Frozen.Section4.lNaught C1 (C1 * s⁻¹ * K) (1 / 2) cStar nu nondeg ≤ (m : ℝ) →
            m - ⌈K * Real.log (m : ℝ)⌉₊ ≤ n → n ≤ m →
            ∀ k : Fin d → ℤ, (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
                  Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)) ⊆
                Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)) →
              ∃ Y1 Y2 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                Measurable Y1 ∧
                IsBigO P.toMeasure (gammaSigma 1) Y1
                  (A * C1 * (s⁻¹ * K ^ ((1 : ℝ) / 2) * (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ *
                    Real.log (m : ℝ) ^ ((1 : ℝ) / 2)) ^ 2) ∧
                Measurable Y2 ∧
                IsBigO P.toMeasure (gammaSigma (1 / 3)) Y2 (A * (m : ℝ) ^ (-(2000 : ℝ))) ∧
                ∀ᵐ omega ∂P.toMeasure, ∀ L : ℕ, (m : ℝ) - C1 * s⁻¹ * ((⌈K * Real.log (m : ℝ)⌉₊ : ℕ) : ℝ) ≤ (L : ℝ) →
                  ∑ l ∈ Finset.range (⌈C0 * s⁻¹ * Real.log (m : ℝ)⌉₊ + 1),
                      srootE_term s (srootE_field nu omega L m n k)
                        ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) • (1 : Homogenization.Mat d)) n l ≤
                    A * C1 * (s ^ (-((1 : ℝ) / 2)) * K ^ ((1 : ℝ) / 2) * (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ *
                      Real.log (m : ℝ)) ^ 2 + Y1 omega + Y2 omega := by
  intro hParam C0 hC0
  have hNZ : NeZero d := inferInstance
  obtain ⟨Cp, hCp1, hCaseA⟩ := srootNS_caseA_pathwise d hParam
  obtain ⟨Aw, hAw1, hAw⟩ := srootNS_window_arith Cp C0 hCp1 hC0
  obtain ⟨Ask, hAsk1, hSk⟩ := srootNS_skewMax d
  obtain ⟨A0, hA01, hCr⟩ := srootNS_response_le_crude d
  have hg1 := srootNSD_gammaTriangleConst_pos 1
  have hg3 := srootNSD_gammaTriangleConst_pos (1 / 3)
  have hcE : 1 ≤ SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst d := by
    clear * - d
    exact SuperdiffusionCLT.Section2.Annealed.one_le_cutoffEnvelopeConst d
  obtain ⟨cE, hcEdef⟩ : ∃ cE, cE = SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst d :=
    ⟨_, rfl⟩
  obtain ⟨ctc, hctcdef⟩ : ∃ ctc, ctc = max (srootN3_tailConst d) 1 := ⟨_, rfl⟩
  set g1 : ℝ := gammaTriangleConst 1 with hg1def
  set g3 : ℝ := gammaTriangleConst (1 / 3) with hg3def
  rw [← hcEdef] at hcE
  clear_value g1 g3
  have hctc1 : 1 ≤ ctc := by clear * - ctc hctcdef; rw [hctcdef]; exact le_max_right _ _
  have hdn : (0 : ℝ) ≤ d := by
    clear * - d
    exact Nat.cast_nonneg d
  obtain ⟨U0, hU0⟩ : ∃ U0, U0 = g1 * (1 + 6 * cE * Ask) := ⟨_, rfl⟩
  obtain ⟨c3, hc3⟩ : ∃ c3, c3 = 3 * (2 + 3 * C0 * (1 + 2 * (d : ℝ))) := ⟨_, rfl⟩
  obtain ⟨Q2, hQ2⟩ : ∃ Q2, Q2 = Cp * (2 : ℝ) ^ (5000 : ℝ) + 16 * cE ^ 2 * ctc := ⟨_, rfl⟩
  obtain ⟨e1c, he1c⟩ : ∃ e1c, e1c = 52 * cE ^ 2 * ctc := ⟨_, rfl⟩
  obtain ⟨A1, hA1⟩ : ∃ A1, A1 = g1 * Cp * (6 + 62 * (d : ℝ)) + g1 ^ 2 * Cp * Ask +
    14 * g1 ^ 3 * Cp := ⟨_, rfl⟩
  have hU0n : 0 ≤ U0 := by
    clear * - hAsk1 hg1 hcE U0 hU0
    rw [hU0]
    exact mul_nonneg hg1.le (add_nonneg zero_le_one (mul_nonneg (mul_nonneg (by norm_num)
      (by linarith only [hcE])) (by linarith only [hAsk1])))
  have hc3n : 0 ≤ c3 := by
    clear * - d C0 hC0 hdn c3 hc3
    rw [hc3]
    have : 0 ≤ C0 * (1 + 2 * (d : ℝ)) := mul_nonneg (by linarith only [hC0]) (by linarith only [hdn])
    linarith only [this, hC0, hdn]
  have hQ2n : 0 ≤ Q2 := by
    clear * - hCp1 hctc1 Q2 hQ2
    rw [hQ2]
    exact add_nonneg (mul_nonneg (by linarith only [hCp1]) (Real.rpow_nonneg (by norm_num) _))
      (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by linarith only [hctc1]))
  have he1n : 0 ≤ e1c := by
    clear * - hctc1 e1c he1c
    rw [he1c]
    exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by linarith only [hctc1])
  have hA1n : 0 ≤ A1 := by
    clear * - d Cp hCp1 Ask hAsk1 hg1 hdn A1 hA1
    rw [hA1]
    have hCp0 : 0 ≤ Cp := by linarith only [hCp1]
    have hAs0 : 0 ≤ Ask := by linarith only [hAsk1]
    have hd62 : 0 ≤ 6 + 62 * (d : ℝ) := by linarith only [hdn]
    exact add_nonneg (add_nonneg (mul_nonneg (mul_nonneg hg1.le hCp0) hd62)
      (mul_nonneg (mul_nonneg (sq_nonneg _) hCp0) hAs0))
      (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hg1.le 3)) hCp0)
  have hA2n : 0 ≤ Cp * (2 * Ask + 44) := by
    clear * - Cp hCp1 Ask hAsk1
    exact mul_nonneg (by linarith only [hCp1]) (by linarith only [hAsk1])
  have hA3n : 0 ≤ g3 * (1 + 16384 * A0) := by
    clear * - A0 hA01 hg3 g3
    exact mul_nonneg hg3.le (by linarith only [hA01])
  obtain ⟨Abig, hAbig⟩ : ∃ Abig : ℝ, Abig = 20000 + Aw + Ask + A0 + U0 + c3 + Q2 + e1c +
      Cp * (2 * Ask + 44) + A1 + g3 * (1 + 16384 * A0) := ⟨_, rfl⟩
  refine ⟨Abig, by rw [hAbig]; linarith only [hAw1, hAsk1, hA01, hU0n, hc3n, hQ2n, he1n, hA1n, hA2n, hA3n], ?_⟩
  intro C1 hC1 nu cStar nondeg hnu hnu1 P hPrefix hJ2 hJ3 hJ1V2 hJ4 hJ5 s hs0 hs1 K hK m n hm hn1 hn2 k hk
  have hc := hJ5.cStar_pos
  have hc2 := hJ5.cStar_le_two
  have hnd := hJ5.K_pos.le
  have hJ1 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1 d P := by
    clear * - d P hJ1V2
    exact SuperdiffusionCLT.Section3.HighContrast.shellLawJ1_of_shellLawJ1Restriction hJ1V2
  obtain ⟨hCw, hC20, hAsk', hU0C, hc3C, hQ2C, he1C, hA1C, hA2C, hA3C⟩ :=
    srootNSD7_consts hAw1 hAsk1 hA01 hU0n hc3n hQ2n he1n hA1n hA2n hA3n hAbig hC1
  clear hAbig
  obtain ⟨hm64, hlg4, hKm', hh2, hhbar2, h1h, h2h, hlog2h, hlog2h2, h4C1, hwin⟩ :=
    hAw C1 hCw nu cStar nondeg hnu hnu1 hc hc2 hnd s hs0 hs1 K hK m n hm hn1 hn2
  clear h2h hKm' hCw hAw
  obtain ⟨_, hcore⟩ := srootNS_threshold_core (by linarith only [hC20]) hs0 hs1 hK hnd hc hc2 hnu
    hnu1 hm
  obtain ⟨hC1m, hPm, hKm⟩ := srootNSD_basic (by linarith only [hC20]) hs0 hs1 hK hlg4 hcore
  clear hKm
  have hni : nu⁻¹ ≤ (m : ℝ) := by
    clear * - nu hnu hnu1 hs0 hK m hm hc hc2 hnd hC20
    exact srootNS_nuInv_le_of_lNaught (by linarith only [hC20])
        (mul_nonneg (mul_nonneg (by linarith only [hC20]) (inv_nonneg.2 hs0.le))
          (by linarith only [hK, hC20])) hnd hc hc2 hnu hnu1 hm
  clear hnd hc2 hc
  obtain ⟨hσpos, hσinv, hσup⟩ := srootD4_sigma_bounds (P := P) hnu m hPrefix hJ2 hJ3 hJ4
  have hm1 : (1 : ℝ) ≤ m := by clear * - m hm64; linarith only [hm64]
  have hlgm : Real.log (m : ℝ) ≤ m := by
    clear * - m hm1
    have := Real.log_le_sub_one_of_pos (by linarith only [hm1] : (0 : ℝ) < m)
    linarith only [this]
  have hni1 : 1 ≤ nu⁻¹ := by
    clear * - nu hnu hnu1
    exact (one_le_inv₀ hnu).2 hnu1
  rw [← hcEdef] at hσinv hσup
  set σ : ℝ := SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P with hσdef
  set lg : ℝ := Real.log (m : ℝ) with hlgdef
  set h : ℕ := ⌈K * lg⌉₊ with hhdef
  set hbar : ℕ := ⌈C0 * s⁻¹ * lg⌉₊ with hhbardef
  clear hhbardef
  clear_value σ lg h hbar
  have hu0 : 0 ≤ σ⁻¹ := by
    clear * - hσpos σ
    exact inv_nonneg.2 hσpos.le
  have hu : σ⁻¹ ≤ 2 * cE * m := by
    clear * - hcE cE m hni hσinv σ
    refine hσinv.trans ?_
    exact mul_le_mul_of_nonneg_left hni (by linarith only [hcE])
  clear hσinv
  obtain ⟨W, hWm, hW0, hWO, hWb⟩ := hSk C1 hAsk' nu cStar nondeg hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 s
    hs0 hs1 K hK m hm
  clear hJ1 hC1 hA3n hA2n hA1n hSk hAw1 hAsk'
  rw [← hlgdef] at hWb hWO
  rw [← hhdef] at hWb
  obtain ⟨G, hGm, hGO, hGae⟩ := hCr C1 (by linarith only [hC20]) nu cStar nondeg hnu hnu1 P hPrefix
    hJ2 hJ3 hJ1V2 hJ4 hJ5 s hs0 hs1 K hK m n hm (by rw [hhdef, hlgdef] at hn1; exact hn1) hn2 k hk
  clear hn2 hn1 hm hCr
  have ht1 : 1 ≤ s⁻¹ := by
    clear * - s hs0 hs1
    exact (one_le_inv₀ hs0).2 hs1
  have hK1 : 1 ≤ K := by clear * - K hK hC20; linarith only [hK, hC20]
  have hlg1 : 1 ≤ lg := by clear * - hlg4 lg; linarith only [hlg4]
  have hCpp : 0 < Cp := by clear * - Cp hCp1; linarith only [hCp1]
  have hAskp : 0 < Ask := by clear * - Ask hAsk1; linarith only [hAsk1]
  have hKpos : 0 < K := by clear * - K hK1; linarith only [hK1]
  have hlgpos : 0 < lg := by clear * - lg hlg1; linarith only [hlg1]
  have hmpos : (0 : ℝ) < m := by clear * - m hm1; linarith only [hm1]
  have hsi : 0 < s⁻¹ := by
    clear * - s hs0
    exact inv_pos.2 hs0
  have hC1pos : 0 < C1 := by clear * - C1 hC20; linarith only [hC20]
  have hKlg : K * lg ≤ m := by
    clear * - s K m hPm lg ht1 hK1 hlg1
    have h1 : K * 1 ≤ K * s⁻¹ := mul_le_mul_of_nonneg_left ht1 (by linarith only [hK1])
    have h3 := mul_le_mul_of_nonneg_right h1 (by linarith only [hlg1] : (0 : ℝ) ≤ lg)
    linarith only [h3, hPm]
  have hCount := srootNSD_count_le (by linarith only [hC20]) ht1 hK1 hlg4
    (by linarith only [hm64]) hcore hh2
  clear ht1 hcore hlg4
  have hh0 : (0 : ℝ) ≤ h := by
    clear * - h
    exact Nat.cast_nonneg h
  have hCt0 : 0 ≤ C1 * s⁻¹ * (h : ℝ) := by
    clear * - C1 s hs0 hC20 h hh0
    exact mul_nonneg (mul_nonneg (by linarith only [hC20]) (inv_nonneg.2 hs0.le)) hh0
    -- opaque data
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a = ⌈(m : ℝ) - C1 * s⁻¹ * (h : ℝ)⌉₊ := ⟨_, rfl⟩
  obtain ⟨Nl, hNldef⟩ : ∃ Nl : ℕ, Nl = hbar + 1 := ⟨_, rfl⟩
  obtain ⟨S, hSdef⟩ : ∃ S : ℕ → Finset (Homogenization.TriadicCube d), ∀ l,
      S l = Homogenization.descendantsAtScale (Homogenization.originCube d (n : ℤ))
        ((n : ℤ) - (l : ℤ)) := ⟨_, fun _ => rfl⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℕ → ℕ →
      Homogenization.TriadicCube d → ℝ, ∀ ω L l R, Φ ω L l R =
      Homogenization.normalizedBlockResponseMax R (srootE_field nu ω L m n k)
        (σ • (1 : Homogenization.Mat d)) := ⟨_, fun _ _ _ _ => rfl⟩
  obtain ⟨Mx, hMxdef⟩ : ∃ Mx : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℕ → ℕ → ℝ,
      ∀ ω L l, Mx ω L l = Homogenization.maxDescendantNormalizedBlockResponseAtScale
        (Homogenization.originCube d (n : ℤ)) ((n : ℤ) - (l : ℤ)) (srootE_field nu ω L m n k)
        (σ • (1 : Homogenization.Mat d)) := ⟨_, fun _ _ _ => rfl⟩
  obtain ⟨q, hqdef⟩ : ∃ q : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℕ → ℝ,
      ∀ ω L, q ω L = (Homogenization.Book.Ch02.matrixOperatorNorm (srootNS_h0 m L ω)) ^ 2 :=
    ⟨_, fun _ _ => rfl⟩
  have hab : a ≤ m + h := by
    clear * - m h hh0 hCt0 a ha
    rw [ha]
    exact Nat.ceil_le.2 (by push_cast; linarith only [hCt0, hh0])
  have hNl : 0 < Nl := by clear * - Nl hNldef; rw [hNldef]; exact Nat.succ_pos _
  have hSne : ∀ l, (S l).Nonempty := by
    clear * - S hSdef
    exact fun l => by
      rw [hSdef]
      exact Homogenization.descendantsAtScale_nonempty _ (sub_le_self _ (Int.natCast_nonneg l))
  have hMx : ∀ ω L l z, a ≤ L → l < Nl → (∀ R ∈ S l, Φ ω L l R ≤ z) → Mx ω L l ≤ z := by
    clear * - n a Nl S hSdef Φ hΦ Mx hMxdef
    intro ω L l z _ _ hz
    rw [hMxdef]
    refine srootNSD_mx_le n l _ _ (fun R hR => ?_)
    rw [← hΦ]
    exact hz R (by rw [hSdef]; exact hR)
  have hwm := hwin m (by linarith only [hCt0, hh0]) (by linarith only [hh0])
  clear hCt0
  have hln : ∀ l ≤ hbar, l ≤ n := by
    clear * - n hbar hwm
    exact fun l hl => (hwm.2.2.2.2.2 l hl).1
  clear hwm
  have hq0 : ∀ ω L, 0 ≤ q ω L := by
    clear * - q hqdef
    exact fun ω L => by rw [hqdef]; exact sq_nonneg _
  have hq1 : ∀ ω L, a ≤ L → L ≤ m + h → q ω L ≤
      Ask * (K * lg * Real.log (2 * (h : ℝ))) + W ω := by
    clear * - Ask K m lg h W hWb a q hqdef
    intro ω L _ hL
    rw [hqdef, srootNS_h0, SuperdiffusionCLT.Frozen.Assumptions.ShellField.matrixOperatorNorm_neg_eq]
    exact hWb ω L hL
  clear hWb
  have hSdesc : ∀ l R, R ∈ S l → R ∈ Homogenization.descendantsAtScale
      (Homogenization.originCube d (n : ℤ)) ((n : ℤ) - (l : ℤ)) := by
    clear * - d n S hSdef
    exact fun l R hR => by
      rw [← hSdef]; exact hR
  have hcaseA : ∀ (L l : ℕ) (R : Homogenization.TriadicCube d),
      ∃ X1 X2 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
        a ≤ L → L ≤ m + h → l < Nl → R ∈ S l →
          Measurable X1 ∧ IsBigO P.toMeasure (gammaSigma 1) X1
            (Cp * σ ^ (-(2 : ℝ)) * (2 * (h : ℝ) + (l : ℝ) + 2 * (4 * C1 * s⁻¹ * K) * lg)) ∧
          Measurable X2 ∧ IsBigO P.toMeasure (gammaSigma (1 / 3)) X2
            (Cp * ((m : ℝ) / 2) ^ (-(5000 : ℝ))) ∧
          ∀ ω, Φ ω L l R ≤ Cp * σ ^ (-(2 : ℝ)) * (q ω L + (2 * (h : ℝ) + (l : ℝ)) +
            (4 * C1 * s⁻¹ * K) * (4 * lg ^ 2)) + X1 ω + (1 + σ ^ (-(1 : ℝ)) * q ω L) * X2 ω := by
    clear * - d Cp hCp1 hCaseA C1 nu cStar nondeg hnu hnu1 P hPrefix hJ2 hJ3 hJ1V2 hJ4 hJ5 s K m n k h4C1 hwin hσpos hm1 σ hσdef lg h hbar hlgpos hh0 a ha Nl hNldef S Φ hΦ q hqdef hSdesc
    intro L l R
    by_cases H : a ≤ L ∧ L ≤ m + h ∧ l < Nl ∧ R ∈ S l
    · obtain ⟨haL, hLb, hl, hR⟩ := H
      have hL1 : (m : ℝ) - C1 * s⁻¹ * (h : ℝ) ≤ L := by rw [ha] at haL; exact Nat.ceil_le.1 haL
      have hL2 : (L : ℝ) ≤ m + h := by exact_mod_cast hLb
      obtain ⟨hLhalf, hL2m, hlogL0, hlogL, habs, hlf⟩ := hwin L hL1 hL2
      have hlhbar : l ≤ hbar := by rw [hNldef] at hl; exact Nat.lt_succ_iff.1 hl
      obtain ⟨hln', hnnhalf, hLnn, hthrL, hthrnn, hscale⟩ := hlf l hlhbar
      obtain ⟨X1, X2, hX1m, hX1O, hX2m, hX2O, hineq⟩ := hCaseA nu cStar nondeg hnu hnu1 P hPrefix hJ2
        hJ3 hJ1V2 hJ4 hJ5 (4 * C1 * s⁻¹ * K) h4C1 m L n l k hln' hthrL hthrnn hscale habs R
        (hSdesc l R hR)
      rw [← hσdef] at hX1O hineq
      have hKp0 : 0 ≤ 4 * C1 * s⁻¹ * K := by linarith only [h4C1]
      have hCS : 0 ≤ Cp * σ ^ (-(2 : ℝ)) := by
        exact mul_nonneg (by linarith only [hCp1]) (Real.rpow_nonneg hσpos.le (-(2 : ℝ)))
      have hZ : max 0 ((L : ℝ) - ((n - l : ℕ) : ℝ)) ≤ 2 * (h : ℝ) + (l : ℝ) :=
        max_le (by linarith only [hh0, Nat.cast_nonneg (α := ℝ) l]) hLnn
      refine ⟨X1, X2, fun _ _ _ _ => ⟨hX1m, ?_, hX2m, ?_, ?_⟩⟩
      · refine hX1O.mono_scale (mul_le_mul_of_nonneg_left ?_ hCS)
        have := mul_le_mul_of_nonneg_left hlogL hKp0
        linarith only [hZ, this]
      · refine hX2O.mono_scale (mul_le_mul_of_nonneg_left ?_ (by linarith only [hCp1]))
        exact Real.rpow_le_rpow_of_nonpos (half_pos (by linarith only [hm1])) hnnhalf (by norm_num)
      · intro ω
        have h1 := hineq ω
        rw [← hΦ, ← hqdef] at h1
        have hΛ : Real.log (L : ℝ) ^ (2 : ℝ) ≤ 4 * lg ^ 2 := by
          rw [Real.rpow_two]
          have := mul_le_mul hlogL hlogL hlogL0 (by linarith only [hlgpos])
          linarith only [this]
        have h2 := mul_le_mul_of_nonneg_left hΛ hKp0
        have h3 : Cp * σ ^ (-(2 : ℝ)) * (q ω L + max 0 ((L : ℝ) - ((n - l : ℕ) : ℝ)) +
            (4 * C1 * s⁻¹ * K) * Real.log (L : ℝ) ^ (2 : ℝ)) ≤
            Cp * σ ^ (-(2 : ℝ)) * (q ω L + (2 * (h : ℝ) + (l : ℝ)) +
              (4 * C1 * s⁻¹ * K) * (4 * lg ^ 2)) :=
          mul_le_mul_of_nonneg_left (by linarith only [hZ, h2]) hCS
        exact h1.trans (add_le_add (add_le_add h3 le_rfl) le_rfl)
    · exact ⟨0, 0, fun h1 h2 h3 h4 => absurd ⟨h1, h2, h3, h4⟩ H⟩
  clear hwin hJ5 hJ1V2 hCaseA
  have hmK : (12000 : ℝ) ≤ K := by clear * - K hK hC20; linarith only [hK, hC20]
  clear hK
  have hhlog : K * lg ≤ (h : ℝ) := by clear * - K lg h hhdef; rw [hhdef]; exact Nat.le_ceil _
  clear hhdef
  have hθle : (3 : ℝ) ^ m * ((3 : ℝ) ^ (m + h))⁻¹ ≤ (m : ℝ) ^ (-(12000 : ℝ)) := by
    clear * - m hm64 hlgdef h hmK hhlog
    exact srootNSD_theta_le (by linarith only [hm64]) hmK (by rw [← hlgdef]; exact hhlog)
  clear hhlog hmK
  have hθ0 : 0 ≤ (3 : ℝ) ^ m * ((3 : ℝ) ^ (m + h))⁻¹ := by
    clear * - m h
    exact mul_nonneg (pow_nonneg (by norm_num) _) (inv_nonneg.2 (pow_nonneg (by norm_num) _))
  have hθ1 : (3 : ℝ) ^ m * ((3 : ℝ) ^ (m + h))⁻¹ ≤ 1 := by
    clear * - m h
    rw [pow_add]
    have : (0 : ℝ) < 3 ^ m := pow_pos (by norm_num) _
    have h3 : (1 : ℝ) ≤ 3 ^ h := one_le_pow₀ (by norm_num)
    rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ this.ne', one_mul]
    exact inv_le_one_of_one_le₀ h3
  have htc : srootN3_tailConst d ≤ ctc := by clear * - d ctc hctcdef; rw [hctcdef]; exact le_max_left _ _
  clear hctcdef
  have hctc0 : 0 ≤ ctc := by clear * - ctc hctc1; linarith only [hctc1]
  have hcE0 : 0 < cE := by clear * - hcE cE; linarith only [hcE]
  have hmmR1 : (1 : ℝ) ≤ ((m + h : ℕ) : ℝ) := by
    clear * - m hm1 h hh0
    have : (1 : ℝ) ≤ m := hm1
    push_cast; linarith only [this, hh0]
  have hmmR3 : ((m + h : ℕ) : ℝ) ≤ 3 * m := by
    clear * - m hh2 hm1 h hKlg
    push_cast; linarith only [hh2, hKlg, hm1]
  have hcaseB : ∀ (l : ℕ) (R : Homogenization.TriadicCube d),
      ∃ X1 X2 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
        l < Nl → R ∈ S l →
          Measurable X1 ∧ Measurable X2 ∧
          IsBigO P.toMeasure (gammaSigma (1 / 3)) X1 (e1c * (m : ℝ) ^ (-(11000 : ℝ))) ∧
          IsBigO P.toMeasure (gammaSigma (1 / 3)) X2
            ((16 * cE ^ 2 * ctc) * (m : ℝ) ^ (-(5000 : ℝ))) ∧
          ∀ᵐ ω ∂P.toMeasure, ∀ L, m + h < L →
            Φ ω L l R ≤ Φ ω (m + h) l R + X1 ω + q ω (m + h) * X2 ω := by
    clear * - d hcE cE hcEdef ctc e1c he1c nu hnu hnu1 P hPrefix hJ2 hJ3 hJ4 m n k hk hni hσpos hσup hni1 σ hσdef h hu0 hu Nl S Φ hΦ q hqdef hSdesc hθle hθ0 hθ1 htc hctc0 hmmR1 hmmR3
    intro l R
    by_cases H : l < Nl ∧ R ∈ S l
    · obtain ⟨hl, hR⟩ := H
      have hRn : Homogenization.cubeSet R ⊆
          Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)) :=
        Homogenization.cubeSet_subset_of_mem_descendantsAtScale
          (sub_le_self _ (Int.natCast_nonneg l)) (hSdesc l R hR)
      obtain ⟨X1, X2, hX1m, hX2m, hX1O, hX2O, hae⟩ := srootNS_caseB_pathwise d hPrefix hJ2 hJ3
        hJ4 hnu (m := m) (mm := m + h) (Nat.le_succ_of_le (Nat.le_add_right m h)) m n k hk R hRn
      refine ⟨X1, X2, fun _ _ => ⟨hX1m, hX2m, hX1O.mono_scale ?_, hX2O.mono_scale ?_, ?_⟩⟩
      · rw [← hσdef]
        have := srootNSD_tail_amp1 (cE := cE) (ctc := ctc) (tc := srootN3_tailConst d)
          (ni := nu⁻¹) (u := σ⁻¹) (σ := σ) (nu := nu) (m := (m : ℝ)) (mmR := ((m + h : ℕ) : ℝ))
          hcE hctc0 htc hni1 hni hnu hnu1 hu0 hu hσpos.le hσup hmmR1 hmmR3
          hθ0 hθ1 hθle
        rw [he1c]
        refine le_trans (le_of_eq ?_) this
        simp only [SuperdiffusionCLT.Section2.Annealed.envelopeUpperScalar,
          SuperdiffusionCLT.Section2.Annealed.envelopeLowerScalar, hcEdef]
      · rw [← hσdef]
        have := srootNSD_tail_amp2 (cE := cE) (ctc := ctc) (tc := srootN3_tailConst d)
          (ni := nu⁻¹) (u := σ⁻¹) (m := (m : ℝ)) hcE hctc0 htc hni1 hni hu0 hu hθ0 hθ1 hθle
        refine le_trans (le_of_eq ?_) this
        simp only [SuperdiffusionCLT.Section2.Annealed.envelopeLowerScalar, hcEdef]
      · filter_upwards [hae] with ω hω L hL
        rw [hΦ, hΦ, hqdef]
        rw [hσdef]
        exact hω L hL
    · exact ⟨0, 0, fun h1 h2 => absurd ⟨h1, h2⟩ H⟩
  clear hmmR3 hmmR1 htc hθ1 hθ0 hθle hqdef hni1 hσup hni hk hJ4 hJ3 hJ2 hPrefix hnu1 hnu hcEdef
  have hSf : S = fun l : ℕ => Homogenization.descendantsAtScale
      (Homogenization.originCube d (n : ℤ)) ((n : ℤ) - (l : ℤ)) := by
    clear * - d n S hSdef
    exact funext hSdef
  have hlb : ∀ l, l < Nl → l ≤ hbar := by
    clear * - hbar Nl hNldef
    exact fun l hl => by rw [hNldef] at hl; exact Nat.lt_succ_iff.1 hl
  have hacast : (m : ℝ) - C1 * s⁻¹ * (h : ℝ) ≤ (a : ℝ) := by clear * - C1 s m h a ha; rw [ha]; exact Nat.le_ceil _
  have hcnt1 : ((m + h + 1 - a : ℕ) : ℝ) ≤ m := by
    clear * - m h hCount a hab hacast
    rw [Nat.cast_sub (hab.trans (Nat.le_succ _))]
    push_cast
    linarith only [hacast, hCount]
  clear hacast hCount
  have hcnt0 : (1 : ℝ) ≤ ((m + h + 1 - a : ℕ) : ℝ) := by
    clear * - m h a hab
    have : 1 ≤ m + h + 1 - a := Nat.sub_pos_of_lt (Nat.lt_succ_of_le hab)
    exact_mod_cast this
  have hcnt2 : ((m + h + 1 + 1 - a : ℕ) : ℝ) ≤ 2 * m := by
    clear * - m hm1 h a hab hcnt1
    have e : m + h + 1 + 1 - a = (m + h + 1 - a) + 1 := Nat.sub_add_comm (hab.trans (Nat.le_succ _))
    rw [e]; push_cast; linarith only [hcnt1, hm1]
  have hlogN : ∀ l < Nl, Real.log (2 * (((m + h + 1 - a : ℕ) : ℝ) * (((S l).card : ℕ) : ℝ))) ≤
      2 * lg + 2 * (d : ℝ) * (l : ℝ) := by
    clear * - d hdn m lg hlgdef h hlg1 a Nl S hSdef hln hlb hcnt1 hcnt0
    intro l hl
    rw [hSdef l, srootN_descendantsAtScale_card (hln l (hlb l hl))]
    push_cast
    have hl1 : 1 ≤ Real.log (m : ℝ) := by rw [← hlgdef]; exact hlg1
    have := srootNSD_logN_l (l := l) hcnt0 hcnt1 hl1 hdn rfl
    rw [← hlgdef] at this
    exact this
  clear hcnt0 hcnt1 hlb hSdef hlgdef
  have hbarn : hbar ≤ n := by
    clear * - n hbar hln
    exact hln hbar le_rfl
  clear hln
  have hcard := srootNSD_card_T (d := d) n a (m + h) Nl (2 * (m : ℝ)) (by rw [hNldef]; exact Nat.succ_le_succ hbarn) hcnt2
    (by linarith only [hm1])
  clear hbarn hcnt2
  have hNcap1 : (((Finset.Icc a (m + h + 1)) ×ˢ ((Finset.range Nl).sigma S)).card : ℝ) ≤
      (2 * (m : ℝ)) * ((Nl : ℝ) * ((3 : ℝ) ^ d) ^ Nl) := by
    clear * - d m h a Nl S hSf hcard
    rw [hSf]; exact hcard.1
  have hNcap2 : ((((Finset.range Nl).sigma S).card : ℕ) : ℝ) ≤
      (2 * (m : ℝ)) * ((Nl : ℝ) * ((3 : ℝ) ^ d) ^ Nl) := by
    clear * - d m Nl S hSf hcard
    rw [hSf]; exact hcard.2
  clear hcard hSf
  have hσi : σ ^ (-(1 : ℝ)) = σ⁻¹ := by
    clear * - σ
    exact Real.rpow_neg_one σ
  have hSg : σ ^ (-(2 : ℝ)) = (σ⁻¹) ^ 2 := by
    clear * - hσpos σ
    rw [Real.rpow_neg hσpos.le, Real.rpow_two, inv_pow]
  have hlg20 : 0 ≤ Real.log (2 * (h : ℝ)) := by
    clear * - h1h h
    have : (1 : ℝ) ≤ h := h1h
    exact Real.log_nonneg (by linarith only [this])
  clear h1h
  have hmC1 : C1 ≤ (m : ℝ) := hC1m
  obtain ⟨hlog3, hLg0, hcapc⟩ := srootNSD7_cap hNldef hhbar2 hC0 hs0 hK1 hlg1 hPm hm1 hm64 hdn
    hc3 hcE hg1 hAsk1 hlgm hKlg hlog2h hlg20 hu0 hu hU0 hCp1 hcE0 hctc0 hQ2 hmC1 hU0C hc3C hQ2C
    hU0n hc3n hQ2n hCpp hmpos
  clear hhbar2 hC0 hm64 hc3 hKlg hu hlgm hPm hlog2h hcE hU0 hQ2 hctc0 hQ2C hU0C hQ2n hc3n hU0n hC1m
  have hCp0 : 0 ≤ Cp := by clear * - Cp hCp1; linarith only [hCp1]
  clear hCp1
  have hAsk0 : 0 ≤ Ask := by clear * - Ask hAsk1; linarith only [hAsk1]
  clear hAsk1
  have hSgpos : 0 < σ ^ (-(2 : ℝ)) := by
    clear * - hσpos σ
    exact Real.rpow_pos_of_pos hσpos _
  have hKp0 : 0 ≤ 4 * C1 * s⁻¹ * K := by clear * - C1 s K h4C1; linarith only [h4C1]
  clear h4C1
  have hκ : 16384 * A0 ≤ (16384 * A0) ^ 2 := by
    clear * - A0 hA01
    exact le_self_pow₀ (by linarith only [hA01]) two_ne_zero
  have hH0n : 0 ≤ Ask * (K * lg * Real.log (2 * (h : ℝ))) := by
    clear * - Ask K lg h hAskp hKpos hlgpos hlg20
    exact mul_nonneg hAskp.le (mul_nonneg (mul_nonneg hKpos.le hlgpos.le) hlg20)
  clear hlg20
  have hmpow : ∀ r : ℝ, 0 < (m : ℝ) ^ r := by
    clear * - m hmpos
    exact fun r => Real.rpow_pos_of_pos hmpos r
  have hctc0' : 0 < ctc := by clear * - ctc hctc1; linarith only [hctc1]
  clear hctc1
  have he1pos : 0 < e1c := by
    clear * - e1c he1c hcE0 hctc0'
    rw [he1c]; exact mul_pos (mul_pos (by norm_num) (pow_pos hcE0 2)) hctc0'
  clear he1c
  have hσi0 : 0 ≤ σ ^ (-(1 : ℝ)) := by
    clear * - hσpos σ
    exact Real.rpow_nonneg hσpos.le _
  clear hσpos
  have hKppos : 0 < 4 * C1 * s⁻¹ * K := by
    clear * - C1 s K hKpos hsi hC1pos
    exact mul_pos (mul_pos (mul_pos (by norm_num) hC1pos) hsi) hKpos
  have hA0pos : 0 < A0 := by clear * - A0 hA01; linarith only [hA01]
  have hκpos : 0 < 16384 * A0 := by clear * - A0 hA01; linarith only [hA01]
  clear hA01
  have hGae' : ∀ᵐ ω ∂P.toMeasure, ∀ L l, ∀ R ∈ S l, Φ ω L l R ≤ G ω := by
    clear * - P hσdef G hGae S Φ hΦ hSdesc
    filter_upwards [hGae] with ω hω L l R hR
    rw [hΦ, hσdef]
    exact hω L l R (hSdesc l R hR)
  clear hSdesc hΦ hGae hσdef
  have hAuE : gammaTriangleConst 1 * ((1 + (σ ^ (-(1 : ℝ)) + 1) *
      (Ask * (K * lg * Real.log (2 * (h : ℝ))))) + (σ ^ (-(1 : ℝ)) + 1) * (Ask * (s⁻¹ * K * lg))) ≤
      g1 * ((1 + (σ⁻¹ + 1) * (Ask * (K * lg * Real.log (2 * (h : ℝ))))) +
        (σ⁻¹ + 1) * (Ask * (s⁻¹ * K * lg))) := by
    clear * - Ask g1 hg1def s K σ lg h hσi
    rw [hσi, hg1def]
  clear hσi
  have hg1le : ∀ x y : ℝ, gammaTriangleConst 1 * (x + gammaTriangleConst 1 * y) ≤ g1 * (x + g1 * y) := by
    clear * - g1 hg1def
    exact fun x y => by rw [hg1def]
  have hg3le : ∀ x : ℝ, gammaTriangleConst (1 / 3) * x ≤ g3 * x := by
    clear * - g3 hg3def
    exact fun x => by rw [hg3def]
  clear hg3def
  obtain ⟨Y1a, Y2, hY1am, hY1aO, hY2m, hY2O, hae⟩ := srootNSD_assemble (μ := P.toMeasure) S hSne
    Φ Mx q W G (a := a) (b := m + h) (Nl := Nl) hab hNl (s := s) (Cp := Cp)
    (Sg := σ ^ (-(2 : ℝ))) (σi := σ ^ (-(1 : ℝ)))
    (H0 := Ask * (K * lg * Real.log (2 * (h : ℝ)))) (h := (h : ℝ)) (Kp := 4 * C1 * s⁻¹ * K)
    (lg := lg) (L2 := 4 * lg ^ 2) (D := (d : ℝ)) (AW := Ask * (s⁻¹ * K * lg))
    (βA := Cp * ((m : ℝ) / 2) ^ (-(5000 : ℝ)))
    (βB := (16 * cE ^ 2 * ctc) * (m : ℝ) ^ (-(5000 : ℝ)))
    (E1 := e1c * (m : ℝ) ^ (-(11000 : ℝ)))
    (Ncap := (2 * (m : ℝ)) * ((Nl : ℝ) * ((3 : ℝ) ^ d) ^ Nl)) (D0 := A0) (κ := 16384 * A0)
    (m := (m : ℝ))
    (Au := g1 * ((1 + (σ⁻¹ + 1) * (Ask * (K * lg * Real.log (2 * (h : ℝ))))) +
      (σ⁻¹ + 1) * (Ask * (s⁻¹ * K * lg))))
    (AY1 := g1 * (Cp * σ ^ (-(2 : ℝ)) * (Ask * (s⁻¹ * K * lg)) + g1 *
      ∑ l ∈ Finset.range Nl, Homogenization.geometricWeight s 2 l *
        (Cp * σ ^ (-(2 : ℝ)) * (2 * (h : ℝ) + (l : ℝ) + 2 * (4 * C1 * s⁻¹ * K) * lg))))
    (AY2 := g3 * ((3 * Real.log (max 2 ((2 * (m : ℝ)) * ((Nl : ℝ) * ((3 : ℝ) ^ d) ^ Nl)))) ^
      ((1 / 3 : ℝ)⁻¹) * (e1c * (m : ℝ) ^ (-(11000 : ℝ))) + 16384 * A0 * (m : ℝ) ^ (-(2000 : ℝ))))
    hs0 hCpp hSgpos hσi0 hH0n hh0 hKppos
    hlgpos (mul_nonneg (by norm_num) (sq_nonneg lg)) hdn
    (mul_pos hAskp (mul_pos (mul_pos hsi hKpos) hlgpos))
    (mul_pos hCpp (Real.rpow_pos_of_pos (half_pos hmpos) _))
    (mul_pos (mul_pos (mul_pos (by norm_num) (pow_pos hcE0 2)) hctc0') (hmpow _))
    (mul_pos he1pos (hmpow _))
    hA0pos hκpos hm1 hMx hcaseA hcaseB hWm hW0 hWO
    (fun ω L h1 h2 => ⟨hq0 ω L, hq1 ω L h1 h2⟩) hGm hGO
    hGae' hlogN hNcap1 hNcap2 hAuE hcapc hκ (hg1le _ _) (hg3le _)
  clear hg3le hg1le hAuE hGae' hκpos hA0pos hKppos hσi0 he1pos hctc0' hmpow hκ hcapc hNcap2 hNcap1 hlogN hcaseB hcE0 hcaseA hq1 hq0 hMx hSne hNl hab hmpos hGO hGm hWO hW0 hWm
  have hC1one : 1 ≤ C1 := by clear * - C1 hC20; linarith only [hC20]
  clear hC20
  obtain ⟨hc0pos, hAY1pos, hY1fin⟩ := srootNSD7_tailY1 (Nl := Nl) (hr := (h : ℝ)) hCpp hAskp
    hKpos hK1 hlgpos hlg1 hs0 hs1 hC1one hSgpos hSg hh0 hh2 hg1 (hA1.symm.trans_le hA1C)
  clear hA1C hA1 hg1
  have hY2fin := srootNSD_Y2_amp (g3 := g3) (κ := 16384 * A0) (E1 := e1c * (m : ℝ) ^ (-(11000 : ℝ)))
    (e1c := e1c) (c3 := c3) (A := Abig) (m := (m : ℝ))
    (Lg := 3 * Real.log (max 2 ((2 * (m : ℝ)) * ((Nl : ℝ) * ((3 : ℝ) ^ d) ^ Nl))))
    hm1 hg3.le hLg0 hlog3 rfl (hc3C.trans hmC1) (he1C.trans hmC1) he1n hA3C
  clear hmC1 hLg0 hlog3 hm1 hA3C he1C hc3C he1n hg3
  refine ⟨fun ω => Cp * (6 + 62 * (d : ℝ)) * C1 * (s⁻¹) ^ 2 * K * σ ^ (-(2 : ℝ)) * lg +
    1 * Y1a ω, Y2, measurable_const.add (measurable_const.mul hY1am),
    (srootNSD_isBigO_affine hc0pos one_pos hAY1pos hY1am hY1aO).mono_scale (by rw [← hg1def]; exact hY1fin), hY2m,
    hY2O.mono_scale hY2fin, ?_⟩
  clear hY2fin hY1fin hAY1pos hc0pos hY2O hY2m hY1aO hY1am hg1def
  filter_upwards [hae] with ω hω L hL
  clear hae
  have haL : a ≤ L := by clear * - a ha hL; rw [ha]; exact Nat.ceil_le.2 hL
  clear hL ha
  have h1 := hω L haL
  clear haL hω
  have hsum_eq : ∑ l ∈ Finset.range (hbar + 1), srootE_term s (srootE_field nu ω L m n k)
      (σ • (1 : Homogenization.Mat d)) n l =
      ∑ l ∈ Finset.range Nl, Homogenization.geometricWeight s 2 l * Mx ω L l := by
    clear * - d nu s m n k σ hbar Nl hNldef Mx hMxdef
    rw [hNldef]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [srootNSD_term_eq, hMxdef]
  clear hMxdef hNldef
  have hT := srootNSD7_tailSum (Nl := Nl) (hr := (h : ℝ)) hCp0 hAsk0 hKpos hlgpos hSgpos hSg hs0
    hs1 hK1 hC1one hlg1 hdn hlog2h2 hH0n hh0 hh2 hKp0 hu0 hA2C
  rw [hsum_eq]
  linarith only [h1, hT]
end

end SuperdiffusionCLT.Section4.MinimalScales
