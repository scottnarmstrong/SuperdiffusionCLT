/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.NewMixing.AssemblyLocErr
public import SuperdiffusionCLT.Section4.NewMixing.T0Refinement

/-!
# `T_0`-refinement, branch `m ≤ L+h`, uniform in `e, sigma, h0`, amplitude `m^{-6000}`

The `T_0` refinement in branch `m ≤ L+h`, with the amplitude of the
witness `X0` sharpened from `Cenv * m^{-3000}` to `Cenv * m^{-6000}`. The proof is the
same: the bracket is bounded by `m^5 * m^{-12000}`, which is below `m^{-6000}`. The sharper
amplitude is what lets the quadratic factor in front of `X0` (polynomial in `m`) be folded into
the printed `m^{-3000}` envelope downstream.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.NewMixing

open Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Assumptions

noncomputable section

/-- **`l.new.mixing.parameterized#T0-refinement`, branch `m ≤ L+h`, uniform in
`e, sigma, h0`.** Same conclusion as the branch `m ≤ L+h` refinement built from
`newMixParam_bracket_branchA`,
except the witness `X0` no longer depends on `e, sigma, h0`: it is chosen
once, at the plain amplitude `Cenv * m^{-6000}`, and the bound picks up the
explicit quadratic factor `⟪G_{-h0}P_e^σ, G_{-h0}P_e^σ⟫`. -/
theorem newMixAsm_t0Strong_branchA (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ Cthr Cenv : ℝ, 1 ≤ Cthr ∧ 1 ≤ Cenv ∧
      ∀ (M K alpha cStar nu nondeg : ℝ),
        1 ≤ M → 1 ≤ K → 0 ≤ alpha → alpha < 1 → 0 < cStar → cStar ≤ 2 →
        ∀ (hnu : 0 < nu), nu ≤ 1 →
        0 ≤ nondeg →
        ∀ (r L m ell n : ℕ) (P : MeasureTheory.ProbabilityMeasure (ShellSeq d)),
          ShellLawPrefix d P → ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P →
          ShellLawJ4 d P →
          SuperdiffusionCLT.Frozen.Section4.lNaught Cthr (Cthr * (M + K)) alpha cStar nu
              nondeg ≤ (L : ℝ) →
          SuperdiffusionCLT.Frozen.Section4.lNaught Cthr (Cthr * (M + K)) alpha cStar nu
              nondeg ≤ (m : ℝ) →
          (L : ℝ) - M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (m : ℝ) →
          |(L : ℝ) - (r : ℝ)| ≤ K * Real.log (L : ℝ) →
          m ≤ L + newMixParam_h K (Real.log (L : ℝ)) →
          ell = m - newMixParam_h K (Real.log (L : ℝ)) →
          n = ell - newMixParam_h K (Real.log (L : ℝ)) →
            ∃ X0 : ShellSeq d → ℝ, Measurable X0 ∧
              Homogenization.IndependentSums.IsBigO P.toMeasure
                  (Homogenization.IndependentSums.gammaSigma ((1 : ℝ) / 3)) X0
                  (Cenv * (m : ℝ) ^ (-(6000 : ℝ))) ∧
              ∀ (e : Vec d), vecNormSq e ≤ 1 →
                ∀ (sigma : ℝ), sigma ^ 2 = 1 →
                  ∀ (h0 : Mat d) (hh0 : matTranspose h0 = -h0)
                    (omega : ShellSeq d),
                    blockVecDot
                        ((sigma * Real.sqrt (sigmaBarInfinite nu r P)⁻¹) • e,
                          Real.sqrt (sigmaBarInfinite nu r P) • e)
                        (blockMatVecMul
                          (Homogenization.Book.Ch02.coarseBlockMatrix
                            (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d (m : ℤ)))
                            (newMixParam_aLplusH0 nu hnu omega L m h0 hh0))
                          ((sigma * Real.sqrt (sigmaBarInfinite nu r P)⁻¹) • e,
                            Real.sqrt (sigmaBarInfinite nu r P) • e)) ≤
                      Homogenization.blockVecDot
                          (blockMatVecMul (blockG (-h0))
                            ((sigma * Real.sqrt (sigmaBarInfinite nu r P)⁻¹) • e,
                              Real.sqrt (sigmaBarInfinite nu r P) • e))
                          (blockMatVecMul (blockG (-h0))
                            ((sigma * Real.sqrt (sigmaBarInfinite nu r P)⁻¹) • e,
                              Real.sqrt (sigmaBarInfinite nu r P) • e)) * X0 omega +
                        Homogenization.descendantsAverage (Homogenization.originCube d (m : ℤ)) (m - n)
                          (fun R => blockVecDot
                            (blockMatVecMul
                              (Homogenization.Book.Ch02.blockG
                                (-(Homogenization.volumeAverageMat (Homogenization.cubeSet R)
                                      (fun y => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                        omega ell L y) + h0)))
                              ((sigma * Real.sqrt (sigmaBarInfinite nu r P)⁻¹) • e,
                                Real.sqrt (sigmaBarInfinite nu r P) • e))
                            (blockMatVecMul
                              (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu ell P
                                (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ))))
                              (blockMatVecMul
                                (Homogenization.Book.Ch02.blockG
                                  (-(Homogenization.volumeAverageMat (Homogenization.cubeSet R)
                                        (fun y => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                          omega ell L y) + h0)))
                                ((sigma * Real.sqrt (sigmaBarInfinite nu r P)⁻¹) • e,
                                  Real.sqrt (sigmaBarInfinite nu r P) • e)))) := by
  obtain ⟨CA, hCA1, hCA100000, hCAbody⟩ := newMixParam_threeNegH_le_mNeg12000
  obtain ⟨C0, hC0, hslack⟩ := newMixParam_absorbSlack
  obtain ⟨CLE, hLE⟩ := newMixAsm_localizationError_uniform d
  refine ⟨max CA C0,
    max 1 (16 * (4 / ((max CA C0) ^ 2 * (Real.log 2) ^ (12 : ℝ))) * |CLE|),
    le_trans hCA1 (le_max_left _ _), le_max_left _ _, ?_⟩
  intro M K alpha cStar nu nondeg hM hK hα0 hα1 hcStar hcStar2 hnu hnu1 hnondeg
    r L m ell n P hPrefix hJ1V2 hJ2 hJ3 hJ4 hL hm hLm hLr hcaseA hellDef hnDef
  set C := max CA C0 with hCdef
  have hCA_le_C : CA ≤ C := le_max_left _ _
  have hC0_le_C : C0 ≤ C := le_max_right _ _
  have hC100000 : (100000 : ℝ) ≤ C := le_trans hCA100000 hCA_le_C
  have hC1 : (1 : ℝ) ≤ C := le_trans hCA1 hCA_le_C
  have hMKnn : (0 : ℝ) ≤ M + K := by linarith only [hM, hK]
  have hCAMK_le : CA * (M + K) ≤ C * (M + K) := mul_le_mul_of_nonneg_right hCA_le_C hMKnn
  have hCAnn : (0 : ℝ) ≤ CA := le_trans zero_le_one hCA1
  have hCAMKnn : (0 : ℝ) ≤ CA * (M + K) := mul_nonneg hCAnn hMKnn
  have hLA : SuperdiffusionCLT.Frozen.Section4.lNaught CA (CA * (M + K)) alpha cStar nu
      nondeg ≤ (L : ℝ) := by
    have hmono := SuperdiffusionCLT.Section4.LNaught.lNaught_mono_both
      (C := CA) (C' := C) (M := CA * (M + K)) (M' := C * (M + K)) (alpha := alpha)
      (cStar := cStar) (nu := nu) (K := nondeg) hCAnn hCA_le_C hCAMKnn hCAMK_le hnondeg
      hcStar hnu hα1
    linarith only [hmono, hL]
  have hmA : SuperdiffusionCLT.Frozen.Section4.lNaught CA (CA * (M + K)) alpha cStar nu
      nondeg ≤ (m : ℝ) := by
    have hmono := SuperdiffusionCLT.Section4.LNaught.lNaught_mono_both
      (C := CA) (C' := C) (M := CA * (M + K)) (M' := C * (M + K)) (alpha := alpha)
      (cStar := cStar) (nu := nu) (K := nondeg) hCAnn hCA_le_C hCAMKnn hCAMK_le hnondeg
      hcStar hnu hα1
    linarith only [hmono, hm]
  have hdecayA := hCAbody M K alpha cStar nu nondeg hM hK hα0 hα1 hcStar hcStar2 hnu hnu1
    hnondeg L m hLA hmA hcaseA
  set h := newMixParam_h K (Real.log (L : ℝ)) with hhdef
  have hL_le_2m := (newMixParam_t0_L_le_2m_r_le_2L (C0 := C0) (C := C) hC0 hslack hC0_le_C hC1
    hM hK hα0 hα1 hcStar hcStar2 hnu hnu1 hnondeg hL hLm hLr).1
  have hr_le_2L := (newMixParam_t0_L_le_2m_r_le_2L (C0 := C0) (C := C) hC0 hslack hC0_le_C hC1
    hM hK hα0 hα1 hcStar hcStar2 hnu hnu1 hnondeg hL hLm hLr).2
  have hh_le_L4 := newMixParam_t0_h_le_L_div_4 (C0 := C0) (C := C) hC0 hslack hC0_le_C hC100000
    hM hK hα0 hα1 hcStar hcStar2 hnu hnu1 hnondeg hL
  have hh_nat_le : 4 * h ≤ L := by
    have h4 : (4 : ℝ) * (h : ℝ) ≤ (L : ℝ) := by linarith only [hh_le_L4]
    exact_mod_cast h4
  have hL_nat_le_2m : L ≤ 2 * m := by exact_mod_cast hL_le_2m
  have hr_nat_le_2L : r ≤ 2 * L := by exact_mod_cast hr_le_2L
  obtain ⟨hL8, _, _⟩ := hslack C hC0_le_C M K alpha cStar nu nondeg hM hK hα0 hα1 hcStar hcStar2
    hnu hnu1 hnondeg L hL
  have hlogLpos : (0 : ℝ) < Real.log (L : ℝ) := Real.log_pos (by linarith only [hL8])
  have hh_pos : 1 ≤ h := by
    apply newMixParam_h_pos
    unfold newMixParam_K0
    have hKnn : (0 : ℝ) ≤ K := by linarith only [hK]
    nlinarith only [hK, hlogLpos]
  have h2h_le_m : 2 * h ≤ m := by omega
  subst hellDef
  subst hnDef
  have hn_ell : m - h - h ≤ m - h := by omega
  have hell_m : m - h ≤ m := by omega
  have hell_L : m - h ≤ L := by omega
  have hell1 : 1 ≤ m - h := by omega
  have hL1 : 1 ≤ L := by omega
  have hmn1 : 1 ≤ m - (m - h - h) := by omega
  obtain ⟨X0, hX0meas, hX0BigO, hX0bound⟩ :=
    hLE hnu hnu1 hPrefix hJ1V2 hJ2 hJ3 hJ4
      hn_ell hell_m hell_L hell1 hL1 hmn1
  have hell_n : (m - h) - (m - h - h) = h := by omega
  have hm_ell : m - (m - h) = h := by omega
  have hbracket := newMixParam_bracket_branchA d hd (L := L) hell_n hm_ell hdecayA
  set Bp := (1 + (↑(m - h) : ℝ) * (↑(m - (m - h - h)) : ℝ)) * (L : ℝ) ^ 2 with hBpdef
  have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
    have : (1 : ℕ) ≤ m := by omega
    exact_mod_cast this
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith only [hm1]
  have hLnn : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have hmh_le_m : ((m - h : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.sub_le m h
  have hmn_le_m : ((m - (m - h - h) : ℕ) : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast Nat.sub_le m (m - h - h)
  have hmh_nn : (0 : ℝ) ≤ ((m - h : ℕ) : ℝ) := Nat.cast_nonneg _
  have hmn_nn : (0 : ℝ) ≤ ((m - (m - h - h) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hBp_le : Bp ≤ 8 * (m : ℝ) ^ 4 := by
    rw [hBpdef]
    have hprod_le : (↑(m - h) : ℝ) * (↑(m - (m - h - h)) : ℝ) ≤ (m : ℝ) * (m : ℝ) :=
      mul_le_mul hmh_le_m hmn_le_m hmn_nn hmnn
    have h1prod_le : (1 : ℝ) + (↑(m - h) : ℝ) * (↑(m - (m - h - h)) : ℝ) ≤ 2 * (m : ℝ) ^ 2 := by
      nlinarith only [hprod_le, hm1]
    have hLsq_le : (L : ℝ) ^ 2 ≤ 4 * (m : ℝ) ^ 2 := by nlinarith only [hL_le_2m, hLnn]
    have h1prod_nn : (0 : ℝ) ≤ 1 + (↑(m - h) : ℝ) * (↑(m - (m - h - h)) : ℝ) := by
      have := mul_nonneg hmh_nn hmn_nn
      linarith only [this]
    calc (1 + (↑(m - h) : ℝ) * (↑(m - (m - h - h)) : ℝ)) * (L : ℝ) ^ 2
        ≤ (2 * (m : ℝ) ^ 2) * (L : ℝ) ^ 2 := mul_le_mul_of_nonneg_right h1prod_le (by positivity)
      _ ≤ (2 * (m : ℝ) ^ 2) * (4 * (m : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hLsq_le (by positivity)
      _ = 8 * (m : ℝ) ^ 4 := by ring
  have hBpnn : (0 : ℝ) ≤ Bp := by rw [hBpdef]; positivity
  have hm12000nn : (0 : ℝ) ≤ (m : ℝ) ^ (-(12000 : ℝ)) := Real.rpow_nonneg hmnn _
  have hbracket_nn : (0 : ℝ) ≤
      (if m - h < L then (L : ℝ) ^ 2 * (3 : ℝ) ^ (-((m - h - (m - h - h) : ℕ) : ℝ)) else 0) +
        (↑(m - h) : ℝ) * (L : ℝ) ^ 2 * (↑(m - (m - h - h)) : ℝ) *
          (3 : ℝ) ^ (-((d : ℝ) / 2 * (↑(m - (m - h)) : ℝ))) := by
    have h1 : (0 : ℝ) ≤
        (if m - h < L then (L : ℝ) ^ 2 * (3 : ℝ) ^ (-((m - h - (m - h - h) : ℕ) : ℝ)) else 0) := by
      split_ifs with hc <;> positivity
    have h2 : (0 : ℝ) ≤ (↑(m - h) : ℝ) * (L : ℝ) ^ 2 * (↑(m - (m - h - h)) : ℝ) *
        (3 : ℝ) ^ (-((d : ℝ) / 2 * (↑(m - (m - h)) : ℝ))) := by positivity
    linarith only [h1, h2]
  -- `CLE * nu^{-4} * Kappa ≤ Cenv * m^{-6000}`, a plain three-factor amplitude
  -- bound with no `V`-folding needed.
  have h2CleMK : 2 * C ≤ C * (M + K) := by nlinarith only [hC1, hM, hK]
  have hnu4 : nu ^ (-(4 : ℝ)) ≤ (4 / (C ^ 2 * (Real.log 2) ^ (12 : ℝ))) * (L : ℝ) :=
    newMixParam_nu4_le_linear_L (C := C) (M := C * (M + K)) (alpha := alpha) (cStar := cStar)
      (nu := nu) (K := nondeg) hC100000 h2CleMK hnondeg hcStar hcStar2 hnu hnu1 hα0 hα1 hL
  set C3 := 4 / (C ^ 2 * (Real.log 2) ^ (12 : ℝ)) with hC3def
  have hC3nn : (0 : ℝ) ≤ C3 := by rw [hC3def]; positivity
  have hnu4nn : (0 : ℝ) ≤ nu ^ (-(4 : ℝ)) := Real.rpow_nonneg hnu.le _
  set Cenv := max 1 (16 * C3 * |CLE|) with hCenvdef
  have hCenv1 : (1 : ℝ) ≤ Cenv := le_max_left _ _
  refine ⟨X0, hX0meas, ?_, ?_⟩
  · refine hX0BigO.mono_scale ?_
    rcases le_or_gt 0 CLE with hCLEnn | hCLEneg
    · have hKappaBp :
          (if m - h < L then (L : ℝ) ^ 2 * (3 : ℝ) ^ (-((m - h - (m - h - h) : ℕ) : ℝ)) else 0) +
              (↑(m - h) : ℝ) * (L : ℝ) ^ 2 * (↑(m - (m - h - h)) : ℝ) *
                (3 : ℝ) ^ (-((d : ℝ) / 2 * (↑(m - (m - h)) : ℝ))) ≤
            Bp * (m : ℝ) ^ (-(12000 : ℝ)) := by
        rw [hBpdef]; linarith only [hbracket]
      have hstep1 : CLE * nu ^ (-(4 : ℝ)) *
          ((if m - h < L then (L : ℝ) ^ 2 * (3 : ℝ) ^ (-((m - h - (m - h - h) : ℕ) : ℝ)) else 0) +
            (↑(m - h) : ℝ) * (L : ℝ) ^ 2 * (↑(m - (m - h - h)) : ℝ) *
              (3 : ℝ) ^ (-((d : ℝ) / 2 * (↑(m - (m - h)) : ℝ)))) ≤
          CLE * (C3 * (L : ℝ)) * (Bp * (m : ℝ) ^ (-(12000 : ℝ))) := by
        have ha : CLE * nu ^ (-(4 : ℝ)) ≤ CLE * (C3 * (L : ℝ)) :=
          mul_le_mul_of_nonneg_left hnu4 hCLEnn
        have hb : CLE * nu ^ (-(4 : ℝ)) *
            ((if m - h < L then (L : ℝ) ^ 2 * (3 : ℝ) ^ (-((m - h - (m - h - h) : ℕ) : ℝ)) else 0) +
              (↑(m - h) : ℝ) * (L : ℝ) ^ 2 * (↑(m - (m - h - h)) : ℝ) *
                (3 : ℝ) ^ (-((d : ℝ) / 2 * (↑(m - (m - h)) : ℝ)))) ≤
            CLE * (C3 * (L : ℝ)) *
              ((if m - h < L then (L : ℝ) ^ 2 * (3 : ℝ) ^ (-((m - h - (m - h - h) : ℕ) : ℝ)) else 0) +
                (↑(m - h) : ℝ) * (L : ℝ) ^ 2 * (↑(m - (m - h - h)) : ℝ) *
                  (3 : ℝ) ^ (-((d : ℝ) / 2 * (↑(m - (m - h)) : ℝ)))) :=
          mul_le_mul_of_nonneg_right ha hbracket_nn
        refine le_trans hb ?_
        exact mul_le_mul_of_nonneg_left hKappaBp (by positivity)
      have hstep2 : CLE * (C3 * (L : ℝ)) * (Bp * (m : ℝ) ^ (-(12000 : ℝ))) ≤
          16 * C3 * CLE * ((m : ℝ) ^ (5 : ℕ) * (m : ℝ) ^ (-(12000 : ℝ))) := by
        have hLBp_le : (L : ℝ) * Bp ≤ (2 * (m : ℝ)) * (8 * (m : ℝ) ^ 4) :=
          mul_le_mul hL_le_2m hBp_le hBpnn (by positivity)
        have hCLEC3nn : (0 : ℝ) ≤ CLE * C3 := mul_nonneg hCLEnn hC3nn
        have hLBp_le' : CLE * C3 * ((L : ℝ) * Bp) ≤
            CLE * C3 * ((2 * (m : ℝ)) * (8 * (m : ℝ) ^ 4)) :=
          mul_le_mul_of_nonneg_left hLBp_le hCLEC3nn
        calc CLE * (C3 * (L : ℝ)) * (Bp * (m : ℝ) ^ (-(12000 : ℝ)))
            = CLE * C3 * ((L : ℝ) * Bp) * (m : ℝ) ^ (-(12000 : ℝ)) := by ring
          _ ≤ CLE * C3 * ((2 * (m : ℝ)) * (8 * (m : ℝ) ^ 4)) * (m : ℝ) ^ (-(12000 : ℝ)) :=
              mul_le_mul_of_nonneg_right hLBp_le' hm12000nn
          _ = 16 * C3 * CLE * ((m : ℝ) ^ (5 : ℕ) * (m : ℝ) ^ (-(12000 : ℝ))) := by ring
      have hm5_strong : (m : ℝ) ^ (5 : ℕ) * (m : ℝ) ^ (-(12000 : ℝ)) ≤ (m : ℝ) ^ (-(6000 : ℝ)) := by
        have hm5cast : (m : ℝ) ^ (5 : ℕ) = (m : ℝ) ^ ((5 : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
        rw [hm5cast, ← Real.rpow_add hmpos]
        apply Real.rpow_le_rpow_of_exponent_le hm1
        norm_num
      have hstep3 : 16 * C3 * CLE * ((m : ℝ) ^ (5 : ℕ) * (m : ℝ) ^ (-(12000 : ℝ))) ≤
          16 * C3 * CLE * (m : ℝ) ^ (-(6000 : ℝ)) :=
        mul_le_mul_of_nonneg_left hm5_strong (by positivity)
      have hCenvle : 16 * C3 * CLE ≤ Cenv := by
        have hstepa : 16 * C3 * CLE ≤ 16 * C3 * |CLE| :=
          mul_le_mul_of_nonneg_left (le_abs_self CLE) (by positivity)
        have hstepb : 16 * C3 * |CLE| ≤ Cenv := by rw [hCenvdef]; exact le_max_right _ _
        linarith only [hstepa, hstepb]
      have hm6000nn : (0 : ℝ) ≤ (m : ℝ) ^ (-(6000 : ℝ)) := Real.rpow_nonneg hmnn _
      have hstep4 : 16 * C3 * CLE * (m : ℝ) ^ (-(6000 : ℝ)) ≤ Cenv * (m : ℝ) ^ (-(6000 : ℝ)) :=
        mul_le_mul_of_nonneg_right hCenvle hm6000nn
      linarith only [hstep1, hstep2, hstep3, hstep4]
    · have hCLEnn' : CLE ≤ 0 := hCLEneg.le
      have hprodnn : (0 : ℝ) ≤ nu ^ (-(4 : ℝ)) *
          ((if m - h < L then (L : ℝ) ^ 2 * (3 : ℝ) ^ (-((m - h - (m - h - h) : ℕ) : ℝ)) else 0) +
            (↑(m - h) : ℝ) * (L : ℝ) ^ 2 * (↑(m - (m - h - h)) : ℝ) *
              (3 : ℝ) ^ (-((d : ℝ) / 2 * (↑(m - (m - h)) : ℝ)))) :=
        mul_nonneg hnu4nn hbracket_nn
      have hLHSnonpos : CLE * nu ^ (-(4 : ℝ)) *
          ((if m - h < L then (L : ℝ) ^ 2 * (3 : ℝ) ^ (-((m - h - (m - h - h) : ℕ) : ℝ)) else 0) +
            (↑(m - h) : ℝ) * (L : ℝ) ^ 2 * (↑(m - (m - h - h)) : ℝ) *
              (3 : ℝ) ^ (-((d : ℝ) / 2 * (↑(m - (m - h)) : ℝ)))) ≤ 0 := by
        have heq : CLE * nu ^ (-(4 : ℝ)) *
            ((if m - h < L then (L : ℝ) ^ 2 * (3 : ℝ) ^ (-((m - h - (m - h - h) : ℕ) : ℝ)) else 0) +
              (↑(m - h) : ℝ) * (L : ℝ) ^ 2 * (↑(m - (m - h - h)) : ℝ) *
                (3 : ℝ) ^ (-((d : ℝ) / 2 * (↑(m - (m - h)) : ℝ)))) =
            CLE * (nu ^ (-(4 : ℝ)) *
              ((if m - h < L then (L : ℝ) ^ 2 * (3 : ℝ) ^ (-((m - h - (m - h - h) : ℕ) : ℝ)) else 0) +
                (↑(m - h) : ℝ) * (L : ℝ) ^ 2 * (↑(m - (m - h - h)) : ℝ) *
                  (3 : ℝ) ^ (-((d : ℝ) / 2 * (↑(m - (m - h)) : ℝ))))) := by ring
        rw [heq]
        exact mul_nonpos_iff.mpr (Or.inr ⟨hCLEnn', hprodnn⟩)
      have hm6000nn : (0 : ℝ) ≤ (m : ℝ) ^ (-(6000 : ℝ)) := Real.rpow_nonneg hmnn _
      have hCenvm6000nn : (0 : ℝ) ≤ Cenv * (m : ℝ) ^ (-(6000 : ℝ)) :=
        mul_nonneg (by linarith only [hCenv1]) hm6000nn
      linarith only [hLHSnonpos, hCenvm6000nn]
  · intro e he sigma hsigma2 h0 hh0 omega
    exact hX0bound h0 hh0
      ((sigma * Real.sqrt (sigmaBarInfinite nu r P)⁻¹) • e, Real.sqrt (sigmaBarInfinite nu r P) • e)
      omega

end

end SuperdiffusionCLT.Section4.NewMixing
