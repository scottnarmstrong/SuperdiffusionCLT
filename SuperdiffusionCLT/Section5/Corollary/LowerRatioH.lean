/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Corollary.LowerRatioF
public import SuperdiffusionCLT.Section5.Corollary.LowerRatioG
public import SuperdiffusionCLT.Section5.Corollary.CellErrorMeasurable
public import SuperdiffusionCLT.Section5.Principal.AssemblyG
public import SuperdiffusionCLT.Section5.Thresholds.OneStepFromCorollaries
public import SuperdiffusionCLT.Section5.Localization.Localization

/-!
# `cor.lower.ratio`

Assembly: the basic split, the measurable majorant of the cell errors (`cellError_majorant`), the
principal-term estimate and the coupled-input estimate.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open MeasureTheory Homogenization Filter
open SuperdiffusionCLT.Section2.Cutoff SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)
open scoped ENNReal

theorem lower_ratio (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C₀ C : ℝ, 1 ≤ C₀ ∧ 1 ≤ C ∧
      ∀ (nu cStar K : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
          (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
          (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
          (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
          ∀ m h : ℕ, 1 ≤ h → 400 * h ≤ m →
            2 * SuperdiffusionCLT.Frozen.Section4.lNaught C₀ C₀ (3 / 4) cStar nu K ≤ (m : ℝ) →
            SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu (m - h) P *
                (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ ≤
              1 + (-(cStar * Real.log 3 * (h : ℝ)) + C * (Real.log (m : ℝ) ^ (2 : ℝ) + K)) *
                  (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu (m - h) P) ^
                    (-(2 : ℝ)) +
                C * (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu (m - h) P) ^
                  (-(4 : ℝ)) * (h : ℝ) ^ (2 : ℝ) := by
  obtain ⟨C₀c, Cc, hC₀c, hCc, Hc⟩ := coupled_input d hd
  obtain ⟨C₀p, Cp, hC₀p, hCp, Hp⟩ := principal_term d hd
  obtain ⟨Cl, hCl, Hl⟩ := cellError_majorant d hd
  obtain ⟨C₀s, Ce, hC₀s, hCe, HSc⟩ := coupled4_scales d
  obtain ⟨C₀h, hC₀h, Hh⟩ := homogBelow_at_scales d hd
  obtain ⟨C₀f, hC₀f, Hf⟩ := pa_scale_facts
  set Cs : ℝ := max (max (max C₀c C₀p) (max Cl C₀s)) (max (max C₀h C₀f) Cp) with hCs
  have hCs1 : 1 ≤ Cs := le_trans hC₀c (le_trans (le_max_left _ _)
    (le_trans (le_max_left _ _) (le_max_left _ _)))
  have hCc' : C₀c ≤ Cs := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hCp' : C₀p ≤ Cs := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hCl' : Cl ≤ Cs := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_left _ _))
  have hCs' : C₀s ≤ Cs := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_left _ _))
  have hCh' : C₀h ≤ Cs := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))
  have hCf' : C₀f ≤ Cs := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))
  have hCpp : Cp ≤ Cs := le_trans (le_max_right _ _) (le_max_right _ _)
  have hCe0 : 0 < Ce := by linarith only [hCe]
  set Cfin : ℝ := (4 * Cp + (Cp + Cl) * Ce ^ 2) + (1 + Cs) + (1 + Cs) * (Cc + 4) + 1 with hCfin
  have hCfin1 : 1 ≤ Cfin := by
    have h1 : 0 ≤ 4 * Cp + (Cp + Cl) * Ce ^ 2 := by positivity
    have h2 : 0 ≤ (1 + Cs) * (Cc + 4) := by
      apply mul_nonneg <;> linarith only [hCs1, hCc]
    linarith only [h1, h2, hCs1]
  refine ⟨Cs, Cfin, hCs1, hCfin1, ?_⟩
  intro nu cStar K hnu hnu1 P hPre hJ2 hJ3 hJ1 hJ4 hJ5 m h hh h400 hm
  have hcStar := hJ5.cStar_pos
  have hcStar2 := hJ5.cStar_le_two
  have hK := hJ5.K_pos.le
  have hlm : ∀ X : ℝ, 0 ≤ X → X ≤ Cs →
      2 * SuperdiffusionCLT.Frozen.Section4.lNaught X X (3 / 4) cStar nu K ≤ (m : ℝ) :=
    fun X hX hXC => le_trans (mul_le_mul_of_nonneg_left
      (SuperdiffusionCLT.Section4.LNaught.lNaught_mono_both hX hXC hX hXC hK hcStar hnu
        (by norm_num)) (by norm_num)) hm
  set n : ℕ := ⌊(m : ℝ) - h - 100 * Real.logb 3 (nu⁻¹ * m)⌋₊ with hn
  obtain ⟨hmR, hinv, -, -, hnm⟩ := Hf Cs hCf' cStar hcStar hcStar2 nu hnu hnu1 K hK m h n hh h400
    hm hn
  obtain ⟨-, -, hσm⟩ := HSc nu cStar K hnu hnu1 P hPre hJ2 hJ3 hJ4 hJ5 m h hh h400
    (hlm C₀s (by linarith only [hC₀s]) hCs')
  have hσ : 0 < sigmaBarInfinite nu (m - h) P :=
    SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite_pos hnu (m - h) hPre hJ2 hJ3 hJ4
  obtain ⟨-, hA2⟩ := Hh Cs hCh' cStar nu K hnu hnu1 P hPre hJ2 hJ3 hJ1 hJ4 hJ5 m h n hh h400 hm hn
  set σ := sigmaBarInfinite nu (m - h) P with hσdef
  have hm1 : (3 : ℝ) ≤ m := by linarith only [hmR]
  have hm0 : (0 : ℝ) < m := by linarith only [hm1]
  have hL1 : 1 ≤ Real.log (m : ℝ) := lowerRatio_one_le_log hm1
  have hL1' : 1 ≤ Real.log (m : ℝ) ^ (2 : ℝ) := by
    rw [Real.rpow_two]; nlinarith only [hL1]
  have hx0 : 0 ≤ σ ^ (-(2 : ℝ)) := Real.rpow_nonneg hσ.le _
  have hlg0 : 0 ≤ Real.log (nu⁻¹ * (m : ℝ)) ^ (2 : ℝ) := by
    rw [Real.rpow_two]; exact sq_nonneg _
  obtain ⟨e, he⟩ := lowerRatio_unit_vector (d := d)
  choose wD hwD using fun (Kc : ℕ) (ω : ShellSeq d) =>
    SuperdiffusionCLT.Section3.ResponseFields.exists_isCubeDirichletResponse
      (originCube d (Kc : ℤ)) (memVectorL2_hshellFlux (m := m) (h := h) nu P ω e Kc)
  have h0 : vecNormSq (0 : Vec d) ≤ 1 := by simp [vecNormSq, vecDot]
  have hTT : ∀ y : ℝ, 0 ≤ y → 0 ≤ 1 - cStar * Real.log 3 * y + K * σ ^ (-(2 : ℝ)) +
      (Cc + 4) * y ^ 2 := fun y hy =>
    lowerRatio_bracket_nonneg hcStar2 hy (mul_nonneg hK hx0) (by linarith only [hCc])
  -- the bound for each large `Kc`
  have key : ∀ Kc : ℕ, 100 * m ≤ Kc →
      ENNReal.ofReal (σ * (sigmaBarInfinite nu m P)⁻¹) ≤
        ENNReal.ofReal (1 + Cp * σ ^ (-(2 : ℝ)) * Real.log (nu⁻¹ * (m : ℝ)) ^ (2 : ℝ)) *
          subcubeAvg Kc n (fun Q => ∫⁻ ω, ENNReal.ofReal
            (blockVecDot (coupledVec nu P m h Q ω e (wD Kc ω).toH1Function.grad)
              (coupledVec nu P m h Q ω e (wD Kc ω).toH1Function.grad)) ∂P.toMeasure) +
          (ENNReal.ofReal (Cp * (m : ℝ) ^ (-(10 : ℝ))) +
            ENNReal.ofReal (Cl * (m : ℝ) ^ (-(50 : ℝ)))) := by
    intro Kc hK100
    have hnK : n ≤ Kc := by omega
    obtain ⟨B, hBm, hB, hBint⟩ := Hl nu cStar K hnu hnu1 P hPre hJ2 hJ3 hJ1 hJ4 hJ5 m h Kc hh h400
      hK100 (hlm Cl (by linarith only [hCl]) hCl') e 0 (le_of_eq he) h0 n hn (wD Kc)
      (fun _ => 0) (hwD Kc) (fun ω => lowerRatio_neumann_zero nu P m h ω _)
    have hN0 : ∀ (ω : ShellSeq d) (y : Vec d),
        ((fun _ : ShellSeq d => (0 : H1MeanZeroFunction (openCubeSet (originCube d (Kc : ℤ))))) ω).toH1Function.grad y +
          hshellFlux nu P m h ω 0 y = 0 := fun ω y => by
      rw [lowerRatio_hshellFlux_zero]; simp
    have hcore := lowerRatio_core hnu m h Kc n hnK P hPre hJ2 hJ3 hJ4 hσ e he (wD Kc)
      (fun _ => 0) (hwD Kc) (fun ω => lowerRatio_neumann_zero nu P m h ω _) hN0 B hBm hB
    have hp := Hp nu cStar K hnu hnu1 P hPre hJ2 hJ3 hJ1 hJ4 hJ5 m h Kc hh h400 hK100
      (hlm C₀p (by linarith only [hC₀p]) hCp') e 0 (le_of_eq he) h0 n hn (wD Kc) (fun _ => 0)
      (hwD Kc) (fun ω => lowerRatio_neumann_zero nu P m h ω _)
    have hlen : ∀ (Q : TriadicCube d) (ω : ShellSeq d),
        blockLenSq (ahomSqrtApply nu (m - h) P (principalPhat m h Q ω
          (blockSlope nu (m - h) P Q e 0 (wD Kc ω).toH1Function.grad
            (fun y => ((fun _ : ShellSeq d => (0 : H1MeanZeroFunction
              (openCubeSet (originCube d (Kc : ℤ))))) ω).toH1Function.grad y +
              hshellFlux nu P m h ω 0 y)))) =
        blockVecDot (coupledVec nu P m h Q ω e (wD Kc ω).toH1Function.grad)
          (coupledVec nu P m h Q ω e (wD Kc ω).toH1Function.grad) := fun Q ω =>
      lowerRatio_len_eq nu P m h Q ω e _ _ (hN0 ω)
    simp only [hlen] at hp
    exact hcore.trans (add_le_add hp hBint) |>.trans (le_of_eq (by rw [add_assoc]))
  set A : ℝ := Cp * σ ^ (-(2 : ℝ)) * Real.log (nu⁻¹ * (m : ℝ)) ^ (2 : ℝ) with hAdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]; exact mul_nonneg (mul_nonneg (by linarith only [hCp]) hx0) hlg0
  have hlim := Hc nu cStar K hnu hnu1 P hPre hJ2 hJ3 hJ1 hJ4 hJ5 m h hh h400
    (hlm C₀c (by linarith only [hC₀c]) hCc') n hn e he wD (fun Kc _ ω => hwD Kc ω)
  have hs4 : σ ^ (-(4 : ℝ)) = (σ ^ (-(2 : ℝ))) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hσ.le]; norm_num
  set T' : ℝ := 1 - cStar * Real.log 3 * h * σ ^ (-(2 : ℝ)) + K * σ ^ (-(2 : ℝ)) +
    (Cc + 4) * σ ^ (-(4 : ℝ)) * (h : ℝ) ^ 2 with hT'def
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  have hT'0 : 0 ≤ T' := by
    have := hTT ((h : ℝ) * σ ^ (-(2 : ℝ))) (mul_nonneg hh0 hx0)
    have e1 : T' = 1 - cStar * Real.log 3 * ((h : ℝ) * σ ^ (-(2 : ℝ))) + K * σ ^ (-(2 : ℝ)) +
        (Cc + 4) * ((h : ℝ) * σ ^ (-(2 : ℝ))) ^ 2 := by
      rw [hT'def, hs4]; ring
    rw [e1]; exact this
  have hs40 : 0 ≤ σ ^ (-(4 : ℝ)) * (h : ℝ) ^ 2 := by
    apply mul_nonneg (Real.rpow_nonneg hσ.le _) (sq_nonneg _)
  have hTT' : 1 - cStar * Real.log 3 * h * σ ^ (-(2 : ℝ)) + K * σ ^ (-(2 : ℝ)) +
      Cc * σ ^ (-(4 : ℝ)) * (h : ℝ) ^ 2 ≤ T' := by
    rw [hT'def]; linarith only [hs40]
  have hcm : ENNReal.ofReal (1 + A) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hfin := lowerRatio_le_of_limsup (N0 := 100 * m) hcm (fun Kc hKc => key Kc hKc)
    (hlim.trans (ENNReal.ofReal_le_ofReal hTT'))
  have hr1 : 0 ≤ Cp * (m : ℝ) ^ (-(10 : ℝ)) := mul_nonneg (by linarith only [hCp])
    (Real.rpow_nonneg hm0.le _)
  have hr2 : 0 ≤ Cl * (m : ℝ) ^ (-(50 : ℝ)) := mul_nonneg (by linarith only [hCl])
    (Real.rpow_nonneg hm0.le _)
  rw [← ENNReal.ofReal_mul (by linarith only [hA0]), ← ENNReal.ofReal_add hr1 hr2,
    ← ENNReal.ofReal_add (mul_nonneg (by linarith only [hA0]) hT'0) (add_nonneg hr1 hr2)] at hfin
  have hR := (ENNReal.ofReal_le_ofReal_iff (add_nonneg (mul_nonneg (by linarith only [hA0]) hT'0)
    (add_nonneg hr1 hr2))).1 hfin
  -- the elementary arithmetic
  have hm10 : (m : ℝ) ^ (-(10 : ℝ)) ≤ Ce ^ 2 * σ ^ (-(2 : ℝ)) := by
    have := lowerRatio_mpow_le (by linarith only [hm1]) hCe0 10 (by norm_num) hσ hσm
    have e10 : ((10 : ℕ) : ℝ) = 10 := by norm_num
    rwa [e10] at this
  have hm50 : (m : ℝ) ^ (-(50 : ℝ)) ≤ Ce ^ 2 * σ ^ (-(2 : ℝ)) := by
    have := lowerRatio_mpow_le (by linarith only [hm1]) hCe0 50 (by norm_num) hσ hσm
    have e50 : ((50 : ℕ) : ℝ) = 50 := by norm_num
    rwa [e50] at this
  have hlog4 := lowerRatio_log_sq_le hnu hnu1 (by linarith only [hm1]) hinv
  set x : ℝ := σ ^ (-(2 : ℝ)) with hxdef
  set L : ℝ := Real.log (m : ℝ) ^ (2 : ℝ) with hLdef
  have hCe2 : 0 ≤ Ce ^ 2 := sq_nonneg Ce
  have hxL : x ≤ x * L := by nlinarith only [hx0, hL1']
  have hr : Cp * (m : ℝ) ^ (-(10 : ℝ)) + Cl * (m : ℝ) ^ (-(50 : ℝ)) ≤
      (Cp + Cl) * Ce ^ 2 * x * L := by
    have h1 := mul_le_mul_of_nonneg_left hm10 (by linarith only [hCp] : 0 ≤ Cp)
    have h2 := mul_le_mul_of_nonneg_left hm50 (by linarith only [hCl] : 0 ≤ Cl)
    have h3 : (Cp + Cl) * Ce ^ 2 * x ≤ (Cp + Cl) * Ce ^ 2 * (x * L) :=
      mul_le_mul_of_nonneg_left hxL (by positivity)
    have h4 : (Cp + Cl) * Ce ^ 2 * x = Cp * (Ce ^ 2 * x) + Cl * (Ce ^ 2 * x) := by ring
    have h5 : (Cp + Cl) * Ce ^ 2 * (x * L) = (Cp + Cl) * Ce ^ 2 * x * L := by ring
    linarith only [h1, h2, h3, h4, h5]
  have hAL : A ≤ 4 * Cp * x * L := by
    have h1 : A = Cp * x * Real.log (nu⁻¹ * (m : ℝ)) ^ (2 : ℝ) := rfl
    have h2 := mul_le_mul_of_nonneg_left hlog4 (mul_nonneg (by linarith only [hCp] : 0 ≤ Cp) hx0)
    have h3 : Cp * x * (4 * L) = 4 * Cp * x * L := by ring
    linarith only [h1, h2, h3]
  have hAs : A ≤ Cs := by
    have hm34 : (m : ℝ) ^ (-(3 / 4 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith only [hm1]) (by norm_num)
    have h1 : Cs * x * Real.log (nu⁻¹ * (m : ℝ)) ^ (2 : ℝ) ≤ Cs := by
      have := mul_le_mul_of_nonneg_left hm34 (by linarith only [hCs1] : 0 ≤ Cs)
      linarith only [hA2, this]
    have h2 : A ≤ Cs * x * Real.log (nu⁻¹ * (m : ℝ)) ^ (2 : ℝ) := by
      rw [hAdef]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCpp hx0) hlg0
    linarith only [h1, h2]
  have hN1 : 0 ≤ 4 * Cp + (Cp + Cl) * Ce ^ 2 := by positivity
  have hN2 : 0 ≤ (1 + Cs) * (Cc + 4) := by
    apply mul_nonneg <;> linarith only [hCs1, hCc]
  have hC1 : 4 * Cp + (Cp + Cl) * Ce ^ 2 ≤ Cfin := by linarith only [hN1, hN2, hCfin, hCs1]
  have hC1' : 4 * Cp + (Cp + Cl) * Ce ^ 2 ≤ Cfin := hC1
  have hC2 : 1 + Cs ≤ Cfin := by linarith only [hN1, hN2, hCfin, hCs1]
  have hC3 : (1 + Cs) * (Cc + 4) ≤ Cfin := by linarith only [hN1, hN2, hCfin, hCs1]
  have hmain := lowerRatio_arith (R := σ * (sigmaBarInfinite nu m P)⁻¹) (A := A)
    (B := cStar * Real.log 3 * h * x) (N := K * x) (H := (Cc + 4) * σ ^ (-(4 : ℝ)) * (h : ℝ) ^ 2)
    (r := Cp * (m : ℝ) ^ (-(10 : ℝ)) + Cl * (m : ℝ) ^ (-(50 : ℝ))) (x := x) (L := L) (Kk := K)
    (s4h := σ ^ (-(4 : ℝ)) * (h : ℝ) ^ 2) (Ca := 4 * Cp) (Ca2 := Cs) (Cr := (Cp + Cl) * Ce ^ 2)
    (Ch := Cc + 4) (C := Cfin) (by linarith only [hR, hT'def]) hA0
    (mul_nonneg (mul_nonneg (mul_nonneg hcStar.le (Real.log_nonneg (by norm_num))) hh0) hx0)
    (mul_nonneg hK hx0)
    (mul_nonneg (mul_nonneg (by linarith only [hCc]) (Real.rpow_nonneg hσ.le _)) (sq_nonneg _))
    hAL hAs hr rfl (le_of_eq (by ring)) hx0 (by linarith only [hL1']) hK hs40
    (by linarith only [hCs1]) hC1 hC2 hC3
  have hh2 : (h : ℝ) ^ (2 : ℝ) = (h : ℝ) ^ 2 := Real.rpow_two _
  have hfinal : 1 - cStar * Real.log 3 * h * x + Cfin * (L + K) * x +
      Cfin * (σ ^ (-(4 : ℝ)) * (h : ℝ) ^ 2) =
      1 + (-(cStar * Real.log 3 * (h : ℝ)) + Cfin * (L + K)) * x +
        Cfin * σ ^ (-(4 : ℝ)) * (h : ℝ) ^ (2 : ℝ) := by
    rw [hh2]; ring
  exact le_trans hmain (le_of_eq hfinal)

/-- Satisfiability: the scale hypotheses of `lower_ratio` hold for suitable `m`, `h`, and the response
families exist, for every choice of the parameters. -/
example (C cStar K nu : ℝ) (hnu : 0 < nu) (hnu1 : nu ≤ 1) :
    ∃ m h : ℕ, 1 ≤ h ∧ 400 * h ≤ m ∧
      2 * SuperdiffusionCLT.Frozen.Section4.lNaught C C (3 / 4) cStar nu K ≤ (m : ℝ) := by
  obtain ⟨m, h, -, h1, h2, h3, -⟩ := homogBelow_at_scales_scale_witness C cStar K nu hnu hnu1
  exact ⟨m, h, h1, h2, h3⟩

end SuperdiffusionCLT.Section5
