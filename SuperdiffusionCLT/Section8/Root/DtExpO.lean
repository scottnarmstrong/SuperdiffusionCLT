/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Root.DtExpN
public import SuperdiffusionCLT.Section8.Prereq.ExitEstimateE
public import SuperdiffusionCLT.Section8.Prereq.ResolventEstimateC
public import SuperdiffusionCLT.Section8.Prereq.DomainIdentificationD

/-!
# The quenched moment clause of Theorem A

`dtExp_clause` is the hypothesis `hDt` of `thmA_of_parts` (`e.Dt.exp`),
from the root theorem `t.superdiffusivity` taken as an explicit hypothesis, with the exit-time
estimate supplied by `exitEst_exit_time_estimate`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization Homogenization.Book.Ch02 MeasureTheory MarkovProcess
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section6
open scoped ENNReal NNReal Matrix.Norms.Elementwise

/-- **The quenched moment clause of Theorem A** (`e.Dt.exp`): the hypothesis `hDt` of
`thmA_of_parts`, from the root theorem `hRoot`. -/

theorem dtExp_clause (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hRoot : ∀ (d : ℕ) [NeZero d], 2 ≤ d →
  ∀ α β : ℝ, 0 < α → α ≤ 1 → 0 < β → β ≤ 1 → β + 2 * α < 1 →
        ∀ U : Set (Homogenization.Vec d),
          SuperdiffusionCLT.Section7.IsSmoothBoundedDomain U →
          ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
            ∀ cStar : ℝ, 0 < cStar →
              ∀ K : ℝ,
                ∃ C : ℝ, 1 ≤ C ∧
                  ∀ (P : MeasureTheory.ProbabilityMeasure
                        (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
                    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
                    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
                    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K
                        hPrefix hJ2 hJ3 →
                    ∃ Z : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                      Measurable Z ∧
                      (∀ ξ : ℝ, 1 ≤ ξ →
                        P.toMeasure {omega | ξ ≤ Z omega} ≤
                          ENNReal.ofReal (C * Real.exp (-(C⁻¹ * Real.log ξ ^ β)))) ∧
                      ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
                        ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → Z omega ≤ ε⁻¹ →
                          ∀ (f : Homogenization.Vec d → ℝ) (g u uhom : Homogenization.H1Function U),
                            SuperdiffusionCLT.Section7.IsDirichletSolution
                                (fun x => ((2 * cStar * |Real.log ε|) ^ ((1 : ℝ) / 2))⁻¹ •
                                  SuperdiffusionCLT.Section7.epField nu omega ε x)
                                U f g u →
                            SuperdiffusionCLT.Section7.IsDirichletSolution
                                (fun _ => (1 : Homogenization.Mat d)) U f g uhom →
                            MeasureTheory.eLpNorm (fun x => u.toFun x - uhom.toFun x) ⊤
                                  (MeasureTheory.volume.restrict U) +
                                SuperdiffusionCLT.Section7.hMinusOneVec U
                                  (fun x => u.grad x - uhom.grad x) +
                                SuperdiffusionCLT.Section7.hMinusOneVec U
                                  (fun x =>
                                    Homogenization.matVecMul
                                        (((2 * cStar * |Real.log ε|) ^ ((1 : ℝ) / 2))⁻¹ •
                                          SuperdiffusionCLT.Section7.epFieldCentered
                                            nu omega ε U x)
                                        (u.grad x) -
                                      uhom.grad x) ≤
                              ENNReal.ofReal (C * |Real.log ε| ^ (-α)) *
                                (MeasureTheory.eLpNorm
                                    (fun x => SuperdiffusionCLT.Section7.eucNorm (g.grad x)) ⊤
                                    (MeasureTheory.volume.restrict U) +
                                  MeasureTheory.eLpNorm f ⊤ (MeasureTheory.volume.restrict U))
    ) :
    ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
      ∀ cStar : ℝ, 0 < cStar →
        ∀ K : ℝ,
          ∀ δ β : ℝ, 0 < δ → δ < 1 / 4 → 0 < β → β < 4 * δ →
            ∃ C : ℝ, 1 ≤ C ∧
              ∀ (P : MeasureTheory.ProbabilityMeasure
                    (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
                (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
                (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
                (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K
                    hPrefix hJ2 hJ3 →
                ∃ S : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d →
                    MarkovProcess.SubMarkovKernelSemigroup (Homogenization.Vec d),
                  (∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
                    SuperdiffusionCLT.Section8.IsDivergenceFormFeller
                      (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega)
                      (S omega)) ∧
                  ∀ t : ℝ, 10 ≤ t →
                    (∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
                      MeasureTheory.Integrable (fun y => Homogenization.vecNormSq y)
                        ((S omega) t.toNNReal (0 : Homogenization.Vec d))) ∧
                    P.toMeasure
                        {omega |
                          C * Real.log t ^ ((1 : ℝ) / 4 + δ) <
                            |(1 / t) * (∫ y, Homogenization.vecNormSq y
                                  ∂((S omega) t.toNNReal (0 : Homogenization.Vec d))) -
                                2 * (d : ℝ) * Real.sqrt cStar * Real.sqrt (Real.log t)| +
                              (1 / t) * Homogenization.vecNormSq
                                (∫ y, y ∂((S omega) t.toNNReal (0 : Homogenization.Vec d)))} ≤
                      ENNReal.ofReal (C * Real.exp (-(C⁻¹ * Real.log t ^ β)))
    := by
  intro nu hnu hnu1 cStar hc K δ β hδ0 hδ1 hβ0 hβ1
  have hd1 : 1 ≤ d := by omega
  have hd0 : (0 : ℝ) < d := Nat.cast_pos.2 (by omega)
  set α : ℝ := 1 / 2 - δ - β / 4 with hαdef
  have hα0 : 0 < α := by rw [hαdef]; linarith only [hδ1, hβ1, hδ0, hβ0]
  have hα1 : α < 1 := by rw [hαdef]; linarith only [hδ0, hβ0]
  have hβ1' : β < 1 := by linarith only [hβ1, hδ1]
  have hαβ : β + 2 * α < 1 := by rw [hαdef]; linarith only [hβ1]
  have hαδ : (1 - α) / 2 ≤ 1 / 4 + δ := by rw [hαdef]; linarith only [hβ1, hδ0]
  have hU : SuperdiffusionCLT.Section7.IsSmoothBoundedDomain (euclideanBall (0 : Vec d) 1) := by
    have h := SuperdiffusionCLT.Section7.isSmoothBoundedDomain_euclidBall (d := d)
    have e : SuperdiffusionCLT.Section6.euclidBall (d := d) 1 = euclideanBall (0 : Vec d) 1 := by
      ext y
      simp [SuperdiffusionCLT.Section6.euclidBall, euclideanBall, euclideanSqDist]
    rwa [e] at h
  obtain ⟨CR, hCR1, HR⟩ := resEst_resolvent_estimate d hd hRoot α β hα0 hα1.le hβ0 hβ1'.le hαβ
    (euclideanBall (0 : Vec d) 1) hU nu hnu hnu1 cStar hc K
  obtain ⟨CX, cE, hCX1, hcE, HX⟩ := exitEst_exit_time_estimate d hd hRoot α β hα0 hα1 hβ0 hβ1'
    hαβ nu hnu hnu1 cStar hc K
  obtain ⟨Cgr, B, HGr⟩ := dtExp_growth (d := d)
  obtain ⟨K3, hK31, HK3⟩ := dtExp_const_grad (d := d) hnu (c0 := Real.sqrt (max Cgr 0))
    (Real.sqrt_nonneg _)
  set B' : ℝ := max B 1 with hB'def
  have hB'0 : 0 < B' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set arate : ℝ := gradScale_rate d with harate
  obtain ⟨L0, hL01, HL0⟩ := dtExp_thresholds (d := d) hd1 (c := cStar) (α := α) (β := β)
    (cE := cE) (K3 := K3) (B' := B') (arate := arate) hα0 hcE (by linarith only [hK31])
  set Cb : ℝ := 16 * (2 + d) * CR + 2 + 2 * d * Real.sqrt (2 * cStar) + 4 * d * Real.sqrt cStar +
    d * (16 * CR + 2) ^ 2 with hCb
  set M : ℝ := max (max (2 * CR) (2 * CX)) (max (4 * B' ^ 2) (max arate 1)) with hM
  set Cfin : ℝ := max (max Cb (CR + CX + 1 + 8)) (max M (L0 ^ β + 1)) with hCfin
  have hM1 : (1 : ℝ) ≤ M := le_trans (le_max_right arate 1)
    (le_trans (le_max_right (4 * B' ^ 2) (max arate 1)) (le_max_right _ _))
  have hCM : M ≤ Cfin := le_trans (le_max_left M (L0 ^ β + 1)) (le_max_right _ _)
  have hCfin1 : 1 ≤ Cfin := hM1.trans hCM
  have hCfin0 : 0 < Cfin := by linarith only [hCfin1]
  have hCR2 : 2 * CR ≤ Cfin := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCM
  have hCX2 : 2 * CX ≤ Cfin := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCM
  have hB2 : 4 * B' ^ 2 ≤ Cfin := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCM
  have hAr : arate ≤ Cfin := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
    (le_max_right _ _))) hCM
  have hSum : CR + CX + 1 + 8 ≤ Cfin := (le_max_right Cb _).trans (le_max_left _ _)
  have hCb : Cb ≤ Cfin := (le_max_left Cb _).trans (le_max_left _ _)
  have hL0b : L0 ^ β + 1 ≤ Cfin := le_trans (le_max_right M _) (le_max_right _ _)
  refine ⟨Cfin, hCfin1, ?_⟩
  intro P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨ZR, hZRm, hZRt, hZRae⟩ := HR P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨ZX, hZXm, hZXt, hZXae⟩ := HX P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨Kf, hKm, hK27, hKb, hKae⟩ := HGr P hPrefix hJ1 hJ2 hJ3 hJ4
  obtain ⟨S, hS, hSD⟩ := dtExp_choice hPrefix hJ3 hnu
  have hlink := thmA_link_data (nu := nu) hJ3
  have hdataG := dtExp_dataG hPrefix hJ3 hnu
  have hcont := ae_contDiff_fullStreamRecentered hJ3
  have harate0 : 0 < arate := annDt_rate_pos hPrefix
  refine ⟨S, hS, fun t ht => ⟨?_, ?_⟩⟩
  · filter_upwards [hSD, fieldInput_ae_data hPrefix hJ3 hnu] with ω hω hne
    obtain ⟨D⟩ := hne
    rw [hω D]
    exact fieldMoment_integrable_vecNormSq D _
  · have ht0 : 0 < t := by linarith only [ht]
    have hL1 : 1 ≤ Real.log t := (dtExp_scale_facts ht hα0 hα1).1
    by_cases hsmall : Real.log t < L0
    · -- the bounded range of times
      refine (prob_le_one).trans ?_
      rw [← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : Real.log t ^ β ≤ L0 ^ β := Real.rpow_le_rpow (by linarith only [hL1]) hsmall.le hβ0.le
      have h2 : Cfin⁻¹ * Real.log t ^ β ≤ 1 := by
        have : Cfin⁻¹ * Real.log t ^ β ≤ Cfin⁻¹ * Cfin :=
          mul_le_mul_of_nonneg_left (by linarith only [h1, hL0b]) (inv_nonneg.2 hCfin0.le)
        rwa [inv_mul_cancel₀ hCfin0.ne'] at this
      have h3 := Real.add_one_le_exp (-(Cfin⁻¹ * Real.log t ^ β))
      have h4 : Cfin * (-(Cfin⁻¹ * Real.log t ^ β) + 1) = Cfin - Real.log t ^ β := by
        field_simp; ring
      have h5 : Cfin * (-(Cfin⁻¹ * Real.log t ^ β) + 1) ≤ Cfin * Real.exp (-(Cfin⁻¹ * Real.log t ^ β)) :=
        mul_le_mul_of_nonneg_left h3 hCfin0.le
      linarith only [h4, h5, h1, hL0b]
    · rw [not_lt] at hsmall
      obtain ⟨T1, T2, T3, T4, T5, T6, T7⟩ := HL0 (Real.log t) hsmall
      set L := Real.log t with hLdef
      have hL0 : 0 < L := by linarith only [hL1]
      set s : ℝ := Real.exp (cE / (64 * d) * L ^ (α / 6)) with hsdef
      have hs1 : 1 ≤ s := Real.one_le_exp (by positivity)
      obtain ⟨hε0, hε2, hεhalf, hv1, hv2, hop, hdiff⟩ : 0 < dtExp_eps t α ∧
          dtExp_eps t α ^ 2 * (t * Real.log t ^ ((1 + α) / 2)) = 1 ∧ dtExp_eps t α ≤ 1 / 2 ∧
          Real.log t / 2 ≤ |Real.log (dtExp_eps t α)| ∧
          |Real.log (dtExp_eps t α)| ≤ Real.log t ∧
          opScale cStar (dtExp_eps t α) *
            (2 * Real.sqrt (2 * cStar * |Real.log (dtExp_eps t α)|)) = 1 ∧
          |2 * Real.sqrt (2 * cStar * |Real.log (dtExp_eps t α)|) -
            2 * Real.sqrt cStar * Real.sqrt (Real.log t)| ≤ 4 * Real.sqrt cStar :=
        dtExp_eps_facts ht hα0 hα1 hc
      set r : ℝ := (dtExp_eps t α)⁻¹ with hrdef
      have hr1 : 1 ≤ r := by
        rw [hrdef]
        exact (one_le_inv₀ hε0).2 (by linarith only [hεhalf])
      have hlogr : L / 2 ≤ Real.log r := by
        have hneg : Real.log (dtExp_eps t α) < 0 := Real.log_neg hε0 (by linarith only [hεhalf])
        rw [hrdef, Real.log_inv]
        rw [abs_of_neg hneg] at hv1
        exact hv1
      -- the events
      have hRb : P.toMeasure {ω | r ≤ ZR ω} ≤
          ENNReal.ofReal (CR * Real.exp (-(CR⁻¹ / 2 * L ^ β))) :=
        (hZRt r hr1).trans (ENNReal.ofReal_le_ofReal (dtExp_tail_shift hCR1 hβ0 hβ1'.le hL1 hlogr))
      have hXb : P.toMeasure {ω | r ≤ ZX ω} ≤
          ENNReal.ofReal (CX * Real.exp (-(CX⁻¹ / 2 * L ^ β))) :=
        (hZXt r hr1).trans (ENNReal.ofReal_le_ofReal (dtExp_tail_shift hCX1 hβ0 hβ1'.le hL1 hlogr))
      have hKbd : P.toMeasure {ω | Real.sqrt t < Kf ω} ≤
          ENNReal.ofReal (Real.exp (-((L / (2 * B')) ^ 2))) :=
        dtExp_measure_K hK27 hKb ht T5
      have hGbd : P.toMeasure {ω | s < gradScale_G ω} ≤
          ENNReal.ofReal (8 * Real.exp (-((s / arate) ^ 2))) :=
        gradScale_measure_G_tail hPrefix hJ3 T6
      -- the inclusion
      have hincl : P.toMeasure {ω | Cfin * L ^ ((1 : ℝ) / 4 + δ) <
            |(1 / t) * (∫ y, vecNormSq y ∂((S ω) t.toNNReal (0 : Vec d))) -
                2 * (d : ℝ) * Real.sqrt cStar * Real.sqrt (Real.log t)| +
              (1 / t) * vecNormSq (∫ y, y ∂((S ω) t.toNNReal (0 : Vec d)))} ≤
          P.toMeasure ({ω | r ≤ ZR ω} ∪ {ω | r ≤ ZX ω} ∪ {ω | Real.sqrt t < Kf ω} ∪
            {ω | s < gradScale_G ω}) := by
        refine measure_mono_ae ?_
        filter_upwards [hdataG, hlink, hSD, hZRae, hZXae, hKae, hcont] with ω hDG hl hSω hZRω hZXω
          hKω hc1 hωE
        by_contra hnot
        simp only [Set.mem_union, not_or, Set.mem_ofPred_eq, not_lt] at hnot
        obtain ⟨⟨⟨hnR, hnX⟩, hnK⟩, hnG⟩ := hnot
        obtain ⟨D, hDg⟩ := hDG
        obtain ⟨hfeller, ⟨Q, hQ⟩, -⟩ := hl D
        rw [hSω D] at hωE
        have ha : ∀ i j, ContDiff ℝ 1 fun y => fullCoefficientRecentered nu ω y i j :=
          fun i j => domId_entries_contDiff hc1 i j
        have hgs : D.gradConst ≤ s := by rw [hDg]; exact hnG
        have hres := dtExp_good D ha hc hα0 hα1 hCR1 hcE ht
          ((hZRω (dtExp_eps t α) hε0 hεhalf (not_le.1 hnR).le 0 le_rfl).1) hQ
          (fun t0 h0 h1 => hZXω D.logGrowthBounds.resolvent.kernelSemigroup Q hfeller hQ
            (dtExp_eps t α) hε0 hεhalf (not_le.1 hnX).le t0 h0 h1 0
            (by simp [vecNormSq, vecDot]))
          (hK27 ω) hnK hKω (HK3 D hs1 hgs) T1 T2 T3 T4
        obtain ⟨-, hbd⟩ := hres
        have hexp : L ^ ((1 - α) / 2) ≤ L ^ ((1 : ℝ) / 4 + δ) :=
          Real.rpow_le_rpow_of_exponent_le hL1 hαδ
        have h6 : Cb * L ^ ((1 - α) / 2) ≤ Cfin * L ^ ((1 : ℝ) / 4 + δ) :=
          mul_le_mul hCb hexp (Real.rpow_nonneg hL0.le _) hCfin0.le
        linarith only [hωE, hbd, h6]
      -- the sum of the four tails
      have hβ2 : β ≤ 2 := by linarith only [hβ1']
      have he0 : 0 ≤ Real.exp (-(Cfin⁻¹ * L ^ β)) := (Real.exp_pos _).le
      have hLβ : 0 ≤ L ^ β := Real.rpow_nonneg hL0.le _
      have hinvle : ∀ {x : ℝ}, 0 < x → x ≤ Cfin → Cfin⁻¹ ≤ x⁻¹ := fun hx hxC => inv_anti₀ hx hxC
      have a1 : CR * Real.exp (-(CR⁻¹ / 2 * L ^ β)) ≤ CR * Real.exp (-(Cfin⁻¹ * L ^ β)) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by linarith only [hCR1])
        have h1 : Cfin⁻¹ ≤ (2 * CR)⁻¹ := hinvle (by linarith only [hCR1]) hCR2
        have h2 : (2 * CR)⁻¹ = CR⁻¹ / 2 := by field_simp
        have := mul_le_mul_of_nonneg_right (h1.trans h2.le) hLβ
        linarith only [this]
      have a2 : CX * Real.exp (-(CX⁻¹ / 2 * L ^ β)) ≤ CX * Real.exp (-(Cfin⁻¹ * L ^ β)) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by linarith only [hCX1])
        have h1 : Cfin⁻¹ ≤ (2 * CX)⁻¹ := hinvle (by linarith only [hCX1]) hCX2
        have h2 : (2 * CX)⁻¹ = CX⁻¹ / 2 := by field_simp
        have := mul_le_mul_of_nonneg_right (h1.trans h2.le) hLβ
        linarith only [this]
      have a3 : Real.exp (-((L / (2 * B')) ^ 2)) ≤ Real.exp (-(Cfin⁻¹ * L ^ β)) := by
        refine (dtExp_tail_K hB'0 hβ2 hL1).trans (Real.exp_le_exp.2 ?_)
        have h1 : Cfin⁻¹ ≤ (4 * B' ^ 2)⁻¹ := hinvle (by positivity) hB2
        have := mul_le_mul_of_nonneg_right h1 hLβ
        linarith only [this, show L ^ β / (4 * B' ^ 2) = (4 * B' ^ 2)⁻¹ * L ^ β by ring]
      have a4 : 8 * Real.exp (-((s / arate) ^ 2)) ≤ 8 * Real.exp (-(Cfin⁻¹ * L ^ β)) := by
        refine (dtExp_tail_G harate0 T6 T7).trans (mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.2 ?_) (by norm_num))
        have h1 : Cfin⁻¹ ≤ arate⁻¹ := hinvle harate0 hAr
        have := mul_le_mul_of_nonneg_right h1 hLβ
        linarith only [this, show L ^ β / arate = arate⁻¹ * L ^ β by ring]
      have hU : P.toMeasure ({ω | r ≤ ZR ω} ∪ {ω | r ≤ ZX ω} ∪ {ω | Real.sqrt t < Kf ω} ∪
          {ω | s < gradScale_G ω}) ≤
          P.toMeasure {ω | r ≤ ZR ω} + P.toMeasure {ω | r ≤ ZX ω} +
            P.toMeasure {ω | Real.sqrt t < Kf ω} + P.toMeasure {ω | s < gradScale_G ω} := by
        calc _ ≤ P.toMeasure ({ω | r ≤ ZR ω} ∪ {ω | r ≤ ZX ω} ∪ {ω | Real.sqrt t < Kf ω}) +
              P.toMeasure {ω | s < gradScale_G ω} := measure_union_le _ _
          _ ≤ (P.toMeasure ({ω | r ≤ ZR ω} ∪ {ω | r ≤ ZX ω}) +
              P.toMeasure {ω | Real.sqrt t < Kf ω}) + P.toMeasure {ω | s < gradScale_G ω} := by
            gcongr; exact measure_union_le _ _
          _ ≤ ((P.toMeasure {ω | r ≤ ZR ω} + P.toMeasure {ω | r ≤ ZX ω}) +
              P.toMeasure {ω | Real.sqrt t < Kf ω}) + P.toMeasure {ω | s < gradScale_G ω} := by
            gcongr; exact measure_union_le _ _
      refine hincl.trans (hU.trans ?_)
      refine (add_le_add (add_le_add (add_le_add hRb hXb) hKbd) hGbd).trans ?_
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hCfe : (CR + CX + 1 + 8) * Real.exp (-(Cfin⁻¹ * L ^ β)) ≤
          Cfin * Real.exp (-(Cfin⁻¹ * L ^ β)) := mul_le_mul_of_nonneg_right hSum he0
      nlinarith only [a1, a2, a3, a4, hCfe]

end SuperdiffusionCLT.Section8
