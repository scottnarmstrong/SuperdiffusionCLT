/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Principal.AverageMomentC

/-!
# The `L̲⁸` increment `k_m - k_{m-h}` has a measurable majorant with the printed moment

`e.kmn.Lp` at `p = 8`, `n = m - h`, `l = K`: `‖k_m - k_{m-h}‖_{L̲⁸(cu_K)} ≤ Z(ω)` with `Z` measurable
and `E[Z⁸]^{1/8} ≤ C h^{1/2}`. The majorant is the one produced by
`Frozen.Section2.streamIncrement_scale_estimates`, so that no measurability of the `L̲⁸` norm
itself is needed.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization MeasureTheory
open scoped ENNReal
open scoped Matrix.Norms.L2Operator

variable {d : ℕ}

theorem increment_L8_majorant (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)),
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
        ∀ m h Kc : ℕ, 1 ≤ h → h ≤ m → m ≤ Kc →
          ∃ Z : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ≥0∞, Measurable Z ∧
            (∀ omega, SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (Kc : ℤ)) 8
              (fun x => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega (m - h) m x)
                ≤ Z omega) ∧
            ∫⁻ omega, Z omega ^ (8 : ℕ) ∂P.toMeasure ≤
              ENNReal.ofReal (C * (h : ℝ) ^ ((1 : ℝ) / 2)) ^ (8 : ℕ) := by
  obtain ⟨C₂, hV⟩ := SuperdiffusionCLT.Frozen.Section2.streamIncrement_scale_estimates d
  obtain ⟨C₀, C₁, hV2⟩ := hV (1 / 2) (by norm_num) (by norm_num)
  obtain ⟨Cv, hV3⟩ := hV2 8 (by norm_num)
  refine ⟨7 * |Cv| + 6, by positivity, ?_⟩
  intro P hPre hJ2 hJ3 hJ1 hJ4 m h Kc hh hhm hmK
  have hV4 := hV3 P hPre hJ1 hJ2 hJ3 hJ4
  have hnm : m - h < m := by omega
  obtain ⟨X, hXm, hXO, hXle⟩ := (hV4.1 Kc m (m - h) hnm hmK).2.1
  have hhm' : m - (m - h) = h := by omega
  rw [hhm'] at hXO hXle
  have h8 : ENNReal.ofReal 8 = 8 := by simp
  rw [h8] at hXle
  have hhpos : (0 : ℝ) < (h : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hh) _
  have hA : 0 < (|Cv| + 1) * 3 * (h : ℝ) ^ ((1 : ℝ) / 2) := by positivity
  have hs8 : (8 : ℝ) ^ ((1 : ℝ) / 2) ≤ 3 := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  have ht : (3 : ℝ) ^ (-((d : ℝ) / (2 * 8) * ((Kc - m : ℕ) : ℝ))) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (by have : 0 ≤ (d : ℝ) / (2 * 8) * ((Kc - m : ℕ) : ℝ) := by positivity
          linarith only [this])
  have hXO' : Homogenization.IndependentSums.IsBigO P.toMeasure
      (Homogenization.IndependentSums.gammaSigma 2) X
      ((|Cv| + 1) * 3 * (h : ℝ) ^ ((1 : ℝ) / 2)) := by
    refine hXO.mono_scale ?_
    have h8nn : 0 ≤ (8 : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
    have htnn : 0 ≤ (3 : ℝ) ^ (-((d : ℝ) / (2 * 8) * ((Kc - m : ℕ) : ℝ))) :=
      Real.rpow_nonneg (by norm_num) _
    calc Cv * (8 : ℝ) ^ ((1 : ℝ) / 2) * (h : ℝ) ^ ((1 : ℝ) / 2) *
          (3 : ℝ) ^ (-((d : ℝ) / (2 * 8) * ((Kc - m : ℕ) : ℝ)))
        ≤ |Cv| * 3 * (h : ℝ) ^ ((1 : ℝ) / 2) * 1 := by
          gcongr
          · exact le_abs_self Cv
        _ ≤ (|Cv| + 1) * 3 * (h : ℝ) ^ ((1 : ℝ) / 2) := by
          rw [mul_one]; gcongr; linarith only
  set c : ℝ := |Cv| * (h : ℝ) ^ ((1 : ℝ) / 2) with hc
  have hcnn : 0 ≤ c := by positivity
  refine ⟨fun omega => ENNReal.ofReal (c + |X omega|), ?_, ?_, ?_⟩
  · exact ENNReal.measurable_ofReal.comp (measurable_const.add (continuous_abs.measurable.comp hXm))
  · intro omega
    refine (hXle omega).trans (ENNReal.ofReal_le_ofReal ?_)
    have : Cv * (h : ℝ) ^ ((1 : ℝ) / 2) ≤ c :=
      mul_le_mul_of_nonneg_right (le_abs_self Cv) hhpos.le
    linarith only [this, le_abs_self (X omega)]
  · have hq : (8 : ℝ≥0∞) ≠ 0 := by norm_num
    have hqt : (8 : ℝ≥0∞) ≠ ⊤ := by norm_num
    have hZm : Measurable (fun omega => c + |X omega|) :=
      measurable_const.add (continuous_abs.measurable.comp hXm)
    have hnorm := eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := P.toMeasure) hq hqt
      hZm.aestronglyMeasurable
    have hb := eLpNorm_eight_const_add_abs_le hA hcnn hXm hXO'
    have h8r : ((8 : ℝ≥0∞).toReal) = 8 := by norm_num
    rw [h8r] at hnorm
    have hl : ∫⁻ omega, ENNReal.ofReal (c + |X omega|) ^ (8 : ℕ) ∂P.toMeasure =
        (∫⁻ omega, ‖c + |X omega|‖ₑ ^ (8 : ℝ) ∂P.toMeasure) := by
      refine lintegral_congr fun omega => ?_
      rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (add_nonneg hcnn (abs_nonneg _)),
        ← ENNReal.rpow_natCast]
      norm_num
    rw [hl]
    have hpow : (∫⁻ omega, ‖c + |X omega|‖ₑ ^ (8 : ℝ) ∂P.toMeasure) =
        eLpNorm (fun omega => c + |X omega|) 8 P.toMeasure ^ (8 : ℝ) := by
      rw [hnorm, ← ENNReal.rpow_mul]
      norm_num
    rw [hpow]
    have e8 : ENNReal.ofReal ((7 * |Cv| + 6) * (h : ℝ) ^ ((1 : ℝ) / 2)) ^ (8 : ℕ) =
        ENNReal.ofReal ((7 * |Cv| + 6) * (h : ℝ) ^ ((1 : ℝ) / 2)) ^ (8 : ℝ) := by
      rw [← ENNReal.rpow_natCast]; norm_num
    rw [e8]
    have : c + 2 * ((|Cv| + 1) * 3 * (h : ℝ) ^ ((1 : ℝ) / 2)) =
        (7 * |Cv| + 6) * (h : ℝ) ^ ((1 : ℝ) / 2) := by rw [hc]; ring
    rw [this] at hb
    exact ENNReal.rpow_le_rpow hb (by norm_num)

end SuperdiffusionCLT.Section5
