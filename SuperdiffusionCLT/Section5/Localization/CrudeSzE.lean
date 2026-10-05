/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Localization.CrudeSzD
public import SuperdiffusionCLT.Section5.Response.GradientL8

/-!
# The `L̲⁸` moment of the shell flux

`E[‖hshell‖⁸_{L̲⁸(cu_K)}]^{1/8} ≤ C shom_{m-h}^{-1} h^{1/2}`, the shell term of
`e.crude.Sz.bound` (the `L^p` clause `e.kmn.Lp` of `l.stream.increment` at `p = 8`).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)
open scoped ENNReal
open scoped Matrix.Norms.L2Operator

variable {d : ℕ}

/-- The `L⁸(P; L̲⁸(cu_K))` moment of the shell increment `k_m - k_{m-h}`. -/
theorem shell_increment_L8 (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
        ∀ (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          ∀ m h Kc : ℕ, 1 ≤ h → 400 * h ≤ m → 100 * m ≤ Kc →
          ∃ Wm : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ≥0∞, Measurable Wm ∧
            (∀ omega, (SuperdiffusionCLT.Section2.Norms.cubeLpENorm
                (originCube d (Kc : ℤ)) 8
                (fun x => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega (m - h) m x))
                ^ (8 : ℕ) ≤ Wm omega) ∧
            ∫⁻ omega, Wm omega ∂P.toMeasure ≤ ENNReal.ofReal (C * (h : ℝ) ^ ((1 : ℝ) / 2)) ^ (8 : ℕ) := by
  obtain ⟨C₂, hV⟩ := SuperdiffusionCLT.Frozen.Section2.streamIncrement_scale_estimates d
  obtain ⟨C₀, C₁, hV2⟩ := hV (1 / 2) (by norm_num) (by norm_num)
  obtain ⟨Cv, hV3⟩ := hV2 8 (by norm_num)
  refine ⟨max 1 ((|Cv| + 1) * 3 * 2 + |Cv|), le_max_left _ _, ?_⟩
  intro nu hnu hnu1 P hPre hJ2 hJ3 hJ1 hJ4 m h Kc hh h400 h100
  have hV4 := hV3 P hPre hJ1 hJ2 hJ3 hJ4
  have hnm : m - h < m := by omega
  have hmK : m ≤ Kc := by omega
  obtain ⟨X, hXm, hXO, hXle⟩ := (hV4.1 Kc m (m - h) hnm hmK).2.1
  have hhm : m - (m - h) = h := by omega
  rw [hhm] at hXO hXle
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
  have hpt : ∀ omega,
      SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (Kc : ℤ)) 8
          (fun x => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega (m - h) m x) ≤
      ENNReal.ofReal (c + |X omega|) := by
    intro omega
    refine (hXle omega).trans (ENNReal.ofReal_le_ofReal ?_)
    have : Cv * (h : ℝ) ^ ((1 : ℝ) / 2) ≤ c :=
      mul_le_mul_of_nonneg_right (le_abs_self Cv) hhpos.le
    linarith only [this, le_abs_self (X omega)]
  have hZnn : ∀ omega, 0 ≤ c + |X omega| := fun omega => add_nonneg hcnn (abs_nonneg _)
  have hq : (8 : ℝ≥0∞) ≠ 0 := by norm_num
  have hqt : (8 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hZm : Measurable (fun omega => c + |X omega|) :=
    measurable_const.add (continuous_abs.measurable.comp hXm)
  refine ⟨fun omega => ENNReal.ofReal (c + |X omega|) ^ (8 : ℕ),
    (ENNReal.measurable_ofReal.comp hZm).pow_const 8,
    fun omega => pow_le_pow_left' (hpt omega) 8, ?_⟩
  have hint : ∫⁻ omega, ENNReal.ofReal (c + |X omega|) ^ (8 : ℕ) ∂P.toMeasure =
      ∫⁻ omega, ‖c + |X omega|‖ₑ ^ ((8 : ℝ≥0∞).toReal) ∂P.toMeasure := by
    refine lintegral_congr fun omega => ?_
    have h8r : ((8 : ℝ≥0∞).toReal) = ((8 : ℕ) : ℝ) := by norm_num
    rw [h8r, ENNReal.rpow_natCast, Real.enorm_eq_ofReal (hZnn omega)]
  have hnorm : (∫⁻ omega, ‖c + |X omega|‖ₑ ^ ((8 : ℝ≥0∞).toReal) ∂P.toMeasure) ^
      (1 / (8 : ℝ≥0∞).toReal) = eLpNorm (fun omega => c + |X omega|) 8 P.toMeasure :=
    (eLpNorm_eq_lintegral_rpow_enorm_toReal hq hqt hZm.aestronglyMeasurable).symm
  have hbound : eLpNorm (fun omega => c + |X omega|) 8 P.toMeasure ≤
      ENNReal.ofReal (max 1 ((|Cv| + 1) * 3 * 2 + |Cv|) * (h : ℝ) ^ ((1 : ℝ) / 2)) := by
    refine (eLpNorm_eight_const_add_abs_le hA hcnn hXm hXO').trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have heq : c + 2 * ((|Cv| + 1) * 3 * (h : ℝ) ^ ((1 : ℝ) / 2)) =
        ((|Cv| + 1) * 3 * 2 + |Cv|) * (h : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [hc]; ring
    rw [heq]
    gcongr
    exact le_max_right _ _
  rw [hint]
  have h8' : (∫⁻ omega, ‖c + |X omega|‖ₑ ^ ((8 : ℝ≥0∞).toReal) ∂P.toMeasure) =
      eLpNorm (fun omega => c + |X omega|) 8 P.toMeasure ^ (8 : ℕ) := by
    rw [← hnorm, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    have : (1 / (8 : ℝ≥0∞).toReal) * ((8 : ℕ) : ℝ) = 1 := by norm_num
    rw [this, ENNReal.rpow_one]
  rw [h8']
  exact pow_le_pow_left' hbound 8

end SuperdiffusionCLT.Section5
