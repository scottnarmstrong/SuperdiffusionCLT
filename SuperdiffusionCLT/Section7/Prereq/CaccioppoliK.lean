/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.CaccioppoliJ

@[expose] public section

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Carriers
open scoped ENNReal

variable {d : ℕ}

namespace SuperdiffusionCLT.Section7

theorem ca1w_master_conv {ν : ℝ} {m n : ℕ} (hν : 0 < ν)
    (h : (m : ℝ) ^ (4 : ℝ) * ν ^ (-(4 : ℝ)) * (1 : ℝ) ^ (4 : ℝ) *
        (3 : ℝ) ^ ((1 : ℝ) * (((n : ℤ) : ℝ) - (m : ℝ))) ≤ ((m : ℝ) ^ 1)⁻¹) :
    (3 : ℝ) ^ (n : ℤ) / (3 : ℝ) ^ (m : ℤ) * ((m : ℝ) / ν) ^ 4 ≤ (m : ℝ)⁻¹ := by
  have e1 : (m : ℝ) ^ (4 : ℝ) = (m : ℝ) ^ 4 := by exact_mod_cast Real.rpow_natCast (m : ℝ) 4
  have e2 : ν ^ (-(4 : ℝ)) = (ν ^ 4)⁻¹ := by
    rw [Real.rpow_neg hν.le]; congr 1; exact_mod_cast Real.rpow_natCast ν 4
  have e3 : (3 : ℝ) ^ ((1 : ℝ) * (((n : ℤ) : ℝ) - (m : ℝ))) = (3 : ℝ) ^ (n : ℤ) / (3 : ℝ) ^ (m : ℤ) := by
    rw [one_mul, Real.rpow_sub (by norm_num), Real.rpow_intCast]
    congr 1
    exact_mod_cast Real.rpow_natCast (3 : ℝ) m
  rw [e1, e2, e3, Real.one_rpow, pow_one, mul_one] at h
  have e4 : ((m : ℝ) / ν) ^ 4 = (m : ℝ) ^ 4 * (ν ^ 4)⁻¹ := by
    rw [div_pow, div_eq_mul_inv]
  rw [e4]
  calc (3 : ℝ) ^ (n : ℤ) / (3 : ℝ) ^ (m : ℤ) * ((m : ℝ) ^ 4 * (ν ^ 4)⁻¹)
      = (m : ℝ) ^ 4 * (ν ^ 4)⁻¹ * ((3 : ℝ) ^ (n : ℤ) / (3 : ℝ) ^ (m : ℤ)) := by ring
    _ ≤ _ := h

/-- Almost surely the centered stream field of the translated sample is continuous on the whole space. -/
theorem ca1w_ae_continuous [NeZero d] {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (nu : ℝ)
    (y : Vec d) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure, ∀ m : ℕ,
      Continuous (fun x => centeredStreamField (ShellField.translateSequence y omega)
        (cubeSet (originCube d (m : ℤ))) x) := by
  have hbase : ∀ᵐ omega : ShellSeq d ∂P.toMeasure, ∀ m : ℕ,
      Continuous (fun x => centeredStreamField omega (cubeSet (originCube d (m : ℤ))) x) := by
    filter_upwards [Section6.ae_continuous_fullStreamRecentered hJ3,
      Section6.ae_centered_eq_recentered_add_skew hJ3 nu] with omega hc hb m
    obtain ⟨K, -, hK⟩ := hb m
    have hfun : (fun x => nu • (1 : Mat d) +
        centeredStreamField omega (cubeSet (originCube d (m : ℤ))) x) =
        fun x => Section6.fullCoefficientRecentered nu omega x + K := funext hK
    have h1 : Continuous fun x => nu • (1 : Mat d) +
        centeredStreamField omega (cubeSet (originCube d (m : ℤ))) x := by
      rw [hfun]
      exact (Section6.continuous_fullCoefficientRecentered hc).add continuous_const
    have h2 : Continuous fun x => (nu • (1 : Mat d) +
        centeredStreamField omega (cubeSet (originCube d (m : ℤ))) x) - nu • (1 : Mat d) :=
      h1.sub continuous_const
    simpa only [add_sub_cancel_left] using h2
  exact (translateSequence_measurePreserving hPrefix hJ2 y).quasiMeasurePreserving.ae hbase

end SuperdiffusionCLT.Section7
