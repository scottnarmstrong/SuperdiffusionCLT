/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.FieldProcessInputB

/-!
# Logarithmic-growth bounds of a localized split datum

The tail estimates of the whole-space exhaustion read a localized split datum only through three
families of constants: the rough bound, the smooth divergence bound and the freezing radius.
`LogGrowthBounds` records that these are given by the displayed logarithmic and algebraic
formulas, with explicit constants.  The marginal split datum (`FieldInputData.splitData`)
satisfies it with vanishing rough constant, the divergence constant `3 G` and the freezing
exponent one.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization Homogenization.Book.Ch02 MeasureTheory Filter Topology
open SuperdiffusionCLT.Section8.Common.Regularity.Ported
open scoped Matrix.Norms.Elementwise

noncomputable section

/-- Logarithmic bounds of the local constants of a split datum.  The rough and divergence
bounds are the logarithmic weight of the observation radius times a constant; the freezing
radius is a power of an amplitude over `1 + |x|`; the Holder exponent and the contrast level are
the fixed ones of the localized tail. -/
structure LogGrowthBounds {d : ℕ} [NeZero d] {A : DivergenceForm.WholeSpaceAnalyticData d}
    (L : DivergenceForm.WholeSpaceLocalizedSplitData A) where
  cs : ℝ
  cg : ℝ
  cs_nonneg : 0 ≤ cs
  cg_nonneg : 0 ≤ cg
  amp : ℝ
  amp_pos : 0 < amp
  amp_le_one : amp ≤ 1
  expo : ℝ
  expo_pos : 0 < expo
  holder_eq : L.holderExponent = 1 / 2
  delta_eq : L.delta = smallContrastThreshold d (1 / 2 : ℝ)
  rough_eq : ∀ (x : Vec d) (r : ℝ),
    L.roughBound x r = cs * fieldInput_logWeight (fieldInput_obsRadius x r)
  smooth_eq : ∀ (x : Vec d) (r : ℝ),
    L.smoothDivBound x r =
      Real.sqrt d * (d : ℝ) * cg * fieldInput_logWeight (fieldInput_obsRadius x r)
  freeze_eq : ∀ x : Vec d,
    L.freezingRadius x = Real.rpow (amp / (1 + euclideanNorm x)) expo

variable {d : ℕ} [NeZero d] {nu : ℝ} {k : Vec d → Mat d}

/-- **The marginal split datum has logarithmic-growth bounds**, with rough constant `0`,
divergence constant `3 G` and freezing exponent `1`. -/
def FieldInputData.logGrowthBounds (D : FieldInputData d nu k) :
    LogGrowthBounds D.splitData where
  cs := 0
  cg := 3 * D.gradConst
  cs_nonneg := le_rfl
  cg_nonneg := mul_nonneg (by norm_num) D.gradConst_nonneg
  amp := D.freezingAmplitude (smallContrastThreshold d (1 / 2 : ℝ))
  amp_pos := D.freezingAmplitude_pos (fieldInput_smallContrastThreshold_half_pos d)
  amp_le_one := D.freezingAmplitude_le_one _
  expo := 1
  expo_pos := one_pos
  holder_eq := rfl
  delta_eq := rfl
  rough_eq := fun x r => by
    rw [FieldInputData.splitData_roughBound, zero_mul]
  smooth_eq := fun x r => rfl
  freeze_eq := fun x => by
    rw [FieldInputData.splitData_freezingRadius]
    unfold FieldInputData.freezingRadius
    exact (Real.rpow_one _).symm

/-- The bounds are satisfiable for a concrete skew field, the zero field. -/
example (hd : 2 ≤ d) :
    ∃ D : FieldInputData d 1 (fun _ : Vec d => (0 : Mat d)),
      D.logGrowthBounds.cs = 0 ∧ D.logGrowthBounds.cg = 0 :=
  ⟨{ two_le := hd
     nu_pos := one_pos
     skew := fun _ => by simp [matTranspose]
     contDiff := contDiff_const
     gradConst := 0
     gradConst_nonneg := le_rfl
     grad_le := fun y => by simp }, rfl, by simp [FieldInputData.logGrowthBounds]⟩

end

end SuperdiffusionCLT.Section8
