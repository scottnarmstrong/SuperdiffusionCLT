/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.FieldProcessInputF

/-!
# Uniform exhaustion budgets

The shift-uniform profile has a finite cubic layer-cake budget.  Its cubic-log cutoff also has an
explicit subpolynomial growth bound for exponents strictly between one and two.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization Homogenization.Book.Ch02 MeasureTheory Set
open SuperdiffusionCLT.Section8.DivergenceForm

noncomputable section

variable {d : ℕ} [NeZero d] {A : WholeSpaceAnalyticData d} {Sp : WholeSpaceLocalizedSplitData A}

namespace LogGrowthBounds

/-- The uniform cubic layer-cake budget. -/
def uniformBudget (T : LogGrowthBounds Sp) : ℝ :=
  (∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal
    (uniformEnvelope T s * s ^ 3)).toReal

/-- The explicit constant in the subpolynomial cutoff-growth estimate. -/
def uniformGrowth (T : LogGrowthBounds Sp) (q : ℝ) : ℝ :=
  if 1 < q ∧ q < 2 then
    uniformScale T ^ 12 *
      (1 + 12 / (2 - q)) ^ 12
  else 0

private theorem uniformRate_pos (T : LogGrowthBounds Sp) :
    0 < uniformRate T := by
  unfold uniformRate
  exact div_pos (decayConst_pos T) (by norm_num)

private theorem uniformScale_pos (T : LogGrowthBounds Sp) :
    0 < uniformScale T := by
  unfold uniformScale
  have hp : 0 < amplitudeExponent T := by
    unfold amplitudeExponent
    have he := T.expo_pos
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hprod := mul_nonneg hd he.le
    linarith only [hprod]
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hc := decayConst_pos T
  have hnum : 0 < 1 + amplitudeExponent T + (d : ℝ) + 1 := by
    linarith only [hp, hd]
  have hterm : 0 < 100000 *
      (1 + amplitudeExponent T + (d : ℝ) + 1) /
        decayConst T := by positivity
  linarith only [hterm]

private theorem one_le_uniformScale (T : LogGrowthBounds Sp) :
    1 ≤ uniformScale T := by
  unfold uniformScale
  have hp : 0 < amplitudeExponent T := by
    unfold amplitudeExponent
    have he := T.expo_pos
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hprod := mul_nonneg hd he.le
    linarith only [hprod]
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hc := decayConst_pos T
  have hterm : 0 ≤ 100000 *
      (1 + amplitudeExponent T + (d : ℝ) + 1) /
        decayConst T := by positivity
  linarith only [hterm]

private theorem one_le_uniformShiftWeight (lam : ℝ) :
    1 ≤ fieldInput_uniformShiftWeight lam := by
  unfold fieldInput_uniformShiftWeight
  have hmax : (1 : ℝ) ≤ max lam 1 := le_max_right _ _
  exact le_add_of_nonneg_right (Real.log_nonneg hmax)

private theorem continuous_uniformEnvelope
    (T : LogGrowthBounds Sp) :
    Continuous (uniformEnvelope T) := by
  unfold uniformEnvelope
  have hmax : Continuous (fun s : ℝ ↦ max s 0) :=
    continuous_id.max continuous_const
  have hroot : Continuous (fun s : ℝ ↦ (max s 0) ^ (1 / 3 : ℝ)) :=
    hmax.rpow_const (fun _ ↦ Or.inr (show (0 : ℝ) ≤ 1 / 3 by norm_num))
  have harg : Continuous (fun s : ℝ ↦
      -(uniformRate T * (max s 0) ^ (1 / 3 : ℝ))) :=
    (continuous_const.mul hroot).neg
  exact continuous_const.mul harg.rexp

private theorem integrableOn_uniformEnvelope_mul_cube
    (T : LogGrowthBounds Sp) :
    IntegrableOn
      (fun s : ℝ ↦ uniformEnvelope T s * s ^ 3)
      (Ioi 1) := by
  let A := amplitudeConst T
  let b := uniformRate T
  have hb : 0 < b := uniformRate_pos T
  have hbase : IntegrableOn
      (fun s : ℝ ↦ s ^ (3 : ℝ) * Real.exp (-b * s ^ (1 / 3 : ℝ)))
      (Ioi 0) := by
    rw [← integrableOn_Ioi_comp_rpow_iff'
      (fun s : ℝ ↦ s ^ (3 : ℝ) * Real.exp (-b * s ^ (1 / 3 : ℝ)))
      (show (3 : ℝ) ≠ 0 by norm_num)]
    have hmajor : IntegrableOn
        (fun x : ℝ ↦ x ^ (11 : ℝ) * Real.exp (-b * x ^ (1 : ℝ)))
        (Ioi 0) := integrableOn_rpow_mul_exp_neg_mul_rpow
          (s := (11 : ℝ)) (p := (1 : ℝ)) (by norm_num) (by norm_num) hb
    refine hmajor.congr_fun ?_ measurableSet_Ioi
    intro x hx
    have hx0 : 0 ≤ x := hx.le
    have hroot : (x ^ (3 : ℝ)) ^ (1 / 3 : ℝ) = x := by
      rw [← Real.rpow_mul hx0, show (3 : ℝ) * (1 / 3 : ℝ) = 1 by norm_num,
        Real.rpow_one]
    change x ^ (11 : ℝ) * Real.exp (-b * x ^ (1 : ℝ)) =
      x ^ ((3 : ℝ) - 1) *
        ((x ^ (3 : ℝ)) ^ (3 : ℝ) *
          Real.exp (-b * (x ^ (3 : ℝ)) ^ (1 / 3 : ℝ)))
    rw [hroot, show (3 : ℝ) - 1 = 2 by norm_num, Real.rpow_one]
    rw [← Real.rpow_mul hx0]
    rw [show x ^ (2 : ℝ) * (x ^ ((3 : ℝ) * 3) * Real.exp (-b * x)) =
      (x ^ (2 : ℝ) * x ^ ((3 : ℝ) * 3)) * Real.exp (-b * x) by ring]
    rw [← Real.rpow_add hx, show (2 : ℝ) + 3 * 3 = 11 by norm_num]
  have hrestricted : IntegrableOn
      (fun s : ℝ ↦ A * (s ^ (3 : ℝ) * Real.exp (-b * s ^ (1 / 3 : ℝ))))
      (Ioi 1) := IntegrableOn.mono_set (hbase.const_mul A)
    (show Ioi (1 : ℝ) ⊆ Ioi 0 by
      intro s hs
      exact zero_lt_one.trans (show 1 < s from hs))
  refine hrestricted.congr_fun ?_ measurableSet_Ioi
  intro s hs
  have hs0 : 0 ≤ s := (zero_lt_one.trans (show 1 < s from hs)).le
  dsimp only [A, b]
  unfold uniformEnvelope
  rw [max_eq_left hs0]
  change amplitudeConst T *
      (Real.rpow s ((3 : ℕ) : ℝ) * Real.exp
        (-uniformRate T * s ^ (1 / 3 : ℝ))) =
    amplitudeConst T *
      Real.exp (-(uniformRate T * s ^ (1 / 3 : ℝ))) * s ^ 3
  have hpoweq : Real.rpow s ((3 : ℕ) : ℝ) = s ^ (3 : ℕ) :=
    Real.rpow_natCast s 3
  rw [hpoweq]
  ring_nf

/-- The displayed uniform budget is nonnegative. -/
theorem uniformBudget_nonneg (T : LogGrowthBounds Sp) :
    0 ≤ uniformBudget T :=
  ENNReal.toReal_nonneg

/-- Above the cutting radius, the cubic layer-cake integral is bounded by the
shift-independent displayed budget. -/
theorem lintegral_uniformProfile_mul_cube_le
    (T : LogGrowthBounds Sp)
    {lam : ℝ} (hlam : 1 ≤ lam) :
    ∫⁻ s in Ioi (uniformCutoff T lam),
        ENNReal.ofReal (uniformProfile T lam s * s ^ 3) ≤
      ENNReal.ofReal (uniformBudget T) := by
  have hweight : 1 ≤ fieldInput_uniformShiftWeight lam := by
    unfold fieldInput_uniformShiftWeight
    rw [max_eq_left hlam]
    exact le_add_of_nonneg_right (Real.log_nonneg hlam)
  have hcut : 1 ≤ uniformCutoff T lam := by
    unfold uniformCutoff
    apply one_le_pow₀
    nlinarith only [one_le_uniformScale T, hweight]
  have hmono : Ioi (uniformCutoff T lam) ⊆ Ioi (1 : ℝ) := by
    intro s hs
    exact lt_of_le_of_lt hcut hs
  have hcont := (continuous_uniformEnvelope T).mul
    (continuous_id.pow 3)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (1 : ℝ))]
      fun s : ℝ ↦ uniformEnvelope T s * s ^ 3 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact mul_nonneg
      (mul_nonneg (amplitudeConst_nonneg T) (Real.exp_pos _).le)
      (pow_nonneg (le_of_lt (zero_lt_one.trans hs)) 3)
  have hne : (∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal
      (uniformEnvelope T s * s ^ 3)) ≠ ⊤ :=
    (lintegral_ofReal_ne_top_iff_integrable hcont.aestronglyMeasurable hnonneg).2
      (integrableOn_uniformEnvelope_mul_cube T)
  calc
    ∫⁻ s in Ioi (uniformCutoff T lam),
        ENNReal.ofReal (uniformProfile T lam s * s ^ 3) =
        ∫⁻ s in Ioi (uniformCutoff T lam),
          ENNReal.ofReal (uniformEnvelope T s * s ^ 3) := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro s hs
      unfold uniformProfile
      change ENNReal.ofReal
        ((if uniformCutoff T lam < s then
          uniformEnvelope T s else 1) * s ^ 3) = _
      simp only [show uniformCutoff T lam < s from hs, ↓reduceIte]
    _ ≤ ∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal
          (uniformEnvelope T s * s ^ 3) :=
      lintegral_mono_set hmono
    _ = ENNReal.ofReal (uniformBudget T) := by
      unfold uniformBudget
      rw [ENNReal.ofReal_toReal hne]

/-- The cutoff-growth coefficient is nonnegative in the admissible exponent
range. -/
theorem uniformGrowth_nonneg (T : LogGrowthBounds Sp) {q : ℝ} (hq1 : 1 < q) (hq2 : q < 2) :
    0 ≤ uniformGrowth T q := by
  unfold uniformGrowth
  simp only [show 1 < q ∧ q < 2 from ⟨hq1, hq2⟩]
  exact mul_nonneg (pow_nonneg (uniformScale_pos T).le _)
    (pow_nonneg (by have : 0 < 2 - q := sub_pos.mpr hq2; positivity) _)

/-- The fourth power of the cubic-log cutoff is subpolynomial in the shift,
with an explicit coefficient for every fixed exponent `q ∈ (1,2)`. -/
theorem uniformCutoff_pow_le
    (T : LogGrowthBounds Sp)
    {q : ℝ} (hq1 : 1 < q) (hq2 : q < 2)
    {lam : ℝ} (hlam : 1 ≤ lam) :
    uniformCutoff T lam ^ 4 ≤
      uniformGrowth T q * lam ^ (2 - q) := by
  let eps : ℝ := (2 - q) / 12
  let C : ℝ := 1 + 12 / (2 - q)
  have heps : 0 < eps := by
    unfold eps
    exact div_pos (sub_pos.mpr hq2) (by norm_num)
  have hlam0 : 0 ≤ lam := zero_le_one.trans hlam
  have hlamPos : 0 < lam := zero_lt_one.trans_le hlam
  have hpowOne : 1 ≤ lam ^ eps := Real.one_le_rpow hlam heps.le
  have hlog := Real.log_le_rpow_div hlam0 heps
  have hweight : fieldInput_uniformShiftWeight lam ≤ C * lam ^ eps := by
    unfold fieldInput_uniformShiftWeight C eps
    rw [max_eq_left hlam]
    have hfactor : lam ^ ((2 - q) / 12) / ((2 - q) / 12) =
        lam ^ ((2 - q) / 12) * (12 / (2 - q)) := by
      field_simp [ne_of_gt (sub_pos.mpr hq2)]
    change Real.log lam ≤ lam ^ ((2 - q) / 12) / ((2 - q) / 12) at hlog
    rw [hfactor] at hlog
    calc
      1 + Real.log lam ≤ 1 + (lam ^ ((2 - q) / 12)) *
          (12 / (2 - q)) := by linarith only [hlog]
      _ ≤ lam ^ ((2 - q) / 12) +
          (lam ^ ((2 - q) / 12)) * (12 / (2 - q)) := by
        linarith only [hpowOne]
      _ = (1 + 12 / (2 - q)) * lam ^ ((2 - q) / 12) := by ring
  have hweightPow := pow_le_pow_left₀
    (by exact zero_le_one.trans (one_le_uniformShiftWeight lam)) hweight 12
  have hpowIdentity : (lam ^ eps) ^ 12 = lam ^ (2 - q) := by
    rw [← Real.rpow_mul_natCast hlam0]
    congr 1
    unfold eps
    ring
  unfold uniformCutoff uniformGrowth
  simp only [show 1 < q ∧ q < 2 from ⟨hq1, hq2⟩]
  rw [← pow_mul, show 3 * 4 = 12 by norm_num, mul_pow]
  calc
    uniformScale T ^ 12 *
        fieldInput_uniformShiftWeight lam ^ 12 ≤
      uniformScale T ^ 12 * (C * lam ^ eps) ^ 12 :=
        mul_le_mul_of_nonneg_left hweightPow
          (pow_nonneg (uniformScale_pos T).le _)
    _ = uniformScale T ^ 12 * C ^ 12 * lam ^ (2 - q) := by
      rw [mul_pow, hpowIdentity]
      ring
    _ = uniformScale T ^ 12 *
        (1 + 12 / (2 - q)) ^ 12 * lam ^ (2 - q) := by rfl

end LogGrowthBounds

/-! ## Satisfiability witnesses -/

/-- The three conditions of the variable-exhaustion input hold for the marginal split datum at
the time exponent `3/2`, at every shift at least one. -/
example {nu : ℝ} {k : Vec d → Mat d} (D : FieldInputData d nu k) (lam : ℝ) (hlam : 1 ≤ lam) :
    0 ≤ D.logGrowthBounds.uniformBudget ∧
      (∫⁻ s in Ioi (D.logGrowthBounds.uniformCutoff lam),
        ENNReal.ofReal (D.logGrowthBounds.uniformProfile lam s * s ^ 3) ≤
          ENNReal.ofReal D.logGrowthBounds.uniformBudget) ∧
      D.logGrowthBounds.uniformCutoff lam ^ 4 ≤
        D.logGrowthBounds.uniformGrowth (3 / 2) * lam ^ (2 - (3 / 2 : ℝ)) :=
  ⟨D.logGrowthBounds.uniformBudget_nonneg, D.logGrowthBounds.lintegral_uniformProfile_mul_cube_le hlam,
    D.logGrowthBounds.uniformCutoff_pow_le (by norm_num) (by norm_num) hlam⟩

end

end SuperdiffusionCLT.Section8
