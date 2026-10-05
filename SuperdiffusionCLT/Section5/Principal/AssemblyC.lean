/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Principal.AssemblyB
public import SuperdiffusionCLT.Section5.Localization.CrudeSzC

/-!
# The averaged Cauchy-Schwarz step of `lem.principal.term`

`pa_avg_chain`: from the per-cube bounds `E[a_Q] ≤ (1+ε) E[(1+D'_Q) L_Q]` and the two averaged moment
bounds `avg E[D'^4] ≤ F`, `avg E[L²] ≤ B`, the averaged inequality
`avg E[a_Q] ≤ (1+ε) avg E[L_Q] + (1+ε)(M³ F + 1/(16M) + B/(2M))` (Young's inequality
`pa_young_dL` replaces the printed Cauchy-Schwarz and Jensen steps).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open MeasureTheory Homogenization
open scoped ENNReal

variable {d : ℕ}

theorem pa_subcubeAvg_mono_on {Kc n : ℕ} {f g : TriadicCube d → ℝ≥0∞}
    (h : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ), f Q ≤ g Q) :
    subcubeAvg Kc n f ≤ subcubeAvg Kc n g := by
  unfold subcubeAvg
  exact mul_le_mul' le_rfl (Finset.sum_le_sum h)

/-- One cube: `E[(1+D) L] ≤ E[L] + M³ E[D⁴] + 1/(16M) + E[L²]/(2M)`. -/
theorem pa_cube_split {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {D L : Ω → ℝ} (hD : Measurable D) (hL : Measurable L) (hD0 : ∀ ω, 0 ≤ D ω)
    (hL0 : ∀ ω, 0 ≤ L ω) {M : ℝ} (hM : 0 < M) :
    ∫⁻ ω, ENNReal.ofReal ((1 + D ω) * L ω) ∂μ ≤
      ∫⁻ ω, ENNReal.ofReal (L ω) ∂μ + ENNReal.ofReal (M ^ 3) * ∫⁻ ω, ENNReal.ofReal (D ω ^ 4) ∂μ +
        ENNReal.ofReal (1 / (16 * M)) + ENNReal.ofReal (1 / (2 * M)) *
          ∫⁻ ω, ENNReal.ofReal (L ω ^ 2) ∂μ := by
  have hpt : ∀ ω, ENNReal.ofReal ((1 + D ω) * L ω) ≤
      ENNReal.ofReal (L ω) + (ENNReal.ofReal (M ^ 3) * ENNReal.ofReal (D ω ^ 4) +
        (ENNReal.ofReal (1 / (16 * M)) +
          ENNReal.ofReal (1 / (2 * M)) * ENNReal.ofReal (L ω ^ 2))) := by
    intro ω
    have hy := pa_young_dL (x := D ω) (y := L ω) hM
    have hD0' := hD0 ω
    have hL0' := hL0 ω
    have h1 : (1 + D ω) * L ω ≤ L ω + (M ^ 3 * D ω ^ 4 + (1 / (16 * M) + 1 / (2 * M) * L ω ^ 2)) := by
      have : 1 / (2 * M) * L ω ^ 2 = L ω ^ 2 / (2 * M) := by ring
      rw [this]
      linarith only [hy]
    refine (ENNReal.ofReal_le_ofReal h1).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_add hL0' (by positivity), ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity)]
  refine (lintegral_mono hpt).trans (le_of_eq ?_)
  have hm1 : Measurable fun ω => ENNReal.ofReal (L ω) := hL.ennreal_ofReal
  have hm2 : Measurable fun ω => ENNReal.ofReal (M ^ 3) * ENNReal.ofReal (D ω ^ 4) :=
    (hD.pow_const 4).ennreal_ofReal.const_mul _
  have hm3 : Measurable fun ω => ENNReal.ofReal (1 / (16 * M)) +
      ENNReal.ofReal (1 / (2 * M)) * ENNReal.ofReal (L ω ^ 2) :=
    measurable_const.add ((hL.pow_const 2).ennreal_ofReal.const_mul _)
  rw [lintegral_add_left hm1, lintegral_add_left hm2, lintegral_add_left measurable_const,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const, measure_univ, mul_one]
  ring

/-- **The averaged step.** -/
theorem pa_avg_chain {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Kc n : ℕ} (hn : n ≤ Kc) {a D L : TriadicCube d → Ω → ℝ} {ε F B M : ℝ} (hε : 0 ≤ ε)
    (hM : 0 < M) (hF0 : 0 ≤ F) (hB0 : 0 ≤ B)
    (hD : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ), Measurable (D Q))
    (hL : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ), Measurable (L Q))
    (hD0 : ∀ Q ω, 0 ≤ D Q ω) (hL0 : ∀ Q ω, 0 ≤ L Q ω)
    (hq : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
      ∫⁻ ω, ENNReal.ofReal (a Q ω) ∂μ ≤
        ENNReal.ofReal (1 + ε) * ∫⁻ ω, ENNReal.ofReal ((1 + D Q ω) * L Q ω) ∂μ)
    (hF : subcubeAvg Kc n (fun Q => ∫⁻ ω, ENNReal.ofReal (D Q ω ^ 4) ∂μ) ≤ ENNReal.ofReal F)
    (hB : subcubeAvg Kc n (fun Q => ∫⁻ ω, ENNReal.ofReal (L Q ω ^ 2) ∂μ) ≤ ENNReal.ofReal B) :
    subcubeAvg Kc n (fun Q => ∫⁻ ω, ENNReal.ofReal (a Q ω) ∂μ) ≤
      ENNReal.ofReal (1 + ε) * subcubeAvg Kc n (fun Q => ∫⁻ ω, ENNReal.ofReal (L Q ω) ∂μ) +
        ENNReal.ofReal ((1 + ε) * (M ^ 3 * F + 1 / (16 * M) + B / (2 * M))) := by
  have h1 : subcubeAvg Kc n (fun Q => ∫⁻ ω, ENNReal.ofReal (a Q ω) ∂μ) ≤
      subcubeAvg Kc n (fun Q => ENNReal.ofReal (1 + ε) *
        (∫⁻ ω, ENNReal.ofReal (L Q ω) ∂μ + ENNReal.ofReal (M ^ 3) *
          ∫⁻ ω, ENNReal.ofReal (D Q ω ^ 4) ∂μ + ENNReal.ofReal (1 / (16 * M)) +
          ENNReal.ofReal (1 / (2 * M)) * ∫⁻ ω, ENNReal.ofReal (L Q ω ^ 2) ∂μ)) := by
    refine pa_subcubeAvg_mono_on fun Q hQ => (hq Q hQ).trans ?_
    exact mul_le_mul' le_rfl (pa_cube_split (hD Q hQ) (hL Q hQ) (hD0 Q) (hL0 Q) hM)
  refine h1.trans ?_
  rw [subcubeAvg_const_mul, subcubeAvg_add, subcubeAvg_add, subcubeAvg_add,
    subcubeAvg_const_mul, subcubeAvg_const hn, subcubeAvg_const_mul]
  have hB' : ENNReal.ofReal (1 / (2 * M)) *
      subcubeAvg Kc n (fun Q => ∫⁻ ω, ENNReal.ofReal (L Q ω ^ 2) ∂μ) ≤
      ENNReal.ofReal (1 / (2 * M)) * ENNReal.ofReal B := mul_le_mul' le_rfl hB
  have hF' : ENNReal.ofReal (M ^ 3) *
      subcubeAvg Kc n (fun Q => ∫⁻ ω, ENNReal.ofReal (D Q ω ^ 4) ∂μ) ≤
      ENNReal.ofReal (M ^ 3) * ENNReal.ofReal F := mul_le_mul' le_rfl hF
  have hs1 : ENNReal.ofReal (M ^ 3 * F + 1 / (16 * M) + 1 / (2 * M) * B) =
      ENNReal.ofReal (M ^ 3) * ENNReal.ofReal F + ENNReal.ofReal (1 / (16 * M)) +
        ENNReal.ofReal (1 / (2 * M)) * ENNReal.ofReal B := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity)]
  have e1 : ENNReal.ofReal ((1 + ε) * (M ^ 3 * F + 1 / (16 * M) + B / (2 * M))) =
      ENNReal.ofReal (1 + ε) * (ENNReal.ofReal (M ^ 3) * ENNReal.ofReal F +
        ENNReal.ofReal (1 / (16 * M)) + ENNReal.ofReal (1 / (2 * M)) * ENNReal.ofReal B) := by
    have : B / (2 * M) = 1 / (2 * M) * B := by ring
    rw [this, ENNReal.ofReal_mul (by linarith only [hε]), hs1]
  rw [e1]
  set X := subcubeAvg Kc n (fun Q => ∫⁻ ω, ENNReal.ofReal (L Q ω) ∂μ)
  set Y := subcubeAvg Kc n (fun Q => ∫⁻ ω, ENNReal.ofReal (D Q ω ^ 4) ∂μ)
  set Z := subcubeAvg Kc n (fun Q => ∫⁻ ω, ENNReal.ofReal (L Q ω ^ 2) ∂μ)
  calc ENNReal.ofReal (1 + ε) * (X + ENNReal.ofReal (M ^ 3) * Y +
          ENNReal.ofReal (1 / (16 * M)) + ENNReal.ofReal (1 / (2 * M)) * Z)
      = ENNReal.ofReal (1 + ε) * X + ENNReal.ofReal (1 + ε) *
          (ENNReal.ofReal (M ^ 3) * Y + ENNReal.ofReal (1 / (16 * M)) +
            ENNReal.ofReal (1 / (2 * M)) * Z) := by ring
    _ ≤ _ := by
        gcongr

end SuperdiffusionCLT.Section5
