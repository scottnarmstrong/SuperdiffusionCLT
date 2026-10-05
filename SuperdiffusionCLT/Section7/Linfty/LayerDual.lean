/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.L2AssemblyG
public import SuperdiffusionCLT.Section7.Prereq.LinftyReductionC

/-!
# The layer term in `W^{-1,p}` from a sup bound

The deterministic core of the layer estimate of the paper: the product of
the gradient of the cutoff with a field bounded on the layer, measured in the normalized dual
norm `W^{-1,p}(W)`, is controlled by the sup bound, the layer volume fraction to the power `1/p`
and the layer Poincare inequality at the conjugate exponent.
-/

@[expose] public section

open MeasureTheory Set Filter Homogenization
open scoped ENNReal NNReal Pointwise

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- A function bounded by `B` on a measurable `A ⊆ W` and cut off to `A` has normalized `L^p(W)`
norm at most `B (|A| / |W|)^{1/p}`. -/
theorem linf_lpBar_indicator_le {W A : Set (Vec d)} (hAm : MeasurableSet A) (hAW : A ⊆ W)
    {G : Vec d → Vec d} (hGm : AEStronglyMeasurable G (volume.restrict W)) {B : ℝ}
    (hGB : ∀ x ∈ A, ‖G x‖ ≤ B) {p : ℝ} (hp : 0 < p) :
    lpBar W (ENNReal.ofReal p) (A.indicator G) ≤
      ENNReal.ofReal B * (volume A / volume W) ^ (1 / p) := by
  have hp0 : (0 : ℝ) ≤ 1 / p := by positivity
  rw [l2b_lpBar_eq hp (hGm.indicator hAm)]
  have hint : ∫⁻ x in W, ‖A.indicator G x‖ₑ ^ p = ∫⁻ x in A, ‖G x‖ₑ ^ p := by
    have : (fun x => ‖A.indicator G x‖ₑ ^ p) = A.indicator (fun x => ‖G x‖ₑ ^ p) := by
      funext x
      by_cases hx : x ∈ A
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx, ENNReal.zero_rpow_of_pos hp]
    rw [this, lintegral_indicator hAm, Measure.restrict_restrict hAm, Set.inter_eq_left.2 hAW]
  rw [hint]
  have hle : ∫⁻ x in A, ‖G x‖ₑ ^ p ≤ ∫⁻ x in A, (ENNReal.ofReal B) ^ p := by
    refine setLIntegral_mono' hAm fun x hx => ?_
    refine ENNReal.rpow_le_rpow ?_ hp.le
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hGB x hx)
  rw [setLIntegral_const] at hle
  calc (volume W)⁻¹ ^ (1 / p) * (∫⁻ x in A, ‖G x‖ₑ ^ p) ^ (1 / p)
      ≤ (volume W)⁻¹ ^ (1 / p) * ((ENNReal.ofReal B) ^ p * volume A) ^ (1 / p) :=
        mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hle hp0)
    _ = ENNReal.ofReal B * (volume A / volume W) ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp0, ← ENNReal.rpow_mul, mul_one_div_cancel hp.ne',
          ENNReal.rpow_one, div_eq_mul_inv (volume A), ENNReal.mul_rpow_of_nonneg _ _ hp0]
        ring

/-- **The layer term in `W^{-1,p}` by a sup bound**: for every `p > 1`, with the
layer Poincare inequality at the conjugate exponent. -/
theorem linf_layer_dual [NeZero d] (M₁ : ℝ) :
    ∃ CP : ℝ, 0 ≤ CP ∧ ∀ {r₀ : ℝ} {W : Set (Vec d)} {M₂ D : ℝ},
      IsUniformC11Domain W r₀ M₁ M₂ D → ∀ {r : ℝ}, 0 < r →
      3 * r ≤ r₀ / (3 * ((d : ℝ) + (1 + d) * max M₁ 0) + 4) → volume W ≠ 0 →
      ∀ {p : ℝ}, 1 < p → ∀ {Gv : Vec d → Vec d} {B : ℝ}, 0 ≤ B →
        AEStronglyMeasurable Gv (volume.restrict W) →
        (∀ x ∈ W, lipGradient (l2a_cutoff W r) x ≠ 0 → ‖Gv x‖ ≤ B) →
        wMinusOneBar W (ENNReal.ofReal p)
            (fun x => vecDot (lipGradient (l2a_cutoff W r) x) (Gv x)) ≤
          ENNReal.ofReal (d * CP * B) *
            (volume (boundaryLayer W (3 * r)) / volume W) ^ (1 / p) := by
  obtain ⟨CP, hCP, H⟩ := l2d_hPoinc (d := d) M₁
  refine ⟨CP, hCP, ?_⟩
  intro r₀ W M₂ D hU r hr h3r hW0 p hp1 Gv B hB hGm hGB
  have hp0 : 0 < p := by linarith only [hp1]
  have hWm : MeasurableSet W := hU.1.measurableSet
  have hWT : volume W ≠ ⊤ := (l2b_bounded_of_uniform hU).measure_lt_top.ne
  set ζ := l2a_cutoff W r with hζ
  set A : Set (Vec d) := {x | lipGradient ζ x ≠ 0} with hA
  have hAm : MeasurableSet A := (l2b_lipGradient_measurable ζ) (measurableSet_singleton 0).compl
  have hAL : A ⊆ l2b_layerA W r := fun x hx => by
    by_contra hc
    exact hx (l2b_lipGradient_zero_off hr x hc)
  have hAW : A ⊆ W := fun x hx => l2b_layerA_subset hr (hAL hx)
  have hAD : A ⊆ boundaryLayer W (3 * r) := fun x hx =>
    l2b_layer_of_infDist hU.2.2.1 (l2b_layerA_subset hr (hAL hx))
      (by linarith only [(hAL hx).2, hr])
  have hgrad0 : ∀ x, x ∉ A → lipGradient ζ x = 0 := fun x hx => by
    by_contra h; exact hx h
  have hgrad := l2b_lipGradient_norm_le W hr
  have hP1 : 1 < ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff hp0).2 hp1
  have hQ : (ENNReal.ofReal p).conjExponent = ENNReal.ofReal (p / (p - 1)) := by
    have := p14_conj hP1 ENNReal.ofReal_ne_top
    rwa [ENNReal.toReal_ofReal hp0.le] at this
  have hq0 : 0 < p / (p - 1) := div_pos hp0 (by linarith only [hp1])
  have hq1 : 1 ≤ p / (p - 1) := by
    rw [le_div_iff₀ (by linarith only [hp1])]; linarith only
  have hPoinc : ∀ ψ : H10Function W,
      eLpNorm ψ.toH1Function.toFun (ENNReal.ofReal (p / (p - 1))) (volume.restrict A) ≤
        ENNReal.ofReal (CP * r) * eLpNorm (fun x => ‖ψ.toH1Function.grad x‖)
          (ENNReal.ofReal (p / (p - 1))) (volume.restrict W) :=
    fun ψ => H hU hq1 hr h3r hAD ψ
  have hlay : lpBar W (ENNReal.ofReal p) (A.indicator Gv) ≤
      ENNReal.ofReal B * (volume (boundaryLayer W (3 * r)) / volume W) ^ (1 / p) := by
    refine (linf_lpBar_indicator_le hAm hAW hGm (fun x hx => hGB x (hAW hx) hx) hp0).trans ?_
    refine mul_le_mul' le_rfl (ENNReal.rpow_le_rpow ?_ (by positivity))
    exact ENNReal.div_le_div_right (measure_mono hAD) _
  unfold wMinusOneBar
  refine iSup₂_le fun ψ hψ => ?_
  have h1 : ∫ x in W, vecDot (lipGradient ζ x) (Gv x) * ψ.toH1Function.toFun x =
      ∫ x in W, vecDot (A.indicator Gv x) (ψ.toH1Function.toFun x • lipGradient ζ x) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x =>
      l2b_pairing_eq hgrad0 Gv ψ.toH1Function.toFun x)
  rw [h1]
  have hψm : AEStronglyMeasurable ψ.toH1Function.toFun (volume.restrict W) :=
    ψ.toH1Function.memL2.aestronglyMeasurable
  have hgm' : AEStronglyMeasurable (fun x => ψ.toH1Function.toFun x • lipGradient ζ x)
      (volume.restrict W) :=
    hψm.smul (l2b_lipGradient_measurable ζ).aestronglyMeasurable
  refine (p14_holder_pairing hW0 hP1 ENNReal.ofReal_ne_top (hGm.indicator hAm) hgm').trans ?_
  rw [hQ] at hψ ⊢
  have hψ' := l2b_lpBar_psi_grad_le hAm hAW hr hgrad hgrad0 hq0 ψ (hPoinc ψ)
  have h2 : lpBar W (ENNReal.ofReal (p / (p - 1))) (fun x => ψ.toH1Function.toFun x • lipGradient ζ x)
      ≤ ENNReal.ofReal CP := by
    refine hψ'.trans ?_
    calc _ ≤ ENNReal.ofReal CP * 1 := mul_le_mul' le_rfl hψ
      _ = _ := mul_one _
  calc ENNReal.ofReal d * lpBar W (ENNReal.ofReal p) (A.indicator Gv) *
        lpBar W (ENNReal.ofReal (p / (p - 1))) (fun x => ψ.toH1Function.toFun x • lipGradient ζ x)
      ≤ ENNReal.ofReal d * (ENNReal.ofReal B *
          (volume (boundaryLayer W (3 * r)) / volume W) ^ (1 / p)) * ENNReal.ofReal CP :=
        mul_le_mul' (mul_le_mul' le_rfl hlay) h2
    _ = _ := by
        rw [ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg d) hCP),
          ENNReal.ofReal_mul (Nat.cast_nonneg d)]
        ring

/-- Satisfiability: the hypotheses of `linf_layer_dual` hold on a dilated Euclidean ball with the
zero field and `p = 2`, with the cutoff scale `r = 3`. -/
example [NeZero d] : ∃ (W : Set (Vec d)) (r₀ M₁ M₂ D : ℝ),
    IsUniformC11Domain W r₀ M₁ M₂ D ∧ (0 : ℝ) < 3 ∧
      3 * (3 : ℝ) ≤ r₀ / (3 * ((d : ℝ) + (1 + d) * max M₁ 0) + 4) ∧ volume W ≠ 0 ∧
      (1 : ℝ) < 2 ∧ (0 : ℝ) ≤ 0 ∧
      AEStronglyMeasurable (fun _ : Vec d => (0 : Vec d)) (volume.restrict W) ∧
      (∀ x ∈ W, lipGradient (l2a_cutoff W 3) x ≠ 0 → ‖(fun _ : Vec d => (0 : Vec d)) x‖ ≤ 0) := by
  obtain ⟨W, r₀, M₁, M₂, D, hU, h3, hW0⟩ := l2d_witness_domain (d := d)
  exact ⟨W, r₀, M₁, M₂, D, hU, by norm_num, h3, hW0, by norm_num, le_rfl,
    aestronglyMeasurable_const, fun x _ _ => by simp⟩

end SuperdiffusionCLT.Section7
