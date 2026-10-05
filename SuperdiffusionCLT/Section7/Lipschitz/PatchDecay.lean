/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Geometry.AtlasTransform
public import SuperdiffusionCLT.Section7.Lipschitz.TraceZero
public import SuperdiffusionCLT.Section7.Analytic.Regularity.BoundaryDecayChartM
public import Homogenization.Book.Ch03.Definitions

/-!
# Pinned boundary decay on the patch of a uniformly `C^{1,1}` domain

One application of `r3e_boundary_decay` at `(a₀, b₀) = (0, b₀)`; the zero trace of an `H¹₀`
function at the chart point (`lip_h10_trace_zero`, applied to `φ` and `-φ`) forces the constant
term `a` to be at most the right-hand side in absolute value.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal Pointwise

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem lip_patch_decay_abs_vecDot_le (b v : Vec d) : |vecDot b v| ≤ (∑ i, |b i|) * ‖v‖ := by
  unfold vecDot
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (by simpa using norm_le_pi_norm v i) (abs_nonneg _)

/-- One sided pinning: if `u` is within `E` of `a + b·(y - x₀)` near `x₀` and cannot stay above a
positive constant near `x₀`, then `a ≤ E`. -/
theorem lip_patch_decay_pin_le {V : Set (Vec d)} (hV : IsOpen V) {x₀ : Vec d} {u : Vec d → ℝ} {a E ρ : ℝ}
    {b : Vec d} (hρ : 0 < ρ)
    (hBT : ∀ A ρ' : ℝ, 0 < ρ' → (∀ᵐ y ∂volume.restrict (V ∩ Metric.ball x₀ ρ'), A ≤ u y) → A ≤ 0)
    (hab : ∀ᵐ y ∂volume.restrict (V ∩ Metric.ball x₀ ρ), |u y - (a + vecDot b (y - x₀))| ≤ E) :
    a ≤ E := by
  by_contra hlt
  have hA : 0 < (a - E) / 2 := by linarith only [not_le.mp hlt]
  set B : ℝ := ∑ i, |b i| with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hB1 : 0 < B + 1 := by linarith only [hB0]
  set ρ' : ℝ := min ρ ((a - E) / 2 / (B + 1)) with hρ'
  have hρ'0 : 0 < ρ' := lt_min hρ (div_pos hA hB1)
  have hsub : V ∩ Metric.ball x₀ ρ' ⊆ V ∩ Metric.ball x₀ ρ :=
    Set.inter_subset_inter_right _ (Metric.ball_subset_ball (min_le_left _ _))
  have hab' := ae_restrict_of_ae_restrict_of_subset hsub hab
  have hmem : ∀ᵐ y ∂volume.restrict (V ∩ Metric.ball x₀ ρ'), y ∈ V ∩ Metric.ball x₀ ρ' :=
    ae_restrict_mem (hV.inter Metric.isOpen_ball).measurableSet
  have key : ∀ᵐ y ∂volume.restrict (V ∩ Metric.ball x₀ ρ'), (a - E) / 2 ≤ u y := by
    filter_upwards [hab', hmem] with y hy hyV
    have hd : ‖y - x₀‖ < ρ' := by
      have := hyV.2
      rwa [Metric.mem_ball, dist_eq_norm] at this
    have h1 : |vecDot b (y - x₀)| ≤ B * ‖y - x₀‖ := lip_patch_decay_abs_vecDot_le b (y - x₀)
    have h2 : B * ‖y - x₀‖ ≤ (B + 1) * ρ' :=
      mul_le_mul (by linarith only) hd.le (norm_nonneg _) hB1.le
    have h3 : (B + 1) * ρ' ≤ (a - E) / 2 := by
      have : ρ' ≤ (a - E) / 2 / (B + 1) := min_le_right _ _
      calc (B + 1) * ρ' ≤ (B + 1) * ((a - E) / 2 / (B + 1)) :=
            mul_le_mul_of_nonneg_left this hB1.le
        _ = (a - E) / 2 := by field_simp
    have h4 := abs_le.mp hy
    have h5 := abs_le.mp (h1.trans (h2.trans h3))
    linarith only [h4.1, h5.1]
  exact absurd (hBT _ ρ' hρ'0 key) (not_le.mpr hA)


/-- **BT2 — pinned boundary excess decay with the flatness of the true patch.**  The estimate
`r3e_boundary_decay` for an open set `V` that coincides near `x₀` with a uniformly `C^{1,1}` set
`W`: the affine approximation vanishes at `x₀` (`a₀ = 0`, `a = 0`), and the slope term carries the
gradient-Lipschitz constant `M₂` of the charts of `W`, not of `V`. -/
theorem lip_patch_decay (d : ℕ) [NeZero d] (hd : 2 ≤ d) (M₁ : ℝ) {p : ℝ} (hp : (d : ℝ) < p) :
    ∃ ε C c K : ℝ, 0 < ε ∧ 0 < C ∧ 0 < c ∧ 1 ≤ K ∧
      ∀ (V W : Set (Vec d)) (rW M₂ DW R₀ : ℝ) (m₁ : ℤ) (x₀ : Vec d),
        IsOpen V → IsUniformC11Domain W rW M₁ M₂ DW → x₀ ∈ frontier W →
        V ∩ Metric.ball x₀ R₀ = W ∩ Metric.ball x₀ R₀ →
        M₂ * (3 : ℝ) ^ m₁ ≤ ε → K * (3 : ℝ) ^ m₁ ≤ rW → K * (3 : ℝ) ^ m₁ ≤ R₀ →
        ∀ (φ : H10Function V) (f : Vec d → ℝ),
          IsWeakSolutionOn (fun _ => (1 : Mat d)) V φ.toH1Function f (fun _ => 0) →
          MemLp f (ENNReal.ofReal p)
            (volume.restrict (V ∩ Metric.ball x₀ (K * (3 : ℝ) ^ m₁))) →
          ∀ (b₀ : Vec d) (ρ : ℝ), 0 < ρ → ρ ≤ c * (3 : ℝ) ^ m₁ →
            ∃ b : Vec d, ∀ᵐ y ∂(volume.restrict (V ∩ Metric.ball x₀ ρ)),
              |φ.toH1Function.toFun y - vecDot b (y - x₀)| ≤
                C * ρ * (ρ / (3 : ℝ) ^ m₁) ^ (1 - (d : ℝ) / p) *
                  (((3 : ℝ) ^ m₁)⁻¹ * (eLpNorm (fun y => φ.toH1Function.toFun y -
                        vecDot b₀ (y - x₀)) 2
                      (p12_nmeas ((3 : ℝ) ^ m₁)
                        (V ∩ Metric.ball x₀ (K * (3 : ℝ) ^ m₁)))).toReal +
                    M₂ * (3 : ℝ) ^ m₁ * ‖b₀‖ +
                    (3 : ℝ) ^ m₁ * (eLpNorm f (ENNReal.ofReal p)
                      (p12_nmeas ((3 : ℝ) ^ m₁)
                        (V ∩ Metric.ball x₀ (K * (3 : ℝ) ^ m₁)))).toReal) := by
  obtain ⟨ε, C, c, K, hε, hC, hc, hK, H⟩ := r3e_boundary_decay (d := d) hd M₁ hp
  refine ⟨ε, 2 * C, c, K, hε, by linarith only [hC], hc, hK, ?_⟩
  intro V W rW M₂ DW R₀ m₁ x₀ hV hW hx₀ hVW hM hKr hKR φ f hw hf b₀ ρ hρ hρc
  obtain ⟨hWo, hr, -, hch⟩ := hW
  obtain ⟨e, ψ, he, hψ, hb1, hb2, hU⟩ := hch x₀ hx₀
  have hgraph : vecDot e x₀ = ψ (x₀ - vecDot e x₀ • e) :=
    vecDot_eq_of_mem_frontier hWo hψ.continuous hU hx₀ (Metric.mem_ball_self hr)
  have hchV : ∀ y ∈ Metric.ball x₀ (K * (3 : ℝ) ^ m₁),
      (y ∈ V ↔ vecDot e y < ψ (y - vecDot e y • e)) := by
    intro y hy
    have hyR : y ∈ Metric.ball x₀ R₀ := Metric.ball_subset_ball hKR hy
    have hyr : y ∈ Metric.ball x₀ rW := Metric.ball_subset_ball hKr hy
    rw [← hU y hyr]
    constructor
    · intro h
      have : y ∈ V ∩ Metric.ball x₀ R₀ := ⟨h, hyR⟩
      rw [hVW] at this
      exact this.1
    · intro h
      have : y ∈ W ∩ Metric.ball x₀ R₀ := ⟨h, hyR⟩
      rw [← hVW] at this
      exact this.1
  have hK0 : 0 < K * (3 : ℝ) ^ m₁ := by positivity
  have hBT : ∀ A ρ' : ℝ, 0 < ρ' →
      (∀ᵐ y ∂volume.restrict (V ∩ Metric.ball x₀ ρ'), A ≤ φ.toH1Function.toFun y) → A ≤ 0 :=
    fun A ρ' hρ' hA => lip_h10_trace_zero d hV hK0 he hψ hgraph hchV φ hρ' hA
  have hBTn : ∀ A ρ' : ℝ, 0 < ρ' →
      (∀ᵐ y ∂volume.restrict (V ∩ Metric.ball x₀ ρ'), A ≤ -φ.toH1Function.toFun y) → A ≤ 0 :=
    fun A ρ' hρ' hA => lip_h10_trace_zero d hV hK0 he hψ hgraph hchV (-φ) hρ'
      (by
        filter_upwards [hA] with y hy
        have h1 : (-φ).toH1Function = -φ.toH1Function := rfl
        rw [h1, H1Function.neg_toFun]
        exact hy)
  obtain ⟨a, b, hab⟩ := H V e ψ x₀ (K * (3 : ℝ) ^ m₁) M₂ m₁ hV he hψ hb1 hb2 hgraph hchV hM
    le_rfl φ f hw hf 0 b₀ ρ hρ hρc
  simp only [zero_add] at hab
  set E : ℝ := C * ρ * (ρ / (3 : ℝ) ^ m₁) ^ (1 - (d : ℝ) / p) *
      (((3 : ℝ) ^ m₁)⁻¹ * (eLpNorm (fun y => φ.toH1Function.toFun y -
            vecDot b₀ (y - x₀)) 2
          (p12_nmeas ((3 : ℝ) ^ m₁)
            (V ∩ Metric.ball x₀ (K * (3 : ℝ) ^ m₁)))).toReal +
        M₂ * (3 : ℝ) ^ m₁ * ‖b₀‖ +
        (3 : ℝ) ^ m₁ * (eLpNorm f (ENNReal.ofReal p)
          (p12_nmeas ((3 : ℝ) ^ m₁)
            (V ∩ Metric.ball x₀ (K * (3 : ℝ) ^ m₁)))).toReal) with hE
  have h1 : a ≤ E := lip_patch_decay_pin_le hV hρ hBT hab
  have h2 : -a ≤ E := by
    refine lip_patch_decay_pin_le (b := -b) hV hρ hBTn ?_
    filter_upwards [hab] with y hy
    have : -φ.toH1Function.toFun y - (-a + vecDot (-b) (y - x₀)) =
        -(φ.toH1Function.toFun y - (a + vecDot b (y - x₀))) := by
      simp [vecDot]
      ring
    rw [this, abs_neg]
    exact hy
  refine ⟨b, ?_⟩
  filter_upwards [hab] with y hy
  have h3 := abs_le.mp hy
  have hgoal : (2 * C) * ρ * (ρ / (3 : ℝ) ^ m₁) ^ (1 - (d : ℝ) / p) *
      (((3 : ℝ) ^ m₁)⁻¹ * (eLpNorm (fun y => φ.toH1Function.toFun y -
            vecDot b₀ (y - x₀)) 2
          (p12_nmeas ((3 : ℝ) ^ m₁)
            (V ∩ Metric.ball x₀ (K * (3 : ℝ) ^ m₁)))).toReal +
        M₂ * (3 : ℝ) ^ m₁ * ‖b₀‖ +
        (3 : ℝ) ^ m₁ * (eLpNorm f (ENNReal.ofReal p)
          (p12_nmeas ((3 : ℝ) ^ m₁)
            (V ∩ Metric.ball x₀ (K * (3 : ℝ) ^ m₁)))).toReal) = 2 * E := by
    rw [hE]; ring
  rw [hgoal, abs_le]
  constructor <;> linarith only [h1, h2, h3.1, h3.2]

end SuperdiffusionCLT.Section7
