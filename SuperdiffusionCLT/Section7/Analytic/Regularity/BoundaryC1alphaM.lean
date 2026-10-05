/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.BoundaryC1alphaL

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal NNReal

/-!
# `L^p` bound of the cutoff datum from pointwise bounds
-/

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem r3c_lpBound4 (Q : TriadicCube d) {p : ℝ≥0∞} (hp : 1 ≤ p) {F f W : Vec d → ℝ}
    {Y : Vec d → Vec d} {a1 a2 a3 : ℝ} (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (ha3 : 0 ≤ a3)
    (hF : AEStronglyMeasurable F (normalizedCubeMeasure Q))
    (hf : MemLp f p (normalizedCubeMeasure Q)) (hY : MemLp Y p (normalizedCubeMeasure Q))
    (hW : MemLp W p (normalizedCubeMeasure Q))
    (h : ∀ᵐ x ∂(normalizedCubeMeasure Q), |F x| ≤ |f x| + a1 * ‖Y x‖ + a2 * |W x| + a3) :
    MemLp F p (normalizedCubeMeasure Q) ∧
      (eLpNorm F p (normalizedCubeMeasure Q)).toReal ≤
        (eLpNorm f p (normalizedCubeMeasure Q)).toReal +
          a1 * (eLpNorm Y p (normalizedCubeMeasure Q)).toReal +
            a2 * (eLpNorm W p (normalizedCubeMeasure Q)).toReal + a3 := by
  have hprob := p12_isProb Q
  set μ := normalizedCubeMeasure Q with hμ
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  set ft : Vec d → ℝ := fun x => |f x| + a3 with hft
  have hftm : MemLp ft p μ := hf.norm.add (memLp_const a3)
  have hb := p12_bound3 (μ := μ) hp (F := F) (X := ft) (Y := Y) (Z := W) (a := 1) (b := a1) (c := a2)
    zero_le_one ha1 ha2 hF hftm hY hW (by
      filter_upwards [h] with x hx
      rw [Real.norm_eq_abs, one_mul]
      have : ‖ft x‖ = |f x| + a3 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [this, Real.norm_eq_abs]
      linarith only [hx])
  refine ⟨hb.1, ?_⟩
  have h2 : eLpNorm (fun x => |f x|) p μ = eLpNorm f p μ := by
    have := eLpNorm_norm (μ := μ) (p := p) f hf.aestronglyMeasurable
    simpa [Real.norm_eq_abs] using this
  have h3 : eLpNorm (fun _ : Vec d => a3) p μ = ENNReal.ofReal a3 := by
    rw [eLpNorm_const _ hp0 hprob.ne_zero]
    simp [hprob.measure_univ, Real.enorm_eq_ofReal ha3]
  have e1 : eLpNorm ft p μ ≤ eLpNorm f p μ + ENNReal.ofReal a3 := by
    have h1 := eLpNorm_add_le (μ := μ) (p := p) (f := fun x => |f x|) (g := fun _ => a3)
      hp
    rw [h2, h3] at h1
    exact h1
  have hfin1 : eLpNorm f p μ ≠ ⊤ := hf.eLpNorm_ne_top
  have hfin2 : eLpNorm Y p μ ≠ ⊤ := hY.eLpNorm_ne_top
  have hfin3 : eLpNorm W p μ ≠ ⊤ := hW.eLpNorm_ne_top
  have hfin4 : eLpNorm ft p μ ≠ ⊤ := hftm.eLpNorm_ne_top
  have hb2 := hb.2
  have hne : ENNReal.ofReal 1 * eLpNorm ft p μ + ENNReal.ofReal a1 * eLpNorm Y p μ +
      ENNReal.ofReal a2 * eLpNorm W p μ ≠ ⊤ := by
    refine ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨?_, ?_⟩, ?_⟩ <;>
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ‹_›
  have h4 := ENNReal.toReal_mono hne hb2
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin4,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin2⟩) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin3),
    ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin4)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin2),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal zero_le_one,
    ENNReal.toReal_ofReal ha1, ENNReal.toReal_ofReal ha2, one_mul] at h4
  have h5 : (eLpNorm ft p μ).toReal ≤ (eLpNorm f p μ).toReal + a3 := by
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin1, ENNReal.ofReal_ne_top⟩) e1
    rwa [ENNReal.toReal_add hfin1 ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal ha3] at this
  linarith only [h4, h5]


theorem r3c_zero_mem_cube (m : ℤ) : (0 : Vec d) ∈ openCubeSet (originCube d m) := by
  rw [hc_mem_openCubeSet_originCube_iff]
  intro i
  have hp : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  simp only [Pi.zero_apply]
  constructor <;> linarith only [hp]

/-- **Pointwise bound of the cutoff datum, almost everywhere on the cube.** -/
theorem r3c_F_bound_ae (e : Fin d) (m : ℤ) {A : CoeffField d}
    (hAs : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => A x i j)) (c : ℝ) {δ K G₁ G₂ : ℝ} (hG1 : 0 ≤ G₁) (hG2 : 0 ≤ G₂)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hKl : K * (3 : ℝ) ^ m ≤ δ)
    (hδ : ∀ x ∈ openCubeSet (originCube d m), ∀ i j, |A x i j - (1 : Mat d) i j| ≤ δ)
    (hK : ∀ x ∈ openCubeSet (originCube d m), ∀ i j k,
      |fderiv ℝ (fun y => A y i j) x (basisVec k)| ≤ K)
    (hcut1 : ∀ (z₀ : Vec d) (lam : ℝ), 0 < lam → ∀ x i, |p12_grad (r3c_cutS z₀ lam) x i| ≤ G₁ / lam)
    (hcut2 : ∀ (z₀ : Vec d) (lam : ℝ), 0 < lam → ∀ x j k,
      |fderiv ℝ (fun y => p12_grad (r3c_cutS z₀ lam) y j) x (basisVec k)| ≤ G₂ / lam ^ 2)
    (f : Vec d → ℝ) {u W : H1Function (openCubeSet (originCube d m))}
    (hW1 : ∀ x, W.toFun x = p12_cut (r3c_z0 e m) ((3 : ℝ) ^ m) d d x * u.toFun x)
    (hW2 : ∀ᵐ x ∂(volume.restrict (openCubeSet (originCube d m))), W.grad x =
      p12_cut (r3c_z0 e m) ((3 : ℝ) ^ m) d d x • u.grad x +
        u.toFun x • p12_grad (p12_cut (r3c_z0 e m) ((3 : ℝ) ^ m) d d) x) :
    ∀ᵐ x ∂(normalizedCubeMeasure (originCube d m)),
      |r3c_cutoffData A (r3c_cutS (r3c_z0 e m) ((3 : ℝ) ^ m / 3)) f (r3c_slopeField A e c) u x| ≤
        |f x| + (4 * (d : ℝ) ^ 2 * G₁ / ((3 : ℝ) ^ m / 3)) * ‖W.grad x‖ +
          ((d : ℝ) ^ 2 * (G₁ + 2 * G₂) / ((3 : ℝ) ^ m / 3) ^ 2) * |W.toFun x| +
          (2 * d * G₁ + d) * (|c| * δ / ((3 : ℝ) ^ m / 3)) := by
  have hℓ : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  have hlam : (0 : ℝ) < (3 : ℝ) ^ m / 3 := by positivity
  set η := r3c_cutS (r3c_z0 e m) ((3 : ℝ) ^ m / 3) with hη
  have hDm : MeasurableSet (openCubeSet (originCube d m)) := (isOpen_openCubeSet _).measurableSet
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0 (r3c_zero_mem_cube m) e e e)
  have hKl' : K * ((3 : ℝ) ^ m / 3) ≤ δ := by
    refine le_trans ?_ hKl
    exact mul_le_mul_of_nonneg_left (by linarith only [hℓ]) hK0
  rw [normalizedCubeMeasure_eq_smul]
  refine Measure.ae_smul_measure ?_ _
  filter_upwards [hW2, ae_restrict_mem hDm] with x hW2x hxD
  by_cases hx : x ∈ tsupport η
  · have hbox := r3c_cutS_tsupport (r3c_z0 e m) hlam hx
    have hbox4 : ∀ i, |x i - r3c_z0 e m i| ≤ (3 : ℝ) ^ m / 4 := fun i => by
      refine (hbox i).trans ?_
      linarith only [hℓ]
    have hχ1 : p12_cut (r3c_z0 e m) ((3 : ℝ) ^ m) d d x = 1 := p12_cut_last _ hℓ d hbox4
    have hgz : p12_grad (p12_cut (r3c_z0 e m) ((3 : ℝ) ^ m) d d) x = 0 :=
      p12_grad_eq_zero_of_eq_one (fun y => (p12_cut_01 _ _ _ _ y).2) hχ1
    have hWx : W.toFun x = u.toFun x := by rw [hW1 x, hχ1, one_mul]
    have hWg : W.grad x = u.grad x := by rw [hW2x, hχ1, hgz]; simp
    rw [hWx, hWg]
    exact r3c_cutoffData_le hAs (r3c_cutS_contDiff _ _) (r3c_cutS_01 _ _) e c hlam hG1 hδ0 hδ1 hKl' f u x
      (hδ x hxD) (hK x hxD) (hcut1 _ _ hlam x) (hcut2 _ _ hlam x)
  · rw [r3c_cutoffData_eq_zero A f _ u hx, abs_zero]
    have h1 : 0 ≤ ‖W.grad x‖ := norm_nonneg _
    have h2 : 0 ≤ |W.toFun x| := abs_nonneg _
    have hc4 : 0 ≤ (4 * (d : ℝ) ^ 2 * G₁ / ((3 : ℝ) ^ m / 3)) := by positivity
    have hc5 : 0 ≤ ((d : ℝ) ^ 2 * (G₁ + 2 * G₂) / ((3 : ℝ) ^ m / 3) ^ 2) := by positivity
    have hc6 : 0 ≤ (2 * d * G₁ + d) * (|c| * δ / ((3 : ℝ) ^ m / 3)) := by positivity
    have := mul_nonneg hc4 h1
    have := mul_nonneg hc5 h2
    have := abs_nonneg (f x)
    linarith only [‹0 ≤ |f x|›, ‹0 ≤ (4 * (d : ℝ) ^ 2 * G₁ / ((3 : ℝ) ^ m / 3)) * ‖W.grad x‖›,
      ‹0 ≤ ((d : ℝ) ^ 2 * (G₁ + 2 * G₂) / ((3 : ℝ) ^ m / 3) ^ 2) * |W.toFun x|›, hc6]

theorem r3c_ae_normalized_of_mem (Q : TriadicCube d) {P : Vec d → Prop}
    (h : ∀ x ∈ openCubeSet Q, P x) : ∀ᵐ x ∂(normalizedCubeMeasure Q), P x := by
  rw [normalizedCubeMeasure_eq_smul]
  refine Measure.ae_smul_measure ?_ _
  exact (ae_restrict_iff' (isOpen_openCubeSet Q).measurableSet).2 (Filter.Eventually.of_forall h)

theorem r3c_vecDot_aesm {μ : Measure (Vec d)} {F H : Vec d → Vec d}
    (hF : ∀ i, AEStronglyMeasurable (fun x => F x i) μ)
    (hH : ∀ i, AEStronglyMeasurable (fun x => H x i) μ) :
    AEStronglyMeasurable (fun x => vecDot (F x) (H x)) μ := by
  unfold vecDot
  exact Finset.univ.aestronglyMeasurable_fun_sum fun i _ => (hF i).mul (hH i)

theorem r3c_matVec_aesm {μ : Measure (Vec d)} {A : CoeffField d} {F : Vec d → Vec d}
    (hA : ∀ i j, AEStronglyMeasurable (fun x => A x i j) μ)
    (hF : ∀ i, AEStronglyMeasurable (fun x => F x i) μ) (i : Fin d) :
    AEStronglyMeasurable (fun x => matVecMul (A x) (F x) i) μ := by
  simp only [matVecMul]
  exact Finset.univ.aestronglyMeasurable_fun_sum fun j _ => (hA i j).mul (hF j)

theorem r3c_cutoffData_aesm {U : Set (Vec d)} {A : CoeffField d}
    (hAs : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => A x i j)) {χ : Vec d → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) {f : Vec d → ℝ} {g : Vec d → Vec d}
    (hgs : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => g x i)) (u : H1Function U) {μ : Measure (Vec d)}
    (hf : AEStronglyMeasurable f μ) (hug : ∀ i, AEStronglyMeasurable (fun x => u.grad x i) μ)
    (huf : AEStronglyMeasurable u.toFun μ) :
    AEStronglyMeasurable (r3c_cutoffData A χ f g u) μ := by
  have hAm : ∀ i j, AEStronglyMeasurable (fun x => A x i j) μ := fun i j =>
    (hAs i j).continuous.aestronglyMeasurable
  have hgχ : ∀ i, AEStronglyMeasurable (fun x => p12_grad χ x i) μ := fun i =>
    (r3c_contDiff_grad_apply hχ i).continuous.aestronglyMeasurable
  have hgm : ∀ i, AEStronglyMeasurable (fun x => g x i) μ := fun i =>
    (hgs i).continuous.aestronglyMeasurable
  have hB : ∀ i, AEStronglyMeasurable (fun x => matVecMul (A x) (p12_grad χ x) i) μ := fun i =>
    (r3c_contDiff_matVec_grad hAs hχ i).continuous.aestronglyMeasurable
  have hB1 : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => (χ x • g x) i) := fun i => by
    simpa using hχ.mul (hgs i)
  have hdiv1 : AEStronglyMeasurable (r3c_div (fun y => χ y • g y)) μ :=
    (r3c_contDiff_div hB1).continuous.aestronglyMeasurable
  have hdiv2 : AEStronglyMeasurable (r3c_div (fun y => matVecMul (A y) (p12_grad χ y))) μ :=
    (r3c_contDiff_div (fun i => r3c_contDiff_matVec_grad hAs hχ i)).continuous.aestronglyMeasurable
  unfold r3c_cutoffData
  refine ((AEStronglyMeasurable.add ?_ ?_).sub ?_).sub (hdiv1.add ?_)
  · exact hχ.continuous.aestronglyMeasurable.mul hf
  · exact r3c_vecDot_aesm hgm hgχ
  · exact r3c_vecDot_aesm (fun i => r3c_matVec_aesm hAm hug i) hgχ
  · exact (r3c_vecDot_aesm hug hB).add (huf.mul hdiv2)

end SuperdiffusionCLT.Section7
