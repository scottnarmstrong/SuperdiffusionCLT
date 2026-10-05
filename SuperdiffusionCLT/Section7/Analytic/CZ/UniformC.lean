/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.CZ.LocalE
public import SuperdiffusionCLT.Section7.Analytic.CZ.Uniform
public import SuperdiffusionCLT.Section7.Analytic.CZ.UniformB

/-!
# Global `W^{1,p}` estimate: local estimates in unnormalized norms

The local estimates of the previous files are stated with the `ℓ^d`-normalized norms of a triadic
cube.  Here they are rewritten with the plain Lebesgue norms on the pieces:

* `p13_unscale`: removal of the scale normalization (algebra in `ℝ≥0∞`);
* `p13_int_local`: the interior estimate on an arbitrary box of side `3^m` inside `U`, obtained from
  the origin-cube estimate by a translation.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal NNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem p13_nmeas_eLpNorm {E : Type*} [NormedAddCommGroup E] (ℓ : ℝ) (S : Set (Vec d)) (h : Vec d → E)
    {q : ℝ≥0∞} (hq0 : q ≠ 0) (hqt : q ≠ ⊤) :
    eLpNorm h q (p12_nmeas ℓ S) =
      ENNReal.ofReal ((ℓ ^ d)⁻¹) ^ (1 / q).toReal * eLpNorm h q (volume.restrict S) := by
  unfold p12_nmeas
  rw [eLpNorm_smul_measure_of_ne_zero_of_ne_top hq0 hqt]
  rfl

theorem p13_cancel {a x y : ℝ≥0∞} (h0 : a ≠ 0) (ht : a ≠ ⊤) (h : a * x ≤ a * y) : x ≤ y :=
  (ENNReal.mul_le_mul_iff_right h0 ht).1 h

/-- Algebra: remove the scale normalization from a local estimate. -/
theorem p13_unscale {ℓ P C : ℝ} (hℓ : 0 < ℓ) (hP : 2 ≤ P) {Ep Eg Eu EF : ℝ≥0∞}
    (h : ENNReal.ofReal ℓ * (ENNReal.ofReal ((ℓ ^ d)⁻¹) ^ (1 / P) * Ep) ≤
      ENNReal.ofReal C *
        (ENNReal.ofReal ℓ * (ENNReal.ofReal ((ℓ ^ d)⁻¹) ^ (1 / 2 : ℝ) * Eg) +
          ENNReal.ofReal ((ℓ ^ d)⁻¹) ^ (1 / 2 : ℝ) * Eu +
          ENNReal.ofReal ℓ * (ENNReal.ofReal ((ℓ ^ d)⁻¹) ^ (1 / P) * EF))) :
    Ep ≤ ENNReal.ofReal C *
      (ENNReal.ofReal ((ℓ ^ d)⁻¹) ^ (1 / 2 - 1 / P : ℝ) * Eg +
        ENNReal.ofReal ((ℓ ^ d)⁻¹) ^ (1 / 2 - 1 / P : ℝ) * ENNReal.ofReal ℓ⁻¹ * Eu + EF) := by
  set lam : ℝ≥0∞ := ENNReal.ofReal ((ℓ ^ d)⁻¹) with hlam
  have hlam0 : lam ≠ 0 := by
    rw [hlam]
    exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hlamt : lam ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsplit : lam ^ (1 / 2 : ℝ) = lam ^ (1 / P) * lam ^ (1 / 2 - 1 / P : ℝ) := by
    have hP0 : 0 < P := by linarith only [hP]
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by
      have : 1 / P ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hP
      linarith only [this])]
    congr 1
    ring
  have hc0 : ENNReal.ofReal ℓ * lam ^ (1 / P) ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.2 hℓ).ne' (ENNReal.rpow_pos (pos_iff_ne_zero.2 hlam0) hlamt).ne'
  have hct : ENNReal.ofReal ℓ * lam ^ (1 / P) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by
        have hP0 : 0 < P := by linarith only [hP]
        positivity) hlamt)
  have hinv : ENNReal.ofReal ℓ * ENNReal.ofReal ℓ⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul hℓ.le, mul_inv_cancel₀ hℓ.ne', ENNReal.ofReal_one]
  refine p13_cancel hc0 hct ?_
  set A := lam ^ (1 / P) with hA
  set Λ := lam ^ (1 / 2 - 1 / P : ℝ) with hΛ
  set Li := ENNReal.ofReal ℓ⁻¹ with hLi
  set L := ENNReal.ofReal ℓ with hL
  have hφ : A * Λ * Eu = L * A * (Λ * Li * Eu) := by
    calc A * Λ * Eu = A * Λ * Eu * (L * Li) := by rw [hinv, mul_one]
      _ = _ := by ring
  rw [hsplit] at h
  calc L * A * Ep = L * (A * Ep) := by ring
    _ ≤ _ := h
    _ = L * A * (ENNReal.ofReal C * (Λ * Eg + Λ * Li * Eu + EF)) := by
      calc _ = ENNReal.ofReal C * (L * (A * Λ * Eg) + A * Λ * Eu + L * (A * EF)) := rfl
        _ = _ := by rw [hφ]; ring

theorem p13_eLpNorm_translate {E : Type*} [NormedAddCommGroup E] (z : Vec d) (S : Set (Vec d))
    (h : Vec d → E) (q : ℝ≥0∞) :
    eLpNorm (fun x => h (x - z)) q (volume.restrict (translateSet z S)) =
      eLpNorm h q (volume.restrict S) := by
  have hmp := measurePreserving_subRight_restrict_translateSet z S
  have hme : MeasurableEmbedding (fun x : Vec d => x - z) :=
    (Homeomorph.subRight z).measurableEmbedding
  rw [← hmp.map_eq, hme.eLpNorm_map_measure]
  rfl

theorem p13_translate_box (z₀ : Vec d) (r : ℝ) :
    translateSet (-z₀) {x : Vec d | ∀ i, |x i - z₀ i| < r} = {y | ∀ i, |y i| < r} := by
  ext y
  rw [mem_translateSet_iff_sub_mem]
  simp only [Set.mem_ofPred_eq, sub_neg_eq_add, Pi.add_apply, add_sub_cancel_right]

theorem p13_translate_cbox (z₀ : Vec d) (r : ℝ) :
    translateSet (-z₀) (p12_box z₀ r) = p12_box 0 r := by
  ext y
  rw [mem_translateSet_iff_sub_mem]
  simp only [p12_box, Set.mem_ofPred_eq, sub_neg_eq_add, Pi.add_apply, add_sub_cancel_right,
    Pi.zero_apply, sub_zero]

theorem p13_isOpen_translate {z : Vec d} {U : Set (Vec d)} (hU : IsOpen U) :
    IsOpen (translateSet z U) := by
  have : translateSet z U = (fun x : Vec d => x - z) ⁻¹' U := by
    ext x; exact mem_translateSet_iff_sub_mem
  rw [this]
  exact hU.preimage (continuous_id.sub continuous_const)

theorem p13_openCube_origin (m : ℤ) :
    openCubeSet (originCube d m) = {y : Vec d | ∀ i, |y i| < (3 : ℝ) ^ m / 2} := by
  ext y
  simp only [openCubeSet, originCube, Set.mem_ofPred_eq, cubeScaleFactor]
  refine forall_congr' fun i => ?_
  rw [abs_lt]
  simp only [Pi.zero_apply, Int.cast_zero, zero_sub, zero_add]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith only [h1, h2]

theorem p13_normalized_box (m : ℤ) :
    (normalizedCubeMeasure (originCube d m)).restrict (p12_box 0 ((3 : ℝ) ^ m / 4)) =
      p12_nmeas ((3 : ℝ) ^ m) (p12_box 0 ((3 : ℝ) ^ m / 4)) := by
  rw [p12_normalized_restrict m (p12_box_measurable _ _)]
  congr 2
  refine Set.inter_eq_left.2 fun y hy => ?_
  rw [p13_openCube_origin]
  intro i
  have h : |y i| ≤ (3 : ℝ) ^ m / 4 := by simpa using hy i
  have hℓ : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  linarith only [h, hℓ]

/-- The local estimate at an interior box, in unnormalized norms. -/
theorem p13_int_local [NeZero d] (hd : 2 ≤ d) {P : ℝ} (hP : 2 ≤ P) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : Set (Vec d)) (m : ℤ) (z₀ : Vec d), IsOpen U →
      {y : Vec d | ∀ i, |y i - z₀ i| < (3 : ℝ) ^ m / 2} ⊆ U →
      ∀ (u : H1Function U) (F : Vec d → Vec d),
        IsWeakSolutionOn (fun _ => (1 : Mat d)) U u (fun _ => 0) F →
        MemLp F (ENNReal.ofReal P)
          (volume.restrict {y : Vec d | ∀ i, |y i - z₀ i| < (3 : ℝ) ^ m / 2}) →
        eLpNorm u.grad (ENNReal.ofReal P) (volume.restrict (p12_box z₀ ((3 : ℝ) ^ m / 4))) ≤
          ENNReal.ofReal C *
            (ENNReal.ofReal ((((3 : ℝ) ^ m) ^ d)⁻¹) ^ (1 / 2 - 1 / P : ℝ) *
                  eLpNorm u.grad 2
                    (volume.restrict {y : Vec d | ∀ i, |y i - z₀ i| < (3 : ℝ) ^ m / 2}) +
                ENNReal.ofReal ((((3 : ℝ) ^ m) ^ d)⁻¹) ^ (1 / 2 - 1 / P : ℝ) *
                  ENNReal.ofReal (((3 : ℝ) ^ m)⁻¹) *
                  eLpNorm u.toFun 2
                    (volume.restrict {y : Vec d | ∀ i, |y i - z₀ i| < (3 : ℝ) ^ m / 2}) +
              eLpNorm F (ENNReal.ofReal P)
                (volume.restrict {y : Vec d | ∀ i, |y i - z₀ i| < (3 : ℝ) ^ m / 2})) := by
  obtain ⟨ε, C, hε, hC, H⟩ := localW1p_interior_domain hd hP
  refine ⟨C, hC, ?_⟩
  intro U m z₀ hU hBU u F hw hF
  have hℓ : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  have hP0 : 0 < P := by linarith only [hP]
  set ℓ : ℝ := (3 : ℝ) ^ m with hℓdef
  set Bx : Set (Vec d) := {y : Vec d | ∀ i, |y i - z₀ i| < ℓ / 2} with hBx
  set Q := originCube d m with hQ
  have hQU : openCubeSet Q ⊆ translateSet (-z₀) U := by
    intro y hy
    rw [p13_openCube_origin] at hy
    rw [mem_translateSet_iff_sub_mem]
    refine hBU fun i => ?_
    simpa using hy i
  have hw' := hw.translate (-z₀)
  have hF' : MemLp (fun x => F (x - (-z₀))) (ENNReal.ofReal P) (normalizedCubeMeasure Q) := by
    have h1 : MemLp (fun x => F (x - (-z₀))) (ENNReal.ofReal P)
        (volume.restrict (translateSet (-z₀) Bx)) :=
      hF.comp_measurePreserving (measurePreserving_subRight_restrict_translateSet (-z₀) Bx)
    rw [hBx, p13_translate_box, ← p13_openCube_origin] at h1
    rw [hQ, p12_normalized_eq, p12_nmeas]
    exact h1.smul_measure ENNReal.ofReal_ne_top
  obtain ⟨-, hmain⟩ := H (translateSet (-z₀) U) Q (fun _ => 1) (p13_isOpen_translate hU) hQU
    (fun i j => aestronglyMeasurable_const) (fun x _ i j => by simp [hε.le]) (fun _ => 0)
    (fun x => F (x - (-z₀))) (u.translate (-z₀)) hw' (by simp) (by simp) hF'
  have hcsf : cubeScaleFactor Q = ℓ := rfl
  have hidx : (fun i => ((Q.index i : ℤ) : ℝ) * cubeScaleFactor Q) = (0 : Vec d) := by
    funext i; simp [hQ, originCube]
  rw [hidx] at hmain
  unfold Section2.Norms.cubeLpENorm at hmain
  rw [hcsf, hQ, p13_normalized_box m, p12_normalized_eq m, p13_openCube_origin,
    ← p13_translate_box z₀] at hmain
  rw [← p13_translate_cbox z₀ (ℓ / 4)] at hmain
  have e1 : (u.translate (-z₀)).grad = fun x => u.grad (x - -z₀) := rfl
  have e2 : (u.translate (-z₀)).toFun = fun x => u.toFun (x - -z₀) := rfl
  have h2 : (1 / (2 : ℝ≥0∞)).toReal = 1 / 2 := by simp
  have hPr : (1 / ENNReal.ofReal P).toReal = 1 / P := by
    rw [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofReal hP0.le, one_div]
  have hP2 : ENNReal.ofReal P ≠ 0 := (ENNReal.ofReal_pos.2 hP0).ne'
  rw [e1, e2] at hmain
  have hz : ∀ (q : ℝ≥0∞) (μ : Measure (Vec d)), eLpNorm (fun _ : Vec d => (0 : ℝ)) q μ = 0 :=
    fun q μ => eLpNorm_zero
  rw [hz] at hmain
  simp only [mul_zero, add_zero] at hmain
  rw [p13_nmeas_eLpNorm ℓ _ _ hP2 ENNReal.ofReal_ne_top, p13_nmeas_eLpNorm ℓ _ _ (by norm_num) (by norm_num),
    p13_nmeas_eLpNorm ℓ _ _ (by norm_num) (by norm_num), p13_nmeas_eLpNorm ℓ _ _ hP2 ENNReal.ofReal_ne_top,
    p13_eLpNorm_translate, p13_eLpNorm_translate, p13_eLpNorm_translate, p13_eLpNorm_translate,
    hPr, h2] at hmain
  exact p13_unscale hℓ hP hmain

end SuperdiffusionCLT.Section7
