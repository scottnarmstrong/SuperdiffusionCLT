/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Response.NeumannOscillationNorms
public import SuperdiffusionCLT.Section5.Response.NeumannOscillationMajorant

/-!
# The oscillation of a field over a subcube

* `osc_sum_le`: for a field split as `gN = g₁ + δ + g₃`, the oscillation of `gN` over a subcube is
  at most twice the sum of the `L̲⁴` oscillations of `g₁`, `g₃` and the `L̲⁴` size of `δ`.
* `osc_le_hessian`, `osc_le_contDiff`: the oscillation of the gradient of an `H¹` function with a
  weak Hessian (resp. of a `C¹` field) over a subcube is controlled by the Jacobian through the
  `L̲⁴` Poincaré inequality.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section3.ResponseFields
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The cube average of a field minus a constant, for an `L²` field. -/
theorem volumeAverageVec_openCubeSet_sub_const {Q : TriadicCube d} {G : Vec d → Vec d}
    (hG : MemVectorL2 (openCubeSet Q) G) (c : Vec d) :
    volumeAverageVec (openCubeSet Q) (fun x => G x - c) =
      volumeAverageVec (openCubeSet Q) G - c := by
  funext i
  have hint : Integrable (fun x => G x i) (volume.restrict (openCubeSet Q)) := by
    have hm := SuperdiffusionCLT.Section3.Terms.memL2On_component_of_memVectorL2 hG i
    have : IsFiniteMeasure (volume.restrict (openCubeSet Q)) :=
      ⟨by simpa using (volume_openCubeSet_lt_top Q)⟩
    exact hm.integrable (by norm_num)
  have hvol : (volume (openCubeSet Q)).toReal ≠ 0 := by
    rw [volume_openCubeSet_toReal]
    exact (cubeVolume_pos Q).ne'
  show volumeAverage (openCubeSet Q) (fun x => G x i - c i) =
    volumeAverage (openCubeSet Q) (fun x => G x i) - c i
  unfold volumeAverage
  rw [integral_sub hint (integrable_const _), setIntegral_const, measureReal_def, smul_eq_mul]
  field_simp

/-- **The oscillation of a sum of three fields**: with `gN = g₁ + δ + g₃`,
`‖gN − (gN)_Q‖_{L̲⁴(Q)} ≤ 2 (‖g₁ − (g₁)_Q‖ + ‖δ‖ + ‖g₃ − (g₃)_Q‖)`. -/
theorem osc_sum_le {Q : TriadicCube d} {g₁ δ g₃ gN : Vec d → Vec d}
    (h₁ : MemVectorL2 (openCubeSet Q) g₁) (hδ : MemVectorL2 (openCubeSet Q) δ)
    (h₃ : MemVectorL2 (openCubeSet Q) g₃) (hsplit : ∀ x, gN x = g₁ x + δ x + g₃ x) :
    vecCubeLpENorm Q 4 (fun x => gN x - volumeAverageVec (cubeSet Q) gN) ≤
      2 * (vecCubeLpENorm Q 4 (fun x => g₁ x - volumeAverageVec (cubeSet Q) g₁) +
        vecCubeLpENorm Q 4 δ +
        vecCubeLpENorm Q 4 (fun x => g₃ x - volumeAverageVec (cubeSet Q) g₃)) := by
  rw [volumeAverageVec_cubeSet_eq_openCubeSet, volumeAverageVec_cubeSet_eq_openCubeSet,
    volumeAverageVec_cubeSet_eq_openCubeSet]
  set c : Vec d := volumeAverageVec (openCubeSet Q) g₁ + volumeAverageVec (openCubeSet Q) g₃
    with hc
  have hgN : MemVectorL2 (openCubeSet Q) gN := by
    have : gN = fun x => g₁ x + δ x + g₃ x := funext hsplit
    rw [this]
    unfold MemVectorL2 at *
    exact (h₁.add hδ).add h₃
  have hG : MemVectorL2 (openCubeSet Q) (fun x => gN x - c) :=
    SuperdiffusionCLT.Section3.Terms.memVectorL2_sub_const c hgN
  have h1 := SuperdiffusionCLT.Section2.Estimates.Stream.vecCubeLpENorm_sub_volumeAverageVec_le
    (q := 4) (by norm_num) hG
  rw [volumeAverageVec_openCubeSet_sub_const hgN c] at h1
  have e1 : (fun x => (gN x - c) - (volumeAverageVec (openCubeSet Q) gN - c)) =
      fun x => gN x - volumeAverageVec (openCubeSet Q) gN := by
    funext x
    abel
  rw [e1] at h1
  have e2 : (fun x => gN x - c) = fun x =>
      ((g₁ x - volumeAverageVec (openCubeSet Q) g₁) + δ x) +
        (g₃ x - volumeAverageVec (openCubeSet Q) g₃) := by
    funext x
    rw [hsplit x, hc]
    abel
  rw [e2] at h1
  have m₁ : AEStronglyMeasurable (hilbertifyVecField
      (fun x => g₁ x - volumeAverageVec (openCubeSet Q) g₁)) (normalizedCubeMeasure Q) :=
    SuperdiffusionCLT.Section3.Terms.aestronglyMeasurable_hilbertifyVecField_of_memVectorL2
      (SuperdiffusionCLT.Section3.Terms.memVectorL2_sub_const _ h₁)
  have m₃ : AEStronglyMeasurable (hilbertifyVecField
      (fun x => g₃ x - volumeAverageVec (openCubeSet Q) g₃)) (normalizedCubeMeasure Q) :=
    SuperdiffusionCLT.Section3.Terms.aestronglyMeasurable_hilbertifyVecField_of_memVectorL2
      (SuperdiffusionCLT.Section3.Terms.memVectorL2_sub_const _ h₃)
  have mδ : AEStronglyMeasurable (hilbertifyVecField δ) (normalizedCubeMeasure Q) :=
    SuperdiffusionCLT.Section3.Terms.aestronglyMeasurable_hilbertifyVecField_of_memVectorL2 hδ
  have mδ' : AEStronglyMeasurable (hilbertifyVecField (fun x =>
      (g₁ x - volumeAverageVec (openCubeSet Q) g₁) + δ x)) (normalizedCubeMeasure Q) := by
    have : hilbertifyVecField (fun x =>
        (g₁ x - volumeAverageVec (openCubeSet Q) g₁) + δ x) =
        hilbertifyVecField (fun x => g₁ x - volumeAverageVec (openCubeSet Q) g₁) +
          hilbertifyVecField δ := by
      funext x
      exact map_add (HilbertVec.linearEquivVec d).symm _ _
    rw [this]
    exact m₁.add mδ
  have h2 := vecCubeLpENorm_add_le (Q := Q) (q := 4) (by norm_num) mδ' m₃
  have h3 := vecCubeLpENorm_add_le (Q := Q) (q := 4) (by norm_num) m₁ mδ
  have h4 : vecCubeLpENorm Q 4 (fun x => gN x - volumeAverageVec (openCubeSet Q) gN) ≤
      2 * vecCubeLpENorm Q 4 (fun x =>
        ((g₁ x - volumeAverageVec (openCubeSet Q) g₁) + δ x) +
          (g₃ x - volumeAverageVec (openCubeSet Q) g₃)) := h1
  refine h4.trans ?_
  gcongr
  exact h2.trans (add_le_add h3 le_rfl)

/-- **Poincaré for the gradient of an `H¹` function with a weak Hessian**, on a subcube `Q` of the
cube `K`: `‖∇u − (∇u)_Q‖_{L̲⁴(Q)} ≤ C 3^{scale Q} ‖∇²u‖_{L̲⁴(Q)}`. -/
theorem osc_le_hessian [NeZero d] :
    ∃ C : ℝ, 0 < C ∧ ∀ {K Q : TriadicCube d}, openCubeSet Q ⊆ openCubeSet K →
      ∀ (u : H1Function (openCubeSet K)) (HD : HasWeakHessianOn (openCubeSet K) u),
        vecCubeLpENorm Q 4 (fun x => u.grad x - volumeAverageVec (cubeSet Q) u.grad) ≤
          ENNReal.ofReal (C * cubeScaleFactor Q) *
            SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 4
              (fun x => HilbertMat.ofMat (fun i j => HD.hess i j x)) := by
  obtain ⟨C, hC, hP⟩ := vecCubeLpENorm_sub_volumeAverageVec_le_h1 (d := d)
  refine ⟨C, hC, fun {K Q} hsub u HD => ?_⟩
  rw [volumeAverageVec_cubeSet_eq_openCubeSet]
  exact hP Q fun i => (HD.gradCoordH1Function i).restrict (isOpen_openCubeSet Q) hsub

/-- **Poincaré for a `C¹` field**: `‖F − (F)_Q‖_{L̲⁴(Q)} ≤ C 3^{scale Q} ‖∇F‖_{L̲⁴(Q)}`. -/
theorem osc_le_contDiff [NeZero d] :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : TriadicCube d) (F : Vec d → Vec d)
      (_hF : ∀ i, ContDiff ℝ 1 (fun x => F x i)),
        vecCubeLpENorm Q 4 (fun x => F x - volumeAverageVec (cubeSet Q) F) ≤
          ENNReal.ofReal (C * cubeScaleFactor Q) *
            SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 4
              (fun x => HilbertMat.ofMat
                (fun i j => fderiv ℝ (fun y => F y i) x (basisVec j))) := by
  obtain ⟨C, hC, hP⟩ := vecCubeLpENorm_sub_volumeAverageVec_le_contDiff (d := d)
  refine ⟨C, hC, fun Q F hF => ?_⟩
  rw [volumeAverageVec_cubeSet_eq_openCubeSet]
  exact hP Q (fun i x => F x i) hF

/-- The `L⁴` oscillation on a subcube of the three fields entering `e.crude.Fz.bound`: the pointwise
(in the sample) domination of
`‖∇u₀ − (∇u₀)_Q‖⁴ + ‖(∇u₂ + hsh) − (∇u₂ + hsh)_Q‖⁴` by the Poincaré terms of `∇u₀`, `∇u₁`, `hsh`
and the size of `δ = ∇u₂ − ∇u₁`. -/
theorem osc_pointwise [NeZero d] :
    ∃ C : ℝ, 0 < C ∧ ∀ {Kc n : ℕ}, n ≤ Kc →
      ∀ (u₀ u₁ u₂ : H1Function (openCubeSet (originCube d (Kc : ℤ))))
        (HD₀ : HasWeakHessianOn (openCubeSet (originCube d (Kc : ℤ))) u₀)
        (HD₁ : HasWeakHessianOn (openCubeSet (originCube d (Kc : ℤ))) u₁)
        (hsh : Vec d → Vec d) (_hshC : ∀ i, ContDiff ℝ 1 (fun x => hsh x i)),
        ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
          (vecCubeLpENorm Q 4 (fun x => u₀.grad x - volumeAverageVec (cubeSet Q) u₀.grad)) ^ 4 +
            (vecCubeLpENorm Q 4 (fun x => (u₂.grad x + hsh x) -
              volumeAverageVec (cubeSet Q) (fun y => u₂.grad y + hsh y))) ^ 4 ≤
          ENNReal.ofReal ((C * (3 : ℝ) ^ n) ^ 4) *
              (SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 4
                (fun x => HilbertMat.ofMat (fun i j => HD₀.hess i j x))) ^ 4 +
            1024 * (ENNReal.ofReal ((C * (3 : ℝ) ^ n) ^ 4) *
                (SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 4
                  (fun x => HilbertMat.ofMat (fun i j => HD₁.hess i j x))) ^ 4 +
              (vecCubeLpENorm Q 4 (fun x => u₂.grad x - u₁.grad x)) ^ 4 +
              ENNReal.ofReal ((C * (3 : ℝ) ^ n) ^ 4) *
                (SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 4
                  (fun x => HilbertMat.ofMat
                    (fun i j => fderiv ℝ (fun y => hsh y i) x (basisVec j)))) ^ 4) := by
  obtain ⟨C₁, hC₁, hH⟩ := osc_le_hessian (d := d)
  obtain ⟨C₂, hC₂, hS⟩ := osc_le_contDiff (d := d)
  refine ⟨C₁ + C₂, add_pos hC₁ hC₂, fun {Kc n} hn u₀ u₁ u₂ HD₀ HD₁ hsh hshC Q hQ => ?_⟩
  have hsub := openCubeSet_subset_of_mem_descendantsAtScale_originCube hn hQ
  have hscale := cubeScaleFactor_eq_of_mem_descendantsAtScale_originCube hn hQ
  set s : ℝ := (3 : ℝ) ^ n with hs
  have hs0 : 0 ≤ s := by positivity
  have hC1 : ENNReal.ofReal (C₁ * cubeScaleFactor Q) ≤ ENNReal.ofReal ((C₁ + C₂) * s) := by
    rw [hscale]
    exact ENNReal.ofReal_le_ofReal (by nlinarith only [hC₂, hs0])
  have hC2 : ENNReal.ofReal (C₂ * cubeScaleFactor Q) ≤ ENNReal.ofReal ((C₁ + C₂) * s) := by
    rw [hscale]
    exact ENNReal.ofReal_le_ofReal (by nlinarith only [hC₁, hs0])
  set c : ℝ≥0∞ := ENNReal.ofReal ((C₁ + C₂) * s) with hc
  set N₀ := SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 4
    (fun x => HilbertMat.ofMat (fun i j => HD₀.hess i j x)) with hN₀
  set N₁ := SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 4
    (fun x => HilbertMat.ofMat (fun i j => HD₁.hess i j x)) with hN₁
  set N₃ := SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 4
    (fun x => HilbertMat.ofMat (fun i j => fderiv ℝ (fun y => hsh y i) x (basisVec j)))
    with hN₃
  have hA : vecCubeLpENorm Q 4 (fun x => u₀.grad x - volumeAverageVec (cubeSet Q) u₀.grad) ≤
      c * N₀ := (hH hsub u₀ HD₀).trans (by gcongr)
  have ha : vecCubeLpENorm Q 4 (fun x => u₁.grad x - volumeAverageVec (cubeSet Q) u₁.grad) ≤
      c * N₁ := (hH hsub u₁ HD₁).trans (by gcongr)
  have hcc : vecCubeLpENorm Q 4 (fun x => hsh x - volumeAverageVec (cubeSet Q) hsh) ≤ c * N₃ :=
    (hS Q hsh hshC).trans (by gcongr)
  -- the sum splitting
  have hL2 : ∀ u : H1Function (openCubeSet (originCube d (Kc : ℤ))),
      MemVectorL2 (openCubeSet Q) u.grad := fun u =>
    SuperdiffusionCLT.Section3.Terms.memVectorL2_mono hsub u.grad_memVectorL2
  have hshL2 : MemVectorL2 (openCubeSet Q) hsh := by
    have hcont : Continuous hsh := continuous_pi fun i => (hshC i).continuous
    exact SuperdiffusionCLT.Section3.Terms.memVectorL2_mono hsub
      (SuperdiffusionCLT.Section3.Setup.memVectorL2_of_continuous (Kc : ℤ) hcont)
  have hδL2 : MemVectorL2 (openCubeSet Q) (fun x => u₂.grad x - u₁.grad x) :=
    (hL2 u₂).sub (hL2 u₁)
  have hB := osc_sum_le (Q := Q) (g₁ := u₁.grad) (δ := fun x => u₂.grad x - u₁.grad x)
    (g₃ := hsh) (gN := fun y => u₂.grad y + hsh y) (hL2 u₁) hδL2 hshL2
    (fun x => by abel)
  set a := vecCubeLpENorm Q 4 (fun x => u₁.grad x - volumeAverageVec (cubeSet Q) u₁.grad)
  set b := vecCubeLpENorm Q 4 (fun x => u₂.grad x - u₁.grad x)
  set cc := vecCubeLpENorm Q 4 (fun x => hsh x - volumeAverageVec (cubeSet Q) hsh)
  have hsum : a + b + cc ≤ c * N₁ + b + c * N₃ := by gcongr
  have hB4 : (vecCubeLpENorm Q 4 (fun x => (u₂.grad x + hsh x) -
      volumeAverageVec (cubeSet Q) (fun y => u₂.grad y + hsh y))) ^ 4 ≤
      1024 * ((c * N₁) ^ 4 + b ^ 4 + (c * N₃) ^ 4) := by
    calc _ ≤ (2 * (c * N₁ + b + c * N₃)) ^ 4 := by
          gcongr
          exact hB.trans (by gcongr)
      _ = 16 * (c * N₁ + b + c * N₃) ^ 4 := by
          rw [mul_pow]
          norm_num
      _ ≤ 16 * (64 * ((c * N₁) ^ 4 + b ^ 4 + (c * N₃) ^ 4)) := by
          gcongr
          exact add_add_pow_four_le _ _ _
      _ = 1024 * ((c * N₁) ^ 4 + b ^ 4 + (c * N₃) ^ 4) := by
          rw [← mul_assoc]
          norm_num
  have hA4 : (vecCubeLpENorm Q 4 (fun x => u₀.grad x - volumeAverageVec (cubeSet Q) u₀.grad)) ^ 4 ≤
      (c * N₀) ^ 4 := pow_le_pow_left' hA 4
  have hcpow : c ^ 4 = ENNReal.ofReal (((C₁ + C₂) * s) ^ 4) := by
    rw [hc, ENNReal.ofReal_pow (by positivity)]
  calc _ ≤ (c * N₀) ^ 4 + 1024 * ((c * N₁) ^ 4 + b ^ 4 + (c * N₃) ^ 4) := add_le_add hA4 hB4
    _ = _ := by
        rw [mul_pow, mul_pow, mul_pow, hcpow]

end

end SuperdiffusionCLT.Section5
