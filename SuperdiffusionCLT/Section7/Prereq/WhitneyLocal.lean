/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.WhitneyInterpolantC
public import SuperdiffusionCLT.Section6.Engine.PoincCube
public import Homogenization.Book.Ch03.Theorems.CoarseCaccioppoliRHS.ZeroTraceValue
public import Homogenization.Book.Ch01.Theorems.DualToCircLoss.FiniteLoss
public import Homogenization.Book.Ch03.Theorems.PublicInternalBridges.EndPoints
public import SuperdiffusionCLT.Section7.Prereq.RhsLemmaC

/-!
# The dual fractional Poincare inequality on an origin cube

For `v ∈ H¹(□_n)`: `3^{-n} ‖v - (v)_{□_n}‖_{L̲²(□_n)} ≤ C · 3^{-n/4} ‖∇v‖_{Ĥ^{-1/4}(□_n)}`, with
`C = C(d)` independent of `n` (the dual form of
the fractional Poincare inequality).  Route: the fluctuation-to-negative-Besov bound at `t = 1/4`,
then the reverse comparison `[F]_{B^{-1/2}} ≤ 220 · (dual norm at 1/4)`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

open Homogenization

variable {d : ℕ}

/-- The dual fractional Poincare inequality on an origin cube (real form). -/
theorem wh2_poincare_dual (d : ℕ) [NeZero d] :
    ∃ Cp : ℝ, 0 < Cp ∧ ∀ (n : ℕ) (v : H1Function (openCubeSet (originCube d (n : ℤ)))),
      cubeLpNorm (originCube d (n : ℤ)) 2 (cubeFluctuation (originCube d (n : ℤ)) (fun x => v x)) ≤
        Cp * (3 : ℝ) ^ n *
          Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo (originCube d (n : ℤ)) (1 / 4)
            v.grad := by
  set Kc : ℝ := ((d : ℝ) * Legacy.cubeNeumannW22CalderonZygmundConstant d *
    (3 : ℝ) ^ ((d : ℝ) + 1)) * ((d : ℝ) * Real.sqrt
      ((1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - 1 / 4)))⁻¹)) with hKc
  have hP : 0 ≤ (d : ℝ) * Legacy.cubeNeumannW22CalderonZygmundConstant d := by
    have h := Homogenization.fullVectorPoincareCubeConstant_nonneg (originCube d 0)
    rwa [fullVectorPoincareCubeConstant_eq_dimensionConstant] at h
  have hKc0 : 0 ≤ Kc := by
    rw [hKc]
    exact mul_nonneg (mul_nonneg hP (Real.rpow_nonneg (by norm_num) _))
      (mul_nonneg (Nat.cast_nonneg d) (Real.sqrt_nonneg _))
  refine ⟨Kc * (55 * ((1 / 2 : ℝ)⁻¹) ^ (2 : ℕ)) + 1, ?_, ?_⟩
  · have : 0 ≤ Kc * (55 * ((1 / 2 : ℝ)⁻¹) ^ (2 : ℕ)) := by positivity
    linarith only [this]
  intro n v
  suffices H : ∀ Q : TriadicCube d, Q = originCube d (n : ℤ) → ∀ v : H1Function (openCubeSet Q),
      cubeLpNorm Q 2 (cubeFluctuation Q (fun x => v x)) ≤
        (Kc * (55 * ((1 / 2 : ℝ)⁻¹) ^ (2 : ℕ)) + 1) * (3 : ℝ) ^ n *
          Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo Q (1 / 4) v.grad from
    H _ rfl v
  intro Q hQ v
  have hfl := Book.Ch03.cubeBesovScaleWeight_one_mul_cubeLpNorm_fluctuation_le_grad_negativeBesovTwo
    (Q := Q) (t := 1 / 4) v (by norm_num) (by norm_num)
  have hPoinc : Book.Ch01.Legacy.fullVectorPoincareConstant Q =
      (d : ℝ) * Legacy.cubeNeumannW22CalderonZygmundConstant d := by
    simp only [Book.Ch01.Legacy.fullVectorPoincareConstant,
      fullVectorPoincareCubeConstant_eq_dimensionConstant]
  rw [hPoinc, show (2 : ℝ) * (1 / 4) = 1 / 2 by norm_num] at hfl
  have hweight : cubeBesovScaleWeight (1 : ℝ) Q = ((3 : ℝ)⁻¹) ^ n := by
    simp [cubeBesovScaleWeight, hQ, Real.rpow_neg_one]
  rw [hweight] at hfl
  have hK : ((d : ℝ) * Legacy.cubeNeumannW22CalderonZygmundConstant d *
      (3 : ℝ) ^ ((d : ℝ) + 1)) * ((d : ℝ) * Real.sqrt
        ((1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - 1 / 4)))⁻¹)) = Kc := rfl
  rw [hK] at hfl
  have hsemi := Book.Ch01.Legacy.cubeBesovNegativeVectorSeminormTwo_le_halfDual_fiftyFive_inv_sq
    (d := d) Q v.grad (s := 1 / 2) (by norm_num) (by norm_num)
    (fun i => v.grad_memL2_normalizedCubeMeasure i)
  have hnd : Book.Ch01.Legacy.normalizedDualNegativeBesovVectorNormTwo Q (1 / 2 / 2) v.grad =
      Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo Q (1 / 4) v.grad := by
    unfold Book.Ch01.Legacy.normalizedDualNegativeBesovVectorNormTwo
      Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
    rw [show (1 / 2 / 2 : ℝ) = 1 / 4 by norm_num, Book.Ch03.publicDualBesovScaleWeight_eq_cubeBesovScaleWeight]
  rw [hnd] at hsemi
  set Nd := Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo Q (1 / 4) v.grad with hNd
  set F := cubeLpNorm Q 2 (cubeFluctuation Q fun x => v x) with hF
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hmul : F ≤ (3 : ℝ) ^ n * (Kc * (55 * ((1 / 2 : ℝ)⁻¹) ^ (2 : ℕ) * Nd)) := by
    have e : ((3 : ℝ)⁻¹) ^ n = ((3 : ℝ) ^ n)⁻¹ := inv_pow _ _
    rw [e] at hfl
    have h1 : F ≤ (3 : ℝ) ^ n * (Kc * cubeBesovNegativeVectorSeminormTwo Q (1 / 2) v.grad) := by
      have := mul_le_mul_of_nonneg_left hfl h3.le
      rwa [← mul_assoc, mul_inv_cancel₀ h3.ne', one_mul] at this
    refine h1.trans ?_
    gcongr
  have hN0 : 0 ≤ Nd := by
    rw [← hnd]
    exact Book.Ch01.Legacy.normalizedDualNegativeBesovVectorNormTwo_nonneg _ _ _
  calc F ≤ (3 : ℝ) ^ n * (Kc * (55 * ((1 / 2 : ℝ)⁻¹) ^ (2 : ℕ) * Nd)) := hmul
    _ ≤ _ := by
      have h4 : 0 ≤ (3 : ℝ) ^ n * Nd := mul_nonneg h3.le hN0
      have e : (3 : ℝ) ^ n * (Kc * (55 * ((1 / 2 : ℝ)⁻¹) ^ (2 : ℕ) * Nd)) =
          (Kc * (55 * ((1 / 2 : ℝ)⁻¹) ^ (2 : ℕ))) * ((3 : ℝ) ^ n * Nd) := by ring
      rw [e]
      have e2 : (Kc * (55 * ((1 / 2 : ℝ)⁻¹) ^ (2 : ℕ)) + 1) * (3 : ℝ) ^ n * Nd =
          (Kc * (55 * ((1 / 2 : ℝ)⁻¹) ^ (2 : ℕ))) * ((3 : ℝ) ^ n * Nd) + (3 : ℝ) ^ n * Nd := by ring
      rw [e2]
      linarith only [h4]

/-- The dual fractional Poincare inequality on an origin cube, extended-real form. -/
theorem wh2_poincare_dual_enorm (d : ℕ) [NeZero d] :
    ∃ Cp : ℝ, 0 < Cp ∧ ∀ (n : ℕ) (v : H1Function (openCubeSet (originCube d (n : ℤ)))),
      SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (n : ℤ)) 2
          (fun x => v x - cubeAverage (originCube d (n : ℤ)) (fun x => v x)) ≤
        ENNReal.ofReal (Cp * (3 : ℝ) ^ n) *
          ENNReal.ofReal
            (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo (originCube d (n : ℤ)) (1 / 4)
              v.grad) := by
  obtain ⟨Cp, hCp, H⟩ := wh2_poincare_dual d
  refine ⟨Cp, hCp, fun n v => ?_⟩
  have hmem : MemLp (fun x => v x - cubeAverage (originCube d (n : ℤ)) (fun x => v x)) 2
      (normalizedCubeMeasure (originCube d (n : ℤ))) :=
    (v.memL2_normalizedCubeMeasure).sub (memLp_const _)
  have hfin : eLpNorm (fun x => v x - cubeAverage (originCube d (n : ℤ)) (fun x => v x)) 2
      (normalizedCubeMeasure (originCube d (n : ℤ))) ≠ ⊤ := hmem.eLpNorm_ne_top
  have h := H n v
  have e : SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (n : ℤ)) 2
        (fun x => v x - cubeAverage (originCube d (n : ℤ)) (fun x => v x)) =
      ENNReal.ofReal (cubeLpNorm (originCube d (n : ℤ)) 2
        (cubeFluctuation (originCube d (n : ℤ)) (fun x => v x))) := by
    unfold SuperdiffusionCLT.Section2.Norms.cubeLpENorm cubeLpNorm cubeFluctuation
    rw [ENNReal.ofReal_toReal hfin]
  rw [e, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by simpa only [mul_assoc] using h)

end SuperdiffusionCLT.Section7
