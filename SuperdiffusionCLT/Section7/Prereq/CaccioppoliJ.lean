/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.CaccioppoliI
public import SuperdiffusionCLT.Section7.Lipschitz.Carriers

/-!
# From the weak-solution core to `LipCaccInt`
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem ca1w_cubeLpNorm_le_const (Q : TriadicCube d) {f : Vec d → ℝ} {F : ℝ} (hF : 0 ≤ F)
    (h : ∀ᵐ x ∂normalizedCubeMeasure Q, |f x| ≤ F) : cubeLpNorm Q (2 : ℝ≥0∞) f ≤ F := by
  have : IsProbabilityMeasure (normalizedCubeMeasure Q) := ⟨normalizedCubeMeasure_apply_univ Q⟩
  by_cases hm : AEStronglyMeasurable f (normalizedCubeMeasure Q)
  · have h1 : eLpNorm f 2 (normalizedCubeMeasure Q) ≤ ENNReal.ofReal F := by
      have := eLpNorm_le_of_ae_bound (p := (2 : ℝ≥0∞)) (μ := normalizedCubeMeasure Q) (f := f)
        (C := F) hm (h.mono fun x hx => by rwa [Real.norm_eq_abs])
      simpa using this
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rwa [ENNReal.toReal_ofReal hF] at this
  · unfold cubeLpNorm
    rw [eLpNorm_of_not_aestronglyMeasurable hm]
    simpa using hF

/-- **`LipCaccInt` from the weak-solution core.** -/
theorem ca1w_lip_of_core {a A : CoeffField d} {ν S Cf C : ℝ} (m : ℕ) (hm1 : 1 ≤ m) (hS : 0 < S)
    (hν : 0 < ν) (hC : 1 ≤ C) (hCf : Cf ≤ C ^ 2)
    (hflux : ∀ u : H1Function (openCubeSet (originCube d (m : ℤ))),
      MemVectorL2 (openCubeSet (originCube d (m : ℤ))) (fun x => matVecMul (a x) (u.grad x)))
    (hbridge : ∀ (u : H1Function (openCubeSet (originCube d (m : ℤ)))) (f : Vec d → ℝ),
      MemVectorL2 (openCubeSet (originCube d (m : ℤ))) (fun x => matVecMul (a x) (u.grad x)) →
      IsWeakSolutionOn a (openCubeSet (originCube d (m : ℤ))) u f (fun _ => 0) →
      IsWeakSolutionOn A (openCubeSet (originCube d (m : ℤ))) u f (fun _ => 0))
    (hcore : ∀ (u : H1Function (openCubeSet (originCube d (m : ℤ)))) (f : Vec d → ℝ),
      MemLp f 2 (volume.restrict (openCubeSet (originCube d (m : ℤ)))) →
      IsWeakSolutionOn A (openCubeSet (originCube d (m : ℤ))) u f (fun _ => 0) →
      ν * cubeLpNorm (originCube d ((m : ℤ) - 1)) (2 : ℝ≥0∞) (fun x => Real.sqrt (vecNormSq (u.grad x))) ^ 2 ≤
        Cf * (S * (3 : ℝ) ^ (-2 * (m : ℤ)) *
            cubeLpNorm (originCube d (m : ℤ)) (2 : ℝ≥0∞)
              (fun x => u.toFun x - cubeAverage (originCube d (m : ℤ)) u.toFun) ^ 2 +
          S⁻¹ * (3 : ℝ) ^ (2 * (m : ℤ)) * cubeLpNorm (originCube d (m : ℤ)) (2 : ℝ≥0∞) f ^ 2)) :
    LipCaccInt a ν S C 1 m := by
  intro f F u hu hF hfF
  have hU : IsOpen (openCubeSet (originCube d (m : ℤ))) := isOpen_openCubeSet _
  have hfin : IsFiniteMeasure (volumeMeasureOn (openCubeSet (originCube d (m : ℤ)))) :=
    ⟨by
      simpa [volumeMeasureOn] using
        (isBounded_openCubeSet (originCube d (m : ℤ))).measure_lt_top⟩
  have hfin' : IsFiniteMeasure (volume.restrict (openCubeSet (originCube d (m : ℤ)))) := by
    simpa [volumeMeasureOn] using hfin
  have ht : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  have hsub : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by omega
  have key : ∀ f' : Vec d → ℝ, MemLp f' 2 (volume.restrict (openCubeSet (originCube d (m : ℤ)))) →
      IsWeakSolutionOn A (openCubeSet (originCube d (m : ℤ))) u f' (fun _ => 0) →
      cubeLpNorm (originCube d (m : ℤ)) (2 : ℝ≥0∞) f' ≤ F →
      Real.sqrt ν * Section6.cubeGradL2 (m - 1) u.grad ≤
        C * (Real.sqrt S * Section6.cubeFlat m u.toFun + (Real.sqrt S)⁻¹ * (3 : ℝ) ^ m * F) := by
    intro f' hf' hu' hfF'
    have h := hcore u f' hf' hu'
    rw [ca1w_zpow_neg_two, ca1w_zpow_two] at h
    have e1 : Section6.cubeGradL2 (m - 1) u.grad =
        cubeLpNorm (originCube d ((m : ℤ) - 1)) (2 : ℝ≥0∞) (fun x => Real.sqrt (vecNormSq (u.grad x))) := by
      unfold Section6.cubeGradL2 Section6.cubeL2 Section6.engNorm
      rw [hsub]
    have e2 : Section6.cubeFlat m u.toFun = ((3 : ℝ) ^ m)⁻¹ *
        cubeLpNorm (originCube d (m : ℤ)) (2 : ℝ≥0∞)
          (fun x => u.toFun x - cubeAverage (originCube d (m : ℤ)) u.toFun) := by
      unfold Section6.cubeFlat Section6.cubeL2
      rw [inv_pow]
    rw [e1, e2]
    exact ca1w_sqrt_step hν hS ENNReal.toReal_nonneg ENNReal.toReal_nonneg hfF' ht hC hCf h
  by_cases hfm : AEStronglyMeasurable f (volume.restrict (openCubeSet (originCube d (m : ℤ))))
  · have hfL2 : MemLp f 2 (volume.restrict (openCubeSet (originCube d (m : ℤ)))) :=
      MemLp.of_bound hfm F (hfF.mono fun x hx => by rwa [Real.norm_eq_abs])
    refine key f hfL2 (hbridge u f (hflux u) hu) ?_
    exact ca1w_cubeLpNorm_le_const _ hF (r1_ae_normalized _ hfF)
  · have hu0 := ca1w_nonmeas_weak hU hfin u hfF (hflux u) hfm hu
    refine key (fun _ => 0) (memLp_const 0) (hbridge u _ (hflux u) hu0) ?_
    unfold cubeLpNorm
    simpa using hF

end SuperdiffusionCLT.Section7
