/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Root.GeneratorsC
public import SuperdiffusionCLT.Section8.Prereq.InteriorC2K
public import SuperdiffusionCLT.Section8.Prereq.ExitEstimateC

/-!
# Passing to the limit in the weak equation, and the coordinate energy

* `gen_weak_test`: a weak solution tested against smooth compactly supported functions;
* `gen_limit_weak`: the weak equation passes to `L²` limits of the gradients;
* `gen_coord_energy`: an energy bound controls each coordinate in `L²`.
-/

@[expose] public section

open Homogenization MeasureTheory Filter Topology SuperdiffusionCLT.Section7
open scoped ENNReal

namespace SuperdiffusionCLT.Section8

variable {d : ℕ}

theorem gen_weak_test {U : Set (Vec d)} (hU : IsOpen U) {a : CoeffField d} {G : Vec d → ℝ}
    {u : H1Function U} (hsol : IsWeakSolutionOn a U u G (fun _ => 0)) :
    intC2_Weak a 0 G U u := by
  intro φ hφ hc hs
  have h := hsol (H10Function.ofContDiff hU hφ hc hs)
  have h0 : ∫ x in U, vecDot ((fun _ => (0 : Vec d)) x) ((H10Function.ofContDiff hU hφ hc hs).toH1Function.grad x) = 0 := by
    simp [vecDot]
  rw [h0, add_zero] at h
  simp only [zero_mul, add_zero]
  exact h

theorem gen_flux_eq (A : Mat d) (g X : Vec d) :
    vecDot (matVecMul A g) X = ∑ i, ∑ j, (A i j * X i) * g j := by
  simp only [vecDot, matVecMul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem gen_limit_weak {U : Set (Vec d)} {a : CoeffField d} {G : Vec d → ℝ}
    (ha : ∀ i j, Continuous fun y => a y i j) (f : ℕ → H1Function U) (W : H1Function U)
    (hf : ∀ n, intC2_Weak a 0 G U (f n))
    (hlim : ∀ j : Fin d, Tendsto (fun n => eLpNorm (fun x => (f n).grad x j - W.grad x j) 2
      (volume.restrict U)) atTop (𝓝 0)) :
    intC2_Weak a 0 G U W := by
  intro φ hφ hc hs
  have hdφ : ∀ i, Continuous fun x => fderiv ℝ φ x (basisVec i) := fun i =>
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcs : ∀ i, HasCompactSupport fun x => fderiv ℝ φ x (basisVec i) := fun i => by
    have := hc.fderiv (𝕜 := ℝ)
    exact this.comp_left (g := fun L : Vec d →L[ℝ] ℝ => L (basisVec i)) (by simp)
  set h : Fin d → Fin d → Vec d → ℝ := fun i j x => a x i j * fderiv ℝ φ x (basisVec i) with hh
  have hhm : ∀ i j, MemLp (h i j) 2 (volume.restrict U) := fun i j =>
    (((ha i j).mul (hdφ i)).memLp_of_hasCompactSupport (μ := volume)
      ((hcs i).mul_left (f := fun x => a x i j))).restrict U
  have key : ∀ H : H1Function U, ∫ x in U, vecDot (matVecMul (a x) (H.grad x))
      (fun i => fderiv ℝ φ x (basisVec i)) =
      ∑ i, ∑ j, ∫ x in U, h i j x * H.grad x j := by
    intro H
    have e : ∀ x, vecDot (matVecMul (a x) (H.grad x)) (fun i => fderiv ℝ φ x (basisVec i)) =
        ∑ i, ∑ j, h i j x * H.grad x j := fun x => by
      rw [gen_flux_eq]
    simp only [e]
    rw [integral_finsetSum (f := fun i x => ∑ j, h i j x * H.grad x j) _ fun i _ =>
      integrable_finsetSum _ fun j _ => (hhm i j).integrable_mul (H.gradMemL2 j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum (f := fun j x => h i j x * H.grad x j) _ fun j _ =>
      (hhm i j).integrable_mul (H.gradMemL2 j)]
  have hT : Tendsto (fun n => ∑ i, ∑ j, ∫ x in U, h i j x * (f n).grad x j) atTop
      (𝓝 (∑ i, ∑ j, ∫ x in U, h i j x * W.grad x j)) := by
    refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
    exact domId_tendsto_integral_mul (hhm i j) (fun n => (f n).gradMemL2 j) (W.gradMemL2 j)
      (hlim j)
  have hconst : ∀ n, ∑ i, ∑ j, ∫ x in U, h i j x * (f n).grad x j = ∫ x in U, G x * φ x := by
    intro n
    have := hf n φ hφ hc hs
    rw [key] at this
    simpa using this
  have hT' := hT.congr hconst
  have := tendsto_nhds_unique hT' tendsto_const_nhds
  simp only [zero_mul, add_zero]
  rw [key W]
  exact this

/-- An energy bound on a set controls each coordinate in `L²`. -/
theorem gen_coord_energy {S : Set (Vec d)} {g : Vec d → Vec d} {E : ℝ}
    (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict S))
    (hE : ∫ x in S, vecNormSq (g x) ≤ E) (i : Fin d) :
    eLpNorm (fun x => g x i) 2 (volume.restrict S) ≤ ENNReal.ofReal (Real.sqrt E) := by
  have hint : Integrable (fun x => vecNormSq (g x)) (volume.restrict S) := by
    unfold vecNormSq vecDot
    exact integrable_finsetSum _ fun j _ => (hg j).integrable_mul (hg j)
  rw [(hg i).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  simp only [ENNReal.toReal_ofNat]
  have h1 : ∫ x in S, ‖g x i‖ ^ (2 : ℝ) ≤ E := by
    refine le_trans ?_ hE
    refine integral_mono ((hg i).integrable_norm_rpow (by norm_num) (by norm_num)) hint fun x => ?_
    rw [Real.norm_eq_abs, Real.rpow_two, sq_abs]
    unfold vecNormSq vecDot
    exact Finset.single_le_sum (f := fun j => g x j * g x j) (fun j _ => mul_self_nonneg _)
      (Finset.mem_univ i) |>.trans' (by rw [sq])
  rw [Real.sqrt_eq_rpow, one_div]
  exact Real.rpow_le_rpow (integral_nonneg fun x => by positivity) h1 (by norm_num)

end SuperdiffusionCLT.Section8
