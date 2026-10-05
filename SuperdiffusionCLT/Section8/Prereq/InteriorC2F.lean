/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.InteriorC2E
public import Mathlib.Order.CompletePartialOrder

/-!
# Symmetry of the weak Hessian and the data of the equation for `∂ₖu`
-/

@[expose] public section

open MeasureTheory Filter Topology Homogenization
open scoped ENNReal

namespace SuperdiffusionCLT.Section8

variable {d : ℕ}

/-- The weak Hessian of a function with continuous weak gradient is symmetric. -/
theorem intC2_hess_symm {B : Set (Vec d)} (hB : IsOpen B) {uf : Vec d → ℝ}
    {G : Fin d → Vec d → ℝ} {Hs : Fin d → Fin d → Vec d → ℝ}
    (hu : ∀ i, HasWeakPartialDerivOn B i uf (G i))
    (hHs : ∀ i j, HasWeakPartialDerivOn B j (G i) (Hs i j))
    (hHs2 : ∀ i j, MemLp (Hs i j) 2 (volume.restrict B)) (j k : Fin d) :
    Hs j k =ᵐ[volume.restrict B] Hs k j := by
  have hid : ∀ j k (ψ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ B → ∫ x in B, Hs j k x * ψ x = ∫ x in B, uf x * intW2p_dd ψ k j x :=
    fun j k ψ hψ hψc hψs ↦ by
    have h1 := hHs j k ψ hψ hψc hψs
    have h2 := hu j (fun y ↦ fderiv ℝ ψ y (basisVec k)) (intW2p_d1_smooth hψ k)
      (intW2p_d1_cs hψc k) ((intC2_d1_ts k).trans hψs)
    have h3 : ∀ x, fderiv ℝ (fun y ↦ fderiv ℝ ψ y (basisVec k)) x (basisVec j) =
        intW2p_dd ψ k j x := fun x ↦ rfl
    simp only [h3] at h2
    linarith only [h1, h2]
  have hloc : LocallyIntegrableOn (fun x ↦ Hs j k x - Hs k j x) B (volume.restrict B) :=
    (((hHs2 j k).sub (hHs2 k j)).locallyIntegrable (by norm_num)).locallyIntegrableOn B
  have hzero := hB.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume.restrict B) hloc
    (fun ψ hψ hψc hψs ↦ by
      have i1 : Integrable (fun x ↦ Hs j k x * ψ x) (volume.restrict B) :=
        intW2p_integrable_mul (hHs2 j k) hψ.continuous hψc
      have i2 : Integrable (fun x ↦ Hs k j x * ψ x) (volume.restrict B) :=
        intW2p_integrable_mul (hHs2 k j) hψ.continuous hψc
      have e : ∫ x, ψ x • (Hs j k x - Hs k j x) ∂(volume.restrict B) =
          (∫ x in B, Hs j k x * ψ x) - ∫ x in B, Hs k j x * ψ x := by
        rw [← integral_sub i1 i2]
        exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp only [smul_eq_mul]; ring)
      rw [e, hid j k ψ hψ hψc hψs, hid k j ψ hψ hψc hψs]
      have hs : intW2p_dd ψ k j = intW2p_dd ψ j k := funext fun x ↦
        intW2p_dd_symm ψ (hψ.of_le (by simp)) k j x
      rw [hs, sub_self])
  filter_upwards [hzero, ae_restrict_mem hB.measurableSet] with x hx hxB
  exact sub_eq_zero.1 (hx hxB)

theorem intC2_memLp_cube_of_restrict {Q : TriadicCube d} {B : Set (Vec d)}
    (hsub : openCubeSet Q ⊆ B) {f : Vec d → ℝ} {p : ENNReal}
    (h : MemLp f p (volume.restrict B)) : MemLp f p (normalizedCubeMeasure Q) :=
  SuperdiffusionCLT.Section7.memLp_normalized_of_restrict Q
    (h.mono_measure (Measure.restrict_mono hsub le_rfl))

end SuperdiffusionCLT.Section8
