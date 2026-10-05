/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.BoundaryDecayI

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal NNReal

/-!
# Bookkeeping for the sub-cube application

The affine functions `φ - ℓ₀` versus `u - m`, the translation of the face box, and the
normalized `L²` norm.
-/

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem r3d_vecDot_sub_z0 (e : Fin d) (m : ℤ) (b : Vec d) (x : Vec d) :
    vecDot b (x - r3c_z0 e m) =
      b e * r3c_nrm e m x + ∑ k ∈ Finset.univ.erase e, b k * x k := by
  unfold vecDot
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ e)]
  congr 1
  · simp [r3c_z0, r3c_nrm]
  · exact Finset.sum_congr rfl fun k hk => by
      have : k ≠ e := (Finset.mem_erase.1 hk).1
      simp [r3c_z0, this]

theorem r3d_u_sub_m (e : Fin d) (m : ℤ) (a0 : ℝ) (b0 : Vec d) {U : Set (Vec d)}
    {φ u : H1Function U} (hu1 : ∀ x, u.toFun x = φ.toFun x - b0 e * r3c_nrm e m x) (x : Vec d) :
    u.toFun x - r3d_m e a0 b0 x = φ.toFun x - (a0 + vecDot b0 (x - r3c_z0 e m)) := by
  rw [hu1 x, r3d_vecDot_sub_z0]
  unfold r3d_m
  ring

theorem r3d_vecDot_basis (e : Fin d) (y : Vec d) : vecDot (basisVec e : Vec d) y = y e := by
  simp [vecDot, basisVec, Pi.single_apply]

theorem r3d_affine_merge (e : Fin d) (m : ℤ) (b : Vec d) (c : ℝ) (x : Vec d) :
    vecDot (b + c • (basisVec e : Vec d)) (x - r3c_z0 e m) =
      vecDot b (x - r3c_z0 e m) + c * r3c_nrm e m x := by
  rw [p12_vecDot_add_left, p12_vecDot_smul_left, r3d_vecDot_basis]
  simp [r3c_z0, r3c_nrm]

theorem r3d_z0_sub_zT (e : Fin d) (m : ℤ) : r3c_z0 e (m - 1) - r3d_zT e m = r3c_z0 e m := by
  funext i
  by_cases hi : i = e
  · subst hi
    simp only [Pi.sub_apply, r3c_z0, r3d_zT, ite_true, r3d_pow_pred]
    ring
  · simp [r3c_z0, r3d_zT, hi]

theorem r3d_nrm_sub (e : Fin d) (m : ℤ) (x : Vec d) :
    r3c_nrm e (m - 1) (x + r3d_zT e m) = r3c_nrm e m x := by
  simp only [r3c_nrm, Pi.add_apply, r3d_zT, ite_true, r3d_pow_pred]
  ring

theorem r3d_preimage_faceBox (e : Fin d) (m : ℤ) (s : ℝ) :
    (fun x : Vec d => x + r3d_zT e m) ⁻¹'
        axisCube (r3c_z0 e (m - 1) + r3c_faceBase e s) s =
      axisCube (r3c_z0 e m + r3c_faceBase e s) s := by
  ext x
  have hz : ∀ i, r3c_z0 e (m - 1) i - r3d_zT e m i = r3c_z0 e m i := fun i =>
    congrFun (r3d_z0_sub_zT e m) i
  simp only [axisCube, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo,
    Pi.add_apply]
  refine forall_congr' fun i => ?_
  have := hz i
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith only [h1, h2, this]

theorem r3d_norm_sq_normalized (m : ℤ) {F : Vec d → ℝ}
    (hF : MemLp F 2 (normalizedCubeMeasure (originCube d m))) :
    ((eLpNorm F 2 (normalizedCubeMeasure (originCube d m))).toReal) ^ 2 =
      (((3 : ℝ) ^ m) ^ d)⁻¹ * ∫ x in openCubeSet (originCube d m), F x ^ 2 := by
  rw [r3d_eLpNorm_sq_eq hF, normalizedCubeMeasure_eq_smul, integral_smul_measure,
    r3c_cubeVolume_originCube, ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [Real.norm_eq_abs, sq_abs]

theorem r3d_sq_to_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x ^ 2 ≤ y ^ 2) : x ≤ y :=
  (pow_le_pow_iff_left₀ hx hy two_ne_zero).1 h

end SuperdiffusionCLT.Section7
