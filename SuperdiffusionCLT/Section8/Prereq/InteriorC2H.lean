/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.InteriorC2G

/-!
# The weak equation `-Δ(∂ₖu) = rhs` on the inner cube
-/

@[expose] public section

open MeasureTheory Filter Topology Homogenization
open scoped ENNReal

namespace SuperdiffusionCLT.Section8

variable {d : ℕ}

theorem intC2_vWeak (n : ℤ) {P : ℝ} (hP2 : 2 ≤ P) {a : CoeffField d} {nu mu : ℝ} (hnu : 0 < nu)
    (hsk : ∀ y i j, a y i j + a y j i = if i = j then 2 * nu else 0)
    (ha : ∀ i j, ContDiff ℝ 2 fun y ↦ a y i j) {g : Vec d → ℝ} (hg : ContDiff ℝ 1 g)
    {uB : H1Function (intC2_box d ((3 : ℝ) ^ n / 4))}
    (hw : intC2_Weak a mu g (intC2_box d ((3 : ℝ) ^ n / 4)) uB)
    {G : Fin d → Vec d → ℝ} {Hs : Fin d → Fin d → Vec d → ℝ}
    (hGae : ∀ i, (G i) =ᵐ[volume.restrict (intC2_box d ((3 : ℝ) ^ n / 4))] fun x ↦ uB.grad x i)
    (hGc : ∀ i, ContinuousOn (G i) (intC2_box d ((3 : ℝ) ^ n / 4)))
    (hHs : ∀ i j, HasWeakPartialDerivOn (intC2_box d ((3 : ℝ) ^ n / 4)) j (G i) (Hs i j))
    (hHsL : ∀ i j, MemLp (Hs i j) (ENNReal.ofReal P)
      (volume.restrict (intC2_box d ((3 : ℝ) ^ n / 4))))
    (k : Fin d) (v : H1Function (openCubeSet (originCube d (n - 1))))
    (hvg : ∀ x j, v.grad x j = Hs k j x) :
    SuperdiffusionCLT.Section7.IsWeakSolutionOn (fun _ ↦ (1 : Mat d))
      (openCubeSet (originCube d (n - 1))) v (intC2_rhs a nu mu g G Hs k) (fun _ ↦ 0) := by
  have hB : IsOpen (intC2_box d ((3 : ℝ) ^ n / 4)) := intC2_isOpen_box _
  have hU2 : IsOpen (openCubeSet (originCube d (n - 1))) := isOpen_openCubeSet _
  have hsub : openCubeSet (originCube d (n - 1)) ⊆ intC2_box d ((3 : ℝ) ^ n / 4) :=
    intC2_box_quarter_sub n
  have : IsFiniteMeasure (volume.restrict (intC2_box d ((3 : ℝ) ^ n / 4))) := intC2_isFinite_box n
  have hP2' : (2 : ENNReal) ≤ ENNReal.ofReal P := by
    rw [← ENNReal.ofReal_ofNat]; exact ENNReal.ofReal_le_ofReal hP2
  have hHs2 : ∀ i j, MemLp (Hs i j) 2 (volume.restrict (intC2_box d ((3 : ℝ) ^ n / 4))) :=
    fun i j ↦ (hHsL i j).mono_exponent hP2'
  have hu' : ∀ i, HasWeakPartialDerivOn (intC2_box d ((3 : ℝ) ^ n / 4)) i uB.toFun (G i) :=
    fun i ↦ intC2_weak_congr Filter.EventuallyEq.rfl (hGae i).symm (uB.hasWeakGradient i)
  have hsym := fun j k ↦ intC2_hess_symm hB hu' hHs hHs2 j k
  have hhv := intC2_rhs_memLp n (nu := nu) (mu := mu) ha hg hGc hHsL k
  have hhv2 : MemLp (intC2_rhs a nu mu g G Hs k) 2
      (volume.restrict (openCubeSet (originCube d (n - 1)))) :=
    (SuperdiffusionCLT.Section7.memLp_restrict_of_normalized _ hhv).mono_exponent hP2'
  intro w
  have key := intW2p_h10_of_smooth (U := openCubeSet (originCube d (n - 1)))
    (W := fun x ↦ v.grad x) (s := fun x ↦ -intC2_rhs a nu mu g G Hs k x) v.grad_memL2 hhv2.neg
    (fun φ hφ hφc hφs ↦ by
      have hφB : tsupport φ ⊆ intC2_box d ((3 : ℝ) ^ n / 4) := hφs.trans hsub
      have eq := intC2_diff_eq hB hsk ha hg hw hGae hGc hHs hHs2 k hφ hφc hφB
      have hsymall : ∀ᵐ x ∂(volume.restrict (intC2_box d ((3 : ℝ) ^ n / 4))),
          ∀ i, Hs i k x = Hs k i x := ae_all_iff.2 fun i ↦ hsym i k
      have hzero : ∀ F : Vec d → ℝ, (∀ x, x ∉ tsupport φ → F x = 0) →
          ∫ x in intC2_box d ((3 : ℝ) ^ n / 4), F x = ∫ x in openCubeSet (originCube d (n - 1)), F x :=
        fun F hF ↦ intC2_set_eq hsub (F := F) (fun x hx ↦ hF x fun h ↦ hx (hφs h))
      -- Step A
      have hdφ := fun j ↦ intW2p_d1_smooth hφ j
      have intg : ∀ j ∈ Finset.univ, Integrable (fun x ↦ Hs k j x * fderiv ℝ φ x (basisVec j))
          (volume.restrict (intC2_box d ((3 : ℝ) ^ n / 4))) := fun j _ ↦
        intW2p_integrable_mul (hHs2 k j) (hdφ j).continuous (intW2p_d1_cs hφc j)
      have A1 : ∑ j, ∫ x in intC2_box d ((3 : ℝ) ^ n / 4), Hs j k x * fderiv ℝ φ x (basisVec j) =
          ∫ x in openCubeSet (originCube d (n - 1)),
            vecDot (v.grad x) (fun i ↦ fderiv ℝ φ x (basisVec i)) := by
        rw [← hzero (fun x ↦ vecDot (v.grad x) (fun i ↦ fderiv ℝ φ x (basisVec i))) (fun x hx ↦ by
          simp [fderiv_of_notMem_tsupport ℝ hx, vecDot])]
        simp only [vecDot, hvg]
        rw [integral_finsetSum _ intg]
        refine Finset.sum_congr rfl fun j _ ↦ integral_congr_ae ?_
        filter_upwards [hsym j k] with x hx
        rw [hx]
      -- Step B
      have B1 : ∫ x in intC2_box d ((3 : ℝ) ^ n / 4), (fderiv ℝ g x (basisVec k) - mu * G k x -
          ∑ i, (intW2p_drift a x i * Hs i k x +
            fderiv ℝ (fun y ↦ intW2p_drift a y i) x (basisVec k) * G i x)) * φ x =
          nu * ∫ x in openCubeSet (originCube d (n - 1)), intC2_rhs a nu mu g G Hs k x * φ x := by
        rw [← hzero (fun x ↦ intC2_rhs a nu mu g G Hs k x * φ x) (fun x hx ↦ by
          rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]), ← integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards [hsymall] with x hx
        simp only [intC2_rhs, hx]
        field_simp
      rw [A1, B1] at eq
      have e2 : ∫ x in openCubeSet (originCube d (n - 1)), -intC2_rhs a nu mu g G Hs k x * φ x =
          -∫ x in openCubeSet (originCube d (n - 1)), intC2_rhs a nu mu g G Hs k x * φ x := by
        rw [← integral_neg]
        exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp only [neg_mul])
      rw [e2]
      have := mul_left_cancel₀ hnu.ne' eq
      linarith only [this]) w
  have h0 : ∀ x, vecDot ((0 : Vec d)) (w.toH1Function.grad x) = 0 := fun x ↦ by simp [vecDot]
  simp only [intW2p_matVecMul_one, h0, integral_zero, add_zero]
  have : ∫ x in openCubeSet (originCube d (n - 1)), -intC2_rhs a nu mu g G Hs k x *
      w.toH1Function.toFun x = -∫ x in openCubeSet (originCube d (n - 1)),
        intC2_rhs a nu mu g G Hs k x * w.toH1Function.toFun x := by
    rw [← integral_neg]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp only [neg_mul])
  rw [this] at key
  linarith only [key]

end SuperdiffusionCLT.Section8
