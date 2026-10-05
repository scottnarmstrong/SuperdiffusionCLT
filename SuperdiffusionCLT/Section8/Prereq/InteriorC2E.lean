/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.InteriorC2D

/-!
# The equation for a partial derivative

If `u` solves `-∇·(a∇u) + μu = g` weakly in an open set `B` and `u` has a continuous gradient `G`
with weak derivatives `Hs` in `L²`, then testing the equation against `∂ₖψ` and integrating by
parts (against the `C¹` test functions `cᵢψ`, where `c` is the drift of `a`) gives
`ν ∑ⱼ ∫ Hs_{jk} ∂ⱼψ = ∫ (∂ₖg - μ Gₖ - ∑ᵢ (cᵢ Hs_{ik} + ∂ₖcᵢ Gᵢ)) ψ`.
-/

@[expose] public section

open MeasureTheory Filter Topology Homogenization
open scoped ENNReal

namespace SuperdiffusionCLT.Section8

variable {d : ℕ}

theorem intC2_drift_d1_cont {a : CoeffField d} (ha : ∀ i j, ContDiff ℝ 2 fun y ↦ a y i j)
    (i k : Fin d) : Continuous fun y ↦ fderiv ℝ (fun y ↦ intW2p_drift a y i) y (basisVec k) :=
  ((intW2p_drift_contDiff ha i).continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- Integration by parts of `∫ G · ∂ₖ(cψ)` for a continuous `G` with weak derivative `H`. -/
theorem intC2_ibp_mul {B : Set (Vec d)} (hB : IsOpen B) {G H c ψ : Vec d → ℝ} {k : Fin d}
    (hGc : ContinuousOn G B) (hH : MemLp H 2 (volume.restrict B))
    (hweak : HasWeakPartialDerivOn B k G H) (hc : ContDiff ℝ 1 c)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ B) :
    ∫ x in B, G x * (c x * fderiv ℝ ψ x (basisVec k)) =
      -(∫ x in B, H x * (c x * ψ x)) - ∫ x in B, G x * (fderiv ℝ c x (basisVec k) * ψ x) := by
  have hψ1 : ContDiff ℝ 1 fun x ↦ c x * ψ x := hc.mul (hψ.of_le (by exact_mod_cast le_top))
  have hcs : HasCompactSupport fun x ↦ c x * ψ x := hψc.mul_left
  have hs : tsupport (fun x ↦ c x * ψ x) ⊆ B := tsupport_mul_subset_right.trans hψs
  have hGl : LocallyIntegrableOn G B volume := hGc.locallyIntegrableOn hB.measurableSet
  have hHl : LocallyIntegrableOn H B volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict (hH.locallyIntegrable (by norm_num))
  have h1 := intW2p_ibp_c1 hB hGl hHl hweak hψ1 hcs hs
  have hpr : ∀ x, fderiv ℝ (fun x ↦ c x * ψ x) x (basisVec k) =
      c x * fderiv ℝ ψ x (basisVec k) + ψ x * fderiv ℝ c x (basisVec k) := fun x ↦ by
    rw [fderiv_fun_mul (hc.differentiable (by simp) x)
      ((hψ.differentiable (by simp)) x)]
    simp
  have hψcont : Continuous ψ := hψ.continuous
  have hdψ := intC2_d1_cont hψ k
  have hdc : Continuous fun x ↦ fderiv ℝ c x (basisVec k) :=
    (hc.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have a1 := intC2_integral_eq hB (θ := fun x ↦ c x * fderiv ℝ ψ x (basisVec k)) (f := G)
    (hc.continuous.mul hdψ) ((intW2p_d1_cs hψc k).mul_left)
    (tsupport_mul_subset_right.trans ((intC2_d1_ts k).trans hψs)) hGc
  have a2 := intC2_integral_eq hB (θ := fun x ↦ ψ x * fderiv ℝ c x (basisVec k)) (f := G)
    (hψcont.mul hdc) (hψc.mul_right)
    (tsupport_mul_subset_left.trans hψs) hGc
  have hsplit : ∫ x in B, G x * fderiv ℝ (fun x ↦ c x * ψ x) x (basisVec k) =
      (∫ x in B, (c x * fderiv ℝ ψ x (basisVec k)) * G x) +
        ∫ x in B, (ψ x * fderiv ℝ c x (basisVec k)) * G x := by
    rw [← integral_add a1.1.integrableOn a2.1.integrableOn]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp only [hpr x]
    ring
  rw [hsplit] at h1
  have e1 : ∫ x in B, G x * (c x * fderiv ℝ ψ x (basisVec k)) =
      ∫ x in B, (c x * fderiv ℝ ψ x (basisVec k)) * G x :=
    integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
  have e2 : ∫ x in B, G x * (fderiv ℝ c x (basisVec k) * ψ x) =
      ∫ x in B, (ψ x * fderiv ℝ c x (basisVec k)) * G x :=
    integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
  rw [e1, e2]
  linarith only [h1]

theorem intC2_dd_weak {B : Set (Vec d)} {G H ψ : Vec d → ℝ} {j k : Fin d}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ B)
    (hweak : HasWeakPartialDerivOn B k G H) :
    ∫ x in B, G x * intW2p_dd ψ k j x = -∫ x in B, H x * fderiv ℝ ψ x (basisVec j) := by
  have h := hweak (fun y ↦ fderiv ℝ ψ y (basisVec j)) (intW2p_d1_smooth hψ j)
    (intW2p_d1_cs hψc j) ((intC2_d1_ts j).trans hψs)
  have e : ∀ x, fderiv ℝ (fun y ↦ fderiv ℝ ψ y (basisVec j)) x (basisVec k) =
      intW2p_dd ψ k j x := fun x ↦ by
    rw [intW2p_dd_symm ψ (hψ.of_le (by simp)) k j x]
    rfl
  simp only [e] at h
  exact h

/-- **The equation for `∂ₖu`.** -/
theorem intC2_diff_eq {B : Set (Vec d)} (hB : IsOpen B) {a : CoeffField d} {nu : ℝ}
    (hsk : ∀ y i j, a y i j + a y j i = if i = j then 2 * nu else 0)
    (ha : ∀ i j, ContDiff ℝ 2 fun y ↦ a y i j) {mu : ℝ} {g : Vec d → ℝ}
    (hg : ContDiff ℝ 1 g) {uB : H1Function B} (hw : intC2_Weak a mu g B uB)
    {G : Fin d → Vec d → ℝ} {Hs : Fin d → Fin d → Vec d → ℝ}
    (hGae : ∀ i, (G i) =ᵐ[volume.restrict B] fun x ↦ uB.grad x i)
    (hGc : ∀ i, ContinuousOn (G i) B)
    (hHs : ∀ i j, HasWeakPartialDerivOn B j (G i) (Hs i j))
    (hHs2 : ∀ i j, MemLp (Hs i j) 2 (volume.restrict B)) (k : Fin d) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ B) :
    nu * ∑ j, ∫ x in B, Hs j k x * fderiv ℝ ψ x (basisVec j) =
      ∫ x in B, (fderiv ℝ g x (basisVec k) - mu * G k x -
        ∑ i, (intW2p_drift a x i * Hs i k x +
          fderiv ℝ (fun y ↦ intW2p_drift a y i) x (basisVec k) * G i x)) * ψ x := by
  have hφ : ContDiff ℝ (⊤ : ℕ∞) fun x ↦ fderiv ℝ ψ x (basisVec k) := intW2p_d1_smooth hψ k
  have hφc : HasCompactSupport fun x ↦ fderiv ℝ ψ x (basisVec k) := intW2p_d1_cs hψc k
  have hφs : tsupport (fun x ↦ fderiv ℝ ψ x (basisVec k)) ⊆ B := (intC2_d1_ts k).trans hψs
  have E := hw _ hφ hφc hφs
  have SC := intW2p_smooth_scalar hB hsk ha uB hφ hφc hφs
  have hψ0 : Continuous ψ := hψ.continuous
  have hcont_c : ∀ i, Continuous fun y ↦ intW2p_drift a y i := fun i ↦
    (intW2p_drift_contDiff ha i).continuous
  -- gradient terms
  have X1 : ∫ x in B, vecDot (uB.grad x) (fun i ↦ fderiv ℝ (fun x ↦ fderiv ℝ ψ x (basisVec k)) x
      (basisVec i)) = ∑ j, ∫ x in B, G j x * intW2p_dd ψ k j x := by
    unfold vecDot
    show ∫ x in B, ∑ j, uB.grad x j * intW2p_dd ψ k j x = _
    have hint : ∀ j ∈ Finset.univ, Integrable (fun x ↦ uB.grad x j * intW2p_dd ψ k j x)
        (volume.restrict B) := fun j _ ↦ intW2p_integrable_mul (uB.grad_memL2 j)
      (intW2p_dd_smooth hψ k j).continuous (intW2p_dd_cs hψc k j)
    rw [integral_finsetSum _ hint]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    refine integral_congr_ae ?_
    filter_upwards [hGae j] with x hx
    rw [hx]
  have X2 : ∫ x in B, vecDot (intW2p_drift a x) (uB.grad x) * fderiv ℝ ψ x (basisVec k) =
      ∑ i, ∫ x in B, G i x * (intW2p_drift a x i * fderiv ℝ ψ x (basisVec k)) := by
    unfold vecDot
    have : ∀ x, (∑ i, intW2p_drift a x i * uB.grad x i) * fderiv ℝ ψ x (basisVec k) =
        ∑ i, uB.grad x i * (intW2p_drift a x i * fderiv ℝ ψ x (basisVec k)) := fun x ↦ by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    simp_rw [this]
    have hint : ∀ i ∈ Finset.univ, Integrable (fun x ↦ uB.grad x i *
        (intW2p_drift a x i * fderiv ℝ ψ x (basisVec k))) (volume.restrict B) := fun i _ ↦
      intW2p_integrable_mul (uB.grad_memL2 i)
        ((hcont_c i).mul (intW2p_d1_smooth hψ k).continuous)
        ((intW2p_d1_cs hψc k).mul_left)
    rw [integral_finsetSum _ hint]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    refine integral_congr_ae ?_
    filter_upwards [hGae i] with x hx
    rw [hx]
  -- the four integrations by parts
  have T1 : ∀ j, ∫ x in B, G j x * intW2p_dd ψ k j x = -∫ x in B, Hs j k x * fderiv ℝ ψ x (basisVec j) :=
    fun j ↦ intC2_dd_weak hψ hψc hψs (hHs j k)
  have T2 : ∀ i, ∫ x in B, G i x * (intW2p_drift a x i * fderiv ℝ ψ x (basisVec k)) =
      -(∫ x in B, Hs i k x * (intW2p_drift a x i * ψ x)) -
        ∫ x in B, G i x * (fderiv ℝ (fun y ↦ intW2p_drift a y i) x (basisVec k) * ψ x) :=
    fun i ↦ intC2_ibp_mul hB (hGc i) (hHs2 i k) (hHs i k) (intW2p_drift_contDiff ha i) hψ hψc hψs
  have T3 : ∫ x in B, uB.toFun x * fderiv ℝ ψ x (basisVec k) = -∫ x in B, G k x * ψ x := by
    have h := uB.hasWeakGradient k ψ hψ hψc hψs
    rw [h]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hGae k] with x hx
    rw [hx]
  have T4 : ∫ x in B, g x * fderiv ℝ ψ x (basisVec k) = -∫ x in B, fderiv ℝ g x (basisVec k) * ψ x :=
    (HasWeakPartialDerivOn.of_contDiff hg) ψ hψ hψc hψs
  -- integrability for the right-hand side
  have J1 : Integrable (fun x ↦ fderiv ℝ g x (basisVec k) * ψ x) (volume.restrict B) :=
    (((hg.continuous_fderiv one_ne_zero).clm_apply continuous_const).mul hψ0
      |>.integrable_of_hasCompactSupport (μ := volume) hψc.mul_left).restrict
  have J2 : Integrable (fun x ↦ ψ x * G k x) (volume.restrict B) :=
    (intC2_integral_eq hB hψ0 hψc hψs (hGc k)).1.restrict
  have J3 : ∀ i, Integrable (fun x ↦ Hs i k x * (intW2p_drift a x i * ψ x)) (volume.restrict B) :=
    fun i ↦ intW2p_integrable_mul (hHs2 i k) ((hcont_c i).mul hψ0) (hψc.mul_left)
  have J4 : ∀ i, Integrable (fun x ↦ G i x * (fderiv ℝ (fun y ↦ intW2p_drift a y i) x
      (basisVec k) * ψ x)) (volume.restrict B) := fun i ↦ by
    have := (intC2_integral_eq hB (θ := fun x ↦ fderiv ℝ (fun y ↦ intW2p_drift a y i) x
      (basisVec k) * ψ x) (f := G i) ((intC2_drift_d1_cont ha i k).mul hψ0) hψc.mul_left
      (tsupport_mul_subset_right.trans hψs) (hGc i)).1.restrict (s := B)
    exact this.congr (Eventually.of_forall fun x ↦ by simp only [mul_comm])
  have R : ∫ x in B, (fderiv ℝ g x (basisVec k) - mu * G k x -
        ∑ i, (intW2p_drift a x i * Hs i k x +
          fderiv ℝ (fun y ↦ intW2p_drift a y i) x (basisVec k) * G i x)) * ψ x =
      (∫ x in B, fderiv ℝ g x (basisVec k) * ψ x) - mu * (∫ x in B, G k x * ψ x) -
        ∑ i, ((∫ x in B, Hs i k x * (intW2p_drift a x i * ψ x)) +
          ∫ x in B, G i x * (fderiv ℝ (fun y ↦ intW2p_drift a y i) x (basisVec k) * ψ x)) := by
    have e : ∀ x, (fderiv ℝ g x (basisVec k) - mu * G k x -
        ∑ i, (intW2p_drift a x i * Hs i k x +
          fderiv ℝ (fun y ↦ intW2p_drift a y i) x (basisVec k) * G i x)) * ψ x =
        (fderiv ℝ g x (basisVec k) * ψ x - mu * (ψ x * G k x)) -
          ∑ i, (Hs i k x * (intW2p_drift a x i * ψ x) +
            G i x * (fderiv ℝ (fun y ↦ intW2p_drift a y i) x (basisVec k) * ψ x)) := fun x ↦ by
      rw [sub_mul, sub_mul, Finset.sum_mul]
      congr 1
      · ring
      · exact Finset.sum_congr rfl fun i _ ↦ by ring
    simp_rw [e]
    have K1 : Integrable (fun x ↦ fderiv ℝ g x (basisVec k) * ψ x - mu * (ψ x * G k x))
        (volume.restrict B) := J1.sub (J2.const_mul mu)
    have K2 : Integrable (fun x ↦ ∑ i, (Hs i k x * (intW2p_drift a x i * ψ x) +
        G i x * (fderiv ℝ (fun y ↦ intW2p_drift a y i) x (basisVec k) * ψ x)))
        (volume.restrict B) := integrable_finsetSum _ fun i _ ↦ (J3 i).add (J4 i)
    have K3 : ∀ i ∈ Finset.univ, Integrable (fun x ↦ Hs i k x * (intW2p_drift a x i * ψ x) +
        G i x * (fderiv ℝ (fun y ↦ intW2p_drift a y i) x (basisVec k) * ψ x))
        (volume.restrict B) := fun i _ ↦ (J3 i).add (J4 i)
    rw [integral_sub K1 K2, integral_sub J1 (J2.const_mul mu), integral_const_mul,
      integral_finsetSum _ K3]
    have e2 : ∫ x in B, ψ x * G k x = ∫ x in B, G k x * ψ x :=
      integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
    rw [e2, Finset.sum_congr rfl fun i _ ↦ integral_add (J3 i) (J4 i)]
  rw [R]
  rw [SC, X1, X2] at E
  simp only [T1, T2] at E
  rw [T3, T4] at E
  simp only [Finset.sum_neg_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.mul_sum, mul_neg] at E ⊢
  linarith only [E]

end SuperdiffusionCLT.Section8
