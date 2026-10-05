/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.InteriorW2p
public import SuperdiffusionCLT.Section8.Prereq.DomainIdentificationB

/-!
# Weak identities from smooth tests

If a linear identity `∫ W · ∇φ + ∫ s φ = 0` with `L²` data `(W, s)` holds for all smooth compactly
supported tests supported in `U`, it holds for every `H¹₀(U)` test (continuity along the
approximating sequence).
-/

@[expose] public section

open MeasureTheory Filter Topology Homogenization

namespace SuperdiffusionCLT.Section8

variable {d : ℕ}

theorem intW2p_memLp_approx_grad {U : Set (Vec d)} (v : H10Function U) (n : ℕ) (i : Fin d) :
    MemLp (fun x ↦ fderiv ℝ (v.approx n) x (basisVec i)) 2 (volume.restrict U) := by
  have hc : Continuous fun x ↦ fderiv ℝ (v.approx n) x (basisVec i) :=
    ((v.approx_smooth n).continuous_fderiv (by simp)).clm_apply continuous_const
  exact (hc.memLp_of_hasCompactSupport
    ((v.approx_hasCompactSupport n).fderiv_apply (𝕜 := ℝ) (basisVec i))).restrict U

theorem intW2p_memLp_approx {U : Set (Vec d)} (v : H10Function U) (n : ℕ) :
    MemLp (v.approx n) 2 (volume.restrict U) :=
  ((v.approx_smooth n).continuous.memLp_of_hasCompactSupport
    (v.approx_hasCompactSupport n)).restrict U

/-- **Density.** A weak identity with `L²` data valid for smooth compactly supported tests holds
for every `H¹₀(U)` test. -/
theorem intW2p_h10_of_smooth {U : Set (Vec d)} {W : Vec d → Vec d} {s : Vec d → ℝ}
    (hW : ∀ i, MemLp (fun x ↦ W x i) 2 (volume.restrict U)) (hs : MemLp s 2 (volume.restrict U))
    (h : ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ x in U, vecDot (W x) (fun i ↦ fderiv ℝ φ x (basisVec i))) +
        ∫ x in U, s x * φ x = 0)
    (v : H10Function U) :
    (∫ x in U, vecDot (W x) (v.toH1Function.grad x)) +
      ∫ x in U, s x * v.toH1Function.toFun x = 0 := by
  have hgrad : ∀ n i, MemLp (fun x ↦ fderiv ℝ (v.approx n) x (basisVec i)) 2 (volume.restrict U) :=
    fun n i ↦ intW2p_memLp_approx_grad v n i
  have h1 : Tendsto (fun n ↦ ∫ x in U, vecDot (W x)
      (fun i ↦ fderiv ℝ (v.approx n) x (basisVec i))) atTop
      (𝓝 (∫ x in U, vecDot (W x) (v.toH1Function.grad x))) := by
    have hi : ∀ i, Tendsto (fun n ↦ ∫ x in U, W x i * fderiv ℝ (v.approx n) x (basisVec i))
        atTop (𝓝 (∫ x in U, W x i * v.toH1Function.grad x i)) := fun i ↦
      domId_tendsto_integral_mul (hW i) (fun n ↦ hgrad n i) (v.toH1Function.grad_memL2 i)
        (v.tendsto_approx_grad i)
    have hsum := tendsto_finsetSum Finset.univ fun i _ ↦ hi i
    have e1 : ∀ n, ∫ x in U, vecDot (W x) (fun i ↦ fderiv ℝ (v.approx n) x (basisVec i)) =
        ∑ i, ∫ x in U, W x i * fderiv ℝ (v.approx n) x (basisVec i) := fun n ↦ by
      unfold vecDot
      exact integral_finsetSum _ fun i _ ↦ (hW i).integrable_mul (hgrad n i)
    have e2 : ∫ x in U, vecDot (W x) (v.toH1Function.grad x) =
        ∑ i, ∫ x in U, W x i * v.toH1Function.grad x i := by
      unfold vecDot
      exact integral_finsetSum _ fun i _ ↦ (hW i).integrable_mul (v.toH1Function.grad_memL2 i)
    rw [e2]
    exact hsum.congr fun n ↦ (e1 n).symm
  have h2 : Tendsto (fun n ↦ ∫ x in U, s x * v.approx n x) atTop
      (𝓝 (∫ x in U, s x * v.toH1Function.toFun x)) :=
    domId_tendsto_integral_mul hs (fun n ↦ intW2p_memLp_approx v n) v.toH1Function.memL2
      v.tendsto_approx
  have h3 := h1.add h2
  have h4 : ∀ n, (∫ x in U, vecDot (W x) (fun i ↦ fderiv ℝ (v.approx n) x (basisVec i))) +
      ∫ x in U, s x * v.approx n x = 0 := fun n ↦
    h _ (v.approx_smooth n) (v.approx_hasCompactSupport n) (v.approx_support_subset n)
  have h5 : Tendsto (fun n ↦ (∫ x in U, vecDot (W x)
      (fun i ↦ fderiv ℝ (v.approx n) x (basisVec i))) + ∫ x in U, s x * v.approx n x)
      atTop (𝓝 0) := by simp only [h4]; exact tendsto_const_nhds
  exact tendsto_nhds_unique h3 h5



/-- The mixed second derivative `∂_j ∂_i f`. -/
noncomputable def intW2p_dd (f : Vec d → ℝ) (i j : Fin d) (x : Vec d) : ℝ :=
  fderiv ℝ (fun y ↦ fderiv ℝ f y (basisVec i)) x (basisVec j)

theorem intW2p_dd_eq (f : Vec d → ℝ) (hf : ContDiff ℝ 2 f) (i j : Fin d) (x : Vec d) :
    intW2p_dd f i j x = fderiv ℝ (fderiv ℝ f) x (basisVec j) (basisVec i) := by
  unfold intW2p_dd
  have h1 : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x
  have h2 := (h1.hasFDerivAt.clm_apply (hasFDerivAt_const (basisVec i) x))
  rw [h2.fderiv]
  simp

theorem intW2p_dd_symm (f : Vec d → ℝ) (hf : ContDiff ℝ 2 f) (i j : Fin d) (x : Vec d) :
    intW2p_dd f i j x = intW2p_dd f j i x := by
  rw [intW2p_dd_eq f hf, intW2p_dd_eq f hf]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)).eq _ _


theorem intW2p_dd_const_sub (f g : Vec d → ℝ) (c : ℝ) (h : ∀ y, f y = c - g y) (i j : Fin d)
    (x : Vec d) : intW2p_dd f i j x = -intW2p_dd g i j x := by
  have hf : f = fun y ↦ c - g y := funext h
  unfold intW2p_dd
  have h1 : (fun y ↦ fderiv ℝ f y (basisVec i)) = fun y ↦ -(fderiv ℝ g y (basisVec i)) := by
    funext y
    rw [hf, fderiv_const_sub]
    simp
  rw [h1, fderiv_fun_neg]
  simp

/-- The skew-structure sum: `∑ aᵢⱼ ∂ⱼ∂ᵢφ = ν Δφ`. -/
theorem intW2p_sum_a_dd {a : CoeffField d} {nu : ℝ}
    (hsk : ∀ y i j, a y i j + a y j i = if i = j then 2 * nu else 0) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ 2 φ) (x : Vec d) :
    ∑ i, ∑ j, a x i j * intW2p_dd φ i j x = nu * ∑ i, intW2p_dd φ i i x := by
  set S := ∑ i, ∑ j, a x i j * intW2p_dd φ i j x with hS
  have h1 : S = ∑ i, ∑ j, a x j i * intW2p_dd φ i j x := by
    rw [hS, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [intW2p_dd_symm φ hφ j i x]
  have h2 : ∑ i, ∑ j, (a x i j + a x j i) * intW2p_dd φ i j x =
      S + ∑ i, ∑ j, a x j i * intW2p_dd φ i j x := by
    rw [hS, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  have h3 : ∑ i, ∑ j, (a x i j + a x j i) * intW2p_dd φ i j x =
      2 * nu * ∑ i, intW2p_dd φ i i x := by
    simp only [hsk, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
      Finset.mul_sum]
  linarith only [h1, h2, h3]

/-- The drift `cᵢ = ∑ⱼ ∂ⱼ aᵢⱼ`. -/
noncomputable def intW2p_drift (a : CoeffField d) (x : Vec d) : Vec d :=
  fun i ↦ ∑ j, fderiv ℝ (fun y ↦ a y i j) x (basisVec j)

/-- The drift is divergence free for a skew-structured `C²` coefficient. -/
theorem intW2p_drift_div {a : CoeffField d} {nu : ℝ}
    (hsk : ∀ y i j, a y i j + a y j i = if i = j then 2 * nu else 0)
    (ha : ∀ i j, ContDiff ℝ 2 fun y ↦ a y i j) (x : Vec d) :
    ∑ i, fderiv ℝ (fun y ↦ intW2p_drift a y i) x (basisVec i) = 0 := by
  have hT : ∀ i, fderiv ℝ (fun y ↦ intW2p_drift a y i) x (basisVec i) =
      ∑ j, intW2p_dd (fun y ↦ a y i j) j i x := fun i ↦ by
    unfold intW2p_drift
    have hd : ∀ j, DifferentiableAt ℝ (fun y ↦ fderiv ℝ (fun w ↦ a w i j) y (basisVec j)) x :=
      fun j ↦ by
        have h1 : DifferentiableAt ℝ (fderiv ℝ (fun w ↦ a w i j)) x :=
          ((ha i j).fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x
        exact h1.clm_apply (differentiableAt_const _)
    rw [fderiv_fun_sum (fun j _ ↦ hd j)]
    simp [intW2p_dd]
  simp only [hT]
  set T : Fin d → Fin d → ℝ := fun i j ↦ intW2p_dd (fun y ↦ a y i j) j i x with hTdef
  have hanti : ∀ i j, T i j = -T j i := fun i j ↦ by
    simp only [hTdef]
    have e1 := intW2p_dd_const_sub (fun y ↦ a y i j) (fun y ↦ a y j i)
      (if j = i then 2 * nu else 0) (fun y ↦ by linarith only [hsk y j i]) j i x
    rw [e1, intW2p_dd_symm _ (ha j i) j i x]
  have hS : ∑ i, ∑ j, T i j = ∑ i, ∑ j, -T i j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    exact hanti j i
  have : ∑ i, ∑ j, T i j = 0 := by
    have h2 : ∑ i, ∑ j, -T i j = -∑ i, ∑ j, T i j := by simp
    linarith only [hS, h2]
  exact this



theorem intW2p_integrable_mul {U : Set (Vec d)} {w θ : Vec d → ℝ}
    (hw : MemLp w 2 (volume.restrict U)) (hθ : Continuous θ) (hc : HasCompactSupport θ) :
    Integrable (fun x ↦ w x * θ x) (volume.restrict U) :=
  by
  have h2 : MemLp θ 2 (volume.restrict U) := (hθ.memLp_of_hasCompactSupport hc).restrict U
  exact hw.integrable_mul h2

theorem intW2p_d1_smooth {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) fun x ↦ fderiv ℝ φ x (basisVec i) :=
  (hφ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

theorem intW2p_d1_cs {φ : Vec d → ℝ} (hc : HasCompactSupport φ) (i : Fin d) :
    HasCompactSupport fun x ↦ fderiv ℝ φ x (basisVec i) :=
  hc.fderiv_apply (𝕜 := ℝ) (basisVec i)

theorem intW2p_dd_eq_fderiv (φ : Vec d → ℝ) (i j : Fin d) (x : Vec d) :
    intW2p_dd φ i j x = fderiv ℝ (fun y ↦ fderiv ℝ φ y (basisVec i)) x (basisVec j) := rfl

theorem intW2p_dd_smooth {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (i j : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (intW2p_dd φ i j) :=
  ((intW2p_d1_smooth hφ i).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

theorem intW2p_dd_cs {φ : Vec d → ℝ} (hc : HasCompactSupport φ) (i j : Fin d) :
    HasCompactSupport (intW2p_dd φ i j) :=
  (intW2p_d1_cs hc i).fderiv_apply (𝕜 := ℝ) (basisVec j)


theorem intW2p_ibp_h1 {U : Set (Vec d)} (hU : IsOpen U) (z : H1Function U) (j : Fin d)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U) :
    ∫ x in U, z.grad x j * ψ x = -∫ x in U, z.toFun x * fderiv ℝ ψ x (basisVec j) := by
  have h2 := intW2p_ibp_c1 hU (w := z.toFun) (g' := fun x ↦ z.grad x j) (i := j)
    (locallyIntegrableOn_of_locallyIntegrable_restrict (z.memL2.locallyIntegrable (by norm_num)))
    (locallyIntegrableOn_of_locallyIntegrable_restrict
      ((z.grad_memL2 j).locallyIntegrable (by norm_num))) (z.hasWeakGradient j) hψ hc hs
  rw [h2, neg_neg]

theorem intW2p_drift_contDiff {a : CoeffField d} (ha : ∀ i j, ContDiff ℝ 2 fun y ↦ a y i j)
    (i : Fin d) : ContDiff ℝ 1 fun y ↦ intW2p_drift a y i := by
  unfold intW2p_drift
  refine ContDiff.sum fun j _ ↦ ?_
  exact ((ha i j).fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

theorem intW2p_claimB {U : Set (Vec d)} (hU : IsOpen U) (z : H1Function U) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U) :
    ∫ x in U, vecDot (z.grad x) (fun i ↦ fderiv ℝ φ x (basisVec i)) =
      -∫ x in U, z.toFun x * ∑ i, intW2p_dd φ i i x := by
  have hd1s : ∀ i, tsupport (fun x ↦ fderiv ℝ φ x (basisVec i)) ⊆ U := fun i ↦
    (tsupport_fderiv_apply_subset ℝ (basisVec i)).trans hs
  have h1 : ∀ i, ∫ x in U, z.grad x i * fderiv ℝ φ x (basisVec i) =
      -∫ x in U, z.toFun x * intW2p_dd φ i i x := fun i ↦
    intW2p_ibp_h1 hU z i ((intW2p_d1_smooth hφ i).of_le (by simp)) (intW2p_d1_cs hc i) (hd1s i)
  calc ∫ x in U, vecDot (z.grad x) (fun i ↦ fderiv ℝ φ x (basisVec i))
      = ∑ i, ∫ x in U, z.grad x i * fderiv ℝ φ x (basisVec i) := by
        unfold vecDot
        exact integral_finsetSum _ fun i _ ↦ intW2p_integrable_mul (z.grad_memL2 i)
          (intW2p_d1_smooth hφ i).continuous (intW2p_d1_cs hc i)
    _ = ∑ i, -∫ x in U, z.toFun x * intW2p_dd φ i i x := Finset.sum_congr rfl fun i _ ↦ h1 i
    _ = -∫ x in U, z.toFun x * ∑ i, intW2p_dd φ i i x := by
        rw [Finset.sum_neg_distrib]
        congr 1
        rw [← integral_finsetSum _ fun i _ ↦ intW2p_integrable_mul z.memL2
          (intW2p_dd_smooth hφ i i).continuous (intW2p_dd_cs hc i i)]
        refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
        simp only [Finset.mul_sum]

theorem intW2p_claimC {U : Set (Vec d)} (hU : IsOpen U) {a : CoeffField d} {nu : ℝ}
    (hsk : ∀ y i j, a y i j + a y j i = if i = j then 2 * nu else 0)
    (ha : ∀ i j, ContDiff ℝ 2 fun y ↦ a y i j) (z : H1Function U) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U) :
    ∫ x in U, vecDot (intW2p_drift a x) (z.grad x) * φ x =
      -∫ x in U, z.toFun x * vecDot (intW2p_drift a x) (fun i ↦ fderiv ℝ φ x (basisVec i)) := by
  have hdr := intW2p_drift_contDiff ha
  have hψ1 : ∀ i, ContDiff ℝ 1 fun x ↦ intW2p_drift a x i * φ x := fun i ↦
    (hdr i).mul (hφ.of_le (by simp))
  have hψc : ∀ i, HasCompactSupport fun x ↦ intW2p_drift a x i * φ x := fun i ↦ hc.mul_left
  have hψs : ∀ i, tsupport (fun x ↦ intW2p_drift a x i * φ x) ⊆ U := fun i ↦
    tsupport_mul_subset_right.trans hs
  have h1 : ∀ i, ∫ x in U, z.grad x i * (intW2p_drift a x i * φ x) =
      -∫ x in U, z.toFun x * (fderiv ℝ (fun y ↦ intW2p_drift a y i) x (basisVec i) * φ x +
        intW2p_drift a x i * fderiv ℝ φ x (basisVec i)) := fun i ↦ by
    rw [intW2p_ibp_h1 hU z i (hψ1 i) (hψc i) (hψs i)]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    have hd := ((hdr i).differentiable one_ne_zero) x
    have hd' := ((hφ.of_le (by simp : (1 : WithTop ℕ∞) ≤ (⊤ : ℕ∞))).differentiable one_ne_zero) x
    simp only [fderiv_fun_mul hd hd', add_apply, smul_apply, smul_eq_mul]
    ring_nf
  have hcs1 : ∀ i, HasCompactSupport fun x ↦ fderiv ℝ (fun y ↦ intW2p_drift a y i) x
      (basisVec i) * φ x := fun i ↦ hc.mul_left
  have hcont1 : ∀ i, Continuous fun x ↦ fderiv ℝ (fun y ↦ intW2p_drift a y i) x (basisVec i) :=
    fun i ↦ ((hdr i).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hcs2 : ∀ i, HasCompactSupport fun x ↦ intW2p_drift a x i *
      fderiv ℝ φ x (basisVec i) := fun i ↦ (intW2p_d1_cs hc i).mul_left
  have hcont2 : ∀ i, Continuous fun x ↦ intW2p_drift a x i := fun i ↦ (hdr i).continuous
  calc ∫ x in U, vecDot (intW2p_drift a x) (z.grad x) * φ x
      = ∑ i, ∫ x in U, z.grad x i * (intW2p_drift a x i * φ x) := by
        have hI : ∀ i ∈ Finset.univ, Integrable (fun x ↦ z.grad x i *
            (intW2p_drift a x i * φ x)) (volume.restrict U) := fun i _ ↦ by
          have := intW2p_integrable_mul (z.grad_memL2 i) ((hcont2 i).mul hφ.continuous) (hψc i)
          exact this
        rw [← integral_finsetSum _ hI]
        refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
        beta_reduce
        unfold vecDot
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ ↦ by ring
    _ = ∑ i, -∫ x in U, z.toFun x * (fderiv ℝ (fun y ↦ intW2p_drift a y i) x (basisVec i) *
        φ x + intW2p_drift a x i * fderiv ℝ φ x (basisVec i)) :=
        Finset.sum_congr rfl fun i _ ↦ h1 i
    _ = -∫ x in U, z.toFun x * ∑ i, (fderiv ℝ (fun y ↦ intW2p_drift a y i) x (basisVec i) *
        φ x + intW2p_drift a x i * fderiv ℝ φ x (basisVec i)) := by
        rw [Finset.sum_neg_distrib]
        congr 1
        have hI : ∀ i ∈ Finset.univ, Integrable (fun x ↦ z.toFun x *
            (fderiv ℝ (fun y ↦ intW2p_drift a y i) x (basisVec i) * φ x +
              intW2p_drift a x i * fderiv ℝ φ x (basisVec i))) (volume.restrict U) := fun i _ ↦ by
          have := intW2p_integrable_mul z.memL2
            (((hcont1 i).mul hφ.continuous).add ((hcont2 i).mul (intW2p_d1_smooth hφ i).continuous))
            ((hcs1 i).add (hcs2 i))
          exact this
        rw [← integral_finsetSum _ hI]
        refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
        simp only [Finset.mul_sum]
    _ = -∫ x in U, z.toFun x * vecDot (intW2p_drift a x)
        (fun i ↦ fderiv ℝ φ x (basisVec i)) := by
        congr 1
        refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
        simp only [Finset.sum_add_distrib, ← Finset.sum_mul, intW2p_drift_div hsk ha x, zero_mul,
          zero_add]
        rfl

theorem intW2p_cs_sum (s : Finset (Fin d)) {f : Fin d → Vec d → ℝ}
    (h : ∀ i ∈ s, HasCompactSupport (f i)) : HasCompactSupport fun x ↦ ∑ i ∈ s, f i x := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact HasCompactSupport.zero
  | insert j s hj ih =>
    have h1 := h j (Finset.mem_insert_self j s)
    have h2 := ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi)
    simp only [Finset.sum_insert hj]
    exact h1.add h2

theorem intW2p_claimA {U : Set (Vec d)} (hU : IsOpen U) {a : CoeffField d} {nu : ℝ}
    (hsk : ∀ y i j, a y i j + a y j i = if i = j then 2 * nu else 0)
    (ha : ∀ i j, ContDiff ℝ 2 fun y ↦ a y i j) (z : H1Function U) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U) :
    ∫ x in U, vecDot (matVecMul (a x) (z.grad x)) (fun i ↦ fderiv ℝ φ x (basisVec i)) =
      -(∫ x in U, z.toFun x * vecDot (intW2p_drift a x) (fun i ↦ fderiv ℝ φ x (basisVec i))) -
        nu * ∫ x in U, z.toFun x * ∑ i, intW2p_dd φ i i x := by
  have ha1 : ∀ i j, ContDiff ℝ 1 fun y ↦ a y i j := fun i j ↦ (ha i j).of_le (by norm_num)
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by simp)
  have hd1s : ∀ i, tsupport (fun x ↦ fderiv ℝ φ x (basisVec i)) ⊆ U := fun i ↦
    (tsupport_fderiv_apply_subset ℝ (basisVec i)).trans hs
  have hψ1 : ∀ i j, ContDiff ℝ 1 fun x ↦ a x i j * fderiv ℝ φ x (basisVec i) := fun i j ↦
    (ha1 i j).mul ((intW2p_d1_smooth hφ i).of_le (by simp))
  have hψc : ∀ i j, HasCompactSupport fun x ↦ a x i j * fderiv ℝ φ x (basisVec i) := fun i j ↦
    (intW2p_d1_cs hc i).mul_left
  have hψs : ∀ i j, tsupport (fun x ↦ a x i j * fderiv ℝ φ x (basisVec i)) ⊆ U := fun i j ↦
    tsupport_mul_subset_right.trans (hd1s i)
  have hcontc : ∀ i j, Continuous fun x ↦ fderiv ℝ (fun y ↦ a y i j) x (basisVec j) :=
    fun i j ↦ ((ha1 i j).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hcontd : ∀ i j, Continuous fun x ↦ a x i j := fun i j ↦ (ha1 i j).continuous
  have hF : ∀ i j, ∫ x in U, z.grad x j * (a x i j * fderiv ℝ φ x (basisVec i)) =
      -∫ x in U, z.toFun x * (fderiv ℝ (fun y ↦ a y i j) x (basisVec j) *
        fderiv ℝ φ x (basisVec i) + a x i j * intW2p_dd φ i j x) := fun i j ↦ by
    rw [intW2p_ibp_h1 hU z j (hψ1 i j) (hψc i j) (hψs i j)]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    have hd := ((ha1 i j).differentiable one_ne_zero) x
    have hd' := (((intW2p_d1_smooth hφ i).of_le (by simp : (1 : WithTop ℕ∞) ≤ (⊤ : ℕ∞))).differentiable
      one_ne_zero) x
    simp only [fderiv_fun_mul hd hd', add_apply, smul_apply, smul_eq_mul]
    rw [intW2p_dd_eq_fderiv]
    ring_nf
  have hcs : ∀ i j, HasCompactSupport fun x ↦ fderiv ℝ (fun y ↦ a y i j) x (basisVec j) *
      fderiv ℝ φ x (basisVec i) + a x i j * intW2p_dd φ i j x := fun i j ↦
    ((intW2p_d1_cs hc i).mul_left).add (intW2p_dd_cs hc i j).mul_left
  have hcn : ∀ i j, Continuous fun x ↦ fderiv ℝ (fun y ↦ a y i j) x (basisVec j) *
      fderiv ℝ φ x (basisVec i) + a x i j * intW2p_dd φ i j x := fun i j ↦
    ((hcontc i j).mul (intW2p_d1_smooth hφ i).continuous).add
      ((hcontd i j).mul (intW2p_dd_smooth hφ i j).continuous)
  have hIz : ∀ i j, Integrable (fun x ↦ z.toFun x * (fderiv ℝ (fun y ↦ a y i j) x (basisVec j) *
      fderiv ℝ φ x (basisVec i) + a x i j * intW2p_dd φ i j x)) (volume.restrict U) := fun i j ↦
    intW2p_integrable_mul z.memL2 (hcn i j) (hcs i j)
  have hIg : ∀ i j, Integrable (fun x ↦ z.grad x j * (a x i j * fderiv ℝ φ x (basisVec i)))
      (volume.restrict U) := fun i j ↦ by
    have := intW2p_integrable_mul (z.grad_memL2 j) ((hcontd i j).mul (intW2p_d1_smooth hφ i).continuous)
      (hψc i j)
    exact this
  have hDc : Continuous fun x ↦ vecDot (intW2p_drift a x) (fun i ↦ fderiv ℝ φ x (basisVec i)) := by
    unfold vecDot
    exact continuous_finsetSum _ fun i _ ↦ ((intW2p_drift_contDiff ha i).continuous).mul
      (intW2p_d1_smooth hφ i).continuous
  have hDcs : HasCompactSupport fun x ↦ vecDot (intW2p_drift a x)
      (fun i ↦ fderiv ℝ φ x (basisVec i)) := by
    unfold vecDot
    exact intW2p_cs_sum Finset.univ fun i _ ↦ (intW2p_d1_cs hc i).mul_left
  have hLc : Continuous fun x ↦ ∑ i, intW2p_dd φ i i x :=
    continuous_finsetSum _ fun i _ ↦ (intW2p_dd_smooth hφ i i).continuous
  have hLcs : HasCompactSupport fun x ↦ ∑ i, intW2p_dd φ i i x :=
    intW2p_cs_sum Finset.univ fun i _ ↦ intW2p_dd_cs hc i i
  calc ∫ x in U, vecDot (matVecMul (a x) (z.grad x)) (fun i ↦ fderiv ℝ φ x (basisVec i))
      = ∑ i, ∑ j, ∫ x in U, z.grad x j * (a x i j * fderiv ℝ φ x (basisVec i)) := by
        have h1 : ∀ i ∈ Finset.univ, Integrable (fun x ↦ ∑ j, z.grad x j *
            (a x i j * fderiv ℝ φ x (basisVec i))) (volume.restrict U) := fun i _ ↦
          integrable_finsetSum _ fun j _ ↦ hIg i j
        have h2 : ∀ x, vecDot (matVecMul (a x) (z.grad x)) (fun i ↦ fderiv ℝ φ x (basisVec i)) =
            ∑ i, ∑ j, z.grad x j * (a x i j * fderiv ℝ φ x (basisVec i)) := fun x ↦ by
          unfold vecDot matVecMul
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun j _ ↦ by ring
        simp_rw [h2]
        rw [integral_finsetSum _ h1]
        exact Finset.sum_congr rfl fun i _ ↦ integral_finsetSum _ fun j _ ↦ hIg i j
    _ = ∑ i, ∑ j, -∫ x in U, z.toFun x * (fderiv ℝ (fun y ↦ a y i j) x (basisVec j) *
        fderiv ℝ φ x (basisVec i) + a x i j * intW2p_dd φ i j x) :=
        Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ hF i j
    _ = -∫ x in U, z.toFun x * ∑ i, ∑ j, (fderiv ℝ (fun y ↦ a y i j) x (basisVec j) *
        fderiv ℝ φ x (basisVec i) + a x i j * intW2p_dd φ i j x) := by
        simp only [Finset.sum_neg_distrib]
        congr 1
        have h1 : ∀ i ∈ Finset.univ, Integrable (fun x ↦ ∑ j, z.toFun x *
            (fderiv ℝ (fun y ↦ a y i j) x (basisVec j) *
            fderiv ℝ φ x (basisVec i) + a x i j * intW2p_dd φ i j x)) (volume.restrict U) :=
          fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hIz i j
        have h2 : ∀ x, z.toFun x * ∑ i, ∑ j, (fderiv ℝ (fun y ↦ a y i j) x (basisVec j) *
            fderiv ℝ φ x (basisVec i) + a x i j * intW2p_dd φ i j x) =
            ∑ i, ∑ j, z.toFun x * (fderiv ℝ (fun y ↦ a y i j) x (basisVec j) *
            fderiv ℝ φ x (basisVec i) + a x i j * intW2p_dd φ i j x) := fun x ↦ by
          simp only [Finset.mul_sum]
        simp_rw [h2]
        rw [integral_finsetSum _ h1]
        exact Finset.sum_congr rfl fun i _ ↦ (integral_finsetSum _ fun j _ ↦ hIz i j).symm
    _ = -∫ x in U, z.toFun x * (vecDot (intW2p_drift a x)
          (fun i ↦ fderiv ℝ φ x (basisVec i)) + nu * ∑ i, intW2p_dd φ i i x) := by
        congr 1
        refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
        simp only [Finset.sum_add_distrib]
        rw [intW2p_sum_a_dd hsk hφ2 x]
        congr 1
        simp only [vecDot, intW2p_drift, Finset.sum_mul]
    _ = _ := by
        have hi1 := intW2p_integrable_mul z.memL2 hDc hDcs
        have hi2 : Integrable (fun x ↦ z.toFun x * ∑ i, intW2p_dd φ i i x) (volume.restrict U) :=
          intW2p_integrable_mul z.memL2 hLc hLcs
        have : ∀ x, z.toFun x * (vecDot (intW2p_drift a x) (fun i ↦ fderiv ℝ φ x (basisVec i)) +
            nu * ∑ i, intW2p_dd φ i i x) =
            z.toFun x * vecDot (intW2p_drift a x) (fun i ↦ fderiv ℝ φ x (basisVec i)) +
            nu * (z.toFun x * ∑ i, intW2p_dd φ i i x) := fun x ↦ by ring
        simp_rw [this]
        rw [integral_add hi1 (hi2.const_mul nu), integral_const_mul]
        ring

/-- **Flux form against smooth tests**: `∫ a∇z·∇φ = ν ∫ ∇z·∇φ - ∫ z (c·∇φ)`. -/
theorem intW2p_smooth_flux {U : Set (Vec d)} (hU : IsOpen U) {a : CoeffField d} {nu : ℝ}
    (hsk : ∀ y i j, a y i j + a y j i = if i = j then 2 * nu else 0)
    (ha : ∀ i j, ContDiff ℝ 2 fun y ↦ a y i j) (z : H1Function U) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U) :
    ∫ x in U, vecDot (matVecMul (a x) (z.grad x)) (fun i ↦ fderiv ℝ φ x (basisVec i)) =
      nu * (∫ x in U, vecDot (z.grad x) (fun i ↦ fderiv ℝ φ x (basisVec i))) -
        ∫ x in U, z.toFun x * vecDot (intW2p_drift a x) (fun i ↦ fderiv ℝ φ x (basisVec i)) := by
  rw [intW2p_claimA hU hsk ha z hφ hc hs, intW2p_claimB hU z hφ hc hs]
  ring

/-- **Scalar form against smooth tests**: `∫ a∇z·∇φ = ν ∫ ∇z·∇φ + ∫ (c·∇z) φ`. -/
theorem intW2p_smooth_scalar {U : Set (Vec d)} (hU : IsOpen U) {a : CoeffField d} {nu : ℝ}
    (hsk : ∀ y i j, a y i j + a y j i = if i = j then 2 * nu else 0)
    (ha : ∀ i j, ContDiff ℝ 2 fun y ↦ a y i j) (z : H1Function U) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U) :
    ∫ x in U, vecDot (matVecMul (a x) (z.grad x)) (fun i ↦ fderiv ℝ φ x (basisVec i)) =
      nu * (∫ x in U, vecDot (z.grad x) (fun i ↦ fderiv ℝ φ x (basisVec i))) +
        ∫ x in U, vecDot (intW2p_drift a x) (z.grad x) * φ x := by
  rw [intW2p_smooth_flux hU hsk ha z hφ hc hs, intW2p_claimC hU hsk ha z hφ hc hs]
  ring

end SuperdiffusionCLT.Section8
