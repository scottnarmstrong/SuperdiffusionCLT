/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Linfty.Energy
public import SuperdiffusionCLT.Section7.Prereq.L2AssemblyG
public import SuperdiffusionCLT.Section7.Prereq.LinftyReductionC
public import SuperdiffusionCLT.Section7.Root.FirstRootB
public import SuperdiffusionCLT.Section7.Prereq.RootCarriersApiC

/-!
# The bound of the oscillation quantity `ℋ`

The two `L²` oscillation terms of the local gradient bound are controlled by the sup distance to the
homogenized solution, up to the energy of the homogenized solution.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization MeasureTheory
open scoped ENNReal Pointwise

variable {d : ℕ}

/-- Monotonicity of the normalized norm under an almost everywhere pointwise bound. -/
theorem linf_H_lpBar_mono {W : Set (Vec d)} {F : Vec d → ℝ} {Q : Vec d → ℝ}
    (hF : AEStronglyMeasurable F (volume.restrict W))
    (h : ∀ᵐ x ∂volume.restrict W, ‖F x‖ ≤ Q x) : lpBar W 2 F ≤ lpBar W 2 Q := by
  unfold lpBar
  exact eLpNorm_mono_ae_real (hF.smul_measure _) (Measure.ae_smul_measure h _)

/-- The triangle inequality for the normalized norm. -/
theorem linf_H_lpBar_add {W : Set (Vec d)} {a b : Vec d → ℝ} :
    lpBar W 2 (fun x => a x + b x) ≤ lpBar W 2 a + lpBar W 2 b := by
  unfold lpBar
  exact eLpNorm_add_le (by norm_num)

/-- The Poincaré inequality for the normalized norm. -/
theorem linf_H_poincare_lpBar [NeZero d] :
    ∃ c : ℝ, 0 < c ∧ ∀ {W : Set (Vec d)}, IsOpen W → ∀ (z : Vec d) {L : ℝ}, 0 < L →
      W ⊆ axisCube z L → volume W ≠ 0 → volume W ≠ ⊤ → ∀ ψ : H10Function W,
        lpBar W 2 ψ.toH1Function.toFun ≤
          ENNReal.ofReal (c * L) * lpBar W 2 (fun x => eucNorm (ψ.toH1Function.grad x)) := by
  obtain ⟨c, hc, hP⟩ := p13_poincare (d := d)
  refine ⟨c, hc, ?_⟩
  intro W hWo z L hL hWL h0 ht ψ
  have hv2 : MemLp ψ.toH1Function.toFun 2 (volume.restrict W) := ψ.toH1Function.memL2
  have hgv : MemLp ψ.toH1Function.grad 2 (volume.restrict W) := ψ.toH1Function.grad_memVectorL2
  have hPo := hP hWo z hL hWL (φ := ψ)
  have hGe : eLpNorm ψ.toH1Function.grad 2 (volume.restrict W) ≤
      eLpNorm (fun x => eucNorm (ψ.toH1Function.grad x)) 2 (volume.restrict W) := by
    refine eLpNorm_mono hgv.aestronglyMeasurable fun x => ?_
    have h0 : 0 ≤ eucNorm (ψ.toH1Function.grad x) := Real.sqrt_nonneg _
    rw [Real.norm_of_nonneg h0]
    exact p13_sup_le_euc _
  rw [li1_lpBar_two_eq W _ hv2.aestronglyMeasurable h0 ht,
    li1_lpBar_two_eq W _ (p13_memLp_euc hgv).aestronglyMeasurable h0 ht, mul_left_comm]
  gcongr
  exact hPo.trans (by gcongr)

/-- The two `L²` oscillation terms by the sup distance to the homogenized solution. -/
theorem linf_H_bound [NeZero d] :
    ∃ C : ℝ, 0 < C ∧ ∀ {W : Set (Vec d)}, IsOpen W → ∀ (z : Vec d) {L : ℝ}, 0 < L →
      W ⊆ axisCube z L → (∀ x ∈ W, ‖x‖ ≤ L) → volume W ≠ 0 →
      ∀ {s : ℝ}, 0 < s → ∀ (f : Vec d → ℝ) {F G : ℝ}, 0 ≤ F → 0 ≤ G →
        AEStronglyMeasurable f (volume.restrict W) → (∀ᵐ x ∂volume.restrict W, |f x| ≤ F) →
      ∀ {gt : Vec d → ℝ}, ContDiff ℝ 1 gt → (∀ x, ‖fderiv ℝ gt x‖ ≤ G) →
      ∀ (v vh : H1Function W),
        IsWeakSolutionOn (fun _ => s • (1 : Mat d)) W vh f (fun _ => 0) →
        MemH10 W (fun x => vh.toFun x - gt x) →
        lpBar W 2 (fun x => v.toFun x - gt 0) + lpBar W 2 (fun x => v.toFun x - gt x) ≤
          2 * eLpNorm (fun x => v.toFun x - vh.toFun x) ⊤ (volume.restrict W) +
            ENNReal.ofReal (C * (L * G + L ^ 2 / s * F)) := by
  obtain ⟨c, hc, hP⟩ := linf_H_poincare_lpBar (d := d)
  obtain ⟨Ce, hCe, hE⟩ := linf_energy (d := d)
  refine ⟨2 * c * (Ce + ((d : ℝ) + 1)) + 2 * c * Ce + 1, by positivity, ?_⟩
  intro W hWo z L hL hWL hLx hW0 s hs f F G hF hG hfm hfF gt hgt hGt v vh hvh hmem
  have hb : IsBoundedDomain W := ⟨L, hL, fun x hx i =>
    (Real.norm_eq_abs _ ▸ norm_le_pi_norm x i).trans (hLx x hx)⟩
  have ht := volume_ne_top_of_isBoundedDomain hb
  by_cases hX : eLpNorm (fun x => v.toFun x - vh.toFun x) ⊤ (volume.restrict W) = ⊤
  · rw [hX]; simp
  set X := eLpNorm (fun x => v.toFun x - vh.toFun x) ⊤ (volume.restrict W) with hXdef
  obtain ⟨ψ, hψ⟩ := hmem
  set gH := li1_h1 hWo hb hgt with hgH
  have hmemW : ∀ᵐ x ∂volume.restrict W, x ∈ W := ae_restrict_mem hWo.measurableSet
  have hvm : AEStronglyMeasurable v.toFun (volume.restrict W) := v.memL2.aestronglyMeasurable
  have hvhm : AEStronglyMeasurable vh.toFun (volume.restrict W) := vh.memL2.aestronglyMeasurable
  have hgtm : AEStronglyMeasurable gt (volume.restrict W) := hgt.continuous.aestronglyMeasurable
  have hψm : AEStronglyMeasurable ψ.toH1Function.toFun (volume.restrict W) :=
    ψ.toH1Function.memL2.aestronglyMeasurable
  -- the sup distance
  have hvv : lpBar W 2 (fun x => v.toFun x - vh.toFun x) ≤ X := by
    have hX' : X ≠ ⊤ := hX
    have hae : ∀ᵐ x ∂volume.restrict W, |v.toFun x - vh.toFun x| ≤ X.toReal := by
      filter_upwards [enorm_ae_le_eLpNormEssSup (fun x => v.toFun x - vh.toFun x)
        (volume.restrict W)] with x hx
      have e := eLpNorm_exponent_top (f := fun x => v.toFun x - vh.toFun x)
        (μ := volume.restrict W) (hvm.sub hvhm)
      rw [← e] at hx
      rw [← Real.norm_eq_abs, ← ENNReal.ofReal_le_iff_le_toReal hX', ofReal_norm]
      exact hx
    have := linf_lpBar_le_of_ae_le hW0 ht (hvm.sub hvhm) hae
    rwa [ENNReal.ofReal_toReal hX'] at this
  -- the datum oscillation
  have hD : lpBar W 2 (fun x => gt x - gt 0) ≤ ENNReal.ofReal (L * G) := by
    refine linf_lpBar_le_of_ae_le hW0 ht (hgtm.sub aestronglyMeasurable_const) ?_
    filter_upwards [hmemW] with x hx
    have h1 := Convex.norm_image_sub_le_of_norm_fderiv_le (f := gt) (s := Set.univ)
      (fun y _ => (hgt.differentiable (by simp)).differentiableAt) (fun y _ => hGt y)
      convex_univ (Set.mem_univ (0 : Vec d)) (Set.mem_univ x)
    rw [sub_zero] at h1
    rw [← Real.norm_eq_abs]
    exact h1.trans (by nlinarith only [hLx x hx, hG])
  -- the energy of the homogenized solution
  have hEn := hE hWo hb z hL hWL hW0 hs (rc_isEllipticFieldOn_smul_one hs hWo.measurableSet)
    vh hgt hfm hvh ⟨ψ, hψ⟩ hF hG hfF (fun x _ => hGt x)
  have hgr : ψ.toH1Function.grad =ᵐ[volume.restrict W] fun x => vh.grad x - gH.grad x :=
    w0_h10_grad_ae hWo gH vh ψ (by rw [hψ]; rfl)
  have hgG : lpBar W 2 (fun x => eucNorm (gH.grad x)) ≤ ENNReal.ofReal (((d : ℝ) + 1) * G) := by
    refine linf_lpBar_le_of_ae_le hW0 ht
      (p13_memLp_euc gH.grad_memVectorL2).aestronglyMeasurable ?_
    filter_upwards [hmemW] with x hx
    rw [abs_of_nonneg (eucNorm_nonneg _)]
    refine (linf_euc_basis_le (fderiv ℝ gt x)).trans ?_
    exact mul_le_mul_of_nonneg_left (hGt x) (by positivity)
  have hgrad : lpBar W 2 (fun x => eucNorm (ψ.toH1Function.grad x)) ≤
      lpBar W 2 (fun x => eucNorm (vh.grad x)) + lpBar W 2 (fun x => eucNorm (gH.grad x)) := by
    refine (linf_H_lpBar_mono (Q := fun x => eucNorm (vh.grad x) + eucNorm (gH.grad x))
      (p13_memLp_euc ψ.toH1Function.grad_memVectorL2).aestronglyMeasurable ?_).trans
      linf_H_lpBar_add
    filter_upwards [hgr] with x hx
    rw [Real.norm_of_nonneg (eucNorm_nonneg _), hx, sub_eq_add_neg]
    refine (r1_eucNorm_add_le _ _).trans (le_of_eq ?_)
    rw [r1_eucNorm_neg]
  have hψE : lpBar W 2 (fun x => vh.toFun x - gt x) ≤ ENNReal.ofReal (c * L *
      (Ce * (s / s * G + L / s * F) + ((d : ℝ) + 1) * G)) := by
    have e : (fun x => vh.toFun x - gt x) = ψ.toH1Function.toFun := hψ.symm
    rw [e]
    refine (hP hWo z hL hWL hW0 ht ψ).trans ?_
    rw [ENNReal.ofReal_mul (p := c * L) (by positivity)]
    refine mul_le_mul' le_rfl (hgrad.trans ?_)
    rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    exact add_le_add hEn hgG
  -- the assembly
  have hA : lpBar W 2 (fun x => v.toFun x - gt 0) ≤
      lpBar W 2 (fun x => v.toFun x - vh.toFun x) + lpBar W 2 (fun x => vh.toFun x - gt x) +
        lpBar W 2 (fun x => gt x - gt 0) := by
    have e : (fun x => v.toFun x - gt 0) = (fun x => (v.toFun x - vh.toFun x) +
        (vh.toFun x - gt x)) + fun x => gt x - gt 0 := by
      funext x; simp only [Pi.add_apply]; ring
    rw [e]
    refine (linf_H_lpBar_add (W := W)).trans ?_
    gcongr
    exact linf_H_lpBar_add
  have hB : lpBar W 2 (fun x => v.toFun x - gt x) ≤
      lpBar W 2 (fun x => v.toFun x - vh.toFun x) + lpBar W 2 (fun x => vh.toFun x - gt x) := by
    have e : (fun x => v.toFun x - gt x) = fun x => (v.toFun x - vh.toFun x) +
        (vh.toFun x - gt x) := by
      funext x; ring
    rw [e]
    exact linf_H_lpBar_add
  set P : ℝ := L * G with hPdef
  set Q : ℝ := L ^ 2 / s * F with hQdef
  have hP0 : 0 ≤ P := by positivity
  have hQ0 : 0 ≤ Q := by positivity
  set e : ℝ := c * L * (Ce * (s / s * G + L / s * F) + ((d : ℝ) + 1) * G) with hedef
  have he : e = c * (Ce + ((d : ℝ) + 1)) * P + c * Ce * Q := by
    rw [hedef, hPdef, hQdef, div_self hs.ne']
    field_simp
    ring
  have hfin : 2 * e + P ≤ (2 * c * (Ce + ((d : ℝ) + 1)) + 2 * c * Ce + 1) * (L * G + L ^ 2 / s * F) := by
    have : 0 ≤ 2 * c * Ce * P + (2 * c * (Ce + ((d : ℝ) + 1)) + 1) * Q := by positivity
    rw [he]
    linarith only [this]
  have he0 : 0 ≤ e := by rw [he]; positivity
  calc lpBar W 2 (fun x => v.toFun x - gt 0) + lpBar W 2 (fun x => v.toFun x - gt x)
      ≤ (X + ENNReal.ofReal e + ENNReal.ofReal P) + (X + ENNReal.ofReal e) := by
        gcongr
        · exact hA.trans (by gcongr)
        · exact hB.trans (by gcongr)
    _ = 2 * X + ENNReal.ofReal (2 * e + P) := by
        rw [ENNReal.ofReal_add (by positivity) hP0, ENNReal.ofReal_mul (p := 2) (by norm_num),
          ENNReal.ofReal_ofNat]
        ring
    _ ≤ _ := by gcongr

/-- Witness: the unit disc, identity field, zero data. -/
example : lpBar (Section6.euclidBall (d := 2) 1) 2
      (fun x => (0 : H1Function (Section6.euclidBall (d := 2) 1)).toFun x - (fun _ : Vec 2 => (0 : ℝ)) 0) +
    lpBar (Section6.euclidBall (d := 2) 1) 2
      (fun x => (0 : H1Function (Section6.euclidBall (d := 2) 1)).toFun x - (fun _ : Vec 2 => (0 : ℝ)) x) ≤
      2 * eLpNorm (fun x => (0 : H1Function (Section6.euclidBall (d := 2) 1)).toFun x -
        (0 : H1Function (Section6.euclidBall (d := 2) 1)).toFun x) ⊤
        (volume.restrict (Section6.euclidBall (d := 2) 1)) +
        ENNReal.ofReal (1 * (2 * 0 + 2 ^ 2 / 1 * 0)) := by
  obtain ⟨C, -, H⟩ := linf_H_bound (d := 2)
  refine (H (Section6.isOpen_euclidBall 1) (fun _ => -1) two_pos ia_euclidBall_subset_axisCube
    (fun x hx => ?_) linf_ball_volume_ne_zero one_pos (fun _ => 0) le_rfl le_rfl
    aestronglyMeasurable_const (Filter.Eventually.of_forall fun x => by simp)
    (gt := fun _ => 0) contDiff_const (fun x => by simp) 0 0 (by simpa only [one_smul] using linf_ball_zero_weak)
    linf_ball_zero_memH10).trans ?_
  · have h1 := p13_sup_le_euc x
    have h2 : eucNorm x ≤ 1 := by
      unfold eucNorm
      exact Real.sqrt_le_one.2 (by
        have : vecNormSq x < 1 := by simpa [Section6.euclidBall] using hx
        exact this.le)
    linarith only [h1, h2]
  · simp

end SuperdiffusionCLT.Section7
