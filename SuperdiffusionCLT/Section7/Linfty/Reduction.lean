/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Linfty.ReductionB

/-!
# Reduction to the smooth datum

The maximum principle comparison `|u - v| ≤ c` and the `L²` bound of `∇(u - v)`, which is small by
the measure of the boundary layer.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal Pointwise

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- **Reduction to the smooth datum**: the maximum-principle comparison
and the `L²` bound of `∇(u - v)`, which is small by the measure of the boundary layer. -/
theorem linf_reduction [NeZero d] :
    ∃ C : ℝ, 0 < C ∧ ∀ {W : Set (Vec d)}, IsOpen W → IsBoundedDomain W → volume W ≠ 0 →
      ∀ {lam Lam : ℝ} {a : CoeffField d}, 0 < lam → IsEllipticFieldOn lam Lam W a →
      ∀ {f : Vec d → ℝ} (g u v : H1Function W) {gt : Vec d → ℝ}, ContDiff ℝ 1 gt →
      IsDirichletSolution a W f g u →
      IsWeakSolutionOn a W v f (fun _ => 0) → MemH10 W (fun x => v.toFun x - gt x) →
      ∀ {c G r : ℝ}, 0 ≤ c → 0 ≤ G → 0 < r →
        (∀ᵐ x ∂volume.restrict W, |gt x - g.toFun x| ≤ c) →
        (∀ᵐ x ∂volume.restrict W, eucNorm (g.grad x) ≤ G) → (∀ x ∈ W, ‖fderiv ℝ gt x‖ ≤ G) →
        (∀ᵐ x ∂volume.restrict W, |u.toFun x - v.toFun x| ≤ c) ∧
          lpBar W 2 (fun x => eucNorm (u.grad x - v.grad x)) ≤
            ENNReal.ofReal (C * (Lam / lam) * (G + c / r)) *
              (volume (boundaryLayer W (2 * r)) / volume W) ^ (1 / 2 : ℝ) := by
  refine ⟨2 * ((d : ℝ) + 2), by positivity, ?_⟩
  intro W hWo hWb hW0 lam Lam a hlam hEll f g u v gt hgt hu hv hvm c G r hc hG hr hgc hgG hgtG
  have ht := volume_ne_top_of_isBoundedDomain hWb
  obtain ⟨hu1, hu2⟩ := hu
  set gH := li1_h1 hWo hWb hgt with hgH
  have hmemW : ∀ᵐ x ∂volume.restrict W, x ∈ W := ae_restrict_mem hWo.measurableSet
  -- the comparison
  have hsup : ∀ᵐ x ∂volume.restrict W, |u.toFun x - v.toFun x| ≤ c := by
    have hae : (fun x => if |gt x - g.toFun x| ≤ c then g.toFun x else gt x) =ᵐ[volume.restrict W]
        g.toFun := by
      filter_upwards [hgc] with x hx
      simp [hx]
    set gh := linf_h1_ae g _ hae with hgh
    have hgh1 : ∀ x, |gh.toFun x - gH.toFun x| ≤ c := by
      intro x
      by_cases hx : |gt x - g.toFun x| ≤ c
      · have : gh.toFun x = g.toFun x := by simp [hgh, hx]
        rw [this, abs_sub_comm]
        exact hx
      · have : gh.toFun x = gt x := by simp [hgh, hx]
        rw [this]
        show |gt x - gt x| ≤ c
        simpa using hc
    have m1 : MemH10 W (fun x => u.toFun x - gh.toFun x) := by
      obtain ⟨ψ, hψ⟩ := hu2
      have := linf_memH10_ae hWo ψ (u - gh) (by
        rw [hψ, H1Function.sub_toFun]
        filter_upwards [hae] with x hx
        show u.toFun x - gh.toFun x = u.toFun x - g.toFun x
        rw [hgh, linf_h1_ae_toFun, hx])
      simpa using this
    exact li1_linfty_comparison hWo hWb hEll gh gH u v hu1 m1 hv hvm hgh1
  refine ⟨hsup, ?_⟩
  -- the cutoff and the test function
  have hζL := l2a_cutoff_lipschitz W hr
  have hζM : ∀ x, |l2a_cutoff W r x| ≤ 1 := l2a_cutoff_abs_le W r
  obtain ⟨hζc, hζU⟩ := l2a_cutoff_compact (linf_isBounded hWb) hr
  set ζ := l2a_cutoff W r with hζ
  set hh : H1Function W := g - gH with hhh
  set zh := mulLipH10 hWo hh hζL hζM hζc hζU with hzh
  set e : H1Function W := u - v with he
  set w : H1Function W := e - (hh - zh.toH1Function) with hw
  have hwm : MemH10 W w.toFun := by
    obtain ⟨ψu, hψu⟩ := hu2
    have h1 := memH10_add (memH10_sub ⟨ψu, hψu⟩ hvm) (⟨zh, rfl⟩ : MemH10 W zh.toH1Function.toFun)
    convert h1 using 1
    funext x
    simp [hw, he, hhh, hzh, mulLipH10_toH1Function, mulLip_toFun, hgH, li1_h1_toFun]
    ring
  obtain ⟨φ, hφ⟩ := hwm
  have hφg : φ.toH1Function.grad =ᵐ[volume.restrict W] w.grad :=
    w0_grad_ae_of_toFun_eq hWo φ.toH1Function w hφ
  set S : Vec d → Vec d := fun x => (g.grad x - gH.grad x) -
    (ζ x • (g.grad x - gH.grad x) + (g.toFun x - gt x) • lipGradient ζ x) with hS
  have hwgrad : ∀ x, w.grad x = e.grad x - S x := by
    intro x
    simp [hw, hhh, hzh, hS, mulLipH10_toH1Function, mulLip_grad, H1Function.sub_grad, hgH,
      li1_h1_toFun]
  have hφS : ∀ᵐ x ∂volume.restrict W, φ.toH1Function.grad x = e.grad x - S x := by
    filter_upwards [hφg] with x hx
    rw [hx, hwgrad]
  -- the energy identity
  have : IsFiniteMeasure (volume.restrict W) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 ht⟩
  have hξ2 : MemLp e.grad 2 (volume.restrict W) := e.grad_memVectorL2
  have hφ2 : MemLp φ.toH1Function.grad 2 (volume.restrict W) := φ.toH1Function.grad_memVectorL2
  have hS2 : MemLp S 2 (volume.restrict W) := by
    refine (memLp_congr_ae ?_).1 (hξ2.sub hφ2)
    filter_upwards [hφS] with x hx
    simp only [Pi.sub_apply, hx]
    abel
  have hfluxξ : MemVectorL2 W (fun x => matVecMul (a x) (e.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll e.grad_memVectorL2
  have hi1 : Integrable (fun x => vecDot (matVecMul (a x) (e.grad x)) (e.grad x))
      (volume.restrict W) := integrableOn_vecDot_of_memVectorL2 hfluxξ e.grad_memVectorL2
  have hi2 : Integrable (fun x => vecDot (matVecMul (a x) (e.grad x)) (S x))
      (volume.restrict W) := integrableOn_vecDot_of_memVectorL2 hfluxξ hS2
  have hweak : IsWeakSolutionOn a W e 0 0 := li1_isWeakSolutionOn_sub hEll hu1 hv
  have hid : ∫ x in W, vecDot (matVecMul (a x) (e.grad x)) (e.grad x) =
      ∫ x in W, vecDot (matVecMul (a x) (e.grad x)) (S x) := by
    have h0 := hweak φ
    simp only [Pi.zero_apply, zero_mul, vecDot_zero_left, integral_zero, add_zero] at h0
    have h1 : ∫ x in W, vecDot (matVecMul (a x) (e.grad x)) (φ.toH1Function.grad x) =
        (∫ x in W, vecDot (matVecMul (a x) (e.grad x)) (e.grad x)) -
          ∫ x in W, vecDot (matVecMul (a x) (e.grad x)) (S x) := by
      rw [← integral_sub hi1 hi2]
      refine integral_congr_ae ?_
      filter_upwards [hφS] with x hx
      rw [hx, linf_vecDot_sub_right]
    linarith only [h0, h1]
  -- coercivity against the cross term
  have hmemE : ∀ x ∈ W, IsEllipticMatrix lam Lam (a x) := fun x hx => hEll.2 x hx
  have hlamLam : lam ≤ Lam := by
    obtain ⟨x₀, hx₀⟩ : W.Nonempty := nonempty_of_measure_ne_zero hW0
    exact (hmemE x₀ hx₀).2.1
  have hiI := p13_integrable_vecNormSq hξ2
  have hiQ := p13_integrable_vecNormSq hS2
  have hco : lam * (∫ x in W, vecNormSq (e.grad x)) ≤
      ∫ x in W, vecDot (matVecMul (a x) (e.grad x)) (e.grad x) := by
    rw [← integral_const_mul]
    refine integral_mono_ae (hiI.const_mul lam) hi1 ?_
    filter_upwards [hmemW] with x hx
    exact linf_coercive (hmemE x hx) _
  have hcr : ∫ x in W, vecDot (matVecMul (a x) (e.grad x)) (S x) ≤
      lam * (∫ x in W, vecNormSq (e.grad x)) / 4 +
        Lam ^ 2 * (∫ x in W, vecNormSq (S x)) / lam := by
    have h1 : ∫ x in W, vecDot (matVecMul (a x) (e.grad x)) (S x) ≤
        ∫ x in W, (lam * vecNormSq (e.grad x) / 4 + Lam ^ 2 * vecNormSq (S x) / lam) := by
      refine integral_mono_ae hi2 (((hiI.const_mul lam).div_const 4).add
        ((hiQ.const_mul (Lam ^ 2)).div_const lam)) ?_
      filter_upwards [hmemW] with x hx
      exact (le_abs_self _).trans (linf_cross_flux_le (hmemE x hx) _ _)
    rw [integral_add ((hiI.const_mul lam).div_const 4) ((hiQ.const_mul (Lam ^ 2)).div_const lam),
      integral_div, integral_div, integral_const_mul, integral_const_mul] at h1
    exact h1
  set I := ∫ x in W, vecNormSq (e.grad x) with hI
  set Q := ∫ x in W, vecNormSq (S x) with hQ
  have hQ0 : 0 ≤ Q := integral_nonneg fun x => s5_vecNormSq_nonneg _
  have hI0 : 0 ≤ I := integral_nonneg fun x => s5_vecNormSq_nonneg _
  have hIQ : I * lam ^ 2 ≤ 2 * (Lam ^ 2 * Q) := by
    have h1 : lam * I ≤ lam * I / 4 + Lam ^ 2 * Q / lam := by
      linarith only [hco, hid, hcr]
    have h2 : lam * I * (3 / 4) ≤ Lam ^ 2 * Q / lam := by linarith only [h1]
    have h3 : lam * I * (3 / 4) * lam ≤ Lam ^ 2 * Q := by
      have := mul_le_mul_of_nonneg_right h2 hlam.le
      rwa [div_mul_cancel₀ _ hlam.ne'] at this
    have h4 : 0 ≤ Lam ^ 2 * Q := by positivity
    nlinarith only [h3, h4]
  -- the bound on `S` in the layer
  set A : Set (Vec d) := {x | x ∈ W ∧ ζ x ≠ 1} with hA
  have hAm : MeasurableSet A :=
    hWo.measurableSet.inter (isOpen_ne_fun (l2a_cutoff_continuous W hr) continuous_const).measurableSet
  have hAW : A ⊆ W := fun x hx => hx.1
  have hAt : volume A ≠ ⊤ := ne_top_of_le_ne_top ht (measure_mono hAW)
  set B : ℝ := G + ((d : ℝ) + 1) * G + c * (d / r) with hB
  have hB0 : 0 ≤ B := by positivity
  have hSb : ∀ᵐ x ∂volume.restrict W, vecNormSq (S x) ≤ A.indicator (fun _ => B ^ 2) x := by
    filter_upwards [hmemW, hgc, hgG] with x hxW hxc hxG
    by_cases h1 : ζ x = 1
    · have h2 : lipGradient ζ x = 0 := linf_lipGradient_cutoff_of_eq_one W r h1
      have hS0 : S x = 0 := by
        simp [hS, h1, h2]
      rw [hS0]
      have : vecNormSq (0 : Vec d) = 0 := by simp [vecNormSq, vecDot]
      rw [this]
      exact Set.indicator_nonneg (fun _ _ => sq_nonneg B) x
    · have hxA : x ∈ A := ⟨hxW, h1⟩
      rw [Set.indicator_of_mem hxA, ← eucNorm_sq]
      refine pow_le_pow_left₀ (eucNorm_nonneg _) ?_ 2
      have hs0 : 0 ≤ ζ x := l2a_cutoff_nonneg W r x
      have hs1 : ζ x ≤ 1 := l2a_cutoff_le_one W r x
      refine (linf_eucNorm_split_le (t := g.toFun x - gt x) hs0 hs1 _ _).trans ?_
      have h2 : eucNorm (g.grad x - gH.grad x) ≤ G + ((d : ℝ) + 1) * G := by
        have e1 : g.grad x - gH.grad x = g.grad x + -gH.grad x := sub_eq_add_neg _ _
        rw [e1]
        refine (r1_eucNorm_add_le _ _).trans ?_
        rw [r1_eucNorm_neg]
        have h3 : eucNorm (gH.grad x) ≤ ((d : ℝ) + 1) * G := by
          refine (linf_euc_basis_le (fderiv ℝ gt x)).trans ?_
          exact mul_le_mul_of_nonneg_left (hgtG x hxW) (by positivity)
        linarith only [hxG, h3]
      have h4 : |g.toFun x - gt x| ≤ c := by rw [abs_sub_comm]; exact hxc
      have h5 := linf_eucNorm_lipGradient_cutoff_le W hr x
      have h6 : |g.toFun x - gt x| * eucNorm (lipGradient ζ x) ≤ c * (d / r) :=
        mul_le_mul h4 h5 (eucNorm_nonneg _) hc
      linarith only [h2, h6]
  have hQB : Q ≤ B ^ 2 * (volume A).toReal := by
    have h1 : Q ≤ ∫ x in W, A.indicator (fun _ => B ^ 2) x :=
      integral_mono_ae hiQ ((integrable_const (B ^ 2)).indicator hAm) hSb
    rw [integral_indicator_const _ hAm, measureReal_def, Measure.restrict_apply hAm,
      Set.inter_eq_left.2 hAW, smul_eq_mul, mul_comm] at h1
    exact h1
  -- the conclusion
  set ρ : ℝ := Lam / lam with hρ
  have hρ1 : 1 ≤ ρ := by rw [hρ, le_div_iff₀ hlam]; linarith only [hlamLam]
  have hρ0 : 0 ≤ ρ := by linarith only [hρ1]
  set K : ℝ := 2 * ((d : ℝ) + 2) * ρ * (G + c / r) with hK
  have hK0 : 0 ≤ K := by positivity
  have hBle : B ≤ ((d : ℝ) + 2) * (G + c / r) := by
    have h1 : 0 ≤ c / r := by positivity
    have e1 : c * (d / r) = (d : ℝ) * (c / r) := by ring
    have h2 : (d : ℝ) * (c / r) ≤ ((d : ℝ) + 2) * (c / r) :=
      mul_le_mul_of_nonneg_right (by linarith only) h1
    rw [hB, e1]
    nlinarith only [h2, hG, Nat.cast_nonneg (α := ℝ) d]
  have hIK : I ≤ K ^ 2 * (volume A).toReal := by
    have hm0 : 0 ≤ (volume A).toReal := ENNReal.toReal_nonneg
    have h1 : I ≤ 2 * ρ ^ 2 * Q := by
      have hl2 : 0 < lam ^ 2 := by positivity
      have e : 2 * ρ ^ 2 * Q = 2 * (Lam ^ 2 * Q) / lam ^ 2 := by
        rw [hρ]; field_simp
      rw [e, le_div_iff₀ hl2]
      exact hIQ
    have h2 : Q ≤ (((d : ℝ) + 2) * (G + c / r)) ^ 2 * (volume A).toReal :=
      hQB.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hB0 hBle 2) hm0)
    have h3 : 2 * ρ ^ 2 * Q ≤ 2 * ρ ^ 2 * ((((d : ℝ) + 2) * (G + c / r)) ^ 2 * (volume A).toReal) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have h4 : 2 * ρ ^ 2 * ((((d : ℝ) + 2) * (G + c / r)) ^ 2 * (volume A).toReal) ≤
        K ^ 2 * (volume A).toReal := by
      have : 2 * ρ ^ 2 * (((d : ℝ) + 2) * (G + c / r)) ^ 2 ≤ K ^ 2 := by
        rw [hK]
        have h5 : 0 ≤ ρ ^ 2 * (((d : ℝ) + 2) * (G + c / r)) ^ 2 := by positivity
        nlinarith only [h5]
      nlinarith only [this, hm0]
    linarith only [h1, h3, h4]
  have hegrad : (fun x => eucNorm (u.grad x - v.grad x)) = fun x => eucNorm (e.grad x) := by
    funext x
    simp [he]
  rw [hegrad]
  refine (linf_lpBar_euc_le_layer hW0 ht hAt hξ2 hK0 hIK).trans ?_
  obtain ⟨D, hD⟩ := linf_dist_le hWb
  have hsub : A ⊆ boundaryLayer W (2 * r) := l2a_cutoff_layer_subset hD hr
  gcongr

/-- Witness for the reduction: the unit disc, identity field, zero data, zero solutions. -/
example : ∃ C : ℝ, 0 < C ∧
    (∀ᵐ x ∂volume.restrict (Section6.euclidBall (d := 2) 1),
      |(0 : H1Function (Section6.euclidBall (d := 2) 1)).toFun x -
        (0 : H1Function (Section6.euclidBall (d := 2) 1)).toFun x| ≤ 0) := by
  obtain ⟨C, hC, h⟩ := linf_reduction (d := 2)
  exact ⟨C, hC, (h (Section6.isOpen_euclidBall 1) (isBoundedDomain_euclidBall one_pos)
    linf_ball_volume_ne_zero one_pos isEllipticFieldOn_one_euclidBall (f := fun _ => 0) 0 0 0
    (gt := fun _ => 0) contDiff_const ⟨linf_ball_zero_weak, linf_ball_zero_memH10⟩
    linf_ball_zero_weak linf_ball_zero_memH10 (c := 0) (G := 0) (r := 1) le_rfl le_rfl one_pos
    (Filter.Eventually.of_forall fun x => by simp)
    (Filter.Eventually.of_forall fun x => by simp [eucNorm, vecNormSq, vecDot])
    (fun x _ => by simp)).1⟩

end SuperdiffusionCLT.Section7
