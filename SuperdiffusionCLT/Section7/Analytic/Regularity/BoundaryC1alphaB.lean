/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.BoundaryC1alpha
public import SuperdiffusionCLT.Section7.Analytic.Morrey.ZeroTrace

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal

/-!
# Affine Taylor remainder on an axis cube from an `L^p` weak Hessian

If `w ∈ H¹(U)` has a weak Hessian whose `L^p` norm on an axis cube `Q ⊆ U` is finite (`p > d`),
then `w` has a continuous representative `ŵ` on `Q` and a vector `c` such that
`|ŵ x - ŵ y - c · (x - y)| ≤ C L^{1+α} ‖D²w‖_{L^p(Q)}`, with `α = 1 - d/p` and `L` the side of `Q`.
This is the first order Taylor remainder bound used for the flat boundary decay.
-/

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The linear function `x ↦ c · x` is smooth. -/
theorem r3c_contDiff_vecDot (c : Vec d) : ContDiff ℝ 1 (fun x : Vec d => vecDot c x) := by
  unfold vecDot
  exact ContDiff.sum fun i _ =>
    contDiff_const.mul ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).contDiff)

theorem r3c_fderiv_vecDot (c : Vec d) (x : Vec d) (i : Fin d) :
    fderiv ℝ (fun x : Vec d => vecDot c x) x (basisVec i) = c i := by
  have h : HasFDerivAt (fun x : Vec d => vecDot c x)
      (∑ j : Fin d, c j • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j)) x := by
    unfold vecDot
    have := HasFDerivAt.sum (u := Finset.univ) (A := fun (j : Fin d) =>
      c j • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j)) (x := x)
      (fun j _ => ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j).hasFDerivAt.const_mul
        (c j)))
    convert this using 1
    funext y; simp
  rw [h.fderiv]
  simp [basisVec, Pi.single_apply]

theorem r3c_vecDot_sub (c x y : Vec d) : vecDot c (x - y) = vecDot c x - vecDot c y := by
  unfold vecDot
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by simp [mul_sub]

/-- The coordinates of a vector are bounded by its (sup) norm. -/
theorem r3c_abs_apply_le (v : Vec d) (i : Fin d) : |v i| ≤ ‖v‖ := by
  have := norm_le_pi_norm v i
  rwa [Real.norm_eq_abs] at this

/-- **Affine Taylor remainder on an axis cube.** -/
theorem r3c_taylor_axisCube [NeZero d] {U : Set (Vec d)} {z : Vec d} {L : ℝ} (hL : 0 < L)
    (hsub : axisCube z L ⊆ U) {p : ℝ} (hp : (d : ℝ) < p) {w : H1Function U}
    (H : HasWeakHessianOn U w)
    (hH : MemLp (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) (ENNReal.ofReal p)
      (volume.restrict (axisCube z L))) :
    ∃ (ŵ : Vec d → ℝ) (c : Vec d), ContinuousOn ŵ (axisCube z L) ∧
      ŵ =ᵐ[volume.restrict (axisCube z L)] w.toFun ∧
      ∀ x ∈ axisCube z L, ∀ y ∈ axisCube z L,
        |ŵ x - ŵ y - vecDot c (x - y)| ≤
          (4 * (d : ℝ) * (1 / (1 - (d : ℝ) / p))) * (4 * (d : ℝ) * (1 / (1 - (d : ℝ) / p))) *
            L ^ (1 + (1 - (d : ℝ) / p)) *
            (eLpNorm (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) (ENNReal.ofReal p)
              (volume.restrict (axisCube z L))).toReal := by
  have hd0 : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd0
  have hp0 : 0 < p := by linarith only [hd1, hp]
  have hp1 : (1 : ℝ≥0∞) < ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff hp0).2 (by linarith only [hd1, hp])
  have hα : 0 < 1 - (d : ℝ) / p := by
    have : (d : ℝ) / p < 1 := (div_lt_one hp0).2 hp
    linarith only [this]
  obtain ⟨g, hgc, hgae, hgH⟩ := r3b_holderGradient_axisCube hL hsub hp H hH
  set N := (eLpNorm (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) (ENNReal.ofReal p)
    (volume.restrict (axisCube z L))).toReal with hN
  have hN0 : 0 ≤ N := ENNReal.toReal_nonneg
  set C₀ : ℝ := 4 * (d : ℝ) * (1 / (1 - (d : ℝ) / p)) with hC₀
  have hC₀0 : 0 ≤ C₀ := by
    have : 0 < 1 / (1 - (d : ℝ) / p) := one_div_pos.2 hα
    rw [hC₀]; positivity
  have hU := isOpenBoundedConvexDomain_axisCube z L
  have hy₀ : (fun i => z i + L / 2 : Vec d) ∈ axisCube z L := by
    intro i _
    simp only [Set.mem_Ioo]
    constructor <;> linarith only [hL]
  set c : Vec d := g (fun i => z i + L / 2) with hc
  set δ : ℝ := C₀ * L ^ (1 - (d : ℝ) / p) * N with hδ
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have hgc_bd : ∀ x ∈ axisCube z L, ‖g x - c‖ ≤ δ := by
    intro x hx
    refine (hgH x hx _ hy₀).trans ?_
    rw [hδ]
    gcongr
    exact (norm_sub_lt_of_mem_axisCube hL hx hy₀).le
  -- the remainder as an `H¹` function on the cube
  set aff : H1Function (axisCube z L) :=
    H1Function.ofContDiffOnIsOpenBoundedConvexDomain hU (r3c_contDiff_vecDot c) with haff
  set v : H1Function (axisCube z L) := (w.restrict hU.isOpen hsub) - aff with hv
  have hvf : ∀ x, v.toFun x = w.toFun x - vecDot c x := by
    intro x
    rw [hv, H1Function.sub_toFun]
    rfl
  have hvg : ∀ x, v.grad x = w.grad x - fun i => c i := by
    intro x
    rw [hv, H1Function.sub_grad]
    funext i
    simp only [Pi.sub_apply]
    congr 1
    exact r3c_fderiv_vecDot c x i
  have hvg_ae : ∀ᵐ x ∂(volume.restrict (axisCube z L)), ‖v.grad x‖ ≤ δ := by
    have hall : ∀ᵐ x ∂(volume.restrict (axisCube z L)), ∀ i, g x i = w.grad x i :=
      ae_all_iff.2 hgae
    filter_upwards [hall, ae_restrict_mem hU.isOpen.measurableSet] with x hx hxc
    rw [hvg x]
    have : (w.grad x - fun i => c i) = g x - c := by
      funext i; simp [Pi.sub_apply, hx i]
    rw [this]
    exact hgc_bd x hxc
  have hfin : volume (axisCube z L) < ⊤ := (isBoundedDomain_axisCube z L).isBounded.measure_lt_top
  have hgrad : GradMemLpOn (axisCube z L) (ENNReal.ofReal p) v.grad := by
    intro i
    refine MemLp.of_bound (C := δ) ?_ ?_
    · exact (v.grad_memL2 i).aestronglyMeasurable
    · filter_upwards [hvg_ae] with x hx
      rw [Real.norm_eq_abs]
      exact (r3c_abs_apply_le (v.grad x) i).trans hx
  let pe : FiniteLpExponent := ⟨ENNReal.ofReal p, hp1, ENNReal.ofReal_lt_top⟩
  let uW : W1pFunction (axisCube z L) (ENNReal.ofReal p) := v.toW1pOfGradMemLp hU pe hgrad
  obtain ⟨ū, hūc, hūae, hūb⟩ := w1p_exists_continuous_representative hd0 hL hp uW
  have hnorm : (eLpNorm (fun x => ‖uW.grad x‖) (ENNReal.ofReal p)
      (volume.restrict (axisCube z L))).toReal ≤ δ * L ^ (d / p : ℝ) := by
    have h1 : eLpNorm (fun x => ‖uW.grad x‖) (ENNReal.ofReal p) (volume.restrict (axisCube z L)) ≤
        (volume.restrict (axisCube z L)) Set.univ ^ (ENNReal.ofReal p).toReal⁻¹ *
          ENNReal.ofReal δ := by
      have hmeas : AEStronglyMeasurable (fun x => ‖uW.grad x‖) (volume.restrict (axisCube z L)) :=
        (aemeasurable_pi_iff.2 fun j => (hgrad j).aestronglyMeasurable.aemeasurable).aestronglyMeasurable.norm
      refine eLpNorm_le_of_ae_bound hmeas ?_
      filter_upwards [hvg_ae] with x hx
      rw [norm_norm]
      exact hx
    have h2 : ((volume.restrict (axisCube z L)) Set.univ ^ (ENNReal.ofReal p).toReal⁻¹ *
        ENNReal.ofReal δ).toReal = δ * L ^ (d / p : ℝ) := by
      rw [Measure.restrict_apply_univ, ENNReal.toReal_mul, ENNReal.toReal_ofReal hδ0,
        ← ENNReal.toReal_rpow, toReal_volume_axisCube z hL, ENNReal.toReal_ofReal hp0.le]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
      rw [mul_comm]
      congr 2
    have hne : (volume.restrict (axisCube z L)) Set.univ ^ (ENNReal.ofReal p).toReal⁻¹ *
        ENNReal.ofReal δ ≠ ⊤ := by
      refine ENNReal.mul_ne_top ?_ ENNReal.ofReal_ne_top
      refine ENNReal.rpow_ne_top_of_nonneg ?_ ?_
      · rw [ENNReal.toReal_ofReal hp0.le]; positivity
      · rw [Measure.restrict_apply_univ]; exact hfin.ne
    rw [← h2]
    exact ENNReal.toReal_mono hne h1
  refine ⟨fun x => ū x + vecDot c x, c, ?_, ?_, ?_⟩
  · exact hūc.add (r3c_contDiff_vecDot c).continuous.continuousOn
  · filter_upwards [hūae] with x hx
    rw [hx]
    show v.toFun x + vecDot c x = w.toFun x
    rw [hvf]; ring
  · intro x hx y hy
    have h1 := hūb x hx y hy
    have h2 : ‖x - y‖ ^ (1 - (d : ℝ) / p) ≤ L ^ (1 - (d : ℝ) / p) :=
      Real.rpow_le_rpow (norm_nonneg _) (norm_sub_lt_of_mem_axisCube hL hx hy).le hα.le
    have h3 : |ū x + vecDot c x - (ū y + vecDot c y) - vecDot c (x - y)| = |ū x - ū y| := by
      rw [r3c_vecDot_sub]; congr 1; ring
    rw [h3]
    refine h1.trans ?_
    have hLL : L ^ (1 - (d : ℝ) / p) * L ^ ((d : ℝ) / p) = L := by
      rw [← Real.rpow_add hL]; simp
    have hL2 : L ^ (1 + (1 - (d : ℝ) / p)) = L * L ^ (1 - (d : ℝ) / p) := by
      rw [Real.rpow_add hL, Real.rpow_one]
    have hGr : (eLpNorm (fun x => ‖uW.grad x‖) (ENNReal.ofReal p)
        (volume.restrict (axisCube z L))).toReal ≤ δ * L ^ ((d : ℝ) / p) := hnorm
    calc 4 * (d : ℝ) * (1 / (1 - (d : ℝ) / p)) * ‖x - y‖ ^ (1 - (d : ℝ) / p) *
          (eLpNorm (fun w => ‖uW.grad w‖) (ENNReal.ofReal p)
            (volume.restrict (axisCube z L))).toReal
        ≤ C₀ * L ^ (1 - (d : ℝ) / p) * (δ * L ^ ((d : ℝ) / p)) := by
          rw [← hC₀]
          gcongr
      _ = C₀ * C₀ * L ^ (1 + (1 - (d : ℝ) / p)) * N := by
          rw [hδ, hL2]
          have := hLL
          calc C₀ * L ^ (1 - (d : ℝ) / p) * (C₀ * L ^ (1 - (d : ℝ) / p) * N * L ^ ((d : ℝ) / p))
              = C₀ * C₀ * N * L ^ (1 - (d : ℝ) / p) * (L ^ (1 - (d : ℝ) / p) * L ^ ((d : ℝ) / p)) := by
                ring
            _ = _ := by rw [this]; ring

end SuperdiffusionCLT.Section7
