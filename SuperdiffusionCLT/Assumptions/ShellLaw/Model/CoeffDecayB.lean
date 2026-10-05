/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.CoeffDecay
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Smoothness and decay of the cell kernel coefficients

The coefficient `x ↦ cellKernelCoeff c x p` is the convolution of the compactly supported
continuous function `u ↦ cellTrig p u * w u` with the smooth bump `ψ`, shifted by `c`.
Hence it is smooth, and its derivatives are the coefficients of the differentiated bump.

## Main results

* `contDiff_cellKernelCoeff`: smoothness in `x`.
* `exists_norm_iteratedFDeriv_cellKernelCoeff_le`: for every `N` there is a constant `C`, depending
  only on `d` and `N`, with
  `‖iteratedFDeriv ℝ i (fun x ↦ cellKernelCoeff c x p) x‖ ≤ C / (1 + cellFreqNorm p) ^ N`
  for `i ≤ 2`, uniformly in `c`, `x`, `p`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Assumptions.ShellLaw.Model

open Homogenization Set Real MeasureTheory
open scoped Convolution

noncomputable section

variable {d : ℕ}

/-! ## The coefficient of `u ↦ w u * h (x - u)` -/

/-- The frame coefficient of `u ↦ w u * h (x - u)`. -/
def nv_Q (p : (Fin d → ℤ) ⊕ (Fin d → ℤ)) (h : Vec d → ℝ) (x : Vec d) : ℝ :=
  cellCoeff p fun u ↦ cellWeight d u * h (x - u)

theorem cellKernelCoeff_eq_nv_Q (c x : Vec d) (p : (Fin d → ℤ) ⊕ (Fin d → ℤ)) :
    cellKernelCoeff c x p = nv_Q p (radialBump d) (x - c) := by
  unfold cellKernelCoeff nv_Q
  rfl

theorem nv_contDiff_of_top {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Vec d → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (N : ℕ) :
    ContDiff ℝ (N : WithTop ℕ∞) f :=
  hf.of_le (by exact_mod_cast le_top)

theorem nv_contDiff_dir {h : Vec d → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (v : Vec d) :
    ContDiff ℝ (⊤ : ℕ∞) (nv_dir v h) := by
  have : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ h) :=
    hh.fderiv_right (m := (⊤ : ℕ∞)) (by exact_mod_cast le_top)
  exact this.clm_apply contDiff_const

/-- Reflection and translation do not change the sup norm of derivatives. -/
theorem nv_norm_iteratedFDeriv_sub_le {h : Vec d → ℝ} {M : ℝ} (x : Vec d) (l : ℕ)
    (hM : ∀ y, ‖iteratedFDeriv ℝ l h y‖ ≤ M) (u : Vec d) :
    ‖iteratedFDeriv ℝ l (fun u ↦ h (x - u)) u‖ ≤ M := by
  have e : (fun u : Vec d ↦ h (x - u))
      = (fun y : Vec d ↦ h (x + y)) ∘ (LinearIsometryEquiv.neg ℝ (E := Vec d)) := by
    funext u; simp [sub_eq_add_neg]
  rw [e, LinearIsometryEquiv.norm_iteratedFDeriv_comp_right, iteratedFDeriv_comp_add_left]
  exact hM _

/-- Uniform bounds on the derivatives of `u ↦ w u * h (x - u)`. -/
theorem nv_norm_iteratedFDeriv_wh_le {N : ℕ} {Mw M : ℝ}
    (hw : ∀ i ≤ N, ∀ y, ‖iteratedFDeriv ℝ i (cellWeight d) y‖ ≤ Mw) {h : Vec d → ℝ}
    (hh : ContDiff ℝ (N : WithTop ℕ∞) h) (hM : ∀ i ≤ N, ∀ y, ‖iteratedFDeriv ℝ i h y‖ ≤ M)
    (x : Vec d) {i : ℕ} (hi : i ≤ N) (u : Vec d) :
    ‖iteratedFDeriv ℝ i (fun u ↦ cellWeight d u * h (x - u)) u‖ ≤ 2 ^ N * (Mw * M) := by
  have hwc : ContDiff ℝ (N : WithTop ℕ∞) (cellWeight d) := nv_contDiff_of_top cellWeight_contDiff N
  have hhc : ContDiff ℝ (N : WithTop ℕ∞) (fun u : Vec d ↦ h (x - u)) :=
    hh.comp (contDiff_const.sub contDiff_id)
  have h1 := norm_iteratedFDeriv_mul_le hwc hhc u (n := i) (by exact_mod_cast hi)
  have hMw : 0 ≤ Mw := (norm_nonneg _).trans (hw 0 (Nat.zero_le _) 0)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (Nat.zero_le _) 0)
  refine h1.trans ?_
  calc ∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) * ‖iteratedFDeriv ℝ k (cellWeight d) u‖
        * ‖iteratedFDeriv ℝ (i - k) (fun u ↦ h (x - u)) u‖
      ≤ ∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) * (Mw * M) := by
        refine Finset.sum_le_sum fun k hk ↦ ?_
        have hk' : k ≤ N := by
          have := Finset.mem_range.1 hk
          omega
        have a1 := hw k hk' u
        have a2 := nv_norm_iteratedFDeriv_sub_le x (i - k) (fun y ↦ hM (i - k) (by omega) y) u
        have hc : (0 : ℝ) ≤ i.choose k := Nat.cast_nonneg _
        calc (i.choose k : ℝ) * ‖iteratedFDeriv ℝ k (cellWeight d) u‖
              * ‖iteratedFDeriv ℝ (i - k) (fun u ↦ h (x - u)) u‖
            ≤ (i.choose k : ℝ) * Mw * M :=
              mul_le_mul (mul_le_mul_of_nonneg_left a1 hc) a2 (norm_nonneg _)
                (mul_nonneg hc hMw)
          _ = (i.choose k : ℝ) * (Mw * M) := by ring
    _ = 2 ^ i * (Mw * M) := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose i
    _ ≤ 2 ^ N * (Mw * M) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hi) (mul_nonneg hMw hM0)

/-- Decay of the coefficient in the single coordinate `j`. -/
theorem nv_abs_Q_pow_le (j : Fin d) {N : ℕ} {Mw M : ℝ}
    (hw : ∀ i ≤ N, ∀ y, ‖iteratedFDeriv ℝ i (cellWeight d) y‖ ≤ Mw) {h : Vec d → ℝ}
    (hh : ContDiff ℝ (N : WithTop ℕ∞) h) (hM : ∀ i ≤ N, ∀ y, ‖iteratedFDeriv ℝ i h y‖ ≤ M)
    (p : (Fin d → ℤ) ⊕ (Fin d → ℤ)) (x : Vec d) :
    (2 * π * |((cellFreq p j : ℤ) : ℝ)|) ^ N * |nv_Q p h x| ≤ 2 ^ N * (Mw * M) := by
  refine nv_pow_mul_abs_cellCoeff_le j (2 ^ N * (Mw * M)) N
    (fun u ↦ cellWeight d u * h (x - u)) ?_ ?_ ?_ p
  · exact (nv_contDiff_of_top cellWeight_contDiff N).mul (hh.comp (contDiff_const.sub contDiff_id))
  · intro u hu
    obtain ⟨i, hi⟩ := hu
    rw [cellWeight_eq_zero_of_half_le hi.le, zero_mul]
  · exact fun i hi u ↦ nv_norm_iteratedFDeriv_wh_le hw hh hM x hi u

/-- The constant of the decay estimate. -/
def nv_K (d N : ℕ) (Mw M : ℝ) : ℝ := ((d : ℝ) + 1) ^ N * 2 ^ (N + 1) * (2 ^ N * (Mw * M))

theorem nv_pow_le_two_mul {a : ℝ} (ha : 0 ≤ a) (N : ℕ) : (1 + a) ^ N ≤ 2 ^ N * (1 + a ^ N) := by
  rcases le_total a 1 with h | h
  · calc (1 + a) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by linarith only [ha]) (by linarith only [h]) N
      _ ≤ 2 ^ N * (1 + a ^ N) := by
        have : (0 : ℝ) ≤ a ^ N := pow_nonneg ha N
        have h2 : (0 : ℝ) ≤ 2 ^ N := by positivity
        nlinarith only [this, h2]
  · calc (1 + a) ^ N ≤ (2 * a) ^ N := pow_le_pow_left₀ (by linarith only [ha]) (by linarith only [h]) N
      _ = 2 ^ N * a ^ N := mul_pow _ _ _
      _ ≤ 2 ^ N * (1 + a ^ N) := by
        have h2 : (0 : ℝ) ≤ 2 ^ N := by positivity
        exact mul_le_mul_of_nonneg_left (by linarith only) h2

/-- **Decay of the coefficient of `u ↦ w u * h (x - u)` in the `ℓ¹` size of the frequency.** -/
theorem nv_abs_Q_mul_pow_le {N : ℕ} {Mw M : ℝ}
    (hw : ∀ i ≤ N, ∀ y, ‖iteratedFDeriv ℝ i (cellWeight d) y‖ ≤ Mw) {h : Vec d → ℝ}
    (hh : ContDiff ℝ (N : WithTop ℕ∞) h) (hM : ∀ i ≤ N, ∀ y, ‖iteratedFDeriv ℝ i h y‖ ≤ M)
    (p : (Fin d → ℤ) ⊕ (Fin d → ℤ)) (x : Vec d) :
    |nv_Q p h x| * (1 + cellFreqNorm p) ^ N ≤ nv_K d N Mw M := by
  have hMw : 0 ≤ Mw := (norm_nonneg _).trans (hw 0 (Nat.zero_le _) 0)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (Nat.zero_le _) 0)
  have hB : 0 ≤ 2 ^ N * (Mw * M) := by positivity
  -- the crude bound for the coefficient itself
  have hc0 : |nv_Q p h x| ≤ 2 ^ N * (Mw * M) := by
    have := nv_norm_iteratedFDeriv_wh_le hw hh hM x (Nat.zero_le N) 0
    refine nv_abs_cellCoeff_le p (fun u hu ↦ ?_) (fun u ↦ ?_)
    · obtain ⟨i, hi⟩ := hu
      rw [cellWeight_eq_zero_of_half_le hi.le, zero_mul]
    · have h2 := nv_norm_iteratedFDeriv_wh_le hw hh hM x (Nat.zero_le N) u
      simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using h2
  have hd : (0 : ℝ) ≤ (d : ℝ) + 1 := by positivity
  by_cases hd0 : d = 0
  · subst hd0
    have hS : cellFreqNorm p = 0 := by simp [cellFreqNorm]
    rw [hS, add_zero, one_pow, mul_one]
    refine hc0.trans ?_
    unfold nv_K
    have h2 : (1 : ℝ) ≤ ((0 : ℕ) : ℝ) + 1 := by simp
    have h3 : (1 : ℝ) ≤ (((0 : ℕ) : ℝ) + 1) ^ N := one_le_pow₀ h2
    have h4 : (1 : ℝ) ≤ 2 ^ (N + 1) := one_le_pow₀ (by norm_num)
    calc 2 ^ N * (Mw * M) = 1 * 1 * (2 ^ N * (Mw * M)) := by ring
      _ ≤ (((0 : ℕ) : ℝ) + 1) ^ N * 2 ^ (N + 1) * (2 ^ N * (Mw * M)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul h3 h4 zero_le_one (by positivity)) hB
  · have hne : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero hd0⟩⟩
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ
      (fun i ↦ |((cellFreq p i : ℤ) : ℝ)|) ⟨Classical.arbitrary _, Finset.mem_univ _⟩
    set a : ℝ := |((cellFreq p j : ℤ) : ℝ)| with ha
    have ha0 : 0 ≤ a := abs_nonneg _
    have hS : cellFreqNorm p ≤ d * a := by
      unfold cellFreqNorm
      calc ∑ i, |((cellFreq p i : ℤ) : ℝ)| ≤ ∑ _i : Fin d, a :=
            Finset.sum_le_sum fun i _ ↦ hj i (Finset.mem_univ i)
        _ = d * a := by simp
    have hS0 := cellFreqNorm_nonneg p
    have hj1 := nv_abs_Q_pow_le j hw hh hM p x
    have hpi : (1 : ℝ) ≤ 2 * π := by linarith only [Real.pi_gt_three]
    have hapow : a ^ N * |nv_Q p h x| ≤ 2 ^ N * (Mw * M) := by
      refine le_trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)) hj1
      exact pow_le_pow_left₀ ha0 (by nlinarith only [hpi, ha0]) N
    have h1 : 1 + cellFreqNorm p ≤ ((d : ℝ) + 1) * (1 + a) := by
      have : (0 : ℝ) ≤ d * a := mul_nonneg (Nat.cast_nonneg _) ha0
      nlinarith only [hS, ha0, this]
    have h2 : (1 + cellFreqNorm p) ^ N ≤ ((d : ℝ) + 1) ^ N * (2 ^ N * (1 + a ^ N)) := by
      calc (1 + cellFreqNorm p) ^ N ≤ (((d : ℝ) + 1) * (1 + a)) ^ N :=
            pow_le_pow_left₀ (by linarith only [hS0]) h1 N
        _ = ((d : ℝ) + 1) ^ N * (1 + a) ^ N := mul_pow _ _ _
        _ ≤ ((d : ℝ) + 1) ^ N * (2 ^ N * (1 + a ^ N)) :=
            mul_le_mul_of_nonneg_left (nv_pow_le_two_mul ha0 N) (by positivity)
    calc |nv_Q p h x| * (1 + cellFreqNorm p) ^ N
        ≤ |nv_Q p h x| * (((d : ℝ) + 1) ^ N * (2 ^ N * (1 + a ^ N))) :=
          mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      _ = ((d : ℝ) + 1) ^ N * 2 ^ N * (|nv_Q p h x| + a ^ N * |nv_Q p h x|) := by ring
      _ ≤ ((d : ℝ) + 1) ^ N * 2 ^ N * (2 ^ N * (Mw * M) + 2 ^ N * (Mw * M)) :=
          mul_le_mul_of_nonneg_left (add_le_add hc0 hapow) (by positivity)
      _ = nv_K d N Mw M := by unfold nv_K; ring

/-! ## Differentiation of the coefficient -/

theorem nv_continuous_g (p : (Fin d → ℤ) ⊕ (Fin d → ℤ)) :
    Continuous fun u : Vec d ↦ cellTrig p u * cellWeight d u :=
  (continuous_cellTrig p).mul cellWeight_contDiff.continuous

theorem nv_Q_eq_convolution (p : (Fin d → ℤ) ⊕ (Fin d → ℤ)) (h : Vec d → ℝ) :
    nv_Q p h = (fun u : Vec d ↦ cellTrig p u * cellWeight d u)
      ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] h := by
  funext x
  rw [convolution_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u ↦ ?_)
  simp only [ContinuousLinearMap.mul_apply', mul_assoc]

theorem nv_contDiff_Q (p : (Fin d → ℤ) ⊕ (Fin d → ℤ)) {h : Vec d → ℝ}
    (hc : HasCompactSupport h) (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    ContDiff ℝ (⊤ : ℕ∞) (nv_Q p h) := by
  have hloc : LocallyIntegrable (fun u : Vec d ↦ cellTrig p u * cellWeight d u) volume :=
    (nv_continuous_g p).locallyIntegrable
  rw [nv_Q_eq_convolution]
  exact hc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hloc hh

/-- **Differentiation under the integral.** -/
theorem nv_fderiv_Q_apply (p : (Fin d → ℤ) ⊕ (Fin d → ℤ)) {h : Vec d → ℝ}
    (hc : HasCompactSupport h) (hh : ContDiff ℝ 1 h) (x v : Vec d) :
    fderiv ℝ (nv_Q p h) x v = nv_Q p (nv_dir v h) x := by
  have hloc : LocallyIntegrable (fun u : Vec d ↦ cellTrig p u * cellWeight d u) volume :=
    (nv_continuous_g p).locallyIntegrable
  have hd := hc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hloc hh x
  rw [← nv_Q_eq_convolution] at hd
  have hint : Integrable (fun t ↦ (ContinuousLinearMap.mul ℝ ℝ).precompR (Vec d)
      (cellTrig p t * cellWeight d t) (fderiv ℝ h (x - t))) volume :=
    ((hc.fderiv ℝ).convolutionExists_right _ hloc
      (hh.continuous_fderiv one_ne_zero) x).integrable
  rw [hd.fderiv, convolution_def, ContinuousLinearMap.integral_apply hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u ↦ ?_)
  simp only [nv_dir, ContinuousLinearMap.precompR_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply', mul_assoc]

theorem nv_fderiv_fderiv_Q_apply (p : (Fin d → ℤ) ⊕ (Fin d → ℤ)) {h : Vec d → ℝ}
    (hc : HasCompactSupport h) (hh : ContDiff ℝ (⊤ : ℕ∞) h) (x v w : Vec d) :
    fderiv ℝ (fderiv ℝ (nv_Q p h)) x v w = nv_Q p (nv_dir v (nv_dir w h)) x := by
  have hQ := nv_contDiff_Q p hc hh
  have hdiff : DifferentiableAt ℝ (fderiv ℝ (nv_Q p h)) x :=
    ((hQ.fderiv_right (m := 1) (WithTop.coe_le_coe.2 le_top)).differentiable one_ne_zero) x
  have h1 := (ContinuousLinearMap.apply ℝ ℝ w).hasFDerivAt.comp x hdiff.hasFDerivAt
  have h2 : ((ContinuousLinearMap.apply ℝ ℝ w) ∘ fderiv ℝ (nv_Q p h))
      = nv_Q p (nv_dir w h) :=
    funext fun y ↦ nv_fderiv_Q_apply p hc (hh.of_le (by exact_mod_cast le_top)) y w
  rw [h2] at h1
  have h3 := nv_fderiv_Q_apply p (h := nv_dir w h) (hc.fderiv_apply ℝ w)
    ((nv_contDiff_dir hh w).of_le (by exact_mod_cast le_top)) x v
  rw [h1.fderiv] at h3
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply] using h3

/-! ## Norms of continuous linear maps on `Vec d` -/

theorem nv_norm_le_sum_single {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : Vec d →L[ℝ] G) : ‖L‖ ≤ ∑ j, ‖L (Pi.single j 1)‖ := by
  refine L.opNorm_le_bound (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) fun v ↦ ?_
  have hv : v = ∑ j, v j • (Pi.single j (1 : ℝ) : Vec d) := by
    ext i; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  rw [map_sum]
  calc ‖∑ j, L (v j • (Pi.single j (1 : ℝ) : Vec d))‖
      ≤ ∑ j, ‖L (v j • (Pi.single j (1 : ℝ) : Vec d))‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖L (Pi.single j 1)‖ * ‖v‖ := by
        refine Finset.sum_le_sum fun j _ ↦ ?_
        rw [map_smul, norm_smul, mul_comm]
        exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (norm_nonneg _)
    _ = (∑ j, ‖L (Pi.single j 1)‖) * ‖v‖ := by rw [Finset.sum_mul]

/-! ## The main estimates for the kernel coefficients -/

/-- **Smoothness in `x`.** -/
theorem contDiff_cellKernelCoeff (c : Vec d) (p : (Fin d → ℤ) ⊕ (Fin d → ℤ)) :
    ContDiff ℝ (⊤ : ℕ∞) fun x ↦ cellKernelCoeff c x p := by
  have : (fun x ↦ cellKernelCoeff c x p) = fun x ↦ nv_Q p (radialBump d) (x - c) := by
    funext x; exact cellKernelCoeff_eq_nv_Q c x p
  rw [this]
  exact (nv_contDiff_Q p radialBump_hasCompactSupport radialBump_contDiff).comp
    (contDiff_id.sub contDiff_const)

/-- The bounds for the bump and its first two directional derivatives, at level `N`. -/
theorem nv_bump_bounds (N : ℕ) :
    ∃ M, 0 ≤ M ∧ (∀ i ≤ N + 2, ∀ y : Vec d, ‖iteratedFDeriv ℝ i (radialBump d) y‖ ≤ M) :=
  radialBump_exists_bound_iteratedFDeriv (N + 2)

theorem nv_norm_iteratedFDeriv_dir_top_le (v : Vec d) (hv : ‖v‖ ≤ 1) {h : Vec d → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (i : ℕ) (u : Vec d) :
    ‖iteratedFDeriv ℝ i (nv_dir v h) u‖ ≤ ‖iteratedFDeriv ℝ (i + 1) h u‖ := by
  have hf : ContDiffAt ℝ (i : WithTop ℕ∞) (fderiv ℝ h) u :=
    ((nv_contDiff_of_top (f := fderiv ℝ h) (hh.fderiv_right (m := (⊤ : ℕ∞))
      (by exact_mod_cast le_top)) i)).contDiffAt
  have := norm_iteratedFDeriv_clm_apply_const (c := v) hf (n := i) le_rfl
  rw [norm_iteratedFDeriv_fderiv] at this
  exact this.trans (mul_le_of_le_one_left (norm_nonneg _) hv)

end

end SuperdiffusionCLT.Assumptions.ShellLaw.Model
