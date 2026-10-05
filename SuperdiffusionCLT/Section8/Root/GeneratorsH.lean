/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Root.GeneratorsG
public import SuperdiffusionCLT.Section8.Prereq.ResolventEstimateC

/-!
# The whole-space solution for one sample and one scale

`gen_fixed_scale`: for one sample and one scale `ε'` for which the decay estimate holds, the
rescaled field has a `C² ∩ C₀` solution `U` of `∇·(a∇U) = -G` on `ℝ^d` (for a smooth source `G`
supported in the unit ball with mean zero), which is the uniform limit of continuous Dirichlet
solutions `w_m` on the balls `B_m`, with an explicit decay rate `ψ_m → 0`.
-/

@[expose] public section

open Homogenization MeasureTheory Filter Topology SuperdiffusionCLT.Section6
  SuperdiffusionCLT.Section7 SuperdiffusionCLT.Section8.DivergenceForm
open scoped ENNReal Pointwise Matrix.Norms.Elementwise

namespace SuperdiffusionCLT.Section8

variable {d : ℕ}

/-- The rescaled operator field has the skew-plus-scalar structure. -/
theorem gen_scaled_skew (nu cs : ℝ) (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
    (ε' : ℝ) (y : Vec d) (i j : Fin d) :
    (opScale cs ε' • epCoeff nu omega ε' y) i j + (opScale cs ε' • epCoeff nu omega ε' y) j i =
      if i = j then 2 * (opScale cs ε' * nu) else 0 := by
  have hk := fullStreamRecentered_skew_entry omega (ε'⁻¹ • y) i j
  by_cases h : i = j
  · subst h
    simp only [epCoeff, fullCoefficientRecentered, Matrix.smul_apply, Matrix.add_apply,
      Matrix.one_apply_eq, smul_eq_mul, ite_true]
    have := fullStreamRecentered_skew_entry omega (ε'⁻¹ • y) i i
    have h0 : fullStreamRecentered omega (ε'⁻¹ • y) i i = 0 := by linarith only [this]
    rw [h0]; ring
  · have h' : ¬ j = i := fun e => h e.symm
    simp only [epCoeff, fullCoefficientRecentered, Matrix.smul_apply, Matrix.add_apply,
      Matrix.one_apply_ne h, Matrix.one_apply_ne h', smul_eq_mul, h, ↓reduceIte]
    rw [hk]; ring

theorem gen_scaled_contDiff (nu cs : ℝ) (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
    (ε' : ℝ) (hS : ContDiff ℝ 2 (fullStreamRecentered omega)) (i j : Fin d) :
    ContDiff ℝ 2 fun y : Vec d => (opScale cs ε' • epCoeff nu omega ε' y) i j := by
  have h1 : ContDiff ℝ 2 fun y : Vec d => fullStreamRecentered omega (ε'⁻¹ • y) :=
    hS.comp (contDiff_const_smul _)
  have h2 : ContDiff ℝ 2 fun y : Vec d => fullStreamRecentered omega (ε'⁻¹ • y) i j :=
    contDiff_pi.1 (contDiff_pi.1 h1 i) j
  simp only [epCoeff, fullCoefficientRecentered, Matrix.smul_apply, Matrix.add_apply,
    smul_eq_mul]
  exact contDiff_const.mul (contDiff_const.add h2)

/-- **The whole-space solution for one sample and one scale.** -/
theorem gen_fixed_scale [NeZero d] (hd : 2 ≤ d) {nu : ℝ} (hnu : 0 < nu) (cs : ℝ)
    {omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d}
    (D : FieldInputData d nu (fullStreamRecentered omega))
    (hS : ContDiff ℝ 2 (fullStreamRecentered omega)) {ε' : ℝ} (hε' : 0 < ε')
    (hs' : 0 < opScale cs ε')
    (hEllEp : ∀ W : Set (Vec d), Bornology.IsBounded W → MeasurableSet W →
      ∃ Lam, IsEllipticFieldOn nu Lam W (epCoeff nu omega ε'))
    {γ Cd : ℝ} (hγ : 0 < γ) (hCd : 0 ≤ Cd)
    (hdecay : ∀ r R : ℝ, 8 ≤ r → r ≤ R → ∀ (u : H10Function (euclidBall (d := d) R))
      (F : Vec d → ℝ), MemLp F 2 (volume.restrict (euclidBall (d := d) 1)) →
      (∀ x, x ∉ euclidBall (d := d) 1 → F x = 0) → (∫ x in euclidBall (d := d) 1, F x = 0) →
      IsWeakSolutionOn (fun x => opScale cs ε' • epCoeff nu omega ε' x) (euclidBall R)
        u.toH1Function F (fun _ => 0) →
      eLpNorm u.toH1Function.toFun ⊤ (volume.restrict (euclidBall (d := d) R \ euclidBall r)) ≤
        ENNReal.ofReal (Cd * r ^ (-((d : ℝ) - 2 + γ))) *
          eLpNorm F 2 (volume.restrict (euclidBall (d := d) 1)))
    {G : Vec d → ℝ} (hG : ContDiff ℝ 1 G) (hGs : HasCompactSupport G)
    (hGsupp : ∀ x, x ∉ euclidBall (d := d) 1 → G x = 0)
    (hGmean : ∫ x in euclidBall (d := d) 1, G x = 0) :
    ∃ U : Vec d → ℝ, ContDiff ℝ 2 U ∧ IsC0Function U ∧
      (∀ x, divForm 1 (fun x => opScale cs ε' • epCoeff nu omega ε' x) U x = -G x) ∧
      ∀ m : ℕ, 16 ≤ m → ∃ (wR : Vec d → ℝ) (uR : H10Function (euclidBall (d := d) (m : ℝ))),
        Continuous wR ∧ (∀ y, y ∉ euclidBall (d := d) (m : ℝ) → wR y = 0) ∧
        (∀ᵐ y ∂volume.restrict (euclidBall (d := d) (m : ℝ)), wR y = uR.toH1Function.toFun y) ∧
        IsWeakSolutionOn (fun x => opScale cs ε' • epCoeff nu omega ε' x)
          (euclidBall (d := d) (m : ℝ)) uR.toH1Function G (fun _ => 0) ∧
        ∀ y, |U y - wR y| ≤ Cd * ((m : ℝ) / 2) ^ (-((d : ℝ) - 2 + γ)) *
          (eLpNorm G 2 (volume.restrict (euclidBall (d := d) 1))).toReal := by
  have hGc : Continuous G := hG.continuous
  set E : ℝ := (eLpNorm G 2 (volume.restrict (euclidBall (d := d) 1))).toReal with hE
  have hE0 : 0 ≤ E := ENNReal.toReal_nonneg
  have hexp : 0 < (d : ℝ) - 2 + γ := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith only [this, hγ]
  set ψ : ℕ → ℝ := fun m => Cd * ((m : ℝ) / 2) ^ (-((d : ℝ) - 2 + γ)) * E with hψ
  have hψ0 : ∀ m, 0 ≤ ψ m := fun m => by
    simp only [hψ]
    exact mul_nonneg (mul_nonneg hCd (Real.rpow_nonneg (by positivity) _)) hE0
  have hψt : Tendsto ψ atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ => ((m : ℝ) / 2)) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num)
    have h2 := (tendsto_rpow_neg_atTop hexp).comp h1
    have := (h2.const_mul Cd).mul_const E
    rw [mul_zero, zero_mul] at this
    exact this
  set c' := opScale cs ε' with hc'
  have hfam : ∀ m : ℕ, ∃ (w : Vec d → ℝ) (u : H10Function (euclidBall (d := d) (m : ℝ))),
      Continuous w ∧ (0 < (m : ℝ) → (∀ y, y ∉ euclidBall (d := d) (m : ℝ) → w y = 0) ∧
        (∀ᵐ y ∂volume.restrict (euclidBall (d := d) (m : ℝ)), w y = u.toH1Function.toFun y) ∧
        IsWeakSolutionOn (fun x => opScale cs ε' • epCoeff nu omega ε' x)
          (euclidBall (d := d) (m : ℝ)) u.toH1Function G (fun _ => 0)) := by
    intro m
    by_cases hm : 0 < (m : ℝ)
    · obtain ⟨w, u, h1, h2, h3, h4⟩ := gen_scaled_dirichlet D cs hε' hs' hGc hGs hm
      exact ⟨w, u, h1, fun _ => ⟨h2, h3, h4⟩⟩
    · exact ⟨0, 0, continuous_const, fun h => absurd h hm⟩
  choose w uR hwc hrest using hfam
  have hpos : ∀ m : ℕ, 16 ≤ m → (0 : ℝ) < m := fun m hm => by
    exact_mod_cast (by omega : 0 < m)
  have hEll : ∀ s : ℝ, 0 < s → ∃ lam Lam, IsEllipticFieldOn lam Lam (euclidBall (d := d) s)
      (fun x => opScale cs ε' • epCoeff nu omega ε' x) := fun s hs => by
    have hb : Bornology.IsBounded (euclidBall (d := d) s) :=
      Metric.isBounded_ball.subset (euclidBall_subset_ball hs)
    obtain ⟨Lam, hL⟩ := hEllEp _ hb (isOpen_euclidBall s).measurableSet
    exact ⟨c' * nu, c' * Lam, resEst_isEllipticFieldOn_smul hs' hL⟩
  have hdec : ∀ m n : ℕ, 16 ≤ m → m ≤ n → ∀ y, y ∉ euclidBall (d := d) (m : ℝ) → |w n y| ≤ ψ m := by
    intro m n hm hmn y hy
    have hmpos := hpos m hm
    have hnpos := hpos n (hm.trans hmn)
    obtain ⟨hw0, hae, hsol⟩ := hrest n hnpos
    by_cases hyn : y ∈ euclidBall (d := d) (n : ℝ)
    swap
    · rw [hw0 y hyn, abs_zero]; exact hψ0 m
    have hmr : (8 : ℝ) ≤ (m : ℝ) / 2 := by
      have : (16 : ℝ) ≤ m := by exact_mod_cast hm
      linarith only [this]
    have hrR : (m : ℝ) / 2 ≤ (n : ℝ) := by
      have : (m : ℝ) ≤ n := by exact_mod_cast hmn
      linarith only [this, hmpos]
    have hF : MemLp G 2 (volume.restrict (euclidBall (d := d) 1)) :=
      (hGc.memLp_of_hasCompactSupport hGs).restrict _
    have hd1 := hdecay ((m : ℝ) / 2) n hmr hrR (uR n) G hF hGsupp hGmean hsol
    set V : Set (Vec d) := decayEst_ann (d := d) ((m : ℝ) / 2) n with hV
    have hVsub : V ⊆ euclidBall (d := d) (n : ℝ) \ euclidBall (d := d) ((m : ℝ) / 2) := by
      intro x hx
      exact ⟨hx.2, fun h => by
        have h1 := hx.1
        have h2 : vecNormSq x < ((m : ℝ) / 2) ^ 2 := h
        linarith only [h1, h2]⟩
    have hd2 : eLpNorm (uR n).toH1Function.toFun ⊤ (volume.restrict V) ≤
        ENNReal.ofReal (Cd * ((m : ℝ) / 2) ^ (-((d : ℝ) - 2 + γ))) *
          eLpNorm G 2 (volume.restrict (euclidBall (d := d) 1)) :=
      (eLpNorm_mono_measure _ (Measure.restrict_mono hVsub le_rfl)).trans hd1
    have hfin : eLpNorm (uR n).toH1Function.toFun ⊤ (volume.restrict V) ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hF.eLpNorm_ne_top) hd2
    have hbd1 := resEst_ae_abs_le (U := V) hfin
    have hbd2 : (eLpNorm (uR n).toH1Function.toFun ⊤ (volume.restrict V)).toReal ≤ ψ m := by
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hF.eLpNorm_ne_top) hd2
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg hCd
        (Real.rpow_nonneg (by positivity) _))] at this
      exact this
    have hae' : ∀ᵐ x ∂volume.restrict V, |w n x| ≤ ψ m := by
      have h1 := ae_restrict_of_ae_restrict_of_subset (hVsub.trans Set.sdiff_subset) hae
      filter_upwards [hbd1, h1] with x hx1 hx2
      rw [hx2]; exact hx1.trans hbd2
    have hyV : y ∈ V := by
      refine ⟨?_, hyn⟩
      have h1 : ¬ vecNormSq y < (m : ℝ) ^ 2 := hy
      have : ((m : ℝ) / 2) ^ 2 < (m : ℝ) ^ 2 := by nlinarith only [hmpos]
      linarith only [not_lt.1 h1, this]
    exact gen_abs_le_of_ae (decayEst_ann_isOpen _ _) (hwc n) hae' y hyV
  obtain ⟨U, hU2, hU0, hUeq, hUb⟩ := gen_whole_space hd (mul_pos hs' hnu)
    (fun y i j => by simpa using gen_scaled_skew nu cs omega ε' y i j)
    (gen_scaled_contDiff nu cs omega ε' hS) hEll hG hGs (by norm_num : 1 ≤ 16) w uR hwc
    (fun n hn => (hrest n (hpos n hn)).1) (fun n hn => (hrest n (hpos n hn)).2.1)
    (fun n hn => (hrest n (hpos n hn)).2.2) hψt hdec
  exact ⟨U, hU2, hU0, hUeq, fun m hm => ⟨w m, uR m, hwc m, (hrest m (hpos m hm)).1,
    (hrest m (hpos m hm)).2.1, (hrest m (hpos m hm)).2.2, hUb m hm⟩⟩

end SuperdiffusionCLT.Section8
