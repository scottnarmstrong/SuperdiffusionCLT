/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.ExitEstimateB
public import SuperdiffusionCLT.Section8.Prereq.ExitEstimateC
public import SuperdiffusionCLT.Section8.Prereq.BallRescalingB
public import SuperdiffusionCLT.Section8.Prereq.ResolventEstimateC
public import SuperdiffusionCLT.Section8.Root.TheoremAAssembly
public import SuperdiffusionCLT.Section8.Prereq.ResolventEstimateC
public import SuperdiffusionCLT.Section7.Prereq.RootCarriersApi
public import SuperdiffusionCLT.Section7.Analytic.Change.DilationB

/-!
# Rescaling to the unit ball, one ball, and the iteration

* `exitEst_scale_solution`: the zero-trace profile on `V`, dilated to the unit ball, solves the
  rescaled problem for `opScale c⋆ ε' • a^{ε'}` with shift `lam' opScale / ε'^2`;
* `exitEst_one_ball`: the one-ball estimate `1 - lam' w ≤ 2 d exp (-√(2 lamT) δ/√d) + lamT E`;
* `exitEst_iterate`: the iteration over concentric balls, from the one-step bound at every radius.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section8.DivergenceForm
open SuperdiffusionCLT.Section7
open scoped Pointwise

variable {d : ℕ}

/-- **Rescaling of the exit-time profile.**  A zero-trace weak solution of
`lam' u - ∇·(a∇u) = 1` on `V` becomes, after the dilation `y ↦ ε' y`, a weak solution on
`U = ε' V` of the rescaled problem for `opScale c⋆ ε' • a^{ε'}` with shift
`lam' opScale / ε'^2`. -/
theorem exitEst_scale_solution (nu cStar : ℝ) (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
    {ε' : ℝ} (hε' : 0 < ε') (hs' : 0 < opScale cStar ε') {lam' : ℝ} {V U : Set (Vec d)}
    (hset : (ε'⁻¹)⁻¹ • V = U) (u : H10Function V)
    (hsol : IsScalarForcedWeakSolution (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega) V
      (fun y => 1 - lam' * u.toH1Function.toFun y) u.toH1Function) :
    ∃ v : H1Function U,
      IsDirichletSolution (fun x => opScale cStar ε' • epField nu omega ε' x) U
        (fun x => 1 - (lam' * (opScale cStar ε' / ε' ^ 2)) * v.toFun x) 0 v ∧
      ∀ x, v.toFun x = (ε' ^ 2 / opScale cStar ε') * u.toH1Function.toFun (ε'⁻¹ • x) := by
  subst hset
  have hs : ε'⁻¹ ≠ 0 := inv_ne_zero hε'.ne'
  have hweakV : IsWeakSolutionOn (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega) V
      u.toH1Function (fun y => 1 - lam' * u.toH1Function.toFun y) (fun _ => 0) := by
    intro φ
    have := hsol.2 φ
    simp only [vecDot, Pi.zero_apply, zero_mul, Finset.sum_const_zero, integral_zero, add_zero]
    exact this
  have hdil := IsWeakSolutionOn.dilate_h10 hs hweakV
  set ũ : H1Function ((ε'⁻¹)⁻¹ • V) := (u.dilateArg hs).toH1Function with hũ
  have h1 : IsDirichletSolution (fun x => ε' ^ 2 • epField nu omega ε' x) ((ε'⁻¹)⁻¹ • V)
      (fun x => 1 - lam' * ũ.toFun x) 0 ũ := by
    refine ⟨?_, ⟨u.dilateArg hs, ?_⟩⟩
    · have h3 := IsWeakSolutionOn.smul (ε' ^ 2) hdil
      refine rc_isWeakSolutionOn_congr (fun y => rfl) (fun y => ?_) (fun y => ?_) h3
      · simp only [hũ, H10Function.dilateArg_toH1Function, H1Function.dilateArg_toFun]
        field_simp
      · simp
    · funext x
      simp [hũ]
  have h2 := resEst_prefactor_shift (A := epField nu omega ε') (s₁ := ε' ^ 2)
    (s₂ := opScale cStar ε') (by positivity) hs' h1
  refine ⟨(ε' ^ 2 / opScale cStar ε') • ũ, h2, fun x => ?_⟩
  simp [hũ, H1Function.smul_toFun, H10Function.dilateArg_toH1Function, H1Function.dilateArg_toFun]

/-- Almost-everywhere statements transfer through the dilation. -/
theorem exitEst_ae_dilate {s : ℝ} (hs : s ≠ 0) (V : Set (Vec d)) {P : Vec d → Prop}
    (h : ∀ᵐ z ∂(volume.restrict V), P z) : ∀ᵐ y ∂(volume.restrict (s⁻¹ • V)), P (s • y) := by
  have hm := a18_measurableEmbedding (d := d) hs
  have hmap := a18_map_restrict (d := d) hs V
  refine ae_of_ae_map hm.measurable.aemeasurable ?_
  rw [hmap]
  exact MeasureTheory.Measure.ae_smul_measure h _

/-- The ball `{y | |ε' y| < 1}` is the dilate of the ball of radius `ε'⁻¹`. -/
theorem exitEst_ball_dilate {ε' : ℝ} (hε' : 0 < ε') :
    (ε'⁻¹)⁻¹ • euclideanBall (0 : Vec d) ε'⁻¹ = euclideanBall (0 : Vec d) 1 := by
  ext y
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ (by simpa using hε'.ne')]
  simp only [inv_inv, euclideanBall, euclideanSqDist, sub_zero, Set.mem_ofPred_eq,
    vecNormSq_smul, one_pow]
  have h2 : 0 < ε' ^ 2 := by positivity
  rw [inv_pow, ← one_div, ← mul_lt_mul_iff_of_pos_left h2]
  field_simp

/-- `opScale` is positive off `ε = 1`. -/
theorem exitEst_opScale_pos {cStar ε : ℝ} (hc : 0 < cStar) (hε : 0 < ε) (hε1 : ε < 1) :
    0 < opScale cStar ε := by
  have hl : 0 < |Real.log ε| := abs_pos.2 (Real.log_neg hε hε1).ne
  unfold opScale
  have : 0 < (2 * cStar * |Real.log ε|) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos (by positivity) _
  positivity

/-- **One ball.**  Let `w` be the continuous zero-trace profile on the ball of radius `ε'⁻¹` for the
shift `lam'`, and suppose that the rescaled profile is within `E` of the profile of the heat field
(the exit-time form of the resolvent estimate).  At every point `x` with
`{y | |y - ε' x| < δ} ⊆ B₁`,
`1 - lam' w x ≤ 2 d exp (-√(2 lamT) δ/√d) + lamT E`, `lamT = lam' opScale / ε'^2`. -/
theorem exitEst_one_ball [NeZero d] (hd : 2 ≤ d) {nu cStar : ℝ}
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) {ε' lam' E : ℝ}
    (hc : 0 < cStar) (hε' : 0 < ε') (hε'1 : ε' < 1) (hlam' : 0 < lam')
    (hA1 : ∀ lam : ℝ, 0 < lam → ∀ v vb : H1Function (euclideanBall (0 : Vec d) 1),
      IsDirichletSolution (fun x => opScale cStar ε' • epField nu omega ε' x)
        (euclideanBall (0 : Vec d) 1) (fun x => 1 - lam * v.toFun x) 0 v →
      IsDirichletSolution (fun _ => (1 / 2 : ℝ) • (1 : Mat d)) (euclideanBall (0 : Vec d) 1)
        (fun x => 1 - lam * vb.toFun x) 0 vb →
      ∀ᵐ x ∂(volume.restrict (euclideanBall (0 : Vec d) 1)), |v.toFun x - vb.toFun x| ≤ E)
    {w : Vec d → ℝ} (u : H10Function (euclideanBall (0 : Vec d) ε'⁻¹)) (hw : Continuous w)
    (hwu : ∀ᵐ y ∂(volume.restrict (euclideanBall (0 : Vec d) ε'⁻¹)),
      w y = u.toH1Function.toFun y)
    (hsol : IsScalarForcedWeakSolution (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega)
      (euclideanBall (0 : Vec d) ε'⁻¹) (fun y => 1 - lam' * u.toH1Function.toFun y) u.toH1Function)
    {δ : ℝ} (hδ : 0 < δ) (x : Vec d)
    (hx : ∀ y : Vec d, vecNormSq (y - ε' • x) < δ ^ 2 → y ∈ euclideanBall (0 : Vec d) 1) :
    1 - lam' * w x ≤
      2 * d * Real.exp (-(Real.sqrt (lam' * (opScale cStar ε' / ε' ^ 2) / (1 / 2)) *
        (δ / Real.sqrt d))) + lam' * (opScale cStar ε' / ε' ^ 2) * E := by
  have hs' := exitEst_opScale_pos hc hε' hε'1
  have hlamT : 0 < lam' * (opScale cStar ε' / ε' ^ 2) := by positivity
  obtain ⟨v, hv, hvx⟩ := exitEst_scale_solution nu cStar omega hε' hs' (exitEst_ball_dilate hε') u hsol
  obtain ⟨wb, vb, hwb, hvb, hwbvb, hdecay⟩ := exitEst_limit_profile hd hlamT
  have hae := hA1 _ hlamT v vb hv hvb
  have hvc : ∀ᵐ y ∂(volume.restrict (euclideanBall (0 : Vec d) 1)),
      v.toFun y = ε' ^ 2 / opScale cStar ε' * w (ε'⁻¹ • y) := by
    have h1 := exitEst_ae_dilate (inv_ne_zero hε'.ne') (euclideanBall (0 : Vec d) ε'⁻¹)
      (P := fun z => w z = u.toH1Function.toFun z) hwu
    rw [exitEst_ball_dilate hε'] at h1
    filter_upwards [h1] with y hy
    rw [hvx, hy]
  have hpt : ∀ᵐ y ∂(volume.restrict (euclideanBall (0 : Vec d) 1)),
      |ε' ^ 2 / opScale cStar ε' * w (ε'⁻¹ • y) - wb y| ≤ E := by
    filter_upwards [hae, hvc, hwbvb] with y h1 h2 h3
    rw [← h2, h3]
    exact h1
  have hV := SuperdiffusionCLT.Section8.Common.Regularity.Ported.isOpenBoundedConvexDomain_euclideanBall
    (0 : Vec d) one_pos
  have hcont : Continuous (fun y : Vec d => ε' ^ 2 / opScale cStar ε' * w (ε'⁻¹ • y)) :=
    continuous_const.mul (hw.comp (continuous_const_smul _))
  have hev : ∀ y ∈ euclideanBall (0 : Vec d) 1,
      |ε' ^ 2 / opScale cStar ε' * w (ε'⁻¹ • y) - wb y| ≤ E := by
    have hup := le_of_ae_le_of_continuousOn hV.isOpen
      ((hcont.sub hwb).abs.continuousOn) continuousOn_const hpt
    exact hup
  have hy : ε' • x ∈ euclideanBall (0 : Vec d) 1 :=
    hx _ (by simp [vecNormSq, vecDot]; positivity)
  have h5 := hev _ hy
  have h6 : ε'⁻¹ • ε' • x = x := inv_smul_smul₀ hε'.ne' x
  rw [h6] at h5
  have h7 := hdecay (ε' • x) δ hδ hx
  have e : lam' * w x = lam' * (opScale cStar ε' / ε' ^ 2) * (ε' ^ 2 / opScale cStar ε' * w x) := by
    field_simp
  rw [e]
  have h8 := (abs_le.1 h5).1
  nlinarith only [h7, h8, hlamT]

/-- **The iteration over concentric balls.**  Let `w₁` be the zero-trace profile of the ball of radius
`1/ε` (shift `lam'`).  If at every radius `ρ ∈ [1/2, 1]` the profile of the ball of radius `ρ/ε` is at
most `q ≤ 1/2` on the ball of radius `(ρ - h)/ε`, then the positive part of `1 - lam' w₁` is at most
`2^{-N}` on the ball of radius `1/(2ε)`, with `N ≥ 1/(4h) - 1`. -/
theorem exitEst_iterate [NeZero d] {nu : ℝ} {k : Vec d → Mat d} (D : FieldInputData d nu k)
    {ε lam' h q : ℝ} (hε : 0 < ε) (hlam' : 0 < lam') (hh : 0 < h) (hh8 : h ≤ 1 / 8)
    (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2)
    (hone : ∀ ρ : ℝ, 1 / 2 ≤ ρ → ρ ≤ 1 →
      ∀ (w : Vec d → ℝ) (u : H10Function (euclideanBall (0 : Vec d) (ρ / ε))), Continuous w →
        (∀ y, y ∉ euclideanBall (0 : Vec d) (ρ / ε) → w y = 0) →
        (∀ᵐ y ∂volumeMeasureOn (euclideanBall (0 : Vec d) (ρ / ε)), w y = u.toH1Function.toFun y) →
        IsScalarForcedWeakSolution D.analyticData.a (euclideanBall (0 : Vec d) (ρ / ε))
          (fun y => 1 - lam' * u.toH1Function.toFun y) u.toH1Function →
        ∀ y : Vec d, vecNormSq y ≤ ((ρ - h) / ε) ^ 2 → max (1 - lam' * w y) 0 ≤ q)
    {w₁ : Vec d → ℝ} (u₁ : H10Function (euclideanBall (0 : Vec d) (1 / ε))) (hw₁ : Continuous w₁)
    (hoff₁ : ∀ y, y ∉ euclideanBall (0 : Vec d) (1 / ε) → w₁ y = 0)
    (hwu₁ : ∀ᵐ y ∂volumeMeasureOn (euclideanBall (0 : Vec d) (1 / ε)),
      w₁ y = u₁.toH1Function.toFun y)
    (hsol₁ : IsScalarForcedWeakSolution D.analyticData.a (euclideanBall (0 : Vec d) (1 / ε))
      (fun y => 1 - lam' * u₁.toH1Function.toFun y) u₁.toH1Function) :
    ∃ N : ℕ, 1 / (4 * h) - 1 ≤ N ∧ ∀ y : Vec d, vecNormSq y ≤ ((1 / 2) / ε) ^ 2 →
      max (1 - lam' * w₁ y) 0 ≤ Real.exp (-(N * Real.log 2)) := by
  have hV₁ := SuperdiffusionCLT.Section8.Common.Regularity.Ported.isOpenBoundedConvexDomain_euclideanBall
    (0 : Vec d) (one_div_pos.2 hε)
  have hrep₁ := ballExit_rep_of_weakSolution D.analyticData hV₁ hlam' hwu₁ hsol₁
  have hw₁nn : ∀ y, 0 ≤ w₁ y := by
    intro y
    by_cases hy : y ∈ euclideanBall (0 : Vec d) (1 / ε)
    · exact ballExit_nonneg_on D hV₁ ⟨lam', hlam'⟩ hw₁ hrep₁ hy
    · rw [hoff₁ y hy]
  set f : Vec d → ℝ := fun y => max (1 - lam' * w₁ y) 0 with hf
  have hf0 : ∀ y, 0 ≤ f y := fun y => le_max_right _ _
  have hf1 : ∀ y, f y ≤ 1 := fun y => max_le (by nlinarith only [hlam', hw₁nn y]) zero_le_one
  let M : ℝ → ℝ := fun r => sSup (f '' {y : Vec d | vecNormSq y ≤ (r / ε) ^ 2})
  have hMle : ∀ r y, vecNormSq y ≤ (r / ε) ^ 2 → f y ≤ M r := fun r y hy =>
    le_csSup ⟨1, by rintro _ ⟨z, -, rfl⟩; exact hf1 z⟩ ⟨y, hy, rfl⟩
  have hM0 : ∀ r, 0 ≤ M r := fun r =>
    (hf0 0).trans (hMle r 0 (by simp [vecNormSq, vecDot]; positivity))
  have hM1 : ∀ r, M r ≤ 1 := fun r =>
    Real.sSup_le (by rintro _ ⟨z, -, rfl⟩; exact hf1 z) zero_le_one
  let M' : ℝ → ℝ := fun r => if r < 1 then M r else 1
  have hM'1 : ∀ r, M' r ≤ 1 := fun r => by
    by_cases hr : r < 1
    · simp [M', hr, hM1 r]
    · simp [M', hr]
  have hstep : ∀ r : ℝ, 1 / 2 ≤ r → r + h ≤ 1 → M' r ≤ q * M' (r + h) := by
    intro r hr hrh
    have hr1 : r < 1 := by linarith only [hrh, hh]
    have hMr : M' r = M r := by simp [M', hr1]
    rw [hMr]
    refine Real.sSup_le ?_ (mul_nonneg hq0 (by by_cases h1 : r + h < 1 <;> simp [M', h1, hM0]))
    rintro _ ⟨y, hy, rfl⟩
    have hy' : vecNormSq y ≤ ((r + h - h) / ε) ^ 2 := by simpa using hy
    by_cases hρ : r + h < 1
    · have hMρ : M' (r + h) = M (r + h) := by simp [M', hρ]
      rw [hMρ]
      obtain ⟨w, u, hw, hoff, hwu, hsol⟩ :=
        ballBdry_data D (0 : Vec d) (div_pos (by linarith only [hr, hh]) hε) hlam' (r := (r + h) / ε)
      have hq' := hone (r + h) (by linarith only [hr, hh]) hρ.le w u hw hoff hwu hsol y hy'
      have hεR : (r + h) / ε < 1 / ε := by gcongr
      have hV₂ := SuperdiffusionCLT.Section8.Common.Regularity.Ported.isOpenBoundedConvexDomain_euclideanBall
        (0 : Vec d) (div_pos (by linarith only [hr, hh]) hε)
      have hy2 : vecNormSq y < ((r + h) / ε) ^ 2 := by
        refine lt_of_le_of_lt hy' ?_
        have : r + h - h < r + h := by linarith only [hh]
        have h0 : 0 ≤ (r + h - h) / ε := div_nonneg (by linarith only [hr]) hε.le
        nlinarith only [this, h0, hε, div_lt_div_of_pos_right this hε]
      have hcmp := exitEst_ball_compare D (div_pos (by linarith only [hr, hh]) hε) hεR hlam'
        u hw hoff hwu hsol u₁ hw₁ hoff₁ hwu₁ hsol₁ (M := M (r + h))
        (fun y' hy'' => hMle (r + h) y' hy'') hy2
      calc f y ≤ M (r + h) * max (1 - lam' * w y) 0 := hcmp
        _ ≤ M (r + h) * q := mul_le_mul_of_nonneg_left hq' (hM0 _)
        _ = q * M (r + h) := mul_comm _ _
    · have hρ1 : r + h = 1 := le_antisymm hrh (not_lt.1 hρ)
      have hMρ : M' (r + h) = 1 := by simp [M', hρ]
      rw [hMρ, mul_one]
      have hrr : 1 - h = r := by linarith only [hρ1]
      exact hone 1 (by norm_num) le_rfl w₁ u₁ hw₁ hoff₁ hwu₁ hsol₁ y (by
        rw [hrr]
        exact hy)
  obtain ⟨N, hN, hMN⟩ := ballResc_iteration hh hh8 hq0 hq M' hM'1 hstep
  refine ⟨N, hN, fun y hy => (hMle (1 / 2) y hy).trans ?_⟩
  have h12 : M' (1 / 2) = M (1 / 2) := by simp only [M', show ((1 : ℝ) / 2) < 1 by norm_num, ↓reduceIte]
  rw [← h12]
  exact hMN

section Witness

open MarkovProcess SuperdiffusionCLT.Section2.Cutoff SuperdiffusionCLT.Section6
open SuperdiffusionCLT.Frozen.Assumptions

end Witness

end SuperdiffusionCLT.Section8
