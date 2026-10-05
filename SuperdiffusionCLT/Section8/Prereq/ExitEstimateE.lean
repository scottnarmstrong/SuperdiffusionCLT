/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.ExitEstimateD
public import SuperdiffusionCLT.Section8.Prereq.FieldProcessInputB
public import SuperdiffusionCLT.Section8.Prereq.BallRescalingB
public import SuperdiffusionCLT.Section8.Prereq.ResolventEstimateC
public import SuperdiffusionCLT.Section8.Root.TheoremAAssembly
public import SuperdiffusionCLT.Section7.Prereq.Domains

/-!
# The exit-time estimate

`l.exit.time.estimate`, from the root theorem
`t.superdiffusivity`, taken as the explicit hypothesis `hRoot`.  The route is elliptic.

For the process of the marginal field and the anchor ball `B = {y | |ε y| < 1}`, the Chernoff bound
gives `Q x {T_B ≤ s} ≤ e^{lam' s} (1 - lam' w x)`, where `w` is the continuous zero-trace profile of
`lam' u - ∇·(a∇u) = 1`.  On the ball of radius `ρ/ε`, rescaled to the unit ball at the scale `ε/ρ`,
the resolvent estimate compares the profile with that of the heat field, which decays exponentially
away from the boundary.  The comparison of the Laplace transforms of nested balls (`ExitEstimateB`)
turns this one-ball bound into an iteration over concentric balls (`ExitEstimateD`), and the
arithmetic of the iteration gives the stated bound (`ballResc_exit_arith`).

* `exitEst_one_ball_R`, `exitEst_hone`: the one-step estimate at every radius `ρ ∈ [1/2, 1]`;
* `exitEst_main_det`: the estimate for a fixed sample, every continuous-path law of the kernel
  semigroup;
* `exitEst_tail`: the tail of the doubled minimal scale;
* `exitEst_exit_time_estimate`: the exit-time estimate, with the root as hypothesis.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization MeasureTheory MarkovProcess
open SuperdiffusionCLT.Section8.DivergenceForm
open SuperdiffusionCLT.Section7
open SuperdiffusionCLT.Section2.Cutoff SuperdiffusionCLT.Section6

variable {d : ℕ}

/-- A point within `δ` of a point of the ball of radius `1 - δ` lies in the unit ball. -/
theorem exitEst_ball_geom {z y' : Vec d} {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hz : vecNormSq z ≤ (1 - δ) ^ 2) (hy : vecNormSq (y' - z) < δ ^ 2) :
    y' ∈ euclideanBall (0 : Vec d) 1 := by
  have h1 : euclideanNorm (y' - z) < δ := by
    have := euclideanNorm_sq (y' - z)
    nlinarith only [this, hy, euclideanNorm_nonneg (y' - z), hδ]
  have h2 : euclideanNorm z ≤ 1 - δ := by
    have := euclideanNorm_sq z
    nlinarith only [this, hz, euclideanNorm_nonneg z, hδ1]
  have h3 : euclideanNorm y' < 1 := by
    have := fieldInput_euclideanNorm_add_le (y' - z) z
    rw [sub_add_cancel] at this
    linarith only [this, h1, h2]
  have h4 : vecNormSq y' < 1 := by
    have := euclideanNorm_sq y'
    nlinarith only [this, h3, euclideanNorm_nonneg y']
  simpa [euclideanBall, euclideanSqDist] using h4

/-- For `ε ≤ 1/4`: `log 2 ≤ |log ε| / 2`. -/
theorem exitEst_log_two_le {ε : ℝ} (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) :
    2 * Real.log 2 ≤ |Real.log ε| := by
  have h1 : Real.log ε ≤ Real.log (1 / 4) := Real.log_le_log hε hε4
  have h2 : Real.log (1 / 4) = -(2 * Real.log 2) := by
    rw [one_div, Real.log_inv, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  have h3 : Real.log ε ≤ 0 := by
    have := (Real.log_pos (by norm_num : (1 : ℝ) < 2))
    linarith only [h1, h2, this]
  rw [abs_of_nonpos h3]
  linarith only [h1, h2]

/-- The change of prefactor between `ε` and `ε/ρ` is a factor in `[1, 2]`. -/
theorem exitEst_opScale_ratio_bounds {cStar ε ρ : ℝ} (hc : 0 < cStar) (hε : 0 < ε)
    (hε4 : ε ≤ 1 / 4) (hρ1 : 1 / 2 ≤ ρ) (hρ : ρ ≤ 1) :
    1 ≤ opScale cStar (ε / ρ) / opScale cStar ε ∧
      opScale cStar (ε / ρ) / opScale cStar ε ≤ 2 := by
  have hερ : ε < ρ := by linarith only [hε4, hρ1]
  have hρ0 : 0 < ρ := by linarith only [hρ1]
  have hrat := ballResc_opScale_ratio hc hε hερ hρ
  have hdiv := ballResc_abs_log_div hε hερ.le hρ
  have hshift := ballResc_abs_log_shift hε (by linarith only [hε4]) hρ1 hρ
  have hL := exitEst_log_two_le hε hε4
  have hl2 := (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  have hLpos : 0 < |Real.log ε| := by linarith only [hL, hl2]
  have hlogρ : 0 ≤ |Real.log ρ| := abs_nonneg _
  set L := |Real.log ε| with hLdef
  set L' := |Real.log (ε / ρ)| with hL'def
  have hL'le : L' ≤ L := by linarith only [hdiv, hlogρ]
  have hL'ge : L / 2 ≤ L' := by
    have := (abs_le.1 hshift).1
    linarith only [this, hL, hl2]
  have hL'pos : 0 < L' := by linarith only [hL'ge, hLpos]
  have hx1 : L' / L ≤ 1 := (div_le_one hLpos).2 hL'le
  have hx2 : 1 / 2 ≤ L' / L := by rw [le_div_iff₀ hLpos]; linarith only [hL'ge]
  have hs0 : 0 < opScale cStar ε := exitEst_opScale_pos hc hε (by linarith only [hε4])
  have hs'0 : 0 < opScale cStar (ε / ρ) := exitEst_opScale_pos hc (div_pos hε hρ0)
    (by rw [div_lt_one hρ0]; exact hερ)
  have hsq1 : Real.sqrt (L' / L) ≤ 1 := by
    rw [Real.sqrt_le_one]; exact hx1
  have hsq2 : 1 / 2 ≤ Real.sqrt (L' / L) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith only [hx2]
  have hsp : 0 < Real.sqrt (L' / L) := by linarith only [hsq2]
  have hinv : opScale cStar (ε / ρ) / opScale cStar ε =
      (Real.sqrt (L' / L))⁻¹ := by
    rw [← hrat, inv_div]
  rw [hinv]
  constructor
  · exact one_le_inv₀ hsp |>.2 hsq1
  · rw [inv_le_comm₀ hsp (by norm_num)]; linarith only [hsq2]

/-- Arithmetic of the error term. -/
theorem exitEst_num_err {C₀ α L L' lam lamT : ℝ} (hC₀ : 1 ≤ C₀) (hα : 0 < α) (hα1 : α ≤ 1)
    (hL : 0 < L) (hL' : L / 2 ≤ L') (hlam0 : 0 ≤ lam)
    (hlam : lam ≤ (1 / (64 * C₀)) * L ^ α) (hlamT : lamT ≤ 2 * lam) :
    lamT * (4 * (C₀ * L' ^ (-α))) ≤ 1 / 4 := by
  have hC0 : 0 < C₀ := by linarith only [hC₀]
  have hL'0 : 0 < L' := by linarith only [hL', hL]
  have h1 : L' ^ (-α) ≤ (L / 2) ^ (-α) :=
    Real.rpow_le_rpow_of_nonpos (by linarith only [hL]) hL' (by linarith only [hα])
  have h2 : (L / 2) ^ (-α) = L ^ (-α) * 2 ^ α := by
    rw [div_eq_mul_inv, Real.mul_rpow hL.le (by norm_num), Real.inv_rpow (by norm_num),
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_inv]
  have h3 : (2 : ℝ) ^ α ≤ 2 := by
    calc (2 : ℝ) ^ α ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hα1
      _ = 2 := Real.rpow_one 2
  have h4 : L' ^ (-α) ≤ 2 * L ^ (-α) := by
    have hp : 0 ≤ L ^ (-α) := Real.rpow_nonneg hL.le _
    calc L' ^ (-α) ≤ L ^ (-α) * 2 ^ α := h2 ▸ h1
      _ ≤ L ^ (-α) * 2 := mul_le_mul_of_nonneg_left h3 hp
      _ = 2 * L ^ (-α) := by ring
  have h5 : L ^ α * L ^ (-α) = 1 := by
    rw [← Real.rpow_add hL]; simp
  have h6 : lam * L ^ (-α) ≤ 1 / (64 * C₀) := by
    have hp : 0 ≤ L ^ (-α) := Real.rpow_nonneg hL.le _
    calc lam * L ^ (-α) ≤ (1 / (64 * C₀)) * L ^ α * L ^ (-α) :=
          mul_le_mul_of_nonneg_right hlam hp
      _ = 1 / (64 * C₀) := by rw [mul_assoc, h5, mul_one]
  have hp' : 0 ≤ L' ^ (-α) := Real.rpow_nonneg hL'0.le _
  calc lamT * (4 * (C₀ * L' ^ (-α))) ≤ (2 * lam) * (4 * (C₀ * (2 * L ^ (-α)))) := by
        refine mul_le_mul hlamT ?_ (mul_nonneg (by norm_num) (mul_nonneg hC0.le hp')) (by linarith only [hlam0])
        have := mul_le_mul_of_nonneg_left h4 hC0.le
        linarith only [this]
    _ = 16 * C₀ * (lam * L ^ (-α)) := by ring
    _ ≤ 16 * C₀ * (1 / (64 * C₀)) := mul_le_mul_of_nonneg_left h6 (by positivity)
    _ = 1 / 4 := by field_simp; norm_num

/-- Arithmetic of the exponential term. -/
theorem exitEst_num_exp (hd : 2 ≤ d) {lam lamT h δ : ℝ} (hlam : 0 < lam) (hlamT : lam / 4 ≤ lamT)
    (hδ : h ≤ δ) (hh : 0 < h)
    (hhlam : Real.sqrt (2 * d) * Real.log (8 * d) ≤ h * Real.sqrt lam) :
    2 * d * Real.exp (-(Real.sqrt (lamT / (1 / 2)) * (δ / Real.sqrt d))) ≤ 1 / 4 := by
  have hd0 : (0 : ℝ) < d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith only [this]
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 hd0
  have h1 : Real.sqrt (lam / 2) ≤ Real.sqrt (lamT / (1 / 2)) :=
    Real.sqrt_le_sqrt (by linarith only [hlamT])
  have h2 : h / Real.sqrt d ≤ δ / Real.sqrt d := div_le_div_of_nonneg_right hδ hsd.le
  have h3 : Real.sqrt (lam / 2) * (h / Real.sqrt d) ≤
      Real.sqrt (lamT / (1 / 2)) * (δ / Real.sqrt d) :=
    mul_le_mul h1 h2 (by positivity) (Real.sqrt_nonneg _)
  have h4 : Real.log (8 * d) ≤ Real.sqrt (lam / 2) * (h / Real.sqrt d) := by
    have e : Real.sqrt (lam / 2) * (h / Real.sqrt d) = (h * Real.sqrt lam) / Real.sqrt (2 * d) := by
      rw [Real.sqrt_div hlam.le, Real.sqrt_mul (by norm_num)]
      have : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
      field_simp
    rw [e, le_div_iff₀ (Real.sqrt_pos.2 (by positivity))]
    linarith only [hhlam]
  have h5 : Real.exp (-(Real.sqrt (lamT / (1 / 2)) * (δ / Real.sqrt d))) ≤ (8 * (d : ℝ))⁻¹ := by
    rw [← Real.exp_log (show (0 : ℝ) < 8 * d by positivity), ← Real.exp_neg]
    exact Real.exp_le_exp.2 (by linarith only [h3, h4])
  calc 2 * d * Real.exp (-(Real.sqrt (lamT / (1 / 2)) * (δ / Real.sqrt d))) ≤ 2 * (d : ℝ) * (8 * (d : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_left h5 (by positivity)
    _ = 1 / 4 := by field_simp; norm_num

/-- The one-ball estimate with the radius as a free variable. -/
theorem exitEst_one_ball_R [NeZero d] (hd : 2 ≤ d) {nu cStar : ℝ}
    (omega : ShellSeq d) {ε' lam' E R : ℝ}
    (hc : 0 < cStar) (hε' : 0 < ε') (hε'1 : ε' < 1) (hlam' : 0 < lam')
    (hA1 : ∀ lam : ℝ, 0 < lam → ∀ v vb : H1Function (euclideanBall (0 : Vec d) 1),
      IsDirichletSolution (fun x => opScale cStar ε' • epField nu omega ε' x)
        (euclideanBall (0 : Vec d) 1) (fun x => 1 - lam * v.toFun x) 0 v →
      IsDirichletSolution (fun _ => (1 / 2 : ℝ) • (1 : Mat d)) (euclideanBall (0 : Vec d) 1)
        (fun x => 1 - lam * vb.toFun x) 0 vb →
      ∀ᵐ x ∂(volume.restrict (euclideanBall (0 : Vec d) 1)), |v.toFun x - vb.toFun x| ≤ E)
    (hR : R = ε'⁻¹) {w : Vec d → ℝ} (u : H10Function (euclideanBall (0 : Vec d) R))
    (hw : Continuous w)
    (hwu : ∀ᵐ y ∂(volume.restrict (euclideanBall (0 : Vec d) R)), w y = u.toH1Function.toFun y)
    (hsol : IsScalarForcedWeakSolution (fullCoefficientRecentered nu omega)
      (euclideanBall (0 : Vec d) R) (fun y => 1 - lam' * u.toH1Function.toFun y) u.toH1Function)
    {δ : ℝ} (hδ : 0 < δ) (x : Vec d)
    (hx : ∀ y : Vec d, vecNormSq (y - ε' • x) < δ ^ 2 → y ∈ euclideanBall (0 : Vec d) 1) :
    1 - lam' * w x ≤
      2 * d * Real.exp (-(Real.sqrt (lam' * (opScale cStar ε' / ε' ^ 2) / (1 / 2)) *
        (δ / Real.sqrt d))) + lam' * (opScale cStar ε' / ε' ^ 2) * E := by
  subst hR
  exact exitEst_one_ball hd omega hc hε' hε'1 hlam' hA1 u hw hwu hsol hδ x hx

/-- For `ε ≤ 1/4` and `ρ ∈ [1/2, 1]`: `|log ε| / 2 ≤ |log (ε/ρ)|`. -/
theorem exitEst_log_ge {ε ρ : ℝ} (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) (hρ1 : 1 / 2 ≤ ρ) (hρ : ρ ≤ 1) :
    |Real.log ε| / 2 ≤ |Real.log (ε / ρ)| := by
  have hshift := ballResc_abs_log_shift hε (by linarith only [hε4]) hρ1 hρ
  have hL := exitEst_log_two_le hε hε4
  have := (abs_le.1 hshift).1
  linarith only [this, hL]

/-- **The one-step estimate at every radius.**  Under the resolvent estimate (in its exit-time
form, at the scales `ε' ∈ [ε, 2ε]`), for `lam ≤ (64 C₀)⁻¹ |log ε|^α` and `h ≥ C₁/√lam`, the
profile of the ball of radius `ρ/ε` is at most `1/2` on the ball of radius `(ρ - h)/ε`. -/
theorem exitEst_hone [NeZero d] (hd : 2 ≤ d) {nu cStar : ℝ} (hc : 0 < cStar) (omega : ShellSeq d)
    (D : FieldInputData d nu (fullStreamRecentered omega)) {C₀ α : ℝ} (hC₀ : 1 ≤ C₀)
    (hα : 0 < α) (hα1 : α ≤ 1) {ε lam h : ℝ} (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) (hlam : 0 < lam)
    (hlamL : lam ≤ (1 / (64 * C₀)) * |Real.log ε| ^ α) (hh : 0 < h) (hh8 : h ≤ 1 / 8)
    (hhlam : Real.sqrt (2 * d) * Real.log (8 * d) ≤ h * Real.sqrt lam)
    (hA1 : ∀ ε' : ℝ, 0 < ε' → ε' ≤ 1 / 2 → ε ≤ ε' → ε' ≤ 2 * ε →
      ∀ lam₂ : ℝ, 0 < lam₂ → ∀ v vb : H1Function (euclideanBall (0 : Vec d) 1),
      IsDirichletSolution (fun x => opScale cStar ε' • epField nu omega ε' x)
        (euclideanBall (0 : Vec d) 1) (fun x => 1 - lam₂ * v.toFun x) 0 v →
      IsDirichletSolution (fun _ => (1 / 2 : ℝ) • (1 : Mat d)) (euclideanBall (0 : Vec d) 1)
        (fun x => 1 - lam₂ * vb.toFun x) 0 vb →
      ∀ᵐ x ∂(volume.restrict (euclideanBall (0 : Vec d) 1)),
        |v.toFun x - vb.toFun x| ≤ 4 * (C₀ * |Real.log ε'| ^ (-α))) :
    ∀ ρ : ℝ, 1 / 2 ≤ ρ → ρ ≤ 1 →
      ∀ (w : Vec d → ℝ) (u : H10Function (euclideanBall (0 : Vec d) (ρ / ε))), Continuous w →
        (∀ y, y ∉ euclideanBall (0 : Vec d) (ρ / ε) → w y = 0) →
        (∀ᵐ y ∂volumeMeasureOn (euclideanBall (0 : Vec d) (ρ / ε)), w y = u.toH1Function.toFun y) →
        IsScalarForcedWeakSolution D.analyticData.a (euclideanBall (0 : Vec d) (ρ / ε))
          (fun y => 1 - (lam / timeScale cStar ε) * u.toH1Function.toFun y) u.toH1Function →
        ∀ y : Vec d, vecNormSq y ≤ ((ρ - h) / ε) ^ 2 →
          max (1 - (lam / timeScale cStar ε) * w y) 0 ≤ 1 / 2 := by
  intro ρ hρ1 hρ2 w u hw _hoff hwu hsol y hy
  have hρ0 : 0 < ρ := by linarith only [hρ1]
  have hε1 : ε < 1 := by linarith only [hε4]
  have hε'0 : 0 < ε / ρ := div_pos hε hρ0
  have hε'2 : ε / ρ ≤ 2 * ε := by
    rw [div_le_iff₀ hρ0]; nlinarith only [hρ1, hε]
  have hε'half : ε / ρ ≤ 1 / 2 := by linarith only [hε'2, hε4]
  have hε'1 : ε / ρ < 1 := by linarith only [hε'half]
  have hεε' : ε ≤ ε / ρ := by
    rw [le_div_iff₀ hρ0]; nlinarith only [hρ2, hε]
  have hτ : timeScale cStar ε = opScale cStar ε / ε ^ 2 := by
    rw [eq_div_iff (by positivity), mul_comm]; exact sq_mul_timeScale cStar ε hc hε
  have hsε : 0 < opScale cStar ε := exitEst_opScale_pos hc hε hε1
  have hτpos : 0 < timeScale cStar ε := by rw [hτ]; positivity
  have hlam'0 : 0 < lam / timeScale cStar ε := div_pos hlam hτpos
  obtain ⟨hr1, hr2⟩ := exitEst_opScale_ratio_bounds hc hε hε4 hρ1 hρ2
  have hs'0 : 0 < opScale cStar (ε / ρ) := exitEst_opScale_pos hc hε'0 hε'1
  have hlamT : lam / timeScale cStar ε * (opScale cStar (ε / ρ) / (ε / ρ) ^ 2) =
      lam * ρ ^ 2 * (opScale cStar (ε / ρ) / opScale cStar ε) := by
    rw [hτ]; field_simp
  have hlamT_lo : lam / 4 ≤ lam / timeScale cStar ε * (opScale cStar (ε / ρ) / (ε / ρ) ^ 2) := by
    rw [hlamT]
    have h1 : 1 / 4 ≤ ρ ^ 2 := by nlinarith only [hρ1]
    have h2 : lam * (1 / 4) * 1 ≤ lam * ρ ^ 2 * (opScale cStar (ε / ρ) / opScale cStar ε) :=
      mul_le_mul (mul_le_mul_of_nonneg_left h1 hlam.le) hr1 zero_le_one (by positivity)
    linarith only [h2]
  have hlamT_hi : lam / timeScale cStar ε * (opScale cStar (ε / ρ) / (ε / ρ) ^ 2) ≤ 2 * lam := by
    rw [hlamT]
    have h1 : ρ ^ 2 ≤ 1 := by nlinarith only [hρ2, hρ0]
    have h2 : lam * ρ ^ 2 * (opScale cStar (ε / ρ) / opScale cStar ε) ≤ lam * 1 * 2 :=
      mul_le_mul (mul_le_mul_of_nonneg_left h1 hlam.le) hr2 (by linarith only [hr1])
        (by positivity)
    linarith only [h2]
  have hδ : 0 < h / ρ := div_pos hh hρ0
  have hδ1 : h / ρ ≤ 1 := by rw [div_le_one hρ0]; linarith only [hh8, hρ1]
  have hz : vecNormSq ((ε / ρ) • y) ≤ (1 - h / ρ) ^ 2 := by
    rw [vecNormSq_smul]
    have e : (ε / ρ) ^ 2 * ((ρ - h) / ε) ^ 2 = (1 - h / ρ) ^ 2 := by field_simp
    rw [← e]
    exact mul_le_mul_of_nonneg_left hy (by positivity)
  have hone := exitEst_one_ball_R hd omega hc hε'0 hε'1 hlam'0
    (fun lam₂ h₂ v vb h1 h2 => hA1 (ε / ρ) hε'0 hε'half hεε' hε'2 lam₂ h₂ v vb h1 h2)
    (R := ρ / ε) (inv_div ε ρ).symm u hw hwu hsol hδ y
    (fun y' hy' => exitEst_ball_geom hδ hδ1 hz hy')
  have hexp := exitEst_num_exp hd (h := h) (δ := h / ρ) hlam hlamT_lo
    (by rw [le_div_iff₀ hρ0]; nlinarith only [hh, hρ2]) hh hhlam
  have hL : 0 < |Real.log ε| := by linarith only [exitEst_log_two_le hε hε4, Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have herr := exitEst_num_err hC₀ hα hα1 hL (exitEst_log_ge hε hε4 hρ1 hρ2) hlam.le hlamL hlamT_hi
  refine max_le ?_ (by norm_num)
  linarith only [hone, hexp, herr]

/-- In the two regimes where the iteration is not run, the exponent `min (t₀^{-1/2}) (L^{α/6})`
is bounded. -/
theorem exitEst_m_bound {t₀ L α c₂ lam0 : ℝ} (ht : 0 < t₀) (hL : 0 < L) (hα : 0 < α)
    (hα1 : α ≤ 1) (hc₂ : 0 < c₂)
    (hcase : L ≤ 2 * Real.log 2 ∨ min (1 / t₀) (c₂ * L ^ α) < lam0) :
    min (t₀ ^ (-(1 / 2 : ℝ))) (L ^ (α / 6)) ≤
      max 3 (max (Real.sqrt lam0) ((lam0 / c₂) ^ (1 / 6 : ℝ))) := by
  have hl2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith only [this]
  rcases hcase with h1 | h2
  · refine (min_le_right _ _).trans (le_trans ?_ (le_max_left _ _))
    have hmax : max 1 L ≤ 3 := max_le (by norm_num) (by linarith only [h1, hl2])
    calc L ^ (α / 6) ≤ (max 1 L) ^ (α / 6) :=
          Real.rpow_le_rpow hL.le (le_max_right _ _) (by positivity)
      _ ≤ (max 1 L) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (le_max_left _ _) (by linarith only [hα1])
      _ = max 1 L := Real.rpow_one _
      _ ≤ 3 := hmax
  · rcases min_lt_iff.1 h2 with h3 | h3
    · have hz : (t₀ ^ (-(1 / 2 : ℝ))) ^ 2 = 1 / t₀ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
        norm_num
        rw [Real.rpow_neg_one]
      have : t₀ ^ (-(1 / 2 : ℝ)) ≤ Real.sqrt lam0 := by
        apply Real.le_sqrt_of_sq_le
        rw [hz]; exact h3.le
      exact (min_le_left _ _).trans (this.trans ((le_max_left _ _).trans (le_max_right _ _)))
    · have h4 : L ^ α ≤ lam0 / c₂ := by
        rw [le_div_iff₀ hc₂, mul_comm]; exact h3.le
      have e : L ^ (α / 6) = (L ^ α) ^ (1 / 6 : ℝ) := by
        rw [← Real.rpow_mul hL.le]; congr 1; ring
      calc min (t₀ ^ (-(1 / 2 : ℝ))) (L ^ (α / 6)) ≤ L ^ (α / 6) := min_le_right _ _
        _ = (L ^ α) ^ (1 / 6 : ℝ) := e
        _ ≤ (lam0 / c₂) ^ (1 / 6 : ℝ) :=
          Real.rpow_le_rpow (Real.rpow_nonneg hL.le _) h4 (by norm_num)
        _ ≤ _ := (le_max_right _ _).trans (le_max_right _ _)

/-- The constant `√(2d) log (8d)` of the step length. -/
noncomputable def exitEst_C1 (d : ℕ) : ℝ := Real.sqrt (2 * d) * Real.log (8 * d)

/-- The smallest shift for which the step length is at most `1/8`. -/
noncomputable def exitEst_lam0 (d : ℕ) : ℝ := (8 * exitEst_C1 d) ^ 2

/-- The constant of the exponent of the exit-time estimate. -/
noncomputable def exitEst_c (C₀ α : ℝ) (d : ℕ) : ℝ :=
  min ((1 / (4 * exitEst_C1 d)) * Real.log 2 *
      (min 1 (Real.sqrt (1 / (64 * C₀))) * Real.log 2 ^ (α / 3)) / 3)
    (Real.log 2 / max 3 (max (Real.sqrt (exitEst_lam0 d))
      ((exitEst_lam0 d / (1 / (64 * C₀))) ^ (1 / 6 : ℝ))))

theorem exitEst_C1_pos (hd : 2 ≤ d) : 0 < exitEst_C1 d := by
  have hd0 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  unfold exitEst_C1
  have h1 : 0 < Real.sqrt (2 * (d : ℝ)) := Real.sqrt_pos.2 (by linarith only [hd0])
  have h2 : 0 < Real.log (8 * (d : ℝ)) :=
    Real.log_pos (by linarith only [hd0])
  positivity

theorem exitEst_c_pos (hd : 2 ≤ d) {C₀ α : ℝ} (hC₀ : 1 ≤ C₀) :
    0 < exitEst_c C₀ α d := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC1 := exitEst_C1_pos hd
  have hC0 : 0 < C₀ := by linarith only [hC₀]
  have hc₂ : 0 < 1 / (64 * C₀) := by positivity
  unfold exitEst_c
  refine lt_min ?_ ?_
  · have : 0 < min 1 (Real.sqrt (1 / (64 * C₀))) :=
      lt_min one_pos (Real.sqrt_pos.2 hc₂)
    positivity
  · refine div_pos hl2 (lt_of_lt_of_le (by norm_num) (le_max_left _ _))

/-- **The exit-time estimate for a fixed sample.**  Let `ζ` be the minimal scale of the resolvent
estimate; for every `ε` with `2 ζ ≤ ε⁻¹`, every continuous-path law `Q` of the kernel semigroup, and
every start in the half ball, the probability of leaving the ball of radius `ε⁻¹` before `τ_ε t₀` is at
most `2 exp (-c min (t₀^{-1/2}) (|log ε|^{α/6}))`. -/
theorem exitEst_main_det [NeZero d] (hd : 2 ≤ d) {nu cStar : ℝ} (hc : 0 < cStar)
    (omega : ShellSeq d) (D : FieldInputData d nu (fullStreamRecentered omega)) {C₀ α : ℝ}
    (hC₀ : 1 ≤ C₀) (hα : 0 < α) (hα1 : α ≤ 1) {ζ : ℝ}
    (hA1 : ∀ ε' : ℝ, 0 < ε' → ε' ≤ 1 / 2 → ζ ≤ ε'⁻¹ →
      ∀ lam₂ : ℝ, 0 < lam₂ → ∀ v vb : H1Function (euclideanBall (0 : Vec d) 1),
      IsDirichletSolution (fun x => opScale cStar ε' • epField nu omega ε' x)
        (euclideanBall (0 : Vec d) 1) (fun x => 1 - lam₂ * v.toFun x) 0 v →
      IsDirichletSolution (fun _ => (1 / 2 : ℝ) • (1 : Mat d)) (euclideanBall (0 : Vec d) 1)
        (fun x => 1 - lam₂ * vb.toFun x) 0 vb →
      ∀ᵐ x ∂(volume.restrict (euclideanBall (0 : Vec d) 1)),
        |v.toFun x - vb.toFun x| ≤ 4 * (C₀ * |Real.log ε'| ^ (-α)))
    {Q : Vec d → Measure (ContinuousPath (Vec d))}
    (hQ : IsContinuousPathLaw D.logGrowthBounds.resolvent.kernelSemigroup Q)
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hζ : 2 * ζ ≤ ε⁻¹) {t₀ : ℝ} (ht0 : 0 < t₀)
    {x : Vec d} (hx : vecNormSq x < (1 / 2) ^ 2) :
    Q (ε⁻¹ • x)
        {w | ContinuousPath.exitTime {y : Vec d | vecNormSq (ε • y) < 1} w ≤
          ENNReal.ofReal (timeScale cStar ε * t₀)} ≤
      2 * ENNReal.ofReal (Real.exp (-(exitEst_c C₀ α d *
        min (t₀ ^ (-(1 / 2 : ℝ))) (|Real.log ε| ^ (α / 6))))) := by
  have hε1 : ε < 1 := by linarith only [hε2]
  have hLpos : 0 < |Real.log ε| := abs_pos.2 (Real.log_neg hε hε1).ne
  have hprob : IsProbabilityMeasure (Q (ε⁻¹ • x)) := (hQ _).1
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC1 := exitEst_C1_pos hd
  have hcpos := exitEst_c_pos hd hC₀ (α := α)
  have hC0 : 0 < C₀ := by linarith only [hC₀]
  have hc₂ : 0 < 1 / (64 * C₀) := by positivity
  set c := exitEst_c C₀ α d with hcdef
  set L := |Real.log ε| with hLdef
  set m := min (t₀ ^ (-(1 / 2 : ℝ))) (L ^ (α / 6)) with hm
  have hm0 : 0 ≤ m := le_min (Real.rpow_nonneg ht0.le _) (Real.rpow_nonneg hLpos.le _)
  set lam := min (1 / t₀) ((1 / (64 * C₀)) * L ^ α) with hlamdef
  set S : Set (ContinuousPath (Vec d)) := {w | ContinuousPath.exitTime
    {y : Vec d | vecNormSq (ε • y) < 1} w ≤ ENNReal.ofReal (timeScale cStar ε * t₀)} with hS
  suffices hreal : (Q (ε⁻¹ • x) S).toReal ≤ 2 * Real.exp (-(c * m)) by
    calc Q (ε⁻¹ • x) S = ENNReal.ofReal ((Q (ε⁻¹ • x) S).toReal) :=
          (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal (2 * Real.exp (-(c * m))) := ENNReal.ofReal_le_ofReal hreal
      _ = 2 * ENNReal.ofReal (Real.exp (-(c * m))) := by
          rw [ENNReal.ofReal_mul (by norm_num)]; simp
  have hp1 : (Q (ε⁻¹ • x) S).toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := Q (ε⁻¹ • x)) (s := S))
    simpa using this
  by_cases hreg : ε ≤ 1 / 4 ∧ exitEst_lam0 d ≤ lam
  · obtain ⟨hε4, hlam0⟩ := hreg
    have hL2 : 2 * Real.log 2 ≤ L := exitEst_log_two_le hε hε4
    have hlam0pos : 0 < exitEst_lam0 d := by unfold exitEst_lam0; positivity
    have hlampos : 0 < lam := lt_of_lt_of_le hlam0pos hlam0
    have hsl : 8 * exitEst_C1 d ≤ Real.sqrt lam := by
      have : Real.sqrt (exitEst_lam0 d) = 8 * exitEst_C1 d := by
        unfold exitEst_lam0; exact Real.sqrt_sq (by positivity)
      rw [← this]; exact Real.sqrt_le_sqrt hlam0
    have hslpos : 0 < Real.sqrt lam := Real.sqrt_pos.2 hlampos
    set h := exitEst_C1 d / Real.sqrt lam with hhdef
    have hh : 0 < h := div_pos hC1 hslpos
    have hh8 : h ≤ 1 / 8 := by
      rw [hhdef, div_le_iff₀ hslpos]; linarith only [hsl]
    have hhlam : Real.sqrt (2 * d) * Real.log (8 * d) ≤ h * Real.sqrt lam := by
      have : h * Real.sqrt lam = exitEst_C1 d := by rw [hhdef]; field_simp
      rw [this]; exact le_rfl
    have hτ : 0 < timeScale cStar ε := by
      have h1 := sq_mul_timeScale cStar ε hc hε
      have h2 : 0 < opScale cStar ε := exitEst_opScale_pos hc hε hε1
      rw [← h1] at h2
      exact pos_of_mul_pos_right h2 (by positivity)
    have hlam'0 : 0 < lam / timeScale cStar ε := div_pos hlampos hτ
    have hlamL : lam ≤ (1 / (64 * C₀)) * L ^ α := min_le_right _ _
    have hA1' : ∀ ε' : ℝ, 0 < ε' → ε' ≤ 1 / 2 → ε ≤ ε' → ε' ≤ 2 * ε →
        ∀ lam₂ : ℝ, 0 < lam₂ → ∀ v vb : H1Function (euclideanBall (0 : Vec d) 1),
        IsDirichletSolution (fun x => opScale cStar ε' • epField nu omega ε' x)
          (euclideanBall (0 : Vec d) 1) (fun x => 1 - lam₂ * v.toFun x) 0 v →
        IsDirichletSolution (fun _ => (1 / 2 : ℝ) • (1 : Mat d)) (euclideanBall (0 : Vec d) 1)
          (fun x => 1 - lam₂ * vb.toFun x) 0 vb →
        ∀ᵐ x ∂(volume.restrict (euclideanBall (0 : Vec d) 1)),
          |v.toFun x - vb.toFun x| ≤ 4 * (C₀ * |Real.log ε'| ^ (-α)) := by
      intro ε' hε'0 hε'half _ hε'2
      refine hA1 ε' hε'0 hε'half ?_
      have h1 : (2 * ε)⁻¹ ≤ ε'⁻¹ := inv_anti₀ hε'0 hε'2
      have h2 : (2 * ε)⁻¹ = ε⁻¹ / 2 := by field_simp
      linarith only [h1, h2, hζ]
    have hone := exitEst_hone hd hc omega D hC₀ hα hα1 hε hε4 hlampos hlamL hh hh8 hhlam hA1'
    obtain ⟨w₁, u₁, hw₁, hoff₁, hwu₁, hsol₁⟩ :=
      ballBdry_data D (0 : Vec d) (r := 1 / ε) (one_div_pos.2 hε) hlam'0
    obtain ⟨N, hN, hbound⟩ := exitEst_iterate D hε hlam'0 hh hh8 (q := 1 / 2) (by norm_num)
      le_rfl hone u₁ hw₁ hoff₁ hwu₁ hsol₁
    have hxy : vecNormSq (ε⁻¹ • x) < ((1 / 2) / ε) ^ 2 := by
      rw [vecNormSq_smul]
      have e : ((1 / 2) / ε) ^ 2 = ε⁻¹ ^ 2 * (1 / 2) ^ 2 := by field_simp
      rw [e]
      exact mul_lt_mul_of_pos_left hx (by positivity)
    have hmem : ε⁻¹ • x ∈ euclideanBall (0 : Vec d) (1 / ε) := by
      rw [exitEst_mem_ball]
      refine lt_of_lt_of_le hxy ?_
      have : (1 / 2) / ε ≤ 1 / ε := by gcongr; norm_num
      exact pow_le_pow_left₀ (by positivity) this 2
    have hV₁ := SuperdiffusionCLT.Section8.Common.Regularity.Ported.isOpenBoundedConvexDomain_euclideanBall
      (0 : Vec d) (one_div_pos.2 hε)
    have hs0 : 0 ≤ timeScale cStar ε * t₀ := by positivity
    have hch := ballExit_exitTime_le_convex D hV₁ hlam'0 u₁ hw₁ hoff₁ hwu₁ hsol₁ hQ hmem hs0
    have hset : {y : Vec d | vecNormSq (ε • y) < 1} = euclideanBall (0 : Vec d) (1 / ε) := by
      rw [ballExit_anchorSet_eq hε, one_div]
    have hS' : S = {path | ContinuousPath.exitTime (euclideanBall (0 : Vec d) (1 / ε)) path ≤
        ENNReal.ofReal (timeScale cStar ε * t₀)} := by
      rw [hS, hset]
    rw [hS'] at hp1 ⊢
    have hf := hbound _ hxy.le
    have hk : Q (ε⁻¹ • x) {path | ContinuousPath.exitTime (euclideanBall (0 : Vec d) (1 / ε)) path ≤
        ENNReal.ofReal (timeScale cStar ε * t₀)} ≤
        ENNReal.ofReal (Real.exp (lam / timeScale cStar ε * (timeScale cStar ε * t₀)) *
          Real.exp (-(N * Real.log 2))) := by
      calc _ ≤ _ := hch
        _ ≤ ENNReal.ofReal (Real.exp (lam / timeScale cStar ε * (timeScale cStar ε * t₀))) *
            ENNReal.ofReal (Real.exp (-(N * Real.log 2))) :=
          mul_le_mul_right (ENNReal.ofReal_le_ofReal ((le_max_left _ _).trans hf)) _
        _ = _ := (ENNReal.ofReal_mul (Real.exp_pos _).le).symm
    have hP := (ENNReal.toReal_mono ENNReal.ofReal_ne_top hk).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
    have hlt : lam / timeScale cStar ε * (timeScale cStar ε * t₀) = lam * t₀ := by
      field_simp
    rw [hlt] at hP
    have hN' : 1 / (4 * exitEst_C1 d) * Real.sqrt lam - 1 ≤ N := by
      have := ballResc_inv_four_h hC1 hlampos
      rw [← this]; exact hN
    have hmain := ballResc_exit_arith (N := N) ht0 (by linarith only [hL2, hl2]) hα hc₂
      (one_div_pos.2 (by positivity : 0 < 4 * exitEst_C1 d)) hp1 hN' hP
    refine hmain.trans ?_
    have hcc : c ≤ 1 / (4 * exitEst_C1 d) * Real.log 2 *
        (min 1 (Real.sqrt (1 / (64 * C₀))) * Real.log 2 ^ (α / 3)) / 3 := min_le_left _ _
    have : Real.exp (-(1 / (4 * exitEst_C1 d) * Real.log 2 *
        (min 1 (Real.sqrt (1 / (64 * C₀))) * Real.log 2 ^ (α / 3)) / 3 * m)) ≤
        Real.exp (-(c * m)) := Real.exp_le_exp.2 (by nlinarith only [hcc, hm0])
    linarith only [this]
  · -- the regime in which the iteration is not run: the right side is at least one
    have hcase : L ≤ 2 * Real.log 2 ∨ lam < exitEst_lam0 d := by
      by_cases h4 : ε ≤ 1 / 4
      · right
        by_contra hnot
        exact hreg ⟨h4, not_lt.1 hnot⟩
      · left
        push Not at h4
        have h5 : Real.log (1 / 4) ≤ Real.log ε := Real.log_le_log (by norm_num) h4.le
        have h6 : Real.log (1 / 4) = -(2 * Real.log 2) := by
          rw [one_div, Real.log_inv, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
          push_cast; ring
        have h7 : Real.log ε ≤ 0 := (Real.log_neg hε hε1).le
        rw [hLdef, abs_of_nonpos h7]
        linarith only [h5, h6]
    have hm_le := exitEst_m_bound ht0 hLpos hα hα1 hc₂ hcase
    have hc_le : c ≤ Real.log 2 / max 3 (max (Real.sqrt (exitEst_lam0 d))
        ((exitEst_lam0 d / (1 / (64 * C₀))) ^ (1 / 6 : ℝ))) := min_le_right _ _
    have hM0 : 0 < max 3 (max (Real.sqrt (exitEst_lam0 d))
        ((exitEst_lam0 d / (1 / (64 * C₀))) ^ (1 / 6 : ℝ))) :=
      lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    have hcm : c * m ≤ Real.log 2 := by
      calc c * m ≤ (Real.log 2 / max 3 (max (Real.sqrt (exitEst_lam0 d))
          ((exitEst_lam0 d / (1 / (64 * C₀))) ^ (1 / 6 : ℝ)))) * max 3 (max (Real.sqrt (exitEst_lam0 d))
          ((exitEst_lam0 d / (1 / (64 * C₀))) ^ (1 / 6 : ℝ))) :=
            mul_le_mul hc_le hm_le hm0 (by positivity)
        _ = Real.log 2 := by field_simp
    have hexp : 1 / 2 ≤ Real.exp (-(c * m)) := by
      have : Real.exp (-Real.log 2) ≤ Real.exp (-(c * m)) := Real.exp_le_exp.2 (by linarith only [hcm])
      rwa [Real.exp_neg, Real.exp_log (by norm_num), ← one_div] at this
    linarith only [hp1, hexp]

/-- Doubling the minimal scale keeps a stretched-logarithmic tail, with a larger constant. -/
theorem exitEst_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Z₀ : Ω → ℝ} {C₀ β : ℝ} (hC₀ : 1 ≤ C₀) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hZt : ∀ ξ : ℝ, 1 ≤ ξ →
      μ {omega | ξ ≤ Z₀ omega} ≤ ENNReal.ofReal (C₀ * Real.exp (-(C₀⁻¹ * Real.log ξ ^ β)))) :
    ∀ ξ : ℝ, 1 ≤ ξ → μ {omega | ξ ≤ 2 * Z₀ omega} ≤
      ENNReal.ofReal ((C₀ * Real.exp (Real.log 2 ^ β)) *
        Real.exp (-((C₀ * Real.exp (Real.log 2 ^ β))⁻¹ * Real.log ξ ^ β))) := by
  intro ξ hξ
  have hC0 : 0 < C₀ := by linarith only [hC₀]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hE : 1 ≤ Real.exp (Real.log 2 ^ β) := Real.one_le_exp (by positivity)
  set Ct := C₀ * Real.exp (Real.log 2 ^ β) with hCt
  have hCt1 : C₀ ≤ Ct := le_mul_of_one_le_right hC0.le hE
  have hCtpos : 0 < Ct := lt_of_lt_of_le hC0 hCt1
  have hinv : Ct⁻¹ ≤ C₀⁻¹ := inv_anti₀ hC0 hCt1
  have hinv1 : Ct⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith only [hC₀, hCt1])
  have hlogξ : 0 ≤ Real.log ξ := Real.log_nonneg hξ
  by_cases h2 : 2 ≤ ξ
  · have hset : {omega | ξ ≤ 2 * Z₀ omega} = {omega | ξ / 2 ≤ Z₀ omega} := by
      ext omega; simp only [Set.mem_ofPred_eq]; constructor <;> intro h <;> linarith only [h]
    rw [hset]
    refine (hZt (ξ / 2) (by linarith only [h2])).trans (ENNReal.ofReal_le_ofReal ?_)
    have ha : Real.log (ξ / 2) = Real.log ξ - Real.log 2 := Real.log_div (by linarith only [h2]) (by norm_num)
    have ha0 : 0 ≤ Real.log (ξ / 2) := Real.log_nonneg (by linarith only [h2])
    have hsub : Real.log ξ ^ β ≤ Real.log (ξ / 2) ^ β + Real.log 2 ^ β := by
      have := Real.rpow_add_le_add_rpow ha0 hl2.le hβ.le hβ1
      have e : Real.log (ξ / 2) + Real.log 2 = Real.log ξ := by rw [ha]; ring
      rwa [e] at this
    have hb0 : 0 ≤ Real.log ξ ^ β := Real.rpow_nonneg hlogξ _
    have h3 : -(C₀⁻¹ * Real.log (ξ / 2) ^ β) ≤ Real.log 2 ^ β + -(Ct⁻¹ * Real.log ξ ^ β) := by
      have e1 : C₀⁻¹ * Real.log ξ ^ β ≤ C₀⁻¹ * (Real.log (ξ / 2) ^ β + Real.log 2 ^ β) :=
        mul_le_mul_of_nonneg_left hsub (by positivity)
      have e2 : Ct⁻¹ * Real.log ξ ^ β ≤ C₀⁻¹ * Real.log ξ ^ β :=
        mul_le_mul_of_nonneg_right hinv hb0
      have e3 : C₀⁻¹ * Real.log 2 ^ β ≤ Real.log 2 ^ β := by
        have : C₀⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hC₀
        nlinarith only [this, Real.rpow_nonneg hl2.le β]
      nlinarith only [e1, e2, e3]
    calc C₀ * Real.exp (-(C₀⁻¹ * Real.log (ξ / 2) ^ β))
        ≤ C₀ * Real.exp (Real.log 2 ^ β + -(Ct⁻¹ * Real.log ξ ^ β)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h3) hC0.le
      _ = Ct * Real.exp (-(Ct⁻¹ * Real.log ξ ^ β)) := by
          rw [Real.exp_add, hCt]; ring
  · push Not at h2
    refine (prob_le_one).trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have hlt : Real.log ξ ≤ Real.log 2 := Real.log_le_log (by linarith only [hξ]) h2.le
    have hb : Real.log ξ ^ β ≤ Real.log 2 ^ β := Real.rpow_le_rpow hlogξ hlt hβ.le
    have h4 : -(Real.log 2 ^ β) ≤ -(Ct⁻¹ * Real.log ξ ^ β) := by
      have : Ct⁻¹ * Real.log ξ ^ β ≤ Real.log ξ ^ β := by
        nlinarith only [hinv1, Real.rpow_nonneg hlogξ β]
      linarith only [this, hb]
    calc (1 : ℝ) ≤ C₀ := hC₀
      _ = Ct * Real.exp (-(Real.log 2 ^ β)) := by
          rw [hCt, mul_assoc, ← Real.exp_add]; simp
      _ ≤ Ct * Real.exp (-(Ct⁻¹ * Real.log ξ ^ β)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h4) hCtpos.le

/-- Witness for `exitEst_tail`: the Dirac measure at `0` with `Z₀ = 0`, `C₀ = 1`, `β = 1/2`. -/
example : ∀ ξ : ℝ, 1 ≤ ξ → (Measure.dirac (0 : ℝ)) {omega | ξ ≤ 2 * (fun _ : ℝ => (0 : ℝ)) omega} ≤
    ENNReal.ofReal ((1 * Real.exp (Real.log 2 ^ (1 / 2 : ℝ))) *
      Real.exp (-((1 * Real.exp (Real.log 2 ^ (1 / 2 : ℝ)))⁻¹ * Real.log ξ ^ (1 / 2 : ℝ)))) :=
  exitEst_tail (Measure.dirac (0 : ℝ)) (Z₀ := fun _ : ℝ => (0 : ℝ)) (C₀ := 1) (β := 1 / 2) le_rfl
    (by norm_num) (by norm_num) (fun ξ hξ => by
      have : {omega : ℝ | ξ ≤ (fun _ : ℝ => (0 : ℝ)) omega} = ∅ := by
        ext omega
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
        linarith only [hξ]
      rw [this]
      simp)

/-- **Lemma `l.exit.time.estimate`**, from the
root theorem `t.superdiffusivity`, taken as the explicit hypothesis `hRoot` (the statement of
`SuperdiffusionCLT.Frozen.Section7.superdiffusivity`).  The conclusion is the statement of
`SuperdiffusionCLT.Frozen.Section8.exit_time_estimate`; the proof is the elliptic route: the
Chernoff bound for early exit, the Laplace transform of the exit time from concentric balls, the
resolvent estimate on the balls rescaled to the unit ball, and an iteration over concentric balls. -/
theorem exitEst_exit_time_estimate
    (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hRoot : ∀ (d : ℕ) [NeZero d], 2 ≤ d →
      ∀ α β : ℝ, 0 < α → α ≤ 1 → 0 < β → β ≤ 1 → β + 2 * α < 1 →
        ∀ U : Set (Homogenization.Vec d),
          SuperdiffusionCLT.Section7.IsSmoothBoundedDomain U →
          ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
            ∀ cStar : ℝ, 0 < cStar →
              ∀ K : ℝ,
                ∃ C : ℝ, 1 ≤ C ∧
                  ∀ (P : MeasureTheory.ProbabilityMeasure
                        (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
                    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
                    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
                    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K
                        hPrefix hJ2 hJ3 →
                    ∃ Z : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                      Measurable Z ∧
                      -- e.Z.integrability
                      (∀ ξ : ℝ, 1 ≤ ξ →
                        P.toMeasure {omega | ξ ≤ Z omega} ≤
                          ENNReal.ofReal (C * Real.exp (-(C⁻¹ * Real.log ξ ^ β)))) ∧
                      ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
                        ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → Z omega ≤ ε⁻¹ →
                          ∀ (f : Homogenization.Vec d → ℝ) (g u uhom : Homogenization.H1Function U),
                            -- e.BVPs
                            SuperdiffusionCLT.Section7.IsDirichletSolution
                                (fun x => ((2 * cStar * |Real.log ε|) ^ ((1 : ℝ) / 2))⁻¹ •
                                  SuperdiffusionCLT.Section7.epField nu omega ε x)
                                U f g u →
                            SuperdiffusionCLT.Section7.IsDirichletSolution
                                (fun _ => (1 : Homogenization.Mat d)) U f g uhom →
                            -- e.homogenization.error
                            MeasureTheory.eLpNorm (fun x => u.toFun x - uhom.toFun x) ⊤
                                  (MeasureTheory.volume.restrict U) +
                                SuperdiffusionCLT.Section7.hMinusOneVec U
                                  (fun x => u.grad x - uhom.grad x) +
                                SuperdiffusionCLT.Section7.hMinusOneVec U
                                  (fun x =>
                                    Homogenization.matVecMul
                                        (((2 * cStar * |Real.log ε|) ^ ((1 : ℝ) / 2))⁻¹ •
                                          SuperdiffusionCLT.Section7.epFieldCentered
                                            nu omega ε U x)
                                        (u.grad x) -
                                      uhom.grad x) ≤
                              ENNReal.ofReal (C * |Real.log ε| ^ (-α)) *
                                (MeasureTheory.eLpNorm
                                    (fun x => SuperdiffusionCLT.Section7.eucNorm (g.grad x)) ⊤
                                    (MeasureTheory.volume.restrict U) +
                                  MeasureTheory.eLpNorm f ⊤ (MeasureTheory.volume.restrict U))) :
    ∀ α β : ℝ, 0 < α → α < 1 → 0 < β → β < 1 → β + 2 * α < 1 →
      ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
        ∀ cStar : ℝ, 0 < cStar →
          ∀ K : ℝ,
            ∃ C c : ℝ, 1 ≤ C ∧ 0 < c ∧
              ∀ (P : MeasureTheory.ProbabilityMeasure
                    (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
                (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
                (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
                (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K
                    hPrefix hJ2 hJ3 →
                ∃ Z : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                  Measurable Z ∧
                  (∀ ξ : ℝ, 1 ≤ ξ →
                    P.toMeasure {omega | ξ ≤ Z omega} ≤
                      ENNReal.ofReal (C * Real.exp (-(C⁻¹ * Real.log ξ ^ β)))) ∧
                  ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
                    ∀ (S : MarkovProcess.SubMarkovKernelSemigroup (Homogenization.Vec d))
                      (Q : Homogenization.Vec d →
                        MeasureTheory.Measure (MarkovProcess.ContinuousPath (Homogenization.Vec d))),
                      SuperdiffusionCLT.Section8.IsDivergenceFormFeller
                          (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega) S →
                      SuperdiffusionCLT.Section8.IsContinuousPathLaw S Q →
                      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → Z omega ≤ ε⁻¹ →
                        ∀ t₀ : ℝ, 0 < t₀ → t₀ ≤ 1 →
                          ∀ x : Homogenization.Vec d, Homogenization.vecNormSq x < (1 / 2) ^ 2 →
                            Q (ε⁻¹ • x)
                                {w | MarkovProcess.ContinuousPath.exitTime
                                    {y : Homogenization.Vec d | Homogenization.vecNormSq (ε • y) < 1} w ≤
                                  ENNReal.ofReal
                                    (SuperdiffusionCLT.Section8.timeScale cStar ε * t₀)} ≤
                              2 * ENNReal.ofReal
                                (Real.exp (-(c * min (t₀ ^ (-(1 / 2 : ℝ)))
                                  (|Real.log ε| ^ (α / 6)))))
    := by
  intro α β hα hα1 hβ hβ1 hαβ nu hnu hnu1 cStar hc K
  have hU : SuperdiffusionCLT.Section7.IsSmoothBoundedDomain (euclideanBall (0 : Vec d) 1) := by
    have h := SuperdiffusionCLT.Section7.isSmoothBoundedDomain_euclidBall (d := d)
    have e : SuperdiffusionCLT.Section6.euclidBall (d := d) 1 = euclideanBall (0 : Vec d) 1 := by
      ext y
      simp [SuperdiffusionCLT.Section6.euclidBall, euclideanBall, euclideanSqDist]
    rwa [e] at h
  obtain ⟨C₀, hC₀, H⟩ := resEst_resolvent_estimate d hd hRoot α β hα hα1.le hβ hβ1.le hαβ
    (euclideanBall (0 : Vec d) 1) hU nu hnu hnu1 cStar hc K
  refine ⟨C₀ * Real.exp (Real.log 2 ^ β), exitEst_c C₀ α d,
    one_le_mul_of_one_le_of_one_le hC₀ (Real.one_le_exp (by positivity)),
    exitEst_c_pos hd hC₀, ?_⟩
  intro P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨Z₀, hZm, hZt, hZae⟩ := H P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  refine ⟨fun omega => 2 * Z₀ omega, measurable_const.mul hZm, ?_, ?_⟩
  · exact exitEst_tail P.toMeasure hC₀ hβ hβ1.le hZt
  · filter_upwards [hZae, fieldInput_ae_data hPrefix hJ3 hnu, thmA_link_data (nu := nu) hJ3]
      with omega hZ hD hL
    obtain ⟨D⟩ := hD
    intro S Q hS hQ ε hε hε2 hZε t₀ ht0 _ht1 x hx
    have hSD := (hL D).2.2 S hS
    subst hSD
    exact exitEst_main_det hd hc omega D hC₀ hα hα1.le (ζ := Z₀ omega)
      (fun ε' h0 h1 h2 lam₂ h₂ v vb hv hvb => ((hZ ε' h0 h1 h2 lam₂ h₂.le).2 h₂ v vb hv hvb).2)
      hQ hε hε2 hZε ht0 hx

end SuperdiffusionCLT.Section8
