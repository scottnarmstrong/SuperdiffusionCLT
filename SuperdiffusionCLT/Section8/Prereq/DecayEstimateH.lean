/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.DecayEstimateG

@[expose] public section

namespace SuperdiffusionCLT.Section8

noncomputable section

/-!
# The `L²` bound on an annulus with the Hölder and Poincaré coefficients

`decayEst_dual_ball` with the coefficients of `large_scale_holder` and of the superdiffusive
Poincaré inequality inserted.
-/

section

open Homogenization MeasureTheory SuperdiffusionCLT.Section6 SuperdiffusionCLT.Section7
open scoped Pointwise ENNReal

variable {d : ℕ}

/-- **`L²` oscillation bound on the annulus `{aa < |x| < bb}`.** -/
theorem decayEst_l2_ann [NeZero d] (a : CoeffField d) {ν cs γ CH CP Y Lg : ℝ} (hν : 0 < ν)
    (hcs : 0 < cs) (hCH : 0 ≤ CH) (hCP : 0 ≤ CP) (hY : 1 ≤ Y) (hLg1 : 1 ≤ Lg)
    (hsym : ∀ x, symmPart (a x) = ν • (1 : Mat d))
    {Rm ρ aa bb : ℝ} (hρY : Y ≤ ρ) (hρa : 2 * ρ ≤ aa) (hab : aa ≤ bb) (hbR : bb ≤ Rm)
    (hLga : Lg ≤ Real.log aa)
    (hexist : ∀ g : Vec d → ℝ, MemLp g 2 (volume.restrict (euclidBall (d := d) Rm)) →
      ∃ v : H10Function (euclidBall (d := d) Rm),
        IsWeakSolutionOn (fun x => matTranspose (a x)) (euclidBall Rm) v.toH1Function g
          (fun _ => 0))
    (hHolR : ∀ R' : ℝ, Y ≤ R' → ∀ (f : Vec d → ℝ) (w : H1Function (euclidBall (d := d) R')),
      IsWeakSolutionOn (fun x => matTranspose (a x)) (euclidBall R') w f (fun _ => 0) →
      ∀ r' : ℝ, Y ≤ r' → r' ≤ R' / 2 →
        eLpNorm (fun x => w.toFun x - ∫ y, w.toFun y ∂ballMeasure (d := d) r') ⊤
            (volume.restrict (euclidBall r')) ≤
          ENNReal.ofReal (CH * (r' / R') ^ γ) *
            (ballL2 R' (fun x => w.toFun x - ∫ y, w.toFun y ∂ballMeasure (d := d) R') +
              ENNReal.ofReal (Real.log R' ^ (-(1 / 2 : ℝ)) * R' ^ 2) *
                eLpNorm f ⊤ (volume.restrict (euclidBall (d := d) R'))))
    (hPoR : ∀ R' : ℝ, Y ≤ R' → ∀ (f : Vec d → ℝ) (w : H1Function (euclidBall (d := d) R')),
      IsWeakSolutionOn (fun x => matTranspose (a x)) (euclidBall R') w f (fun _ => 0) →
      lpBar (euclidBall (d := d) R') 2 (fun x => w.toFun x - ⨍ z in euclidBall R', w.toFun z) ≤
        ENNReal.ofReal (CP * R' * cs ^ (-(1 / 4 : ℝ)) * Real.sqrt ν *
            Real.log R' ^ (-(1 / 4 : ℝ))) *
          lpBar (euclidBall R') 2 (fun x => eucNorm (w.grad x)) +
        ENNReal.ofReal (CP * R' ^ 2 * ν⁻¹ * Real.log R' ^ (-(100 : ℝ))) *
          lpBar (euclidBall R') 2 f)
    (u : H10Function (euclidBall (d := d) Rm)) (h : Vec d → ℝ)
    (hu : IsWeakSolutionOn a (euclidBall Rm) u.toH1Function h (fun _ => 0))
    (hsupp : ∀ x, x ∉ euclidBall (d := d) ρ → h x = 0)
    (hmean : ∫ x in euclidBall (d := d) ρ, h x = 0)
    (hh : MemLp h 2 (volume.restrict (euclidBall (d := d) ρ))) :
    Real.sqrt (∫ x in decayEst_ann (d := d) aa bb,
        (u.toH1Function.toFun x - h1_avg (decayEst_ann aa bb) u.toH1Function.toFun) ^ 2) ≤
      ((CH * CP * (CP * cs ^ (-(1 / 4 : ℝ)) * Real.sqrt ν / ν + Real.sqrt CP / ν) *
          cs ^ (-(1 / 4 : ℝ)) * Real.sqrt ν) *
        (ρ / aa) ^ (γ + (d : ℝ) / 2) * (aa * bb) * Lg ^ (-(1 / 2 : ℝ))) *
        Real.sqrt (∫ x in euclidBall (d := d) ρ, h x ^ 2) := by
  have hρ : 0 < ρ := lt_of_lt_of_le (by linarith only [hY]) hρY
  have haa : 0 < aa := by linarith only [hρ, hρa]
  have hbb : 0 < bb := lt_of_lt_of_le haa hab
  have hρa' : ρ ≤ aa := by linarith only [hρ, hρa]
  have hLa1 : 1 ≤ Real.log aa := hLg1.trans hLga
  have hLb1 : 1 ≤ Real.log bb := hLa1.trans (Real.log_le_log haa hab)
  have hlogb : 0 ≤ Real.log bb := by linarith only [hLb1]
  have hloga : 0 ≤ Real.log aa := by linarith only [hLa1]
  refine le_trans (decayEst_dual_ball a hν hsym hρ hρa' hab hbR (decayEst_ann aa bb)
    (decayEst_ann_measurable aa bb) (decayEst_ann_subset aa bb)
    (fun x hx hxb => decayEst_ann_disjoint hxb hx) u h hu hsupp hmean hh hexist
    (Cc := CH * (ρ / aa) ^ γ) (κ := Real.log aa ^ (-(1 / 2 : ℝ)) * aa ^ 2)
    (α₁ := CP * aa * cs ^ (-(1 / 4 : ℝ)) * Real.sqrt ν * Real.log aa ^ (-(1 / 4 : ℝ)))
    (β₁ := CP * aa ^ 2 * ν⁻¹ * Real.log aa ^ (-(100 : ℝ)))
    (α₂ := CP * bb * cs ^ (-(1 / 4 : ℝ)) * Real.sqrt ν * Real.log bb ^ (-(1 / 4 : ℝ)))
    (β₂ := CP * bb ^ 2 * ν⁻¹ * Real.log bb ^ (-(100 : ℝ)))
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    ?_ ?_ ?_) ?_
  · intro w f _ hw
    exact hHolR aa (hρY.trans hρa') f w hw ρ hρY (by linarith only [hρa])
  · intro w f hw
    exact hPoR aa (hρY.trans hρa') f w hw
  · intro w f hw
    exact hPoR bb (hρY.trans (hρa'.trans hab)) f w hw
  · refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
    exact decayEst_K_bound hν hcs hCH hCP hρ hρa' hab hLg1 hLga


/-- Powers of the scale: `(ρ/(s/p))^Θ (s/p)(q s) (2/(Ω s^d))^{1/2} = c ρ^Θ s^{-β}`. -/
theorem decayEst_scale_arith {γ ρ s p q Ω : ℝ} (hρ : 0 < ρ) (hs : 0 < s) (hp : 0 < p)
    (hq : 0 < q) (hΩ : 0 < Ω) :
    (ρ / (s / p)) ^ (γ + (d : ℝ) / 2) * ((s / p) * (q * s)) *
        Real.sqrt (2 / (Ω * s ^ d)) =
      (p ^ (γ + (d : ℝ) / 2) * (q / p) * Real.sqrt (2 / Ω)) * ρ ^ (γ + (d : ℝ) / 2) *
        s ^ (-((d : ℝ) - 2 + γ)) := by
  set Θ : ℝ := γ + (d : ℝ) / 2 with hΘ
  have h1 : (ρ / (s / p)) ^ Θ = p ^ Θ * ρ ^ Θ * s ^ (-Θ) := by
    rw [show ρ / (s / p) = p * ρ * s⁻¹ by field_simp, Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow hs.le, ← Real.rpow_neg hs.le]
  have hsd : Real.sqrt (s ^ d) = s ^ ((d : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hs.le]
    congr 1
    ring
  have h2 : Real.sqrt (2 / (Ω * s ^ d)) = Real.sqrt (2 / Ω) * s ^ (-((d : ℝ) / 2)) := by
    rw [show 2 / (Ω * s ^ d) = 2 / Ω * (s ^ d)⁻¹ by field_simp, Real.sqrt_mul (by positivity),
      Real.sqrt_inv, hsd, Real.rpow_neg hs.le]
  have h3 : s ^ (2 : ℝ) * s ^ (-Θ) * s ^ (-((d : ℝ) / 2)) = s ^ (-((d : ℝ) - 2 + γ)) := by
    rw [← Real.rpow_add hs, ← Real.rpow_add hs]
    congr 1
    rw [hΘ]
    ring
  have h4 : (s / p) * (q * s) = (q / p) * s ^ (2 : ℝ) := by
    rw [Real.rpow_two]; field_simp
  rw [h1, h2, h4]
  calc p ^ Θ * ρ ^ Θ * s ^ (-Θ) * (q / p * s ^ (2 : ℝ)) * (Real.sqrt (2 / Ω) * s ^ (-((d : ℝ) / 2)))
      = (p ^ Θ * (q / p) * Real.sqrt (2 / Ω)) * ρ ^ Θ *
        (s ^ (2 : ℝ) * s ^ (-Θ) * s ^ (-((d : ℝ) / 2))) := by ring
    _ = _ := by rw [h3]

end

/-!
# The boundary anchor and the micro-scale decay estimate

The `L^∞` bound near `∂B_R` from the boundary `L^∞`-`L²` estimate and the dual `L²` bound on
`{R/4 < |x| < R}`, then the decay estimate at unit scale: for `u ∈ H¹₀(B_{Rm})` with
`-∇·(a∇u) = h`, `h` of mean zero supported in `B_ρ`,
`|u| ≤ C ρ^{γ+d/2} r^{2-γ-d} (log)^{-1/2} ‖h‖_{L²}` on `B_{Rm} \ B_r`.
-/

section

open Homogenization MeasureTheory SuperdiffusionCLT.Section6 SuperdiffusionCLT.Section7
open scoped Pointwise ENNReal

variable {d : ℕ}

/-- The constant of the dual `L²` bound. -/
def decayEst_Kc (ν cs CH CP : ℝ) : ℝ :=
  CH * CP * (CP * cs ^ (-(1 / 4 : ℝ)) * Real.sqrt ν / ν + Real.sqrt CP / ν) *
    cs ^ (-(1 / 4 : ℝ)) * Real.sqrt ν

/-- `|B_1|`. -/
def decayEst_Omega (d : ℕ) : ℝ := (volume (euclidBall (d := d) 1)).toReal

theorem decayEst_Omega_pos [NeZero d] : 0 < decayEst_Omega d := decayEst_volT_ball_pos one_pos

/-- **Anchor bound** near the boundary from an `L²` bound on the larger annulus. -/
theorem decayEst_anchor [NeZero d] {Rm CB M : ℝ} (hR : 0 < Rm) (hCB : 0 ≤ CB)
    (u : H10Function (euclidBall (d := d) Rm))
    (hBd : eLpNorm u.toH1Function.toFun ⊤ (volume.restrict (decayEst_ann (d := d) (Rm / 3) Rm)) ≤
      ENNReal.ofReal CB * lpBar (decayEst_ann (d := d) (Rm / 4) Rm) 2
        (fun x => u.toH1Function.toFun x -
          ⨍ z in decayEst_ann (d := d) (Rm / 4) Rm, u.toH1Function.toFun z))
    (hM : Real.sqrt (∫ x in decayEst_ann (d := d) (Rm / 4) Rm,
      (u.toH1Function.toFun x - h1_avg (decayEst_ann (Rm / 4) Rm) u.toH1Function.toFun) ^ 2) ≤ M) :
    ∀ᵐ x ∂volume.restrict (decayEst_ann (d := d) (Rm / 3) Rm),
      |u.toH1Function.toFun x| ≤
        CB * M * Real.sqrt (2 / (decayEst_Omega d * Rm ^ d)) := by
  set W : Set (Vec d) := decayEst_ann (Rm / 4) Rm with hW
  set w : Vec d → ℝ := u.toH1Function.toFun with hw
  have hWfin : volume W ≠ ⊤ := decayEst_ann_vol_ne_top hR
  have hvolW := decayEst_vol_ann_ge (d := d) hR
  have hbig : (volume (euclidBall (d := d) Rm)).toReal = Rm ^ d * decayEst_Omega d :=
    decayEst_volT_ball hR
  have hΩ := decayEst_Omega_pos (d := d)
  have hWlow : decayEst_Omega d * Rm ^ d / 2 ≤ (volume W).toReal := by
    refine le_trans ?_ hvolW
    rw [hbig]
    nlinarith only [hΩ]
  have hWpos : 0 < (volume W).toReal := lt_of_lt_of_le (by positivity) hWlow
  have hwL2 : MemLp w 2 (volume.restrict W) :=
    u.toH1Function.memL2.mono_measure (Measure.restrict_mono
      ((decayEst_ann_subset _ _)) le_rfl)
  simp only [hr_avg_eq] at hBd
  rw [hr_lpBar_eq hWfin hWpos hwL2, ← ENNReal.ofReal_mul hCB] at hBd
  have hmeas : AEStronglyMeasurable w (volume.restrict (decayEst_ann (d := d) (Rm / 3) Rm)) :=
    u.toH1Function.memL2.aestronglyMeasurable.mono_measure
      (Measure.restrict_mono (decayEst_ann_subset _ _) le_rfl)
  have hae := decayEst_ae_le_of_eLpNorm_top hmeas (mul_nonneg hCB (Real.sqrt_nonneg _)) hBd
  have hI0 : 0 ≤ ∫ x in W, (w x - h1_avg W w) ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hM0 : 0 ≤ M := (Real.sqrt_nonneg _).trans hM
  have hI : ∫ x in W, (w x - h1_avg W w) ^ 2 ≤ M ^ 2 := (Real.sqrt_le_left hM0).1 hM
  have hl2 : h1_l2 W w ≤ M * Real.sqrt (2 / (decayEst_Omega d * Rm ^ d)) := by
    unfold h1_l2
    have h1 : (∫ x in W, (w x - h1_avg W w) ^ 2) / (volume W).toReal ≤
        M ^ 2 / (decayEst_Omega d * Rm ^ d / 2) :=
      div_le_div₀ (sq_nonneg M) hI (by positivity) hWlow
    refine (Real.sqrt_le_sqrt h1).trans (le_of_eq ?_)
    rw [show M ^ 2 / (decayEst_Omega d * Rm ^ d / 2) =
        M ^ 2 * (2 / (decayEst_Omega d * Rm ^ d)) by field_simp,
      Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hM0]
  filter_upwards [hae] with x hx
  refine hx.trans ?_
  calc CB * h1_l2 W w ≤ CB * (M * Real.sqrt (2 / (decayEst_Omega d * Rm ^ d))) :=
        mul_le_mul_of_nonneg_left hl2 hCB
    _ = _ := by ring


/-- The constant of the micro-scale decay estimate. -/
def decayEst_Cmicro (d : ℕ) (γ ν cs CH CP CL CB : ℝ) : ℝ :=
  (CB * decayEst_Kc ν cs CH CP *
      (4 ^ (γ + (d : ℝ) / 2) * (1 / 4) * Real.sqrt (2 / decayEst_Omega d))) +
    (CL * decayEst_Kc ν cs CH CP *
      (3 ^ (γ + (d : ℝ) / 2) * ((4 / 3) / 3) * Real.sqrt (2 / decayEst_Omega d))) +
    ((CB * decayEst_Kc ν cs CH CP *
        (4 ^ (γ + (d : ℝ) / 2) * (1 / 4) * Real.sqrt (2 / decayEst_Omega d))) +
      2 * (CL * decayEst_Kc ν cs CH CP *
        (3 ^ (γ + (d : ℝ) / 2) * ((4 / 3) / 3) * Real.sqrt (2 / decayEst_Omega d))) +
      2 * (CL * decayEst_Kc ν cs CH CP *
        (3 ^ (γ + (d : ℝ) / 2) * ((4 / 3) / 3) * Real.sqrt (2 / decayEst_Omega d))) /
        (1 - (3 / 2 : ℝ) ^ (-((d : ℝ) - 2 + γ))))

theorem decayEst_Kc_nonneg {ν cs CH CP : ℝ} (hν : 0 < ν) (hcs : 0 < cs) (hCH : 0 ≤ CH)
    (hCP : 0 ≤ CP) : 0 ≤ decayEst_Kc ν cs CH CP := by
  unfold decayEst_Kc
  have := Real.rpow_nonneg hcs.le (-(1 / 4 : ℝ))
  positivity


/-- **The decay estimate at unit scale.** -/
theorem decayEst_micro [NeZero d] (hd : 2 ≤ d) (a : CoeffField d)
    {ν cs γ CH CP CL CB Y Lg : ℝ} (hν : 0 < ν) (hcs : 0 < cs) (hγ : 0 < γ) (hCH : 0 ≤ CH)
    (hCP : 0 ≤ CP) (hCL : 0 ≤ CL) (hCB : 0 ≤ CB) (hY : 1 ≤ Y) (hLg1 : 1 ≤ Lg)
    (hsym : ∀ x, symmPart (a x) = ν • (1 : Mat d))
    {Rm rm ρ : ℝ} (hρY : Y ≤ ρ) (hρr : 8 * ρ ≤ rm) (hrR : rm ≤ Rm)
    (hLg : Lg ≤ Real.log (rm / 4))
    (hexist : ∀ g : Vec d → ℝ, MemLp g 2 (volume.restrict (euclidBall (d := d) Rm)) →
      ∃ v : H10Function (euclidBall (d := d) Rm),
        IsWeakSolutionOn (fun x => matTranspose (a x)) (euclidBall Rm) v.toH1Function g
          (fun _ => 0))
    (hHolR : ∀ R' : ℝ, Y ≤ R' → ∀ (f : Vec d → ℝ) (w : H1Function (euclidBall (d := d) R')),
      IsWeakSolutionOn (fun x => matTranspose (a x)) (euclidBall R') w f (fun _ => 0) →
      ∀ r' : ℝ, Y ≤ r' → r' ≤ R' / 2 →
        eLpNorm (fun x => w.toFun x - ∫ y, w.toFun y ∂ballMeasure (d := d) r') ⊤
            (volume.restrict (euclidBall r')) ≤
          ENNReal.ofReal (CH * (r' / R') ^ γ) *
            (ballL2 R' (fun x => w.toFun x - ∫ y, w.toFun y ∂ballMeasure (d := d) R') +
              ENNReal.ofReal (Real.log R' ^ (-(1 / 2 : ℝ)) * R' ^ 2) *
                eLpNorm f ⊤ (volume.restrict (euclidBall (d := d) R'))))
    (hPoR : ∀ R' : ℝ, Y ≤ R' → ∀ (f : Vec d → ℝ) (w : H1Function (euclidBall (d := d) R')),
      IsWeakSolutionOn (fun x => matTranspose (a x)) (euclidBall R') w f (fun _ => 0) →
      lpBar (euclidBall (d := d) R') 2 (fun x => w.toFun x - ⨍ z in euclidBall R', w.toFun z) ≤
        ENNReal.ofReal (CP * R' * cs ^ (-(1 / 4 : ℝ)) * Real.sqrt ν *
            Real.log R' ^ (-(1 / 4 : ℝ))) *
          lpBar (euclidBall R') 2 (fun x => eucNorm (w.grad x)) +
        ENNReal.ofReal (CP * R' ^ 2 * ν⁻¹ * Real.log R' ^ (-(100 : ℝ))) *
          lpBar (euclidBall R') 2 f)
    (hLin : ∀ s : ℝ, Y ≤ s → ∀ W V : Set (Vec d), V ⊆ W →
      (∀ x ∈ V, Metric.ball x (1 / (12 * (d : ℝ)) * s) ⊆ W) → W ⊆ Metric.ball 0 (2 * s) →
      ∀ w : H1Function W, IsWeakSolutionOn a W w (fun _ => 0) (fun _ => 0) →
        eLpNorm (fun x => w.toFun x - ⨍ z in V, w.toFun z) ⊤ (volume.restrict V) ≤
          ENNReal.ofReal CL * lpBar W 2 (fun x => w.toFun x - ⨍ z in W, w.toFun z))
    (hBd : ∀ R' : ℝ, Y ≤ R' → ∀ u' : H10Function (euclidBall (d := d) R'),
      IsWeakSolutionOn a (decayEst_ann (R' / 8) R')
        (u'.toH1Function.restrict (decayEst_ann_isOpen _ _) (decayEst_ann_subset _ _))
        (fun _ => 0) (fun _ => 0) →
      eLpNorm u'.toH1Function.toFun ⊤ (volume.restrict (decayEst_ann (d := d) (R' / 3) R')) ≤
        ENNReal.ofReal CB * lpBar (decayEst_ann (d := d) (R' / 4) R') 2
          (fun x => u'.toH1Function.toFun x -
            ⨍ z in decayEst_ann (d := d) (R' / 4) R', u'.toH1Function.toFun z))
    (u : H10Function (euclidBall (d := d) Rm)) (h : Vec d → ℝ)
    (hu : IsWeakSolutionOn a (euclidBall Rm) u.toH1Function h (fun _ => 0))
    (hsupp : ∀ x, x ∉ euclidBall (d := d) ρ → h x = 0)
    (hmean : ∫ x in euclidBall (d := d) ρ, h x = 0)
    (hh : MemLp h 2 (volume.restrict (euclidBall (d := d) ρ))) :
    ∀ᵐ x ∂volume.restrict (euclidBall (d := d) Rm \ euclidBall rm),
      |u.toH1Function.toFun x| ≤
        decayEst_Cmicro d γ ν cs CH CP CL CB * rm ^ (-((d : ℝ) - 2 + γ)) *
          (ρ ^ (γ + (d : ℝ) / 2) * Lg ^ (-(1 / 2 : ℝ)) *
            Real.sqrt (∫ x in euclidBall (d := d) ρ, h x ^ 2)) := by
  have hρ : 0 < ρ := lt_of_lt_of_le (by linarith only [hY]) hρY
  have hrm : 0 < rm := by linarith only [hρ, hρr]
  have hRm : 0 < Rm := lt_of_lt_of_le hrm hrR
  have hβ : 0 < (d : ℝ) - 2 + γ := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith only [this, hγ]
  have hΩ := decayEst_Omega_pos (d := d)
  set Hn : ℝ := Real.sqrt (∫ x in euclidBall (d := d) ρ, h x ^ 2) with hHn
  set T : ℝ := ρ ^ (γ + (d : ℝ) / 2) * Lg ^ (-(1 / 2 : ℝ)) * Hn with hT
  have hT0 : 0 ≤ T := by
    have : 0 ≤ Lg ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by linarith only [hLg1]) _
    positivity
  set Kc : ℝ := decayEst_Kc ν cs CH CP with hKc
  have hKc0 : 0 ≤ Kc := decayEst_Kc_nonneg hν hcs hCH hCP
  set C₁ : ℝ := CL * Kc * (3 ^ (γ + (d : ℝ) / 2) * ((4 / 3) / 3) * Real.sqrt (2 / decayEst_Omega d))
    with hC₁
  set C₂ : ℝ := CB * Kc * (4 ^ (γ + (d : ℝ) / 2) * (1 / 4) * Real.sqrt (2 / decayEst_Omega d))
    with hC₂
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hC₂0 : 0 ≤ C₂ := by positivity
  -- the oscillation on each annulus
  have hosc : ∀ s : ℝ, 7 * rm / 4 ≤ s → s ≤ 2 * Rm / 3 →
      ∀ᵐ x ∂volume.restrict (decayEst_ann (d := d) (s / 2) s),
        |u.toH1Function.toFun x - h1_avg (decayEst_ann (s / 2) s) u.toH1Function.toFun| ≤
          C₁ * s ^ (-((d : ℝ) - 2 + γ)) * T := by
    intro s hs1 hs2
    have hspos : 0 < s := by linarith only [hs1, hrm]
    have hl2 := decayEst_l2_ann a hν hcs hCH hCP hY hLg1 hsym (Rm := Rm) (ρ := ρ)
      (aa := s / 3) (bb := 4 * s / 3) hρY (by linarith only [hs1, hρr, hρ]) (by linarith only [hspos])
      (by linarith only [hs2, hRm]) (hLg.trans (Real.log_le_log (by positivity)
        (by linarith only [hs1, hrm]))) hexist hHolR hPoR u h hu hsupp hmean hh
    have hl2' : Real.sqrt (∫ x in decayEst_ann (d := d) (s / 3) (4 * s / 3),
        (u.toH1Function.toFun x -
          h1_avg (decayEst_ann (s / 3) (4 * s / 3)) u.toH1Function.toFun) ^ 2) ≤
        (Kc * (ρ / (s / 3)) ^ (γ + (d : ℝ) / 2) * (s / 3 * (4 * s / 3)) *
          Lg ^ (-(1 / 2 : ℝ))) * Hn := hl2
    have hos := decayEst_linf_annulus (R := Rm) (ρ := ρ) hspos hρ.le
      (by linarith only [hs1, hρr, hρ]) (by linarith only [hs2, hRm]) hCL
      (hLin s (by linarith only [hs1, hρY, hρr, hY, hρ])) u.toH1Function h hu hsupp hl2'
    have hos' : ∀ᵐ x ∂volume.restrict (decayEst_ann (d := d) (s / 2) s),
        |u.toH1Function.toFun x - h1_avg (decayEst_ann (s / 2) s) u.toH1Function.toFun| ≤
          CL * ((Kc * (ρ / (s / 3)) ^ (γ + (d : ℝ) / 2) * (s / 3 * (4 * s / 3)) *
            Lg ^ (-(1 / 2 : ℝ))) * Hn) * Real.sqrt (2 / (decayEst_Omega d * s ^ d)) := hos
    refine hos'.mono fun x hx => hx.trans (le_of_eq ?_)
    have hP := decayEst_scale_arith (γ := γ) (d := d) hρ hspos (by norm_num : (0 : ℝ) < 3)
      (by norm_num : (0 : ℝ) < 4 / 3) hΩ
    rw [show 4 * s / 3 = 4 / 3 * s by ring]
    have : CL * ((Kc * (ρ / (s / 3)) ^ (γ + (d : ℝ) / 2) * (s / 3 * (4 / 3 * s)) *
          Lg ^ (-(1 / 2 : ℝ))) * Hn) * Real.sqrt (2 / (decayEst_Omega d * s ^ d)) =
        CL * Kc * Lg ^ (-(1 / 2 : ℝ)) * Hn * ((ρ / (s / 3)) ^ (γ + (d : ℝ) / 2) *
          (s / 3 * (4 / 3 * s)) * Real.sqrt (2 / (decayEst_Omega d * s ^ d))) := by ring
    rw [this, hP, hC₁, hT]
    ring
  -- the anchor near the boundary
  have hanch : ∀ᵐ x ∂volume.restrict (decayEst_ann (d := d) (Rm / 3) Rm),
      |u.toH1Function.toFun x| ≤ C₂ * Rm ^ (-((d : ℝ) - 2 + γ)) * T := by
    have hRY : Y ≤ Rm := hρY.trans ((by linarith only [hρr, hρ] : ρ ≤ rm).trans hrR)
    have hl2 := decayEst_l2_ann a hν hcs hCH hCP hY hLg1 hsym (Rm := Rm) (ρ := ρ)
      (aa := Rm / 4) (bb := Rm) hρY (by linarith only [hρr, hrR, hρ]) (by linarith only [hRm])
      le_rfl (hLg.trans (Real.log_le_log (by positivity) (by linarith only [hrR])))
      hexist hHolR hPoR u h hu hsupp hmean hh
    have hl2' : Real.sqrt (∫ x in decayEst_ann (d := d) (Rm / 4) Rm,
        (u.toH1Function.toFun x -
          h1_avg (decayEst_ann (Rm / 4) Rm) u.toH1Function.toFun) ^ 2) ≤
        (Kc * (ρ / (Rm / 4)) ^ (γ + (d : ℝ) / 2) * (Rm / 4 * Rm) * Lg ^ (-(1 / 2 : ℝ))) * Hn :=
      hl2
    have hweak : IsWeakSolutionOn a (decayEst_ann (Rm / 8) Rm)
        (u.toH1Function.restrict (decayEst_ann_isOpen _ _) (decayEst_ann_subset _ _))
        (fun _ => 0) (fun _ => 0) := by
      refine decayEst_weak_congr_rhs (decayEst_ann_measurable _ _) (fun x hx => ?_)
        (decayEst_weak_restrict (decayEst_ann_isOpen _ _) (decayEst_ann_subset _ _) hu)
      refine hsupp x (fun hxρ => ?_)
      have h1 := hx.1
      have h2 : vecNormSq x < ρ ^ 2 := hxρ
      have h3 : ρ ^ 2 ≤ (Rm / 8) ^ 2 :=
        pow_le_pow_left₀ hρ.le (by linarith only [hρr, hrR]) 2
      linarith only [h1, h2, h3]
    have hanc := decayEst_anchor hRm hCB u (hBd Rm hRY u hweak) hl2'
    refine hanc.mono fun x hx => hx.trans (le_of_eq ?_)
    have hP := decayEst_scale_arith (γ := γ) (d := d) hρ hRm (by norm_num : (0 : ℝ) < 4)
      (by norm_num : (0 : ℝ) < 1) hΩ
    have : CB * ((Kc * (ρ / (Rm / 4)) ^ (γ + (d : ℝ) / 2) * (Rm / 4 * Rm) *
          Lg ^ (-(1 / 2 : ℝ))) * Hn) * Real.sqrt (2 / (decayEst_Omega d * Rm ^ d)) =
        CB * Kc * Lg ^ (-(1 / 2 : ℝ)) * Hn * ((ρ / (Rm / 4)) ^ (γ + (d : ℝ) / 2) *
          (Rm / 4 * (1 * Rm)) * Real.sqrt (2 / (decayEst_Omega d * Rm ^ d))) := by ring
    rw [this, hP, hC₂, hT]
    ring
  have hchain := decayEst_chain (u := fun x => u.toH1Function.toFun x) (R := Rm) (r := rm)
    (s₀ := 7 * rm / 4) (β := (d : ℝ) - 2 + γ) (T := T) (C₁ := C₁) (C₂ := C₂) hβ hT0 hC₁0 hC₂0 hrm hrR
    (by linarith only [hrm]) le_rfl hosc hanch
  refine hchain.mono fun x hx => hx.trans (le_of_eq ?_)
  unfold decayEst_Cmicro
  rw [hT, hC₁, hC₂]

end

end

end SuperdiffusionCLT.Section8
