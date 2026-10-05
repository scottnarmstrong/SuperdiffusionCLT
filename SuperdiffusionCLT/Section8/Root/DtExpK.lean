/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Root.DtExpH
public import SuperdiffusionCLT.Section8.Prereq.ExitEstimateD
public import SuperdiffusionCLT.Section8.Root.DtExpG

/-!
# The exit probability and the homogenization estimate in the scales of the clause
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization MeasureTheory MarkovProcess
open scoped Pointwise ENNReal NNReal Topology

/-- The set of the exit estimate is the Euclidean ball of radius `ε⁻¹`. -/
theorem dtExp_ball_eq {d : ℕ} {ε : ℝ} (hε : 0 < ε) :
    {y : Vec d | vecNormSq (ε • y) < 1} = euclideanBall (0 : Vec d) ε⁻¹ := by
  ext y
  simp only [euclideanBall, euclideanSqDist, sub_zero, Set.mem_ofPred_eq, vecNormSq_smul]
  rw [inv_pow, ← one_div, lt_div_iff₀ (by positivity), mul_comm]

/-- **The exit probability, in the scales of the clause.**  If the exit estimate holds at the scale
`ε = (√(tΛ))⁻¹` with every `t₀ ∈ (0, 1]`, then the exit probability of the ball of radius `ε⁻¹`
before the time `t` is at most `2 exp (-(c/2) L^{α/6})`. -/
theorem dtExp_p_bound {d : ℕ} {t α c cE : ℝ} (ht : 10 ≤ t) (hα0 : 0 < α) (hα1 : α < 1) (hc : 0 < c) (hcE : 0 ≤ cE)
    (hLc : Real.sqrt (8 * c) ≤ Real.log t ^ (α / 6))
    {μ : Measure (ContinuousPath (Vec d))} [IsProbabilityMeasure μ]
    (hex : ∀ t0 : ℝ, 0 < t0 → t0 ≤ 1 →
      μ {w | ContinuousPath.exitTime {y : Vec d | vecNormSq
          (((Real.sqrt (t * Real.log t ^ ((1 + α) / 2)))⁻¹) • y) < 1} w ≤
        ENNReal.ofReal (timeScale c ((Real.sqrt (t * Real.log t ^ ((1 + α) / 2)))⁻¹) * t0)} ≤
        2 * ENNReal.ofReal (Real.exp (-(cE * min (t0 ^ (-(1 / 2 : ℝ)))
          (|Real.log ((Real.sqrt (t * Real.log t ^ ((1 + α) / 2)))⁻¹)| ^ (α / 6)))))) :
    μ.real {w | ContinuousPath.exitTime (euclideanBall (0 : Vec d)
        ((Real.sqrt (t * Real.log t ^ ((1 + α) / 2)))⁻¹)⁻¹) w ≤ (t.toNNReal : ℝ≥0∞)} ≤
      2 * Real.exp (-(cE / 2 * Real.log t ^ (α / 6))) := by
  obtain ⟨hL, hΛ1, hΛL⟩ := dtExp_scale_facts ht hα0 hα1
  obtain ⟨hε0, hε2, hεhalf, hv1, hv2, hop, hdiff⟩ := dtExp_eps_facts ht hα0 hα1 hc
  set L := Real.log t with hLdef
  set Λ := L ^ ((1 + α) / 2) with hΛdef
  set ε := (Real.sqrt (t * Λ))⁻¹ with hεdef
  set v := |Real.log ε| with hvdef
  have ht0 : 0 < t := by linarith only [ht]
  have hΛ0 : 0 < Λ := by linarith only [hΛ1]
  have hL0 : 0 < L := by linarith only [hL]
  have hvpos : 0 < v := by linarith only [hv1, hL]
  have hρ : ε ^ 2 = 1 / (t * Λ) := by
    rw [eq_div_iff (mul_pos ht0 hΛ0).ne']; linarith only [hε2]
  have hset := dtExp_ball_eq (d := d) hε0
  have hTS : timeScale c ε = t * Λ / Real.sqrt (8 * c * v) := by
    unfold timeScale
    have h1 : (ε ^ 2)⁻¹ = t * Λ := by rw [hρ]; field_simp
    rw [h1, ← Real.sqrt_eq_rpow, div_eq_mul_inv]
  have hsv : 0 < Real.sqrt (8 * c * v) := Real.sqrt_pos.2 (by positivity)
  have hTSpos : 0 < timeScale c ε := by rw [hTS]; positivity
  set t0 : ℝ := t / timeScale c ε with ht0def
  have ht0pos : 0 < t0 := div_pos ht0 hTSpos
  have hTt0 : timeScale c ε * t0 = t := by rw [ht0def]; field_simp
  have ht0eq : t0 = Real.sqrt (8 * c * v) / Λ := by
    rw [ht0def, hTS]; field_simp
  -- the size of `t0`
  have hΛfac : Λ = Real.sqrt L * L ^ (α / 2) := by
    rw [hΛdef, show (1 + α) / 2 = 1 / 2 + α / 2 by ring, Real.rpow_add hL0,
      ← Real.sqrt_eq_rpow]
  have hLα : 0 < L ^ (α / 2) := Real.rpow_pos_of_pos hL0 _
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.2 hL0
  have hsv_le : Real.sqrt (8 * c * v) ≤ Real.sqrt (8 * c) * Real.sqrt L := by
    rw [← Real.sqrt_mul (by positivity)]; exact Real.sqrt_le_sqrt (by gcongr)
  have hLc' : L ^ (α / 6) ≤ L ^ (α / 2) :=
    Real.rpow_le_rpow_of_exponent_le hL (by linarith only [hα0])
  have ht0le : t0 ≤ 1 := by
    rw [ht0eq, div_le_one hΛ0, hΛfac]
    calc Real.sqrt (8 * c * v) ≤ Real.sqrt (8 * c) * Real.sqrt L := hsv_le
      _ ≤ L ^ (α / 2) * Real.sqrt L := by
          gcongr; exact hLc.trans hLc'
      _ = Real.sqrt L * L ^ (α / 2) := mul_comm _ _
  have hinv : L ^ (α / 3) ≤ t0⁻¹ := by
    rw [ht0eq, inv_div, hΛfac]
    have h1 : Real.sqrt L * L ^ (α / 2) / (Real.sqrt (8 * c) * Real.sqrt L) =
        L ^ (α / 2) / Real.sqrt (8 * c) := by field_simp
    have h2 : L ^ (α / 2) / Real.sqrt (8 * c) ≤ Real.sqrt L * L ^ (α / 2) / Real.sqrt (8 * c * v) := by
      rw [← h1]
      exact div_le_div_of_nonneg_left (by positivity) hsv (by
        simpa [mul_comm] using hsv_le)
    refine le_trans ?_ h2
    have hpos : 0 < Real.sqrt (8 * c) := Real.sqrt_pos.2 (by positivity)
    rw [le_div_iff₀ hpos]
    calc L ^ (α / 3) * Real.sqrt (8 * c) ≤ L ^ (α / 3) * L ^ (α / 6) := by gcongr
      _ = L ^ (α / 2) := by rw [← Real.rpow_add hL0]; congr 1; ring
  have hrt : L ^ (α / 6) ≤ t0 ^ (-(1 / 2 : ℝ)) := by
    rw [Real.rpow_neg ht0pos.le, ← Real.inv_rpow ht0pos.le]
    calc L ^ (α / 6) = (L ^ (α / 3)) ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_mul hL0.le]; congr 1; ring
      _ ≤ (t0⁻¹) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by positivity) hinv (by norm_num)
  have hrv : L ^ (α / 6) / 2 ≤ v ^ (α / 6) := by
    have h1 : (L / 2) ^ (α / 6) ≤ v ^ (α / 6) :=
      Real.rpow_le_rpow (by positivity) hv1 (by positivity)
    refine le_trans ?_ h1
    rw [Real.div_rpow hL0.le (by norm_num)]
    have h2 : (2 : ℝ) ^ (α / 6) ≤ 2 := by
      calc (2 : ℝ) ^ (α / 6) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hα1])
        _ = 2 := Real.rpow_one 2
    have h3 : 0 < (2 : ℝ) ^ (α / 6) := by positivity
    rw [div_le_div_iff₀ (by norm_num) h3]
    nlinarith only [h2, Real.rpow_pos_of_pos hL0 (α / 6)]
  have hmin : L ^ (α / 6) / 2 ≤ min (t0 ^ (-(1 / 2 : ℝ))) (v ^ (α / 6)) := by
    refine le_min ?_ hrv
    have : 0 ≤ L ^ (α / 6) := Real.rpow_nonneg hL0.le _
    linarith only [hrt, this]
  have hh := hex t0 ht0pos ht0le
  rw [hTt0, hset] at hh
  have hofReal : ENNReal.ofReal t = (t.toNNReal : ℝ≥0∞) := rfl
  rw [hofReal] at hh
  have hexp : Real.exp (-(cE * min (t0 ^ (-(1 / 2 : ℝ))) (v ^ (α / 6)))) ≤
      Real.exp (-(cE / 2 * L ^ (α / 6))) := by
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_left hmin hcE
    linarith only [this]
  have hfin : (μ {w | ContinuousPath.exitTime (euclideanBall (0 : Vec d) ε⁻¹) w ≤
      (t.toNNReal : ℝ≥0∞)}).toReal ≤ 2 * Real.exp (-(cE / 2 * L ^ (α / 6))) := by
    have h1 := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top) hh
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at h1
    simp only [ENNReal.toReal_ofNat] at h1
    linarith only [h1, hexp]
  exact hfin

section Dirichlet

open SuperdiffusionCLT.Section7 SuperdiffusionCLT.Section2.Cutoff

/-- **The homogenization estimate in the form used for the stopped moments.**  At shift zero, the
resolvent estimate on the unit ball is the comparison on the dilated ball, with every constant at
least the printed one. -/
theorem dtExp_hA {d : ℕ} {nu cStar : ℝ} {omega : ShellSeq d} {ε Er E0 : ℝ} (hε : 0 < ε)
    (hE : Er ≤ E0)
    (h : ∀ (f : Vec d → ℝ) (g u uhom : H1Function (euclideanBall (0 : Vec d) 1)),
      IsDirichletSolution (fun x => opScale cStar ε • epField nu omega ε x)
        (euclideanBall (0 : Vec d) 1) (fun x => f x - 0 * u.toFun x) g u →
      IsDirichletSolution (fun _ => (1 / 2 : ℝ) • (1 : Mat d)) (euclideanBall (0 : Vec d) 1)
        (fun x => f x - 0 * uhom.toFun x) g uhom →
      eLpNorm (fun x => u.toFun x - uhom.toFun x) ⊤ (volume.restrict (euclideanBall (0 : Vec d) 1)) ≤
        ENNReal.ofReal Er *
          (eLpNorm (fun x => eucNorm (g.grad x)) ⊤ (volume.restrict (euclideanBall (0 : Vec d) 1)) +
            eLpNorm (fun x => f x - 0 * u.toFun x) ⊤
              (volume.restrict (euclideanBall (0 : Vec d) 1)))) :
    ∀ (f : Vec d → ℝ) (g u uhom : H1Function ((ε⁻¹)⁻¹ • euclideanBall (0 : Vec d) ε⁻¹)),
      IsDirichletSolution (fun x => opScale cStar ε • epField nu omega ε x) _ f g u →
      IsDirichletSolution (fun _ => (1 / 2 : ℝ) • (1 : Mat d)) _ f g uhom →
      eLpNorm (fun x => u.toFun x - uhom.toFun x) ⊤
          (volume.restrict ((ε⁻¹)⁻¹ • euclideanBall (0 : Vec d) ε⁻¹)) ≤
        ENNReal.ofReal E0 *
          (eLpNorm (fun x => eucNorm (g.grad x)) ⊤
              (volume.restrict ((ε⁻¹)⁻¹ • euclideanBall (0 : Vec d) ε⁻¹)) +
            eLpNorm f ⊤ (volume.restrict ((ε⁻¹)⁻¹ • euclideanBall (0 : Vec d) ε⁻¹))) := by
  rw [exitEst_ball_dilate hε]
  intro f g u uhom hu huh
  have e : ∀ w : H1Function (euclideanBall (0 : Vec d) 1), (fun x => f x - 0 * w.toFun x) = f := by
    intro w; funext x; simp
  have hu' : IsDirichletSolution (fun x => opScale cStar ε • epField nu omega ε x)
      (euclideanBall (0 : Vec d) 1) (fun x => f x - 0 * u.toFun x) g u := by rw [e]; exact hu
  have huh' : IsDirichletSolution (fun _ => (1 / 2 : ℝ) • (1 : Mat d)) (euclideanBall (0 : Vec d) 1)
      (fun x => f x - 0 * uhom.toFun x) g uhom := by rw [e]; exact huh
  have h1 := h f g u uhom hu' huh'
  rw [e] at h1
  exact h1.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hE) le_rfl)

end Dirichlet

end SuperdiffusionCLT.Section8
