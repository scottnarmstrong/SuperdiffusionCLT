/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Root.InteriorApproxB
public import SuperdiffusionCLT.Section7.Root.InteriorApproxH
public import SuperdiffusionCLT.Section7.Lipschitz.Calc
public import SuperdiffusionCLT.Section7.MinimalScale.TranslatedInputsB
public import SuperdiffusionCLT.Section6.Prereq.GammaMax

/-!
# Interior approximation: real-variable estimates for the deterministic core
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem ip_sqrt_mul_le {σ σ' : ℝ} (hσ : 0 < σ) (hσ' : σ' ≤ 2 * σ) :
    Real.sqrt σ * Real.sqrt σ' ≤ 2 * σ := by
  have h1 : Real.sqrt σ' ≤ 2 * Real.sqrt σ := by
    rw [Real.sqrt_le_left (by positivity)]
    rw [mul_pow, Real.sq_sqrt hσ.le]
    nlinarith only [hσ', hσ]
  have h2 : Real.sqrt σ * Real.sqrt σ = σ := Real.mul_self_sqrt hσ.le
  have := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg σ)
  nlinarith only [this, h2]

theorem ip_sqrt_div_le {σ σ' : ℝ} (hσ' : 0 < σ') (h : σ / 2 ≤ σ') :
    Real.sqrt σ / Real.sqrt σ' ≤ 2 := by
  have hs' : 0 < Real.sqrt σ' := Real.sqrt_pos.2 hσ'
  rw [div_le_iff₀ hs']
  have h1 : Real.sqrt σ ≤ 2 * Real.sqrt σ' := by
    rw [Real.sqrt_le_left (by positivity)]
    rw [mul_pow, Real.sq_sqrt hσ'.le]
    nlinarith only [h, hσ']
  exact h1

/-- The flux part of the real algebra. -/
theorem ip_alg_flux {T1 s3 Om F σ σ' ν δ CF Clip a1 a2 Kd : ℝ} (hT1 : 0 < T1) (hs3 : 0 ≤ s3)
    (hOm : 0 ≤ Om) (hF : 0 ≤ F) (hσ : 0 < σ) (hσ'1 : σ / 2 ≤ σ') (hσ'2 : σ' ≤ 2 * σ)
    (hν : 0 < ν) (hδ : 0 < δ) (hCF : 0 ≤ CF) (hClip : 0 ≤ Clip) 
    (ha1b : a1 ≤ CF * δ * Real.sqrt σ * Real.sqrt ν) (hKd : 0 ≤ Kd)
    (hN1 : Kd * a2 ≤ δ * (3 * T1)) :
    (3 * T1 / 2) * (Kd * (a1 * (Real.sqrt σ' / Real.sqrt ν *
        (Clip * (T1⁻¹ * (s3 * Om)) + Clip * (σ'⁻¹ * T1 * F))) + a2 * F)) / σ ≤
      (Kd + 1) * (3 * (s3 + 1) * CF * Clip + 1) * δ * (Om + σ⁻¹ * (3 * T1) ^ 2 * F) := by
  have hσ'0 : 0 < σ' := by linarith only [hσ'1, hσ]
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hsσ' : 0 < Real.sqrt σ' := Real.sqrt_pos.2 hσ'0
  have hsσ : 0 < Real.sqrt σ := Real.sqrt_pos.2 hσ
  have hP := ip_sqrt_mul_le hσ hσ'2
  have hQ := ip_sqrt_div_le hσ'0 hσ'1
  -- the gradient part
  have hE : a1 * (Real.sqrt σ' / Real.sqrt ν *
        (Clip * (T1⁻¹ * (s3 * Om)) + Clip * (σ'⁻¹ * T1 * F))) ≤
      CF * δ * Clip * (2 * σ * T1⁻¹ * s3 * Om + 2 * T1 * F) := by
    have e1 : CF * δ * Real.sqrt σ * Real.sqrt ν * (Real.sqrt σ' / Real.sqrt ν *
        (Clip * (T1⁻¹ * (s3 * Om)) + Clip * (σ'⁻¹ * T1 * F))) =
        CF * δ * Clip * (Real.sqrt σ * Real.sqrt σ' * (T1⁻¹ * (s3 * Om)) +
          (Real.sqrt σ / Real.sqrt σ') * (T1 * F)) := by
      have hinv : σ'⁻¹ = (Real.sqrt σ' * Real.sqrt σ')⁻¹ := by rw [Real.mul_self_sqrt hσ'0.le]
      rw [hinv]
      field_simp
    have hmono : a1 * (Real.sqrt σ' / Real.sqrt ν *
        (Clip * (T1⁻¹ * (s3 * Om)) + Clip * (σ'⁻¹ * T1 * F))) ≤
        CF * δ * Real.sqrt σ * Real.sqrt ν * (Real.sqrt σ' / Real.sqrt ν *
        (Clip * (T1⁻¹ * (s3 * Om)) + Clip * (σ'⁻¹ * T1 * F))) :=
      mul_le_mul_of_nonneg_right ha1b (by positivity)
    refine hmono.trans (e1.le.trans ?_)
    have h3 : Real.sqrt σ * Real.sqrt σ' * (T1⁻¹ * (s3 * Om)) ≤ 2 * σ * (T1⁻¹ * (s3 * Om)) :=
      mul_le_mul_of_nonneg_right hP (by positivity)
    have h4 : (Real.sqrt σ / Real.sqrt σ') * (T1 * F) ≤ 2 * (T1 * F) :=
      mul_le_mul_of_nonneg_right hQ (by positivity)
    have h5 := mul_le_mul_of_nonneg_left (add_le_add h3 h4) (by positivity : 0 ≤ CF * δ * Clip)
    refine h5.trans (le_of_eq ?_)
    ring
  set X : ℝ := σ⁻¹ * T1 ^ 2 * F with hX
  have hX0 : 0 ≤ X := by positivity
  have h1 : Kd * (a1 * (Real.sqrt σ' / Real.sqrt ν *
        (Clip * (T1⁻¹ * (s3 * Om)) + Clip * (σ'⁻¹ * T1 * F))) + a2 * F) ≤
      Kd * (CF * δ * Clip * (2 * σ * T1⁻¹ * s3 * Om + 2 * T1 * F)) + δ * (3 * T1) * F := by
    have := mul_le_mul_of_nonneg_left (add_le_add_left hE (a2 * F)) hKd
    have h2 : Kd * (a2 * F) ≤ δ * (3 * T1) * F := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hN1 hF
    linarith only [this, h2]
  have h3 : (3 * T1 / 2) * (Kd * (a1 * (Real.sqrt σ' / Real.sqrt ν *
        (Clip * (T1⁻¹ * (s3 * Om)) + Clip * (σ'⁻¹ * T1 * F))) + a2 * F)) / σ ≤
      (3 * T1 / 2) * (Kd * (CF * δ * Clip * (2 * σ * T1⁻¹ * s3 * Om + 2 * T1 * F)) +
        δ * (3 * T1) * F) / σ := by
    gcongr
  refine h3.trans ?_
  have e1 : (3 * T1 / 2) * (Kd * (CF * δ * Clip * (2 * σ * T1⁻¹ * s3 * Om + 2 * T1 * F)) +
        δ * (3 * T1) * F) / σ =
      3 * Kd * CF * Clip * δ * s3 * Om + 3 * Kd * CF * Clip * δ * X + 9 / 2 * δ * X := by
    rw [hX]
    field_simp
    ring
  rw [e1]
  have e2 : σ⁻¹ * (3 * T1) ^ 2 * F = 9 * X := by rw [hX]; ring
  rw [e2]
  have k1 : 0 ≤ δ * (3 * Kd * CF * Clip + 3 * (s3 + 1) * CF * Clip + 1 + Kd) := by positivity
  have k2 : 0 ≤ δ * (24 * Kd * CF * Clip + 27 * Kd * s3 * CF * Clip + 27 * (s3 + 1) * CF * Clip +
      9 * Kd + 9 / 2) := by positivity
  have e3 : (Kd + 1) * (3 * (s3 + 1) * CF * Clip + 1) * δ - 3 * Kd * CF * Clip * δ * s3 =
      δ * (3 * Kd * CF * Clip + 3 * (s3 + 1) * CF * Clip + 1 + Kd) := by ring
  have e4 : 9 * ((Kd + 1) * (3 * (s3 + 1) * CF * Clip + 1) * δ) -
      (3 * Kd * CF * Clip * δ + 9 / 2 * δ) =
      δ * (24 * Kd * CF * Clip + 27 * Kd * s3 * CF * Clip + 27 * (s3 + 1) * CF * Clip +
      9 * Kd + 9 / 2) := by ring
  have f1 := mul_nonneg k1 hOm
  have f2 := mul_nonneg k2 hX0
  nlinarith only [f1, f2, e3, e4]

/-- From the Lipschitz estimate at the scale `l + 3` to a uniform bound of the oscillation. -/
theorem ip_alg_T2 {t T Om Oz osc s3 Clip σ σ' F : ℝ} (ht : 0 < t) (hT : 0 < T) (hσ : 0 < σ)
    (hσ'1 : σ / 2 ≤ σ') (hF : 0 ≤ F) (hClip : 0 ≤ Clip) (hs3 : 0 ≤ s3) (hOm : 0 ≤ Om)
    (hOz : Oz ≤ s3 * Om)
    (h : (27 * t)⁻¹ * osc ≤ Clip * ((T / 3)⁻¹ * Oz) + Clip * (σ'⁻¹ * (T / 3) * F)) :
    osc ≤ (81 * Clip * s3 + 18 * Clip) * (t / T) * (Om + σ⁻¹ * T ^ 2 * F) := by
  have hσ'0 : 0 < σ' := by linarith only [hσ'1, hσ]
  have h27 : osc ≤ 27 * t * (Clip * ((T / 3)⁻¹ * Oz) + Clip * (σ'⁻¹ * (T / 3) * F)) := by
    have := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 27 * t)
    rwa [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul] at this
  refine h27.trans ?_
  have hi : σ'⁻¹ ≤ 2 * σ⁻¹ := by
    rw [inv_le_comm₀ hσ'0 (by positivity), mul_inv, inv_inv]
    linarith only [hσ'1]
  have h1 : (T / 3)⁻¹ * Oz ≤ (T / 3)⁻¹ * (s3 * Om) := mul_le_mul_of_nonneg_left hOz (by positivity)
  have h2 : σ'⁻¹ * (T / 3) * F ≤ 2 * σ⁻¹ * (T / 3) * F := by gcongr
  have h3 := add_le_add (mul_le_mul_of_nonneg_left h1 hClip) (mul_le_mul_of_nonneg_left h2 hClip)
  have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 27 * t)
  refine h4.trans ?_
  have e : 27 * t * (Clip * ((T / 3)⁻¹ * (s3 * Om)) + Clip * (2 * σ⁻¹ * (T / 3) * F)) =
      81 * Clip * s3 * (t / T) * Om + 18 * Clip * (t / T) * (σ⁻¹ * T ^ 2 * F) := by
    field_simp
    ring
  rw [e]
  have x1 : 0 ≤ 81 * Clip * s3 * (t / T) * (σ⁻¹ * T ^ 2 * F) := by positivity
  have x2 : 0 ≤ 18 * Clip * (t / T) * Om := by positivity
  nlinarith only [x1, x2]

/-- The bound of the mollification error, in units of `δ (‖u - (u)‖ + σ⁻¹ 3^{2m} ‖f‖)`. -/
theorem ip_alg_S {CDG Lt Clip s3 σ ν T t Om F δ Cthr T2 : ℝ} (hCDG : 0 ≤ CDG) (hLt : 0 ≤ Lt)
    (ht : 0 < t) (hT : 0 < T) (hσ : 0 < σ) (hν : 0 < ν) (hF : 0 ≤ F) (hClip : 0 ≤ Clip)
    (hs3 : 0 ≤ s3) (hOm : 0 ≤ Om)
    (hT2 : T2 ≤ (81 * Clip * s3 + 18 * Clip) * (t / T) * (Om + σ⁻¹ * T ^ 2 * F))
    (hN3 : Cthr * Lt * (t / T + σ / ν * (t / T) ^ 2) ≤ δ)
    (hC : CDG * (81 * Clip * s3 + 18 * Clip + 729) ≤ Cthr) :
    CDG * Lt * (T2 + 729 * t ^ 2 / ν * F) ≤ δ * (Om + σ⁻¹ * T ^ 2 * F) := by
  set R : ℝ := Om + σ⁻¹ * T ^ 2 * F with hR
  have hR0 : 0 ≤ R := by positivity
  set τ : ℝ := t / T with hτ
  have hτ0 : 0 ≤ τ := by positivity
  have e : 729 * t ^ 2 / ν * F = 729 * (σ / ν * τ ^ 2) * (σ⁻¹ * T ^ 2 * F) := by
    rw [hτ]; field_simp
  have h1 : T2 + 729 * t ^ 2 / ν * F ≤
      ((81 * Clip * s3 + 18 * Clip) * τ + 729 * (σ / ν * τ ^ 2)) * R := by
    rw [e]
    have : 729 * (σ / ν * τ ^ 2) * (σ⁻¹ * T ^ 2 * F) ≤ 729 * (σ / ν * τ ^ 2) * R := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [hR]; linarith only [hOm]
    nlinarith only [hT2, this]
  have h2 : CDG * Lt * (T2 + 729 * t ^ 2 / ν * F) ≤
      CDG * Lt * (((81 * Clip * s3 + 18 * Clip) * τ + 729 * (σ / ν * τ ^ 2)) * R) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  refine h2.trans ?_
  have h3 : CDG * (81 * Clip * s3 + 18 * Clip + 729) * (Lt * (τ + σ / ν * τ ^ 2)) ≤
      Cthr * (Lt * (τ + σ / ν * τ ^ 2)) :=
    mul_le_mul_of_nonneg_right hC (by positivity)
  have h4 : Cthr * (Lt * (τ + σ / ν * τ ^ 2)) ≤ δ := by
    have : Cthr * Lt * (τ + σ / ν * τ ^ 2) = Cthr * (Lt * (τ + σ / ν * τ ^ 2)) := by ring
    linarith only [hN3, this]
  have h5 : CDG * Lt * (((81 * Clip * s3 + 18 * Clip) * τ + 729 * (σ / ν * τ ^ 2))) ≤
      CDG * (81 * Clip * s3 + 18 * Clip + 729) * (Lt * (τ + σ / ν * τ ^ 2)) := by
    have hc : 0 ≤ σ / ν * τ ^ 2 := by positivity
    have hcc : 0 ≤ CDG * Lt := by positivity
    have : (81 * Clip * s3 + 18 * Clip) * τ + 729 * (σ / ν * τ ^ 2) ≤
        (81 * Clip * s3 + 18 * Clip + 729) * (τ + σ / ν * τ ^ 2) := by
      nlinarith only [hc, hτ0, mul_nonneg (by positivity : (0 : ℝ) ≤ 81 * Clip * s3 + 18 * Clip) hc,
        mul_nonneg hτ0 (by positivity : (0 : ℝ) ≤ 729)]
    calc CDG * Lt * ((81 * Clip * s3 + 18 * Clip) * τ + 729 * (σ / ν * τ ^ 2))
        ≤ CDG * Lt * ((81 * Clip * s3 + 18 * Clip + 729) * (τ + σ / ν * τ ^ 2)) :=
          mul_le_mul_of_nonneg_left this hcc
      _ = _ := by ring
  have h6 : CDG * Lt * (((81 * Clip * s3 + 18 * Clip) * τ + 729 * (σ / ν * τ ^ 2))) ≤ δ :=
    h5.trans (h3.trans h4)
  calc CDG * Lt * (((81 * Clip * s3 + 18 * Clip) * τ + 729 * (σ / ν * τ ^ 2)) * R)
      = (CDG * Lt * (((81 * Clip * s3 + 18 * Clip) * τ + 729 * (σ / ν * τ ^ 2)))) * R := by ring
    _ ≤ δ * R := mul_le_mul_of_nonneg_right h6 hR0

/-- A smooth profile with its bound and its Lipschitz constant. -/
theorem ip_profile (d : ℕ) :
    ∃ η : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) η ∧ (∀ w, 0 ≤ η w) ∧ ∫ w, η w = 1 ∧
      (∀ w, (∃ i, 1 < |w i|) → η w = 0) ∧ ∃ (A : ℝ) (L : NNReal), (∀ w, |η w| ≤ A) ∧
        LipschitzWith L η := by
  obtain ⟨η, hη, hη0, hη1, hηs⟩ := ia_exists_profile d
  have hsupp : HasCompactSupport η := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Vec d) 1) ?_
    intro w hw
    rw [mem_closedBall_zero_iff]
    by_contra hlt
    apply hw
    apply hηs
    by_contra h
    push Not at h
    exact hlt ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by
      rw [Real.norm_eq_abs]; exact h i)
  obtain ⟨A, hA⟩ := hsupp.exists_bound_of_continuous hη.continuous
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (𝕂 := ℝ) hsupp hη (by simp)
  exact ⟨η, hη, hη0, hη1, hηs, A, L, fun w => by simpa using hA w, hL⟩

/-- **The approximation at one scale, deterministic form**.  On the rounded cube `V ⊆ y + □_m`,
the solution `u` of the equation with the field `a` is within
`C δ (‖u - (u)‖_{L̲²(y+□_m)} + σ⁻¹ 3^{2m} ‖f‖_∞)` in `L^∞(V)` of a solution `uhom` of
`-σ Δ uhom = f` in `V`, provided the mollified-flux bounds on the cells of scale `3^l`
(`HFlux`) and the Lipschitz estimates on the cubes around the cell centres (`HL1`, `HL2`) hold,
together with the scale separation (the last three numerical hypotheses). -/
theorem ia_approx_det [NeZero d] (hd : 2 ≤ d) (CF Clip : ℝ) (hCF : 1 ≤ CF) (hClip : 1 ≤ Clip) :
    ∃ (N0 : ℕ) (Cthr Cdet : ℝ), 1 ≤ N0 ∧ (d : ℝ) * (4 / 5 : ℝ) ^ (2 * N0) < 1 ∧ 1 ≤ Cthr ∧ 1 ≤ Cdet ∧
      ∀ {y : Vec d} {l m : ℕ}, l + 5 ≤ m →
      ∀ {a : CoeffField d} {nu σ σ' δ Lam a1 a2 F : ℝ},
        0 < nu → 0 < σ → σ / 2 ≤ σ' → σ' ≤ 2 * σ → 0 < δ → 0 ≤ F → 0 ≤ a1 → 0 ≤ a2 →
        a1 ≤ CF * δ * Real.sqrt σ * Real.sqrt nu →
        IsEllipticFieldOn nu Lam (shiftCube y (m : ℤ)) a →
        ∀ (u : H1Function (shiftCube y (m : ℤ))) {f : Vec d → ℝ}, Measurable f →
        (∀ x, |f x| ≤ F) →
        IsWeakSolutionOn a (shiftCube y (m : ℤ)) u f (fun _ => 0) →
        (∀ (η : Vec d → ℝ) (A : ℝ) (L : NNReal), (∀ w, |η w| ≤ A) → LipschitzWith L η →
          (∀ w, (∃ i, 1 < |w i|) → η w = 0) →
          ∀ j : Fin d → ℤ, dist (y + l2b_pt l j) y ≤ (3 : ℝ) ^ m / 4 + 3 ^ l →
            ∀ x ∈ l2b_cell (y + l2b_pt l j) l,
              ‖a16_mollify d ((3 : ℝ) ^ l) η
                  (fun w => matVecMul (a w - σ • (1 : Mat d)) (u.grad w)) x‖ ≤
                3 ^ d * (6 * (L : ℝ) + A) *
                  (a1 * lipGradL2 (shiftCube (y + l2b_pt l j) ((l + 1 : ℕ) : ℤ)) u.grad +
                    a2 * F)) →
        (∀ j : Fin d → ℤ, dist (y + l2b_pt l j) y ≤ (3 : ℝ) ^ m / 4 + 3 ^ l →
          Real.sqrt nu / Real.sqrt σ' *
              lipGradL2 (shiftCube (y + l2b_pt l j) ((l + 1 : ℕ) : ℤ)) u.grad ≤
            Clip * (((3 : ℝ) ^ (m - 1))⁻¹ * h1_l2 (h1_cube (y + l2b_pt l j) (m - 1)) u.toFun) +
              Clip * (σ'⁻¹ * (3 : ℝ) ^ (m - 1) * F)) →
        (∀ j : Fin d → ℤ, dist (y + l2b_pt l j) y ≤ (3 : ℝ) ^ m / 4 + 3 ^ l →
          ((3 : ℝ) ^ (l + 3))⁻¹ * h1_l2 (h1_cube (y + l2b_pt l j) (l + 3)) u.toFun ≤
            Clip * (((3 : ℝ) ^ (m - 1))⁻¹ * h1_l2 (h1_cube (y + l2b_pt l j) (m - 1)) u.toFun) +
              Clip * (σ'⁻¹ * (3 : ℝ) ^ (m - 1) * F)) →
        Cthr * a2 ≤ δ * 3 ^ m → Cthr * 3 ^ l ≤ δ * 3 ^ m →
        Cthr * (Lam / nu) ^ deGiorgiPower d *
          ((3 : ℝ) ^ l / 3 ^ m + σ / nu * ((3 : ℝ) ^ l / 3 ^ m) ^ 2) ≤ δ →
        ∃ uhom : H1Function (ia_V d N0 m y),
          IsWeakSolutionOn (fun _ => σ • (1 : Mat d)) (ia_V d N0 m y) uhom f (fun _ => 0) ∧
          eLpNorm (fun x => u.toFun x - uhom.toFun x) ⊤ (volume.restrict (ia_V d N0 m y)) ≤
            ENNReal.ofReal (Cdet * δ *
              (h1_l2 (h1_cube y m) u.toFun + σ⁻¹ * (3 : ℝ) ^ (2 * m) * F)) := by
  obtain ⟨N0, r0, M1, M2, D0, hN0, hdim, hr0, hfam⟩ := ia_uniform_family (d := d)
  obtain ⟨Cc, hCc, Hcore⟩ := ia_core hd M1 (r0 * M2) (D0 / r0)
  obtain ⟨CDG, hCDG, Hmb⟩ := ip_moll_bound hd
  obtain ⟨η, hη, hη0, hη1, hηs, A, L, hA, hL⟩ := ip_profile d
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  set Kd : ℝ := 3 ^ d * (6 * (L : ℝ) + A) with hKd
  have hKd0 : 0 ≤ Kd := by positivity
  set s3 : ℝ := Real.sqrt ((3 : ℝ) ^ d) with hs3
  have hs30 : 0 ≤ s3 := Real.sqrt_nonneg _
  have hdd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  refine ⟨N0, 1 + Kd + CDG * (81 * Clip * s3 + 18 * Clip + 729),
    3 + Cc * (Kd + 1) * (3 * (s3 + 1) * CF * Clip + 1) + Cc * d * Real.sqrt d, hN0, hdim,
    by have : 0 ≤ CDG * (81 * Clip * s3 + 18 * Clip + 729) := by positivity
       linarith only [this, hKd0],
    by have : 0 ≤ Cc * (Kd + 1) * (3 * (s3 + 1) * CF * Clip + 1) := by positivity
       have : 0 ≤ Cc * d * Real.sqrt d := by positivity
       linarith only [‹0 ≤ Cc * (Kd + 1) * (3 * (s3 + 1) * CF * Clip + 1)›, this], ?_⟩
  intro y l m hml a nu σ σ' δ Lam a1 a2 F hnu hσ hσ'1 hσ'2 hδ hF ha1 ha2 ha1b hEll u f hfm hfb hu
    HFlux HL1 HL2 hN1 hN2 hN3
  have hhml : 1 ≤ m := by omega
  set V := ia_V d N0 m y with hVdef
  have hV : V ⊆ Metric.ball y ((3 : ℝ) ^ m / 4) := ia_V_subset_ball hN0 m y
  have hVo : IsOpen V := ia_V_isOpen m y
  have hT0 : (0 : ℝ) < 3 ^ m := by positivity
  have ht0 : (0 : ℝ) < 3 ^ l := by positivity
  have hgap := ip_pow_gap hml
  have hQo : IsOpen (shiftCube y (m : ℤ)) := rc_isOpen_shiftCube y _
  have hQb : Bornology.IsBounded (shiftCube y (m : ℤ)) := by
    rw [ip_shiftCube_ball]; exact Metric.isBounded_ball
  have hVQ : V ⊆ shiftCube y (m : ℤ) := by
    rw [ip_shiftCube_ball]
    exact hV.trans (Metric.ball_subset_ball (by linarith only [hT0]))
  have hVL : V ⊆ axisCube (fun i => y i - (3 : ℝ) ^ m / 4) ((3 : ℝ) ^ m / 2) := by
    intro x hx i _
    have h1 := hV hx
    rw [Metric.mem_ball, dist_pi_lt_iff (by positivity)] at h1
    have := h1 i
    rw [Real.dist_eq, abs_lt] at this
    simp only [Set.mem_Ioo]
    constructor <;> linarith only [this.1, this.2]
  have hmarg := ip_marg (d := d) hml hV
  have hσ'0 : 0 < σ' := by linarith only [hσ'1, hσ]
  -- the homogenized solution
  obtain ⟨uhom, hhom, hw⟩ := ia_exists_uhom hQo hQb hVo hVQ ht0 hη hηs
    (by positivity : (0 : ℝ) < 3 ^ m / 16) hmarg u hfm (Fs := F) (fun x _ => hfb x) hσ
  refine ⟨uhom, hhom, ?_⟩
  -- the flux bound
  set Om : ℝ := h1_l2 (h1_cube y m) u.toFun with hOm
  have hOm0 : 0 ≤ Om := Real.sqrt_nonneg _
  set Estar : ℝ := Real.sqrt σ' / Real.sqrt nu *
    (Clip * (((3 : ℝ) ^ (m - 1))⁻¹ * (s3 * Om)) + Clip * (σ'⁻¹ * (3 : ℝ) ^ (m - 1) * F)) with hEstar
  have hB : ∀ x ∈ V, ‖a16_mollify d ((3 : ℝ) ^ l) η
      (fun w => matVecMul (a w - σ • (1 : Mat d)) (u.grad w)) x‖ ≤ Kd * (a1 * Estar + a2 * F) := by
    intro x hx
    exact ip_flux_sup (u := u) hml hnu hσ'0 hKd0 ha1 (Clip := Clip) (F := F) (a1 := a1) (a2 := a2)
      (G := fun x => a16_mollify d ((3 : ℝ) ^ l) η
        (fun w => matVecMul (a w - σ • (1 : Mat d)) (u.grad w)) x)
      (HFlux η A L hA hL hηs) HL1 (by linarith only [hClip]) x (Metric.mem_ball.1 (hV hx))
  -- the core estimate
  have hfi : IntegrableOn f (shiftCube y (m : ℤ)) := by
    refine Measure.integrableOn_of_bounded (M := F) ?_ hfm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hfb x)
    exact hQb.measure_lt_top.ne
  have hfl : LocallyIntegrableOn f (shiftCube y (m : ℤ)) volume := hfi.locallyIntegrableOn
  have hFl : ∀ i, LocallyIntegrableOn (fun x => matVecMul (a x) (u.grad x) i) (shiftCube y (m : ℤ))
      volume := fun i =>
    locallyIntegrableOn_of_locallyIntegrable_restrict
      ((memLp_pi_iff.1 (memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.grad_memVectorL2) i).locallyIntegrable (by norm_num))
  have hκ : (3 : ℝ) ^ m / 4 * r0 * (M2 / ((3 : ℝ) ^ m / 4)) ≤ r0 * M2 :=
    le_of_eq (by field_simp)
  have hρ' : (3 : ℝ) ^ m / 4 * D0 ≤ D0 / r0 * ((3 : ℝ) ^ m / 4 * r0) :=
    le_of_eq (by field_simp)
  have hcore := Hcore (Q := shiftCube y (m : ℤ)) (V := V) (r := (3 : ℝ) ^ m / 4 * r0)
    (M₂ := M2 / ((3 : ℝ) ^ m / 4)) (D := (3 : ℝ) ^ m / 4 * D0)
    (z := fun i => y i - (3 : ℝ) ^ m / 4) (L := (3 : ℝ) ^ m / 2) hQo hQb (hfam m y) hκ hρ'
    (by positivity) hVL hVQ ht0 hη hη0 hη1 hηs (by positivity : (0 : ℝ) < 3 ^ m / 16) hmarg hσ hFl
    hfl hfm hF (fun x _ => hfb x) hu uhom hhom hw hB
  -- real bounds
  set R : ℝ := Om + σ⁻¹ * (3 : ℝ) ^ (2 * m) * F with hR
  have hpow2 : (3 : ℝ) ^ (2 * m) = ((3 : ℝ) ^ m) ^ 2 := by rw [mul_comm, pow_mul]
  have hR0 : 0 ≤ R := by positivity
  have hT1 : (3 : ℝ) ^ m = 3 * 3 ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hCthr1 : 1 ≤ 1 + Kd + CDG * (81 * Clip * s3 + 18 * Clip + 729) := by
    have : 0 ≤ CDG * (81 * Clip * s3 + 18 * Clip + 729) := by positivity
    linarith only [this, hKd0]
  have hKdC : Kd ≤ 1 + Kd + CDG * (81 * Clip * s3 + 18 * Clip + 729) := by
    have : 0 ≤ CDG * (81 * Clip * s3 + 18 * Clip + 729) := by positivity
    linarith only [this]
  have hN1' : Kd * a2 ≤ δ * (3 * 3 ^ (m - 1)) := by
    rw [← hT1]
    exact (mul_le_mul_of_nonneg_right hKdC ha2).trans hN1
  have halg := ip_alg_flux (T1 := (3 : ℝ) ^ (m - 1)) (s3 := s3) (Om := Om) (F := F) (σ := σ)
    (σ' := σ') (ν := nu) (δ := δ) (CF := CF) (Clip := Clip) (a1 := a1) (a2 := a2) (Kd := Kd)
    (by positivity) hs30 hOm0 hF hσ hσ'1 hσ'2 hnu hδ (by linarith only [hCF]) (by linarith only [hClip])
    ha1b hKd0 hN1'
  have hBnn : 0 ≤ Kd * (a1 * Estar + a2 * F) := by positivity
  have hX2 : 0 ≤ σ⁻¹ * (F * (Real.sqrt d * (3 : ℝ) ^ l) * d) := by positivity
  have hl3 : (3 : ℝ) ^ l ≤ δ * 3 ^ m := by
    have : (1 : ℝ) * 3 ^ l ≤ (1 + Kd + CDG * (81 * Clip * s3 + 18 * Clip + 729)) * 3 ^ l :=
      mul_le_mul_of_nonneg_right hCthr1 ht0.le
    linarith only [this, hN2]
  have hb2 : (3 : ℝ) ^ m / 2 * (σ⁻¹ * (F * (Real.sqrt d * (3 : ℝ) ^ l) * d)) ≤
      d * Real.sqrt d * δ * R := by
    have h1 : (3 : ℝ) ^ m / 2 * (σ⁻¹ * (F * (Real.sqrt d * (3 : ℝ) ^ l) * d)) ≤
        (3 : ℝ) ^ m / 2 * (σ⁻¹ * (F * (Real.sqrt d * (δ * 3 ^ m)) * d)) := by gcongr
    refine h1.trans ?_
    have e : (3 : ℝ) ^ m / 2 * (σ⁻¹ * (F * (Real.sqrt d * (δ * 3 ^ m)) * d)) =
        (d * Real.sqrt d / 2 * δ) * (σ⁻¹ * ((3 : ℝ) ^ m) ^ 2 * F) := by ring
    rw [e]
    have : σ⁻¹ * ((3 : ℝ) ^ m) ^ 2 * F ≤ R := by
      rw [hR, hpow2]; linarith only [hOm0]
    have h0 : 0 ≤ (d : ℝ) * Real.sqrt d * δ := by positivity
    nlinarith only [this, h0, mul_nonneg h0 (by positivity : (0 : ℝ) ≤ σ⁻¹ * ((3 : ℝ) ^ m) ^ 2 * F)]
  have hb1 : (3 : ℝ) ^ m / 2 * (Kd * (a1 * Estar + a2 * F) / σ) ≤
      (Kd + 1) * (3 * (s3 + 1) * CF * Clip + 1) * δ * R := by
    have e : (3 : ℝ) ^ m / 2 * (Kd * (a1 * Estar + a2 * F) / σ) =
        (3 ^ m / 2) * (Kd * (a1 * Estar + a2 * F)) / σ := by ring
    rw [e]
    have := halg
    rw [← hT1] at this
    rw [hR, hpow2]
    exact this
  -- the mollification error
  have hT2j : ∀ j : Fin d → ℤ, dist (y + l2b_pt l j) y ≤ (3 : ℝ) ^ m / 4 + 3 ^ l →
      h1_l2 (h1_cube (y + l2b_pt l j) (l + 3)) u.toFun ≤
        (81 * Clip * s3 + 18 * Clip) * ((3 : ℝ) ^ l / 3 ^ m) *
          (Om + σ⁻¹ * ((3 : ℝ) ^ m) ^ 2 * F) := by
    intro j hj
    have hOz := ip_osc_pred hml hj (v := u.toFun) (by rw [← hr_shiftCube_eq]; exact u.memL2)
    have h := HL2 j hj
    have e1 : (3 : ℝ) ^ (l + 3) = 27 * 3 ^ l := by rw [pow_add]; norm_num; ring
    have e2 : (3 : ℝ) ^ (m - 1) = 3 ^ m / 3 := by rw [hT1]; ring
    rw [e1, e2] at h
    exact ip_alg_T2 ht0 hT0 hσ hσ'1 hF (by linarith only [hClip]) hs30 hOm0 hOz h
  have hmb := Hmb hml hnu hF hEll u hfm hfb hu hT2j hη.continuous hη0 hη1 hηs hVo.measurableSet hV
  have he729 : (3 : ℝ) ^ (2 * (l + 3)) = 729 * ((3 : ℝ) ^ l) ^ 2 := by ring
  have hS := ip_alg_S (CDG := CDG) (Lt := (Lam / nu) ^ deGiorgiPower d) (Clip := Clip) (s3 := s3)
    (σ := σ) (ν := nu) (T := (3 : ℝ) ^ m) (t := (3 : ℝ) ^ l) (Om := Om) (F := F) (δ := δ)
    (Cthr := 1 + Kd + CDG * (81 * Clip * s3 + 18 * Clip + 729))
    (T2 := (81 * Clip * s3 + 18 * Clip) * ((3 : ℝ) ^ l / 3 ^ m) *
      (Om + σ⁻¹ * ((3 : ℝ) ^ m) ^ 2 * F)) hCDG.le
    (by
      obtain ⟨-, hle, -, -⟩ := hEll.2 y (rc_mem_shiftCube_self y _)
      exact Real.rpow_nonneg (div_nonneg (hnu.le.trans hle) hnu.le) _)
    ht0 hT0 hσ hnu hF (by linarith only [hClip]) hs30 hOm0 le_rfl hN3 (by linarith only [hKd0])
  have hae1 : ∀ᵐ x ∂(volume.restrict V),
      |u.toFun x - l2a_moll d ((3 : ℝ) ^ l) η u.toFun x| ≤ 2 * (δ * R) := by
    filter_upwards [hmb] with x hx
    refine hx.trans ?_
    rw [he729]
    have : (3 : ℝ) ^ (2 * m) = ((3 : ℝ) ^ m) ^ 2 := hpow2
    rw [hR, this]
    linarith only [hS]
  have hcore' := hcore
  rw [← ENNReal.ofReal_add (div_nonneg hBnn hσ.le) hX2, ← ENNReal.ofReal_mul (by positivity)] at hcore'
  have hnn1 : 0 ≤ Cc * ((3 : ℝ) ^ m / 2) * (Kd * (a1 * Estar + a2 * F) / σ +
      σ⁻¹ * (F * (Real.sqrt d * (3 : ℝ) ^ l) * d)) := by positivity
  have hae2 := ip_ae_of_eLpNorm hnn1 hcore'
  have hb12 : Cc * ((3 : ℝ) ^ m / 2) * (Kd * (a1 * Estar + a2 * F) / σ +
      σ⁻¹ * (F * (Real.sqrt d * (3 : ℝ) ^ l) * d)) ≤
      (Cc * (Kd + 1) * (3 * (s3 + 1) * CF * Clip + 1) + Cc * d * Real.sqrt d) * δ * R := by
    have e : Cc * ((3 : ℝ) ^ m / 2) * (Kd * (a1 * Estar + a2 * F) / σ +
        σ⁻¹ * (F * (Real.sqrt d * (3 : ℝ) ^ l) * d)) =
        Cc * ((3 : ℝ) ^ m / 2 * (Kd * (a1 * Estar + a2 * F) / σ)) +
          Cc * ((3 : ℝ) ^ m / 2 * (σ⁻¹ * (F * (Real.sqrt d * (3 : ℝ) ^ l) * d))) := by ring
    rw [e]
    have := add_le_add (mul_le_mul_of_nonneg_left hb1 hCc.le) (mul_le_mul_of_nonneg_left hb2 hCc.le)
    refine this.trans (le_of_eq ?_)
    ring
  have hmeas : AEStronglyMeasurable (fun x => u.toFun x - uhom.toFun x) (volume.restrict V) :=
    (u.memL2.aestronglyMeasurable.mono_measure (Measure.restrict_mono hVQ le_rfl)).sub
      uhom.memL2.aestronglyMeasurable
  rw [eLpNorm_exponent_top hmeas]
  refine eLpNormEssSup_le_of_ae_bound (C := (3 + Cc * (Kd + 1) * (3 * (s3 + 1) * CF * Clip + 1) +
    Cc * d * Real.sqrt d) * δ * R) ?_
  filter_upwards [hae1, hae2] with x h1 h2
  rw [Real.norm_eq_abs]
  have e : u.toFun x - uhom.toFun x = (u.toFun x - l2a_moll d ((3 : ℝ) ^ l) η u.toFun x) +
      (l2a_moll d ((3 : ℝ) ^ l) η u.toFun x - uhom.toFun x) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_sub_comm (l2a_moll d ((3 : ℝ) ^ l) η u.toFun x) (uhom.toFun x)]
  have hδR : 0 ≤ δ * R := by positivity
  nlinarith only [h1, h2, hb12, hδR]


theorem ip_rpow_neg_nat (l : ℕ) : (3 : ℝ) ^ (-(l : ℝ)) = ((3 : ℝ) ^ l)⁻¹ := by
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]

/-- The normalized oscillation, in real terms. -/
theorem ip_lpBar_osc {z : Vec d} {l : ℕ} {v : Vec d → ℝ} (hv : MemLp v 2 (volume.restrict (h1_cube z l))) :
    lpBar (shiftCube z (l : ℤ)) 2 (fun x => v x - ⨍ w in shiftCube z (l : ℤ), v w) =
      ENNReal.ofReal (h1_l2 (h1_cube z l) v) := by
  rw [hr_shiftCube_eq, hr_avg_eq]
  exact hr_lpBar_eq (h1_vol_cube_ne_top z l) (h1_vol_cube_pos z l) hv

/-- **The Lipschitz estimate on a translated cube, in real form.** -/
theorem ip_lip_real {z : Vec d} {lh m' : ℕ} (hlm : lh ≤ m') {u : H1Function (shiftCube z (m' : ℤ))}
    {f : Vec d → ℝ} {F C nu σ' : ℝ} (hF : 0 ≤ F) (hC : 0 ≤ C) (hnu : 0 < nu) (hσ' : 0 < σ')
    (hfF : eLpNorm f ⊤ (volume.restrict (shiftCube z (m' : ℤ))) ≤ ENNReal.ofReal F)
    (h : ENNReal.ofReal ((Real.sqrt σ')⁻¹ * Real.sqrt nu) *
          lpBar (shiftCube z (lh : ℤ)) 2 (fun x => eucNorm (u.grad x)) +
        ENNReal.ofReal ((3 : ℝ) ^ (-(lh : ℝ))) *
          lpBar (shiftCube z (lh : ℤ)) 2 (fun x => u.toFun x - ⨍ w in shiftCube z (lh : ℤ), u.toFun w) ≤
      ENNReal.ofReal (C * (3 : ℝ) ^ (-(m' : ℝ))) *
          lpBar (shiftCube z (m' : ℤ)) 2 (fun x => u.toFun x - ⨍ w in shiftCube z (m' : ℤ), u.toFun w) +
        ENNReal.ofReal (C * σ'⁻¹ * (3 : ℝ) ^ m') *
          eLpNorm f ⊤ (volume.restrict (shiftCube z (m' : ℤ)))) :
    Real.sqrt nu / Real.sqrt σ' * lipGradL2 (shiftCube z (lh : ℤ)) u.grad ≤
        C * (((3 : ℝ) ^ m')⁻¹ * h1_l2 (h1_cube z m') u.toFun) + C * (σ'⁻¹ * (3 : ℝ) ^ m' * F) ∧
      ((3 : ℝ) ^ lh)⁻¹ * h1_l2 (h1_cube z lh) u.toFun ≤
        C * (((3 : ℝ) ^ m')⁻¹ * h1_l2 (h1_cube z m') u.toFun) + C * (σ'⁻¹ * (3 : ℝ) ^ m' * F) := by
  have hsub : shiftCube z (lh : ℤ) ⊆ shiftCube z (m' : ℤ) := by
    rw [ip_shiftCube_ball, ip_shiftCube_ball]
    exact Metric.ball_subset_ball (by
      have : (3 : ℝ) ^ lh ≤ 3 ^ m' := pow_le_pow_right₀ (by norm_num) hlm
      linarith only [this])
  have hum : MemLp u.toFun 2 (volume.restrict (shiftCube z (m' : ℤ))) := u.memL2
  have hum' : MemLp u.toFun 2 (volume.restrict (h1_cube z m')) := by rw [← hr_shiftCube_eq]; exact hum
  have hul' : MemLp u.toFun 2 (volume.restrict (h1_cube z lh)) := by
    rw [← hr_shiftCube_eq]; exact hum.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hmem : MemLp (fun x => eucNorm (u.grad x)) 2 (volume.restrict (shiftCube z (lh : ℤ))) :=
    (memLp_eucNorm_grad u).mono_measure (Measure.restrict_mono hsub le_rfl)
  have hne : lpBar (shiftCube z (lh : ℤ)) 2 (fun x => eucNorm (u.grad x)) ≠ ⊤ :=
    lip_lpBar_ne_top (ip_volume_shiftCube_ne z lh).1 hmem
  have e2 : ENNReal.ofReal (lipGradL2 (shiftCube z (lh : ℤ)) u.grad) =
      lpBar (shiftCube z (lh : ℤ)) 2 (fun x => eucNorm (u.grad x)) := ENNReal.ofReal_toReal hne
  rw [← e2, ip_lpBar_osc hul', ip_lpBar_osc hum', ip_rpow_neg_nat, ip_rpow_neg_nat] at h
  have hr : ENNReal.ofReal (C * ((3 : ℝ) ^ m')⁻¹) * ENNReal.ofReal (h1_l2 (h1_cube z m') u.toFun) +
      ENNReal.ofReal (C * σ'⁻¹ * (3 : ℝ) ^ m') * eLpNorm f ⊤ (volume.restrict (shiftCube z (m' : ℤ))) ≤
      ENNReal.ofReal (C * (((3 : ℝ) ^ m')⁻¹ * h1_l2 (h1_cube z m') u.toFun) +
        C * (σ'⁻¹ * (3 : ℝ) ^ m' * F)) := by
    have hl0 : 0 ≤ h1_l2 (h1_cube z m') u.toFun := Real.sqrt_nonneg _
    have h1 : 0 ≤ C * ((3 : ℝ) ^ m')⁻¹ * h1_l2 (h1_cube z m') u.toFun := by positivity
    have h2 : 0 ≤ C * σ'⁻¹ * (3 : ℝ) ^ m' * F := by positivity
    have e : C * (((3 : ℝ) ^ m')⁻¹ * h1_l2 (h1_cube z m') u.toFun) +
        C * (σ'⁻¹ * (3 : ℝ) ^ m' * F) =
        C * ((3 : ℝ) ^ m')⁻¹ * h1_l2 (h1_cube z m') u.toFun + C * σ'⁻¹ * (3 : ℝ) ^ m' * F := by ring
    rw [e, ENNReal.ofReal_add h1 h2]
    refine add_le_add ?_ ?_
    · rw [← ENNReal.ofReal_mul (by positivity)]
    · calc ENNReal.ofReal (C * σ'⁻¹ * (3 : ℝ) ^ m') *
            eLpNorm f ⊤ (volume.restrict (shiftCube z (m' : ℤ))) ≤
            ENNReal.ofReal (C * σ'⁻¹ * (3 : ℝ) ^ m') * ENNReal.ofReal F := by gcongr
        _ = ENNReal.ofReal (C * σ'⁻¹ * (3 : ℝ) ^ m' * F) := (ENNReal.ofReal_mul (by positivity)).symm
  have hh := h.trans hr
  have hl0m : 0 ≤ h1_l2 (h1_cube z m') u.toFun := Real.sqrt_nonneg _
  have hRnn : 0 ≤ C * (((3 : ℝ) ^ m')⁻¹ * h1_l2 (h1_cube z m') u.toFun) +
      C * (σ'⁻¹ * (3 : ℝ) ^ m' * F) := by positivity
  have hs : Real.sqrt nu / Real.sqrt σ' = (Real.sqrt σ')⁻¹ * Real.sqrt nu := by
    rw [div_eq_inv_mul]
  have hl0 : 0 ≤ lipGradL2 (shiftCube z (lh : ℤ)) u.grad := ENNReal.toReal_nonneg
  have hl1 : 0 ≤ h1_l2 (h1_cube z lh) u.toFun := Real.sqrt_nonneg _
  have hq0 : 0 ≤ (Real.sqrt σ')⁻¹ * Real.sqrt nu := by positivity
  have hq1 : 0 ≤ ((3 : ℝ) ^ lh)⁻¹ := by positivity
  constructor
  · have := le_trans le_self_add hh
    rw [← ENNReal.ofReal_mul hq0, ENNReal.ofReal_le_ofReal_iff hRnn] at this
    rw [hs]; exact this
  · have := le_trans le_add_self hh
    rw [← ENNReal.ofReal_mul hq1, ENNReal.ofReal_le_ofReal_iff hRnn] at this
    exact this

open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff (ShellSeq)


/-- **One scale for every centre of the grid.** -/
theorem ia_grid_scale (d : ℕ) [NeZero d] {N ρ : ℝ} (hN : 0 ≤ N) (hρ : 0 < ρ) (A : ℕ) :
    ∃ Lfun : ℝ → ℝ, (∀ L : ℝ, 1 ≤ L → L ≤ Lfun L ∧ 1 ≤ Lfun L) ∧
      ∀ (P : ProbabilityMeasure (ShellSeq d)) (_ : ShellLawPrefix d P) (_ : ShellLawJ2 d P)
        (X0 : ShellSeq d → ℝ), Measurable X0 → ∀ Lh0 : ℝ, 1 ≤ Lh0 →
        Homogenization.IndependentSums.IsBigO P.toMeasure
          (Homogenization.IndependentSums.gammaSigma ρ) (fun ω => Real.log (X0 ω)) Lh0 →
        ∃ X : ShellSeq d → ℝ, Measurable X ∧ (∀ ω, 1 ≤ X ω) ∧
          Homogenization.IndependentSums.IsBigO P.toMeasure
            (Homogenization.IndependentSums.gammaSigma ρ) (fun ω => Real.log (X ω)) (Lfun Lh0) ∧
          ∀ᵐ ω ∂P.toMeasure, ∀ n : ℕ, Lfun Lh0 ≤ (nK N n : ℝ) → X ω ≤ (3 : ℝ) ^ nK N n →
            ∀ y ∈ gridPts d ((nK N n : ℤ) - 3) ((3 : ℝ) ^ (n + A)),
              X0 (ShellField.translateSequence y ω) ≤ (3 : ℝ) ^ nK N n := by
  obtain ⟨Cg, hCg, hG⟩ := b2_gridMax_scale d hN hρ A
  have hC1 := b2c_C1_nonneg N hN A
  have h3 := b2c_one_lt_log3
  have hexp : 1 ≤ Real.exp (A : ℝ) := Real.one_le_exp (Nat.cast_nonneg A)
  have hB : 0 ≤ (b2c_C1 N A + 3 * 1 + (b2c_n0 N : ℝ)) * Real.log 3 :=
    mul_nonneg (by linarith only [hC1, (Nat.cast_nonneg (b2c_n0 N) : (0 : ℝ) ≤ _)])
      (by linarith only [h3])
  have ha : 1 ≤ 1 + 4 * (1 : ℝ) * Real.log 3 := by linarith only [h3]
  refine ⟨fun Lh0 => (1 + 4 * (1 : ℝ) * Real.log 3) *
      max (Cg * Lh0 * (1 + Real.log Lh0) ^ ρ⁻¹) (Real.exp (A : ℝ)) +
      (b2c_C1 N A + 3 * 1 + (b2c_n0 N : ℝ)) * Real.log 3, ?_, ?_⟩
  · intro L hL
    have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL
    have hpow : 1 ≤ (1 + Real.log L) ^ ρ⁻¹ :=
      Real.one_le_rpow (by linarith only [hlogL]) (inv_nonneg.2 hρ.le)
    have hLam1 : L ≤ max (Cg * L * (1 + Real.log L) ^ ρ⁻¹) (Real.exp (A : ℝ)) := by
      refine le_trans ?_ (le_max_left _ _)
      calc L = 1 * L * 1 := by ring
        _ ≤ Cg * L * (1 + Real.log L) ^ ρ⁻¹ := by gcongr
    have hLam1' : 1 ≤ max (Cg * L * (1 + Real.log L) ^ ρ⁻¹) (Real.exp (A : ℝ)) :=
      le_trans hexp (le_max_right _ _)
    set Lam := max (Cg * L * (1 + Real.log L) ^ ρ⁻¹) (Real.exp (A : ℝ))
    constructor
    · nlinarith only [ha, hB, hLam1, hLam1']
    · nlinarith only [ha, hB, hLam1']
  · intro P hPrefix hJ2 X0 hX0m Lh0 hLh0 hX0O
    obtain ⟨Xs, hXs, hXs1, hXsO, hXsae⟩ := hG P hPrefix hJ2 X0 hX0m Lh0 hLh0 hX0O
    have hlogL : 0 ≤ Real.log Lh0 := Real.log_nonneg hLh0
    have hpow : 1 ≤ (1 + Real.log Lh0) ^ ρ⁻¹ :=
      Real.one_le_rpow (by linarith only [hlogL]) (inv_nonneg.2 hρ.le)
    have hLam1 : Lh0 ≤ max (Cg * Lh0 * (1 + Real.log Lh0) ^ ρ⁻¹) (Real.exp (A : ℝ)) := by
      refine le_trans ?_ (le_max_left _ _)
      calc Lh0 = 1 * Lh0 * 1 := by ring
        _ ≤ Cg * Lh0 * (1 + Real.log Lh0) ^ ρ⁻¹ := by gcongr
    have hLam1' : 1 ≤ max (Cg * Lh0 * (1 + Real.log Lh0) ^ ρ⁻¹) (Real.exp (A : ℝ)) :=
      le_trans hexp (le_max_right _ _)
    set Lam := max (Cg * Lh0 * (1 + Real.log Lh0) ^ ρ⁻¹) (Real.exp (A : ℝ)) with hLam
    have hLhat : Lam ≤ (1 + 4 * (1 : ℝ) * Real.log 3) * Lam +
        (b2c_C1 N A + 3 * 1 + (b2c_n0 N : ℝ)) * Real.log 3 := by nlinarith only [ha, hB, hLam1']
    refine ⟨fun omega => b2c_enl 1 (b2c_C1 N A) (b2c_n0 N) (Xs omega),
      b2c_enl_measurable hXs _ _ _, fun omega => b2c_enl_ge_one _ _ _ _, ?_, ?_⟩
    · exact b2c_enl_isBigO (μ := P.toMeasure) (κ := 1) (C := b2c_C1 N A) zero_le_one hC1
        (b2c_n0 N) hXs1 hXsO
    · filter_upwards [hXsae] with omega hsω
      intro n hLn hXn y hy
      obtain ⟨-, hXsn⟩ := b2c_enl_spec hN A n hXn
      have hnK : (nK N n : ℝ) ≤ n := by exact_mod_cast nK_le N n
      have hLamn : Lam ≤ (n : ℝ) := le_trans (le_trans hLhat hLn) hnK
      exact hsω n hLamn hXsn y hy

/-- **The maximum of two random scales.** -/
theorem ia_max_scale {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ Cm : ℝ, 1 ≤ Cm ∧ ∀ {Ω : Type _} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
      {X Y : Ω → ℝ} {A B : ℝ}, 0 ≤ A → 0 ≤ B → (∀ ω, 1 ≤ X ω) → (∀ ω, 1 ≤ Y ω) →
      Homogenization.IndependentSums.IsBigO μ (Homogenization.IndependentSums.gammaSigma ρ)
        (fun ω => Real.log (X ω)) A →
      Homogenization.IndependentSums.IsBigO μ (Homogenization.IndependentSums.gammaSigma ρ)
        (fun ω => Real.log (Y ω)) B →
      Homogenization.IndependentSums.IsBigO μ (Homogenization.IndependentSums.gammaSigma ρ)
        (fun ω => Real.log (max (X ω) (Y ω))) (Cm * (A + B)) := by
  obtain ⟨C, hC, H⟩ := Section6.exists_isBigO_gammaSigma_max_two_add hρ
  refine ⟨max C 1, le_max_right _ _, ?_⟩
  intro Ω _ μ _ X Y A B hA hB hX hY hXO hYO
  have h := H hA hB hXO hYO
  have e : (fun ω => Real.log (max (X ω) (Y ω))) = fun ω => max (Real.log (X ω)) (Real.log (Y ω)) := by
    funext ω
    rcases le_total (X ω) (Y ω) with h1 | h1
    · rw [max_eq_right h1, max_eq_right (Real.log_le_log (by linarith only [hX ω]) h1)]
    · rw [max_eq_left h1, max_eq_left (Real.log_le_log (by linarith only [hY ω]) h1)]
  rw [e]
  refine h.mono_scale ?_
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith only [hA, hB])

/-- **The Lipschitz estimate on `z + □_{k-1}`, in real form, for the restriction of a solution on
`y + □_k`.** -/
theorem ia_lipz {z : Vec d} {k lh : ℕ} {W : Set (Vec d)}
    (hsubz : shiftCube z ((k - 1 : ℕ) : ℤ) ⊆ W) (hlm : lh ≤ k - 1) (hW0 : IsOpen (shiftCube z ((k - 1 : ℕ) : ℤ)))
    (u : H1Function W) {f : Vec d → ℝ} (hfin : eLpNorm f ⊤ (volume.restrict W) ≠ ⊤) {CL nu σ' : ℝ}
    (hCL : 0 ≤ CL) (hnu : 0 < nu) (hσ' : 0 < σ')
    (h : ENNReal.ofReal ((Real.sqrt σ')⁻¹ * Real.sqrt nu) *
          lpBar (shiftCube z (lh : ℤ)) 2 (fun x => eucNorm ((u.restrict hW0 hsubz).grad x)) +
        ENNReal.ofReal ((3 : ℝ) ^ (-(lh : ℝ))) *
          lpBar (shiftCube z (lh : ℤ)) 2 (fun x => (u.restrict hW0 hsubz).toFun x -
            ⨍ w in shiftCube z (lh : ℤ), (u.restrict hW0 hsubz).toFun w) ≤
      ENNReal.ofReal (CL * (3 : ℝ) ^ (-((k - 1 : ℕ) : ℝ))) *
          lpBar (shiftCube z ((k - 1 : ℕ) : ℤ)) 2 (fun x => (u.restrict hW0 hsubz).toFun x -
            ⨍ w in shiftCube z ((k - 1 : ℕ) : ℤ), (u.restrict hW0 hsubz).toFun w) +
        ENNReal.ofReal (CL * σ'⁻¹ * (3 : ℝ) ^ (k - 1)) *
          eLpNorm f ⊤ (volume.restrict (shiftCube z ((k - 1 : ℕ) : ℤ)))) :
    Real.sqrt nu / Real.sqrt σ' * lipGradL2 (shiftCube z (lh : ℤ)) u.grad ≤
        CL * (((3 : ℝ) ^ (k - 1))⁻¹ * h1_l2 (h1_cube z (k - 1)) u.toFun) +
          CL * (σ'⁻¹ * (3 : ℝ) ^ (k - 1) * (eLpNorm f ⊤ (volume.restrict W)).toReal) ∧
      ((3 : ℝ) ^ lh)⁻¹ * h1_l2 (h1_cube z lh) u.toFun ≤
        CL * (((3 : ℝ) ^ (k - 1))⁻¹ * h1_l2 (h1_cube z (k - 1)) u.toFun) +
          CL * (σ'⁻¹ * (3 : ℝ) ^ (k - 1) * (eLpNorm f ⊤ (volume.restrict W)).toReal) := by
  have hfF : eLpNorm f ⊤ (volume.restrict (shiftCube z ((k - 1 : ℕ) : ℤ))) ≤
      ENNReal.ofReal (eLpNorm f ⊤ (volume.restrict W)).toReal := by
    calc eLpNorm f ⊤ (volume.restrict (shiftCube z ((k - 1 : ℕ) : ℤ)))
        ≤ eLpNorm f ⊤ (volume.restrict W) := eLpNorm_mono_measure f (Measure.restrict_mono hsubz le_rfl)
      _ = ENNReal.ofReal (eLpNorm f ⊤ (volume.restrict W)).toReal := (ENNReal.ofReal_toReal hfin).symm
  have := ip_lip_real (z := z) (lh := lh) (m' := k - 1) hlm (u := u.restrict hW0 hsubz) (f := f)
    ENNReal.toReal_nonneg hCL hnu hσ' hfF h
  exact this

end SuperdiffusionCLT.Section7
