/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.CrudeMomentsLarge
public import SuperdiffusionCLT.Section8.Prereq.CrudeMomentsLargeB
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.Vanishing

/-!
# The localized tail of the rough split at every shift

For a rough split datum with logarithmic bounds the localized two-scale tail at shift `mu ≤ 1`
about a centre `x` with `|x| ≤ θ ρ` is bounded by the expression `crudeMomL_phi` of the absorption
inequality, with `t = 1 / mu`, `s = sqrt mu * ρ` and the logarithmic scale
`ℓ = 2 log (1 + θ) + log (K ^ 2 + t)`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization Homogenization.Book.Ch02 MeasureTheory Set
open SuperdiffusionCLT.Section8.DivergenceForm
open SuperdiffusionCLT.Section8.DivergenceForm.Decay
open SuperdiffusionCLT.Section8.Common.Regularity.Ported
open MarkovProcess.Semigroup

noncomputable section

section Coefficients

variable {d : ℕ}

theorem crudeMomL_l2Coefficient_scale (lam Lam : ℝ) :
    agmonTailL2Coefficient d lam Lam = agmonTailL2Coefficient d lam 1 * Lam := by
  unfold agmonTailL2Coefficient
  ring

theorem crudeMomL_gradientCoefficient_scale [NeZero d] (lam Lam alpha : ℝ) :
    agmonTailGradientCoefficient d lam Lam alpha =
      agmonTailGradientCoefficient d lam 1 alpha * Lam := by
  unfold agmonTailGradientCoefficient
  ring

theorem crudeMomL_rate_scale (lam alpha : ℝ) {Lam : ℝ} (hLam : 0 < Lam) :
    agmonTailRate d lam Lam alpha = agmonTailRate d lam 1 alpha / Lam := by
  unfold agmonTailRate
  field_simp

/-- The constant of the polynomial factor of the tail. -/
def crudeMomL_Cc (d : ℕ) [NeZero d] (nu : ℝ) : ℝ :=
  agmonTailL2Coefficient d nu 1 + agmonTailGradientCoefficient d nu 1 (1 / 2 : ℝ) +
    agmonTailForcingCoefficient d (1 / 2 : ℝ) / nu

/-- The constant bounding the effective upper constant by a power of the logarithm. -/
def crudeMomL_Lam1 (nu c0 : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt 2 * (nu + c0 * 2 ^ n)

/-- The decay constant of the tail. -/
def crudeMomL_r1 (d : ℕ) (nu : ℝ) : ℝ := agmonTailRate d nu 1 (1 / 2 : ℝ)

theorem crudeMomL_Cc_nonneg [NeZero d] {nu : ℝ} (hnu : 0 < nu) : 0 ≤ crudeMomL_Cc d nu := by
  unfold crudeMomL_Cc
  have h1 := agmonTailL2Coefficient_nonneg d (lam := nu) (Lam := 1) zero_le_one
  have h2 := agmonTailGradientCoefficient_nonneg d (lam := nu) (alpha := (1 / 2 : ℝ)) hnu zero_le_one
  have h3 := agmonTailForcingCoefficient_nonneg d (1 / 2 : ℝ)
  have h4 : 0 ≤ agmonTailForcingCoefficient d (1 / 2 : ℝ) / nu := div_nonneg h3 hnu.le
  linarith only [h1, h2, h4]

theorem crudeMomL_Lam1_pos {nu c0 : ℝ} (hnu : 0 < nu) (hc0 : 0 ≤ c0) (n : ℕ) :
    0 < crudeMomL_Lam1 nu c0 n := by
  unfold crudeMomL_Lam1
  have : 0 ≤ c0 * 2 ^ n := by positivity
  exact mul_pos (Real.sqrt_pos.2 (by norm_num)) (by linarith only [hnu, this])

theorem crudeMomL_r1_pos {nu : ℝ} (hnu : 0 < nu) : 0 < crudeMomL_r1 d nu := by
  unfold crudeMomL_r1 agmonTailRate
  positivity

end Coefficients

section Geometry

/-- The ratio of the outer scale to twice the clipped freezing scale lies between one and an
explicit polynomial of the observation scale. -/
theorem crudeMomL_q_bounds {amp nx θ ρ μ : ℝ} (hamp : 0 < amp) (hamp1 : amp ≤ 1)
    (hnx : 0 ≤ nx) (hθ : 0 ≤ θ) (hxθ : nx ≤ θ * ρ) (hρ : 0 < ρ) (hμ : 0 < μ) (hμ1 : μ ≤ 1) :
    1 ≤ (Real.sqrt μ * ρ) / (2 * (Real.sqrt μ * min (amp / (1 + nx)) (ρ / 2))) ∧
      (Real.sqrt μ * ρ) / (2 * (Real.sqrt μ * min (amp / (1 + nx)) (ρ / 2))) ≤
        (1 + θ) / amp * μ⁻¹ * (1 + Real.sqrt μ * ρ) ^ 2 := by
  have hsm : 0 < Real.sqrt μ := Real.sqrt_pos.2 hμ
  have hsm1 : Real.sqrt μ ≤ 1 := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hμ1
  have hsq : Real.sqrt μ ^ 2 = μ := Real.sq_sqrt hμ.le
  have hnx1 : 0 < 1 + nx := by linarith only [hnx]
  have hR : 0 < min (amp / (1 + nx)) (ρ / 2) :=
    lt_min (div_pos hamp hnx1) (by linarith only [hρ])
  have hq : (Real.sqrt μ * ρ) / (2 * (Real.sqrt μ * min (amp / (1 + nx)) (ρ / 2))) =
      ρ / (2 * min (amp / (1 + nx)) (ρ / 2)) := by
    field_simp
  rw [hq]
  have hRle : min (amp / (1 + nx)) (ρ / 2) ≤ ρ / 2 := min_le_right _ _
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ (by positivity)]
    linarith only [hRle]
  · set B : ℝ := (1 + θ) / amp * μ⁻¹ * (1 + Real.sqrt μ * ρ) ^ 2 with hB
    have hB1 : 1 ≤ (1 + θ) * (1 + ρ) ^ 2 / amp := by
      rw [le_div_iff₀ hamp]
      nlinarith only [hamp1, hθ, hρ]
    have hstep : (1 + θ) * (1 + ρ) ^ 2 / amp ≤ B := by
      have h1 : (1 + ρ) ≤ (1 + Real.sqrt μ * ρ) / Real.sqrt μ := by
        rw [le_div_iff₀ hsm]
        nlinarith only [hsm1, hρ, hsm]
      have h2 : (1 + ρ) ^ 2 ≤ μ⁻¹ * (1 + Real.sqrt μ * ρ) ^ 2 := by
        calc (1 + ρ) ^ 2 ≤ ((1 + Real.sqrt μ * ρ) / Real.sqrt μ) ^ 2 :=
              pow_le_pow_left₀ (by positivity) h1 2
          _ = μ⁻¹ * (1 + Real.sqrt μ * ρ) ^ 2 := by
              rw [div_pow, hsq]; ring
      rw [hB]
      calc (1 + θ) * (1 + ρ) ^ 2 / amp = (1 + θ) / amp * (1 + ρ) ^ 2 := by ring
        _ ≤ (1 + θ) / amp * (μ⁻¹ * (1 + Real.sqrt μ * ρ) ^ 2) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = _ := by ring
    refine le_trans ?_ hstep
    rcases min_choice (amp / (1 + nx)) (ρ / 2) with h | h
    · rw [h, show ρ / (2 * (amp / (1 + nx))) = ρ * (1 + nx) / (2 * amp) by field_simp]
      rw [div_le_div_iff₀ (by positivity) hamp]
      have hx1 : 1 + nx ≤ 1 + θ * ρ := by linarith only [hxθ]
      have h1 : ρ * (1 + nx) ≤ (1 + θ) * (1 + ρ) ^ 2 := by
        nlinarith only [hx1, hρ, hθ, mul_nonneg hθ hρ.le, mul_nonneg (mul_nonneg hθ hρ.le) hρ.le]
      have h2 : (1 + θ) * (1 + ρ) ^ 2 * amp ≤ (1 + θ) * (1 + ρ) ^ 2 * (2 * amp) :=
        mul_le_mul_of_nonneg_left (by linarith only [hamp]) (by positivity)
      nlinarith only [mul_le_mul_of_nonneg_right h1 hamp.le, h2]
    · rw [h]
      have : ρ / (2 * (ρ / 2)) = 1 := by field_simp
      rw [this]
      exact hB1

end Geometry

section Frozen

variable {d : ℕ} [NeZero d]

/-- **The two-scale tail function of the freezing argument**, bounded by the polynomial factor
times the exponential with the rate `r₁ / Λ`. -/
theorem crudeMomL_frozen_le {nu Lam s s₀ : ℝ} (hnu : 0 < nu) (hLam : 0 < Lam) (hs : 1 ≤ s)
    (hs₀ : 0 < s₀) (hs₀s : 2 * s₀ ≤ s) :
    agmonTailFunctionFrozen d nu Lam nu (1 / 2 : ℝ) s s₀ ≤
      crudeMomL_Cc d nu * (Lam + s ^ 2) * (s / (2 * s₀)) ^ d *
        Real.exp (-(crudeMomL_r1 d nu * s / Lam)) := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hq1 : 1 ≤ s / (2 * s₀) := by
    rw [le_div_iff₀ (by positivity)]; linarith only [hs₀s]
  set q : ℝ := s / (2 * s₀) with hq
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq1
  have hqd : (1 : ℝ) ≤ q ^ d := one_le_pow₀ hq1
  have hqrp : ∀ e : ℝ, e ≤ d → q ^ e ≤ q ^ d := by
    intro e he
    calc q ^ e ≤ q ^ (d : ℝ) := Real.rpow_le_rpow_of_exponent_le hq1 he
      _ = q ^ d := Real.rpow_natCast q d
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hc1 := agmonTailL2Coefficient_nonneg d (lam := nu) (Lam := 1) zero_le_one
  have hc2 := agmonTailGradientCoefficient_nonneg d (lam := nu) (alpha := (1 / 2 : ℝ)) hnu zero_le_one
  have hc3 := agmonTailForcingCoefficient_nonneg d (1 / 2 : ℝ)
  unfold agmonTailFunctionFrozen
  rw [abs_of_pos hs0, abs_of_pos hs₀, crudeMomL_l2Coefficient_scale,
    crudeMomL_gradientCoefficient_scale, crudeMomL_rate_scale nu (1 / 2 : ℝ) hLam]
  rw [← hq]
  have hexp : agmonTailRate d nu 1 (1 / 2 : ℝ) / Lam * s = crudeMomL_r1 d nu * s / Lam := by
    unfold crudeMomL_r1; ring
  rw [hexp]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  have hA : agmonTailL2Coefficient d nu 1 * Lam / s * q ^ ((d : ℝ) / 2) ≤
      agmonTailL2Coefficient d nu 1 * Lam * q ^ d := by
    have : agmonTailL2Coefficient d nu 1 * Lam / s ≤ agmonTailL2Coefficient d nu 1 * Lam :=
      div_le_self (by positivity) hs
    exact (mul_le_mul_of_nonneg_right this (by positivity)).trans
      (mul_le_mul_of_nonneg_left (hqrp _ (by linarith only [hd0])) (by positivity))
  have hB : agmonTailGradientCoefficient d nu 1 (1 / 2 : ℝ) * Lam * q ^ ((d : ℝ) / 2 - 1) ≤
      agmonTailGradientCoefficient d nu 1 (1 / 2 : ℝ) * Lam * q ^ d :=
    mul_le_mul_of_nonneg_left (hqrp _ (by linarith only [hd0])) (by positivity)
  have hC : 4 * agmonTailForcingCoefficient d (1 / 2 : ℝ) * s₀ ^ 2 / nu ≤
      agmonTailForcingCoefficient d (1 / 2 : ℝ) / nu * s ^ 2 * q ^ d := by
    have h1 : 4 * s₀ ^ 2 ≤ s ^ 2 := by nlinarith only [hs₀s, hs₀]
    have h2 : 4 * agmonTailForcingCoefficient d (1 / 2 : ℝ) * s₀ ^ 2 / nu ≤
        agmonTailForcingCoefficient d (1 / 2 : ℝ) / nu * s ^ 2 := by
      rw [show 4 * agmonTailForcingCoefficient d (1 / 2 : ℝ) * s₀ ^ 2 / nu =
        agmonTailForcingCoefficient d (1 / 2 : ℝ) / nu * (4 * s₀ ^ 2) by ring]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    calc _ ≤ agmonTailForcingCoefficient d (1 / 2 : ℝ) / nu * s ^ 2 := h2
      _ = agmonTailForcingCoefficient d (1 / 2 : ℝ) / nu * s ^ 2 * 1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hqd (by positivity)
  unfold crudeMomL_Cc
  calc _ ≤ agmonTailL2Coefficient d nu 1 * Lam * q ^ d +
        agmonTailGradientCoefficient d nu 1 (1 / 2 : ℝ) * Lam * q ^ d +
        agmonTailForcingCoefficient d (1 / 2 : ℝ) / nu * s ^ 2 * q ^ d := by
        refine add_le_add (add_le_add hA ?_) hC
        exact hB
    _ ≤ agmonTailL2Coefficient d nu 1 * Lam * q ^ d +
        agmonTailGradientCoefficient d nu 1 (1 / 2 : ℝ) * Lam * q ^ d +
        agmonTailForcingCoefficient d (1 / 2 : ℝ) / nu * s ^ 2 * q ^ d +
        (agmonTailL2Coefficient d nu 1 * s ^ 2 + agmonTailGradientCoefficient d nu 1 (1 / 2 : ℝ) * s ^ 2 +
          agmonTailForcingCoefficient d (1 / 2 : ℝ) / nu * Lam) * q ^ d :=
        le_add_of_nonneg_right (by positivity)
    _ = _ := by ring

end Frozen

section LogScale

/-- The logarithmic scale of the observation radius. -/
def crudeMomL_ell (Kc θ t : ℝ) : ℝ := 2 * Real.log (1 + θ) + Real.log (Kc ^ 2 + t)

theorem crudeMomL_ell_ge {Kc θ t : ℝ} (hK : 2 ≤ Kc) (hθ : 0 ≤ θ) (ht : 1 ≤ t) :
    1 ≤ crudeMomL_ell Kc θ t ∧ Real.log t ≤ crudeMomL_ell Kc θ t := by
  have h1 := crudeMomL_one_le_log hK (show 0 ≤ t by linarith only [ht])
  have h2 : 0 ≤ Real.log (1 + θ) := Real.log_nonneg (by linarith only [hθ])
  have h3 : Real.log t ≤ Real.log (Kc ^ 2 + t) :=
    Real.log_le_log (by linarith only [ht]) (by nlinarith only [hK])
  unfold crudeMomL_ell
  constructor <;> linarith only [h1, h2, h3]

/-- The logarithm of the observation scale is at most the scale `ℓ` plus twice `log (1 + s)`. -/
theorem crudeMomL_log_obs_le {Kc θ ρ μ nx : ℝ} (hK : 2 ≤ Kc) (hθ : 0 ≤ θ) (hρ : 0 < ρ)
    (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hnx : 0 ≤ nx) (hxθ : nx ≤ θ * ρ) :
    Real.log (Kc ^ 2 + (nx + ρ) ^ 2) ≤
      crudeMomL_ell Kc θ μ⁻¹ + 2 * Real.log (1 + Real.sqrt μ * ρ) := by
  have hsm : 0 < Real.sqrt μ := Real.sqrt_pos.2 hμ
  have hsq : Real.sqrt μ ^ 2 = μ := Real.sq_sqrt hμ.le
  set s : ℝ := Real.sqrt μ * ρ with hs
  have hs0 : 0 ≤ s := by positivity
  have hρ2 : ρ ^ 2 = s ^ 2 * μ⁻¹ := by
    rw [hs, mul_pow, hsq]; field_simp
  have hμi : 1 ≤ μ⁻¹ := by rw [one_le_inv₀ hμ]; exact hμ1
  have hK2 : 0 ≤ Kc ^ 2 := sq_nonneg _
  have h1 : (nx + ρ) ^ 2 ≤ (1 + θ) ^ 2 * (s ^ 2 * μ⁻¹) := by
    rw [← hρ2, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith only [hxθ]) 2
  have hθ1 : 1 ≤ (1 + θ) ^ 2 := by nlinarith only [hθ]
  have h2 : Kc ^ 2 + (nx + ρ) ^ 2 ≤ (1 + θ) ^ 2 * (Kc ^ 2 + μ⁻¹) * (1 + s) ^ 2 := by
    have hμi0 : 0 ≤ μ⁻¹ := by linarith only [hμi]
    have h3 : Kc ^ 2 + s ^ 2 * μ⁻¹ ≤ (Kc ^ 2 + μ⁻¹) * (1 + s) ^ 2 := by
      nlinarith only [mul_nonneg hK2 hs0, mul_nonneg hK2 (sq_nonneg s), mul_nonneg hμi0 hs0,
        mul_nonneg hK2 (mul_nonneg hs0 hs0), hK2, hμi0, sq_nonneg s]
    calc Kc ^ 2 + (nx + ρ) ^ 2 ≤ Kc ^ 2 + (1 + θ) ^ 2 * (s ^ 2 * μ⁻¹) := by linarith only [h1]
      _ ≤ (1 + θ) ^ 2 * Kc ^ 2 + (1 + θ) ^ 2 * (s ^ 2 * μ⁻¹) := by nlinarith only [hθ1, hK2]
      _ = (1 + θ) ^ 2 * (Kc ^ 2 + s ^ 2 * μ⁻¹) := by ring
      _ ≤ (1 + θ) ^ 2 * ((Kc ^ 2 + μ⁻¹) * (1 + s) ^ 2) := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = _ := by ring
  have hpos : 0 < Kc ^ 2 + (nx + ρ) ^ 2 := by positivity
  have h4 := Real.log_le_log hpos h2
  have hθp : 0 < 1 + θ := by linarith only [hθ]
  have hKp : 0 < Kc ^ 2 + μ⁻¹ := by positivity
  have hsp : 0 < 1 + s := by linarith only [hs0]
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow] at h4
  unfold crudeMomL_ell
  push_cast at h4
  linarith only [h4]

end LogScale

section Main

variable {d : ℕ} [NeZero d] {A : WholeSpaceAnalyticData d} {S : WholeSpaceLocalizedSplitData A}

/-- **The localized tail of the rough split at every shift `mu ≤ 1`.**  For a centre `x` with
`|x| ≤ θ ρ` and `sqrt mu * ρ ≥ 1` the two-scale tail is at most the absorbed expression with the
scale `ℓ = 2 log (1 + θ) + log (K ^ 2 + 1 / mu)`. -/
theorem RoughLogBounds.crudeMomL_tail_le (Rb : RoughLogBounds S) (mu : PositiveShift)
    (hmu1 : (mu : ℝ) ≤ 1) (x : Vec d) {ρ θ : ℝ} (hρ : 0 < ρ) (hθ : 0 ≤ θ)
    (hx : euclideanNorm x ≤ θ * ρ) (hs : 1 ≤ Real.sqrt (mu : ℝ) * ρ) :
    S.tail mu x ρ ≤ crudeMomL_phi d Rb.n (crudeMomL_Cc d A.nu)
      (crudeMomL_Lam1 A.nu Rb.c0 Rb.n) (crudeMomL_r1 d A.nu) ((1 + θ) / Rb.amp)
      (crudeMomL_ell Rb.Kc θ (mu : ℝ)⁻¹) (mu : ℝ)⁻¹ (Real.sqrt (mu : ℝ) * ρ) := by
  have hμ : 0 < (mu : ℝ) := mu.property
  have hnx : 0 ≤ euclideanNorm x := euclideanNorm_nonneg x
  have hsm : 0 < Real.sqrt (mu : ℝ) := Real.sqrt_pos.2 hμ
  have hμi : 1 ≤ (mu : ℝ)⁻¹ := by rw [one_le_inv₀ hμ]; exact hmu1
  set s : ℝ := Real.sqrt (mu : ℝ) * ρ with hsdef
  set ℓ : ℝ := crudeMomL_ell Rb.Kc θ (mu : ℝ)⁻¹ with hℓdef
  obtain ⟨hℓ1, -⟩ := crudeMomL_ell_ge Rb.two_le_Kc hθ hμi
  have hs0 : 0 ≤ s := by linarith only [hs]
  have hlog0 : 0 ≤ Real.log (1 + s) := Real.log_nonneg (by linarith only [hs0])
  set g : ℝ := ℓ + Real.log (1 + s) with hg
  have hg1 : 1 ≤ g := by linarith only [hℓ1, hlog0]
  -- the effective upper constant
  have hKs : S.roughBound x ρ ≤ Rb.c0 * 2 ^ Rb.n * g ^ Rb.n := by
    rw [Rb.rough_eq]
    have hW := crudeMomL_log_obs_le Rb.two_le_Kc hθ hρ hμ hmu1 hnx hx
    have hW0 : 0 ≤ Real.log (Rb.Kc ^ 2 + (euclideanNorm x + ρ) ^ 2) :=
      zero_le_one.trans (crudeMomL_one_le_log Rb.two_le_Kc (sq_nonneg _))
    have h2g : Real.log (Rb.Kc ^ 2 + (euclideanNorm x + ρ) ^ 2) ≤ 2 * g := by
      rw [hg]; linarith only [hW, hℓ1, hlog0]
    calc Rb.c0 * Real.log (Rb.Kc ^ 2 + (euclideanNorm x + ρ) ^ 2) ^ Rb.n
        ≤ Rb.c0 * (2 * g) ^ Rb.n :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hW0 h2g _) Rb.c0_nonneg
      _ = _ := by rw [mul_pow]; ring
  have hKs0 : 0 ≤ S.roughBound x ρ := S.roughBound_nonneg x ρ hρ.le
  have hΛeq : localizedAgmonUpper A.nu (mu : ℝ) (S.roughBound x ρ) 0 =
      Real.sqrt 2 * (A.nu + S.roughBound x ρ) := by
    unfold localizedAgmonUpper; ring
  have hΛpos : 0 < Real.sqrt 2 * (A.nu + S.roughBound x ρ) :=
    mul_pos (Real.sqrt_pos.2 (by norm_num)) (by linarith only [A.hnu, hKs0])
  have hgn1 : 1 ≤ g ^ Rb.n := one_le_pow₀ hg1
  have hΛle : Real.sqrt 2 * (A.nu + S.roughBound x ρ) ≤
      crudeMomL_Lam1 A.nu Rb.c0 Rb.n * g ^ Rb.n := by
    unfold crudeMomL_Lam1
    have hc : 0 ≤ Rb.c0 * 2 ^ Rb.n := by have := Rb.c0_nonneg; positivity
    have : A.nu + S.roughBound x ρ ≤ (A.nu + Rb.c0 * 2 ^ Rb.n) * g ^ Rb.n := by
      nlinarith only [hKs, A.hnu, hgn1, hc]
    calc _ ≤ Real.sqrt 2 * ((A.nu + Rb.c0 * 2 ^ Rb.n) * g ^ Rb.n) :=
          mul_le_mul_of_nonneg_left this (Real.sqrt_nonneg _)
      _ = _ := by ring
  -- the geometry of the freezing scale
  have hq := crudeMomL_q_bounds (amp := Rb.amp) (nx := euclideanNorm x) (θ := θ) (ρ := ρ)
    (μ := (mu : ℝ)) Rb.amp_pos Rb.amp_le_one hnx hθ hx hρ hμ hmu1
  have hclip : S.clippedFreezingRadius x ρ = min (Rb.amp / (1 + euclideanNorm x)) (ρ / 2) := by
    unfold WholeSpaceLocalizedSplitData.clippedFreezingRadius
    rw [Rb.freeze_eq]
  have hR0 : 0 < min (Rb.amp / (1 + euclideanNorm x)) (ρ / 2) :=
    lt_min (div_pos Rb.amp_pos (by linarith only [hnx])) (by linarith only [hρ])
  have hs₀ : 0 < Real.sqrt (mu : ℝ) * min (Rb.amp / (1 + euclideanNorm x)) (ρ / 2) :=
    mul_pos hsm hR0
  have hs₀s : 2 * (Real.sqrt (mu : ℝ) * min (Rb.amp / (1 + euclideanNorm x)) (ρ / 2)) ≤ s := by
    have := min_le_right (Rb.amp / (1 + euclideanNorm x)) (ρ / 2)
    rw [hsdef]; nlinarith only [this, hsm]
  unfold WholeSpaceLocalizedSplitData.tail
  rw [Rb.holder_eq, Rb.smooth_eq x ρ, hΛeq, hclip]
  have hfro := crudeMomL_frozen_le (d := d) A.hnu hΛpos hs hs₀ hs₀s
  refine hfro.trans ?_
  unfold crudeMomL_phi
  have hCc := crudeMomL_Cc_nonneg (d := d) A.hnu
  have hr1 := crudeMomL_r1_pos (d := d) A.hnu
  have hL1 := crudeMomL_Lam1_pos A.hnu Rb.c0_nonneg Rb.n
  have hgn0 : 0 < g ^ Rb.n := lt_of_lt_of_le zero_lt_one hgn1
  have hqq : s / (2 * (Real.sqrt (mu : ℝ) * min (Rb.amp / (1 + euclideanNorm x)) (ρ / 2))) =
      (Real.sqrt (mu : ℝ) * ρ) /
        (2 * (Real.sqrt (mu : ℝ) * min (Rb.amp / (1 + euclideanNorm x)) (ρ / 2))) := rfl
  have hq0 : 0 ≤ s / (2 * (Real.sqrt (mu : ℝ) * min (Rb.amp / (1 + euclideanNorm x)) (ρ / 2))) :=
    by positivity
  have hexp : Real.exp (-(crudeMomL_r1 d A.nu * s / (Real.sqrt 2 * (A.nu + S.roughBound x ρ)))) ≤
      Real.exp (-(crudeMomL_r1 d A.nu * s / (crudeMomL_Lam1 A.nu Rb.c0 Rb.n * g ^ Rb.n))) := by
    apply Real.exp_le_exp.2
    apply neg_le_neg
    exact div_le_div_of_nonneg_left (by positivity) hΛpos hΛle
  have hpoly : Real.sqrt 2 * (A.nu + S.roughBound x ρ) + s ^ 2 ≤
      crudeMomL_Lam1 A.nu Rb.c0 Rb.n * g ^ Rb.n + (1 + s) ^ 2 := by
    nlinarith only [hΛle, hs0]
  have hqp : (s / (2 * (Real.sqrt (mu : ℝ) * min (Rb.amp / (1 + euclideanNorm x)) (ρ / 2)))) ^ d ≤
      ((1 + θ) / Rb.amp * (mu : ℝ)⁻¹ * (1 + s) ^ 2) ^ d :=
    pow_le_pow_left₀ hq0 hq.2 d
  have hpos1 : 0 ≤ Real.sqrt 2 * (A.nu + S.roughBound x ρ) + s ^ 2 := by positivity
  have hμi0 : (0 : ℝ) ≤ (mu : ℝ)⁻¹ := by linarith only [hμi]
  have hθa : 0 ≤ (1 + θ) / Rb.amp := div_nonneg (by linarith only [hθ]) Rb.amp_pos.le
  have hbase : 0 ≤ (1 + θ) / Rb.amp * (mu : ℝ)⁻¹ * (1 + s) ^ 2 :=
    mul_nonneg (mul_nonneg hθa hμi0) (sq_nonneg _)
  have hfac : 0 ≤ crudeMomL_Lam1 A.nu Rb.c0 Rb.n * g ^ Rb.n + (1 + s) ^ 2 := by positivity
  refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hpoly hCc) hqp (pow_nonneg hq0 d)
    (mul_nonneg hCc hfac)) hexp (Real.exp_pos _).le
    (mul_nonneg (mul_nonneg hCc hfac) (pow_nonneg hbase d))

end Main

end

end SuperdiffusionCLT.Section8
