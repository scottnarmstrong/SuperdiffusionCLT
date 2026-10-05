/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Sobolev.Fractional.ContinuousInterpolation.FullNormEquivalence

/-!
# The real `K`-method for one linear map between the interpolation endpoints

In Step 2 of the proof of `l.abstract.response.fields`, the paper obtains the fractional display
`e.abstract.response.Hhalf` "by interpolating the corresponding `L²` and `H¹`
estimates". This module supplies the interpolation step itself, in the
vocabulary of the `K`-functional CoarseGraining already carries on the unit
centered cube.

## The mathematics

For a map `T` bounded `X₀ → Y₀` with norm `A` and `X₁ → Y₁` with norm `B`, the
`K`-functional of the image is dominated pointwise in the scale parameter,

> `K(t, T x; Y₀, Y₁) ≤ max (A, B) · K(t, x; X₀, X₁)`,

because every competitor decomposition `x = (x - g) + g` is carried by `T` to a
competitor decomposition `T x = (T x - T g) + T g` whose two pieces are
controlled by the two endpoint bounds. Integrating the pointwise domination
against the measure `t^{-2θ} dt / t` gives boundedness between the
interpolation spaces with the same constant.

## The concrete pair

`Homogenization.continuousKFunctional t F` is the infimum over genuine `H¹`
competitors `G` of `(‖F - G‖²_{L̲²} + t² ‖∇G‖²_{L̲²})^{1/2}` on the unit
centered cube, and `Homogenization.continuousKSeminorm s F` is the resulting
`(∫₀¹ (t^{-s} K(t,F))² dt/t)^{1/2}`. The endpoint pair is therefore
`(L̲², H̲¹)` and the interpolation order is `s`. The hypotheses below are
exactly the two endpoint bounds, expressed at the level at which the package
can state them: a competitor transfer `G ↦ transfer G` together with the
residual bound at constant `A` and the gradient bound at constant `B`.

## Main results

* `continuousKFunctionalCompetitorValue_le_of_endpoints`: the pointwise
  domination at one competitor.
* `continuousKFunctional_le_of_endpoints`: `K(t, F') ≤ max A B · K(t, F)`.
* `continuousKSeminorm_le_of_continuousKFunctional_le`: the interpolation
  seminorm inherits any pointwise domination of the `K`-functional.
* `continuousKFullENorm_le_of_endpoints`: the full interpolation norm bound.
* `euclideanHsFullENorm_le_of_endpoints`: the same bound transported to the
  exact Euclidean `H^s` full norm, with the squared equivalence constant of
  `exists_continuousKFullENorm_euclideanHsFullENorm_equivalence`.
-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Sobolev

open Homogenization
open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The pointwise domination -/

/-- One competitor decomposition transported by the two endpoint bounds: if the
residual is scaled by at most `A` and the gradient by at most `B`, then the
`K`-competitor value is scaled by at most `max A B`. -/
theorem continuousKFunctionalCompetitorValue_le_of_endpoints
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    {F F' : UnitCubeEuclideanL2Field d} {G G' : ContinuousKCompetitor d}
    (hres : continuousKResidualNorm F' G' ≤ A * continuousKResidualNorm F G)
    (hgrad : continuousKGradientNorm G' ≤ B * continuousKGradientNorm G)
    (t : ContinuousKScale) :
    continuousKFunctionalCompetitorValue t F' G' ≤
      max A B * continuousKFunctionalCompetitorValue t F G := by
  set M : ℝ := max A B with hM
  have hMnonneg : 0 ≤ M := le_trans hA (le_max_left A B)
  have hAsq : A ^ 2 ≤ M ^ 2 := by
    simpa only [pow_two] using mul_self_le_mul_self hA (le_max_left A B)
  have hBsq : B ^ 2 ≤ M ^ 2 := by
    simpa only [pow_two] using mul_self_le_mul_self hB (le_max_right A B)
  have hrsq : continuousKResidualNorm F' G' ^ 2 ≤
      M ^ 2 * continuousKResidualNorm F G ^ 2 := by
    have hstep : continuousKResidualNorm F' G' ^ 2 ≤
        A ^ 2 * continuousKResidualNorm F G ^ 2 := by
      have := mul_self_le_mul_self (continuousKResidualNorm_nonneg F' G') hres
      simpa only [pow_two, mul_mul_mul_comm] using this
    exact hstep.trans (mul_le_mul_of_nonneg_right hAsq (sq_nonneg _))
  have hgsq : continuousKGradientNorm G' ^ 2 ≤
      M ^ 2 * continuousKGradientNorm G ^ 2 := by
    have hstep : continuousKGradientNorm G' ^ 2 ≤
        B ^ 2 * continuousKGradientNorm G ^ 2 := by
      have := mul_self_le_mul_self (continuousKGradientNorm_nonneg G') hgrad
      simpa only [pow_two, mul_mul_mul_comm] using this
    exact hstep.trans (mul_le_mul_of_nonneg_right hBsq (sq_nonneg _))
  have hsum :
      continuousKResidualNorm F' G' ^ 2 + t.1 ^ 2 * continuousKGradientNorm G' ^ 2 ≤
        M ^ 2 * (continuousKResidualNorm F G ^ 2 +
          t.1 ^ 2 * continuousKGradientNorm G ^ 2) := by
    have hsecond : t.1 ^ 2 * continuousKGradientNorm G' ^ 2 ≤
        t.1 ^ 2 * (M ^ 2 * continuousKGradientNorm G ^ 2) :=
      mul_le_mul_of_nonneg_left hgsq (sq_nonneg _)
    calc
      continuousKResidualNorm F' G' ^ 2 + t.1 ^ 2 * continuousKGradientNorm G' ^ 2
          ≤ M ^ 2 * continuousKResidualNorm F G ^ 2 +
            t.1 ^ 2 * (M ^ 2 * continuousKGradientNorm G ^ 2) :=
        add_le_add hrsq hsecond
      _ = M ^ 2 * (continuousKResidualNorm F G ^ 2 +
            t.1 ^ 2 * continuousKGradientNorm G ^ 2) := by ring
  unfold continuousKFunctionalCompetitorValue
  calc
    Real.sqrt (continuousKResidualNorm F' G' ^ 2 +
        t.1 ^ 2 * continuousKGradientNorm G' ^ 2)
        ≤ Real.sqrt (M ^ 2 * (continuousKResidualNorm F G ^ 2 +
            t.1 ^ 2 * continuousKGradientNorm G ^ 2)) := Real.sqrt_le_sqrt hsum
    _ = M * Real.sqrt (continuousKResidualNorm F G ^ 2 +
          t.1 ^ 2 * continuousKGradientNorm G ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hMnonneg]

/-! ## The `K`-functional bound -/

private theorem le_mul_csInf_of_forall {c : ℝ} (hc : 0 ≤ c) {S : Set ℝ}
    (hne : S.Nonempty) {x : ℝ} (h : ∀ y ∈ S, x ≤ c * y) : x ≤ c * sInf S := by
  rcases hc.eq_or_lt with hzero | hpos
  · obtain ⟨y, hy⟩ := hne
    have hx : x ≤ 0 := by simpa only [← hzero, zero_mul] using h y hy
    simpa only [← hzero, zero_mul] using hx
  · have hdiv : x / c ≤ sInf S := by
      refine le_csInf hne (fun y hy => ?_)
      rw [div_le_iff₀ hpos, mul_comm]
      exact h y hy
    rw [mul_comm]
    exact (div_le_iff₀ hpos).1 hdiv

/-- **The real `K`-method.** A competitor transfer satisfying the two endpoint
bounds dominates the `K`-functional pointwise in the scale parameter, with the
larger of the two endpoint constants. -/
theorem continuousKFunctional_le_of_endpoints
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    {F F' : UnitCubeEuclideanL2Field d}
    (transfer : ContinuousKCompetitor d → ContinuousKCompetitor d)
    (hres : ∀ G : ContinuousKCompetitor d,
      continuousKResidualNorm F' (transfer G) ≤ A * continuousKResidualNorm F G)
    (hgrad : ∀ G : ContinuousKCompetitor d,
      continuousKGradientNorm (transfer G) ≤ B * continuousKGradientNorm G)
    (t : ContinuousKScale) :
    continuousKFunctional t F' ≤ max A B * continuousKFunctional t F := by
  rw [continuousKFunctional_eq_sInf t F]
  refine le_mul_csInf_of_forall (le_trans hA (le_max_left A B))
    (continuousKFunctional_range_nonempty t F) ?_
  rintro y ⟨G, rfl⟩
  exact (continuousKFunctional_le_competitor t F' (transfer G)).trans
    (continuousKFunctionalCompetitorValue_le_of_endpoints hA hB (hres G) (hgrad G) t)

/-! ## The interpolation seminorm -/

private theorem ofReal_sq_rpow_half {c : ℝ} (hc : 0 ≤ c) :
    (ENNReal.ofReal (c ^ 2)) ^ ((1 : ℝ) / 2) = ENNReal.ofReal c := by
  rw [ENNReal.ofReal_pow hc, ← ENNReal.rpow_natCast (ENNReal.ofReal c) 2,
    ← ENNReal.rpow_mul]
  norm_num

/-- Any pointwise domination of the `K`-functional passes to the continuum
interpolation seminorm `(∫₀¹ (t^{-s} K(t, ·))² dt/t)^{1/2}`. -/
theorem continuousKSeminorm_le_of_continuousKFunctional_le
    {c : ℝ} (hc : 0 ≤ c) {F F' : UnitCubeEuclideanL2Field d}
    (h : ∀ t : ContinuousKScale,
      continuousKFunctional t F' ≤ c * continuousKFunctional t F)
    (s : FractionalOrder) :
    continuousKSeminorm s F' ≤ ENNReal.ofReal c * continuousKSeminorm s F := by
  have hpt : ∀ t : ℝ, continuousKSeminormIntegrand s.1 F' t ≤
      ENNReal.ofReal (c ^ 2) * continuousKSeminormIntegrand s.1 F t := by
    intro t
    by_cases ht : t ∈ Set.Ioo (0 : ℝ) 1
    · have hK : continuousKFunctionalOnOpenScale F' t ≤
          c * continuousKFunctionalOnOpenScale F t := by
        simp only [continuousKFunctionalOnOpenScale, ht, ↓reduceDIte]
        exact h ⟨t, ⟨ht.1, ht.2.le⟩⟩
      have hnonneg : 0 ≤ continuousKFunctionalOnOpenScale F' t := by
        simp only [continuousKFunctionalOnOpenScale, ht, ↓reduceDIte]
        exact continuousKFunctional_nonneg _ F'
      have hsq : continuousKFunctionalOnOpenScale F' t ^ 2 ≤
          c ^ 2 * continuousKFunctionalOnOpenScale F t ^ 2 := by
        have := mul_self_le_mul_self hnonneg hK
        simpa only [pow_two, mul_mul_mul_comm] using this
      have hofReal : ENNReal.ofReal (continuousKFunctionalOnOpenScale F' t ^ 2) ≤
          ENNReal.ofReal (c ^ 2) *
            ENNReal.ofReal (continuousKFunctionalOnOpenScale F t ^ 2) := by
        rw [← ENNReal.ofReal_mul (sq_nonneg c)]
        exact ENNReal.ofReal_le_ofReal hsq
      unfold continuousKSeminormIntegrand
      calc
        ENNReal.ofReal (Real.rpow t (-2 * s.1)) *
              ENNReal.ofReal (continuousKFunctionalOnOpenScale F' t ^ 2) *
              ENNReal.ofReal t⁻¹
            ≤ ENNReal.ofReal (Real.rpow t (-2 * s.1)) *
              (ENNReal.ofReal (c ^ 2) *
                ENNReal.ofReal (continuousKFunctionalOnOpenScale F t ^ 2)) *
              ENNReal.ofReal t⁻¹ :=
          mul_le_mul' (mul_le_mul' le_rfl hofReal) le_rfl
        _ = ENNReal.ofReal (c ^ 2) *
              (ENNReal.ofReal (Real.rpow t (-2 * s.1)) *
                ENNReal.ofReal (continuousKFunctionalOnOpenScale F t ^ 2) *
                ENNReal.ofReal t⁻¹) := by ring
    · have hzero : continuousKSeminormIntegrand s.1 F' t = 0 := by
        unfold continuousKSeminormIntegrand continuousKFunctionalOnOpenScale
        simp only [ht, ↓reduceDIte]
        simp
      rw [hzero]
      exact zero_le
  have hint : (∫⁻ t in Set.Ioo (0 : ℝ) 1, continuousKSeminormIntegrand s.1 F' t) ≤
      ENNReal.ofReal (c ^ 2) *
        ∫⁻ t in Set.Ioo (0 : ℝ) 1, continuousKSeminormIntegrand s.1 F t := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_mono hpt
  calc
    continuousKSeminorm s F'
        = (∫⁻ t in Set.Ioo (0 : ℝ) 1, continuousKSeminormIntegrand s.1 F' t) ^
            ((1 : ℝ) / 2) := rfl
    _ ≤ (ENNReal.ofReal (c ^ 2) *
            ∫⁻ t in Set.Ioo (0 : ℝ) 1, continuousKSeminormIntegrand s.1 F t) ^
          ((1 : ℝ) / 2) := ENNReal.rpow_le_rpow hint (by norm_num)
    _ = ENNReal.ofReal c * continuousKSeminorm s F := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
          ofReal_sq_rpow_half hc]
        rfl

/-! ## The full interpolation norm -/

/-- **The interpolation step.** The two endpoint bounds — the `L̲²` bound at
constant `A` and the competitor-level `H̲¹` bound at constant `B` — give the
full continuum interpolation norm bound at every fractional order, with the
constant `max A B`. -/
theorem continuousKFullENorm_le_of_endpoints
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (s : FractionalOrder)
    {F F' : UnitCubeEuclideanL2Field d}
    (transfer : ContinuousKCompetitor d → ContinuousKCompetitor d)
    (hres : ∀ G : ContinuousKCompetitor d,
      continuousKResidualNorm F' (transfer G) ≤ A * continuousKResidualNorm F G)
    (hgrad : ∀ G : ContinuousKCompetitor d,
      continuousKGradientNorm (transfer G) ≤ B * continuousKGradientNorm G)
    (hL2 : (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) F' ≤
      ENNReal.ofReal A *
        (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) F) :
    continuousKFullENorm s F' ≤ ENNReal.ofReal (max A B) * continuousKFullENorm s F := by
  have hMnonneg : 0 ≤ max A B := le_trans hA (le_max_left A B)
  have hseminorm : continuousKSeminorm s F' ≤
      ENNReal.ofReal (max A B) * continuousKSeminorm s F :=
    continuousKSeminorm_le_of_continuousKFunctional_le hMnonneg
      (continuousKFunctional_le_of_endpoints hA hB transfer hres hgrad) s
  have hL2' : (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) F' ≤
      ENNReal.ofReal (max A B) *
        (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) F :=
    hL2.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left A B)) le_rfl)
  calc
    continuousKFullENorm s F'
        = (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) F' +
            continuousKSeminorm s F' := rfl
    _ ≤ ENNReal.ofReal (max A B) *
            (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) F +
          ENNReal.ofReal (max A B) * continuousKSeminorm s F :=
        add_le_add hL2' hseminorm
    _ = ENNReal.ofReal (max A B) * continuousKFullENorm s F := by
        rw [continuousKFullENorm_eq, mul_add]

/-- The same interpolation step read in the exact Euclidean `H^s` full norm,
through the two-sided equivalence of
`exists_continuousKFullENorm_euclideanHsFullENorm_equivalence`. The constant
picks up the square of the equivalence constant. -/
theorem euclideanHsFullENorm_le_of_endpoints
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (s : FractionalOrder)
    {F F' : UnitCubeEuclideanL2Field d}
    (transfer : ContinuousKCompetitor d → ContinuousKCompetitor d)
    (hres : ∀ G : ContinuousKCompetitor d,
      continuousKResidualNorm F' (transfer G) ≤ A * continuousKResidualNorm F G)
    (hgrad : ∀ G : ContinuousKCompetitor d,
      continuousKGradientNorm (transfer G) ≤ B * continuousKGradientNorm G)
    (hL2 : (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) F' ≤
      ENNReal.ofReal A *
        (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) F) :
    euclideanHsFullENorm s F' ≤
      (continuousKEuclideanHsFullENormConstant s d ^ 2 * ENNReal.ofReal (max A B)) *
        euclideanHsFullENorm s F := by
  set C : ℝ≥0∞ := continuousKEuclideanHsFullENormConstant s d with hC
  calc
    euclideanHsFullENorm s F' ≤ C * continuousKFullENorm s F' :=
      euclideanHsFullENorm_le_mul_continuousKFullENorm s F'
    _ ≤ C * (ENNReal.ofReal (max A B) * continuousKFullENorm s F) :=
      mul_le_mul' le_rfl
        (continuousKFullENorm_le_of_endpoints hA hB s transfer hres hgrad hL2)
    _ ≤ C * (ENNReal.ofReal (max A B) * (C * euclideanHsFullENorm s F)) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl
        (continuousKFullENorm_le_mul_euclideanHsFullENorm s F))
    _ = (C ^ 2 * ENNReal.ofReal (max A B)) * euclideanHsFullENorm s F := by ring

end

end Sobolev
end SuperdiffusionCLT
