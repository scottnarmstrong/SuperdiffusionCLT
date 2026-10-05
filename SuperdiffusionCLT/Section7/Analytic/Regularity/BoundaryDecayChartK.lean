/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.BoundaryDecayChartJ

@[expose] public section

open Homogenization MeasureTheory Filter Topology Matrix
open scoped ENNReal NNReal

/-!
# From the face box back to the ball

A bound valid almost everywhere on the face box of side `2 K ρ` of the flat picture transfers to
`U ∩ B(x₀, ρ)`, because the chart map preserves the volume.
-/

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem r3e_pullback_ae {U : Set (Vec d)} (hU : IsOpen U) {e : Vec d} (he : vecNormSq e = 1)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {x₀ : Vec d}
    (hx₀ : vecDot e x₀ = ψ (x₀ - vecDot e x₀ • e)) {r : ℝ}
    (hch : ∀ y ∈ Metric.ball x₀ r, (y ∈ U ↔ vecDot e y < ψ (y - vecDot e y • e))) (i₀ : Fin d)
    {K : ℝ} (hK1 : 1 ≤ K)
    (hKlipF : ∀ y z : Vec d, ‖flattenMap e ψ x₀ (-(basisVec i₀)) y -
        flattenMap e ψ x₀ (-(basisVec i₀)) z‖ ≤ K * ‖y - z‖)
    (m : ℤ) {ρ : ℝ} (hρr : ρ ≤ r) (φ' : Vec d → ℝ) (a : ℝ) (b : Vec d) {E : ℝ}
    (h : ∀ᵐ x ∂(volume.restrict (r3e_F i₀ m (2 * K * ρ))),
      |φ' (flattenInv e ψ x₀ (-(basisVec i₀)) (x - r3c_z0 i₀ m)) -
        (a + vecDot b (x - r3c_z0 i₀ m))| ≤ E) :
    ∀ᵐ y ∂(volume.restrict (U ∩ Metric.ball x₀ ρ)),
      |φ' y - (a + vecDot b (flattenMap e ψ x₀ (-(basisVec i₀)) y))| ≤ E := by
  have hSm : MeasurableSet (U ∩ Metric.ball x₀ ρ) :=
    hU.measurableSet.inter Metric.isOpen_ball.measurableSet
  have h1 := (ae_restrict_iff' (r3e_measurableSet_axisCube _ _)).1 h
  have h2 := (p12_chartMap_measurePreserving he hψ (-(basisVec i₀)) x₀
    (r3c_z0 i₀ m)).quasiMeasurePreserving.ae h1
  filter_upwards [ae_restrict_of_ae h2, ae_restrict_mem hSm] with y hy hyS
  have hmem := r3e_push_mem he hψ hx₀ hch i₀ hK1 hKlipF m hρr hyS.1 hyS.2
  have := hy hmem
  simpa only [add_sub_cancel_right, flattenInv_flattenMap he hψ] using this

/-- The final real arithmetic: the chain error and the second order chart error are absorbed
into `(ρ / R)^α` times the original datum. -/
theorem r3e_final_alg {R ρ M₂ B Bo α C₀ Kl CB Cs dd cT nb nb0 Es err : ℝ} (hR : 0 < R)
    (hρ : 0 < ρ) (hρR : ρ ≤ R) (hKl : 0 ≤ Kl) (hα1 : α ≤ 1) (hM : 0 ≤ M₂)
    (hMR : M₂ * R ≤ 1) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀) (hCs : 0 ≤ Cs)
    (hdd : 0 ≤ dd) (hcT : 0 ≤ cT) (hnb : 0 ≤ nb) (hBB : B ≤ CB * Bo)
    (hsl : M₂ * R * nb0 ≤ Bo) (hb : nb ≤ Cs * B + dd * nb0)
    (hE : Es ≤ C₀ * (4 * Kl * ρ) * (4 * Kl * ρ / R) ^ α * B)
    (herr : err ≤ cT * M₂ * ρ ^ 2 * nb) :
    Es + err ≤ ((C₀ * (4 * Kl) * (4 * Kl) ^ α + cT * Cs) * CB + cT * dd) * ρ * (ρ / R) ^ α * Bo := by
  have hx0 : 0 ≤ ρ / R := by positivity
  have hx1 : ρ / R ≤ 1 := (div_le_one hR).2 hρR
  have hxa : ρ / R ≤ (ρ / R) ^ α := Real.self_le_rpow_of_le_one hx0 hx1 hα1
  have hxa0 : 0 ≤ (ρ / R) ^ α := Real.rpow_nonneg hx0 α
  have hmul : (4 * Kl * ρ / R) ^ α = (4 * Kl) ^ α * (ρ / R) ^ α := by
    rw [show 4 * Kl * ρ / R = (4 * Kl) * (ρ / R) by ring]
    exact Real.mul_rpow (by positivity) hx0
  have hK4 : 0 ≤ (4 * Kl) ^ α := Real.rpow_nonneg (by positivity) α
  have hE' : Es ≤ (C₀ * (4 * Kl) * (4 * Kl) ^ α) * ρ * (ρ / R) ^ α * B := by
    refine hE.trans (le_of_eq ?_)
    rw [hmul]; ring
  -- the error term
  have hMρ : M₂ * ρ ≤ M₂ * R * (ρ / R) ^ α := by
    calc M₂ * ρ = M₂ * R * (ρ / R) := by field_simp
      _ ≤ M₂ * R * (ρ / R) ^ α := mul_le_mul_of_nonneg_left hxa (by positivity)
  have hMRnb : M₂ * R * nb ≤ Cs * B + dd * Bo := by
    have h1 : M₂ * R * nb ≤ M₂ * R * (Cs * B + dd * nb0) := mul_le_mul_of_nonneg_left hb (by positivity)
    have h2 : M₂ * R * (Cs * B) ≤ Cs * B := by
      have : 0 ≤ Cs * B := by positivity
      nlinarith only [hMR, this]
    have h3 : M₂ * R * (dd * nb0) ≤ dd * Bo := by
      have := mul_le_mul_of_nonneg_left hsl hdd
      linarith only [this, show M₂ * R * (dd * nb0) = dd * (M₂ * R * nb0) by ring]
    linarith only [h1, h2, h3, show M₂ * R * (Cs * B + dd * nb0) = M₂ * R * (Cs * B) + M₂ * R * (dd * nb0) by ring]
  have herr' : err ≤ cT * ρ * (ρ / R) ^ α * (Cs * B + dd * Bo) := by
    refine herr.trans ?_
    have h1 : cT * M₂ * ρ ^ 2 * nb = cT * ρ * ((M₂ * ρ) * nb) := by ring
    rw [h1]
    have h2 : (M₂ * ρ) * nb ≤ (M₂ * R * (ρ / R) ^ α) * nb := mul_le_mul_of_nonneg_right hMρ hnb
    have h3 : (M₂ * R * (ρ / R) ^ α) * nb = (ρ / R) ^ α * (M₂ * R * nb) := by ring
    have h4 : (ρ / R) ^ α * (M₂ * R * nb) ≤ (ρ / R) ^ α * (Cs * B + dd * Bo) :=
      mul_le_mul_of_nonneg_left hMRnb hxa0
    have h5 : cT * ρ * ((M₂ * ρ) * nb) ≤ cT * ρ * ((ρ / R) ^ α * (Cs * B + dd * Bo)) :=
      mul_le_mul_of_nonneg_left (by linarith only [h2, h3, h4]) (by positivity)
    linarith only [h5, show cT * ρ * ((ρ / R) ^ α * (Cs * B + dd * Bo)) =
      cT * ρ * (ρ / R) ^ α * (Cs * B + dd * Bo) by ring]
  have hpos : 0 ≤ ρ * (ρ / R) ^ α := by positivity
  have hBB' : (C₀ * (4 * Kl) * (4 * Kl) ^ α + cT * Cs) * B ≤
      (C₀ * (4 * Kl) * (4 * Kl) ^ α + cT * Cs) * (CB * Bo) :=
    mul_le_mul_of_nonneg_left hBB (by positivity)
  have hsum : Es + err ≤ ρ * (ρ / R) ^ α *
      ((C₀ * (4 * Kl) * (4 * Kl) ^ α + cT * Cs) * B + cT * dd * Bo) := by
    have e1 : (C₀ * (4 * Kl) * (4 * Kl) ^ α) * ρ * (ρ / R) ^ α * B +
        cT * ρ * (ρ / R) ^ α * (Cs * B + dd * Bo) =
        ρ * (ρ / R) ^ α * ((C₀ * (4 * Kl) * (4 * Kl) ^ α + cT * Cs) * B + cT * dd * Bo) := by ring
    linarith only [hE', herr', e1]
  refine hsum.trans ?_
  have : ρ * (ρ / R) ^ α * ((C₀ * (4 * Kl) * (4 * Kl) ^ α + cT * Cs) * B + cT * dd * Bo) ≤
      ρ * (ρ / R) ^ α * ((C₀ * (4 * Kl) * (4 * Kl) ^ α + cT * Cs) * (CB * Bo) + cT * dd * Bo) :=
    mul_le_mul_of_nonneg_left (by linarith only [hBB']) hpos
  refine this.trans (le_of_eq ?_)
  ring

end SuperdiffusionCLT.Section7
