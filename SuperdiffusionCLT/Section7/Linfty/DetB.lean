/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Linfty.Det

/-!
# The deterministic assembly of the `L^∞` proposition: pointwise and real-number steps

The pointwise bound of `v - w` from the two De Giorgi bounds, the bound of `η_h ∗ ũ - g̃` on the
transition layer of the cutoff, and the collection of the monomials into `linfErr`.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- `|v - (ζ M + (1 - ζ) g)| ≤ X₁ + X₂` from `|v - M| ≤ X₁` where `ζ ≠ 0` and `|v - g| ≤ X₂` where
`ζ ≠ 1`. -/
theorem linf_det_mix {ζ M g v X1 X2 : ℝ} (h0 : 0 ≤ ζ) (h1 : ζ ≤ 1) (hX1 : 0 ≤ X1)
    (hX2 : 0 ≤ X2) (hM : ζ ≠ 0 → |v - M| ≤ X1) (hg : ζ ≠ 1 → |v - g| ≤ X2) :
    |v - (ζ * M + (1 - ζ) * g)| ≤ X1 + X2 := by
  have e : v - (ζ * M + (1 - ζ) * g) = ζ * (v - M) + (1 - ζ) * (v - g) := by ring
  have h1' : 0 ≤ 1 - ζ := by linarith only [h1]
  have t1 : ζ * |v - M| ≤ X1 := by
    by_cases hz : ζ = 0
    · rw [hz, zero_mul]; exact hX1
    · calc ζ * |v - M| ≤ ζ * X1 := mul_le_mul_of_nonneg_left (hM hz) h0
        _ ≤ 1 * X1 := mul_le_mul_of_nonneg_right h1 hX1
        _ = X1 := one_mul X1
  have t2 : (1 - ζ) * |v - g| ≤ X2 := by
    by_cases hz : ζ = 1
    · rw [hz, sub_self, zero_mul]; exact hX2
    · calc (1 - ζ) * |v - g| ≤ (1 - ζ) * X2 := mul_le_mul_of_nonneg_left (hg hz) h1'
        _ ≤ 1 * X2 := mul_le_mul_of_nonneg_right (by linarith only [h0]) hX2
        _ = X2 := one_mul X2
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg h0, abs_of_nonneg h1']
  linarith only [t1, t2]

/-- **The datum term on the transition layer** (step 4 of the assembly): where `∇ζ ≠ 0`, the
mollification of `ũ` is within `X + h G` of `g̃`, from the boundary bound `|v - g̃| ≤ X` on the
layer of width `10 h`. -/
theorem linf_det_B2 {W : Set (Vec d)} {h : ℝ} (hh : 0 < h) {u : Vec d → ℝ}
    (hul : LocallyIntegrable u volume) {v gt : Vec d → ℝ} (hgt : ContDiff ℝ 1 gt) {G X : ℝ}
    (hgtG : ∀ x, ‖fderiv ℝ gt x‖ ≤ G)
    (hu : ∀ y ∈ W, 2 * h ≤ Metric.infDist y Wᶜ → u y = v y)
    (hbd : ∀ᵐ y ∂(volume : Measure (Vec d)), y ∈ W → Metric.infDist y Wᶜ < 10 * h →
      |v y - gt y| ≤ X) :
    ∀ x ∈ W, lipGradient (l2a_cutoff W (4 * h)) x ≠ 0 →
      |l2a_moll d h (li1_bump d) u x - gt x| ≤ X + h * G := by
  intro x _ hx
  obtain ⟨-, hη0, hη1, hηs⟩ := l2c_mollifier_witness d
  have hr : 0 < 4 * h := by positivity
  have hdx : 4 * h ≤ Metric.infDist x Wᶜ ∧ Metric.infDist x Wᶜ ≤ 2 * (4 * h) := by
    by_contra hc
    refine hx (l2a_lipGradient_cutoff_eq_zero W hr ?_)
    rcases not_and_or.1 hc with hc | hc
    · exact Or.inl (not_le.1 hc)
    · exact Or.inr (not_le.1 hc)
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hgtG x)
  refine linf_det_moll_le hh (li1_bump_contDiff d).continuous hη0 hη1 hηs hul ?_
  filter_upwards [hbd] with w hw hwb
  rw [Metric.mem_closedBall] at hwb
  have t1 := Metric.infDist_le_infDist_add_dist (s := Wᶜ) (x := x) (y := w)
  have t2 := Metric.infDist_le_infDist_add_dist (s := Wᶜ) (x := w) (y := x)
  rw [dist_comm] at t1
  have hwW : w ∈ W := by
    by_contra hwW
    have : Metric.infDist w Wᶜ = 0 := Metric.infDist_zero_of_mem hwW
    linarith only [this, t1, hwb, hdx.1, hh]
  rw [hu w hwW (by linarith only [t1, hwb, hdx.1, hh])]
  have hmv : ‖gt w - gt x‖ ≤ G * ‖w - x‖ :=
    convex_univ.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => (hgt.differentiable one_ne_zero) z) (fun z _ => hgtG z) trivial trivial
  rw [Real.norm_eq_abs, ← dist_eq_norm w x] at hmv
  have hmv' : |gt w - gt x| ≤ h * G := by
    refine hmv.trans ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right hwb hG0
  have hb := hw hwW (by linarith only [t2, hwb, hdx.2, hh])
  calc |v w - gt x| = |(v w - gt w) + (gt w - gt x)| := by ring_nf
    _ ≤ |v w - gt w| + |gt w - gt x| := abs_add_le _ _
    _ ≤ X + h * G := add_le_add hb hmv'

/-- **The collection of the monomials** (Appendix A.1, step 10): the six bounds of the assembly
sum to at most a constant times `linfErr`. -/
theorem linf_det_real {L h s ν Λ q θ α β α' β' Gb Bb F G P CI CB Cc Cw Ce D : ℝ}
    {X1 X2 B2 Ev Xφ : ℝ} (hL : 0 < L) (hh : 0 < h) (hs : 0 < s) (hν : 0 < ν) (hΛ : 0 ≤ Λ)
    (hq : 1 ≤ q) (hθ : 0 ≤ θ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hα' : 0 ≤ α') (hβ' : 0 ≤ β')
    (hGb : 0 ≤ Gb) (hBb : 0 ≤ Bb) (hF : 0 ≤ F) (hG : 0 ≤ G) (hPq : P ≤ q)
    (hCI : 0 ≤ CI) (hCB : 0 ≤ CB) (hCc : 0 ≤ Cc) (hCw : 0 ≤ Cw) (hCe : 0 ≤ Ce) (hD : 0 ≤ D)
    (eX1 : X1 = CI * P * (h * Gb + h ^ 2 / ν * F))
    (eX2 : X2 = CB * q * (Bb + h ^ 2 / ν * F + h * G)) (eB2 : B2 = X2 + h * G)
    (eEv : Ev = Ce * (Λ / ν * G + L / ν * F))
    (eXφ : Xφ = Cc * L * (s⁻¹ * (α * Gb + β * F) + θ * (B2 / (4 * h) + G) + s⁻¹ * (4 * h) * F +
      θ * (s⁻¹ * (α' * Gb + β' * F)))) :
    X1 + X2 + Xφ + (Cw * (4 * h * (Ev + G) + B2) + D * Xφ) +
        (Cw * (L * (s⁻¹ * (α * Gb + β * F)) + 4 * h * (s⁻¹ * (Λ * Ev) + Ev + G) + B2) +
          D * Xφ) ≤
      (1 + CI + CB + (1 + 2 * D) * Cc * (CB + 8) + 2 * Cw * (4 * Ce + CB + 6)) *
        linfErr L h s ν Λ q θ α β α' β' Gb Bb F G := by
  have hsi : 0 ≤ s⁻¹ := (inv_pos.2 hs).le
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  -- the atoms
  have a1 : 0 ≤ h * Gb := by positivity
  have a2 : 0 ≤ h ^ 2 / ν * F := by positivity
  have a3 : 0 ≤ h * G := by positivity
  have hDG : linfDG q h ν Gb Bb F G = q * (h * Gb + h ^ 2 / ν * F + Bb + h * G) := rfl
  set DG := linfDG q h ν Gb Bb F G with hDGdef
  set B1 := α * Gb + β * F with hB1
  set B5 := α' * Gb + β' * F with hB5
  have hB10 : 0 ≤ B1 := by positivity
  have hB50 : 0 ≤ B5 := by positivity
  set Y := Λ / ν * G + L / ν * F with hY
  have hY0 : 0 ≤ Y := by positivity
  set T1 := L * s⁻¹ * B1 with hT1
  set T3 := L * θ * (DG / h + G + s⁻¹ * B5) with hT3
  set T4 := L * s⁻¹ * h * F with hT4
  set T5 := h * (1 + s⁻¹ * Λ) * Y with hT5
  have hE : linfErr L h s ν Λ q θ α β α' β' Gb Bb F G = T1 + DG + T3 + T4 + T5 := rfl
  set E := linfErr L h s ν Λ q θ α β α' β' Gb Bb F G with hEdef
  have hDG0 : 0 ≤ DG := by rw [hDG]; positivity
  have hT10 : 0 ≤ T1 := by positivity
  have hT30 : 0 ≤ T3 := by positivity
  have hT40 : 0 ≤ T4 := by positivity
  have hT50 : 0 ≤ T5 := by positivity
  have hE0 : 0 ≤ E := by
    rw [hE]
    exact add_nonneg (add_nonneg (add_nonneg (add_nonneg hT10 hDG0) hT30) hT40) hT50
  have hDGE : DG ≤ E := by rw [hE]; linarith only [hT10, hT30, hT40, hT50]
  have hT5E : T5 ≤ E := by rw [hE]; linarith only [hT10, hT30, hT40, hDG0]
  have h134 : T1 + T3 + T4 ≤ E := by rw [hE]; linarith only [hDG0, hT50]
  -- the two De Giorgi bounds
  have f1 : X1 ≤ CI * E := by
    have i1 : P * (h * Gb + h ^ 2 / ν * F) ≤ q * (h * Gb + h ^ 2 / ν * F) :=
      mul_le_mul_of_nonneg_right hPq (by positivity)
    have i2 : q * (h * Gb + h ^ 2 / ν * F) ≤ DG := by
      rw [hDG]; exact mul_le_mul_of_nonneg_left (by linarith only [hBb, a3]) hq0
    rw [eX1, mul_assoc]
    exact mul_le_mul_of_nonneg_left (i1.trans (i2.trans hDGE)) hCI
  have i3 : q * (Bb + h ^ 2 / ν * F + h * G) ≤ DG := by
    rw [hDG]; exact mul_le_mul_of_nonneg_left (by linarith only [a1]) hq0
  have f2 : X2 ≤ CB * DG := by
    rw [eX2, mul_assoc]; exact mul_le_mul_of_nonneg_left i3 hCB
  have f2' : X2 ≤ CB * E := f2.trans (mul_le_mul_of_nonneg_left hDGE hCB)
  have ha3 : h * G ≤ DG := by
    have : h * G ≤ q * (h * G) := le_mul_of_one_le_left a3 hq
    refine this.trans ?_
    rw [hDG]; exact mul_le_mul_of_nonneg_left (by linarith only [a1, a2, hBb]) hq0
  have fB2 : B2 ≤ (CB + 1) * DG := by rw [eB2]; linarith only [f2, ha3]
  have fB2E : B2 ≤ (CB + 1) * E := fB2.trans (mul_le_mul_of_nonneg_left hDGE (by positivity))
  have hB20 : 0 ≤ B2 := by
    rw [eB2, eX2]; positivity
  -- the comparison function
  have p2 : L * θ * (B2 / (4 * h)) ≤ (CB + 1) * (L * θ * (DG / h)) := by
    have e1 : L * θ * (B2 / (4 * h)) = L * θ / (4 * h) * B2 := by ring
    have e2 : (CB + 1) * (L * θ * (DG / h)) = 4 * (L * θ / (4 * h) * ((CB + 1) * DG)) := by
      field_simp
    have k0 : 0 ≤ L * θ / (4 * h) := by positivity
    rw [e1, e2]
    have := mul_le_mul_of_nonneg_left fB2 k0
    have k1 : 0 ≤ L * θ / (4 * h) * ((CB + 1) * DG) := by positivity
    linarith only [this, k1]
  have hT3s : T3 = L * θ * (DG / h) + L * θ * G + L * θ * (s⁻¹ * B5) := by rw [hT3]; ring
  have q1 : 0 ≤ L * θ * (DG / h) := by positivity
  have q2 : 0 ≤ L * θ * G := by positivity
  have q3 : 0 ≤ L * θ * (s⁻¹ * B5) := by positivity
  have hCB1 : (CB + 1) * (L * θ * (DG / h)) ≤ (CB + 1) * T3 :=
    mul_le_mul_of_nonneg_left (by rw [hT3s]; linarith only [q2, q3]) (by positivity)
  have hCBT3 : CB * T3 ≤ CB * E := mul_le_mul_of_nonneg_left
    (by rw [hE]; linarith only [hT10, hDG0, hT40, hT50]) hCB
  have inner : s⁻¹ * B1 * L + L * θ * (B2 / (4 * h) + G) + L * (s⁻¹ * (4 * h) * F) +
      L * θ * (s⁻¹ * B5) ≤ (CB + 8) * E := by
    have e1 : s⁻¹ * B1 * L = T1 := by rw [hT1]; ring
    have e2 : L * θ * (B2 / (4 * h) + G) = L * θ * (B2 / (4 * h)) + L * θ * G := by ring
    have e3 : L * (s⁻¹ * (4 * h) * F) = 4 * T4 := by rw [hT4]; ring
    rw [e1, e2, e3]
    linarith only [p2, hCB1, hT3s, h134, hCBT3, hT10, hT30, hT40, hE0, q1, q2, q3]
  have fφ : Xφ ≤ Cc * ((CB + 8) * E) := by
    have e : Xφ = Cc * (s⁻¹ * B1 * L + L * θ * (B2 / (4 * h) + G) + L * (s⁻¹ * (4 * h) * F) +
        L * θ * (s⁻¹ * B5)) := by rw [eXφ]; ring
    rw [e]; exact mul_le_mul_of_nonneg_left inner hCc
  have fDφ : D * Xφ ≤ D * (Cc * ((CB + 8) * E)) := mul_le_mul_of_nonneg_left fφ hD
  -- the two weak norms
  have hhY : h * Y ≤ T5 := by
    rw [hT5]
    have : h * Y ≤ h * (1 + s⁻¹ * Λ) * Y := by
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hh.le
      have : 0 ≤ s⁻¹ * Λ * Y := by positivity
      linarith only [this]
    exact this
  have hCeT5 : Ce * T5 ≤ Ce * E := mul_le_mul_of_nonneg_left hT5E hCe
  have hCeY : Ce * (h * Y) ≤ Ce * T5 := mul_le_mul_of_nonneg_left hhY hCe
  have hCBDG : CB * DG ≤ CB * E := mul_le_mul_of_nonneg_left hDGE hCB
  have g3 : Cw * (4 * h * (Ev + G) + B2) ≤ Cw * ((4 * Ce + CB + 5) * E) := by
    refine mul_le_mul_of_nonneg_left ?_ hCw
    have e : 4 * h * (Ev + G) = 4 * (Ce * (h * Y)) + 4 * (h * G) := by rw [eEv, hY]; ring
    rw [e]
    linarith only [hCeY, hCeT5, ha3, hDGE, fB2E, hE0]
  have g4 : Cw * (L * (s⁻¹ * B1) + 4 * h * (s⁻¹ * (Λ * Ev) + Ev + G) + B2) ≤
      Cw * ((4 * Ce + CB + 6) * E) := by
    refine mul_le_mul_of_nonneg_left ?_ hCw
    have e : L * (s⁻¹ * B1) + 4 * h * (s⁻¹ * (Λ * Ev) + Ev + G) =
        T1 + 4 * (Ce * T5) + 4 * (h * G) := by rw [eEv, hT1, hT5, hY]; ring
    rw [e]
    linarith only [hCeT5, ha3, hDGE, fB2E, hE0, h134, hT30, hT40]
  have hCwE : 0 ≤ Cw * E := mul_nonneg hCw hE0
  linarith only [f1, f2', fφ, fDφ, g3, g4, hCwE, hE0]

theorem linf_det_ofReal_core {k a b c e t : ℝ} (hk : 0 ≤ k) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (he : 0 ≤ e) (ht : 0 ≤ t) :
    ENNReal.ofReal k * (ENNReal.ofReal a + ENNReal.ofReal t * ENNReal.ofReal b + ENNReal.ofReal c +
        ENNReal.ofReal t * ENNReal.ofReal e) =
      ENNReal.ofReal (k * (a + t * b + c + t * e)) := by
  rw [← ENNReal.ofReal_mul ht, ← ENNReal.ofReal_mul ht,
    ← ENNReal.ofReal_add ha (mul_nonneg ht hb),
    ← ENNReal.ofReal_add (add_nonneg ha (mul_nonneg ht hb)) hc,
    ← ENNReal.ofReal_add (add_nonneg (add_nonneg ha (mul_nonneg ht hb)) hc) (mul_nonneg ht he),
    ← ENNReal.ofReal_mul hk]

/-- A sup-norm bound gives the pointwise bound almost everywhere. -/
theorem linf_det_ae_of_eLpNorm_top {W : Set (Vec d)} {f : Vec d → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict W)) {c : ℝ} (hc : 0 ≤ c) (h : eLpNorm f ⊤ (volume.restrict W) ≤ ENNReal.ofReal c) :
    ∀ᵐ x ∂volume.restrict W, |f x| ≤ c := by
  filter_upwards [ae_le_eLpNormEssSup (f := f) (μ := volume.restrict W)] with x hx
  have h2 : ‖f x‖ₑ ≤ ENNReal.ofReal c := hx.trans (by rw [← eLpNorm_exponent_top hf]; exact h)
  rw [Real.enorm_eq_ofReal_abs] at h2
  exact (ENNReal.ofReal_le_ofReal_iff hc).1 h2

end SuperdiffusionCLT.Section7
