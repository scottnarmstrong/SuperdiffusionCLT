/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.NearShiftAssemblyD
public import SuperdiffusionCLT.Section4.MinimalScales.NearShiftCap

/-!
# Near-scale assembly: the pathwise weighted sum

For one sample `ω`, the near-scale bound is combined across the window and the depths:

* `srootNSD_caseA_pointwise`, `srootNSD_caseB_pointwise`: the bound `Φ ≤ T + B` for one
  `(L, l, R)`, in the cutoff range `L ≤ b` and in the tail `L > b`, where `T` collects the
  deterministic part and the centered `Γ₁` part and `B = (1 + (σ⁻¹ + 1)(H₀ + w)) v` is the
  product part.
* `srootNSD_pathwise`: with the crude cap `g`, the weighted sum over depths of the maximal
  responses is at most the deterministic sum plus `Cp σ⁻² w + Σ w_l y_l + v₁ + min (B, g)`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

noncomputable section

/-- The core of the case `L ≤ b`: the shifted local base with `q ≤ H0 + w`. -/
theorem srootNSD_caseA_core {Φ q x1 X1 x2 y Cp Sg σi H0 w h l Kp L2 v : ℝ}
    (hCp : 0 ≤ Cp) (hSg : 0 ≤ Sg) (hσi : 0 ≤ σi) (hv : 0 ≤ v) (hq0 : 0 ≤ q) (hq : q ≤ H0 + w)
    (hΦ : Φ ≤ Cp * Sg * (q + (2 * h + l) + Kp * L2) + x1 + (1 + σi * q) * x2)
    (hx1 : x1 ≤ X1 + y) (hx2 : |x2| ≤ v) :
    Φ ≤ (Cp * Sg * (H0 + 2 * h + l + Kp * L2) + X1 + (Cp * Sg * w + y)) +
      (1 + σi * (H0 + w)) * v := by
  have h1 : Cp * Sg * (q + (2 * h + l) + Kp * L2) ≤
      Cp * Sg * (H0 + 2 * h + l + Kp * L2) + Cp * Sg * w := by
    have := mul_le_mul_of_nonneg_left (by linarith only [hq] :
      q + (2 * h + l) + Kp * L2 ≤ (H0 + 2 * h + l + Kp * L2) + w) (mul_nonneg hCp hSg)
    linarith only [this]
  have h2 : (1 + σi * q) * x2 ≤ (1 + σi * (H0 + w)) * v := by
    have hx2' : x2 ≤ v := (le_abs_self x2).trans hx2
    have hc : 0 ≤ 1 + σi * q := by positivity
    have e1 := mul_le_mul_of_nonneg_left hx2' hc
    have hle : 1 + σi * q ≤ 1 + σi * (H0 + w) := by
      have := mul_le_mul_of_nonneg_left hq hσi
      linarith only [this]
    have e2 := mul_le_mul_of_nonneg_right hle hv
    linarith only [e1, e2]
  linarith only [hΦ, hx1, h1, h2]

/-- Case `L ≤ b`. -/
theorem srootNSD_caseA_pointwise {Φ q x1 X1 x2 y Cp Sg σi H0 w h l Kp L2 v v1 : ℝ}
    (hCp : 0 ≤ Cp) (hSg : 0 ≤ Sg) (hσi : 0 ≤ σi) (hH0 : 0 ≤ H0) (hw : 0 ≤ w) (hv : 0 ≤ v)
    (hv1 : 0 ≤ v1) (hq0 : 0 ≤ q) (hq : q ≤ H0 + w)
    (hΦ : Φ ≤ Cp * Sg * (q + (2 * h + l) + Kp * L2) + x1 + (1 + σi * q) * x2)
    (hx1 : x1 ≤ X1 + y) (hx2 : |x2| ≤ v) :
    Φ ≤ (Cp * Sg * (H0 + 2 * h + l + Kp * L2) + X1 + (Cp * Sg * w + v1 + y)) +
      (1 + (σi + 1) * (H0 + w)) * v := by
  have h := srootNSD_caseA_core hCp hSg hσi hv hq0 hq hΦ hx1 hx2
  have : 0 ≤ (H0 + w) * v := by positivity
  nlinarith only [h, hv1, this]

/-- Case `L > b`: the tail comparison against the cutoff `b`. -/
theorem srootNSD_caseB_pointwise {Φ Φb q x1 X1 x2 x1' x2' y Cp Sg σi H0 w h l Kp L2 v v1 : ℝ}
    (hCp : 0 ≤ Cp) (hSg : 0 ≤ Sg) (hσi : 0 ≤ σi) (hv : 0 ≤ v)
    (hq0 : 0 ≤ q) (hq : q ≤ H0 + w)
    (hΦb : Φb ≤ Cp * Sg * (q + (2 * h + l) + Kp * L2) + x1 + (1 + σi * q) * x2)
    (hx1 : x1 ≤ X1 + y) (hx2 : |x2| ≤ v)
    (hΦ : Φ ≤ Φb + x1' + q * x2') (hx1' : x1' ≤ v1) (hx2' : |x2'| ≤ v) :
    Φ ≤ (Cp * Sg * (H0 + 2 * h + l + Kp * L2) + X1 + (Cp * Sg * w + v1 + y)) +
      (1 + (σi + 1) * (H0 + w)) * v := by
  have hA := srootNSD_caseA_core hCp hSg hσi hv hq0 hq hΦb hx1 hx2
  have hx2'' : x2' ≤ v := (le_abs_self x2').trans hx2'
  have e1 : q * x2' ≤ q * v := mul_le_mul_of_nonneg_left hx2'' hq0
  have e2 : q * v ≤ (H0 + w) * v := mul_le_mul_of_nonneg_right hq hv
  have e3 : (1 + (σi + 1) * (H0 + w)) * v = (1 + σi * (H0 + w)) * v + (H0 + w) * v := by ring
  linarith only [hA, hΦ, hx1', e1, e2, e3]

/-- The pathwise weighted sum for one sample. `Mx L l` is the maximal response over the
descendants `S l` of depth `l`, `Φ L l R` the response of one descendant. -/
theorem srootNSD_pathwise {ι : Type*} (S : ℕ → Finset ι) (Φ : ℕ → ℕ → ι → ℝ) (Mx : ℕ → ℕ → ℝ)
    (q : ℕ → ℝ) (x1 x2 : ℕ → ℕ → ι → ℝ) (x1' x2' : ℕ → ι → ℝ) (y : ℕ → ℝ)
    {a b Nl : ℕ} (hab : a ≤ b) {s Cp Sg σi H0 w h Kp lg L2 D v v1 g : ℝ} (hs : 0 < s)
    (hCp : 0 ≤ Cp) (hSg : 0 ≤ Sg) (hσi : 0 ≤ σi) (hH0 : 0 ≤ H0) (hw : 0 ≤ w) (hh : 0 ≤ h)
    (hKp : 0 ≤ Kp) (hlg : 0 ≤ lg) (hL2 : 0 ≤ L2) (hD : 0 ≤ D) (hv : 0 ≤ v) (hv1 : 0 ≤ v1)
    (hg : 0 ≤ g) (hy : ∀ l, 0 ≤ y l)
    (hMx : ∀ L l z, a ≤ L → l < Nl → (∀ R ∈ S l, Φ L l R ≤ z) → Mx L l ≤ z)
    (hA : ∀ L, a ≤ L → L ≤ b → ∀ l < Nl, ∀ R ∈ S l,
      Φ L l R ≤ Cp * Sg * (q L + (2 * h + (l : ℝ)) + Kp * L2) + x1 L l R +
        (1 + σi * q L) * x2 L l R)
    (hq : ∀ L, a ≤ L → L ≤ b → 0 ≤ q L ∧ q L ≤ H0 + w)
    (hx1 : ∀ L, a ≤ L → L ≤ b → ∀ l < Nl, ∀ R ∈ S l,
      x1 L l R ≤ Cp * Sg * (2 * h + (l : ℝ) + 2 * Kp * lg) * (2 * lg + 2 * D * (l : ℝ)) + y l)
    (hx2 : ∀ L, a ≤ L → L ≤ b → ∀ l < Nl, ∀ R ∈ S l, |x2 L l R| ≤ v)
    (hB : ∀ L, b < L → ∀ l < Nl, ∀ R ∈ S l, Φ L l R ≤ Φ b l R + x1' l R + q b * x2' l R)
    (hx1' : ∀ l < Nl, ∀ R ∈ S l, x1' l R ≤ v1) (hx2' : ∀ l < Nl, ∀ R ∈ S l, |x2' l R| ≤ v)
    (hcap : ∀ L, a ≤ L → ∀ l < Nl, ∀ R ∈ S l, Φ L l R ≤ g) :
    ∀ L, a ≤ L →
      ∑ l ∈ Finset.range Nl, Homogenization.geometricWeight s 2 l * Mx L l ≤
        ∑ l ∈ Finset.range Nl, Homogenization.geometricWeight s 2 l *
            (Cp * Sg * (H0 + 2 * h + (l : ℝ) + Kp * L2) +
              Cp * Sg * (2 * h + (l : ℝ) + 2 * Kp * lg) * (2 * lg + 2 * D * (l : ℝ))) +
          Cp * Sg * w +
          ∑ l ∈ Finset.range Nl, Homogenization.geometricWeight s 2 l * y l +
          (v1 + min ((1 + (σi + 1) * (H0 + w)) * v) g) := by
  intro L hL
  set T : ℕ → ℝ := fun l => (Cp * Sg * (H0 + 2 * h + (l : ℝ) + Kp * L2) +
    Cp * Sg * (2 * h + (l : ℝ) + 2 * Kp * lg) * (2 * lg + 2 * D * (l : ℝ))) +
      (Cp * Sg * w + v1 + y l) with hT
  set B : ℝ := (1 + (σi + 1) * (H0 + w)) * v with hBdef
  have hCS : 0 ≤ Cp * Sg := mul_nonneg hCp hSg
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hT0 : ∀ l : ℕ, 0 ≤ T l := fun l => by rw [hT]; have := hy l; positivity
  have hwl : ∀ l : ℕ, 0 ≤ Homogenization.geometricWeight s 2 l := fun l =>
    Homogenization.geometricWeight_nonneg l (by linarith only [hs])
  have hΦTB : ∀ l < Nl, ∀ R ∈ S l, Φ L l R ≤ T l + B := by
    intro l hl R hR
    rcases le_or_gt L b with hLb | hLb
    · obtain ⟨hq0, hq1⟩ := hq L hL hLb
      have := srootNSD_caseA_pointwise (Φ := Φ L l R) (q := q L) (x1 := x1 L l R)
        (X1 := Cp * Sg * (2 * h + (l : ℝ) + 2 * Kp * lg) * (2 * lg + 2 * D * (l : ℝ)))
        (x2 := x2 L l R) (y := y l) (h := h) (l := (l : ℝ)) (Kp := Kp) (L2 := L2) hCp hSg hσi
        hH0 hw hv hv1 hq0 hq1 (hA L hL hLb l hl R hR) (hx1 L hL hLb l hl R hR)
        (hx2 L hL hLb l hl R hR)
      rw [hT, hBdef]
      linarith only [this]
    · obtain ⟨hq0, hq1⟩ := hq b hab le_rfl
      have := srootNSD_caseB_pointwise (Φ := Φ L l R) (Φb := Φ b l R) (q := q b)
        (x1 := x1 b l R)
        (X1 := Cp * Sg * (2 * h + (l : ℝ) + 2 * Kp * lg) * (2 * lg + 2 * D * (l : ℝ)))
        (x2 := x2 b l R) (x1' := x1' l R) (x2' := x2' l R) (y := y l) (h := h) (l := (l : ℝ))
        (Kp := Kp) (L2 := L2) hCp hSg hσi hv hq0 hq1 (hA b hab le_rfl l hl R hR)
        (hx1 b hab le_rfl l hl R hR) (hx2 b hab le_rfl l hl R hR) (hB L hLb l hl R hR)
        (hx1' l hl R hR) (hx2' l hl R hR)
      rw [hT, hBdef]
      linarith only [this]
  have hterm : ∀ l ∈ Finset.range Nl, Mx L l ≤ max (T l) 0 + min B g := by
    intro l hl
    have hl' := Finset.mem_range.1 hl
    have h1 : Mx L l ≤ T l + B := hMx L l _ hL hl' (fun R hR => hΦTB l hl' R hR)
    have h2 : Mx L l ≤ g := hMx L l _ hL hl' (fun R hR => hcap L hL l hl' R hR)
    exact srootNS_le_max_zero_add_min h1 h2
  have hcap0 : 0 ≤ min B g := le_min hB0 hg
  have hsum := srootNS_weighted_sum_cap_le Nl (w := fun l => Homogenization.geometricWeight s 2 l)
    (Φ := fun l => Mx L l) (T := T) (B := fun _ => B) (Bmax := B) (G := g) hwl
    (srootNS_weight_sum_le_one hs Nl) hterm (fun _ _ => le_rfl) hcap0
  refine hsum.trans ?_
  have hmax : ∀ l ∈ Finset.range Nl, Homogenization.geometricWeight s 2 l * max (T l) 0 =
      Homogenization.geometricWeight s 2 l * T l := fun l _ => by rw [max_eq_left (hT0 l)]
  rw [Finset.sum_congr rfl hmax]
  have hexp : ∀ l ∈ Finset.range Nl, Homogenization.geometricWeight s 2 l * T l =
      Homogenization.geometricWeight s 2 l *
          (Cp * Sg * (H0 + 2 * h + (l : ℝ) + Kp * L2) +
            Cp * Sg * (2 * h + (l : ℝ) + 2 * Kp * lg) * (2 * lg + 2 * D * (l : ℝ))) +
        (Homogenization.geometricWeight s 2 l * y l +
          Homogenization.geometricWeight s 2 l * (Cp * Sg * w + v1)) := fun l _ => by
    rw [hT]; ring
  rw [Finset.sum_congr rfl hexp, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul]
  have hc := mul_le_mul_of_nonneg_right (srootNS_weight_sum_le_one hs Nl)
    (by positivity : 0 ≤ Cp * Sg * w + v1)
  have hmin : 0 ≤ min B g := hcap0
  have e : v1 + min B g = min B g + v1 := by ring
  have e2 : Cp * Sg * w + v1 = Cp * Sg * w + v1 := rfl
  nlinarith only [hc, hmin, e, e2]

end

end SuperdiffusionCLT.Section4.MinimalScales
