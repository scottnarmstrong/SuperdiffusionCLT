/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Linfty.Smooth
public import SuperdiffusionCLT.Section7.Linfty.DetC
public import SuperdiffusionCLT.Section7.Linfty.LocalB
public import SuperdiffusionCLT.Section7.Linfty.HBound
public import SuperdiffusionCLT.Section7.Prereq.CenteringD

/-!
# The `L^∞` proposition for a smooth datum: one sample

The facts about the dilated domain `R U`, `3^{K-1} < R ≤ 3^K`, used by the assembly: it lies in
the cube `□_K`, its rescaling by `3^{-K}` has uniform `C^{1,1}` data independent of `R`, and the
normalized cell averages of the cell bounds are the normalized norms on the translated cubes.
`linf_smooth_sample` is the comparison for one sample: from the cell bounds of the mollified
fluxes, the boundary Lipschitz estimate at the fine-grid centres and the numerical thresholds, it
combines `linf_local`, `linf_H_bound` and `linf_det` with the numerics of `Smooth.lean`.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal Pointwise

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- An open subset of the half-open unit cube lies in the open unit cube. -/
theorem linf_smooth_hU0 {U : Set (Vec d)} (hUo : IsOpen U) (hU : U ⊆ kc2_Q0 d) :
    U ⊆ openCubeSet (originCube d 0) := by
  have e : kc2_Q0 d = cubeSet (originCube d ((0 : ℕ) : ℤ)) := by
    have := kc3_smul_Q0 (d := d) 0
    simpa using this
  rw [e] at hU
  have h := interior_maximal hU hUo
  rw [Homogenization.interior_cubeSet_eq_openCubeSet] at h
  simpa using h

/-- Monotonicity of the uniform `C^{1,1}` data. -/
theorem linf_smooth_unif_mono {U : Set (Vec d)} {r M₁ M₂ D r' M₂' D' : ℝ}
    (h : IsUniformC11Domain U r M₁ M₂ D) (hr' : 0 < r') (hr : r' ≤ r) (hM : M₂ ≤ M₂')
    (hD : D ≤ D') : IsUniformC11Domain U r' M₁ M₂' D' :=
  ⟨h.1, hr', fun x hx y hy => (h.2.2.1 x hx y hy).trans hD,
    fun x hx => (h.2.2.2 x hx).mono hr le_rfl hM⟩

/-- The dilates `l U`, `1/3 < l ≤ 1`, have the common data `(r/3, M₁, 3 max M₂ 0, max D 0)`. -/
theorem linf_smooth_unif_dil {U : Set (Vec d)} {r M₁ M₂ D : ℝ}
    (h : IsUniformC11Domain U r M₁ M₂ D) {l : ℝ} (hl : 1 / 3 < l) (hl1 : l ≤ 1) :
    IsUniformC11Domain (l • U) (r / 3) M₁ (3 * max M₂ 0) (max D 0) := by
  have hl0 : 0 < l := lt_trans (by norm_num) hl
  have hr : 0 < r := h.2.1
  refine linf_smooth_unif_mono (h.smul hl0) (by positivity) ?_ ?_ ?_
  · have : r / 3 ≤ l * r := by
      have := mul_le_mul_of_nonneg_right hl.le hr.le
      linarith only [this]
    exact this
  · have h1 : M₂ / l ≤ max M₂ 0 / l := div_le_div_of_nonneg_right (le_max_left _ _) hl0.le
    have h2 : max M₂ 0 / l ≤ 3 * max M₂ 0 := by
      rw [div_le_iff₀ hl0]
      have hm : 0 ≤ max M₂ 0 := le_max_right _ _
      have := mul_le_mul_of_nonneg_left hl.le hm
      nlinarith only [this, hm]
    exact h1.trans h2
  · have hm : 0 ≤ max D 0 := le_max_right _ _
    calc l * D ≤ l * max D 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) hl0.le
      _ ≤ 1 * max D 0 := mul_le_mul_of_nonneg_right hl1 hm
      _ = max D 0 := one_mul _

/-- The dilated domain lies in the cube `□_K`, in the axis cube of side `3^K` and in the sup-ball of
radius `3^K`. -/
theorem linf_smooth_dom {U : Set (Vec d)} (hU0 : U ⊆ openCubeSet (originCube d 0)) {K : ℕ}
    {R : ℝ} (hR : 0 < R) (hRK : R ≤ (3 : ℝ) ^ K) :
    R • U ⊆ Section6.engCube d K ∧
      R • U ⊆ axisCube (fun _ => -((3 : ℝ) ^ K / 2)) ((3 : ℝ) ^ K) ∧
      ∀ x ∈ R • U, ‖x‖ ≤ (3 : ℝ) ^ K := by
  have h1 := linf_local_dil_subset hU0 hR
  have hb : Metric.ball (0 : Vec d) (R / 2) ⊆ Metric.ball (0 : Vec d) ((3 : ℝ) ^ K / 2) :=
    Metric.ball_subset_ball (by linarith only [hRK])
  have hc : Metric.ball (0 : Vec d) ((3 : ℝ) ^ K / 2) = openCubeSet (originCube d (K : ℤ)) := by
    rw [← rc_shiftCube_zero, lip_datum_shiftCube_eq]
    simp
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have := hb (h1 hx)
    rw [hc] at this
    exact this
  · intro x hx
    have := hb (h1 hx)
    rw [hc, ← rc_shiftCube_zero, rc_shiftCube_eq_axisCube] at this
    simpa using this
  · intro x hx
    have := h1 hx
    rw [mem_ball_zero_iff] at this
    linarith only [this, hRK, hR]

/-- The shifted cube is the translated open cube. -/
theorem linf_smooth_shiftCube_eq (y : Vec d) (m : ℤ) :
    shiftCube y m = translateSet y (openCubeSet (originCube d m)) := by
  ext x
  rw [mem_translateSet_iff_sub_mem]
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa using hw
  · intro hx
    exact ⟨x - y, hx, by simp⟩

/-- The shifted cube lies in the cell. -/
theorem linf_smooth_shiftCube_sub_cell (z : Vec d) (n : ℕ) :
    shiftCube z (n : ℤ) ⊆ l2b_cell z n := by
  intro x hx
  rw [linf_smooth_shiftCube_eq, mem_translateSet_iff_sub_mem] at hx
  unfold l2b_cell
  rw [mem_translateSet_iff_sub_mem]
  exact openCubeSet_subset_cubeSet _ hx

/-- The cell and the shifted cube differ by a null set. -/
theorem linf_smooth_restrict_cell (z : Vec d) (n : ℕ) :
    volume.restrict (l2b_cell z n) = volume.restrict (shiftCube z (n : ℤ)) := by
  have h1 := (measurePreserving_addRight_restrict_translateSet z
    (cubeSet (originCube d (n : ℤ)))).map_eq
  have h2 := (measurePreserving_addRight_restrict_translateSet z
    (openCubeSet (originCube d (n : ℤ)))).map_eq
  have e := volume_restrict_cubeSet_eq_volume_restrict_openCubeSet (originCube d (n : ℤ))
  rw [linf_smooth_shiftCube_eq, ← h2, ← e, h1]
  rfl

/-- The cell average is the normalized norm on the shifted cube. -/
theorem linf_smooth_avg_eq {z : Vec d} {n : ℕ} {g : Vec d → ℝ} {r : ℝ} (hr : 0 < r)
    (hg : AEStronglyMeasurable g (volume.restrict (shiftCube z (n : ℤ)))) :
    l2b_avg (ENNReal.ofReal (cubeVolume (originCube d (n : ℤ)))) (l2b_cell z n)
        (fun x => ‖g x‖ₑ) r = lpBar (shiftCube z (n : ℤ)) (ENNReal.ofReal r) g := by
  have h0 : ENNReal.ofReal r ≠ 0 := by simpa using hr
  have hvol : volume (shiftCube z (n : ℤ)) =
      ENNReal.ofReal (cubeVolume (originCube d (n : ℤ))) := by
    have := congrArg (fun μ => μ Set.univ) (linf_smooth_restrict_cell z n)
    simp only [Measure.restrict_apply_univ] at this
    rw [← this]
    exact l2b_volume_cell' z n
  unfold l2b_avg lpBar
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h0 ENNReal.ofReal_ne_top
    (hg.smul_measure ((volume (shiftCube z (n : ℤ)))⁻¹)), ENNReal.toReal_ofReal hr.le,
    lintegral_smul_measure, hvol, linf_smooth_restrict_cell]
  simp only [smul_eq_mul]

/-- A function bounded almost everywhere on a set containing the cell has a bounded cell
average. -/
theorem linf_smooth_avg_le {z : Vec d} {n : ℕ} {W : Set (Vec d)} (hW : l2b_cell z n ⊆ W)
    {f : Vec d → ℝ} {F r : ℝ} (hr : 0 < r) (hF : 0 ≤ F)
    (hf : ∀ᵐ x ∂volume.restrict W, |f x| ≤ F) :
    l2b_avg (ENNReal.ofReal (cubeVolume (originCube d (n : ℤ)))) (l2b_cell z n)
        (fun x => ‖f x‖ₑ) r ≤ ENNReal.ofReal F := by
  unfold l2b_avg
  have hv0 : ENNReal.ofReal (cubeVolume (originCube d (n : ℤ))) ≠ 0 := by
    have := cubeVolume_pos (originCube d (n : ℤ))
    simpa using this
  have hvt : ENNReal.ofReal (cubeVolume (originCube d (n : ℤ))) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hf' : ∀ᵐ x ∂volume.restrict (l2b_cell z n), |f x| ≤ F :=
    ae_restrict_of_ae_restrict_of_subset hW hf
  have h1 : ∫⁻ x in l2b_cell z n, ‖f x‖ₑ ^ r ≤
      ∫⁻ x in l2b_cell z n, ENNReal.ofReal F ^ r := by
    refine lintegral_mono_ae (hf'.mono fun x hx => ?_)
    refine ENNReal.rpow_le_rpow ?_ hr.le
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal hx
  rw [lintegral_const, Measure.restrict_apply_univ, l2b_volume_cell'] at h1
  have _hF := hF
  have h2 : (ENNReal.ofReal (cubeVolume (originCube d (n : ℤ))))⁻¹ *
      ∫⁻ x in l2b_cell z n, ‖f x‖ₑ ^ r ≤ ENNReal.ofReal F ^ r := by
    calc (ENNReal.ofReal (cubeVolume (originCube d (n : ℤ))))⁻¹ * ∫⁻ x in l2b_cell z n, ‖f x‖ₑ ^ r
        ≤ (ENNReal.ofReal (cubeVolume (originCube d (n : ℤ))))⁻¹ *
          (ENNReal.ofReal F ^ r * ENNReal.ofReal (cubeVolume (originCube d (n : ℤ)))) := by
          gcongr
      _ = ENNReal.ofReal F ^ r := by
          rw [mul_comm (ENNReal.ofReal F ^ r), ← mul_assoc, ENNReal.inv_mul_cancel hv0 hvt,
            one_mul]
  calc ((ENNReal.ofReal (cubeVolume (originCube d (n : ℤ))))⁻¹ *
        ∫⁻ x in l2b_cell z n, (fun x => ‖f x‖ₑ) x ^ r) ^ (1 / r)
      ≤ (ENNReal.ofReal F ^ r) ^ (1 / r) := ENNReal.rpow_le_rpow h2 (by positivity)
    _ = ENNReal.ofReal F := by
        rw [← ENNReal.rpow_mul, mul_one_div_cancel hr.ne', ENNReal.rpow_one]

/-- **The cell bound in real form**: from the bound of the mollified flux by the cell averages of
`|∇u|` and `|f|`, with `‖∇u‖_{L̲²(z + □_{n+1})} ≤ Gb` and `|f| ≤ F` almost everywhere. -/
theorem linf_smooth_flux_real {W : Set (Vec d)} {u : H1Function W} {z : Vec d} {n : ℕ}
    (hcell : l2b_cell z (n + 1) ⊆ W) {f : Vec d → ℝ} {F q Gb nm a b : ℝ} (hq : 0 < q)
    (hF : 0 ≤ F) (hf : ∀ᵐ x ∂volume.restrict W, |f x| ≤ F) (ha : 0 ≤ a) (hb : 0 ≤ b) (hGb0 : 0 ≤ Gb)
    (hGb : lpBar (shiftCube z ((n : ℤ) + 1)) 2 (fun x => eucNorm (u.grad x)) ≤
      ENNReal.ofReal Gb)
    (h : ENNReal.ofReal nm ≤ ENNReal.ofReal a *
        l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ))))
          (l2b_cell z (n + 1)) (fun x => ‖eucNorm (u.grad x)‖ₑ) 2 +
      ENNReal.ofReal b * l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ))))
          (l2b_cell z (n + 1)) (fun x => ‖f x‖ₑ) q) :
    nm ≤ a * Gb + b * F := by
  have hsub : shiftCube z ((n + 1 : ℕ) : ℤ) ⊆ W :=
    (linf_smooth_shiftCube_sub_cell z (n + 1)).trans hcell
  have hm : AEStronglyMeasurable (fun x => eucNorm (u.grad x))
      (volume.restrict (shiftCube z ((n + 1 : ℕ) : ℤ))) :=
    ((wh2_aemeasurable_eucNorm u).mono_measure (Measure.restrict_mono hsub le_rfl)).aestronglyMeasurable
  have e1 := linf_smooth_avg_eq (z := z) (n := n + 1) (r := 2) (by norm_num) hm
  have e2 : (((n + 1 : ℕ) : ℤ)) = (n : ℤ) + 1 := by push_cast; ring
  rw [e1, e2, ENNReal.ofReal_ofNat] at h
  have h2 := linf_smooth_avg_le hcell hq hF hf
  have h3 : ENNReal.ofReal nm ≤ ENNReal.ofReal a * ENNReal.ofReal Gb +
      ENNReal.ofReal b * ENNReal.ofReal F :=
    h.trans (add_le_add (mul_le_mul' le_rfl hGb) (mul_le_mul' le_rfl h2))
  rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul hb,
    ← ENNReal.ofReal_add (mul_nonneg ha hGb0) (mul_nonneg hb hF)] at h3
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3

/-- Merging the products of real constants inside `ENNReal.ofReal`, one flux. -/
private theorem linf_smooth_ofReal_mul_two {K a b : ℝ} {X Y : ℝ≥0∞} {nm : ℝ} (hK : 0 ≤ K)
    (h : ENNReal.ofReal nm ≤ ENNReal.ofReal K * ENNReal.ofReal a * X +
      ENNReal.ofReal K * ENNReal.ofReal b * Y) :
    ENNReal.ofReal nm ≤ ENNReal.ofReal (K * a) * X + ENNReal.ofReal (K * b) * Y := by
  rw [ENNReal.ofReal_mul hK, ENNReal.ofReal_mul hK]
  exact h

/-- Merging the products of real constants inside `ENNReal.ofReal`, the sum of two fluxes. -/
private theorem linf_smooth_ofReal_mul_four {K s a b e g : ℝ} {X Y : ℝ≥0∞} {nm : ℝ} (hK : 0 ≤ K)
    (hs : 0 ≤ s) (ha : 0 ≤ a) (hb : 0 ≤ b) (he : 0 ≤ e) (hg : 0 ≤ g)
    (h : ENNReal.ofReal nm ≤ (ENNReal.ofReal K * ENNReal.ofReal a +
        ENNReal.ofReal (s * K) * ENNReal.ofReal e) * X +
      (ENNReal.ofReal K * ENNReal.ofReal b + ENNReal.ofReal (s * K) * ENNReal.ofReal g) * Y) :
    ENNReal.ofReal nm ≤ ENNReal.ofReal (K * a + s * K * e) * X +
      ENNReal.ofReal (K * b + s * K * g) * Y := by
  have hsK : 0 ≤ s * K := mul_nonneg hs hK
  rw [ENNReal.ofReal_add (mul_nonneg hK ha) (mul_nonneg hsK he),
    ENNReal.ofReal_add (mul_nonneg hK hb) (mul_nonneg hsK hg), ENNReal.ofReal_mul hK,
    ENNReal.ofReal_mul hK, ENNReal.ofReal_mul hsK, ENNReal.ofReal_mul hsK]
  exact h

/-- Nonnegativity of the local-bound radius. -/
private theorem linf_smooth_Rb_nonneg {Cloc Cl σ F G G2 Hs E : ℝ} {K n : ℕ} (hCloc : 0 ≤ Cloc)
    (hCl : 0 ≤ Cl) (hσ : 0 < σ) (hF : 0 ≤ F) (hG : 0 ≤ G) (hG2 : 0 ≤ G2) (hHs : 0 ≤ Hs)
    (hKn : 0 ≤ (K : ℝ) - (n : ℝ)) (hK : 1 ≤ (K : ℝ)) :
    0 ≤ Cloc * Cl * (((3 : ℝ)⁻¹) ^ K * Hs + σ⁻¹ * (3 : ℝ) ^ K * F +
      ((K : ℝ) - (n : ℝ)) * G + (K : ℝ) ^ (-E) * (3 : ℝ) ^ K * G2) := by
  have : 0 ≤ (K : ℝ) ^ (-E) := Real.rpow_nonneg (by linarith only [hK]) _
  positivity

/-- Nonnegativity of the flux constants. -/
private theorem linf_smooth_l2e_nonneg {Cin σ ν ρ δ k : ℝ} {n : ℕ} (hCin : 0 ≤ Cin) (hσ : 0 < σ)
    (hν : 0 < ν) (hδ : 0 ≤ δ) (hk : 0 ≤ k) :
    0 ≤ l2e_aC Cin σ ν δ ∧ 0 ≤ l2e_b Cin σ ν ρ δ k n ∧ 0 ≤ l2e_e Cin σ ν ∧
      0 ≤ l2e_g Cin σ ν n := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold l2e_aC; positivity
  · unfold l2e_b l2e_aC; positivity
  · unfold l2e_e; positivity
  · unfold l2e_g l2e_e; positivity

/-- **The final absorption, in extended reals.** -/
theorem linf_smooth_final {X P1 P2 l1 l2 : ℝ≥0∞} {Cd Kp Cin δ Y ϖ Φ Γ Hs CH lk Cloc Cl N κ ι : ℝ}
    (hCd : 0 ≤ Cd) (hKp : 0 ≤ Kp) (hCin : 0 ≤ Cin) (hδ : 0 ≤ δ) (hΦ : 0 ≤ Φ) (hΓ : 0 ≤ Γ)
    (hCH : 0 ≤ CH) (hCloc : 0 ≤ Cloc) (hCl : 0 ≤ Cl) (hN : 0 ≤ N) (hY0 : 0 ≤ Y) (hϖ0 : 0 ≤ ϖ)
    (hdet : X + P1 + P2 ≤ ENNReal.ofReal (Cd * (Kp * Cin * δ * Y + ϖ * (Y + Φ + Γ))))
    (hH : l1 + l2 ≤ 2 * X + ENNReal.ofReal (CH * (Γ + Φ)))
    (hHs : Hs = l1.toReal + l2.toReal)
    (hY : Y = Cloc * Cl * (Hs + Φ + κ * Γ + ι * Γ))
    (hκ : κ ≤ (N + 1) * lk) (hι : ι ≤ 3) (hlk : 1 ≤ lk) (hϖ : ϖ ≤ δ)
    (hsmall : Cd * (Kp * Cin + 1) * (Cloc * Cl * (CH + N + 7)) * δ ≤ 1 / 2) :
    X + P1 + P2 ≤
      ENNReal.ofReal (2 * Cd * (Kp * Cin + 1) * (Cloc * Cl * (CH + N + 7) + 1) * δ *
        (Φ + lk * Γ)) := by
  have hZfin : X + P1 + P2 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hdet
  have hZr : (X + P1 + P2).toReal ≤ Cd * (Kp * Cin * δ * Y + ϖ * (Y + Φ + Γ)) :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hdet
  have hXZ : X ≤ X + P1 + P2 := le_add_right (le_add_right le_rfl)
  have hXfin := ne_top_of_le_ne_top hZfin hXZ
  have hXr := ENNReal.toReal_mono hZfin hXZ
  have hHfin : 2 * X + ENNReal.ofReal (CH * (Γ + Φ)) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by simp) hXfin, ENNReal.ofReal_ne_top⟩
  have hl12 := ne_top_of_le_ne_top hHfin hH
  obtain ⟨hl1, hl2⟩ := ENNReal.add_ne_top.1 hl12
  have hHs' : Hs ≤ 2 * (X + P1 + P2).toReal + CH * (Γ + Φ) := by
    have h1 := ENNReal.toReal_mono hHfin hH
    rw [ENNReal.toReal_add hl1 hl2, ENNReal.toReal_add (ENNReal.mul_ne_top (by simp) hXfin)
      ENNReal.ofReal_ne_top, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h1
    have h2 : (2 : ℝ≥0∞).toReal = 2 := by simp
    rw [h2] at h1
    rw [hHs]
    linarith only [h1, hXr]
  have hYb := linf_smooth_Yb (CL := Cloc * Cl) (by positivity) hHs' hκ hι hΦ hΓ
    ENNReal.toReal_nonneg hlk hCH hN
  rw [← hY] at hYb
  have hfinal := linf_smooth_absorb (Z := (X + P1 + P2).toReal) (Y := Y) (Φ := Φ) (Γ := Γ)
    (lk := lk) (Cd := Cd) (KC := Kp * Cin) (δ := δ) (ϖ := ϖ) (CY := Cloc * Cl * (CH + N + 7))
    ENNReal.toReal_nonneg hΦ hΓ hlk hCd (by positivity) hδ hZr hYb hY0 hϖ hsmall
  rw [← ENNReal.ofReal_toReal hZfin]
  exact ENNReal.ofReal_le_ofReal hfinal

/-- **The numerical tail of the one-sample comparison.** From the deterministic bound, the
oscillation bound and the local bound for `Rb`, the three terms are at most the stated multiple of
`δ (σ⁻¹ 3^{2K} F + log K 3^K G)`. -/
private theorem linf_smooth_tail {X P1 P2 l1 l2 : ℝ≥0∞}
    {Cd Kp Cin δ Cloc CH Cl N E σ cθ cΛ Q τ F G G2 Hs Rb : ℝ} {K n nC : ℕ}
    (hCd : 0 ≤ Cd) (hKp0 : 0 ≤ Kp) (hCin : 0 ≤ Cin) (hδ0 : 0 ≤ δ) (hCH : 0 ≤ CH)
    (hCloc : 0 ≤ Cloc) (hCl : 0 ≤ Cl) (hN : 0 ≤ N) (hF : 0 ≤ F) (hG : 0 ≤ G) (hσ0 : 0 < σ)
    (hRb0 : 0 ≤ Rb) (hτ0 : 0 ≤ τ) (hQ0 : 0 ≤ Q) (hcθ0 : 0 ≤ cθ) (hK3 : (3 : ℝ) ≤ K)
    (hdet : X + P1 + P2 ≤ ENNReal.ofReal (Cd * (Kp * Cin * δ * ((3 : ℝ) ^ K * Rb) +
      linfCp Kp Cin cθ cΛ * ((Q + 1) * (K : ℝ) ^ 11) * τ *
        ((3 : ℝ) ^ K * Rb + σ⁻¹ * ((3 : ℝ) ^ K) ^ 2 * F + (3 : ℝ) ^ K * G))))
    (hH : l1 + l2 ≤ 2 * X + ENNReal.ofReal (CH * ((3 : ℝ) ^ K * G + ((3 : ℝ) ^ K) ^ 2 / σ * F)))
    (hHs : Hs = l1.toReal + l2.toReal) (hG2 : G2 = G / (3 : ℝ) ^ nC)
    (hRb : Rb = Cloc * Cl * (((3 : ℝ)⁻¹) ^ K * Hs + σ⁻¹ * (3 : ℝ) ^ K * F +
      ((K : ℝ) - (n : ℝ)) * G + (K : ℝ) ^ (-E) * (3 : ℝ) ^ K * G2))
    (hKn : (K : ℝ) - (n : ℝ) ≤ (N + 1) * Real.log (K : ℝ))
    (hEn : (K : ℝ) ^ (-E) * (3 : ℝ) ^ K ≤ 3 * (3 : ℝ) ^ nC)
    (hϖ : linfCp Kp Cin cθ cΛ * ((Q + 1) * (K : ℝ) ^ 11) * τ ≤ δ)
    (hsmall : Cd * (Kp * Cin + 1) * (Cloc * Cl * (CH + N + 7)) * δ ≤ 1 / 2) :
    X + P1 + P2 ≤
      ENNReal.ofReal (2 * Cd * (Kp * Cin + 1) * (Cloc * Cl * (CH + N + 7) + 1) * δ *
        (σ⁻¹ * (3 : ℝ) ^ (2 * K) * F + Real.log (K : ℝ) * (3 : ℝ) ^ K * G)) := by
  have h3K : (0 : ℝ) < (3 : ℝ) ^ K := by positivity
  have hι : (K : ℝ) ^ (-E) * (3 : ℝ) ^ K / (3 : ℝ) ^ nC ≤ 3 := by
    rw [div_le_iff₀ (by positivity)]; exact hEn
  have hY : (3 : ℝ) ^ K * Rb = Cloc * Cl * (Hs + σ⁻¹ * ((3 : ℝ) ^ K) ^ 2 * F +
      ((K : ℝ) - (n : ℝ)) * ((3 : ℝ) ^ K * G) +
      ((K : ℝ) ^ (-E) * (3 : ℝ) ^ K / (3 : ℝ) ^ nC) * ((3 : ℝ) ^ K * G)) := by
    rw [hRb, hG2, inv_pow]
    field_simp
  have hlk : 1 ≤ Real.log (K : ℝ) := by
    have h3 : (1 : ℝ) ≤ Real.log 3 :=
      SuperdiffusionCLT.Section2.Estimates.Stream.one_lt_log_three.le
    exact h3.trans (Real.log_le_log (by norm_num) hK3)
  have hH' : l1 + l2 ≤ 2 * X + ENNReal.ofReal (CH * ((3 : ℝ) ^ K * G +
      σ⁻¹ * ((3 : ℝ) ^ K) ^ 2 * F)) := by
    refine hH.trans (le_of_eq ?_)
    congr 3
    ring
  have hCp0 : 0 ≤ linfCp Kp Cin cθ cΛ := by
    unfold linfCp; positivity
  have hΦ : 0 ≤ σ⁻¹ * ((3 : ℝ) ^ K) ^ 2 * F := by positivity
  have hΓ : 0 ≤ (3 : ℝ) ^ K * G := by positivity
  have hY0 : 0 ≤ (3 : ℝ) ^ K * Rb := mul_nonneg h3K.le hRb0
  have hϖ0 : 0 ≤ linfCp Kp Cin cθ cΛ * ((Q + 1) * (K : ℝ) ^ 11) * τ := by positivity
  refine (linf_smooth_final hCd hKp0 hCin hδ0 hΦ hΓ hCH hCloc hCl hN hY0 hϖ0 hdet hH' hHs hY
    hKn hι hlk hϖ hsmall).trans (le_of_eq ?_)
  congr 1
  ring

/-- **The `L^∞` comparison for one sample.** For the recentred field `a`, the centred field
`ac = a + K₀` (`K₀` skew) elliptic on `□_K` with constants `(ν, Λ)`, the cell bounds of the mollified
fluxes of `ac`, and the boundary Lipschitz estimate at the fine-grid centres, the three terms of the
`L^∞` proposition for a smooth datum are bounded by `C δ (σ⁻¹ 3^{2K} F + log K 3^K G)`, provided the
numerical thresholds hold. -/
theorem linf_smooth_sample [NeZero d] (hd : 2 ≤ d) {U : Set (Vec d)}
    (hU : IsSmoothBoundedDomain U) (hU0 : U ⊆ openCubeSet (originCube d 0)) :
    ∃ (s0 : ℕ) (B₀ Cd Cloc CH cθ : ℝ), 243 ≤ B₀ ∧ 0 ≤ Cd ∧ 0 ≤ Cloc ∧ 0 ≤ CH ∧ 0 ≤ cθ ∧
    ∀ (a ac : CoeffField d) (K₀ Mavg : Mat d) (ν σ Λ cΛ Q Cin Cl N E δ ρ : ℝ) (K n nC : ℕ)
      (R : ℝ),
      0 < ν → ν ≤ 1 → 1 ≤ (K : ℝ) * ν → 1 ≤ σ → σ ≤ (K : ℝ) → 3 ≤ (K : ℝ) →
      0 ≤ δ → δ ≤ (K : ℝ) → ρ ≤ 1 → 1 ≤ Cin → 1 ≤ Cl → 0 ≤ N → 0 ≤ E →
      ν ≤ Λ → Λ ≤ cΛ * (K : ℝ) ^ 5 → (Λ / ν) ^ (deGiorgiPower d + 1) ≤ Q →
      B₀ * (3 : ℝ) ^ n ≤ (3 : ℝ) ^ K →
      (K : ℝ) - (n : ℝ) ≤ (N + 1) * Real.log (K : ℝ) →
      (K : ℝ) ^ (-E) * (3 : ℝ) ^ K ≤ 3 * (3 : ℝ) ^ nC →
      linfCp (l2e_Kp d) Cin cθ cΛ * ((Q + 1) * (K : ℝ) ^ 11) *
          ((3 : ℝ) ^ n / (3 : ℝ) ^ K) ^ (1 / (2 * (d : ℝ))) ≤ δ →
      Cd * (l2e_Kp d * Cin + 1) * (Cloc * Cl * (CH + N + 7)) * δ ≤ 1 / 2 →
      (3 : ℝ) ^ K < 3 * R → R ≤ (3 : ℝ) ^ K →
      matTranspose K₀ = -K₀ → (∀ x, ac x = a x + K₀) → (∀ x, a x - Mavg = ac x) →
      IsEllipticFieldOn ν Λ (openCubeSet (originCube d (K : ℤ))) ac →
      (∀ (u : H1Function (R • U)) (f : Vec d → ℝ), AEMeasurable f (volume.restrict (R • U)) →
        IsWeakSolutionOn ac (R • U) u f (fun _ => 0) →
        ∀ kk : Fin d → ℤ, l2b_cell (l2b_pt n kk) (n + 1) ⊆ R • U →
        ∀ x ∈ l2b_cell (l2b_pt n kk) n,
          ENNReal.ofReal ‖a16_mollify d ((3 : ℝ) ^ n) (li1_bump d)
              (fun y => matVecMul (ac y - σ • (1 : Mat d)) (u.grad y)) x‖ ≤
            (ENNReal.ofReal (l2e_Kp d) * ENNReal.ofReal (l2e_aC Cin σ ν δ)) *
                l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ))))
                  (l2b_cell (l2b_pt n kk) (n + 1)) (fun x => ‖eucNorm (u.grad x)‖ₑ) 2 +
              (ENNReal.ofReal (l2e_Kp d) * ENNReal.ofReal (l2e_b Cin σ ν ρ δ K n)) *
                l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ))))
                  (l2b_cell (l2b_pt n kk) (n + 1)) (fun x => ‖f x‖ₑ)
                  (Real.conjExponent (sobStar d)) ∧
          ENNReal.ofReal ‖a16_mollify d ((3 : ℝ) ^ n) (li1_bump d)
              (fun y => matVecMul (ac y) (u.grad y)) x‖ ≤
            (ENNReal.ofReal (l2e_Kp d) * ENNReal.ofReal (l2e_aC Cin σ ν δ) +
                ENNReal.ofReal (σ * l2e_Kp d) * ENNReal.ofReal (l2e_e Cin σ ν)) *
                l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ))))
                  (l2b_cell (l2b_pt n kk) (n + 1)) (fun x => ‖eucNorm (u.grad x)‖ₑ) 2 +
              (ENNReal.ofReal (l2e_Kp d) * ENNReal.ofReal (l2e_b Cin σ ν ρ δ K n) +
                  ENNReal.ofReal (σ * l2e_Kp d) * ENNReal.ofReal (l2e_g Cin σ ν n)) *
                l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ))))
                  (l2b_cell (l2b_pt n kk) (n + 1)) (fun x => ‖f x‖ₑ)
                  (Real.conjExponent (sobStar d))) →
      ∀ (f gt : Vec d → ℝ) (F G : ℝ), ContDiff ℝ (⊤ : ℕ∞) gt → 0 ≤ F → 0 ≤ G →
        AEStronglyMeasurable f (volume.restrict (R • U)) →
        (∀ᵐ x ∂volume.restrict (R • U), |f x| ≤ F) → (∀ x, ‖fderiv ℝ gt x‖ ≤ G) →
        (∀ x, ‖fderiv ℝ (fderiv ℝ gt) x‖ ≤ G / (3 : ℝ) ^ nC) →
      (∀ j : ℕ, n ≤ j → j ≤ n + 3 →
        ∀ z ∈ gridPts d ((j : ℤ) - s0) ((3 : ℝ) ^ (K + 2)), z ∈ R • U →
        ∀ u : H1Function (shiftCube z ((K - 1 : ℕ) : ℤ) ∩ R • U),
          IsWeakSolutionOn a (shiftCube z ((K - 1 : ℕ) : ℤ) ∩ R • U) u f (fun _ => 0) →
          LocalizedZeroTraceFunctionOn (shiftCube z ((K - 1 : ℕ) : ℤ) ∩ R • U)
            (shiftCube z ((K - 1 : ℕ) : ℤ)) (fun x => u.toFun x - gt x) →
          ∀ Rr : ℝ≥0∞,
            Rr = ENNReal.ofReal (Cl * (3 : ℝ) ^ (-((K - 1 : ℕ) : ℝ))) *
                (lpBar (shiftCube z ((K - 1 : ℕ) : ℤ) ∩ R • U) 2
                    (fun x => u.toFun x -
                      ⨍ w in shiftCube z ((K - 1 : ℕ) : ℤ) ∩ R • U, u.toFun w) +
                  lpBar (shiftCube z ((K - 1 : ℕ) : ℤ) ∩ R • U) 2 (fun x => u.toFun x - gt x)) +
              ENNReal.ofReal (Cl * σ⁻¹ * (3 : ℝ) ^ (K - 1 : ℕ)) *
                eLpNorm f ⊤ (volume.restrict (shiftCube z ((K - 1 : ℕ) : ℤ) ∩ R • U)) +
              ENNReal.ofReal (Cl * (((K - 1 : ℕ) : ℝ) - (j : ℝ))) *
                eLpNorm (fun x => ‖fderiv ℝ gt x‖) ⊤
                  (volume.restrict (shiftCube z ((K - 1 : ℕ) : ℤ))) +
              ENNReal.ofReal (Cl * (K : ℝ) ^ (-E) * (3 : ℝ) ^ (K - 1 : ℕ)) *
                eLpNorm (fun x => ‖fderiv ℝ (fderiv ℝ gt) x‖) ⊤
                  (volume.restrict (shiftCube z ((K - 1 : ℕ) : ℤ))) →
            ENNReal.ofReal ((Real.sqrt σ)⁻¹ * Real.sqrt ν) *
                  lpBar (shiftCube z (j : ℤ) ∩ R • U) 2 (fun x => eucNorm (u.grad x)) +
                ENNReal.ofReal ((3 : ℝ) ^ (-(j : ℝ))) *
                  lpBar (shiftCube z (j : ℤ) ∩ R • U) 2
                    (fun x => u.toFun x - ⨍ w in shiftCube z (j : ℤ) ∩ R • U, u.toFun w) ≤ Rr ∧
              (¬ shiftCube z (j : ℤ) ⊆ R • U →
                ENNReal.ofReal ((3 : ℝ) ^ (-(j : ℝ))) *
                  lpBar (shiftCube z (j : ℤ) ∩ R • U) 2 (fun x => u.toFun x - gt x) ≤ Rr)) →
      ∀ v vh : H1Function (R • U),
        IsWeakSolutionOn a (R • U) v f (fun _ => 0) →
        MemH10 (R • U) (fun x => v.toFun x - gt x) →
        IsWeakSolutionOn (fun _ => σ • (1 : Mat d)) (R • U) vh f (fun _ => 0) →
        MemH10 (R • U) (fun x => vh.toFun x - gt x) →
        eLpNorm (fun x => v.toFun x - vh.toFun x) ⊤ (volume.restrict (R • U)) +
            hMinusOneVec (R • U) (fun x => v.grad x - vh.grad x) +
            hMinusOneVec (R • U) (fun x =>
              matVecMul (σ⁻¹ • (a x - Mavg)) (v.grad x) - vh.grad x) ≤
          ENNReal.ofReal (2 * Cd * (l2e_Kp d * Cin + 1) * (Cloc * Cl * (CH + N + 7) + 1) * δ *
            (σ⁻¹ * (3 : ℝ) ^ (2 * K) * F + Real.log (K : ℝ) * (3 : ℝ) ^ K * G)) := by
  obtain ⟨r, M₁, M₂, D, hUd⟩ := exists_isUniformC11Domain_of_isSmoothBoundedDomain hU
  have hr : 0 < r := hUd.2.1
  set r' : ℝ := r / 3 with hr'
  set M₂' : ℝ := 3 * max M₂ 0 with hM₂'
  set D' : ℝ := max D 0 with hD'
  have hr'0 : 0 < r' := by positivity
  obtain ⟨cvol, hcvol, Hgeom⟩ := l2e_geom (d := d) r' M₁ D'
  obtain ⟨Cd, hCd, Hdet⟩ := linf_det hd M₁ (r' * M₂') (D' / r')
  obtain ⟨s0, Cloc, hCloc, Hloc⟩ := linf_local hU hU0
  obtain ⟨CH, hCH, HH⟩ := linf_H_bound (d := d)
  set κd : ℝ := (d : ℝ) + (1 + d) * max M₁ 0 with hκd
  have hκd0 : 0 ≤ κd := by
    have : 0 ≤ max M₁ 0 := le_max_right _ _
    positivity
  set B₀ : ℝ := 243 * Cloc + 12 * (3 * κd + 4) / r' + 1 with hB₀
  have hB₀1 : 243 ≤ B₀ := by
    have : 0 ≤ 12 * (3 * κd + 4) / r' := by positivity
    linarith only [this, hCloc, hB₀]
  set cθ : ℝ := cvol ^ (1 / (2 * (d : ℝ))) with hcθ
  have hcθ0 : 0 ≤ cθ := Real.rpow_nonneg hcvol.le _
  refine ⟨s0, B₀, Cd, Cloc, CH, cθ, hB₀1, by linarith only [hCd], by linarith only [hCloc],
    hCH.le, hcθ0, ?_⟩
  intro a ac K₀ Mavg ν σ Λ cΛ Q Cin Cl N E δ ρ K n nC R hν hν1 hKν hσ1 hσK hK3 hδ0 hδK hρ1 hCin
    hCl hN hE hνΛ hΛ hQ hB hKn hEn hϖ hsmall hR1 hR2 hskew hK0 hid hell hcell f gt F G hgt hF hG
    hfm hfF hgtG hgt2G hblock v vh hv hvmem hvh hvhmem
  revert hcell hblock
  -- numbers
  have h3n : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have h3K : (0 : ℝ) < (3 : ℝ) ^ K := by positivity
  have hR0 : 0 < R := by linarith only [hR1, h3K]
  have hσ0 : 0 < σ := lt_of_lt_of_le one_pos hσ1
  have hK1 : (1 : ℝ) ≤ K := by linarith only [hK3]
  have hCloc81 : Cloc * (3 : ℝ) ^ (n + 4) ≤ (3 : ℝ) ^ K := by
    have e : (3 : ℝ) ^ (n + 4) = 81 * (3 : ℝ) ^ n := by ring
    rw [e]
    have : Cloc * (81 * (3 : ℝ) ^ n) ≤ B₀ * (3 : ℝ) ^ n := by
      have h1 : 0 ≤ 12 * (3 * κd + 4) / r' := by positivity
      have h2 : Cloc * 81 ≤ B₀ := by linarith only [hCloc, h1, hB₀]
      nlinarith only [h2, h3n]
    linarith only [this, hB]
  have hn4 : n + 4 ≤ K := by
    have h1 : (3 : ℝ) ^ (n + 4) ≤ (3 : ℝ) ^ K := by
      have : (3 : ℝ) ^ (n + 4) ≤ Cloc * (3 : ℝ) ^ (n + 4) :=
        le_mul_of_one_le_left (by positivity) hCloc
      linarith only [this, hCloc81]
    exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1 h1
  have hnK : (3 : ℝ) ^ n ≤ (3 : ℝ) ^ K := pow_le_pow_right₀ (by norm_num) (by omega)
  have hgeo : 12 * (3 * κd + 4) / r' * (3 : ℝ) ^ n ≤ (3 : ℝ) ^ K := by
    have h1 : 0 ≤ 243 * Cloc := by linarith only [hCloc]
    have : 12 * (3 * κd + 4) / r' ≤ B₀ := by linarith only [h1, hB₀]
    nlinarith only [this, h3n, hB]
  have h12 : 12 * (3 : ℝ) ^ n ≤ (3 : ℝ) ^ K * r' := by
    have e : 12 * (3 * κd + 4) / r' * (3 : ℝ) ^ n * r' = 12 * (3 * κd + 4) * (3 : ℝ) ^ n := by
      field_simp
    have h1 := mul_le_mul_of_nonneg_right hgeo hr'0.le
    rw [e] at h1
    nlinarith only [h1, hκd0, h3n]
  have h3r : 3 * (4 * (3 : ℝ) ^ n) ≤
      ((3 : ℝ) ^ K * r') / (3 * ((d : ℝ) + (1 + d) * max M₁ 0) + 4) := by
    rw [← hκd, le_div_iff₀ (by positivity)]
    have e : 12 * (3 * κd + 4) / r' * (3 : ℝ) ^ n * r' = 12 * (3 * κd + 4) * (3 : ℝ) ^ n := by
      field_simp
    have h1 := mul_le_mul_of_nonneg_right hgeo hr'0.le
    rw [e] at h1
    linarith only [h1]
  -- the domain
  set l : ℝ := ((3 : ℝ) ^ K)⁻¹ * R with hl
  have hl1 : 1 / 3 < l := by
    rw [hl, lt_inv_mul_iff₀ h3K]; linarith only [hR1]
  have hl2 : l ≤ 1 := by
    rw [hl, inv_mul_le_iff₀ h3K]; linarith only [hR2]
  have hsmul : ((3 : ℝ) ^ K)⁻¹ • (R • U) = l • U := by rw [smul_smul]
  have hUl : IsUniformC11Domain (((3 : ℝ) ^ K)⁻¹ • (R • U)) r' M₁ M₂' D' := by
    rw [hsmul]; exact linf_smooth_unif_dil hUd hl1 hl2
  obtain ⟨hWK, hWax, hWn⟩ := linf_smooth_dom hU0 hR0 hR2
  have hne : (R • U).Nonempty := hU.2.1.nonempty.smul_set
  obtain ⟨hUV, hW0, -, hratio⟩ := Hgeom hWK hUl hne h12
  have hWo : IsOpen (R • U) := hUV.1
  have hWm : MeasurableSet (R • U) := hWo.measurableSet
  have hWb : Bornology.IsBounded (R • U) := l2c_bounded hUV
  have : IsFiniteMeasure (volumeMeasureOn (R • U)) :=
    ⟨by
      show volume.restrict (R • U) Set.univ < ⊤
      rw [Measure.restrict_apply_univ]
      exact hWb.measure_lt_top⟩
  have hEllW : IsEllipticFieldOn ν Λ (R • U) ac := wh2_isEllipticFieldOn_mono hWm hWK hell
  -- the centred field
  have hfla : MemVectorL2 (R • U) (fun x => matVecMul (a x) (v.grad x)) := by
    have h2 := (memVectorL2_matVecMul_of_isEllipticFieldOn hEllW v.grad_memVectorL2).sub
      (SuperdiffusionCLT.Section2.CoarseGraining.memVectorL2_matVecMul_const K₀
        v.grad_memVectorL2)
    have e : (fun x => matVecMul (a x) (v.grad x)) =
        ((fun x => matVecMul (ac x) (v.grad x)) - fun x => matVecMul K₀ (v.grad x)) := by
      funext x
      rw [Pi.sub_apply, hK0 x, add_matVecMul]
      abel
    rw [e]
    exact h2
  have hvc : IsWeakSolutionOn ac (R • U) v f (fun _ => 0) :=
    (isWeakSolutionOn_congr_const_skew hWo hskew (a := a) (b := ac) hK0 hfla).2 hv
  -- the scale `τ` and the layer
  set t : ℝ := (3 : ℝ) ^ n / (3 : ℝ) ^ K with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 := by rw [ht, div_le_one h3K]; exact hnK
  have hd0 : (0 : ℝ) < d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith only [this]
  set θ₀ : ℝ := 1 / (2 * (d : ℝ)) with hθ₀
  have hθ₀0 : 0 < θ₀ := by positivity
  have hθ₀1 : θ₀ ≤ 1 := by
    rw [hθ₀, div_le_one (by positivity)]
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith only [this]
  set τ : ℝ := t ^ θ₀ with hτdef
  have hτ0 : 0 ≤ τ := Real.rpow_nonneg ht0.le _
  have htτ : t ≤ τ := by
    have := Real.rpow_le_rpow_of_exponent_ge ht0 ht1 hθ₀1
    rwa [Real.rpow_one] at this
  have hτ : (3 : ℝ) ^ n ≤ τ * (3 : ℝ) ^ K := by
    have e : (3 : ℝ) ^ n = t * (3 : ℝ) ^ K := by rw [ht]; field_simp
    rw [e]; exact mul_le_mul_of_nonneg_right htτ h3K.le
  have hθl : (volume (boundaryLayer (R • U) (3 * (4 * (3 : ℝ) ^ n))) / volume (R • U)) ^
      (1 / (2 * (d : ℝ))) ≤ ENNReal.ofReal (cθ * τ) := by
    refine (ENNReal.rpow_le_rpow hratio hθ₀0.le).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hθ₀0.le, Real.mul_rpow hcvol.le ht0.le]
  -- the local bounds
  set G2 : ℝ := G / (3 : ℝ) ^ nC with hG2
  have hG20 : 0 ≤ G2 := div_nonneg hG (pow_nonneg (by norm_num) _)
  have hgt2 : ContDiff ℝ 2 gt := hgt.of_le (by simp)
  have hgt1 : ContDiff ℝ 1 gt := hgt.of_le (by simp)
  set Hs : ℝ := (lpBar (R • U) 2 (fun x => v.toFun x - gt 0)).toReal +
    (lpBar (R • U) 2 (fun x => v.toFun x - gt x)).toReal with hHs
  set Rb : ℝ := Cloc * Cl * (((3 : ℝ)⁻¹) ^ K * Hs + σ⁻¹ * (3 : ℝ) ^ K * F +
    ((K : ℝ) - (n : ℝ)) * G + (K : ℝ) ^ (-E) * (3 : ℝ) ^ K * G2) with hRb
  intro hcell hblock
  obtain ⟨hGb, hBb⟩ := Hloc a ν σ Cl E K n (K - 1) R hν hσ0 hCl hE (by omega) hn4 hR1 hR2
    hCloc81 f gt F G G2 (gt 0) hgt2 hF hG hG20 hfF hfm hgtG hgt2G v hv hvmem hblock Rb rfl
  clear hblock
  revert hcell
  -- the bound of the oscillation terms
  have hH := HH hWo (fun _ => -((3 : ℝ) ^ K / 2)) h3K hWax hWn hW0 hσ0 f hF hG hfm hfF hgt1 hgtG
    v vh hvh hvhmem
  -- the cell bounds of the fluxes
  have hKp0 : 0 ≤ l2e_Kp d := by
    have hB : 0 ≤ l2e_bumpB d := (abs_nonneg _).trans (l2e_bump_bound d 0)
    unfold l2e_Kp
    positivity
  obtain ⟨hp1, -, -, -⟩ := l2d_exponents hd
  have hp0 : 0 < Real.conjExponent (sobStar d) := by linarith only [hp1]
  have hηs : ∀ w : Vec d, (∃ i, 1 < |w i|) → li1_bump d w = 0 := (l2c_mollifier_witness d).2.2.2
  have hKn0 : 0 ≤ (K : ℝ) - (n : ℝ) := by
    have : (n : ℝ) ≤ K := by exact_mod_cast (show n ≤ K by omega)
    linarith only [this]
  have hHs0 : 0 ≤ Hs := add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hRb0 : 0 ≤ Rb := linf_smooth_Rb_nonneg (zero_le_one.trans hCloc) (zero_le_one.trans hCl) hσ0 hF hG hG20 hHs0
    hKn0 hK1
  set Gb : ℝ := Real.sqrt σ * (Real.sqrt ν)⁻¹ * Rb with hGbdef
  have hGb0 : 0 ≤ Gb :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (inv_nonneg.2 (Real.sqrt_nonneg _))) hRb0
  obtain ⟨haC0, hb0, he0, hg0⟩ := linf_smooth_l2e_nonneg (ρ := ρ) (n := n) (zero_le_one.trans hCin)
    hσ0 hν hδ0 (by linarith only [hK1])
  intro hcell
  have hflux : ∀ kk : Fin d → ℤ, l2b_cell (l2b_pt n kk) (n + 1) ⊆ R • U →
      ∀ x ∈ l2b_cell (l2b_pt n kk) n,
        ‖a16_mollify d ((3 : ℝ) ^ n) (li1_bump d)
            (fun y => l2d_flux ac (R • U) v y - σ • l2d_gradc (R • U) v y) x‖ ≤
          (l2e_Kp d * l2e_aC Cin σ ν δ) * Gb + (l2e_Kp d * l2e_b Cin σ ν ρ δ K n) * F ∧
        ‖a16_mollify d ((3 : ℝ) ^ n) (li1_bump d) (l2d_flux ac (R • U) v) x‖ ≤
          (l2e_Kp d * l2e_aC Cin σ ν δ + σ * l2e_Kp d * l2e_e Cin σ ν) * Gb +
            (l2e_Kp d * l2e_b Cin σ ν ρ δ K n + σ * l2e_Kp d * l2e_g Cin σ ν n) * F := by
    intro kk hcs x hx
    obtain ⟨b1, b2⟩ := hcell v f hfm.aemeasurable hvc kk hcs x hx
    have c3 : a16_mollify d ((3 : ℝ) ^ n) (li1_bump d)
          (fun y => l2d_flux ac (R • U) v y - σ • l2d_gradc (R • U) v y) x =
        a16_mollify d ((3 : ℝ) ^ n) (li1_bump d)
          (fun y => matVecMul (ac y - σ • (1 : Mat d)) (v.grad y)) x := by
      refine l2e_mollify_congr hcs hx hηs fun y hy => ?_
      simp only [l2d_flux, l2d_gradc, Set.indicator_of_mem hy, l2e_matVecMul_sub_smul_one]
    have c2 : a16_mollify d ((3 : ℝ) ^ n) (li1_bump d) (l2d_flux ac (R • U) v) x =
        a16_mollify d ((3 : ℝ) ^ n) (li1_bump d) (fun y => matVecMul (ac y) (v.grad y)) x := by
      refine l2e_mollify_congr hcs hx hηs fun y hy => ?_
      simp only [l2d_flux, Set.indicator_of_mem hy]
    rw [c3, c2]
    constructor
    · exact linf_smooth_flux_real hcs hp0 hF hfF (mul_nonneg hKp0 haC0) (mul_nonneg hKp0 hb0)
        hGb0 (hGb kk hcs) (linf_smooth_ofReal_mul_two hKp0 b1)
    · exact linf_smooth_flux_real hcs hp0 hF hfF
        (add_nonneg (mul_nonneg hKp0 haC0) (mul_nonneg (mul_nonneg hσ0.le hKp0) he0))
        (add_nonneg (mul_nonneg hKp0 hb0) (mul_nonneg (mul_nonneg hσ0.le hKp0) hg0)) hGb0
        (hGb kk hcs)
        (linf_smooth_ofReal_mul_four hKp0 hσ0.le haC0 hb0 he0 hg0 b2)
  clear hcell
  -- the deterministic assembly
  have hdet := Hdet hUV (le_of_eq (by field_simp)) (le_of_eq (by field_simp)) h3r hW0
    (fun _ => -((3 : ℝ) ^ K / 2)) h3K hWax (θ := cθ * τ) (mul_nonneg hcθ0 hτ0) hθl ac hν hνΛ hσ0
    hEllW v vh f hgt1 hfm hvc hvh hvmem hvhmem (mul_nonneg hKp0 haC0) (mul_nonneg hKp0 hb0)
    (add_nonneg (mul_nonneg hKp0 haC0) (mul_nonneg (mul_nonneg hσ0.le hKp0) he0))
    (add_nonneg (mul_nonneg hKp0 hb0) (mul_nonneg (mul_nonneg hσ0.le hKp0) hg0)) hGb0
    (mul_nonneg h3n.le hRb0) hF hG hfF hgtG hGb hBb hflux
  -- the third term is the centred flux
  have e3 : (fun x => matVecMul (σ⁻¹ • (a x - Mavg)) (v.grad x) - vh.grad x) =
      (fun x => σ⁻¹ • matVecMul (ac x) (v.grad x) - vh.grad x) := by
    funext x; rw [hid x, s12_matVecMul_smul_left]
  rw [e3]
  -- the numerics
  have herr := linf_smooth_err (k := (K : ℝ)) (n := n) (L := (3 : ℝ) ^ K) (τ := τ) (cθ := cθ)
    (cΛ := cΛ) (Q := Q) (Rb := Rb) (F := F) (G := G) (Kp := l2e_Kp d) (Cin := Cin) (δ := δ)
    (ρ := ρ) (Λ := Λ) (q := (Λ / ν) ^ (deGiorgiPower d + 1)) hK1 hν hKν hν1 hσ1 hσK hδ0 hδK
    hρ1 (by linarith only [hCin]) hKp0 h3K hnK hτ hcθ0 (le_trans hν.le hνΛ) hΛ
    (Real.rpow_nonneg (div_nonneg (le_trans hν.le hνΛ) hν.le) _) hQ hRb0 hF hG
  have hQ0 : 0 ≤ Q := le_trans (Real.rpow_nonneg (div_nonneg (le_trans hν.le hνΛ) hν.le) _) hQ
  have hdet2 := hdet.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left herr
    (zero_le_one.trans hCd)))
  exact linf_smooth_tail (zero_le_one.trans hCd) hKp0 (zero_le_one.trans hCin) hδ0 hCH.le (zero_le_one.trans hCloc)
    (zero_le_one.trans hCl) hN hF hG hσ0 hRb0 hτ0 hQ0 hcθ0 hK3 hdet2 hH hHs hG2 hRb hKn hEn hϖ
    hsmall

end SuperdiffusionCLT.Section7
