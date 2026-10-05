/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Linfty.Core

/-!
# The comparison function against the homogenized solution: the main estimate

Displays `e.Dir.new.Linfty.Morrey`, `e.Dir.new.Linfty.CZ` and `e.Dir.new.Linfty.w.vhom`.
-/

@[expose] public section

open MeasureTheory Set Filter Homogenization
open scoped ENNReal NNReal Pointwise

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The scalar data `h₁ + h₂` of the equation for `w - v̄` are in `L²`, when `f` and the
mollified flux are bounded. -/
theorem linf_memScalarL2 [NeZero d] {W : Set (Vec d)}
    (hWb : Bornology.IsBounded W) {r h : ℝ} (hr : 0 < r) (hh : 0 < h) {η : Vec d → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηs : ∀ w, (∃ i, 1 < |w i|) → η w = 0) {s : ℝ} (hs : 0 < s)
    {fc : Vec d → ℝ} (hfcl : LocallyIntegrable fc volume)
    (hfcm : AEStronglyMeasurable fc (volume.restrict W)) {F : ℝ}
    (hfcF : ∀ᵐ x ∂volume.restrict W, |fc x| ≤ F) {F' : Vec d → Vec d}
    (hFc : ∀ i, LocallyIntegrable (fun x => F' x i) volume) :
    MemScalarL2 W (fun x => l2d_h1 W r h η s fc x + l2d_h2 W r h η s F' x) := by
  have hfin : IsFiniteMeasure (volume.restrict W) := ⟨by simpa using hWb.measure_lt_top⟩
  have hζc : Continuous (l2a_cutoff W r) := l2a_cutoff_continuous W hr
  have hcs : HasCompactSupport (l2a_cutoff W r) := (l2a_cutoff_compact hWb hr).1
  have hmf : Continuous (l2a_moll d h η fc) :=
    (l2a_moll_contDiff hh hη hηs hfcl).continuous
  have hGc : ∀ i, Continuous fun x => a16_mollify d h η F' x i := fun i =>
    (l2a_moll_contDiff hh hη hηs (hFc i)).continuous
  obtain ⟨BZ, hBZ⟩ := l2d_bdd_of_compact (hζc.mul hmf) hcs.mul_right
  obtain ⟨B2, hB2⟩ := l2d_lip_dot_bdd (V := W) hr hcs hGc
  have hdot : Measurable fun x => vecDot (lipGradient (l2a_cutoff W r) x) (a16_mollify d h η F' x) := by
    simp only [vecDot]
    exact Finset.measurable_sum _ fun i _ =>
      ((measurable_pi_apply i).comp (l2b_lipGradient_measurable (l2a_cutoff W r))).mul
        ((measurable_pi_apply i).comp (continuous_pi hGc).measurable)
  refine MemLp.of_bound ?_ (s⁻¹ * (BZ + F + B2)) ?_
  · refine AEStronglyMeasurable.add ?_ ?_
    · exact (aestronglyMeasurable_const.mul
        ((hζc.mul hmf).aestronglyMeasurable.sub hfcm))
    · exact (aestronglyMeasurable_const.mul hdot.aestronglyMeasurable)
  · filter_upwards [hfcF] with x hx
    have h1 : |l2a_cutoff W r x * l2a_moll d h η fc x| ≤ BZ := by
      have := hBZ x
      rwa [Real.norm_eq_abs] at this
    have h2 : |vecDot (lipGradient (l2a_cutoff W r) x) (a16_mollify d h η F' x)| ≤ B2 := by
      have := hB2 x
      rwa [Real.norm_eq_abs] at this
    rw [Real.norm_eq_abs]
    have hs' : l2d_h1 W r h η s fc x + l2d_h2 W r h η s F' x =
        s⁻¹ * (l2a_cutoff W r x * l2a_moll d h η fc x - fc x -
          vecDot (lipGradient (l2a_cutoff W r) x) (a16_mollify d h η F' x)) := by
      simp only [l2d_h1, l2d_h2]; ring
    rw [hs', abs_mul, abs_of_pos (inv_pos.2 hs)]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hs.le)
    have a1 := abs_le.1 h1
    have a2 := abs_le.1 hx
    have a3 := abs_le.1 h2
    exact abs_le.2 ⟨by linarith only [a1.1, a2.2, a3.2], by linarith only [a1.2, a2.1, a3.1]⟩

/-- **The comparison function against the homogenized solution** (`e.Dir.new.Linfty.Morrey`,
`e.Dir.new.Linfty.CZ`, `e.Dir.new.Linfty.w.vhom`): the sup norm of `w - v̄` and
the `L^{2d}` norm of its gradient, from sup bounds of the mollified fluxes. -/
theorem linf_core [NeZero d] (hd : 2 ≤ d) (M₁ κ ρ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {r₀ : ℝ} {W : Set (Vec d)} {M₂ D : ℝ}
      (hU : IsUniformC11Domain W r₀ M₁ M₂ D), r₀ * M₂ ≤ κ → D ≤ ρ * r₀ →
      ∀ {n : ℕ} {r : ℝ} (hr : 0 < r),
      3 * r ≤ r₀ / (3 * ((d : ℝ) + (1 + d) * max M₁ 0) + 4) → 2 * (3 : ℝ) ^ n < r →
      (3 : ℝ) ^ n ≤ r / 4 → volume W ≠ 0 → ∀ (z : Vec d) {L : ℝ}, 0 < L → W ⊆ axisCube z L →
      ∀ {η : Vec d → ℝ} {Bη : ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η), (∀ w, |η w| ≤ Bη) →
        (∀ w, 0 ≤ η w) → ∫ w, η w = 1 → ∀ (hηs : ∀ w, (∃ i, 1 < |w i|) → η w = 0) {ϑ : ℝ≥0∞},
        (volume (boundaryLayer W (3 * r)) / volume W) ^ (1 / (2 * (d : ℝ))) ≤ ϑ →
      ∀ (a : CoeffField d) {s : ℝ}, 0 < s → ∀ (v vh : H1Function W) (f : Vec d → ℝ)
        {gt : Vec d → ℝ} (hgt : ContDiff ℝ 1 gt),
        AEStronglyMeasurable f (volume.restrict W) →
        MemVectorL2 W (fun x => matVecMul (a x) (v.grad x)) →
        IsWeakSolutionOn a W v f (fun _ => 0) →
        IsWeakSolutionOn (fun _ => s • (1 : Mat d)) W vh f (fun _ => 0) →
        MemH10 W (fun x => v.toFun x - gt x) → MemH10 W (fun x => vh.toFun x - gt x) →
      ∀ {B1 B2 B5 F G : ℝ}, 0 ≤ B1 → 0 ≤ B2 → 0 ≤ B5 → 0 ≤ F → 0 ≤ G →
        (∀ᵐ x ∂volume.restrict W, |f x| ≤ F) → (∀ x ∈ W, ‖fderiv ℝ gt x‖ ≤ G) →
        (∀ x ∈ W, l2a_cutoff W r x ≠ 0 →
          ‖a16_mollify d ((3 : ℝ) ^ n) η
            (fun y => l2d_flux a W v y - s • l2d_gradc W v y) x‖ ≤ B1) →
        (∀ x ∈ W, lipGradient (l2a_cutoff W r) x ≠ 0 →
          |l2a_moll d ((3 : ℝ) ^ n) η (l2c_ext hU.1 (l2c_bounded hU) hr v).toFun x - gt x| ≤ B2) →
        (∀ x ∈ W, lipGradient (l2a_cutoff W r) x ≠ 0 →
          ‖a16_mollify d ((3 : ℝ) ^ n) η (l2d_flux a W v) x‖ ≤ B5) →
        ∃ φ : H10Function W,
          φ.toH1Function =
            l2d_w hU.1 (l2c_bounded hU) hr (pow_pos (by norm_num : (0 : ℝ) < 3) n) hη hηs
              (l2c_ext hU.1 (l2c_bounded hU) hr v) (li1_h1 hU.1 (p14g_isBoundedDomain hU) hgt) -
              vh ∧
          eLpNorm φ.toH1Function.toFun ⊤ (volume.restrict W) +
              ENNReal.ofReal L * lpBar W (ENNReal.ofReal (2 * d)) φ.toH1Function.grad ≤
            ENNReal.ofReal (C * L) *
              (ENNReal.ofReal (s⁻¹ * B1) + ϑ * ENNReal.ofReal (B2 / r + G) +
                ENNReal.ofReal (s⁻¹ * r * F) + ϑ * ENNReal.ofReal (s⁻¹ * B5)) := by
  obtain ⟨Cm, hCm, HM⟩ := ia_linfty_cz_morrey hd M₁ κ ρ
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hp1 : (1 : ℝ≥0∞) < ENNReal.ofReal (2 * d) := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith only [hdR])).2 (by linarith only [hdR])
  obtain ⟨Cz, hCz, HZ⟩ := cz_unif hd (ENNReal.ofReal (2 * d)) hp1 ENNReal.ofReal_lt_top M₁ κ ρ
  obtain ⟨K₁, K₂, hK₁, hK₂, HH⟩ := linf_h_bound (d := d) M₁
  refine ⟨(Cm + Cz) * (1 + K₁ + K₂), by positivity, ?_⟩
  intro r₀ W M₂ D hU hκ hρ n r hr h3r hn hhr hW0 z L hL hWL η Bη hη hηB hη0 hη1 hηs ϑ hϑ a s hs v vh f gt
    hgt hfm hflux hv hvh hv10 hvh10 B1 B2 B5 F G hB1 hB2 hB5 hF hG hfF hgtG hBm1 hBm2 hBm5
  have hWb := l2c_bounded hU
  have hWm : MeasurableSet W := hU.1.measurableSet
  have hWT : volume W ≠ ⊤ := hWb.measure_lt_top.ne
  have h3 : (0 : ℝ) < 3 ^ n := by positivity
  have hs0 : s ≠ 0 := hs.ne'
  have hfin : IsFiniteMeasure (volume.restrict W) := ⟨by simpa using hWb.measure_lt_top⟩
  set g := li1_h1 hU.1 (p14g_isBoundedDomain hU) hgt with hg
  obtain ⟨ψb, hψb⟩ := l2d_h10_of_mem hU.1 vh g hvh10
  -- the cleaned data
  have hfae : AEStronglyMeasurable (W.indicator f) volume :=
    (aestronglyMeasurable_indicator_iff hWm).2 hfm
  have hfint : Integrable f (volume.restrict W) := Integrable.of_bound hfm F (by
    filter_upwards [hfF] with x hx
    rwa [Real.norm_eq_abs])
  have hfcI : Integrable (W.indicator f) volume := (integrable_indicator_iff hWm).2 hfint
  have hfcF : ∀ᵐ x ∂volume.restrict W, |W.indicator f x| ≤ F := by
    filter_upwards [ae_restrict_mem hWm, hfF] with x hx hb
    simpa [Set.indicator_of_mem hx] using hb
  have hFi : ∀ i, LocallyIntegrable (fun x => l2d_flux a W v x i) volume := by
    intro i
    have h1 : Integrable (fun z => matVecMul (a z) (v.grad z) i) (volume.restrict W) :=
      ((MeasureTheory.memLp_pi_iff.1 hflux i).integrable (by norm_num))
    have h2 := (integrable_indicator_iff hWm).2 h1
    have e : (fun x => l2d_flux a W v x i) =
        W.indicator (fun z => matVecMul (a z) (v.grad z) i) :=
      funext fun x => l2d_indicator_apply W _ x i
    rw [e]
    exact h2.locallyIntegrable
  have hweak : ∀ φ : H10Function W, ∫ x in W, vecDot (l2d_flux a W v x) (φ.toH1Function.grad x) =
      ∫ x in W, W.indicator f x * φ.toH1Function.toFun x := by
    intro φ
    have h0 := hv φ
    have hz : ∫ x in W, vecDot ((fun _ : Vec d => (0 : Vec d)) x) (φ.toH1Function.grad x) = 0 := by
      simp [vecDot]
    rw [hz, add_zero] at h0
    calc ∫ x in W, vecDot (l2d_flux a W v x) (φ.toH1Function.grad x)
        = ∫ x in W, vecDot (matVecMul (a x) (v.grad x)) (φ.toH1Function.grad x) :=
          setIntegral_congr_fun hWm fun x hx => by simp [l2d_flux, Set.indicator_of_mem hx]
      _ = ∫ x in W, f x * φ.toH1Function.toFun x := h0
      _ = _ := setIntegral_congr_fun hWm fun x hx => by simp [Set.indicator_of_mem hx]
  have hhom : ∀ φ : H10Function W, s * ∫ x in W, vecDot (vh.grad x) (φ.toH1Function.grad x) =
      ∫ x in W, W.indicator f x * φ.toH1Function.toFun x := by
    intro φ
    have h0 := hvh φ
    have hz : ∫ x in W, vecDot ((fun _ : Vec d => (0 : Vec d)) x) (φ.toH1Function.grad x) = 0 := by
      simp [vecDot]
    rw [hz, add_zero] at h0
    simp only [l2d_matVecMul_smul_one, l2d_vecDot_smul_left] at h0
    rw [integral_const_mul] at h0
    rw [h0]
    exact setIntegral_congr_fun hWm fun x hx => by simp [Set.indicator_of_mem hx]
  have hfφ : ∀ φ : H10Function W,
      IntegrableOn (fun x => W.indicator f x * φ.toH1Function.toFun x) W := by
    intro φ
    exact Integrable.bdd_mul (l2a_integrableOn_of_memL2 hWb φ.toH1Function.memL2)
      (hfae.mono_measure Measure.restrict_le_self) (by
        filter_upwards [hfcF] with x hx
        rwa [Real.norm_eq_abs])
  obtain ⟨φ, hφH, hsol, hFvL2, hI1, hI2⟩ := l2d_equation hU.1 hWb hr h3 hhr hη hηs
    (l2c_ext hU.1 hWb hr v) g vh ⟨ψb, hψb⟩ (F := l2d_flux a W v) (f := W.indicator f) hFi
    hfcI.locallyIntegrable hweak hs0 hhom hfφ
  have hfcm : AEStronglyMeasurable (W.indicator f) (volume.restrict W) :=
    hfae.mono_measure Measure.restrict_le_self
  have hhL2 := linf_memScalarL2 (W := W) (r := r) (h := (3 : ℝ) ^ n) hWb hr h3 hη hηs (s := s) hs
    hfcI.locallyIntegrable hfcm hfcF hFi
  have hFv := linf_Fv_bound hU hr hhr hη hηs hϑ a hs v hgt hFi hB1 hB2 hG hgtG hBm1 hBm2
  have hHb := HH hU hr h3r hn hhr hW0 hη hηB hη0 hη1 hηs hϑ hs hfcm hF hfcF
    hfcI.integrableOn hfφ hFi hI1 hI2 hB5 hBm5
  have hCZ := HZ hU hκ hρ _ _ φ hFvL2 hhL2 hsol
  have hMo := HM hU hκ hρ hL hWL _ _ φ hFvL2 hhL2 hsol
  refine ⟨φ, hφH, ?_⟩
  have hX := (add_le_add hFv hHb).trans_eq (add_assoc _ _ _).symm |>.trans
    (linf_comb (ENNReal.ofReal (s⁻¹ * B1)) (ϑ * ENNReal.ofReal (B2 / r + G))
      (ENNReal.ofReal (s⁻¹ * r * F)) (ϑ * ENNReal.ofReal (s⁻¹ * B5)) hK₁ hK₂)
  have hC1 : (0 : ℝ) ≤ Cm * L := by positivity
  calc _ ≤ ENNReal.ofReal (Cm * L) * (lpBar W (ENNReal.ofReal (2 * d)) _ + wMinusOneBar W
        (ENNReal.ofReal (2 * d)) _) + ENNReal.ofReal L * (ENNReal.ofReal Cz * (lpBar W
        (ENNReal.ofReal (2 * d)) _ + wMinusOneBar W (ENNReal.ofReal (2 * d)) _)) :=
        add_le_add hMo (mul_le_mul' le_rfl hCZ)
    _ = ENNReal.ofReal ((Cm + Cz) * L) * (lpBar W (ENNReal.ofReal (2 * d)) _ + wMinusOneBar W
        (ENNReal.ofReal (2 * d)) _) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hL.le, ← add_mul, ← ENNReal.ofReal_add hC1
          (by positivity)]
        congr 2
        ring
    _ ≤ ENNReal.ofReal ((Cm + Cz) * L) * (ENNReal.ofReal (1 + K₁ + K₂) * _) :=
        mul_le_mul' le_rfl hX
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring

/-- Satisfiability of `linf_core`: zero data and the identity field on a dilate of the unit ball,
with the standard bump and all sup bounds equal to zero, so that all the hypotheses hold. -/
example : True := by
  obtain ⟨W, r₀, M₁, M₂, D, hU, h3r, hW0⟩ := l2d_witness_domain4 (d := 2)
  have hr0 : 0 < r₀ := hU.2.1
  obtain ⟨C, hC, H⟩ := linf_core (d := 2) le_rfl M₁ (r₀ * M₂) (D / r₀)
  have hWb := l2c_bounded hU
  obtain ⟨ρ, hρ⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Vec 2)).1 hWb
  have hWL : W ⊆ axisCube (fun _ => -(|ρ| + 1)) (2 * (|ρ| + 1)) := by
    intro x hx j _
    have h1 := hρ hx
    rw [mem_closedBall_zero_iff] at h1
    have h2 : |x j| ≤ ‖x‖ := by
      rw [← Real.norm_eq_abs]; exact norm_le_pi_norm x j
    have h3 := abs_le.1 h2
    have h4 := le_abs_self ρ
    simp only [Set.mem_Ioo]
    constructor <;> linarith only [h1, h3.1, h3.2, h4, abs_nonneg ρ]
  obtain ⟨B, hB⟩ := (li1_bump_contDiff 2).continuous.bounded_above_of_compact_support
    (li1_bump_compact 2)
  obtain ⟨hη, hη0, hη1, hηs⟩ := l2c_mollifier_witness 2
  have hext : ∀ y, (l2c_ext hU.1 hWb (show (0 : ℝ) < 4 by norm_num) (0 : H1Function W)).toFun y = 0 := by
    intro y
    by_cases hy : y ∈ W
    · simp [l2c_ext, H10Function.zeroExtension_apply_of_mem _ hy]
    · simp [l2c_ext, H10Function.zeroExtension_apply_of_not_mem _ hy]
  have _ := H hU le_rfl (div_mul_cancel₀ D hr0.ne').ge (n := 0) (r := 4) (by norm_num) h3r
    (by norm_num) (by norm_num) hW0 (fun _ => -(|ρ| + 1)) (L := 2 * (|ρ| + 1)) (by positivity) hWL
    (η := li1_bump 2) (Bη := B) hη (fun w => by simpa [Real.norm_eq_abs] using hB w) hη0 hη1 hηs
    (ϑ := ⊤) le_top (fun _ => (1 : Mat 2)) (s := 1) one_pos (0 : H1Function W)
    (0 : H1Function W) (fun _ => 0) (gt := fun _ => 0) contDiff_const aestronglyMeasurable_const
    ((MeasureTheory.memLp_pi_iff).2 fun i => by simp [matVecMul])
    (fun φ => by simp [vecDot, matVecMul]) (fun φ => by simp [vecDot, matVecMul])
    ⟨0, by funext x; simp; rfl⟩ ⟨0, by funext x; simp; rfl⟩
    (B1 := 0) (B2 := 0) (B5 := 0) (F := 0) (G := 0) le_rfl le_rfl le_rfl le_rfl le_rfl
    (Filter.Eventually.of_forall fun x => by simp) (fun x _ => by simp)
    (fun x _ _ => by
      simp [l2d_flux, l2d_gradc, l2d_matVecMul_zero, Set.indicator_zero', l2d_mollify_zero])
    (fun x _ _ => by simp [hext, l2a_moll])
    (fun x _ _ => by
      simp [l2d_flux, l2d_matVecMul_zero, l2d_mollify_zero])
  trivial

end SuperdiffusionCLT.Section7
