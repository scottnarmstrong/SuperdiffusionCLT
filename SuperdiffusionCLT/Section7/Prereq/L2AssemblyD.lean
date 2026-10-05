/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.L2AssemblyC

/-!
# Scale-uniform forms of the layer estimates

The layer Poincare inequality, the boundary terms `w - u` and `∇ζ (η_h ∗ ũ - g)`, the datum term
`(1 - ζ) ∇g`, and the two duality terms, with constants independent of the scale `r₀` of the
domain.
-/

@[expose] public section

open MeasureTheory Set Filter Homogenization
open scoped ENNReal NNReal Pointwise

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- **The layer Poincaré inequality for `u - g`**, scale-free constants. -/
theorem l2d_poincare [NeZero d] (M₁ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {r₀ : ℝ} {W : Set (Vec d)} {M₂ D : ℝ},
      IsUniformC11Domain W r₀ M₁ M₂ D → ∀ (u g : H1Function W) (ψ : H10Function W),
        ψ.toH1Function = u - g → ∀ {r : ℝ}, 0 < r →
        3 * r ≤ r₀ / (3 * ((d : ℝ) + (1 + d) * max M₁ 0) + 4) → ∀ {S : Set (Vec d)},
          S ⊆ boundaryLayer W (3 * r) →
          eLpNorm (fun x => u.toFun x - g.toFun x) 2 (volume.restrict S) ≤
            ENNReal.ofReal (C * (3 * r)) *
              (eLpNorm u.grad 2 (volume.restrict W) + eLpNorm g.grad 2 (volume.restrict W)) := by
  obtain ⟨CP, hCP, H⟩ := l2d_hPoinc (d := d) M₁
  refine ⟨CP / 3, by positivity, fun {r₀ W M₂ D} hU u g ψ hψ r hr h3r S hS => ?_⟩
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  have hH := H hU (q := 2) (by norm_num) hr h3r hS ψ
  rw [← h2] at hH
  have hf : ∀ x, ψ.toH1Function.toFun x = u.toFun x - g.toFun x := fun x => by
    rw [hψ, H1Function.sub_toFun]
  have hgr : ∀ x, ψ.toH1Function.grad x = u.grad x - g.grad x := fun x => by
    rw [hψ, H1Function.sub_grad]
  have hfun : ψ.toH1Function.toFun = fun x => u.toFun x - g.toFun x := funext hf
  rw [hfun] at hH
  refine hH.trans ?_
  have e : CP / 3 * (3 * r) = CP * r := by ring
  rw [e]
  gcongr
  rw [eLpNorm_norm _ ((l2c_aesm_grad ψ.toH1Function))]
  have hgfun : ψ.toH1Function.grad = u.grad - g.grad := funext hgr
  rw [hgfun]
  exact eLpNorm_sub_le (by norm_num)


/-- **The boundary term `e.Dir.new.boundary.u.term`** with scale-free constants. -/
theorem l2d_E5_unif [NeZero d] (M₁ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {r₀ : ℝ} {W : Set (Vec d)} {M₂ D : ℝ}
      (hU : IsUniformC11Domain W r₀ M₁ M₂ D) {r h : ℝ} (hr : 0 < r),
      3 * r ≤ r₀ / (3 * ((d : ℝ) + (1 + d) * max M₁ 0) + 4) → 0 < h → h ≤ r / 4 →
      ∀ {η : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) η → (∀ w, 0 ≤ η w) → ∫ w, η w = 1 →
      (∀ w, (∃ i, 1 < |w i|) → η w = 0) →
      ∀ (u g : H1Function W) (ψ : H10Function W), ψ.toH1Function = u - g →
      ∀ {p : ℝ}, 1 ≤ p → p ≤ 2 → volume W ≠ 0 →
        lpBar W (ENNReal.ofReal p) (fun x =>
            (l2a_moll d h η (l2c_ext hU.1 (l2c_bounded hU) hr u).toFun x - g.toFun x) •
              lipGradient (l2a_cutoff W r) x) ≤
          (volume (boundaryLayer W (3 * r)) / volume W) ^ (1 / p - 1 / 2) *
            (ENNReal.ofReal C * (lpBar W 2 u.grad + lpBar W 2 g.grad)) := by
  obtain ⟨C₁, hC₁, HP⟩ := l2d_poincare (d := d) M₁
  refine ⟨d / 4 + 3 * C₁, by positivity, ?_⟩
  intro r₀ W M₂ D hU r h hr h3r hh hhr η hη hη0 hη1 hηs u g ψ hψ p hp1 hp2 hW0
  have hWb := l2c_bounded hU
  have hWt : volume W ≠ ⊤ := hWb.measure_lt_top.ne
  have hraw := l2c_E5_raw hU.1 hWb hr hh hhr hη hη0 hη1 hηs u g hC₁ (fun S hS =>
    HP hU u g ψ hψ hr h3r hS)
  have hFm := l2c_E5_meas hU.1 hWb hr hh hη hηs u g
  refine (l2c_holder_layer hU.1.measurableSet hW0 hWt hp1 hp2 hFm
    (L := boundaryLayer W (3 * r)) (fun x hx hxl => l2c_E5_zero hWb hr hx hxl)).trans ?_
  gcongr
  rw [l2c_lpBar_two hFm, l2c_lpBar_two (l2c_aesm_grad u), l2c_lpBar_two (l2c_aesm_grad g),
    ← mul_add, ← mul_assoc, mul_comm (ENNReal.ofReal _), mul_assoc]
  gcongr

/-- **The difference `w - u`** (`e.Dir.new.w.minus.u`) with scale-free constants. -/
theorem l2d_wu_unif [NeZero d] (M₁ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {r₀ : ℝ} {W : Set (Vec d)} {M₂ D : ℝ}
      (hU : IsUniformC11Domain W r₀ M₁ M₂ D) {r h : ℝ} (hr : 0 < r),
      3 * r ≤ r₀ / (3 * ((d : ℝ) + (1 + d) * max M₁ 0) + 4) → ∀ (hh : 0 < h),
      h ≤ r / 4 →
      ∀ {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η), (∀ w, 0 ≤ η w) → ∫ w, η w = 1 →
      ∀ (hηs : ∀ w, (∃ i, 1 < |w i|) → η w = 0),
      ∀ (u g : H1Function W) (ψ : H10Function W), ψ.toH1Function = u - g →
        lpBar W 2 (fun x => (l2a_wH1 hU.1 (l2c_bounded hU) hh hη hηs
            (l2c_ext hU.1 (l2c_bounded hU) hr u) g (l2a_cutoff_lipschitz W hr)
            (l2a_cutoff_nonneg W r) (l2a_cutoff_le_one W r)).toFun x - u.toFun x) ≤
          ENNReal.ofReal (C * (h + r)) * (lpBar W 2 u.grad + lpBar W 2 g.grad) := by
  obtain ⟨C₁, hC₁, HP⟩ := l2d_poincare (d := d) M₁
  refine ⟨d + 3 * C₁, by positivity, ?_⟩
  intro r₀ W M₂ D hU r h hr h3r hh hhr η hη hη0 hη1 hηs u g ψ hψ
  have hWb := l2c_bounded hU
  have hraw := l2c_wu_raw hU.1 hWb hr hh hhr hη hη0 hη1 hηs u g (C₁ := C₁) (fun S hS =>
    HP hU u g ψ hψ hr h3r hS)
  have hm : AEStronglyMeasurable (fun x => (l2a_wH1 hU.1 hWb hh hη hηs
      (l2c_ext hU.1 hWb hr u) g (l2a_cutoff_lipschitz W hr) (l2a_cutoff_nonneg W r)
      (l2a_cutoff_le_one W r)).toFun x - u.toFun x) (volume.restrict W) :=
    (l2c_aesm_toFun _).sub (l2c_aesm_toFun u)
  rw [l2c_lpBar_two hm, l2c_lpBar_two (l2c_aesm_grad u), l2c_lpBar_two (l2c_aesm_grad g),
    ← mul_add, mul_left_comm]
  gcongr
  refine hraw.trans ?_
  set A := eLpNorm u.grad 2 (volume.restrict W)
  set B := eLpNorm g.grad 2 (volume.restrict W)
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hh0 := hh.le
  calc ENNReal.ofReal (d * h) * A + ENNReal.ofReal (C₁ * (3 * r)) * (A + B)
      ≤ ENNReal.ofReal (d * h) * (A + B) + ENNReal.ofReal (C₁ * (3 * r)) * (A + B) := by
        gcongr; exact le_self_add
    _ = ENNReal.ofReal (d * h + C₁ * (3 * r)) * (A + B) := by
        rw [← add_mul, ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal ((d + 3 * C₁) * (h + r)) * (A + B) := by
        gcongr
        nlinarith only [mul_nonneg hd hr.le, mul_nonneg hC₁ hh0, hr, hC₁, hd, hh0]

/-- **The datum term** `‖(1 - ζ) G‖_{L̲^p}` with the layer of width `3 r` and the cutoff `ζ` of
margin `r`. -/
theorem l2d_E4 [NeZero d] {W : Set (Vec d)} {r₀ M₁ M₂ D : ℝ}
    (hU : IsUniformC11Domain W r₀ M₁ M₂ D) {r : ℝ} (hr : 0 < r) {p : ℝ} (hp1 : 1 ≤ p)
    (hp2 : p ≤ 2) (hW0 : volume W ≠ 0) {G : Vec d → Vec d}
    (hG : AEStronglyMeasurable G (volume.restrict W)) :
    lpBar W (ENNReal.ofReal p) (fun x => (1 - l2a_cutoff W r x) • G x) ≤
      (volume (boundaryLayer W (3 * r)) / volume W) ^ (1 / p - 1 / 2) * lpBar W 2 G := by
  have hWt : volume W ≠ ⊤ := (l2c_bounded hU).measure_lt_top.ne
  have he : 0 ≤ 1 / p - 1 / 2 := by
    have : 1 / 2 ≤ 1 / p := one_div_le_one_div_of_le (by linarith only [hp1]) hp2
    linarith only [this]
  refine (l2c_boundary_g_term hU.1.measurableSet hW0 hWt hp1 hp2 (l2a_cutoff_continuous W hr)
    (l2a_cutoff_nonneg W r) (l2a_cutoff_le_one W r) hG).trans ?_
  refine mul_le_mul' ?_ le_rfl
  refine l2c_ratio_le ?_ he
  refine (measure_mono ((l2a_cutoff_layer_subset hU.2.2.1 hr).trans ?_))
  intro x hx
  exact ⟨hx.1, lt_trans hx.2 (by linarith only [hr])⟩


/-- **The layer term with the cutoff**, scale-free constant (`l2b_E2_cutoff` with `l2d_hPoinc`). -/
theorem l2d_E2_cutoff [NeZero d] (M₁ : ℝ) :
    ∃ CP : ℝ, 0 ≤ CP ∧ ∀ {r₀ : ℝ} {W : Set (Vec d)} {M₂ D : ℝ},
      IsUniformC11Domain W r₀ M₁ M₂ D → ∀ (n : ℕ) {r : ℝ}, 0 < r →
        3 * r ≤ r₀ / (3 * ((d : ℝ) + (1 + d) * max M₁ 0) + 4) →
        2 * (3 : ℝ) ^ n < r → volume W ≠ 0 → volume W ≠ ⊤ → ∀ {G : Vec d → Vec d},
        AEStronglyMeasurable G (volume.restrict W) → ∀ {v w : Vec d → ℝ},
        AEStronglyMeasurable v (volume.restrict W) → AEStronglyMeasurable w (volume.restrict W) →
        ∀ {p : ℝ}, 1 < p → p < 2 → ∀ {α β : ℝ≥0∞},
        (∀ k : Fin d → ℤ, l2b_cell (l2b_pt n k) (n + 1) ⊆ W →
          ∀ x ∈ l2b_cell (l2b_pt n k) n, ENNReal.ofReal ‖G x‖ ≤
            α * l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ))))
                (l2b_cell (l2b_pt n k) (n + 1)) (fun x => ‖v x‖ₑ) 2 +
              β * l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ))))
                (l2b_cell (l2b_pt n k) (n + 1)) (fun x => ‖w x‖ₑ) p) →
        wMinusOneBar W (ENNReal.ofReal p)
            (fun x => vecDot (lipGradient (l2a_cutoff W r) x) (G x)) ≤
          ENNReal.ofReal (d * CP) *
            (α * (volume (boundaryLayer W (3 * r)) * (volume W)⁻¹) ^ (1 / p - 1 / 2) *
                lpBar W (ENNReal.ofReal 2) v +
              β * lpBar W (ENNReal.ofReal p) w) := by
  obtain ⟨CP, hCP, H⟩ := l2d_hPoinc (d := d) M₁
  refine ⟨CP, hCP, ?_⟩
  intro r₀ W M₂ D hU n r hr h3r hn hW0 hWT G hGm v w hvm hwm p hp1 hp2 α β hG
  have hWm : MeasurableSet W := hU.1.measurableSet
  have hAD : l2b_layerA W r ⊆ boundaryLayer W (3 * r) := fun x hx =>
    l2b_layer_of_infDist hU.2.2.1 (l2b_layerA_subset hr hx) (by linarith only [hx.2, hr])
  have hq1 : 1 ≤ p / (p - 1) := by
    rw [le_div_iff₀ (by linarith only [hp1])]; linarith only
  have hmain := l2b_E2_core n (l2b_layerA_measurable W r) (l2b_layerA_subset hr) hW0 hWT hr
    (l2b_lipGradient_norm_le W hr) (l2b_lipGradient_zero_off hr) (l2b_layerA_marg hn) hGm hvm hwm
    hp1 hp2 hG (CP := CP) (fun ψ => H hU hq1 hr h3r hAD ψ)
  refine hmain.trans (mul_le_mul' le_rfl (add_le_add (mul_le_mul' (mul_le_mul' le_rfl ?_) le_rfl) le_rfl))
  have hθ : 0 ≤ 1 / p - 1 / 2 := by
    have : 1 / 2 ≤ 1 / p := by
      rw [div_le_div_iff₀ (by norm_num) (by linarith only [hp1])]; linarith only [hp2]
    linarith only [this]
  exact ENNReal.rpow_le_rpow (mul_le_mul' (measure_mono hAD) le_rfl) hθ

/-- **The mollification error against `f` with the cutoff**, scale-free constant. -/
theorem l2d_E1_cutoff [NeZero d] (M₁ : ℝ) :
    ∃ CP : ℝ, 0 ≤ CP ∧ ∀ {r₀ : ℝ} {W : Set (Vec d)} {M₂ D : ℝ},
      IsUniformC11Domain W r₀ M₁ M₂ D → ∀ (n : ℕ) {r : ℝ}, 0 < r →
        3 * r ≤ r₀ / (3 * ((d : ℝ) + (1 + d) * max M₁ 0) + 4) →
        2 * (3 : ℝ) ^ n < r → volume W ≠ 0 → volume W ≠ ⊤ → ∀ {η : Vec d → ℝ}, Continuous η →
        ∀ {Bη : ℝ}, (∀ w, |η w| ≤ Bη) → (∀ w, 0 ≤ η w) → ∫ w, η w = 1 →
        (∀ w, (∃ i, 1 < |w i|) → η w = 0) → ∀ {p q : ℝ}, p.HolderConjugate q →
        ∀ {f : Vec d → ℝ}, IntegrableOn f W volume →
        (∀ ψ : H10Function W, IntegrableOn (fun x => f x * ψ.toH1Function.toFun x) W volume) →
        wMinusOneBar W (ENNReal.ofReal p)
            (fun x => l2a_cutoff W r x * l2a_moll d ((3 : ℝ) ^ n) η f x - f x) ≤
          ENNReal.ofReal (d * (3 : ℝ) ^ n + CP * r) * lpBar W (ENNReal.ofReal p) f := by
  obtain ⟨CP, hCP, H⟩ := l2d_hPoinc (d := d) M₁
  refine ⟨CP, hCP, ?_⟩
  intro r₀ W M₂ D hU n r hr h3r hn hW0 hWT η hηc Bη hηA hη0 hη1 hηs p q hpq f hfi hfψ
  have hWm : MeasurableSet W := hU.1.measurableSet
  have h3 : (0 : ℝ) < 3 ^ n := by positivity
  have hLB : l2b_layerB W r ⊆ boundaryLayer W (3 * r) := fun x hx =>
    l2b_layer_of_infDist hU.2.2.1 hx.1 (by linarith only [hx.2, hr])
  exact l2b_E1_core hWm (l2b_bounded_of_uniform hU) hW0 hWT h3 hηc hηA hη0 hη1 hηs
    (l2a_cutoff_continuous W hr).measurable (l2a_cutoff_nonneg W r) (l2a_cutoff_le_one W r)
    (l2b_cutoff_loc hr (by linarith only [hn, h3])) (l2b_layerB_measurable hWm r)
    (l2b_layerB_cover hr) (mul_nonneg hCP hr.le) hpq
    (fun ψ => H hU hpq.symm.lt.le hr h3r hLB ψ) hfi hfψ


/-- A domain meeting the hypotheses of the scale-free layer estimates with margin `r = 3`:
a dilate of the unit Euclidean ball. -/
theorem l2d_witness_domain [NeZero d] :
    ∃ (W : Set (Vec d)) (r₀ M₁ M₂ D : ℝ), IsUniformC11Domain W r₀ M₁ M₂ D ∧
      3 * (3 : ℝ) ≤ r₀ / (3 * ((d : ℝ) + (1 + d) * max M₁ 0) + 4) ∧ volume W ≠ 0 := by
  obtain ⟨r₁, M₁, M₂, D, hU⟩ := isUniformC11Domain_euclidBall (d := d)
  have hr1 : 0 < r₁ := hU.2.1
  set κ : ℝ := (d : ℝ) + (1 + d) * max M₁ 0 with hκ
  have hκ0 : 0 ≤ κ := by
    have : 0 ≤ max M₁ 0 := le_max_right _ _
    positivity
  set R : ℝ := 9 * (3 * κ + 4) / r₁ + 1 with hR
  have hR0 : 0 < R := by positivity
  have hRU := hU.smul hR0
  have hne : (R • Section6.euclidBall (d := d) 1).Nonempty :=
    ⟨R • (0 : Vec d), Set.smul_mem_smul_set (by simp [Section6.euclidBall, vecNormSq, vecDot])⟩
  refine ⟨_, _, _, _, _, hRU, ?_, (hRU.1.measure_pos volume hne).ne'⟩
  rw [le_div_iff₀ (by positivity)]
  have : 9 * (3 * κ + 4) ≤ R * r₁ := by
    rw [hR, add_mul, div_mul_cancel₀ _ hr1.ne']; linarith only [hr1]
  linarith only [this, hκ]

/-- Witness for the scale-free layer estimates: zero data on the dilate of the unit ball. -/
example : True := by
  obtain ⟨W, r₀, M₁, M₂, D, hU, h3, hW0⟩ := l2d_witness_domain (d := 2)
  have hWT : volume W ≠ ⊤ := (l2c_bounded hU).measure_lt_top.ne
  obtain ⟨CP, hCP, H2⟩ := l2d_E2_cutoff (d := 2) M₁
  have _ := H2 hU 0 (r := 3) (by norm_num) h3 (by norm_num) hW0 hWT (G := fun _ => 0)
    aestronglyMeasurable_const (v := fun _ => 0) (w := fun _ => 0) aestronglyMeasurable_const
    aestronglyMeasurable_const (p := 3 / 2) (by norm_num) (by norm_num) (α := 0) (β := 0)
    (fun k _ x _ => by simp)
  obtain ⟨CP', hCP', H1⟩ := l2d_E1_cutoff (d := 2) M₁
  obtain ⟨η, Bη, L, hηc, hη0, hη1, hηA, -, hηs⟩ := m1_exists_profile 2
  have _ := H1 hU 0 (r := 3) (by norm_num) h3 (by norm_num) hW0 hWT hηc hηA hη0 hη1 hηs
    (p := 2) (q := 2) Real.HolderConjugate.two_two (f := fun _ => 0) (integrableOn_const ..)
    (fun ψ => by simp)
  have _ := l2d_E4 (r := 3) hU (by norm_num) (p := 3 / 2) (by norm_num) (by norm_num) hW0
    (G := fun _ => 0) aestronglyMeasurable_const
  obtain ⟨CE, hCE, H5⟩ := l2d_E5_unif (d := 2) M₁
  obtain ⟨η', hη', hηs'⟩ := l2a_exists_smooth_profile 2
  trivial

end SuperdiffusionCLT.Section7
