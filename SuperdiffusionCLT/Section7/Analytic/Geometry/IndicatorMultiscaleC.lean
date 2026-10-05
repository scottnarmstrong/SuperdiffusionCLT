/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Geometry.IndicatorMultiscaleB
public import Mathlib.Data.Pi.Interval
public import SuperdiffusionCLT.Section7.Analytic.Geometry.AtlasTransform
public import SuperdiffusionCLT.Section6.Prereq.EuclidBall

/-!
# The indicator of a regular domain in the unit cube is `H^θ` for `θ < 1/2`, multiscale form

For an open `W ⊆ [-1/2, 1/2)^d`, `g = 1_W` and `E j = ` conditional expectation on the generation-`j`
triadic cells, `‖g − E j g‖²_{L²} ≤ |{x ∈ W : dist(x, ∂W) < 3^{-j}}|`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open MeasureTheory Homogenization

variable {d : ℕ}

/-- The unit-cube measure. -/
noncomputable abbrev kc2_μ (d : ℕ) : Measure (Vec d) := (volume : Measure (Vec d)).restrict (kc2_Q0 d)

/-- The cells of generation `j` contained in `W`, as a function of the cell. -/
noncomputable def kc2_good (W : Set (Vec d)) (j : ℕ) (n : Fin d → ℤ) : ℝ :=
  open Classical in if ∀ y ∈ kc2_Q0 d, kc2_proj j y = n → y ∈ W then 1 else 0

theorem kc2_good_of {W : Set (Vec d)} {j : ℕ} {n : Fin d → ℤ}
    (h : ∀ y ∈ kc2_Q0 d, kc2_proj j y = n → y ∈ W) : kc2_good W j n = 1 := by
  unfold kc2_good
  simp only [eq_true h, ↓reduceIte]

theorem kc2_good_of_not {W : Set (Vec d)} {j : ℕ} {n : Fin d → ℤ}
    (h : ¬ ∀ y ∈ kc2_Q0 d, kc2_proj j y = n → y ∈ W) : kc2_good W j n = 0 := by
  unfold kc2_good
  simp only [eq_false h, ↓reduceIte]

theorem kc2_layer_measurable {W : Set (Vec d)} (hW : IsOpen W) (t : ℝ) :
    MeasurableSet (boundaryLayer W t) :=
  hW.measurableSet.inter (measurableSet_lt
    (Metric.continuous_infDist_pt _).measurable measurable_const)

theorem kc2_sq_le_layer {W : Set (Vec d)} (hW : IsOpen W) (j : ℕ) {x : Vec d}
    (hx : x ∈ kc2_Q0 d) :
    (W.indicator (fun _ => (1 : ℝ)) x - kc2_good W j (kc2_proj j x)) ^ 2 ≤
      (boundaryLayer W ((3 ^ j : ℝ)⁻¹)).indicator (fun _ => (1 : ℝ)) x := by
  by_cases hxW : x ∈ W
  · by_cases hc : ∀ y ∈ kc2_Q0 d, kc2_proj j y = kc2_proj j x → y ∈ W
    · have := Set.indicator_nonneg (s := boundaryLayer W ((3 ^ j : ℝ)⁻¹))
        (f := fun _ => (1 : ℝ)) (fun _ _ => zero_le_one) x
      have e : W.indicator (fun _ => (1 : ℝ)) x = 1 := by simp [hxW]
      rw [e, kc2_good_of hc, sub_self, zero_pow two_ne_zero]
      exact this
    · rw [not_forall] at hc
      obtain ⟨y, hc⟩ := hc
      rw [not_forall] at hc
      obtain ⟨hy, hc⟩ := hc
      rw [not_forall] at hc
      obtain ⟨hyp, hyW⟩ := hc
      have hlt : Metric.infDist x (frontier W) < ((3 : ℝ) ^ j)⁻¹ :=
        (kc2_infDist_le hW hxW hyW).trans_lt (kc2_norm_sub_lt hx hy hyp.symm)
      have hmem : x ∈ boundaryLayer W ((3 ^ j : ℝ)⁻¹) := ⟨hxW, hlt⟩
      rw [kc2_good_of_not (by
        intro h
        exact hyW (h y hy hyp))]
      simp [hxW, hmem]
  · have hc : ¬ ∀ y ∈ kc2_Q0 d, kc2_proj j y = kc2_proj j x → y ∈ W :=
      fun h => hxW (h x hx rfl)
    have hmem : x ∉ boundaryLayer W ((3 ^ j : ℝ)⁻¹) := fun h => hxW h.1
    rw [kc2_good_of_not hc]
    simp [hxW, hmem]

theorem kc2_abs_le_layer {W : Set (Vec d)} (hW : IsOpen W) (j : ℕ) {x : Vec d}
    (hx : x ∈ kc2_Q0 d) :
    |W.indicator (fun _ => (1 : ℝ)) x - kc2_good W j (kc2_proj j x)| ≤
      (boundaryLayer W ((3 ^ j : ℝ)⁻¹)).indicator (fun _ => (1 : ℝ)) x := by
  have hsq := kc2_sq_le_layer hW j hx
  by_cases hm : x ∈ boundaryLayer W ((3 ^ j : ℝ)⁻¹)
  · rw [Set.indicator_of_mem hm]
    have hg : W.indicator (fun _ => (1 : ℝ)) x = 0 ∨ W.indicator (fun _ => (1 : ℝ)) x = 1 := by
      by_cases h : x ∈ W <;> simp [h]
    have hH : kc2_good W j (kc2_proj j x) = 0 ∨ kc2_good W j (kc2_proj j x) = 1 := by
      by_cases h : ∀ y ∈ kc2_Q0 d, kc2_proj j y = kc2_proj j x → y ∈ W
      · exact Or.inr (kc2_good_of h)
      · exact Or.inl (kc2_good_of_not h)
    rcases hg with hg | hg <;> rcases hH with hH | hH <;> simp [hg, hH]
  · rw [Set.indicator_of_notMem hm] at hsq ⊢
    have : W.indicator (fun _ => (1 : ℝ)) x - kc2_good W j (kc2_proj j x) = 0 :=
      pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm hsq (sq_nonneg _))
    rw [this, abs_zero]

/-- `L¹` distance of `1_W` to its generation-`j` conditional expectation: at most twice the
volume of the boundary layer of width `3^{-j}`. -/
theorem kc2_l1_osc_le {W : Set (Vec d)} (hW : IsOpen W) (hWQ : W ⊆ kc2_Q0 d) (j : ℕ) :
    ∫ x, |W.indicator (fun _ => (1 : ℝ)) x -
        ((kc2_μ d)[W.indicator (fun _ => (1 : ℝ)) | kc2_sig d j]) x| ∂(kc2_μ d) ≤
      2 * (volume (boundaryLayer W ((3 ^ j : ℝ)⁻¹))).toReal := by
  set g : Vec d → ℝ := W.indicator (fun _ => (1 : ℝ)) with hg
  have hgm : Measurable g := measurable_const.indicator hW.measurableSet
  have hgL : MemLp g 2 (kc2_μ d) :=
    MemLp.of_bound hgm.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun x => by
      by_cases h : x ∈ W <;> simp [hg, h])
  have hHn : Measurable (kc2_good W j) := measurable_of_countable _
  have hHs : StronglyMeasurable[kc2_sig d j] (fun x => kc2_good W j (kc2_proj j x)) :=
    (hHn.comp (comap_measurable (kc2_proj (d := d) j))).stronglyMeasurable
  have hHm : Measurable (fun x => kc2_good W j (kc2_proj j x)) :=
    hHn.comp (kc2_measurable_proj j)
  have hHb : ∀ x, ‖kc2_good W j (kc2_proj j x)‖ ≤ 1 := fun x => by
    by_cases h : ∀ y ∈ kc2_Q0 d, kc2_proj j y = kc2_proj j x → y ∈ W
    · simp [kc2_good_of h]
    · simp [kc2_good_of_not h]
  have hHL : MemLp (fun x => kc2_good W j (kc2_proj j x)) 2 (kc2_μ d) :=
    MemLp.of_bound hHm.aestronglyMeasurable 1 (Filter.Eventually.of_forall hHb)
  have h1 := kc2_l1_remainder_le (kc2_sig_le j) (hgL.integrable (by norm_num))
    (hHL.integrable (by norm_num)) hHs
  have hlm := kc2_layer_measurable hW ((3 ^ j : ℝ)⁻¹)
  have hle : ∫ x, |g x - kc2_good W j (kc2_proj j x)| ∂(kc2_μ d) ≤
      ∫ x, (boundaryLayer W ((3 ^ j : ℝ)⁻¹)).indicator (fun _ => (1 : ℝ)) x ∂(kc2_μ d) := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _)
      ((integrable_const (1 : ℝ)).indicator hlm) ?_
    rw [Filter.EventuallyLE, ae_restrict_iff' kc2_Q0_measurable]
    exact Filter.Eventually.of_forall fun x hx => kc2_abs_le_layer hW j hx
  rw [show (boundaryLayer W ((3 ^ j : ℝ)⁻¹)).indicator (fun _ => (1 : ℝ)) =
    (boundaryLayer W ((3 ^ j : ℝ)⁻¹)).indicator 1 from rfl, integral_indicator_one hlm] at hle
  have hfin : volume (boundaryLayer W ((3 ^ j : ℝ)⁻¹)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := volume (kc2_Q0 d)) (by simp [kc2_volume_Q0]) ?_
    exact measure_mono fun x hx => hWQ hx.1
  have h3 : (kc2_μ d).real (boundaryLayer W ((3 ^ j : ℝ)⁻¹)) ≤
      (volume (boundaryLayer W ((3 ^ j : ℝ)⁻¹))).toReal := by
    simp only [Measure.real]
    exact ENNReal.toReal_mono hfin (Measure.restrict_apply_le _ _)
  linarith only [h1, hle, h3]

/-- The boundary layer of width `3^{-j}` of a uniform `C^{1,1}` domain inside the unit cube has
volume at most `C 3^{-j}`, with `C = C(d, r, M₁, D)`. -/
theorem kc2_layer_vol_le_const [NeZero d] (r M₁ D : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {W : Set (Vec d)} {M₂ : ℝ}, IsUniformC11Domain W r M₁ M₂ D →
      W ⊆ kc2_Q0 d → ∀ j : ℕ,
        (volume (boundaryLayer W ((3 ^ j : ℝ)⁻¹))).toReal ≤ C * ((3 : ℝ) ^ j)⁻¹ := by
  obtain ⟨C, hC0, hC⟩ := exists_volume_boundaryLayer_le (d := d) r M₁ D hr
  refine ⟨max C r⁻¹, (hC0.trans (le_max_left _ _)), fun {W M₂} hU hWQ j => ?_⟩
  have ht : (0 : ℝ) < ((3 : ℝ) ^ j)⁻¹ := by positivity
  have hCm : 0 ≤ max C r⁻¹ := hC0.trans (le_max_left _ _)
  have h1 : volume (boundaryLayer W (((3 : ℝ) ^ j)⁻¹)) ≤
      ENNReal.ofReal (max C r⁻¹ * ((3 : ℝ) ^ j)⁻¹) := by
    by_cases hle : ((3 : ℝ) ^ j)⁻¹ ≤ r
    · exact (hC hU _ ht hle).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (le_max_left _ _) ht.le))
    · have hlt : r < ((3 : ℝ) ^ j)⁻¹ := not_le.1 hle
      have h2 : volume (boundaryLayer W (((3 : ℝ) ^ j)⁻¹)) ≤ 1 := by
        rw [← kc2_volume_Q0 (d := d)]
        exact measure_mono fun x hx => hWQ hx.1
      refine h2.trans ?_
      rw [← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      calc (1 : ℝ) = r⁻¹ * r := (inv_mul_cancel₀ hr.ne').symm
        _ ≤ r⁻¹ * ((3 : ℝ) ^ j)⁻¹ := mul_le_mul_of_nonneg_left hlt.le (inv_nonneg.2 hr.le)
        _ ≤ max C r⁻¹ * ((3 : ℝ) ^ j)⁻¹ :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) ht.le
  exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hCm ht.le) h1

/-- The generation-zero conditional expectation is the mean. -/
theorem kc2_E0_pair {W : Set (Vec d)} (hW : IsOpen W) (hWQ : W ⊆ kc2_Q0 d) (κ : Vec d → ℝ) :
    ∫ x, ((kc2_μ d)[κ | kc2_sig d 0]) x *
      ((kc2_μ d)[W.indicator (fun _ => (1 : ℝ)) | kc2_sig d 0]) x ∂(kc2_μ d) =
      (∫ x, κ x ∂(kc2_μ d)) * (volume W).toReal := by
    rw [kc2_sig_zero]
    have hR : (kc2_μ d).real Set.univ = 1 := by simp [Measure.real, kc2_volume_Q0]
    have e1 := condExp_bot_ae_eq (μ := kc2_μ d) κ
    have e2 := condExp_bot_ae_eq (μ := kc2_μ d) (W.indicator (fun _ => (1 : ℝ)))
    rw [hR] at e1 e2
    have hW : ∫ x, W.indicator (fun _ => (1 : ℝ)) x ∂(kc2_μ d) = (volume W).toReal := by
      rw [integral_indicator_const _ hW.measurableSet]
      simp only [Measure.real, smul_eq_mul, mul_one, Measure.restrict_apply hW.measurableSet,
        Set.inter_eq_left.2 hWQ]
    have : ∀ᵐ x ∂(kc2_μ d), ((kc2_μ d)[κ | ⊥]) x *
        ((kc2_μ d)[W.indicator (fun _ => (1 : ℝ)) | ⊥]) x =
        (∫ x, κ x ∂(kc2_μ d)) * (volume W).toReal := by
      filter_upwards [e1, e2] with x h1 h2
      rw [h1, h2, hW]
      simp
    rw [integral_congr_ae this, integral_const]
    simp [hR]

/-- **Pairing with the indicator, sup-times-`L¹` form.** For any open `W ⊆ Q₀`, square-integrable
`κ`, a depth `m`, bounds `Dseq t` on the generation increments of `κ` and `R` on `κ − E m κ`:
`|∫ κ 1_W − (∫ κ)|W|| ≤ ∑_{t<m} Dseq t ‖E (t+1) 1_W − E t 1_W‖_{L¹} + R ‖1_W − E m 1_W‖_{L¹}`. -/
theorem kc2_pairing_sup_indicator {W : Set (Vec d)} (hW : IsOpen W) (hWQ : W ⊆ kc2_Q0 d)
    {κ : Vec d → ℝ} (hκ : MemLp κ 2 (kc2_μ d)) (m : ℕ) (Dseq : ℕ → ℝ) (R : ℝ)
    (hD : ∀ t < m, ∀ᵐ x ∂(kc2_μ d), |kc2_incr (kc2_μ d) (kc2_sig d) κ t x| ≤ Dseq t)
    (hR : ∀ᵐ x ∂(kc2_μ d), |κ x - ((kc2_μ d)[κ | kc2_sig d m]) x| ≤ R) :
    |∫ x, κ x * W.indicator (fun _ => (1 : ℝ)) x ∂(kc2_μ d) -
        (∫ x, κ x ∂(kc2_μ d)) * (volume W).toReal| ≤
      ∑ t ∈ Finset.range m, Dseq t * ∫ x, |kc2_incr (kc2_μ d) (kc2_sig d)
          (W.indicator (fun _ => (1 : ℝ))) t x| ∂(kc2_μ d) +
        R * ∫ x, |W.indicator (fun _ => (1 : ℝ)) x -
          ((kc2_μ d)[W.indicator (fun _ => (1 : ℝ)) | kc2_sig d m]) x| ∂(kc2_μ d) := by
  have hg : MemLp (W.indicator (fun _ => (1 : ℝ))) 2 (kc2_μ d) :=
    memLp_indicator_const 2 hW.measurableSet 1 (Or.inr (by
      exact ne_top_of_le_ne_top (b := (kc2_μ d) Set.univ) (by simp [kc2_volume_Q0])
        (measure_mono (Set.subset_univ _))))
  have := kc2_pairing_sup (m := kc2_sig d) (fun j => kc2_sig_le j) kc2_sig_mono hκ hg m Dseq R hD hR
  rwa [kc2_E0_pair hW hWQ κ] at this

/-- **Decay of the indicator increments**: `‖E (t+1) 1_W − E t 1_W‖_{L¹} ≤ C (1/3)^t`, and
`‖1_W − E t 1_W‖_{L¹} ≤ C (1/3)^t`, with `C = C(d, r, M₁, D)`. -/
theorem kc2_l1_incr_decay [NeZero d] (r M₁ D : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {W : Set (Vec d)} {M₂ : ℝ}, IsUniformC11Domain W r M₁ M₂ D →
      W ⊆ kc2_Q0 d → ∀ t : ℕ,
        ∫ x, |kc2_incr (kc2_μ d) (kc2_sig d) (W.indicator (fun _ => (1 : ℝ))) t x|
            ∂(kc2_μ d) ≤ C * (1 / 3 : ℝ) ^ t ∧
        ∫ x, |W.indicator (fun _ => (1 : ℝ)) x -
          ((kc2_μ d)[W.indicator (fun _ => (1 : ℝ)) | kc2_sig d t]) x| ∂(kc2_μ d) ≤
          C * (1 / 3 : ℝ) ^ t := by
  obtain ⟨C, hC0, hC⟩ := kc2_layer_vol_le_const (d := d) r M₁ D hr
  refine ⟨4 * C, by positivity, fun {W M₂} hU hWQ t => ?_⟩
  have hg : MemLp (W.indicator (fun _ => (1 : ℝ))) 2 (kc2_μ d) :=
    memLp_indicator_const 2 hU.1.measurableSet 1 (Or.inr (by
      exact ne_top_of_le_ne_top (b := (kc2_μ d) Set.univ) (by simp [kc2_volume_Q0])
        (measure_mono (Set.subset_univ _))))
  have e : ∀ s : ℕ, C * ((3 : ℝ) ^ s)⁻¹ = C * (1 / 3 : ℝ) ^ s := fun s => by
    rw [one_div, inv_pow]
  have a0 := (kc2_l1_osc_le hU.1 hWQ t).trans (mul_le_mul_of_nonneg_left (hC hU hWQ t) (by norm_num))
  have a1 := (kc2_l1_osc_le hU.1 hWQ (t + 1)).trans
    (mul_le_mul_of_nonneg_left (hC hU hWQ (t + 1)) (by norm_num))
  rw [e] at a0 a1
  have hp : (1 / 3 : ℝ) ^ (t + 1) ≤ (1 / 3 : ℝ) ^ t :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ t)
  have hpos : 0 ≤ (1 / 3 : ℝ) ^ t := by positivity
  have hCt : 0 ≤ C * (1 / 3 : ℝ) ^ t := mul_nonneg hC0 hpos
  have hmono : C * (1 / 3 : ℝ) ^ (t + 1) ≤ C * (1 / 3 : ℝ) ^ t :=
    mul_le_mul_of_nonneg_left hp hC0
  have hi := kc2_incr_l1_le (μ := kc2_μ d) (m := kc2_sig d) (hg.integrable (by norm_num)) t
  constructor
  · linarith only [hi, a0, a1, hmono]
  · linarith only [a0, hCt]

/-! ### The conditional expectation is the cell average -/

/-- The generation-`j` cell with index `n` (as a subset of the whole space; it is meaningful
inside the unit cube). -/
def kc2_cell (j : ℕ) (n : Fin d → ℤ) : Set (Vec d) := kc2_proj j ⁻¹' {n}

theorem kc2_cell_measurable (j : ℕ) (n : Fin d → ℤ) : MeasurableSet (kc2_cell j n) :=
  kc2_measurable_proj j (measurableSet_singleton n)

/-- The average of `κ` over the generation-`j` cell `n` of the unit cube. -/
noncomputable def kc2_cellavg (κ : Vec d → ℝ) (j : ℕ) (n : Fin d → ℤ) : ℝ :=
  (∫ y in kc2_cell j n, κ y ∂(kc2_μ d)) / ((kc2_μ d) (kc2_cell j n)).toReal

theorem kc2_proj_image_finite (j : ℕ) : (kc2_proj (d := d) j '' kc2_Q0 d).Finite := by
  classical
  refine (Set.finite_Icc (0 : Fin d → ℤ) (fun _ => (3 : ℤ) ^ j)).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  simp only [kc2_proj, hx, ↓reduceIte]
  constructor
  · intro i
    obtain ⟨h1, -⟩ := kc2_mem_Q0.1 hx i
    have : (0 : ℝ) ≤ x i + 1 / 2 := by linarith only [h1]
    exact Int.floor_nonneg.2 (by positivity)
  · intro i
    obtain ⟨-, h2⟩ := kc2_mem_Q0.1 hx i
    have h3 : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
    have : (3 : ℝ) ^ j * (x i + 1 / 2) < (3 : ℝ) ^ j := by
      nlinarith only [h2, h3]
    have h4 : ⌊(3 : ℝ) ^ j * (x i + 1 / 2)⌋ < (3 : ℤ) ^ j := by
      rw [Int.floor_lt]
      exact_mod_cast this
    exact h4.le

theorem kc2_cellavg_integrable (κ : Vec d → ℝ) (j : ℕ) :
    Integrable (fun x => kc2_cellavg κ j (kc2_proj j x)) (kc2_μ d) := by
  obtain ⟨M, hM⟩ := ((kc2_proj_image_finite (d := d) j).image fun n => |kc2_cellavg κ j n|).bddAbove
  have hmeas : Measurable (fun x => kc2_cellavg κ j (kc2_proj j x)) :=
    (measurable_of_countable (kc2_cellavg κ j)).comp (kc2_measurable_proj j)
  refine Integrable.mono' (integrable_const M) hmeas.aestronglyMeasurable ?_
  refine (ae_restrict_iff' kc2_Q0_measurable).2 (Filter.Eventually.of_forall fun x hx => ?_)
  rw [Real.norm_eq_abs]
  exact hM ⟨kc2_proj j x, ⟨x, hx, rfl⟩, rfl⟩

theorem kc2_condExp_cell {κ : Vec d → ℝ} (hκ : Integrable κ (kc2_μ d)) (j : ℕ) :
    (fun x => kc2_cellavg κ j (kc2_proj j x)) =ᵐ[kc2_μ d] (kc2_μ d)[κ | kc2_sig d j] := by
  have hgi := kc2_cellavg_integrable κ j
  have hgm : StronglyMeasurable[kc2_sig d j] (fun x => kc2_cellavg κ j (kc2_proj j x)) :=
    ((measurable_of_countable (kc2_cellavg κ j)).comp
      (comap_measurable (kc2_proj (d := d) j))).stronglyMeasurable
  refine ae_eq_condExp_of_forall_setIntegral_eq (kc2_sig_le j) hκ
    (fun s _ _ => hgi.integrableOn) (fun s hs _ => ?_) hgm.aestronglyMeasurable
  obtain ⟨T, -, rfl⟩ := hs
  have hU : kc2_proj (d := d) j ⁻¹' T = ⋃ n : T, kc2_cell j n.1 := by
    ext x
    simp [kc2_cell]
  have hd : Pairwise (Function.onFun Disjoint fun n : T => kc2_cell j n.1) := by
    intro a b hab
    refine Set.disjoint_left.2 fun x hxa hxb => hab ?_
    exact Subtype.ext ((show kc2_proj j x = a.1 from hxa).symm.trans hxb)
  have hm : ∀ n : T, MeasurableSet (kc2_cell j n.1) := fun n => kc2_cell_measurable j n.1
  rw [hU, integral_iUnion hm hd hgi.integrableOn, integral_iUnion hm hd hκ.integrableOn]
  refine tsum_congr fun n => ?_
  have hc : ∫ x in kc2_cell j n.1, kc2_cellavg κ j (kc2_proj j x) ∂(kc2_μ d) =
      ∫ x in kc2_cell j n.1, kc2_cellavg κ j n.1 ∂(kc2_μ d) :=
    setIntegral_congr_fun (hm n) fun x hx => by
      have : kc2_proj j x = n.1 := hx
      simp only [this]
  rw [hc, setIntegral_const]
  by_cases h0 : (kc2_μ d).real (kc2_cell j n.1) = 0
  · have : (kc2_μ d) (kc2_cell j n.1) = 0 := by
      have hfin : (kc2_μ d) (kc2_cell j n.1) ≠ ⊤ := measure_ne_top _ _
      simpa [Measure.real, ENNReal.toReal_eq_zero_iff, hfin] using h0
    rw [Measure.restrict_eq_zero.2 this]
    simp [h0]
  · simp only [smul_eq_mul, kc2_cellavg, Measure.real] at h0 ⊢
    field_simp

/-- Sup bound for the generation increments from a bound on child-minus-parent cell averages. -/
theorem kc2_incr_bound_of_cells {κ : Vec d → ℝ} (hκ : Integrable κ (kc2_μ d)) (t : ℕ) (Dt : ℝ)
    (h : ∀ n : Fin d → ℤ, (kc2_μ d) (kc2_cell (t + 1) n) ≠ 0 →
      |kc2_cellavg κ (t + 1) n - kc2_cellavg κ t (fun i => n i / 3)| ≤ Dt) :
    ∀ᵐ x ∂(kc2_μ d), |kc2_incr (kc2_μ d) (kc2_sig d) κ t x| ≤ Dt := by
  have h1 := kc2_condExp_cell hκ (t + 1)
  have h0 := kc2_condExp_cell hκ t
  have hpos : ∀ᵐ x ∂(kc2_μ d), (kc2_μ d) (kc2_cell (t + 1) (kc2_proj (t + 1) x)) ≠ 0 := by
    have hnull : (kc2_μ d) {x | (kc2_μ d) (kc2_cell (t + 1) (kc2_proj (t + 1) x)) = 0} = 0 := by
      have : {x | (kc2_μ d) (kc2_cell (t + 1) (kc2_proj (t + 1) x)) = 0} =
          ⋃ n : {n : Fin d → ℤ // (kc2_μ d) (kc2_cell (t + 1) n) = 0}, kc2_cell (t + 1) n.1 := by
        ext x
        refine ⟨fun hx => Set.mem_iUnion.2 ⟨⟨_, hx⟩, rfl⟩, fun hx => ?_⟩
        obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hx
        have : kc2_proj (t + 1) x = n.1 := hn
        show (kc2_μ d) (kc2_cell (t + 1) (kc2_proj (t + 1) x)) = 0
        rw [this]
        exact n.2
      rw [this]
      exact measure_iUnion_null fun n => n.2
    exact measure_eq_zero_iff_ae_notMem.1 hnull |>.mono fun x hx => hx
  filter_upwards [h1, h0, hpos] with x e1 e0 hx
  simp only [kc2_incr]
  rw [← e1, ← e0, kc2_proj_succ (d := d) t x]
  exact h _ hx

/-- Sup bound for `κ − E m κ` from a bound on the oscillation within generation-`m` cells. -/
theorem kc2_remainder_bound_of_cells {κ : Vec d → ℝ} (hκ : Integrable κ (kc2_μ d)) (m : ℕ) (R : ℝ)
    (h : ∀ x ∈ kc2_Q0 d, |κ x - kc2_cellavg κ m (kc2_proj m x)| ≤ R) :
    ∀ᵐ x ∂(kc2_μ d), |κ x - ((kc2_μ d)[κ | kc2_sig d m]) x| ≤ R := by
  have h1 := kc2_condExp_cell hκ m
  have hQ : ∀ᵐ x ∂(kc2_μ d), x ∈ kc2_Q0 d := by
    rw [ae_restrict_iff' kc2_Q0_measurable]
    exact Filter.Eventually.of_forall fun x hx => hx
  filter_upwards [h1, hQ] with x e1 hx
  rw [← e1]
  exact h x hx

/-! ### Witnesses -/

/-- The ball of radius `1/4` about the centre is a uniform `C^{1,1}` domain inside the unit cube. -/
theorem kc2_witness_ball [NeZero d] :
    ∃ r M₁ M₂ D : ℝ, 0 < r ∧
      IsUniformC11Domain ((fun y : Vec d => (1 / 4 : ℝ) • y + 0) '' Section6.euclidBall (d := d) 1)
        r M₁ M₂ D ∧
      ((fun y : Vec d => (1 / 4 : ℝ) • y + 0) '' Section6.euclidBall (d := d) 1) ⊆ kc2_Q0 d := by
  obtain ⟨r, M₁, M₂, D, h⟩ := isUniformC11Domain_affineImage_euclidBall (d := d)
    (l := 1 / 4) (by norm_num) 0
  refine ⟨r, M₁, M₂, D, h.2.1, h, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  rw [kc2_mem_Q0]
  intro i
  have h1 : y i * y i ≤ 1 := by
    have hy' : vecNormSq y < 1 ^ 2 := hy
    have : y i * y i ≤ vecNormSq y :=
      Finset.single_le_sum (f := fun j => y j * y j) (fun j _ => mul_self_nonneg _)
        (Finset.mem_univ i)
    linarith only [this, hy']
  have h2 : |y i| ≤ 1 := by
    by_contra hc
    have hc' := not_le.1 hc
    nlinarith only [h1, hc', abs_mul_abs_self (y i)]
  have h3 := abs_le.1 h2
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero]
  constructor <;> linarith only [h3.1, h3.2]

/-- Satisfiability of the centering estimate on the unit cube: the ball of radius `1/4`,
`κ = 0`, `Λ = 0`. -/
example [NeZero d] :
    ∃ r M₁ M₂ D : ℝ, 0 < r ∧ ∃ W : Set (Vec d), IsUniformC11Domain W r M₁ M₂ D ∧ W ⊆ kc2_Q0 d ∧
      MemLp (fun _ : Vec d => (0 : ℝ)) 2 (kc2_μ d) ∧
      ∀ j : ℕ, kc2_l2 (kc2_μ d) (kc2_incr (kc2_μ d) (kc2_sig d) (fun _ : Vec d => (0 : ℝ)) j) ≤
        0 * ((3 : ℝ) ^ (0 : ℝ)) ^ j := by
  obtain ⟨r, M₁, M₂, D, hr, h, hs⟩ := kc2_witness_ball (d := d)
  refine ⟨r, M₁, M₂, D, hr, _, h, hs, MemLp.zero, fun j => ?_⟩
  have : kc2_incr (kc2_μ d) (kc2_sig d) (fun _ : Vec d => (0 : ℝ)) j = fun _ => 0 := by
    funext x
    simp [kc2_incr]
  rw [this]
  simp [kc2_l2]

end SuperdiffusionCLT.Section7
