/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Geometry.AtlasTransform
public import SuperdiffusionCLT.Section7.Analytic.Change.ShearB
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Slabs of bounded cross-section have small volume
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization MeasureTheory Pointwise

variable {d : ℕ}

theorem volume_affine_slice_le {p m a b : ℝ} (hp : p ≠ 0) :
    volume {t : ℝ | a < p * t + m ∧ p * t + m < b} ≤ ENNReal.ofReal ((b - a) / |p|) := by
  rcases lt_or_gt_of_ne hp with hn | hpos
  · have hsub : {t : ℝ | a < p * t + m ∧ p * t + m < b} ⊆ Set.Ioo ((b - m) / p) ((a - m) / p) := by
      rintro t ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · rw [div_lt_iff_of_neg hn]; linarith only [h2]
      · rw [lt_div_iff_of_neg hn]; linarith only [h1]
    refine (measure_mono hsub).trans ?_
    rw [Real.volume_Ioo, abs_of_neg hn]
    refine le_of_eq (congrArg _ ?_)
    field_simp
    ring
  · have hsub : {t : ℝ | a < p * t + m ∧ p * t + m < b} ⊆ Set.Ioo ((a - m) / p) ((b - m) / p) := by
      rintro t ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · rw [div_lt_iff₀ hpos]; linarith only [h1]
      · rw [lt_div_iff₀ hpos]; linarith only [h2]
    refine (measure_mono hsub).trans ?_
    rw [Real.volume_Ioo, abs_of_pos hpos]
    refine le_of_eq (congrArg _ ?_)
    field_simp
    ring

theorem exists_abs_apply_ge {n : ℕ} {e : Vec (n + 1)} (he : vecNormSq e = 1) :
    ∃ i, 1 / ((n : ℝ) + 1) ≤ |e i| := by
  have hsum : ∑ _i : Fin (n + 1), 1 / ((n : ℝ) + 1) ≤ ∑ i, e i * e i := by
    have : ∑ i, e i * e i = 1 := he
    rw [this]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    rw [mul_one_div_cancel (by positivity)]
  obtain ⟨i, -, hi⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  refine ⟨i, hi.trans ?_⟩
  have := abs_apply_le_one he i
  rw [← abs_mul_abs_self (e i)]
  exact mul_le_of_le_one_left (abs_nonneg _) this

theorem isOpen_slab {n : ℕ} (e : Vec (n + 1)) (c : Vec (n + 1)) (R a b : ℝ) :
    IsOpen {z : Vec (n + 1) | ‖z - c‖ < R ∧ a < vecDot e z ∧ vecDot e z < b} := by
  have hdot : Continuous fun z : Vec (n + 1) => vecDot e z := by unfold vecDot; fun_prop
  exact (isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const).inter
      ((isOpen_lt continuous_const hdot).inter (isOpen_lt hdot continuous_const))

/-- A slab `{a < ⟨e, z⟩ < b}` inside a sup-norm ball of radius `R` has volume at most
`d (b - a) (2R)^{d-1}`. -/
theorem volume_slab_le {n : ℕ} {e : Vec (n + 1)} (he : vecNormSq e = 1) (c : Vec (n + 1))
    {R a b : ℝ} (hR : 0 < R) (hab : a ≤ b) :
    volume {z : Vec (n + 1) | ‖z - c‖ < R ∧ a < vecDot e z ∧ vecDot e z < b}
      ≤ ENNReal.ofReal (((n : ℝ) + 1) * (b - a) * (2 * R) ^ n) := by
  obtain ⟨i0, hi0⟩ := exists_abs_apply_ge he
  have hi0pos : 0 < |e i0| := lt_of_lt_of_le (by positivity) hi0
  set A : Set (Vec (n + 1)) := {z | ‖z - c‖ < R ∧ a < vecDot e z ∧ vecDot e z < b} with hA
  have hAopen : IsOpen A := isOpen_slab e c R a b
  have hAmeas : MeasurableSet A := hAopen.measurableSet
  let Φ := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i0
  have hΦ : MeasurePreserving Φ.symm :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i0).symm
  have h1 : volume A = volume (Φ.symm ⁻¹' A) := (hΦ.measure_preimage_equiv A).symm
  rw [h1, Measure.volume_eq_prod, Measure.prod_apply_symm (Φ.symm.measurable hAmeas)]
  set L : ENNReal := ENNReal.ofReal ((b - a) / |e i0|) with hL
  let c' : Fin n → ℝ := fun j => c (i0.succAbove j)
  have hpt : ∀ w : Fin n → ℝ, volume ((fun t : ℝ => (t, w)) ⁻¹' (Φ.symm ⁻¹' A))
      ≤ (Metric.ball c' R).indicator (fun _ => L) w := by
    intro w
    have hz : ∀ t : ℝ, Φ.symm (t, w) = Fin.insertNth i0 t w := fun t => rfl
    by_cases hw : w ∈ Metric.ball c' R
    · rw [Set.indicator_of_mem hw]
      refine le_trans (measure_mono ?_) (volume_affine_slice_le (p := e i0)
        (m := ∑ j, e (i0.succAbove j) * w j) (a := a) (b := b) (abs_pos.1 hi0pos))
      intro t ht
      simp only [Set.mem_preimage, hz, hA, Set.mem_ofPred_eq] at ht
      obtain ⟨-, h2, h3⟩ := ht
      unfold vecDot at h2 h3
      rw [Fin.sum_univ_succAbove _ i0] at h2 h3
      simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove] at h2 h3
      exact ⟨h2, h3⟩
    · rw [Set.indicator_of_notMem hw]
      have hempty : (fun t : ℝ => (t, w)) ⁻¹' (Φ.symm ⁻¹' A) = ∅ := by
        ext t
        simp only [Set.mem_preimage, hz, hA, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
          iff_false]
        rintro ⟨h1, -, -⟩
        apply hw
        rw [Metric.mem_ball, dist_eq_norm]
        refine (pi_norm_lt_iff hR).2 fun j => ?_
        have := norm_le_pi_norm (Fin.insertNth i0 t w - c) (i0.succAbove j)
        simp only [Pi.sub_apply, Fin.insertNth_apply_succAbove] at this
        exact lt_of_le_of_lt this h1
      rw [hempty]; simp
  calc ∫⁻ w, volume ((fun t : ℝ => (t, w)) ⁻¹' (Φ.symm ⁻¹' A))
      ≤ ∫⁻ w, (Metric.ball c' R).indicator (fun _ => L) w := lintegral_mono hpt
    _ = L * volume (Metric.ball c' R) := lintegral_indicator_const Metric.isOpen_ball.measurableSet L
    _ = L * ENNReal.ofReal ((2 * R) ^ n) := by
        rw [Real.volume_pi_ball c' hR]; simp
    _ ≤ ENNReal.ofReal (((n : ℝ) + 1) * (b - a)) * ENNReal.ofReal ((2 * R) ^ n) := by
        gcongr
        refine ENNReal.ofReal_le_ofReal ?_
        rw [div_le_iff₀ hi0pos]
        have h2 : 1 ≤ ((n : ℝ) + 1) * |e i0| := by
          rw [div_le_iff₀ (by positivity)] at hi0
          linarith only [hi0]
        have : 0 ≤ b - a := sub_nonneg.2 hab
        nlinarith only [h2, this]
    _ = ENNReal.ofReal (((n : ℝ) + 1) * (b - a) * (2 * R) ^ n) := by
        rw [← ENNReal.ofReal_mul (mul_nonneg (by positivity) (sub_nonneg.2 hab))]

/-- The part of a chart ball within vertical distance `s` below the graph has volume at most
`d s (2((1+d) r + s))^{d-1}`. -/
theorem volume_graphSlab_le {n : ℕ} {e : Vec (n + 1)} (he : vecNormSq e = 1)
    {ψ : Vec (n + 1) → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (p : Vec (n + 1)) {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) :
    volume {y : Vec (n + 1) | y ∈ Metric.ball p r ∧ 0 < ψ (y - vecDot e y • e) - vecDot e y ∧
        ψ (y - vecDot e y • e) - vecDot e y < s}
      ≤ ENNReal.ofReal (((n : ℝ) + 1) * s * (2 * (((1 + ((n : ℝ) + 1)) * r + s))) ^ n) := by
  have hdiff : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hmp := measurePreserving_shear he hdiff
  set R : ℝ := (1 + ((n : ℝ) + 1)) * r + s with hRdef
  have hR : 0 < R := by positivity
  have hA := isOpen_slab e (p - vecDot e p • e) R (-s) 0
  have hsub : {y : Vec (n + 1) | y ∈ Metric.ball p r ∧
      0 < ψ (y - vecDot e y • e) - vecDot e y ∧ ψ (y - vecDot e y • e) - vecDot e y < s}
      ⊆ shear e ψ ⁻¹' {z : Vec (n + 1) | ‖z - (p - vecDot e p • e)‖ < R ∧
        -s < vecDot e z ∧ vecDot e z < 0} := by
    rintro y ⟨hy, h1, h2⟩
    have hdz : vecDot e (shear e ψ y) = vecDot e y - ψ (y - vecDot e y • e) := by
      unfold shear; rw [vecDot_sub_smul_self he]
    refine ⟨?_, by rw [hdz]; linarith only [h2], by rw [hdz]; linarith only [h1]⟩
    have hz : shear e ψ y - (p - vecDot e p • e)
        = ((y - vecDot e y • e) - (p - vecDot e p • e)) + vecDot e (shear e ψ y) • e := by
      have := proj_shear he ψ y
      ext i
      have hi := congrFun this i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply] at hi ⊢
      linarith only [hi]
    rw [hz]
    have hdzb : |vecDot e (shear e ψ y)| < s := by
      rw [abs_lt, hdz]; constructor <;> linarith only [h1, h2]
    calc ‖((y - vecDot e y • e) - (p - vecDot e p • e)) + vecDot e (shear e ψ y) • e‖
        ≤ ‖(y - vecDot e y • e) - (p - vecDot e p • e)‖ + ‖vecDot e (shear e ψ y) • e‖ :=
          norm_add_le _ _
      _ < (1 + ((n : ℝ) + 1)) * r + s := by
          have h3 := norm_proj_sub_le he y p
          have h4 : ‖vecDot e (shear e ψ y) • e‖ ≤ |vecDot e (shear e ψ y)| := by
            rw [norm_smul, Real.norm_eq_abs]
            exact mul_le_of_le_one_right (abs_nonneg _) (norm_le_one_of_vecNormSq he)
          have h5 : ‖y - p‖ < r := by rwa [Metric.mem_ball, dist_eq_norm] at hy
          have h6 : (1 + ((n : ℝ) + 1)) * ‖y - p‖ < (1 + ((n : ℝ) + 1)) * r :=
            mul_lt_mul_of_pos_left h5 (by positivity)
          push_cast at h3 h6
          linarith only [h3, h4, hdzb, h6]
  refine (measure_mono hsub).trans ?_
  rw [hmp.measure_preimage hA.measurableSet.nullMeasurableSet]
  have := volume_slab_le he (p - vecDot e p • e) (R := R) (a := -s) (b := 0) hR
    (by linarith only [hs])
  rwa [zero_sub, neg_neg] at this

/-! ### The boundary layer of a uniformly `C^{1,1}` domain -/

/-- The boundary layer of thickness `t` of `U`: the points of `U` within `t` of the frontier. -/
def boundaryLayer {d : ℕ} (U : Set (Vec d)) (t : ℝ) : Set (Vec d) :=
  {x | x ∈ U ∧ Metric.infDist x (frontier U) < t}

/-- The slope constant `d + (1 + d) max(M₁, 0)` of the vertical-distance estimate. -/
noncomputable def layerSlope (n : ℕ) (M₁ : ℝ) : ℝ :=
  ((n : ℝ) + 1) + (1 + ((n : ℝ) + 1)) * max M₁ 0

/-- The constant `C(d, r, M₁, D)` of the boundary-layer measure for `t ≤ r / 2`. -/
noncomputable def layerConst (n : ℕ) (r M₁ D : ℝ) : ℝ :=
  (8 * max D 0 / r + 2) ^ (n + 1) * (((n : ℝ) + 1) * layerSlope n M₁) *
    (2 * ((1 + ((n : ℝ) + 1)) * r + layerSlope n M₁ * r)) ^ n

theorem layerSlope_pos (n : ℕ) (M₁ : ℝ) : 0 < layerSlope n M₁ := by
  unfold layerSlope
  have : 0 ≤ max M₁ 0 := le_max_right _ _
  positivity

theorem dist_le_of_mem_closure {d : ℕ} {U : Set (Vec d)} {D : ℝ}
    (hD : ∀ x ∈ U, ∀ y ∈ U, ‖x - y‖ ≤ D) {x y : Vec d} (hx : x ∈ closure U)
    (hy : y ∈ closure U) : ‖x - y‖ ≤ D := by
  have hc : IsClosed {p : Vec d × Vec d | ‖p.1 - p.2‖ ≤ D} :=
    isClosed_le (by fun_prop) continuous_const
  have h : closure (U ×ˢ U) ⊆ {p : Vec d × Vec d | ‖p.1 - p.2‖ ≤ D} :=
    closure_minimal (fun p hp => hD _ hp.1 _ hp.2) hc
  rw [closure_prod_eq] at h
  exact h (show (x, y) ∈ closure U ×ˢ closure U from ⟨hx, hy⟩)

theorem abs_sub_lt_of_floor_eq {ρ : ℝ} (hρ : 0 < ρ) {a b : ℝ} (h : ⌊a / ρ⌋ = ⌊b / ρ⌋) :
    |a - b| < ρ := by
  have := Int.abs_sub_lt_one_of_floor_eq_floor h
  rwa [← sub_div, abs_div, abs_of_pos hρ, div_lt_one hρ] at this

theorem frontier_nonempty_of_uniform {n : ℕ} {U : Set (Vec (n + 1))} {D : ℝ}
    (hD : ∀ x ∈ U, ∀ y ∈ U, ‖x - y‖ ≤ D) (hU0 : U ≠ ∅) :
    (frontier U).Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty, frontier_eq_empty_iff] at hne
  rcases hne with h | h
  · exact hU0 h
  · have := hD 0 (h ▸ Set.mem_univ _) (fun _ => -(|D| + 1)) (h ▸ Set.mem_univ _)
    rw [zero_sub, norm_neg, pi_norm_const, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (by positivity)] at this
    linarith only [this, le_abs_self D]

/-- One piece: the points of the layer whose nearest frontier point lies within `r / 4` of a
frontier point `q` have small volume. -/
theorem volume_layerPiece_le {n : ℕ} {U : Set (Vec (n + 1))} {r M₁ M₂ D : ℝ}
    (h : IsUniformC11Domain U r M₁ M₂ D) {t : ℝ} (ht : 0 < t) (htr : t ≤ r / 2)
    {q : Vec (n + 1)} (hq : q ∈ frontier U) :
    volume {y : Vec (n + 1) | y ∈ boundaryLayer U t ∧
        ∃ x' ∈ frontier U, ‖y - x'‖ < t ∧ ‖x' - q‖ < r / 4}
      ≤ ENNReal.ofReal (((n : ℝ) + 1) * layerSlope n M₁ *
          (2 * ((1 + ((n : ℝ) + 1)) * r + layerSlope n M₁ * r)) ^ n * t) := by
  obtain ⟨hopen, hr, -, hch⟩ := h
  obtain ⟨e, ψ, he, hψ, hb1, -, hU⟩ := hch q hq
  have hc := layerSlope_pos n M₁
  have hcM : ((n : ℝ) + 1) + (1 + ((n : ℝ) + 1)) * M₁ ≤ layerSlope n M₁ := by
    unfold layerSlope
    have : M₁ ≤ max M₁ 0 := le_max_left _ _
    nlinarith only [this]
  have hsub : {y : Vec (n + 1) | y ∈ boundaryLayer U t ∧
        ∃ x' ∈ frontier U, ‖y - x'‖ < t ∧ ‖x' - q‖ < r / 4} ⊆
      {y : Vec (n + 1) | y ∈ Metric.ball q r ∧
        0 < ψ (y - vecDot e y • e) - vecDot e y ∧
        ψ (y - vecDot e y • e) - vecDot e y < layerSlope n M₁ * t} := by
    rintro y ⟨⟨hyU, -⟩, x', hx', hyx, hx'q⟩
    have hx'b : x' ∈ Metric.ball q r := by
      rw [Metric.mem_ball, dist_eq_norm]; linarith only [hx'q, hr]
    have hyb : y ∈ Metric.ball q r := by
      rw [Metric.mem_ball, dist_eq_norm]
      have := norm_sub_le_norm_sub_add_norm_sub y x' q
      linarith only [this, hyx, hx'q, htr, hr]
    obtain ⟨hp, hle⟩ := vertical_dist_le hopen he hψ hb1 hU hyU hyb hx' hx'b
    refine ⟨hyb, hp, ?_⟩
    push_cast at hle
    calc _ ≤ _ := hle
      _ ≤ layerSlope n M₁ * ‖y - x'‖ :=
          mul_le_mul_of_nonneg_right hcM (norm_nonneg _)
      _ < layerSlope n M₁ * t := mul_lt_mul_of_pos_left hyx hc
  refine (measure_mono hsub).trans ?_
  refine (volume_graphSlab_le he hψ q hr (mul_pos hc ht)).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hs : layerSlope n M₁ * t ≤ layerSlope n M₁ * r :=
    mul_le_mul_of_nonneg_left (by linarith only [htr, hr]) hc.le
  have hbase : 0 ≤ 2 * ((1 + ((n : ℝ) + 1)) * r + layerSlope n M₁ * t) := by positivity
  have hpow : (2 * ((1 + ((n : ℝ) + 1)) * r + layerSlope n M₁ * t)) ^ n
      ≤ (2 * ((1 + ((n : ℝ) + 1)) * r + layerSlope n M₁ * r)) ^ n :=
    pow_le_pow_left₀ hbase (by linarith only [hs]) n
  have hn : (0 : ℝ) ≤ ((n : ℝ) + 1) * (layerSlope n M₁ * t) := by positivity
  calc ((n : ℝ) + 1) * (layerSlope n M₁ * t) *
        (2 * ((1 + ((n : ℝ) + 1)) * r + layerSlope n M₁ * t)) ^ n
      ≤ ((n : ℝ) + 1) * (layerSlope n M₁ * t) *
        (2 * ((1 + ((n : ℝ) + 1)) * r + layerSlope n M₁ * r)) ^ n :=
        mul_le_mul_of_nonneg_left hpow hn
    _ = _ := by ring

/-- The boundary-layer measure for `t ≤ r / 2`. -/
theorem volume_boundaryLayer_le_of_le_half {n : ℕ} {U : Set (Vec (n + 1))} {r M₁ M₂ D : ℝ}
    (h : IsUniformC11Domain U r M₁ M₂ D) {t : ℝ} (ht : 0 < t) (htr : t ≤ r / 2) :
    volume (boundaryLayer U t) ≤ ENNReal.ofReal (layerConst n r M₁ D * t) := by
  classical
  by_cases hU0 : U = ∅
  · have : boundaryLayer U t = ∅ := by
      ext x; simp [boundaryLayer, hU0]
    rw [this]; simp
  have hr : 0 < r := h.2.1
  have hD := h.2.2.1
  have hFne := frontier_nonempty_of_uniform hD hU0
  obtain ⟨x0, hx0⟩ := hFne
  set ρ : ℝ := r / 4 with hρ
  have hρ0 : 0 < ρ := by positivity
  let cell : Vec (n + 1) → (Fin (n + 1) → ℤ) := fun x i => ⌊x i / ρ⌋
  let Kfin : Finset (Fin (n + 1) → ℤ) := Fintype.piFinset fun i =>
    Finset.Icc ⌊(x0 i - max D 0) / ρ⌋ ⌊(x0 i + max D 0) / ρ⌋
  let K' : Finset (Fin (n + 1) → ℤ) := Kfin.filter fun k => ∃ x ∈ frontier U, cell x = k
  have hex : ∀ k : Fin (n + 1) → ℤ, (∃ x ∈ frontier U, cell x = k) →
      ∃ x, x ∈ frontier U ∧ cell x = k := fun k hk => hk
  choose! p hp using hex
  -- the cover
  have hcover : boundaryLayer U t ⊆ ⋃ k ∈ K', {y : Vec (n + 1) | y ∈ boundaryLayer U t ∧
      ∃ x' ∈ frontier U, ‖y - x'‖ < t ∧ ‖x' - p k‖ < r / 4} := by
    intro y hy
    obtain ⟨x', hx', hdx⟩ := (Metric.infDist_lt_iff ⟨x0, hx0⟩).1 hy.2
    have hxk : ∃ x ∈ frontier U, cell x = cell x' := ⟨x', hx', rfl⟩
    obtain ⟨hpF, hpc⟩ := hp (cell x') hxk
    have hmemK : cell x' ∈ K' := by
      refine Finset.mem_filter.2 ⟨?_, hxk⟩
      refine Fintype.mem_piFinset.2 fun i => Finset.mem_Icc.2 ⟨?_, ?_⟩
      · have hdi : |x' i - x0 i| ≤ max D 0 := by
          have := dist_le_of_mem_closure hD (frontier_subset_closure hx')
            (frontier_subset_closure hx0)
          have h2 := norm_le_pi_norm (x' - x0) i
          rw [Pi.sub_apply, Real.norm_eq_abs] at h2
          exact h2.trans (this.trans (le_max_left _ _))
        show ⌊(x0 i - max D 0) / ρ⌋ ≤ ⌊x' i / ρ⌋
        refine Int.floor_le_floor ?_
        exact div_le_div_of_nonneg_right (by linarith only [(abs_le.1 hdi).1]) hρ0.le
      · have hdi : |x' i - x0 i| ≤ max D 0 := by
          have := dist_le_of_mem_closure hD (frontier_subset_closure hx')
            (frontier_subset_closure hx0)
          have h2 := norm_le_pi_norm (x' - x0) i
          rw [Pi.sub_apply, Real.norm_eq_abs] at h2
          exact h2.trans (this.trans (le_max_left _ _))
        show ⌊x' i / ρ⌋ ≤ ⌊(x0 i + max D 0) / ρ⌋
        refine Int.floor_le_floor ?_
        exact div_le_div_of_nonneg_right (by linarith only [(abs_le.1 hdi).2]) hρ0.le
    refine Set.mem_iUnion₂.2 ⟨cell x', hmemK, hy, x', hx', ?_, ?_⟩
    · rwa [dist_eq_norm] at hdx
    · rw [norm_sub_rev, ← hρ]
      refine (pi_norm_lt_iff hρ0).2 fun i => ?_
      have hi : ⌊p (cell x') i / ρ⌋ = ⌊x' i / ρ⌋ := congrFun hpc i
      rw [Pi.sub_apply, Real.norm_eq_abs]
      rw [abs_sub_comm]
      exact abs_sub_lt_of_floor_eq hρ0 hi.symm
  have hcard : (K'.card : ℝ) ≤ (8 * max D 0 / r + 2) ^ (n + 1) := by
    have h1 : K'.card ≤ Kfin.card := Finset.card_filter_le _ _
    have h2 : Kfin.card = ∏ i : Fin (n + 1),
        (Finset.Icc ⌊(x0 i - max D 0) / ρ⌋ ⌊(x0 i + max D 0) / ρ⌋).card :=
      Fintype.card_piFinset _
    have h3 : ∀ i : Fin (n + 1),
        ((Finset.Icc ⌊(x0 i - max D 0) / ρ⌋ ⌊(x0 i + max D 0) / ρ⌋).card : ℝ)
          ≤ 8 * max D 0 / r + 2 := by
      intro i
      rw [Int.card_Icc]
      have hpos : 0 ≤ 8 * max D 0 / r + 2 := by positivity
      rcases le_or_gt (⌊(x0 i + max D 0) / ρ⌋ + 1 - ⌊(x0 i - max D 0) / ρ⌋) 0 with hz | hz
      · rw [Int.toNat_of_nonpos hz]; simpa using hpos
      · have e1 : (((⌊(x0 i + max D 0) / ρ⌋ + 1 - ⌊(x0 i - max D 0) / ρ⌋).toNat : ℕ) : ℝ)
            = ((⌊(x0 i + max D 0) / ρ⌋ + 1 - ⌊(x0 i - max D 0) / ρ⌋ : ℤ) : ℝ) := by
          exact_mod_cast Int.toNat_of_nonneg hz.le
        rw [e1]
        push_cast
        have f1 := Int.floor_le ((x0 i + max D 0) / ρ)
        have f2 := Int.lt_floor_add_one ((x0 i - max D 0) / ρ)
        have f3 : (x0 i + max D 0) / ρ - (x0 i - max D 0) / ρ = 8 * max D 0 / r := by
          rw [hρ]; field_simp; ring
        linarith only [f1, f2, f3]
    calc (K'.card : ℝ) ≤ (Kfin.card : ℝ) := by exact_mod_cast h1
      _ = ∏ i : Fin (n + 1), ((Finset.Icc ⌊(x0 i - max D 0) / ρ⌋ ⌊(x0 i + max D 0) / ρ⌋).card : ℝ) := by
          rw [h2]; push_cast; rfl
      _ ≤ ∏ _i : Fin (n + 1), (8 * max D 0 / r + 2) :=
          Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) (fun i _ => h3 i)
      _ = _ := by simp
  have hpiece : ∀ k ∈ K', volume {y : Vec (n + 1) | y ∈ boundaryLayer U t ∧
      ∃ x' ∈ frontier U, ‖y - x'‖ < t ∧ ‖x' - p k‖ < r / 4}
      ≤ ENNReal.ofReal (((n : ℝ) + 1) * layerSlope n M₁ *
          (2 * ((1 + ((n : ℝ) + 1)) * r + layerSlope n M₁ * r)) ^ n * t) := fun k hk =>
    volume_layerPiece_le h ht htr (hp k (Finset.mem_filter.1 hk).2).1
  have hVnn : 0 ≤ ((n : ℝ) + 1) * layerSlope n M₁ *
      (2 * ((1 + ((n : ℝ) + 1)) * r + layerSlope n M₁ * r)) ^ n * t := by
    have := layerSlope_pos n M₁
    positivity
  calc volume (boundaryLayer U t)
      ≤ volume (⋃ k ∈ K', {y : Vec (n + 1) | y ∈ boundaryLayer U t ∧
          ∃ x' ∈ frontier U, ‖y - x'‖ < t ∧ ‖x' - p k‖ < r / 4}) := measure_mono hcover
    _ ≤ ∑ k ∈ K', volume {y : Vec (n + 1) | y ∈ boundaryLayer U t ∧
          ∃ x' ∈ frontier U, ‖y - x'‖ < t ∧ ‖x' - p k‖ < r / 4} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ K', ENNReal.ofReal (((n : ℝ) + 1) * layerSlope n M₁ *
          (2 * ((1 + ((n : ℝ) + 1)) * r + layerSlope n M₁ * r)) ^ n * t) :=
        Finset.sum_le_sum hpiece
    _ = ENNReal.ofReal ((K'.card : ℝ) * (((n : ℝ) + 1) * layerSlope n M₁ *
          (2 * ((1 + ((n : ℝ) + 1)) * r + layerSlope n M₁ * r)) ^ n * t)) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (layerConst n r M₁ D * t) := by
        refine ENNReal.ofReal_le_ofReal ?_
        unfold layerConst
        calc (K'.card : ℝ) * (((n : ℝ) + 1) * layerSlope n M₁ *
              (2 * ((1 + ((n : ℝ) + 1)) * r + layerSlope n M₁ * r)) ^ n * t)
            ≤ (8 * max D 0 / r + 2) ^ (n + 1) * (((n : ℝ) + 1) * layerSlope n M₁ *
              (2 * ((1 + ((n : ℝ) + 1)) * r + layerSlope n M₁ * r)) ^ n * t) :=
              mul_le_mul_of_nonneg_right hcard hVnn
          _ = _ := by ring

/-- Volume of a uniformly bounded open set: `|U| ≤ (2D)^d`. -/
theorem volume_le_of_uniform {n : ℕ} {U : Set (Vec (n + 1))} {D : ℝ}
    (hD : ∀ x ∈ U, ∀ y ∈ U, ‖x - y‖ ≤ D) :
    volume U ≤ ENNReal.ofReal ((2 * max D 0) ^ (n + 1)) := by
  rcases U.eq_empty_or_nonempty with rfl | ⟨x0, hx0⟩
  · simp
  have hsub : U ⊆ Metric.closedBall x0 (max D 0) := fun y hy => by
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact (hD y hy x0 hx0).trans (le_max_left _ _)
  refine (measure_mono hsub).trans (le_of_eq ?_)
  rw [Real.volume_pi_closedBall x0 (le_max_right _ _)]
  simp

/-- BOUNDARY-LAYER MEASURE: for a uniformly `C^{1,1}` bounded open set with data
`(r, M₁, M₂, D)` and `0 < t ≤ r`, `|{x ∈ U : dist(x, ∂U) < t}| ≤ C t`, where `C` depends only
on `(d, r, M₁, D)`. -/
theorem exists_volume_boundaryLayer_le [NeZero d] (r M₁ D : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {U : Set (Vec d)} {M₂ : ℝ}, IsUniformC11Domain U r M₁ M₂ D →
      ∀ t : ℝ, 0 < t → t ≤ r → volume (boundaryLayer U t) ≤ ENNReal.ofReal (C * t) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne d)
  have hc0 : 0 ≤ layerConst n r M₁ D := by
    unfold layerConst
    have := layerSlope_pos n M₁
    positivity
  refine ⟨max (layerConst n r M₁ D) ((2 * max D 0) ^ (n + 1) * 2 / r), ?_, ?_⟩
  · exact hc0.trans (le_max_left _ _)
  intro U M₂ h t ht htr
  rcases le_or_gt t (r / 2) with hsmall | hbig
  · refine (volume_boundaryLayer_le_of_le_half h ht hsmall).trans ?_
    exact ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) ht.le)
  · refine ((measure_mono fun x hx => hx.1).trans (volume_le_of_uniform h.2.2.1)).trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : (2 * max D 0) ^ (n + 1) * 2 / r * t ≤
        max (layerConst n r M₁ D) ((2 * max D 0) ^ (n + 1) * 2 / r) * t :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) ht.le
    have h2 : (2 * max D 0) ^ (n + 1) ≤ (2 * max D 0) ^ (n + 1) * 2 / r * t := by
      have hp : 0 ≤ (2 * max D 0) ^ (n + 1) := by positivity
      rw [mul_div_assoc, mul_assoc]
      refine le_mul_of_one_le_right hp ?_
      rw [div_mul_eq_mul_div, le_div_iff₀ hr]
      linarith only [hbig]
    exact h2.trans h1

/-- The boundary layer of a dilate: `t • ` of the layer at the rescaled thickness. -/
theorem boundaryLayer_smul {U : Set (Vec d)} {l : ℝ} (hl : 0 < l) (t : ℝ) :
    boundaryLayer (l • U) t = l • boundaryLayer U (t / l) := by
  have hl0 : l ≠ 0 := hl.ne'
  have hfr : frontier (l • U) = l • frontier U := by
    have := (Homeomorph.smulOfNeZero l hl0).image_frontier U
    simpa [Set.image_smul] using this.symm
  have key : ∀ x : Vec d, Metric.infDist (l • x) (frontier (l • U)) < t ↔
      Metric.infDist x (frontier U) < t / l := by
    intro x
    rw [hfr]
    rcases (frontier U).eq_empty_or_nonempty with he | hne
    · simp [he, hl]
    · rw [Metric.infDist_lt_iff hne.smul_set, Metric.infDist_lt_iff hne]
      constructor
      · rintro ⟨_, hz', hd⟩
        obtain ⟨z, hz, rfl⟩ := Set.mem_smul_set.1 hz'
        refine ⟨z, hz, ?_⟩
        rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hl] at hd
        rw [lt_div_iff₀ hl]; linarith only [hd]
      · rintro ⟨z, hz, hd⟩
        refine ⟨l • z, Set.mem_smul_set.2 ⟨z, hz, rfl⟩, ?_⟩
        rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hl]
        rw [lt_div_iff₀ hl] at hd; linarith only [hd]
  ext y
  constructor
  · rintro ⟨hy, hd⟩
    obtain ⟨x, hx, rfl⟩ := Set.mem_smul_set.1 hy
    exact Set.mem_smul_set.2 ⟨x, ⟨hx, (key x).1 hd⟩, rfl⟩
  · intro hy
    obtain ⟨x, ⟨hx, hd⟩, rfl⟩ := Set.mem_smul_set.1 hy
    exact ⟨Set.mem_smul_set.2 ⟨x, hx, rfl⟩, (key x).2 hd⟩

/-- The form used in Section 7: for the dilate `l • U` (`l = 3^K`), the layer of thickness `t`
has volume at most `C t l^{d-1}`, for `t ≤ l r`. -/
theorem exists_volume_boundaryLayer_smul_le [NeZero d] (r M₁ D : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {U : Set (Vec d)} {M₂ : ℝ}, IsUniformC11Domain U r M₁ M₂ D →
      ∀ l : ℝ, 0 < l → ∀ t : ℝ, 0 < t → t ≤ l * r →
        volume (boundaryLayer (l • U) t) ≤ ENNReal.ofReal (C * t * l ^ (d - 1)) := by
  obtain ⟨C, hC0, hC⟩ := exists_volume_boundaryLayer_le (d := d) r M₁ D hr
  refine ⟨C, hC0, fun {U M₂} h l hl t ht htr => ?_⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne d)
  rw [boundaryLayer_smul hl, Measure.addHaar_smul, abs_of_pos (pow_pos hl _)]
  have h1 := hC h (t / l) (div_pos ht hl) (by rw [div_le_iff₀ hl]; linarith only [htr])
  simp only [Module.finrank_pi, Fintype.card_fin]
  calc ENNReal.ofReal (l ^ (n + 1)) * volume (boundaryLayer U (t / l))
      ≤ ENNReal.ofReal (l ^ (n + 1)) * ENNReal.ofReal (C * (t / l)) := by gcongr
    _ = ENNReal.ofReal (l ^ (n + 1) * (C * (t / l))) :=
        (ENNReal.ofReal_mul (by positivity)).symm
    _ = _ := by
        congr 1
        simp only [Nat.succ_sub_one]
        field_simp
        ring

end SuperdiffusionCLT.Section7
