/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Geometry.BoundaryLayer
public import SuperdiffusionCLT.Section7.Analytic.OpenH10.LipschitzB

/-!
# The boundary cutoff of the comparison function in the Dirichlet `L²` homogenization

A cutoff `ζ` that vanishes within the margin `r` of the complement of the domain `W`, equals one
at distance at least `2 r`, has gradient bounded by `1 / r`, and whose transition layer sits
inside the boundary layer of thickness `2 r`.  It is the Lipschitz function
`max 0 (min 1 ((dist x Wᶜ - r) / r))`.

## Main results

* `Section7.l2a_cutoff`, `l2a_cutoff_lipschitz`, `l2a_cutoff_eq_one`, `l2a_cutoff_eq_zero`.
* `Section7.l2a_cutoff_compact`: compact support inside a bounded open set.
* `Section7.l2a_lipGradient_cutoff_abs_le`, `l2a_lipGradient_cutoff_eq_zero`.
* `Section7.l2a_exists_cutoff`: the layer `{ζ ≠ 1} ∩ W` has measure at most `C r`.
-/

@[expose] public section

open MeasureTheory Set Filter Homogenization
open scoped ENNReal NNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The cutoff at margin `r`: `0` within `r` of `Wᶜ`, `1` at distance `≥ 2 r`, linear between. -/
noncomputable def l2a_cutoff (W : Set (Vec d)) (r : ℝ) (x : Vec d) : ℝ :=
  max 0 (min 1 ((Metric.infDist x Wᶜ - r) / r))

theorem l2a_clamp_dist (a b : ℝ) :
    |max 0 (min 1 a) - max 0 (min 1 b)| ≤ |a - b| := by
  have h1 : |max 0 (min 1 a) - max 0 (min 1 b)| ≤ |min 1 a - min 1 b| := by
    rw [max_comm 0, max_comm 0 (min 1 b)]
    exact abs_max_sub_max_le_abs _ _ _
  refine h1.trans ((abs_min_sub_min_le_max _ _ _ _).trans ?_)
  simp

theorem l2a_cutoff_lipschitz (W : Set (Vec d)) {r : ℝ} (hr : 0 < r) :
    LipschitzWith (Real.toNNReal (1 / r)) (l2a_cutoff W r) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
  refine (l2a_clamp_dist _ _).trans ?_
  have h := (Metric.lipschitz_infDist_pt (s := Wᶜ)).dist_le_mul x y
  rw [Real.dist_eq] at h
  have e : (Metric.infDist x Wᶜ - r) / r - (Metric.infDist y Wᶜ - r) / r =
      (Metric.infDist x Wᶜ - Metric.infDist y Wᶜ) / r := by ring
  rw [e, abs_div, abs_of_pos hr, div_eq_mul_inv, one_div, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hr.le)
  simpa using h

theorem l2a_cutoff_nonneg (W : Set (Vec d)) (r : ℝ) (x : Vec d) : 0 ≤ l2a_cutoff W r x :=
  le_max_left _ _

theorem l2a_cutoff_le_one (W : Set (Vec d)) (r : ℝ) (x : Vec d) : l2a_cutoff W r x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem l2a_cutoff_abs_le (W : Set (Vec d)) (r : ℝ) (x : Vec d) : |l2a_cutoff W r x| ≤ 1 := by
  rw [abs_of_nonneg (l2a_cutoff_nonneg W r x)]
  exact l2a_cutoff_le_one W r x

theorem l2a_cutoff_eq_one {W : Set (Vec d)} {r : ℝ} (hr : 0 < r) {x : Vec d}
    (hx : 2 * r ≤ Metric.infDist x Wᶜ) : l2a_cutoff W r x = 1 := by
  unfold l2a_cutoff
  have : 1 ≤ (Metric.infDist x Wᶜ - r) / r := by
    rw [le_div_iff₀ hr]; linarith only [hx]
  rw [min_eq_left this, max_eq_right zero_le_one]

theorem l2a_cutoff_eq_zero {W : Set (Vec d)} {r : ℝ} (hr : 0 < r) {x : Vec d}
    (hx : Metric.infDist x Wᶜ ≤ r) : l2a_cutoff W r x = 0 := by
  unfold l2a_cutoff
  have : (Metric.infDist x Wᶜ - r) / r ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith only [hx]) hr.le
  rw [min_eq_right (by linarith only [this]), max_eq_left (by linarith only [this])]

theorem l2a_cutoff_ne_zero_imp {W : Set (Vec d)} {r : ℝ} (hr : 0 < r) {x : Vec d}
    (hx : l2a_cutoff W r x ≠ 0) : r < Metric.infDist x Wᶜ := by
  by_contra h
  exact hx (l2a_cutoff_eq_zero hr (not_lt.1 h))

theorem l2a_cutoff_continuous (W : Set (Vec d)) {r : ℝ} (hr : 0 < r) :
    Continuous (l2a_cutoff W r) :=
  (l2a_cutoff_lipschitz W hr).continuous

/-- The set of points at distance at least `r` from `Wᶜ` is a compact subset of a bounded open
`W`. -/
theorem l2a_margin_compact {W : Set (Vec d)} (hW : Bornology.IsBounded W) {r : ℝ}
    (hr : 0 < r) : IsCompact {x : Vec d | r ≤ Metric.infDist x Wᶜ} := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_le continuous_const
    (Metric.continuous_infDist_pt _)) (hW.subset fun x hx => ?_)
  by_contra hxW
  have : Metric.infDist x Wᶜ = 0 := Metric.infDist_zero_of_mem (show x ∈ Wᶜ from hxW)
  have hx' : r ≤ Metric.infDist x Wᶜ := hx
  linarith only [this, hx', hr]

theorem l2a_margin_subset {W : Set (Vec d)} {r : ℝ} (hr : 0 < r) :
    {x : Vec d | r ≤ Metric.infDist x Wᶜ} ⊆ W := by
  intro x hx
  by_contra hxW
  have : Metric.infDist x Wᶜ = 0 := Metric.infDist_zero_of_mem (show x ∈ Wᶜ from hxW)
  have hx' : r ≤ Metric.infDist x Wᶜ := hx
  linarith only [this, hx', hr]

theorem l2a_tsupport_cutoff_subset (W : Set (Vec d)) {r : ℝ} (hr : 0 < r) :
    tsupport (l2a_cutoff W r) ⊆ {x : Vec d | r ≤ Metric.infDist x Wᶜ} := by
  refine closure_minimal (fun x hx => ?_) (isClosed_le continuous_const
    (Metric.continuous_infDist_pt _))
  exact (l2a_cutoff_ne_zero_imp hr hx).le

/-- The cutoff has compact support inside a bounded set. -/
theorem l2a_cutoff_compact {W : Set (Vec d)} (hW : Bornology.IsBounded W) {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (l2a_cutoff W r) ∧ tsupport (l2a_cutoff W r) ⊆ W :=
  ⟨(l2a_margin_compact hW hr).of_isClosed_subset isClosed_closure (l2a_tsupport_cutoff_subset W hr),
    (l2a_tsupport_cutoff_subset W hr).trans (l2a_margin_subset hr)⟩

/-- Coordinate derivatives of the cutoff are bounded by `1 / r`. -/
theorem l2a_lipGradient_cutoff_abs_le (W : Set (Vec d)) {r : ℝ} (hr : 0 < r) (x : Vec d)
    (i : Fin d) : |lipGradient (l2a_cutoff W r) x i| ≤ 1 / r := by
  have h := lipschitzWith_ae_norm_partialDeriv_le (l2a_cutoff_lipschitz W hr) i
  have h1 : ‖fderiv ℝ (l2a_cutoff W r) x‖ ≤ ((Real.toNNReal (1 / r) : ℝ≥0) : ℝ) :=
    norm_fderiv_le_of_lipschitz ℝ (l2a_cutoff_lipschitz W hr)
  have h2 : ‖basisVec (d := d) i‖ = 1 := by simp [basisVec, Pi.norm_single]
  have h3 : ‖fderiv ℝ (l2a_cutoff W r) x (basisVec i)‖ ≤ 1 / r := by
    calc ‖fderiv ℝ (l2a_cutoff W r) x (basisVec i)‖
        ≤ ‖fderiv ℝ (l2a_cutoff W r) x‖ * ‖basisVec (d := d) i‖ := (fderiv ℝ _ x).le_opNorm _
      _ ≤ 1 / r := by
        rw [h2, mul_one]
        rwa [Real.coe_toNNReal _ (by positivity)] at h1
  simpa [lipGradient] using h3

/-- The gradient of the cutoff vanishes off the transition region `r ≤ dist ≤ 2 r`. -/
theorem l2a_lipGradient_cutoff_eq_zero (W : Set (Vec d)) {r : ℝ} (hr : 0 < r) {x : Vec d}
    (hx : Metric.infDist x Wᶜ < r ∨ 2 * r < Metric.infDist x Wᶜ) :
    lipGradient (l2a_cutoff W r) x = 0 := by
  funext i
  have hcont : Continuous fun y : Vec d => Metric.infDist y Wᶜ := Metric.continuous_infDist_pt _
  rcases hx with hx | hx
  · have hev : ∀ᶠ y in nhds x, Metric.infDist y Wᶜ < r := hcont.continuousAt.eventually_lt
      continuousAt_const hx
    have : l2a_cutoff W r =ᶠ[nhds x] fun _ => (0 : ℝ) :=
      hev.mono fun y hy => l2a_cutoff_eq_zero hr hy.le
    simp [lipGradient, this.fderiv_eq]
  · have hev : ∀ᶠ y in nhds x, 2 * r < Metric.infDist y Wᶜ :=
      continuousAt_const.eventually_lt hcont.continuousAt hx
    have : l2a_cutoff W r =ᶠ[nhds x] fun _ => (1 : ℝ) :=
      hev.mono fun y hy => l2a_cutoff_eq_one hr hy.le
    simp [lipGradient, this.fderiv_eq]

/-- The transition layer lies in the boundary layer of thickness `2 r`. -/
theorem l2a_cutoff_layer_subset [NeZero d] {W : Set (Vec d)} {D : ℝ}
    (hD : ∀ x ∈ W, ∀ y ∈ W, ‖x - y‖ ≤ D) {r : ℝ} (hr : 0 < r) :
    {x | x ∈ W ∧ l2a_cutoff W r x ≠ 1} ⊆ boundaryLayer W (2 * r) := by
  intro x ⟨hxW, hx1⟩
  have hne : W ≠ univ := by
    intro hWu
    subst hWu
    have hb : Bornology.IsBounded (univ : Set (Vec d)) := by
      refine (Metric.isBounded_iff_subset_closedBall (0 : Vec d)).2 ⟨D + ‖(0 : Vec d)‖, fun y _ => ?_⟩
      have := hD y (mem_univ _) 0 (mem_univ _)
      rw [mem_closedBall_zero_iff]
      simpa using this
    exact NormedSpace.unbounded_univ ℝ (Vec d) hb
  obtain ⟨y, hy, hxy⟩ := exists_mem_frontier_infDist_compl_eq_dist hxW hne
  refine ⟨hxW, ?_⟩
  have hlt : Metric.infDist x Wᶜ < 2 * r := by
    by_contra h
    exact hx1 (l2a_cutoff_eq_one hr (not_lt.1 h))
  have : Metric.infDist x (frontier W) ≤ dist x y := Metric.infDist_le_dist_of_mem hy
  linarith only [this, hxy, hlt]

/-- **The cutoff and its layer** (margin `r`, scale `2 r`).  For a bounded
uniformly `C^{1,1}` domain `W` of scale `r₀` and every margin `0 < r` with `2 r ≤ r₀`, the cutoff
`ζ = l2a_cutoff W r` is `1 / r`-Lipschitz, takes values in `[0, 1]`, vanishes within `r` of
`Wᶜ`, equals `1` beyond `2 r`, and the layer `{x ∈ W | ζ x ≠ 1}` has measure at most `C (2 r)`
with `C` depending only on `(d, r₀, M₁, D)`. -/
theorem l2a_exists_cutoff [NeZero d] (r₀ M₁ D : ℝ) (hr₀ : 0 < r₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {W : Set (Vec d)} {M₂ : ℝ}, IsUniformC11Domain W r₀ M₁ M₂ D →
      ∀ {r : ℝ}, 0 < r → 2 * r ≤ r₀ →
        LipschitzWith (Real.toNNReal (1 / r)) (l2a_cutoff W r) ∧
        (∀ x, 0 ≤ l2a_cutoff W r x ∧ l2a_cutoff W r x ≤ 1) ∧
        (∀ x, Metric.infDist x Wᶜ ≤ r → l2a_cutoff W r x = 0) ∧
        (∀ x, 2 * r ≤ Metric.infDist x Wᶜ → l2a_cutoff W r x = 1) ∧
        HasCompactSupport (l2a_cutoff W r) ∧ tsupport (l2a_cutoff W r) ⊆ W ∧
        volume {x | x ∈ W ∧ l2a_cutoff W r x ≠ 1} ≤ ENNReal.ofReal (C * (2 * r)) := by
  obtain ⟨C, hC, hlayer⟩ := exists_volume_boundaryLayer_le (d := d) r₀ M₁ D hr₀
  refine ⟨C, hC, fun {W M₂} h r hr h2r => ?_⟩
  have hbd : Bornology.IsBounded W := by
    rcases W.eq_empty_or_nonempty with he | ⟨x₀, hx₀⟩
    · rw [he]; exact Bornology.isBounded_empty
    · refine (Metric.isBounded_iff_subset_closedBall x₀).2 ⟨D, fun y hy => ?_⟩
      rw [mem_closedBall_iff_norm]
      exact h.2.2.1 y hy x₀ hx₀
  obtain ⟨hc, hs⟩ := l2a_cutoff_compact hbd hr
  refine ⟨l2a_cutoff_lipschitz W hr, fun x => ⟨l2a_cutoff_nonneg W r x, l2a_cutoff_le_one W r x⟩,
    fun x hx => l2a_cutoff_eq_zero hr hx, fun x hx => l2a_cutoff_eq_one hr hx, hc, hs, ?_⟩
  exact (measure_mono (l2a_cutoff_layer_subset h.2.2.1 hr)).trans
    (hlayer h (2 * r) (by positivity) h2r)

/-- The `h`-thickening of the margin set stays in `W` when `h < r`. -/
theorem l2a_cthickening_margin_subset {W : Set (Vec d)} (hWb : Bornology.IsBounded W) {r h : ℝ}
    (hr : 0 < r) (hh : 0 ≤ h) (hhr : h < r) :
    Metric.cthickening h {x : Vec d | r ≤ Metric.infDist x Wᶜ} ⊆ W := by
  intro y hy
  rw [(l2a_margin_compact hWb hr).cthickening_eq_biUnion_closedBall hh] at hy
  obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 hy
  by_contra hyW
  have h1 : Metric.infDist y Wᶜ = 0 := Metric.infDist_zero_of_mem (show y ∈ Wᶜ from hyW)
  have h2 := Metric.infDist_le_infDist_add_dist (x := x) (y := y) (s := Wᶜ)
  have h3 : dist x y ≤ h := by rw [dist_comm]; exact Metric.mem_closedBall.1 hyx
  have hx' : r ≤ Metric.infDist x Wᶜ := hx
  linarith only [h1, h2, h3, hx', hhr]

/-- The data of the margin cutoff: the compact set `K`, the thickening inside `W`, and the
vanishing of the cutoff off `K`. -/
theorem l2a_cutoff_margin_data {W : Set (Vec d)} (hWb : Bornology.IsBounded W) {r h : ℝ}
    (hr : 0 < r) (hh : 0 ≤ h) (hhr : h < r) :
    ∃ K : Set (Vec d), IsCompact K ∧ Metric.cthickening h K ⊆ W ∧
      ∀ x, x ∉ K → l2a_cutoff W r x = 0 :=
  ⟨_, l2a_margin_compact hWb hr, l2a_cthickening_margin_subset hWb hr hh hhr, fun _ hx =>
    l2a_cutoff_eq_zero hr (le_of_lt (not_le.1 hx))⟩

end SuperdiffusionCLT.Section7
