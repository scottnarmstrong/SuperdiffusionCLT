/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.L2BoundaryB
public import SuperdiffusionCLT.Section7.Analytic.Geometry.LayerPoincareB
public import SuperdiffusionCLT.Section7.Prereq.LinftyReduction

/-!
# The boundary-layer terms and the difference `w - u`

Displays `e.Dir.new.w.minus.u` and `e.Dir.new.boundary.u.term`.
-/

@[expose] public section

open MeasureTheory Set Filter Homogenization
open scoped ENNReal NNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ} {W : Set (Vec d)}

/-- A function vanishing on `W \ V` and bounded on `V` by `Φ` has `L^p(W)` norm at most that of
`Φ` on `V`. -/
theorem l2c_eLpNorm_le_on {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedAddCommGroup E₂]
    (hWm : MeasurableSet W) {V : Set (Vec d)} (hV : MeasurableSet V) (hVW : V ⊆ W)
    {F : Vec d → E₁} {Φ : Vec d → E₂} {p : ℝ≥0∞}
    (hFm : AEStronglyMeasurable F (volume.restrict W)) (hF0 : ∀ x ∈ W, x ∉ V → F x = 0)
    (hFΦ : ∀ x ∈ V, ‖F x‖ ≤ ‖Φ x‖) :
    eLpNorm F p (volume.restrict W) ≤ eLpNorm Φ p (volume.restrict V) := by
  have h1 : eLpNorm F p (volume.restrict W) ≤ eLpNorm (V.indicator Φ) p (volume.restrict W) := by
    refine eLpNorm_mono_ae hFm ((ae_restrict_iff' hWm).2 (Eventually.of_forall fun x hx => ?_))
    by_cases hxV : x ∈ V
    · rw [indicator_of_mem hxV]
      exact hFΦ x hxV
    · rw [hF0 x hx hxV]
      simp
  refine h1.trans (le_of_eq ?_)
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hV, Measure.restrict_restrict hV,
    inter_eq_left.2 hVW]

/-- A point of `W` at distance `< t` from `Wᶜ` lies in the boundary layer of width `t`. -/
theorem l2c_mem_layer [NeZero d] (hWb : Bornology.IsBounded W) {x : Vec d} (hx : x ∈ W) {t : ℝ}
    (ht : Metric.infDist x Wᶜ < t) : x ∈ boundaryLayer W t := by
  have hne : W ≠ univ := by
    intro hWu
    subst hWu
    exact NormedSpace.unbounded_univ ℝ (Vec d) hWb
  obtain ⟨y, hy, hxy⟩ := exists_mem_frontier_infDist_compl_eq_dist hx hne
  refine ⟨hx, ?_⟩
  have : Metric.infDist x (frontier W) ≤ dist x y := Metric.infDist_le_dist_of_mem hy
  linarith only [this, hxy, ht]

/-- A uniformly `C^{1,1}` domain is bounded. -/
theorem l2c_bounded {r₀ M₁ M₂ D : ℝ} (hU : IsUniformC11Domain W r₀ M₁ M₂ D) :
    Bornology.IsBounded W := by
  rcases W.eq_empty_or_nonempty with he | ⟨x₀, hx₀⟩
  · rw [he]; exact Bornology.isBounded_empty
  · refine (Metric.isBounded_iff_subset_closedBall x₀).2 ⟨D, fun y hy => ?_⟩
    rw [mem_closedBall_iff_norm]
    exact hU.2.2.1 y hy x₀ hx₀

theorem l2c_continuous_eucNorm : Continuous (eucNorm : Vec d → ℝ) := by
  unfold eucNorm vecNormSq vecDot
  exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ =>
    (continuous_apply i).mul (continuous_apply i))

/-- **The mollification error of the extension**: for `V` at distance `≥ r` from `Wᶜ`
and `h ≤ r / 4`, `‖ũ - η_h ∗ ũ‖_{L²(V)} ≤ d h ‖∇u‖_{L²(W)}`. -/
theorem l2c_mollError (hW : IsOpen W) (hWb : Bornology.IsBounded W) {r : ℝ} (hr : 0 < r)
    {h : ℝ} (hh : 0 < h) (hhr : h ≤ r / 4) {η : Vec d → ℝ} (hηc : Continuous η)
    (hη0 : ∀ w, 0 ≤ η w) (hη1 : ∫ w, η w = 1) (hηs : ∀ w, (∃ i, 1 < |w i|) → η w = 0)
    (u : H1Function W) {V : Set (Vec d)} (hV : MeasurableSet V)
    (hVr : ∀ x ∈ V, r ≤ Metric.infDist x Wᶜ) :
    eLpNorm (fun x => (l2c_ext hW hWb hr u).toFun x -
        l2a_moll d h η (l2c_ext hW hWb hr u).toFun x) 2 (volume.restrict V) ≤
      ENNReal.ofReal (d * h) * eLpNorm u.grad 2 (volume.restrict W) := by
  set Wo : Set (Vec d) := {x | r / 2 < Metric.infDist x Wᶜ} with hWo
  have hWoo : IsOpen Wo :=
    isOpen_lt continuous_const (Metric.continuous_infDist_pt _)
  have hWoW : Wo ⊆ W := fun x hx => by
    by_contra hxW
    have : Metric.infDist x Wᶜ = 0 := Metric.infDist_zero_of_mem (show x ∈ Wᶜ from hxW)
    have hx' : r / 2 < Metric.infDist x Wᶜ := hx
    linarith only [this, hx', hr]
  have hVW : ∀ x ∈ V, ∀ y, dist y x ≤ h → y ∈ Wo := fun x hx y hy => by
    have h1 := Metric.infDist_le_infDist_add_dist (x := x) (y := y) (s := Wᶜ)
    have h2 := hVr x hx
    show r / 2 < Metric.infDist y Wᶜ
    rw [dist_comm] at hy
    linarith only [h1, h2, hy, hhr, hr]
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  have key := l2c_sub_conv_ae hh hηc hη0 hη1 hηs hWoo hV hVW (l2c_ext hW hWb hr u)
    (q := 2) (by norm_num)
  rw [← h2] at key
  refine key.trans ?_
  have hgr : eLpNorm (fun y => eucNorm ((l2c_ext hW hWb hr u).grad y)) 2 (volume.restrict Wo) ≤
      ENNReal.ofReal (Real.sqrt d) * eLpNorm u.grad 2 (volume.restrict W) := by
    have hm : AEStronglyMeasurable (fun y => eucNorm ((l2c_ext hW hWb hr u).grad y))
        (volume.restrict Wo) := by
      have h0 := l2c_aesm_grad (l2c_ext hW hWb hr u)
      rw [Measure.restrict_univ] at h0
      exact (l2c_continuous_eucNorm.comp_aestronglyMeasurable h0).mono_measure
        Measure.restrict_le_self
    have h3 : eLpNorm (fun y => eucNorm ((l2c_ext hW hWb hr u).grad y)) 2 (volume.restrict Wo) ≤
        eLpNorm ((Real.sqrt d) • u.grad) 2 (volume.restrict Wo) := by
      refine eLpNorm_mono_ae hm ((ae_restrict_iff' hWoo.measurableSet).2
        (Eventually.of_forall fun x hx => ?_))
      have hn : 0 ≤ eucNorm (u.grad x) := Real.sqrt_nonneg _
      rw [l2c_ext_grad hW hWb hr u (hWoW hx) hx, Real.norm_eq_abs, abs_of_nonneg hn]
      simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact l2c_eucNorm_le _
    rw [eLpNorm_const_smul] at h3
    refine h3.trans ?_
    rw [Real.enorm_eq_ofReal (Real.sqrt_nonneg _)]
    gcongr
  refine (mul_le_mul' le_rfl hgr).trans (le_of_eq ?_)
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  have := Real.mul_self_sqrt (Nat.cast_nonneg (α := ℝ) d)
  linear_combination h * this

/-- **The layer Poincaré estimate for `u - g ∈ H¹₀(W)`**: on every subset `S`
of the boundary layer of width `t ≤ t₀`, `‖u - g‖_{L²(S)} ≤ C t (‖∇u‖_{L²(W)} + ‖∇g‖_{L²(W)})`.
The constants depend only on `(d, r₀, M₁)`. -/
theorem l2c_poincare [NeZero d] (r₀ M₁ : ℝ) (hr₀ : 0 < r₀) :
    ∃ C t₀ : ℝ, 0 ≤ C ∧ 0 < t₀ ∧ ∀ {W : Set (Vec d)} {M₂ D : ℝ},
      IsUniformC11Domain W r₀ M₁ M₂ D → ∀ (u g : H1Function W) (ψ : H10Function W),
        ψ.toH1Function = u - g → ∀ {t : ℝ}, 0 < t → t ≤ t₀ → ∀ {S : Set (Vec d)},
          S ⊆ boundaryLayer W t →
          eLpNorm (fun x => u.toFun x - g.toFun x) 2 (volume.restrict S) ≤
            ENNReal.ofReal (C * t) *
              (eLpNorm u.grad 2 (volume.restrict W) + eLpNorm g.grad 2 (volume.restrict W)) := by
  obtain ⟨C, K, t₀, hC, hK, ht₀, H⟩ := exists_layerPoincare (d := d) r₀ M₁ hr₀
  refine ⟨C, t₀, hC, ht₀, fun {W M₂ D} hU u g ψ hψ t ht htt S hS => ?_⟩
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  have hH := H hU ψ (q := 2) (by norm_num) ht htt
  rw [← h2] at hH
  have hf : ∀ x, ψ.toH1Function.toFun x = u.toFun x - g.toFun x := fun x => by
    rw [hψ, H1Function.sub_toFun]
  have hgr : ∀ x, ψ.toH1Function.grad x = u.grad x - g.grad x := fun x => by
    rw [hψ, H1Function.sub_grad]
  have h1 : eLpNorm (fun x => u.toFun x - g.toFun x) 2 (volume.restrict S) ≤
      eLpNorm ψ.toH1Function.toFun 2 (volume.restrict (boundaryLayer W t)) := by
    have : ψ.toH1Function.toFun = fun x => u.toFun x - g.toFun x := funext hf
    rw [this]
    exact eLpNorm_mono_measure _ (Measure.restrict_mono hS le_rfl)
  refine h1.trans (hH.trans ?_)
  gcongr
  have hbl : boundaryLayer W (K * t) ⊆ W := fun x hx => hx.1
  rw [eLpNorm_norm _ ((l2c_aesm_grad ψ.toH1Function).mono_measure (Measure.restrict_mono hbl le_rfl))]
  have hgfun : ψ.toH1Function.grad = u.grad - g.grad := funext hgr
  rw [hgfun]
  refine (eLpNorm_mono_measure _ (Measure.restrict_mono hbl le_rfl)).trans ?_
  exact eLpNorm_sub_le (by norm_num)

/-- Measurability of a whole-space `H¹` function on any restricted measure. -/
theorem l2c_aesm_toFun_univ (ψ : H1Function (Set.univ : Set (Vec d))) (V : Set (Vec d)) :
    AEStronglyMeasurable ψ.toFun (volume.restrict V) := by
  have h0 := ψ.memL2.aestronglyMeasurable
  rw [Measure.restrict_univ] at h0
  exact h0.mono_measure Measure.restrict_le_self

/-- Measurability of the value of an `H¹(W)` function. -/
theorem l2c_aesm_toFun {V : Set (Vec d)} (g : H1Function V) :
    AEStronglyMeasurable g.toFun (volume.restrict V) :=
  g.memL2.aestronglyMeasurable

/-- Elementary combination of the two layer terms. -/
theorem l2c_combine {r h D C₁ : ℝ} (hr : 0 < r) (hhr : h ≤ r / 4) (hD : 0 ≤ D)
    (hC : 0 ≤ C₁) (A B : ℝ≥0∞) :
    ENNReal.ofReal (1 / r) * (ENNReal.ofReal (D * h) * A +
        ENNReal.ofReal (C₁ * (3 * r)) * (A + B)) ≤
      ENNReal.ofReal (D / 4 + 3 * C₁) * (A + B) := by
  rw [mul_add, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (by positivity) (by positivity),
    add_mul]
  have e1 : 1 / r * (D * h) ≤ D / 4 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hr]
    nlinarith only [hhr, hD, hr]
  have e2 : 1 / r * (C₁ * (3 * r)) = 3 * C₁ := by field_simp
  rw [e2]
  gcongr
  exact le_self_add

/-- Measurability of the boundary term `∇ζ (η_h ∗ ũ - g)`. -/
theorem l2c_E5_meas (hW : IsOpen W) (hWb : Bornology.IsBounded W) {r : ℝ} (hr : 0 < r)
    {h : ℝ} (hh : 0 < h) {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηs : ∀ w, (∃ i, 1 < |w i|) → η w = 0) (u g : H1Function W) :
    AEStronglyMeasurable (fun x => (l2a_moll d h η (l2c_ext hW hWb hr u).toFun x - g.toFun x) •
        lipGradient (l2a_cutoff W r) x) (volume.restrict W) := by
  have hmc : Continuous (l2a_moll d h η (l2c_ext hW hWb hr u).toFun) :=
    (l2a_moll_contDiff hh hη hηs
      (l2a_locInt_of_memL2_univ (l2c_ext hW hWb hr u).memL2)).continuous
  refine ((hmc.aestronglyMeasurable.sub (l2c_aesm_toFun g))).smul ?_
  exact (aemeasurable_pi_iff.2 fun i =>
    (aestronglyMeasurable_partialDeriv (l2a_cutoff W r) i).aemeasurable).aestronglyMeasurable
    |>.mono_measure Measure.restrict_le_self


/-- The `L²` form of the boundary term `∇ζ (η_h ∗ ũ - g)`, given the layer
Poincaré estimate for `u - g` on subsets of the layer of width `3 r`. -/
theorem l2c_E5_raw [NeZero d] (hW : IsOpen W) (hWb : Bornology.IsBounded W) {r : ℝ} (hr : 0 < r)
    {h : ℝ} (hh : 0 < h) (hhr : h ≤ r / 4) {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη0 : ∀ w, 0 ≤ η w) (hη1 : ∫ w, η w = 1) (hηs : ∀ w, (∃ i, 1 < |w i|) → η w = 0)
    (u g : H1Function W) {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hP : ∀ S : Set (Vec d), S ⊆ boundaryLayer W (3 * r) →
      eLpNorm (fun x => u.toFun x - g.toFun x) 2 (volume.restrict S) ≤
        ENNReal.ofReal (C₁ * (3 * r)) *
          (eLpNorm u.grad 2 (volume.restrict W) + eLpNorm g.grad 2 (volume.restrict W))) :
    eLpNorm (fun x => (l2a_moll d h η (l2c_ext hW hWb hr u).toFun x - g.toFun x) •
        lipGradient (l2a_cutoff W r) x) 2 (volume.restrict W) ≤
      ENNReal.ofReal (d / 4 + 3 * C₁) *
        (eLpNorm u.grad 2 (volume.restrict W) + eLpNorm g.grad 2 (volume.restrict W)) := by
  set ũ := l2c_ext hW hWb hr u with hũ
  set m : Vec d → ℝ := l2a_moll d h η ũ.toFun with hm
  have hmc : Continuous m :=
    (l2a_moll_contDiff hh hη hηs (l2a_locInt_of_memL2_univ ũ.memL2)).continuous
  set S : Set (Vec d) := {x | x ∈ W ∧ r ≤ Metric.infDist x Wᶜ ∧ Metric.infDist x Wᶜ ≤ 2 * r}
    with hS
  have hcont : Continuous fun x : Vec d => Metric.infDist x Wᶜ := Metric.continuous_infDist_pt _
  have hSm : MeasurableSet S :=
    hW.measurableSet.inter ((measurableSet_le measurable_const hcont.measurable).inter
      (measurableSet_le hcont.measurable measurable_const))
  have hSW : S ⊆ W := fun x hx => hx.1
  have hSl : S ⊆ boundaryLayer W (3 * r) := fun x hx =>
    l2c_mem_layer hWb hx.1 (by linarith only [hx.2.2, hr])
  have hlip : ∀ x, ‖lipGradient (l2a_cutoff W r) x‖ ≤ 1 / r := fun x =>
    (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => by
      rw [Real.norm_eq_abs]; exact l2a_lipGradient_cutoff_abs_le W hr x i
  have hFm := l2c_E5_meas hW hWb hr hh hη hηs u g
  have ha : AEStronglyMeasurable (fun x => ũ.toFun x - m x) (volume.restrict S) :=
    (l2c_aesm_toFun_univ ũ S).sub hmc.aestronglyMeasurable
  have hb : AEStronglyMeasurable (fun x => u.toFun x - g.toFun x) (volume.restrict S) :=
    ((l2c_aesm_toFun u).sub (l2c_aesm_toFun g)).mono_measure (Measure.restrict_mono hSW le_rfl)
  set A := eLpNorm u.grad 2 (volume.restrict W)
  set B := eLpNorm g.grad 2 (volume.restrict W)
  have hΦ : eLpNorm ((1 / r : ℝ) • fun x => ‖ũ.toFun x - m x‖ + ‖u.toFun x - g.toFun x‖) 2
      (volume.restrict S) ≤
      ENNReal.ofReal (1 / r) * (ENNReal.ofReal (d * h) * A +
        ENNReal.ofReal (C₁ * (3 * r)) * (A + B)) := by
    rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (by positivity)]
    gcongr
    refine (eLpNorm_add_le (by norm_num)).trans ?_
    rw [eLpNorm_norm _ ha, eLpNorm_norm _ hb]
    exact add_le_add
      (l2c_mollError hW hWb hr hh hhr hη.continuous hη0 hη1 hηs u hSm fun x hx => hx.2.1)
      (hP S hSl)
  refine (l2c_eLpNorm_le_on hW.measurableSet hSm hSW hFm (fun x hx hxS => ?_) (fun x hx => ?_)).trans
    (hΦ.trans (l2c_combine hr hhr (Nat.cast_nonneg d) hC₁ A B))
  · have : lipGradient (l2a_cutoff W r) x = 0 := by
      refine l2a_lipGradient_cutoff_eq_zero W hr ?_
      rcases lt_or_ge (Metric.infDist x Wᶜ) r with h1 | h1
      · exact Or.inl h1
      · right
        by_contra h2
        exact hxS ⟨hx, h1, not_lt.1 h2⟩
    simp [this]
  · have hũu : ũ.toFun x = u.toFun x :=
      l2c_ext_toFun hW hWb hr u hx.1 (by linarith only [hx.2.1, hr])
    have h1 : |m x - g.toFun x| ≤ ‖ũ.toFun x - m x‖ + ‖u.toFun x - g.toFun x‖ := by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, hũu]
      calc |m x - g.toFun x| = |(u.toFun x - g.toFun x) - (u.toFun x - m x)| := by ring_nf
        _ ≤ |u.toFun x - g.toFun x| + |u.toFun x - m x| := abs_sub _ _
        _ = _ := by rw [add_comm, abs_sub_comm (u.toFun x) (m x)]
    have h2 := hlip x
    have hn : 0 ≤ ‖ũ.toFun x - m x‖ + ‖u.toFun x - g.toFun x‖ := by positivity
    calc ‖(m x - g.toFun x) • lipGradient (l2a_cutoff W r) x‖
        = |m x - g.toFun x| * ‖lipGradient (l2a_cutoff W r) x‖ := by
          rw [norm_smul, Real.norm_eq_abs]
      _ ≤ (‖ũ.toFun x - m x‖ + ‖u.toFun x - g.toFun x‖) * (1 / r) := by gcongr
      _ = ‖((1 / r : ℝ) • fun x => ‖ũ.toFun x - m x‖ + ‖u.toFun x - g.toFun x‖) x‖ := by
        rw [Pi.smul_apply, smul_eq_mul, norm_mul, Real.norm_of_nonneg hn,
          Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / r), mul_comm]

/-- The boundary term vanishes at the points of `W` outside the layer of width `3 r`. -/
theorem l2c_E5_zero [NeZero d] (hWb : Bornology.IsBounded W) {r : ℝ} (hr : 0 < r) {x : Vec d}
    (hx : x ∈ W) (hxl : x ∉ boundaryLayer W (3 * r)) {c : ℝ} :
    c • lipGradient (l2a_cutoff W r) x = 0 := by
  have : lipGradient (l2a_cutoff W r) x = 0 := by
    refine l2a_lipGradient_cutoff_eq_zero W hr (Or.inr ?_)
    by_contra h2
    exact hxl (l2c_mem_layer hWb hx (by linarith only [not_lt.1 h2, hr]))
  simp [this]

theorem l2c_lpBar_two {E : Type*} [NormedAddCommGroup E] {V : Set (Vec d)} {F : Vec d → E}
    (hF : AEStronglyMeasurable F (volume.restrict V)) :
    lpBar V 2 F = ((volume V)⁻¹) ^ (1 / 2 : ℝ) * eLpNorm F 2 (volume.restrict V) := by
  have := l2c_lpBar_eq (V := V) (p := 2) (by norm_num) hF
  simpa using this

/-- **The boundary term `e.Dir.new.boundary.u.term`**: for `1 ≤ p ≤ 2` (`p = 2_*`),
`‖∇ζ (η_h ∗ ũ - g)‖_{L̲^p(W)} ≤ (|layer| / |W|)^{1/p - 1/2} C (‖∇u‖_{L̲²(W)} + ‖∇g‖_{L̲²(W)})`,
where `ζ` is the cutoff of margin `r`, `h ≤ r / 4`, and the layer is the boundary layer of width `3 r`.
The constants `C, ρ` depend only on `(d, r₀, M₁)`. -/
theorem l2c_boundary_u_term [NeZero d] (r₀ M₁ : ℝ) (hr₀ : 0 < r₀) :
    ∃ C ρ : ℝ, 0 ≤ C ∧ 0 < ρ ∧ ∀ {W : Set (Vec d)} {M₂ D : ℝ}
      (hU : IsUniformC11Domain W r₀ M₁ M₂ D) {r h : ℝ} (hr : 0 < r), r ≤ ρ → 0 < h → h ≤ r / 4 →
      ∀ {η : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) η → (∀ w, 0 ≤ η w) → ∫ w, η w = 1 →
      (∀ w, (∃ i, 1 < |w i|) → η w = 0) →
      ∀ (u g : H1Function W) (ψ : H10Function W), ψ.toH1Function = u - g →
      ∀ {p : ℝ}, 1 ≤ p → p ≤ 2 → volume W ≠ 0 →
        lpBar W (ENNReal.ofReal p) (fun x =>
            (l2a_moll d h η (l2c_ext hU.1 (l2c_bounded hU) hr u).toFun x - g.toFun x) •
              lipGradient (l2a_cutoff W r) x) ≤
          (volume (boundaryLayer W (3 * r)) / volume W) ^ (1 / p - 1 / 2) *
            (ENNReal.ofReal C * (lpBar W 2 u.grad + lpBar W 2 g.grad)) := by
  obtain ⟨C₁, t₀, hC₁, ht₀, HP⟩ := l2c_poincare (d := d) r₀ M₁ hr₀
  refine ⟨d / 4 + 3 * C₁, t₀ / 3, by positivity, by positivity, ?_⟩
  intro W M₂ D hU r h hr hrρ hh hhr η hη hη0 hη1 hηs u g ψ hψ p hp1 hp2 hW0
  have hWb := l2c_bounded hU
  have hWt : volume W ≠ ⊤ := hWb.measure_lt_top.ne
  have hraw := l2c_E5_raw hU.1 hWb hr hh hhr hη hη0 hη1 hηs u g hC₁ (fun S hS =>
    HP hU u g ψ hψ (t := 3 * r) (by positivity) (by linarith only [hrρ]) hS)
  have hFm := l2c_E5_meas hU.1 hWb hr hh hη hηs u g
  refine (l2c_holder_layer hU.1.measurableSet hW0 hWt hp1 hp2 hFm
    (L := boundaryLayer W (3 * r)) (fun x hx hxl => l2c_E5_zero hWb hr hx hxl)).trans ?_
  gcongr
  rw [l2c_lpBar_two hFm, l2c_lpBar_two (l2c_aesm_grad u), l2c_lpBar_two (l2c_aesm_grad g),
    ← mul_add, ← mul_assoc, mul_comm (ENNReal.ofReal _), mul_assoc]
  gcongr

/-- The `L²` form of `w - u`, given the layer Poincaré estimate for `u - g`. -/
theorem l2c_wu_raw [NeZero d] (hW : IsOpen W) (hWb : Bornology.IsBounded W) {r : ℝ} (hr : 0 < r)
    {h : ℝ} (hh : 0 < h) (hhr : h ≤ r / 4) {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη0 : ∀ w, 0 ≤ η w) (hη1 : ∫ w, η w = 1) (hηs : ∀ w, (∃ i, 1 < |w i|) → η w = 0)
    (u g : H1Function W) {C₁ : ℝ}
    (hP : ∀ S : Set (Vec d), S ⊆ boundaryLayer W (3 * r) →
      eLpNorm (fun x => u.toFun x - g.toFun x) 2 (volume.restrict S) ≤
        ENNReal.ofReal (C₁ * (3 * r)) *
          (eLpNorm u.grad 2 (volume.restrict W) + eLpNorm g.grad 2 (volume.restrict W))) :
    eLpNorm (fun x => (l2a_wH1 hW hWb hh hη hηs (l2c_ext hW hWb hr u) g
        (l2a_cutoff_lipschitz W hr) (l2a_cutoff_nonneg W r) (l2a_cutoff_le_one W r)).toFun x -
        u.toFun x) 2 (volume.restrict W) ≤
      ENNReal.ofReal (d * h) * eLpNorm u.grad 2 (volume.restrict W) +
        ENNReal.ofReal (C₁ * (3 * r)) *
          (eLpNorm u.grad 2 (volume.restrict W) + eLpNorm g.grad 2 (volume.restrict W)) := by
  set ũ := l2c_ext hW hWb hr u with hũ
  set m : Vec d → ℝ := l2a_moll d h η ũ.toFun with hm
  set ζ : Vec d → ℝ := l2a_cutoff W r with hζ
  have hmc : Continuous m :=
    (l2a_moll_contDiff hh hη hηs (l2a_locInt_of_memL2_univ ũ.memL2)).continuous
  have hζc : Continuous ζ := l2a_cutoff_continuous W hr
  have hcont : Continuous fun x : Vec d => Metric.infDist x Wᶜ := Metric.continuous_infDist_pt _
  set V₁ : Set (Vec d) := {x | x ∈ W ∧ r ≤ Metric.infDist x Wᶜ} with hV₁
  have hV₁m : MeasurableSet V₁ :=
    hW.measurableSet.inter (measurableSet_le measurable_const hcont.measurable)
  have hV₁W : V₁ ⊆ W := fun x hx => hx.1
  have hV₂m : MeasurableSet (boundaryLayer W (3 * r)) := by
    have : IsOpen (boundaryLayer W (3 * r)) := layerPoincare_isOpen_boundaryLayer hW _
    exact this.measurableSet
  have hV₂W : boundaryLayer W (3 * r) ⊆ W := fun x hx => hx.1
  have hF₁m : AEStronglyMeasurable (fun x => ζ x * (m x - u.toFun x)) (volume.restrict W) :=
    hζc.aestronglyMeasurable.mul (hmc.aestronglyMeasurable.sub (l2c_aesm_toFun u))
  have hF₂m : AEStronglyMeasurable (fun x => (1 - ζ x) * (g.toFun x - u.toFun x))
      (volume.restrict W) :=
    (continuous_const.sub hζc).aestronglyMeasurable.mul
      ((l2c_aesm_toFun g).sub (l2c_aesm_toFun u))
  have hsplit : (fun x => (l2a_wH1 hW hWb hh hη hηs ũ g
        (l2a_cutoff_lipschitz W hr) (l2a_cutoff_nonneg W r) (l2a_cutoff_le_one W r)).toFun x -
        u.toFun x) = fun x => ζ x * (m x - u.toFun x) + (1 - ζ x) * (g.toFun x - u.toFun x) := by
    funext x
    rw [l2a_wH1_toFun]
    ring
  rw [hsplit]
  refine (eLpNorm_add_le (by norm_num)).trans (add_le_add ?_ ?_)
  · have hmo := l2c_mollError hW hWb hr hh hhr hη.continuous hη0 hη1 hηs u hV₁m
      (fun x hx => hx.2)
    refine le_trans (l2c_eLpNorm_le_on hW.measurableSet hV₁m hV₁W hF₁m (Φ := fun x => ũ.toFun x - m x)
      (fun x hx hxV => ?_) (fun x hx => ?_)) hmo
    · have : ζ x = 0 := l2a_cutoff_eq_zero hr (not_le.1 fun h' => hxV ⟨hx, h'⟩).le
      simp [this]
    · have hũu : ũ.toFun x = u.toFun x := l2c_ext_toFun hW hWb hr u hx.1 (by linarith only [hx.2, hr])
      rw [norm_mul, Real.norm_of_nonneg (l2a_cutoff_nonneg W r x), hũu, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_sub_comm (m x) (u.toFun x)]
      calc ζ x * |u.toFun x - m x| ≤ 1 * |u.toFun x - m x| := by
            gcongr; exact l2a_cutoff_le_one W r x
        _ = _ := one_mul _
  · refine le_trans (l2c_eLpNorm_le_on hW.measurableSet hV₂m hV₂W hF₂m
      (Φ := fun x => u.toFun x - g.toFun x) (fun x hx hxV => ?_) (fun x hx => ?_)) (hP _ le_rfl)
    · have h3 : 3 * r ≤ Metric.infDist x Wᶜ := not_lt.1 fun h' => hxV (l2c_mem_layer hWb hx h')
      have : ζ x = 1 := l2a_cutoff_eq_one hr (by linarith only [h3, hr])
      simp [this]
    · rw [norm_mul, Real.norm_of_nonneg (by linarith only [l2a_cutoff_le_one W r x] : 0 ≤ 1 - ζ x),
        Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm (g.toFun x) (u.toFun x)]
      calc (1 - ζ x) * |u.toFun x - g.toFun x| ≤ 1 * |u.toFun x - g.toFun x| := by
            gcongr; linarith only [l2a_cutoff_nonneg W r x]
        _ = _ := one_mul _

/-- **The difference `w - u`** (`e.Dir.new.w.minus.u`):
`‖w - u‖_{L̲²(W)} ≤ C (h + r) (‖∇u‖_{L̲²(W)} + ‖∇g‖_{L̲²(W)})`, for `w = ζ (η_h ∗ ũ) + (1 - ζ) g`,
`ζ` the cutoff of margin `r`, `h ≤ r / 4`.  Constants depend only on `(d, r₀, M₁)`. -/
theorem l2c_w_minus_u [NeZero d] (r₀ M₁ : ℝ) (hr₀ : 0 < r₀) :
    ∃ C ρ : ℝ, 0 ≤ C ∧ 0 < ρ ∧ ∀ {W : Set (Vec d)} {M₂ D : ℝ}
      (hU : IsUniformC11Domain W r₀ M₁ M₂ D) {r h : ℝ} (hr : 0 < r), r ≤ ρ → ∀ (hh : 0 < h),
      h ≤ r / 4 →
      ∀ {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η), (∀ w, 0 ≤ η w) → ∫ w, η w = 1 →
      ∀ (hηs : ∀ w, (∃ i, 1 < |w i|) → η w = 0),
      ∀ (u g : H1Function W) (ψ : H10Function W), ψ.toH1Function = u - g →
        lpBar W 2 (fun x => (l2a_wH1 hU.1 (l2c_bounded hU) hh hη hηs
            (l2c_ext hU.1 (l2c_bounded hU) hr u) g (l2a_cutoff_lipschitz W hr)
            (l2a_cutoff_nonneg W r) (l2a_cutoff_le_one W r)).toFun x - u.toFun x) ≤
          ENNReal.ofReal (C * (h + r)) * (lpBar W 2 u.grad + lpBar W 2 g.grad) := by
  obtain ⟨C₁, t₀, hC₁, ht₀, HP⟩ := l2c_poincare (d := d) r₀ M₁ hr₀
  refine ⟨d + 3 * C₁, t₀ / 3, by positivity, by positivity, ?_⟩
  intro W M₂ D hU r h hr hrρ hh hhr η hη hη0 hη1 hηs u g ψ hψ
  have hWb := l2c_bounded hU
  have hraw := l2c_wu_raw hU.1 hWb hr hh hhr hη hη0 hη1 hηs u g (C₁ := C₁) (fun S hS =>
    HP hU u g ψ hψ (t := 3 * r) (by positivity) (by linarith only [hrρ]) hS)
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

/-- A bound on the layer measure passes to the ratio. -/
theorem l2c_ratio_le {L W : Set (Vec d)} {B : ℝ≥0∞} (hL : volume L ≤ B) {e : ℝ} (he : 0 ≤ e) :
    (volume L / volume W) ^ e ≤ (B / volume W) ^ e := by
  gcongr

/-- **The boundary term of the datum with the explicit layer measure**
(`e.Dir.new.boundary.g.term`): on a uniformly `C^{1,1}` domain, for the cutoff of margin `r`
(`2 r ≤ r₀`),
`‖(1 - ζ) G‖_{L̲^p(W)} ≤ (C₀ (2 r) / |W|)^{1/p - 1/2} ‖G‖_{L̲²(W)}` for `1 ≤ p ≤ 2`. -/
theorem l2c_boundary_g_term_explicit [NeZero d] (r₀ M₁ D : ℝ) (hr₀ : 0 < r₀) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {W : Set (Vec d)} {M₂ : ℝ}, IsUniformC11Domain W r₀ M₁ M₂ D →
      ∀ {r : ℝ}, 0 < r → 2 * r ≤ r₀ → ∀ {p : ℝ}, 1 ≤ p → p ≤ 2 → volume W ≠ 0 →
      ∀ {G : Vec d → Vec d}, AEStronglyMeasurable G (volume.restrict W) →
        lpBar W (ENNReal.ofReal p) (fun x => (1 - l2a_cutoff W r x) • G x) ≤
          (ENNReal.ofReal (C₀ * (2 * r)) / volume W) ^ (1 / p - 1 / 2) * lpBar W 2 G := by
  obtain ⟨C₀, hC₀, H⟩ := l2a_exists_cutoff (d := d) r₀ M₁ D hr₀
  refine ⟨C₀, hC₀, fun {W M₂} hU r hr h2r p hp1 hp2 hW0 G hG => ?_⟩
  have hWt : volume W ≠ ⊤ := (l2c_bounded hU).measure_lt_top.ne
  have he : 0 ≤ 1 / p - 1 / 2 := by
    have : 1 / 2 ≤ 1 / p := one_div_le_one_div_of_le (by linarith only [hp1]) hp2
    linarith only [this]
  refine (l2c_boundary_g_term hU.1.measurableSet hW0 hWt hp1 hp2 (l2a_cutoff_continuous W hr)
    (l2a_cutoff_nonneg W r) (l2a_cutoff_le_one W r) hG).trans ?_
  exact mul_le_mul' (l2c_ratio_le (H hU hr h2r).2.2.2.2.2.2 he) le_rfl

/-- The mollifier hypotheses of the boundary-layer estimates are satisfiable. -/
theorem l2c_mollifier_witness (d : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (li1_bump d) ∧ (∀ w, 0 ≤ li1_bump d w) ∧ ∫ w, li1_bump d w = 1 ∧
      ∀ w : Vec d, (∃ i, 1 < |w i|) → li1_bump d w = 0 := by
  refine ⟨li1_bump_contDiff d, li1_bump_nonneg d, li1_bump_integral d, fun w ⟨i, hi⟩ => ?_⟩
  by_contra hne
  have := li1_bump_norm_lt hne
  have h2 := norm_le_pi_norm w i
  rw [Real.norm_eq_abs] at h2
  linarith only [this, h2, hi]

/-- **Satisfiability** of `l2c_boundary_u_term` and `l2c_w_minus_u`: on the unit ball, with the
standard bump and zero data (`u = g = ψ = 0`), all hypotheses hold, and the conclusions are
instantiated. -/
theorem l2c_witness [NeZero d] :
    ∃ (r₀ M₁ M₂ D : ℝ), IsUniformC11Domain (Section6.euclidBall (d := d) 1) r₀ M₁ M₂ D ∧
      volume (Section6.euclidBall (d := d) 1) ≠ 0 ∧
      ((0 : H10Function (Section6.euclidBall (d := d) 1)).toH1Function =
        (0 : H1Function (Section6.euclidBall (d := d) 1)) - 0) := by
  obtain ⟨r₀, M₁, M₂, D, hU⟩ := isUniformC11Domain_euclidBall (d := d)
  exact ⟨r₀, M₁, M₂, D, hU, Section6.volume_euclidBall_ne_zero one_pos, by simp; rfl⟩

example [NeZero d] : True := by
  obtain ⟨r₀, M₁, M₂, D, hU, hvol, hψ⟩ := l2c_witness (d := d)
  obtain ⟨hη, hη0, hη1, hηs⟩ := l2c_mollifier_witness d
  obtain ⟨C, ρ, hC, hρ, H⟩ := l2c_boundary_u_term (d := d) r₀ M₁ hU.2.1
  have := H hU (r := ρ) hρ le_rfl (h := ρ / 4) (by positivity) le_rfl hη hη0 hη1 hηs 0 0 0 hψ
    (p := 3 / 2) (by norm_num) (by norm_num) hvol
  obtain ⟨C', ρ', hC', hρ', H'⟩ := l2c_w_minus_u (d := d) r₀ M₁ hU.2.1
  have := H' hU (r := ρ') hρ' le_rfl (h := ρ' / 4) (by positivity) le_rfl hη hη0 hη1 hηs 0 0 0 hψ
  obtain ⟨C₀, hC₀, H₀⟩ := l2c_boundary_g_term_explicit (d := d) r₀ M₁ D hU.2.1
  have := H₀ hU (r := r₀ / 2) (by have := hU.2.1; positivity) (by linarith only)
    (p := 3 / 2) (by norm_num) (by norm_num) hvol (G := fun _ => 0) aestronglyMeasurable_const
  trivial

end SuperdiffusionCLT.Section7
