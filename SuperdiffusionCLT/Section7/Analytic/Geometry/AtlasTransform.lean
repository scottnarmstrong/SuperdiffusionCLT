/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Geometry.Atlas
public import SuperdiffusionCLT.Section7.Analytic.Change.Shear

/-!
# Affine changes of variables and chart estimates for uniformly `C^{1,1}` domains

* `Section7.IsUniformC11Domain.affineImage`: the image of a uniformly `C^{1,1}` domain under
  `x ↦ λ x + z` (`λ > 0`) has data `(λ r, M₁, M₂ / λ, λ D)`.
* `Section7.IsUniformC11Domain.translate`, `Section7.IsUniformC11Domain.smul`: the two special
  cases (translation keeps all four parameters; dilation by `λ` gives `(λ r, M₁, M₂/λ, λ D)`).
* chart estimates: Lipschitz bounds for the graph projection `y ↦ y - ⟨e, y⟩ e`, for the
  graph function `ψ` and for the shear `y ↦ y - ψ(Py) e` and its inverse; frontier points of `U`
  inside a chart ball lie on the graph; the vertical distance of a point of `U` to the graph is
  at most a constant times its distance to any frontier point in the chart ball.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization Pointwise

variable {d : ℕ}

/-! ### Affine images -/

theorem vecDot_affine (e : Vec d) (l : ℝ) (y z : Vec d) :
    vecDot e (l • y + z) = l * vecDot e y + vecDot e z := by
  simp only [vecDot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

theorem proj_affine (e : Vec d) (l : ℝ) (y z : Vec d) :
    (l • y + z) - vecDot e (l • y + z) • e
      = l • (y - vecDot e y • e) + (z - vecDot e z • e) := by
  rw [vecDot_affine]
  ext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The homeomorphism `x ↦ λ x + z` for `λ ≠ 0`. -/
noncomputable def affineHomeo {l : ℝ} (hl : l ≠ 0) (z : Vec d) : Vec d ≃ₜ Vec d :=
  (Homeomorph.smulOfNeZero l hl).trans (Homeomorph.addRight z)

/-- The rescaled graph function of the affine image. -/
noncomputable def affineGraph (e : Vec d) (ψ : Vec d → ℝ) (l : ℝ) (z : Vec d) (w : Vec d) : ℝ :=
  l * ψ (l⁻¹ • (w - (z - vecDot e z • e))) + vecDot e z

theorem HasC11ChartAt.affine {U : Set (Vec d)} {x : Vec d} {r M₁ M₂ : ℝ}
    (h : HasC11ChartAt U x r M₁ M₂) {l : ℝ} (hl : 0 < l) (z : Vec d) :
    HasC11ChartAt ((fun y => l • y + z) '' U) (l • x + z) (l * r) M₁ (M₂ / l) := by
  obtain ⟨e, ψ, he, hψ, hb1, hb2, hU⟩ := h
  have hl0 : l ≠ 0 := hl.ne'
  have hdiff : Differentiable ℝ ψ := hψ.differentiable (by simp)
  set g : Vec d → Vec d := fun w => l⁻¹ • (w - (z - vecDot e z • e)) with hgdef
  have hg : ∀ w, HasFDerivAt g ((l⁻¹ : ℝ) • ContinuousLinearMap.id ℝ (Vec d)) w := fun w =>
    ((hasFDerivAt_id w).sub_const _).const_smul (l⁻¹ : ℝ)
  have hψ' : ∀ w, HasFDerivAt (affineGraph e ψ l z) (fderiv ℝ ψ (g w)) w := fun w => by
    have h1 := (((hdiff (g w)).hasFDerivAt.comp w (hg w)).const_mul l).add_const (vecDot e z)
    refine h1.congr_fderiv ?_
    ext v
    simp [smul_smul, hl0]
  have hfd : ∀ w, fderiv ℝ (affineGraph e ψ l z) w = fderiv ℝ ψ (g w) := fun w =>
    (hψ' w).fderiv
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (affineGraph e ψ l z) := by
    unfold affineGraph
    exact (contDiff_const.mul (hψ.comp (((contDiff_id.sub contDiff_const).const_smul (l⁻¹ : ℝ))))).add contDiff_const
  refine ⟨e, affineGraph e ψ l z, he, hsm, fun w => ?_, fun w w' => ?_, fun y' hy' => ?_⟩
  · rw [hfd]; exact hb1 _
  · rw [hfd, hfd]
    refine (hb2 _ _).trans ?_
    have : g w - g w' = l⁻¹ • (w - w') := by
      simp only [hgdef, ← smul_sub]
      congr 1
      abel
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hl), div_eq_inv_mul]
    exact le_of_eq (by ring)
  · obtain ⟨y, rfl⟩ : ∃ y, y' = l • y + z := by
      refine ⟨l⁻¹ • (y' - z), ?_⟩
      rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]; abel
    have hy : y ∈ Metric.ball x r := by
      rw [Metric.mem_ball] at hy' ⊢
      rw [dist_eq_norm] at hy' ⊢
      have : l • y + z - (l • x + z) = l • (y - x) := by rw [smul_sub]; abel
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos hl] at hy'
      exact lt_of_mul_lt_mul_left hy' hl.le
    have hgy : l⁻¹ • (l • y + z - vecDot e (l • y + z) • e - (z - vecDot e z • e))
        = y - vecDot e y • e := by
      rw [proj_affine]
      rw [add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hl0, one_smul]
    rw [Function.Injective.mem_set_image (f := fun y : Vec d => l • y + z)
      (affineHomeo hl0 z).injective, hU y hy]
    unfold affineGraph
    rw [hgy, vecDot_affine]
    constructor <;> intro h <;> nlinarith only [h, hl]

/-- Affine images: `x ↦ λ x + z` sends a uniformly `C^{1,1}` domain with data `(r, M₁, M₂, D)` to
one with data `(λ r, M₁, M₂ / λ, λ D)`. -/
theorem IsUniformC11Domain.affineImage {U : Set (Vec d)} {r M₁ M₂ D : ℝ}
    (h : IsUniformC11Domain U r M₁ M₂ D) {l : ℝ} (hl : 0 < l) (z : Vec d) :
    IsUniformC11Domain ((fun y => l • y + z) '' U) (l * r) M₁ (M₂ / l) (l * D) := by
  obtain ⟨hopen, hr, hD, hch⟩ := h
  have hl0 : l ≠ 0 := hl.ne'
  have himg : (fun y : Vec d => l • y + z) '' U = affineHomeo hl0 z '' U := rfl
  refine ⟨?_, mul_pos hl hr, ?_, ?_⟩
  · rw [himg]; exact (affineHomeo hl0 z).isOpenMap U hopen
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have : l • x + z - (l • y + z) = l • (x - y) := by rw [smul_sub]; abel
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos hl]
    exact mul_le_mul_of_nonneg_left (hD x hx y hy) hl.le
  · intro x' hx'
    rw [himg, ← (affineHomeo hl0 z).image_frontier] at hx'
    obtain ⟨x, hx, rfl⟩ := hx'
    exact (hch x hx).affine hl z

/-- Translations preserve all four parameters. -/
theorem IsUniformC11Domain.translate {U : Set (Vec d)} {r M₁ M₂ D : ℝ}
    (h : IsUniformC11Domain U r M₁ M₂ D) (z : Vec d) :
    IsUniformC11Domain ((fun y => y + z) '' U) r M₁ M₂ D := by
  simpa using h.affineImage one_pos z

/-- Dilation by `λ > 0`: data `(λ r, M₁, M₂ / λ, λ D)`. -/
theorem IsUniformC11Domain.smul {U : Set (Vec d)} {r M₁ M₂ D : ℝ}
    (h : IsUniformC11Domain U r M₁ M₂ D) {l : ℝ} (hl : 0 < l) :
    IsUniformC11Domain (l • U) (l * r) M₁ (M₂ / l) (l * D) := by
  have := h.affineImage hl 0
  simpa [Set.image_smul] using this

/-- Witness: dilates and translates of the unit Euclidean ball. -/
theorem isUniformC11Domain_affineImage_euclidBall [NeZero d] {l : ℝ} (hl : 0 < l) (z : Vec d) :
    ∃ r M₁ M₂ D : ℝ,
      IsUniformC11Domain ((fun y => l • y + z) '' Section6.euclidBall (d := d) 1) r M₁ M₂ D := by
  obtain ⟨r, M₁, M₂, D, h⟩ := isUniformC11Domain_euclidBall (d := d)
  exact ⟨_, _, _, _, h.affineImage hl z⟩

/-! ### Chart estimates -/

theorem abs_apply_le_one {e : Vec d} (he : vecNormSq e = 1) (i : Fin d) : |e i| ≤ 1 := by
  have h1 : e i * e i ≤ 1 := by
    rw [← he]
    exact Finset.single_le_sum (f := fun j => e j * e j) (fun j _ => mul_self_nonneg _)
      (Finset.mem_univ i)
  by_contra hc
  have hc' := not_le.1 hc
  nlinarith only [h1, hc', abs_mul_abs_self (e i)]

theorem norm_le_one_of_vecNormSq {e : Vec d} (he : vecNormSq e = 1) : ‖e‖ ≤ 1 :=
  (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by simpa using abs_apply_le_one he i

theorem abs_vecDot_le {e : Vec d} (he : vecNormSq e = 1) (y : Vec d) :
    |vecDot e y| ≤ d * ‖y‖ := by
  unfold vecDot
  calc |∑ i, e i * y i| ≤ ∑ i, |e i * y i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, ‖y‖ := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]
        calc |e i| * |y i| ≤ 1 * ‖y‖ :=
              mul_le_mul (abs_apply_le_one he i) (by simpa using norm_le_pi_norm y i)
                (abs_nonneg _) zero_le_one
          _ = ‖y‖ := one_mul _
    _ = d * ‖y‖ := by simp

theorem vecDot_sub (e y z : Vec d) : vecDot e (y - z) = vecDot e y - vecDot e z := by
  simp only [vecDot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- The projection onto the hyperplane orthogonal to `e` is `(1 + d)`-Lipschitz (sup norm). -/
theorem norm_proj_sub_le {e : Vec d} (he : vecNormSq e = 1) (y z : Vec d) :
    ‖(y - vecDot e y • e) - (z - vecDot e z • e)‖ ≤ (1 + d) * ‖y - z‖ := by
  have h : (y - vecDot e y • e) - (z - vecDot e z • e) = (y - z) - vecDot e (y - z) • e := by
    rw [vecDot_sub]
    ext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h]
  calc ‖(y - z) - vecDot e (y - z) • e‖ ≤ ‖y - z‖ + ‖vecDot e (y - z) • e‖ := norm_sub_le _ _
    _ ≤ ‖y - z‖ + d * ‖y - z‖ := by
        gcongr
        rw [norm_smul, Real.norm_eq_abs]
        calc |vecDot e (y - z)| * ‖e‖ ≤ (d * ‖y - z‖) * 1 :=
              mul_le_mul (abs_vecDot_le he _) (norm_le_one_of_vecNormSq he) (norm_nonneg _)
                (by positivity)
          _ = d * ‖y - z‖ := mul_one _
    _ = (1 + d) * ‖y - z‖ := by ring

/-- A graph function with gradient bound `M₁` is `M₁`-Lipschitz (sup norm). -/
theorem abs_sub_le_of_fderiv_bound {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {M₁ : ℝ}
    (hb : ∀ y, ‖fderiv ℝ ψ y‖ ≤ M₁) (y z : Vec d) : |ψ y - ψ z| ≤ M₁ * ‖y - z‖ := by
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := ψ) (s := Set.univ)
    (fun x _ => (hψ.differentiable (by simp)) x) (fun x _ => hb x) convex_univ
    (Set.mem_univ z) (Set.mem_univ y)
  simpa [Real.norm_eq_abs, abs_sub_comm] using this

/-- `ψ ∘ P` is `(1 + d) M₁`-Lipschitz. -/
theorem abs_proj_comp_sub_le {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {M₁ : ℝ} (hb : ∀ y, ‖fderiv ℝ ψ y‖ ≤ M₁) (y z : Vec d) :
    |ψ (y - vecDot e y • e) - ψ (z - vecDot e z • e)| ≤ (1 + d) * M₁ * ‖y - z‖ := by
  have hM : 0 ≤ M₁ := (norm_nonneg _).trans (hb 0)
  refine (abs_sub_le_of_fderiv_bound hψ hb _ _).trans ?_
  calc M₁ * ‖(y - vecDot e y • e) - (z - vecDot e z • e)‖ ≤ M₁ * ((1 + d) * ‖y - z‖) :=
        mul_le_mul_of_nonneg_left (norm_proj_sub_le he y z) hM
    _ = (1 + d) * M₁ * ‖y - z‖ := by ring

/-- The shear `y ↦ y - ψ(Py) e` of a `K`-Lipschitz graph function is `(1 + (1 + d) K)`-Lipschitz.
It applies equally to the inverse shear `shear e (-ψ)`, since `-ψ` is `K`-Lipschitz too. -/
theorem norm_shear_sub_le {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ} {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ y z, |ψ y - ψ z| ≤ K * ‖y - z‖) (y z : Vec d) :
    ‖shear e ψ y - shear e ψ z‖ ≤ (1 + (1 + d) * K) * ‖y - z‖ := by
  have h : shear e ψ y - shear e ψ z
      = (y - z) - (ψ (y - vecDot e y • e) - ψ (z - vecDot e z • e)) • e := by
    unfold shear
    ext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h]
  have h1 := hK (y - vecDot e y • e) (z - vecDot e z • e)
  have h2 := norm_proj_sub_le he y z
  calc ‖(y - z) - (ψ (y - vecDot e y • e) - ψ (z - vecDot e z • e)) • e‖
      ≤ ‖y - z‖ + ‖(ψ (y - vecDot e y • e) - ψ (z - vecDot e z • e)) • e‖ := norm_sub_le _ _
    _ ≤ ‖y - z‖ + K * ((1 + d) * ‖y - z‖) := by
        gcongr
        rw [norm_smul, Real.norm_eq_abs]
        calc |ψ (y - vecDot e y • e) - ψ (z - vecDot e z • e)| * ‖e‖
            ≤ (K * ‖(y - vecDot e y • e) - (z - vecDot e z • e)‖) * 1 :=
              mul_le_mul h1 (norm_le_one_of_vecNormSq he) (norm_nonneg _)
                (mul_nonneg hK0 (norm_nonneg _))
          _ ≤ K * ((1 + d) * ‖y - z‖) := by
              rw [mul_one]; exact mul_le_mul_of_nonneg_left h2 hK0
    _ = (1 + (1 + d) * K) * ‖y - z‖ := by ring

/-- A frontier point of `U` inside a chart ball lies on the graph. -/
theorem vecDot_eq_of_mem_frontier {U : Set (Vec d)} (hU : IsOpen U) {x : Vec d} {r : ℝ}
    {e : Vec d} {ψ : Vec d → ℝ} (hψ : Continuous ψ)
    (hch : ∀ y ∈ Metric.ball x r, (y ∈ U ↔ vecDot e y < ψ (y - vecDot e y • e)))
    {x' : Vec d} (hx' : x' ∈ frontier U) (hmem : x' ∈ Metric.ball x r) :
    vecDot e x' = ψ (x' - vecDot e x' • e) := by
  have hnot : x' ∉ U := by
    rw [frontier, hU.interior_eq] at hx'
    exact hx'.2
  have hcl : x' ∈ closure U := frontier_subset_closure hx'
  have hge : ψ (x' - vecDot e x' • e) ≤ vecDot e x' := by
    by_contra hlt
    exact hnot ((hch x' hmem).2 (not_le.1 hlt))
  refine le_antisymm ?_ hge
  by_contra hlt
  have hlt' : ψ (x' - vecDot e x' • e) < vecDot e x' := not_le.1 hlt
  have hcont : Continuous fun y : Vec d => vecDot e y - ψ (y - vecDot e y • e) := by
    have : Continuous fun y : Vec d => vecDot e y := by unfold vecDot; fun_prop
    exact this.sub (hψ.comp (continuous_id.sub (this.smul continuous_const)))
  have hopen : IsOpen (Metric.ball x r ∩ {y | 0 < vecDot e y - ψ (y - vecDot e y • e)}) :=
    Metric.isOpen_ball.inter (isOpen_lt continuous_const hcont)
  obtain ⟨y, ⟨hyb, hypos⟩, hyU⟩ := mem_closure_iff.1 hcl _ hopen
    ⟨hmem, by simp only [Set.mem_ofPred_eq]; linarith only [hlt']⟩
  have := (hch y hyb).1 hyU
  simp only [Set.mem_ofPred_eq] at hypos
  linarith only [this, hypos]

/-- Vertical distance of a point of `U` in a chart ball to the graph is at most
`(d + (1 + d) M₁)` times its distance to any frontier point in the chart ball. -/
theorem vertical_dist_le {U : Set (Vec d)} (hU : IsOpen U) {x : Vec d} {r : ℝ}
    {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {M₁ : ℝ}
    (hb : ∀ y, ‖fderiv ℝ ψ y‖ ≤ M₁)
    (hch : ∀ y ∈ Metric.ball x r, (y ∈ U ↔ vecDot e y < ψ (y - vecDot e y • e)))
    {y x' : Vec d} (hy : y ∈ U) (hyb : y ∈ Metric.ball x r) (hx' : x' ∈ frontier U)
    (hx'b : x' ∈ Metric.ball x r) :
    0 < ψ (y - vecDot e y • e) - vecDot e y ∧
      ψ (y - vecDot e y • e) - vecDot e y ≤ (d + (1 + d) * M₁) * ‖y - x'‖ := by
  refine ⟨sub_pos.2 ((hch y hyb).1 hy), ?_⟩
  have hg := vecDot_eq_of_mem_frontier hU hψ.continuous hch hx' hx'b
  have h1 := abs_proj_comp_sub_le he hψ hb y x'
  have h2 := abs_vecDot_le he (y - x')
  rw [vecDot_sub] at h2
  have h3 := (abs_le.1 h1).2
  have h4 := (abs_le.1 h2).1
  nlinarith only [h3, h4, hg]

end SuperdiffusionCLT.Section7
