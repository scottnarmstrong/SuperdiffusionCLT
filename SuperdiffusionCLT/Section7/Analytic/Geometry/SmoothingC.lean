/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Geometry.SmoothingB
public import SuperdiffusionCLT.Section7.Analytic.Change.ShearH1B
public import Homogenization.Sobolev.H1.BasicLemmas
public import SuperdiffusionCLT.Section7.Analytic.Geometry.AtlasTransform

/-!
# Lipschitz representatives on a chart piece

Let `U ∩ B(x, r) = {y ∈ B(x, r) : ⟨e, y⟩ < ψ(P y)}` with `ψ` smooth and `M₁`-Lipschitz.  The shear
`Ψ = shear e (-ψ)` is a bi-Lipschitz volume preserving map taking the half space `{⟨e, z⟩ < 0}`
into `U` inside the chart.  Pulling an `H¹(U)` function with bounded gradient back by `Ψ` and
restricting to a convex half ball gives a Lipschitz representative (convex `W^{1,∞}`), which is
pushed forward by the inverse shear.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open MeasureTheory Homogenization Filter Topology

variable {d : ℕ}

/-- The partial derivatives of `ψ ∘ P` are at most `(1 + d) K` for a `K`-Lipschitz `ψ`. -/
theorem abs_projGrad_le {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ} {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ y z, |ψ y - ψ z| ≤ K * ‖y - z‖) (i : Fin d) (y : Vec d) :
    |projGrad e ψ i y| ≤ (1 + d) * K := by
  have hlip : LipschitzWith (Real.toNNReal ((1 + d) * K)) (projComp e ψ) := by
    refine LipschitzWith.of_dist_le_mul fun y z => ?_
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity), Real.norm_eq_abs]
    calc |projComp e ψ y - projComp e ψ z| ≤ K * ‖(y - vecDot e y • e) - (z - vecDot e z • e)‖ :=
          hK _ _
      _ ≤ K * ((1 + d) * ‖y - z‖) :=
          mul_le_mul_of_nonneg_left (norm_proj_sub_le he y z) hK0
      _ = _ := by ring
  have h1 := norm_fderiv_le_of_lipschitz ℝ hlip (x₀ := y)
  have h2 := (fderiv ℝ (projComp e ψ) y).le_opNorm (Pi.single i 1 : Vec d)
  have h3 : ‖(Pi.single i (1 : ℝ) : Vec d)‖ = 1 := by rw [Pi.norm_single]; simp
  rw [h3, mul_one] at h2
  rw [Real.coe_toNNReal _ (by positivity)] at h1
  unfold projGrad
  rw [← Real.norm_eq_abs]
  exact h2.trans h1

/-- The gradient of the pulled-back function is bounded by `A G`, `A = 1 + d (1 + d) M₁`. -/
theorem abs_compShear_grad_le {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ} {M₁ : ℝ}
    (hM : 0 ≤ M₁) (hK : ∀ y z, |ψ y - ψ z| ≤ M₁ * ‖y - z‖) (gr : Vec d) {G : ℝ}
    (hg : ∀ i, |gr i| ≤ G) (i : Fin d) (y : Vec d) :
    |gr i - vecDot e gr * projGrad e ψ i y| ≤ (1 + d * (1 + d) * M₁) * G := by
  have hG0 : 0 ≤ G := (abs_nonneg _).trans (hg i)
  have h1 : |vecDot e gr| ≤ d * G := by
    unfold vecDot
    calc |∑ j, e j * gr j| ≤ ∑ j, |e j * gr j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin d, G := Finset.sum_le_sum fun j _ => by
          rw [abs_mul]
          calc |e j| * |gr j| ≤ 1 * G :=
                mul_le_mul (abs_apply_le_one he j) (hg j) (abs_nonneg _) zero_le_one
            _ = G := one_mul _
      _ = d * G := by simp
  have h2 := abs_projGrad_le he hM hK i y
  calc |gr i - vecDot e gr * projGrad e ψ i y| ≤ |gr i| + |vecDot e gr * projGrad e ψ i y| :=
        abs_sub _ _
    _ ≤ G + (d * G) * ((1 + d) * M₁) := by
        rw [abs_mul]
        exact add_le_add (hg i) (mul_le_mul h1 h2 (abs_nonneg _) (by positivity))
    _ = _ := by ring

/-- **Chart piece.** Let `U ∩ B(x, r)` be the subgraph of the `M₁`-Lipschitz smooth graph function
`ψ`, and `g ∈ H¹(U)` with `|∂ᵢ g| ≤ G` a.e.  Then `g` has a Lipschitz representative on
`U ∩ B(x, r / L²)`, `L = 1 + (1 + d) M₁`, with constant `d (1 + d (1 + d) M₁) G L`. -/
theorem exists_chart_lipschitz_representative {U : Set (Vec d)} {x : Vec d}
    {r : ℝ} (hr : 0 < r) {e : Vec d} {ψ : Vec d → ℝ} {M₁ : ℝ} (he : vecNormSq e = 1)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hb : ∀ y, ‖fderiv ℝ ψ y‖ ≤ M₁)
    (hch : ∀ y ∈ Metric.ball x r, (y ∈ U ↔ vecDot e y < ψ (y - vecDot e y • e)))
    (g : H1Function U) {G : ℝ} (hG0 : 0 ≤ G)
    (hG : ∀ᵐ w ∂volume.restrict U, ∀ i, |g.grad w i| ≤ G) :
    ∃ ū : Vec d → ℝ,
      ū =ᵐ[volume.restrict (U ∩ Metric.ball x (r / (1 + (1 + d) * M₁) ^ 2))] g.toFun ∧
      ∀ y ∈ U ∩ Metric.ball x (r / (1 + (1 + d) * M₁) ^ 2),
        ∀ z ∈ U ∩ Metric.ball x (r / (1 + (1 + d) * M₁) ^ 2),
          |ū y - ū z| ≤ d * ((1 + d * (1 + d) * M₁) * G) * (1 + (1 + d) * M₁) * ‖y - z‖ := by
  have hM : 0 ≤ M₁ := (norm_nonneg _).trans (hb 0)
  set L : ℝ := 1 + (1 + d) * M₁ with hL
  have hL1 : 1 ≤ L := by rw [hL]; nlinarith only [hM, (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hL0 : 0 < L := by linarith only [hL1]
  set A : ℝ := 1 + d * (1 + d) * M₁ with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hK : ∀ y z, |ψ y - ψ z| ≤ M₁ * ‖y - z‖ := abs_sub_le_of_fderiv_bound hψ hb
  have hbn : ∀ y, ‖fderiv ℝ (-ψ) y‖ ≤ M₁ := fun y => by
    rw [fderiv_neg, norm_neg]; exact hb y
  have hKn : ∀ y z, |(-ψ) y - (-ψ) z| ≤ M₁ * ‖y - z‖ := fun y z => by
    have := abs_sub_le_of_fderiv_bound hψ.neg hbn y z
    simpa using this
  have hΦ : ∀ y z, ‖shear e ψ y - shear e ψ z‖ ≤ L * ‖y - z‖ :=
    norm_shear_sub_le he hM hK
  have hΨ : ∀ y z, ‖shear e (-ψ) y - shear e (-ψ) z‖ ≤ L * ‖y - z‖ :=
    norm_shear_sub_le he hM hKn
  have hbs : ∀ i, ∃ M, ∀ y, |fderiv ℝ (-ψ) y (Pi.single i 1)| ≤ M := fun i =>
    ⟨M₁, fun y => by
      have h1 := (fderiv ℝ (-ψ) y).le_opNorm (Pi.single i 1 : Vec d)
      have h3 : ‖(Pi.single i (1 : ℝ) : Vec d)‖ = 1 := by rw [Pi.norm_single]; simp
      rw [h3, mul_one, Real.norm_eq_abs] at h1
      exact h1.trans (hbn y)⟩
  -- the pullback
  set v : H1Function (shear e (-ψ) ⁻¹' U) := H1Function.compShear he hψ.neg hbs g with hv
  set x'' : Vec d := shear e ψ x with hx''
  set R : Set (Vec d) := {z | vecDot e z < 0} ∩ Metric.ball x'' (r / L) with hR
  have hRopen : IsOpen R := by
    have : Continuous fun z : Vec d => vecDot e z := by unfold vecDot; fun_prop
    exact (isOpen_lt this continuous_const).inter Metric.isOpen_ball
  have hRconv : Convex ℝ R := by
    have h1 : Convex ℝ {z : Vec d | vecDot e z < 0} := by
      have := (convex_Iio (0 : ℝ)).linear_preimage (dotCLM e).toLinearMap
      convert this using 1
      ext z
      simp [dotCLM_apply]
    exact h1.inter (convex_ball _ _)
  have hRbdd : IsOpenBoundedConvexDomain R :=
    ⟨hRopen, (Metric.isBounded_ball.subset Set.inter_subset_right).isBoundedDomain, hRconv⟩
  have hxx : shear e (-ψ) x'' = x := shear_neg_shear he ψ x
  have hRsub : R ⊆ shear e (-ψ) ⁻¹' U := by
    intro z hz
    have hzb : shear e (-ψ) z ∈ Metric.ball x r := by
      rw [Metric.mem_ball, dist_eq_norm]
      have h1 := hΨ z x''
      rw [hxx] at h1
      have h2 : ‖z - x''‖ < r / L := by
        have := hz.2
        rwa [Metric.mem_ball, dist_eq_norm] at this
      calc _ ≤ L * ‖z - x''‖ := h1
        _ < L * (r / L) := mul_lt_mul_of_pos_left h2 hL0
        _ = r := by field_simp
    refine (hch _ hzb).2 ?_
    have h1 := proj_shear he (-ψ) z
    have h2 : vecDot e (shear e (-ψ) z) = vecDot e z + ψ (z - vecDot e z • e) := by
      unfold shear
      rw [vecDot_sub_smul_self he]
      simp
    rw [h1, h2]
    have := hz.1
    simp only [Set.mem_ofPred_eq] at this
    linarith only [this]
  set vR : H1Function R := v.restrict hRopen hRsub with hvR
  -- the bound on the gradient
  have hmpΨ := measurePreserving_restrict_shear he hψ.neg U
  have hGΨ : ∀ᵐ z ∂volume.restrict (shear e (-ψ) ⁻¹' U), ∀ i, |g.grad (shear e (-ψ) z) i| ≤ G :=
    hmpΨ.quasiMeasurePreserving.ae hG
  have hGR := ae_restrict_of_ae_restrict_of_subset hRsub hGΨ
  have hGv : ∀ᵐ z ∂volume.restrict R, ∀ i, |vR.grad z i| ≤ A * G := by
    filter_upwards [hGR] with z hz i
    exact abs_compShear_grad_le he hM hKn (g.grad (shear e (-ψ) z)) hz i z
  obtain ⟨ūR, hae, hlip⟩ := exists_lipschitz_representative_of_convex hRbdd vR
    (mul_nonneg hA0 hG0) hGv
  -- the representative on the chart piece
  have hPR : ∀ y ∈ U ∩ Metric.ball x (r / L ^ 2), shear e ψ y ∈ R := by
    intro y hy
    have hyb : y ∈ Metric.ball x r := by
      refine Metric.ball_subset_ball ?_ hy.2
      rw [div_le_iff₀ (by positivity)]
      have hL2 : 1 ≤ L ^ 2 := by nlinarith only [hL1]
      nlinarith only [hr, mul_le_mul_of_nonneg_left hL2 hr.le]
    refine ⟨?_, ?_⟩
    · have h1 := (hch y hyb).1 hy.1
      show vecDot e (shear e ψ y) < 0
      unfold shear
      rw [vecDot_sub_smul_self he]
      linarith only [h1]
    · rw [Metric.mem_ball, dist_eq_norm]
      have h1 := hΦ y x
      have h2 : ‖y - x‖ < r / L ^ 2 := by
        have := hy.2
        rwa [Metric.mem_ball, dist_eq_norm] at this
      calc _ ≤ L * ‖y - x‖ := h1
        _ < L * (r / L ^ 2) := mul_lt_mul_of_pos_left h2 hL0
        _ = r / L := by field_simp
  refine ⟨fun y => ūR (shear e ψ y), ?_, ?_⟩
  · have hmpΦ := measurePreserving_restrict_shear he hψ R
    have hae' : ∀ᵐ z ∂volume.restrict R, ūR z = vR.toFun z := hae
    have h1 := hmpΦ.quasiMeasurePreserving.ae hae'
    have h2 : ∀ᵐ y ∂volume.restrict (U ∩ Metric.ball x (r / L ^ 2)),
        ūR (shear e ψ y) = vR.toFun (shear e ψ y) :=
      ae_restrict_of_ae_restrict_of_subset (fun y hy => hPR y hy) h1
    filter_upwards [h2] with y hy
    rw [hy]
    show g.toFun (shear e (-ψ) (shear e ψ y)) = g.toFun y
    rw [shear_neg_shear he ψ y]
  · intro y hy z hz
    have h1 := hlip _ (hPR y hy) _ (hPR z hz)
    refine h1.trans ?_
    calc d * (A * G) * ‖shear e ψ y - shear e ψ z‖ ≤ d * (A * G) * (L * ‖y - z‖) :=
          mul_le_mul_of_nonneg_left (hΦ y z) (by positivity)
      _ = _ := by ring

end SuperdiffusionCLT.Section7
