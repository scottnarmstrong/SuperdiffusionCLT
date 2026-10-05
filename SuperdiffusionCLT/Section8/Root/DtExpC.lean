/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Root.DtExpB
public import SuperdiffusionCLT.Section8.Prereq.ResolventEstimateB
public import SuperdiffusionCLT.Section8.Prereq.BallRescaling
public import SuperdiffusionCLT.Section8.Prereq.FieldDiffusionApi

/-!
# The error engine on a ball

Given the resolvent comparison on the dilated ball, a datum `b` that near the ball is the dilate of
a function `p` with `½ Δ p = κ`, the stopped solution `b + w - σ τ` (with `σ = κ ε² / opScale`) is
within `E₀ (G + |κ|)` of `p(ε ·)` on the closed ball.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization MeasureTheory MarkovProcess
open SuperdiffusionCLT.Section8.DivergenceForm
open SuperdiffusionCLT.Section7
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section6
open SuperdiffusionCLT.Section8.Brownian (vecLaplacian)
open scoped Pointwise ENNReal NNReal Topology

variable {d : ℕ} {nu : ℝ}

/-- The scalar-forced weak equation depends on the solution only through its gradient. -/
theorem dtExp_forced_congr_grad {U : Set (Vec d)} {a : CoeffField d} {g : Vec d → ℝ}
    {u₁ u₂ : H1Function U} (h : u₁.grad = u₂.grad)
    (h₁ : IsScalarForcedWeakSolution a U g u₁) : IsScalarForcedWeakSolution a U g u₂ := by
  refine ⟨h₁.1, fun φ => ?_⟩
  rw [← h]
  exact h₁.2 φ

/-- A scalar-forced weak solution is a weak solution in the sense of `IsWeakSolutionOn`. -/
theorem dtExp_weak_of_forced {U : Set (Vec d)} {a : CoeffField d} {g : Vec d → ℝ}
    {u : H1Function U} (h : IsScalarForcedWeakSolution a U g u) :
    IsWeakSolutionOn a U u g (fun _ => 0) := by
  intro φ
  have := h.2 φ
  simp only [vecDot, Pi.zero_apply, zero_mul, Finset.sum_const_zero, integral_zero, add_zero]
  exact this

/-- An almost-everywhere bound bounds the `L^∞` seminorm. -/
theorem dtExp_eLpNorm_top_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ} {C : ℝ}
    (hm : AEStronglyMeasurable f μ) (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    eLpNorm f ⊤ μ ≤ ENNReal.ofReal C := by
  rw [eLpNorm_exponent_top hm]
  exact eLpNormEssSup_le_of_ae_bound h

/-- `½ Δ` of the dilate of `p`, as a divergence form with the constant coefficient `½ Id`. -/
theorem dtExp_divForm_hom_dilate {ε : ℝ} (hε : ε ≠ 0) {p : Vec d → ℝ} (hp : ContDiff ℝ 2 p)
    {κ : ℝ} (hlap : ∀ x, (1 / 2 : ℝ) * vecLaplacian p x = κ) (y : Vec d) :
    divForm 1 (fun _ => (1 / 2 : ℝ) • (1 : Mat d)) (fun y' => p (ε • y')) y = ε ^ 2 * κ := by
  have h := ballResc_divForm_comp_smul 1 hε (fun _ => (1 / 2 : ℝ) • (1 : Mat d)) p y
  have hdc : divForm 1 (fun _ => (1 / 2 : ℝ) • (1 : Mat d)) (fun y' => p (ε • y')) y =
      ε ^ 2 * divForm 1 (fun _ => (1 / 2 : ℝ) • (1 : Mat d)) p (ε • y) := h
  rw [hdc, divForm_const_smul_one _ p hp, hlap]

/-- **The error engine.** -/
theorem dtExp_engine [NeZero d] {cStar : ℝ} {omega : ShellSeq d}
    (D : FieldInputData d nu (fullStreamRecentered omega))
    (hDa : D.analyticData.a = fullCoefficientRecentered nu omega)
    (ha : ∀ i j, ContDiff ℝ 1 fun y => fullCoefficientRecentered nu omega y i j)
    {ε : ℝ} (hε : 0 < ε) (hs : 0 < opScale cStar ε) {E0 : ℝ} (hE0 : 0 ≤ E0)
    (hA : ∀ (f : Vec d → ℝ) (g u uhom : H1Function ((ε⁻¹)⁻¹ • euclideanBall (0 : Vec d) ε⁻¹)),
      IsDirichletSolution (fun x => opScale cStar ε • epField nu omega ε x) _ f g u →
      IsDirichletSolution (fun _ => (1 / 2 : ℝ) • (1 : Mat d)) _ f g uhom →
      eLpNorm (fun x => u.toFun x - uhom.toFun x) ⊤
          (volume.restrict ((ε⁻¹)⁻¹ • euclideanBall (0 : Vec d) ε⁻¹)) ≤
        ENNReal.ofReal E0 *
          (eLpNorm (fun x => eucNorm (g.grad x)) ⊤
              (volume.restrict ((ε⁻¹)⁻¹ • euclideanBall (0 : Vec d) ε⁻¹)) +
            eLpNorm f ⊤ (volume.restrict ((ε⁻¹)⁻¹ • euclideanBall (0 : Vec d) ε⁻¹))))
    {b : Vec d → ℝ} (hb : ContDiff ℝ 2 b) (hbc : HasCompactSupport b)
    {p : Vec d → ℝ} (hp : ContDiff ℝ 2 p) {κ G : ℝ}
    (hbp : ∀ y ∈ euclideanBall (0 : Vec d) ε⁻¹, b =ᶠ[𝓝 y] fun y' => p (ε • y'))
    (hlap : ∀ x, (1 / 2 : ℝ) * vecLaplacian p x = κ)
    (hGp : ∀ x, vecNormSq x < 1 → eucNorm (fun i => fderiv ℝ p x (basisVec i)) ≤ G) :
    ∃ (w τ : Vec d → ℝ), Continuous w ∧ Continuous τ ∧
      (∀ y, y ∉ euclideanBall (0 : Vec d) ε⁻¹ → w y = 0) ∧
      (∀ y, y ∉ euclideanBall (0 : Vec d) ε⁻¹ → τ y = 0) ∧ (∀ y, 0 ≤ τ y) ∧
      (∀ y ∈ closure (euclideanBall (0 : Vec d) ε⁻¹),
        |b y + w y - (κ * ε ^ 2 / opScale cStar ε) * τ y - p (ε • y)| ≤
          E0 * (G + |κ|)) ∧
      ∀ {Q : Vec d → Measure (ContinuousPath (Vec d))},
        IsContinuousPathLaw D.logGrowthBounds.resolvent.kernelSemigroup Q →
        ∀ (t : NNReal),
        ∫ path, (fun z => b z + w z - (κ * ε ^ 2 / opScale cStar ε) * τ z)
            (path (ContinuousPath.exitTimeTrunc (euclideanBall (0 : Vec d) ε⁻¹) t path)) ∂(Q 0) =
          (b 0 + w 0 - (κ * ε ^ 2 / opScale cStar ε) * τ 0) +
            (κ * ε ^ 2 / opScale cStar ε) *
              ∫ path, ((ContinuousPath.exitTimeTrunc (euclideanBall (0 : Vec d) ε⁻¹) t path :
                NNReal) : ℝ) ∂(Q 0) := by
  set σ : ℝ := κ * ε ^ 2 / opScale cStar ε with hσ
  have hRpos : 0 < ε⁻¹ := inv_pos.2 hε
  have hs' : ε⁻¹ ≠ 0 := hRpos.ne'
  have hV := SuperdiffusionCLT.Section8.Common.Regularity.Ported.isOpenBoundedConvexDomain_euclideanBall
    (0 : Vec d) hRpos
  obtain ⟨w, τ, g, v, hwc, hτc, hwoff, hτoff, hτ0, hsolB, hgf, hgg, hv, hstop⟩ :=
    dtExp_ball_solution D hDa ha hRpos hb hbc σ
  refine ⟨w, τ, hwc, hτc, hwoff, hτoff, hτ0, ?_, fun {Q} hQ t => hstop hQ t⟩
  -- the scaled solutions
  have hproc := dtExp_dilate_dirichlet nu cStar omega hε hsolB
  have hf' : (fun x : Vec d => opScale cStar ε * (ε⁻¹ ^ 2 * (fun _ : Vec d => -σ) (ε⁻¹ • x))) =
      fun _ => -κ := by
    funext x
    simp only [hσ]
    field_simp
  rw [hf'] at hproc
  set U : Set (Vec d) := (ε⁻¹)⁻¹ • euclideanBall (0 : Vec d) ε⁻¹ with hU
  have hUo : IsOpen U := hV.isOpen.smul₀ (by simpa using hε.ne')
  have hmem : ∀ x, x ∈ U ↔ ε⁻¹ • x ∈ euclideanBall (0 : Vec d) ε⁻¹ := by
    intro x
    rw [hU, Set.mem_smul_set_iff_inv_smul_mem₀ (by simpa using hε.ne')]
    simp
  -- the homogeneous side
  have hca : ∀ i j, ContDiff ℝ 1 fun _ : Vec d => ((1 / 2 : ℝ) • (1 : Mat d)) i j :=
    fun i j => contDiff_const
  have hforced := domId_weak_of_classical hV (a := fun _ : Vec d => (1 / 2 : ℝ) • (1 : Mat d))
    hca (hb.of_le (by norm_num))
  have hforced' := dtExp_forced_congr_grad (u₂ := g) (by funext x; exact (hgg x).symm) hforced
  have hweak := dtExp_weak_of_forced hforced'
  have hdil := IsWeakSolutionOn.dilate hs' hweak
  have hhom : IsWeakSolutionOn (fun _ => (1 / 2 : ℝ) • (1 : Mat d)) U
      (g.dilateArg hs') (fun _ => -κ) (fun _ => 0) := by
    have h1 : IsWeakSolutionOn (fun _ => (1 / 2 : ℝ) • (1 : Mat d)) U (g.dilateArg hs')
        (fun y => ε⁻¹ ^ 2 * -divForm 1 (fun _ : Vec d => (1 / 2 : ℝ) • (1 : Mat d)) b (ε⁻¹ • y))
        (fun _ => 0) :=
      rc_isWeakSolutionOn_congr (g' := fun _ => 0) (fun y => rfl) (fun y => rfl)
        (fun y => by simp) hdil
    refine dtExp_weak_congr_forcing hUo.measurableSet (fun x hx => ?_) h1
    have hy := (hmem x).1 hx
    have e1 : divForm 1 (fun _ : Vec d => (1 / 2 : ℝ) • (1 : Mat d)) b (ε⁻¹ • x) =
        ε ^ 2 * κ := by
      rw [divForm_congr_of_eventuallyEq 1 (a' := fun _ : Vec d => (1 / 2 : ℝ) • (1 : Mat d))
        (u' := fun y' => p (ε • y')) Filter.EventuallyEq.rfl (hbp _ hy)]
      exact dtExp_divForm_hom_dilate hε.ne' hp hlap _
    show ε⁻¹ ^ 2 * -divForm 1 (fun _ : Vec d => (1 / 2 : ℝ) • (1 : Mat d)) b (ε⁻¹ • x) = -κ
    rw [e1]
    field_simp
  have hhomD : IsDirichletSolution (fun _ => (1 / 2 : ℝ) • (1 : Mat d)) U (fun _ => -κ)
      (g.dilateArg hs') (g.dilateArg hs') := by
    refine ⟨hhom, ?_⟩
    have : (fun x => (g.dilateArg hs').toFun x - (g.dilateArg hs').toFun x) = 0 := by
      funext x; simp
    rw [this]
    exact memH10_zero
  have hbound := hA (fun _ => -κ) (g.dilateArg hs') (v.dilateArg hs') (g.dilateArg hs') hproc hhomD
  -- the gradient of the trace
  have hgrad : ∀ᵐ x ∂(volume.restrict U), ‖eucNorm ((g.dilateArg hs').grad x)‖ ≤ G := by
    rw [ae_restrict_iff' hUo.measurableSet]
    refine Filter.Eventually.of_forall fun x hx => ?_
    have hy := (hmem x).1 hx
    have h1 : (g.dilateArg hs').grad x = fun i => fderiv ℝ p x (basisVec i) := by
      rw [H1Function.dilateArg_grad, hgg]
      have h2 : fderiv ℝ b (ε⁻¹ • x) = ε • fderiv ℝ p x := by
        rw [(hbp _ hy).fderiv_eq, ballResc_fderiv_comp_smul hε.ne']
        simp [smul_smul, hε.ne']
      funext i
      simp [h2]
      field_simp
    have h3 : 0 ≤ eucNorm ((g.dilateArg hs').grad x) := Real.sqrt_nonneg _
    rw [Real.norm_of_nonneg h3, h1]
    have hx1 : vecNormSq x < 1 := by
      have hU1 : U = euclideanBall (0 : Vec d) 1 := exitEst_ball_dilate hε
      rw [hU1] at hx
      simpa [euclideanBall, euclideanSqDist] using hx
    exact hGp x hx1
  have hG0 : 0 ≤ G := le_trans (Real.sqrt_nonneg _) (hGp 0 (by simp [vecNormSq, vecDot]))
  have hgm : AEStronglyMeasurable (fun x => eucNorm ((g.dilateArg hs').grad x))
      (volume.restrict U) := by
    have hc : Continuous fun x : Vec d => eucNorm ((g.dilateArg hs').grad x) := by
      have hfd : Continuous fun z : Vec d => fderiv ℝ b z := hb.continuous_fderiv (by norm_num)
      have : (fun x : Vec d => eucNorm ((g.dilateArg hs').grad x)) = fun x =>
          Real.sqrt (∑ i, (ε⁻¹ * fderiv ℝ b (ε⁻¹ • x) (basisVec i)) *
            (ε⁻¹ * fderiv ℝ b (ε⁻¹ • x) (basisVec i))) := by
        funext x
        simp only [eucNorm, vecNormSq, vecDot, H1Function.dilateArg_grad, hgg, Pi.smul_apply,
          smul_eq_mul]
      rw [this]
      refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => ?_)
      have h1 : Continuous fun x : Vec d => ε⁻¹ * fderiv ℝ b (ε⁻¹ • x) (basisVec i) :=
        continuous_const.mul ((hfd.comp (continuous_const_smul ε⁻¹)).clm_apply continuous_const)
      exact h1.mul h1
    exact hc.aestronglyMeasurable
  have hgn : eLpNorm (fun x => eucNorm ((g.dilateArg hs').grad x)) ⊤ (volume.restrict U) ≤
      ENNReal.ofReal G := by
    exact dtExp_eLpNorm_top_le hgm hgrad
  have hfn : eLpNorm (fun _ : Vec d => -κ) ⊤ (volume.restrict U) ≤ ENNReal.ofReal |κ| := by
    exact dtExp_eLpNorm_top_le aestronglyMeasurable_const (Filter.Eventually.of_forall fun x => by simp)
  have hfin : eLpNorm (fun x => (v.dilateArg hs').toFun x - (g.dilateArg hs').toFun x) ⊤
      (volume.restrict U) ≤ ENNReal.ofReal (E0 * (G + |κ|)) := by
    refine hbound.trans ?_
    rw [ENNReal.ofReal_mul hE0, ENNReal.ofReal_add hG0 (abs_nonneg _)]
    exact mul_le_mul_right (add_le_add hgn hfn) _
  have hae := resEst_ae_abs_le (U := U) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hfin)
  have hle := ENNReal.toReal_mono ENNReal.ofReal_ne_top hfin
  rw [ENNReal.toReal_ofReal (mul_nonneg hE0 (add_nonneg hG0 (abs_nonneg _)))] at hle
  have hvae := exitEst_ae_dilate hs' (euclideanBall (0 : Vec d) ε⁻¹) hv
  have hcont : Continuous fun x : Vec d =>
      |b (ε⁻¹ • x) + w (ε⁻¹ • x) - σ * τ (ε⁻¹ • x) - p x| := by
    have hbc' := hb.continuous
    exact (((hbc'.comp (continuous_const_smul ε⁻¹)).add (hwc.comp (continuous_const_smul ε⁻¹))).sub
      (continuous_const.mul (hτc.comp (continuous_const_smul ε⁻¹))) |>.sub hp.continuous).abs
  have hU : ∀ x ∈ U, |b (ε⁻¹ • x) + w (ε⁻¹ • x) - σ * τ (ε⁻¹ • x) - p x| ≤
      E0 * (G + |κ|) := by
    refine le_of_ae_le_of_continuousOn hUo hcont.continuousOn continuousOn_const ?_
    filter_upwards [hae, hvae, ae_restrict_mem hUo.measurableSet] with x h1 h2 hx
    have hy := (hmem x).1 hx
    have h3 : (v.dilateArg hs').toFun x = b (ε⁻¹ • x) + w (ε⁻¹ • x) - σ * τ (ε⁻¹ • x) := by
      rw [H1Function.dilateArg_toFun]; exact h2
    have h4 : (g.dilateArg hs').toFun x = p x := by
      rw [H1Function.dilateArg_toFun, hgf, (hbp _ hy).eq_of_nhds]
      simp [smul_smul, hε.ne']
    rw [h3, h4] at h1
    exact h1.trans hle
  have hclosed : IsClosed {y : Vec d | |b y + w y - σ * τ y - p (ε • y)| ≤ E0 * (G + |κ|)} :=
    isClosed_le ((((hb.continuous.add hwc).sub (continuous_const.mul hτc)).sub
      (hp.continuous.comp (continuous_const_smul ε))).abs) continuous_const
  intro y hy
  refine closure_minimal (fun y' hy' => ?_) hclosed hy
  have hx : ε • y' ∈ U := by
    rw [hmem]; simpa [smul_smul, hε.ne'] using hy'
  have := hU _ hx
  simpa [smul_smul, hε.ne'] using this

end SuperdiffusionCLT.Section8
