/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Root.DtExpD

/-!
# The stopped first and second moments on a ball

From the error engine: for the stopped position `Y = X_{t ∧ T}` of the ball of radius `ε⁻¹`,

* `|E[e · Y]| ≤ 2 E₀ ε⁻¹` for every unit vector `e`;
* `|(ε²/d) E|Y|² - (ε² / opScale) E[t ∧ T]| ≤ 2 E₀ (2/d + 1)`.
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

variable {d : ℕ} [NeZero d] {nu : ℝ}

omit [NeZero d] in
/-- The closure of the Euclidean ball lies in the closed Euclidean ball. -/
theorem dtExp_closure_le {R : ℝ} {y : Vec d} (hy : y ∈ closure (euclideanBall (0 : Vec d) R)) :
    vecNormSq y ≤ R ^ 2 := by
  have hc : IsClosed {z : Vec d | vecNormSq z ≤ R ^ 2} := by
    refine isClosed_le ?_ continuous_const
    unfold vecNormSq vecDot
    exact continuous_finsetSum _ fun i _ => (continuous_apply i).mul (continuous_apply i)
  refine closure_minimal (fun z hz => ?_) hc hy
  simp only [euclideanBall, euclideanSqDist, sub_zero, Set.mem_ofPred_eq] at hz
  exact hz.le

omit [NeZero d] in
/-- The stopped position is measurable, and lies in the closure of the ball. -/
theorem dtExp_stopped_mem {S : SubMarkovKernelSemigroup (Vec d)}
    {Q : Vec d → Measure (ContinuousPath (Vec d))} (hQ : IsContinuousPathLaw S Q) {R : ℝ}
    (hR : 0 < R) (t : NNReal) :
    Measurable (fun path : ContinuousPath (Vec d) =>
      path (ContinuousPath.exitTimeTrunc (euclideanBall (0 : Vec d) R) t path)) ∧
    ∀ᵐ path ∂(Q 0), path (ContinuousPath.exitTimeTrunc (euclideanBall (0 : Vec d) R) t path) ∈
      closure (euclideanBall (0 : Vec d) R) := by
  have hV := SuperdiffusionCLT.Section8.Common.Regularity.Ported.isOpenBoundedConvexDomain_euclideanBall
    (0 : Vec d) hR
  refine ⟨ContinuousPath.measurable_eval_stoppingTime_borel _
    (ContinuousPath.isStoppingTime_exitTimeTrunc _ hV.isOpen t), ?_⟩
  filter_upwards [dtExp_ae_start hQ 0] with path h0
  refine ContinuousPath.stopped_exitTimeTrunc_mem_closure _ hV.isOpen t path ?_
  rw [h0]
  simp only [euclideanBall, euclideanSqDist, sub_zero, Set.mem_ofPred_eq]
  simpa [vecNormSq, vecDot] using pow_pos hR 2

/-- **The stopped first moment.** -/
theorem dtExp_first_moment {cStar : ℝ} {omega : ShellSeq d}
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
    (e : Vec d) (he : vecNormSq e = 1)
    {Q : Vec d → Measure (ContinuousPath (Vec d))}
    (hQ : IsContinuousPathLaw D.logGrowthBounds.resolvent.kernelSemigroup Q) (t : NNReal) :
    |∫ path, vecDot e (path (ContinuousPath.exitTimeTrunc (euclideanBall (0 : Vec d) ε⁻¹) t path))
        ∂(Q 0)| ≤ 2 * E0 * ε⁻¹ := by
  have hRpos : 0 < ε⁻¹ := inv_pos.2 hε
  obtain ⟨χ, hχ, hχc, hχ1⟩ := dtExp_bump (d := d) hRpos
  set b : Vec d → ℝ := fun y => ε * (χ y * vecDot e y) with hb
  have hbd : ContDiff ℝ 2 b := contDiff_const.mul (hχ.mul (dtExp_contDiff_lin e))
  have hbc : HasCompactSupport b := by
    have h1 : HasCompactSupport (χ * fun y => vecDot e y) := hχc.mul_right
    exact h1.mul_left (f := fun _ => ε)
  have hsm : ∀ z : Vec d, vecDot e (ε • z) = ε * vecDot e z := by
    intro z
    simp [vecDot, Finset.mul_sum, mul_left_comm]
  have hbp : ∀ y ∈ euclideanBall (0 : Vec d) ε⁻¹,
      b =ᶠ[nhds y] fun y' => vecDot e (ε • y') := by
    intro y hy
    filter_upwards [hχ1 y hy] with z hz
    simp only [hb, hz, hsm, one_mul]
  have hlap : ∀ x : Vec d, (1 / 2 : ℝ) * vecLaplacian (fun y => vecDot e y) x = 0 := by
    intro x; rw [dtExp_vecLaplacian_lin]; simp
  have hGp : ∀ x : Vec d, vecNormSq x < 1 →
      eucNorm (fun i => fderiv ℝ (fun y => vecDot e y) x (basisVec i)) ≤ 1 := by
    intro x _
    have : (fun i => fderiv ℝ (fun y => vecDot e y) x (basisVec i)) = e :=
      funext (dtExp_fderiv_lin_basis e x)
    rw [this]
    unfold eucNorm
    rw [he]; simp
  obtain ⟨w, τ, hwc, hτc, -, -, -, hsup, hstop⟩ := dtExp_engine D hDa ha hε hs hE0 hA hbd hbc
    (dtExp_contDiff_lin e) hbp hlap hGp
  have hV := SuperdiffusionCLT.Section8.Common.Regularity.Ported.isOpenBoundedConvexDomain_euclideanBall
    (0 : Vec d) hRpos
  have : IsProbabilityMeasure (Q 0) := (hQ 0).1
  obtain ⟨hYm, hYK⟩ := dtExp_stopped_mem hQ hRpos t
  have hΦc : Continuous fun y => b y + w y - (0 * ε ^ 2 / opScale cStar ε) * τ y :=
    (hbd.continuous.add hwc).sub (continuous_const.mul hτc)
  have hPc : Continuous fun y : Vec d => vecDot e (ε • y) := by
    unfold vecDot
    exact continuous_finsetSum _ fun i _ =>
      continuous_const.mul (continuous_const.mul (continuous_apply i))
  have hM : ∀ y ∈ closure (euclideanBall (0 : Vec d) ε⁻¹), |vecDot e (ε • y)| ≤ 1 := by
    intro y hy
    have h1 := dtExp_closure_le hy
    have h2 := sq_vecDot_le_vecNormSq_mul_vecNormSq e (ε • y)
    rw [he, one_mul, vecNormSq_smul] at h2
    have h3 : ε ^ 2 * vecNormSq y ≤ 1 := by
      calc ε ^ 2 * vecNormSq y ≤ ε ^ 2 * (ε⁻¹) ^ 2 := by gcongr
        _ = 1 := by field_simp
    exact abs_le_of_sq_le_sq (by linarith only [h2, h3]) zero_le_one
  have happ := dtExp_integral_approx (μ := Q 0) hYm hYK hΦc hPc
    (fun y hy => by simpa using hsup y hy) hM
  have hid := hstop hQ t
  have h00 : (0 : Vec d) ∈ closure (euclideanBall (0 : Vec d) ε⁻¹) := subset_closure (by
    simp only [euclideanBall, euclideanSqDist, sub_zero, Set.mem_ofPred_eq]
    simpa [vecNormSq, vecDot] using pow_pos hRpos 2)
  have h0 := hsup 0 h00
  have hP0 : vecDot e (ε • (0 : Vec d)) = 0 := by simp [vecDot]
  rw [hP0] at h0
  simp only [zero_mul, zero_div, sub_zero, add_zero, abs_zero] at hid h0 happ
  rw [hid] at happ
  have hint : ∫ x, vecDot e (ε • (fun path : ContinuousPath (Vec d) =>
      path (ContinuousPath.exitTimeTrunc (euclideanBall (0 : Vec d) ε⁻¹) t path)) x) ∂(Q 0) =
      ε * ∫ path, vecDot e (path (ContinuousPath.exitTimeTrunc (euclideanBall (0 : Vec d) ε⁻¹) t
        path)) ∂(Q 0) := by
    simp_rw [hsm]
    exact integral_const_mul _ _
  have hI : |ε * ∫ path, vecDot e (path (ContinuousPath.exitTimeTrunc (euclideanBall (0 : Vec d)
      ε⁻¹) t path)) ∂(Q 0)| ≤ 2 * E0 := by
    rw [← hint]
    have h3 := abs_sub_abs_le_abs_sub (∫ x : ContinuousPath (Vec d),
      vecDot e (ε • x (ContinuousPath.exitTimeTrunc (euclideanBall 0 ε⁻¹) t x)) ∂Q 0) (b 0 + w 0)
    rw [abs_sub_comm] at h3
    linarith only [h3, h0, happ]
  rw [abs_mul, abs_of_pos hε] at hI
  have : |∫ path, vecDot e (path (ContinuousPath.exitTimeTrunc (euclideanBall (0 : Vec d) ε⁻¹) t
      path)) ∂(Q 0)| ≤ 2 * E0 / ε := by
    rw [le_div_iff₀ hε]; linarith only [hI]
  simpa [div_eq_mul_inv] using this

omit [NeZero d] in
/-- Triangle inequality in the form used for the second moment. -/
theorem dtExp_abs_two {A B E : ℝ} (hA : |A| ≤ E) (hAB : |A + B| ≤ E) : |B| ≤ 2 * E := by
  have h1 := abs_le.1 hA
  have h2 := abs_le.1 hAB
  rw [abs_le]
  constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2]

/-- **The stopped second moment.**  With `σ = ε² / opScale`, the stopped position `Y` of the ball
of radius `ε⁻¹` satisfies `|(ε²/d) E|Y|² - σ E[t ∧ T]| ≤ 2 E₀ (2/d + 1)`. -/
theorem dtExp_second_moment {cStar : ℝ} {omega : ShellSeq d}
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
    {Q : Vec d → Measure (ContinuousPath (Vec d))}
    (hQ : IsContinuousPathLaw D.logGrowthBounds.resolvent.kernelSemigroup Q) (t : NNReal) :
    |ε ^ 2 / d * ∫ path, vecNormSq (path (ContinuousPath.exitTimeTrunc
        (euclideanBall (0 : Vec d) ε⁻¹) t path)) ∂(Q 0) -
      ε ^ 2 / opScale cStar ε * ∫ path, ((ContinuousPath.exitTimeTrunc
        (euclideanBall (0 : Vec d) ε⁻¹) t path : NNReal) : ℝ) ∂(Q 0)| ≤
      2 * (E0 * (2 / d + 1)) := by
  have hRpos : 0 < ε⁻¹ := inv_pos.2 hε
  have hd0 : (0 : ℝ) < d := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne d))
  obtain ⟨χ, hχ, hχc, hχ1⟩ := dtExp_bump (d := d) hRpos
  set b : Vec d → ℝ := fun y => χ y * (ε ^ 2 / d * vecNormSq y) with hb
  have hq : ContDiff ℝ 2 (fun y : Vec d => (ε ^ 2 / d) * vecNormSq y) := dtExp_contDiff_quad _
  have hbd : ContDiff ℝ 2 b := hχ.mul hq
  have hbc : HasCompactSupport b := hχc.mul_right
  have hsm : ∀ z : Vec d, (1 / (d : ℝ)) * vecNormSq (ε • z) = ε ^ 2 / d * vecNormSq z := by
    intro z; rw [vecNormSq_smul]; ring
  have hbp : ∀ y ∈ euclideanBall (0 : Vec d) ε⁻¹,
      b =ᶠ[nhds y] fun y' => (fun x : Vec d => (1 / (d : ℝ)) * vecNormSq x) (ε • y') := by
    intro y hy
    filter_upwards [hχ1 y hy] with z hz
    simp only [hb, hz, hsm, one_mul]
  have hp : ContDiff ℝ 2 (fun x : Vec d => (1 / (d : ℝ)) * vecNormSq x) := dtExp_contDiff_quad _
  have hlap : ∀ x : Vec d, (1 / 2 : ℝ) * vecLaplacian
      (fun x : Vec d => (1 / (d : ℝ)) * vecNormSq x) x = 1 := by
    intro x; rw [dtExp_vecLaplacian_quad]; field_simp
  have hGp : ∀ x : Vec d, vecNormSq x < 1 →
      eucNorm (fun i => fderiv ℝ (fun x : Vec d => (1 / (d : ℝ)) * vecNormSq x) x (basisVec i)) ≤
        2 / d := by
    intro x hx
    have : (fun i => fderiv ℝ (fun x : Vec d => (1 / (d : ℝ)) * vecNormSq x) x (basisVec i)) =
        (2 / (d : ℝ)) • x := by
      funext i
      rw [dtExp_fderiv_quad_basis]; simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [this]
    unfold eucNorm
    rw [vecNormSq_smul]
    calc Real.sqrt ((2 / (d : ℝ)) ^ 2 * vecNormSq x) ≤ Real.sqrt ((2 / (d : ℝ)) ^ 2 * 1) :=
          Real.sqrt_le_sqrt (by gcongr)
      _ = 2 / d := by rw [mul_one, Real.sqrt_sq (by positivity)]
  obtain ⟨w, τ, hwc, hτc, -, -, -, hsup, hstop⟩ := dtExp_engine D hDa ha hε hs hE0 hA hbd hbc
    hp hbp hlap hGp
  have hV := SuperdiffusionCLT.Section8.Common.Regularity.Ported.isOpenBoundedConvexDomain_euclideanBall
    (0 : Vec d) hRpos
  have : IsProbabilityMeasure (Q 0) := (hQ 0).1
  obtain ⟨hYm, hYK⟩ := dtExp_stopped_mem hQ hRpos t
  set σ : ℝ := 1 * ε ^ 2 / opScale cStar ε with hσ
  have hΦc : Continuous fun y => b y + w y - σ * τ y :=
    (hbd.continuous.add hwc).sub (continuous_const.mul hτc)
  have hPc : Continuous fun y : Vec d => (1 / (d : ℝ)) * vecNormSq (ε • y) := by
    unfold vecNormSq vecDot
    exact continuous_const.mul (continuous_finsetSum _ fun i _ =>
      (continuous_const.mul (continuous_apply i)).mul (continuous_const.mul (continuous_apply i)))
  have hM : ∀ y ∈ closure (euclideanBall (0 : Vec d) ε⁻¹),
      |(1 / (d : ℝ)) * vecNormSq (ε • y)| ≤ 1 := by
    intro y hy
    have h1 := dtExp_closure_le hy
    have h3 : ε ^ 2 * vecNormSq y ≤ 1 := by
      calc ε ^ 2 * vecNormSq y ≤ ε ^ 2 * (ε⁻¹) ^ 2 := by gcongr
        _ = 1 := by field_simp
    have h4 : 0 ≤ vecNormSq y := by unfold vecNormSq vecDot; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    rw [vecNormSq_smul, abs_of_nonneg (by positivity)]
    have h5 : 1 ≤ (d : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
    calc 1 / (d : ℝ) * (ε ^ 2 * vecNormSq y) ≤ 1 / (d : ℝ) * 1 := by gcongr
      _ ≤ 1 := by rw [mul_one, div_le_one hd0]; exact h5
  have happ := dtExp_integral_approx (μ := Q 0) hYm hYK hΦc hPc
    (fun y hy => hsup y hy) hM
  have hid := hstop hQ t
  have h00 : (0 : Vec d) ∈ closure (euclideanBall (0 : Vec d) ε⁻¹) := subset_closure (by
    simp only [euclideanBall, euclideanSqDist, sub_zero, Set.mem_ofPred_eq]
    simpa [vecNormSq, vecDot] using pow_pos hRpos 2)
  have h0 := hsup 0 h00
  have hP0 : (1 / (d : ℝ)) * vecNormSq (ε • (0 : Vec d)) = 0 := by simp [vecNormSq, vecDot]
  rw [hP0, sub_zero] at h0
  have hint : ∫ x, (1 / (d : ℝ)) * vecNormSq (ε • (fun path : ContinuousPath (Vec d) =>
      path (ContinuousPath.exitTimeTrunc (euclideanBall (0 : Vec d) ε⁻¹) t path)) x) ∂(Q 0) =
      ε ^ 2 / d * ∫ path, vecNormSq (path (ContinuousPath.exitTimeTrunc
        (euclideanBall (0 : Vec d) ε⁻¹) t path)) ∂(Q 0) := by
    simp_rw [hsm]
    exact integral_const_mul _ _
  rw [hint] at happ
  have hid2 : ∫ x : ContinuousPath (Vec d), (b (x (ContinuousPath.exitTimeTrunc
      (euclideanBall (0 : Vec d) ε⁻¹) t x)) + w (x (ContinuousPath.exitTimeTrunc
      (euclideanBall (0 : Vec d) ε⁻¹) t x)) - σ * τ (x (ContinuousPath.exitTimeTrunc
      (euclideanBall (0 : Vec d) ε⁻¹) t x))) ∂(Q 0) = b 0 + w 0 - σ * τ 0 + σ * ∫ path,
        ((ContinuousPath.exitTimeTrunc (euclideanBall (0 : Vec d) ε⁻¹) t path : NNReal) : ℝ)
          ∂(Q 0) := hid
  rw [hid2, abs_one] at happ
  rw [abs_one] at h0
  have h5 := dtExp_abs_two (E := E0 * (2 / d + 1)) h0 (by
    have : b 0 + w 0 - σ * τ 0 + σ * ∫ path, ((ContinuousPath.exitTimeTrunc
        (euclideanBall (0 : Vec d) ε⁻¹) t path : NNReal) : ℝ) ∂(Q 0) -
        ε ^ 2 / d * ∫ path, vecNormSq (path (ContinuousPath.exitTimeTrunc
          (euclideanBall (0 : Vec d) ε⁻¹) t path)) ∂(Q 0) =
        (b 0 + w 0 - σ * τ 0) + (σ * ∫ path, ((ContinuousPath.exitTimeTrunc
          (euclideanBall (0 : Vec d) ε⁻¹) t path : NNReal) : ℝ) ∂(Q 0) -
        ε ^ 2 / d * ∫ path, vecNormSq (path (ContinuousPath.exitTimeTrunc
          (euclideanBall (0 : Vec d) ε⁻¹) t path)) ∂(Q 0)) := by ring
    rw [← this]; exact happ)
  have e1 : ε ^ 2 / d * ∫ path, vecNormSq (path (ContinuousPath.exitTimeTrunc
      (euclideanBall (0 : Vec d) ε⁻¹) t path)) ∂(Q 0) - ε ^ 2 / opScale cStar ε *
      ∫ path, ((ContinuousPath.exitTimeTrunc (euclideanBall (0 : Vec d) ε⁻¹) t path : NNReal) : ℝ)
        ∂(Q 0) = -(σ * ∫ path, ((ContinuousPath.exitTimeTrunc (euclideanBall (0 : Vec d) ε⁻¹) t
          path : NNReal) : ℝ) ∂(Q 0) - ε ^ 2 / d * ∫ path, vecNormSq (path
            (ContinuousPath.exitTimeTrunc (euclideanBall (0 : Vec d) ε⁻¹) t path)) ∂(Q 0)) := by
    rw [hσ]; ring
  rw [e1, abs_neg]
  exact h5

end SuperdiffusionCLT.Section8
