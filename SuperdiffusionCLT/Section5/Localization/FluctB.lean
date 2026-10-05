/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Localization.Fluct
public import SuperdiffusionCLT.Section5.Localization.IdentitiesB
public import SuperdiffusionCLT.Section5.Localization.CrudeSz
public import SuperdiffusionCLT.Section2.Annealed.Integrability
public import SuperdiffusionCLT.Section3.Setup.WholeSpaceEnergyD
public import SuperdiffusionCLT.Section2.Estimates.Stream.ShellHminusEndpointOrderOneC

/-!
# The energy of the fluctuation `F_z` against the block coefficient

Pointwise in `(ω, z)`: `⟪F_z, F_z⟫ = ⨍_Q F · A_m F` is bounded through the pointwise quadratic bound
`(p,q)·A_m(p,q) ≤ (ν + 2ν⁻¹|k_m|²)|p|² + 2ν⁻¹|q|²` by Young's inequality, in terms of the fourth
moments `⨍_Q |k_m|⁴`, `‖g_D'‖⁴_{L̲⁴(Q)}`, `‖g_N'‖⁴_{L̲⁴(Q)}` of the fields.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open MeasureTheory Homogenization SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Frozen.Section2 SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section3.ResponseFields
open scoped ENNReal

variable {d : ℕ}

theorem loc_ofReal_integral_le_lintegral {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {h : α → ℝ} (hi : Integrable h ν) :
    ENNReal.ofReal (∫ x, h x ∂ν) ≤ ∫⁻ x, ENNReal.ofReal (h x) ∂ν := by
  have hp : Integrable (fun x => max (h x) 0) ν := hi.pos_part
  have h1 : ∫ x, h x ∂ν ≤ ∫ x, max (h x) 0 ∂ν :=
    integral_mono hi hp fun x => le_max_left _ _
  have h2 := ofReal_integral_eq_lintegral_ofReal hp
    (Filter.Eventually.of_forall fun x => le_max_right _ _)
  refine (ENNReal.ofReal_le_ofReal h1).trans (h2.le.trans (lintegral_mono fun x => ?_))
  rw [ENNReal.ofReal_max, ENNReal.ofReal_zero]
  exact max_le le_rfl bot_le

theorem loc_volumeAverage_cubeSet_eq (Q : TriadicCube d) (f : Vec d → ℝ) :
    volumeAverage (cubeSet Q) f = ∫ x, f x ∂normalizedCubeMeasure Q := by
  rw [SuperdiffusionCLT.Section3.Setup.integral_normalizedCubeMeasure_eq_volumeAverage]
  unfold volumeAverage
  rw [volume_cubeSet_toReal, volume_openCubeSet_toReal,
    MeasureTheory.setIntegral_congr_set (cubeSet_ae_eq_openCubeSet Q)]

theorem loc_integrable_normalized_of_integrableOn (Q : TriadicCube d) {f : Vec d → ℝ}
    (hf : IntegrableOn f (cubeSet Q)) : Integrable f (normalizedCubeMeasure Q) := by
  rw [SuperdiffusionCLT.Section2.Estimates.Stream.normalizedCubeMeasure_eq_smul_volume_restrict_cubeSet]
  exact hf.smul_measure ENNReal.ofReal_ne_top

/-- `ofReal` of a cube average is at most the lintegral against the normalized cube measure. -/
theorem loc_ofReal_volumeAverage_le_lintegral (Q : TriadicCube d) {f : Vec d → ℝ}
    (hf : IntegrableOn f (cubeSet Q)) :
    ENNReal.ofReal (volumeAverage (cubeSet Q) f) ≤
      ∫⁻ x, ENNReal.ofReal (f x) ∂normalizedCubeMeasure Q := by
  rw [loc_volumeAverage_cubeSet_eq]
  exact loc_ofReal_integral_le_lintegral (loc_integrable_normalized_of_integrableOn Q hf)

/-- The Young splitting of the pointwise majorant, in `ℝ≥0∞`. -/
theorem loc_maj_le {a b c u κ v : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hu : 0 ≤ u)
    (hκ : 0 ≤ κ) (hv : 0 ≤ v) {c1 c1' c2 c2' c3 c3' : ℝ≥0∞} (h1 : c1 * c1' = 1)
    (h2 : c2 * c2' = 1) (h3 : c3 * c3' = 1) :
    ENNReal.ofReal (a * u + 2 * b * (κ * u) + 2 * c * v) ≤
      ENNReal.ofReal a * (c2 + c2' * ENNReal.ofReal u ^ 2) +
        ENNReal.ofReal b * (c1 * ENNReal.ofReal κ ^ 2 + c1' * ENNReal.ofReal u ^ 2) +
        ENNReal.ofReal c * (c3 + c3' * ENNReal.ofReal v ^ 2) := by
  have y1 := ennreal_young h1 (ENNReal.ofReal κ) (ENNReal.ofReal u)
  have y2 := ennreal_young h2 1 (ENNReal.ofReal u)
  have y3 := ennreal_young h3 1 (ENNReal.ofReal v)
  have hU : ENNReal.ofReal u ≤ 2 * (1 * ENNReal.ofReal u) := by
    rw [one_mul]
    calc ENNReal.ofReal u = 1 * ENNReal.ofReal u := (one_mul _).symm
      _ ≤ 2 * ENNReal.ofReal u := mul_le_mul' (by norm_num) le_rfl
  have e2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  have t1 : ENNReal.ofReal (a * u) = ENNReal.ofReal a * ENNReal.ofReal u := ENNReal.ofReal_mul ha
  have t2 : ENNReal.ofReal (2 * b * (κ * u)) =
      ENNReal.ofReal b * (2 * (ENNReal.ofReal κ * ENNReal.ofReal u)) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_mul hκ, ← e2]
    ring
  have t3 : ENNReal.ofReal (2 * c * v) =
      ENNReal.ofReal c * (2 * (1 * ENNReal.ofReal v)) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ← e2,
      one_mul]
    ring
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity), t1, t2, t3]
  refine add_le_add (add_le_add ?_ ?_) ?_
  · refine mul_le_mul' le_rfl (hU.trans (y2.trans ?_))
    simp
  · exact mul_le_mul' le_rfl y1
  · exact mul_le_mul' le_rfl (y3.trans (by simp))

theorem loc_lintegral_aff {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {U K V : α → ℝ≥0∞} (hU : AEMeasurable U μ) (hK : AEMeasurable K μ) (hV : AEMeasurable V μ)
    (a b c c1 c1' c2 c2' c3 c3' : ℝ≥0∞) :
    ∫⁻ x, (a * (c2 + c2' * U x) + b * (c1 * K x + c1' * U x) + c * (c3 + c3' * V x)) ∂μ =
      a * (c2 + c2' * ∫⁻ x, U x ∂μ) + b * (c1 * ∫⁻ x, K x ∂μ + c1' * ∫⁻ x, U x ∂μ) +
        c * (c3 + c3' * ∫⁻ x, V x ∂μ) := by
  have hA : AEMeasurable (fun x => a * (c2 + c2' * U x)) μ :=
    ((hU.const_mul c2').const_add c2).const_mul a
  have hB : AEMeasurable (fun x => b * (c1 * K x + c1' * U x)) μ :=
    (((hK.const_mul c1).add (hU.const_mul c1'))).const_mul b
  have hC : AEMeasurable (fun x => c * (c3 + c3' * V x)) μ :=
    ((hV.const_mul c3').const_add c3).const_mul c
  have h1 := lintegral_add_left' (μ := μ) (hA.add hB) (fun x => c * (c3 + c3' * V x))
  have h2 := lintegral_add_left' (μ := μ) hA (fun x => b * (c1 * K x + c1' * U x))
  simp only [Pi.add_apply] at h1 h2
  rw [h1, h2]
  have e0 : ∀ (k : ℝ≥0∞) (f : α → ℝ≥0∞), AEMeasurable f μ →
      ∫⁻ x, (k + f x) ∂μ = k + ∫⁻ x, f x ∂μ := by
    intro k f hf
    have := lintegral_add_left' (μ := μ) (aemeasurable_const (b := k)) f
    simpa only [lintegral_const, measure_univ, mul_one] using this
  have e1 : ∀ (a k k' : ℝ≥0∞) (f : α → ℝ≥0∞), AEMeasurable f μ →
      ∫⁻ x, a * (k + k' * f x) ∂μ = a * (k + k' * ∫⁻ x, f x ∂μ) := by
    intro a k k' f hf
    rw [lintegral_const_mul'' _ ((hf.const_mul k').const_add k), e0 _ _ (hf.const_mul k'),
      lintegral_const_mul'' _ hf]
  have e2 : ∫⁻ x, b * (c1 * K x + c1' * U x) ∂μ =
      b * (c1 * ∫⁻ x, K x ∂μ + c1' * ∫⁻ x, U x ∂μ) := by
    have hs : AEMeasurable (fun x => c1 * K x + c1' * U x) μ :=
      (hK.const_mul c1).add (hU.const_mul c1')
    rw [lintegral_const_mul'' b hs]
    congr 1
    have h3 := lintegral_add_left' (μ := μ) (hK.const_mul c1) (fun x => c1' * U x)
    rw [h3, lintegral_const_mul'' _ hK, lintegral_const_mul'' _ hU]
  rw [e1 a c2 c2' U hU, e2, e1 c c3 c3' V hV]

theorem loc_ofReal_vecNormSq_sq (G : Vec d → Vec d) (x : Vec d) :
    ENNReal.ofReal (vecNormSq (G x)) ^ 2 = ‖hilbertifyVecField G x‖ₑ ^ 4 := by
  rw [← ofReal_norm, norm_hilbertifyVecField_apply, ← ENNReal.ofReal_pow (vecNormSq_nonneg _),
    ← ENNReal.ofReal_pow (Book.Ch02.vecNorm_nonneg _), ← SuperdiffusionCLT.Section3.Setup.vecNorm_sq_eq_vecNormSq,
    ← pow_mul]

theorem loc_ofReal_sq_sq {r : ℝ} (hr : 0 ≤ r) : ENNReal.ofReal (r ^ 2) ^ 2 = ENNReal.ofReal r ^ 4 := by
  rw [ENNReal.ofReal_pow hr, ← pow_mul]

/-- The energy of the fluctuation `F_z` against `A_m`, by Young's inequality. -/
theorem loc_pairing_fluct_le [NeZero d] {nu : ℝ} (hnu : 0 < nu) (omega : ShellSeq d) (m : ℕ)
    (Q : TriadicCube d) {s : ℝ} (hs : 0 < s) {gD gN : Vec d → Vec d}
    (hD : MemVectorL2 (openCubeSet Q) gD) (hN : MemVectorL2 (openCubeSet Q) gN)
    {F : BlockState d} (hFp : ∀ x, F.potential x = s ^ (-(1 : ℝ) / 2) • gD x)
    (hFf : ∀ x, F.flux x = s ^ ((1 : ℝ) / 2) • gN x)
    {c1 c1' c2 c2' c3 c3' : ℝ≥0∞} (h1 : c1 * c1' = 1) (h2 : c2 * c2' = 1) (h3 : c3 * c3' = 1) :
    ENNReal.ofReal (blockPairingAverage (cubeSet Q) (coefficientCutoff nu omega m).toCoeffField F F) ≤
      ENNReal.ofReal (nu * s⁻¹) * (c2 + c2' * vecCubeLpENorm Q 4 gD ^ 4) +
        ENNReal.ofReal (nu⁻¹ * s⁻¹) * (c1 * locKFour m Q omega + c1' * vecCubeLpENorm Q 4 gD ^ 4) +
        ENNReal.ofReal (nu⁻¹ * s) * (c3 + c3' * vecCubeLpENorm Q 4 gN ^ 4) := by
  obtain ⟨lam, Lam, hEll⟩ := exists_isEllipticFieldOn_coefficientCutoff_cubeSet hnu omega m Q
  have hFpot : F.potential = fun x => s ^ (-(1 : ℝ) / 2) • gD x := funext hFp
  have hFflux : F.flux = fun x => s ^ ((1 : ℝ) / 2) • gN x := funext hFf
  have hL2 : IsBlockL2 (cubeSet Q) F := by
    refine ⟨?_, ?_⟩
    · rw [hFpot, memVectorL2_cubeSet_iff_openCubeSet]
      exact hD.const_smul (s ^ (-(1 : ℝ) / 2))
    · rw [hFflux, memVectorL2_cubeSet_iff_openCubeSet]
      exact hN.const_smul (s ^ ((1 : ℝ) / 2))
  have hI := hL2.integrableOn_pair hEll hL2
  have hprob : IsProbabilityMeasure (normalizedCubeMeasure Q) := ⟨normalizedCubeMeasure_apply_univ Q⟩
  refine (loc_ofReal_volumeAverage_le_lintegral Q hI).trans ?_
  have hpt : ∀ x, ENNReal.ofReal (blockPairingIntegrand (coefficientCutoff nu omega m).toCoeffField F F x) ≤
      ENNReal.ofReal (nu * s⁻¹) * (c2 + c2' * (‖hilbertifyVecField gD x‖ₑ ^ 4)) +
        ENNReal.ofReal (nu⁻¹ * s⁻¹) * (c1 * (ENNReal.ofReal (Book.Ch02.matrixOperatorNorm
          (streamCutoff omega m x)) ^ (4 : ℕ)) + c1' * (‖hilbertifyVecField gD x‖ₑ ^ 4)) +
        ENNReal.ofReal (nu⁻¹ * s) * (c3 + c3' * (‖hilbertifyVecField gN x‖ₑ ^ 4)) := by
    intro x
    have hq := blockQuadratic_coefficientCutoff_le hnu omega m x (F.potential x) (F.flux x)
    have hint : blockPairingIntegrand (coefficientCutoff nu omega m).toCoeffField F F x ≤
        nu * s⁻¹ * vecNormSq (gD x) + 2 * (nu⁻¹ * s⁻¹) *
          (Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ^ 2 * vecNormSq (gD x)) +
          2 * (nu⁻¹ * s) * vecNormSq (gN x) := by
      have e : blockPairingIntegrand (coefficientCutoff nu omega m).toCoeffField F F x =
          blockVecDot (F.potential x, F.flux x) (blockMatVecMul (blockMatrixOfCoeff
            ((coefficientCutoff nu omega m).toCoeffField x)) (F.potential x, F.flux x)) := rfl
      rw [e]
      refine hq.trans (le_of_eq ?_)
      rw [hFp, hFf, vecNormSq_smul, vecNormSq_smul, rpow_neg_half_sq hs, rpow_half_sq hs]
      ring
    have hk0 := Book.Ch02.matrixOperatorNorm_nonneg (streamCutoff omega m x)
    refine (ENNReal.ofReal_le_ofReal hint).trans ?_
    have hm := loc_maj_le (a := nu * s⁻¹) (b := nu⁻¹ * s⁻¹) (c := nu⁻¹ * s)
      (u := vecNormSq (gD x)) (κ := Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ^ 2)
      (v := vecNormSq (gN x)) (by positivity) (by positivity) (by positivity)
      (vecNormSq_nonneg _) (by positivity) (vecNormSq_nonneg _) h1 h2 h3
    refine hm.trans (le_of_eq ?_)
    rw [loc_ofReal_vecNormSq_sq gD x, loc_ofReal_vecNormSq_sq gN x, loc_ofReal_sq_sq hk0]
  have hmD := SuperdiffusionCLT.Section3.Terms.aestronglyMeasurable_hilbertifyVecField_of_memVectorL2 hD
  have hmN := SuperdiffusionCLT.Section3.Terms.aestronglyMeasurable_hilbertifyVecField_of_memVectorL2 hN
  have hUm : AEMeasurable (fun x => ‖hilbertifyVecField gD x‖ₑ ^ 4) (normalizedCubeMeasure Q) :=
    AEMeasurable.pow_const hmD.enorm 4
  have hVm : AEMeasurable (fun x => ‖hilbertifyVecField gN x‖ₑ ^ 4) (normalizedCubeMeasure Q) :=
    AEMeasurable.pow_const hmN.enorm 4
  have hKm : AEMeasurable (fun x => ENNReal.ofReal (Book.Ch02.matrixOperatorNorm
      (streamCutoff omega m x)) ^ (4 : ℕ)) (normalizedCubeMeasure Q) :=
    ((ENNReal.measurable_ofReal.comp (ShellField.continuous_matrixOperatorNorm.comp
      (continuous_streamCutoff_apply omega m)).measurable).pow_const 4).aemeasurable
  refine (lintegral_mono hpt).trans (le_of_eq ?_)
  rw [loc_lintegral_aff _ hUm hKm hVm, ← lintegral_enorm_pow_four_eq hD,
    ← lintegral_enorm_pow_four_eq hN]
  rfl

/-- The pointwise combination of the Young bound. -/
theorem loc_energy_combine {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) {θ : ℝ} (hθ : 0 < θ)
    (K D N : ℝ≥0∞) :
    ENNReal.ofReal a * (ENNReal.ofReal θ + ENNReal.ofReal θ⁻¹ * D) +
        ENNReal.ofReal b * (ENNReal.ofReal θ * K + ENNReal.ofReal θ⁻¹ * D) +
        ENNReal.ofReal c * (ENNReal.ofReal θ + ENNReal.ofReal θ⁻¹ * N) ≤
      ENNReal.ofReal ((a + c) * θ) + (ENNReal.ofReal (b * θ) * K +
        ENNReal.ofReal ((a + b + c) * θ⁻¹) * (D + N)) := by
  have hθ' : 0 ≤ θ⁻¹ := inv_nonneg.2 hθ.le
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add ha hc,
    ENNReal.ofReal_add (by positivity) hc, ENNReal.ofReal_add ha hb]
  set A := ENNReal.ofReal a
  set B := ENNReal.ofReal b
  set C := ENNReal.ofReal c
  set T := ENNReal.ofReal θ
  set T' := ENNReal.ofReal θ⁻¹
  have e : (A + B + C) * T' * (D + N) =
      (A * T' * D + B * T' * D + C * T' * D) + (A * T' * N + B * T' * N + C * T' * N) := by ring
  have k1 : A * T' * D + B * T' * D ≤ A * T' * D + B * T' * D + C * T' * D := le_self_add
  have k2 : C * T' * N ≤ A * T' * N + B * T' * N + C * T' * N := le_add_self
  calc _ = (A * T + C * T) + (B * T * K + (A * T' * D + B * T' * D + C * T' * N)) := by ring
    _ ≤ (A * T + C * T) + (B * T * K + ((A * T' * D + B * T' * D + C * T' * D) +
          (A * T' * N + B * T' * N + C * T' * N))) := by
        gcongr
    _ = _ := by rw [e]; ring

end SuperdiffusionCLT.Section5
