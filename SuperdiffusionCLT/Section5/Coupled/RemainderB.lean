/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Coupled.Remainder
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscInputs
public import SuperdiffusionCLT.Section5.Response.DirichletHessian

/-!
# The residual `R_z` of `lem.coupled.input`: the deterministic bound

`|R_z|² ≤ M² ⨍_{z+cu_n} |∇ w_D - e_{D,z}|²`, with `M` a bound of `|hshell - hbar_z|` on the box.
This is the Cauchy-Schwarz form of the printed Holder step of `e.coupled.Rz`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open MeasureTheory Homogenization
open scoped ENNReal NNReal
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream

variable {d : ℕ}

/-- Jensen: the squared norm of an average is at most the average of the squared norm. -/
theorem coupled_vecNormSq_volumeAverageVec_le {U : Set (Vec d)} (hV0 : (volume U).toReal ≠ 0)
    (hVt : volume U ≠ ⊤) {F : Vec d → Vec d} (hF : ∀ i, IntegrableOn (fun x => F x i) U)
    (hF2 : ∀ i, IntegrableOn (fun x => F x i * F x i) U) :
    vecNormSq (volumeAverageVec U F) ≤ volumeAverage U (fun x => vecNormSq (F x)) := by
  have hVpos : 0 < (volume U).toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hV0)
  have hcomp : ∀ i, volumeAverageVec U F i * volumeAverageVec U F i ≤
      volumeAverage U (fun x => F x i * F x i) := by
    intro i
    have hcov := volumeAverage_mul_sub_sub hV0 hVt (hF i) (hF i) (hF2 i)
    have hnn : 0 ≤ volumeAverage U (fun x => (F x i - volumeAverage U (fun y => F y i)) *
        (F x i - volumeAverage U (fun y => F y i))) := by
      unfold volumeAverage
      exact mul_nonneg (inv_nonneg.mpr hVpos.le)
        (integral_nonneg fun x => mul_self_nonneg _)
    show volumeAverage U (fun y => F y i) * volumeAverage U (fun y => F y i) ≤ _
    linarith only [hcov, hnn]
  unfold vecNormSq vecDot
  have hsum := volumeAverage_finset_sum (U := U) Finset.univ (fun i x => F x i * F x i)
    (fun i _ => hF2 i)
  calc ∑ i, volumeAverageVec U F i * volumeAverageVec U F i
      ≤ ∑ i, volumeAverage U (fun x => F x i * F x i) := Finset.sum_le_sum fun i _ => hcomp i
    _ = _ := hsum.symm


instance isFiniteMeasure_restrict_cubeSet (Q : TriadicCube d) :
    IsFiniteMeasure (volume.restrict (cubeSet Q)) :=
  ⟨by simpa only [MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter] using volume_cubeSet_lt_top Q⟩

/-- **`|R_z|² ≤ M² ⨍ |g_{D,z}|²`**: for a gradient field square-integrable on `z + cu_n` and `M`
a bound of `|hshell - hbar_z|` there. -/
theorem vecNormSq_coupledR_le (m h : ℕ) (Q : TriadicCube d) (omega : ShellSeq d)
    {gD : Vec d → Vec d}
    (hg2 : ∀ i, MemLp (fun x => gD x i) 2 (volume.restrict (cubeSet Q))) {M : ℝ}
    (hM : ∀ x ∈ cubeSet Q, Book.Ch02.matrixOperatorNorm
      (finiteShellIncrement omega (m - h) m x - principalGauge m h Q omega) ≤ M) :
    vecNormSq (coupledR m h Q omega gD) ≤
      M ^ 2 * volumeAverage (cubeSet Q) (fun x => vecNormSq (gD x - coupledE Q gD)) := by
  have hV0 : (volume (cubeSet Q)).toReal ≠ 0 := by
    rw [volume_cubeSet_toReal]; exact (cubeVolume_pos Q).ne'
  have hVt : volume (cubeSet Q) ≠ ⊤ := (volume_cubeSet_lt_top Q).ne
  have hVpos : 0 < (volume (cubeSet Q)).toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hV0)
  have hg1 : ∀ i, IntegrableOn (fun x => gD x i) (cubeSet Q) :=
    fun i => (hg2 i).integrable one_le_two
  rw [coupledR_eq_average m h Q omega hg1]
  set A : Vec d → Mat d := fun x => finiteShellIncrement omega (m - h) m x - principalGauge m h Q omega
    with hA
  set u : Vec d → Vec d := fun x => gD x - coupledE Q gD with hu
  have hM0 : 0 ≤ M := by
    obtain ⟨x, hx⟩ : (cubeSet Q).Nonempty := by
      by_contra hne
      rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne] at hV0
      simp at hV0
    exact (Book.Ch02.matrixOperatorNorm_nonneg _).trans (hM x hx)
  -- the components of `u` are `L²`
  have hu2 : ∀ j, MemLp (fun x => u x j) 2 (volume.restrict (cubeSet Q)) := by
    intro j
    exact (hg2 j).sub (memLp_const _)
  have huq : Integrable (fun x => vecNormSq (u x)) (volume.restrict (cubeSet Q)) := by
    unfold vecNormSq vecDot
    refine integrable_finsetSum _ fun j _ => ?_
    exact (hu2 j).integrable_sq.congr (Filter.Eventually.of_forall fun x => by simp [sq])
  -- the components of `A u` are measurable, with square bounded by `M² |u|²`
  have hAm : ∀ i j, Continuous (fun x => A x i j) := fun i j => by
    show Continuous (fun x => finiteShellIncrement omega (m - h) m x i j -
      principalGauge m h Q omega i j)
    exact (continuous_finiteShellIncrement_entry omega (m - h) m i j).sub continuous_const
  have hFm : ∀ i, AEStronglyMeasurable (fun x => matVecMul (A x) (u x) i) (volume.restrict (cubeSet Q)) := by
    intro i
    unfold matVecMul
    refine Finset.aestronglyMeasurable_fun_sum _ fun j _ => ?_
    exact (hAm i j).aestronglyMeasurable.mul (hu2 j).aestronglyMeasurable
  have hFpt : ∀ x ∈ cubeSet Q, vecNormSq (matVecMul (A x) (u x)) ≤ M ^ 2 * vecNormSq (u x) := by
    intro x hx
    have h1 := Book.Ch02.vecNormSq_matVecMul_le_matrixOperatorNorm_sq_mul_vecNormSq (A x) (u x)
    have h2 : Book.Ch02.matrixOperatorNorm (A x) ^ 2 ≤ M ^ 2 :=
      pow_le_pow_left₀ (Book.Ch02.matrixOperatorNorm_nonneg _) (hM x hx) 2
    exact h1.trans (mul_le_mul_of_nonneg_right h2 (vecNormSq_nonneg _))
  have hF2int : ∀ i, IntegrableOn (fun x => matVecMul (A x) (u x) i * matVecMul (A x) (u x) i)
      (cubeSet Q) := by
    intro i
    refine Integrable.mono' (huq.const_mul (M ^ 2)) ((hFm i).mul (hFm i)) ?_
    rw [ae_restrict_iff' (measurableSet_cubeSet Q)]
    refine Filter.Eventually.of_forall fun x hx => ?_
    rw [Real.norm_of_nonneg (mul_self_nonneg _)]
    exact (sq_apply_le_vecNormSq (matVecMul (A x) (u x)) i |>.trans' (le_of_eq (by ring))).trans
      (hFpt x hx)
  have hF1int : ∀ i, IntegrableOn (fun x => matVecMul (A x) (u x) i) (cubeSet Q) := by
    intro i
    have hmem : MemLp (fun x => matVecMul (A x) (u x) i) 2 (volume.restrict (cubeSet Q)) :=
      (memLp_two_iff_integrable_sq (hFm i)).2
        ((hF2int i).congr (Filter.Eventually.of_forall fun x => by simp [sq]))
    exact hmem.integrable one_le_two
  refine (coupled_vecNormSq_volumeAverageVec_le hV0 hVt hF1int hF2int).trans ?_
  unfold volumeAverage
  rw [← mul_assoc, mul_comm (M ^ 2), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hVpos.le)
  rw [← integral_const_mul]
  refine setIntegral_mono_on ?_ ((huq.const_mul (M ^ 2))) (measurableSet_cubeSet Q) hFpt
  unfold vecNormSq vecDot
  refine integrable_finsetSum _ fun i _ => ?_
  exact hF2int i


/-! ## The Poincare step on the boxes -/

/-- The boxes `descendantsAtScale (cu_Kc) n` are the sub-cubes `largeCubeSubcubes d n Kc` of the
Poincare inequality. -/
theorem mem_largeCubeSubcubes_of_mem_descendantsAtScale {Kc n : ℕ} (hn : n ≤ Kc)
    {Q : TriadicCube d} (hQ : Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ)) :
    Q ∈ SuperdiffusionCLT.Section2.Estimates.Stream.largeCubeSubcubes d n Kc := by
  have hk : (n : ℤ) ≤ (originCube d (Kc : ℤ)).scale := by
    show (n : ℤ) ≤ (Kc : ℤ)
    exact_mod_cast hn
  have h := descendantsAtScale_eq_descendantsAtDepth (originCube d (Kc : ℤ)) hk
  have hnat : Int.toNat ((originCube d (Kc : ℤ)).scale - (n : ℤ)) = Kc - n := by
    show Int.toNat ((Kc : ℤ) - (n : ℤ)) = Kc - n
    omega
  rw [hnat] at h
  rw [h] at hQ
  exact hQ

/-- The squared normalized `L̲²` norm on a box is the `ofReal` of the squared-norm average. -/
theorem vecCubeLpENorm_two_sq_eq_ofReal_volumeAverage {Q : TriadicCube d} {F : Vec d → Vec d}
    (hF : MemVectorL2 (openCubeSet Q) F) :
    SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm Q 2 F ^ (2 : ℕ) =
      ENNReal.ofReal (volumeAverage (cubeSet Q) (fun x => vecNormSq (F x))) := by
  rw [SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm_two_sq_eq_ofReal hF,
    SuperdiffusionCLT.Section3.ResponseFields.integral_normalizedCubeMeasure_eq]
  congr 1
  unfold volumeAverage
  rw [volume_cubeSet_toReal, MeasureTheory.setIntegral_congr_set (cubeSet_ae_eq_openCubeSet Q)]


theorem coupledE_eq_open (Q : TriadicCube d) (gD : Vec d → Vec d) :
    coupledE Q gD = volumeAverageVec (openCubeSet Q) gD := by
  funext i
  simp only [coupledE, volumeAverageVec, volumeAverage, volume_openCubeSet_eq_volume_cubeSet]
  rw [MeasureTheory.setIntegral_congr_set (cubeSet_ae_eq_openCubeSet Q)]

/-- **`|R_z|²` against the weak Hessian**: on each box `Q ∈ descendantsAtScale cu_Kc n`,
`|R_z|² ≤ M_Q² (c_P 3^n ‖∇² w_D‖_{L̲²(Q)})²`, `M_Q = d √d 3^n g_Q` (the shell oscillation, `g_Q` the
derivative gauge of the translated shell sequence). -/
theorem ofReal_vecNormSq_coupledR_le {Kc n m h : ℕ} (hn : n ≤ m - h) (hnK : n ≤ Kc)
    (wD : H10Function (openCubeSet (originCube d (Kc : ℤ))))
    (HD : HasWeakHessianOn (openCubeSet (originCube d (Kc : ℤ))) wD.toH1Function)
    {Q : TriadicCube d} (hQ : Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ))
    (omega : ShellSeq d) :
    ENNReal.ofReal (vecNormSq (coupledR m h Q omega wD.toH1Function.grad)) ≤
      ENNReal.ofReal (((d : ℝ) * (Real.sqrt d * (3 : ℝ) ^ n *
          finiteShellDerivGauge (m - h) m (ShellField.translateSequence (cubeCenter Q) omega))) ^ 2) *
        (ENNReal.ofReal (SuperdiffusionCLT.Section3.Terms.termTwoPoincareConst d *
            (3 : ℝ) ^ ((n : ℕ) : ℝ)) *
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2
            (fun x => HilbertMat.ofMat (fun i j => HD.hess i j x))) ^ 2 := by
  have hQs : Q.scale = (n : ℤ) :=
    Homogenization.Book.Ch04.scale_eq_of_mem_descendantsAtScale_originCube
      (by exact_mod_cast hnK) hQ
  have hR := mem_largeCubeSubcubes_of_mem_descendantsAtScale hnK hQ
  have hsub : openCubeSet Q ⊆ openCubeSet (originCube d (Kc : ℤ)) :=
    openCubeSet_subset_of_mem_descendantsAtDepth (by
      have := hR; unfold SuperdiffusionCLT.Section2.Estimates.Stream.largeCubeSubcubes at this
      exact this)
  have hg2 : ∀ i, MemLp (fun x => wD.toH1Function.grad x i) 2 (volume.restrict (cubeSet Q)) := by
    intro i
    have h1 := (wD.toH1Function.gradMemL2 i).mono_measure (Measure.restrict_mono_set volume hsub)
    rwa [← Measure.restrict_congr_set (cubeSet_ae_eq_openCubeSet Q)] at h1
  have hM : ∀ x ∈ cubeSet Q, Book.Ch02.matrixOperatorNorm
      (finiteShellIncrement omega (m - h) m x - principalGauge m h Q omega) ≤
        (d : ℝ) * (Real.sqrt d * (3 : ℝ) ^ n *
          finiteShellDerivGauge (m - h) m (ShellField.translateSequence (cubeCenter Q) omega)) :=
    fun x hx => norm_shell_sub_gauge_le hn Q hQs omega hx
  have h1 := vecNormSq_coupledR_le m h Q omega hg2 hM
  have hM0 : 0 ≤ ((d : ℝ) * (Real.sqrt d * (3 : ℝ) ^ n *
          finiteShellDerivGauge (m - h) m (ShellField.translateSequence (cubeCenter Q) omega))) ^ 2 :=
    sq_nonneg _
  have hu : MemVectorL2 (openCubeSet Q) (fun x => wD.toH1Function.grad x -
      volumeAverageVec (openCubeSet Q) wD.toH1Function.grad) := by
    have hgrad : MemVectorL2 (openCubeSet Q) wD.toH1Function.grad :=
      (SuperdiffusionCLT.Section3.Terms.memVectorL2_of_gradMemL2On _ wD.toH1Function.gradMemL2).mono_measure
        (Measure.restrict_mono_set volume hsub)
    exact hgrad.sub (memLp_const _)
  calc ENNReal.ofReal (vecNormSq (coupledR m h Q omega wD.toH1Function.grad))
      ≤ ENNReal.ofReal (_ * volumeAverage (cubeSet Q)
          (fun x => vecNormSq (wD.toH1Function.grad x - coupledE Q wD.toH1Function.grad))) :=
        ENNReal.ofReal_le_ofReal h1
    _ = ENNReal.ofReal _ * ENNReal.ofReal (volumeAverage (cubeSet Q)
          (fun x => vecNormSq (wD.toH1Function.grad x - coupledE Q wD.toH1Function.grad))) :=
        ENNReal.ofReal_mul hM0
    _ = ENNReal.ofReal _ * SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm Q 2
          (fun x => wD.toH1Function.grad x -
            volumeAverageVec (openCubeSet Q) wD.toH1Function.grad) ^ (2 : ℕ) := by
        rw [vecCubeLpENorm_two_sq_eq_ofReal_volumeAverage hu, coupledE_eq_open]
    _ ≤ _ := by
        refine mul_le_mul_right ?_ _
        exact pow_le_pow_left' (SuperdiffusionCLT.Section3.Terms.oscH1Carrier_poincare hnK HD hR) 2


/-- Weighted AM-GM in `ℝ≥0∞`: `a b ≤ t a² + t⁻¹ b²` for `0 < t < ∞`. -/
theorem ennreal_mul_le_amgm (a b t : ℝ≥0∞) (ht0 : t ≠ 0) (htt : t ≠ ⊤) :
    a * b ≤ t * a ^ 2 + t⁻¹ * b ^ 2 := by
  have hti : t⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr htt
  by_cases ha : a = ⊤
  · subst ha
    calc (⊤ : ℝ≥0∞) * b ≤ ⊤ := le_top
      _ = t * (⊤ : ℝ≥0∞) ^ 2 := by simp [ht0]
      _ ≤ _ := le_self_add
  by_cases hb : b = ⊤
  · subst hb
    calc a * (⊤ : ℝ≥0∞) ≤ ⊤ := le_top
      _ = t⁻¹ * (⊤ : ℝ≥0∞) ^ 2 := by simp [hti]
      _ ≤ _ := le_add_self
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  lift t to ℝ≥0 using htt
  have ht0' : t ≠ 0 := by exact_mod_cast ht0
  have htpos : (0 : ℝ) < t := by exact_mod_cast pos_iff_ne_zero.mpr ht0'
  rw [← ENNReal.coe_inv ht0']
  norm_cast
  rw [← NNReal.coe_le_coe]
  push_cast
  have h1 : (a : ℝ) * b * t ≤ t ^ 2 * a ^ 2 + b ^ 2 := by
    nlinarith only [sq_nonneg ((t : ℝ) * a - b), sq_nonneg (t : ℝ), sq_nonneg (a : ℝ), sq_nonneg (b : ℝ), mul_nonneg a.coe_nonneg b.coe_nonneg, htpos]
  rw [← sub_nonneg]
  have : (t : ℝ) * a ^ 2 + (t : ℝ)⁻¹ * b ^ 2 - a * b = ((t : ℝ) ^ 2 * a ^ 2 + b ^ 2 - a * b * t) / t := by
    field_simp
  rw [this]
  exact div_nonneg (by linarith only [h1]) htpos.le


theorem coupled_sum_lintegral_le_lintegral_sum {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (S : Finset ι) (f : ι → Ω → ℝ≥0∞) :
    ∑ i ∈ S, ∫⁻ ω, f i ω ∂μ ≤ ∫⁻ ω, ∑ i ∈ S, f i ω ∂μ := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    calc ∫⁻ ω, f a ω ∂μ + ∑ i ∈ s, ∫⁻ ω, f i ω ∂μ
        ≤ ∫⁻ ω, f a ω ∂μ + ∫⁻ ω, ∑ i ∈ s, f i ω ∂μ := add_le_add le_rfl ih
      _ ≤ ∫⁻ ω, (f a ω + ∑ i ∈ s, f i ω) ∂μ := le_lintegral_add _ _
      _ = _ := by simp_rw [Finset.sum_insert ha]

theorem subcubeAvg_lintegral_le_lintegral_subcubeAvg {Kc n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (f : TriadicCube d → Ω → ℝ≥0∞) :
    subcubeAvg Kc n (fun Q => ∫⁻ ω, f Q ω ∂μ) ≤ ∫⁻ ω, subcubeAvg Kc n (fun Q => f Q ω) ∂μ := by
  unfold subcubeAvg
  set D := descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ)
  by_cases hD : D.card = 0
  · rw [Finset.card_eq_zero.mp hD]; simp
  · have hne : (D.card : ℝ≥0∞)⁻¹ ≠ ⊤ :=
      ENNReal.inv_ne_top.mpr (by exact_mod_cast hD)
    rw [lintegral_const_mul' _ _ hne]
    exact mul_le_mul_right (coupled_sum_lintegral_le_lintegral_sum _ _) _

theorem coupled_eLpNorm_four_pow {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} (f : α → E) (hf : AEStronglyMeasurable f μ) :
    (eLpNorm f 4 μ) ^ (4 : ℕ) = ∫⁻ x, ‖f x‖ₑ ^ (4 : ℕ) ∂μ := by
  have hq : (4 : ℝ≥0∞) ≠ 0 := by norm_num
  have hqt : (4 : ℝ≥0∞) ≠ ⊤ := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq hqt hf]
  have h4 : (4 : ℝ≥0∞).toReal = ((4 : ℕ) : ℝ) := by norm_num
  rw [h4, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  have : (1 / ((4 : ℕ) : ℝ)) * ((4 : ℕ) : ℝ) = 1 := by norm_num
  rw [this, ENNReal.rpow_one]
  exact lintegral_congr fun x => ENNReal.rpow_natCast _ _

/-- From the `L⁸(P)` bound of the `L̲⁸` norm to the `L⁴(P)` bound of the `L̲⁴` norm (weighted AM-GM,
no measurability of the family is used). -/
theorem lintegral_cubeLpENorm_four_pow_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (Q : TriadicCube d) (F : Ω → Vec d → HilbertMat d) {B : ℝ} (hB : 0 < B)
    (hV : (∫⁻ ω, (SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 8 (F ω)) ^ (8 : ℕ) ∂μ) ^
      ((1 : ℝ) / 8) ≤ ENNReal.ofReal B) :
    ∫⁻ ω, (SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 4 (F ω)) ^ (4 : ℕ) ∂μ ≤
      2 * ENNReal.ofReal (B ^ 4) := by
  set X : Ω → ℝ≥0∞ := fun ω => SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 8 (F ω) with hX
  have h8 : ∫⁻ ω, (X ω) ^ (8 : ℕ) ∂μ ≤ ENNReal.ofReal (B ^ 8) := by
    have := ENNReal.rpow_le_rpow hV (by norm_num : (0 : ℝ) ≤ 8)
    rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ (by norm_num), ENNReal.rpow_one,
      ENNReal.ofReal_rpow_of_nonneg hB.le (by norm_num)] at this
    simpa only [ge_iff_le, Real.rpow_ofNat] using this
  set t : ℝ≥0∞ := ENNReal.ofReal (B ^ 4) with ht
  have ht0 : t ≠ 0 := by
    rw [ht]; exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have htt : t ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpt : ∀ ω, (SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 4 (F ω)) ^ (4 : ℕ) ≤
      t + t⁻¹ * (X ω) ^ (8 : ℕ) := by
    intro ω
    have h1 : SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 4 (F ω) ≤ X ω :=
      eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
    have h2 := ennreal_mul_le_amgm 1 ((X ω) ^ (4 : ℕ)) t ht0 htt
    calc _ ≤ (X ω) ^ (4 : ℕ) := pow_le_pow_left' h1 4
      _ = 1 * (X ω) ^ (4 : ℕ) := (one_mul _).symm
      _ ≤ _ := h2.trans (by
          refine le_of_eq ?_
          rw [one_pow, mul_one, ← pow_mul])
  calc ∫⁻ ω, (SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 4 (F ω)) ^ (4 : ℕ) ∂μ
      ≤ ∫⁻ ω, (t + t⁻¹ * (X ω) ^ (8 : ℕ)) ∂μ := lintegral_mono hpt
    _ = t + t⁻¹ * ∫⁻ ω, (X ω) ^ (8 : ℕ) ∂μ := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr ht0)]
    _ ≤ t + t⁻¹ * ENNReal.ofReal (B ^ 8) := by gcongr
    _ = 2 * t := by
        have e8 : ENNReal.ofReal (B ^ 8) = t * t := by
          rw [ht, ← ENNReal.ofReal_mul (by positivity)]
          congr 1; ring
        rw [e8, ← mul_assoc, ENNReal.inv_mul_cancel ht0 htt, one_mul, two_mul]
    _ = _ := rfl


theorem coupled_subcubeAvg_mono_on {Kc n : ℕ} {f g : TriadicCube d → ENNReal}
    (h : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ), f Q ≤ g Q) :
    subcubeAvg Kc n f ≤ subcubeAvg Kc n g := by
  unfold subcubeAvg
  exact mul_le_mul_right (Finset.sum_le_sum h) _

/-- The assembled bound for the box-average of `E|R_z|²`, with explicit constants. -/
theorem subcubeAvg_coupledR_le [NeZero d] {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    {P : MeasureTheory.ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) {m h n Kc : ℕ} (hh : 1 ≤ h)
    (h400 : 400 * h ≤ m) (hm : 1000000 ≤ m) (hnum : nu⁻¹ ≤ (m : ℝ))
    (hn : n = ⌊(m : ℝ) - h - 100 * Real.logb 3 (nu⁻¹ * m)⌋₊) (hnK : n ≤ Kc)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d (Kc : ℤ))))
    (HD : ∀ omega, HasWeakHessianOn (openCubeSet (originCube d (Kc : ℤ))) (wD omega).toH1Function)
    {B : ℝ} (hB : 0 < B)
    (hV : (∫⁻ ω, (SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (Kc : ℤ)) 8
        (fun x => HilbertMat.ofMat (fun i j => (HD ω).hess i j x))) ^ (8 : ℕ) ∂P.toMeasure) ^
        ((1 : ℝ) / 8) ≤ ENNReal.ofReal B)
    {c A : ℝ} (hc : 0 < c) (hA : 0 < A)
    (hcn : SuperdiffusionCLT.Section3.Terms.termTwoPoincareConst d * (3 : ℝ) ^ n ≤ c)
    (hAm : shellOscConst d * ((m : ℝ) ^ 100)⁻¹ ≤ A) :
    subcubeAvg Kc n (fun Q => ∫⁻ ω, ENNReal.ofReal
        (vecNormSq (coupledR m h Q ω (wD ω).toH1Function.grad)) ∂P.toMeasure) ≤
      3 * ENNReal.ofReal (c ^ 2 * B ^ 2 * A ^ 2) := by
  have hnm := scale_le_sub hnu hnu1 h400 hm hnum hn
  set t : ℝ≥0∞ := ENNReal.ofReal (c ^ 2 * B ^ 2 / A ^ 2) with ht
  have ht0 : t ≠ 0 := by
    rw [ht]; exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have htt : t ≠ ⊤ := ENNReal.ofReal_ne_top
  -- pointwise AM-GM bound
  have hpt : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ), ∀ ω,
      ENNReal.ofReal (vecNormSq (coupledR m h Q ω (wD ω).toH1Function.grad)) ≤
        t * ENNReal.ofReal (((d : ℝ) * (Real.sqrt d * (3 : ℝ) ^ n *
            finiteShellDerivGauge (m - h) m (ShellField.translateSequence (cubeCenter Q) ω))) ^ 4) +
          t⁻¹ * (ENNReal.ofReal c * SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 4 (fun x => HilbertMat.ofMat (fun i j => (HD ω).hess i j x))) ^ 4 := by
    intro Q hQ ω
    have h1 := ofReal_vecNormSq_coupledR_le hnm hnK (wD ω) (HD ω) hQ ω
    set M : ℝ := (d : ℝ) * (Real.sqrt d * (3 : ℝ) ^ n *
      finiteShellDerivGauge (m - h) m (ShellField.translateSequence (cubeCenter Q) ω)) with hM
    set H2 := SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2
      (fun x => HilbertMat.ofMat (fun i j => (HD ω).hess i j x)) with hH2
    set H4 := SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 4
      (fun x => HilbertMat.ofMat (fun i j => (HD ω).hess i j x)) with hH4
    have hH24 : H2 ≤ H4 := eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
    have hcc : ENNReal.ofReal (SuperdiffusionCLT.Section3.Terms.termTwoPoincareConst d *
        (3 : ℝ) ^ ((n : ℕ) : ℝ)) ≤ ENNReal.ofReal c := by
      apply ENNReal.ofReal_le_ofReal
      rw [Real.rpow_natCast]; exact hcn
    have h2 : ENNReal.ofReal (M ^ 2) * (ENNReal.ofReal
        (SuperdiffusionCLT.Section3.Terms.termTwoPoincareConst d * (3 : ℝ) ^ ((n : ℕ) : ℝ)) * H2) ^ 2 ≤
        ENNReal.ofReal (M ^ 2) * (ENNReal.ofReal c * H4) ^ 2 :=
      mul_le_mul_right (pow_le_pow_left' (mul_le_mul' hcc hH24) 2) _
    have h3 := ennreal_mul_le_amgm (ENNReal.ofReal (M ^ 2)) ((ENNReal.ofReal c * H4) ^ 2) t ht0 htt
    refine h1.trans (h2.trans (h3.trans (le_of_eq ?_)))
    rw [← ENNReal.ofReal_pow (sq_nonneg M), ← pow_mul, ← pow_mul]
  have hmeasM : ∀ Q : TriadicCube d, Measurable (fun ω : ShellSeq d => ENNReal.ofReal
      (((d : ℝ) * (Real.sqrt d * (3 : ℝ) ^ n *
        finiteShellDerivGauge (m - h) m (ShellField.translateSequence (cubeCenter Q) ω))) ^ 4)) := by
    intro Q
    exact ENNReal.measurable_ofReal.comp
      ((((measurable_finiteShellDerivGauge_translate (cubeCenter Q) (m - h) m).const_mul
        (Real.sqrt d * (3 : ℝ) ^ n)).const_mul (d : ℝ)).pow_const 4)
  set oc : ℝ≥0∞ := ENNReal.ofReal c with hoc
  have hK2 : t⁻¹ * oc ^ 4 ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr ht0)
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hQbd : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
      ∫⁻ ω, ENNReal.ofReal (vecNormSq (coupledR m h Q ω (wD ω).toH1Function.grad)) ∂P.toMeasure ≤
        t * ∫⁻ ω, ENNReal.ofReal (((d : ℝ) * (Real.sqrt d * (3 : ℝ) ^ n *
            finiteShellDerivGauge (m - h) m (ShellField.translateSequence (cubeCenter Q) ω))) ^ 4)
              ∂P.toMeasure +
          (t⁻¹ * oc ^ 4) * ∫⁻ ω, (SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 4
              (fun x => HilbertMat.ofMat (fun i j => (HD ω).hess i j x))) ^ 4 ∂P.toMeasure := by
    intro Q hQ
    calc _ ≤ ∫⁻ ω, (t * ENNReal.ofReal (((d : ℝ) * (Real.sqrt d * (3 : ℝ) ^ n *
            finiteShellDerivGauge (m - h) m (ShellField.translateSequence (cubeCenter Q) ω))) ^ 4) +
          (t⁻¹ * oc ^ 4) * (SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 4
              (fun x => HilbertMat.ofMat (fun i j => (HD ω).hess i j x))) ^ 4) ∂P.toMeasure :=
          lintegral_mono fun ω => (hpt Q hQ ω).trans (le_of_eq (by rw [mul_pow oc]; ring))
      _ = _ := by
          rw [lintegral_add_left ((hmeasM Q).const_mul t), lintegral_const_mul' _ _ htt,
            lintegral_const_mul' _ _ hK2]
  have hA4 : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
      ∫⁻ ω, ENNReal.ofReal (((d : ℝ) * (Real.sqrt d * (3 : ℝ) ^ n *
            finiteShellDerivGauge (m - h) m (ShellField.translateSequence (cubeCenter Q) ω))) ^ 4)
              ∂P.toMeasure ≤ ENNReal.ofReal (A ^ 4) := by
    intro Q _
    refine (lintegral_scaledGauge_pow_four_le hnu hnu1 hPrefix hJ3 hh h400 hm hnum hn Q).trans ?_
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (mul_nonneg (shellOscConst_nonneg d)
      (by positivity)) hAm 4)
  -- the sum of the fourth powers of the box Hessian norms is the fourth power of the large one
  have haeQ : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ), ∀ ω,
      AEStronglyMeasurable (fun x => HilbertMat.ofMat (fun i j => (HD ω).hess i j x))
        (normalizedCubeMeasure Q) := fun Q hQ ω =>
    SuperdiffusionCLT.Section3.Terms.aestronglyMeasurable_hessMat_of_weakHessian_subcube
      (HD ω) (mem_largeCubeSubcubes_of_mem_descendantsAtScale hnK hQ)
  have haeK : ∀ ω, AEStronglyMeasurable (fun x => HilbertMat.ofMat (fun i j => (HD ω).hess i j x))
      (normalizedCubeMeasure (originCube d (Kc : ℤ))) := by
    intro ω
    rw [SuperdiffusionCLT.Section3.ResponseFields.normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
    exact ((SuperdiffusionCLT.Section3.Terms.memLp_hessMat_of_weakHessian _ (HD ω)).smul_measure
      ENNReal.ofReal_ne_top).aestronglyMeasurable
  have hX4 : ∀ ω, subcubeAvg Kc n (fun Q => (SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 4
      (fun x => HilbertMat.ofMat (fun i j => (HD ω).hess i j x))) ^ 4) =
        (SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (Kc : ℤ)) 4
          (fun x => HilbertMat.ofMat (fun i j => (HD ω).hess i j x))) ^ 4 := by
    intro ω
    calc _ = subcubeAvg Kc n (fun Q => ∫⁻ x, ‖HilbertMat.ofMat (fun i j => (HD ω).hess i j x)‖ₑ ^ (4 : ℕ)
          ∂normalizedCubeMeasure Q) := by
          unfold subcubeAvg
          congr 1
          exact Finset.sum_congr rfl fun Q hQ => coupled_eLpNorm_four_pow _ (haeQ Q hQ ω)
      _ = ∫⁻ x, ‖HilbertMat.ofMat (fun i j => (HD ω).hess i j x)‖ₑ ^ (4 : ℕ)
          ∂normalizedCubeMeasure (originCube d (Kc : ℤ)) :=
          subcubeAvg_lintegral_normalizedCubeMeasure hnK _
      _ = _ := (coupled_eLpNorm_four_pow _ (haeK ω)).symm
  have hB4 : ∫⁻ ω, (SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (Kc : ℤ)) 4
      (fun x => HilbertMat.ofMat (fun i j => (HD ω).hess i j x))) ^ 4 ∂P.toMeasure ≤
      2 * ENNReal.ofReal (B ^ 4) :=
    lintegral_cubeLpENorm_four_pow_le (originCube d (Kc : ℤ))
      (fun ω x => HilbertMat.ofMat (fun i j => (HD ω).hess i j x)) hB hV
  have hbavg : subcubeAvg Kc n (fun Q => ∫⁻ ω, (SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 4
      (fun x => HilbertMat.ofMat (fun i j => (HD ω).hess i j x))) ^ 4 ∂P.toMeasure) ≤
      2 * ENNReal.ofReal (B ^ 4) := by
    refine (subcubeAvg_lintegral_le_lintegral_subcubeAvg _).trans ?_
    simp_rw [hX4]
    exact hB4
  have haavg : subcubeAvg Kc n (fun Q => ∫⁻ ω, ENNReal.ofReal (((d : ℝ) * (Real.sqrt d * (3 : ℝ) ^ n *
            finiteShellDerivGauge (m - h) m (ShellField.translateSequence (cubeCenter Q) ω))) ^ 4)
              ∂P.toMeasure) ≤ ENNReal.ofReal (A ^ 4) := subcubeAvg_le_of_le hA4
  have hsum := coupled_subcubeAvg_mono_on hQbd
  rw [subcubeAvg_add, subcubeAvg_const_mul, subcubeAvg_const_mul] at hsum
  refine hsum.trans ?_
  have e1 : t * ENNReal.ofReal (A ^ 4) = ENNReal.ofReal (c ^ 2 * B ^ 2 * A ^ 2) := by
    rw [ht, ← ENNReal.ofReal_mul (by positivity)]
    congr 1; field_simp
  have e2 : (t⁻¹ * oc ^ 4) * (2 * ENNReal.ofReal (B ^ 4)) = 2 * ENNReal.ofReal (c ^ 2 * B ^ 2 * A ^ 2) := by
    have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
    rw [ht, hoc, h2, ← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_pow hc.le,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    field_simp
  calc _ ≤ t * ENNReal.ofReal (A ^ 4) + (t⁻¹ * oc ^ 4) * (2 * ENNReal.ofReal (B ^ 4)) :=
        add_le_add (mul_le_mul_right haavg _) (mul_le_mul_right hbavg _)
    _ = _ := by rw [e1, e2]; ring


/-- **`e.coupled.Rz`**: `(avsum_z E|R_z|²)^{1/2} ≤ C shom_{m-h}^{-1} m^{-100}`.
The binders `wN`, `hwN` are those of the Hessian clause (`response_hessian_L8`); the weak
Hessian exists (`exists_hasWeakHessianOn_of_isDirichletResponse`) and is a `Nonempty` hypothesis
here. -/
theorem coupled_Rz (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
      ∀ (P : MeasureTheory.ProbabilityMeasure (ShellSeq d)), ShellLawPrefix d P → ShellLawJ2 d P →
        ShellLawJ3 d P → ShellLawJ1Restriction d P → ShellLawJ4 d P →
      ∀ m h Kc n : ℕ, 1 ≤ h → 400 * h ≤ m → 100 * m ≤ Kc → 1000000 ≤ m → nu⁻¹ ≤ (m : ℝ) →
        n = ⌊(m : ℝ) - h - 100 * Real.logb 3 (nu⁻¹ * m)⌋₊ →
      ∀ e : Vec d, vecNormSq e ≤ 1 →
      ∀ (wD : ShellSeq d → H10Function (openCubeSet (originCube d (Kc : ℤ))))
        (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d (Kc : ℤ)))),
        (∀ omega, SuperdiffusionCLT.Section3.ResponseFields.IsCubeDirichletResponse
          (originCube d (Kc : ℤ)) (hshellFlux nu P m h omega e) (wD omega)) →
        (∀ omega, SuperdiffusionCLT.Section3.ResponseFields.IsCubeNeumannResponse
          (originCube d (Kc : ℤ)) (hshellFlux nu P m h omega e) (wN omega)) →
        (∀ omega, Nonempty (HasWeakHessianOn (openCubeSet (originCube d (Kc : ℤ)))
            (wD omega).toH1Function)) →
        (subcubeAvg Kc n (fun Q => ∫⁻ ω, ENNReal.ofReal
            (vecNormSq (coupledR m h Q ω (wD ω).toH1Function.grad)) ∂P.toMeasure)) ^
            ((1 : ℝ) / 2) ≤
          ENNReal.ofReal (C * (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu (m - h) P)⁻¹ *
            (m : ℝ) ^ (-(100 : ℝ))) := by
  obtain ⟨Ch, hCh1, HH⟩ := response_hessian_L8 d hd
  set cP := SuperdiffusionCLT.Section3.Terms.termTwoPoincareConst d with hcP
  have hcP0 : 0 ≤ cP := SuperdiffusionCLT.Section3.Terms.termTwoPoincareConst_nonneg d
  set K := shellOscConst d with hK
  have hK0 : 0 ≤ K := shellOscConst_nonneg d
  set C0 := Real.sqrt 3 * (cP + 1) * Ch * (K + 1) with hC0
  have hC00 : 0 ≤ C0 := by positivity
  refine ⟨max 1 C0, le_max_left _ _, ?_⟩
  intro nu hnu hnu1 P hPre hJ2 hJ3 hJ1 hJ4 m h Kc n hh h400 h100 hm hnum hn e he wD wN hwD hwN hHD
  have hnm := scale_le_sub hnu hnu1 h400 hm hnum hn
  have hnK : n ≤ Kc := by omega
  let HD : ∀ omega, HasWeakHessianOn (openCubeSet (originCube d (Kc : ℤ))) (wD omega).toH1Function :=
    fun omega => (hHD omega).some
  have hσ : 0 < SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu (m - h) P :=
    SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite_pos hnu (m - h) hPre hJ2 hJ3 hJ4
  set σ := SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu (m - h) P with hσdef
  have hm' : (1000000 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith only [hm']
  have hmu : 0 < ((m : ℝ) ^ 100)⁻¹ := by positivity
  have hpow : (m : ℝ) ^ (-(100 : ℝ)) = ((m : ℝ) ^ 100)⁻¹ := by
    rw [Real.rpow_neg hm0.le, show (100 : ℝ) = ((100 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hpow]
  set μ : ℝ := ((m : ℝ) ^ 100)⁻¹ with hμ
  set B : ℝ := Ch * σ⁻¹ * (3 : ℝ) ^ (-((m - h : ℕ) : ℝ)) with hB
  have hB0 : 0 < B := by positivity
  have hV := HH nu hnu hnu1 P hPre hJ2 hJ3 hJ1 hJ4 m h Kc hh h400 h100 e he wD wN hwD hwN HD
  set c : ℝ := (cP + 1) * (3 : ℝ) ^ n with hc
  set A : ℝ := (K + 1) * μ with hA
  have hc0 : 0 < c := by positivity
  have hA0 : 0 < A := by positivity
  have hmain := subcubeAvg_coupledR_le hnu hnu1 hPre hJ3 hh h400 hm hnum hn hnK wD HD hB0 hV hc0 hA0
    (by rw [hc]; nlinarith only [pow_pos (by norm_num : (0 : ℝ) < 3) n]) 
    (by rw [hA]; nlinarith only [hmu])
  have hratio := principal_pow_ratio_le hnu hnu1 h400 hm hnum hn
  have hnu99 : (nu / m) ^ 100 ≤ 1 := pow_le_one₀ (by positivity) (by
    rw [div_le_one hm0]; linarith only [hnu1, hm'])
  have h3 : (3 : ℝ) ^ n * (3 : ℝ) ^ (-((m - h : ℕ) : ℝ)) ≤ 1 := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
    exact hratio.trans hnu99
  have hμ1 : μ ≤ 1 := by
    rw [hμ]; exact inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith only [hm']))
  calc _ ≤ (3 * ENNReal.ofReal (c ^ 2 * B ^ 2 * A ^ 2)) ^ ((1 : ℝ) / 2) :=
        ENNReal.rpow_le_rpow hmain (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt 3 * (c * B * A)) := by
        have h3' : (3 : ℝ≥0∞) = ENNReal.ofReal 3 := by simp
        rw [h3', ← ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_rpow_of_nonneg (by positivity)
          (by norm_num), ← Real.sqrt_eq_rpow]
        congr 1
        rw [Real.sqrt_mul (by norm_num), show c ^ 2 * B ^ 2 * A ^ 2 = (c * B * A) ^ 2 by ring,
          Real.sqrt_sq (by positivity)]
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have e1 : c * B * A = ((cP + 1) * Ch * (K + 1)) * σ⁻¹ * μ *
            ((3 : ℝ) ^ n * (3 : ℝ) ^ (-((m - h : ℕ) : ℝ))) := by rw [hc, hB, hA]; ring
        have hsq : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
        have hpos : 0 ≤ ((cP + 1) * Ch * (K + 1)) * σ⁻¹ * μ := by positivity
        calc Real.sqrt 3 * (c * B * A)
            = Real.sqrt 3 * (((cP + 1) * Ch * (K + 1)) * σ⁻¹ * μ) *
                ((3 : ℝ) ^ n * (3 : ℝ) ^ (-((m - h : ℕ) : ℝ))) := by rw [e1]; ring
          _ ≤ Real.sqrt 3 * (((cP + 1) * Ch * (K + 1)) * σ⁻¹ * μ) * 1 :=
              mul_le_mul_of_nonneg_left h3 (by positivity)
          _ = C0 * σ⁻¹ * μ := by rw [hC0]; ring
          _ ≤ max 1 C0 * σ⁻¹ * μ := by
              gcongr
              exact le_max_right _ _

end SuperdiffusionCLT.Section5
