/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3CgFinalD
public import Homogenization.Sobolev.FiniteLpCoordinate
public import Homogenization.Sobolev.Foundations.PoincareW1p.Dilation
public import Homogenization.Sobolev.Foundations.PoincareW1p.Translation
public import SuperdiffusionCLT.Section2.Annealed.MixingAnchorAssembly
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3AnchorsConstFirst
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3LocAnchor

/-! Selected-scale coarse-block bounds and the deterministic fourth-power
Poincare estimate from the proof of `e.RHS.term3.A`. -/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

/-- The offset dominates the logarithm strongly enough to contain any
window below the outer cutoff. -/
theorem cgFinalE_window_bound {nu K : ℝ} {L h : ℕ}
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hL : 1 ≤ L) (hh : h < L)
    (hlog : 0 ≤ Real.log (nu⁻¹ * (L : ℝ))) (hKlog3 : 8056 ≤ K * Real.log 3) :
    h + 1 ≤ 3 ^ SuperdiffusionCLT.Section3.Setup.scaleOffset K nu L := by
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  have hinv : (1 : ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
  have hLt : (L : ℝ) ≤ nu⁻¹ * (L : ℝ) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hinv hLp.le
  have hlogL : Real.log (L : ℝ) ≤ Real.log (nu⁻¹ * (L : ℝ)) :=
    Real.log_le_log hLp hLt
  have hSix := SuperdiffusionCLT.Section3.Setup.six_log_le_scaleOffset_mul_log_three
    hKlog3 hlog
  have hpow : (L : ℝ) ≤ (3 : ℝ) ^
      SuperdiffusionCLT.Section3.Setup.scaleOffset K nu L := by
    calc
      (L : ℝ) = Real.exp (Real.log (L : ℝ)) := (Real.exp_log hLp).symm
      _ ≤ Real.exp ((SuperdiffusionCLT.Section3.Setup.scaleOffset K nu L : ℝ) *
          Real.log 3) := Real.exp_le_exp.mpr (by linarith only [hlogL, hSix, hlog])
      _ = (3 : ℝ) ^ SuperdiffusionCLT.Section3.Setup.scaleOffset K nu L := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
  have hnat : L ≤ 3 ^ SuperdiffusionCLT.Section3.Setup.scaleOffset K nu L := by
    exact_mod_cast hpow
  exact (Nat.succ_le_of_lt hh).trans hnat

/-- Jensen's inequality and the exact cube partition control the fourth
power of the difference of the two cube means by the coarse-cube fluctuation.
This is the averaging step before Poincare in the proof of `e.RHS.term3.A`. -/
theorem cgFinalE_fourth_mean_difference {d : ℕ} (Q : Homogenization.TriadicCube d)
    (j : ℕ) {F : Homogenization.Vec d → Homogenization.Vec d}
    (hF : Homogenization.MemVectorL2 (Homogenization.openCubeSet Q) F) :
    ENNReal.ofReal (((Homogenization.descendantsAtDepth Q j).card : ℝ)⁻¹ *
      ∑ R ∈ Homogenization.descendantsAtDepth Q j,
        Homogenization.vecNormSq
          (Homogenization.volumeAverageVec (Homogenization.openCubeSet R) F -
            Homogenization.volumeAverageVec (Homogenization.openCubeSet Q) F) ^ (2 : ℕ)) ≤
      SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm Q 4
        (fun x => F x - Homogenization.volumeAverageVec (Homogenization.openCubeSet Q) F) ^
          (4 : ℕ) := by
  classical
  let c := Homogenization.volumeAverageVec (Homogenization.openCubeSet Q) F
  let G := fun x => F x - c
  have hG : Homogenization.MemVectorL2 (Homogenization.openCubeSet Q) G :=
    memVectorL2_sub_const c hF
  have hRmem : ∀ R ∈ Homogenization.descendantsAtDepth Q j,
      Homogenization.MemVectorL2 (Homogenization.openCubeSet R) F :=
    fun R hR => memVectorL2_mono (Homogenization.openCubeSet_subset_of_mem_descendantsAtDepth hR) hF
  have hmean : ∀ R ∈ Homogenization.descendantsAtDepth Q j,
      Homogenization.volumeAverageVec (Homogenization.openCubeSet R) F - c =
        Homogenization.volumeAverageVec (Homogenization.openCubeSet R) G := by
    intro R hR
    let : MeasureTheory.IsFiniteMeasure
        (MeasureTheory.volume.restrict (Homogenization.openCubeSet R)) :=
      (Homogenization.isOpenBoundedConvexDomain_openCubeSet R).isFiniteMeasure_restrict_volume
    exact (volumeAverageVec_sub_const
      (fun i => (memL2On_component_of_memVectorL2 (hRmem R hR) i).integrable (by norm_num)) c).symm
  have hstep : ∀ R ∈ Homogenization.descendantsAtDepth Q j,
      ENNReal.ofReal (Homogenization.vecNormSq
        (Homogenization.volumeAverageVec (Homogenization.openCubeSet R) F - c) ^ (2 : ℕ)) ≤
      SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm R 4 G ^ (4 : ℕ) := by
    intro R hR
    rw [hmean R hR]
    exact ofReal_vecNormSq_volumeAverageVec_sq_le
      (memVectorL2_mono (Homogenization.openCubeSet_subset_of_mem_descendantsAtDepth hR) hG)
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ ((Homogenization.descendantsAtDepth Q j).card : ℝ)⁻¹),
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
  refine (mul_le_mul_right (Finset.sum_le_sum hstep) _).trans_eq ?_
  exact (cubeLpENorm_four_pow_eq_inv_card_mul_sum j (Homogenization.hilbertifyVecField G)).symm

/-- The scalar fourth-power Poincare estimate used for components of the
response gradient has one dimension-only constant and the exact cube scale. -/
theorem cgFinalE_scalar_poincare_four (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q : Homogenization.TriadicCube d)
      (u : Homogenization.H1Function (Homogenization.openCubeSet Q))
      (_hu : MeasureTheory.MemLp u.toFun 4
        (Homogenization.volumeMeasureOn (Homogenization.openCubeSet Q)))
      (_hgrad : ∀ i : Fin d, MeasureTheory.MemLp (fun x => u.grad x i) 4
        (Homogenization.volumeMeasureOn (Homogenization.openCubeSet Q))),
      (MeasureTheory.eLpNorm
          (fun x => u.toFun x - Homogenization.integralAverage (Homogenization.openCubeSet Q) u.toFun)
          4 (Homogenization.volumeMeasureOn (Homogenization.openCubeSet Q))).toReal ≤
        C * Homogenization.cubeScaleFactor Q *
          ∑ i : Fin d, (MeasureTheory.eLpNorm (fun x => u.grad x i) 4
            (Homogenization.volumeMeasureOn (Homogenization.openCubeSet Q))).toReal := by
  let E : Homogenization.W1pPoincareEstimate
      (Homogenization.openCubeSet (Homogenization.originCube d 0)) 4 := by
    simpa only [ENNReal.ofReal_ofNat] using Homogenization.w1pPoincareEstimate_of_isOpenBoundedConvexDomain
      (Homogenization.isOpenBoundedConvexDomain_openCubeSet (Homogenization.originCube d 0))
      (show (1 : ℝ) < 4 by norm_num)
  refine ⟨E.constant, E.constant_nonneg, ?_⟩
  intro Q u hu hgrad
  have hscale : 0 < Homogenization.cubeScaleFactor Q := by
    unfold Homogenization.cubeScaleFactor
    positivity
  obtain ⟨EQ, hEQ⟩ : ∃ EQ : Homogenization.W1pPoincareEstimate (Homogenization.openCubeSet Q) 4,
      EQ.constant = Homogenization.cubeScaleFactor Q * E.constant := by
    rw [Homogenization.openCubeSet_eq_translateSet_smul_originCube_zero]
    exact ⟨(E.dilate hscale (by norm_num)).translate (Homogenization.triadicCubeShift Q), rfl⟩
  let : MeasureTheory.IsFiniteMeasure
      (Homogenization.volumeMeasureOn (Homogenization.openCubeSet Q)) :=
    (Homogenization.isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  let v : Homogenization.W1pMeanZeroFunction (Homogenization.openCubeSet Q) 4 :=
    { toW1pFunction :=
        { toFun := u.subAverage.toFun
          grad := u.subAverage.grad
          memLp := by
            exact hu.sub (MeasureTheory.memLp_const
                (Homogenization.integralAverage (Homogenization.openCubeSet Q) u.toFun))
          gradMemLp := by
            intro i
            simpa only [Homogenization.H1Function.grad_subAverage] using hgrad i
          hasWeakGradient := u.subAverage.hasWeakGradient }
      meanZero := u.meanZeroOn_subAverage }
  have h := EQ.bound v
  rw [hEQ] at h
  simp only [v, Homogenization.W1pMeanZeroFunction.valueLpSeminorm,
    Homogenization.W1pFunction.valueLpSeminorm,
    Homogenization.W1pMeanZeroFunction.gradientCoordLpSeminormSum,
    Homogenization.W1pFunction.gradientCoordLpSeminormSum,
    Homogenization.W1pFunction.gradCoordLpSeminorm,
    Homogenization.H1Function.grad_subAverage,
    mul_comm (Homogenization.cubeScaleFactor Q) E.constant] at h ⊢
  exact h

/-- The vector fourth-power Poincare estimate, with a dimension-only constant,
for the components and weak derivatives of a response gradient. -/
theorem cgFinalE_vector_poincare_four (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q : Homogenization.TriadicCube d)
      (u : Fin d → Homogenization.H1Function (Homogenization.openCubeSet Q))
      (_hu : ∀ i, MeasureTheory.MemLp (u i).toFun 4
        (Homogenization.volumeMeasureOn (Homogenization.openCubeSet Q)))
      (_hgrad : ∀ i j, MeasureTheory.MemLp (fun x => (u i).grad x j) 4
        (Homogenization.volumeMeasureOn (Homogenization.openCubeSet Q))),
      (MeasureTheory.eLpNorm (fun x => Homogenization.HilbertVec.ofVec
        (fun i => (u i).toFun x - Homogenization.integralAverage
          (Homogenization.openCubeSet Q) (u i).toFun)) 4
        (Homogenization.volumeMeasureOn (Homogenization.openCubeSet Q))).toReal ≤
      C * Homogenization.cubeScaleFactor Q *
        (MeasureTheory.eLpNorm (fun x => Homogenization.HilbertMat.ofMat
          (fun i j => (u i).grad x j)) 4
          (Homogenization.volumeMeasureOn (Homogenization.openCubeSet Q))).toReal := by
  obtain ⟨C, hC, hscalar⟩ := cgFinalE_scalar_poincare_four d
  refine ⟨(d : ℝ) ^ 3 * C, mul_nonneg (pow_nonneg (Nat.cast_nonneg d) 3) hC, ?_⟩
  intro Q u hu hgrad
  let μ := Homogenization.volumeMeasureOn (Homogenization.openCubeSet Q)
  let R := fun x i => (u i).toFun x - Homogenization.integralAverage
    (Homogenization.openCubeSet Q) (u i).toFun
  let M := fun x => Homogenization.HilbertMat.ofMat (fun i j => (u i).grad x j)
  let : MeasureTheory.IsFiniteMeasure μ :=
    (Homogenization.isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hR : ∀ i, MeasureTheory.MemLp (fun x => R x i) 4 μ :=
    fun i => (hu i).sub (MeasureTheory.memLp_const _)
  have hM : MeasureTheory.MemLp M 4 μ := by
    rw [MeasureTheory.memLp_piLp_iff]
    intro i
    rw [MeasureTheory.memLp_piLp_iff]
    intro j
    exact hgrad i j
  have hvec := Homogenization.euclidean_eLpNorm_le_dimension_mul_sum_coordinates μ
    (⟨4, by norm_num, by norm_num⟩ : Homogenization.FiniteLpExponent) R
    (fun i => (hR i).aestronglyMeasurable)
  have hvecReal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top enorm_ne_top (ENNReal.sum_ne_top.mpr fun i _ => (hR i).eLpNorm_ne_top)) hvec
  have hvec' : (MeasureTheory.eLpNorm (fun x => Homogenization.HilbertVec.ofVec (R x)) 4 μ).toReal ≤
      (d : ℝ) * ∑ i, (MeasureTheory.eLpNorm (fun x => R x i) 4 μ).toReal := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_sum (fun i _ => (hR i).eLpNorm_ne_top),
      toReal_enorm, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ (d : ℝ))] using hvecReal
  have hentry : ∀ i j, (MeasureTheory.eLpNorm (fun x => (u i).grad x j) 4 μ).toReal ≤
      (MeasureTheory.eLpNorm M 4 μ).toReal := by
    intro i j
    apply ENNReal.toReal_mono hM.eLpNorm_ne_top
    refine MeasureTheory.eLpNorm_mono_ae (hgrad i j).aestronglyMeasurable ?_
    filter_upwards [] with x
    exact (PiLp.norm_apply_le ((M x).ofLp i) j).trans (PiLp.norm_apply_le (M x) i)
  have hscale : 0 ≤ C * Homogenization.cubeScaleFactor Q := by
    unfold Homogenization.cubeScaleFactor
    positivity
  have hcoord : ∀ i, (MeasureTheory.eLpNorm (fun x => R x i) 4 μ).toReal ≤
      C * Homogenization.cubeScaleFactor Q *
        ((d : ℝ) * (MeasureTheory.eLpNorm M 4 μ).toReal) := by
    intro i
    refine (hscalar Q (u i) (hu i) (hgrad i)).trans ?_
    apply mul_le_mul_of_nonneg_left _ hscale
    calc
      ∑ j, (MeasureTheory.eLpNorm (fun x => (u i).grad x j) 4 μ).toReal ≤
          ∑ _j : Fin d, (MeasureTheory.eLpNorm M 4 μ).toReal :=
        Finset.sum_le_sum fun j _ => hentry i j
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  refine hvec'.trans ?_
  calc
    (d : ℝ) * ∑ i, (MeasureTheory.eLpNorm (fun x => R x i) 4 μ).toReal ≤
        (d : ℝ) * ∑ _i : Fin d, C * Homogenization.cubeScaleFactor Q *
          ((d : ℝ) * (MeasureTheory.eLpNorm M 4 μ).toReal) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hcoord i) (Nat.cast_nonneg d)
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- The dimension-only fourth-power Poincare estimate in the volume-normalized
norms used by the coarse-block display. -/
theorem cgFinalE_normalized_poincare_four (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q : Homogenization.TriadicCube d)
      (u : Fin d → Homogenization.H1Function (Homogenization.openCubeSet Q))
      (_hu : ∀ i, MeasureTheory.MemLp (u i).toFun 4
        (Homogenization.volumeMeasureOn (Homogenization.openCubeSet Q)))
      (_hgrad : ∀ i j, MeasureTheory.MemLp (fun x => (u i).grad x j) 4
        (Homogenization.volumeMeasureOn (Homogenization.openCubeSet Q))),
      SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm Q 4
        (fun x i => (u i).toFun x - Homogenization.integralAverage
          (Homogenization.openCubeSet Q) (u i).toFun) ≤
      ENNReal.ofReal (C * Homogenization.cubeScaleFactor Q) *
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 4
          (fun x => Homogenization.HilbertMat.ofMat (fun i j => (u i).grad x j)) := by
  obtain ⟨C, hC, hvec⟩ := cgFinalE_vector_poincare_four d
  refine ⟨C, hC, ?_⟩
  intro Q u hu hgrad
  let μ := Homogenization.volumeMeasureOn (Homogenization.openCubeSet Q)
  let R := fun x i => (u i).toFun x - Homogenization.integralAverage
    (Homogenization.openCubeSet Q) (u i).toFun
  let M := fun x => Homogenization.HilbertMat.ofMat (fun i j => (u i).grad x j)
  let : MeasureTheory.IsFiniteMeasure μ :=
    (Homogenization.isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hR : MeasureTheory.MemLp (fun x => Homogenization.HilbertVec.ofVec (R x)) 4 μ := by
    rw [MeasureTheory.memLp_piLp_iff]
    intro i
    exact (hu i).sub (MeasureTheory.memLp_const _)
  have hM : MeasureTheory.MemLp M 4 μ := by
    rw [MeasureTheory.memLp_piLp_iff]
    intro i
    rw [MeasureTheory.memLp_piLp_iff]
    intro j
    exact hgrad i j
  have hscale : 0 ≤ C * Homogenization.cubeScaleFactor Q := by
    unfold Homogenization.cubeScaleFactor
    positivity
  have hENN : MeasureTheory.eLpNorm (fun x => Homogenization.HilbertVec.ofVec (R x)) 4 μ ≤
      ENNReal.ofReal (C * Homogenization.cubeScaleFactor Q) * MeasureTheory.eLpNorm M 4 μ := by
    rw [← ENNReal.ofReal_toReal hR.eLpNorm_ne_top,
      ← ENNReal.ofReal_toReal hM.eLpNorm_ne_top, ← ENNReal.ofReal_mul hscale]
    exact ENNReal.ofReal_le_ofReal (hvec Q u hu hgrad)
  unfold SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm
    SuperdiffusionCLT.Section2.Norms.cubeLpENorm
  rw [SuperdiffusionCLT.Section3.ResponseFields.normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet,
    MeasureTheory.eLpNorm_smul_measure_of_ne_top (by norm_num : (4 : ENNReal) ≠ ⊤)
      (Homogenization.hilbertifyVecField R) _ hR.aestronglyMeasurable,
    MeasureTheory.eLpNorm_smul_measure_of_ne_top (by norm_num : (4 : ENNReal) ≠ ⊤) _ _ hM.aestronglyMeasurable]
  exact (mul_le_mul_right hENN _).trans_eq (mul_left_comm _ _ _)

/-- The complete deterministic fourth-power mean-difference estimate preceding
the Hessian moment bound in the proof of `e.RHS.term3.A`. No Poincare estimate is assumed. -/
theorem cgFinalE_two_scale_poincare_four (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q : Homogenization.TriadicCube d) (j : ℕ)
      (u : Fin d → Homogenization.H1Function (Homogenization.openCubeSet Q))
      (_hu : ∀ i, MeasureTheory.MemLp (u i).toFun 4
        (Homogenization.volumeMeasureOn (Homogenization.openCubeSet Q)))
      (_hgrad : ∀ i k, MeasureTheory.MemLp (fun x => (u i).grad x k) 4
        (Homogenization.volumeMeasureOn (Homogenization.openCubeSet Q))),
      ENNReal.ofReal (((Homogenization.descendantsAtDepth Q j).card : ℝ)⁻¹ *
        ∑ R ∈ Homogenization.descendantsAtDepth Q j,
          Homogenization.vecNormSq
            (Homogenization.volumeAverageVec (Homogenization.openCubeSet R) (fun x i => (u i).toFun x) -
              Homogenization.volumeAverageVec (Homogenization.openCubeSet Q) (fun x i => (u i).toFun x)) ^ (2 : ℕ)) ≤
        ENNReal.ofReal (C * Homogenization.cubeScaleFactor Q) ^ (4 : ℕ) *
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 4
            (fun x => Homogenization.HilbertMat.ofMat (fun i k => (u i).grad x k)) ^ (4 : ℕ) := by
  obtain ⟨C, hC, hnorm⟩ := cgFinalE_normalized_poincare_four d
  refine ⟨C, hC, ?_⟩
  intro Q j u hu hgrad
  have hmem : Homogenization.MemVectorL2 (Homogenization.openCubeSet Q)
      (fun x i => (u i).toFun x) := MeasureTheory.MemLp.of_eval fun i => (u i).memL2
  have hjensen := cgFinalE_fourth_mean_difference Q j hmem
  have hpow := pow_le_pow_left' (hnorm Q u hu hgrad) 4
  rw [mul_pow] at hpow
  exact hjensen.trans hpow

end SuperdiffusionCLT.Section3.Terms
