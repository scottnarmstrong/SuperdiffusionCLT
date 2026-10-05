/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3CgFinalE
public import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.HessianGradientH1
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3CgAssemblyB

/-!
# Quantitative coarse-graining error

The exact residual in `RHSTerm3CgFinalE.lean` is

`hCerr : cgBoundConst (cgBoundAmpP d P S w) (cgBoundAmpW nu S) (bEllipConst d) ≤ Cerr`.

The bound occurs in the proof of `e.RHS.term3.A`.
`cgCerr_fourth_root_window` bounds that carrier with the regularity window
factor explicit. The final error envelope has a dimension-only constant,
obtained by absorbing the window factor before weakening the
one-third spatial rate to one-quarter. It does not assert a dimension-only
bound on the original normalized constant carrier.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

/-- The fourth-power Poincare estimate applied to the weak Hessian itself. -/
theorem cgCerr_hessian_poincare (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q : Homogenization.TriadicCube d) (j : ℕ)
      (u : Homogenization.H1Function (Homogenization.openCubeSet Q))
      (H : Homogenization.HasWeakHessianOn (Homogenization.openCubeSet Q) u)
      (_hu : ∀ i, MeasureTheory.MemLp (fun x => u.grad x i) 4
        (Homogenization.volumeMeasureOn (Homogenization.openCubeSet Q)))
      (_hH : ∀ i k, MeasureTheory.MemLp (H.hess i k) 4
        (Homogenization.volumeMeasureOn (Homogenization.openCubeSet Q))),
      ENNReal.ofReal (((Homogenization.descendantsAtDepth Q j).card : ℝ)⁻¹ *
        ∑ R ∈ Homogenization.descendantsAtDepth Q j,
          Homogenization.vecNormSq
            (Homogenization.volumeAverageVec (Homogenization.openCubeSet R) u.grad -
              Homogenization.volumeAverageVec (Homogenization.openCubeSet Q) u.grad) ^ (2 : ℕ)) ≤
        ENNReal.ofReal (C * Homogenization.cubeScaleFactor Q) ^ (4 : ℕ) *
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 4
            (fun x => Homogenization.HilbertMat.ofMat (fun i k => H.hess i k x)) ^ (4 : ℕ) := by
  obtain ⟨C, hC, hbound⟩ := cgFinalE_two_scale_poincare_four d
  exact ⟨C, hC, fun Q j u H hu hH => hbound Q j H.gradCoordH1Function hu hH⟩

/-- Summing the coarse-cube Poincare estimates gives the full nested spatial
average in the proof of `e.RHS.term3.A`, with no loss from the number of cubes. -/
theorem cgCerr_nested_hessian_poincare (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q : Homogenization.TriadicCube d) (a b : ℕ)
      (u : Homogenization.H1Function (Homogenization.openCubeSet Q))
      (H : Homogenization.HasWeakHessianOn (Homogenization.openCubeSet Q) u)
      (_hu : ∀ i, MeasureTheory.MemLp (fun x => u.grad x i) 4
        (Homogenization.volumeMeasureOn (Homogenization.openCubeSet Q)))
      (_hH : ∀ i k, MeasureTheory.MemLp (H.hess i k) 4
        (Homogenization.volumeMeasureOn (Homogenization.openCubeSet Q))),
      ENNReal.ofReal (((Homogenization.descendantsAtDepth Q a).card : ℝ)⁻¹ *
        ∑ R ∈ Homogenization.descendantsAtDepth Q a,
          ((Homogenization.descendantsAtDepth R b).card : ℝ)⁻¹ *
            ∑ T ∈ Homogenization.descendantsAtDepth R b,
              Homogenization.vecNormSq
                (Homogenization.volumeAverageVec (Homogenization.openCubeSet T) u.grad -
                  Homogenization.volumeAverageVec (Homogenization.openCubeSet R) u.grad) ^ (2 : ℕ)) ≤
        ENNReal.ofReal (C * (Homogenization.cubeScaleFactor Q / (3 : ℝ) ^ a)) ^ (4 : ℕ) *
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 4
            (fun x => Homogenization.HilbertMat.ofMat (fun i k => H.hess i k x)) ^ (4 : ℕ) := by
  obtain ⟨C, hC, hbound⟩ := cgCerr_hessian_poincare d
  refine ⟨C, hC, ?_⟩
  intro Q a b u H hu hH
  classical
  have hR : ∀ R ∈ Homogenization.descendantsAtDepth Q a,
      ENNReal.ofReal (((Homogenization.descendantsAtDepth R b).card : ℝ)⁻¹ *
        ∑ T ∈ Homogenization.descendantsAtDepth R b,
          Homogenization.vecNormSq
            (Homogenization.volumeAverageVec (Homogenization.openCubeSet T) u.grad -
              Homogenization.volumeAverageVec (Homogenization.openCubeSet R) u.grad) ^ (2 : ℕ)) ≤
        ENNReal.ofReal (C * (Homogenization.cubeScaleFactor Q / (3 : ℝ) ^ a)) ^ (4 : ℕ) *
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm R 4
            (fun x => Homogenization.HilbertMat.ofMat (fun i k => H.hess i k x)) ^ (4 : ℕ) := by
    intro R hR
    have hsub := Homogenization.openCubeSet_subset_of_mem_descendantsAtDepth hR
    have hmeasure := MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hsub
    have h := hbound R b (u.restrict (Homogenization.isOpen_openCubeSet R) hsub)
      (H.restrict (Homogenization.isOpen_openCubeSet R) hsub)
      (fun i => (hu i).mono_measure hmeasure) (fun i k => (hH i k).mono_measure hmeasure)
    rw [Homogenization.cubeScaleFactor_descendant_eq_div_pow hR] at h
    exact h
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ ((Homogenization.descendantsAtDepth Q a).card : ℝ)⁻¹),
    ENNReal.ofReal_sum_of_nonneg (fun R _ =>
      mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
        (Finset.sum_nonneg fun _ _ => sq_nonneg _))]
  refine (mul_le_mul_right (Finset.sum_le_sum hR) _).trans_eq ?_
  rw [← Finset.mul_sum, mul_left_comm,
    ← cubeLpENorm_four_pow_eq_inv_card_mul_sum]

private theorem cgCerr_memLp_continuous {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (Q : Homogenization.TriadicCube d) {q : ENNReal} {f : Homogenization.Vec d → E}
    (hf : Continuous f) : MeasureTheory.MemLp f q (Homogenization.normalizedCubeMeasure Q) := by
  rw [SuperdiffusionCLT.Section3.ResponseFields.normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
  let : MeasureTheory.IsFiniteMeasure
      (MeasureTheory.volume.restrict (Homogenization.openCubeSet Q)) :=
    (Homogenization.isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  apply MeasureTheory.MemLp.smul_measure _ ENNReal.ofReal_ne_top
  have hsub : Homogenization.openCubeSet Q ⊆
      Metric.closedBall (Homogenization.cubeCenter Q) (Homogenization.cubeRadius Q) := by
    rw [← Homogenization.ball_cubeCenter_eq_openCubeSet Q]
    exact Metric.ball_subset_closedBall
  have hK : IsCompact (Metric.closedBall (Homogenization.cubeCenter Q)
      (Homogenization.cubeRadius Q)) := ProperSpace.isCompact_closedBall _ _
  have hbdd := hK.bddAbove_image hf.norm.continuousOn
  refine MeasureTheory.MemLp.of_bound hf.aestronglyMeasurable
    (sSup ((fun y => ‖f y‖) ''
      Metric.closedBall (Homogenization.cubeCenter Q) (Homogenization.cubeRadius Q))) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem (Homogenization.isOpen_openCubeSet Q).measurableSet]
    with y hy
  exact le_csSup hbdd (Set.mem_image_of_mem _ (hsub hy))

private theorem cgCerr_memLp_volume {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (Q : Homogenization.TriadicCube d) {q : ENNReal} {f : Homogenization.Vec d → E}
    (hf : MeasureTheory.MemLp f q (Homogenization.normalizedCubeMeasure Q)) :
    MeasureTheory.MemLp f q (Homogenization.volumeMeasureOn (Homogenization.openCubeSet Q)) := by
  have h := hf.smul_measure (c := ENNReal.ofReal (Homogenization.cubeVolume Q)) ENNReal.ofReal_ne_top
  rw [SuperdiffusionCLT.Section3.ResponseFields.normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet,
    smul_smul, ← ENNReal.ofReal_mul (Homogenization.cubeVolume_pos Q).le,
    mul_inv_cancel₀ (Homogenization.cubeVolume_pos Q).ne', ENNReal.ofReal_one, one_smul] at h
  exact h

/-- Both fourth-power membership conditions needed by spatial Poincare follow
from the response equation and the smooth finite-cutoff forcing. -/
theorem cgCerr_response_four_membership {d : ℕ} (hd : 2 ≤ d)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) {LPrime ellPrime m : ℕ}
    (hab : ellPrime ≤ LPrime) (p : Homogenization.Vec d)
    (w : Homogenization.H10Function (Homogenization.openCubeSet (Homogenization.originCube d (m : ℤ))))
    (hw : SuperdiffusionCLT.Section3.Setup.IsDirichletResponse omega LPrime ellPrime m p w) :
    ∃ H : Homogenization.HasWeakHessianOn
        (Homogenization.openCubeSet (Homogenization.originCube d (m : ℤ))) w.toH1Function,
      (∀ i, MeasureTheory.MemLp (fun x => w.toH1Function.grad x i) 4
        (Homogenization.volumeMeasureOn (Homogenization.openCubeSet (Homogenization.originCube d (m : ℤ))))) ∧
      (∀ i j, MeasureTheory.MemLp (H.hess i j) 4
        (Homogenization.volumeMeasureOn (Homogenization.openCubeSet (Homogenization.originCube d (m : ℤ))))) := by
  obtain ⟨_C, _hC, hess⟩ := SuperdiffusionCLT.Sobolev.exists_cubeDirichletResponseHessianLpEstimate
    hd 4 (by norm_num) (by norm_num)
  have hflux := SuperdiffusionCLT.Section3.Setup.continuous_dirichletRhsField omega LPrime ellPrime p
  have hjac := SuperdiffusionCLT.Section3.ResponseFields.continuous_streamFluxJacobian omega hab p
  have hresponse := (SuperdiffusionCLT.Section3.Setup.isDirichletResponse_iff_isCubeDirichletResponse
    omega LPrime ellPrime m p w).mp hw
  obtain ⟨H, hH, _⟩ := hess (m : ℤ)
    (SuperdiffusionCLT.Section3.Setup.dirichletRhsField omega LPrime ellPrime p)
    (SuperdiffusionCLT.Section3.ResponseFields.streamFluxWeakGradient omega ellPrime LPrime p)
    (cgCerr_memLp_continuous _ hflux)
    (fun i => SuperdiffusionCLT.Section3.ResponseFields.hasWeakGradientOn_streamFluxWeakGradient
      omega hab p i (Homogenization.openCubeSet (Homogenization.originCube d (m : ℤ))))
    (cgCerr_memLp_continuous _ hjac) (cgCerr_memLp_continuous _ hjac) w hresponse
  obtain ⟨_Cg, _hCg, grad⟩ := SuperdiffusionCLT.Section3.ResponseFields.exists_cubeResponseGradientLpEstimate
    hd 4 (by norm_num) (by norm_num)
  have hfluxHilbert : Continuous (Homogenization.hilbertifyVecField
      (SuperdiffusionCLT.Section3.Setup.dirichletRhsField omega LPrime ellPrime p)) :=
    SuperdiffusionCLT.Section2.Estimates.Stream.continuous_hilbertifyVecField hflux
  have hgrad := (grad (Homogenization.originCube d (m : ℤ)) _
    (cgCerr_memLp_continuous _ hfluxHilbert)).1 w hresponse
  have hgradvol := cgCerr_memLp_volume _ hgrad.1
  have hHvol := cgCerr_memLp_volume _ hH
  refine ⟨H, ?_, ?_⟩
  · rw [MeasureTheory.memLp_piLp_iff] at hgradvol
    exact hgradvol
  · rw [MeasureTheory.memLp_piLp_iff] at hHvol
    intro i
    have hi := hHvol i
    rw [MeasureTheory.memLp_piLp_iff] at hi
    exact hi

/-- The deterministic fourth-moment bound at the exact coarse-pair carrier. -/
theorem cgCerr_coarse_pairs_hessian (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n k m : ℕ) (_hnk : n ≤ k) (_hkm : k ≤ m)
      (u : Homogenization.H1Function (Homogenization.openCubeSet (Homogenization.originCube d (m : ℤ))))
      (H : Homogenization.HasWeakHessianOn
        (Homogenization.openCubeSet (Homogenization.originCube d (m : ℤ))) u)
      (_hu : ∀ i, MeasureTheory.MemLp (fun x => u.grad x i) 4
        (Homogenization.volumeMeasureOn (Homogenization.openCubeSet (Homogenization.originCube d (m : ℤ)))))
      (_hH : ∀ i j, MeasureTheory.MemLp (H.hess i j) 4
        (Homogenization.volumeMeasureOn (Homogenization.openCubeSet (Homogenization.originCube d (m : ℤ))))),
      ENNReal.ofReal (((coarsePairs d n k m).card : ℝ)⁻¹ *
        ∑ q ∈ coarsePairs d n k m,
          Homogenization.vecNormSq
            (Homogenization.volumeAverageVec (Homogenization.openCubeSet q.2) u.grad -
              Homogenization.volumeAverageVec (Homogenization.openCubeSet q.1) u.grad) ^ (2 : ℝ)) ≤
        ENNReal.ofReal (C * (3 : ℝ) ^ (k : ℝ)) ^ (4 : ℕ) *
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm (Homogenization.originCube d (m : ℤ)) 4
            (fun x => Homogenization.HilbertMat.ofMat (fun i j => H.hess i j x)) ^ (4 : ℕ) := by
  obtain ⟨C, hC, hbound⟩ := cgCerr_nested_hessian_poincare d
  refine ⟨C, hC, ?_⟩
  intro n k m hnk hkm u H hu hH
  have hscale : Homogenization.cubeScaleFactor (Homogenization.originCube d (m : ℤ)) /
      (3 : ℝ) ^ (m - k) = (3 : ℝ) ^ (k : ℝ) := by
    change (3 : ℝ) ^ (m : ℤ) / (3 : ℝ) ^ (m - k) = (3 : ℝ) ^ (k : ℝ)
    rw [zpow_natCast]
    rw [div_eq_mul_inv, ← pow_sub₀ (3 : ℝ) (by norm_num : (3 : ℝ) ≠ 0) (Nat.sub_le m k), Nat.sub_sub_self hkm,
      Real.rpow_natCast]
  have h := hbound (Homogenization.originCube d (m : ℤ)) (m - k) (k - n) u H hu hH
  rw [hscale] at h
  rw [avsum_coarsePairs_eq_double_avsum hnk hkm (fun R T =>
    Homogenization.vecNormSq
      (Homogenization.volumeAverageVec (Homogenization.openCubeSet T) u.grad -
        Homogenization.volumeAverageVec (Homogenization.openCubeSet R) u.grad) ^ (2 : ℝ))]
  simpa only [largeCubeSubcubes_eq_descendantsAtDepth,
    Real.rpow_two] using h

/-- The fourth moment of the actual coarse-pair observable is controlled by
an actual weak Hessian of the response, with all spatial membership conditions
proved from the response equation. -/
theorem cgCerr_annealed_poincare (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {nu : ℝ} (_hnu : 0 < nu) (_hnu1 : nu ≤ 1)
      {P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)}
      (_hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
      (_hJ1V2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P)
      (_hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
      (_hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
      (_hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
      (S : SuperdiffusionCLT.Section3.Setup.ScaleSelection)
      (_hS : SuperdiffusionCLT.Section3.Setup.ScalesOrdering S)
      {e : Homogenization.Vec d} (_he : Homogenization.vecNormSq e = 1)
      (w : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d →
        Homogenization.H10Function (Homogenization.openCubeSet (Homogenization.originCube d (S.m : ℤ))))
      (_hw : ∀ omega, SuperdiffusionCLT.Section3.Setup.IsDirichletResponse
        omega S.LPrime S.ellPrime S.m
        (SuperdiffusionCLT.Section3.Setup.testVector nu S.LPrime P S.n e) (w omega)),
      ∃ H : ∀ omega, Homogenization.HasWeakHessianOn
          (Homogenization.openCubeSet (Homogenization.originCube d (S.m : ℤ))) (w omega).toH1Function,
        ENNReal.ofReal (cgPoincareCarrier d P S w) ≤
          ENNReal.ofReal (C * (3 : ℝ) ^ (coarseBlockScale d S : ℝ)) ^ (4 : ℕ) *
            ∫⁻ omega, SuperdiffusionCLT.Section2.Norms.cubeLpENorm
              (Homogenization.originCube d (S.m : ℤ)) 4
              (fun x => Homogenization.HilbertMat.ofMat (fun i j => (H omega).hess i j x)) ^ (4 : ℕ)
              ∂P.toMeasure := by
  obtain ⟨C, hC, hbound⟩ := cgCerr_coarse_pairs_hessian d
  refine ⟨C, hC, ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hS e he w hw
  have hab : S.ellPrime ≤ S.LPrime := by
    have h1 := S.ellPrime_add_h
    have h2 := S.LPrime_eq
    omega
  choose H hgrad hhess using fun omega => cgCerr_response_four_membership hd omega hab
    (SuperdiffusionCLT.Section3.Setup.testVector nu S.LPrime P S.n e) (w omega) (hw omega)
  refine ⟨H, ?_⟩
  have hscales := coarse_block_scale_choice d S hS.ell_lt_ellPrime.le
  have hnk : S.n ≤ coarseBlockScale d S := hS.n_lt_ell.le.trans hscales.1
  have hkm : coarseBlockScale d S ≤ S.m := hscales.2.1.trans hS.ellPrime_lt_m.le
  let f := fun omega => ((coarsePairs d S.n (coarseBlockScale d S) S.m).card : ℝ)⁻¹ *
    ∑ q ∈ coarsePairs d S.n (coarseBlockScale d S) S.m,
      Homogenization.vecNormSq
        (Homogenization.volumeAverageVec (Homogenization.openCubeSet q.2) (w omega).toH1Function.grad -
          Homogenization.volumeAverageVec (Homogenization.openCubeSet q.1) (w omega).toH1Function.grad) ^ (2 : ℝ)
  have hfnn : ∀ omega, 0 ≤ f omega := by
    intro omega
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (Homogenization.vecNormSq_nonneg _) _)
  rw [cgFinalD_poincareCarrier_eq_integral hd hnu hnu1 hPrefix hJ1V2 hJ2 hJ3 hJ4 S hS he w hw]
  change ENNReal.ofReal (∫ omega, f omega ∂P.toMeasure) ≤ _
  calc
    ENNReal.ofReal (∫ omega, f omega ∂P.toMeasure) = ‖∫ omega, f omega ∂P.toMeasure‖ₑ :=
      (Real.enorm_eq_ofReal (MeasureTheory.integral_nonneg hfnn)).symm
    _ ≤ ∫⁻ omega, ‖f omega‖ₑ ∂P.toMeasure := MeasureTheory.enorm_integral_le_lintegral_enorm f
    _ = ∫⁻ omega, ENNReal.ofReal (f omega) ∂P.toMeasure := by
      apply MeasureTheory.lintegral_congr
      intro omega
      exact Real.enorm_eq_ofReal (hfnn omega)
    _ ≤ ∫⁻ omega, ENNReal.ofReal (C * (3 : ℝ) ^ (coarseBlockScale d S : ℝ)) ^ (4 : ℕ) *
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm (Homogenization.originCube d (S.m : ℤ)) 4
          (fun x => Homogenization.HilbertMat.ofMat (fun i j => (H omega).hess i j x)) ^ (4 : ℕ)
        ∂P.toMeasure := by
      apply MeasureTheory.lintegral_mono
      intro omega
      exact hbound S.n (coarseBlockScale d S) S.m hnk hkm (w omega).toH1Function
        (H omega) (hgrad omega) (hhess omega)
    _ = _ := MeasureTheory.lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)

private theorem cgCerr_envelope_four_finite {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {N : Ω → ENNReal} {Z : Ω → ℝ} {A : ℝ} (hA : 0 < A)
    (hZmeas : AEMeasurable Z μ)
    (hZ : Homogenization.IndependentSums.IsBigO μ
      (Homogenization.IndependentSums.gammaSigma 2) Z A)
    (hbound : ∀ omega, N omega ≤ ENNReal.ofReal (Z omega)) :
    (∫⁻ omega, N omega ^ (4 : ℕ) ∂μ) ≠ ⊤ := by
  have hint := SuperdiffusionCLT.Probability.integrable_abs_rpow_of_isBigO_gammaSigma_two
    hA hZmeas hZ 4
  norm_num only [Nat.cast_ofNat] at hint
  have hmajor : (∫⁻ omega, N omega ^ (4 : ℕ) ∂μ) ≤
      ENNReal.ofReal (∫ omega, |Z omega| ^ (4 : ℝ) ∂μ) := by
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun omega => Real.rpow_nonneg (abs_nonneg (Z omega)) 4)]
    apply MeasureTheory.lintegral_mono
    intro omega
    calc
      _ ≤ ENNReal.ofReal |Z omega| ^ (4 : ℕ) :=
        pow_le_pow_left' ((hbound omega).trans (ENNReal.ofReal_le_ofReal (le_abs_self _))) 4
      _ = _ := by rw [← ENNReal.ofReal_pow (abs_nonneg _), ← Real.rpow_natCast]; norm_num
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmajor

/-- The quantitative fourth-root estimate obtained from the regularity
bounds, with their window factor stated explicitly. -/
theorem cgCerr_fourth_root_window (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {nu : ℝ} (_hnu : 0 < nu) (_hnu1 : nu ≤ 1)
      {P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)}
      (_hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
      (_hJ1V2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P)
      (_hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
      (_hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
      (_hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
      (S : SuperdiffusionCLT.Section3.Setup.ScaleSelection)
      (_hS : SuperdiffusionCLT.Section3.Setup.ScalesOrdering S)
      {e : Homogenization.Vec d} (_he : Homogenization.vecNormSq e = 1)
      (w : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d →
        Homogenization.H10Function (Homogenization.openCubeSet (Homogenization.originCube d (S.m : ℤ))))
      (_hw : ∀ omega, SuperdiffusionCLT.Section3.Setup.IsDirichletResponse
        omega S.LPrime S.ellPrime S.m
        (SuperdiffusionCLT.Section3.Setup.testVector nu S.LPrime P S.n e) (w omega)),
      cgPoincareCarrier d P S w ^ ((1 : ℝ) / 4) ≤
        C * (1 + (S.h : ℝ)) ^ ((1 : ℝ) / 2) *
          (3 : ℝ) ^ ((coarseBlockScale d S : ℝ) - (S.ellPrime : ℝ)) *
            nu ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨Cp, hCp, hpoincare⟩ := cgCerr_annealed_poincare d hd
  obtain ⟨Cw, hCw, hmoment⟩ := hNablawFour_of_window d hd
  obtain ⟨Cr, hCr, hreg⟩ := SuperdiffusionCLT.Section3.ResponseFields.l_w_basic_regbounds_window d hd
  refine ⟨Cp * Cw, mul_nonneg hCp hCw, ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hS e he w hw
  obtain ⟨H, hH⟩ := hpoincare hnu hnu1 hPrefix hJ1V2 hJ2 hJ3 hJ4 S hS he w hw
  let N := fun omega => SuperdiffusionCLT.Section2.Norms.cubeLpENorm
    (Homogenization.originCube d (S.m : ℤ)) 8
      (fun x => Homogenization.HilbertMat.ofMat (fun i j => (H omega).hess i j x))
  have hpoint : ∀ omega,
      SuperdiffusionCLT.Section2.Norms.cubeLpENorm (Homogenization.originCube d (S.m : ℤ)) 4
        (fun x => Homogenization.HilbertMat.ofMat (fun i j => (H omega).hess i j x)) ≤ N omega := by
    intro omega
    have hmem := memLp_hessMat_of_weakHessian (Homogenization.originCube d (S.m : ℤ)) (H omega)
    have hmeas : MeasureTheory.AEStronglyMeasurable
        (fun x => Homogenization.HilbertMat.ofMat (fun i j => (H omega).hess i j x))
        (Homogenization.normalizedCubeMeasure (Homogenization.originCube d (S.m : ℤ))) := by
      rw [SuperdiffusionCLT.Section3.ResponseFields.normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
      exact (hmem.smul_measure ENNReal.ofReal_ne_top).aestronglyMeasurable
    exact cubeLpENorm_mono_exponent _ (by norm_num) hmeas
  have hH8 := hH.trans (mul_le_mul_right (MeasureTheory.lintegral_mono
    (fun omega => pow_le_pow_left' (hpoint omega) 4)) _)
  obtain ⟨_, hregH, _⟩ := hreg nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hS e he
    (SuperdiffusionCLT.Section3.Setup.testVector nu S.LPrime P S.n e) rfl w hw
  obtain ⟨Z, hZm, hZ, hZbound⟩ := hregH H
  have hp : 0 < Homogenization.vecNormSq
      (SuperdiffusionCLT.Section3.Setup.testVector nu S.LPrime P S.n e) := by
    rw [SuperdiffusionCLT.Section3.Setup.vecNormSq_testVector hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n he]
    exact SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq_pos
      hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n
  have hA : 0 < Cr * (Real.sqrt (Homogenization.vecNormSq
      (SuperdiffusionCLT.Section3.Setup.testVector nu S.LPrime P S.n e)) *
      (Real.sqrt (1 + (S.h : ℝ)) * (3 : ℝ) ^ (-(S.ellPrime : ℝ)))) := by
    have hc : 0 < Cr := lt_of_lt_of_le zero_lt_one hCr
    have hs := Real.sqrt_pos.mpr hp
    positivity
  have hfin : (∫⁻ omega, N omega ^ (4 : ℕ) ∂P.toMeasure) ≠ ⊤ :=
    cgCerr_envelope_four_finite hA hZm.aemeasurable hZ hZbound
  have hr := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hfin) hH8
  have hscale : 0 ≤ Cp * (3 : ℝ) ^ (coarseBlockScale d S : ℝ) := by positivity
  rw [ENNReal.toReal_ofReal (cgPoincareCarrier_nonneg d P S w), ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hscale] at hr
  have hroot := Real.rpow_le_rpow (cgPoincareCarrier_nonneg d P S w) hr
    (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 4)
  rw [Real.mul_rpow (pow_nonneg hscale 4) ENNReal.toReal_nonneg,
    ← Real.rpow_natCast (Cp * (3 : ℝ) ^ (coarseBlockScale d S : ℝ)) 4,
    ← Real.rpow_mul hscale, show ((4 : ℕ) : ℝ) * (1 / 4) = 1 by norm_num, Real.rpow_one] at hroot
  have hm := hmoment nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hS e he
    (SuperdiffusionCLT.Section3.Setup.testVector nu S.LPrime P S.n e) rfl w hw H
  refine hroot.trans ((mul_le_mul_of_nonneg_left hm hscale).trans_eq ?_)
  rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 3),
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
  ring

end SuperdiffusionCLT.Section3.Terms
