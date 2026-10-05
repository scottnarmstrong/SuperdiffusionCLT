/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Coupled.Pointwise
public import SuperdiffusionCLT.Section5.Coupled.RemainderB
public import SuperdiffusionCLT.Section3.Terms.MaximizerGradientL2
public import SuperdiffusionCLT.Section3.Setup.WholeSpaceEnergyD
public import SuperdiffusionCLT.Assumptions.ShellLaw.Nonvacuity

@[expose] public section

namespace SuperdiffusionCLT.Section5
open Homogenization Homogenization.Book.Ch02 MeasureTheory
open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)
open SuperdiffusionCLT.Section2.Cutoff
open scoped ENNReal
variable {d : ℕ}

theorem coupled3_volume_open_ne (Q : TriadicCube d) :
    (volume (openCubeSet Q)).toReal ≠ 0 := by
  rw [volume_openCubeSet_toReal]; exact (cubeVolume_pos Q).ne'

theorem coupled3_volume_open_ne_top (Q : TriadicCube d) : volume (openCubeSet Q) ≠ ⊤ := by
  rw [volume_openCubeSet_eq_volume_cubeSet]; exact (volume_cubeSet_lt_top Q).ne

theorem coupled3_integrableOn_comp {Q : TriadicCube d} {F : Vec d → Vec d}
    (hF : MemVectorL2 (openCubeSet Q) F) (i : Fin d) :
    IntegrableOn (fun x => F x i) (openCubeSet Q) := by
  have : IsFiniteMeasure (volume.restrict (openCubeSet Q)) :=
    ⟨by simpa [Measure.restrict_apply_univ] using (coupled3_volume_open_ne_top Q).lt_top⟩
  exact ((memLp_pi_iff.mp hF) i).integrable one_le_two

theorem coupled3_integrableOn_comp_mul {Q : TriadicCube d} {F : Vec d → Vec d}
    (hF : MemVectorL2 (openCubeSet Q) F) (i : Fin d) :
    IntegrableOn (fun x => F x i * F x i) (openCubeSet Q) := by
  exact (((memLp_pi_iff.mp hF) i).integrable_sq).congr
    (Filter.Eventually.of_forall fun x => by simp [sq])

theorem coupled3_integrableOn_vecNormSq {Q : TriadicCube d} {F : Vec d → Vec d}
    (hF : MemVectorL2 (openCubeSet Q) F) :
    IntegrableOn (fun x => vecNormSq (F x)) (openCubeSet Q) := by
  unfold vecNormSq vecDot
  exact integrable_finsetSum _ fun i _ => coupled3_integrableOn_comp_mul hF i

theorem coupled3_jensen {Q : TriadicCube d} {F : Vec d → Vec d}
    (hF : MemVectorL2 (openCubeSet Q) F) :
    vecNormSq (volumeAverageVec (openCubeSet Q) F) ≤
      volumeAverage (openCubeSet Q) (fun x => vecNormSq (F x)) :=
  coupled_vecNormSq_volumeAverageVec_le (coupled3_volume_open_ne Q) (coupled3_volume_open_ne_top Q)
    (coupled3_integrableOn_comp hF) (coupled3_integrableOn_comp_mul hF)

theorem coupled3_va_affine {U : Set (Vec d)} (hV : (volume U).toReal ≠ 0)
    (hVt : volume U ≠ ⊤) {a b : Vec d → ℝ}
    (ha : IntegrableOn a U) (hb : IntegrableOn b U) (c : ℝ) :
    volumeAverage U (fun x => 1 + c ^ 2 * a x - 2 * c * b x) =
      1 + c ^ 2 * volumeAverage U a - 2 * c * volumeAverage U b := by
  have h : (fun x => 1 + c ^ 2 * a x - 2 * c * b x) =
      ((fun _ => (1 : ℝ)) + (c ^ 2) • a) - (2 * c) • b := by
    funext x; simp
  have h1 : IntegrableOn (fun _ : Vec d => (1 : ℝ)) U := integrableOn_const hVt
  rw [h, volumeAverage_sub (h1.add (ha.smul _)) (hb.smul _), volumeAverage_add h1 (ha.smul _),
    volumeAverage_smul, volumeAverage_smul, volumeAverage_const hV]

theorem coupled3_memL2_gauge {Q : TriadicCube d} {F : Vec d → Vec d} (e : Vec d) (c : ℝ)
    (hF : MemVectorL2 (openCubeSet Q) F) :
    MemVectorL2 (openCubeSet Q) (fun x => e - c • F x) := by
  have : IsFiniteMeasure (volume.restrict (openCubeSet Q)) :=
    ⟨by simpa [Measure.restrict_apply_univ] using (coupled3_volume_open_ne_top Q).lt_top⟩
  exact (memLp_const e).sub (hF.const_smul c)

/-- The average of `|g|^2 + |e - c F|^2` with `|e| = 1`. -/
theorem coupled3_avg_f {Q : TriadicCube d} {e : Vec d} (he : vecNormSq e = 1) (c : ℝ)
    {g F : Vec d → Vec d} (hg : MemVectorL2 (openCubeSet Q) g)
    (hF : MemVectorL2 (openCubeSet Q) F) :
    volumeAverage (openCubeSet Q) (fun x => vecNormSq (g x) + vecNormSq (e - c • F x)) =
      volumeAverage (openCubeSet Q) (fun x => vecNormSq (g x)) +
        (1 + c ^ 2 * volumeAverage (openCubeSet Q) (fun x => vecNormSq (F x)) -
          2 * c * volumeAverage (openCubeSet Q) (fun x => vecDot e (F x))) := by
  have hV := coupled3_volume_open_ne Q
  have hVt := coupled3_volume_open_ne_top Q
  have hFi := coupled3_integrableOn_comp hF
  have hnF := coupled3_integrableOn_vecNormSq hF
  have hng := coupled3_integrableOn_vecNormSq hg
  have hdot : IntegrableOn (fun x => vecDot e (F x)) (openCubeSet Q) := by
    unfold vecDot
    exact integrable_finsetSum _ fun i _ => (hFi i).const_mul (e i)
  have hpt : ∀ x, vecNormSq (e - c • F x) =
      1 + c ^ 2 * vecNormSq (F x) - 2 * c * vecDot e (F x) := by
    intro x
    rw [coupled3_vecNormSq_sub_smul, he]
    rfl
  have hGint : IntegrableOn (fun x => 1 + c ^ 2 * vecNormSq (F x) - 2 * c * vecDot e (F x))
      (openCubeSet Q) := by
    have h1 : IntegrableOn (fun _ : Vec d => (1 : ℝ)) (openCubeSet Q) := integrableOn_const hVt
    exact (h1.add (hnF.const_mul _)).sub (hdot.const_mul _)
  have h2 := coupled3_va_affine hV hVt hnF hdot c
  have h3 := volumeAverage_add (U := openCubeSet Q) hng
    (f := fun x => vecNormSq (g x))
    (g := fun x => 1 + c ^ 2 * vecNormSq (F x) - 2 * c * vecDot e (F x)) hGint
  simp only [hpt]
  rw [← h2]
  exact h3

/-- Box step of `e.coupled.bulk`: Jensen on the two bulk terms, rewritten with `|e| = 1`. -/
theorem coupled3_box_le {Q : TriadicCube d} {e : Vec d} (he : vecNormSq e = 1) (c : ℝ)
    {g F : Vec d → Vec d} (hg : MemVectorL2 (openCubeSet Q) g)
    (hF : MemVectorL2 (openCubeSet Q) F) :
    1 + vecNormSq (volumeAverageVec (openCubeSet Q) g) +
        c ^ 2 * vecNormSq (volumeAverageVec (openCubeSet Q) F) -
        2 * c * ∑ i, e i * volumeAverageVec (openCubeSet Q) F i ≤
      volumeAverage (openCubeSet Q) (fun x => vecNormSq (g x) + vecNormSq (e - c • F x)) := by
  have hFi := coupled3_integrableOn_comp hF
  have hdotavg : volumeAverage (openCubeSet Q) (fun x => vecDot e (F x)) =
      ∑ i, e i * volumeAverageVec (openCubeSet Q) F i :=
    volumeAverage_vecDot_left e F hFi
  rw [coupled3_avg_f he c hg hF, hdotavg]
  have j1 := coupled3_jensen hg
  have j2 := coupled3_jensen hF
  have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
  linarith only [j1, mul_le_mul_of_nonneg_left j2 hc2]

theorem coupledB_eq_open (m h : ℕ) (Q : TriadicCube d) (omega : ShellSeq d) (gD : Vec d → Vec d) :
    coupledB m h Q omega gD = volumeAverageVec (openCubeSet Q)
      (fun x => matVecMul (finiteShellIncrement omega (m - h) m x) (gD x)) := by
  funext i
  simp only [coupledB, volumeAverageVec, volumeAverage, volume_openCubeSet_eq_volume_cubeSet]
  rw [MeasureTheory.setIntegral_congr_set (cubeSet_ae_eq_openCubeSet Q)]

theorem coupled3_continuous_entry (omega : ShellSeq d) (l L : ℕ) (i j : Fin d) :
    Continuous (fun x => finiteShellIncrement omega l L x i j) :=
  continuous_finiteShellIncrement_entry omega l L i j

/-- The energy identity `e.setup.w-energy` for a cube Dirichlet response of `hshellFlux`:
`⨍ |∇w|² = σ⁻¹ ⨍ e · hshell ∇w`. -/
theorem coupled3_energy [NeZero d] (nu : ℝ)
    (P : MeasureTheory.ProbabilityMeasure (ShellSeq d)) (m h Kc : ℕ) (omega : ShellSeq d)
    (e : Vec d) (w : H10Function (openCubeSet (originCube d (Kc : ℤ))))
    (hw : SuperdiffusionCLT.Section3.ResponseFields.IsCubeDirichletResponse
      (originCube d (Kc : ℤ)) (hshellFlux nu P m h omega e) w) :
    volumeAverage (openCubeSet (originCube d (Kc : ℤ)))
        (fun x => vecNormSq (w.toH1Function.grad x)) =
      (sigmaBarInfinite nu (m - h) P)⁻¹ *
        volumeAverage (openCubeSet (originCube d (Kc : ℤ)))
          (fun x => vecDot e (matVecMul (finiteShellIncrement omega (m - h) m x)
            (w.toH1Function.grad x))) := by
  have h1 := hw w
  have hpt : ∀ x, vecDot (hshellFlux nu P m h omega e x) (w.toH1Function.grad x) =
      -((sigmaBarInfinite nu (m - h) P)⁻¹ * vecDot e (matVecMul (finiteShellIncrement omega (m - h) m x)
        (w.toH1Function.grad x))) := by
    intro x
    have hH : matVecMul (SuperdiffusionCLT.Frozen.Section2.streamCutoff omega m x -
        SuperdiffusionCLT.Frozen.Section2.streamCutoff omega (m - h) x) e =
        matVecMul (finiteShellIncrement omega (m - h) m x) e := by
      rw [finiteShellIncrement_apply_eq_streamCutoff_sub omega (Nat.sub_le m h) x]
    have hsk := finiteShellIncrement_skew omega (m - h) m x
    have hsk' : matTranspose (finiteShellIncrement omega (m - h) m x) =
        -finiteShellIncrement omega (m - h) m x := hsk
    have h2 := vecDot_matVecMul_transpose e (w.toH1Function.grad x)
      (finiteShellIncrement omega (m - h) m x)
    have hneg : matVecMul (-finiteShellIncrement omega (m - h) m x) (w.toH1Function.grad x) =
        -matVecMul (finiteShellIncrement omega (m - h) m x) (w.toH1Function.grad x) := by
      funext i
      simp [matVecMul, Finset.sum_neg_distrib]
    rw [hsk', hneg, vecDot_neg_right] at h2
    unfold hshellFlux
    rw [hH, vecDot_smul_left, ← h2]
    ring
  simp only [hpt] at h1
  unfold volumeAverage
  rw [integral_neg] at h1
  have h3 : ∫ x in openCubeSet (originCube d (Kc : ℤ)), vecNormSq (w.toH1Function.grad x) =
      ∫ x in openCubeSet (originCube d (Kc : ℤ)), (sigmaBarInfinite nu (m - h) P)⁻¹ *
        vecDot e (matVecMul (finiteShellIncrement omega (m - h) m x) (w.toH1Function.grad x)) := by
    rw [neg_neg] at h1
    exact h1
  rw [h3, integral_const_mul]
  ring

theorem coupled3_ofReal_box_le {Q : TriadicCube d} {e : Vec d} (he : vecNormSq e = 1) (c : ℝ)
    {g F : Vec d → Vec d} (hg : MemVectorL2 (openCubeSet Q) g)
    (hF : MemVectorL2 (openCubeSet Q) F) :
    ENNReal.ofReal (1 + vecNormSq (volumeAverageVec (openCubeSet Q) g) +
        c ^ 2 * vecNormSq (volumeAverageVec (openCubeSet Q) F) -
        2 * c * ∑ i, e i * volumeAverageVec (openCubeSet Q) F i) ≤
      ∫⁻ x, ENNReal.ofReal (vecNormSq (g x) + vecNormSq (e - c • F x))
        ∂normalizedCubeMeasure Q := by
  have hint : Integrable (fun x => vecNormSq (g x) + vecNormSq (e - c • F x))
      (normalizedCubeMeasure Q) :=
    (SuperdiffusionCLT.Section3.ResponseFields.integrable_vecNormSq_normalizedCubeMeasure hg).add
      (SuperdiffusionCLT.Section3.ResponseFields.integrable_vecNormSq_normalizedCubeMeasure
        (coupled3_memL2_gauge e c hF))
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun x => add_nonneg (vecNormSq_nonneg _) (vecNormSq_nonneg _)),
    SuperdiffusionCLT.Section3.Setup.integral_normalizedCubeMeasure_eq_volumeAverage]
  exact ENNReal.ofReal_le_ofReal (coupled3_box_le he c hg hF)

/-- `e.coupled.bulk`, one shell sequence: the box average of
`1 + |e_{D,z}|² + σ⁻² |B_z|² - 2σ⁻¹ e·B_z` plus the energy `‖∇w‖²_{L̲²(cu_K)}` is at most
`1 + σ⁻² ‖hshell ∇w‖²_{L̲²(cu_K)}`. -/
theorem coupled_bulk_det [NeZero d] (nu : ℝ)
    (P : MeasureTheory.ProbabilityMeasure (ShellSeq d)) (m h Kc n : ℕ) (hn : n ≤ Kc)
    (omega : ShellSeq d) (e : Vec d) (he : vecNormSq e = 1)
    (w : H10Function (openCubeSet (originCube d (Kc : ℤ))))
    (hw : SuperdiffusionCLT.Section3.ResponseFields.IsCubeDirichletResponse
      (originCube d (Kc : ℤ)) (hshellFlux nu P m h omega e) w) :
    subcubeAvg Kc n (fun Q => ENNReal.ofReal
        (1 + vecNormSq (coupledE Q w.toH1Function.grad) +
          ((sigmaBarInfinite nu (m - h) P)⁻¹) ^ 2 *
            vecNormSq (coupledB m h Q omega w.toH1Function.grad) -
          2 * (sigmaBarInfinite nu (m - h) P)⁻¹ *
            ∑ i, e i * coupledB m h Q omega w.toH1Function.grad i)) +
      SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm (originCube d (Kc : ℤ)) 2
        w.toH1Function.grad ^ (2 : ℕ) ≤
    1 + ENNReal.ofReal ((sigmaBarInfinite nu (m - h) P)⁻¹ ^ 2) *
      SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm (originCube d (Kc : ℤ)) 2
        (fun x => matVecMul (finiteShellIncrement omega (m - h) m x)
          (w.toH1Function.grad x)) ^ (2 : ℕ) := by
  set c := (sigmaBarInfinite nu (m - h) P)⁻¹ with hc
  set g := w.toH1Function.grad with hgdef
  set F : Vec d → Vec d := fun x => matVecMul (finiteShellIncrement omega (m - h) m x) (g x)
    with hFdef
  have hg0 : MemVectorL2 (openCubeSet (originCube d (Kc : ℤ))) g := w.toH1Function.grad_memVectorL2
  have hF0 : MemVectorL2 (openCubeSet (originCube d (Kc : ℤ))) F :=
    SuperdiffusionCLT.Section3.Terms.memVectorL2_matVecMul_of_continuous (originCube d (Kc : ℤ))
      (fun i j => coupled3_continuous_entry omega (m - h) m i j) hg0
  set f0 : Vec d → ℝ := fun x => vecNormSq (g x) + vecNormSq (e - c • F x) with hf0
  -- boxwise bound
  have hbox : subcubeAvg Kc n (fun Q => ENNReal.ofReal
        (1 + vecNormSq (coupledE Q g) + c ^ 2 * vecNormSq (coupledB m h Q omega g) -
          2 * c * ∑ i, e i * coupledB m h Q omega g i)) ≤
      subcubeAvg Kc n (fun Q => ∫⁻ x, ENNReal.ofReal (f0 x) ∂normalizedCubeMeasure Q) := by
    refine coupled_subcubeAvg_mono_on fun Q hQ => ?_
    have hk : (n : ℤ) ≤ (originCube d (Kc : ℤ)).scale := by
      show (n : ℤ) ≤ (Kc : ℤ)
      exact_mod_cast hn
    have hsub := openCubeSet_subset_of_mem_descendantsAtScale hk hQ
    have hgQ : MemVectorL2 (openCubeSet Q) g :=
      hg0.mono_measure (Measure.restrict_mono hsub le_rfl)
    have hFQ : MemVectorL2 (openCubeSet Q) F :=
      hF0.mono_measure (Measure.restrict_mono hsub le_rfl)
    rw [coupledE_eq_open, coupledB_eq_open]
    exact coupled3_ofReal_box_le he c hgQ hFQ
  rw [subcubeAvg_lintegral_normalizedCubeMeasure hn (fun x => ENNReal.ofReal (f0 x))] at hbox
  have hint : Integrable f0 (normalizedCubeMeasure (originCube d (Kc : ℤ))) :=
    (SuperdiffusionCLT.Section3.ResponseFields.integrable_vecNormSq_normalizedCubeMeasure hg0).add
      (SuperdiffusionCLT.Section3.ResponseFields.integrable_vecNormSq_normalizedCubeMeasure
        (coupled3_memL2_gauge e c hF0))
  have hq : ∫⁻ x, ENNReal.ofReal (f0 x) ∂normalizedCubeMeasure (originCube d (Kc : ℤ)) =
      ENNReal.ofReal (volumeAverage (openCubeSet (originCube d (Kc : ℤ))) f0) := by
    rw [← SuperdiffusionCLT.Section3.Setup.integral_normalizedCubeMeasure_eq_volumeAverage,
      ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun x => add_nonneg (vecNormSq_nonneg _) (vecNormSq_nonneg _))]
  have hnn : 0 ≤ volumeAverage (openCubeSet (originCube d (Kc : ℤ))) f0 := by
    rw [← SuperdiffusionCLT.Section3.Setup.integral_normalizedCubeMeasure_eq_volumeAverage]
    exact integral_nonneg fun x => add_nonneg (vecNormSq_nonneg _) (vecNormSq_nonneg _)
  have hA : SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm (originCube d (Kc : ℤ)) 2 g ^ (2 : ℕ) =
      ENNReal.ofReal (volumeAverage (openCubeSet (originCube d (Kc : ℤ))) (fun x => vecNormSq (g x))) := by
    rw [SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm_two_sq_eq_ofReal hg0,
      SuperdiffusionCLT.Section3.Setup.integral_normalizedCubeMeasure_eq_volumeAverage]
  have hH : SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm (originCube d (Kc : ℤ)) 2 F ^ (2 : ℕ) =
      ENNReal.ofReal (volumeAverage (openCubeSet (originCube d (Kc : ℤ))) (fun x => vecNormSq (F x))) := by
    rw [SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm_two_sq_eq_ofReal hF0,
      SuperdiffusionCLT.Section3.Setup.integral_normalizedCubeMeasure_eq_volumeAverage]
  have hen := coupled3_energy nu P m h Kc omega e w hw
  have havg := coupled3_avg_f he c hg0 hF0
  have ha0 : 0 ≤ volumeAverage (openCubeSet (originCube d (Kc : ℤ))) (fun x => vecNormSq (g x)) := by
    rw [← SuperdiffusionCLT.Section3.Setup.integral_normalizedCubeMeasure_eq_volumeAverage]
    exact integral_nonneg fun x => vecNormSq_nonneg _
  have hH0 : 0 ≤ volumeAverage (openCubeSet (originCube d (Kc : ℤ))) (fun x => vecNormSq (F x)) := by
    rw [← SuperdiffusionCLT.Section3.Setup.integral_normalizedCubeMeasure_eq_volumeAverage]
    exact integral_nonneg fun x => vecNormSq_nonneg _
  rw [hq] at hbox
  rw [hA, hH]
  set a := volumeAverage (openCubeSet (originCube d (Kc : ℤ))) (fun x => vecNormSq (g x))
  set H := volumeAverage (openCubeSet (originCube d (Kc : ℤ))) (fun x => vecNormSq (F x))
  set J := volumeAverage (openCubeSet (originCube d (Kc : ℤ))) (fun x => vecDot e (F x))
  have ht : volumeAverage (openCubeSet (originCube d (Kc : ℤ))) f0 + a = 1 + c ^ 2 * H := by
    rw [havg]
    have hen' : a = c * J := hen
    linarith only [hen']
  calc _ ≤ ENNReal.ofReal (volumeAverage (openCubeSet (originCube d (Kc : ℤ))) f0) + ENNReal.ofReal a :=
        add_le_add hbox le_rfl
    _ = ENNReal.ofReal (1 + c ^ 2 * H) := by
        rw [← ENNReal.ofReal_add hnn ha0, ht]
    _ = _ := by
        rw [ENNReal.ofReal_add zero_le_one (mul_nonneg (sq_nonneg c) hH0), ENNReal.ofReal_mul (sq_nonneg c),
          ENNReal.ofReal_one]

/-- **`e.coupled.bulk`**: the averaged bulk bound with the energy identity
`e.setup.w-energy`, in the form `avg E[X_z] + E‖∇w_D‖² ≤ 1 + σ⁻² E‖hshell ∇w_D‖²` with
`X_z = 1 + |e_{D,z}|² + σ⁻²|B_z|² - 2σ⁻¹ e·B_z` (`X_z ≥ 0`, so no positive part is lost; the
printed display is this inequality after subtracting `E‖∇w_D‖²`). -/
theorem coupled_bulk [NeZero d] (nu : ℝ)
    (P : MeasureTheory.ProbabilityMeasure (ShellSeq d)) (m h Kc n : ℕ) (hn : n ≤ Kc)
    (e : Vec d) (he : vecNormSq e = 1)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d (Kc : ℤ))))
    (hwD : ∀ omega, SuperdiffusionCLT.Section3.ResponseFields.IsCubeDirichletResponse
      (originCube d (Kc : ℤ)) (hshellFlux nu P m h omega e) (wD omega)) :
    subcubeAvg Kc n (fun Q => ∫⁻ omega, ENNReal.ofReal
        (1 + vecNormSq (coupledE Q (wD omega).toH1Function.grad) +
          ((sigmaBarInfinite nu (m - h) P)⁻¹) ^ 2 *
            vecNormSq (coupledB m h Q omega (wD omega).toH1Function.grad) -
          2 * (sigmaBarInfinite nu (m - h) P)⁻¹ *
            ∑ i, e i * coupledB m h Q omega (wD omega).toH1Function.grad i) ∂P.toMeasure) +
      ∫⁻ omega, SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm
        (originCube d (Kc : ℤ)) 2 (wD omega).toH1Function.grad ^ (2 : ℕ) ∂P.toMeasure ≤
    1 + ENNReal.ofReal ((sigmaBarInfinite nu (m - h) P)⁻¹ ^ 2) *
      ∫⁻ omega, SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm
        (originCube d (Kc : ℤ)) 2
        (fun x => matVecMul (finiteShellIncrement omega (m - h) m x)
          ((wD omega).toH1Function.grad x)) ^ (2 : ℕ) ∂P.toMeasure := by
  set k : ℝ≥0∞ := ENNReal.ofReal ((sigmaBarInfinite nu (m - h) P)⁻¹ ^ 2) with hk
  have hk' : k ≠ ⊤ := ENNReal.ofReal_ne_top
  calc _ ≤ ∫⁻ omega, subcubeAvg Kc n (fun Q => ENNReal.ofReal
        (1 + vecNormSq (coupledE Q (wD omega).toH1Function.grad) +
          ((sigmaBarInfinite nu (m - h) P)⁻¹) ^ 2 *
            vecNormSq (coupledB m h Q omega (wD omega).toH1Function.grad) -
          2 * (sigmaBarInfinite nu (m - h) P)⁻¹ *
            ∑ i, e i * coupledB m h Q omega (wD omega).toH1Function.grad i)) ∂P.toMeasure +
      ∫⁻ omega, SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm
        (originCube d (Kc : ℤ)) 2 (wD omega).toH1Function.grad ^ (2 : ℕ) ∂P.toMeasure :=
        add_le_add (subcubeAvg_lintegral_le_lintegral_subcubeAvg _) le_rfl
    _ ≤ _ := le_lintegral_add _ _
    _ ≤ ∫⁻ omega, (1 + k * SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm
        (originCube d (Kc : ℤ)) 2
        (fun x => matVecMul (finiteShellIncrement omega (m - h) m x)
          ((wD omega).toH1Function.grad x)) ^ (2 : ℕ)) ∂P.toMeasure :=
        lintegral_mono fun omega => coupled_bulk_det nu P m h Kc n hn omega e he (wD omega) (hwD omega)
    _ = _ := by
        rw [lintegral_add_left measurable_const, lintegral_const_mul' _ _ hk']
        simp

theorem coupled3_vecNormSq_single : vecNormSq (Pi.single (0 : Fin 2) (1 : ℝ) : Vec 2) = 1 := by
  simp [vecNormSq, vecDot, Pi.single_apply]

theorem coupled3_memL2_hshellFlux [NeZero d] (nu : ℝ)
    (P : MeasureTheory.ProbabilityMeasure (ShellSeq d)) (m h : ℕ) (omega : ShellSeq d)
    (e : Vec d) (Q : TriadicCube d) :
    MemVectorL2 (openCubeSet Q) (hshellFlux nu P m h omega e) := by
  have hc : MemVectorL2 (openCubeSet Q) (fun _ : Vec d => e) := by
    have : IsFiniteMeasure (volume.restrict (openCubeSet Q)) :=
      ⟨by simpa [Measure.restrict_apply_univ] using (coupled3_volume_open_ne_top Q).lt_top⟩
    exact memLp_const e
  have := SuperdiffusionCLT.Section3.Terms.memVectorL2_matVecMul_of_continuous Q
    (A := fun x => (sigmaBarInfinite nu (m - h) P)⁻¹ • finiteShellIncrement omega (m - h) m x)
    (fun i j => Continuous.const_smul
      (g := fun x => finiteShellIncrement omega (m - h) m x i j)
      (coupled3_continuous_entry omega (m - h) m i j) (sigmaBarInfinite nu (m - h) P)⁻¹) hc
  have heq : hshellFlux nu P m h omega e = fun x =>
      matVecMul ((sigmaBarInfinite nu (m - h) P)⁻¹ • finiteShellIncrement omega (m - h) m x) e := by
    funext x
    unfold hshellFlux
    rw [finiteShellIncrement_apply_eq_streamCutoff_sub omega (Nat.sub_le m h) x]
    funext i
    simp [matVecMul, Finset.mul_sum, Matrix.smul_apply, mul_assoc]
  rw [heq]
  exact this

/-- Witness for `coupled_pointwise` and `coupled_pointwise_split`: the hypotheses (positive
`σ`, a unit vector) hold for the Dirac law at the zero shell sequence in `d = 2`. -/
example : ∃ (e : Vec 2), vecNormSq e = 1 ∧
    0 < sigmaBarInfinite 1 (2 - 1) (SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw 2) := by
  refine ⟨Pi.single 0 1, coupled3_vecNormSq_single, ?_⟩
  exact SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite_pos one_pos _
    (SuperdiffusionCLT.Assumptions.ShellLaw.shellLawPrefix_diracZeroLaw le_rfl)
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ2_diracZeroLaw
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ3_diracZeroLaw
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ4_diracZeroLaw

/-- Witness for `coupled_bulk`: Dirichlet responses exist for every shell sequence. -/
example : ∃ wD : ShellSeq 2 → H10Function (openCubeSet (originCube 2 ((1 : ℕ) : ℤ))),
    ∀ omega, SuperdiffusionCLT.Section3.ResponseFields.IsCubeDirichletResponse
      (originCube 2 ((1 : ℕ) : ℤ))
      (hshellFlux 1 (SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw 2) 2 1 omega
        (Pi.single 0 1)) (wD omega) := by
  have := fun omega : ShellSeq 2 =>
    SuperdiffusionCLT.Section3.ResponseFields.exists_isCubeDirichletResponse
      (originCube 2 ((1 : ℕ) : ℤ))
      (coupled3_memL2_hshellFlux 1 (SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw 2) 2 1
        omega (Pi.single 0 1) _)
  exact ⟨fun omega => (this omega).choose, fun omega => (this omega).choose_spec⟩

end SuperdiffusionCLT.Section5
