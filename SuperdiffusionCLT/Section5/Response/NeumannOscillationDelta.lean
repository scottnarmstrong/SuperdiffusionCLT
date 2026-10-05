/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Response.NeumannOscillationMoments
public import SuperdiffusionCLT.Section5.Response.ResponseData
public import SuperdiffusionCLT.Section5.Response.NeumannMeasurable
public import SuperdiffusionCLT.Section3.Setup.ResponseMeasurabilitySelection

/-!
# The gap `δ = ∇w_N - ∇w_D` between the Neumann and the Dirichlet gradient

`‖δ‖⁴_{L̲⁴}` is interpolated between `‖δ‖²_{L̲²}` (the energy gap) and `‖δ‖⁸_{L̲⁸}` (the sum of the
`L⁸` gradient norms).  Only the energy gap needs to be measurable in the sample; its
measurability follows from the measurability of the two gradient classes in `L²(cu_Kc)`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- **`E‖δ‖⁴_{L̲⁴}` by interpolation**: for every `t > 0`,
`E ‖gN - gD‖⁴_{L̲⁴} ≤ (2t/3) E ‖gN - gD‖²_{L̲²} + 128 E(‖gD‖⁸_{L̲⁸} + ‖gN‖⁸_{L̲⁸}) / (3t²)`. -/
theorem lintegral_gap_pow_four_le {Kc : ℕ} (μ : Measure (ShellSeq d)) (gD gN : ShellSeq d → Vec d → Vec d)
    (hD : ∀ omega, MemVectorL2 (openCubeSet (originCube d (Kc : ℤ))) (gD omega))
    (hN : ∀ omega, MemVectorL2 (openCubeSet (originCube d (Kc : ℤ))) (gN omega))
    (hX : Measurable fun omega => vecCubeLpENorm (originCube d (Kc : ℤ)) 2
      (fun x => gN omega x - gD omega x))
    {t : ℝ} (ht : 0 < t) :
    ∫⁻ omega, (vecCubeLpENorm (originCube d (Kc : ℤ)) 4 (fun x => gN omega x - gD omega x)) ^ 4 ∂μ ≤
      ENNReal.ofReal (2 * t / 3) * ∫⁻ omega, (vecCubeLpENorm (originCube d (Kc : ℤ)) 2
        (fun x => gN omega x - gD omega x)) ^ 2 ∂μ +
      ENNReal.ofReal (1 / (3 * t ^ 2)) * (128 * ∫⁻ omega,
        ((vecCubeLpENorm (originCube d (Kc : ℤ)) 8 (gD omega)) ^ 8 +
          (vecCubeLpENorm (originCube d (Kc : ℤ)) 8 (gN omega)) ^ 8) ∂μ) := by
  set K := originCube d (Kc : ℤ) with hK
  have hδ : ∀ omega, MemVectorL2 (openCubeSet K) (fun x => gN omega x - gD omega x) :=
    fun omega => (hN omega).sub (hD omega)
  have hmeas : ∀ omega, AEStronglyMeasurable
      (hilbertifyVecField (fun x => gN omega x - gD omega x)) (normalizedCubeMeasure K) :=
    fun omega => SuperdiffusionCLT.Section3.Terms.aestronglyMeasurable_hilbertifyVecField_of_memVectorL2 (hδ omega)
  have hmeasR : ∀ omega, AEStronglyMeasurable
      (hilbertifyVecField (fun x => gN omega x - gD omega x))
      (volume.restrict (openCubeSet K)) := fun omega =>
    (memHilbertVectorL2_hilbertifyVecField (hδ omega)).aestronglyMeasurable
  have h1 := lintegral_pow_four_le_interpolation (d := d) (Kc := Kc) μ
    (fun omega => hilbertifyVecField (fun x => gN omega x - gD omega x)) hmeas hX ht
  refine h1.trans (add_le_add le_rfl (mul_le_mul_right ?_ _))
  rw [← lintegral_const_mul' _ _ (by norm_num)]
  refine lintegral_mono fun omega => ?_
  have hmD : AEStronglyMeasurable (hilbertifyVecField (gD omega)) (normalizedCubeMeasure K) :=
    SuperdiffusionCLT.Section3.Terms.aestronglyMeasurable_hilbertifyVecField_of_memVectorL2 (hD omega)
  have hmN : AEStronglyMeasurable (hilbertifyVecField (gN omega)) (normalizedCubeMeasure K) :=
    SuperdiffusionCLT.Section3.Terms.aestronglyMeasurable_hilbertifyVecField_of_memVectorL2 (hN omega)
  have hsub : vecCubeLpENorm K 8 (fun x => gN omega x - gD omega x) ≤
      vecCubeLpENorm K 8 (gN omega) + vecCubeLpENorm K 8 (gD omega) := by
    have hneg : AEStronglyMeasurable (hilbertifyVecField (fun x => -gD omega x))
        (normalizedCubeMeasure K) := by
      have : hilbertifyVecField (fun x => -gD omega x) = -hilbertifyVecField (gD omega) := by
        funext x
        exact map_neg (HilbertVec.linearEquivVec d).symm (gD omega x)
      rw [this]
      exact hmD.neg
    have h := vecCubeLpENorm_add_le (Q := K) (q := 8) (F := gN omega) (G := fun x => -gD omega x)
      (by norm_num) hmN hneg
    rw [vecCubeLpENorm_neg] at h
    simpa [sub_eq_add_neg] using h
  calc (vecCubeLpENorm K 8 (fun x => gN omega x - gD omega x)) ^ 8
      ≤ (vecCubeLpENorm K 8 (gN omega) + vecCubeLpENorm K 8 (gD omega)) ^ 8 :=
        pow_le_pow_left' hsub 8
    _ ≤ 128 * ((vecCubeLpENorm K 8 (gN omega)) ^ 8 + (vecCubeLpENorm K 8 (gD omega)) ^ 8) :=
        add_pow_eight_le _ _
    _ = 128 * ((vecCubeLpENorm K 8 (gD omega)) ^ 8 + (vecCubeLpENorm K 8 (gN omega)) ^ 8) := by
        rw [add_comm]

/-- **The energy gap is measurable in the sample**: `ω ↦ ‖∇w_N(ω) - ∇w_D(ω)‖_{L̲²(cu_Kc)}` for
the Neumann and Dirichlet responses of the same shell flux. -/
theorem measurable_gap_energy [NeZero d] (nu : ℝ) (P : MeasureTheory.ProbabilityMeasure (ShellSeq d))
    (m h Kc : ℕ) (e : Vec d)
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d (Kc : ℤ))))
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d (Kc : ℤ))))
    (hwN : ∀ omega, IsCubeNeumannResponse (originCube d (Kc : ℤ))
      (hshellFlux nu P m h omega e) (wN omega))
    (hwD : ∀ omega, IsCubeDirichletResponse (originCube d (Kc : ℤ))
      (hshellFlux nu P m h omega e) (wD omega)) :
    Measurable fun omega => vecCubeLpENorm (originCube d (Kc : ℤ)) 2
      (fun x => (wN omega).toH1Function.grad x - (wD omega).toH1Function.grad x) := by
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  set p0 : Vec d := (sigmaBarInfinite nu (m - h) P)⁻¹ • e with hp0
  have hwN' : ∀ omega, IsCubeNeumannResponse (originCube d (Kc : ℤ))
      (dirichletRhsField omega m (m - h) p0) (wN omega) := fun omega => by
    have := hwN omega
    rwa [responseData_hshellFlux_eq_dirichletRhsField] at this
  have hwD' : ∀ omega, IsDirichletResponse omega m (m - h) Kc p0 (wD omega) := fun omega => by
    have := hwD omega
    rwa [responseData_hshellFlux_eq_dirichletRhsField] at this
  have hNm : Measurable (fun omega : ShellSeq d => (wN omega).toH1Function.gradToHilbertVectorL2) :=
    measurable_gradToHilbertVectorL2_of_isCubeNeumannResponse_rhsField hwN'
  have hDm : Measurable (fun omega : ShellSeq d => (wD omega).toH1Function.gradToHilbertVectorL2) :=
    measurable_gradToHilbertVectorL2_of_isDirichletResponse hwD'
  have hfun : (fun omega => vecCubeLpENorm (originCube d (Kc : ℤ)) 2
      (fun x => (wN omega).toH1Function.grad x - (wD omega).toH1Function.grad x)) =
      fun omega => ENNReal.ofReal ((cubeVolume (originCube d (Kc : ℤ)))⁻¹) ^
          ((1 : ENNReal) / 2).toReal *
        ‖(wN omega).toH1Function.gradToHilbertVectorL2 -
          (wD omega).toH1Function.gradToHilbertVectorL2‖ₑ := by
    funext omega
    have hmem : MemVectorL2 (openCubeSet (originCube d (Kc : ℤ)))
        (fun x => (wN omega).toH1Function.grad x - (wD omega).toH1Function.grad x) :=
      (wN omega).toH1Function.grad_memVectorL2.sub (wD omega).toH1Function.grad_memVectorL2
    rw [vecCubeLpENorm_eq_enorm_toHilbertVectorL2OfVecField hmem]
    congr 2
  rw [hfun]
  exact (continuous_enorm.measurable.comp (hNm.sub hDm)).const_mul _

end

end SuperdiffusionCLT.Section5
