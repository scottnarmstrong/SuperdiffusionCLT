/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Localization.FluctC
public import SuperdiffusionCLT.Section5.Response.NeumannOscillationDelta

/-!
# Measurability in the sample of the energy of the local minimizer `S_z`

The conclusion of `lem.localization` splits, by Young's inequality, into the energy `⟪S_z, S_z⟫`
and the energy `⟪F_z, F_z⟫`; the two expectations are added in `ℝ≥0∞`, which needs one of the two
summands to be measurable in the sample.  Here `ω ↦ ⟪S_z, S_z⟫` is measurable: it is the quadratic
form of the coarse-grained block matrix `bfA_m(z + cu_n)` (measurable in the sample) at the
constant slope `P_z`, whose entries are cube means of the response gradients (measurable by the
measurability of the `L²` classes of the responses) and of the shell flux.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)
open SuperdiffusionCLT.Section2.Cutoff SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed (measurable_coarseBlockMatrix_upperLeft_apply measurable_coarseBlockMatrix_upperRight_apply measurable_coarseBlockMatrix_lowerLeft_apply measurable_coarseBlockMatrix_lowerRight_apply aeLocallyUniformlyEllipticField_coefficientCutoff)
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

variable {d : ℕ}

/-- The cube mean of the coordinates of a family of `L²` fields is measurable in the sample as soon
as the family of their `L²` classes is. -/
theorem loc_measurable_mean_of_class {U : Set (Vec d)} {Q : TriadicCube d}
    (hQ : openCubeSet Q ⊆ U) {G : ShellSeq d → Vec d → Vec d}
    (hmem : ∀ omega, MemVectorL2 U (G omega))
    (hmeas : Measurable fun omega => toHilbertVectorL2OfVecField (hmem omega)) (i : Fin d) :
    Measurable fun omega => volumeAverage (openCubeSet Q) (fun x => G omega x i) := by
  have hR : MeasurableSet (openCubeSet Q) := measurableSet_openCubeSet Q
  have hμR : volumeMeasureOn U (openCubeSet Q) ≠ ∞ := by
    rw [volumeMeasureOn, Measure.restrict_apply hR]
    exact ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_left)
      (volume_openCubeSet_lt_top Q))
  set c : HilbertVec d := HilbertVec.ofVec (Pi.single i 1) with hc
  have hT : Continuous fun u : HilbertVectorL2 U =>
      inner ℝ (indicatorConstLp 2 hR hμR c) u := continuous_const.inner continuous_id
  have key : ∀ omega, inner ℝ (indicatorConstLp 2 hR hμR c)
      (toHilbertVectorL2OfVecField (hmem omega)) = ∫ x in openCubeSet Q, G omega x i := by
    intro omega
    rw [L2.inner_indicatorConstLp_eq_setIntegral_inner]
    have hae := coeFn_toHilbertVectorL2OfVecField (hmem omega)
    have hae' : ∀ᵐ x ∂(volumeMeasureOn U).restrict (openCubeSet Q),
        (toHilbertVectorL2OfVecField (hmem omega) : Vec d → HilbertVec d) x =
          hilbertifyVecField (G omega) x := ae_restrict_of_ae hae
    rw [integral_congr_ae (hae'.mono fun x hx => by rw [hx])]
    rw [volumeMeasureOn, Measure.restrict_restrict hR, Set.inter_eq_left.2 hQ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [hilbertifyVecField, hc, HilbertVec.inner_def, vecDot, HilbertVec.toVec, PiLp.single_apply]
  have hfun : (fun omega => volumeAverage (openCubeSet Q) (fun x => G omega x i)) =
      fun omega => ((volume (openCubeSet Q)).toReal)⁻¹ *
        inner ℝ (indicatorConstLp 2 hR hμR c) (toHilbertVectorL2OfVecField (hmem omega)) := by
    funext omega
    rw [key omega]
    rfl
  rw [hfun]
  exact (hT.measurable.comp hmeas).const_mul _

theorem loc_measurable_vecDot_matVecMul {α : Type*} [MeasurableSpace α] {u v : α → Vec d}
    {M : α → Mat d} (hu : ∀ i, Measurable fun a => u a i) (hv : ∀ i, Measurable fun a => v a i)
    (hM : ∀ i j, Measurable fun a => M a i j) :
    Measurable fun a => vecDot (u a) (matVecMul (M a) (v a)) := by
  unfold vecDot matVecMul
  refine Finset.measurable_sum _ fun i _ => (hu i).mul ?_
  exact Finset.measurable_sum _ fun j _ => (hM i j).mul (hv j)

theorem loc_measurable_blockQuadratic {α : Type*} [MeasurableSpace α] {p q : α → Vec d}
    {C : α → BlockMat d} (hp : ∀ i, Measurable fun a => p a i) (hq : ∀ i, Measurable fun a => q a i)
    (h1 : ∀ i j, Measurable fun a => (C a).upperLeft i j)
    (h2 : ∀ i j, Measurable fun a => (C a).upperRight i j)
    (h3 : ∀ i j, Measurable fun a => (C a).lowerLeft i j)
    (h4 : ∀ i j, Measurable fun a => (C a).lowerRight i j) :
    Measurable fun a => blockVecDot (p a, q a) (blockMatVecMul (C a) (p a, q a)) := by
  have e : (fun a => blockVecDot (p a, q a) (blockMatVecMul (C a) (p a, q a))) = fun a =>
      vecDot (p a) (matVecMul (C a).upperLeft (p a)) + vecDot (p a) (matVecMul (C a).upperRight (q a)) +
        vecDot (q a) (matVecMul (C a).lowerLeft (p a)) + vecDot (q a) (matVecMul (C a).lowerRight (q a)) :=
    funext fun a => SuperdiffusionCLT.Section2.Annealed.blockQuadratic_eq (C a) (p a) (q a)
  rw [e]
  exact (((loc_measurable_vecDot_matVecMul hp hp h1).add (loc_measurable_vecDot_matVecMul hp hq h2)).add
    (loc_measurable_vecDot_matVecMul hq hp h3)).add (loc_measurable_vecDot_matVecMul hq hq h4)

theorem loc_class_hshell_measurable [NeZero d] (nu : ℝ)
    (P : ProbabilityMeasure (ShellSeq d)) (m h Kc : ℕ) (e : Vec d) :
    Measurable fun omega : ShellSeq d => toHilbertVectorL2OfVecField
      (memVectorL2_hshellFlux nu P (m := m) (h := h) omega e Kc) := by
  have hfun : (fun omega : ShellSeq d => toHilbertVectorL2OfVecField
      (memVectorL2_hshellFlux nu P (m := m) (h := h) omega e Kc)) =
      fun omega : ShellSeq d => toHilbertVectorL2OfVecField
        (memVectorL2_dirichletRhsField omega m (m - h) Kc ((sigmaBarInfinite nu (m - h) P)⁻¹ • e)) := by
    funext omega
    refine toHilbertVectorL2OfVecField_congr _ _ ?_
    exact Filter.Eventually.of_forall fun x => by
      rw [responseData_hshellFlux_eq_dirichletRhsField]
  rw [hfun]
  exact measurable_toHilbertVectorL2OfVecField_dirichletRhsField m (m - h) Kc _

theorem loc_measurable_gradClass_dirichlet [NeZero d] (nu : ℝ)
    (P : ProbabilityMeasure (ShellSeq d)) (m h Kc : ℕ) (e : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d (Kc : ℤ))))
    (hwD : ∀ omega, IsCubeDirichletResponse (originCube d (Kc : ℤ))
      (hshellFlux nu P m h omega e) (wD omega)) :
    Measurable fun omega : ShellSeq d => (wD omega).toH1Function.gradToHilbertVectorL2 := by
  have hwD' : ∀ omega, IsDirichletResponse omega m (m - h) Kc ((sigmaBarInfinite nu (m - h) P)⁻¹ • e)
      (wD omega) := fun omega => by
    have := hwD omega
    rwa [responseData_hshellFlux_eq_dirichletRhsField] at this
  exact measurable_gradToHilbertVectorL2_of_isDirichletResponse hwD'

theorem loc_measurable_gradClass_neumann [NeZero d] (nu : ℝ)
    (P : ProbabilityMeasure (ShellSeq d)) (m h Kc : ℕ) (e : Vec d)
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d (Kc : ℤ))))
    (hwN : ∀ omega, IsCubeNeumannResponse (originCube d (Kc : ℤ))
      (hshellFlux nu P m h omega e) (wN omega)) :
    Measurable fun omega : ShellSeq d => (wN omega).toH1Function.gradToHilbertVectorL2 := by
  have hwN' : ∀ omega, IsCubeNeumannResponse (originCube d (Kc : ℤ))
      (dirichletRhsField omega m (m - h) ((sigmaBarInfinite nu (m - h) P)⁻¹ • e)) (wN omega) :=
    fun omega => by
    have := hwN omega
    rwa [responseData_hshellFlux_eq_dirichletRhsField] at this
  exact measurable_gradToHilbertVectorL2_of_isCubeNeumannResponse_rhsField hwN'

theorem loc_measurable_mean_grad_dirichlet [NeZero d] (nu : ℝ)
    (P : ProbabilityMeasure (ShellSeq d)) (m h Kc : ℕ) (e : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d (Kc : ℤ))))
    (hwD : ∀ omega, IsCubeDirichletResponse (originCube d (Kc : ℤ))
      (hshellFlux nu P m h omega e) (wD omega)) {Q : TriadicCube d}
    (hsub : openCubeSet Q ⊆ openCubeSet (originCube d (Kc : ℤ))) (i : Fin d) :
    Measurable fun omega => volumeAverage (openCubeSet Q)
      (fun x => (wD omega).toH1Function.grad x i) :=
  loc_measurable_mean_of_class (G := fun omega => (wD omega).toH1Function.grad) hsub
    (fun omega => (wD omega).toH1Function.grad_memVectorL2)
    (loc_measurable_gradClass_dirichlet nu P m h Kc e wD hwD) i

theorem loc_measurable_mean_grad_neumann [NeZero d] (nu : ℝ)
    (P : ProbabilityMeasure (ShellSeq d)) (m h Kc : ℕ) (e : Vec d)
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d (Kc : ℤ))))
    (hwN : ∀ omega, IsCubeNeumannResponse (originCube d (Kc : ℤ))
      (hshellFlux nu P m h omega e) (wN omega)) {Q : TriadicCube d}
    (hsub : openCubeSet Q ⊆ openCubeSet (originCube d (Kc : ℤ))) (i : Fin d) :
    Measurable fun omega => volumeAverage (openCubeSet Q)
      (fun x => ((wN omega).toH1Function.grad x + hshellFlux nu P m h omega e x) i) := by
  have hmem : ∀ omega, MemVectorL2 (openCubeSet (originCube d (Kc : ℤ)))
      (fun x => (wN omega).toH1Function.grad x + hshellFlux nu P m h omega e x) :=
    fun omega => (wN omega).toH1Function.grad_memVectorL2.add
      (memVectorL2_hshellFlux nu P omega e Kc)
  refine loc_measurable_mean_of_class (G := fun omega x =>
      (wN omega).toH1Function.grad x + hshellFlux nu P m h omega e x) hsub hmem ?_ i
  have hfun : (fun omega => toHilbertVectorL2OfVecField (hmem omega)) = fun omega =>
      (wN omega).toH1Function.gradToHilbertVectorL2 + toHilbertVectorL2OfVecField
        (memVectorL2_hshellFlux nu P (m := m) (h := h) omega e Kc) := by
    funext omega
    exact toHilbertVectorL2OfVecField_add (wN omega).toH1Function.grad_memVectorL2
      (memVectorL2_hshellFlux nu P omega e Kc)
  rw [hfun]
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  exact (loc_measurable_gradClass_neumann nu P m h Kc e wN hwN).add
    (loc_class_hshell_measurable nu P m h Kc e)

theorem loc_measurable_coarse_entries [NeZero d] {nu : ℝ} (hnu : 0 < nu) (m : ℕ)
    (Q : TriadicCube d) :
    (∀ i j, Measurable fun omega : ShellSeq d => (coarseBlockMatrix (cubeSet Q)
        (coefficientCutoff nu omega m).toCoeffField).upperLeft i j) ∧
    (∀ i j, Measurable fun omega : ShellSeq d => (coarseBlockMatrix (cubeSet Q)
        (coefficientCutoff nu omega m).toCoeffField).upperRight i j) ∧
    (∀ i j, Measurable fun omega : ShellSeq d => (coarseBlockMatrix (cubeSet Q)
        (coefficientCutoff nu omega m).toCoeffField).lowerLeft i j) ∧
    (∀ i j, Measurable fun omega : ShellSeq d => (coarseBlockMatrix (cubeSet Q)
        (coefficientCutoff nu omega m).toCoeffField).lowerRight i j) := by
  have hA := measurable_coefficientCutoff (d := d) nu m
  have hE := fun omega : ShellSeq d => aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega m
  exact ⟨fun i j => measurable_coarseBlockMatrix_upperLeft_apply (A := fun omega => coefficientCutoff nu omega m) hA hE Q i j,
    fun i j => measurable_coarseBlockMatrix_upperRight_apply (A := fun omega => coefficientCutoff nu omega m) hA hE Q i j,
    fun i j => measurable_coarseBlockMatrix_lowerLeft_apply (A := fun omega => coefficientCutoff nu omega m) hA hE Q i j,
    fun i j => measurable_coarseBlockMatrix_lowerRight_apply (A := fun omega => coefficientCutoff nu omega m) hA hE Q i j⟩

/-- **The energy `⟪S_z, S_z⟫` of the constant-offset minimizer is measurable in the sample.** -/
theorem loc_measurable_pairing_S [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (m h Kc : ℕ) (e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d (Kc : ℤ))))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d (Kc : ℤ))))
    (hwD : ∀ omega, IsCubeDirichletResponse (originCube d (Kc : ℤ))
      (hshellFlux nu P m h omega e) (wD omega))
    (hwN : ∀ omega, IsCubeNeumannResponse (originCube d (Kc : ℤ))
      (hshellFlux nu P m h omega e') (wN omega)) {Q : TriadicCube d}
    (hsub : openCubeSet Q ⊆ openCubeSet (originCube d (Kc : ℤ)))
    (S : ShellSeq d → BlockState d)
    (hS : ∀ omega, IsBlockOffsetMinimizer (coefficientCutoff nu omega m).toCoeffField (cubeSet Q)
      (constBlockState (blockSlope nu (m - h) P Q e e' (wD omega).toH1Function.grad
        (fun y => (wN omega).toH1Function.grad y + hshellFlux nu P m h omega e' y))) (S omega)) :
    Measurable fun omega => ENNReal.ofReal (blockPairingAverage (cubeSet Q)
      (coefficientCutoff nu omega m).toCoeffField (S omega) (S omega)) := by
  refine ENNReal.measurable_ofReal.comp ?_
  have heq : (fun omega => blockPairingAverage (cubeSet Q)
      (coefficientCutoff nu omega m).toCoeffField (S omega) (S omega)) = fun omega =>
      blockVecDot (blockSlope nu (m - h) P Q e e' (wD omega).toH1Function.grad
        (fun y => (wN omega).toH1Function.grad y + hshellFlux nu P m h omega e' y))
        (blockMatVecMul (coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega m).toCoeffField)
          (blockSlope nu (m - h) P Q e e' (wD omega).toH1Function.grad
            (fun y => (wN omega).toH1Function.grad y + hshellFlux nu P m h omega e' y))) := by
    funext omega
    obtain ⟨lam, Lam, hEll⟩ := exists_isEllipticFieldOn_coefficientCutoff_cubeSet hnu omega m Q
    exact blockPairingAverage_self_eq_coarseBlockMatrix Q hEll _ (hS omega)
  rw [heq]
  obtain ⟨c1, c2, c3, c4⟩ := loc_measurable_coarse_entries hnu m Q
  have hD := fun i => loc_measurable_mean_grad_dirichlet nu P m h Kc e wD hwD hsub i
  have hN := fun i => loc_measurable_mean_grad_neumann nu P m h Kc e' wN hwN hsub i
  refine loc_measurable_blockQuadratic (p := fun omega => (sigmaBarInfinite nu (m - h) P) ^ (-(1 : ℝ) / 2) •
      (e' + volumeAverageVec (cubeSet Q) (wD omega).toH1Function.grad))
    (q := fun omega => (sigmaBarInfinite nu (m - h) P) ^ ((1 : ℝ) / 2) •
      (e + volumeAverageVec (cubeSet Q) (fun y => (wN omega).toH1Function.grad y +
        hshellFlux nu P m h omega e' y))) ?_ ?_ c1 c2 c3 c4
  · intro i
    have e1 : (fun omega => ((sigmaBarInfinite nu (m - h) P) ^ (-(1 : ℝ) / 2) •
        (e' + volumeAverageVec (cubeSet Q) (wD omega).toH1Function.grad)) i) = fun omega =>
        (sigmaBarInfinite nu (m - h) P) ^ (-(1 : ℝ) / 2) *
          (e' i + volumeAverage (openCubeSet Q) (fun x => (wD omega).toH1Function.grad x i)) := by
      funext omega
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, volumeAverageVec,
        volumeAverage_cubeSet_eq_openCubeSet]
    rw [e1]
    exact ((hD i).const_add (e' i)).const_mul _
  · intro i
    have e1 : (fun omega => ((sigmaBarInfinite nu (m - h) P) ^ ((1 : ℝ) / 2) •
        (e + volumeAverageVec (cubeSet Q) (fun y => (wN omega).toH1Function.grad y +
          hshellFlux nu P m h omega e' y))) i) = fun omega =>
        (sigmaBarInfinite nu (m - h) P) ^ ((1 : ℝ) / 2) *
          (e i + volumeAverage (openCubeSet Q) (fun x =>
            ((wN omega).toH1Function.grad x + hshellFlux nu P m h omega e' x) i)) := by
      funext omega
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, volumeAverageVec,
        volumeAverage_cubeSet_eq_openCubeSet]
    rw [e1]
    exact ((hN i).const_add (e i)).const_mul _

end SuperdiffusionCLT.Section5
