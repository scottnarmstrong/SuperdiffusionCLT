/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Engine.Carriers
public import SuperdiffusionCLT.Section6.Root.CenteredRecenteredBridge
public import SuperdiffusionCLT.Section6.Lemma.Assembly
public import SuperdiffusionCLT.Section6.Prereq.FullFieldGrad
public import Homogenization.Ambient.ScalarMatrix
public import Homogenization.Deterministic.HomogenizationBlackBoxes.Duality

/-!
# Almost-sure field facts for the engine

Local ellipticity of the recentered field, and the centered field of each cube `□_m` as the
recentered field plus a constant skew matrix, with the same solutions on every origin cube.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory

variable {d : ℕ}

theorem ea0_isElliptic_of_bound [NeZero d] {nu : ℝ} (hnu : 0 < nu) (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
    {S : Set (Vec d)} (hS : MeasurableSet S) {C : ℝ}
    (hC : ∀ x ∈ S, ∀ i j : Fin d, |fullCoefficientRecentered nu omega x i j| ≤ C) :
    ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam S (fullCoefficientRecentered nu omega) := by
  classical
  refine ⟨nu, ((d : ℝ) * (d : ℝ) * C ^ 2 + nu ^ 2) / nu, ?_, fun x hx => ?_⟩
  · refine measurable_matrix_of_entries fun i j => Measurable.ite hS ?_ measurable_const
    exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp
      (measurable_fullCoefficientRecentered nu omega))
  · exact SuperdiffusionCLT.Section2.CoarseGraining.isEllipticMatrix_of_symmPart_eq_smul_one
      hnu (symmPart_fullCoefficientRecentered nu omega x) (fun i j => hC x hx i j)

theorem ea0_isSolOn_add_const_skew_iff {a : CoeffField d} {U : Set (Vec d)} (hU : IsOpen U)
    (hfin : volume U < ⊤)
    (hell : ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam U a)
    {K : Mat d} (hK : matTranspose K = -K) {u : Vec d → ℝ} {g : Vec d → Vec d} :
    IsSolOn (fun x => a x + K) U u g ↔ IsSolOn a U u g := by
  have : IsFiniteMeasure (volumeMeasureOn U) := ⟨by simpa [volumeMeasureOn] using hfin⟩
  obtain ⟨lam, Lam, hEll⟩ := hell
  have hfl : ∀ v : H1Function U, MemVectorL2 U (fun x => matVecMul (a x) (v.grad x)) := fun v =>
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll (MeasureTheory.MemLp.of_eval fun i => v.gradMemL2 i)
  constructor
  · rintro ⟨v, hv1, hv2⟩
    exact ⟨⟨v.toH1,
      (Section2.CoarseGraining.isAHarmonicGradient_add_const_skew_iff hU hK (hfl v.toH1)).1
        v.isHarmonic⟩, hv1, hv2⟩
  · rintro ⟨v, hv1, hv2⟩
    exact ⟨⟨v.toH1,
      Section2.CoarseGraining.isAHarmonicGradient_add_const_skew hU hK (hfl v.toH1)
        v.isHarmonic⟩, hv1, hv2⟩

/-- **E-A0 (the almost-sure field facts)**: local ellipticity of the recentered field, and
the centered field of every cube `□_m` is the recentered field plus a constant skew matrix,
elliptic on every origin cube, with the same solutions. -/
theorem eng_ae_field (d : ℕ) [NeZero d]
    {P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)}
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P) {nu : ℝ} (hnu : 0 < nu) :
    ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
      GrowthElliptic (fullCoefficientRecentered nu omega) ∧
        (∀ n : ℕ, ∃ lam Lam : ℝ,
          IsEllipticFieldOn lam Lam (engCube d n) (fullCoefficientRecentered nu omega)) ∧
        ∀ m n : ℕ,
          (∃ lam Lam : ℝ, 0 < lam ∧ lam ≤ Lam ∧
            IsEllipticFieldOn lam Lam (cubeSet (originCube d (n : ℤ)))
              (fun x => nu • (1 : Mat d) +
                SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
                  (cubeSet (originCube d (m : ℤ))) x)) ∧
            (∀ x : Vec d, symmPart (nu • (1 : Mat d) +
                SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
                  (cubeSet (originCube d (m : ℤ))) x) = nu • (1 : Mat d)) ∧
            ∀ (u : Vec d → ℝ) (g : Vec d → Vec d),
              IsSolOn (fullCoefficientRecentered nu omega) (engCube d n) u g ↔
                IsSolOn (fun x => nu • (1 : Mat d) +
                  SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
                    (cubeSet (originCube d (m : ℤ))) x) (engCube d n) u g := by
  classical
  filter_upwards [ae_centered_eq_recentered_add_skew hJ3 nu,
    ae_exists_entryBound_fullCoefficientRecentered hJ3 nu,
    l9_ae_exists_ell_centered hJ3 hnu] with omega hb hbd hell
  have hE : ∀ S : Set (Vec d), Bornology.IsBounded S → MeasurableSet S →
      ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam S (fullCoefficientRecentered nu omega) :=
    fun S hS hm => by
      obtain ⟨C, hC⟩ := hbd S hS
      exact ea0_isElliptic_of_bound hnu omega hm hC
  have hEc : ∀ n : ℕ, ∃ lam Lam : ℝ,
      IsEllipticFieldOn lam Lam (engCube d n) (fullCoefficientRecentered nu omega) := fun n =>
    hE _ (isBounded_openCubeSet _) (measurableSet_openCubeSet _)
  refine ⟨fun R hR => hE _ (Metric.isBounded_ball.subset (euclidBall_subset_ball hR)) (measurableSet_euclidBall R), hEc, fun m n => ?_⟩
  obtain ⟨K, hK, hKx⟩ := hb m
  obtain ⟨lam, Lam, hl⟩ := hell m n 0
  have hl' : IsEllipticFieldOn lam Lam (cubeSet (originCube d (n : ℤ)))
      (fun x => nu • (1 : Mat d) + SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
        (cubeSet (originCube d (m : ℤ))) x) := by
    simpa only [zero_add] using hl
  refine ⟨⟨lam, Lam, (l9_ell_pos _ hl').1, (l9_ell_pos _ hl').2, hl'⟩, fun x =>
    HarmonicApprox.symmPart_centeredStreamField_add nu omega _ x, fun u g => ?_⟩
  have hfun : (fun x => nu • (1 : Mat d) + SuperdiffusionCLT.Section2.Carriers.centeredStreamField
      omega (cubeSet (originCube d (m : ℤ))) x) =
      fun x => fullCoefficientRecentered nu omega x + K := funext hKx
  rw [hfun]
  exact (ea0_isSolOn_add_const_skew_iff (isOpen_openCubeSet _) (volume_openCubeSet_lt_top _)
    (hEc n) hK).symm

/-- Witness: the Dirac zero law meets `J3`. -/
example [NeZero d] {nu : ℝ} (hnu : 0 < nu) :
    ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d
        ∂(SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw d).toMeasure,
      GrowthElliptic (fullCoefficientRecentered nu omega) :=
  (eng_ae_field d SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ3_diracZeroLaw hnu).mono
    fun _ h => h.1

end SuperdiffusionCLT.Section6
