/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Engine.HarmonicAffine
public import SuperdiffusionCLT.Section8.Common.ExcessDecay.OneStepWeylRepresentative
public import SuperdiffusionCLT.Section8.Common.ExcessDecay.CubeMoments
public import SuperdiffusionCLT.Section8.Common.ExcessDecay.IterationLemmaWindowGeometry
public import Homogenization.Sobolev.Foundations.CubePoisson.AnalyticInput

/-!
# Harmonic functions on a cube: `L²` calculus on the cubes `□_n`

Bridges between the normalized norm `cubeL2` of the engine and the volume-normalized
`normalizedL2On` of the Schauder development, and the Weyl representative of a solution of the
identity field on a cube.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6

open MeasureTheory Homogenization InnerProductSpace
open SuperdiffusionCLT.Section8.Common.ExcessDecay.Schauder
open SuperdiffusionCLT.Section8.Common.Support (normalizedL2On)

variable {d : ℕ}

theorem eh_isOpen_engCube (n : ℕ) : IsOpen (engCube d n) := isOpen_openCubeSet _

theorem eh_measurableSet_engCube (n : ℕ) : MeasurableSet (engCube d n) :=
  measurableSet_openCubeSet _

theorem eh_volume_engCube_ne_top (n : ℕ) : volume (engCube d n) ≠ ⊤ :=
  (volume_openCubeSet_lt_top _).ne

theorem eh_volume_engCube_pos (n : ℕ) : 0 < (volume (engCube d n)).toReal := by
  rw [eh_volume_engCube]
  positivity

/-- On `□_n` the engine norm is the volume-normalized `L²` seminorm. -/
theorem eh_cubeL2_eq {n : ℕ} {f : Vec d → ℝ} (hf : MemLp f 2 (volume.restrict (engCube d n))) :
    cubeL2 n f = normalizedL2On (engCube d n) f := by
  have hf' : MemLp f 2 (normalizedCubeMeasure (originCube d (n : ℤ))) :=
    memL2On_openCubeSet_normalizedCubeMeasure hf
  have h := setIntegral_openCubeSet_sq_eq_cubeVolume_mul_cubeLpNorm_two_rpow
    (originCube d (n : ℤ)) f hf'
  have hV : (volume (engCube d n)).toReal = cubeVolume (originCube d (n : ℤ)) :=
    volume_openCubeSet_toReal _
  have hVpos : 0 < cubeVolume (originCube d (n : ℤ)) := cubeVolume_pos _
  have hint : ∫ x in engCube d n, f x ^ 2
      = cubeVolume (originCube d (n : ℤ)) * cubeL2 n f ^ 2 := by
    have h2 : ∫ x in engCube d n, f x ^ 2 = ∫ x in openCubeSet (originCube d (n : ℤ)), f x * f x :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [sq])
    rw [h2, h, Real.rpow_two]
    rfl
  unfold normalizedL2On volumeAverage
  rw [hV, hint, ← mul_assoc, inv_mul_cancel₀ hVpos.ne', one_mul]
  exact (Real.sqrt_sq (cubeLpNorm_nonneg (originCube d (n : ℤ)) 2 f)).symm

/-- A continuous function is square integrable on every cube `□_n`. -/
theorem eh_memLp_of_continuous (n : ℕ) {g : Vec d → ℝ} (hg : Continuous g) :
    MemLp g 2 (volume.restrict (engCube d n)) := by
  set b : ℝ := (3 : ℝ) ^ n / 2 with hb
  set K : Set (Vec d) := Set.pi Set.univ (fun _ => Set.Icc (-b) b) with hK
  have hKc : IsCompact K := isCompact_univ_pi fun _ => isCompact_Icc
  have hsub : engCube d n ⊆ K := by
    intro y hy
    have h := mem_openCubeSet_originCube_iff.1 hy
    simp only [hK, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
    intro i
    have hi := h i
    rw [zpow_natCast] at hi
    constructor <;> linarith only [hi.1, hi.2, hb]
  have hint : IntegrableOn (fun y => g y ^ 2) (engCube d n) volume :=
    ((hg.pow 2).continuousOn.integrableOn_compact hKc).mono_set hsub
  exact (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).2 hint

/-- An almost-everywhere bound on a set bounds its normalized `L²` seminorm. -/
theorem eh_nL2_le_of_ae_abs_le {W : Set (Vec d)} (hfin : volume W ≠ ⊤)
    (hpos : 0 < (volume W).toReal) {f : Vec d → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hle : ∀ᵐ x ∂(volume.restrict W), |f x| ≤ M) : normalizedL2On W f ≤ M := by
  refine SuperdiffusionCLT.Section8.Common.Support.normalizedL2On_le_of_sq_le hM ?_
  unfold volumeAverage
  have hint : ∫ x in W, f x ^ 2 ≤ ∫ _x in W, M ^ 2 := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _)
      (integrableOn_const hfin) ?_
    filter_upwards [hle] with x hx
    have h2 : |f x| ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hx 2
    rwa [sq_abs] at h2
  rw [setIntegral_const, measureReal_def, smul_eq_mul] at hint
  calc ((volume W).toReal)⁻¹ * ∫ x in W, f x ^ 2
      ≤ ((volume W).toReal)⁻¹ * ((volume W).toReal * M ^ 2) :=
        mul_le_mul_of_nonneg_left hint (inv_nonneg.2 hpos.le)
    _ = M ^ 2 := by field_simp

/-- A solution of the identity field on `□_k` agrees a.e. with a harmonic function whose
Euclidean avatar is harmonic in the classical sense, and is square integrable. -/
theorem eh_weyl [NeZero d] {k : ℕ} {w : Vec d → ℝ} {gw : Vec d → Vec d}
    (h : IsSolOn (fun _ => (1 : Mat d)) (engCube d k) w gw) :
    ∃ v : Vec d → ℝ,
      HarmonicOnNhd (v ∘ toEuc.symm) (toEuc '' engCube d k) ∧
        v =ᵐ[volume.restrict (engCube d k)] w ∧ MemLp w 2 (volume.restrict (engCube d k)) := by
  obtain ⟨a, ha1, _⟩ := h
  have hweak : SuperdiffusionCLT.Section8.Common.Support.IsWeaklyHarmonicOn
      (engCube d k) a.toH1 := by
    intro φ
    have h0 := a.isHarmonic.2 φ
    have hmv : ∀ x, matVecMul ((fun _ => (1 : Mat d)) x) (a.toH1.grad x) = a.toH1.grad x := by
      intro x
      funext i
      simp [matVecMul, Matrix.one_apply]
    simpa only [hmv] using h0
  obtain ⟨v, hv, hae⟩ := exists_harmonicRepresentative_full (eh_isOpen_engCube k) hweak
  refine ⟨v, hv, ?_, a.toH1.memL2.ae_eq ha1⟩
  have h1 : ∀ᵐ x ∂(volume.restrict (engCube d k)), v x = (engCube d k).indicator a.toH1.toFun x :=
    ae_restrict_of_ae hae
  have h2 : ∀ᵐ x ∂(volume.restrict (engCube d k)), x ∈ engCube d k :=
    ae_restrict_mem (eh_measurableSet_engCube k)
  filter_upwards [h1, h2, ha1] with x hx1 hx2 hx3
  rw [hx1, Set.indicator_of_mem hx2, hx3]

end SuperdiffusionCLT.Section6
