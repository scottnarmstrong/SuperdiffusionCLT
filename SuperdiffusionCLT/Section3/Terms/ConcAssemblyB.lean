/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm1ConcDepth
public import SuperdiffusionCLT.Section3.Terms.PerClassCentering
public import SuperdiffusionCLT.Section3.Terms.ConcentrationComparisonB
public import SuperdiffusionCLT.Section3.Terms.ConcXIntegrated
public import SuperdiffusionCLT.Section3.Terms.ConcentrationMean
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
# The `0`-exponent branch of the per-cube concentration `hconc`

`SuperdiffusionCLT.Section3.Terms.concDepthClause_of_hconc`
(in `RHSTerm1ConcDepth.lean`) reduces the depth moment `_hConcDepth`
of `term1_close` to the single per-cube concentration

`hconc : ∀ j, ∀ R ∈ descendantsAtDepth (originCube d S.m) j,
  ∫⁻ ‖⟨a_ℓ ∇ũ_n − q̃⟩_R‖² ≤ Cc · 3^{−d (m−j−ℓ)} · ∫⁻ ‖a_ℓ ∇ũ_n − q̃‖²_{L̲²(R)}`.

This module proves the branch of `hconc` at depths `j` with `S.m ≤ j + S.ℓ`, where the
printed exponent `S.m − j − S.ℓ` is `0`.  There the clause is the pointwise vector Jensen on one
cube, integrated over the sample, and it needs no independence, centring or measurability input:
only the `L̲²` membership of the observable field on every cube and the constant gate `1 ≤ Cc`.

* `vecNormSq_volumeAverageVec_le_vecSqAvg_of_memLp`: the vector Jensen on one cube.
* `lintegral_ofReal_vecNormSq_volumeAverageVec_le_mul_vecSqAvg_of_one_le`: the integrated
  single-cube Jensen with an arbitrary constant `Cc ≥ 1`.
* `hconc_concDepthField_truncated`: the `0`-exponent branch of `hconc` at the observable field.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory Homogenization
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The vector Jensen at the `L̲²` carrier

The clause at exponent `0` is the pointwise vector Jensen on one cube.  The
lemma `ShellHminusEndpointOrderOne.vecNormSq_volumeAverageVec_le` needs `Continuous F`,
which `concDepthField` is not, so the Jensen is taken from the scalar cube Jensen
`ConcentrationComparisonB.sq_volumeAverage_le_volumeAverage_sq` at the `L̲²`
carrier. -/

/-- **Vector Jensen on one cube from the scalar cube Jensen.**  For a field that
is `L̲²` on a cube `Q`, the squared norm of the vector cube average is at most the
average of the squared norm. -/
theorem vecNormSq_volumeAverageVec_le_vecSqAvg_of_memLp (Q : TriadicCube d) {F : Vec d → Vec d}
    (hF : MemLp (hilbertifyVecField F) 2 (normalizedCubeMeasure Q)) :
    vecNormSq (volumeAverageVec (cubeSet Q) F) ≤ vecSqAvg Q F := by
  have hcoord : ∀ i : Fin d, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q) :=
    fun i => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).comp_memLp'
      (memLp_hilbertifyVecField_iff.mp hF)
  calc vecNormSq (volumeAverageVec (cubeSet Q) F)
      = ∑ i : Fin d, (volumeAverage (cubeSet Q) (fun x => F x i)) ^ 2 := by
        rw [vecNormSq_eq_sum_coordSq]
        exact Finset.sum_congr rfl fun i _ => by rw [volumeAverageVec_apply_coord]
    _ ≤ ∑ i : Fin d, volumeAverage (cubeSet Q) (fun x => (F x i) ^ 2) :=
        Finset.sum_le_sum fun i _ => sq_volumeAverage_le_volumeAverage_sq Q (hcoord i)
    _ = vecSqAvg Q F := (vecSqAvg_eq_sum_coordSq Q hF).symm

/-! ## The integrated single-cube Jensen: the `0`-exponent clause -/

/-- **The integrated single-cube Jensen with an arbitrary constant `Cc ≥ 1`.**
This is the printed concentration clause at exponent `0`: the `ℝ≥0∞` second moment
of the cube average is at most `Cc` times the annealed cube energy.  No
independence, centring or measurability of the field enters, only its `L̲²`
membership at each sample. -/
theorem lintegral_ofReal_vecNormSq_volumeAverageVec_le_mul_vecSqAvg_of_one_le
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Q : TriadicCube d) {F : Ω → Vec d → Vec d} {Cc : ℝ} (hCc : 1 ≤ Cc)
    (hL2 : ∀ ω, MemLp (hilbertifyVecField (F ω)) 2 (normalizedCubeMeasure Q)) :
    (∫⁻ ω, ENNReal.ofReal (vecNormSq (volumeAverageVec (cubeSet Q) (F ω))) ∂μ) ≤
      ENNReal.ofReal Cc * ∫⁻ ω, ENNReal.ofReal (vecSqAvg Q (F ω)) ∂μ := by
  have hpt : (∫⁻ ω, ENNReal.ofReal (vecNormSq (volumeAverageVec (cubeSet Q) (F ω))) ∂μ) ≤
      ∫⁻ ω, ENNReal.ofReal (vecSqAvg Q (F ω)) ∂μ :=
    lintegral_mono fun ω => ENNReal.ofReal_le_ofReal
      (vecNormSq_volumeAverageVec_le_vecSqAvg_of_memLp Q (hL2 ω))
  have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal Cc := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hCc
  calc (∫⁻ ω, ENNReal.ofReal (vecNormSq (volumeAverageVec (cubeSet Q) (F ω))) ∂μ)
      ≤ ∫⁻ ω, ENNReal.ofReal (vecSqAvg Q (F ω)) ∂μ := hpt
    _ = 1 * ∫⁻ ω, ENNReal.ofReal (vecSqAvg Q (F ω)) ∂μ := (one_mul _).symm
    _ ≤ ENNReal.ofReal Cc * ∫⁻ ω, ENNReal.ofReal (vecSqAvg Q (F ω)) ∂μ :=
        mul_le_mul' hone le_rfl

/-! ## The `0`-exponent branch of `hconc` is unconditional

For `S.m ≤ j + S.ℓ` the exponent `S.m − j − S.ℓ` is `0`, so the clause is the
integrated single-cube Jensen at the observable field.  The field is `L̲²` on
every cube by `ConcentrationMean.memLp_hilbertifyVecField_concDepthField_of_cube`,
so no input of the independence rule enters. -/

/-- **The `0`-exponent branch of the per-cube concentration, unconditional.**  For
every depth `j` with `S.m ≤ j + S.ℓ` and every depth-`j` descendant `R` of `cu_m`,
the per-cube concentration holds with the printed exponent `0`, from the `L̲²`
membership of the observable field alone plus the constant gate `1 ≤ Cc`. -/
theorem hconc_concDepthField_truncated [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) (e : Vec d) {Cc : ℝ}
    (hCc : 1 ≤ Cc) :
    ∀ j : ℕ, S.m ≤ j + S.ell → ∀ R ∈ descendantsAtDepth (originCube d (S.m : ℤ)) j,
      (∫⁻ omega, ENNReal.ofReal
          (vecNormSq (volumeAverageVec (cubeSet R) (concDepthField hnu P S e omega)))
          ∂P.toMeasure) ≤
        ENNReal.ofReal (Cc * (3 : ℝ) ^ (-((d : ℝ) * ((S.m - j - S.ell : ℕ) : ℝ)))) *
          (∫⁻ omega, ENNReal.ofReal
            (vecSqAvg R (concDepthField hnu P S e omega)) ∂P.toMeasure) := by
  intro j hj R _
  have hzero : S.m - j - S.ell = 0 := by omega
  have hbase := lintegral_ofReal_vecNormSq_volumeAverageVec_le_mul_vecSqAvg_of_one_le
    (μ := P.toMeasure) (Q := R) (F := fun omega => concDepthField hnu P S e omega) hCc
    (fun omega => memLp_hilbertifyVecField_concDepthField_of_cube hnu P S e omega R)
  simpa only [hzero, Nat.cast_zero, mul_zero, neg_zero, Real.rpow_zero, mul_one] using hbase

section Assembly

variable {nu : ℝ}

end Assembly

end

end SuperdiffusionCLT.Section3.Terms
