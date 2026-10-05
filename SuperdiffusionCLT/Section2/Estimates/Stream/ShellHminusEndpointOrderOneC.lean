/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Estimates.Stream.ShellHminusEndpointOrderOne

/-!
# The truncated multiscale bound for an `L̲²` vector field

The estimate `e.jk.Hminus.endpoint`, with the
`Continuous F` hypothesis of `ShellHminusEndpointOrderOneB.vecHatNegENormOrderOne_le_depthSum`
weakened to `MeasureTheory.MemLp (hilbertifyVecField F) 2 (normalizedCubeMeasure Q)`:
on a triadic cube `Q` of scale `l`, for an `L̲²` vector field `F` and every
truncation depth `J`,
`‖F‖_{Ĥ̲^{-1}(Q)} ≤ C(d)(∑_{j ≤ J} 3^{-j}(avsum_{R∈D_j}|(F)_R|²)^{1/2}
+ 3^{-J}‖F‖_{L̲²(Q)})`.

Continuity was used in `ShellHminusEndpointOrderOneB` only through the integrability,
on the cube and on its descendants, of the pointwise size, the coordinates and
the pairings of `F`, and through the descendant partition identities; here those
integrability steps are supplied from the `L̲²` membership instead, and every
smooth test input (`ContDiff` potential, Poincare aggregation, test constraint)
is reused from `ShellHminusEndpointOrderOne` unchanged.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Estimates.Stream

open Homogenization MeasureTheory
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section3.ResponseFields
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## `L̲²` on a cube for a merely integrable field -/

/-- The normalized cube measure is a scalar multiple of the volume restricted to
the cube. -/
theorem normalizedCubeMeasure_eq_smul_volume_restrict_cubeSet (Q : TriadicCube d) :
    normalizedCubeMeasure Q =
      ENNReal.ofReal ((cubeVolume Q)⁻¹) • volume.restrict (cubeSet Q) := rfl

theorem ofReal_cubeVolume_inv_ne_zero (Q : TriadicCube d) :
    ENNReal.ofReal ((cubeVolume Q)⁻¹) ≠ 0 :=
  (ENNReal.ofReal_pos.2 (inv_pos.2 (cubeVolume_pos Q))).ne'

theorem isFiniteMeasure_volume_restrict_cubeSet (Q : TriadicCube d) :
    IsFiniteMeasure (volume.restrict (cubeSet Q)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact volume_cubeSet_lt_top Q⟩

/-- **`L̲²` on a cube as an unnormalized square integrability condition.** -/
theorem memLp_two_iff_integrableOn_sq {E : Type*} [NormedAddCommGroup E]
    (Q : TriadicCube d) {f : Vec d → E}
    (hfm : AEStronglyMeasurable f (normalizedCubeMeasure Q)) :
    MemLp f 2 (normalizedCubeMeasure Q) ↔
      IntegrableOn (fun x => ‖f x‖ ^ 2) (cubeSet Q) volume := by
  rw [memLp_two_iff_integrable_sq_norm hfm,
    normalizedCubeMeasure_eq_smul_volume_restrict_cubeSet]
  exact integrable_smul_measure (ofReal_cubeVolume_inv_ne_zero Q) ENNReal.ofReal_ne_top

theorem integrableOn_sq_of_memLp_two {E : Type*} [NormedAddCommGroup E]
    (Q : TriadicCube d) {f : Vec d → E}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    IntegrableOn (fun x => ‖f x‖ ^ 2) (cubeSet Q) volume :=
  (memLp_two_iff_integrableOn_sq Q hf.aestronglyMeasurable).1 hf

theorem memLp_two_of_integrableOn_sq {E : Type*} [NormedAddCommGroup E]
    (Q : TriadicCube d) {f : Vec d → E}
    (hfm : AEStronglyMeasurable f (normalizedCubeMeasure Q))
    (hf : IntegrableOn (fun x => ‖f x‖ ^ 2) (cubeSet Q) volume) :
    MemLp f 2 (normalizedCubeMeasure Q) :=
  (memLp_two_iff_integrableOn_sq Q hfm).2 hf

/-- The `L̲²` membership descends from the normalized cube measure to the
restricted volume of the same cube. -/
theorem memLp_two_volume_restrict_of_memLp {E : Type*} [NormedAddCommGroup E]
    (Q : TriadicCube d) {f : Vec d → E}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    MemLp f 2 (volume.restrict (cubeSet Q)) := by
  have hc0 := ofReal_cubeVolume_inv_ne_zero Q
  have hfm : AEStronglyMeasurable f (volume.restrict (cubeSet Q)) :=
    hf.aestronglyMeasurable.mono_ac (Measure.absolutelyContinuous_smul hc0)
  have hint : Integrable (fun x => ‖f x‖ ^ 2) (volume.restrict (cubeSet Q)) := by
    have h := hf.integrable_norm_pow'
    rw [normalizedCubeMeasure_eq_smul_volume_restrict_cubeSet] at h
    exact (integrable_smul_measure hc0 ENNReal.ofReal_ne_top).1 h
  exact (memLp_two_iff_integrable_sq_norm hfm).2 hint

/-- `L̲²` transfers from a cube to any sub-cube. -/
theorem memLp_two_cubeSet_subset {E : Type*} [NormedAddCommGroup E]
    {Q R : TriadicCube d} {f : Vec d → E} (hsub : cubeSet R ⊆ cubeSet Q)
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    MemLp f 2 (normalizedCubeMeasure R) := by
  have hfm : AEStronglyMeasurable f (normalizedCubeMeasure R) := by
    rw [normalizedCubeMeasure_eq_smul_volume_restrict_cubeSet]
    exact ((hf.aestronglyMeasurable.mono_ac
      (Measure.absolutelyContinuous_smul (ofReal_cubeVolume_inv_ne_zero Q))).mono_set
        hsub).smul_measure _
  exact memLp_two_of_integrableOn_sq R hfm ((integrableOn_sq_of_memLp_two Q hf).mono_set hsub)

/-- A coordinate of an `L̲²` vector field is integrable on the cube. -/
theorem integrableOn_coord_of_memLp (Q : TriadicCube d) {F : Vec d → Vec d}
    (hF : MemLp (hilbertifyVecField F) 2 (normalizedCubeMeasure Q)) (i : Fin d) :
    IntegrableOn (fun x : Vec d => F x i) (cubeSet Q) volume := by
  have := isFiniteMeasure_volume_restrict_cubeSet Q
  have h : MemLp (fun x : Vec d => F x i) 2 (volume.restrict (cubeSet Q)) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).comp_memLp'
      (memLp_hilbertifyVecField_iff.1 (memLp_two_volume_restrict_of_memLp Q hF))
  exact h.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)

/-! ## The real-carrier readings for an `L̲²` field -/

theorem toReal_vecCubeLpENorm_two_sq_memLp (Q : TriadicCube d) {F : Vec d → Vec d}
    (hF : MemLp (hilbertifyVecField F) 2 (normalizedCubeMeasure Q)) :
    (vecCubeLpENorm Q 2 F).toReal ^ 2 = vecSqAvg Q F :=
  toReal_cubeLpENorm_two_sq Q hF

theorem toReal_vecCubeLpENorm_eq_sqrt_memLp (Q : TriadicCube d) {F : Vec d → Vec d}
    (hF : MemLp (hilbertifyVecField F) 2 (normalizedCubeMeasure Q)) :
    (vecCubeLpENorm Q 2 F).toReal = Real.sqrt (vecSqAvg Q F) := by
  rw [← toReal_vecCubeLpENorm_two_sq_memLp Q hF, Real.sqrt_sq ENNReal.toReal_nonneg]

/-- The descendant partition of a volume-normalized cube average, for an
integrable integrand. -/
theorem volumeAverage_eq_descendantsAverage_integrableOn (Q : TriadicCube d) (j : ℕ)
    {f : Vec d → ℝ} (hf : IntegrableOn f (cubeSet Q) volume) :
    volumeAverage (cubeSet Q) f =
      descendantsAverage Q j (fun R => volumeAverage (cubeSet R) f) :=
  volumeAverage_cubeSet_eq_inv_card_mul_sum_descendants Q j (fun _ hR =>
    (hf.mono_set (cubeSet_subset_of_mem_descendantsAtDepth hR)))

theorem vecSqAvg_eq_descendantsAverage_memLp (Q : TriadicCube d) (j : ℕ)
    {F : Vec d → Vec d} (hF : MemLp (hilbertifyVecField F) 2 (normalizedCubeMeasure Q)) :
    vecSqAvg Q F = descendantsAverage Q j (fun R => vecSqAvg R F) :=
  volumeAverage_eq_descendantsAverage_integrableOn Q j (integrableOn_sq_of_memLp_two Q hF)

theorem volumeAverageVec_eq_descendantsAverage_memLp (Q : TriadicCube d) (j : ℕ)
    {F : Vec d → Vec d} (hF : MemLp (hilbertifyVecField F) 2 (normalizedCubeMeasure Q))
    (i : Fin d) :
    volumeAverageVec (cubeSet Q) F i =
      descendantsAverage Q j (fun R => volumeAverageVec (cubeSet R) F i) :=
  volumeAverage_eq_descendantsAverage_integrableOn Q j (integrableOn_coord_of_memLp Q hF i)

/-- **The tower property of the cube averages**, in the pairing form, for an
`L̲²` field. -/
theorem vecDot_volumeAverageVec_eq_descendantsAverage_memLp (R : TriadicCube d) (j : ℕ)
    {F : Vec d → Vec d} (hF : MemLp (hilbertifyVecField F) 2 (normalizedCubeMeasure R))
    (c : Vec d) :
    vecDot (volumeAverageVec (cubeSet R) F) c =
      descendantsAverage R j
        (fun R' => vecDot (volumeAverageVec (cubeSet R') F) c) := by
  classical
  have hsum : descendantsAverage R j
      (fun R' => vecDot (volumeAverageVec (cubeSet R') F) c) =
      ∑ i : Fin d, descendantsAverage R j
        (fun R' => volumeAverageVec (cubeSet R') F i * c i) :=
    descendantsAverage_sum R j Finset.univ
      (fun R' i => volumeAverageVec (cubeSet R') F i * c i)
  rw [hsum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [descendantsAverage_mul_right,
    ← volumeAverageVec_eq_descendantsAverage_memLp R j hF i]

/-- **Cauchy-Schwarz on one triadic cube**, in the real square-average form, for
two `L̲²` fields. -/
theorem abs_volumeAverage_vecDot_le_sqrt_mul_sqrt_memLp (R : TriadicCube d)
    {F G : Vec d → Vec d}
    (hF : MemLp (hilbertifyVecField F) 2 (normalizedCubeMeasure R))
    (hG : MemLp (hilbertifyVecField G) 2 (normalizedCubeMeasure R)) :
    |volumeAverage (cubeSet R) (fun x => vecDot (F x) (G x))| ≤
      Real.sqrt (vecSqAvg R F) * Real.sqrt (vecSqAvg R G) := by
  have h := SuperdiffusionCLT.Section2.Norms.abs_volumeAverage_vecDot_le_mul
    (Q := R) (a := F) (b := G) hF hG
  rwa [toReal_vecCubeLpENorm_eq_sqrt_memLp R hF, toReal_vecCubeLpENorm_eq_sqrt_memLp R hG] at h

/-! ## Integrability of the pairings of an `L̲²` field -/

/-- The pairing of two `L̲²` fields is integrable on the cube. -/
theorem integrableOn_vecDot (R : TriadicCube d) {F G : Vec d → Vec d}
    (hF : MemLp (hilbertifyVecField F) 2 (normalizedCubeMeasure R))
    (hG : MemLp (hilbertifyVecField G) 2 (normalizedCubeMeasure R)) :
    IntegrableOn (fun x => vecDot (F x) (G x)) (cubeSet R) volume := by
  have := isFiniteMeasure_volume_restrict_cubeSet R
  have hFv := memLp_two_volume_restrict_of_memLp R hF
  have hGv := memLp_two_volume_restrict_of_memLp R hG
  have hint : ∀ i : Fin d, IntegrableOn (fun x : Vec d => F x i * G x i)
      (cubeSet R) volume := by
    intro i
    have h1 : MemLp (fun x : Vec d => F x i) 2 (volume.restrict (cubeSet R)) :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).comp_memLp'
        (memLp_hilbertifyVecField_iff.1 hFv)
    have h2 : MemLp (fun x : Vec d => G x i) 2 (volume.restrict (cubeSet R)) :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).comp_memLp'
        (memLp_hilbertifyVecField_iff.1 hGv)
    exact h1.integrable_mul h2
  have hpt : (fun x : Vec d => vecDot (F x) (G x))
      = fun x : Vec d => ∑ i : Fin d, F x i * G x i := rfl
  rw [hpt]
  exact integrable_finsetSum _ fun i _ => hint i

/-- The pairing of an `L̲²` field with a constant vector is integrable on the
cube. -/
theorem integrableOn_vecDot_const_left (R : TriadicCube d) {F : Vec d → Vec d}
    (hF : MemLp (hilbertifyVecField F) 2 (normalizedCubeMeasure R)) (c : Vec d) :
    IntegrableOn (fun x => vecDot (F x) c) (cubeSet R) volume := by
  have := isFiniteMeasure_volume_restrict_cubeSet R
  have hint : ∀ i : Fin d, IntegrableOn (fun x : Vec d => F x i * c i)
      (cubeSet R) volume := by
    intro i
    have h1 : MemLp (fun x : Vec d => F x i) 2 (volume.restrict (cubeSet R)) :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).comp_memLp'
        (memLp_hilbertifyVecField_iff.1 (memLp_two_volume_restrict_of_memLp R hF))
    have h2 : MemLp (fun _ : Vec d => c i) 2 (volume.restrict (cubeSet R)) :=
      memLp_const (c i)
    exact h1.integrable_mul h2
  have hpt : (fun x : Vec d => vecDot (F x) c)
      = fun x : Vec d => ∑ i : Fin d, F x i * c i := rfl
  rw [hpt]
  exact integrable_finsetSum _ fun i _ => hint i

/-- A constant factor comes out of a volume-normalized cube average of an `L̲²`
field's pairing. -/
theorem volumeAverage_vecDot_const_right_memLp (R : TriadicCube d) {F : Vec d → Vec d}
    (hF : MemLp (hilbertifyVecField F) 2 (normalizedCubeMeasure R)) (c : Vec d) :
    volumeAverage (cubeSet R) (fun x => vecDot (F x) c) =
      vecDot (volumeAverageVec (cubeSet R) F) c := by
  have h := volumeAverage_vecDot_const_left (cubeSet R) c (F := F)
    (fun i => integrableOn_coord_of_memLp R hF i)
  rw [vecDot_comm' (volumeAverageVec (cubeSet R) F) c, ← h]
  exact congrArg (volumeAverage (cubeSet R)) (funext fun x => vecDot_comm' (F x) c)

/-- A difference comes out of a volume-normalized cube average of two
integrable integrands. -/
theorem volumeAverage_cubeSet_sub_integrable (R : TriadicCube d) {f h : Vec d → ℝ}
    (hf : IntegrableOn f (cubeSet R) volume) (hh : IntegrableOn h (cubeSet R) volume) :
    volumeAverage (cubeSet R) (fun x => f x - h x) =
      volumeAverage (cubeSet R) f - volumeAverage (cubeSet R) h := by
  simp only [volumeAverage]
  rw [MeasureTheory.integral_sub hf hh]
  ring

/-- The centring identity on one cube: the pairing of an `L̲²` field with a
continuous field minus its constant-average truncation is the pairing against
the centred field. -/
theorem volumeAverage_vecDot_sub_average_memLp (R : TriadicCube d) {F G : Vec d → Vec d}
    (hF : MemLp (hilbertifyVecField F) 2 (normalizedCubeMeasure R))
    (hG : Continuous G) :
    volumeAverage (cubeSet R) (fun x => vecDot (F x) (G x)) -
        vecDot (volumeAverageVec (cubeSet R) F)
          (volumeAverageVec (cubeSet R) G) =
      volumeAverage (cubeSet R)
        (fun x => vecDot (F x) (G x - volumeAverageVec (cubeSet R) G)) := by
  have hsplit : (fun x => vecDot (F x) (G x - volumeAverageVec (cubeSet R) G))
      = fun x => vecDot (F x) (G x) -
          vecDot (F x) (volumeAverageVec (cubeSet R) G) :=
    funext fun x => vecDot_sub_right _ _ _
  have hint1 : IntegrableOn (fun x => vecDot (F x) (G x)) (cubeSet R) volume :=
    integrableOn_vecDot R hF
      (memLp_two_normalizedCubeMeasure_of_continuous R (continuous_hilbertifyVecField hG))
  have hint2 : IntegrableOn (fun x => vecDot (F x) (volumeAverageVec (cubeSet R) G))
      (cubeSet R) volume := integrableOn_vecDot_const_left R hF _
  rw [hsplit, volumeAverage_cubeSet_sub_integrable R hint1 hint2,
    volumeAverage_vecDot_const_right_memLp R hF]

/-- Pointwise congruence on the descendants of one depth. -/
theorem descendantsAverage_congr_of_forall (Q : TriadicCube d) (j : ℕ)
    (A B : TriadicCube d → ℝ) (h : ∀ R ∈ descendantsAtDepth Q j, A R = B R) :
    descendantsAverage Q j A = descendantsAverage Q j B := by
  classical
  have hsum : ∑ R ∈ descendantsAtDepth Q j, A R = ∑ R ∈ descendantsAtDepth Q j, B R :=
    Finset.sum_congr rfl fun R hR => h R hR
  simp only [descendantsAverage]
  exact congrArg _ hsum

/-! ## The depth-`j` truncation of the pairing -/

/-- **The depth-`J` truncation error of the pairing**, for an `L̲²` field. The
pairing of an `L̲²` vector field against an admissible order-one test gradient
differs from its depth-`J` sub-cube truncation by at most
`C(d) 3^{l-J} ‖F‖_{L̲²(Q)} ‖∇²g‖_{L̲²(Q)}`. -/
theorem abs_volumeAverage_vecDot_sub_depthPairing_le_memLp (hd : 0 < d)
    (Q : TriadicCube d) (j : ℕ) {F : Vec d → Vec d}
    (hF : MemLp (hilbertifyVecField F) 2 (normalizedCubeMeasure Q))
    {g : Vec d → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    |volumeAverage (cubeSet Q) (fun x => vecDot (F x) (euclideanGradient g x)) -
        descendantsAverage Q j (fun R => vecDot (volumeAverageVec (cubeSet R) F)
          (volumeAverageVec (cubeSet R) (euclideanGradient g)))| ≤
      Real.sqrt (vecSqAvg Q F) *
        (poincareCubeConst d * ((3 : ℝ) ^ Q.scale * ((3 : ℝ) ^ j)⁻¹) *
          Real.sqrt (matSqAvg Q (euclideanGradientJacobian g))) := by
  set G : Vec d → Vec d := euclideanGradient g with hGdef
  have hGcont : Continuous G := continuous_euclideanGradient' hg
  set K : ℝ := poincareCubeConst d * ((3 : ℝ) ^ Q.scale * ((3 : ℝ) ^ j)⁻¹) with hKdef
  have hKnn : 0 ≤ K :=
    mul_nonneg (poincareCubeConst_nonneg d) (by positivity)
  have hFdesc : ∀ R ∈ descendantsAtDepth Q j,
      MemLp (hilbertifyVecField F) 2 (normalizedCubeMeasure R) :=
    fun R hR => memLp_two_cubeSet_subset (cubeSet_subset_of_mem_descendantsAtDepth hR) hF
  have hid : volumeAverage (cubeSet Q) (fun x => vecDot (F x) (G x)) -
      descendantsAverage Q j (fun R => vecDot (volumeAverageVec (cubeSet R) F)
        (volumeAverageVec (cubeSet R) G)) =
      descendantsAverage Q j (fun R => volumeAverage (cubeSet R)
        (fun x => vecDot (F x) (G x - volumeAverageVec (cubeSet R) G))) := by
    rw [volumeAverage_eq_descendantsAverage_integrableOn Q j
      (integrableOn_vecDot Q hF (memLp_two_normalizedCubeMeasure_of_continuous Q
        (continuous_hilbertifyVecField hGcont))), descendantsAverage_sub]
    exact descendantsAverage_congr_of_forall Q j _ _
      (fun R hR => volumeAverage_vecDot_sub_average_memLp R (hFdesc R hR) hGcont)
  rw [hid]
  refine le_trans (abs_descendantsAverage_le Q j _) ?_
  have hCS : ∀ R ∈ descendantsAtDepth Q j,
      |volumeAverage (cubeSet R)
          (fun x => vecDot (F x) (G x - volumeAverageVec (cubeSet R) G))| ≤
        Real.sqrt (vecSqAvg R F) *
          Real.sqrt (vecSqAvg R (fun x => G x - volumeAverageVec (cubeSet R) G)) :=
    fun R hR => abs_volumeAverage_vecDot_le_sqrt_mul_sqrt_memLp R (hFdesc R hR)
      (memLp_two_normalizedCubeMeasure_of_continuous R
        (continuous_hilbertifyVecField (hGcont.sub continuous_const)))
  refine le_trans (descendantsAverage_le_descendantsAverage Q j hCS) ?_
  refine le_trans (descendantsAverage_mul_le_sqrt_mul_sqrt Q j _ _) ?_
  have hA : descendantsAverage Q j (fun R => Real.sqrt (vecSqAvg R F) ^ 2) =
      vecSqAvg Q F := by
    rw [show (fun R : TriadicCube d => Real.sqrt (vecSqAvg R F) ^ 2)
        = fun R : TriadicCube d => vecSqAvg R F from
      funext fun R => Real.sq_sqrt (vecSqAvg_nonneg R F)]
    exact (vecSqAvg_eq_descendantsAverage_memLp Q j hF).symm
  have hB : descendantsAverage Q j (fun R =>
        Real.sqrt (vecSqAvg R (fun x => G x - volumeAverageVec (cubeSet R) G)) ^ 2) =
      descendantsAverage Q j (fun R =>
        vecSqAvg R (fun x => G x - volumeAverageVec (cubeSet R) G)) :=
    congrArg (descendantsAverage Q j)
      (funext fun R => Real.sq_sqrt (vecSqAvg_nonneg R _))
  rw [hA, hB]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  have hKP := descendantsAverage_vecSqAvg_sub_average_le hd Q j hg
  rw [← hKdef] at hKP
  calc Real.sqrt (descendantsAverage Q j (fun R =>
        vecSqAvg R (fun x => G x - volumeAverageVec (cubeSet R) G)))
      ≤ Real.sqrt (K ^ 2 * matSqAvg Q (euclideanGradientJacobian g)) :=
        Real.sqrt_le_sqrt hKP
    _ = K * Real.sqrt (matSqAvg Q (euclideanGradientJacobian g)) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hKnn]

/-! ## The telescoping increment -/

/-- **The depth-`j` increment of the truncated pairing**, for an `L̲²` field. -/
theorem abs_depthPairing_succ_sub_le_memLp (hd : 0 < d) (Q : TriadicCube d) (j : ℕ)
    {F : Vec d → Vec d}
    (hF : MemLp (hilbertifyVecField F) 2 (normalizedCubeMeasure Q))
    {g : Vec d → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    |descendantsAverage Q (j + 1) (fun R => vecDot (volumeAverageVec (cubeSet R) F)
          (volumeAverageVec (cubeSet R) (euclideanGradient g))) -
        descendantsAverage Q j (fun R => vecDot (volumeAverageVec (cubeSet R) F)
          (volumeAverageVec (cubeSet R) (euclideanGradient g)))| ≤
      vecDepthMoment Q (j + 1) F *
        (poincareCubeConst d * ((3 : ℝ) ^ Q.scale * ((3 : ℝ) ^ j)⁻¹) *
          Real.sqrt (matSqAvg Q (euclideanGradientJacobian g))) := by
  set G : Vec d → Vec d := euclideanGradient g with hGdef
  have hGcont : Continuous G := continuous_euclideanGradient' hg
  set K : ℝ := poincareCubeConst d * ((3 : ℝ) ^ Q.scale * ((3 : ℝ) ^ j)⁻¹) with hKdef
  have hKnn : 0 ≤ K :=
    mul_nonneg (poincareCubeConst_nonneg d) (by positivity)
  -- the increment as an iterated average
  have hFdesc : ∀ R ∈ descendantsAtDepth Q j,
      MemLp (hilbertifyVecField F) 2 (normalizedCubeMeasure R) :=
    fun R hR => memLp_two_cubeSet_subset (cubeSet_subset_of_mem_descendantsAtDepth hR) hF
  have hid : descendantsAverage Q (j + 1) (fun R => vecDot
        (volumeAverageVec (cubeSet R) F) (volumeAverageVec (cubeSet R) G)) -
      descendantsAverage Q j (fun R => vecDot (volumeAverageVec (cubeSet R) F)
        (volumeAverageVec (cubeSet R) G)) =
      descendantsAverage Q j (fun R => descendantsAverage R 1 (fun R' =>
        vecDot (volumeAverageVec (cubeSet R') F)
          (volumeAverageVec (cubeSet R') G - volumeAverageVec (cubeSet R) G))) := by
    rw [descendantsAverage_succ_eq_descendantsAverage_descendantsAverage,
      descendantsAverage_sub]
    refine descendantsAverage_congr_of_forall Q j _ _ fun R hR => ?_
    rw [vecDot_volumeAverageVec_eq_descendantsAverage_memLp R 1 (hFdesc R hR)
      (volumeAverageVec (cubeSet R) G), descendantsAverage_sub]
    exact congrArg (descendantsAverage R 1) (funext fun R' => (vecDot_sub_right _ _ _).symm)
  rw [hid]
  -- two absolute values and the pointwise Cauchy-Schwarz
  refine le_trans (abs_descendantsAverage_le Q j _) ?_
  have hinner : ∀ R ∈ descendantsAtDepth Q j,
      |descendantsAverage R 1 (fun R' => vecDot (volumeAverageVec (cubeSet R') F)
          (volumeAverageVec (cubeSet R') G - volumeAverageVec (cubeSet R) G))| ≤
        Real.sqrt (descendantsAverage R 1
            (fun R' => vecNorm (volumeAverageVec (cubeSet R') F) ^ 2)) *
          Real.sqrt (descendantsAverage R 1 (fun R' =>
            vecNorm (volumeAverageVec (cubeSet R') G -
              volumeAverageVec (cubeSet R) G) ^ 2)) := by
    intro R _
    refine le_trans (abs_descendantsAverage_le R 1 _) ?_
    refine le_trans (descendantsAverage_le_descendantsAverage R 1
      (fun R' _ => abs_vecDot_le_vecNorm_mul_vecNorm _ _)) ?_
    exact descendantsAverage_mul_le_sqrt_mul_sqrt R 1 _ _
  refine le_trans (descendantsAverage_le_descendantsAverage Q j hinner) ?_
  refine le_trans (descendantsAverage_mul_le_sqrt_mul_sqrt Q j _ _) ?_
  -- identify the two factors
  have hnnA : ∀ R : TriadicCube d, 0 ≤ descendantsAverage R 1
      (fun R' => vecNorm (volumeAverageVec (cubeSet R') F) ^ 2) :=
    fun R => descendantsAverage_nonneg R 1 _ fun _ _ => by positivity
  have hnnB : ∀ R : TriadicCube d, 0 ≤ descendantsAverage R 1 (fun R' =>
      vecNorm (volumeAverageVec (cubeSet R') G -
        volumeAverageVec (cubeSet R) G) ^ 2) :=
    fun R => descendantsAverage_nonneg R 1 _ fun _ _ => by positivity
  have hA : descendantsAverage Q j (fun R => Real.sqrt (descendantsAverage R 1
        (fun R' => vecNorm (volumeAverageVec (cubeSet R') F) ^ 2)) ^ 2) =
      vecDepthSqMoment Q (j + 1) F := by
    rw [show (fun R : TriadicCube d => Real.sqrt (descendantsAverage R 1
          (fun R' => vecNorm (volumeAverageVec (cubeSet R') F) ^ 2)) ^ 2)
        = fun R : TriadicCube d => descendantsAverage R 1
          (fun R' => vecNorm (volumeAverageVec (cubeSet R') F) ^ 2) from
      funext fun R => Real.sq_sqrt (hnnA R)]
    rw [vecDepthSqMoment,
      descendantsAverage_succ_eq_descendantsAverage_descendantsAverage]
    exact congrArg (descendantsAverage Q j) (funext fun R =>
      congrArg (descendantsAverage R 1) (funext fun R' => Book.Ch02.vecNorm_sq_eq_vecNormSq _))
  have hB : descendantsAverage Q j (fun R => Real.sqrt (descendantsAverage R 1
        (fun R' => vecNorm (volumeAverageVec (cubeSet R') G -
          volumeAverageVec (cubeSet R) G) ^ 2)) ^ 2) ≤
      K ^ 2 * matSqAvg Q (euclideanGradientJacobian g) := by
    rw [show (fun R : TriadicCube d => Real.sqrt (descendantsAverage R 1
          (fun R' => vecNorm (volumeAverageVec (cubeSet R') G -
            volumeAverageVec (cubeSet R) G) ^ 2)) ^ 2)
        = fun R : TriadicCube d => descendantsAverage R 1
          (fun R' => vecNorm (volumeAverageVec (cubeSet R') G -
            volumeAverageVec (cubeSet R) G) ^ 2) from
      funext fun R => Real.sq_sqrt (hnnB R)]
    have hstep : ∀ R ∈ descendantsAtDepth Q j,
        descendantsAverage R 1 (fun R' => vecNorm (volumeAverageVec (cubeSet R') G -
            volumeAverageVec (cubeSet R) G) ^ 2) ≤
          vecSqAvg R (fun x => G x - volumeAverageVec (cubeSet R) G) := by
      intro R _
      have hcent : Continuous (fun x => G x - volumeAverageVec (cubeSet R) G) :=
        hGcont.sub continuous_const
      have hpt : ∀ R' : TriadicCube d,
          vecNorm (volumeAverageVec (cubeSet R') G -
              volumeAverageVec (cubeSet R) G) ^ 2 ≤
            vecSqAvg R' (fun x => G x - volumeAverageVec (cubeSet R) G) := by
        intro R'
        rw [Book.Ch02.vecNorm_sq_eq_vecNormSq, ← volumeAverageVec_sub_const R' hGcont
          (volumeAverageVec (cubeSet R) G)]
        exact vecNormSq_volumeAverageVec_le R' hcent
      refine le_trans (descendantsAverage_le_descendantsAverage R 1
        (fun R' _ => hpt R')) ?_
      exact le_of_eq (vecSqAvg_eq_descendantsAverage R 1 hcent).symm
    refine le_trans (descendantsAverage_le_descendantsAverage Q j hstep) ?_
    have hKP := descendantsAverage_vecSqAvg_sub_average_le hd Q j hg
    rw [← hKdef] at hKP
    exact hKP
  rw [hA]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  calc Real.sqrt (descendantsAverage Q j (fun R => Real.sqrt (descendantsAverage R 1
        (fun R' => vecNorm (volumeAverageVec (cubeSet R') G -
          volumeAverageVec (cubeSet R) G) ^ 2)) ^ 2))
      ≤ Real.sqrt (K ^ 2 * matSqAvg Q (euclideanGradientJacobian g)) :=
        Real.sqrt_le_sqrt hB
    _ = K * Real.sqrt (matSqAvg Q (euclideanGradientJacobian g)) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hKnn]

/-! ## The truncated multiscale bound -/

/-- **The truncated multiscale Poincare inequality at order one**, for one
admissible test potential and an `L̲²` field: the pairing `⨍_Q F·∇g` is at most
the printed `ℓ¹` depth sum down to depth `J`, plus the truncation remainder
`3^{-J}‖F‖_{L̲²(Q)}`. -/
theorem volumeAverage_vecGradientPairingDensity_le_memLp (hd : 0 < d)
    (Q : TriadicCube d) {F : Vec d → Vec d}
    (hF : MemLp (hilbertifyVecField F) 2 (normalizedCubeMeasure Q)) (J : ℕ)
    {g : Vec d → ℝ} (hg : IsVecHatTestFieldOrderOne Q g) :
    volumeAverage (cubeSet Q) (vecGradientPairingDensity F g) ≤
      multiscaleOrderOneConst d *
        ((∑ j ∈ Finset.range (J + 1), ((3 : ℝ) ^ j)⁻¹ * vecDepthMoment Q j F) +
          ((3 : ℝ) ^ J)⁻¹ * Real.sqrt (vecSqAvg Q F)) := by
  classical
  set G : Vec d → Vec d := euclideanGradient g with hGdef
  set H : Vec d → Mat d := euclideanGradientJacobian g with hHdef
  have hGcont : Continuous G := continuous_euclideanGradient' hg.contDiff
  set C : ℝ := poincareCubeConst d with hCdef
  have hCnn : 0 ≤ C := poincareCubeConst_nonneg d
  set S : ℝ := (3 : ℝ) ^ Q.scale * Real.sqrt (matSqAvg Q H) with hSdef
  have hS1 : S ≤ 1 := threePow_mul_sqrt_matSqAvg_le_one hg
  have hSnn : 0 ≤ S := by
    rw [hSdef]
    positivity
  set P : ℕ → ℝ := fun j => descendantsAverage Q j
    (fun R => vecDot (volumeAverageVec (cubeSet R) F)
      (volumeAverageVec (cubeSet R) G)) with hPdef
  set I : ℝ := volumeAverage (cubeSet Q) (fun x => vecDot (F x) (G x)) with hIdef
  have hdens : volumeAverage (cubeSet Q) (vecGradientPairingDensity F g) = I := by
    rw [hIdef]
    exact congrArg (volumeAverage (cubeSet Q))
      (funext fun x =>
        SuperdiffusionCLT.Section2.Norms.vecGradientPairingDensity_eq_vecDot F g x)
  rw [hdens]
  -- the weights
  have hw : ∀ j : ℕ, (0 : ℝ) ≤ ((3 : ℝ) ^ j)⁻¹ := fun j => by positivity
  have hterm : ∀ j : ℕ, (0 : ℝ) ≤ ((3 : ℝ) ^ j)⁻¹ * vecDepthMoment Q j F :=
    fun j => mul_nonneg (hw j) (vecDepthMoment_nonneg Q j F)
  set T : ℝ := ∑ j ∈ Finset.range (J + 1), ((3 : ℝ) ^ j)⁻¹ * vecDepthMoment Q j F
    with hTdef
  have hTnn : 0 ≤ T := Finset.sum_nonneg fun j _ => hterm j
  -- the three pieces
  have hP0 : P 0 = vecDot (volumeAverageVec (cubeSet Q) F)
      (volumeAverageVec (cubeSet Q) G) := descendantsAverage_zero Q _
  have h0 : |P 0| ≤ vecDepthMoment Q 0 F := by
    rw [hP0, vecDepthMoment_zero]
    refine le_trans (abs_vecDot_le_vecNorm_mul_vecNorm _ _) ?_
    have hG1 : vecNorm (volumeAverageVec (cubeSet Q) G) ≤ 1 :=
      le_trans (vecNorm_volumeAverageVec_le_sqrt Q hGcont)
        (sqrt_vecSqAvg_euclideanGradient_le_one hg)
    calc vecNorm (volumeAverageVec (cubeSet Q) F) *
          vecNorm (volumeAverageVec (cubeSet Q) G)
        ≤ vecNorm (volumeAverageVec (cubeSet Q) F) * 1 :=
          mul_le_mul_of_nonneg_left hG1 (vecNorm_nonneg _)
      _ = vecNorm (volumeAverageVec (cubeSet Q) F) := mul_one _
  have hstep : ∀ j : ℕ, |P (j + 1) - P j| ≤
      3 * C * (((3 : ℝ) ^ (j + 1))⁻¹ * vecDepthMoment Q (j + 1) F) := by
    intro j
    refine le_trans (abs_depthPairing_succ_sub_le_memLp hd Q j hF hg.contDiff) ?_
    have hrw : vecDepthMoment Q (j + 1) F *
        (C * ((3 : ℝ) ^ Q.scale * ((3 : ℝ) ^ j)⁻¹) * Real.sqrt (matSqAvg Q H)) =
        (C * (((3 : ℝ) ^ j)⁻¹ * vecDepthMoment Q (j + 1) F)) * S := by
      rw [hSdef]; ring
    rw [hrw]
    have hle : (C * (((3 : ℝ) ^ j)⁻¹ * vecDepthMoment Q (j + 1) F)) * S ≤
        (C * (((3 : ℝ) ^ j)⁻¹ * vecDepthMoment Q (j + 1) F)) * 1 :=
      mul_le_mul_of_nonneg_left hS1
        (mul_nonneg hCnn (mul_nonneg (hw j) (vecDepthMoment_nonneg Q (j + 1) F)))
    refine le_trans hle (le_of_eq ?_)
    have h3 : ((3 : ℝ) ^ (j + 1))⁻¹ = ((3 : ℝ) ^ j)⁻¹ / 3 := by
      rw [pow_succ, mul_inv]
      ring
    rw [h3]
    ring
  have hrem : |I - P J| ≤ C * (((3 : ℝ) ^ J)⁻¹ * Real.sqrt (vecSqAvg Q F)) := by
    refine le_trans
      (abs_volumeAverage_vecDot_sub_depthPairing_le_memLp hd Q J hF hg.contDiff) ?_
    have hrw : Real.sqrt (vecSqAvg Q F) *
        (C * ((3 : ℝ) ^ Q.scale * ((3 : ℝ) ^ J)⁻¹) * Real.sqrt (matSqAvg Q H)) =
        (C * (((3 : ℝ) ^ J)⁻¹ * Real.sqrt (vecSqAvg Q F))) * S := by
      rw [hSdef]; ring
    rw [hrw]
    have hle : (C * (((3 : ℝ) ^ J)⁻¹ * Real.sqrt (vecSqAvg Q F))) * S ≤
        (C * (((3 : ℝ) ^ J)⁻¹ * Real.sqrt (vecSqAvg Q F))) * 1 :=
      mul_le_mul_of_nonneg_left hS1
        (mul_nonneg hCnn (mul_nonneg (hw J) (Real.sqrt_nonneg _)))
    rw [mul_one] at hle
    exact hle
  -- the telescoping identity
  have htel : I = P 0 + (∑ j ∈ Finset.range J, (P (j + 1) - P j)) + (I - P J) := by
    rw [Finset.sum_range_sub P J]
    ring
  have hchain : I ≤ |P 0| + (∑ j ∈ Finset.range J, |P (j + 1) - P j|) +
      |I - P J| := by
    have h1 : P 0 ≤ |P 0| := le_abs_self _
    have h2 : (∑ j ∈ Finset.range J, (P (j + 1) - P j)) ≤
        ∑ j ∈ Finset.range J, |P (j + 1) - P j| :=
      Finset.sum_le_sum fun j _ => le_abs_self _
    have h3 : I - P J ≤ |I - P J| := le_abs_self _
    linarith only [htel, h1, h2, h3]
  -- the sum of the increments
  have hsumstep : (∑ j ∈ Finset.range J, |P (j + 1) - P j|) ≤ 3 * C * T := by
    have hb : (∑ j ∈ Finset.range J, |P (j + 1) - P j|) ≤
        ∑ j ∈ Finset.range J,
          3 * C * (((3 : ℝ) ^ (j + 1))⁻¹ * vecDepthMoment Q (j + 1) F) :=
      Finset.sum_le_sum fun j _ => hstep j
    refine le_trans hb ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hsplit : T = (∑ j ∈ Finset.range J,
        ((3 : ℝ) ^ (j + 1))⁻¹ * vecDepthMoment Q (j + 1) F) +
        ((3 : ℝ) ^ 0)⁻¹ * vecDepthMoment Q 0 F := by
      rw [hTdef]
      exact Finset.sum_range_succ' (fun j => ((3 : ℝ) ^ j)⁻¹ * vecDepthMoment Q j F) J
    have h0nn : (0 : ℝ) ≤ ((3 : ℝ) ^ 0)⁻¹ * vecDepthMoment Q 0 F := hterm 0
    linarith only [hsplit, h0nn]
  -- the depth-zero term
  have hzero : vecDepthMoment Q 0 F ≤ T := by
    have hmem : (0 : ℕ) ∈ Finset.range (J + 1) := Finset.mem_range.2 (Nat.succ_pos J)
    have hle := Finset.single_le_sum
      (f := fun j => ((3 : ℝ) ^ j)⁻¹ * vecDepthMoment Q j F)
      (fun j _ => hterm j) hmem
    simpa using hle
  -- assemble
  have hfinal : I ≤ T + 3 * C * T + C * (((3 : ℝ) ^ J)⁻¹ * Real.sqrt (vecSqAvg Q F)) := by
    have := le_trans h0 hzero
    linarith only [hchain, this, hsumstep, hrem]
  have hCle : C ≤ multiscaleOrderOneConst d :=
    poincareCubeConst_le_multiscaleOrderOneConst d
  have hRnn : (0 : ℝ) ≤ ((3 : ℝ) ^ J)⁻¹ * Real.sqrt (vecSqAvg Q F) :=
    mul_nonneg (hw J) (Real.sqrt_nonneg _)
  have hexp : multiscaleOrderOneConst d * (T + ((3 : ℝ) ^ J)⁻¹ *
      Real.sqrt (vecSqAvg Q F)) =
      (1 + 3 * C) * T + multiscaleOrderOneConst d *
        (((3 : ℝ) ^ J)⁻¹ * Real.sqrt (vecSqAvg Q F)) := by
    rw [multiscaleOrderOneConst, hCdef]
    ring
  rw [hexp]
  have hlast : C * (((3 : ℝ) ^ J)⁻¹ * Real.sqrt (vecSqAvg Q F)) ≤
      multiscaleOrderOneConst d * (((3 : ℝ) ^ J)⁻¹ * Real.sqrt (vecSqAvg Q F)) :=
    mul_le_mul_of_nonneg_right hCle hRnn
  linarith only [hfinal, hlast]

/-- **The truncated multiscale Poincare inequality at order one.**  For an
`L̲²` field `F` on a triadic cube `Q` of scale `l` and every truncation
depth `J`,

`‖F‖_{Ĥ̲^{-1}(Q)} ≤ C(d) ( ∑_{j ≤ J} 3^{-j} (avsum_{R ∈ D_j} |(F)_R|²)^{1/2}
    + 3^{-J} ‖F‖_{L̲²(Q)} )`.

This is `ShellHminusEndpointOrderOneB.vecHatNegENormOrderOne_le_depthSum` with the
`Continuous F` hypothesis replaced by `L̲²` membership on the cube. -/
theorem vecHatNegENormOrderOne_le_depthSum_memLp (hd : 0 < d) (Q : TriadicCube d)
    {F : Vec d → Vec d}
    (hF : MeasureTheory.MemLp (hilbertifyVecField F) 2 (normalizedCubeMeasure Q))
    (J : ℕ) :
    vecHatNegENormOrderOne Q F ≤ ENNReal.ofReal (multiscaleOrderOneConst d *
      ((∑ j ∈ Finset.range (J + 1), ((3 : ℝ) ^ j)⁻¹ * vecDepthMoment Q j F) +
        ((3 : ℝ) ^ J)⁻¹ * Real.sqrt (vecSqAvg Q F))) :=
  vecHatNegENormOrderOne_le fun _g hg => ENNReal.ofReal_le_ofReal
    (volumeAverage_vecGradientPairingDensity_le_memLp hd Q hF J hg)

end

end SuperdiffusionCLT.Section2.Estimates.Stream