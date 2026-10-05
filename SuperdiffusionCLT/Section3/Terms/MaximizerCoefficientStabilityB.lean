/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.MaximizerCoefficientStability
public import SuperdiffusionCLT.Section3.Terms.MaximizerGradientL2
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# The cube maximizer gradient class is Lipschitz in the sample

`MaximizerCoefficientStability.lean` proves that the gradient of a Chapter 2
response maximizer of the pure-flux loading `(0, F)` is Lipschitz in the
coefficient, in the `L∞(U)` operator norm, whenever both coefficients have
symmetric part `ν Id`.  Both cube coefficients of `e.u.k.y.def` have symmetric
part exactly `ν Id` (`symmPart_coefficientCutoff`, an identity, not an
assumption) and differ only in the sample, so the estimate specializes to the
sample dependence of the cube maximizer of `GluedField.lean`:

`ν² ‖[∇u_{k,z}(ω)] − [∇u_{k,z}(ω')]‖_{L²(z)} ≤ 3 M ‖F‖_{L²(z)}`,

with `M` any bound for the operator norm of `k_L(ω, ·) − k_L(ω', ·)` on the
cube.  The sample enters the cube problem only through `k_L`, so this is the
complete modulus of continuity of the cube maximizer in the sample.

## From the estimate to measurability

The sample estimate is the whole modulus of continuity of `ω ↦ [∇u_{k,z}(ω)]`
for the pseudometric `ω, ω' ↦ ‖k_L(ω, ·) − k_L(ω', ·)‖_{L∞(z)}`, which is
uniform convergence on the closed cube; the compact-open carrier of one shell
(`Frozen.Assumptions.ShellField`) makes that modulus small near any
sample, so the sub-cube class map is *continuous* in the sample.  The sample
carrier is a countable product of second-countable Borel spaces, hence a Borel
space for its product topology, so the sub-cube class map is measurable.  The
glued field of `e.u.k.def` is the finite sum of the sub-cube gradients against
the indicators of the half-open sub-cubes, and zero-extension is an isometry of
class spaces, so the `L²(cu_m)` class of the glued field is measurable in the
sample.  That is exactly the fact needed by `GluedFieldL2Class.lean`, so the
measurability obligation of `RHSTerm1.lean` is proved here.

## Main results

* `cubeMaximizerGradientClass`: the `L²(z)` class of `∇u_{k,z}`.
* `symmPart_cubeCutoffCoeffOn`, `cubeCutoffCoeffOn_toCoeffField_sub`: the two
  structural facts about the cube coefficient that make the estimate apply.
* `norm_cubeMaximizerGradientClass_sub_le`: the sample estimate.
* `eventually_forall_mem_matrixOperatorNorm_streamCutoff_sub_le`: the sample
  modulus of the cutoff coefficient on a compact set.
* `continuous_cubeMaximizerGradientClass`,
  `measurable_cubeMaximizerGradientClass`: the sub-cube class map.
* `extendCubeClass`, `norm_extendCubeClass_sub`, `gluedGradientClass_eq_sum`:
  zero-extension and the glued class as a sum of sub-cube classes.
* `measurable_gluedGradientClass`,
  `aemeasurable_ofReal_abs_volumeAverage_vecDot_grad_gluedField`: the glued
  class measurability and the measurability obligation of `RHSTerm1.lean`.

## References

* The paper: `e.u.k.y.def`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.CoarseGraining
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Localization
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section2.Estimates.Stream
open Homogenization
open Filter Topology
open scoped ENNReal
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-! ## The cube coefficient of `e.u.k.y.def` -/

section CubeCoefficient

variable {nu : ℝ}

/-- **The symmetric part of the cube coefficient is `ν Id`.**  This is the
pointwise identity `symmPart_coefficientCutoff`, a consequence of the
anti-symmetry of the shells, read on the Chapter 2 coefficient object of the
cube. -/
theorem symmPart_cubeCutoffCoeffOn (hnu : 0 < nu) (omega : ShellSeq d) (L : ℕ)
    (z : TriadicCube d) (x : Vec d) :
    symmPart ((cubeCutoffCoeffOn hnu omega L z).toCoeffField x) = nu • (1 : Mat d) := by
  rw [cubeCutoffCoeffOn_toCoeffField]
  exact symmPart_coefficientCutoff nu omega L x

/-- **The sample dependence of the cube coefficient is the stream cutoff.**  The
two cube coefficients of two samples differ exactly by `k_L(ω, ·) − k_L(ω', ·)`;
the elliptic part `ν Id` cancels. -/
theorem cubeCutoffCoeffOn_toCoeffField_sub (hnu : 0 < nu) (omega omega' : ShellSeq d)
    (L : ℕ) (z : TriadicCube d) (x : Vec d) :
    (cubeCutoffCoeffOn hnu omega L z).toCoeffField x -
        (cubeCutoffCoeffOn hnu omega' L z).toCoeffField x =
      streamCutoff omega L x - streamCutoff omega' L x := by
  rw [cubeCutoffCoeffOn_toCoeffField, cubeCutoffCoeffOn_toCoeffField,
    coefficientCutoff_toCoeffField_apply, coefficientCutoff_toCoeffField_apply]
  abel

end CubeCoefficient

/-! ## The `L²(z)` class of the cube maximizer gradient -/

section MaximizerClass

variable {nu : ℝ}

/-- **The `L²(z)` class of `∇u_{k,z}`**, the cube-wise maximizer gradient of
`e.u.k.y.def` read as an element of the class space. -/
def cubeMaximizerGradientClass (hnu : 0 < nu) (omega : ShellSeq d) (L : ℕ)
    (F : Vec d) (z : TriadicCube d) : HilbertVectorL2 (openCubeSet z) :=
  toHilbertVectorL2OfVecField (memVectorL2_cubeMaximizerGradient hnu omega L F z)

end MaximizerClass

/-! ## The sample estimate -/

section SampleStability

variable {nu : ℝ}

/-- **The cube maximizer gradient class is Lipschitz in the sample.**

For two samples and the same cutoff level, the `L²(z)` classes of the cube
maximizer gradients of `e.u.k.y.def` satisfy

`ν² ‖[∇u_{k,z}(ω)] − [∇u_{k,z}(ω')]‖ ≤ 3 M ‖F‖_{L²(z)}`,

where `M` bounds the operator norm of `k_L(ω, ·) − k_L(ω', ·)` almost everywhere
on the cube.  The only inputs are the identity `symmPart a_L = ν Id`, the
cube-Dirichlet transfer of `Section2/Localization/CutoffComparison.lean`,
and the Chapter 2 first-variation theorem; in particular the estimate holds for
the choice-made maximizer `cubeMaximizer`, with no extra hypothesis on
the choice. -/
theorem norm_cubeMaximizerGradientClass_sub_le [NeZero d] (hnu : 0 < nu)
    (omega omega' : ShellSeq d) (L : ℕ) (F : Vec d) (z : TriadicCube d) {M : ℝ}
    (hM : ∀ᵐ x ∂volumeMeasureOn (openCubeSet z),
      Book.Ch02.matrixOperatorNorm
        (streamCutoff omega L x - streamCutoff omega' L x) ≤ M) :
    nu ^ 2 * ‖cubeMaximizerGradientClass hnu omega L F z -
        cubeMaximizerGradientClass hnu omega' L F z‖ ≤
      3 * M * ‖toHilbertVectorL2OfVecField
        (memVectorL2_const (U := openCubeSet z) F)‖ := by
  have hM' : ∀ᵐ x ∂volumeMeasureOn
      ((Book.Ch02.cubeDomain z : Book.Ch02.Domain d) : Set (Vec d)),
      Book.Ch02.matrixOperatorNorm
        ((cubeCutoffCoeffOn hnu omega L z).toCoeffField x -
          (cubeCutoffCoeffOn hnu omega' L z).toCoeffField x) ≤ M := by
    filter_upwards [hM] with x hx
    rwa [cubeCutoffCoeffOn_toCoeffField_sub]
  exact norm_gradToHilbertVectorL2_sub_le_of_isResponseMaximizer hnu
    (Filter.Eventually.of_forall (symmPart_cubeCutoffCoeffOn hnu omega L z))
    (Filter.Eventually.of_forall (symmPart_cubeCutoffCoeffOn hnu omega' L z))
    hM'
    (cubeMaximizer hnu omega L F z).isMaximizer
    (cubeMaximizer hnu omega' L F z).isMaximizer

/-- The sample estimate with an everywhere bound on the open cube. -/
theorem norm_cubeMaximizerGradientClass_sub_le_of_forall_mem [NeZero d] (hnu : 0 < nu)
    (omega omega' : ShellSeq d) (L : ℕ) (F : Vec d) (z : TriadicCube d) {M : ℝ}
    (hM : ∀ x ∈ openCubeSet z, Book.Ch02.matrixOperatorNorm
      (streamCutoff omega L x - streamCutoff omega' L x) ≤ M) :
    nu ^ 2 * ‖cubeMaximizerGradientClass hnu omega L F z -
        cubeMaximizerGradientClass hnu omega' L F z‖ ≤
      3 * M * ‖toHilbertVectorL2OfVecField
        (memVectorL2_const (U := openCubeSet z) F)‖ := by
  refine norm_cubeMaximizerGradientClass_sub_le hnu omega omega' L F z ?_
  filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_openCubeSet z)]
    with x hx using hM x hx

end SampleStability

/-! ## The sample modulus of the cutoff coefficient

The sample carrier of one shell is the compact-open carrier
`Frozen/Assumptions/ShellField.lean`, so convergence of samples is uniform
convergence of the shells on compact sets, which is exactly the modulus the
stability estimate consumes. -/

section SampleModulus

/-- On a compact set, the compact-open topology of `C(ℝ^d, Mat d)` controls the
uniform distance: the uniform ball around a map is a neighbourhood. -/
theorem mem_nhds_forall_mem_dist_lt (g₀ : C(Vec d, Mat d)) {K : Set (Vec d)}
    (hK : IsCompact K) {delta : ℝ} (hdelta : 0 < delta) :
    {g : C(Vec d, Mat d) | ∀ x ∈ K, dist (g x) (g₀ x) < delta} ∈ nhds g₀ := by
  have hbasis := ContinuousMap.hasBasis_compactConvergenceUniformity (α := Vec d) (β := Mat d)
  rw [nhds_eq_comap_uniformity]
  refine Filter.mem_comap.2 ⟨_,
    hbasis.mem_of_mem (i := (K, {p : Mat d × Mat d | dist p.1 p.2 < delta}))
      ⟨hK, Metric.dist_mem_uniformity hdelta⟩, ?_⟩
  intro g hg x hx
  exact dist_comm (g₀ x) (g x) ▸ hg x hx

/-- **One shell is uniformly close on a compact set, near a sample.**  The
operator norm is continuous, so a uniform ball in the ambient matrix norm sits
inside a uniform operator-norm ball, and the compact-open carrier makes the
latter a neighbourhood of the shell. -/
theorem eventually_forall_mem_matrixOperatorNorm_shellField_sub_lt (j₀ : ShellField d)
    {K : Set (Vec d)} (hK : IsCompact K) {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ j in nhds j₀, ∀ x ∈ K, Book.Ch02.matrixOperatorNorm (j x - j₀ x) < eta := by
  obtain ⟨delta, hdelta, hball⟩ := Metric.isOpen_iff.1
    (isOpen_lt ShellField.continuous_matrixOperatorNorm continuous_const) 0
    (by simpa only [Set.mem_ofPred_eq, Book.Ch02.matrixOperatorNorm_zero] using heta)
  have hcont : Continuous fun j : ShellField d => (j.1.1 : C(Vec d, Mat d)) :=
    continuous_subtype_val.fst
  have hpre := hcont.continuousAt.preimage_mem_nhds
    (mem_nhds_forall_mem_dist_lt (j₀.1.1) hK hdelta)
  filter_upwards [hpre] with j hj x hx
  have hd : dist (j x) (j₀ x) < delta := hj x hx
  have hmem : j x - j₀ x ∈ Metric.ball (0 : Mat d) delta := by
    simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using hd
  exact hball hmem

/-- The infrared cutoff is the finite shell sum, evaluated. -/
theorem streamCutoff_apply_eq_sum (omega : ShellSeq d) (L : ℕ) (x : Vec d) :
    streamCutoff omega L x = ∑ n ∈ Finset.range (L + 1), omega n x := by
  simp [streamCutoff, RegCoeffField.finset_sum_apply, shellReg]

/-- **The cutoff coefficient is uniformly close on a compact set, near a
sample.**  `k_L` is the sum of the finitely many shells `0, …, L`, each of which
is a continuous coordinate of the sample, so the `L∞(K)` modulus that the
stability estimate consumes is arbitrarily small near any sample. -/
theorem eventually_forall_mem_matrixOperatorNorm_streamCutoff_sub_le
    (omega₀ : ShellSeq d) (L : ℕ) {K : Set (Vec d)} (hK : IsCompact K)
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ omega in nhds omega₀, ∀ x ∈ K,
      Book.Ch02.matrixOperatorNorm
        (streamCutoff omega L x - streamCutoff omega₀ L x) ≤ eta := by
  have heps : 0 < eta / ((L : ℝ) + 1) := by positivity
  have hshell : ∀ n ∈ Finset.range (L + 1), ∀ᶠ omega : ShellSeq d in nhds omega₀,
      ∀ x ∈ K, Book.Ch02.matrixOperatorNorm (omega n x - omega₀ n x) <
        eta / ((L : ℝ) + 1) := fun n _ =>
    (continuous_apply n).continuousAt.preimage_mem_nhds
      (eventually_forall_mem_matrixOperatorNorm_shellField_sub_lt (omega₀ n) hK heps)
  filter_upwards [(Filter.eventually_all_finset (Finset.range (L + 1))).2 hshell]
    with omega homega x hx
  have hsum : streamCutoff omega L x - streamCutoff omega₀ L x =
      ∑ n ∈ Finset.range (L + 1), (omega n x - omega₀ n x) := by
    rw [streamCutoff_apply_eq_sum, streamCutoff_apply_eq_sum, Finset.sum_sub_distrib]
  rw [hsum]
  calc Book.Ch02.matrixOperatorNorm
        (∑ n ∈ Finset.range (L + 1), (omega n x - omega₀ n x))
      ≤ ∑ n ∈ Finset.range (L + 1),
          Book.Ch02.matrixOperatorNorm (omega n x - omega₀ n x) := by
        simp only [Book.Ch02.matrixOperatorNorm, map_sum]
        exact norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.range (L + 1), eta / ((L : ℝ) + 1) :=
        Finset.sum_le_sum fun n hn => (homega n hn x hx).le
    _ = eta := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
        field_simp

end SampleModulus

/-! ## The cube maximizer gradient class is continuous in the sample -/

section SampleContinuity

variable {nu : ℝ}

/-- **The `L²(z)` class of `∇u_{k,z}` is a continuous function of the sample.**

The sample enters the cube problem only through `k_L`, the maximizer gradient
class is Lipschitz in `k_L` for the `L∞(z)` operator norm
(`norm_cubeMaximizerGradientClass_sub_le`), and the compact-open carrier of one
shell makes `k_L` uniformly small near any sample on the compact closure of the
cube (`eventually_forall_mem_matrixOperatorNorm_streamCutoff_sub_le`). -/
theorem continuous_cubeMaximizerGradientClass [NeZero d] (hnu : 0 < nu) (L : ℕ)
    (F : Vec d) (z : TriadicCube d) :
    Continuous fun omega : ShellSeq d => cubeMaximizerGradientClass hnu omega L F z := by
  have hK : IsCompact (closure (openCubeSet z)) :=
    (Book.Ch02.cubeDomain z).isDomain.isBoundedDomain.isBounded.isCompact_closure
  rw [continuous_iff_continuousAt]
  intro omega₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro eps heps
  have hc : (0 : ℝ) ≤ 3 * ‖toHilbertVectorL2OfVecField
      (memVectorL2_const (U := openCubeSet z) F)‖ := by positivity
  set c : ℝ := 3 * ‖toHilbertVectorL2OfVecField
    (memVectorL2_const (U := openCubeSet z) F)‖ with hcdef
  have heta : 0 < eps * nu ^ 2 / (c + 1) := by positivity
  filter_upwards [eventually_forall_mem_matrixOperatorNorm_streamCutoff_sub_le
    omega₀ L hK heta] with omega homega
  have hest := norm_cubeMaximizerGradientClass_sub_le_of_forall_mem hnu omega omega₀ L F z
    (fun x hx => homega x (subset_closure hx))
  have hkey : nu ^ 2 * ‖cubeMaximizerGradientClass hnu omega L F z -
      cubeMaximizerGradientClass hnu omega₀ L F z‖ ≤ (eps * nu ^ 2 / (c + 1)) * c := by
    refine le_trans hest (le_of_eq ?_)
    rw [hcdef]; ring
  have hlt : (eps * nu ^ 2 / (c + 1)) * c < eps * nu ^ 2 := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith only [hc])]
    have h1 : 0 < eps * nu ^ 2 := by positivity
    have h2 : c < c + 1 := by linarith only []
    exact mul_lt_mul_of_pos_left h2 h1
  have hnu2 : 0 < nu ^ 2 := by positivity
  rw [dist_eq_norm]
  exact lt_of_mul_lt_mul_left (by linarith only [lt_of_le_of_lt hkey hlt]) hnu2.le

/-- **The sample carrier is a Borel space for its product topology.**  One
shell is a subspace of a triple of compact-open carriers over a second-countable
locally compact base, hence second countable; the sample carrier is a countable
product of Borel spaces, so its product `σ`-algebra is the Borel `σ`-algebra of
its product topology. -/
theorem borelSpace_shellSeq : BorelSpace (ShellSeq d) := by
  have : SecondCountableTopology (Mat d) :=
    inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℝ))
  have : SecondCountableTopology (ShellAmbient d) := by
    have h1 : SecondCountableTopology (Vec d →L[ℝ] Mat d) := by
      have : ProperSpace (Vec d →L[ℝ] Mat d) := FiniteDimensional.proper_real _
      exact secondCountable_of_proper
    have h2 : SecondCountableTopology (Vec d →L[ℝ] Vec d →L[ℝ] Mat d) := by
      have : ProperSpace (Vec d →L[ℝ] Vec d →L[ℝ] Mat d) := FiniteDimensional.proper_real _
      exact secondCountable_of_proper
    unfold ShellAmbient
    infer_instance
  have : SecondCountableTopology (ShellField d) :=
    TopologicalSpace.secondCountableTopology_induced (ShellField d) (ShellAmbient d)
      fun j => j.1
  infer_instance

/-- **The `L²(z)` class of `∇u_{k,z}` is a measurable function of the sample.**
Continuity in the sample plus the Borel structure of the sample carrier.  This
is the per-sub-cube half of the `L²(cu_m)` class measurability of the glued
field of `GluedFieldL2Class.lean`. -/
theorem measurable_cubeMaximizerGradientClass [NeZero d] (hnu : 0 < nu) (L : ℕ)
    (F : Vec d) (z : TriadicCube d) :
    Measurable fun omega : ShellSeq d => cubeMaximizerGradientClass hnu omega L F z := by
  have := borelSpace_shellSeq (d := d)
  exact (continuous_cubeMaximizerGradientClass hnu L F z).measurable

end SampleContinuity

/-! ## Gluing the sub-cube classes

The glued field of `e.u.k.def` is the finite sum of the maximizer gradients
against the indicators of the half-open sub-cubes, so its `L²(cu_m)` class is
the sum of the zero-extensions of the sub-cube classes.  Zero-extension is an
isometry of class spaces, so the glued class is measurable in the sample. -/

section Gluing

/-- The half-open cube differs from the open cube by a null set. -/
theorem volume_cubeSet_sdiff_openCubeSet (Q : TriadicCube d) :
    MeasureTheory.volume (cubeSet Q \ openCubeSet Q) = 0 := by
  have h := volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q
  have hmeas : MeasurableSet (cubeSet Q \ openCubeSet Q) :=
    (measurableSet_cubeSet Q).diff (measurableSet_openCubeSet Q)
  have h1 := congrArg (fun mu : MeasureTheory.Measure (Vec d) =>
    mu (cubeSet Q \ openCubeSet Q)) h
  simp only [MeasureTheory.Measure.restrict_apply hmeas] at h1
  have h2 : (cubeSet Q \ openCubeSet Q) ∩ cubeSet Q = cubeSet Q \ openCubeSet Q := by
    ext x
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, hx.1⟩⟩
  have h3 : (cubeSet Q \ openCubeSet Q) ∩ openCubeSet Q = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨-, hno⟩, hyes⟩
    exact hno hyes
  rw [h2, h3] at h1
  simpa only [measure_empty] using h1

/-- On a sub-cube of the large cube, the restricted volume of the intersection
with the large open cube is the restricted volume of the open sub-cube. -/
theorem restrict_inter_cubeSet_eq {k m : ℕ} {z : TriadicCube d}
    (hz : z ∈ largeCubeSubcubes d k m) :
    MeasureTheory.volume.restrict
        (openCubeSet (originCube d (m : ℤ)) ∩ cubeSet z) =
      MeasureTheory.volume.restrict (openCubeSet z) := by
  have hsub : cubeSet z ⊆ cubeSet (originCube d (m : ℤ)) :=
    cubeSet_subset_of_mem_largeCubeSubcubes hz
  have hnull : MeasureTheory.volume
      (cubeSet z \ (openCubeSet (originCube d (m : ℤ)) ∩ cubeSet z)) = 0 := by
    refine MeasureTheory.measure_mono_null ?_
      (volume_cubeSet_sdiff_openCubeSet (originCube d (m : ℤ)))
    rintro x ⟨hxz, hxno⟩
    exact ⟨hsub hxz, fun hxopen => hxno ⟨hxopen, hxz⟩⟩
  have hae : ((openCubeSet (originCube d (m : ℤ)) ∩ cubeSet z : Set (Vec d)))
      =ᵐ[MeasureTheory.volume] (cubeSet z : Set (Vec d)) := by
    rw [MeasureTheory.ae_eq_set]
    refine ⟨?_, hnull⟩
    have hempty : (openCubeSet (originCube d (m : ℤ)) ∩ cubeSet z) \ cubeSet z = ∅ := by
      ext x
      simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false,
        not_and, not_not]
      exact fun hx => hx.2
    rw [hempty]
    simp
  rw [MeasureTheory.Measure.restrict_congr_set hae,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]

/-- The zero-extension of a square-integrable field on a sub-cube is square
integrable on any cube. -/
theorem memVectorL2_indicator_cubeSet {Q z : TriadicCube d} {g : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet z) g) :
    MemVectorL2 (openCubeSet Q) (Set.indicator (cubeSet z) g) := by
  refine MeasureTheory.MemLp.restrict _ ?_
  rw [memLp_indicator_iff_restrict (measurableSet_cubeSet z),
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet z]
  exact hg

/-- The zero-extension only depends on the `L²(z)` class of the field. -/
theorem toHilbertVectorL2OfVecField_indicator_congr {Q z : TriadicCube d}
    {g h : Vec d → Vec d} (hg : MemVectorL2 (openCubeSet z) g)
    (hh : MemVectorL2 (openCubeSet z) h)
    (hgh : g =ᵐ[volumeMeasureOn (openCubeSet z)] h) :
    toHilbertVectorL2OfVecField (memVectorL2_indicator_cubeSet (Q := Q) hg) =
      toHilbertVectorL2OfVecField (memVectorL2_indicator_cubeSet (Q := Q) hh) := by
  refine toHilbertVectorL2OfVecField_congr _ _ ?_
  have hnull1 : MeasureTheory.volume ({x | ¬ g x = h x} ∩ openCubeSet z) = 0 := by
    have hae : (MeasureTheory.volume.restrict (openCubeSet z)) {x | ¬ g x = h x} = 0 := by
      rw [← MeasureTheory.ae_iff]
      exact hgh
    rwa [MeasureTheory.Measure.restrict_apply' (measurableSet_openCubeSet z)] at hae
  refine Filter.EventuallyEq.filter_mono ?_
    (MeasureTheory.ae_mono MeasureTheory.Measure.restrict_le_self)
  rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null ?_
    (MeasureTheory.measure_union_null hnull1 (volume_cubeSet_sdiff_openCubeSet z))
  intro x hx
  by_cases hxz : x ∈ cubeSet z
  · by_cases hxo : x ∈ openCubeSet z
    · refine Or.inl ⟨fun hgh' => hx ?_, hxo⟩
      rw [Set.indicator_of_mem hxz, Set.indicator_of_mem hxz, hgh']
    · exact Or.inr ⟨hxz, hxo⟩
  · refine absurd ?_ hx
    rw [Set.indicator_of_notMem hxz, Set.indicator_of_notMem hxz]

/-- **Zero-extension of an `L²(z)` class to the large cube.** -/
def extendCubeClass (Q z : TriadicCube d) (f : HilbertVectorL2 (openCubeSet z)) :
    HilbertVectorL2 (openCubeSet Q) :=
  toHilbertVectorL2OfVecField
    (memVectorL2_indicator_cubeSet (Q := Q) (memVectorL2_hilbertClassField f))

/-- The zero-extension of the class of a field is the class of its
zero-extension. -/
theorem extendCubeClass_toHilbertVectorL2OfVecField {Q z : TriadicCube d}
    {g : Vec d → Vec d} (hg : MemVectorL2 (openCubeSet z) g) :
    extendCubeClass Q z (toHilbertVectorL2OfVecField hg) =
      toHilbertVectorL2OfVecField (memVectorL2_indicator_cubeSet (Q := Q) hg) :=
  toHilbertVectorL2OfVecField_indicator_congr
    (memVectorL2_hilbertClassField (toHilbertVectorL2OfVecField hg)) hg
    (hilbertClassField_toHilbertVectorL2OfVecField hg)

/-- **Zero-extension is an isometry of class spaces.**  The half-open sub-cube
carries the same restricted volume as the open sub-cube, and it meets the large
open cube up to a null set. -/
theorem norm_extendCubeClass_sub {k m : ℕ} {z : TriadicCube d}
    (hz : z ∈ largeCubeSubcubes d k m) (f f' : HilbertVectorL2 (openCubeSet z)) :
    ‖extendCubeClass (originCube d (m : ℤ)) z f -
        extendCubeClass (originCube d (m : ℤ)) z f'‖ = ‖f - f'‖ := by
  have hmg : MemVectorL2 (openCubeSet z) (hilbertClassField f) :=
    memVectorL2_hilbertClassField f
  have hmg' : MemVectorL2 (openCubeSet z) (hilbertClassField f') :=
    memVectorL2_hilbertClassField f'
  have hdiff : extendCubeClass (originCube d (m : ℤ)) z f -
      extendCubeClass (originCube d (m : ℤ)) z f' =
      toHilbertVectorL2OfVecField
        (memVectorL2_indicator_cubeSet (Q := originCube d (m : ℤ)) (hmg.sub hmg')) := by
    rw [extendCubeClass, extendCubeClass, ← toHilbertVectorL2OfVecField_sub]
    refine toHilbertVectorL2OfVecField_congr _ _ (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ cubeSet z
    · simp [Set.indicator_of_mem hx, Pi.sub_apply]
    · simp [Set.indicator_of_notMem hx]
  have hfdiff : f - f' = toHilbertVectorL2OfVecField (hmg.sub hmg') := by
    rw [toHilbertVectorL2OfVecField_sub hmg hmg',
      toHilbertVectorL2OfVecField_hilbertClassField,
      toHilbertVectorL2OfVecField_hilbertClassField]
  rw [hdiff, hfdiff, norm_toHilbertVectorL2OfVecField_eq_sqrt,
    norm_toHilbertVectorL2OfVecField_eq_sqrt]
  congr 1
  have hpoint : (fun x => vecDot (Set.indicator (cubeSet z)
        (hilbertClassField f - hilbertClassField f') x)
        (Set.indicator (cubeSet z) (hilbertClassField f - hilbertClassField f') x)) =
      Set.indicator (cubeSet z) (fun y => vecDot
        ((hilbertClassField f - hilbertClassField f') y)
        ((hilbertClassField f - hilbertClassField f') y)) := by
    funext x
    by_cases hx : x ∈ cubeSet z
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx, vecDot]
  rw [hpoint, MeasureTheory.setIntegral_indicator (measurableSet_cubeSet z),
    restrict_inter_cubeSet_eq hz]

/-- Zero-extension is continuous. -/
theorem continuous_extendCubeClass {k m : ℕ} {z : TriadicCube d}
    (hz : z ∈ largeCubeSubcubes d k m) :
    Continuous (extendCubeClass (originCube d (m : ℤ)) z) :=
  (Isometry.of_dist_eq fun f f' => by
    rw [dist_eq_norm, dist_eq_norm]
    exact norm_extendCubeClass_sub hz f f').continuous

/-- The class of the zero field is zero. -/
theorem toHilbertVectorL2OfVecField_zero {U : Set (Vec d)}
    (h : MemVectorL2 U (0 : Vec d → Vec d)) :
    toHilbertVectorL2OfVecField h = 0 := by
  refine MeasureTheory.Lp.ext ?_
  filter_upwards [coeFn_toHilbertVectorL2OfVecField h,
    MeasureTheory.Lp.coeFn_zero (HilbertVec d) 2 (volumeMeasureOn U)] with x hx hzero
  rw [hx, hzero]
  simp [hilbertifyVecField]

/-- The class of a finite sum of square-integrable fields is the sum of their
classes. -/
theorem toHilbertVectorL2OfVecField_finset_sum {U : Set (Vec d)} {iota : Type*}
    (s : Finset iota) {f : iota → Vec d → Vec d} (hf : ∀ i, MemVectorL2 U (f i))
    (hsum : MemVectorL2 U (∑ i ∈ s, f i)) :
    toHilbertVectorL2OfVecField hsum =
      ∑ i ∈ s, toHilbertVectorL2OfVecField (hf i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      exact (toHilbertVectorL2OfVecField_zero (U := U) hsum).trans (Finset.sum_empty).symm
  | insert a s ha ih =>
      have hrest : MemVectorL2 U (∑ i ∈ s, f i) := memLp_finsetSum' s fun i _ => hf i
      have h1 : toHilbertVectorL2OfVecField hsum =
          toHilbertVectorL2OfVecField ((hf a).add hrest) := by
        refine toHilbertVectorL2OfVecField_congr _ _ (Filter.Eventually.of_forall fun x => ?_)
        rw [Finset.sum_insert (f := f) ha]
      rw [h1, toHilbertVectorL2OfVecField_add (hf a) hrest, ih hrest,
        Finset.sum_insert ha]

/-- **The glued class is the sum of the zero-extended sub-cube classes.**  This
is `e.u.k.def` read on `L²(cu_m)` classes. -/
theorem gluedGradientClass_eq_sum {nu : ℝ} (hnu : 0 < nu) (L k m : ℕ) (F : Vec d)
    (omega : ShellSeq d) :
    toHilbertVectorL2OfVecField
        (memVectorL2_gluedGradientField hnu L k m F omega (originCube d (m : ℤ))) =
      ∑ z ∈ largeCubeSubcubes d k m,
        extendCubeClass (originCube d (m : ℤ)) z
          (cubeMaximizerGradientClass hnu omega L F z) := by
  have hmem : ∀ z : TriadicCube d, MemVectorL2 (openCubeSet (originCube d (m : ℤ)))
      (Set.indicator (cubeSet z) (cubeMaximizerGradient hnu omega L F z)) :=
    fun z => memVectorL2_indicator_cubeSet
      (memVectorL2_cubeMaximizerGradient hnu omega L F z)
  have hsum : MemVectorL2 (openCubeSet (originCube d (m : ℤ)))
      (∑ z ∈ largeCubeSubcubes d k m,
        Set.indicator (cubeSet z) (cubeMaximizerGradient hnu omega L F z)) :=
    memLp_finsetSum' _ fun z _ => hmem z
  have hclass : toHilbertVectorL2OfVecField
      (memVectorL2_gluedGradientField hnu L k m F omega (originCube d (m : ℤ))) =
      toHilbertVectorL2OfVecField hsum := by
    refine toHilbertVectorL2OfVecField_congr _ _ (Filter.Eventually.of_forall fun x => ?_)
    rw [gluedGradientField_apply, Finset.sum_apply]
  rw [hclass, toHilbertVectorL2OfVecField_finset_sum _ hmem hsum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [cubeMaximizerGradientClass, extendCubeClass_toHilbertVectorL2OfVecField]

/-- **The `L²(cu_m)` class of the glued field is measurable in the sample.**
The glued class is the finite sum of the zero-extensions of the sub-cube
classes, each of which is a continuous image of a measurable sub-cube class.
This is the fact left open by `GluedFieldL2Class.lean`. -/
theorem measurable_gluedGradientClass [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L k m : ℕ)
    (F : Vec d) :
    Measurable fun omega : ShellSeq d => toHilbertVectorL2OfVecField
      (memVectorL2_gluedGradientField hnu L k m F omega (originCube d (m : ℤ))) := by
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  have hrw : (fun omega : ShellSeq d => toHilbertVectorL2OfVecField
      (memVectorL2_gluedGradientField hnu L k m F omega (originCube d (m : ℤ)))) =
      fun omega : ShellSeq d => ∑ z ∈ largeCubeSubcubes d k m,
        extendCubeClass (originCube d (m : ℤ)) z
          (cubeMaximizerGradientClass hnu omega L F z) := by
    funext omega
    exact gluedGradientClass_eq_sum hnu L k m F omega
  rw [hrw]
  refine Finset.measurable_sum _ fun z hz => ?_
  exact (continuous_extendCubeClass hz).measurable.comp
    (measurable_cubeMaximizerGradientClass hnu L F z)

/-- **The measurability obligation of `l.RHS.term1`.**  The obligation is
proved outright: `GluedFieldL2Class.lean` reduced it to the `L²(cu_m)` class
measurability of the glued field, and that is
`measurable_gluedGradientClass`. -/
theorem aemeasurable_ofReal_abs_volumeAverage_vecDot_grad_gluedField
    [NeZero d] {LPrime ellPrime k m : ℕ} {nu : ℝ} (hnu : 0 < nu) (L : ℕ)
    {F qTilde p : Vec d} {mu : MeasureTheory.Measure (ShellSeq d)}
    {w : ShellSeq d → H10Function (openCubeSet (originCube d (m : ℤ)))}
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega LPrime ellPrime m p (w omega)) :
    AEMeasurable (fun omega : ShellSeq d =>
      ENNReal.ofReal |volumeAverage (openCubeSet (originCube d (m : ℤ)))
        (fun x => vecDot ((w omega).toH1Function.grad x)
          (pairingField hnu L k m F qTilde omega x))|) mu :=
  aemeasurable_ofReal_abs_volumeAverage_vecDot_grad_of_pairingField hnu L hw
    (measurable_gluedGradientClass hnu L k m F).aemeasurable

end Gluing

end

end SuperdiffusionCLT.Section3.Terms
