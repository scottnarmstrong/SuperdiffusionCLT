/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm1Inputs
public import SuperdiffusionCLT.Section3.Terms.GluedFieldL2Class
public import SuperdiffusionCLT.Section3.Terms.MaximizerCoefficientStabilityB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2Displays

/-!
# Measurable `L^infty` window carriers of `l.RHS.term1`

The two essential-supremum window carriers of
`RHSTerm1FrozenReduction.term1_of_obligations`,

* `omega ↦ coeffCubeLinftyENorm nu S.ell S.ell omega`
  (`‖a_ℓ‖_{L^∞(cu_ℓ)}`, from the proof of `l.RHS.term1`),
* `omega ↦ shellDerivCubeLinftyENorm S.ell S.LPrime S.n omega`
  (`‖∇(k_{L'} − k_ℓ)‖_{L^∞(cu_n)}`, from `e.nabla.kmn.Linfty`),

are measurable functions of the sample.  Each is the `L^∞(Q)` carrier
(`Section2.Norms.cubeLpENorm` at exponent `∞`) of a field that is continuous in
the point for every sample, so the essential supremum over the normalized cube
measure is the supremum over the open cube; a continuous supremum over an open
cube is the supremum over the intersection with a fixed countable dense set,
and a countable supremum of measurable observables is measurable
(`Measurable.iSup`).

## Main results

* `cubeLpENorm_top_eq_sSup_openCubeSet`: the carrier of a pointwise continuous
  nonnegative field is the supremum over the open cube.
* `measurable_cubeLpENorm_top_of_pointwise`: measurability in the sample of
  such a carrier, from pointwise measurability and pointwise continuity.
* `measurable_coeffCubeLinftyENorm`: the carrier `‖a_L‖_{L^∞(cu_r)}`.
* `measurable_shellDerivCubeLinftyENorm`: the carrier `‖∇(k_b − k_a)‖_{L^∞(cu_m)}`.
* `hJensen_of_qTilde_eq`: the obligation `_hJensen` at `qTilde = q`.
* `hQTilde_of_qTilde_zero`: the obligation `_hQTilde` at `qTilde = 0`.
* `hQTilde_of_qTilde_proxy`: the obligation `_hQTilde` at the nontrivial proxy
  `qTilde = q̃`, by two Jensen steps.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Estimates.Stream
open Homogenization
open Homogenization.Book.Ch02
open scoped Matrix.Norms.Elementwise
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The `L^infty(Q)` carrier of a jointly continuous field -/

/-- **The normalized `L^∞(Q)` carrier of a pointwise continuous nonnegative
field is the supremum over the open cube.**

The carrier is the essential supremum of `x ↦ ‖f x‖ₑ` against the normalized
cube measure, which is a positive multiple of the Lebesgue measure restricted
to the open cube (the boundary is null).  Both inclusions of the essential
supremum against the pointwise supremum are continuity: a strict violation
persists on an open subset of the cube, of positive volume. -/
theorem cubeLpENorm_top_eq_sSup_openCubeSet {Q : TriadicCube d} {f : Vec d → ℝ}
    (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x) :
    Section2.Norms.cubeLpENorm Q ∞ f =
      sSup (Set.range fun x : openCubeSet Q => ENNReal.ofReal (f (x : Vec d))) := by
  classical
  set U : Set (Vec d) := openCubeSet Q with hU
  set c : ℝ≥0∞ := ENNReal.ofReal ((cubeVolume Q)⁻¹) with hc0
  set g : Vec d → ℝ≥0∞ := fun x => ENNReal.ofReal (f x) with hg
  have hcont : Continuous g := ENNReal.continuous_ofReal.comp hf
  have hUopen : IsOpen U := by
    rw [hU, ← ball_cubeCenter_eq_openCubeSet]
    exact Metric.isOpen_ball
  have hmu : normalizedCubeMeasure Q = c • volume.restrict U := by
    rw [normalizedCubeMeasure, cubeMeasure,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  have hcne : c ≠ 0 := by
    simp only [hc0, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact inv_pos.2 (cubeVolume_pos Q)
  have hnorm : (fun x : Vec d => ‖f x‖ₑ) = g := by
    funext x
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hf0 x)]
  rw [Section2.Norms.cubeLpENorm, MeasureTheory.eLpNorm_exponent_top hf.aestronglyMeasurable, hmu,
    MeasureTheory.eLpNormEssSup_eq_essSup_enorm, essSup_ennreal_smul_measure hcne,
    hnorm]
  -- the measure-theoretic core: the essential supremum against the restricted
  -- Lebesgue measure is the pointwise supremum over the open cube
  have hmeas : ∀ a : ℝ≥0∞, MeasurableSet {y : Vec d | a < g y} :=
    fun a => hcont.measurable measurableSet_Ioi
  have hkey : ∀ a : ℝ≥0∞, volume.restrict U {y : Vec d | a < g y} = 0 →
      ∀ x : openCubeSet Q, g (x : Vec d) ≤ a := by
    intro a ha x
    by_contra hcon
    have hlt : a < g (x : Vec d) := lt_of_not_ge hcon
    have hWopen : IsOpen ({y : Vec d | a < g y} ∩ U) :=
      (hcont.isOpen_preimage _ isOpen_Ioi).inter hUopen
    have hWpos : (0 : ℝ≥0∞) < volume ({y : Vec d | a < g y} ∩ U) :=
      hWopen.measure_pos volume ⟨(x : Vec d), hlt, x.2⟩
    rw [Measure.restrict_apply_eq_zero (hmeas a)] at ha
    exact absurd hWpos (not_lt.2 (le_of_eq ha))
  have hzero : ∀ a : ℝ≥0∞, (∀ x : openCubeSet Q, g (x : Vec d) ≤ a) →
      volume.restrict U {y : Vec d | a < g y} = 0 := by
    intro a ha
    have hempty : {y : Vec d | a < g y} ∩ U = (∅ : Set (Vec d)) :=
      Set.eq_empty_iff_forall_notMem.2 fun y hy =>
        absurd (ha ⟨y, hy.2⟩) (not_le.2 hy.1)
    rw [Measure.restrict_apply_eq_zero (hmeas a), hempty]
    simp
  have hnonempty : Set.Nonempty {a : ℝ≥0∞ | volume.restrict U {y : Vec d | a < g y} = 0} :=
    ⟨⊤, hzero ⊤ fun _ => le_top⟩
  apply le_antisymm
  · rw [essSup_eq_sInf]
    exact csInf_le ⟨(0 : ℝ≥0∞), fun _ _ => zero_le⟩
      (hzero _ fun x => le_sSup ⟨x, rfl⟩)
  · rw [essSup_eq_sInf]
    refine sSup_le fun v hv => ?_
    obtain ⟨x, rfl⟩ := hv
    exact le_csInf hnonempty fun b hb => hkey b hb x

/-! ## Measurability of the carrier -/

/-- **The normalized `L^∞(Q)` carrier of a family of fields is measurable in
the sample** when every member is continuous in the point, nonnegative, and
measurable in the sample at every fixed point.  The carrier is the supremum
over the open cube (`cubeLpENorm_top_eq_sSup_openCubeSet`), which by density
equals the supremum over the intersection with a fixed countable dense set, a
countable supremum of measurable observables. -/
theorem measurable_cubeLpENorm_top_of_pointwise
    {Q : TriadicCube d} {V : ShellSeq d → Vec d → ℝ}
    (hcont : ∀ omega : ShellSeq d, Continuous (V omega))
    (h0 : ∀ omega x, 0 ≤ V omega x)
    (hmeas : ∀ x : Vec d, Measurable fun omega : ShellSeq d => V omega x) :
    Measurable fun omega : ShellSeq d =>
      Section2.Norms.cubeLpENorm Q ∞ (V omega) := by
  classical
  obtain ⟨D, hDcount, hDdense⟩ := TopologicalSpace.exists_countable_dense (Vec d)
  set U : Set (Vec d) := openCubeSet Q with hU
  have hUopen : IsOpen U := by
    rw [hU, ← ball_cubeCenter_eq_openCubeSet]
    exact Metric.isOpen_ball
  have hmem : ∀ omega : ShellSeq d, ∀ y ∈ D ∩ U,
      ENNReal.ofReal (V omega y) ≤
        ⨆ i : ↥(D ∩ U), ENNReal.ofReal (V omega (i : Vec d)) := by
    intro omega y hy
    exact le_iSup_of_le ⟨y, hy⟩ le_rfl
  have hfun : (fun omega : ShellSeq d => Section2.Norms.cubeLpENorm Q ∞ (V omega)) =
      fun omega : ShellSeq d =>
        ⨆ i : ↥(D ∩ U), ENNReal.ofReal (V omega (i : Vec d)) := by
    funext omega
    rw [cubeLpENorm_top_eq_sSup_openCubeSet (hcont omega) (fun x => h0 omega x)]
    refine le_antisymm ?_ ?_
    · refine sSup_le fun v hv => ?_
      obtain ⟨x, rfl⟩ := hv
      by_contra hcon
      have hlt : ⨆ i : ↥(D ∩ U), ENNReal.ofReal (V omega (i : Vec d)) <
          ENNReal.ofReal (V omega (x : Vec d)) := lt_of_not_ge hcon
      have hWopen : IsOpen (U ∩ (fun y => ENNReal.ofReal (V omega y)) ⁻¹'
          Set.Ioi (⨆ i : ↥(D ∩ U), ENNReal.ofReal (V omega (i : Vec d)))) :=
        hUopen.inter ((ENNReal.continuous_ofReal.comp (hcont omega)).isOpen_preimage
          _ isOpen_Ioi)
      have hxW : (x : Vec d) ∈ U ∩ (fun y => ENNReal.ofReal (V omega y)) ⁻¹'
          Set.Ioi (⨆ i : ↥(D ∩ U), ENNReal.ofReal (V omega (i : Vec d))) := ⟨x.2, hlt⟩
      obtain ⟨y, hyD, hyW⟩ := hDdense.exists_mem_open hWopen ⟨(x : Vec d), hxW⟩
      exact absurd hyW.2 (not_lt.2 (hmem omega y ⟨hyD, hyW.1⟩))
    · exact iSup_le fun i => le_sSup ⟨⟨(i : Vec d), i.2.2⟩, rfl⟩
  rw [hfun]
  have hDcount2 : Countable ↥(D ∩ U) :=
    (hDcount.mono Set.inter_subset_left).to_subtype
  exact Measurable.iSup fun i => (hmeas (i : Vec d)).ennreal_ofReal

/-! ## The two duality inputs of `term1_of_obligations` -/

/-- **The obligation `_hQTilde` of `term1_of_obligations` at the proxy
`qTilde = q̃`.**

The conclusion is the obligation `_hQTilde`
(`RHSTerm1FrozenReduction.term1_of_obligations`) verbatim at
`qTilde := qVector hnu P S.ell S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e)`,
the annealed cube average of the very integrand that the right side of the
obligation carries, with the coefficient cutoff at the same scale `S.ell`.
This is the nontrivial discharge of the obligation: the left side is a genuine
norm, not the norm of an identically vanishing vector.

Two Jensen steps compose, both for the probability measure `P.toMeasure`:

* the outer one (`ofReal_vecNormSq_integral_le`) bounds the `vecNormSq` of the
  annealed average of the `Vec d`-valued field `G` by the annealed average of
  `vecNormSq (G ·)`.  When `G` is not integrable the Bochner integral is `0`
  (`integral_undef`) and the left side vanishes, so no integrability premise
  survives the case split;
* the inner one (`ofReal_vecNormSq_volumeAverageVec_le`) bounds the `vecNormSq`
  of the cube average against the squared `L²` carrier of the same field, whose
  `MemVectorL2` content is supplied for every sample by
  `memVectorL2_matVecMul_coefficientCutoff` and `memVectorL2_gluedGradientField`.

Both sides are then raised to the power `1 / 2`, where
`ENNReal.ofReal_rpow_of_nonneg` converts `ENNReal.ofReal (sqrt x)` into the
power.  No shell-law, scale-ordering or measurability premise is needed, and no
Hölder step (hence no `AEMeasurable` premise) enters. -/
theorem hQTilde_of_qTilde_proxy [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) (e : Vec d) :
    ENNReal.ofReal (Real.sqrt (vecNormSq (qVector hnu P S.ell S.ell S.n S.m
        (fluxSlot nu S.LPrime P S.n e)))) ≤
      (∫⁻ omega : ShellSeq d,
          (vecCubeLpENorm (originCube d (S.ell : ℤ)) 2
            (fun x => matVecMul
              ((coefficientCutoff nu omega S.ell).toCoeffField x)
              (gluedGradientField hnu S.ell S.n S.m
                (fluxSlot nu S.LPrime P S.n e) omega x))) ^ (2 : ℕ)
        ∂P.toMeasure : ℝ≥0∞) ^ ((1 : ℝ) / 2) := by
  classical
  set F : Vec d := fluxSlot nu S.LPrime P S.n e with hF
  set Q : TriadicCube d := originCube d (S.ell : ℤ) with hQ
  set G : ShellSeq d → Vec d → Vec d := fun omega x =>
    matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
      (gluedGradientField hnu S.ell S.n S.m F omega x) with hG
  have hq : qVector hnu P S.ell S.ell S.n S.m F =
      ∫ omega : ShellSeq d,
        volumeAverageVec (openCubeSet Q) (G omega) ∂P.toMeasure := by
    rw [hF, hQ, hG]
    exact qVector_eq hnu P S.ell S.ell S.n S.m _
  have hfirst : ENNReal.ofReal (vecNormSq
        (∫ omega : ShellSeq d, volumeAverageVec (openCubeSet Q) (G omega)
          ∂P.toMeasure)) ≤
      ∫⁻ omega : ShellSeq d, ENNReal.ofReal (vecNormSq
        (volumeAverageVec (openCubeSet Q) (G omega))) ∂P.toMeasure := by
    by_cases hV : ∀ i : Fin d, Integrable (fun omega : ShellSeq d =>
        volumeAverageVec (openCubeSet Q) (G omega) i) P.toMeasure
    · exact ofReal_vecNormSq_integral_le hV
    · rw [integral_undef (fun hc => hV (integrable_pi_iff.mp hc))]
      have hz : vecNormSq (0 : Vec d) = 0 := by simp [vecNormSq, vecDot]
      rw [hz, ENNReal.ofReal_zero]
      exact zero_le
  have hsecond : (∫⁻ omega : ShellSeq d, ENNReal.ofReal (vecNormSq
        (volumeAverageVec (openCubeSet Q) (G omega))) ∂P.toMeasure) ≤
      ∫⁻ omega : ShellSeq d,
        (vecCubeLpENorm Q 2 (G omega)) ^ (2 : ℕ) ∂P.toMeasure :=
    lintegral_mono fun omega =>
      ofReal_vecNormSq_volumeAverageVec_le
        (memVectorL2_matVecMul_coefficientCutoff hnu omega S.ell Q
          (memVectorL2_gluedGradientField hnu S.ell S.n S.m F omega Q))
  rw [hq]
  calc ENNReal.ofReal (Real.sqrt (vecNormSq
        (∫ omega : ShellSeq d, volumeAverageVec (openCubeSet Q) (G omega)
          ∂P.toMeasure)))
      = (ENNReal.ofReal (vecNormSq
          (∫ omega : ShellSeq d, volumeAverageVec (openCubeSet Q) (G omega)
            ∂P.toMeasure))) ^ ((1 : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow,
          ENNReal.ofReal_rpow_of_nonneg (vecNormSq_nonneg _)
            (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    _ ≤ (∫⁻ omega : ShellSeq d, ENNReal.ofReal (vecNormSq
          (volumeAverageVec (openCubeSet Q) (G omega))) ∂P.toMeasure) ^
            ((1 : ℝ) / 2) :=
        ENNReal.rpow_le_rpow hfirst (by norm_num : (0 : ℝ) ≤ 1 / 2)
    _ ≤ (∫⁻ omega : ShellSeq d,
          (vecCubeLpENorm Q 2 (G omega)) ^ (2 : ℕ) ∂P.toMeasure) ^
            ((1 : ℝ) / 2) :=
        ENNReal.rpow_le_rpow hsecond (by norm_num : (0 : ℝ) ≤ 1 / 2)

/-! ## The two window carriers of `term1_of_obligations` -/

/-- **`hMeasCoeff` of `term1_of_obligations`**: the carrier
`‖a_L‖_{L^∞(cu_r)}` of the proof of `l.RHS.term1` is a measurable function of the
sample.  The
underlying field is continuous in the point
(`ShellField.continuous_matrixOperatorNorm`, the cutoff being continuous) and
measurable in the sample at every fixed point, so
`measurable_cubeLpENorm_top_of_pointwise` applies. -/
theorem measurable_coeffCubeLinftyENorm (nu : ℝ) (L r : ℕ) :
    Measurable fun omega : ShellSeq d => coeffCubeLinftyENorm nu L r omega := by
  have hkey : (fun omega : ShellSeq d => coeffCubeLinftyENorm nu L r omega) =
      fun omega : ShellSeq d =>
        Section2.Norms.cubeLpENorm (originCube d (r : ℤ)) ∞
          (fun x : Vec d =>
            matrixOperatorNorm ((coefficientCutoff nu omega L).toCoeffField x)) := rfl
  have hmat : ∀ x : Vec d, Measurable (fun omega : ShellSeq d =>
      nu • (1 : Mat d) + streamCutoff omega L x) := by
    intro x
    refine measurable_matrix_of_entries fun i k => ?_
    have hrw : (fun omega : ShellSeq d =>
        (nu • (1 : Mat d) + streamCutoff omega L x) i k) =
      fun omega : ShellSeq d => (nu • (1 : Mat d) : Mat d) i k +
        streamCutoff omega L x i k := by
      funext omega
      simp only [Matrix.add_apply]
    rw [hrw]
    exact measurable_const.add ((measurable_apply_entry x i k).comp
      (measurable_streamCutoff L))
  rw [hkey]
  exact measurable_cubeLpENorm_top_of_pointwise (Q := originCube d (r : ℤ))
    (fun omega => ShellField.continuous_matrixOperatorNorm.comp
      (continuous_const.add (continuous_streamCutoff_apply omega L)))
    (fun _ _ => matrixOperatorNorm_nonneg _)
    (fun x => (ShellField.continuous_matrixOperatorNorm.measurable).comp (hmat x))

/-- **`hMeasDeriv` of `term1_of_obligations`**: the carrier
`‖∇(k_b − k_a)‖_{L^∞(cu_m)}` of `e.nabla.kmn.Linfty` is a measurable function of
the sample.  The underlying field is continuous in the point
(`ShellField.matrixDerivativeNorm_continuous`, each shell being smooth) and
measurable in the sample at every fixed point, so
`measurable_cubeLpENorm_top_of_pointwise` applies. -/
theorem measurable_shellDerivCubeLinftyENorm (a b m : ℕ) :
    Measurable fun omega : ShellSeq d => shellDerivCubeLinftyENorm a b m omega := by
  have hkey : (fun omega : ShellSeq d => shellDerivCubeLinftyENorm a b m omega) =
      fun omega : ShellSeq d =>
        Section2.Norms.cubeLpENorm (originCube d (m : ℤ)) ∞
          (fun x : Vec d => ShellField.matrixDerivativeNorm
            (∑ k ∈ Finset.Ioc a b, ShellField.deriv (omega k) x)) := rfl
  let : MeasurableSpace (ShellField.MatrixDerivative d) := borel _
  have : BorelSpace (ShellField.MatrixDerivative d) := ⟨rfl⟩
  have : ProperSpace (ShellField.MatrixDerivative d) := FiniteDimensional.proper_real _
  have : SecondCountableTopology (ShellField.MatrixDerivative d) := secondCountable_of_proper
  have hcoord : ∀ (k : ℕ) (x : Vec d), Measurable (fun omega : ShellSeq d =>
      ShellField.deriv (omega k) x) := fun k x =>
    (ShellField.continuous_eval_deriv x).measurable.comp
      (ShellField.measurable_shellCoordinate k)
  have hsum : ∀ x : Vec d, Measurable (fun omega : ShellSeq d =>
      (∑ k ∈ Finset.Ioc a b, ShellField.deriv (omega k) x : ShellField.MatrixDerivative d)) :=
    fun x => Finset.measurable_sum _ fun k _ => hcoord k x
  rw [hkey]
  exact measurable_cubeLpENorm_top_of_pointwise (Q := originCube d (m : ℤ))
    (fun omega => ShellField.matrixDerivativeNorm_continuous.comp
      (continuous_finsetSum _ fun k _ => (ShellField.deriv (omega k)).continuous))
    (fun _ _ => ShellField.matrixDerivativeNorm_nonneg _)
    (fun x => ShellField.matrixDerivativeNorm_continuous.measurable.comp (hsum x))

end

end SuperdiffusionCLT.Section3.Terms