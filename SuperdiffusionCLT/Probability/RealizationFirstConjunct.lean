/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Probability.HonestSliceAssembly
public import SuperdiffusionCLT.Probability.StationaryRealizationPoincare

/-!
# The first conjunct of the stationary potential realization at `ShellSeq d`

The statement `SuperdiffusionCLT.Frozen.Section3.stationaryPotentialRealization`
asks, among other things, that for a.e. sample `ω` the realized stationary potential field
`x ↦ gradHatW (x +ᵥ ω)` be the weak gradient of an honest `H¹` function on the cube.  This
module proves exactly that first conjunct at the concrete carrier `Ω := ShellSeq d`, `μ := P.toMeasure`,
for every field whose `L²(Ω)` class lies in the closed stationary potential subspace
`stationaryPotentialSubspace` — the closure of the range of strong horizontal gradients.  That membership
is the *whole* hypothesis class (a genuine hypothesis carried below, `hmem` or `hproj`), not all of `L²(Ω)`: **not** an arbitrary `L²(Ω)` field.

The proof is the four-step route:

1. pick a sequence `G n` of honest strong horizontal gradients converging to the class of
   the field in `L²(Ω)`, together with potentials `φ n`;
2. measure-theoretically replace each `G n` and each `φ n` by an honest *measurable*
   representative (an `Lp` class is only a.e. strongly measurable);
3. `honestSlice` realizes each `G n` on the cube for a.e. `ω`, and
   `exists_strictMono_ae_tendsto_slice_lintegral_volumeOn` extracts a single subsequence —
   chosen once, not per `ω` — along which the spatial slices converge in `L²` on the cube
   for a.e. `ω`;
4. Poincaré–Wirtinger on the convex cube makes the mean-zero primitives Cauchy in `H¹`, so
   `exists_h1MeanZeroFunction_of_tendsto_gradToHilbertVectorL2` produces the limit, whose
   weak gradient is the realized limit field.

Nothing here needs measurability in `ω` of the chosen realization: the realization is
selected at each `ω` of a full-measure set by `Classical.choose`, out of a pointwise `∃`.

## Scope

The first conjunct is proved at the hypothesis set that the main statement actually supplies
(see `lhs_term1_of_stationaryAnchor`): the finite second moment `hGmemLp` of the field and,
through `exists_h1_realization_of_eq_neg_stationaryPotentialProjection`, the projection
identity, equivalently membership of the field's `L²(Ω)` class in `stationaryPotentialSubspace`.
That membership is a genuine hypothesis of the theorems below, not a claim about an arbitrary
`L²(Ω)` field, since the class it defines is smaller than `L²(Ω)`.  What is discharged is
measurability of `gradHatW`, removed by
`exists_h1_realization_of_mem_stationaryPotentialSubspace`.

The *second* conjunct of that same binder, the per-sample weak equation
`∫ x in U, vecDot (∇(uReal ω) x) (φ.grad x) = -∫ x in U, vecDot (F ω x) (φ.grad x)` for every
`φ : H10Function U`, is not a consequence of the first one: the pairing identities of this part
are the `Ω`-averaged ones, while the binder needs the identity at almost every *single* sample.
It is proved in `RealizationSecondConjunct`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Homogenization
open SuperdiffusionCLT.Section2.Cutoff
open scoped ENNReal Topology

noncomputable section

namespace SuperdiffusionCLT.Probability.Stationary

variable {d : ℕ}

/-! ## Measurability of the Euclidean carrier identifications -/

/-- The Hilbert carrier of a vector is a measurable function of the vector. -/
theorem measurable_ofVec_hilbert : Measurable (HilbertVec.ofVec (d := d)) := by
  have h : Measurable (fun x : Vec d => (HilbertVec.continuousLinearEquivVec d).symm x) :=
    (HilbertVec.continuousLinearEquivVec d).symm.continuous.measurable
  simpa only [HilbertVec.continuousLinearEquivVec_symm_apply] using h

/-- The vector of a Hilbert vector is a measurable function of the Hilbert vector. -/
theorem measurable_toVec_hilbert : Measurable (HilbertVec.toVec (d := d)) := by
  have h : Measurable (fun x : HilbertVec d => (HilbertVec.continuousLinearEquivVec d) x) :=
    (HilbertVec.continuousLinearEquivVec d).continuous.measurable
  simpa only [HilbertVec.continuousLinearEquivVec_apply] using h

/-! ## Honest measurable representatives of `L²` classes

An `Lp` element carries only a.e. strong measurability, while `honestSlice` consumes an
honest `Measurable` representative.  At the concrete carrier the replacement is free: the
canonical a.e.-strongly-measurable representative is replaced by a measurable one, and both
carry the same `L²` class. -/

/-- Every scalar `L²(Ω)` class has a measurable representative with the same class. -/
theorem exists_measurable_representative_of_scalarL2 {P : ProbabilityMeasure (ShellSeq d)}
    (φ : Lp ℝ 2 P.toMeasure) :
    ∃ f : ShellSeq d → ℝ, Measurable f ∧
      ∃ hf : MemLp f 2 P.toMeasure, hf.toLp f = φ := by
  let f : ShellSeq d → ℝ := (Lp.aestronglyMeasurable φ).mk φ
  have hfm : Measurable f := (Lp.aestronglyMeasurable φ).measurable_mk
  have hae : (φ : ShellSeq d → ℝ) =ᵐ[P.toMeasure] f := (Lp.aestronglyMeasurable φ).ae_eq_mk
  have hmem : MemLp f 2 P.toMeasure := (Lp.memLp φ).ae_eq hae
  refine ⟨f, hfm, hmem, ?_⟩
  rw [MemLp.toLp_congr hmem (Lp.memLp φ) hae.symm]
  exact Lp.toLp_coeFn φ (Lp.memLp φ)

/-- Every Hilbert-vector `L²(Ω)` class has a measurable `Vec d`-valued representative with
the same class. -/
theorem exists_measurable_representative_of_vectorL2 {P : ProbabilityMeasure (ShellSeq d)}
    (G : Lp (HilbertVec d) 2 P.toMeasure) :
    ∃ F : ShellSeq d → Vec d, Measurable F ∧
      ∃ hF : MemLp (fun ω => HilbertVec.ofVec (F ω)) 2 P.toMeasure,
        hF.toLp (fun ω => HilbertVec.ofVec (F ω)) = G := by
  let G' : ShellSeq d → HilbertVec d := (Lp.aestronglyMeasurable G).mk G
  have hG'm : Measurable G' := (Lp.aestronglyMeasurable G).measurable_mk
  have hG'ae : (G : ShellSeq d → HilbertVec d) =ᵐ[P.toMeasure] G' :=
    (Lp.aestronglyMeasurable G).ae_eq_mk
  let F : ShellSeq d → Vec d := fun ω => HilbertVec.toVec (G' ω)
  have hFm : Measurable F := measurable_toVec_hilbert.comp hG'm
  have hG'mem : MemLp G' 2 P.toMeasure := (Lp.memLp G).ae_eq hG'ae
  have haeF : (fun ω => HilbertVec.ofVec (F ω)) =ᵐ[P.toMeasure] G' := by
    filter_upwards with ω
    exact HilbertVec.ofVec_toVec (G' ω)
  have hFmem : MemLp (fun ω => HilbertVec.ofVec (F ω)) 2 P.toMeasure :=
    MemLp.ae_eq haeF hG'mem
  refine ⟨F, hFm, hFmem, ?_⟩
  rw [MemLp.toLp_congr hFmem (Lp.memLp G) (haeF.trans hG'ae.symm)]
  exact Lp.toLp_coeFn G (Lp.memLp G)

/-- **The slices of a Hilbert-vector-valued field are `L²` on the open cube.**  This is
`ae_memLp_slice` at the normalised cube measure, converted to the unnormalised volume on
the cube by the constant `cubeVolume Q`. -/
theorem ae_memLp_slice_openCube_vec {P : ProbabilityMeasure (ShellSeq d)}
    [VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure]
    (Q : TriadicCube d) {g : ShellSeq d → Vec d}
    (hgm : Measurable g) (hg : MemLp (fun ω => HilbertVec.ofVec (g ω)) 2 P.toMeasure) :
    ∀ᵐ ω ∂P.toMeasure, MemLp (fun x => HilbertVec.ofVec (g (x +ᵥ ω))) 2
      (MeasureTheory.volume.restrict (openCubeSet Q)) := by
  have : IsProbabilityMeasure (normalizedCubeMeasure Q) :=
    ⟨normalizedCubeMeasure_apply_univ Q⟩
  filter_upwards [ae_memLp_slice (μ := P.toMeasure) (ν := normalizedCubeMeasure Q)
    (measurable_ofVec_hilbert.comp hgm) hg] with ω hω
  rw [volumeMeasureOn_openCubeSet_eq_smul_normalizedCubeMeasure Q]
  exact hω.smul_measure ENNReal.ofReal_ne_top

/-- **A.e. equality of two fields transfers to a.e. equality of their slices.**  If two
fields agree `P.toMeasure`-almost everywhere, then at almost every sample their spatial
realizations agree on the cube.  No measurability of either field is needed: the agreement
set contains a measurable set of full measure, whose translate-preimage carries full product
measure, and Fubini reads the slice statement off that set. -/
theorem ae_slice_eq_of_ae_eq {P : ProbabilityMeasure (ShellSeq d)}
    [VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure]
    {W G : ShellSeq d → Vec d} (h : W =ᵐ[P.toMeasure] G) (Q : TriadicCube d) :
    ∀ᵐ ω ∂P.toMeasure, (fun x => W (x +ᵥ ω)) =ᵐ[volumeMeasureOn (openCubeSet Q)]
      (fun x => G (x +ᵥ ω)) := by
  classical
  have : IsProbabilityMeasure (normalizedCubeMeasure Q) :=
    ⟨normalizedCubeMeasure_apply_univ Q⟩
  obtain ⟨t, ht_mem, ht_meas, ht_sub⟩ :=
    Filter.IsMeasurablyGenerated.exists_measurable_subset (f := ae P.toMeasure)
      (s := {ω : ShellSeq d | W ω = G ω}) h
  have ht_null : P.toMeasure tᶜ = 0 := MeasureTheory.mem_ae_iff.mp ht_mem
  have hzero : (P.toMeasure.prod (normalizedCubeMeasure Q))
      (((fun p : ShellSeq d × Vec d => p.2 +ᵥ p.1) ⁻¹' t)ᶜ) = 0 := by
    rw [← Set.preimage_compl,
      ← MeasureTheory.Measure.map_apply
        (SuperdiffusionCLT.Section3.Terms.measurable_vadd_shellSeq (d := d)) ht_meas.compl,
      SuperdiffusionCLT.Section3.Terms.map_vadd_prod_eq (P := P) (Q := Q)]
    exact ht_null
  have hν : ∀ᵐ ω ∂P.toMeasure, (fun x => W (x +ᵥ ω)) =ᵐ[normalizedCubeMeasure Q]
      (fun x => G (x +ᵥ ω)) := by
    have hae : ∀ᵐ p ∂(P.toMeasure.prod (normalizedCubeMeasure Q)),
        p ∈ (fun p : ShellSeq d × Vec d => p.2 +ᵥ p.1) ⁻¹' t := by
      rw [MeasureTheory.ae_iff]
      exact hzero
    filter_upwards [MeasureTheory.Measure.ae_ae_of_ae_prod hae] with ω hω
    filter_upwards [hω] with x hx
    exact ht_sub (Set.mem_preimage.mp hx)
  filter_upwards [hν] with ω hω
  unfold volumeMeasureOn
  rw [volumeMeasureOn_openCubeSet_eq_smul_normalizedCubeMeasure Q]
  exact MeasureTheory.Measure.ae_smul_measure hω (ENNReal.ofReal (cubeVolume Q))

/-! ## The gradient class of an `H¹` function and of its mean-zero reduction -/

/-- The Hilbert-vector `L²` class of the gradient of an `H¹` function, read on an explicit
representative of that gradient. -/
theorem gradToHilbertVectorL2_eq_toLp {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {v : H1Function U} {G : Vec d → Vec d} (hgrad : v.grad = G)
    (hG : MemLp (fun x => HilbertVec.ofVec (G x)) 2 (volumeMeasureOn U)) :
    v.gradToHilbertVectorL2 = hG.toLp (fun x => HilbertVec.ofVec (G x)) := by
  rw [H1Function.gradToHilbertVectorL2, Homogenization.toHilbertVectorL2OfVecField,
    Homogenization.toHilbertVectorL2]
  refine MemLp.toLp_congr _ hG ?_
  filter_upwards with x
  have hx := congrFun hgrad x
  simp only [Homogenization.hilbertifyVecField, hx]

/-- Subtracting the average does not change the Hilbert-vector `L²` class of the gradient. -/
theorem gradToHilbertVectorL2_subAverage {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] (v : H1Function U) :
    v.subAverage.gradToHilbertVectorL2 = v.gradToHilbertVectorL2 := by
  refine MeasureTheory.Lp.ext ?_
  have h1 : v.subAverage.gradToHilbertVectorL2
      =ᵐ[volumeMeasureOn U] Homogenization.hilbertifyVecField v.subAverage.grad :=
    H1Function.coeFn_gradToHilbertVectorL2 v.subAverage
  have h2 : Homogenization.hilbertifyVecField v.subAverage.grad
      =ᵐ[volumeMeasureOn U] Homogenization.hilbertifyVecField v.grad := by
    filter_upwards with x
    have hx := H1Function.grad_subAverage v x
    simp only [Homogenization.hilbertifyVecField, hx]
  have h3 : Homogenization.hilbertifyVecField v.grad
      =ᵐ[volumeMeasureOn U] v.gradToHilbertVectorL2 :=
    (H1Function.coeFn_gradToHilbertVectorL2 v).symm
  exact h1.trans (h2.trans h3)

/-- A sequence whose squared `L²` deficit integral tends to zero tends to zero in `L²`. -/
theorem tendsto_eLpNorm_of_tendsto_lintegral {α E : Type*} [MeasurableSpace α]
    [SeminormedAddCommGroup E] {μ : Measure α} {H : ℕ → α → E}
    (hH : ∀ n, AEStronglyMeasurable (H n) μ)
    (h : Filter.Tendsto (fun n => ∫⁻ x, ‖H n x‖ₑ ^ (2 : ℝ) ∂μ) Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun n => eLpNorm (H n) 2 μ) Filter.atTop (𝓝 0) := by
  have hrpow : Filter.Tendsto
      (fun n => (∫⁻ x, ‖H n x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)) Filter.atTop (𝓝 0) := by
    have hc := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).continuousAt.tendsto.comp h
    rwa [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at hc
  refine hrpow.congr (fun n => ?_)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (by norm_num) (by norm_num) (hH n)]
  simp only [ENNReal.toReal_ofNat]

/-! ## The first conjunct -/

/-- **The first conjunct, for an honest measurable field.**  At the concrete carrier
`Ω := ShellSeq d`, for every measurable field `gradHatW` whose `L²(Ω)` class lies in the
closed stationary potential subspace, and for almost every sample `ω`, the spatial realization
`x ↦ gradHatW (x +ᵥ ω)` is the weak gradient of an honest `H¹` function on the cube
`openCubeSet (originCube d M)`.

The proof picks a sequence of honest strong horizontal gradients in the range whose classes
converge to the class of `gradHatW`, realizes each of them by `honestSlice`, extracts a single
subsequence along which the spatial slices converge for a.e. `ω`, and closes the mean-zero
`H¹` graph by Poincaré–Wirtinger.  The measurability of the field is consumed by `honestSlice`
and is not part of the data; it is discharged in
`exists_h1_realization_of_mem_stationaryPotentialSubspace`. -/
theorem exists_h1_realization_of_mem_stationaryPotentialSubspace_of_measurable
    {P : ProbabilityMeasure (ShellSeq d)}
    [VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure]
    (M : ℕ) {gradHatW : ShellSeq d → Vec d}
    (hGm : Measurable gradHatW)
    (hG : MemLp (fun ω => HilbertVec.ofVec (gradHatW ω)) 2 P.toMeasure)
    (hmem : hG.toLp (fun ω => HilbertVec.ofVec (gradHatW ω)) ∈
      stationaryPotentialSubspace (μ := P.toMeasure) (d := d)) :
    ∀ᵐ ω ∂P.toMeasure, ∃ u : H1Function (openCubeSet (originCube d (M : ℤ))),
      u.grad =ᵐ[volumeMeasureOn (openCubeSet (originCube d (M : ℤ)))]
        fun x => gradHatW (x +ᵥ ω) := by
  classical
  set Q : TriadicCube d := originCube d (M : ℤ) with hQ
  have hU : IsOpenBoundedConvexDomain (openCubeSet Q) := isOpenBoundedConvexDomain_openCubeSet Q
  have : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) := hU.isFiniteMeasure_restrict_volume
  have hmem' : hG.toLp (fun ω => HilbertVec.ofVec (gradHatW ω)) ∈
      (horizontalGradientRange (μ := P.toMeasure) (d := d)).topologicalClosure := by
    simpa only [stationaryPotentialSubspace] using hmem
  -- Step 1: a sequence of honest horizontal gradients converging to the class.
  have hex : ∀ n : ℕ, ∃ y ∈ (horizontalGradientRange (μ := P.toMeasure) (d := d) :
      Set (Lp (HilbertVec d) 2 P.toMeasure)),
      dist (hG.toLp (fun ω => HilbertVec.ofVec (gradHatW ω))) y < ((n : ℝ) + 1)⁻¹ := by
    intro n
    have hcl : hG.toLp (fun ω => HilbertVec.ofVec (gradHatW ω)) ∈
        closure ((horizontalGradientRange (μ := P.toMeasure) (d := d) :
          Set (Lp (HilbertVec d) 2 P.toMeasure))) := by
      rw [← Submodule.topologicalClosure_coe]
      exact hmem'
    exact Metric.mem_closure_iff.mp hcl _ (by positivity)
  choose G hGK hGd using hex
  have hcast : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1)) Filter.atTop Filter.atTop := by
    refine Filter.Tendsto.congr (fun n => ?_)
      ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (Filter.tendsto_add_atTop_nat 1))
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
  have hinv : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) Filter.atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hcast
  have hGtend : Filter.Tendsto G Filter.atTop
      (𝓝 (hG.toLp (fun ω => HilbertVec.ofVec (gradHatW ω)))) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hinv.eventually (Iio_mem_nhds hε))
    exact ⟨N, fun n hn => by
      have hdn := hGd n
      rw [dist_comm] at hdn
      exact lt_trans hdn (hN n hn)⟩
  -- Step 2: potentials, and honest measurable representatives.
  have hpot : ∀ n : ℕ, ∃ φ : Lp ℝ 2 P.toMeasure,
      HasHorizontalGradient (μ := P.toMeasure) φ (G n) := fun n => hGK n
  choose φ hφ using hpot
  have hrep : ∀ n : ℕ, ∃ F : ShellSeq d → Vec d, Measurable F ∧
      ∃ hF : MemLp (fun ω => HilbertVec.ofVec (F ω)) 2 P.toMeasure,
        hF.toLp (fun ω => HilbertVec.ofVec (F ω)) = G n :=
    fun n => exists_measurable_representative_of_vectorL2 (P := P) (G n)
  choose Fr hFrm hFrmem hFrtoLp using hrep
  have hrepp : ∀ n : ℕ, ∃ f : ShellSeq d → ℝ, Measurable f ∧
      ∃ hf : MemLp f 2 P.toMeasure, hf.toLp f = φ n :=
    fun n => exists_measurable_representative_of_scalarL2 (P := P) (φ n)
  choose φr hφrm hφrmem hφrtoLp using hrepp
  -- Step 3a: `honestSlice` for each member of the sequence.
  have hslice : ∀ n : ℕ, ∀ᵐ ω ∂P.toMeasure,
      HasWeakGradientOn (openCubeSet Q) (fun x => φr n (x +ᵥ ω)) (fun x => Fr n (x +ᵥ ω)) := by
    intro n
    refine honestSlice (P := P) (Q := Q) (φ := φr n) (F := Fr n) (hφrmem n) (hFrmem n)
      (hφrm n) (hFrm n) ?_
    rw [hφrtoLp n, hFrtoLp n]
    exact hφ n
  have hweak_all : ∀ᵐ ω ∂P.toMeasure, ∀ n : ℕ,
      HasWeakGradientOn (openCubeSet Q) (fun x => φr n (x +ᵥ ω)) (fun x => Fr n (x +ᵥ ω)) := by
    rw [MeasureTheory.ae_all_iff]
    exact hslice
  have hφsl : ∀ᵐ ω ∂P.toMeasure, ∀ n : ℕ,
      MemLp (fun x => φr n (x +ᵥ ω)) 2 (volumeMeasureOn (openCubeSet Q)) := by
    rw [MeasureTheory.ae_all_iff]
    exact fun n => ae_memLp_slice_openCube (P := P) Q (hφrm n) (hφrmem n)
  have hFsl : ∀ᵐ ω ∂P.toMeasure, ∀ n : ℕ, ∀ i : Fin d,
      MemLp (fun x => Fr n (x +ᵥ ω) i) 2 (volumeMeasureOn (openCubeSet Q)) := by
    rw [MeasureTheory.ae_all_iff]
    intro n
    rw [MeasureTheory.ae_all_iff]
    intro i
    exact ae_memLp_slice_openCube (P := P) Q (g := fun ω => Fr n ω i)
      ((measurable_pi_apply i).comp (hFrm n))
      (memLp_coord_of_memLp_ofVec (P := P) i (Fr n) (hFrmem n))
  have hFslv : ∀ᵐ ω ∂P.toMeasure, ∀ n : ℕ,
      MemLp (fun x => HilbertVec.ofVec (Fr n (x +ᵥ ω))) 2 (volumeMeasureOn (openCubeSet Q)) := by
    rw [MeasureTheory.ae_all_iff]
    exact fun n => ae_memLp_slice_openCube_vec (P := P) Q (hFrm n) (hFrmem n)
  -- Step 3b: the single subsequence, chosen once for all samples.
  have hdeficit0 : Filter.Tendsto
      (fun n => ∫⁻ ω, ‖G n ω - hG.toLp (fun ω => HilbertVec.ofVec (gradHatW ω)) ω‖ₑ
        ^ (2 : ℝ) ∂P.toMeasure) Filter.atTop (𝓝 0) :=
    tendsto_lintegral_enorm_sq_of_tendsto_Lp (E := HilbertVec d) (μ := P.toMeasure) hGtend
  have hdeficit : Filter.Tendsto
      (fun n => ∫⁻ ω, ‖HilbertVec.ofVec (Fr n ω) - HilbertVec.ofVec (gradHatW ω)‖ₑ
        ^ (2 : ℝ) ∂P.toMeasure) Filter.atTop (𝓝 0) := by
    refine Filter.Tendsto.congr' ?_ hdeficit0
    filter_upwards with n
    refine MeasureTheory.lintegral_congr_ae ?_
    have e1 : (G n : ShellSeq d → HilbertVec d) =ᵐ[P.toMeasure]
        fun ω => HilbertVec.ofVec (Fr n ω) := by
      have h := MemLp.coeFn_toLp (hFrmem n)
      rw [hFrtoLp n] at h
      exact h
    have e2 : (hG.toLp (fun ω => HilbertVec.ofVec (gradHatW ω)) : ShellSeq d → HilbertVec d)
        =ᵐ[P.toMeasure] fun ω => HilbertVec.ofVec (gradHatW ω) := MemLp.coeFn_toLp hG
    filter_upwards [e1, e2] with ω h1 h2
    rw [h1, h2]
  obtain ⟨k, _hk, hkslice⟩ := exists_strictMono_ae_tendsto_slice_lintegral_volumeOn (P := P)
    (Q := Q) (E := HilbertVec d)
    (f := fun n ω => HilbertVec.ofVec (Fr n ω))
    (g := fun ω => HilbertVec.ofVec (gradHatW ω))
    (fun n => (measurable_ofVec_hilbert.comp (hFrm n)).stronglyMeasurable)
    (measurable_ofVec_hilbert.comp hGm).stronglyMeasurable hdeficit
  have hGslv : ∀ᵐ ω ∂P.toMeasure,
      MemLp (fun x => HilbertVec.ofVec (gradHatW (x +ᵥ ω))) 2 (volumeMeasureOn (openCubeSet Q)) :=
    ae_memLp_slice_openCube_vec (P := P) Q hGm hG
  -- Step 4: close the mean-zero `H¹` graph sample by sample.
  filter_upwards [hweak_all, hφsl, hFsl, hFslv, hGslv, hkslice] with ω hweak hφsl hFsl hFslv hGslv hsub
  let v : ℕ → H1Function (openCubeSet Q) := fun n =>
    { toFun := fun x => φr (k n) (x +ᵥ ω)
      grad := fun x => Fr (k n) (x +ᵥ ω)
      memL2 := hφsl (k n)
      gradMemL2 := fun i => hFsl (k n) i
      hasWeakGradient := hweak (k n) }
  let w : ℕ → H1MeanZeroFunction (openCubeSet Q) := fun n =>
    ⟨(v n).subAverage, (v n).meanZeroOn_subAverage⟩
  have hwgrad : ∀ n : ℕ, (w n).gradToHilbertVectorL2 =
      (hFslv (k n)).toLp (fun x => HilbertVec.ofVec (Fr (k n) (x +ᵥ ω))) := by
    intro n
    have h1 : (w n).gradToHilbertVectorL2 = (v n).subAverage.gradToHilbertVectorL2 := rfl
    rw [h1, gradToHilbertVectorL2_subAverage]
    exact gradToHilbertVectorL2_eq_toLp rfl (hFslv (k n))
  have heLp : Filter.Tendsto (fun n => eLpNorm
      ((fun x => HilbertVec.ofVec (Fr (k n) (x +ᵥ ω))) -
        (fun x => HilbertVec.ofVec (gradHatW (x +ᵥ ω)))) 2
      (volumeMeasureOn (openCubeSet Q))) Filter.atTop (𝓝 0) :=
    tendsto_eLpNorm_of_tendsto_lintegral (E := HilbertVec d)
      (μ := volumeMeasureOn (openCubeSet Q))
      (fun n => (hFslv (k n)).aestronglyMeasurable.sub hGslv.aestronglyMeasurable) hsub
  have hlim : Filter.Tendsto
      (fun n => (hFslv (k n)).toLp (fun x => HilbertVec.ofVec (Fr (k n) (x +ᵥ ω))))
      Filter.atTop (𝓝 ((hGslv).toLp (fun x => HilbertVec.ofVec (gradHatW (x +ᵥ ω))))) :=
    (MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun n x => HilbertVec.ofVec (Fr (k n) (x +ᵥ ω)))
      (fun n => hFslv (k n)) (fun x => HilbertVec.ofVec (gradHatW (x +ᵥ ω))) hGslv).mpr heLp
  obtain ⟨ulim, hulim⟩ := exists_h1MeanZeroFunction_of_tendsto_gradToHilbertVectorL2
    (U := openCubeSet Q) hU (hlim.congr (fun n => (hwgrad n).symm))
  refine ⟨ulim.toH1Function, ?_⟩
  have h1 : (hGslv).toLp (fun x => HilbertVec.ofVec (gradHatW (x +ᵥ ω)))
      =ᵐ[volumeMeasureOn (openCubeSet Q)]
        Homogenization.hilbertifyVecField (ulim.toH1Function).grad := by
    rw [← hulim]
    exact H1Function.coeFn_gradToHilbertVectorL2 ulim.toH1Function
  have h2 : Homogenization.hilbertifyVecField (ulim.toH1Function).grad
      =ᵐ[volumeMeasureOn (openCubeSet Q)] fun x => HilbertVec.ofVec (gradHatW (x +ᵥ ω)) :=
    h1.symm.trans (MemLp.coeFn_toLp hGslv)
  have h3 : (fun x => HilbertVec.toVec
        (Homogenization.hilbertifyVecField (ulim.toH1Function).grad x))
      =ᵐ[volumeMeasureOn (openCubeSet Q)]
        (fun x => HilbertVec.toVec (HilbertVec.ofVec (gradHatW (x +ᵥ ω)))) := by
    filter_upwards [h2] with x hx
    rw [hx]
  have h4 : (fun x => HilbertVec.toVec
        (Homogenization.hilbertifyVecField (ulim.toH1Function).grad x))
      =ᵐ[volumeMeasureOn (openCubeSet Q)] (ulim.toH1Function).grad := by
    filter_upwards with x
    exact (HilbertVec.toVec_ofVec ((ulim.toH1Function).grad x)).symm
  have h5 : (fun x => HilbertVec.toVec (HilbertVec.ofVec (gradHatW (x +ᵥ ω))))
      =ᵐ[volumeMeasureOn (openCubeSet Q)] fun x => gradHatW (x +ᵥ ω) := by
    filter_upwards with x
    exact HilbertVec.toVec_ofVec (gradHatW (x +ᵥ ω))
  exact h4.symm.trans (h3.trans h5)

/-! ## The hypothesis set

The main statement binds only the finite second moment of the field and the projection
identity; it does not bind measurability of the field.  The two theorems below put the first
conjunct at exactly that hypothesis set. -/

/-- **The first conjunct of the stationary potential realization, with the measurability of
the field discharged.**  An `L²(Ω)` class carries only almost everywhere strong measurability,
while `honestSlice` consumes an honest measurable field.  The class of `gradHatW` is replaced
by an honest measurable representative with the same class, the measurable version is applied
to it, and `ae_slice_eq_of_ae_eq` identifies the slices of the representative with the slices
of `gradHatW` almost everywhere.  So only the finite second moment of the field and its
membership in the closed stationary potential subspace remain — the latter a genuine
hypothesis, the class it defines being smaller than `L²(Ω)`: this is not a statement about an
arbitrary `L²(Ω)` field. -/
theorem exists_h1_realization_of_mem_stationaryPotentialSubspace
    {P : ProbabilityMeasure (ShellSeq d)}
    [VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure]
    (M : ℕ) {gradHatW : ShellSeq d → Vec d}
    (hG : MemLp (fun ω => HilbertVec.ofVec (gradHatW ω)) 2 P.toMeasure)
    (hmem : hG.toLp (fun ω => HilbertVec.ofVec (gradHatW ω)) ∈
      stationaryPotentialSubspace (μ := P.toMeasure) (d := d)) :
    ∀ᵐ ω ∂P.toMeasure, ∃ u : H1Function (openCubeSet (originCube d (M : ℤ))),
      u.grad =ᵐ[volumeMeasureOn (openCubeSet (originCube d (M : ℤ)))]
        fun x => gradHatW (x +ᵥ ω) := by
  classical
  obtain ⟨W, hWm, hWmem, hWtoLp⟩ :=
    exists_measurable_representative_of_vectorL2 (P := P)
      (hG.toLp (fun ω => HilbertVec.ofVec (gradHatW ω)))
  have hWmem' : hWmem.toLp (fun ω => HilbertVec.ofVec (W ω)) ∈
      stationaryPotentialSubspace (μ := P.toMeasure) (d := d) := by
    rw [hWtoLp]
    exact hmem
  have h1 : (hWmem.toLp (fun ω => HilbertVec.ofVec (W ω)) : ShellSeq d → HilbertVec d)
      =ᵐ[P.toMeasure] fun ω => HilbertVec.ofVec (W ω) := MemLp.coeFn_toLp hWmem
  have h2 : (hWmem.toLp (fun ω => HilbertVec.ofVec (W ω)) : ShellSeq d → HilbertVec d)
      =ᵐ[P.toMeasure] fun ω => HilbertVec.ofVec (gradHatW ω) := by
    rw [hWtoLp]
    exact MemLp.coeFn_toLp hG
  have haeOfVec : (fun ω => HilbertVec.ofVec (W ω)) =ᵐ[P.toMeasure]
      fun ω => HilbertVec.ofVec (gradHatW ω) := h1.symm.trans h2
  have hae : W =ᵐ[P.toMeasure] gradHatW := haeOfVec.mono fun ω hω => by
    have h := congrArg HilbertVec.toVec hω
    simpa only [HilbertVec.toVec_ofVec] using h
  have hreal := exists_h1_realization_of_mem_stationaryPotentialSubspace_of_measurable
    (P := P) M hWm hWmem hWmem'
  have hslice := ae_slice_eq_of_ae_eq (P := P) hae (originCube d (M : ℤ))
  filter_upwards [hreal, hslice] with ω hω1 hω2
  obtain ⟨u, hu⟩ := hω1
  exact ⟨u, hu.trans hω2⟩

/-- **The first conjunct in the shape of the binder of the main statement.**  This is
`exists_h1_realization_of_mem_stationaryPotentialSubspace` with the stationary potential
membership discharged from the projection identity: the class of
`-stationaryPotentialProjection (F (·) 0)` lies in the closed stationary potential subspace by
`stationaryPotentialProjection_mem`.  The finite second moments of the two fields and the
projection equation are then the only inputs. -/
theorem exists_h1_realization_of_eq_neg_stationaryPotentialProjection
    {P : ProbabilityMeasure (ShellSeq d)}
    [VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure]
    (M : ℕ) {F : ShellSeq d → Vec d → Vec d} {gradHatW : ShellSeq d → Vec d}
    (hFmemLp : MemLp (fun ω => HilbertVec.ofVec (F ω 0)) 2 P.toMeasure)
    (hG : MemLp (fun ω => HilbertVec.ofVec (gradHatW ω)) 2 P.toMeasure)
    (hproj : hG.toLp (fun ω => HilbertVec.ofVec (gradHatW ω)) =
      -stationaryPotentialProjection (μ := P.toMeasure) (d := d)
        (hFmemLp.toLp (fun ω => HilbertVec.ofVec (F ω 0)))) :
    ∀ᵐ ω ∂P.toMeasure, ∃ u : H1Function (openCubeSet (originCube d (M : ℤ))),
      u.grad =ᵐ[volumeMeasureOn (openCubeSet (originCube d (M : ℤ)))]
        fun x => gradHatW (x +ᵥ ω) := by
  refine exists_h1_realization_of_mem_stationaryPotentialSubspace (P := P) M hG ?_
  rw [hproj]
  exact Submodule.neg_mem _
    (stationaryPotentialProjection_mem (μ := P.toMeasure) (d := d)
      (hFmemLp.toLp (fun ω => HilbertVec.ofVec (F ω 0))))

end SuperdiffusionCLT.Probability.Stationary

end
