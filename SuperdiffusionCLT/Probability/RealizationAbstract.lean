/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Probability.RealizationConjunctTwo

/-!
# Abstract stationary realization

Section 3 of the paper (stationary potential realization).
Joint measurability suffices on an arbitrary probability space; no topology
on the sample space is required. The first realization conjunct follows
from the projection identity. The second retains the concrete assembly's
explicit divergence step and countable test-gradient density input.
No necessity or counterexample to the weaker assumptions is asserted.
-/

@[expose] public section

open scoped ENNReal Topology
noncomputable section
namespace SuperdiffusionCLT.Probability.Stationary
/-- Null changes of a field remain null on almost every spatial slice. -/
theorem realizationAbstract_ae_slice_congr
    {d : ℕ} {Ω E : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.SFinite μ]
    [AddAction (Homogenization.Vec d) Ω] [MeasurableVAdd₂ (Homogenization.Vec d) Ω]
    [MeasureTheory.VAddInvariantMeasure (Homogenization.Vec d) Ω μ]
    (ν : MeasureTheory.Measure (Homogenization.Vec d)) [MeasureTheory.IsProbabilityMeasure ν]
    {f g : Ω → E} (h : f =ᵐ[μ] g) :
    ∀ᵐ ω ∂μ, (fun x => f (x +ᵥ ω)) =ᵐ[ν] (fun x => g (x +ᵥ ω)) := by
  have hmp : MeasureTheory.MeasurePreserving
      (fun p : Ω × Homogenization.Vec d => p.2 +ᵥ p.1) (μ.prod ν) μ :=
    ⟨measurable_vadd_prod, map_vadd_prod_eq_of_measurableVAdd₂ ν⟩
  exact MeasureTheory.Measure.ae_ae_of_ae_prod
    (h.comp_tendsto hmp.quasiMeasurePreserving.tendsto_ae)
universe u
variable {d : ℕ} {Ω : Type u} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
variable [AddAction (Homogenization.Vec d) Ω] [MeasurableVAdd₂ (Homogenization.Vec d) Ω] [MeasureTheory.VAddInvariantMeasure (Homogenization.Vec d) Ω μ]
omit [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.VAddInvariantMeasure (Homogenization.Vec d) Ω μ] in
theorem realizationAbstract_aemeasurable_realize_prod {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E] [TopologicalSpace.PseudoMetrizableSpace E] {X : Ω → E} (hX
    : MeasureTheory.StronglyMeasurable X) (Q : Homogenization.TriadicCube d) : AEMeasurable (fun p : Ω × Homogenization.Vec d => X (p.2 +ᵥ p.1)) (μ.prod (Homogenization.normalizedCubeMeasure Q)) :=
  (hX.comp_measurable (measurable_vadd_prod (d := d))).aemeasurable
theorem realizationAbstract_lintegral_enorm_rpow_realize_prod {E : Type*} [SeminormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] {X : Ω → E} (hX : MeasureTheory.StronglyMeasurable X) (Q :
    Homogenization.TriadicCube d) (r : ℝ) : ∫⁻ p : Ω × Homogenization.Vec d, ‖X (p.2 +ᵥ p.1)‖ₑ ^ r ∂(μ.prod (Homogenization.normalizedCubeMeasure Q)) = ∫⁻ ω, ‖X ω‖ₑ ^ r ∂μ := by
  let : MeasureTheory.IsProbabilityMeasure (Homogenization.normalizedCubeMeasure Q) := ⟨Homogenization.normalizedCubeMeasure_apply_univ Q⟩
  exact lintegral_vadd_prod_eq (μ := μ) (Homogenization.normalizedCubeMeasure Q) (hX.measurable.enorm.pow_const r).aemeasurable
private theorem realizationAbstract_tendsto_nhds_zero_of_tendsto_toReal_min {u : ℕ → ℝ≥0∞} (h : Filter.Tendsto (fun n => (min (u n) 1).toReal) Filter.atTop (𝓝 0)) : Filter.Tendsto u
    Filter.atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hδpos : 0 < min ε 1 := lt_min hε zero_lt_one
  have hδtop : min ε 1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right ε 1)
  have hδreal : (0 : ℝ) < (min ε 1).toReal := ENNReal.toReal_pos hδpos.ne' hδtop
  filter_upwards [h.eventually ((isOpen_Iio).mem_nhds (by simpa using hδreal))] with n hn
  have hlt : min (u n) 1 < min ε 1 :=
    calc min (u n) 1
        = ENNReal.ofReal ((min (u n) 1).toReal) :=
          (ENNReal.ofReal_toReal
            (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right (u n) 1))).symm
      _ < ENNReal.ofReal ((min ε 1).toReal) :=
          (ENNReal.ofReal_lt_ofReal_iff hδreal).mpr hn
      _ = min ε 1 := ENNReal.ofReal_toReal hδtop
  have hu : u n ≤ min ε 1 := by
    by_contra hcon
    push Not at hcon
    have h3 : min (min ε 1) 1 ≤ min (u n) 1 := min_le_min hcon.le le_rfl
    rw [min_eq_left (min_le_right ε 1)] at h3
    exact absurd h3 (not_le.mpr hlt)
  exact le_trans hu (min_le_left ε 1)
theorem realizationAbstract_exists_strictMono_ae_tendsto_slice_lintegral {E : Type*} [SeminormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] {Q : Homogenization.TriadicCube d} {f : ℕ → Ω →
    E} {g : Ω → E} (hf : ∀ n, MeasureTheory.StronglyMeasurable (f n)) (hg : MeasureTheory.StronglyMeasurable g) (h : Filter.Tendsto (fun n => ∫⁻ ω, ‖f n ω - g ω‖ₑ ^ (2 : ℝ) ∂μ) Filter.atTop (𝓝 0)) : ∃ k : ℕ →
    ℕ, StrictMono k ∧ ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => ∫⁻ x, ‖f (k n) (x +ᵥ ω) - g (x +ᵥ ω)‖ₑ ^ (2 : ℝ) ∂(Homogenization.normalizedCubeMeasure Q)) Filter.atTop (𝓝 0) := by
  classical
  have : MeasureTheory.IsProbabilityMeasure (Homogenization.normalizedCubeMeasure Q) :=
    ⟨Homogenization.normalizedCubeMeasure_apply_univ Q⟩
  have hjoint : ∀ n, AEMeasurable
      (fun p : Ω × Homogenization.Vec d => ‖f n (p.2 +ᵥ p.1) - g (p.2 +ᵥ p.1)‖ₑ ^ (2 : ℝ))
      (μ.prod (Homogenization.normalizedCubeMeasure Q)) := fun n =>
    ((realizationAbstract_aemeasurable_realize_prod (μ := μ) ((hf n).sub hg) Q).enorm).pow_const (2 : ℝ)
  have hG_ae : ∀ n, AEMeasurable
      (fun ω => ∫⁻ x, ‖f n (x +ᵥ ω) - g (x +ᵥ ω)‖ₑ ^ (2 : ℝ)
        ∂(Homogenization.normalizedCubeMeasure Q)) μ := fun n =>
    (hjoint n).lintegral_prod_right'
  have hG_int : ∀ n, (∫⁻ ω, ∫⁻ x, ‖f n (x +ᵥ ω) - g (x +ᵥ ω)‖ₑ ^ (2 : ℝ)
        ∂(Homogenization.normalizedCubeMeasure Q) ∂μ) =
      ∫⁻ ω, ‖f n ω - g ω‖ₑ ^ (2 : ℝ) ∂μ := by
    intro n
    have hprod : (∫⁻ p : Ω × Homogenization.Vec d,
          ‖(fun ω => f n ω - g ω) (p.2 +ᵥ p.1)‖ₑ ^ (2 : ℝ)
          ∂(μ.prod (Homogenization.normalizedCubeMeasure Q))) =
        ∫⁻ ω, ‖f n ω - g ω‖ₑ ^ (2 : ℝ) ∂μ :=
      realizationAbstract_lintegral_enorm_rpow_realize_prod (μ := μ) ((hf n).sub hg) Q (2 : ℝ)
    have hiter : (∫⁻ p : Ω × Homogenization.Vec d,
          ‖f n (p.2 +ᵥ p.1) - g (p.2 +ᵥ p.1)‖ₑ ^ (2 : ℝ)
          ∂(μ.prod (Homogenization.normalizedCubeMeasure Q))) =
        ∫⁻ ω, ∫⁻ x, ‖f n (x +ᵥ ω) - g (x +ᵥ ω)‖ₑ ^ (2 : ℝ)
          ∂(Homogenization.normalizedCubeMeasure Q) ∂μ :=
      MeasureTheory.lintegral_prod
        (fun p : Ω × Homogenization.Vec d => ‖f n (p.2 +ᵥ p.1) - g (p.2 +ᵥ p.1)‖ₑ ^ (2 : ℝ))
        (hjoint n)
    exact hiter.symm.trans hprod
  have hG_tend : Filter.Tendsto
      (fun n => ∫⁻ ω, ∫⁻ x, ‖f n (x +ᵥ ω) - g (x +ᵥ ω)‖ₑ ^ (2 : ℝ)
        ∂(Homogenization.normalizedCubeMeasure Q) ∂μ) Filter.atTop (𝓝 0) := by
    have heq : (fun n => ∫⁻ ω, ∫⁻ x, ‖f n (x +ᵥ ω) - g (x +ᵥ ω)‖ₑ ^ (2 : ℝ)
          ∂(Homogenization.normalizedCubeMeasure Q) ∂μ)
        = fun n => ∫⁻ ω, ‖f n ω - g ω‖ₑ ^ (2 : ℝ) ∂μ := funext hG_int
    rw [heq]
    exact h
  have hmin : Filter.Tendsto
      (fun n => ∫⁻ ω, min (∫⁻ x, ‖f n (x +ᵥ ω) - g (x +ᵥ ω)‖ₑ ^ (2 : ℝ)
        ∂(Homogenization.normalizedCubeMeasure Q)) 1 ∂μ) Filter.atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hG_tend
      (fun n => zero_le)
      (fun n => MeasureTheory.lintegral_mono (fun ω => min_le_left _ _))
  have hH_meas : ∀ n, MeasureTheory.AEStronglyMeasurable
      (fun ω => (min (∫⁻ x, ‖f n (x +ᵥ ω) - g (x +ᵥ ω)‖ₑ ^ (2 : ℝ)
        ∂(Homogenization.normalizedCubeMeasure Q)) 1).toReal) μ := fun n =>
    (ENNReal.measurable_toReal.comp_aemeasurable
      ((hG_ae n).min aemeasurable_const)).aestronglyMeasurable
  have hLp : Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (fun ω => (min (∫⁻ x, ‖f n (x +ᵥ ω) - g (x +ᵥ ω)‖ₑ ^ (2 : ℝ)
        ∂(Homogenization.normalizedCubeMeasure Q)) 1).toReal - 0) 1 μ) Filter.atTop (𝓝 0) := by
    have heq : (fun n => MeasureTheory.eLpNorm (fun ω => (min (∫⁻ x,
            ‖f n (x +ᵥ ω) - g (x +ᵥ ω)‖ₑ ^ (2 : ℝ)
            ∂(Homogenization.normalizedCubeMeasure Q)) 1).toReal - 0) 1 μ)
        = fun n => ∫⁻ ω, min (∫⁻ x, ‖f n (x +ᵥ ω) - g (x +ᵥ ω)‖ₑ ^ (2 : ℝ)
            ∂(Homogenization.normalizedCubeMeasure Q)) 1 ∂μ := by
      funext n
      refine (MeasureTheory.eLpNorm_one_eq_lintegral_enorm
        ((hH_meas n).sub MeasureTheory.aestronglyMeasurable_const)).trans ?_
      refine MeasureTheory.lintegral_congr fun ω => ?_
      simp only [Pi.sub_apply]
      rw [Real.enorm_eq_ofReal_abs, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal
          (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _))]
    rw [heq]
    exact hmin
  have hTIM : MeasureTheory.TendstoInMeasure μ
      (fun n ω => (min (∫⁻ x, ‖f n (x +ᵥ ω) - g (x +ᵥ ω)‖ₑ ^ (2 : ℝ)
        ∂(Homogenization.normalizedCubeMeasure Q)) 1).toReal) Filter.atTop (fun _ => (0 : ℝ)) :=
    MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hLp
  obtain ⟨k, hk, hae⟩ := hTIM.exists_seq_tendsto_ae
  exact ⟨k, hk, by
    filter_upwards [hae] with ω hω
    exact realizationAbstract_tendsto_nhds_zero_of_tendsto_toReal_min hω⟩
theorem realizationAbstract_exists_strictMono_ae_tendsto_slice_lintegral_volumeOn   {E : Type*} [SeminormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] {Q : Homogenization.TriadicCube d} {f
    : ℕ → Ω → E} {g : Ω → E} (hf : ∀ n, MeasureTheory.StronglyMeasurable (f n)) (hg : MeasureTheory.StronglyMeasurable g) (h : Filter.Tendsto (fun n => ∫⁻ ω, ‖f n ω - g ω‖ₑ ^ (2 : ℝ) ∂μ) Filter.atTop (𝓝 0)) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => ∫⁻ x, ‖f (k n) (x +ᵥ ω) - g (x +ᵥ ω)‖ₑ ^ (2 : ℝ) ∂(MeasureTheory.volume.restrict (Homogenization.openCubeSet Q))) Filter.atTop (𝓝
    0) := by
  obtain ⟨k, hk, hkconv⟩ :=
    realizationAbstract_exists_strictMono_ae_tendsto_slice_lintegral (μ := μ) (Q := Q) hf hg h
  refine ⟨k, hk, hkconv.mono fun ω hω => ?_⟩
  have hnorm : Homogenization.normalizedCubeMeasure Q = ENNReal.ofReal ((Homogenization.cubeVolume Q)⁻¹)
      • MeasureTheory.volume.restrict (Homogenization.openCubeSet Q) := by
    simp only [Homogenization.normalizedCubeMeasure, Homogenization.cubeMeasure,
      Homogenization.volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  rw [hnorm] at hω
  exact tendsto_lintegral_of_tendsto_smul_measure _
    (ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr (Homogenization.cubeVolume_pos Q)))
    ENNReal.ofReal_ne_top hω
omit [MeasurableSpace Ω] [MeasurableVAdd₂ (Homogenization.Vec d) Ω] in
theorem realizationAbstract_differenceQuotient_slice_eq (h : ℝ) (i : Fin d) (f : Ω → ℝ) (ω : Ω) (x : Homogenization.Vec d) : h⁻¹ * (f (h • Homogenization.basisVec i +ᵥ (x +ᵥ ω)) - f (x +ᵥ ω)) =
    Homogenization.euclideanForwardDifferenceQuotient h i (fun y : Homogenization.Vec d => f (y +ᵥ ω)) x := by
  have harg : h • Homogenization.basisVec i +ᵥ (x +ᵥ ω) =
      (x + h • Homogenization.basisVec i) +ᵥ ω := by
    rw [vadd_vadd, add_comm]
  rw [Homogenization.euclideanForwardDifferenceQuotient_apply,
    Homogenization.euclideanCoordShift_apply, harg, div_eq_mul_inv, mul_comm]
omit [MeasureTheory.IsProbabilityMeasure μ] in
theorem realizationAbstract_koopman_coeFn (x : Homogenization.Vec d) (g : ScalarL2 μ) : (koopman (μ := μ) x g : Ω → ℝ) =ᵐ[μ] fun ω => g (x +ᵥ ω) :=
  MeasureTheory.Lp.coeFn_compMeasurePreserving g
    (measurePreserving_const_vadd (μ := μ) (Ω := Ω) x)
omit [MeasureTheory.IsProbabilityMeasure μ] [AddAction (Homogenization.Vec d) Ω] [MeasurableVAdd₂ (Homogenization.Vec d) Ω] [MeasureTheory.VAddInvariantMeasure (Homogenization.Vec d) Ω μ] in
theorem realizationAbstract_vectorL2Coord_toLp (i : Fin d) (f : Ω → Homogenization.Vec d) (hf : MeasureTheory.MemLp (fun ω => Homogenization.HilbertVec.ofVec (f ω)) 2 μ) : (vectorL2Coord (μ := μ) i (hf.toLp (fun ω =>
    Homogenization.HilbertVec.ofVec (f ω))) : Ω → ℝ) =ᵐ[μ] fun ω => f ω i := by
  have h1 := ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := μ)
    (L := PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) i)
    (f := hf.toLp (fun ω => Homogenization.HilbertVec.ofVec (f ω)))
  have h2 := (MeasureTheory.MemLp.coeFn_toLp hf).fun_comp
    (PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) i)
  refine h1.trans (h2.trans ?_)
  filter_upwards with ω
  simp only [Function.comp_apply]
  simp
omit [MeasureTheory.IsProbabilityMeasure μ] [AddAction (Homogenization.Vec d) Ω] [MeasurableVAdd₂ (Homogenization.Vec d) Ω] [MeasureTheory.VAddInvariantMeasure (Homogenization.Vec d) Ω μ] in
theorem realizationAbstract_memLp_coord_of_memLp_ofVec (i : Fin d) (f : Ω → Homogenization.Vec d) (hf : MeasureTheory.MemLp (fun ω => Homogenization.HilbertVec.ofVec (f ω)) 2 μ) : MeasureTheory.MemLp (fun ω => f ω i) 2 μ := by
  refine ((PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) i).comp_memLp' hf).ae_eq ?_
  filter_upwards with ω
  simp only [Function.comp_apply]
  simp
theorem realizationAbstract_ae_memLp_slice_openCube (Q : Homogenization.TriadicCube d) {g : Ω → ℝ} (hgm : Measurable g) (hg : MeasureTheory.MemLp g 2 μ) : ∀ᵐ ω ∂μ, MeasureTheory.MemLp (fun x => g (x +ᵥ ω)) 2
    (MeasureTheory.volume.restrict (Homogenization.openCubeSet Q)) := by
  have : MeasureTheory.IsProbabilityMeasure (Homogenization.normalizedCubeMeasure Q) :=
    ⟨Homogenization.normalizedCubeMeasure_apply_univ Q⟩
  filter_upwards [ae_memLp_slice (μ := μ) (ν := Homogenization.normalizedCubeMeasure Q) hgm hg]
    with ω hω
  rw [volumeMeasureOn_openCubeSet_eq_smul_normalizedCubeMeasure Q]
  exact hω.smul_measure ENNReal.ofReal_ne_top
omit [MeasureTheory.IsProbabilityMeasure μ] in
theorem realizationAbstract_differenceQuotient_class_coeFn (h : ℝ) (i : Fin d) {f : Ω → ℝ} (hf : MeasureTheory.MemLp f 2 μ) : (((h⁻¹ : ℝ) • (koopman (μ := μ) (h • Homogenization.basisVec i)
    (hf.toLp f) - hf.toLp f) : ScalarL2 μ) : Ω → ℝ) =ᵐ[μ] fun ω => h⁻¹ * (f (h • Homogenization.basisVec i +ᵥ ω) - f ω) := by
  have hshift : Filter.Tendsto (fun ω : Ω => h • Homogenization.basisVec i +ᵥ ω)
      (MeasureTheory.ae μ) (MeasureTheory.ae μ) :=
    (measurePreserving_const_vadd (μ := μ) (Ω := Ω)
      (h • Homogenization.basisVec i)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [MeasureTheory.Lp.coeFn_smul (h⁻¹ : ℝ)
      (koopman (μ := μ) (h • Homogenization.basisVec i) (hf.toLp f) - hf.toLp f),
    MeasureTheory.Lp.coeFn_sub (koopman (μ := μ) (h • Homogenization.basisVec i) (hf.toLp f))
      (hf.toLp f),
    realizationAbstract_koopman_coeFn (μ := μ) (h • Homogenization.basisVec i) (hf.toLp f),
    (MeasureTheory.MemLp.coeFn_toLp hf).comp_tendsto hshift,
    MeasureTheory.MemLp.coeFn_toLp hf] with ω h0 h1 h2 h3 h4
  simp only [Function.comp_apply] at h3
  rw [h0, Pi.smul_apply, smul_eq_mul, h1, Pi.sub_apply, h2, h3, h4]
theorem realizationAbstract_differenceQuotient_measurable (h : ℝ) (i : Fin d) {f : Ω → ℝ} (hfm : Measurable f) : Measurable (fun ω : Ω => h⁻¹ * (f (h • Homogenization.basisVec i +ᵥ
    ω) - f ω)) :=
  ((hfm.comp (measurable_const_vadd (h • Homogenization.basisVec i))).sub hfm).const_mul h⁻¹
omit [MeasureTheory.IsProbabilityMeasure μ] in
theorem realizationAbstract_differenceQuotient_memLp (h : ℝ) (i : Fin d) {f : Ω → ℝ} (hf : MeasureTheory.MemLp f 2 μ) : MeasureTheory.MemLp (fun ω : Ω => h⁻¹ * (f (h • Homogenization.basisVec i +ᵥ ω) - f ω)) 2
    μ :=
  (MeasureTheory.Lp.memLp ((h⁻¹ : ℝ) • (koopman (μ := μ) (h • Homogenization.basisVec i)
    (hf.toLp f) - hf.toLp f))).ae_eq (realizationAbstract_differenceQuotient_class_coeFn (μ := μ) h i hf)
theorem realizationAbstract_ae_memLp_slice_differenceQuotient (Q : Homogenization.TriadicCube d) (h : ℝ) (i : Fin d) {f : Ω → ℝ} (hfm : Measurable f) (hf : MeasureTheory.MemLp f 2 μ) : ∀ᵐ ω ∂μ, MeasureTheory.MemLp (fun x =>
    Homogenization.euclideanForwardDifferenceQuotient h i (fun y : Homogenization.Vec d => f (y +ᵥ ω)) x) 2 (MeasureTheory.volume.restrict (Homogenization.openCubeSet Q)) := by
  filter_upwards [realizationAbstract_ae_memLp_slice_openCube (μ := μ) Q
    (realizationAbstract_differenceQuotient_measurable h i hfm)
    (realizationAbstract_differenceQuotient_memLp (μ := μ) h i hf)] with ω hω
  refine hω.ae_eq ?_
  filter_upwards with x
  exact realizationAbstract_differenceQuotient_slice_eq h i f ω x
theorem realizationAbstract_honestSlice (Q : Homogenization.TriadicCube d) {φ : Ω → ℝ} {F : Ω → Homogenization.Vec d} (hφ : MeasureTheory.MemLp φ 2 μ) (hF : MeasureTheory.MemLp (fun ω => Homogenization.HilbertVec.ofVec (F ω)) 2 μ) (hφm : Measurable φ)
    (hFm : Measurable F) (hgrad : HasHorizontalGradient (μ := μ) (hφ.toLp φ) (hF.toLp (fun ω => Homogenization.HilbertVec.ofVec (F ω)))) : ∀ᵐ ω ∂μ, Homogenization.HasWeakGradientOn (Homogenization.openCubeSet Q) (fun x => φ (x
    +ᵥ ω)) (fun x => F (x +ᵥ ω)) := by
  classical
  have : MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict (Homogenization.openCubeSet Q)) :=
    (Homogenization.isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hUopen : IsOpen (Homogenization.openCubeSet Q) := (Homogenization.isOpenBoundedConvexDomain_openCubeSet Q).isOpen
  have hUbd : Bornology.IsBounded (Homogenization.openCubeSet Q) :=
    (Homogenization.isOpenBoundedConvexDomain_openCubeSet Q).isBoundedDomain.isBounded
  let hs : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have hcast : Filter.Tendsto (fun n : ℕ => (n : ℝ) + 1) Filter.atTop Filter.atTop := by
    refine Filter.Tendsto.congr (fun n => ?_)
      ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (Filter.tendsto_add_atTop_nat 1))
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
  have hst : Filter.Tendsto hs Filter.atTop (𝓝[≠] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨tendsto_inv_atTop_zero.comp hcast, ?_⟩
    filter_upwards with n
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact inv_ne_zero (ne_of_gt (by positivity))
  have hφslice : ∀ᵐ ω ∂μ, MeasureTheory.MemLp (fun x => φ (x +ᵥ ω)) 2
      (MeasureTheory.volume.restrict (Homogenization.openCubeSet Q)) :=
    realizationAbstract_ae_memLp_slice_openCube (μ := μ) Q hφm hφ
  refine Filter.eventually_all.2 fun i => ?_
  have hFslice : ∀ᵐ ω ∂μ, MeasureTheory.MemLp (fun x => F (x +ᵥ ω) i) 2
      (MeasureTheory.volume.restrict (Homogenization.openCubeSet Q)) :=
    realizationAbstract_ae_memLp_slice_openCube (μ := μ) Q (g := fun ω => F ω i) ((measurable_pi_apply i).comp hFm)
      (realizationAbstract_memLp_coord_of_memLp_ofVec (μ := μ) i F hF)
  have hslope : Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (koopman (μ := μ) (t • Homogenization.basisVec i)
        (hφ.toLp φ) - hφ.toLp φ)) (𝓝[≠] (0 : ℝ))
      (𝓝 (vectorL2Coord (μ := μ) i (hF.toLp (fun ω => Homogenization.HilbertVec.ofVec (F ω))))) := by
    have h := HasDerivAt.tendsto_slope_zero (hgrad i)
    simp only [zero_add, zero_smul, koopman_zero] at h
    exact h
  let u : ℕ → ScalarL2 μ := fun n =>
    (hs n)⁻¹ • (koopman (μ := μ) (hs n • Homogenization.basisVec i) (hφ.toLp φ)
      - hφ.toLp φ)
  have hseq : Filter.Tendsto u Filter.atTop
      (𝓝 (vectorL2Coord (μ := μ) i (hF.toLp (fun ω => Homogenization.HilbertVec.ofVec (F ω))))) := by
    simp only [u]
    exact hslope.comp hst
  have hdeficit := tendsto_lintegral_enorm_sq_of_tendsto_Lp (E := ℝ) (μ := μ) hseq
  have hdeficit' : Filter.Tendsto
      (fun n => ∫⁻ ω, ‖(hs n)⁻¹ * (φ (hs n • Homogenization.basisVec i +ᵥ ω) - φ ω)
        - F ω i‖ₑ ^ (2 : ℝ) ∂μ) Filter.atTop (𝓝 0) := by
    refine Filter.Tendsto.congr' ?_ hdeficit
    filter_upwards with n
    refine MeasureTheory.lintegral_congr_ae ?_
    filter_upwards [realizationAbstract_differenceQuotient_class_coeFn (μ := μ) (hs n) i hφ,
      realizationAbstract_vectorL2Coord_toLp (μ := μ) i F hF] with ω h1 h2
    simp only [u]
    rw [h1, h2]
  obtain ⟨k, hk, hkconv⟩ := realizationAbstract_exists_strictMono_ae_tendsto_slice_lintegral_volumeOn (μ := μ)
    (Q := Q) (E := ℝ)
    (f := fun n ω => (hs n)⁻¹ * (φ (hs n • Homogenization.basisVec i +ᵥ ω) - φ ω))
    (g := fun ω => F ω i)
    (fun n => (realizationAbstract_differenceQuotient_measurable (hs n) i hφm).stronglyMeasurable)
    ((measurable_pi_apply i).comp hFm).stronglyMeasurable hdeficit'
  have hDqslice : ∀ᵐ ω ∂μ, ∀ n, MeasureTheory.MemLp (fun x =>
      Homogenization.euclideanForwardDifferenceQuotient (hs (k n)) i (fun y : Homogenization.Vec d => φ (y +ᵥ ω)) x)
      2 (MeasureTheory.volume.restrict (Homogenization.openCubeSet Q)) := by
    rw [MeasureTheory.ae_all_iff]
    exact fun n => realizationAbstract_ae_memLp_slice_differenceQuotient (μ := μ) Q (hs (k n)) i hφm hφ
  have hconv : ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => ∫⁻ x,
      ‖Homogenization.euclideanForwardDifferenceQuotient (hs (k n)) i
          (fun y : Homogenization.Vec d => φ (y +ᵥ ω)) x - F (x +ᵥ ω) i‖ₑ ^ (2 : ℝ)
        ∂(MeasureTheory.volume.restrict (Homogenization.openCubeSet Q))) Filter.atTop (𝓝 0) := by
    filter_upwards [hkconv] with ω hω
    refine Filter.Tendsto.congr (fun n => ?_) hω
    refine MeasureTheory.lintegral_congr fun x => ?_
    rw [realizationAbstract_differenceQuotient_slice_eq (hs (k n)) i φ ω x]
  exact ae_hasWeakPartialDerivOn_of_ae_tendsto_slice_deficit (μ := μ)
    (U := Homogenization.openCubeSet Q) hUopen hUbd (fun ω x => φ (x +ᵥ ω)) (fun ω x => F (x +ᵥ ω) i) i
    (hs := fun n => hs (k n)) (hst.comp hk.tendsto_atTop) hφslice hFslice hDqslice hconv
omit [MeasureTheory.IsProbabilityMeasure μ] in
theorem realizationAbstract_exists_measurable_representative_of_scalarL2 (φ : MeasureTheory.Lp ℝ 2 μ) : ∃ f : Ω → ℝ, Measurable f ∧ ∃ hf : MeasureTheory.MemLp f 2 μ, hf.toLp f = φ := by
  let f : Ω → ℝ := (MeasureTheory.Lp.aestronglyMeasurable φ).mk φ
  have hfm : Measurable f := (MeasureTheory.Lp.aestronglyMeasurable φ).measurable_mk
  have hae : (φ : Ω → ℝ) =ᵐ[μ] f := (MeasureTheory.Lp.aestronglyMeasurable φ).ae_eq_mk
  have hmem : MeasureTheory.MemLp f 2 μ := (MeasureTheory.Lp.memLp φ).ae_eq hae
  refine ⟨f, hfm, hmem, ?_⟩
  rw [MeasureTheory.MemLp.toLp_congr hmem (MeasureTheory.Lp.memLp φ) hae.symm]
  exact MeasureTheory.Lp.toLp_coeFn φ (MeasureTheory.Lp.memLp φ)
omit [MeasureTheory.IsProbabilityMeasure μ] [AddAction (Homogenization.Vec d) Ω] [MeasurableVAdd₂ (Homogenization.Vec d) Ω] [MeasureTheory.VAddInvariantMeasure (Homogenization.Vec d) Ω μ] in
theorem realizationAbstract_exists_measurable_representative_of_vectorL2 (G : MeasureTheory.Lp (Homogenization.HilbertVec d) 2 μ) : ∃ F : Ω → Homogenization.Vec d, Measurable F ∧ ∃ hF : MeasureTheory.MemLp (fun ω => Homogenization.HilbertVec.ofVec (F ω))
    2 μ, hF.toLp (fun ω => Homogenization.HilbertVec.ofVec (F ω)) = G := by
  let G' : Ω → Homogenization.HilbertVec d := (MeasureTheory.Lp.aestronglyMeasurable G).mk G
  have hG'm : Measurable G' := (MeasureTheory.Lp.aestronglyMeasurable G).measurable_mk
  have hG'MeasureTheory.ae : (G : Ω → Homogenization.HilbertVec d) =ᵐ[μ] G' :=
    (MeasureTheory.Lp.aestronglyMeasurable G).ae_eq_mk
  let F : Ω → Homogenization.Vec d := fun ω => Homogenization.HilbertVec.toVec (G' ω)
  have hFm : Measurable F := measurable_toVec_hilbert.comp hG'm
  have hG'mem : MeasureTheory.MemLp G' 2 μ := (MeasureTheory.Lp.memLp G).ae_eq hG'MeasureTheory.ae
  have haeF : (fun ω => Homogenization.HilbertVec.ofVec (F ω)) =ᵐ[μ] G' := by
    filter_upwards with ω
    exact Homogenization.HilbertVec.ofVec_toVec (G' ω)
  have hFmem : MeasureTheory.MemLp (fun ω => Homogenization.HilbertVec.ofVec (F ω)) 2 μ :=
    MeasureTheory.MemLp.ae_eq haeF hG'mem
  refine ⟨F, hFm, hFmem, ?_⟩
  rw [MeasureTheory.MemLp.toLp_congr hFmem (MeasureTheory.Lp.memLp G) (haeF.trans hG'MeasureTheory.ae.symm)]
  exact MeasureTheory.Lp.toLp_coeFn G (MeasureTheory.Lp.memLp G)
theorem realizationAbstract_ae_memLp_slice_openCube_vec  (Q : Homogenization.TriadicCube d) {g : Ω → Homogenization.Vec d} (hgm : Measurable g) (hg : MeasureTheory.MemLp (fun ω => Homogenization.HilbertVec.ofVec (g ω)) 2 μ) : ∀ᵐ ω ∂μ, MeasureTheory.MemLp
    (fun x => Homogenization.HilbertVec.ofVec (g (x +ᵥ ω))) 2 (MeasureTheory.volume.restrict (Homogenization.openCubeSet Q)) := by
  have : MeasureTheory.IsProbabilityMeasure (Homogenization.normalizedCubeMeasure Q) :=
    ⟨Homogenization.normalizedCubeMeasure_apply_univ Q⟩
  filter_upwards [ae_memLp_slice (μ := μ) (ν := Homogenization.normalizedCubeMeasure Q)
    (measurable_ofVec_hilbert.comp hgm) hg] with ω hω
  rw [volumeMeasureOn_openCubeSet_eq_smul_normalizedCubeMeasure Q]
  exact hω.smul_measure ENNReal.ofReal_ne_top
theorem realizationAbstract_ae_slice_eq_of_ae_eq  {W G : Ω → Homogenization.Vec d} (h : W =ᵐ[μ] G) (Q : Homogenization.TriadicCube d) : ∀ᵐ ω ∂μ, (fun x => W (x +ᵥ ω)) =ᵐ[Homogenization.volumeMeasureOn (Homogenization.openCubeSet Q)] (fun x
    => G (x +ᵥ ω)) := by
  let : MeasureTheory.IsProbabilityMeasure (Homogenization.normalizedCubeMeasure Q) := ⟨Homogenization.normalizedCubeMeasure_apply_univ Q⟩
  filter_upwards [realizationAbstract_ae_slice_congr (Homogenization.normalizedCubeMeasure Q) h] with ω hω
  unfold Homogenization.volumeMeasureOn
  rw [volumeMeasureOn_openCubeSet_eq_smul_normalizedCubeMeasure Q]
  exact MeasureTheory.Measure.ae_smul_measure hω (ENNReal.ofReal (Homogenization.cubeVolume Q))
theorem realizationAbstract_exists_h1_realization_of_mem_stationaryPotentialSubspace_of_measurable   (M : ℕ) {gradHatW : Ω → Homogenization.Vec d} (hGm : Measurable gradHatW) (hG : MeasureTheory.MemLp (fun ω =>
    Homogenization.HilbertVec.ofVec (gradHatW ω)) 2 μ) (hmem : hG.toLp (fun ω => Homogenization.HilbertVec.ofVec (gradHatW ω)) ∈ stationaryPotentialSubspace (μ := μ) (d := d)) : ∀ᵐ ω ∂μ, ∃ u : Homogenization.H1Function
    (Homogenization.openCubeSet (Homogenization.originCube d (M : ℤ))), u.grad =ᵐ[Homogenization.volumeMeasureOn (Homogenization.openCubeSet (Homogenization.originCube d (M : ℤ)))] fun x => gradHatW (x +ᵥ ω) := by
  classical
  set Q : Homogenization.TriadicCube d := Homogenization.originCube d (M : ℤ) with hQ
  have hU : Homogenization.IsOpenBoundedConvexDomain (Homogenization.openCubeSet Q) := Homogenization.isOpenBoundedConvexDomain_openCubeSet Q
  have : MeasureTheory.IsFiniteMeasure (Homogenization.volumeMeasureOn (Homogenization.openCubeSet Q)) := hU.isFiniteMeasure_restrict_volume
  have hmem' : hG.toLp (fun ω => Homogenization.HilbertVec.ofVec (gradHatW ω)) ∈
      (horizontalGradientRange (μ := μ) (d := d)).topologicalClosure := by
    simpa only [stationaryPotentialSubspace] using hmem
  have hex : ∀ n : ℕ, ∃ y ∈ (horizontalGradientRange (μ := μ) (d := d) :
      Set (MeasureTheory.Lp (Homogenization.HilbertVec d) 2 μ)),
      dist (hG.toLp (fun ω => Homogenization.HilbertVec.ofVec (gradHatW ω))) y < ((n : ℝ) + 1)⁻¹ := by
    intro n
    have hcl : hG.toLp (fun ω => Homogenization.HilbertVec.ofVec (gradHatW ω)) ∈
        closure ((horizontalGradientRange (μ := μ) (d := d) :
          Set (MeasureTheory.Lp (Homogenization.HilbertVec d) 2 μ))) := by
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
      (𝓝 (hG.toLp (fun ω => Homogenization.HilbertVec.ofVec (gradHatW ω)))) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hinv.eventually (Iio_mem_nhds hε))
    exact ⟨N, fun n hn => by
      have hdn := hGd n
      rw [dist_comm] at hdn
      exact lt_trans hdn (hN n hn)⟩
  have hpot : ∀ n : ℕ, ∃ φ : MeasureTheory.Lp ℝ 2 μ,
      HasHorizontalGradient (μ := μ) φ (G n) := fun n => hGK n
  choose φ hφ using hpot
  have hrep : ∀ n : ℕ, ∃ F : Ω → Homogenization.Vec d, Measurable F ∧
      ∃ hF : MeasureTheory.MemLp (fun ω => Homogenization.HilbertVec.ofVec (F ω)) 2 μ,
        hF.toLp (fun ω => Homogenization.HilbertVec.ofVec (F ω)) = G n :=
    fun n => realizationAbstract_exists_measurable_representative_of_vectorL2 (μ := μ) (G n)
  choose Fr hFrm hFrmem hFrtoLp using hrep
  have hrepp : ∀ n : ℕ, ∃ f : Ω → ℝ, Measurable f ∧
      ∃ hf : MeasureTheory.MemLp f 2 μ, hf.toLp f = φ n :=
    fun n => realizationAbstract_exists_measurable_representative_of_scalarL2 (μ := μ) (φ n)
  choose φr hφrm hφrmem hφrtoLp using hrepp
  have hslice : ∀ n : ℕ, ∀ᵐ ω ∂μ,
      Homogenization.HasWeakGradientOn (Homogenization.openCubeSet Q) (fun x => φr n (x +ᵥ ω)) (fun x => Fr n (x +ᵥ ω)) := by
    intro n
    refine realizationAbstract_honestSlice (μ := μ) (Q := Q) (φ := φr n) (F := Fr n) (hφrmem n) (hFrmem n)
      (hφrm n) (hFrm n) ?_
    rw [hφrtoLp n, hFrtoLp n]
    exact hφ n
  have hweak_all : ∀ᵐ ω ∂μ, ∀ n : ℕ,
      Homogenization.HasWeakGradientOn (Homogenization.openCubeSet Q) (fun x => φr n (x +ᵥ ω)) (fun x => Fr n (x +ᵥ ω)) := by
    rw [MeasureTheory.ae_all_iff]
    exact hslice
  have hφsl : ∀ᵐ ω ∂μ, ∀ n : ℕ,
      MeasureTheory.MemLp (fun x => φr n (x +ᵥ ω)) 2 (Homogenization.volumeMeasureOn (Homogenization.openCubeSet Q)) := by
    rw [MeasureTheory.ae_all_iff]
    exact fun n => realizationAbstract_ae_memLp_slice_openCube (μ := μ) Q (hφrm n) (hφrmem n)
  have hFsl : ∀ᵐ ω ∂μ, ∀ n : ℕ, ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => Fr n (x +ᵥ ω) i) 2 (Homogenization.volumeMeasureOn (Homogenization.openCubeSet Q)) := by
    rw [MeasureTheory.ae_all_iff]
    intro n
    rw [MeasureTheory.ae_all_iff]
    intro i
    exact realizationAbstract_ae_memLp_slice_openCube (μ := μ) Q (g := fun ω => Fr n ω i) ((measurable_pi_apply i).comp (hFrm n))
      (realizationAbstract_memLp_coord_of_memLp_ofVec (μ := μ) i (Fr n) (hFrmem n))
  have hFslv : ∀ᵐ ω ∂μ, ∀ n : ℕ,
      MeasureTheory.MemLp (fun x => Homogenization.HilbertVec.ofVec (Fr n (x +ᵥ ω))) 2 (Homogenization.volumeMeasureOn (Homogenization.openCubeSet Q)) := by
    rw [MeasureTheory.ae_all_iff]
    exact fun n => realizationAbstract_ae_memLp_slice_openCube_vec (μ := μ) Q (hFrm n) (hFrmem n)
  have hdeficit0 : Filter.Tendsto
      (fun n => ∫⁻ ω, ‖G n ω - hG.toLp (fun ω => Homogenization.HilbertVec.ofVec (gradHatW ω)) ω‖ₑ
        ^ (2 : ℝ) ∂μ) Filter.atTop (𝓝 0) :=
    tendsto_lintegral_enorm_sq_of_tendsto_Lp (E := Homogenization.HilbertVec d) (μ := μ) hGtend
  have hdeficit : Filter.Tendsto
      (fun n => ∫⁻ ω, ‖Homogenization.HilbertVec.ofVec (Fr n ω) - Homogenization.HilbertVec.ofVec (gradHatW ω)‖ₑ
        ^ (2 : ℝ) ∂μ) Filter.atTop (𝓝 0) := by
    refine Filter.Tendsto.congr' ?_ hdeficit0
    filter_upwards with n
    refine MeasureTheory.lintegral_congr_ae ?_
    have e1 : (G n : Ω → Homogenization.HilbertVec d) =ᵐ[μ]
        fun ω => Homogenization.HilbertVec.ofVec (Fr n ω) := by
      have h := MeasureTheory.MemLp.coeFn_toLp (hFrmem n)
      rw [hFrtoLp n] at h
      exact h
    have e2 : (hG.toLp (fun ω => Homogenization.HilbertVec.ofVec (gradHatW ω)) : Ω → Homogenization.HilbertVec d)
        =ᵐ[μ] fun ω => Homogenization.HilbertVec.ofVec (gradHatW ω) := MeasureTheory.MemLp.coeFn_toLp hG
    filter_upwards [e1, e2] with ω h1 h2
    rw [h1, h2]
  obtain ⟨k, _hk, hkslice⟩ := realizationAbstract_exists_strictMono_ae_tendsto_slice_lintegral_volumeOn (μ := μ)
    (Q := Q) (E := Homogenization.HilbertVec d)
    (f := fun n ω => Homogenization.HilbertVec.ofVec (Fr n ω))
    (g := fun ω => Homogenization.HilbertVec.ofVec (gradHatW ω))
    (fun n => (measurable_ofVec_hilbert.comp (hFrm n)).stronglyMeasurable)
    (measurable_ofVec_hilbert.comp hGm).stronglyMeasurable hdeficit
  have hGslv : ∀ᵐ ω ∂μ,
      MeasureTheory.MemLp (fun x => Homogenization.HilbertVec.ofVec (gradHatW (x +ᵥ ω))) 2 (Homogenization.volumeMeasureOn (Homogenization.openCubeSet Q)) :=
    realizationAbstract_ae_memLp_slice_openCube_vec (μ := μ) Q hGm hG
  filter_upwards [hweak_all, hφsl, hFsl, hFslv, hGslv, hkslice] with ω hweak hφsl hFsl hFslv hGslv hsub
  let v : ℕ → Homogenization.H1Function (Homogenization.openCubeSet Q) := fun n =>
    { toFun := fun x => φr (k n) (x +ᵥ ω)
      grad := fun x => Fr (k n) (x +ᵥ ω)
      memL2 := hφsl (k n)
      gradMemL2 := fun i => hFsl (k n) i
      hasWeakGradient := hweak (k n) }
  let w : ℕ → Homogenization.H1MeanZeroFunction (Homogenization.openCubeSet Q) := fun n =>
    ⟨(v n).subAverage, (v n).meanZeroOn_subAverage⟩
  have hwgrad : ∀ n : ℕ, (w n).gradToHilbertVectorL2 =
      (hFslv (k n)).toLp (fun x => Homogenization.HilbertVec.ofVec (Fr (k n) (x +ᵥ ω))) := by
    intro n
    have h1 : (w n).gradToHilbertVectorL2 = (v n).subAverage.gradToHilbertVectorL2 := rfl
    rw [h1, gradToHilbertVectorL2_subAverage]
    exact gradToHilbertVectorL2_eq_toLp rfl (hFslv (k n))
  have heLp : Filter.Tendsto (fun n => MeasureTheory.eLpNorm
      ((fun x => Homogenization.HilbertVec.ofVec (Fr (k n) (x +ᵥ ω))) -
        (fun x => Homogenization.HilbertVec.ofVec (gradHatW (x +ᵥ ω)))) 2
      (Homogenization.volumeMeasureOn (Homogenization.openCubeSet Q))) Filter.atTop (𝓝 0) :=
    tendsto_eLpNorm_of_tendsto_lintegral (E := Homogenization.HilbertVec d)
      (μ := Homogenization.volumeMeasureOn (Homogenization.openCubeSet Q))
      (fun n => (hFslv (k n)).aestronglyMeasurable.sub hGslv.aestronglyMeasurable) hsub
  have hlim : Filter.Tendsto
      (fun n => (hFslv (k n)).toLp (fun x => Homogenization.HilbertVec.ofVec (Fr (k n) (x +ᵥ ω))))
      Filter.atTop (𝓝 ((hGslv).toLp (fun x => Homogenization.HilbertVec.ofVec (gradHatW (x +ᵥ ω))))) :=
    (MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun n x => Homogenization.HilbertVec.ofVec (Fr (k n) (x +ᵥ ω)))
      (fun n => hFslv (k n)) (fun x => Homogenization.HilbertVec.ofVec (gradHatW (x +ᵥ ω))) hGslv).mpr heLp
  obtain ⟨ulim, hulim⟩ := exists_h1MeanZeroFunction_of_tendsto_gradToHilbertVectorL2
    (U := Homogenization.openCubeSet Q) hU (hlim.congr (fun n => (hwgrad n).symm))
  refine ⟨ulim.toH1Function, ?_⟩
  have h1 : (hGslv).toLp (fun x => Homogenization.HilbertVec.ofVec (gradHatW (x +ᵥ ω)))
      =ᵐ[Homogenization.volumeMeasureOn (Homogenization.openCubeSet Q)]
        Homogenization.hilbertifyVecField (ulim.toH1Function).grad := by
    rw [← hulim]
    exact Homogenization.H1Function.coeFn_gradToHilbertVectorL2 ulim.toH1Function
  have h2 : Homogenization.hilbertifyVecField (ulim.toH1Function).grad
      =ᵐ[Homogenization.volumeMeasureOn (Homogenization.openCubeSet Q)] fun x => Homogenization.HilbertVec.ofVec (gradHatW (x +ᵥ ω)) :=
    h1.symm.trans (MeasureTheory.MemLp.coeFn_toLp hGslv)
  exact h2.mono fun x hx => by
    have heq := congrArg Homogenization.HilbertVec.toVec hx
    simpa only [Homogenization.hilbertifyVecField, Homogenization.HilbertVec.toVec_ofVec] using heq

theorem realizationAbstract_exists_h1_realization_of_mem_stationaryPotentialSubspace   (M : ℕ) {gradHatW : Ω → Homogenization.Vec d} (hG : MeasureTheory.MemLp (fun ω => Homogenization.HilbertVec.ofVec (gradHatW ω)) 2 μ) (hmem
    : hG.toLp (fun ω => Homogenization.HilbertVec.ofVec (gradHatW ω)) ∈ stationaryPotentialSubspace (μ := μ) (d := d)) : ∀ᵐ ω ∂μ, ∃ u : Homogenization.H1Function (Homogenization.openCubeSet (Homogenization.originCube d (M : ℤ))), u.grad
    =ᵐ[Homogenization.volumeMeasureOn (Homogenization.openCubeSet (Homogenization.originCube d (M : ℤ)))] fun x => gradHatW (x +ᵥ ω) := by
  classical
  obtain ⟨W, hWm, hWmem, hWtoLp⟩ :=
    realizationAbstract_exists_measurable_representative_of_vectorL2 (μ := μ)
      (hG.toLp (fun ω => Homogenization.HilbertVec.ofVec (gradHatW ω)))
  have hWmem' : hWmem.toLp (fun ω => Homogenization.HilbertVec.ofVec (W ω)) ∈
      stationaryPotentialSubspace (μ := μ) (d := d) := by
    rw [hWtoLp]
    exact hmem
  have h1 : (hWmem.toLp (fun ω => Homogenization.HilbertVec.ofVec (W ω)) : Ω → Homogenization.HilbertVec d)
      =ᵐ[μ] fun ω => Homogenization.HilbertVec.ofVec (W ω) := MeasureTheory.MemLp.coeFn_toLp hWmem
  have h2 : (hWmem.toLp (fun ω => Homogenization.HilbertVec.ofVec (W ω)) : Ω → Homogenization.HilbertVec d)
      =ᵐ[μ] fun ω => Homogenization.HilbertVec.ofVec (gradHatW ω) := by
    rw [hWtoLp]
    exact MeasureTheory.MemLp.coeFn_toLp hG
  have haeOfVec : (fun ω => Homogenization.HilbertVec.ofVec (W ω)) =ᵐ[μ]
      fun ω => Homogenization.HilbertVec.ofVec (gradHatW ω) := h1.symm.trans h2
  have hae : W =ᵐ[μ] gradHatW := haeOfVec.mono fun ω hω => by
    have h := congrArg Homogenization.HilbertVec.toVec hω
    simpa only [Homogenization.HilbertVec.toVec_ofVec] using h
  have hreal := realizationAbstract_exists_h1_realization_of_mem_stationaryPotentialSubspace_of_measurable
    (μ := μ) M hWm hWmem hWmem'
  have hslice := realizationAbstract_ae_slice_eq_of_ae_eq (μ := μ) hae (Homogenization.originCube d (M : ℤ))
  filter_upwards [hreal, hslice] with ω hω1 hω2
  obtain ⟨u, hu⟩ := hω1
  exact ⟨u, hu.trans hω2⟩
theorem realizationAbstract_exists_h1_realization_of_eq_neg_stationaryPotentialProjection   (M : ℕ) {F : Ω → Homogenization.Vec d → Homogenization.Vec d} {gradHatW : Ω → Homogenization.Vec d} (hFmemLp : MeasureTheory.MemLp (fun ω =>
    Homogenization.HilbertVec.ofVec (F ω 0)) 2 μ) (hG : MeasureTheory.MemLp (fun ω => Homogenization.HilbertVec.ofVec (gradHatW ω)) 2 μ) (hproj : hG.toLp (fun ω => Homogenization.HilbertVec.ofVec (gradHatW ω)) =
    -stationaryPotentialProjection (μ := μ) (d := d) (hFmemLp.toLp (fun ω => Homogenization.HilbertVec.ofVec (F ω 0)))) : ∀ᵐ ω ∂μ, ∃ u : Homogenization.H1Function (Homogenization.openCubeSet (Homogenization.originCube d (M : ℤ))), u.grad
    =ᵐ[Homogenization.volumeMeasureOn (Homogenization.openCubeSet (Homogenization.originCube d (M : ℤ)))] fun x => gradHatW (x +ᵥ ω) := by
  refine realizationAbstract_exists_h1_realization_of_mem_stationaryPotentialSubspace (μ := μ) M hG ?_
  rw [hproj]
  exact Submodule.neg_mem _
    (stationaryPotentialProjection_mem (μ := μ) (d := d)
      (hFmemLp.toLp (fun ω => Homogenization.HilbertVec.ofVec (F ω 0))))
def realizationAbstract_anchorStationaryField (gradHatW : Ω → Homogenization.Vec d) (F : Ω → Homogenization.Vec d → Homogenization.Vec d) (ω : Ω) : Homogenization.Vec d :=
  gradHatW ω + F ω 0
omit [MeasurableSpace Ω] [AddAction (Homogenization.Vec d) Ω] [MeasurableVAdd₂ (Homogenization.Vec d) Ω] in
theorem realizationAbstract_ofVec_anchorStationaryField (gradHatW : Ω → Homogenization.Vec d) (F : Ω → Homogenization.Vec d → Homogenization.Vec d) (ω : Ω) : Homogenization.HilbertVec.ofVec (realizationAbstract_anchorStationaryField gradHatW
    F ω) = Homogenization.HilbertVec.ofVec (gradHatW ω) + Homogenization.HilbertVec.ofVec (F ω 0) := by
  ext i
  simp [realizationAbstract_anchorStationaryField]
omit [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.VAddInvariantMeasure (Homogenization.Vec d) Ω μ] [AddAction (Homogenization.Vec d) Ω] [MeasurableVAdd₂ (Homogenization.Vec d) Ω] in
theorem realizationAbstract_anchorStationaryField_memLp  {gradHatW : Ω → Homogenization.Vec d} {F : Ω → Homogenization.Vec d → Homogenization.Vec d} (hF : MeasureTheory.MemLp (fun ω : Ω => Homogenization.HilbertVec.ofVec (F ω 0)) 2 μ) (hG : MeasureTheory.MemLp (fun ω :
    Ω => Homogenization.HilbertVec.ofVec (gradHatW ω)) 2 μ) : MeasureTheory.MemLp (fun ω : Ω => Homogenization.HilbertVec.ofVec (realizationAbstract_anchorStationaryField gradHatW F ω)) 2 μ := by
  have h : (fun ω : Ω => Homogenization.HilbertVec.ofVec (realizationAbstract_anchorStationaryField gradHatW F ω)) =
      fun ω : Ω => Homogenization.HilbertVec.ofVec (gradHatW ω) + Homogenization.HilbertVec.ofVec (F ω 0) :=
    funext fun ω => realizationAbstract_ofVec_anchorStationaryField gradHatW F ω
  rw [h]
  exact hG.add hF
omit [MeasureTheory.IsProbabilityMeasure μ] in
theorem realizationAbstract_anchorStationaryField_toLp_mem_stationarySolenoidalSubspace   {gradHatW : Ω → Homogenization.Vec d} {F : Ω → Homogenization.Vec d → Homogenization.Vec d} {hF : MeasureTheory.MemLp (fun ω : Ω => Homogenization.HilbertVec.ofVec
    (F ω 0)) 2 μ} {hG : MeasureTheory.MemLp (fun ω : Ω => Homogenization.HilbertVec.ofVec (gradHatW ω)) 2 μ} (hproj : hG.toLp (fun ω : Ω => Homogenization.HilbertVec.ofVec (gradHatW ω)) = -stationaryPotentialProjection (μ :=
    μ) (d := d) (hF.toLp (fun ω : Ω => Homogenization.HilbertVec.ofVec (F ω 0)))) : (realizationAbstract_anchorStationaryField_memLp (μ := μ) hF hG).toLp (fun ω : Ω => Homogenization.HilbertVec.ofVec
    (realizationAbstract_anchorStationaryField gradHatW F ω)) ∈ stationarySolenoidalSubspace (μ := μ) (d := d) := by
  have h := SuperdiffusionCLT.Section3.Terms.add_field_toLp_mem_stationarySolenoidalSubspace
    (μ := μ) hproj
  have hkey : (realizationAbstract_anchorStationaryField_memLp (μ := μ) hF hG).toLp
      (fun ω : Ω => Homogenization.HilbertVec.ofVec (realizationAbstract_anchorStationaryField gradHatW F ω)) =
      (hG.add hF).toLp (fun ω : Ω =>
        Homogenization.HilbertVec.ofVec (gradHatW ω) + Homogenization.HilbertVec.ofVec (F ω 0)) :=
    MeasureTheory.MemLp.toLp_congr (realizationAbstract_anchorStationaryField_memLp (μ := μ) hF hG) (hG.add hF)
      (Filter.Eventually.of_forall fun ω => realizationAbstract_ofVec_anchorStationaryField gradHatW F ω)
  rwa [hkey]
omit [MeasurableSpace Ω] [MeasurableVAdd₂ (Homogenization.Vec d) Ω] in
theorem realizationAbstract_weakEquation_of_anchorPairing_eq_zero (M : ℕ) {F : Ω → Homogenization.Vec d → Homogenization.Vec d} {gradHatW : Ω → Homogenization.Vec d} {ω : Ω} {u : Homogenization.H1Function (Homogenization.openCubeSet (Homogenization.originCube d (M :
    ℤ)))} (hgrad : u.grad =ᵐ[Homogenization.volumeMeasureOn (Homogenization.openCubeSet (Homogenization.originCube d (M : ℤ)))] fun x => gradHatW (x +ᵥ ω)) (hcocycle : ∀ x y : Homogenization.Vec d, F (x +ᵥ ω) y = F ω (y + x)) (hGslice :
    MeasureTheory.MemLp (fun x => Homogenization.HilbertVec.ofVec (gradHatW (x +ᵥ ω))) 2 (Homogenization.volumeMeasureOn (Homogenization.openCubeSet (Homogenization.originCube d (M : ℤ))))) (hFslice : MeasureTheory.MemLp (fun x => Homogenization.HilbertVec.ofVec (F (x +ᵥ ω) 0)) 2
    (Homogenization.volumeMeasureOn (Homogenization.openCubeSet (Homogenization.originCube d (M : ℤ))))) (hanchor : ∀ φ : Homogenization.H10Function (Homogenization.openCubeSet (Homogenization.originCube d (M : ℤ))), ∫ x in Homogenization.openCubeSet (Homogenization.originCube d (M : ℤ)), Homogenization.vecDot
    (realizationAbstract_anchorStationaryField gradHatW F (x +ᵥ ω)) (φ.toH1Function.grad x) = 0) : ∀ φ : Homogenization.H10Function (Homogenization.openCubeSet (Homogenization.originCube d (M : ℤ))), ∫ x in Homogenization.openCubeSet
    (Homogenization.originCube d (M : ℤ)), Homogenization.vecDot (u.grad x) (φ.toH1Function.grad x) = -∫ x in Homogenization.openCubeSet (Homogenization.originCube d (M : ℤ)), Homogenization.vecDot (F ω x) (φ.toH1Function.grad x) := by
  intro φ
  have hGc : u.gradToHilbertVectorL2 = hGslice.toLp
      (fun x => Homogenization.HilbertVec.ofVec (gradHatW (x +ᵥ ω))) :=
    gradToHilbertVectorL2_eq_toLp_of_ae_eq hgrad hGslice
  have hFU : u.gradToHilbertVectorL2 =ᵐ[Homogenization.volumeMeasureOn (Homogenization.openCubeSet (Homogenization.originCube d (M : ℤ)))]
      fun x => Homogenization.HilbertVec.ofVec (u.grad x) := by
    filter_upwards [Homogenization.H1Function.coeFn_gradToHilbertVectorL2 u] with x hx
    simpa only [Homogenization.hilbertifyVecField] using hx
  have hpairG : ∫ x in Homogenization.openCubeSet (Homogenization.originCube d (M : ℤ)),
      Homogenization.vecDot (gradHatW (x +ᵥ ω)) (φ.toH1Function.grad x) =
      inner ℝ (hGslice.toLp (fun x => Homogenization.HilbertVec.ofVec (gradHatW (x +ᵥ ω))))
        φ.toH1Function.gradToHilbertVectorL2 :=
    integral_vecDot_eq_inner_of_ae_eq (MeasureTheory.MemLp.coeFn_toLp hGslice) φ.toH1Function
  have hpairF : ∫ x in Homogenization.openCubeSet (Homogenization.originCube d (M : ℤ)),
      Homogenization.vecDot (F (x +ᵥ ω) 0) (φ.toH1Function.grad x) =
      inner ℝ (hFslice.toLp (fun x => Homogenization.HilbertVec.ofVec (F (x +ᵥ ω) 0)))
        φ.toH1Function.gradToHilbertVectorL2 :=
    integral_vecDot_eq_inner_of_ae_eq (MeasureTheory.MemLp.coeFn_toLp hFslice) φ.toH1Function
  have hanchorClass : inner ℝ (hGslice.toLp (fun x => Homogenization.HilbertVec.ofVec (gradHatW (x +ᵥ ω))) +
      hFslice.toLp (fun x => Homogenization.HilbertVec.ofVec (F (x +ᵥ ω) 0)))
      φ.toH1Function.gradToHilbertVectorL2 = 0 := by
    rw [← integral_vecDot_eq_inner_of_ae_eq
      (f := hGslice.toLp (fun x => Homogenization.HilbertVec.ofVec (gradHatW (x +ᵥ ω))) +
        hFslice.toLp (fun x => Homogenization.HilbertVec.ofVec (F (x +ᵥ ω) 0)))
      (G := fun x => realizationAbstract_anchorStationaryField gradHatW F (x +ᵥ ω))
      (by
        filter_upwards [MeasureTheory.Lp.coeFn_add
            (hGslice.toLp (fun x => Homogenization.HilbertVec.ofVec (gradHatW (x +ᵥ ω))))
            (hFslice.toLp (fun x => Homogenization.HilbertVec.ofVec (F (x +ᵥ ω) 0))),
          MeasureTheory.MemLp.coeFn_toLp hGslice, MeasureTheory.MemLp.coeFn_toLp hFslice] with x h0 h1 h2
        rw [h0, Pi.add_apply, h1, h2]
        exact (realizationAbstract_ofVec_anchorStationaryField gradHatW F (x +ᵥ ω)).symm)
      φ.toH1Function]
    exact hanchor φ
  have hsum : inner ℝ (hGslice.toLp (fun x => Homogenization.HilbertVec.ofVec (gradHatW (x +ᵥ ω))))
        φ.toH1Function.gradToHilbertVectorL2 +
      inner ℝ (hFslice.toLp (fun x => Homogenization.HilbertVec.ofVec (F (x +ᵥ ω) 0)))
        φ.toH1Function.gradToHilbertVectorL2 = 0 := by
    rw [← inner_add_left]
    exact hanchorClass
  have hu : ∫ x in Homogenization.openCubeSet (Homogenization.originCube d (M : ℤ)),
      Homogenization.vecDot (u.grad x) (φ.toH1Function.grad x) =
      inner ℝ (hGslice.toLp (fun x => Homogenization.HilbertVec.ofVec (gradHatW (x +ᵥ ω))))
        φ.toH1Function.gradToHilbertVectorL2 := by
    rw [integral_vecDot_eq_inner_of_ae_eq hFU φ.toH1Function, hGc]
  have hFω : ∫ x in Homogenization.openCubeSet (Homogenization.originCube d (M : ℤ)),
      Homogenization.vecDot (F ω x) (φ.toH1Function.grad x) =
      inner ℝ (hFslice.toLp (fun x => Homogenization.HilbertVec.ofVec (F (x +ᵥ ω) 0)))
        φ.toH1Function.gradToHilbertVectorL2 := by
    rw [← hpairF]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with x
    have hx := hcocycle x 0
    rw [zero_add] at hx
    rw [hx]
  rw [hu, hFω]
  exact eq_neg_of_add_eq_zero_left hsum
theorem realizationAbstract_exists_realization_of_anchorPairing  (M : ℕ) {F : Ω → Homogenization.Vec d → Homogenization.Vec d} {gradHatW : Ω → Homogenization.Vec d} (hcocycle : ∀ (ω : Ω) (x y : Homogenization.Vec d), F (x +ᵥ ω) y = F ω (y +
    x)) (hFmemLp : MeasureTheory.MemLp (fun ω : Ω => Homogenization.HilbertVec.ofVec (F ω 0)) 2 μ) (hG : MeasureTheory.MemLp (fun ω : Ω => Homogenization.HilbertVec.ofVec (gradHatW ω)) 2 μ) (hproj : hG.toLp (fun ω : Ω => Homogenization.HilbertVec.ofVec
    (gradHatW ω)) = -stationaryPotentialProjection (μ := μ) (d := d) (hFmemLp.toLp (fun ω : Ω => Homogenization.HilbertVec.ofVec (F ω 0)))) (hpair : ∀ᵐ ω ∂μ, ∀ φ : Homogenization.H10Function (Homogenization.openCubeSet
    (Homogenization.originCube d (M : ℤ))), ∫ x in Homogenization.openCubeSet (Homogenization.originCube d (M : ℤ)), Homogenization.vecDot (realizationAbstract_anchorStationaryField gradHatW F (x +ᵥ ω)) (φ.toH1Function.grad x) = 0) : ∃ uReal
    : Ω → Homogenization.H1Function (Homogenization.openCubeSet (Homogenization.originCube d (M : ℤ))), (∀ᵐ ω ∂μ, (uReal ω).grad =ᵐ[Homogenization.volumeMeasureOn (Homogenization.openCubeSet (Homogenization.originCube d (M : ℤ)))] fun x => gradHatW (x +ᵥ ω)) ∧ (∀ᵐ ω ∂μ,
    ∀ φ : Homogenization.H10Function (Homogenization.openCubeSet (Homogenization.originCube d (M : ℤ))), ∫ x in Homogenization.openCubeSet (Homogenization.originCube d (M : ℤ)), Homogenization.vecDot ((uReal ω).grad x) (φ.toH1Function.grad x) = -∫ x in Homogenization.openCubeSet
    (Homogenization.originCube d (M : ℤ)), Homogenization.vecDot (F ω x) (φ.toH1Function.grad x)) := by
  classical
  obtain ⟨W, hWm, hWmem, hWtoLp⟩ := realizationAbstract_exists_measurable_representative_of_vectorL2 (μ := μ)
    (hG.toLp (fun ω : Ω => Homogenization.HilbertVec.ofVec (gradHatW ω)))
  have hW1 : (hWmem.toLp (fun ω => Homogenization.HilbertVec.ofVec (W ω)) : Ω → Homogenization.HilbertVec d)
      =ᵐ[μ] fun ω => Homogenization.HilbertVec.ofVec (W ω) := MeasureTheory.MemLp.coeFn_toLp hWmem
  have hW2 : (hWmem.toLp (fun ω => Homogenization.HilbertVec.ofVec (W ω)) : Ω → Homogenization.HilbertVec d)
      =ᵐ[μ] fun ω => Homogenization.HilbertVec.ofVec (gradHatW ω) := by
    rw [hWtoLp]
    exact MeasureTheory.MemLp.coeFn_toLp hG
  have hWae : W =ᵐ[μ] gradHatW :=
    (hW1.symm.trans hW2).mono fun ω hω => by
      have h := congrArg Homogenization.HilbertVec.toVec hω
      simpa only [Homogenization.HilbertVec.toVec_ofVec] using h
  obtain ⟨G₀, hG₀m, hG₀mem, hG₀toLp⟩ := realizationAbstract_exists_measurable_representative_of_vectorL2 (μ := μ)
    (hFmemLp.toLp (fun ω : Ω => Homogenization.HilbertVec.ofVec (F ω 0)))
  have hG₀1 : (hG₀mem.toLp (fun ω => Homogenization.HilbertVec.ofVec (G₀ ω)) : Ω → Homogenization.HilbertVec d)
      =ᵐ[μ] fun ω => Homogenization.HilbertVec.ofVec (G₀ ω) := MeasureTheory.MemLp.coeFn_toLp hG₀mem
  have hG₀2 : (hG₀mem.toLp (fun ω => Homogenization.HilbertVec.ofVec (G₀ ω)) : Ω → Homogenization.HilbertVec d)
      =ᵐ[μ] fun ω => Homogenization.HilbertVec.ofVec (F ω 0) := by
    rw [hG₀toLp]
    exact MeasureTheory.MemLp.coeFn_toLp hFmemLp
  have hG₀ae : G₀ =ᵐ[μ] (fun ω : Ω => F ω 0) :=
    (hG₀1.symm.trans hG₀2).mono fun ω hω => by
      have h := congrArg Homogenization.HilbertVec.toVec hω
      simpa only [Homogenization.HilbertVec.toVec_ofVec] using h
  have hWslice := realizationAbstract_ae_memLp_slice_openCube_vec (μ := μ) (Homogenization.originCube d (M : ℤ)) hWm hWmem
  have hG₀slice := realizationAbstract_ae_memLp_slice_openCube_vec (μ := μ) (Homogenization.originCube d (M : ℤ)) hG₀m hG₀mem
  have hWsliceEq := realizationAbstract_ae_slice_eq_of_ae_eq (μ := μ) hWae (Homogenization.originCube d (M : ℤ))
  have hG₀sliceEq := realizationAbstract_ae_slice_eq_of_ae_eq (μ := μ) hG₀ae (Homogenization.originCube d (M : ℤ))
  have hGslice : ∀ᵐ ω ∂μ, MeasureTheory.MemLp
      (fun x => Homogenization.HilbertVec.ofVec (gradHatW (x +ᵥ ω))) 2
      (Homogenization.volumeMeasureOn (Homogenization.openCubeSet (Homogenization.originCube d (M : ℤ)))) := by
    filter_upwards [hWslice, hWsliceEq] with ω h1 h2
    exact h1.ae_eq (h2.mono fun x hx => congrArg Homogenization.HilbertVec.ofVec hx)
  have hFslice : ∀ᵐ ω ∂μ, MeasureTheory.MemLp
      (fun x => Homogenization.HilbertVec.ofVec (F (x +ᵥ ω) 0)) 2
      (Homogenization.volumeMeasureOn (Homogenization.openCubeSet (Homogenization.originCube d (M : ℤ)))) := by
    filter_upwards [hG₀slice, hG₀sliceEq] with ω h1 h2
    exact h1.ae_eq (h2.mono fun x hx => congrArg Homogenization.HilbertVec.ofVec hx)
  obtain ⟨uReal, huReal⟩ :
      ∃ uReal : Ω → Homogenization.H1Function (Homogenization.openCubeSet (Homogenization.originCube d (M : ℤ))),
        ∀ᵐ ω ∂μ,
          (uReal ω).grad =ᵐ[Homogenization.volumeMeasureOn (Homogenization.openCubeSet (Homogenization.originCube d (M : ℤ)))]
            fun x => gradHatW (x +ᵥ ω) := by
    have hex := realizationAbstract_exists_h1_realization_of_eq_neg_stationaryPotentialProjection (μ := μ) M
      hFmemLp hG hproj
    let v : Ω → Homogenization.H1Function (Homogenization.openCubeSet (Homogenization.originCube d (M : ℤ))) := fun ω =>
      if h : ∃ u : Homogenization.H1Function (Homogenization.openCubeSet (Homogenization.originCube d (M : ℤ))),
          u.grad =ᵐ[Homogenization.volumeMeasureOn (Homogenization.openCubeSet (Homogenization.originCube d (M : ℤ)))]
            fun x => gradHatW (x +ᵥ ω)
        then h.choose else 0
    refine ⟨v, ?_⟩
    filter_upwards [hex] with ω hω
    rw [show v ω = hω.choose from dite_eq_left hω]
    exact hω.choose_spec
  refine ⟨uReal, huReal, ?_⟩
  filter_upwards [huReal, hpair, hGslice, hFslice] with ω hωu hωpair hωG hωF
  exact realizationAbstract_weakEquation_of_anchorPairing_eq_zero M hωu (hcocycle ω) hωG hωF hωpair
omit [MeasureTheory.IsProbabilityMeasure μ] in
theorem realizationAbstract_divFreeStep_ae_all  (hstep : ∀ (G : Ω → Homogenization.Vec d) (hG : MeasureTheory.MemLp (fun ω => Homogenization.HilbertVec.ofVec (G ω)) 2 μ), hG.toLp (fun ω => Homogenization.HilbertVec.ofVec (G ω)) ∈
    stationarySolenoidalSubspace (μ := μ) (d := d) → ∀ θ : Homogenization.Vec d → ℝ, ContDiff ℝ 1 θ → HasCompactSupport θ → ∀ᵐ ω ∂μ, ∫ x, Homogenization.vecDot (G (x +ᵥ ω)) (Homogenization.euclideanGradient θ x) = 0) {G : Ω →
    Homogenization.Vec d} (hG : MeasureTheory.MemLp (fun ω => Homogenization.HilbertVec.ofVec (G ω)) 2 μ) (hGsol : hG.toLp (fun ω => Homogenization.HilbertVec.ofVec (G ω)) ∈ stationarySolenoidalSubspace (μ := μ) (d := d)) (θs : ℕ → Homogenization.Vec d →
    ℝ) (hθ : ∀ j, ContDiff ℝ 1 (θs j)) (hθs : ∀ j, HasCompactSupport (θs j)) : ∀ᵐ ω ∂μ, ∀ j, ∫ x, Homogenization.vecDot (G (x +ᵥ ω)) (Homogenization.euclideanGradient (θs j) x) = 0 :=
  MeasureTheory.ae_all_iff.2 fun j => hstep G hG hGsol (θs j) (hθ j) (hθs j)
omit [MeasureTheory.IsProbabilityMeasure μ] [MeasurableSpace Ω] [MeasurableVAdd₂ (Homogenization.Vec d) Ω] in
theorem realizationAbstract_pairing_zero_of_family_zero {Q : Homogenization.TriadicCube d} {θs : ℕ → Homogenization.Vec d → ℝ} (hθ : ∀ j, ContDiff ℝ 1 (θs j) ∧ HasCompactSupport (θs
    j) ∧ tsupport (θs j) ⊆ Homogenization.openCubeSet Q) (hdense : ∀ φ : Homogenization.H10Function (Homogenization.openCubeSet Q), φ.toH1Function.gradToHilbertVectorL2 ∈ closure
    (Set.range fun j => (Homogenization.H1Function.ofContDiff (Homogenization.isOpen_openCubeSet Q) (hθ j).1 (hθ j).2.1).gradToHilbertVectorL2)) {W : Ω → Homogenization.Vec d} {ω :
    Ω} (hWsl : MeasureTheory.MemLp (fun x => Homogenization.HilbertVec.ofVec (W (x +ᵥ ω))) 2 (Homogenization.volumeMeasureOn (Homogenization.openCubeSet Q))) (hzero : ∀ j, ∫ x,
    Homogenization.vecDot (W (x +ᵥ ω)) (Homogenization.euclideanGradient (θs j) x) = 0) : ∀ φ : Homogenization.H10Function (Homogenization.openCubeSet Q), ∫ x in
    Homogenization.openCubeSet Q, Homogenization.vecDot (W (x +ᵥ ω)) (φ.toH1Function.grad x) = 0 := by
  set cls := hWsl.toLp (fun x => Homogenization.HilbertVec.ofVec (W (x +ᵥ ω))) with hcls
  set Gcls : ℕ → Homogenization.HilbertVectorL2 (Homogenization.openCubeSet Q) := fun j =>
    (Homogenization.H1Function.ofContDiff (Homogenization.isOpen_openCubeSet Q) (hθ j).1 (hθ j).2.1).gradToHilbertVectorL2
    with hGcls
  have hinner : ∀ j, inner ℝ cls (Gcls j) = 0 := by
    intro j
    rw [hcls, hGcls]
    rw [← integral_vecDot_eq_inner_of_ae_eq (MeasureTheory.MemLp.coeFn_toLp hWsl)
      (Homogenization.H1Function.ofContDiff (Homogenization.isOpen_openCubeSet Q) (hθ j).1 (hθ j).2.1)]
    change (∫ x in Homogenization.openCubeSet Q, Homogenization.vecDot (W (x +ᵥ ω)) (Homogenization.euclideanGradient (θs j) x)) = 0
    rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [Homogenization.euclideanGradient_eq_zero_of_notMem_tsupport
        (fun h => hx ((hθ j).2.2 h)), Homogenization.vecDot_zero_right])]
    exact hzero j
  have hclosed : IsClosed {v : Homogenization.HilbertVectorL2 (Homogenization.openCubeSet Q) | inner ℝ cls v = 0} :=
    isClosed_eq (by fun_prop) continuous_const
  have hsub : Set.range Gcls ⊆
      {v : Homogenization.HilbertVectorL2 (Homogenization.openCubeSet Q) | inner ℝ cls v = 0} := by
    rintro v ⟨j, rfl⟩
    exact hinner j
  intro φ
  have hmem : φ.toH1Function.gradToHilbertVectorL2 ∈ closure (Set.range Gcls) := by
    rw [hGcls]
    exact hdense φ
  have hzeroφ : inner ℝ cls φ.toH1Function.gradToHilbertVectorL2 = 0 :=
    closure_minimal hsub hclosed hmem
  rw [integral_vecDot_eq_inner_of_ae_eq (MeasureTheory.MemLp.coeFn_toLp hWsl) φ.toH1Function, ← hcls]
  exact hzeroφ
theorem realizationAbstract_hpair_of_divFreeStep  (M : ℕ) {F : Ω → Homogenization.Vec d → Homogenization.Vec d} {gradHatW : Ω → Homogenization.Vec d} (hstep : ∀ (G : Ω → Homogenization.Vec d) (hG : MeasureTheory.MemLp (fun ω => Homogenization.HilbertVec.ofVec (G ω)) 2
    μ), hG.toLp (fun ω => Homogenization.HilbertVec.ofVec (G ω)) ∈ stationarySolenoidalSubspace (μ := μ) (d := d) → ∀ θ : Homogenization.Vec d → ℝ, ContDiff ℝ 1 θ → HasCompactSupport θ → ∀ᵐ ω ∂μ, ∫ x, Homogenization.vecDot (G
    (x +ᵥ ω)) (Homogenization.euclideanGradient θ x) = 0) (hdense : CountableTestGradientsDense (Homogenization.originCube d (M : ℤ))) (hFmemLp : MeasureTheory.MemLp (fun ω : Ω => Homogenization.HilbertVec.ofVec (F ω 0)) 2 μ) (hGmemLp :
    MeasureTheory.MemLp (fun ω : Ω => Homogenization.HilbertVec.ofVec (gradHatW ω)) 2 μ) (hproj : hGmemLp.toLp (fun ω : Ω => Homogenization.HilbertVec.ofVec (gradHatW ω)) = -stationaryPotentialProjection (μ := μ) (d := d)
    (hFmemLp.toLp (fun ω : Ω => Homogenization.HilbertVec.ofVec (F ω 0)))) : ∀ᵐ ω ∂μ, ∀ φ : Homogenization.H10Function (Homogenization.openCubeSet (Homogenization.originCube d (M : ℤ))), ∫ x in Homogenization.openCubeSet (Homogenization.originCube d (M : ℤ)), Homogenization.vecDot
    (realizationAbstract_anchorStationaryField gradHatW F (x +ᵥ ω)) (φ.toH1Function.grad x) = 0 := by
  classical
  obtain ⟨θs, hθ, hdense'⟩ := hdense
  obtain ⟨W, hWm, hWmem, hWtoLp⟩ := realizationAbstract_exists_measurable_representative_of_vectorL2 (μ := μ)
    ((realizationAbstract_anchorStationaryField_memLp (μ := μ) hFmemLp hGmemLp).toLp
      (fun ω : Ω => Homogenization.HilbertVec.ofVec (realizationAbstract_anchorStationaryField gradHatW F ω)))
  have hWsol : hWmem.toLp (fun ω : Ω => Homogenization.HilbertVec.ofVec (W ω)) ∈
      stationarySolenoidalSubspace (μ := μ) (d := d) := by
    rw [hWtoLp]
    exact realizationAbstract_anchorStationaryField_toLp_mem_stationarySolenoidalSubspace (μ := μ) hproj
  have hstep_all : ∀ᵐ ω ∂μ, ∀ j,
      ∫ x, Homogenization.vecDot (W (x +ᵥ ω)) (Homogenization.euclideanGradient (θs j) x) = 0 :=
    realizationAbstract_divFreeStep_ae_all (μ := μ) hstep hWmem hWsol θs
      (fun j => (hθ j).1) (fun j => (hθ j).2.1)
  have hWae : W =ᵐ[μ] realizationAbstract_anchorStationaryField gradHatW F := by
    have h1 : (hWmem.toLp (fun ω : Ω => Homogenization.HilbertVec.ofVec (W ω)) :
        Ω → Homogenization.HilbertVec d) =ᵐ[μ] fun ω => Homogenization.HilbertVec.ofVec (W ω) :=
      MeasureTheory.MemLp.coeFn_toLp hWmem
    have h2 : (hWmem.toLp (fun ω : Ω => Homogenization.HilbertVec.ofVec (W ω)) :
        Ω → Homogenization.HilbertVec d) =ᵐ[μ]
        fun ω => Homogenization.HilbertVec.ofVec (realizationAbstract_anchorStationaryField gradHatW F ω) := by
      rw [hWtoLp]
      exact MeasureTheory.MemLp.coeFn_toLp (realizationAbstract_anchorStationaryField_memLp (μ := μ) hFmemLp hGmemLp)
    exact (h1.symm.trans h2).mono fun _ hω => by
      have h := congrArg Homogenization.HilbertVec.toVec hω
      simpa only [Homogenization.HilbertVec.toVec_ofVec] using h
  have hWslice := realizationAbstract_ae_memLp_slice_openCube_vec (μ := μ) (Homogenization.originCube d (M : ℤ)) hWm hWmem
  have hsliceEq := realizationAbstract_ae_slice_eq_of_ae_eq (μ := μ) hWae (Homogenization.originCube d (M : ℤ))
  filter_upwards [hstep_all, hWslice, hsliceEq] with ω hωzero hωsl hωeq
  have hkey : ∀ φ : Homogenization.H10Function (Homogenization.openCubeSet (Homogenization.originCube d (M : ℤ))),
      ∫ x in Homogenization.openCubeSet (Homogenization.originCube d (M : ℤ)),
        Homogenization.vecDot (W (x +ᵥ ω)) (φ.toH1Function.grad x) = 0 :=
    realizationAbstract_pairing_zero_of_family_zero (Q := Homogenization.originCube d (M : ℤ)) hθ hdense' hωsl hωzero
  intro φ
  have hcongr : (fun x => Homogenization.vecDot (W (x +ᵥ ω)) (φ.toH1Function.grad x))
      =ᵐ[Homogenization.volumeMeasureOn (Homogenization.openCubeSet (Homogenization.originCube d (M : ℤ)))]
      fun x => Homogenization.vecDot (realizationAbstract_anchorStationaryField gradHatW F (x +ᵥ ω))
        (φ.toH1Function.grad x) := by
    filter_upwards [hωeq] with x hx
    rw [hx]
  rw [← MeasureTheory.integral_congr_ae hcongr]
  exact hkey φ
theorem realizationAbstract_exists_realization_of_divFreeStep  (M : ℕ) {F : Ω → Homogenization.Vec d → Homogenization.Vec d} {gradHatW : Ω → Homogenization.Vec d} (hstep : ∀ (G : Ω → Homogenization.Vec d) (hG : MeasureTheory.MemLp (fun ω =>
    Homogenization.HilbertVec.ofVec (G ω)) 2 μ), hG.toLp (fun ω => Homogenization.HilbertVec.ofVec (G ω)) ∈ stationarySolenoidalSubspace (μ := μ) (d := d) → ∀ θ : Homogenization.Vec d → ℝ, ContDiff ℝ 1 θ → HasCompactSupport θ
    → ∀ᵐ ω ∂μ, ∫ x, Homogenization.vecDot (G (x +ᵥ ω)) (Homogenization.euclideanGradient θ x) = 0) (hdense : CountableTestGradientsDense (Homogenization.originCube d (M : ℤ))) (hcocycle : ∀ (ω : Ω) (x y : Homogenization.Vec d), F (x +ᵥ ω) y
    = F ω (y + x)) (hFmemLp : MeasureTheory.MemLp (fun ω : Ω => Homogenization.HilbertVec.ofVec (F ω 0)) 2 μ) (hGmemLp : MeasureTheory.MemLp (fun ω : Ω => Homogenization.HilbertVec.ofVec (gradHatW ω)) 2 μ) (hproj : hGmemLp.toLp (fun ω : Ω
    => Homogenization.HilbertVec.ofVec (gradHatW ω)) = -stationaryPotentialProjection (μ := μ) (d := d) (hFmemLp.toLp (fun ω : Ω => Homogenization.HilbertVec.ofVec (F ω 0)))) : ∃ uReal : Ω → Homogenization.H1Function
    (Homogenization.openCubeSet (Homogenization.originCube d (M : ℤ))), (∀ᵐ ω ∂μ, (uReal ω).grad =ᵐ[Homogenization.volumeMeasureOn (Homogenization.openCubeSet (Homogenization.originCube d (M : ℤ)))] fun x => gradHatW (x +ᵥ ω)) ∧ (∀ᵐ ω ∂μ, ∀ φ : Homogenization.H10Function
    (Homogenization.openCubeSet (Homogenization.originCube d (M : ℤ))), ∫ x in Homogenization.openCubeSet (Homogenization.originCube d (M : ℤ)), Homogenization.vecDot ((uReal ω).grad x) (φ.toH1Function.grad x) = -∫ x in Homogenization.openCubeSet (Homogenization.originCube d (M : ℤ)),
    Homogenization.vecDot (F ω x) (φ.toH1Function.grad x)) :=
  realizationAbstract_exists_realization_of_anchorPairing (μ := μ) M hcocycle hFmemLp hGmemLp hproj
    (realizationAbstract_hpair_of_divFreeStep (μ := μ) M hstep hdense hFmemLp hGmemLp hproj)
end SuperdiffusionCLT.Probability.Stationary
end
