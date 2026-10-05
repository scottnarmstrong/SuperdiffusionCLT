/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Probability.HonestSliceStep
public import SuperdiffusionCLT.Probability.StationaryRealizationLimit

/-!
# Assembling the honest-slice step from its two halves

This module proves `honestSlice` at the concrete carrier `Ω := ShellSeq d`,
`μ := P.toMeasure`: for a stationary scalar field `φ` with full strong horizontal
gradient `F`, the sample field `x ↦ F (x +ᵥ ω)` is the weak gradient of the
sample field `x ↦ φ (x +ᵥ ω)` on the cube `U = openCubeSet (originCube d M)`,
for almost every `ω`.

The two halves it consumes are

* the deterministic half `Probability/HonestSliceStep.lean`, which converts a
  per-sample difference-quotient convergence against a test function into the
  weak-derivative identity, and
* the probabilistic half `Probability/StationaryRealizationLimit.lean`, whose
  `exists_strictMono_ae_tendsto_slice_lintegral` extracts a single subsequence
  along which the *spatial* slices converge in `L²` on the cube for a.e. `ω`.

## The test-function subtlety, and why it is discharged here

The a.e.-`ω` set produced by the subsequence extraction is a statement about the
full `L²` deficit `∫⁻ x, ‖f n (x +ᵥ ω) - g (x +ᵥ ω)‖ₑ ^ 2`, *not* about a single
test function: the subsequence and the null set depend only on the pair `(f n)`,
`g`, never on `ψ`.  Pairing against a test function `ψ` is done afterwards, by
Cauchy–Schwarz on the cube, with the bound

`‖∫ x in U, (f n (x +ᵥ ω) - g (x +ᵥ ω)) * ψ x‖ ≤
   (∫⁻ x, ‖f n (x +ᵥ ω) - g (x +ᵥ ω)‖ₑ ^ 2) ^ (1/2) * (∫ x, ‖ψ x‖ ^ 2) ^ (1/2)`,

so **no countable family of test functions is needed**: the intersection of
countably many full-measure sets never arises, and every test function is
handled by the same null set.  This is the reason `HasWeakPartialDerivOn` (all
smooth compactly supported test functions) is reached directly rather than
through density.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Homogenization
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section3.Terms
open scoped ENNReal Topology

noncomputable section

namespace SuperdiffusionCLT.Probability.Stationary

variable {d : ℕ}

/-- **Undoing a positive normalisation of the measure.**  If the `ℝ≥0∞`-valued
integrals against the normalised measure `c • ν` tend to zero, and the constant
`c` is nonzero and finite, then the integrals against `ν` themselves tend to
zero.  This is what turns the cube-normalised `L²` deficit produced by
`exists_strictMono_ae_tendsto_slice_lintegral` into the deficit with respect to
plain volume on the cube. -/
theorem tendsto_lintegral_of_tendsto_smul_measure {α : Type*} [MeasurableSpace α]
    {ν : Measure α} {F : ℕ → α → ℝ≥0∞} (c : ℝ≥0∞) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (h : Filter.Tendsto (fun n => ∫⁻ x, F n x ∂(c • ν)) Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun n => ∫⁻ x, F n x ∂ν) Filter.atTop (𝓝 0) := by
  have hsm : ∀ n, ∫⁻ x, F n x ∂(c • ν) = c * ∫⁻ x, F n x ∂ν := fun n =>
    MeasureTheory.lintegral_smul_measure c (F n)
  have hε : ∀ ε > 0, ∀ᶠ n in Filter.atTop, c * ∫⁻ x, F n x ∂ν ≤ ε := by
    intro ε hε
    simpa only [hsm] using (ENNReal.tendsto_nhds_zero.mp h) ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hεpos
  by_cases htop : ε = ⊤
  · subst htop
    exact Filter.Eventually.of_forall fun n => le_top
  · filter_upwards [hε (c * ε) (ENNReal.mul_pos hc0 hεpos.ne')] with n hn
    calc ∫⁻ x, F n x ∂ν = c⁻¹ * (c * ∫⁻ x, F n x ∂ν) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]
      _ ≤ c⁻¹ * (c * ε) := mul_le_mul_right hn c⁻¹
      _ = ε := by rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]

/-- **`L²`-convergence is convergence of the realised squared deficit.**  This
is the step that lets the derivative supplied by `HasHorizontalGradient` be fed
to the a.e. slice extraction, whose input is the `ℝ≥0∞`-valued lintegral of the
squared deficit. -/
theorem tendsto_lintegral_enorm_sq_of_tendsto_Lp {ι : Type*} {l : Filter ι}
    {E : Type*} [NormedAddCommGroup E] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {u : ι → Lp E 2 μ} {v : Lp E 2 μ}
    (h : Filter.Tendsto u l (𝓝 v)) :
    Filter.Tendsto (fun n => ∫⁻ ω, ‖(u n) ω - v ω‖ₑ ^ (2 : ℝ) ∂μ) l (𝓝 0) := by
  have h1 : Filter.Tendsto (fun n => u n - v) l (𝓝 0) := by
    simpa using h.sub (tendsto_const_nhds : Filter.Tendsto (fun _ : ι => v) l (𝓝 v))
  have h2 : Filter.Tendsto (fun n => ‖u n - v‖) l (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mp h1
  have h3 : Filter.Tendsto (fun n => (eLpNorm (u n - v) 2 μ).toReal) l (𝓝 0) := by
    simpa only [Lp.norm_def] using h2
  have h4 : Filter.Tendsto (fun n => eLpNorm (u n - v) 2 μ) l (𝓝 0) :=
    (ENNReal.tendsto_toReal_iff (fun n => ne_of_lt (Lp.memLp (u n - v)).eLpNorm_lt_top)
      (by simp : (0 : ℝ≥0∞) ≠ ⊤)).mp h3
  have h5 : Filter.Tendsto (fun n => (∫⁻ ω, ‖(u n - v) ω‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ))
      l (𝓝 0) := by
    refine Filter.Tendsto.congr (fun n => ?_) h4
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := μ) (f := (↑↑(u n - v) : Ω → E))
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      (Lp.memLp (u n - v)).aestronglyMeasurable]
    simp only [ENNReal.toReal_ofNat]
  have h6 : Filter.Tendsto (fun n => ((∫⁻ ω, ‖(u n - v) ω‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ))
      ^ (2 : ℝ)) l (𝓝 (0 ^ (2 : ℝ))) :=
    ENNReal.continuous_rpow_const.continuousAt.tendsto.comp h5
  rw [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)] at h6
  have hD : Filter.Tendsto (fun n => ∫⁻ ω, ‖(u n - v) ω‖ₑ ^ (2 : ℝ) ∂μ) l (𝓝 0) :=
    Filter.Tendsto.congr (fun n =>
      (ENNReal.rpow_mul (x := ∫⁻ ω, ‖(u n - v) ω‖ₑ ^ (2 : ℝ) ∂μ)
        (y := (1 / 2 : ℝ)) 2).symm.trans
        (by rw [one_div, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), ENNReal.rpow_one])) h6
  refine Filter.Tendsto.congr (fun n => ?_) hD
  exact MeasureTheory.lintegral_congr_ae
    ((MeasureTheory.Lp.coeFn_sub (u n) v).mono fun ω hω => by simp only [hω, Pi.sub_apply])

/-- **From an `L²` deficit to a paired convergence.**  If the `L²` deficit of
`f n` against `g` on `U` tends to zero, then pairing against any fixed `L²(U)`
test function `ψ` converges.  This is the Cauchy–Schwarz step: it is performed
*after* the a.e. statement, so it never refines the null set. -/
theorem tendsto_setIntegral_mul_of_tendsto_deficit {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict U)]
    {f : ℕ → Vec d → ℝ} {g ψ : Vec d → ℝ}
    (hf : ∀ n, MemLp (f n) 2 (MeasureTheory.volume.restrict U))
    (hg : MemLp g 2 (MeasureTheory.volume.restrict U))
    (hψ : MemLp ψ 2 (MeasureTheory.volume.restrict U))
    (hconv : Filter.Tendsto (fun n => ∫⁻ x, ‖f n x - g x‖ₑ ^ (2 : ℝ)
      ∂(MeasureTheory.volume.restrict U)) Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun n => ∫ x in U, f n x * ψ x) Filter.atTop
      (𝓝 (∫ x in U, g x * ψ x)) := by
  set ν : MeasureTheory.Measure (Vec d) := MeasureTheory.volume.restrict U with hν
  set D : ℕ → ℝ≥0∞ := fun n => ∫⁻ x, ‖f n x - g x‖ₑ ^ (2 : ℝ) ∂ν with hD
  have hDfin : ∀ n, D n ≠ ⊤ := fun n =>
    ne_of_lt (MeasureTheory.lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := 2)
      (by norm_num) (by norm_num) ((hf n).sub hg).eLpNorm_lt_top)
  have hDreal : Filter.Tendsto (fun n => (D n).toReal) Filter.atTop (𝓝 0) := by
    simpa only [ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal_iff hDfin (by simp : (0 : ℝ≥0∞) ≠ ⊤)).mpr hconv
  have hsqrt : Filter.Tendsto (fun n => (D n).toReal ^ (1 / 2 : ℝ)) Filter.atTop (𝓝 0) := by
    have := (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 2)).continuousAt.tendsto.comp
      hDreal
    rw [Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0)] at this
    exact this
  have hDbochner : ∀ n, (∫ x, ‖f n x - g x‖ ^ (2 : ℝ) ∂ν) = (D n).toReal := by
    intro n
    rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (μ := ν) (f := fun x => ‖f n x - g x‖ ^ (2 : ℝ))
      (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) _)
      (by
        simp only [Real.rpow_two]
        exact (((hf n).sub hg).aestronglyMeasurable.norm.aemeasurable.pow_const 2).aestronglyMeasurable)]
    refine congrArg ENNReal.toReal (MeasureTheory.lintegral_congr fun x => ?_)
    rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
      Real.enorm_eq_ofReal_abs, Real.norm_eq_abs]
  have hHolder : ∀ n, ∫ x, ‖f n x - g x‖ * ‖ψ x‖ ∂ν ≤
      (D n).toReal ^ (1 / 2 : ℝ) * (∫ x, ‖ψ x‖ ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) := by
    intro n
    have hb := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq (μ := ν)
      (f := fun x => f n x - g x) (g := ψ) (p := 2) (q := 2) Real.HolderConjugate.two_two
      (by rw [show ENNReal.ofReal 2 = 2 by simp]; exact (hf n).sub hg) (by simpa using hψ)
    simpa only [hDbochner n, one_div] using hb
  have hbound : ∀ n, ‖∫ x in U, (f n x - g x) * ψ x‖ ≤
      (D n).toReal ^ (1 / 2 : ℝ) * (∫ x, ‖ψ x‖ ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) := by
    intro n
    calc ‖∫ x in U, (f n x - g x) * ψ x‖
        = ‖∫ x, (f n x * ψ x - g x * ψ x) ∂ν‖ := by
          congr 1
          exact integral_congr_ae (Filter.Eventually.of_forall fun x => sub_mul _ _ _)
      _ ≤ ∫ x, ‖f n x * ψ x - g x * ψ x‖ ∂ν :=
          MeasureTheory.norm_integral_le_integral_norm (μ := ν) _
      _ = ∫ x, ‖f n x - g x‖ * ‖ψ x‖ ∂ν :=
          integral_congr_ae (Filter.Eventually.of_forall fun x => by
            show ‖f n x * ψ x - g x * ψ x‖ = ‖f n x - g x‖ * ‖ψ x‖
            rw [← sub_mul, norm_mul])
      _ ≤ _ := hHolder n
  have hsq : Filter.Tendsto (fun n => ‖∫ x in U, (f n x - g x) * ψ x‖) Filter.atTop (𝓝 0) :=
    squeeze_zero (fun n => norm_nonneg _) hbound
      (by simpa using hsqrt.mul_const ((∫ x, ‖ψ x‖ ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ)))
  have hzero : Filter.Tendsto (fun n => ∫ x in U, (f n x - g x) * ψ x) Filter.atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hsq
  have hsub : Filter.Tendsto
      (fun n => (∫ x in U, f n x * ψ x) - (∫ x in U, g x * ψ x)) Filter.atTop (𝓝 0) := by
    refine Filter.Tendsto.congr (fun n => ?_) hzero
    calc ∫ x in U, (f n x - g x) * ψ x
        = ∫ x, (f n x * ψ x - g x * ψ x) ∂ν :=
          integral_congr_ae (Filter.Eventually.of_forall fun x => sub_mul _ _ _)
      _ = ∫ x, (fun y => f n y * ψ y) x - (fun y => g y * ψ y) x ∂ν := rfl
      _ = ∫ x, (fun y => f n y * ψ y) x ∂ν - ∫ x, (fun y => g y * ψ y) x ∂ν :=
          MeasureTheory.integral_sub ((hf n).integrable_mul hψ) (hg.integrable_mul hψ)
      _ = (∫ x in U, f n x * ψ x) - (∫ x in U, g x * ψ x) := rfl
  have hmain : Filter.Tendsto
      (fun n => ((∫ x in U, f n x * ψ x) - (∫ x in U, g x * ψ x)) + (∫ x in U, g x * ψ x))
      Filter.atTop (𝓝 ((0 : ℝ) + ∫ x in U, g x * ψ x)) :=
    hsub.add tendsto_const_nhds
  simpa only [sub_add_cancel, zero_add] using hmain

/-- **The honest-slice step for a single sample, in sequence form.**  This is
the composition of the two halves: the probabilistic half feeds the
`L²(U)` deficit convergence along a sequence of steps `hs n → 0` (with
`hs n ≠ 0` asymptotically), and the deterministic half converts it into the
weak-derivative identity for one sample `u`, one coordinate `i` and one smooth
compactly supported test function `ψ`.

The hypothesis `hfq` is the `L²(U)`-membership of the difference quotients;
in the application it is read off from `u ∈ L²(U)` and the measure-preserving
shift. -/
theorem eq_neg_setIntegral_coordDeriv_of_tendsto_differenceQuotient_seq
    {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict U)]
    (hUopen : IsOpen U) (hUbd : Bornology.IsBounded U)
    {u gi : Vec d → ℝ} (hu : MemLp u 2 (MeasureTheory.volume.restrict U))
    (hgi : MemLp gi 2 (MeasureTheory.volume.restrict U))
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψU : tsupport ψ ⊆ U) (i : Fin d)
    {hs : ℕ → ℝ} (hst : Filter.Tendsto hs Filter.atTop (𝓝[≠] 0))
    (hfq : ∀ n, MemLp (fun x => Homogenization.euclideanForwardDifferenceQuotient
      (hs n) i u x) 2 (MeasureTheory.volume.restrict U))
    (hconv : Filter.Tendsto (fun n => ∫⁻ x,
      ‖Homogenization.euclideanForwardDifferenceQuotient (hs n) i u x - gi x‖ₑ
        ^ (2 : ℝ) ∂(MeasureTheory.volume.restrict U)) Filter.atTop (𝓝 0)) :
    ∫ x in U, gi x * ψ x = -(∫ x in U, u x * Homogenization.euclideanCoordDeriv i ψ x) := by
  have hcpt : HasCompactSupport ψ :=
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_tsupport ψ, hUbd.subset hψU⟩
  obtain ⟨Cψ, hCψ⟩ := hcpt.exists_bound_of_continuous hψ.continuous
  have hψmem : MemLp ψ 2 (MeasureTheory.volume.restrict U) :=
    MemLp.of_bound hψ.continuous.aestronglyMeasurable Cψ
      (Filter.Eventually.of_forall fun x => hCψ x)
  have hL : Filter.Tendsto
      (fun n => ∫ x in U, Homogenization.euclideanForwardDifferenceQuotient (hs n) i u x * ψ x)
      Filter.atTop (𝓝 (∫ x in U, gi x * ψ x)) :=
    tendsto_setIntegral_mul_of_tendsto_deficit hfq hgi hψmem hconv
  have hR : Filter.Tendsto
      (fun n => -(∫ x in U, u x
        * Homogenization.euclideanBackwardDifferenceQuotient (hs n) i ψ x))
      Filter.atTop (𝓝 (-(∫ x in U, u x * Homogenization.euclideanCoordDeriv i ψ x))) :=
    ((tendsto_setIntegral_mul_backwardDifferenceQuotient hUbd hu hψ hψU i).comp hst).neg
  obtain ⟨δ, hδ0, hδU⟩ := hcpt.exists_cthickening_subset_open hUopen hψU
  have hev : ∀ᶠ h : ℝ in 𝓝[≠] (0 : ℝ), ‖h • Homogenization.basisVec i‖ ≤ δ := by
    have hcont : Continuous fun h : ℝ => ‖h • Homogenization.basisVec i‖ :=
      continuous_norm.comp (continuous_id.smul continuous_const)
    have hlt : ∀ᶠ h : ℝ in 𝓝 (0 : ℝ), ‖h • Homogenization.basisVec i‖ < δ :=
      (hcont.tendsto 0).eventually (Iio_mem_nhds (by simpa using hδ0))
    exact (hlt.mono fun _ hh => le_of_lt hh).filter_mono nhdsWithin_le_nhds
  have hid : ∀ᶠ n in Filter.atTop,
      (∫ x in U, Homogenization.euclideanForwardDifferenceQuotient (hs n) i u x * ψ x)
        = -(∫ x in U, u x * Homogenization.euclideanBackwardDifferenceQuotient (hs n) i ψ x) := by
    filter_upwards [hst.eventually hev] with n hδ
    have hthick : Metric.cthickening ‖(-(hs n)) • Homogenization.basisVec i‖ (tsupport ψ) ⊆ U :=
      fun x hx => hδU (Metric.cthickening_mono (by simpa only [neg_smul, norm_neg] using hδ)
        (tsupport ψ) hx)
    have hshiftsupp : tsupport (fun x => ψ (Homogenization.euclideanCoordShift (-(hs n)) i x)) ⊆ U :=
      fun x hx => hthick (tsupport_comp_euclideanCoordShift_subset_cthickening (-(hs n)) i hx)
    have h3 : Integrable (fun x : Vec d => u x * ψ (Homogenization.euclideanCoordShift (-(hs n)) i x))
        MeasureTheory.volume :=
      integrable_mul_of_memLp_of_hasCompactSupport_subset hu
        (hψ.continuous.comp (continuous_id.add continuous_const))
        (Homogenization.hasCompactSupport_comp_euclideanCoordShift hcpt (-(hs n)) i) hshiftsupp
    have h2 : Integrable (fun x : Vec d => u x * ψ x) MeasureTheory.volume :=
      integrable_mul_of_memLp_of_hasCompactSupport_subset hu hψ.continuous hcpt hψU
    have h1 : Integrable
        (fun x : Vec d => u (Homogenization.euclideanCoordShift (hs n) i x) * ψ x)
        MeasureTheory.volume := by
      have hmp : MeasureTheory.MeasurePreserving
          (fun x : Vec d => x + hs n • Homogenization.basisVec i)
          MeasureTheory.volume MeasureTheory.volume :=
        measurePreserving_add_right MeasureTheory.volume (hs n • Homogenization.basisVec i)
      have hme : MeasurableEmbedding (fun x : Vec d => x + hs n • Homogenization.basisVec i) :=
        measurableEmbedding_addRight (hs n • Homogenization.basisVec i)
      have hcomp : Integrable
          ((fun y : Vec d => u y * ψ (Homogenization.euclideanCoordShift (-(hs n)) i y))
            ∘ fun x : Vec d => x + hs n • Homogenization.basisVec i) MeasureTheory.volume :=
        (hmp.integrable_comp_emb hme).mpr h3
      refine hcomp.congr (Filter.Eventually.of_forall fun x => ?_)
      have harg : (x + hs n • Homogenization.basisVec i) + (-(hs n)) • Homogenization.basisVec i
          = x := by
        rw [neg_smul, add_neg_cancel_right]
      simp only [Function.comp_apply, Homogenization.euclideanCoordShift_apply, harg]
    have hlanded := integral_euclideanForwardDifferenceQuotient_mul_eq_neg_of_integrable
      (u := u) (v := ψ) (hs n) i h1 h2 h3
    calc
      ∫ x in U, Homogenization.euclideanForwardDifferenceQuotient (hs n) i u x * ψ x
          = ∫ x, Homogenization.euclideanForwardDifferenceQuotient (hs n) i u x * ψ x :=
            setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
              rw [image_eq_zero_of_notMem_tsupport fun hmem => hx (hψU hmem), mul_zero]
      _ = -(∫ x, u x * Homogenization.euclideanBackwardDifferenceQuotient (hs n) i ψ x) := hlanded
      _ = -(∫ x in U, u x * Homogenization.euclideanBackwardDifferenceQuotient (hs n) i ψ x) := by
            rw [integral_mul_euclideanBackwardDifferenceQuotient_eq_setIntegral (hs n) i hthick]
  exact tendsto_nhds_unique_of_eventuallyEq hL hR hid

/-- **The extraction, with the cube measure replaced by plain volume.**  The
lemma `exists_strictMono_ae_tendsto_slice_lintegral` produces the spatial
deficit against the *normalised* cube measure; undoing the normalisation turns
it into the deficit against `volume` restricted to the open cube, which is what
the deterministic half consumes. -/
theorem exists_strictMono_ae_tendsto_slice_lintegral_volumeOn
    {P : ProbabilityMeasure (ShellSeq d)}
    [VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure]
    {E : Type*} [SeminormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {Q : TriadicCube d} {f : ℕ → ShellSeq d → E} {g : ShellSeq d → E}
    (hf : ∀ n, StronglyMeasurable (f n)) (hg : StronglyMeasurable g)
    (h : Filter.Tendsto (fun n => ∫⁻ ω, ‖f n ω - g ω‖ₑ ^ (2 : ℝ) ∂P.toMeasure)
      Filter.atTop (𝓝 0)) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∀ᵐ ω ∂P.toMeasure,
      Filter.Tendsto (fun n => ∫⁻ x, ‖f (k n) (x +ᵥ ω) - g (x +ᵥ ω)‖ₑ ^ (2 : ℝ)
        ∂(MeasureTheory.volume.restrict (openCubeSet Q))) Filter.atTop (𝓝 0) := by
  obtain ⟨k, hk, hkconv⟩ :=
    exists_strictMono_ae_tendsto_slice_lintegral (P := P) (Q := Q) hf hg h
  refine ⟨k, hk, hkconv.mono fun ω hω => ?_⟩
  have hnorm : normalizedCubeMeasure Q = ENNReal.ofReal ((cubeVolume Q)⁻¹)
      • MeasureTheory.volume.restrict (openCubeSet Q) := by
    simp only [Homogenization.normalizedCubeMeasure, Homogenization.cubeMeasure,
      Homogenization.volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  rw [hnorm] at hω
  exact tendsto_lintegral_of_tendsto_smul_measure _
    (ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr (Homogenization.cubeVolume_pos Q)))
    ENNReal.ofReal_ne_top hω

/-- **The honest-slice step at the sample level, for one coordinate.**  This is
the statement of `honestSlice` with the whole probabilistic half reduced to its
a.e.-`ω` output: given the `L²(U)` deficit convergence of the sample difference
quotients, almost every sample has the weak `i`-partial derivative.  The only
extra hypotheses beyond `honestSlice`'s data are the `L²(U)`-memberships of the
sample field, of the sample gradient and of the sample difference quotients —
all consequences of the slice-membership transfer `ae_memLp_slice` at the
shifted samples. -/
theorem ae_hasWeakPartialDerivOn_of_ae_tendsto_slice_deficit
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict U)]
    (hUopen : IsOpen U) (hUbd : Bornology.IsBounded U)
    (φs : Ω → Vec d → ℝ) (gs : Ω → Vec d → ℝ) (i : Fin d)
    {hs : ℕ → ℝ} (hst : Filter.Tendsto hs Filter.atTop (𝓝[≠] 0))
    (hφmem : ∀ᵐ ω ∂μ, MemLp (φs ω) 2 (MeasureTheory.volume.restrict U))
    (hgsmem : ∀ᵐ ω ∂μ, MemLp (gs ω) 2 (MeasureTheory.volume.restrict U))
    (hfqmem : ∀ᵐ ω ∂μ, ∀ n, MemLp
      (fun x => Homogenization.euclideanForwardDifferenceQuotient (hs n) i (φs ω) x)
      2 (MeasureTheory.volume.restrict U))
    (hconv : ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => ∫⁻ x,
      ‖Homogenization.euclideanForwardDifferenceQuotient (hs n) i (φs ω) x - gs ω x‖ₑ
        ^ (2 : ℝ) ∂(MeasureTheory.volume.restrict U)) Filter.atTop (𝓝 0)) :
    ∀ᵐ ω ∂μ, Homogenization.HasWeakPartialDerivOn U i (φs ω) (gs ω) := by
  filter_upwards [hφmem, hgsmem, hfqmem, hconv] with ω h1 h2 h3 h4
  intro ψ hψ hψc hψU
  show ∫ x in U, φs ω x * Homogenization.euclideanCoordDeriv i ψ x
    = -∫ x in U, gs ω x * ψ x
  have h := eq_neg_setIntegral_coordDeriv_of_tendsto_differenceQuotient_seq
    hUopen hUbd h1 h2 hψ hψU i hst h3 h4
  rw [h, neg_neg]

/-- **The slice identity, in inverse form.**  The spatial slice of the `L²(Ω)`
difference quotient of a stationary field along the coordinate direction `i` is the
ordinary forward coordinate difference quotient of the spatial slice, written with
`h⁻¹`. -/
theorem differenceQuotient_slice_eq (h : ℝ) (i : Fin d) (f : ShellSeq d → ℝ)
    (ω : ShellSeq d) (x : Vec d) :
    h⁻¹ * (f (h • Homogenization.basisVec i +ᵥ (x +ᵥ ω)) - f (x +ᵥ ω)) =
      Homogenization.euclideanForwardDifferenceQuotient h i (fun y : Vec d => f (y +ᵥ ω)) x := by
  have harg : h • Homogenization.basisVec i +ᵥ (x +ᵥ ω) =
      (x + h • Homogenization.basisVec i) +ᵥ ω := by
    rw [vadd_vadd, add_comm]
  rw [Homogenization.euclideanForwardDifferenceQuotient_apply,
    Homogenization.euclideanCoordShift_apply, harg, div_eq_mul_inv, mul_comm]

section SliceLayer

variable {P : ProbabilityMeasure (ShellSeq d)}
variable [VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure]

/-- **The Koopman translate on the ambient function.**  The translate of a scalar
`L²(Ω)` class is the translate of its representing function. -/
theorem koopman_coeFn (x : Vec d) (g : ScalarL2 P.toMeasure) :
    (koopman (μ := P.toMeasure) x g : ShellSeq d → ℝ) =ᵐ[P.toMeasure] fun ω => g (x +ᵥ ω) :=
  Lp.coeFn_compMeasurePreserving g
    (measurePreserving_const_vadd (μ := P.toMeasure) (Ω := ShellSeq d) x)

omit [VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure] in
/-- **The coordinate of a Hilbert-vector `L²(Ω)` field.**  The `i`th coordinate of
the class of a vector field is the representative coordinate, a.e. -/
theorem vectorL2Coord_toLp (i : Fin d) (f : ShellSeq d → Vec d)
    (hf : MemLp (fun ω => HilbertVec.ofVec (f ω)) 2 P.toMeasure) :
    (vectorL2Coord (μ := P.toMeasure) i (hf.toLp (fun ω => HilbertVec.ofVec (f ω)))
      : ShellSeq d → ℝ) =ᵐ[P.toMeasure] fun ω => f ω i := by
  have h1 := ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := P.toMeasure)
    (L := PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) i)
    (f := hf.toLp (fun ω => HilbertVec.ofVec (f ω)))
  have h2 := (MemLp.coeFn_toLp hf).fun_comp
    (PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) i)
  refine h1.trans (h2.trans ?_)
  filter_upwards with ω
  simp only [Function.comp_apply]
  simp

omit [VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure] in
/-- **Each coordinate of a Hilbert-vector `MemLp` field is `MemLp`.** -/
theorem memLp_coord_of_memLp_ofVec (i : Fin d) (f : ShellSeq d → Vec d)
    (hf : MemLp (fun ω => HilbertVec.ofVec (f ω)) 2 P.toMeasure) :
    MemLp (fun ω => f ω i) 2 P.toMeasure := by
  refine ((PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) i).comp_memLp' hf).ae_eq ?_
  filter_upwards with ω
  simp only [Function.comp_apply]
  simp

/-- **The volume measure on the open cube is a multiple of the normalised cube
measure.** -/
theorem volumeMeasureOn_openCubeSet_eq_smul_normalizedCubeMeasure (Q : TriadicCube d) :
    MeasureTheory.volume.restrict (openCubeSet Q) =
      ENNReal.ofReal (cubeVolume Q) • normalizedCubeMeasure Q := by
  have hnorm : normalizedCubeMeasure Q = ENNReal.ofReal ((cubeVolume Q)⁻¹)
      • MeasureTheory.volume.restrict (openCubeSet Q) := by
    simp only [Homogenization.normalizedCubeMeasure, Homogenization.cubeMeasure,
      Homogenization.volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  rw [hnorm, smul_smul, ← ENNReal.ofReal_mul (le_of_lt (Homogenization.cubeVolume_pos Q)),
    mul_inv_cancel₀ (ne_of_gt (Homogenization.cubeVolume_pos Q)), ENNReal.ofReal_one, one_smul]

/-- **The slices of a scalar field are `L²` on the open cube.**  This is the
slice-membership transfer `ae_memLp_slice` at the normalised cube measure, converted
to the unnormalised volume on the cube. -/
theorem ae_memLp_slice_openCube (Q : TriadicCube d) {g : ShellSeq d → ℝ}
    (hgm : Measurable g) (hg : MemLp g 2 P.toMeasure) :
    ∀ᵐ ω ∂P.toMeasure, MemLp (fun x => g (x +ᵥ ω)) 2
      (MeasureTheory.volume.restrict (openCubeSet Q)) := by
  have : IsProbabilityMeasure (normalizedCubeMeasure Q) :=
    ⟨normalizedCubeMeasure_apply_univ Q⟩
  filter_upwards [ae_memLp_slice (μ := P.toMeasure) (ν := normalizedCubeMeasure Q) hgm hg]
    with ω hω
  rw [volumeMeasureOn_openCubeSet_eq_smul_normalizedCubeMeasure Q]
  exact hω.smul_measure ENNReal.ofReal_ne_top

/-- **The `L²(Ω)` difference quotient, read at a sample.**  The sample value of the
scalar multiple of the Koopman difference of a field is the plain difference quotient
of the field. -/
theorem differenceQuotient_class_coeFn (h : ℝ) (i : Fin d) {f : ShellSeq d → ℝ}
    (hf : MemLp f 2 P.toMeasure) :
    (((h⁻¹ : ℝ) • (koopman (μ := P.toMeasure) (h • Homogenization.basisVec i) (hf.toLp f)
        - hf.toLp f) : ScalarL2 P.toMeasure) : ShellSeq d → ℝ)
      =ᵐ[P.toMeasure] fun ω => h⁻¹ * (f (h • Homogenization.basisVec i +ᵥ ω) - f ω) := by
  have hshift : Filter.Tendsto (fun ω : ShellSeq d => h • Homogenization.basisVec i +ᵥ ω)
      (ae P.toMeasure) (ae P.toMeasure) :=
    (measurePreserving_const_vadd (μ := P.toMeasure) (Ω := ShellSeq d)
      (h • Homogenization.basisVec i)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [Lp.coeFn_smul (h⁻¹ : ℝ)
      (koopman (μ := P.toMeasure) (h • Homogenization.basisVec i) (hf.toLp f) - hf.toLp f),
    Lp.coeFn_sub (koopman (μ := P.toMeasure) (h • Homogenization.basisVec i) (hf.toLp f))
      (hf.toLp f),
    koopman_coeFn (P := P) (h • Homogenization.basisVec i) (hf.toLp f),
    (MemLp.coeFn_toLp hf).comp_tendsto hshift,
    MemLp.coeFn_toLp hf] with ω h0 h1 h2 h3 h4
  simp only [Function.comp_apply] at h3
  rw [h0, Pi.smul_apply, smul_eq_mul, h1, Pi.sub_apply, h2, h3, h4]

/-- **The sample difference quotient is measurable.** -/
theorem differenceQuotient_measurable (h : ℝ) (i : Fin d) {f : ShellSeq d → ℝ}
    (hfm : Measurable f) :
    Measurable (fun ω : ShellSeq d => h⁻¹ * (f (h • Homogenization.basisVec i +ᵥ ω) - f ω)) :=
  ((hfm.comp (measurable_const_vadd (h • Homogenization.basisVec i))).sub hfm).const_mul h⁻¹

/-- **The sample difference quotient is `L²(Ω)`.** -/
theorem differenceQuotient_memLp (h : ℝ) (i : Fin d) {f : ShellSeq d → ℝ}
    (hf : MemLp f 2 P.toMeasure) :
    MemLp (fun ω : ShellSeq d => h⁻¹ * (f (h • Homogenization.basisVec i +ᵥ ω) - f ω))
      2 P.toMeasure :=
  (Lp.memLp ((h⁻¹ : ℝ) • (koopman (μ := P.toMeasure) (h • Homogenization.basisVec i)
    (hf.toLp f) - hf.toLp f))).ae_eq (differenceQuotient_class_coeFn (P := P) h i hf)

/-- **The spatial slices of the sample difference quotient are `L²` on the cube.** -/
theorem ae_memLp_slice_differenceQuotient (Q : TriadicCube d) (h : ℝ) (i : Fin d)
    {f : ShellSeq d → ℝ} (hfm : Measurable f) (hf : MemLp f 2 P.toMeasure) :
    ∀ᵐ ω ∂P.toMeasure, MemLp (fun x => Homogenization.euclideanForwardDifferenceQuotient h i
      (fun y : Vec d => f (y +ᵥ ω)) x) 2 (MeasureTheory.volume.restrict (openCubeSet Q)) := by
  filter_upwards [ae_memLp_slice_openCube (P := P) Q
    (differenceQuotient_measurable h i hfm)
    (differenceQuotient_memLp (P := P) h i hf)] with ω hω
  refine hω.ae_eq ?_
  filter_upwards with x
  exact differenceQuotient_slice_eq h i f ω x

/-- **The honest slice.**  If `F` is the strong horizontal gradient in `L²(Ω)` of the
scalar field `φ`, then at almost every sample the spatial slice of `F` is the weak
gradient, on the open cube `Q`, of the spatial slice of `φ`. -/
theorem honestSlice (Q : TriadicCube d) {φ : ShellSeq d → ℝ} {F : ShellSeq d → Vec d}
    (hφ : MemLp φ 2 P.toMeasure)
    (hF : MemLp (fun ω => HilbertVec.ofVec (F ω)) 2 P.toMeasure)
    (hφm : Measurable φ) (hFm : Measurable F)
    (hgrad : HasHorizontalGradient (μ := P.toMeasure) (hφ.toLp φ)
      (hF.toLp (fun ω => HilbertVec.ofVec (F ω)))) :
    ∀ᵐ ω ∂P.toMeasure, HasWeakGradientOn (openCubeSet Q) (fun x => φ (x +ᵥ ω))
      (fun x => F (x +ᵥ ω)) := by
  classical
  have : IsFiniteMeasure (MeasureTheory.volume.restrict (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hUopen : IsOpen (openCubeSet Q) := (isOpenBoundedConvexDomain_openCubeSet Q).isOpen
  have hUbd : Bornology.IsBounded (openCubeSet Q) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isBoundedDomain.isBounded
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
  have hφslice : ∀ᵐ ω ∂P.toMeasure, MemLp (fun x => φ (x +ᵥ ω)) 2
      (MeasureTheory.volume.restrict (openCubeSet Q)) :=
    ae_memLp_slice_openCube (P := P) Q hφm hφ
  refine Filter.eventually_all.2 fun i => ?_
  have hFslice : ∀ᵐ ω ∂P.toMeasure, MemLp (fun x => F (x +ᵥ ω) i) 2
      (MeasureTheory.volume.restrict (openCubeSet Q)) :=
    ae_memLp_slice_openCube (P := P) Q (g := fun ω => F ω i) ((measurable_pi_apply i).comp hFm)
      (memLp_coord_of_memLp_ofVec (P := P) i F hF)
  have hslope : Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (koopman (μ := P.toMeasure) (t • Homogenization.basisVec i)
        (hφ.toLp φ) - hφ.toLp φ)) (𝓝[≠] (0 : ℝ))
      (𝓝 (vectorL2Coord (μ := P.toMeasure) i (hF.toLp (fun ω => HilbertVec.ofVec (F ω))))) := by
    have h := HasDerivAt.tendsto_slope_zero (hgrad i)
    simp only [zero_add, zero_smul, koopman_zero] at h
    exact h
  let u : ℕ → ScalarL2 P.toMeasure := fun n =>
    (hs n)⁻¹ • (koopman (μ := P.toMeasure) (hs n • Homogenization.basisVec i) (hφ.toLp φ)
      - hφ.toLp φ)
  have hseq : Filter.Tendsto u Filter.atTop
      (𝓝 (vectorL2Coord (μ := P.toMeasure) i (hF.toLp (fun ω => HilbertVec.ofVec (F ω))))) := by
    exact hslope.comp hst
  have hdeficit := tendsto_lintegral_enorm_sq_of_tendsto_Lp (E := ℝ) (μ := P.toMeasure) hseq
  have hdeficit' : Filter.Tendsto
      (fun n => ∫⁻ ω, ‖(hs n)⁻¹ * (φ (hs n • Homogenization.basisVec i +ᵥ ω) - φ ω)
        - F ω i‖ₑ ^ (2 : ℝ) ∂P.toMeasure) Filter.atTop (𝓝 0) := by
    refine Filter.Tendsto.congr' ?_ hdeficit
    filter_upwards with n
    refine MeasureTheory.lintegral_congr_ae ?_
    filter_upwards [differenceQuotient_class_coeFn (P := P) (hs n) i hφ,
      vectorL2Coord_toLp (P := P) i F hF] with ω h1 h2
    simp only [u]
    rw [h1, h2]
  obtain ⟨k, hk, hkconv⟩ := exists_strictMono_ae_tendsto_slice_lintegral_volumeOn (P := P)
    (Q := Q) (E := ℝ)
    (f := fun n ω => (hs n)⁻¹ * (φ (hs n • Homogenization.basisVec i +ᵥ ω) - φ ω))
    (g := fun ω => F ω i)
    (fun n => (differenceQuotient_measurable (hs n) i hφm).stronglyMeasurable)
    ((measurable_pi_apply i).comp hFm).stronglyMeasurable hdeficit'
  have hDqslice : ∀ᵐ ω ∂P.toMeasure, ∀ n, MemLp (fun x =>
      Homogenization.euclideanForwardDifferenceQuotient (hs (k n)) i (fun y : Vec d => φ (y +ᵥ ω)) x)
      2 (MeasureTheory.volume.restrict (openCubeSet Q)) := by
    rw [MeasureTheory.ae_all_iff]
    exact fun n => ae_memLp_slice_differenceQuotient (P := P) Q (hs (k n)) i hφm hφ
  have hconv : ∀ᵐ ω ∂P.toMeasure, Filter.Tendsto (fun n => ∫⁻ x,
      ‖Homogenization.euclideanForwardDifferenceQuotient (hs (k n)) i
          (fun y : Vec d => φ (y +ᵥ ω)) x - F (x +ᵥ ω) i‖ₑ ^ (2 : ℝ)
        ∂(MeasureTheory.volume.restrict (openCubeSet Q))) Filter.atTop (𝓝 0) := by
    filter_upwards [hkconv] with ω hω
    refine Filter.Tendsto.congr (fun n => ?_) hω
    refine MeasureTheory.lintegral_congr fun x => ?_
    rw [differenceQuotient_slice_eq (hs (k n)) i φ ω x]
  exact ae_hasWeakPartialDerivOn_of_ae_tendsto_slice_deficit (μ := P.toMeasure)
    (U := openCubeSet Q) hUopen hUbd (fun ω x => φ (x +ᵥ ω)) (fun ω x => F (x +ᵥ ω) i) i
    (hs := fun n => hs (k n)) (hst.comp hk.tendsto_atTop) hφslice hFslice hDqslice hconv

end SliceLayer

end SuperdiffusionCLT.Probability.Stationary

end
