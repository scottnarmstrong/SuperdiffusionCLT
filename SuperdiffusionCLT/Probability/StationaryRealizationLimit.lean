/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.StationaryRealizationConcrete
public import Homogenization.Sobolev.WeakDerivatives
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.Metrizable.Basic

/-!
# The stationary realization: the transfer and almost-every-sample limit layer

This module works at the concrete carrier `Ω := ShellSeq d`, `μ := P.toMeasure`, where the
translation action is jointly measurable
(`SuperdiffusionCLT.Section3.Terms.measurable_vadd_shellSeq`) and the pushforward identity
`SuperdiffusionCLT.Section3.Terms.map_vadd_prod_eq` holds for the normalized cube
measure.

The declarations below are the analytic layer that turns a *convergence in `L²(Ω)`* of
stationary fields into a convergence of their *spatial realizations* at almost every
sample, together with the deterministic cube layer that reads a difference-quotient
convergence on a single sample as a weak derivative.

1. the transfer layer: `aemeasurable_realize_prod`, `lintegral_enorm_rpow_realize_prod`;
2. the almost-every-sample extraction: `exists_strictMono_ae_tendsto_slice_lintegral`
   turns `∫⁻ ω, ‖f n ω - g ω‖ₑ ^ 2 → 0` into a *single* strictly monotone subsequence
   whose *spatial* realizations converge in `L²` on the cube for almost every sample —
   the passage to a subsequence of convergence in measure.

Everything here is stated with every input as a named hypothesis; no statement is
asserted of the realization itself.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Homogenization
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section3.Terms
open scoped BigOperators ENNReal Topology Pointwise

noncomputable section

namespace SuperdiffusionCLT.Probability.Stationary

variable {d : ℕ}

section Transfer

variable {P : ProbabilityMeasure (ShellSeq d)}
variable [VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure]

omit [VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure] in
/-- The spatial realization of a shell-sequence field is a.e.-measurable on the
product of the sample law with the cube measure. -/
theorem aemeasurable_realize_prod {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [BorelSpace E] [TopologicalSpace.PseudoMetrizableSpace E]
    {X : ShellSeq d → E} (hX : StronglyMeasurable X) (Q : TriadicCube d) :
    AEMeasurable (fun p : ShellSeq d × Vec d => X (p.2 +ᵥ p.1))
      (P.toMeasure.prod (normalizedCubeMeasure Q)) :=
  (hX.comp_measurable (measurable_vadd_shellSeq (d := d))).aemeasurable

/-- **The `L^r`-transfer.**  The `r`-th power of the norm of a shell-sequence field
and the same power of the norm of its spatial realization have the same integral over
the sample law and over the product of the sample law with the cube measure.  This is
the integrated pushforward identity `map_vadd_prod_eq`, read on `ℝ≥0∞`-valued
integrands. -/
theorem lintegral_enorm_rpow_realize_prod {E : Type*} [SeminormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E]
    {X : ShellSeq d → E} (hX : StronglyMeasurable X) (Q : TriadicCube d) (r : ℝ) :
    ∫⁻ p : ShellSeq d × Vec d, ‖X (p.2 +ᵥ p.1)‖ₑ ^ r
        ∂(P.toMeasure.prod (normalizedCubeMeasure Q)) =
      ∫⁻ ω, ‖X ω‖ₑ ^ r ∂P.toMeasure := by
  have hpow : AEMeasurable (fun p : ShellSeq d × Vec d => ‖X (p.2 +ᵥ p.1)‖ₑ ^ r)
      (P.toMeasure.prod (normalizedCubeMeasure Q)) :=
    ((aemeasurable_realize_prod (P := P) hX Q).enorm).pow_const r
  rw [lintegral_prod _ hpow]
  exact (lintegral_cubeAverage_vadd_shellSeq (P := P) (Q := Q)
    (hX.measurable.enorm.pow_const r)).symm

end Transfer

section Deterministic

end Deterministic

/-- A sequence of `ℝ≥0∞` numbers whose truncation at `1` has real part tending to zero
itself tends to zero. -/
private theorem tendsto_nhds_zero_of_tendsto_toReal_min {u : ℕ → ℝ≥0∞}
    (h : Filter.Tendsto (fun n => (min (u n) 1).toReal) Filter.atTop (𝓝 0)) :
    Filter.Tendsto u Filter.atTop (𝓝 0) := by
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

section SliceExtraction

variable {P : ProbabilityMeasure (ShellSeq d)}
variable [VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure]

/-- **The almost-every-sample extraction.**  If the realized deficits
`∫⁻ ω, ‖f n ω - g ω‖ₑ ^ 2` tend to zero, then there is a single strictly monotone
subsequence `k` such that, at almost every sample `ω`, the *spatial* slices
`x ↦ f (k n) (x +ᵥ ω)` converge to `x ↦ g (x +ᵥ ω)` in `L²` on the cube: the slice
deficit `∫⁻ x, ‖f (k n) (x +ᵥ ω) - g (x +ᵥ ω)‖ₑ ^ 2` tends to zero for a.e. `ω`.

The subsequence is extracted once and for all, not per sample: the transfer lemmas
`lintegral_enorm_rpow_realize_prod` and `lintegral_prod` identify the iterated
integral of the slice deficit with the realized `L²(Ω)`-deficit, and the extraction is
the passage to a subsequence from convergence in measure. -/
theorem exists_strictMono_ae_tendsto_slice_lintegral
    {E : Type*} [SeminormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {Q : TriadicCube d} {f : ℕ → ShellSeq d → E} {g : ShellSeq d → E}
    (hf : ∀ n, StronglyMeasurable (f n)) (hg : StronglyMeasurable g)
    (h : Filter.Tendsto (fun n => ∫⁻ ω, ‖f n ω - g ω‖ₑ ^ (2 : ℝ) ∂P.toMeasure)
      Filter.atTop (𝓝 0)) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∀ᵐ ω ∂P.toMeasure,
      Filter.Tendsto (fun n => ∫⁻ x, ‖f (k n) (x +ᵥ ω) - g (x +ᵥ ω)‖ₑ ^ (2 : ℝ)
        ∂(normalizedCubeMeasure Q)) Filter.atTop (𝓝 0) := by
  classical
  have : IsProbabilityMeasure (normalizedCubeMeasure Q) :=
    ⟨normalizedCubeMeasure_apply_univ Q⟩
  have hjoint : ∀ n, AEMeasurable
      (fun p : ShellSeq d × Vec d => ‖f n (p.2 +ᵥ p.1) - g (p.2 +ᵥ p.1)‖ₑ ^ (2 : ℝ))
      (P.toMeasure.prod (normalizedCubeMeasure Q)) := fun n =>
    ((aemeasurable_realize_prod (P := P) ((hf n).sub hg) Q).enorm).pow_const (2 : ℝ)
  have hG_ae : ∀ n, AEMeasurable
      (fun ω => ∫⁻ x, ‖f n (x +ᵥ ω) - g (x +ᵥ ω)‖ₑ ^ (2 : ℝ)
        ∂(normalizedCubeMeasure Q)) P.toMeasure := fun n =>
    (hjoint n).lintegral_prod_right'
  have hG_int : ∀ n, (∫⁻ ω, ∫⁻ x, ‖f n (x +ᵥ ω) - g (x +ᵥ ω)‖ₑ ^ (2 : ℝ)
        ∂(normalizedCubeMeasure Q) ∂P.toMeasure) =
      ∫⁻ ω, ‖f n ω - g ω‖ₑ ^ (2 : ℝ) ∂P.toMeasure := by
    intro n
    have hprod : (∫⁻ p : ShellSeq d × Vec d,
          ‖(fun ω => f n ω - g ω) (p.2 +ᵥ p.1)‖ₑ ^ (2 : ℝ)
          ∂(P.toMeasure.prod (normalizedCubeMeasure Q))) =
        ∫⁻ ω, ‖f n ω - g ω‖ₑ ^ (2 : ℝ) ∂P.toMeasure :=
      lintegral_enorm_rpow_realize_prod (P := P) ((hf n).sub hg) Q (2 : ℝ)
    have hiter : (∫⁻ p : ShellSeq d × Vec d,
          ‖f n (p.2 +ᵥ p.1) - g (p.2 +ᵥ p.1)‖ₑ ^ (2 : ℝ)
          ∂(P.toMeasure.prod (normalizedCubeMeasure Q))) =
        ∫⁻ ω, ∫⁻ x, ‖f n (x +ᵥ ω) - g (x +ᵥ ω)‖ₑ ^ (2 : ℝ)
          ∂(normalizedCubeMeasure Q) ∂P.toMeasure :=
      lintegral_prod
        (fun p : ShellSeq d × Vec d => ‖f n (p.2 +ᵥ p.1) - g (p.2 +ᵥ p.1)‖ₑ ^ (2 : ℝ))
        (hjoint n)
    exact hiter.symm.trans hprod
  have hG_tend : Filter.Tendsto
      (fun n => ∫⁻ ω, ∫⁻ x, ‖f n (x +ᵥ ω) - g (x +ᵥ ω)‖ₑ ^ (2 : ℝ)
        ∂(normalizedCubeMeasure Q) ∂P.toMeasure) Filter.atTop (𝓝 0) := by
    have heq : (fun n => ∫⁻ ω, ∫⁻ x, ‖f n (x +ᵥ ω) - g (x +ᵥ ω)‖ₑ ^ (2 : ℝ)
          ∂(normalizedCubeMeasure Q) ∂P.toMeasure)
        = fun n => ∫⁻ ω, ‖f n ω - g ω‖ₑ ^ (2 : ℝ) ∂P.toMeasure := funext hG_int
    rw [heq]
    exact h
  have hmin : Filter.Tendsto
      (fun n => ∫⁻ ω, min (∫⁻ x, ‖f n (x +ᵥ ω) - g (x +ᵥ ω)‖ₑ ^ (2 : ℝ)
        ∂(normalizedCubeMeasure Q)) 1 ∂P.toMeasure) Filter.atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hG_tend
      (fun n => zero_le)
      (fun n => lintegral_mono (fun ω => min_le_left _ _))
  have hH_meas : ∀ n, AEStronglyMeasurable
      (fun ω => (min (∫⁻ x, ‖f n (x +ᵥ ω) - g (x +ᵥ ω)‖ₑ ^ (2 : ℝ)
        ∂(normalizedCubeMeasure Q)) 1).toReal) P.toMeasure := fun n =>
    (ENNReal.measurable_toReal.comp_aemeasurable
      ((hG_ae n).min aemeasurable_const)).aestronglyMeasurable
  have hLp : Filter.Tendsto
      (fun n => eLpNorm (fun ω => (min (∫⁻ x, ‖f n (x +ᵥ ω) - g (x +ᵥ ω)‖ₑ ^ (2 : ℝ)
        ∂(normalizedCubeMeasure Q)) 1).toReal - 0) 1 P.toMeasure) Filter.atTop (𝓝 0) := by
    have heq : (fun n => eLpNorm (fun ω => (min (∫⁻ x,
            ‖f n (x +ᵥ ω) - g (x +ᵥ ω)‖ₑ ^ (2 : ℝ)
            ∂(normalizedCubeMeasure Q)) 1).toReal - 0) 1 P.toMeasure)
        = fun n => ∫⁻ ω, min (∫⁻ x, ‖f n (x +ᵥ ω) - g (x +ᵥ ω)‖ₑ ^ (2 : ℝ)
            ∂(normalizedCubeMeasure Q)) 1 ∂P.toMeasure := by
      funext n
      rw [eLpNorm_one_eq_lintegral_enorm (by simpa only [sub_zero] using hH_meas n)]
      refine lintegral_congr fun ω => ?_
      rw [Real.enorm_eq_ofReal_abs, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal
          (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _))]
    rw [heq]
    exact hmin
  have hTIM : TendstoInMeasure P.toMeasure
      (fun n ω => (min (∫⁻ x, ‖f n (x +ᵥ ω) - g (x +ᵥ ω)‖ₑ ^ (2 : ℝ)
        ∂(normalizedCubeMeasure Q)) 1).toReal) Filter.atTop (fun _ => (0 : ℝ)) :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hLp
  obtain ⟨k, hk, hae⟩ := hTIM.exists_seq_tendsto_ae
  exact ⟨k, hk, by
    filter_upwards [hae] with ω hω
    exact tendsto_nhds_zero_of_tendsto_toReal_min hω⟩

end SliceExtraction

end SuperdiffusionCLT.Probability.Stationary

end
