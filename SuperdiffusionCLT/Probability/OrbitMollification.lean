/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Probability.StationaryProjectionTransport
public import SuperdiffusionCLT.Section3.Terms.StationaryRealizationConcrete
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Orbit mollification of a stationary field

Let `Ω := ShellSeq d` carry the measure-preserving translation action of `Vec d`
and the law `μ := P.toMeasure`.  For a kernel `θ : Vec d → ℝ` and a square
integrable field `X` on `Ω`, the *orbit mollification* is

`mollify θ X ω = ∫ y, θ y • X (y +ᵥ ω)`,

the average of the whole orbit of `X` under the smooth weight `θ`.  This module
builds that operator and the `L²` facts the stationary second conjunct consumes:

* `memLp_mollify` — mollification by an integrable continuous kernel stays in `L²(μ)`;
* `normSq_mollify_le` — the pointwise square bound
  `‖X_θ ω‖² ≤ ‖θ‖_{L¹} ∫ |θ y| ‖X (y +ᵥ ω)‖² dy`, behind that estimate;
* `ae_integrable_smul_realize` — for almost every sample, the shifted integrand of the
  mollification is Bochner integrable in the space variable.

The sign convention `y +ᵥ ω` is the printed one of the brief.

Everything here is at the concrete carrier, where the instance
`instMeasurableVAdd₂ShellSeq` (`Section3/Terms/StationaryRealizationConcrete.lean`)
provides the joint measurability the sample-wise Fubini arguments need.
-/

@[expose] public section

open MeasureTheory Homogenization
open SuperdiffusionCLT.Section2.Cutoff
open scoped BigOperators ENNReal InnerProductSpace

noncomputable section

namespace SuperdiffusionCLT.Probability.Stationary

variable {d : ℕ}

/-! ## The mollification operator -/

/-- **The orbit mollification of a Hilbert-vector-valued field.**  This is the
carrier-honest form (the `L²(μ)` class of a `Vec d`-valued field is the class of
its `HilbertVec.ofVec` image, as everywhere in this development). -/
def mollify (θ : Vec d → ℝ) (X : ShellSeq d → HilbertVec d) (ω : ShellSeq d) : HilbertVec d :=
  ∫ y, θ y • X (y +ᵥ ω)

/-! ## Linearity of the mollification in its kernel -/

/-! ## Measurability and the `L²` layer -/

/-- Joint measurability of the mollification integrand on the concrete carrier. -/
theorem stronglyMeasurable_mollify {θ : Vec d → ℝ} (hθ : Continuous θ)
    {X : ShellSeq d → HilbertVec d} (hX : StronglyMeasurable X) :
    StronglyMeasurable (mollify θ X) := by
  have hmeas : Measurable fun q : ShellSeq d × Vec d => q.2 +ᵥ q.1 :=
    (measurable_vadd (M := Vec d) (α := ShellSeq d)).comp measurable_swap
  have hjm : StronglyMeasurable fun q : ShellSeq d × Vec d => θ q.2 • X (q.2 +ᵥ q.1) :=
    ((hθ.measurable.comp measurable_snd).stronglyMeasurable).smul
      (hX.comp_measurable hmeas)
  have h : StronglyMeasurable fun x : ShellSeq d => ∫ y : Vec d, θ y • X (y +ᵥ x) :=
    hjm.integral_prod_right' (ν := (volume : Measure (Vec d)))
  exact h

/-- Joint integrability of `(ω, y) ↦ ρ y · g (y +ᵥ ω)` for an integrable weight
`ρ` and an integrable observable `g` on the sequence carrier. -/
theorem integrable_prod_weighted_comp_vadd {P : ProbabilityMeasure (ShellSeq d)}
    [VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure]
    {ρ : Vec d → ℝ} (hρm : Continuous ρ) (hρ : Integrable ρ volume)
    {g : ShellSeq d → ℝ} (hgm : StronglyMeasurable g) (hg : Integrable g P.toMeasure) :
    Integrable (fun q : ShellSeq d × Vec d => ρ q.2 * g (q.2 +ᵥ q.1))
      (P.toMeasure.prod volume) := by
  have hmeas : Measurable fun q : ShellSeq d × Vec d => q.2 +ᵥ q.1 :=
    (measurable_vadd (M := Vec d) (α := ShellSeq d)).comp measurable_swap
  have hjm : StronglyMeasurable fun q : ShellSeq d × Vec d => ρ q.2 * g (q.2 +ᵥ q.1) :=
    ((hρm.measurable.comp measurable_snd).stronglyMeasurable).mul
      (hgm.comp_measurable hmeas)
  refine (integrable_prod_iff' hjm.aestronglyMeasurable).2 ⟨?_, ?_⟩
  · exact Filter.Eventually.of_forall fun y =>
      ((measurePreserving_const_vadd (μ := P.toMeasure) (Ω := ShellSeq d) y).integrable_comp_of_integrable
        hg).const_mul (ρ y)
  · have hval : ∀ y : Vec d,
        (∫ ω, ‖ρ y * g (y +ᵥ ω)‖ ∂P.toMeasure) = |ρ y| * ∫ ω, ‖g ω‖ ∂P.toMeasure := by
      intro y
      simp only [norm_mul, Real.norm_eq_abs]
      rw [integral_const_mul]
      exact congrArg (fun t => |ρ y| * t)
        (SuperdiffusionCLT.Section3.Terms.integral_comp_vadd_shellSeq
          (fun ω => |g ω|) y)
    refine (integrable_congr (Filter.Eventually.of_forall hval)).2 ?_
    exact hρ.abs.mul_const _

/-! ## The weighted Cauchy-Schwarz inequality

The square of a weighted mean is at most the weighted mean of the square.  This
is what turns the pointwise norm bound for a Bochner integral into the `L²`
estimate on a mollification. -/

/-- The weighted Cauchy-Schwarz inequality: for a nonnegative weight `ρ`, the
square of `∫ ρ g` is at most `(∫ ρ) (∫ ρ g²)`. -/
theorem sq_weighted_integral_le {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {ρ g : α → ℝ} (hρ0 : ∀ a, 0 ≤ ρ a) (hρ : Integrable ρ ν)
    (h1 : Integrable (fun a => ρ a * g a) ν) (h2 : Integrable (fun a => ρ a * g a ^ 2) ν) :
    (∫ a, ρ a * g a ∂ν) ^ 2 ≤ (∫ a, ρ a ∂ν) * ∫ a, ρ a * g a ^ 2 ∂ν := by
  have hexp : ∀ c : ℝ, ∫ a, ρ a * (g a - c) ^ 2 ∂ν
      = ((∫ a, ρ a * g a ^ 2 ∂ν) - 2 * c * ∫ a, ρ a * g a ∂ν) + c ^ 2 * ∫ a, ρ a ∂ν := by
    intro c
    have hpt : ∀ a, ρ a * (g a - c) ^ 2
        = ρ a * g a ^ 2 - 2 * c * (ρ a * g a) + c ^ 2 * ρ a := by
      intro a; ring
    have hmul1 : Integrable (fun a => 2 * c * (ρ a * g a)) ν := h1.const_mul (2 * c)
    have hmul2 : Integrable (fun a => c ^ 2 * ρ a) ν := hρ.const_mul (c ^ 2)
    have hA : Integrable (fun a => ρ a * g a ^ 2 - 2 * c * (ρ a * g a)) ν := h2.sub hmul1
    calc ∫ a, ρ a * (g a - c) ^ 2 ∂ν
        = ∫ a, ((ρ a * g a ^ 2 - 2 * c * (ρ a * g a)) + c ^ 2 * ρ a) ∂ν := by
          simp only [hpt]
      _ = (∫ a, (ρ a * g a ^ 2 - 2 * c * (ρ a * g a)) ∂ν) + ∫ a, c ^ 2 * ρ a ∂ν :=
          integral_add hA hmul2
      _ = ((∫ a, ρ a * g a ^ 2 ∂ν) - 2 * c * ∫ a, ρ a * g a ∂ν) + c ^ 2 * ∫ a, ρ a ∂ν := by
          rw [integral_sub h2 hmul1, integral_const_mul, integral_const_mul]
  have hquad : ∀ c : ℝ, 0 ≤ (∫ a, ρ a ∂ν) * (c * c)
      + (-2 * ∫ a, ρ a * g a ∂ν) * c + ∫ a, ρ a * g a ^ 2 ∂ν := by
    intro c
    have hnn : 0 ≤ ∫ a, ρ a * (g a - c) ^ 2 ∂ν :=
      integral_nonneg fun a => mul_nonneg (hρ0 a) (sq_nonneg _)
    rw [hexp c] at hnn
    nlinarith only [hnn]
  have hdisc := discrim_le_zero hquad
  rw [discrim] at hdisc
  have ha : 0 ≤ ∫ a, ρ a ∂ν := integral_nonneg hρ0
  have hc : 0 ≤ ∫ a, ρ a * g a ^ 2 ∂ν := integral_nonneg fun a => mul_nonneg (hρ0 a) (sq_nonneg _)
  nlinarith only [hdisc, ha, hc]

/-- Almost every sample admits the two weighted integrability facts that the
`L²` bound on a mollification consumes. -/
theorem ae_integrable_weighted_realize {P : ProbabilityMeasure (ShellSeq d)}
    [VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure]
    {w : Vec d → ℝ} (hw0 : ∀ y, 0 ≤ w y) (hwc : Continuous w) (hwi : Integrable w volume)
    {X : ShellSeq d → HilbertVec d} (hXm : StronglyMeasurable X) (hX : MemLp X 2 P.toMeasure) :
    ∀ᵐ ω ∂P.toMeasure, Integrable (fun y => w y * ‖X (y +ᵥ ω)‖ ^ 2) volume ∧
      Integrable (fun y => w y * ‖X (y +ᵥ ω)‖) volume := by
  have hnormsq : StronglyMeasurable fun ω => ‖X ω‖ ^ 2 := hXm.norm.pow 2
  have hsq : Integrable (fun ω => ‖X ω‖ ^ 2) P.toMeasure :=
    (memLp_two_iff_integrable_sq_norm hX.aestronglyMeasurable).1 hX
  have hprod := integrable_prod_weighted_comp_vadd (P := P) hwc hwi hnormsq hsq
  filter_upwards [hprod.prod_right_ae] with ω hω
  refine ⟨hω, ?_⟩
  have hsum : Integrable (fun y => w y * ‖X (y +ᵥ ω)‖ ^ 2 + w y) volume := hω.add hwi
  have hdom : Integrable (fun y => (1 / 2 : ℝ) * (w y * ‖X (y +ᵥ ω)‖ ^ 2 + w y)) volume :=
    hsum.const_mul _
  refine Integrable.mono' hdom ?_ ?_
  · have hsm : StronglyMeasurable (fun y => w y * ‖X (y +ᵥ ω)‖) :=
      hwc.stronglyMeasurable.mul
        (hXm.comp_measurable
          (SuperdiffusionCLT.Section3.Terms.measurable_vadd_const_sample_shellSeq ω)).norm
    exact hsm.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun y => ?_
    have h0 := hw0 y
    have hn := norm_nonneg (X (y +ᵥ ω))
    have hkey : 0 ≤ w y * (‖X (y +ᵥ ω)‖ - 1) ^ 2 := mul_nonneg h0 (sq_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 hn)]
    nlinarith only [hkey]

/-- The pointwise square bound behind the `L²` estimates on a mollification. -/
theorem normSq_mollify_le {P : ProbabilityMeasure (ShellSeq d)}
    [VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure]
    {θ : Vec d → ℝ} (hθc : Continuous θ) (hθi : Integrable θ volume)
    {X : ShellSeq d → HilbertVec d} (hXm : StronglyMeasurable X) (hX : MemLp X 2 P.toMeasure) :
    ∀ᵐ ω ∂P.toMeasure, ‖mollify θ X ω‖ ^ 2
      ≤ (∫ y, |θ y|) * ∫ y, |θ y| * ‖X (y +ᵥ ω)‖ ^ 2 := by
  filter_upwards [ae_integrable_weighted_realize (P := P) (w := fun y => |θ y|)
    (fun y => abs_nonneg (θ y)) hθc.abs hθi.abs hXm hX] with ω hω
  have hb : ‖mollify θ X ω‖ ≤ ∫ y, |θ y| * ‖X (y +ᵥ ω)‖ := by
    refine (norm_integral_le_integral_norm (fun y => θ y • X (y +ᵥ ω))).trans (le_of_eq ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [norm_smul, Real.norm_eq_abs]
  have hjensen := sq_weighted_integral_le (ν := (volume : Measure (Vec d)))
    (ρ := fun y => |θ y|) (g := fun y => ‖X (y +ᵥ ω)‖) (fun y => abs_nonneg (θ y))
    hθi.abs hω.2 hω.1
  calc ‖mollify θ X ω‖ ^ 2
      ≤ (∫ y, |θ y| * ‖X (y +ᵥ ω)‖) ^ 2 := by
        nlinarith only [norm_nonneg (mollify θ X ω), hb]
    _ ≤ (∫ y, |θ y|) * ∫ y, |θ y| * ‖X (y +ᵥ ω)‖ ^ 2 := hjensen

/-- **Item 1, membership**: mollification by an integrable kernel preserves the
stationary `L²` layer. -/
theorem memLp_mollify {P : ProbabilityMeasure (ShellSeq d)}
    [VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure]
    {θ : Vec d → ℝ} (hθc : Continuous θ) (hθi : Integrable θ volume)
    {X : ShellSeq d → HilbertVec d} (hXm : StronglyMeasurable X) (hX : MemLp X 2 P.toMeasure) :
    MemLp (mollify θ X) 2 P.toMeasure := by
  have hsm := stronglyMeasurable_mollify hθc hXm
  have hnormsq : StronglyMeasurable fun ω => ‖X ω‖ ^ 2 := hXm.norm.pow 2
  have hsq : Integrable (fun ω => ‖X ω‖ ^ 2) P.toMeasure :=
    (memLp_two_iff_integrable_sq_norm hX.aestronglyMeasurable).1 hX
  have hprod := integrable_prod_weighted_comp_vadd (P := P) hθc.abs hθi.abs hnormsq hsq
  have hdom : Integrable
      (fun ω => (∫ y, |θ y|) * ∫ y, |θ y| * ‖X (y +ᵥ ω)‖ ^ 2) P.toMeasure :=
    hprod.integral_prod_left.const_mul _
  refine (memLp_two_iff_integrable_sq_norm hsm.aestronglyMeasurable).2 ?_
  refine Integrable.mono' hdom (hsm.norm.pow 2).aestronglyMeasurable ?_
  filter_upwards [normSq_mollify_le (P := P) hθc hθi hXm hX] with ω hω
  convert hω using 1
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]

/-! ## The `L²` norm bound -/

/-! ## Translates of horizontal gradients -/

section Translate

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable [AddAction (Vec d) Ω] [MeasurableConstVAdd (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]

end Translate

/-! ## The mollification pairing identity -/

section Pairing

/-- For almost every sample, the shifted integrand of the mollification is
Bochner integrable in the space variable. -/
theorem ae_integrable_smul_realize {P : ProbabilityMeasure (ShellSeq d)}
    [VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure]
    {θ : Vec d → ℝ} (hθc : Continuous θ) (hθi : Integrable θ volume)
    {X : ShellSeq d → HilbertVec d} (hXm : StronglyMeasurable X) (hX : MemLp X 2 P.toMeasure) :
    ∀ᵐ ω ∂P.toMeasure, Integrable (fun y => θ y • X (y +ᵥ ω)) volume := by
  filter_upwards [ae_integrable_weighted_realize (P := P) (w := fun y => |θ y|)
    (fun y => abs_nonneg (θ y)) hθc.abs hθi.abs hXm hX] with ω hω
  refine Integrable.mono' hω.2 ?_ ?_
  · have hsm2 : StronglyMeasurable fun y : Vec d => X (y +ᵥ ω) :=
      hXm.comp_measurable
        (SuperdiffusionCLT.Section3.Terms.measurable_vadd_const_sample_shellSeq ω)
    exact (hθc.stronglyMeasurable.smul hsm2).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun y => ?_
    rw [norm_smul, Real.norm_eq_abs]
