/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Probability.RealizationSecondConjunct

/-!
# The orbit smear is a stationary horizontal gradient

This module continues `SuperdiffusionCLT.Probability.RealizationSecondConjunct`.
That module reduces the second conjunct of the stationary-potential realization to the
single per-sample statement `hpair`, which rests on two analytic facts:

* the horizontal-gradient property of the smear — the smeared pair
  `(smearScalar θ f, smearGrad θ f)` is a strong horizontal gradient, for a smooth compactly
  supported test function `θ` and a square-integrable field `f`; and
* the pairing transfer — the Fubini identity converting the `L²(Ω)`-orthogonality against the
  smeared gradient into the vanishing of the per-sample divergence pairing.

Here we land the *qualitative* half of the first fact in the case where the test field `f` is
bounded and measurable — which is all that is needed, because bounded functions are dense in
`L²(Ω)` and the orthogonality is linear in `f`.  Concretely:

* the smeared scalar `smearScalar θ f` and each coordinate of `smearGrad θ f` are a.e. strongly
  measurable and square integrable (`aestronglyMeasurable_smearScalar`, `memLp_smearScalar`,
  `memLp_smearGrad`), so the pair can be read as an element of `ScalarL2 μ × VectorL2 d μ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Homogenization
open SuperdiffusionCLT.Section2.Cutoff
open scoped ENNReal Topology

noncomputable section

namespace SuperdiffusionCLT.Probability.Stationary

variable {d : ℕ}

/-! ## Joint measurability of the orbit shift -/

/-- The uncurried orbit shift `(ω, y) ↦ (-y) +ᵥ ω` is measurable at the concrete carrier
`ShellSeq d`, in the argument order used by the smearing integrals.  It is
`measurable_vadd_shellSeq` composed with the measurable flip-negation of the second argument. -/
theorem measurable_negVadd_shellSeq :
    Measurable (fun p : ShellSeq d × Vec d => (-p.2) +ᵥ p.1) :=
  (SuperdiffusionCLT.Section3.Terms.measurable_vadd_shellSeq (d := d)).comp
    (measurable_fst.prodMk (measurable_neg.comp measurable_snd))

/-- **A.e. strong measurability of the smeared scalar.**  For a measurable test function `θ`
and a measurable field `f`, the orbit smear `ω ↦ ∫ y, θ y * f ((-y) +ᵥ ω)` is a.e. strongly
measurable.  The joint integrand `(ω, y) ↦ θ y * f ((-y) +ᵥ ω)` is measurable, and the
Bochner integral of a measurable function over the second variable is a.e. strongly
measurable. -/
theorem aestronglyMeasurable_smearScalar {P : ProbabilityMeasure (ShellSeq d)}
    {θ : Vec d → ℝ} {f : ShellSeq d → ℝ}
    (hθm : Measurable θ) (hfm : Measurable f) :
    AEStronglyMeasurable (smearScalar θ f) P.toMeasure := by
  have hjoint : StronglyMeasurable (fun p : ShellSeq d × Vec d => θ p.2 * f ((-p.2) +ᵥ p.1)) :=
    ((hθm.comp measurable_snd).mul
      (hfm.comp (measurable_negVadd_shellSeq (d := d)))).stronglyMeasurable
  have h := hjoint.integral_prod_right' (ν := (volume : Measure (Vec d)))
  exact h.aestronglyMeasurable

/-- **A.e. strong measurability of a coordinate of the smeared gradient.** -/
theorem aestronglyMeasurable_smearGrad_apply {P : ProbabilityMeasure (ShellSeq d)}
    {θ : Vec d → ℝ} {f : ShellSeq d → ℝ}
    (hθ : ContDiff ℝ 1 θ) (hfm : Measurable f) (i : Fin d) :
    AEStronglyMeasurable (fun ω => smearGrad θ f ω i) P.toMeasure := by
  have hdθm : Measurable (fun y : Vec d => fderiv ℝ θ y (Homogenization.basisVec i)) :=
    ((hθ.continuous_fderiv (by simp)).clm_apply continuous_const).measurable
  have hjoint : StronglyMeasurable
      (fun p : ShellSeq d × Vec d =>
        fderiv ℝ θ p.2 (Homogenization.basisVec i) * f ((-p.2) +ᵥ p.1)) :=
    ((hdθm.comp measurable_snd).mul
      (hfm.comp (measurable_negVadd_shellSeq (d := d)))).stronglyMeasurable
  have h := hjoint.integral_prod_right' (ν := (volume : Measure (Vec d)))
  simpa [smearGrad] using h.aestronglyMeasurable

/-! ## Square integrability of the smear for bounded measurable fields -/

/-- **`L²` membership of the smeared scalar for a bounded measurable field.**  If `f` is
measurable and bounded by `Cf` and `θ` is `C¹` with compact support, then `smearScalar θ f` is
bounded by `Cf * ∫ |θ|`, hence square integrable.  The bound is uniform in `ω`, so no Fubini
step is needed here. -/
theorem memLp_smearScalar {P : ProbabilityMeasure (ShellSeq d)}
    {θ : Vec d → ℝ} {f : ShellSeq d → ℝ} {Cf : ℝ}
    (hθ : ContDiff ℝ 1 θ) (hθc : HasCompactSupport θ)
    (hfm : Measurable f) (hf : ∀ ω, |f ω| ≤ Cf) :
    MemLp (smearScalar θ f) 2 P.toMeasure := by
  have hθi : Integrable θ (volume : Measure (Vec d)) :=
    hθ.continuous.integrable_of_hasCompactSupport hθc
  refine MemLp.of_bound (aestronglyMeasurable_smearScalar (P := P) hθ.continuous.measurable hfm)
    (Cf * ∫ y, |θ y|) ?_
  filter_upwards with ω
  calc ‖smearScalar θ f ω‖ = ‖∫ y, θ y * f ((-y) +ᵥ ω)‖ := by
        rw [smearScalar]
    _ ≤ ∫ y, ‖θ y * f ((-y) +ᵥ ω)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, Cf * |θ y| := by
        refine integral_mono_of_nonneg ?_ (hθi.abs.const_mul Cf) ?_
        · filter_upwards with y; positivity
        · filter_upwards with y
          rw [Real.norm_eq_abs, abs_mul]
          calc |θ y| * |f ((-y) +ᵥ ω)| ≤ |θ y| * Cf :=
                mul_le_mul_of_nonneg_left (hf _) (abs_nonneg _)
            _ = Cf * |θ y| := mul_comm _ _
    _ = Cf * ∫ y, |θ y| := integral_const_mul _ _

/-- **`L²` membership of a coordinate of the smeared gradient for a bounded measurable
field.** -/
theorem memLp_smearGrad_apply {P : ProbabilityMeasure (ShellSeq d)}
    {θ : Vec d → ℝ} {f : ShellSeq d → ℝ} {Cf : ℝ}
    (hθ : ContDiff ℝ 1 θ) (hθc : HasCompactSupport θ)
    (hfm : Measurable f) (hf : ∀ ω, |f ω| ≤ Cf) (i : Fin d) :
    MemLp (fun ω => smearGrad θ f ω i) 2 P.toMeasure := by
  have hdθc : HasCompactSupport (fun y : Vec d => fderiv ℝ θ y (Homogenization.basisVec i)) :=
    hθc.fderiv_apply (𝕜 := ℝ) (Homogenization.basisVec i)
  have hdθcont : Continuous (fun y : Vec d => fderiv ℝ θ y (Homogenization.basisVec i)) :=
    (hθ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdθi : Integrable (fun y : Vec d => fderiv ℝ θ y (Homogenization.basisVec i))
      (volume : Measure (Vec d)) :=
    hdθcont.integrable_of_hasCompactSupport hdθc
  refine MemLp.of_bound (aestronglyMeasurable_smearGrad_apply (P := P) hθ hfm i)
    (Cf * ∫ y, |fderiv ℝ θ y (Homogenization.basisVec i)|) ?_
  filter_upwards with ω
  calc ‖smearGrad θ f ω i‖ =
        ‖∫ y, fderiv ℝ θ y (Homogenization.basisVec i) * f ((-y) +ᵥ ω)‖ := by
        rw [smearGrad]
    _ ≤ ∫ y, ‖fderiv ℝ θ y (Homogenization.basisVec i) * f ((-y) +ᵥ ω)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ y, Cf * |fderiv ℝ θ y (Homogenization.basisVec i)| := by
        refine integral_mono_of_nonneg ?_ (hdθi.abs.const_mul Cf) ?_
        · filter_upwards with y; positivity
        · filter_upwards with y
          rw [Real.norm_eq_abs, abs_mul]
          calc |fderiv ℝ θ y (Homogenization.basisVec i)| * |f ((-y) +ᵥ ω)| ≤
                |fderiv ℝ θ y (Homogenization.basisVec i)| * Cf :=
                mul_le_mul_of_nonneg_left (hf _) (abs_nonneg _)
            _ = Cf * |fderiv ℝ θ y (Homogenization.basisVec i)| := mul_comm _ _
    _ = Cf * ∫ y, |fderiv ℝ θ y (Homogenization.basisVec i)| := integral_const_mul _ _

/-- **`L²` membership of the smeared gradient as a `VectorL2 d μ`.**  Packaging the
coordinate-wise statement `memLp_smearGrad_apply` through the Hilbert-vector carrier; this is the
field that the smeared potential's strong horizontal gradient lives in. -/
theorem memLp_smearGrad {P : ProbabilityMeasure (ShellSeq d)}
    {θ : Vec d → ℝ} {f : ShellSeq d → ℝ} {Cf : ℝ}
    (hθ : ContDiff ℝ 1 θ) (hθc : HasCompactSupport θ)
    (hfm : Measurable f) (hf : ∀ ω, |f ω| ≤ Cf) :
    MemLp (fun ω => HilbertVec.ofVec (smearGrad θ f ω)) 2 P.toMeasure := by
  classical
  refine MemLp.of_eval_piLp (fun i => ?_)
  have h := memLp_smearGrad_apply (P := P) hθ hθc hfm hf i
  have hfun : (fun ω : ShellSeq d => HilbertVec.ofVec (smearGrad θ f ω) i) =
      fun ω : ShellSeq d => smearGrad θ f ω i := by
    funext ω
    exact PiLp.toLp_apply 2 (fun _ : Fin d => ℝ) (smearGrad θ f ω) i
  rwa [hfun]

end SuperdiffusionCLT.Probability.Stationary

end
