/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.Section2.Annealed.Symmetry
public import Homogenization.Book.Ch04.Theorems.DilationLaw
public import Homogenization.Book.Ch05.Theorems.Section55.AnnealedConvergence

/-!
# The cutoff law rebased to unit range of dependence

The proof of Lemma `l.b.ell.homogenization` of the paper applies the high-contrast
entry theorem of [AK] to the infrared cutoff field `a_k = nu Id + k_k`. It records
exactly which properties of the cutoff field the entry theorem consumes:

> The cutoff field `a_k` is stationary, has range of dependence `C 3^k`, and
> satisfies the high-contrast ellipticity envelope required in
> [AK, Theorem 3.1] with contrast bounded by a dimensional polynomial in
> `nu^{-1} k`.

`CoarseGraining` states its entry theorem
(`Book.Ch05.Section55.annealedPerturbativeEntry_homogenizationScale`) for a law
whose range of dependence is **one**. This module performs the rescaling that
turns the printed range `3^m sqrt d` into a unit range, and assembles the
structural half of the entry theorem's hypotheses for the rescaled law.

## The dilation factor

The range of dependence of the shell `j_n` is `3^n sqrt d` (assumption J1), so
the cutoff `k_m = sum_{n <= m} j_n` has range `3^m sqrt d`, which exceeds `3^m`
by the factor `sqrt d`. Dilating by `3^m` alone would therefore not reach unit
range. The dilation used here is by `3^(m + triadicOffset d)`, where
`triadicOffset d` is the least natural number `t` with `sqrt d <= 3 ^ t`; the
cost is an additive dimensional offset in the scale bookkeeping, and the
triadic cube correspondence is preserved because the offset is again a triadic
power.

## What is proved and what is assumed

Three of the four structural assumptions are transported outright: stationarity
from `restrictionStationaryLaw_cutoffLaw`, isotropy and adjoint invariance from
the two halves of J4. The fourth, unit range of dependence, is reduced here to
the single statement `CutoffRangeDependence`, which is the range of dependence
of the *unrescaled* cutoff law in `CoarseGraining`'s pointwise-restriction
lane. That statement is not proved in this module: the assumption J1 is
phrased for the integral-generated local sigma-field
`ShellField.lihLocalSigma`, and the only comparison available between the two
lanes is `Homogenization.localSigmaR_le_restrictionSigmaR`, which runs in the
direction opposite to the one a transport of J1 would need.

The quantitative coarse-grained ellipticity hypothesis is split the same way:
the eleven parameter conditions are supplied from the parameter record, and the
two moment-integrability conditions are collected in `CutoffEllipticityMoments`.
These are the conditions that the size estimates of the paper
(`l.ellip.k.scales.estimates`, `e.km.Ltwo.size` and the envelope
`e.Enaught.mixing`) have to deliver; they are stated here, not proved.

This module assembles the hypotheses of the entry theorem for the rebased law; it does not
apply the theorem. One further obligation is open: no declaration bounds the initial-scale contrast
`widetildeThetaAtScale (rebasedCutoffLaw nu m P) 0` by a dimensional polynomial
in `nu^{-1} m`, although the entry scale of the theorem is defined through that
quantity and the bound printed in the paper asks for exactly such a
polynomial.

## Main definitions

* `triadicOffset`: a natural number `t` with `sqrt d <= 3 ^ t`.
* `IsRangeDependentR`: range of dependence at a general range, in
  `CoarseGraining`'s pointwise-restriction lane.
* `rebasedCutoffLaw`: the cutoff law pushed forward by the dilation by
  `3 ^ (m + triadicOffset d)`.
* `CutoffRangeDependence`: the range of dependence of the cutoff law at the
  printed range `3 ^ m sqrt d`.
* `CutoffEllipticityMoments`: the two multiscale ellipticity moment bounds of
  `CoarseGraining`'s quantitative coarse-grained ellipticity, at the rebased
  law.

## Main results

* `sqrt_natCast_le_pow_triadicOffset`: `sqrt d <= 3 ^ triadicOffset d`.
* `isRestrictionUnitRangeDependentR_restrictionScaleNormalizedLaw`: a law of
  range `R` becomes unit range after dilation by any `3 ^ k` with `R <= 3 ^ k`.
* `restrictionLawCarrier_rebasedCutoffLaw`: the rebased law is a Chapter 4 law
  carrier.
* `restrictionStationaryLaw_rebasedCutoffLaw`,
  `restrictionIsotropicLaw_rebasedCutoffLaw`,
  `restrictionAdjointInvariantLaw_rebasedCutoffLaw`: the three transported
  structural assumptions.
* `restrictionStructuralLaw_rebasedCutoffLaw`: the full structural package,
  given `CutoffRangeDependence`.
* `quantitativeCoarseGrainedEllipticity_rebasedCutoffLaw`: the
  quantitative ellipticity package built from a parameter record and the two
  moment bounds.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.HighContrast

open Homogenization MeasureTheory ProbabilityTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## The dimensional triadic offset

The shells of the marginal stream are separated in the Euclidean metric, at the
range `3 ^ n sqrt d` of J1, while `CoarseGraining` separates observation sets in
the sup metric. Sup separation is the stronger of the two, so the offset only
has to absorb the factor `sqrt d`. -/

/-- A natural number `t` with `sqrt d <= 3 ^ t`, namely `ceil(log_3 sqrt d)`:
the dimensional offset in the dilation that turns the range `3 ^ m sqrt d` of
the cutoff into a unit range. Minimality is not proved and not used. -/
def triadicOffset (d : ℕ) : ℕ :=
  ⌈Real.logb 3 (Real.sqrt (d : ℝ))⌉₊

/-- The defining property of the dimensional offset. -/
theorem sqrt_natCast_le_pow_triadicOffset (d : ℕ) :
    Real.sqrt (d : ℝ) ≤ (3 : ℝ) ^ triadicOffset d := by
  rcases le_or_gt (Real.sqrt (d : ℝ)) 1 with h | h
  · exact h.trans (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3))
  · have hpos : (0 : ℝ) < Real.sqrt (d : ℝ) := lt_trans one_pos h
    calc Real.sqrt (d : ℝ)
        = (3 : ℝ) ^ Real.logb 3 (Real.sqrt (d : ℝ)) :=
          (Real.rpow_logb (by norm_num) (by norm_num) hpos).symm
      _ ≤ (3 : ℝ) ^ ((triadicOffset d : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
      _ = (3 : ℝ) ^ triadicOffset d := by rw [Real.rpow_natCast]

/-- The printed range `3 ^ m sqrt d` of the cutoff field is at most the dilation
factor `3 ^ (m + triadicOffset d)`. -/
theorem pow_mul_sqrt_le_pow_add_triadicOffset (d m : ℕ) :
    (3 : ℝ) ^ m * Real.sqrt (d : ℝ) ≤ (3 : ℝ) ^ (m + triadicOffset d) := by
  rw [pow_add]
  exact mul_le_mul_of_nonneg_left (sqrt_natCast_le_pow_triadicOffset d) (by positivity)

/-! ## Range of dependence at a general range

`CoarseGraining`'s `IsRestrictionUnitRangeDependentR` is the range-one instance
of the following predicate, and the dilation by `3 ^ k` divides the range by
`3 ^ k`. -/

/-- A carrier law has **range of dependence `R`** if the pointwise-restriction
sigma-algebras of any two measurable sets separated by `R` in the sup metric are
independent. The range-one instance is `CoarseGraining`'s
`IsRestrictionUnitRangeDependentR`. -/
def IsRangeDependentR (R : ℝ) (P : Book.Ch04.RestrictionCoeffLaw d) : Prop :=
  ∀ (U V : Set (Vec d)) (hU : MeasurableSet U) (hV : MeasurableSet V),
    (∀ ⦃x y : Vec d⦄, x ∈ U → y ∈ V → R ≤ dist x y) →
      Indep (RestrictionSigmaR U hU) (RestrictionSigmaR V hV) P

/-- Range of dependence is monotone: a smaller range is a stronger statement. -/
theorem IsRangeDependentR.mono {R R' : ℝ} {P : Book.Ch04.RestrictionCoeffLaw d}
    (hP : IsRangeDependentR R P) (hRR' : R ≤ R') : IsRangeDependentR R' P :=
  fun U V hU hV hsep ↦ hP U V hU hV fun _ _ hx hy ↦ hRR'.trans (hsep hx hy)

/-- Independence of two sub-sigma-algebras transfers to a pushforward law along
a measurable map, provided both are below the ambient sigma-algebra of the
target. -/
private theorem indep_map_of_comap {alpha beta : Type*} [malpha : MeasurableSpace alpha]
    [mbeta : MeasurableSpace beta] {mu : Measure alpha} {f : alpha → beta}
    (hf : Measurable f) {m₁ m₂ : MeasurableSpace beta}
    (h₁ : m₁ ≤ mbeta) (h₂ : m₂ ≤ mbeta)
    (h : @Indep alpha (m₁.comap f) (m₂.comap f) malpha mu) :
    @Indep beta m₁ m₂ mbeta (@Measure.map alpha beta malpha mbeta f mu) := by
  refine (@Indep_iff beta m₁ m₂ mbeta (@Measure.map alpha beta malpha mbeta f mu)).2 ?_
  intro s t hs ht
  have hs' : @MeasurableSet beta mbeta s := h₁ s hs
  have ht' : @MeasurableSet beta mbeta t := h₂ t ht
  have hst' : @MeasurableSet beta mbeta (s ∩ t) := hs'.inter ht'
  rw [@Measure.map_apply alpha beta malpha mbeta mu f hf (s ∩ t) hst',
    @Measure.map_apply alpha beta malpha mbeta mu f hf s hs',
    @Measure.map_apply alpha beta malpha mbeta mu f hf t ht', Set.preimage_inter]
  exact (@Indep_iff alpha (m₁.comap f) (m₂.comap f) malpha mu).1 h _ _
    ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩

/-- The triadic dilation scales distances by `3 ^ k`. -/
private theorem dist_triadicDilateVec (k : ℕ) (x y : Vec d) :
    dist (triadicDilateVec k x) (triadicDilateVec k y) = (3 : ℝ) ^ k * dist x y := by
  have hsub : triadicDilateVec k x - triadicDilateVec k y = ((3 : ℝ) ^ k) • (x - y) := by
    funext i
    simp only [triadicDilateVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [dist_eq_norm, dist_eq_norm, hsub, norm_smul_of_nonneg (by positivity)]

/-- Dilating two unit-separated sets by `3 ^ k` separates them by any `R` with
`R ≤ 3 ^ k`. -/
private theorem le_dist_of_areUnitSeparated_triadicDilateSet {R : ℝ} {U V : Set (Vec d)}
    (hUV : AreUnitSeparated U V) (k : ℕ) (hR : R ≤ (3 : ℝ) ^ k) :
    ∀ ⦃x y : Vec d⦄, x ∈ triadicDilateSet k U → y ∈ triadicDilateSet k V →
      R ≤ dist x y := by
  rintro x y ⟨x₀, hx₀, rfl⟩ ⟨y₀, hy₀, rfl⟩
  rw [dist_triadicDilateVec]
  calc R ≤ (3 : ℝ) ^ k := hR
    _ = (3 : ℝ) ^ k * 1 := (mul_one _).symm
    _ ≤ (3 : ℝ) ^ k * dist x₀ y₀ :=
        mul_le_mul_of_nonneg_left (hUV hx₀ hy₀) (by positivity)

/-- **Rescaling to unit range.** A law of range of dependence `R` becomes a
unit-range law after the triadic scale normalization by any `3 ^ k` with
`R ≤ 3 ^ k`. This is the range-of-dependence half of the rescaling in the paper. -/
theorem isRestrictionUnitRangeDependentR_restrictionScaleNormalizedLaw {R : ℝ}
    {P : Book.Ch04.RestrictionCoeffLaw d} (hP : IsRangeDependentR R P) (k : ℕ)
    (hR : R ≤ (3 : ℝ) ^ k) :
    Book.Ch04.RestrictionUnitRangeDependentLaw
      (Book.Ch04.restrictionScaleNormalizedLaw k P) := by
  intro U V hU hV hUV
  have hUk : MeasurableSet (triadicDilateSet k U) :=
    Book.Ch04.measurableSet_triadicDilateSet k hU
  have hVk : MeasurableSet (triadicDilateSet k V) :=
    Book.Ch04.measurableSet_triadicDilateSet k hV
  have hIndep : Indep (RestrictionSigmaR (triadicDilateSet k U) hUk)
      (RestrictionSigmaR (triadicDilateSet k V) hVk) P :=
    hP _ _ hUk hVk (le_dist_of_areUnitSeparated_triadicDilateSet hUV k hR)
  have hUle :
      MeasurableSpace.comap (rescaleReg (d := d) k) (RestrictionSigmaR U hU) ≤
        RestrictionSigmaR (triadicDilateSet k U) hUk :=
    (Book.Ch04.measurable_rescaleReg_restrictionSigmaR (d := d) k U hU).comap_le
  have hVle :
      MeasurableSpace.comap (rescaleReg (d := d) k) (RestrictionSigmaR V hV) ≤
        RestrictionSigmaR (triadicDilateSet k V) hVk :=
    (Book.Ch04.measurable_rescaleReg_restrictionSigmaR (d := d) k V hV).comap_le
  have hComap :
      Indep (MeasurableSpace.comap (rescaleReg (d := d) k) (RestrictionSigmaR U hU))
        (MeasurableSpace.comap (rescaleReg (d := d) k) (RestrictionSigmaR V hV)) P :=
    indep_of_indep_of_le_right (indep_of_indep_of_le_left hIndep hUle) hVle
  rw [Book.Ch04.restrictionScaleNormalizedLaw_eq_map_rescaleReg]
  exact indep_map_of_comap (measurable_rescaleReg k)
    (restrictionSigmaR_le U hU) (restrictionSigmaR_le V hV) hComap

/-! ## The rebased cutoff law -/

variable (nu : ℝ) (m : ℕ) (P : ProbabilityMeasure (ShellSeq d))

/-- The law of the infrared cutoff `a_m = nu Id + k_m` after the dilation
`x ↦ 3 ^ (m + triadicOffset d) x` that brings its range of dependence
`3 ^ m sqrt d` down to at most one. It is `CoarseGraining`'s triadic scale
normalization applied to `cutoffLaw`, so that library's transport lemmas apply
verbatim. -/
def rebasedCutoffLaw : Book.Ch04.RestrictionCoeffLaw d :=
  Book.Ch04.restrictionScaleNormalizedLaw (m + triadicOffset d)
    (cutoffLaw (d := d) nu m P)

/-- The rebased cutoff law is the pushforward of the cutoff law along the
carrier rescaling `a ↦ a (3 ^ (m + triadicOffset d) • ·)`. -/
theorem rebasedCutoffLaw_eq_map :
    rebasedCutoffLaw nu m P =
      Measure.map (rescaleReg (d := d) (m + triadicOffset d)) (cutoffLaw (d := d) nu m P) :=
  Book.Ch04.restrictionScaleNormalizedLaw_eq_map_rescaleReg _ _

/-- The rebased cutoff law is a Chapter 4 law carrier. -/
theorem restrictionLawCarrier_rebasedCutoffLaw {nu : ℝ} (hnu : 0 < nu) (m : ℕ)
    (P : ProbabilityMeasure (ShellSeq d)) :
    Book.Ch04.RestrictionLawCarrier (rebasedCutoffLaw nu m P) :=
  Book.Ch04.RestrictionLawCarrier.scaleNormalized
    (restrictionLawCarrier_cutoffLaw hnu m P) _

/-- Stationarity of the rebased cutoff law, transported from the stationarity of
the cutoff law under integer translations. -/
theorem restrictionStationaryLaw_rebasedCutoffLaw {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (nu : ℝ) (m : ℕ) :
    Book.Ch04.RestrictionStationaryLaw (rebasedCutoffLaw nu m P) :=
  Book.Ch04.RestrictionStationaryLaw.scaleNormalized
    (restrictionStationaryLaw_cutoffLaw hPrefix hJ2 nu m) _

/-- Isotropy of the rebased cutoff law, transported from the hyperoctahedral
half of J4. -/
theorem restrictionIsotropicLaw_rebasedCutoffLaw {P : ProbabilityMeasure (ShellSeq d)}
    (hJ4 : ShellLawJ4 d P) (nu : ℝ) (m : ℕ) :
    Book.Ch04.RestrictionIsotropicLaw (rebasedCutoffLaw nu m P) :=
  Book.Ch04.RestrictionIsotropicLaw.scaleNormalized
    (isIsotropicInLawR_cutoffLaw nu m hJ4) _

/-- Adjoint invariance of the rebased cutoff law, transported from the negation
half of J4. -/
theorem restrictionAdjointInvariantLaw_rebasedCutoffLaw
    {P : ProbabilityMeasure (ShellSeq d)} (hJ4 : ShellLawJ4 d P) (nu : ℝ) (m : ℕ) :
    Book.Ch04.RestrictionAdjointInvariantLaw (rebasedCutoffLaw nu m P) :=
  Book.Ch04.RestrictionAdjointInvariantLaw.scaleNormalized
    (isAdjointInvariantInLawR_cutoffLaw nu m hJ4) _

/-- The range of dependence of the cutoff law at the range printed in the paper,
in the pointwise-restriction lane of `CoarseGraining`. The shell `j_n` has range
`3 ^ n sqrt d` by J1 and `k_m` is the sum of the shells `j_0, …, j_m`, so this
is the range of `a_m = nu Id + k_m`. -/
def CutoffRangeDependence : Prop :=
  IsRangeDependentR ((3 : ℝ) ^ m * Real.sqrt (d : ℝ)) (cutoffLaw (d := d) nu m P)

/-- Unit range of dependence of the rebased cutoff law: the dilation factor
`3 ^ (m + triadicOffset d)` dominates the range `3 ^ m sqrt d`. -/
theorem restrictionUnitRangeDependentLaw_rebasedCutoffLaw
    {nu : ℝ} {m : ℕ} {P : ProbabilityMeasure (ShellSeq d)}
    (hrange : CutoffRangeDependence nu m P) :
    Book.Ch04.RestrictionUnitRangeDependentLaw (rebasedCutoffLaw nu m P) :=
  isRestrictionUnitRangeDependentR_restrictionScaleNormalizedLaw hrange _
    (pow_mul_sqrt_le_pow_add_triadicOffset d m)

/-- **The structural law of the rebased cutoff field.** Stationarity, unit range
of dependence, isotropy and adjoint invariance: the four structural assumptions
that `CoarseGraining`'s high-contrast entry theorem places on a coefficient law,
verified for the cutoff law rebased to unit range. Only the range of dependence
is an assumption; the other three come from the shell-law prefix, J2 and J4. -/
theorem restrictionStructuralLaw_rebasedCutoffLaw
    {nu : ℝ} {m : ℕ} {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ4 : ShellLawJ4 d P)
    (hrange : CutoffRangeDependence nu m P) :
    Book.Ch04.RestrictionStructuralLaw (rebasedCutoffLaw nu m P) where
  stationary := restrictionStationaryLaw_rebasedCutoffLaw hPrefix hJ2 nu m
  unit_range := restrictionUnitRangeDependentLaw_rebasedCutoffLaw hrange
  isotropic := restrictionIsotropicLaw_rebasedCutoffLaw hJ4 nu m
  adjoint_invariant := restrictionAdjointInvariantLaw_rebasedCutoffLaw hJ4 nu m

/-! ## The quantitative coarse-grained ellipticity of the rebased law

The remaining hypothesis of the entry theorem is `CoarseGraining`'s
`QuantitativeCoarseGrainedEllipticity`: eleven conditions on the parameters
`(sUpper, sLower, xi)`, which are conditions on the parameter record alone, and
two moment bounds on the multiscale ellipticity observables of the unit cube
under the law. The first group is discharged here; the second is the content of
the size estimates of the paper and is stated, not proved. -/

/-- The two moment conditions of `CoarseGraining`'s quantitative coarse-grained
ellipticity at the rebased cutoff law: the `xi`-th moment of the upper
multiscale ellipticity observable of the unit cube, and the `xi`-th moment of
the reciprocal of the lower one. These are the quantitative form of the
ellipticity envelope of the paper, and they are what the cutoff size
estimates `e.kmn.Linfty` and `e.km.Ltwo.size` together with
the envelope `e.Enaught.mixing` have to supply. -/
def CutoffEllipticityMoments [NeZero d] (sUpper sLower : ℝ) (xi : ℕ) : Prop :=
  Integrable (fun a : RegCoeffField d ↦
      Book.Ch04.LambdaSqCoeffField (originCube d (0 : ℤ)) sUpper (.finite 1) a ^ xi)
    (rebasedCutoffLaw nu m P) ∧
  Integrable (fun a : RegCoeffField d ↦
      (Book.Ch04.lambdaSqCoeffField (originCube d (0 : ℤ)) sLower (.finite 1) a)⁻¹ ^ xi)
    (rebasedCutoffLaw nu m P)

/-- The quantitative coarse-grained ellipticity package of the rebased cutoff
law, assembled from a parameter record and the two moment bounds. -/
def quantitativeCoarseGrainedEllipticity_rebasedCutoffLaw [NeZero d]
    (params : Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d)
    (hmom : CutoffEllipticityMoments nu m P params.sUpper params.sLower params.xi) :
    Book.Ch05.QuantitativeCoarseGrainedEllipticity (rebasedCutoffLaw nu m P) where
  sUpper := params.sUpper
  sLower := params.sLower
  xi := params.xi
  two_le_dim := params.two_le_dim
  sUpper_nonneg := params.sUpper_nonneg
  sUpper_lt_one := params.sUpper_lt_one
  sLower_nonneg := params.sLower_nonneg
  sLower_lt_one := params.sLower_lt_one
  xi_gt_two_mul_dim := params.xi_gt_two_mul_dim
  sum_lt_one := params.sum_lt_one
  dim_div_xi_lt_min := params.dim_div_xi_lt_min
  upper_moment_integrable := hmom.1
  lower_inv_moment_integrable := hmom.2

end

end SuperdiffusionCLT.Section3.HighContrast
