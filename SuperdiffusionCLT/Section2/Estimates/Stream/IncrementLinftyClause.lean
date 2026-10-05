/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Probability.GammaSigmaHelpers
public import SuperdiffusionCLT.Section2.Norms.CubeLp
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementLinftyLargeCube

/-!
# The `L∞` clause of the estimates on the finite shell increment

This module proves clause (c) of the paper's estimates on the increment
`k_m - k_n`, display `e.kmn.Linfty`: for `n < m ≤ l` the `L∞(cu_l)` carrier of the finite
shell increment is dominated pointwise in the sample by a measurable random variable
with a `Γ₂` tail at the amplitude `C (m-n)^{1/2} (l-n)^{1/2}`.

The carrier is `Section2.Norms.cubeLpENorm (originCube d l) ∞`, the clause's exact
carrier, so this file is the assembly step that turns the large-cube estimate
`IncrementLinftyLargeCube` into the shape of the clause.

## The pointwise enorm identity

`Section2.Norms.CubeLp` measures its fields in the `NormedAddCommGroup (Mat d)`
instance selected by `open scoped Matrix.Norms.L2Operator`, whose norm is
`Homogenization.Book.Ch02.matrixOperatorNorm` (`matrixOperatorNorm_eq_l2_opNorm`).
The pointwise enorm identity
`enorm_eq_ofReal_matrixOperatorNorm` therefore identifies the carrier's
pointwise size with the pointwise bound; it is kept `private` here
because the shared carrier identifications are owned by
`Section2.Norms.CubeCarrierIdents`.

## The carrier domination

The normalized cube measure is supported on the half-open `cubeSet`, where the
pointwise bound
`matrixOperatorNorm_finiteShellIncrement_le_largeCubeIncrementSupBound` holds;
off the support the essential supremum is blind, so the a.e. form of the bound
suffices, and the carrier domination follows from the essential-supremum
reading of `cubeLpENorm` at exponent `∞`.

## The clause and its constant

The witness is the measurable envelope `largeCubeIncrementSupBound n m l`,
whose `Γ₂` tail is `isBigOWith_gammaSigma_largeCubeIncrementSupBound` at the
amplitude `largeCubeLinftyConst d (m-n)^{1/2} (l-n)^{1/2}`. For a nonnegative
random variable the one-sided tail predicate and the absolute-value predicate
`IsBigO` agree (`isBigOWith_iff_isBigO_of_nonneg`),
and `IsBigO.mono_scale` rescales the tail to any larger amplitude, so the
shape `C (m-n)^{1/2} (l-n)^{1/2}` is reached exactly for

`C ≥ largeCubeLinftyConst d`,

which is the constant stated here explicitly. The printed proof (see the proof of
`e.kmn.Linfty`) reaches the same shape by its union bound over the sub-cube centres
of `3^n ℤ^d ∩ cu_l`, which is the argument that the envelope already
contains; the printed constant is again absorbed into `C`.

## Main results

* `cubeLpENorm_infty_finiteShellIncrement_le_largeCubeIncrementSupBound`.
* `exists_witness_cubeLpENormInfty_finiteShellIncrement`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Estimates.Stream

open MeasureTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Probability
open scoped ENNReal
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}
variable {P : ProbabilityMeasure (ShellSeq d)}

/-! ## The pointwise enorm of the pointwise size -/

private theorem enorm_eq_ofReal_matrixOperatorNorm (A : Mat d) :
    ‖A‖ₑ = ENNReal.ofReal (matrixOperatorNorm A) := by
  rw [← ofReal_norm, matrixOperatorNorm_eq_l2_opNorm]

/-! ## The carrier domination -/

/-- **The `L∞` carrier of the clause is dominated by the
large-cube envelope.** For every sample, every `n ≤ l` and every `m`,

`cubeLpENorm (cu_l) ∞ (k_m - k_n) ≤ ofReal (largeCubeIncrementSupBound n m l omega)`,

the pointwise bound
`matrixOperatorNorm_finiteShellIncrement_le_largeCubeIncrementSupBound`
(read on the half-open cube `cubeSet (originCube d l)`)
transported through the essential-supremum reading of `cubeLpENorm` at
exponent `∞`: the normalized cube measure is carried by the half-open cube, so
the pointwise enorm
`‖finiteShellIncrement omega n m x‖ₑ = ofReal (matrixOperatorNorm …)`
is converted from a bound on the carrier to an almost-everywhere bound. -/
theorem cubeLpENorm_infty_finiteShellIncrement_le_largeCubeIncrementSupBound
    (omega : ShellSeq d) {n m l : ℕ} (hnl : n ≤ l) :
    cubeLpENorm (originCube d (l : ℤ)) ∞
      (fun x => finiteShellIncrement omega n m x) ≤
      ENNReal.ofReal (largeCubeIncrementSupBound n m l omega) := by
  have hae : ∀ᵐ x ∂(normalizedCubeMeasure (originCube d (l : ℤ))),
      ‖finiteShellIncrement omega n m x‖ₑ ≤
        ENNReal.ofReal (largeCubeIncrementSupBound n m l omega) := by
    have h0 : ∀ᵐ x ∂(volume.restrict (cubeSet (originCube d (l : ℤ)))),
        ‖finiteShellIncrement omega n m x‖ₑ ≤
          ENNReal.ofReal (largeCubeIncrementSupBound n m l omega) := by
      filter_upwards
        [ae_restrict_mem (measurableSet_cubeSet (originCube d (l : ℤ)))]
        with x hx
      rw [enorm_eq_ofReal_matrixOperatorNorm]
      exact ENNReal.ofReal_le_ofReal
        (matrixOperatorNorm_finiteShellIncrement_le_largeCubeIncrementSupBound
          omega hnl hx)
    exact Measure.ae_smul_measure h0 _
  show eLpNorm
    (fun x : Vec d => finiteShellIncrement omega n m x) ∞
    (normalizedCubeMeasure (originCube d (l : ℤ))) ≤ _
  have hcont : Continuous (fun x : Vec d ↦ finiteShellIncrement omega n m x) := by
    have hfun : (fun x : Vec d ↦ finiteShellIncrement omega n m x) =
        fun x : Vec d ↦ ∑ k ∈ Finset.Ioc n m, (omega k) x := by
      funext x
      rw [finiteShellIncrement_apply]
      rfl
    rw [hfun]
    exact continuous_finsetSum _ fun k _ ↦ (omega k).1.1.continuous
  rw [eLpNorm_exponent_top hcont.aestronglyMeasurable]
  exact eLpNormEssSup_le_of_ae_enorm_bound hae

/-! ## The clause -/

/-- **The `L∞` clause**: for `n < m ≤ l` there is
a measurable witness `X` with a `Γ₂` tail at the amplitude
`C (m-n)^{1/2} (l-n)^{1/2}` and, pointwise in the sample,

`cubeLpENorm (cu_l) ∞ (k_m - k_n) ≤ ofReal (X omega)`.

The witness is `largeCubeIncrementSupBound n m l` (measurable), whose
`Γ₂` tail is `isBigOWith_gammaSigma_largeCubeIncrementSupBound` at the
amplitude `largeCubeLinftyConst d (m-n)^{1/2} (l-n)^{1/2}`; the nonnegativity
of the envelope converts the `IsBigOWith` into the `IsBigO` of the
clause (`isBigOWith_iff_isBigO_of_nonneg`), and the amplitude is rescaled to
the required shape by `IsBigO.mono_scale`. The constant is therefore explicit:

`C ≥ largeCubeLinftyConst d = streamLinftyConst d * √(3 d log 3)`,

the dimensional constant of the envelope. The hypothesis `hC` carries
the only content the existentially chosen `C` always has: a
tail relation at a negative amplitude is refuted by the same clause, because
its pointwise domination forces the witness to dominate a nonzero carrier
while a nonpositive amplitude would force it under the tail threshold
almost everywhere, so the existentially quantified `C` is
reached here by the monotone rescaling and never by a smaller choice. The
Sobolev data `s`, `p` and the `J1` law are carried in the
signature for shape compatibility with the quantifier structure of the clause; this
clause does not depend on them. -/
theorem exists_witness_cubeLpENormInfty_finiteShellIncrement
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1 d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (C : ℝ) (s p : ℝ)
    (hs : 0 < s) (hsp : s < 1) (hp : 1 ≤ p) {n m l : ℕ} (hnm : n < m) (hml : m ≤ l)
    (hC : largeCubeLinftyConst d ≤ C) :
    ∃ X : ShellSeq d → ℝ, Measurable X ∧
      IsBigO P.toMeasure (gammaSigma 2) X
        (C * ((m - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) * ((l - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2)) ∧
      ∀ omega : ShellSeq d,
        cubeLpENorm (originCube d (l : ℤ)) ∞
          (fun x => finiteShellIncrement omega n m x) ≤ ENNReal.ofReal (X omega) := by
  -- The `J1` law and the Sobolev data `s`, `p` are referenced
  -- here only so that the signature carries the quantifier shape of the clause.
  have _shapeJ1 := hJ1
  have _shapeS := hs
  have _shapeSp := hsp
  have _shapeP := hp
  refine ⟨largeCubeIncrementSupBound n m l,
    measurable_largeCubeIncrementSupBound n m l, ?_, ?_⟩
  · have hwith := isBigOWith_gammaSigma_largeCubeIncrementSupBound
      hPrefix hJ2 hJ3 hJ4 hnm hml
    rw [isBigOWith_iff_isBigO_of_nonneg
      (largeCubeIncrementSupBound_nonneg n m l)] at hwith
    refine hwith.mono_scale ?_
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    refine (mul_le_mul_of_nonneg_right hC ?_).trans_eq ?_
    · exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    · ring
  · intro omega
    have hnl : n ≤ l := le_trans hnm.le hml
    exact cubeLpENorm_infty_finiteShellIncrement_le_largeCubeIncrementSupBound
      omega hnl

end

end SuperdiffusionCLT.Section2.Estimates.Stream