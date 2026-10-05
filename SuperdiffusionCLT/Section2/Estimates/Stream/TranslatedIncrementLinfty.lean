/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Probability.GammaSigmaHelpers
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementLinfty

/-!
# Marginal finite-increment envelopes on translated cubes

This module gives the ordinary translated version of the finite-increment
supremum envelope.  For a deterministic center `z`, one common random variable
controls the increment at every point `z + x` with `x ∈ cu_n`, and it has the
same `Gamma₂` amplitude as the envelope centered at the origin.

`ShellField.translateSequence` is used only as deterministic notation for
applying `ShellField.translate z` coordinatewise.  The probabilistic proof does
not assert that this whole sequence has the original law: it transports the
regularity observable of each shell separately through the one-coordinate
stationarity field in `ShellLawPrefix`, and only then takes the finite sum.
No joint stationarity or shell-scaling law is used.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Estimates.Stream

open MeasureTheory
open Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Section2.Cutoff
open scoped BigOperators Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}
variable {P : ProbabilityMeasure (ShellSeq d)}

/-! ## Deterministic translation -/

/-- Coordinatewise translation of the shell sequence translates the finite
increment.  This is a deterministic identity, not a sequence-law statement. -/
theorem finiteShellIncrement_translateSequence (z : Vec d) (omega : ShellSeq d)
    (n m : ℕ) (x : Vec d) :
    finiteShellIncrement (ShellField.translateSequence z omega) n m x =
      finiteShellIncrement omega n m (z + x) := by
  ext i l
  simp only [finiteShellIncrement_apply_entry, ShellField.translateSequence_apply,
    ShellField.translate_apply]
  rw [add_comm x z]

/-- The small-cube envelope applied to the deterministically translated shell
sequence.  No invariance of the whole sequence law is built into this
definition. -/
def translatedIncrementSupBound (z : Vec d) (n m : ℕ)
    (omega : ShellSeq d) : ℝ :=
  incrementSupBound n m (ShellField.translateSequence z omega)

/-- The translated envelope is the value at its center plus the natural-cube
derivative gauge of the coordinatewise translated shells. -/
theorem translatedIncrementSupBound_eq (z : Vec d) (n m : ℕ)
    (omega : ShellSeq d) :
    translatedIncrementSupBound z n m omega =
      matrixOperatorNorm (finiteShellIncrement omega n m z) +
        (d : ℝ) ^ 2 * Real.sqrt d * ((3 : ℝ) ^ n / 2) *
          finiteShellDerivGauge n m (ShellField.translateSequence z omega) := by
  rw [translatedIncrementSupBound, incrementSupBound,
    finiteShellIncrement_translateSequence, add_zero]

/-- Every point `z + x` of the translated cube is controlled by the translated
finite-increment envelope. -/
theorem matrixOperatorNorm_finiteShellIncrement_le_translatedIncrementSupBound
    (z : Vec d) (omega : ShellSeq d) (n m : ℕ) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d (n : ℤ))) :
    matrixOperatorNorm (finiteShellIncrement omega n m (z + x)) ≤
      translatedIncrementSupBound z n m omega := by
  have h := matrixOperatorNorm_finiteShellIncrement_le_incrementSupBound
    (ShellField.translateSequence z omega) n m hx
  simpa only [translatedIncrementSupBound,
    finiteShellIncrement_translateSequence] using h

/-- The translated finite-increment envelope is measurable. -/
theorem measurable_translatedIncrementSupBound (z : Vec d) (n m : ℕ) :
    Measurable (translatedIncrementSupBound z n m : ShellSeq d → ℝ) :=
  (measurable_incrementSupBound n m).comp
    (ShellField.measurable_translateSequence z)

/-- The translated finite-increment envelope is nonnegative. -/
theorem translatedIncrementSupBound_nonneg (z : Vec d) (n m : ℕ)
    (omega : ShellSeq d) :
    0 ≤ translatedIncrementSupBound z n m omega :=
  incrementSupBound_nonneg n m (ShellField.translateSequence z omega)

/-! ## One-shell translated derivative tails -/

/-- The exact cube-`n` derivative norm of shell `k`, after a deterministic
translation, has the same `Gamma₂` amplitude as before translation.  Only the
stationarity of coordinate `k` is used. -/
theorem isBigOWith_gammaSigma_shellCubeDerivNorm_translate
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P)
    {n k : ℕ} (hnk : n ≤ k) (z : Vec d) :
    IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d ↦
        ShellField.shellCubeDerivNorm n
          (ShellField.translate z (omega k)))
      (((3 : ℝ) ^ k)⁻¹) := by
  apply ShellLawPrefix.isBigOWith_gammaSigma_shellObservable_translate
    hPrefix k z (ShellField.shellCubeDerivNorm_measurable n)
  exact (isBigOWith_gammaSigma_shellCubeDerivNorm_coordinate hJ3 k).of_le
    (fun omega ↦ ShellField.shellCubeDerivNorm_mono hnk (omega k))

/-- The translated summed derivative gauge is measurable. -/
theorem measurable_finiteShellDerivGauge_translate (z : Vec d) (n m : ℕ) :
    Measurable (fun omega : ShellSeq d ↦
      finiteShellDerivGauge n m (ShellField.translateSequence z omega)) :=
  (measurable_finiteShellDerivGauge n m).comp
    (ShellField.measurable_translateSequence z)

/-- The common cube-`n` derivative gauge of the translated shells over
`(n,m]` has the same explicit geometric-tail amplitude as the origin gauge.
The proof transports each summand separately before applying the generalized
`Gamma₂` triangle inequality. -/
theorem isBigOWith_gammaSigma_finiteShellDerivGauge_translate
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P)
    {n m : ℕ} (hnm : n < m) (z : Vec d) :
    IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d ↦
        finiteShellDerivGauge n m (ShellField.translateSequence z omega))
      (IndependentSums.gammaTriangleConst 2 * ((3 : ℝ) ^ n)⁻¹) := by
  have hs : (Finset.Ioc n m).Nonempty := Finset.nonempty_Ioc.mpr hnm
  have hbigO : ∀ k ∈ Finset.Ioc n m,
      IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
        (fun omega : ShellSeq d ↦
          ShellField.shellCubeDerivNorm n
            (ShellField.translate z (omega k)))
        (((3 : ℝ) ^ k)⁻¹) := by
    intro k hk
    have hnk : n ≤ k := (Finset.mem_Ioc.mp hk).1.le
    exact
      (isBigOWith_iff_isBigO_of_nonneg
        (mu := P.toMeasure) (Psi := IndependentSums.gammaSigma 2)
        (X := fun omega : ShellSeq d ↦
          ShellField.shellCubeDerivNorm n
            (ShellField.translate z (omega k)))
        (A := ((3 : ℝ) ^ k)⁻¹)
        (fun omega ↦ ShellField.shellCubeDerivNorm_nonneg n
          (ShellField.translate z (omega k)))).1
        (isBigOWith_gammaSigma_shellCubeDerivNorm_translate
          hPrefix hJ3 hnk z)
  have hfinite := IndependentSums.isBigO_finset_sum_of_isBigO_gammaSigma
    (μ := P.toMeasure) (Finset.Ioc n m)
    (X := fun (k : ℕ) (omega : ShellSeq d) ↦
      ShellField.shellCubeDerivNorm n
        (ShellField.translate z (omega k)))
    (a := fun k : ℕ ↦ ((3 : ℝ) ^ k)⁻¹) (σ := 2)
    (by norm_num) hs (fun k _ ↦ by positivity) hbigO
    (fun k _ ↦
      ((ShellField.shellCubeDerivNorm_measurable n).comp
        (ShellField.measurable_translate z)).comp
          (ShellField.measurable_shellCoordinate k))
  have hwith :
      IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 2)
        (fun omega : ShellSeq d ↦
          finiteShellDerivGauge n m (ShellField.translateSequence z omega))
        (IndependentSums.gammaTriangleConst 2 *
          ∑ k ∈ Finset.Ioc n m, ((3 : ℝ) ^ k)⁻¹) := by
    apply
      (isBigOWith_iff_isBigO_of_nonneg
        (fun omega ↦ finiteShellDerivGauge_nonneg n m
          (ShellField.translateSequence z omega))).2
    simpa only [finiteShellDerivGauge, ShellField.translateSequence_apply] using hfinite
  refine hwith.mono_scale (mul_le_mul_of_nonneg_left ?_
    IndependentSums.gammaTriangleConst_pos.le)
  exact sum_Ioc_inv_pow_three_le hnm.le

/-! ## The translated supremum envelope tail -/

/-- The translated finite-increment supremum envelope has the same `Gamma₂`
bound and the same explicit dimension constant as the origin envelope.  The
value term uses fixed-point concentration at `z`; the derivative term is the
sum of individually stationarity-transported shell observables. -/
theorem isBigOWith_gammaSigma_translatedIncrementSupBound
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    {n m : ℕ} (hnm : n < m) (z : Vec d) :
    IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 2)
      (translatedIncrementSupBound z n m)
      (streamLinftyConst d * Real.sqrt ((m - n : ℕ) : ℝ)) := by
  let gap : ℝ := (m - n : ℕ)
  let tri : ℝ := IndependentSums.gammaTriangleConst 2
  let ind : ℝ := Book.Ch04.gammaSigmaIndependentSumConst 2
  let p : ℝ := (3 : ℝ) ^ n
  let geo : ℝ := (d : ℝ) ^ 2 * Real.sqrt d * (p / 2)
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) hPrefix.dimension
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hgapNat : 1 ≤ m - n := Nat.sub_pos_of_lt hnm
  have hgap : (0 : ℝ) < gap := by
    dsimp only [gap]
    exact_mod_cast Nat.sub_pos_of_lt hnm
  have hone_le_sqrt : (1 : ℝ) ≤ Real.sqrt gap := by
    rw [← Real.sqrt_one]
    apply Real.sqrt_le_sqrt
    dsimp only [gap]
    exact_mod_cast hgapNat
  have htri : 0 < tri := by
    dsimp only [tri]
    exact IndependentSums.gammaTriangleConst_pos
  have hind : 0 < ind := by
    dsimp only [ind]
    exact gammaSigmaIndependentSumConst_two_pos
  have hp : 0 < p := by
    dsimp only [p]
    exact pow_pos (by norm_num) n
  have hgeo : 0 < geo := by
    dsimp only [geo]
    positivity
  have hA : 0 < tri * ((d : ℝ) ^ 2 * (ind * Real.sqrt gap)) := by
    exact mul_pos htri (mul_pos (sq_pos_of_pos hdR)
      (mul_pos hind (Real.sqrt_pos.2 hgap)))
  have hB : 0 < geo * (tri * p⁻¹) := by positivity
  have hValueWith :
      IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 2)
        (fun omega : ShellSeq d ↦
          matrixOperatorNorm (finiteShellIncrement omega n m z))
        (tri * ((d : ℝ) ^ 2 * (ind * Real.sqrt gap))) := by
    dsimp only [tri, ind, gap]
    exact isBigOWith_gammaSigma_incrementAt hPrefix hJ2 hJ3 hJ4 hnm z
  have hValue :
      IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
        (fun omega : ShellSeq d ↦
          matrixOperatorNorm (finiteShellIncrement omega n m z))
        (tri * ((d : ℝ) ^ 2 * (ind * Real.sqrt gap))) :=
    (isBigOWith_iff_isBigO_of_nonneg
      (mu := P.toMeasure) (Psi := IndependentSums.gammaSigma 2)
      (X := fun omega : ShellSeq d ↦
        matrixOperatorNorm (finiteShellIncrement omega n m z))
      (A := tri * ((d : ℝ) ^ 2 * (ind * Real.sqrt gap)))
      (fun omega ↦ matrixOperatorNorm_nonneg
        (finiteShellIncrement omega n m z))).1 hValueWith
  have hDerivWith :
      IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 2)
        (fun omega : ShellSeq d ↦ geo *
          finiteShellDerivGauge n m (ShellField.translateSequence z omega))
        (geo * (tri * p⁻¹)) := by
    have h := (isBigOWith_gammaSigma_finiteShellDerivGauge_translate
      hPrefix hJ3 hnm z).const_mul hgeo.le
    dsimp only [geo, tri, p]
    exact h
  have hDeriv :
      IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
        (fun omega : ShellSeq d ↦ geo *
          finiteShellDerivGauge n m (ShellField.translateSequence z omega))
        (geo * (tri * p⁻¹)) :=
    (isBigOWith_iff_isBigO_of_nonneg
      (mu := P.toMeasure) (Psi := IndependentSums.gammaSigma 2)
      (X := fun omega : ShellSeq d ↦ geo *
        finiteShellDerivGauge n m (ShellField.translateSequence z omega))
      (A := geo * (tri * p⁻¹))
      (fun omega ↦ mul_nonneg hgeo.le
        (finiteShellDerivGauge_nonneg n m
          (ShellField.translateSequence z omega)))).1 hDerivWith
  have hValueMeas : Measurable (fun omega : ShellSeq d ↦
      matrixOperatorNorm (finiteShellIncrement omega n m z)) := by
    have h := (measurable_matrixOperatorNorm_finiteShellIncrement_origin n m).comp
      (ShellField.measurable_translateSequence z)
    have hfun :
        ((fun omega : ShellSeq d ↦
          matrixOperatorNorm (finiteShellIncrement omega n m 0)) ∘
            ShellField.translateSequence z) =
          fun omega : ShellSeq d ↦
            matrixOperatorNorm (finiteShellIncrement omega n m z) := by
      funext omega
      rw [Function.comp_apply, finiteShellIncrement_translateSequence, add_zero]
    rw [hfun] at h
    exact h
  have hcombine := isBigO_gammaSigma_add_of_isBigO
    (by norm_num : (0 : ℝ) < 2) hA hB hValue hDeriv hValueMeas
    ((measurable_finiteShellDerivGauge_translate z n m).const_mul geo)
  have hcancel : p * p⁻¹ = 1 := mul_inv_cancel₀ hp.ne'
  have hderivScale :
      geo * (tri * p⁻¹) = tri * (d : ℝ) ^ 2 * (Real.sqrt d / 2) := by
    calc
      geo * (tri * p⁻¹) =
          tri * (d : ℝ) ^ 2 * (Real.sqrt d / 2) * (p * p⁻¹) := by
        dsimp only [geo]
        ring
      _ = tri * (d : ℝ) ^ 2 * (Real.sqrt d / 2) := by
        rw [hcancel, mul_one]
  have hderivScale_le :
      geo * (tri * p⁻¹) ≤
        (tri * (d : ℝ) ^ 2 * (Real.sqrt d / 2)) * Real.sqrt gap := by
    let c : ℝ := tri * (d : ℝ) ^ 2 * (Real.sqrt d / 2)
    have hc : 0 ≤ c := by
      dsimp only [c]
      positivity
    calc
      geo * (tri * p⁻¹) = c := hderivScale
      _ = c * 1 := (mul_one c).symm
      _ ≤ c * Real.sqrt gap := mul_le_mul_of_nonneg_left hone_le_sqrt hc
  have hscale :
      tri *
          (tri * ((d : ℝ) ^ 2 * (ind * Real.sqrt gap)) +
            geo * (tri * p⁻¹)) ≤
        streamLinftyConst d * Real.sqrt gap := by
    calc
      tri *
          (tri * ((d : ℝ) ^ 2 * (ind * Real.sqrt gap)) +
            geo * (tri * p⁻¹)) ≤
          tri *
            (tri * ((d : ℝ) ^ 2 * (ind * Real.sqrt gap)) +
              (tri * (d : ℝ) ^ 2 * (Real.sqrt d / 2)) *
                Real.sqrt gap) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (le_refl _) hderivScale_le) htri.le
      _ = streamLinftyConst d * Real.sqrt gap := by
        rw [streamLinftyConst]
        dsimp only [tri, ind]
        ring
  apply (isBigOWith_iff_isBigO_of_nonneg
    (mu := P.toMeasure) (Psi := IndependentSums.gammaSigma 2)
    (X := translatedIncrementSupBound z n m)
    (A := streamLinftyConst d * Real.sqrt ((m - n : ℕ) : ℝ))
    (translatedIncrementSupBound_nonneg z n m)).2
  have hfun : translatedIncrementSupBound z n m =
      fun omega : ShellSeq d ↦
        matrixOperatorNorm (finiteShellIncrement omega n m z) +
          geo * finiteShellDerivGauge n m
            (ShellField.translateSequence z omega) := by
    funext omega
    rw [translatedIncrementSupBound_eq]
  rw [hfun]
  change IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
    (fun omega : ShellSeq d ↦
      matrixOperatorNorm (finiteShellIncrement omega n m z) +
        geo * finiteShellDerivGauge n m
          (ShellField.translateSequence z omega))
    (streamLinftyConst d * Real.sqrt gap)
  exact hcombine.mono_scale hscale

end

end SuperdiffusionCLT.Section2.Estimates.Stream
