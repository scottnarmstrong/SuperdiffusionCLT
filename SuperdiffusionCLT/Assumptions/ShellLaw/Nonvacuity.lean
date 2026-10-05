/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellField.J3DerivativeAPI
public import SuperdiffusionCLT.Assumptions.ShellField.J3LInftyInterpretation
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5

/-!
# A law satisfying the marginal shell prefix and J1-J4

The marginal Section 2 estimates are all stated conditionally on the
assumption structures. This module shows that the conditional hypotheses are
not empty: the identically zero shell field is a legitimate element of the
carrier, and the Dirac law at the constant zero shell sequence satisfies
the dimension prefix, J1, J2, J3 and J4 simultaneously.

It also records the opposite fact for J5. The zero forcing has zero stationary
response, so the J5 block estimate `|energy - c⋆ (log 3) (m - n)| ≤ K` fails as
soon as `m - n` exceeds `K / (c⋆ log 3)`. J5 therefore genuinely excludes
degenerate laws, and a certificate for the full bundle needs a nondegenerate
example, namely the log-correlated Gaussian field of the manuscript's
appendix, which is not built here.

## Main definitions

* `SuperdiffusionCLT.Frozen.Assumptions.ShellField.zero`: the identically
  zero shell field.
* `SuperdiffusionCLT.Assumptions.ShellLaw.zeroShellSeq`: the constant zero
  shell sequence.
* `SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw`: the Dirac law at
  that sequence.

## Main results

* `SuperdiffusionCLT.Probability.indep_dirac`,
  `SuperdiffusionCLT.Probability.iIndep_dirac` and
  `SuperdiffusionCLT.Probability.iIndepFun_dirac`: two sub-sigma-fields,
  every family of sub-sigma-fields, and every family of measurable functions
  are independent under a Dirac measure. This certificate establishes the
  logical consistency of the assumptions; it carries no information about a
  nontrivial field.
* `SuperdiffusionCLT.Assumptions.ShellLaw.exists_law_satisfying_prefix_J1_J4`:
  the prefix together with J1, J2, J3 and J4 is satisfiable in every
  dimension `d ≥ 2`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Probability

open MeasureTheory ProbabilityTheory

/-! ## Independence under a Dirac measure

A Dirac measure gives every measurable set the value `0` or `1`, so the
product rule holds for arbitrary sub-sigma-fields. Mathlib has no such lemma at
the pinned revision, so both the pairwise and the indexed form are proved here
from `MeasureTheory.Measure.dirac_apply'`. -/

/-- Any two sub-sigma-fields are independent under a Dirac measure. -/
theorem indep_dirac {Omega : Type*} {m₁ m₂ : MeasurableSpace Omega}
    {mOmega : MeasurableSpace Omega} (h₁ : m₁ ≤ mOmega) (h₂ : m₂ ≤ mOmega)
    (x : Omega) :
    Indep m₁ m₂ (Measure.dirac x) := by
  refine (Indep_iff m₁ m₂ (Measure.dirac x)).2 fun t₁ t₂ ht₁ ht₂ ↦ ?_
  rw [Measure.dirac_apply' x ((h₁ t₁ ht₁).inter (h₂ t₂ ht₂)),
    Measure.dirac_apply' x (h₁ t₁ ht₁), Measure.dirac_apply' x (h₂ t₂ ht₂),
    Set.inter_indicator_one]
  rfl

/-- Any family of sub-sigma-fields is mutually independent under a Dirac
measure. -/
theorem iIndep_dirac {Omega iota : Type*} {m : iota → MeasurableSpace Omega}
    {mOmega : MeasurableSpace Omega} (hm : ∀ i, m i ≤ mOmega) (x : Omega) :
    iIndep m (Measure.dirac x) := by
  refine (iIndep_iff m (Measure.dirac x)).2 fun s f hf ↦ ?_
  by_cases hx : ∀ i ∈ s, x ∈ f i
  · rw [Measure.dirac_apply_of_mem (Set.mem_iInter₂.2 hx)]
    exact (Finset.prod_eq_one fun i hi ↦
      Measure.dirac_apply_of_mem (hx i hi)).symm
  · push Not at hx
    obtain ⟨i, hi, hxi⟩ := hx
    have hzero : Measure.dirac x (f i) = 0 := by
      rw [Measure.dirac_apply' x (hm i (f i) (hf i hi))]
      exact Set.indicator_of_notMem hxi _
    rw [Finset.prod_eq_zero hi hzero]
    exact le_antisymm
      ((measure_mono (Set.biInter_subset_of_mem hi)).trans hzero.le) zero_le

/-- Any family of measurable functions is mutually independent under a Dirac
measure. -/
theorem iIndepFun_dirac {Omega iota : Type*} {beta : iota → Type*}
    [∀ i, MeasurableSpace (beta i)] {mOmega : MeasurableSpace Omega}
    {f : ∀ i, Omega → beta i} (hf : ∀ i, Measurable (f i)) (x : Omega) :
    iIndepFun f (Measure.dirac x) :=
  (iIndepFun_iff_iIndep _ f (Measure.dirac x)).2
    (iIndep_dirac (fun i ↦ (hf i).comap_le) x)

end SuperdiffusionCLT.Probability

namespace SuperdiffusionCLT.Frozen.Assumptions.ShellField

open Homogenization MeasureTheory
open Homogenization.Book.Ch02
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-! ## The identically zero shell field -/

/-- The identically zero shell field: the stored value and both stored
derivatives are the constant zero continuous maps. -/
def zero (d : ℕ) : ShellField d :=
  ⟨(0, (0, 0)), by
    refine ⟨fun x ↦ ?_, fun x ↦ ?_, fun _ _ _ ↦ ?_⟩
    · exact hasFDerivAt_const (0 : Mat d) x
    · exact hasFDerivAt_const (0 : Vec d →L[ℝ] Mat d) x
    · exact neg_zero.symm⟩

@[simp]
theorem zero_apply (d : ℕ) (x : Vec d) : zero d x = 0 :=
  rfl

@[simp]
theorem deriv_zero (d : ℕ) (x : Vec d) : deriv (zero d) x = 0 :=
  rfl

@[simp]
theorem secondDeriv_zero (d : ℕ) (x : Vec d) : secondDeriv (zero d) x = 0 :=
  rfl

/-! ## The zero shell under the J4 actions -/

/-- Every real translation fixes the zero shell. -/
@[simp]
theorem translate_zero (z : Vec d) : translate z (zero d) = zero d := by
  refine ShellField.ext fun x ↦ ?_
  rw [translate_apply, zero_apply, zero_apply]

/-- Negation fixes the zero shell. -/
@[simp]
theorem negate_zero : negate (zero d) = zero d := by
  refine ShellField.ext fun x ↦ ?_
  rw [negate_apply, zero_apply, neg_zero]

/-- Every signed-permutation conjugation fixes the zero shell. -/
@[simp]
theorem rotate_zero (R : Mat d) (hR : IsSignedPermutationMatrix R) :
    rotate R hR (zero d) = zero d := by
  refine ShellField.ext fun x ↦ ?_
  rw [rotate_apply, zero_apply, zero_apply, Matrix.mul_zero, Matrix.zero_mul]

/-! ## The J3 observable of the zero shell -/

/-- The exact induced first-derivative norm of the zero derivative is zero. -/
@[simp]
theorem matrixDerivativeNorm_zero :
    matrixDerivativeNorm (0 : MatrixDerivative d) = 0 :=
  le_antisymm
    (by
      simpa only [norm_zero, mul_zero] using
        matrixDerivativeNorm_le_sq_mul_norm (0 : MatrixDerivative d))
    (matrixDerivativeNorm_nonneg _)

/-- The exact twice-induced second-derivative norm of the zero second
derivative is zero. -/
@[simp]
theorem matrixSecondDerivativeNorm_zero :
    matrixSecondDerivativeNorm (0 : MatrixSecondDerivative d) = 0 :=
  le_antisymm
    ((matrixSecondDerivativeNorm_le_iff _ 0).2
      ⟨le_rfl, fun _ _ ↦ by
        simpa only [_root_.zero_apply] using
          (matrixDerivativeNorm_zero (d := d)).le⟩)
    (matrixSecondDerivativeNorm_nonneg _)

@[simp]
theorem shellCubeValueNorm_zero (n : ℕ) :
    shellCubeValueNorm n (zero d) = 0 := by
  have hfun : (fun x : Vec d ↦ matrixOperatorNorm ((zero d) x)) =
      (0 : Vec d → ℝ) := by
    funext x
    simp only [zero_apply, matrixOperatorNorm_zero, Pi.zero_apply]
  rw [shellCubeValueNorm_eq_eLpNorm_top, hfun, eLpNorm_zero, ENNReal.toReal_zero]

@[simp]
theorem shellCubeDerivNorm_zero (n : ℕ) :
    shellCubeDerivNorm n (zero d) = 0 :=
  le_antisymm
    ((shellCubeDerivNorm_le_iff n (zero d) 0).2
      ⟨le_rfl, fun _ ↦ by
        simpa only [deriv_zero] using (matrixDerivativeNorm_zero (d := d)).le⟩)
    (shellCubeDerivNorm_nonneg n (zero d))

@[simp]
theorem shellCubeSecondDerivNorm_zero (n : ℕ) :
    shellCubeSecondDerivNorm n (zero d) = 0 :=
  le_antisymm
    ((shellCubeSecondDerivNorm_le_iff n (zero d) 0).2
      ⟨le_rfl, fun _ ↦ by
        simpa only [secondDeriv_zero] using
          (matrixSecondDerivativeNorm_zero (d := d)).le⟩)
    (shellCubeSecondDerivNorm_nonneg n (zero d))

/-- All three terms of the J3 observable vanish on the zero shell. -/
@[simp]
theorem j3Observable_zero (n : ℕ) : j3Observable d n (zero d) = 0 := by
  rw [j3Observable, shellCubeValueNorm_zero, shellCubeDerivNorm_zero,
    shellCubeSecondDerivNorm_zero, mul_zero, mul_zero, add_zero, add_zero]

end

end SuperdiffusionCLT.Frozen.Assumptions.ShellField

namespace SuperdiffusionCLT.Assumptions.ShellLaw

open Homogenization MeasureTheory ProbabilityTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-! ## The Dirac law at the constant zero shell sequence -/

/-- The shell sequence all of whose coordinates are the zero shell. -/
def zeroShellSeq (d : ℕ) : ℕ → ShellField d := fun _ ↦ ShellField.zero d

@[simp]
theorem zeroShellSeq_apply (d : ℕ) (n : ℕ) :
    zeroShellSeq d n = ShellField.zero d :=
  rfl

/-- The Dirac law at the constant zero shell sequence. -/
def diracZeroLaw (d : ℕ) : ProbabilityMeasure (ℕ → ShellField d) :=
  ⟨Measure.dirac (zeroShellSeq d), Measure.dirac.isProbabilityMeasure⟩

@[simp]
theorem diracZeroLaw_toMeasure (d : ℕ) :
    (diracZeroLaw d).toMeasure = Measure.dirac (zeroShellSeq d) :=
  rfl

/-- Every shell marginal of the Dirac law is the Dirac law at the zero shell. -/
theorem shellMarginalLaw_diracZeroLaw (d n : ℕ) :
    (ShellField.shellMarginalLaw (diracZeroLaw d) n).toMeasure =
      Measure.dirac (ShellField.zero d) := by
  show Measure.map (fun F : ℕ → ShellField d ↦ F n)
      (Measure.dirac (zeroShellSeq d)) = _
  rw [Measure.map_dirac' (ShellField.measurable_shellCoordinate n)]
  rfl

/-! ## The prefix and J1 to J4 for the Dirac law -/

/-- Every translate of the zero shell is the zero shell, so each shell marginal
of the Dirac law is translation invariant. -/
theorem shellLawPrefix_diracZeroLaw (hd : 2 ≤ d) :
    ShellLawPrefix d (diracZeroLaw d) where
  dimension := hd
  stationary n z := by
    rw [shellMarginalLaw_diracZeroLaw,
      Measure.map_dirac' (ShellField.measurable_translate z),
      ShellField.translate_zero]

/-- Under a Dirac measure any two local sigma-fields are independent, so the
range-of-dependence requirement holds at every separation. -/
theorem shellLawJ1_diracZeroLaw : ShellLawJ1 d (diracZeroLaw d) where
  range_dependence n U V _ _ _ := by
    rw [shellMarginalLaw_diracZeroLaw]
    exact SuperdiffusionCLT.Probability.indep_dirac
      (ShellField.lihLocalSigma_le_borel U)
      (ShellField.lihLocalSigma_le_borel V) (ShellField.zero d)

/-- The coordinates of a Dirac law on a product space are mutually
independent. -/
theorem shellLawJ2_diracZeroLaw : ShellLawJ2 d (diracZeroLaw d) where
  independent := by
    rw [diracZeroLaw_toMeasure]
    exact SuperdiffusionCLT.Probability.iIndepFun_dirac
      (fun n ↦ measurable_pi_apply n) (zeroShellSeq d)

/-- The J3 observable of the zero shell is `0`, so the strict superlevel set at
any `t ≥ 1` is empty and carries measure `0`. -/
theorem shellLawJ3_diracZeroLaw : ShellLawJ3 d (diracZeroLaw d) where
  gaussian_tail n t ht := by
    have hmeas : MeasurableSet
        {F : ℕ → ShellField d | t < ShellField.j3Observable d n (F n)} :=
      measurableSet_lt measurable_const
        ((ShellField.j3Observable_measurable d n).comp (measurable_pi_apply n))
    have hzero : (diracZeroLaw d).toMeasure
        {F : ℕ → ShellField d | t < ShellField.j3Observable d n (F n)} = 0 := by
      rw [diracZeroLaw_toMeasure, Measure.dirac_apply' _ hmeas]
      refine Set.indicator_of_notMem ?_ _
      simp only [Set.mem_ofPred_eq, zeroShellSeq_apply,
        ShellField.j3Observable_zero]
      exact not_lt.2 (le_trans zero_le_one ht)
    rw [hzero]
    exact zero_le

/-- Rotating or negating the constant zero sequence returns the same sequence,
and the pushforward of a Dirac law is the Dirac law at the image point. -/
theorem shellLawJ4_diracZeroLaw : ShellLawJ4 d (diracZeroLaw d) where
  hyperoctahedral R hR := by
    apply MeasureTheory.ProbabilityMeasure.toMeasure_injective
    show Measure.map (ShellField.rotateSequence R hR)
        (Measure.dirac (zeroShellSeq d)) = Measure.dirac (zeroShellSeq d)
    rw [Measure.map_dirac' (ShellField.measurable_rotateSequence R hR)]
    congr 1
    funext n
    exact ShellField.rotate_zero R hR
  negation := by
    apply MeasureTheory.ProbabilityMeasure.toMeasure_injective
    show Measure.map ShellField.negateSequence
        (Measure.dirac (zeroShellSeq d)) = Measure.dirac (zeroShellSeq d)
    rw [Measure.map_dirac' (ShellField.measurable_negateSequence (d := d))]
    congr 1
    funext n
    exact ShellField.negate_zero

/-- **The prefix together with J1, J2, J3 and J4 is satisfiable.** -/
theorem exists_law_satisfying_prefix_J1_J4 (hd : 2 ≤ d) :
    ∃ P : ProbabilityMeasure (ℕ → ShellField d),
      ShellLawPrefix d P ∧ ShellLawJ1 d P ∧ ShellLawJ2 d P ∧
        ShellLawJ3 d P ∧ ShellLawJ4 d P :=
  ⟨diracZeroLaw d, shellLawPrefix_diracZeroLaw hd, shellLawJ1_diracZeroLaw,
    shellLawJ2_diracZeroLaw, shellLawJ3_diracZeroLaw, shellLawJ4_diracZeroLaw⟩

/-! ## J5 fails for the Dirac law

The zero shell sequence has zero block forcing, hence zero stationary response,
so the J5 block energy is identically `0` while the manuscript's target grows
linearly in the block length. -/

end

end SuperdiffusionCLT.Assumptions.ShellLaw
