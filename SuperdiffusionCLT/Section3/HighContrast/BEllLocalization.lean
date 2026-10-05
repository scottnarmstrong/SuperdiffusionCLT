/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Frozen.Section2.LocalizationA
public import SuperdiffusionCLT.Section2.Localization.CutoffComparison
public import SuperdiffusionCLT.Section2.Annealed.Measurability
public import SuperdiffusionCLT.Probability.GammaSigmaHelpers
public import SuperdiffusionCLT.Probability.IndexSigma
public import SuperdiffusionCLT.Probability.OrliczMoments

/-!
# Localizing the coarse block matrix between two infrared cutoffs

The printed proof of the homogenization step for `σ̄_ℓ` compares the coarse block
matrices of the two cutoff fields `a_ell` and `a_k` on the cube `cu_n`, using
the localization lemma `l.localization.A` at `a = a_k` with the anti-symmetric
perturbation `k_ell - k_k` and `U = cu_n`. The relative size of the
perturbation is measured by

`Dbar = nu^{-1} ||k_ell - k_k||_{L^infty(cu_n)}
          + nu^{-2} ||k_ell - k_k||^2_{L^infty(cu_n)}`,

and the printed conclusion is the pathwise Loewner comparison

`bfA_ell(cu_n) - bfA_k(cu_n) <= Dbar * bfA_k(cu_n)`.

## The relative-`theta` bound

`SuperdiffusionCLT.Frozen.Section2.coarseBlockMatrix_localization`
writes the printed `||s^{-1/2} h s^{-1/2}||_{L^infty}` square-root-free, as the
relative bound `2 r . h(x) p <= theta (p . s(x) p + r . s(x) r)`. Here
`s(x) = nu Id` at every point (`symmPart_coefficientCutoff`), so the bound holds
with `theta = nu^{-1} ||h||_{L^infty(cu_n)}`: this is
`two_vecDot_le_of_matrixOperatorNorm_le`, the Euclidean operator-norm
estimate `2 r · h p <= ||h|| (|p|^2 + |r|^2)`. The constant of the conclusion is
`theta (1 + theta)`, which for that `theta` is exactly `Dbar`.

The `L^infty(cu_n)` norm is realized by the carrier
`finiteShellIncrementLinftyNormLargeCube k l n`, a supremum over the open cube
`cu_n`, which is precisely the carrier set of `Book.Ch02.cubeDomain`.

## Measurability of the supremum

`finiteShellIncrementLinftyNormLargeCube` is an uncountable supremum, so its
measurability is not formal. The increment is continuous in the space variable
and the cube is open, so the supremum is unchanged when the index set is cut
down to a countable dense subset; that reduction is
`measurable_finiteShellIncrementLinftyNormLargeCube_of_coords`, stated for an
arbitrary sigma-algebra on the sample space under the sole hypothesis that the
shell coordinates in `(k, l]` are measurable for it. Instantiating it at the
ambient sigma-algebra and at `indexSigma _ (Set.Ioc k l)` gives both the
ambient measurability needed for the moment bounds and the statement that
`Dbar` reads only the shells `k < r <= l`, which is the measurability half of
the independence argument.

## The expectation

By `e.kmn.Linfty` in its linear-amplitude form
(`isBigOWith_gammaSigma_finiteShellIncrementLinftyNormLargeCube_linear`, read at
`k < n <= l`) the `L^infty(cu_n)` norm is `O_{Gamma_2}(C (l - k))`, so its first
and second moments are controlled by
`abs_moment_le_of_isBigO_gammaSigma_two`. For `nu <= 1` and `k < l` the linear
term is absorbed into the quadratic one and

`E[Dbar] <= dBarMomentConst d * nu^{-2} * (l - k)^2`,

with the explicit dimensional constant
`dBarMomentConst d = C(d) (1 + Gamma(3/2)) + 2 C(d)^2`,
`C(d) = largeCubeLinftyConst d`. The constant is quantified before `nu`, `P`
and the scales, so this statement can be consumed with the constant hoisted.

## Main definitions

* `DBar`: the manuscript's `Dbar` at the cube `cu_n`.
* `dBarMomentConst`: the explicit dimensional constant of the moment bound.

## Main results

* `measurable_finiteShellIncrementLinftyNormLargeCube`: ambient measurability of
  the `L^infty(cu_l)` carrier.
* `measurable_DBar_indexSigma`.
* `integrable_DBar`, `integral_DBar_le`.
* `blockMatLoewnerLE_coarseBlockMatrix_coefficientCutoff`: the pathwise Loewner
  comparison.
* `blockMatLoewnerLE_coarseBlockMatrix_coefficientCutoff_add`: the same in the
  additive form `bfA_ell(cu_n) <= (1 + Dbar) bfA_k(cu_n)`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.HighContrast

open Homogenization
open Homogenization.Book.Ch02
open MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Localization
open SuperdiffusionCLT.Section2.Estimates.Stream

noncomputable section

variable {d : ℕ}
variable {P : ProbabilityMeasure (ShellSeq d)}

/-! ## Ambient algebra

Two elementary identities about the constant symmetric field `nu Id` and the
Euclidean operator norm; they are the whole content of the relative-`theta`
bound demanded by the localization lemma. -/

/-- The quadratic form of the constant field `nu Id`. -/
private theorem vecDot_matVecMul_smul_one (nu : ℝ) (p : Vec d) :
    vecDot p (matVecMul (nu • (1 : Mat d)) p) = nu * vecNormSq p := by
  have hone : matVecMul (1 : Mat d) p = p := by
    funext i
    simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]
  rw [smul_matVecMul, hone, vecDot_smul_right]
  rfl

/-- The square-root-free relative bound: an operator-norm bound `M` on a matrix
`A` gives `2 r . A p <= M (|p|^2 + |r|^2)` for all `p` and `r`. -/
private theorem two_vecDot_le_of_matrixOperatorNorm_le {A : Mat d} {M : ℝ}
    (hA : matrixOperatorNorm A ≤ M) (p r : Vec d) :
    2 * vecDot r (matVecMul A p) ≤ M * (vecNormSq p + vecNormSq r) := by
  have hM0 : (0 : ℝ) ≤ M := le_trans (matrixOperatorNorm_nonneg A) hA
  have h1 : vecDot r (matVecMul A p) ≤ vecNorm r * vecNorm (matVecMul A p) :=
    le_trans (le_abs_self _) (abs_vecDot_le_vecNorm_mul_vecNorm r (matVecMul A p))
  have h2 : vecNorm (matVecMul A p) ≤ M * vecNorm p :=
    le_trans (vecNorm_matVecMul_le_matrixOperatorNorm_mul_vecNorm A p)
      (mul_le_mul_of_nonneg_right hA (vecNorm_nonneg p))
  have h3 : vecNorm r * vecNorm (matVecMul A p) ≤ vecNorm r * (M * vecNorm p) :=
    mul_le_mul_of_nonneg_left h2 (vecNorm_nonneg r)
  calc 2 * vecDot r (matVecMul A p)
      ≤ 2 * (vecNorm r * (M * vecNorm p)) :=
        mul_le_mul_of_nonneg_left (le_trans h1 h3) (by norm_num)
    _ = M * (2 * vecNorm p * vecNorm r) := by ring
    _ ≤ M * (vecNorm p ^ 2 + vecNorm r ^ 2) :=
        mul_le_mul_of_nonneg_left (two_mul_le_add_sq _ _) hM0
    _ = M * (vecNormSq p + vecNormSq r) := by
        rw [vecNorm_sq_eq_vecNormSq, vecNorm_sq_eq_vecNormSq]

/-! ## Measurability of the `L^infty` carrier on a large cube -/

/-- The shell increment is continuous in the space variable. -/
private theorem continuous_matrixOperatorNorm_increment (omega : ShellSeq d)
    (n m : ℕ) :
    Continuous fun x : Vec d ↦
      matrixOperatorNorm (finiteShellIncrement omega n m x) := by
  have hsum : Continuous fun x : Vec d ↦ ∑ k ∈ Finset.Ioc n m, (omega k) x :=
    continuous_finsetSum _ fun k _ ↦ (omega k).1.1.continuous
  refine ShellField.continuous_matrixOperatorNorm.comp (hsum.congr ?_)
  intro x
  rw [finiteShellIncrement_apply]
  rfl

/-- The `L^infty(cu_l)` carrier of the shell increment over `(n, m]` is
measurable for **any** sigma-algebra on the sample space for which the shell
coordinates indexed by `(n, m]` are measurable.

The supremum defining the carrier ranges over the uncountable open cube. The
increment is continuous in the space variable and the cube is open, so the
supremum over the cube coincides with the supremum over the intersection of the
cube with a fixed countable dense set, and that countable supremum is
measurable coordinatewise. -/
theorem measurable_finiteShellIncrementLinftyNormLargeCube_of_coords
    {mS : MeasurableSpace (ShellSeq d)} (n m l : ℕ)
    (hcoord : ∀ r ∈ Finset.Ioc n m,
      Measurable[mS] fun omega : ShellSeq d ↦ omega r) :
    Measurable[mS] (finiteShellIncrementLinftyNormLargeCube n m l) := by
  classical
  obtain ⟨D, hDcount, hDdense⟩ := TopologicalSpace.exists_countable_dense (Vec d)
  have hpt : ∀ x : Vec d, Measurable[mS] fun omega : ShellSeq d ↦
      matrixOperatorNorm (finiteShellIncrement omega n m x) := by
    intro x
    refine ShellField.continuous_matrixOperatorNorm.measurable.comp ?_
    refine measurable_matrix_of_entries ?_
    intro i j
    have hrw : (fun omega : ShellSeq d ↦ finiteShellIncrement omega n m x i j) =
        fun omega : ShellSeq d ↦ ∑ r ∈ Finset.Ioc n m, (omega r) x i j := by
      funext omega
      exact finiteShellIncrement_apply_entry omega n m x i j
    rw [hrw]
    exact Finset.measurable_sum _ fun r hr ↦
      (ShellField.measurable_eval_entry x i j).comp (hcoord r hr)
  set U : Set (Vec d) := openCubeSet (originCube d (l : ℤ)) with hUdef
  have hUopen : IsOpen U := by
    rw [hUdef, ← ball_cubeCenter_eq_openCubeSet]
    exact Metric.isOpen_ball
  have : Countable (D ∩ U : Set (Vec d)) :=
    (hDcount.mono Set.inter_subset_left).to_subtype
  set F : Option (D ∩ U : Set (Vec d)) → ShellSeq d → ℝ := fun o ↦
    match o with
    | none => fun _ ↦ 0
    | some x => fun omega ↦ matrixOperatorNorm (finiteShellIncrement omega n m x.1)
    with hFdef
  have hFmeas : ∀ o, Measurable[mS] (F o) := by
    intro o
    cases o with
    | none => exact measurable_const
    | some x => exact hpt x.1
  have hkey : finiteShellIncrementLinftyNormLargeCube n m l =
      fun omega ↦ ⨆ o, F o omega := by
    funext omega
    have hbdd : BddAbove (Set.range fun o ↦ F o omega) := by
      refine ⟨finiteShellIncrementLinftyNormLargeCube n m l omega, ?_⟩
      rintro r ⟨o, rfl⟩
      cases o with
      | none => exact finiteShellIncrementLinftyNormLargeCube_nonneg n m l omega
      | some x =>
          exact matrixOperatorNorm_finiteShellIncrement_le_linftyNormLargeCube
            omega n m l x.2.2
    have hS0 : (0 : ℝ) ≤ ⨆ o, F o omega := le_ciSup hbdd none
    refine le_antisymm ?_ (ciSup_le fun o ↦ ?_)
    · dsimp only [finiteShellIncrementLinftyNormLargeCube]
      apply csSup_le (Set.range_nonempty _)
      rintro r ⟨o, rfl⟩
      cases o with
      | none => exact hS0
      | some x =>
          change matrixOperatorNorm (finiteShellIncrement omega n m x.1) ≤ _
          by_contra hcon
          have hlt : (⨆ o, F o omega) <
              matrixOperatorNorm (finiteShellIncrement omega n m x.1) :=
            lt_of_not_ge hcon
          have hVopen : IsOpen (U ∩ (fun y : Vec d ↦
              matrixOperatorNorm (finiteShellIncrement omega n m y)) ⁻¹'
                Set.Ioi (⨆ o, F o omega)) :=
            hUopen.inter
              (isOpen_Ioi.preimage (continuous_matrixOperatorNorm_increment omega n m))
          obtain ⟨y, hyD, hyV⟩ := hDdense.exists_mem_open hVopen ⟨x.1, x.2, hlt⟩
          have hmem : y ∈ D ∩ U := ⟨hyD, hyV.1⟩
          have hle : F (some ⟨y, hmem⟩) omega ≤ ⨆ o, F o omega :=
            le_ciSup hbdd (some ⟨y, hmem⟩)
          exact absurd hyV.2 (not_lt.mpr hle)
    · cases o with
      | none => exact finiteShellIncrementLinftyNormLargeCube_nonneg n m l omega
      | some x =>
          exact matrixOperatorNorm_finiteShellIncrement_le_linftyNormLargeCube
            omega n m l x.2.2
  rw [hkey]
  exact Measurable.iSup hFmeas

/-- The `L^infty(cu_l)` carrier of the shell increment is measurable. -/
theorem measurable_finiteShellIncrementLinftyNormLargeCube (n m l : ℕ) :
    Measurable (finiteShellIncrementLinftyNormLargeCube n m l : ShellSeq d → ℝ) :=
  measurable_finiteShellIncrementLinftyNormLargeCube_of_coords n m l
    fun r _ ↦ measurable_pi_apply r

/-! ## The relative size `Dbar` -/

/-- The quantity `Dbar` of the paper at the cube `cu_n`: the relative
`L^infty(cu_n)` size of the shell increment `k_l - k_k` measured against the
molecular diffusivity `nu`. -/
def DBar (nu : ℝ) (k l n : ℕ) (omega : ShellSeq d) : ℝ :=
  nu⁻¹ * finiteShellIncrementLinftyNormLargeCube k l n omega +
    nu⁻¹ ^ 2 * finiteShellIncrementLinftyNormLargeCube k l n omega ^ 2

/-- `Dbar` reads only the shells `k < r <= l`: it is measurable for the
sigma-field generated by those shell coordinates. This is the measurability
half of the independence argument. -/
theorem measurable_DBar_indexSigma {nu : ℝ} (k l n : ℕ) :
    Measurable[SuperdiffusionCLT.Probability.indexSigma
        (fun F : ShellSeq d ↦ F) (Set.Ioc k l)]
      (DBar (d := d) nu k l n) := by
  have hcoord : ∀ r ∈ Finset.Ioc k l,
      Measurable[SuperdiffusionCLT.Probability.indexSigma
        (fun F : ShellSeq d ↦ F) (Set.Ioc k l)]
        fun omega : ShellSeq d ↦ omega r := fun r hr ↦
    SuperdiffusionCLT.Probability.measurable_coordinate_of_mem
      (fun F : ShellSeq d ↦ F) (Finset.mem_Ioc.mp hr)
  have hM := measurable_finiteShellIncrementLinftyNormLargeCube_of_coords
    (mS := SuperdiffusionCLT.Probability.indexSigma
      (fun F : ShellSeq d ↦ F) (Set.Ioc k l)) k l n hcoord
  unfold DBar
  exact (hM.const_mul _).add ((hM.pow_const 2).const_mul _)

/-! ## The expectation of `Dbar`

The `Gamma_2` tail of the `L^infty(cu_n)` norm at linear
amplitude gives the two moments, and for `nu <= 1` and `k < l` the linear term
is absorbed into the quadratic one. -/

/-- The explicit dimensional constant of `integral_DBar_le`, built from the
`Gamma_2` amplitude `largeCubeLinftyConst d` of the shell increment and the
printed moment constants `1 + Gamma(k/2 + 1)` at `k = 1` and `k = 2`. -/
def dBarMomentConst (d : ℕ) : ℝ :=
  largeCubeLinftyConst d * (1 + Real.Gamma (3 / 2)) + 2 * largeCubeLinftyConst d ^ 2

/-- The moment constant is positive. -/
theorem dBarMomentConst_pos (hd : 0 < d) : 0 < dBarMomentConst d := by
  have hc : 0 < largeCubeLinftyConst d := largeCubeLinftyConst_pos_of_pos hd
  have hg : 0 ≤ Real.Gamma (3 / 2) := Real.Gamma_nonneg_of_nonneg (by norm_num)
  unfold dBarMomentConst
  positivity

/-- The printed display `e.kmn.Linfty` at `k < n <= l`, in the two-sided form
required by the moment lemma. -/
private theorem isBigO_gammaSigma_linftyNormLargeCube [NeZero d] {k l n : ℕ}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (hkn : k < n) (hnl : n ≤ l) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
      (finiteShellIncrementLinftyNormLargeCube k l n)
      (largeCubeLinftyConst d * ((l - k : ℕ) : ℝ)) :=
  (isBigOWith_iff_isBigO_of_nonneg
      (fun omega ↦ finiteShellIncrementLinftyNormLargeCube_nonneg k l n omega)).mp
    (isBigOWith_gammaSigma_finiteShellIncrementLinftyNormLargeCube_linear
      hPrefix hJ2 hJ3 hJ4 hkn hnl)

/-- The amplitude of that display is positive. -/
private theorem largeCubeLinftyAmplitude_pos [NeZero d] {k l n : ℕ} (hkn : k < n)
    (hnl : n ≤ l) :
    0 < largeCubeLinftyConst d * ((l - k : ℕ) : ℝ) := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hkl : k < l := lt_of_lt_of_le hkn hnl
  have ht : (0 : ℝ) < ((l - k : ℕ) : ℝ) := by
    have h : 0 < l - k := Nat.sub_pos_of_lt hkl
    exact_mod_cast h
  exact mul_pos (largeCubeLinftyConst_pos_of_pos hd) ht

/-- The first power of the `L^infty` carrier, in the form produced by the
moment lemma. -/
private theorem abs_rpow_one_linftyNormLargeCube (k l n : ℕ) (omega : ShellSeq d) :
    |finiteShellIncrementLinftyNormLargeCube k l n omega| ^ (((1 : ℕ)) : ℝ) =
      finiteShellIncrementLinftyNormLargeCube k l n omega := by
  rw [Nat.cast_one, Real.rpow_one,
    abs_of_nonneg (finiteShellIncrementLinftyNormLargeCube_nonneg k l n omega)]

/-- The second power of the `L^infty` carrier, in the form produced by the
moment lemma. -/
private theorem abs_rpow_two_linftyNormLargeCube (k l n : ℕ) (omega : ShellSeq d) :
    |finiteShellIncrementLinftyNormLargeCube k l n omega| ^ (((2 : ℕ)) : ℝ) =
      finiteShellIncrementLinftyNormLargeCube k l n omega ^ 2 := by
  rw [Real.rpow_natCast, sq_abs]

/-- `Dbar` is integrable: both of its terms are moments of a `Gamma_2` variable
at finite amplitude. -/
theorem integrable_DBar [NeZero d] {nu : ℝ} {k l n : ℕ}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (hkn : k < n) (hnl : n ≤ l) :
    Integrable (DBar (d := d) nu k l n) P.toMeasure := by
  have hA := largeCubeLinftyAmplitude_pos (d := d) (k := k) (l := l) (n := n) hkn hnl
  have hbig := isBigO_gammaSigma_linftyNormLargeCube hPrefix hJ2 hJ3 hJ4 hkn hnl
  have hMm := measurable_finiteShellIncrementLinftyNormLargeCube (d := d) k l n
  have i1 := (integrable_abs_rpow_of_isBigO_gammaSigma_two hA hMm.aemeasurable
    hbig 1).congr (Filter.Eventually.of_forall (abs_rpow_one_linftyNormLargeCube k l n))
  have i2 := (integrable_abs_rpow_of_isBigO_gammaSigma_two hA hMm.aemeasurable
    hbig 2).congr (Filter.Eventually.of_forall (abs_rpow_two_linftyNormLargeCube k l n))
  exact (i1.const_mul _).add (i2.const_mul _)

/-- **The expectation bound for `Dbar`**: for `nu <= 1` and
`k < n <= l`,

`E[Dbar] <= dBarMomentConst d * nu^{-2} * (l - k)^2`.

The constant depends only on the dimension; it is quantified before the
diffusivity, the shell law and the scales. -/
theorem integral_DBar_le [NeZero d] {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    {k l n : ℕ} (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (hkn : k < n) (hnl : n ≤ l) :
    ∫ omega, DBar (d := d) nu k l n omega ∂P.toMeasure ≤
      dBarMomentConst d * nu⁻¹ ^ 2 * (((l - k : ℕ) : ℝ)) ^ 2 := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hkl : k < l := lt_of_lt_of_le hkn hnl
  have hA := largeCubeLinftyAmplitude_pos (d := d) (k := k) (l := l) (n := n) hkn hnl
  have hbig := isBigO_gammaSigma_linftyNormLargeCube hPrefix hJ2 hJ3 hJ4 hkn hnl
  have hMm := measurable_finiteShellIncrementLinftyNormLargeCube (d := d) k l n
  have i1 := (integrable_abs_rpow_of_isBigO_gammaSigma_two hA hMm.aemeasurable
    hbig 1).congr (Filter.Eventually.of_forall (abs_rpow_one_linftyNormLargeCube k l n))
  have i2 := (integrable_abs_rpow_of_isBigO_gammaSigma_two hA hMm.aemeasurable
    hbig 2).congr (Filter.Eventually.of_forall (abs_rpow_two_linftyNormLargeCube k l n))
  have m1 : ∫ omega, finiteShellIncrementLinftyNormLargeCube k l n omega ∂P.toMeasure ≤
      largeCubeLinftyConst d * ((l - k : ℕ) : ℝ) * (1 + Real.Gamma (3 / 2)) := by
    have hraw := abs_moment_le_of_isBigO_gammaSigma_two hA hMm.aemeasurable hbig 1
    rw [integral_congr_ae
      (Filter.Eventually.of_forall (abs_rpow_one_linftyNormLargeCube k l n))] at hraw
    have hg : (((1 : ℕ) : ℝ)) / 2 + 1 = 3 / 2 := by norm_num
    rw [hg, Nat.cast_one, Real.rpow_one] at hraw
    exact hraw
  have m2 : ∫ omega, finiteShellIncrementLinftyNormLargeCube k l n omega ^ 2
        ∂P.toMeasure ≤
      (largeCubeLinftyConst d * ((l - k : ℕ) : ℝ)) ^ 2 * 2 := by
    have hraw := abs_moment_le_of_isBigO_gammaSigma_two hA hMm.aemeasurable hbig 2
    rw [integral_congr_ae
      (Filter.Eventually.of_forall (abs_rpow_two_linftyNormLargeCube k l n))] at hraw
    have hg : (1 : ℝ) + Real.Gamma ((((2 : ℕ) : ℝ)) / 2 + 1) = 2 := by norm_num
    rw [hg, Real.rpow_natCast] at hraw
    exact hraw
  have hsplit : ∫ omega, DBar (d := d) nu k l n omega ∂P.toMeasure =
      nu⁻¹ * ∫ omega, finiteShellIncrementLinftyNormLargeCube k l n omega ∂P.toMeasure +
        nu⁻¹ ^ 2 *
          ∫ omega, finiteShellIncrementLinftyNormLargeCube k l n omega ^ 2
            ∂P.toMeasure := by
    unfold DBar
    rw [integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul,
      integral_const_mul]
  have hnuinv : (1 : ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).mpr hnu1
  have hnn : (0 : ℝ) ≤ nu⁻¹ := le_trans zero_le_one hnuinv
  have ht1 : (1 : ℝ) ≤ ((l - k : ℕ) : ℝ) := by
    have h : 1 ≤ l - k := Nat.one_le_iff_ne_zero.mpr (Nat.sub_ne_zero_of_lt hkl)
    exact_mod_cast h
  have hprod : (1 : ℝ) ≤ nu⁻¹ * ((l - k : ℕ) : ℝ) := by
    have h := mul_le_mul hnuinv ht1 zero_le_one hnn
    rwa [one_mul] at h
  have hkey : nu⁻¹ * ((l - k : ℕ) : ℝ) ≤ nu⁻¹ ^ 2 * ((l - k : ℕ) : ℝ) ^ 2 := by
    calc nu⁻¹ * ((l - k : ℕ) : ℝ) = 1 * (nu⁻¹ * ((l - k : ℕ) : ℝ)) := (one_mul _).symm
      _ ≤ (nu⁻¹ * ((l - k : ℕ) : ℝ)) * (nu⁻¹ * ((l - k : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right hprod (le_trans zero_le_one hprod)
      _ = nu⁻¹ ^ 2 * ((l - k : ℕ) : ℝ) ^ 2 := by ring
  have hc0 : (0 : ℝ) ≤ largeCubeLinftyConst d := (largeCubeLinftyConst_pos_of_pos hd).le
  have hg0 : (0 : ℝ) ≤ 1 + Real.Gamma (3 / 2) := by
    have hgamma := Real.Gamma_nonneg_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2)
    linarith only [hgamma]
  rw [hsplit]
  calc nu⁻¹ * ∫ omega, finiteShellIncrementLinftyNormLargeCube k l n omega ∂P.toMeasure +
        nu⁻¹ ^ 2 *
          ∫ omega, finiteShellIncrementLinftyNormLargeCube k l n omega ^ 2 ∂P.toMeasure
      ≤ nu⁻¹ * (largeCubeLinftyConst d * ((l - k : ℕ) : ℝ) * (1 + Real.Gamma (3 / 2))) +
          nu⁻¹ ^ 2 * ((largeCubeLinftyConst d * ((l - k : ℕ) : ℝ)) ^ 2 * 2) :=
        add_le_add (mul_le_mul_of_nonneg_left m1 hnn)
          (mul_le_mul_of_nonneg_left m2 (sq_nonneg _))
    _ = largeCubeLinftyConst d * (1 + Real.Gamma (3 / 2)) *
            (nu⁻¹ * ((l - k : ℕ) : ℝ)) +
          2 * largeCubeLinftyConst d ^ 2 * (nu⁻¹ ^ 2 * ((l - k : ℕ) : ℝ) ^ 2) := by ring
    _ ≤ largeCubeLinftyConst d * (1 + Real.Gamma (3 / 2)) *
            (nu⁻¹ ^ 2 * ((l - k : ℕ) : ℝ) ^ 2) +
          2 * largeCubeLinftyConst d ^ 2 * (nu⁻¹ ^ 2 * ((l - k : ℕ) : ℝ) ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hkey (mul_nonneg hc0 hg0)) le_rfl
    _ = dBarMomentConst d * nu⁻¹ ^ 2 * ((l - k : ℕ) : ℝ) ^ 2 := by
        rw [dBarMomentConst]
        ring

/-! ## The pathwise Loewner comparison

The localization lemma at `a = a_k`, perturbation
`k_l - k_k` and `U = cu_n`. -/

/-- The Chapter 2 coefficient object of `a_m` on a triadic cube, from the
unconditional admissibility of the cutoff field. -/
private def cutoffCoeffOnCube [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (omega : ShellSeq d) (m : ℕ) (Q : TriadicCube d) :
    Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q) :=
  (Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
    (coefficientCutoff nu omega m)
    (SuperdiffusionCLT.Section2.Annealed.aeLocallyUniformlyEllipticField_coefficientCutoff
      hnu omega m)).coeffOn Q

/-- The coarse block matrix of the cutoff field on a triadic cube is the
Chapter 2 coarse block matrix of its Chapter 2 coefficient object. -/
private theorem coarseBlockMatrix_cubeSet_coefficientCutoff_eq_ch02 [NeZero d]
    {nu : ℝ} (hnu : 0 < nu) (omega : ShellSeq d) (m : ℕ) (Q : TriadicCube d) :
    coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega m).toFun =
      Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q)
        (cutoffCoeffOnCube hnu omega m Q) :=
  Book.Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
    (SuperdiffusionCLT.Section2.Annealed.aeLocallyUniformlyEllipticField_coefficientCutoff
      hnu omega m) Q

/-- **The pathwise block Loewner comparison**: the
localization lemma `l.localization.A` applied at `a = a_k`, perturbation
`k_l - k_k` and `U = cu_n`, whose constant `theta (1 + theta)` at
`theta = nu^{-1} ||k_l - k_k||_{L^infty(cu_n)}` is exactly `Dbar`. -/
theorem blockMatLoewnerLE_coarseBlockMatrix_coefficientCutoff [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (omega : ShellSeq d) {k l n : ℕ} (hkl : k ≤ l) :
    BlockMatLoewnerLE
      (ofFullBlockMat
        (toFullBlockMat (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
            (coefficientCutoff nu omega l).toFun) -
          toFullBlockMat (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
            (coefficientCutoff nu omega k).toFun)))
      (DBar nu k l n omega •
        coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
          (coefficientCutoff nu omega k).toFun) := by
  classical
  set Q : TriadicCube d := originCube d (n : ℤ) with hQ
  set M : ℝ := finiteShellIncrementLinftyNormLargeCube k l n omega with hM
  set theta : ℝ := nu⁻¹ * M with htheta
  have hsymm : ∀ x : Vec d,
      matTranspose ((fun _ : Vec d ↦ nu • (1 : Mat d)) x) =
        (fun _ : Vec d ↦ nu • (1 : Mat d)) x := by
    intro _
    simp only [matTranspose, Matrix.transpose_smul, Matrix.transpose_one]
  have hposdef : ∀ (x : Vec d) (p : Vec d), p ≠ 0 →
      0 < vecDot p (matVecMul ((fun _ : Vec d ↦ nu • (1 : Mat d)) x) p) := by
    intro _ p hp
    rw [vecDot_matVecMul_smul_one]
    refine mul_pos hnu ?_
    rcases lt_or_eq_of_le (vecNormSq_nonneg p) with h | h
    · exact h
    · exact absurd (vecNormSq_eq_zero h.symm) hp
  have hskewk : ∀ x : Vec d,
      matTranspose ((streamCutoff omega k).toCoeffField x) =
        -(streamCutoff omega k).toCoeffField x := fun x ↦ streamCutoff_skew omega k x
  have hskewh : ∀ x : Vec d,
      matTranspose ((finiteShellIncrement omega k l).toCoeffField x) =
        -(finiteShellIncrement omega k l).toCoeffField x := fun x ↦
    finiteShellIncrement_skew omega k l x
  have hsplitA : ∀ᵐ x ∂(volumeMeasureOn
      ((Book.Ch02.cubeDomain Q : Book.Ch02.Domain d) : Set (Vec d))),
      (cutoffCoeffOnCube hnu omega k Q).toCoeffField x =
        (fun _ : Vec d ↦ nu • (1 : Mat d)) x +
          (streamCutoff omega k).toCoeffField x :=
    Filter.Eventually.of_forall fun _ ↦ rfl
  have hsplitB : ∀ᵐ x ∂(volumeMeasureOn
      ((Book.Ch02.cubeDomain Q : Book.Ch02.Domain d) : Set (Vec d))),
      (cutoffCoeffOnCube hnu omega l Q).toCoeffField x =
        (cutoffCoeffOnCube hnu omega k Q).toCoeffField x +
          (finiteShellIncrement omega k l).toCoeffField x :=
    Filter.Eventually.of_forall fun x ↦
      sub_eq_iff_eq_add'.mp (coefficientCutoff_toCoeffField_sub nu omega hkl x)
  have hrelative : ∀ᵐ x ∂(volumeMeasureOn
      ((Book.Ch02.cubeDomain Q : Book.Ch02.Domain d) : Set (Vec d))),
      ∀ p r : Vec d,
        2 * vecDot r (matVecMul ((finiteShellIncrement omega k l).toCoeffField x) p) ≤
          theta *
            (vecDot p (matVecMul ((fun _ : Vec d ↦ nu • (1 : Mat d)) x) p) +
              vecDot r (matVecMul ((fun _ : Vec d ↦ nu • (1 : Mat d)) x) r)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem
      (Book.Ch02.cubeDomain Q : Book.Ch02.Domain d).measurableSet] with x hx
    intro p r
    have hxmem : x ∈ openCubeSet Q := by
      rwa [Book.Ch02.cubeDomain_coe] at hx
    have hnorm : matrixOperatorNorm (finiteShellIncrement omega k l x) ≤ M :=
      matrixOperatorNorm_finiteShellIncrement_le_linftyNormLargeCube omega k l n hxmem
    have hrhs : theta *
        (vecDot p (matVecMul ((fun _ : Vec d ↦ nu • (1 : Mat d)) x) p) +
          vecDot r (matVecMul ((fun _ : Vec d ↦ nu • (1 : Mat d)) x) r)) =
        M * (vecNormSq p + vecNormSq r) := by
      simp only [vecDot_matVecMul_smul_one, htheta]
      field_simp
    rw [hrhs]
    exact two_vecDot_le_of_matrixOperatorNorm_le hnorm p r
  have hfrozen := SuperdiffusionCLT.Frozen.Section2.coarseBlockMatrix_localization
    d (Book.Ch02.cubeDomain Q) (fun _ : Vec d ↦ nu • (1 : Mat d))
    (streamCutoff omega k).toCoeffField (finiteShellIncrement omega k l).toCoeffField
    (cutoffCoeffOnCube hnu omega k Q) (cutoffCoeffOnCube hnu omega l Q) theta
    hsymm hposdef hskewk hskewh hsplitA hsplitB hrelative
  have hDBar : DBar nu k l n omega = theta * (1 + theta) := by
    rw [htheta, DBar, ← hM]
    ring
  rw [coarseBlockMatrix_cubeSet_coefficientCutoff_eq_ch02 hnu omega l Q,
    coarseBlockMatrix_cubeSet_coefficientCutoff_eq_ch02 hnu omega k Q, hDBar]
  exact hfrozen.2

/-- The additive form of the comparison:
`bfA_l(cu_n) <= (1 + Dbar) bfA_k(cu_n)`. -/
theorem blockMatLoewnerLE_coarseBlockMatrix_coefficientCutoff_add [NeZero d]
    {nu : ℝ} (hnu : 0 < nu) (omega : ShellSeq d) {k l n : ℕ} (hkl : k ≤ l) :
    BlockMatLoewnerLE
      (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
        (coefficientCutoff nu omega l).toFun)
      ((1 + DBar nu k l n omega) •
        coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
          (coefficientCutoff nu omega k).toFun) := by
  intro X
  have h := blockMatLoewnerLE_coarseBlockMatrix_coefficientCutoff (n := n) hnu omega hkl X
  rw [blockVecDot_blockMatVecMul_ofFullBlockMat_sub, blockMatVecMul_blockSMul,
    blockVecDot_smul_right] at h
  rw [blockMatVecMul_blockSMul, blockVecDot_smul_right]
  linarith only [h]

end

end SuperdiffusionCLT.Section3.HighContrast
