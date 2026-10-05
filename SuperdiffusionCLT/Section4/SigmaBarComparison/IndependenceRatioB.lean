/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.LocalizationAverageT2Centring
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementPthMoment
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementLpLargeCube
public import SuperdiffusionCLT.Section2.Annealed.Symmetry

/-!
# Supporting lemmas for `l.shomm.vs.shomell#independence-and-ratio`

This file assembles, for the gauge `h := (k_L - k_ell)_{cu_n}` of
the paper, three facts consumed by
the independence-ratio estimate:

* `sbIndep_hMat` is the Lean carrier of `h`: the volume average of the finite
  shell increment `k_L - k_ell` on the open origin cube `cu_n`.
* `sbIndep_integral_hMat_entry_eq_zero`: `E[h] = 0`, from the negation
  symmetry `a.j.iso` (the paper: "by the negation symmetry in a.j.iso, as in the
  derivation of `khom_ell(cu_n) = 0`, `E[h] = 0`"). `h` is a
  functional of the shells strictly above `ell`, each of which the whole
  sequence negation `ShellField.negateSequence` flips in sign, so `h` is odd
  under it; `ShellLawJ4.negation` (the law's invariance under that map) then
  forces the mean to vanish, exactly as
  `Stream.integral_eq_zero_of_odd_under_negateSequence` derives
  `khom_ell(cu_n) = 0` in `Symmetry.lean`.
* `sbIndep_stronglyMeasurable_hMat_entry`: `h`'s entries are measurable with
  respect to the shell coordinates strictly above `ell`
  (`localizationUpperShells ell`), the printed "`h` ... measurable with
  respect to the scales in `(ell, L]`": each shell coordinate
  contributes to `h` only through its own value, and a finite sum/integral of
  functionals of upper coordinates stays upper-measurable.
* `sbIndep_integral_mul_eq_mul_integral`: the printed independence step
  `a.j.indy` in product form, `E[c * Y] = E[c] * E[Y]` for `c` measurable with
  respect to a coordinate family `S` and `Y` measurable with respect to a
  disjoint family `T`, reusing the partial-integral step
  `condExp_mul_eq_mul_integral_of_compl` (`LocalizationAverageT2Centring.lean`)
  and the tower property of the conditional expectation.
* `sbIndep_integral_hMat_colSq_le`: the second-moment
  bound `e.kmn.bounds` at `p = 2` ("By Jensen's inequality and
  `e.kmn.bounds` with `p=2`, `E|h|^2 ≤ C(L-ell)`"), assembled from the
  `p`-th moment display `isBigO_gammaSigma_finiteShellIncrementPthMoment` and
  the Jensen bound `ConvexOn.map_set_average_le` for the convex squaring map.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.SigmaBarComparison

open MeasureTheory Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Localization (localizationUpperShells localizationLowerShells
  localizationUpperShells_disjoint_lowerShells shellSigma_coordinate_measurable)
open SuperdiffusionCLT.Probability (shellSigma shellSigma_le_ambient
  indep_shellSigma_of_shellLawJ2 condExp_shellSigma_eq_integral_of_measurable)

noncomputable section

variable {d : ℕ}

/-! ## The gauge `h` -/

/-- **The gauge `h := (k_L - k_ell)_{cu_n}`** of the paper: the volume
average of the finite shell increment `k_L - k_ell` on the open origin cube
`cu_n`. -/
def sbIndep_hMat (ell L n : ℕ) (omega : ShellSeq d) : Mat d :=
  volumeAverageMat (openCubeSet (originCube d (n : ℤ)))
    (fun y => finiteShellIncrement omega ell L y)

/-! ## Measurability of `h` for the shells above `ell` -/

private theorem sbIndep_measurable_shellReg_upper {ell k : ℕ} (hk : ell < k) :
    Measurable[shellSigma (d := d) (localizationUpperShells ell)]
      (fun omega : ShellSeq d => shellReg omega k) :=
  ShellField.measurable_forgetShell.comp
    (shellSigma_coordinate_measurable (d := d) (S := localizationUpperShells ell) hk)

private theorem sbIndep_measurable_finiteShellIncrement_upper (ell L : ℕ) :
    Measurable[shellSigma (d := d) (localizationUpperShells ell)]
      (fun omega : ShellSeq d => finiteShellIncrement omega ell L) := by
  unfold finiteShellIncrement
  refine Finset.measurable_sum _ fun k hk => ?_
  have hk' : ell < k := (Finset.mem_Ioc.mp hk).1
  exact sbIndep_measurable_shellReg_upper hk'

/-- **`h`'s entries are measurable for the shells strictly above `ell`.** The
printed reading is that `h` is measurable with respect to the scales in `(ell, L]`. -/
theorem sbIndep_stronglyMeasurable_hMat_entry (ell L n : ℕ) (i j : Fin d) :
    StronglyMeasurable[shellSigma (d := d) (localizationUpperShells ell)]
      (fun omega : ShellSeq d => sbIndep_hMat (d := d) ell L n omega i j) := by
  rw [stronglyMeasurable_iff_measurable]
  have hM : Measurable[shellSigma (d := d) (localizationUpperShells ell)]
      (fun omega : ShellSeq d => sbIndep_hMat (d := d) ell L n omega) :=
    @measurable_volumeAverageMat_of_isBounded d (ShellSeq d)
      (shellSigma (d := d) (localizationUpperShells ell))
      (openCubeSet (originCube d (n : ℤ)))
      (isBounded_openCubeSet (originCube d (n : ℤ)))
      (measurableSet_openCubeSet (originCube d (n : ℤ)))
      (fun omega => finiteShellIncrement omega ell L)
      (sbIndep_measurable_finiteShellIncrement_upper ell L)
  exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hM)

/-! ## Oddness of `h` and `E[h] = 0` -/

private theorem sbIndep_finiteShellIncrement_negateSequence (ell L : ℕ) (omega : ShellSeq d)
    (y : Vec d) (i j : Fin d) :
    finiteShellIncrement (ShellField.negateSequence omega) ell L y i j =
      -(finiteShellIncrement omega ell L y i j) := by
  rw [finiteShellIncrement_apply_entry, finiteShellIncrement_apply_entry, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [ShellField.negateSequence_apply, ShellField.negate_apply, Matrix.neg_apply]

theorem sbIndep_hMat_negateSequence (ell L n : ℕ) (omega : ShellSeq d) :
    sbIndep_hMat (d := d) ell L n (ShellField.negateSequence omega) =
      -(sbIndep_hMat (d := d) ell L n omega) := by
  ext i j
  show volumeAverage (openCubeSet (originCube d (n : ℤ)))
      (fun y => finiteShellIncrement (ShellField.negateSequence omega) ell L y i j) =
    -volumeAverage (openCubeSet (originCube d (n : ℤ)))
      (fun y => finiteShellIncrement omega ell L y i j)
  have hfun : (fun y => finiteShellIncrement (ShellField.negateSequence omega) ell L y i j) =
      (fun y => -(finiteShellIncrement omega ell L y i j)) :=
    funext fun y => sbIndep_finiteShellIncrement_negateSequence ell L omega y i j
  rw [hfun, volumeAverage, volumeAverage, integral_neg, mul_neg]

/-- **`E[h] = 0`**: `h` is odd under the whole-sequence
negation, and `ShellLawJ4` makes the law invariant under it. -/
theorem sbIndep_integral_hMat_entry_eq_zero {P : ProbabilityMeasure (ShellSeq d)}
    (hJ4 : ShellLawJ4 d P) (ell L n : ℕ) (i j : Fin d) :
    ∫ omega, sbIndep_hMat (d := d) ell L n omega i j ∂P.toMeasure = 0 := by
  have hmeas : Measurable (fun omega : ShellSeq d => sbIndep_hMat (d := d) ell L n omega i j) :=
    ((sbIndep_stronglyMeasurable_hMat_entry ell L n i j).mono
      (shellSigma_le_ambient (d := d) (localizationUpperShells ell))).measurable
  refine SuperdiffusionCLT.Section2.Estimates.Stream.integral_eq_zero_of_odd_under_negateSequence
    hJ4 hmeas ?_
  intro omega
  rw [sbIndep_hMat_negateSequence]
  rfl

/-! ## The independence product formula `a.j.indy` -/

/-- **`E[c * Y] = E[c] * E[Y]`** for `c` measurable with respect to a
coordinate family `S` and `Y` measurable with respect to a disjoint family
`T`, under `ShellLawJ2`: the printed independence step `a.j.indy` in product
form. This is the partial-integral step
`condExp_mul_eq_mul_integral_of_compl` (`LocalizationAverageT2Centring.lean`)
composed with the tower property of the conditional expectation. -/
theorem sbIndep_integral_mul_eq_mul_integral {P : ProbabilityMeasure (ShellSeq d)}
    {S T : Set ℕ} (hST : Disjoint S T) (hJ2 : ShellLawJ2 d P)
    {c Y : ShellSeq d → ℝ}
    (hc : StronglyMeasurable[shellSigma (d := d) S] c)
    (hY : StronglyMeasurable[shellSigma (d := d) T] Y)
    (hYint : Integrable Y P.toMeasure) (hcYint : Integrable (c * Y) P.toMeasure) :
    ∫ omega, c omega * Y omega ∂P.toMeasure =
      (∫ omega, c omega ∂P.toMeasure) * (∫ omega, Y omega ∂P.toMeasure) := by
  have hfin : IsFiniteMeasure (P.toMeasure.trim (shellSigma_le_ambient (d := d) S)) :=
    isFiniteMeasure_trim _
  have hcond := SuperdiffusionCLT.Section2.Localization.condExp_mul_eq_mul_integral_of_compl
    (d := d) hST hJ2.independent hc hY hYint hcYint
  have htower := MeasureTheory.integral_condExp (μ := P.toMeasure)
    (shellSigma_le_ambient (d := d) S) (f := c * Y)
  have hgoal : ∫ omega, (c * Y) omega ∂P.toMeasure =
      (∫ omega, c omega ∂P.toMeasure) * (∫ omega, Y omega ∂P.toMeasure) := by
    rw [← htower, MeasureTheory.integral_congr_ae hcond, MeasureTheory.integral_mul_const]
  simpa only [Pi.mul_apply] using hgoal

/-! ## Integrability of `h`'s entries and the moment bound -/

private theorem sbIndep_volumeAverage_cubeSet_eq_openCubeSet (Q : TriadicCube d) (f : Vec d → ℝ) :
    volumeAverage (cubeSet Q) f = volumeAverage (openCubeSet Q) f := by
  simp only [volumeAverage, volume_openCubeSet_eq_volume_cubeSet]
  rw [MeasureTheory.setIntegral_congr_set (cubeSet_ae_eq_openCubeSet Q)]

private theorem sbIndep_volume_openCubeSet_ne_zero (n : ℕ) :
    volume (openCubeSet (originCube d (n : ℤ))) ≠ 0 := by
  rw [volume_openCubeSet_eq_volume_cubeSet]
  intro h0
  have hreal := volume_cubeSet_toReal (originCube d (n : ℤ))
  rw [h0, ENNReal.toReal_zero] at hreal
  exact absurd hreal.symm (cubeVolume_pos (originCube d (n : ℤ))).ne'

private theorem sbIndep_volume_openCubeSet_ne_top (n : ℕ) :
    volume (openCubeSet (originCube d (n : ℤ))) ≠ ⊤ :=
  (volume_openCubeSet_lt_top (originCube d (n : ℤ))).ne

private theorem sbIndep_integrableOn_finiteShellIncrement_entry (omega : ShellSeq d) (ell L n : ℕ)
    (i j : Fin d) :
    IntegrableOn (fun x => finiteShellIncrement omega ell L x i j)
      (openCubeSet (originCube d (n : ℤ))) volume := by
  have hg : IntegrableOn (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x))
      (openCubeSet (originCube d (n : ℤ))) volume := by
    have h := SuperdiffusionCLT.Section2.Estimates.Stream.integrableOn_matrixOperatorNorm_rpow_finiteShellIncrement
      omega ell L n (p := (1 : ℝ)) (by norm_num)
    simpa only [Real.rpow_one] using h
  have hmeas : AEStronglyMeasurable (fun x => finiteShellIncrement omega ell L x i j)
      (volume.restrict (openCubeSet (originCube d (n : ℤ)))) :=
    ((finiteShellIncrement omega ell L).entry_measurable i j).aestronglyMeasurable.restrict
  refine Integrable.mono' hg hmeas ?_
  filter_upwards [ae_restrict_mem (measurableSet_openCubeSet (originCube d (n : ℤ)))] with x _
  rw [Real.norm_eq_abs]
  exact abs_entry_le_matrixOperatorNorm _ i j

variable [NeZero d]

/-- **`|h_{i0}| ≤ ⨍_{cu_n} |k_L - k_ell|`**: the triangle inequality for the
volume average combined with the entrywise domination of a matrix by its
operator norm. -/
private theorem sbIndep_abs_hMat_le (omega : ShellSeq d) (ell L n : ℕ) (i : Fin d) :
    |sbIndep_hMat (d := d) ell L n omega i 0| ≤
      volumeAverage (openCubeSet (originCube d (n : ℤ)))
        (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x)) := by
  show |volumeAverage (openCubeSet (originCube d (n : ℤ)))
      (fun x => finiteShellIncrement omega ell L x i 0)| ≤ _
  set U : Set (Vec d) := openCubeSet (originCube d (n : ℤ)) with hUdef
  have hint := sbIndep_integrableOn_finiteShellIncrement_entry omega ell L n i 0
  have hgint : IntegrableOn (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x))
      U volume := by
    have h := SuperdiffusionCLT.Section2.Estimates.Stream.integrableOn_matrixOperatorNorm_rpow_finiteShellIncrement
      omega ell L n (p := (1 : ℝ)) (by norm_num)
    simpa only [Real.rpow_one] using h
  have habs1 : |∫ x in U, finiteShellIncrement omega ell L x i 0 ∂volume| ≤
      ∫ x in U, |finiteShellIncrement omega ell L x i 0| ∂volume := by
    simpa only [Real.norm_eq_abs] using
      norm_integral_le_integral_norm (μ := volume.restrict U)
        (f := fun x => finiteShellIncrement omega ell L x i 0)
  have habs2 : ∫ x in U, |finiteShellIncrement omega ell L x i 0| ∂volume ≤
      ∫ x in U, matrixOperatorNorm (finiteShellIncrement omega ell L x) ∂volume := by
    refine MeasureTheory.setIntegral_mono hint.abs hgint fun x => ?_
    exact abs_entry_le_matrixOperatorNorm _ i 0
  have hcnn : (0:ℝ) ≤ (volume U).toReal⁻¹ := inv_nonneg.2 ENNReal.toReal_nonneg
  calc |volumeAverage U (fun x => finiteShellIncrement omega ell L x i 0)|
      = (volume U).toReal⁻¹ * |∫ x in U, finiteShellIncrement omega ell L x i 0 ∂volume| := by
        rw [volumeAverage, abs_mul, abs_of_nonneg hcnn]
    _ ≤ (volume U).toReal⁻¹ * ∫ x in U, |finiteShellIncrement omega ell L x i 0| ∂volume :=
        mul_le_mul_of_nonneg_left habs1 hcnn
    _ ≤ (volume U).toReal⁻¹ * ∫ x in U, matrixOperatorNorm (finiteShellIncrement omega ell L x) ∂volume :=
        mul_le_mul_of_nonneg_left habs2 hcnn
    _ = volumeAverage U (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x)) := rfl

omit [NeZero d] in
/-- **The Jensen step**: `(⨍ g)^2 ≤ ⨍ (g^2)` for the normalized average over
`cu_n`, `g ω x := |(k_L - k_ell)(x)|` (the pointwise operator-norm size). -/
private theorem sbIndep_sq_volumeAverage_matrixOperatorNorm_le (omega : ShellSeq d) (ell L n : ℕ) :
    (volumeAverage (openCubeSet (originCube d (n : ℤ)))
        (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x))) ^ 2 ≤
      volumeAverage (openCubeSet (originCube d (n : ℤ)))
        (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ 2) := by
  set U : Set (Vec d) := openCubeSet (originCube d (n : ℤ)) with hUdef
  set g : Vec d → ℝ := fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x) with hgdef
  have hg1 : IntegrableOn g U volume := by
    have h := SuperdiffusionCLT.Section2.Estimates.Stream.integrableOn_matrixOperatorNorm_rpow_finiteShellIncrement
      omega ell L n (p := (1 : ℝ)) (by norm_num)
    simpa only [Real.rpow_one] using h
  have hg2 : IntegrableOn (fun x => g x ^ 2) U volume := by
    have h := SuperdiffusionCLT.Section2.Estimates.Stream.integrableOn_matrixOperatorNorm_rpow_finiteShellIncrement
      omega ell L n (p := (2 : ℝ)) (by norm_num)
    have h2 : (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ (2 : ℝ)) =
        fun x => g x ^ (2 : ℕ) := by
      funext x
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rwa [h2] at h
  have hconv : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) := Even.convexOn_pow (by decide)
  have hJensen := hconv.map_set_average_le
    (hgc := (continuous_pow 2).continuousOn) (hsc := isClosed_univ)
    (h0 := sbIndep_volume_openCubeSet_ne_zero n) (ht := sbIndep_volume_openCubeSet_ne_top n)
    (hfs := Filter.Eventually.of_forall fun x => Set.mem_univ (g x))
    (hfi := hg1) (hgi := hg2)
  have heq : ⨍ x in U, g x ∂volume = volumeAverage U g :=
    (SuperdiffusionCLT.Probability.volumeAverage_eq_setAverage U g).symm
  have heq2 : (⨍ x in U, g x ^ 2 ∂volume) = volumeAverage U (fun x => g x ^ 2) :=
    (SuperdiffusionCLT.Probability.volumeAverage_eq_setAverage U (fun x => g x ^ 2)).symm
  rw [heq, heq2] at hJensen
  exact hJensen

omit [NeZero d] in
theorem sbIndep_measurable_volumeAverage_matrixOperatorNorm_rpow (ell L n : ℕ) {p : ℝ}
    (hp : (0 : ℝ) ≤ p) :
    Measurable (fun omega : ShellSeq d =>
      volumeAverage (cubeSet (originCube d (n : ℤ)))
        (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ p)) := by
  have hjoint : Measurable (Function.uncurry
      (fun (omega : ShellSeq d) (x : Vec d) =>
        matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ p)) := by
    have h := SuperdiffusionCLT.Section2.Estimates.Stream.measurable_uncurry_matrixOperatorNorm_rpow_finiteShellIncrement
      (d := d) ell L (p := p) hp
    have hswap : (Function.uncurry
        (fun (omega : ShellSeq d) (x : Vec d) =>
          matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ p)) =
        (Function.uncurry
          (fun (x : Vec d) (omega : ShellSeq d) =>
            matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ p)) ∘ Prod.swap := by
      funext q
      simp only [Function.uncurry, Function.comp, Prod.swap]
    rw [hswap]
    exact h.comp measurable_swap
  have hSF : SFinite (volume.restrict (cubeSet (originCube d (n : ℤ)))) := inferInstance
  have hSM : StronglyMeasurable fun omega : ShellSeq d =>
      ∫ x, matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ p
        ∂(volume.restrict (cubeSet (originCube d (n : ℤ)))) :=
    haveI := hSF
    MeasureTheory.StronglyMeasurable.integral_prod_right hjoint.stronglyMeasurable
  have hM : Measurable (fun omega : ShellSeq d =>
      ∫ x in cubeSet (originCube d (n : ℤ)),
        matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ p ∂volume) :=
    hSM.measurable
  exact hM.const_mul _

/-- **The moment-bound constant**, `d`-only (no dependence on `nu`, `P`, `L`,
`ell`): exposed by name so that a uniform outer constant can be chosen before
`nu`, `P`, `L`, `ell` are fixed, matching this development's `∃ C, 1 ≤ C ∧
∀ nu, ...` shape. -/
def sbIndep_Cmom0 (d : ℕ) : ℝ :=
  (Fintype.card (Fin d) : ℝ) * IndependentSums.gammaMomentConst 1 *
    SuperdiffusionCLT.Section2.Estimates.Stream.finiteShellIncrementPthMomentConst d 2 ^ 2

theorem sbIndep_Cmom0_nonneg (d : ℕ) : 0 ≤ sbIndep_Cmom0 d :=
  mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (IndependentSums.gammaMomentConst_pos (by norm_num)).le) (sq_nonneg _)

/-- **The second-moment bound `e.kmn.bounds` at `p = 2`**:
"By Jensen's inequality and `e.kmn.bounds` with `p=2`, `E|h|^2 ≤ C(L-ell)`". -/
theorem sbIndep_integral_hMat_colSq_le {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) {ell L : ℕ} (hellL : ell < L) (n : ℕ) :
    ∫ omega, (∑ i : Fin d, (sbIndep_hMat (d := d) ell L n omega i 0) ^ 2) ∂P.toMeasure ≤
        sbIndep_Cmom0 d * ((L : ℝ) - (ell : ℝ)) := by
  set Y : ShellSeq d → ℝ := fun omega =>
      volumeAverage (openCubeSet (originCube d (n : ℤ)))
        (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ 2) with hYdef
  have hpoint : ∀ omega : ShellSeq d, ∀ i : Fin d,
      (sbIndep_hMat (d := d) ell L n omega i 0) ^ 2 ≤ Y omega := by
    intro omega i
    have h1 := sbIndep_abs_hMat_le omega ell L n i
    have h2 : (sbIndep_hMat (d := d) ell L n omega i 0) ^ 2 ≤
        (volumeAverage (openCubeSet (originCube d (n : ℤ)))
          (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x))) ^ 2 := by
      rw [← sq_abs (sbIndep_hMat (d := d) ell L n omega i 0)]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    exact h2.trans (sbIndep_sq_volumeAverage_matrixOperatorNorm_le omega ell L n)
  have hsum_le : ∀ omega : ShellSeq d,
      (∑ i : Fin d, (sbIndep_hMat (d := d) ell L n omega i 0) ^ 2) ≤ (Fintype.card (Fin d) : ℝ) * Y omega := by
    intro omega
    calc (∑ i : Fin d, (sbIndep_hMat (d := d) ell L n omega i 0) ^ 2) ≤
        ∑ _i : Fin d, Y omega := Finset.sum_le_sum fun i _ => hpoint omega i
      _ = (Fintype.card (Fin d) : ℝ) * Y omega := by
          rw [Finset.sum_const, Fintype.card, nsmul_eq_mul]
  have hYeq : Y = fun omega => volumeAverage (cubeSet (originCube d (n : ℤ)))
      (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ 2) := by
    funext omega
    rw [hYdef, sbIndep_volumeAverage_cubeSet_eq_openCubeSet]
  have hYmeas : Measurable Y := by
    rw [hYeq]
    have h2 : (fun omega : ShellSeq d => volumeAverage (cubeSet (originCube d (n : ℤ)))
        (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ 2)) =
        (fun omega : ShellSeq d => volumeAverage (cubeSet (originCube d (n : ℤ)))
        (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ (2 : ℝ))) := by
      funext omega
      congr 1
      funext x
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [h2]
    exact sbIndep_measurable_volumeAverage_matrixOperatorNorm_rpow ell L n (by norm_num : (0:ℝ) ≤ (2:ℝ))
  have hSpos := SuperdiffusionCLT.Section2.Estimates.Stream.streamLinftyConst_pos hPrefix
  have hgm : (0 : ℝ) < Real.exp 1 * IndependentSums.gammaMomentConst (2 / 2) :=
    mul_pos (Real.exp_pos 1) (IndependentSums.gammaMomentConst_pos (by norm_num))
  have hCpos : 0 < SuperdiffusionCLT.Section2.Estimates.Stream.finiteShellIncrementPthMomentConst d 2 := by
    rw [SuperdiffusionCLT.Section2.Estimates.Stream.finiteShellIncrementPthMomentConst]
    exact mul_pos (Real.rpow_pos_of_pos hgm _) hSpos
  have hLellPos : (0 : ℝ) < ((L - ell : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hellL
  have hbig := SuperdiffusionCLT.Section2.Estimates.Stream.isBigO_gammaSigma_finiteShellIncrementPthMoment
    hPrefix hJ2 hJ3 hJ4 (p := (2 : ℝ)) (by norm_num) hellL (originCube d (n : ℤ))
  rw [show (2 : ℝ) / 2 = (1 : ℝ) by norm_num] at hbig
  set X : ShellSeq d → ℝ := fun omega => volumeAverage (cubeSet (originCube d (n : ℤ)))
      (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ (2 : ℝ)) with hXdef
  set K : ℝ := SuperdiffusionCLT.Section2.Estimates.Stream.finiteShellIncrementPthMomentConst d 2 ^ (2 : ℝ) *
      Real.sqrt (((L - ell : ℕ) : ℝ)) ^ (2 : ℝ) with hKdef
  -- `hbig : IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 1) X K`
  have hXnn : ∀ omega : ShellSeq d, 0 ≤ X omega := by
    intro omega
    show 0 ≤ volumeAverage (cubeSet (originCube d (n : ℤ)))
      (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ (2 : ℝ))
    rw [volumeAverage]
    exact mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
      (integral_nonneg fun x => Real.rpow_nonneg (matrixOperatorNorm_nonneg _) 2)
  have hXmeas : Measurable X := sbIndep_measurable_volumeAverage_matrixOperatorNorm_rpow ell L n (by norm_num : (0:ℝ) ≤ (2:ℝ))
  have hK : 0 < K :=
    mul_pos (Real.rpow_pos_of_pos hCpos 2) (Real.rpow_pos_of_pos (Real.sqrt_pos.2 hLellPos) 2)
  have hYX : Y = X := by
    rw [hYeq, hXdef]
    funext omega
    congr 1
    funext x
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hbigWith : IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma (1 : ℝ)) X K := by
    have heqabs : (fun omega => |X omega|) = X := funext fun omega => abs_of_nonneg (hXnn omega)
    rw [IndependentSums.IsBigO, heqabs] at hbig
    exact hbig
  have hXint1 : Integrable (fun omega => X omega ^ (1 : ℝ)) P.toMeasure :=
    IndependentSums.integrable_rpow_of_isBigOWith_gammaSigma
      (by norm_num) hK le_rfl hXnn hXmeas.aemeasurable hbigWith
  have hXint : Integrable X P.toMeasure := by
    simpa only [Real.rpow_one] using hXint1
  have hYint : Integrable Y P.toMeasure := by
    rw [hYX]
    exact hXint
  have hcardY : Integrable (fun omega => (Fintype.card (Fin d) : ℝ) * Y omega) P.toMeasure :=
    hYint.const_mul _
  have hsum_nonneg : 0 ≤ᵐ[P.toMeasure]
      fun omega => ∑ i : Fin d, (sbIndep_hMat (d := d) ell L n omega i 0) ^ 2 :=
    Filter.Eventually.of_forall fun omega => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hXbound : ∫ omega, X omega ∂P.toMeasure ≤ IndependentSums.gammaMomentConst 1 * K := by
    have hraw := IndependentSums.integral_abs_rpow_le_of_isBigO_gammaSigma
      (μ := P.toMeasure) (X := X) (K := K) (σ := (1 : ℝ)) (p := (1 : ℝ))
      (by norm_num) hK le_rfl hXmeas.aemeasurable hbig
    have heqabs2 : (fun omega => |X omega| ^ (1 : ℝ)) = X := by
      funext omega
      rw [abs_of_nonneg (hXnn omega), Real.rpow_one]
    rw [heqabs2] at hraw
    have hrhs : IndependentSums.gammaMomentConst 1 * (1 : ℝ) ^ (1 : ℝ)⁻¹ * K =
        IndependentSums.gammaMomentConst 1 * K := by
      rw [Real.one_rpow, mul_one]
    rwa [hrhs, Real.rpow_one] at hraw
  have hKeq : K = SuperdiffusionCLT.Section2.Estimates.Stream.finiteShellIncrementPthMomentConst d 2 ^ 2 *
      ((L : ℝ) - (ell : ℝ)) := by
    rw [hKdef, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.rpow_natCast,
      Real.sq_sqrt hLellPos.le]
    congr 1
    exact_mod_cast (Nat.cast_sub hellL.le : ((L - ell : ℕ) : ℝ) = (L : ℝ) - (ell : ℝ))
  have hint_le : ∫ omega, (∑ i : Fin d, (sbIndep_hMat (d := d) ell L n omega i 0) ^ 2) ∂P.toMeasure ≤
      ∫ omega, (Fintype.card (Fin d) : ℝ) * Y omega ∂P.toMeasure :=
    MeasureTheory.integral_mono_of_nonneg hsum_nonneg hcardY
      (Filter.Eventually.of_forall fun omega => hsum_le omega)
  rw [sbIndep_Cmom0]
  calc ∫ omega, (∑ i : Fin d, (sbIndep_hMat (d := d) ell L n omega i 0) ^ 2) ∂P.toMeasure ≤
      ∫ omega, (Fintype.card (Fin d) : ℝ) * Y omega ∂P.toMeasure := hint_le
    _ = (Fintype.card (Fin d) : ℝ) * ∫ omega, Y omega ∂P.toMeasure :=
        MeasureTheory.integral_const_mul _ _
    _ = (Fintype.card (Fin d) : ℝ) * ∫ omega, X omega ∂P.toMeasure := by rw [hYX]
    _ ≤ (Fintype.card (Fin d) : ℝ) * (IndependentSums.gammaMomentConst 1 * K) :=
        mul_le_mul_of_nonneg_left hXbound (Nat.cast_nonneg _)
    _ = (Fintype.card (Fin d) : ℝ) * IndependentSums.gammaMomentConst 1 *
        SuperdiffusionCLT.Section2.Estimates.Stream.finiteShellIncrementPthMomentConst d 2 ^ 2 *
        ((L : ℝ) - (ell : ℝ)) := by
        rw [hKeq]; ring

/-- **`h`'s entries are integrable** (`e.kmn.bounds` at `p = 1`), needed for
the independence product formula to apply to `h` itself. -/
theorem sbIndep_integrable_hMat_entry {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) {ell L : ℕ} (hellL : ell < L) (n : ℕ) (i : Fin d) :
    Integrable (fun omega => sbIndep_hMat (d := d) ell L n omega i 0) P.toMeasure := by
  set Z : ShellSeq d → ℝ := fun omega => volumeAverage (cubeSet (originCube d (n : ℤ)))
      (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ (1 : ℝ)) with hZdef
  have hZnn : ∀ omega : ShellSeq d, 0 ≤ Z omega := by
    intro omega
    show 0 ≤ volumeAverage (cubeSet (originCube d (n : ℤ)))
      (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ (1 : ℝ))
    rw [volumeAverage]
    exact mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
      (integral_nonneg fun x => Real.rpow_nonneg (matrixOperatorNorm_nonneg _) 1)
  have hZmeas : Measurable Z :=
    sbIndep_measurable_volumeAverage_matrixOperatorNorm_rpow ell L n (by norm_num : (0 : ℝ) ≤ (1 : ℝ))
  have hSpos := SuperdiffusionCLT.Section2.Estimates.Stream.streamLinftyConst_pos hPrefix
  have hgm : (0 : ℝ) < Real.exp 1 * IndependentSums.gammaMomentConst (2 / 1) :=
    mul_pos (Real.exp_pos 1) (IndependentSums.gammaMomentConst_pos (by norm_num))
  have hCpos : 0 < SuperdiffusionCLT.Section2.Estimates.Stream.finiteShellIncrementPthMomentConst d 1 := by
    rw [SuperdiffusionCLT.Section2.Estimates.Stream.finiteShellIncrementPthMomentConst]
    exact mul_pos (Real.rpow_pos_of_pos hgm _) hSpos
  have hLellPos : (0 : ℝ) < ((L - ell : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hellL
  have hbig := SuperdiffusionCLT.Section2.Estimates.Stream.isBigO_gammaSigma_finiteShellIncrementPthMoment
    hPrefix hJ2 hJ3 hJ4 (p := (1 : ℝ)) le_rfl hellL (originCube d (n : ℤ))
  set K : ℝ := SuperdiffusionCLT.Section2.Estimates.Stream.finiteShellIncrementPthMomentConst d 1 ^ (1 : ℝ) *
      Real.sqrt (((L - ell : ℕ) : ℝ)) ^ (1 : ℝ) with hKdef
  have hK : 0 < K :=
    mul_pos (Real.rpow_pos_of_pos hCpos 1) (Real.rpow_pos_of_pos (Real.sqrt_pos.2 hLellPos) 1)
  have hbigWith : IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma (2 / 1)) Z K := by
    have heqabs : (fun omega => |Z omega|) = Z := funext fun omega => abs_of_nonneg (hZnn omega)
    rw [IndependentSums.IsBigO, heqabs] at hbig
    exact hbig
  have hZint1 : Integrable (fun omega => Z omega ^ (1 : ℝ)) P.toMeasure :=
    IndependentSums.integrable_rpow_of_isBigOWith_gammaSigma
      (by norm_num) hK le_rfl hZnn hZmeas.aemeasurable hbigWith
  have hZint : Integrable Z P.toMeasure := by simpa only [Real.rpow_one] using hZint1
  have hZint' : Integrable (fun omega => volumeAverage (cubeSet (originCube d (n : ℤ)))
      (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x))) P.toMeasure := by
    have heq : Z = fun omega => volumeAverage (cubeSet (originCube d (n : ℤ)))
        (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x)) := by
      rw [hZdef]
      funext omega
      congr 1
      funext x
      rw [Real.rpow_one]
    rwa [heq] at hZint
  have hZint'' : Integrable (fun omega => volumeAverage (openCubeSet (originCube d (n : ℤ)))
      (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x))) P.toMeasure := by
    have heq2 : (fun omega => volumeAverage (openCubeSet (originCube d (n : ℤ)))
        (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x))) =
        (fun omega => volumeAverage (cubeSet (originCube d (n : ℤ)))
        (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x))) := by
      funext omega
      exact (sbIndep_volumeAverage_cubeSet_eq_openCubeSet _ _).symm
    rwa [heq2]
  have hmeas : AEStronglyMeasurable (fun omega => sbIndep_hMat (d := d) ell L n omega i 0) P.toMeasure :=
    ((sbIndep_stronglyMeasurable_hMat_entry ell L n i 0).mono
      (shellSigma_le_ambient (d := d) (localizationUpperShells ell))).measurable.aestronglyMeasurable
  refine Integrable.mono' hZint'' hmeas ?_
  filter_upwards with omega
  rw [Real.norm_eq_abs]
  exact sbIndep_abs_hMat_le omega ell L n i

/-- **`h`'s entries squared are integrable** (`e.kmn.bounds` at `p = 2`,
Jensen form), the `L^2` companion of `sbIndep_integrable_hMat_entry`. -/
theorem sbIndep_integrable_hMat_entry_sq {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) {ell L : ℕ} (hellL : ell < L) (n : ℕ) (i : Fin d) :
    Integrable (fun omega => (sbIndep_hMat (d := d) ell L n omega i 0) ^ 2) P.toMeasure := by
  set Y : ShellSeq d → ℝ := fun omega =>
      volumeAverage (openCubeSet (originCube d (n : ℤ)))
        (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ 2) with hYdef
  have hpoint : ∀ omega : ShellSeq d,
      (sbIndep_hMat (d := d) ell L n omega i 0) ^ 2 ≤ Y omega := by
    intro omega
    have h1 := sbIndep_abs_hMat_le omega ell L n i
    have h2 : (sbIndep_hMat (d := d) ell L n omega i 0) ^ 2 ≤
        (volumeAverage (openCubeSet (originCube d (n : ℤ)))
          (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x))) ^ 2 := by
      rw [← sq_abs (sbIndep_hMat (d := d) ell L n omega i 0)]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    exact h2.trans (sbIndep_sq_volumeAverage_matrixOperatorNorm_le omega ell L n)
  have hYeq : Y = fun omega => volumeAverage (cubeSet (originCube d (n : ℤ)))
      (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ 2) := by
    funext omega
    rw [hYdef, sbIndep_volumeAverage_cubeSet_eq_openCubeSet]
  set X : ShellSeq d → ℝ := fun omega => volumeAverage (cubeSet (originCube d (n : ℤ)))
      (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ (2 : ℝ)) with hXdef
  have hXnn : ∀ omega : ShellSeq d, 0 ≤ X omega := by
    intro omega
    show 0 ≤ volumeAverage (cubeSet (originCube d (n : ℤ)))
      (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ (2 : ℝ))
    rw [volumeAverage]
    exact mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
      (integral_nonneg fun x => Real.rpow_nonneg (matrixOperatorNorm_nonneg _) 2)
  have hXmeas : Measurable X :=
    sbIndep_measurable_volumeAverage_matrixOperatorNorm_rpow ell L n (by norm_num : (0 : ℝ) ≤ (2 : ℝ))
  have hSpos := SuperdiffusionCLT.Section2.Estimates.Stream.streamLinftyConst_pos hPrefix
  have hgm : (0 : ℝ) < Real.exp 1 * IndependentSums.gammaMomentConst (2 / 2) :=
    mul_pos (Real.exp_pos 1) (IndependentSums.gammaMomentConst_pos (by norm_num))
  have hCpos : 0 < SuperdiffusionCLT.Section2.Estimates.Stream.finiteShellIncrementPthMomentConst d 2 := by
    rw [SuperdiffusionCLT.Section2.Estimates.Stream.finiteShellIncrementPthMomentConst]
    exact mul_pos (Real.rpow_pos_of_pos hgm _) hSpos
  have hLellPos : (0 : ℝ) < ((L - ell : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hellL
  have hbig := SuperdiffusionCLT.Section2.Estimates.Stream.isBigO_gammaSigma_finiteShellIncrementPthMoment
    hPrefix hJ2 hJ3 hJ4 (p := (2 : ℝ)) (by norm_num) hellL (originCube d (n : ℤ))
  rw [show (2 : ℝ) / 2 = (1 : ℝ) by norm_num] at hbig
  set K : ℝ := SuperdiffusionCLT.Section2.Estimates.Stream.finiteShellIncrementPthMomentConst d 2 ^ (2 : ℝ) *
      Real.sqrt (((L - ell : ℕ) : ℝ)) ^ (2 : ℝ) with hKdef
  have hK : 0 < K :=
    mul_pos (Real.rpow_pos_of_pos hCpos 2) (Real.rpow_pos_of_pos (Real.sqrt_pos.2 hLellPos) 2)
  have hYX : Y = X := by
    rw [hYeq, hXdef]
    funext omega
    congr 1
    funext x
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hbigWith : IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma (1 : ℝ)) X K := by
    have heqabs : (fun omega => |X omega|) = X := funext fun omega => abs_of_nonneg (hXnn omega)
    rw [IndependentSums.IsBigO, heqabs] at hbig
    exact hbig
  have hXint1 : Integrable (fun omega => X omega ^ (1 : ℝ)) P.toMeasure :=
    IndependentSums.integrable_rpow_of_isBigOWith_gammaSigma
      (by norm_num) hK le_rfl hXnn hXmeas.aemeasurable hbigWith
  have hXint : Integrable X P.toMeasure := by
    simpa only [Real.rpow_one] using hXint1
  have hYint : Integrable Y P.toMeasure := by
    rw [hYX]
    exact hXint
  have hmeas : AEStronglyMeasurable
      (fun omega => (sbIndep_hMat (d := d) ell L n omega i 0) ^ 2) P.toMeasure :=
    (((sbIndep_stronglyMeasurable_hMat_entry ell L n i 0).mono
      (shellSigma_le_ambient (d := d) (localizationUpperShells ell))).measurable.pow_const 2).aestronglyMeasurable
  refine Integrable.mono' hYint hmeas ?_
  filter_upwards with omega
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hpoint omega

end

end SuperdiffusionCLT.Section4.SigmaBarComparison
