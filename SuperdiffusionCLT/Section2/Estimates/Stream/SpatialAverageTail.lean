/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellField.SpatialAverageColoring
public import SuperdiffusionCLT.Assumptions.ShellLaw.EntryConsequences
public import SuperdiffusionCLT.Probability.GammaSigmaHelpers

/-!
# The one-shell spatial-average tail

Display `e.jk.spatialavg`: for every shell `k`, every scale `h` and
every centre `y`, the spatial average of shell `k` over the translated cube
`y + cu_h` obeys

`|(j_k)_{y + cu_h}| ≤ O_{Γ₂}(C 3^{-(d/2)((h - k) ∨ 0)})`.

The proof splits at `h = k`. Below that scale the average is dominated by the
`L∞` value norm of the shell on the cube, which is the J3 observable
transported by the stationarity of the prefix law. Above it the cube is
partitioned into `3 ^ (d (h - k))` translated scale-`k` cubes; those cubes are
sorted into the colour classes of `SpatialAverageColoring`, so that two
distinct cubes of one colour are separated at the J1 range `3 ^ k √d`. Within
a colour class the sub-averages are mutually independent by J1 and centred by
the negation half of J4, so the independent-sum concentration of the CoarseGraining
library applies; the finite triangle inequality over the colours and then over the matrix entries
finishes the proof.

## Main definitions

* `spatialAverageColorConst`, `spatialAverageTailConst`: the explicit
  dimension-only constants.

## Main results

* `isBigO_gammaSigma_shellSpatialAverage_entry`: the entrywise display.
* `isBigOWith_gammaSigma_matrixOperatorNorm_shellSpatialAverage`: the matrix
  operator-norm display `e.jk.spatialavg`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Estimates.Stream

open Homogenization MeasureTheory ProbabilityTheory
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Assumptions.ShellField

noncomputable section

variable {d : ℕ}
variable {P : ProbabilityMeasure (ℕ → ShellField d)}

instance instNonemptyShellCubeColor (d : ℕ) : Nonempty (ShellCubeColor d) :=
  ⟨fun _ ↦ ⟨0, shellColorPeriod_pos d⟩⟩

/-! ## One translated cube average -/

theorem measurable_translatedShellCubeAverage_entry_coordinate
    (k : ℕ) (y : Vec d) (Q : TriadicCube d) (i l : Fin d) :
    Measurable (fun omega : ℕ → ShellField d ↦
      translatedShellCubeAverage y Q (omega k) i l) := by
  have hrow : Measurable (fun A : Mat d ↦ A i) := measurable_pi_apply i
  have hcol : Measurable (fun v : Fin d → ℝ ↦ v l) := measurable_pi_apply l
  exact ((hcol.comp hrow).comp
    (measurable_translatedShellCubeAverage y Q)).comp
    (ShellField.measurable_shellCoordinate k)

/-- Unit-scale symmetric `Γ₂` tail for one entry of one translated cube
average, for any cube contained in a translate of the natural scale-`k` cube.
Only the prefix stationarity and J3 are used. -/
theorem isBigO_gammaSigma_translatedShellCubeAverage_entry
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) (k : ℕ)
    (y z : Vec d) (Q : TriadicCube d) (i l : Fin d)
    (hQ : ∀ x ∈ openCubeSet Q, x - z ∈ openCubeSet (originCube d (k : ℤ))) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ℕ → ShellField d ↦
        translatedShellCubeAverage y Q (omega k) i l) 1 := by
  have hOrigin : IndependentSums.IsBigOWith P.toMeasure
      (IndependentSums.gammaSigma 2)
      (fun omega : ℕ → ShellField d ↦ shellCubeValueNorm k (omega k)) 1 :=
    (hJ3.isBigOWith_gammaSigma_j3Observable_coordinate k).of_le
      fun F ↦ shellCubeValueNorm_le_j3Observable k (F k)
  have hTranslated := hPrefix.isBigOWith_gammaSigma_shellObservable_translate k
    (z + y) (F := fun jf : ShellField d ↦ shellCubeValueNorm k jf)
    (shellCubeValueNorm_measurable k) hOrigin
  show IndependentSums.IsBigOWith _ _ _ _
  exact hTranslated.of_le fun omega ↦
    abs_translatedShellCubeAverage_entry_le y z Q k (omega k) i l hQ

/-- Whole-sequence negation symmetry centres every entry of every translated
cube average. -/
theorem integral_translatedShellCubeAverage_entry_eq_zero
    (hJ4 : ShellLawJ4 d P) (k : ℕ) (y : Vec d) (Q : TriadicCube d)
    (i l : Fin d) :
    ∫ omega : ℕ → ShellField d,
        translatedShellCubeAverage y Q (omega k) i l ∂P.toMeasure = 0 := by
  set X : (ℕ → ShellField d) → ℝ := fun omega ↦
    translatedShellCubeAverage y Q (omega k) i l with hXdef
  have hXMeas : Measurable X :=
    measurable_translatedShellCubeAverage_entry_coordinate k y Q i l
  have hNegLaw : Measure.map (ShellField.negateSequence (d := d)) P.toMeasure =
      P.toMeasure := by
    have h := congrArg ProbabilityMeasure.toMeasure hJ4.negation
    change Measure.map (ShellField.negateSequence (d := d)) P.toMeasure =
      P.toMeasure at h
    exact h
  have hEq : (∫ omega, X omega ∂P.toMeasure) = -∫ omega, X omega ∂P.toMeasure := by
    calc
      ∫ omega, X omega ∂P.toMeasure =
          ∫ omega, X omega
            ∂Measure.map (ShellField.negateSequence (d := d)) P.toMeasure := by
        rw [hNegLaw]
      _ = ∫ omega, X (ShellField.negateSequence omega) ∂P.toMeasure :=
        integral_map ShellField.measurable_negateSequence.aemeasurable
          hXMeas.aestronglyMeasurable
      _ = ∫ omega, -X omega ∂P.toMeasure := by
        refine integral_congr_ae ?_
        filter_upwards with omega
        simp only [hXdef, ShellField.negateSequence_apply,
          translatedShellCubeAverage_negate, Matrix.neg_apply]
      _ = -∫ omega, X omega ∂P.toMeasure := integral_neg X
  exact CharZero.eq_neg_self_iff.mp hEq

/-! ## One colour class -/

private theorem isBigO_gammaSigma_zero {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu] {B sigma : ℝ} (hB : 0 ≤ B) :
    IndependentSums.IsBigO mu (IndependentSums.gammaSigma sigma)
      (fun _ : Omega ↦ (0 : ℝ)) B := by
  intro t ht
  have hempty : IndependentSums.upperTailEvent
      (fun _ : Omega ↦ |(0 : ℝ)|) (B * t) = (∅ : Set Omega) := by
    ext omega
    simp only [IndependentSums.mem_upperTailEvent, abs_zero,
      Set.mem_empty_iff_false, iff_false, not_lt]
    exact mul_nonneg hB (le_trans zero_le_one ht)
  rw [hempty, measureReal_empty, IndependentSums.gammaSigma_inv]
  exact (Real.exp_pos _).le

/-- Within one colour class the translated cube averages are mutually
independent: J1 applies because same-colour cubes of the same scale are
separated at the J1 range. -/
theorem iIndepFun_translatedShellCubeAverage_entry_colorClass
    (hJ1 : ShellLawJ1 d P) (k : ℕ) (y : Vec d) (D : Finset (TriadicCube d))
    (hD : ∀ R ∈ D, R.scale = (k : ℤ)) (c : ShellCubeColor d) (i l : Fin d) :
    iIndepFun
      (fun (R : {R : TriadicCube d // R ∈ D.filter fun S ↦ cubeShellColor S = c})
          (omega : ℕ → ShellField d) ↦
        translatedShellCubeAverage y R.1 (omega k) i l) P.toMeasure := by
  classical
  have hentry : ∀ Q : TriadicCube d,
      @Measurable (ShellField d) ℝ
        (lihLocalSigma (translateSet y (cubeSet Q))) inferInstance
        (fun jf : ShellField d ↦ translatedShellCubeAverage y Q jf i l) := by
    intro Q
    have hrow : Measurable (fun A : Mat d ↦ A i) := measurable_pi_apply i
    have hcol : Measurable (fun v : Fin d → ℝ ↦ v l) := measurable_pi_apply l
    exact (hcol.comp hrow).comp
      (measurable_translatedShellCubeAverage_lihLocalSigma y Q)
  have hsep : Pairwise fun R S :
      {R : TriadicCube d // R ∈ D.filter fun S ↦ cubeShellColor S = c} ↦
        AreShellSeparated k (translateSet y (cubeSet R.1))
          (translateSet y (cubeSet S.1)) := by
    intro R S hRS
    have hRmem := Finset.mem_filter.mp R.2
    have hSmem := Finset.mem_filter.mp S.2
    have hne : R.1 ≠ S.1 := fun hcon ↦ hRS (Subtype.ext hcon)
    exact (areShellSeparated_cubeSet_of_cubeShellColor_eq (hD R.1 hRmem.1)
      (hD S.1 hSmem.1) (hRmem.2.trans hSmem.2.symm) hne).translate y
  have hmain := ShellLawJ1.iIndepFun_shellCoordinate (beta := fun _ ↦ ℝ) hJ1 k
    (U := fun R : {R : TriadicCube d //
        R ∈ D.filter fun S ↦ cubeShellColor S = c} ↦
      translateSet y (cubeSet R.1))
    (X := fun R jf ↦ translatedShellCubeAverage y R.1 jf i l)
    (fun R ↦ measurableSet_translateSet_cubeSet y R.1)
    (fun R ↦ hentry R.1) hsep
  exact hmain

/-- Concentration of the sum of the translated cube averages over one colour
class. -/
theorem isBigO_gammaSigma_colorClassSum_entry
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (k : ℕ) (y : Vec d) (D : Finset (TriadicCube d))
    (hD : ∀ R ∈ D, R.scale = (k : ℤ)) (c : ShellCubeColor d) (i l : Fin d)
    {A : ℝ} (hA : 0 ≤ A)
    (hcard : Real.sqrt
      (((D.filter fun S ↦ cubeShellColor S = c).card : ℕ) : ℝ) ≤ A) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ℕ → ShellField d ↦
        ∑ R ∈ D.filter fun S ↦ cubeShellColor S = c,
          translatedShellCubeAverage y R (omega k) i l)
      (Book.Ch04.gammaSigmaIndependentSumConst 2 * A) := by
  classical
  set Dc : Finset (TriadicCube d) := D.filter fun S ↦ cubeShellColor S = c with hDc
  have hCpos : 0 < Book.Ch04.gammaSigmaIndependentSumConst 2 :=
    SuperdiffusionCLT.Probability.gammaSigmaIndependentSumConst_two_pos
  by_cases hne : Dc.Nonempty
  · have hindep := iIndepFun_translatedShellCubeAverage_entry_colorClass hJ1 k y D
      hD c i l
    have hmeas : ∀ R : {R : TriadicCube d // R ∈ Dc},
        Measurable (fun omega : ℕ → ShellField d ↦
          translatedShellCubeAverage y R.1 (omega k) i l) :=
      fun R ↦ measurable_translatedShellCubeAverage_entry_coordinate k y R.1 i l
    have hattach : Dc.attach.Nonempty := by simpa using hne
    have htail : ∀ R ∈ Dc.attach,
        IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
          (fun omega : ℕ → ShellField d ↦
            translatedShellCubeAverage y R.1 (omega k) i l) 1 := by
      intro R _
      refine isBigO_gammaSigma_translatedShellCubeAverage_entry hPrefix hJ3 k y
        (cubeCenter R.1) R.1 i l ?_
      intro x hx
      exact sub_cubeCenter_mem_openCubeSet_originCube
        (hD R.1 (Finset.mem_filter.mp R.2).1) hx
    have hmean : ∀ R ∈ Dc.attach,
        ∫ omega : ℕ → ShellField d,
          translatedShellCubeAverage y R.1 (omega k) i l ∂P.toMeasure = 0 :=
      fun R _ ↦ integral_translatedShellCubeAverage_entry_eq_zero hJ4 k y R.1 i l
    have hsum :=
      Book.Ch04.isBigO_gammaSigma_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero
        (μ := P.toMeasure)
        (X := fun (R : {R : TriadicCube d // R ∈ Dc})
          (omega : ℕ → ShellField d) ↦
            translatedShellCubeAverage y R.1 (omega k) i l)
        (s := Dc.attach) (σ := 2) (K := 1)
        hindep hmeas hattach (by norm_num) (by norm_num) (by norm_num)
        htail hmean
    have hattach_eq : (fun omega : ℕ → ShellField d ↦
        ∑ R ∈ Dc.attach, translatedShellCubeAverage y R.1 (omega k) i l) =
        fun omega : ℕ → ShellField d ↦
          ∑ R ∈ Dc, translatedShellCubeAverage y R (omega k) i l := by
      funext omega
      exact Finset.sum_attach Dc
        fun R ↦ translatedShellCubeAverage y R (omega k) i l
    rw [hattach_eq] at hsum
    refine hsum.mono_scale ?_
    rw [Finset.card_attach, mul_one]
    exact mul_le_mul_of_nonneg_left hcard hCpos.le
  · have hempty : Dc = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hzero : (fun omega : ℕ → ShellField d ↦
        ∑ R ∈ Dc, translatedShellCubeAverage y R (omega k) i l) =
        fun _ : ℕ → ShellField d ↦ (0 : ℝ) := by
      funext omega
      rw [hempty, Finset.sum_empty]
    rw [hzero]
    exact isBigO_gammaSigma_zero P.toMeasure (mul_nonneg hCpos.le hA)

/-! ## Summing the colour classes -/

/-- The dimension-only constant produced by the colour decomposition: one
finite triangle constant, one colour count, and the independent-sum
constant of the CoarseGraining library. -/
def spatialAverageColorConst (d : ℕ) : ℝ :=
  IndependentSums.gammaTriangleConst 2 *
    ((shellColorPeriod d : ℝ) ^ d * Book.Ch04.gammaSigmaIndependentSumConst 2)

theorem spatialAverageColorConst_nonneg (d : ℕ) :
    0 ≤ spatialAverageColorConst d := by
  have htri : 0 ≤ IndependentSums.gammaTriangleConst 2 := by
    rw [IndependentSums.gammaTriangleConst]
    have h2 : (2 : ℝ) ≤ IndependentSums.gammaGrowthConst 2 :=
      IndependentSums.two_le_gammaGrowthConst 2
    have : (0 : ℝ) ≤ IndependentSums.gammaGrowthConst 2 := by linarith only [h2]
    positivity
  have hsum : 0 ≤ Book.Ch04.gammaSigmaIndependentSumConst 2 :=
    SuperdiffusionCLT.Probability.gammaSigmaIndependentSumConst_two_pos.le
  have hcol : (0 : ℝ) ≤ (shellColorPeriod d : ℝ) ^ d := by positivity
  exact mul_nonneg htri (mul_nonneg hcol hsum)

/-- The whole descendant sum obeys a `Γ₂` bound with the colour constant and
the square root of the number of subcubes. -/
theorem isBigO_gammaSigma_descendantSum_entry
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (k : ℕ) (y : Vec d) (D : Finset (TriadicCube d))
    (hD : ∀ R ∈ D, R.scale = (k : ℤ)) (hDne : D.Nonempty) (i l : Fin d) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ℕ → ShellField d ↦
        ∑ R ∈ D, translatedShellCubeAverage y R (omega k) i l)
      (spatialAverageColorConst d * Real.sqrt ((D.card : ℕ) : ℝ)) := by
  classical
  have hCpos : 0 < Book.Ch04.gammaSigmaIndependentSumConst 2 :=
    SuperdiffusionCLT.Probability.gammaSigmaIndependentSumConst_two_pos
  have hApos : 0 < Real.sqrt ((D.card : ℕ) : ℝ) := by
    refine Real.sqrt_pos.2 ?_
    exact_mod_cast Finset.card_pos.2 hDne
  have hclass : ∀ c ∈ (Finset.univ : Finset (ShellCubeColor d)),
      IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
        (fun omega : ℕ → ShellField d ↦
          ∑ R ∈ D.filter fun S ↦ cubeShellColor S = c,
            translatedShellCubeAverage y R (omega k) i l)
        (Book.Ch04.gammaSigmaIndependentSumConst 2 *
          Real.sqrt ((D.card : ℕ) : ℝ)) := by
    intro c _
    refine isBigO_gammaSigma_colorClassSum_entry hPrefix hJ1 hJ3 hJ4 k y D hD c
      i l hApos.le ?_
    refine Real.sqrt_le_sqrt ?_
    exact_mod_cast Finset.card_filter_le D _
  have hclassMeas : ∀ c ∈ (Finset.univ : Finset (ShellCubeColor d)),
      Measurable (fun omega : ℕ → ShellField d ↦
        ∑ R ∈ D.filter fun S ↦ cubeShellColor S = c,
          translatedShellCubeAverage y R (omega k) i l) := by
    intro c _
    exact Finset.measurable_sum _ fun R _ ↦
      measurable_translatedShellCubeAverage_entry_coordinate k y R i l
  have huniv : (Finset.univ : Finset (ShellCubeColor d)).Nonempty :=
    Finset.univ_nonempty
  have htriangle := Book.Ch04.isBigO_finset_sum_of_isBigO_gammaSigma
    (μ := P.toMeasure) (Finset.univ : Finset (ShellCubeColor d))
    (X := fun c omega ↦
      ∑ R ∈ D.filter fun S ↦ cubeShellColor S = c,
        translatedShellCubeAverage y R (omega k) i l)
    (a := fun _ : ShellCubeColor d ↦
      Book.Ch04.gammaSigmaIndependentSumConst 2 * Real.sqrt ((D.card : ℕ) : ℝ))
    (σ := 2) (by norm_num) huniv (fun _ _ ↦ mul_pos hCpos hApos) hclass
    hclassMeas
  have hfiber : (fun omega : ℕ → ShellField d ↦
      ∑ c : ShellCubeColor d, ∑ R ∈ D.filter fun S ↦ cubeShellColor S = c,
        translatedShellCubeAverage y R (omega k) i l) =
      fun omega : ℕ → ShellField d ↦
        ∑ R ∈ D, translatedShellCubeAverage y R (omega k) i l := by
    funext omega
    exact Finset.sum_fiberwise D cubeShellColor
      fun R ↦ translatedShellCubeAverage y R (omega k) i l
  have hcardcolor : (Finset.univ : Finset (ShellCubeColor d)).card =
      shellColorPeriod d ^ d := by
    simp
  have hamp : IndependentSums.gammaTriangleConst 2 *
        ∑ _c : ShellCubeColor d,
          (Book.Ch04.gammaSigmaIndependentSumConst 2 *
            Real.sqrt ((D.card : ℕ) : ℝ)) =
      spatialAverageColorConst d * Real.sqrt ((D.card : ℕ) : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, hcardcolor, spatialAverageColorConst]
    push_cast
    ring
  rw [hfiber, hamp] at htriangle
  exact htriangle

/-! ## The entrywise spatial-average tail -/

private theorem inv_mul_sqrt_eq_sqrt_inv {N : ℝ} (hN : 0 < N) :
    N⁻¹ * Real.sqrt N = Real.sqrt N⁻¹ := by
  calc
    N⁻¹ * Real.sqrt N
        = (Real.sqrt N * Real.sqrt N)⁻¹ * Real.sqrt N := by
      rw [Real.mul_self_sqrt hN.le]
    _ = (Real.sqrt N)⁻¹ := by
      field_simp
    _ = Real.sqrt N⁻¹ := (Real.sqrt_inv N).symm

private theorem sqrt_inv_pow_eq_rpow (d p : ℕ) :
    Real.sqrt ((((3 : ℝ) ^ d) ^ p)⁻¹) =
      (3 : ℝ) ^ (-((d : ℝ) / 2) * (p : ℝ)) := by
  have h3 : (0 : ℝ) ≤ 3 := by norm_num
  have hbase : (((3 : ℝ) ^ d) ^ p) = (3 : ℝ) ^ ((d : ℝ) * (p : ℝ)) := by
    rw [Real.rpow_mul h3, Real.rpow_natCast, Real.rpow_natCast]
  rw [hbase, Real.sqrt_inv, Real.sqrt_eq_rpow, ← Real.rpow_mul h3,
    ← Real.rpow_neg h3]
  congr 1
  ring

/-- Below the shell scale the average over the cube is dominated by the shell's
`L∞` value norm, at unit amplitude. -/
theorem isBigO_gammaSigma_shellSpatialAverage_entry_of_le_scale
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) (k : ℕ) {h : ℤ}
    (hhk : h ≤ (k : ℤ)) (y : Vec d) (i l : Fin d) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ℕ → ShellField d ↦
        shellSpatialAverage h y (omega k) i l) 1 := by
  refine isBigO_gammaSigma_translatedShellCubeAverage_entry hPrefix hJ3 k y 0
    (originCube d h) i l ?_
  intro x hx
  rw [sub_zero]
  exact openCubeSet_originCube_subset_of_le hhk hx

/-- Above the shell scale the cube is partitioned into scale-`k` subcubes and
the colour decomposition gives the square-root gain. -/
theorem isBigO_gammaSigma_shellSpatialAverage_entry_of_scale_le
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (k : ℕ) {h : ℤ} (hkh : (k : ℤ) ≤ h) (y : Vec d)
    (i l : Fin d) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ℕ → ShellField d ↦
        shellSpatialAverage h y (omega k) i l)
      (spatialAverageColorConst d *
        (3 : ℝ) ^ (-((d : ℝ) / 2) * ((h - (k : ℤ)).toNat : ℝ))) := by
  classical
  set p : ℕ := (h - (k : ℤ)).toNat with hp
  set Q : TriadicCube d := originCube d h with hQ
  set Dd : Finset (TriadicCube d) := descendantsAtDepth Q p with hDd
  have hQscale : Q.scale = h := rfl
  have hpcast : ((p : ℕ) : ℤ) = h - (k : ℤ) := Int.toNat_of_nonneg (by omega)
  have hscale : ∀ R ∈ Dd, R.scale = (k : ℤ) := by
    intro R hR
    have := scale_eq_sub_of_mem_descendantsAtDepth hR
    rw [this, hQscale, hpcast]
    ring
  have hne : Dd.Nonempty := descendantsAtDepth_nonempty Q p
  have hcard : (Dd.card : ℕ) = (3 ^ d) ^ p := descendantsAtDepth_card Q p
  have hcardReal : ((Dd.card : ℕ) : ℝ) = ((3 : ℝ) ^ d) ^ p := by
    rw [hcard]
    push_cast
    ring
  have hcardpos : (0 : ℝ) < ((Dd.card : ℕ) : ℝ) := by
    rw [hcardReal]
    positivity
  have hsum := isBigO_gammaSigma_descendantSum_entry hPrefix hJ1 hJ3 hJ4 k y Dd
    hscale hne i l
  have hscaled := hsum.const_mul (c := ((Dd.card : ℕ) : ℝ)⁻¹)
    (inv_nonneg.2 hcardpos.le)
  have hpartition : (fun omega : ℕ → ShellField d ↦
      ((Dd.card : ℕ) : ℝ)⁻¹ *
        ∑ R ∈ Dd, translatedShellCubeAverage y R (omega k) i l) =
      fun omega : ℕ → ShellField d ↦
        shellSpatialAverage h y (omega k) i l := by
    funext omega
    exact (translatedShellCubeAverage_entry_eq_descendants y Q p (omega k) i l).symm
  have hamp : ((Dd.card : ℕ) : ℝ)⁻¹ *
        (spatialAverageColorConst d * Real.sqrt ((Dd.card : ℕ) : ℝ)) =
      spatialAverageColorConst d *
        (3 : ℝ) ^ (-((d : ℝ) / 2) * (p : ℝ)) := by
    rw [← sqrt_inv_pow_eq_rpow d p, ← hcardReal,
      ← inv_mul_sqrt_eq_sqrt_inv hcardpos]
    ring
  rw [hpartition, hamp] at hscaled
  exact hscaled

/-- The entrywise form of manuscript display `e.jk.spatialavg`. -/
theorem isBigO_gammaSigma_shellSpatialAverage_entry
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (k : ℕ) (h : ℤ) (y : Vec d) (i l : Fin d) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ℕ → ShellField d ↦
        shellSpatialAverage h y (omega k) i l)
      ((1 + spatialAverageColorConst d) *
        (3 : ℝ) ^ (-((d : ℝ) / 2) * ((max (h - (k : ℤ)) 0 : ℤ) : ℝ))) := by
  have hconst : 0 ≤ spatialAverageColorConst d := spatialAverageColorConst_nonneg d
  rcases le_or_gt h (k : ℤ) with hhk | hkh
  · have hmax : max (h - (k : ℤ)) 0 = 0 := max_eq_right (by omega)
    have hbase := isBigO_gammaSigma_shellSpatialAverage_entry_of_le_scale
      hPrefix hJ3 k hhk y i l
    refine hbase.mono_scale ?_
    rw [hmax]
    norm_num
    linarith only [hconst]
  · have hkh' : (k : ℤ) ≤ h := le_of_lt hkh
    have hmax : ((max (h - (k : ℤ)) 0 : ℤ) : ℝ) = (((h - (k : ℤ)).toNat : ℕ) : ℝ) := by
      have : max (h - (k : ℤ)) 0 = ((h - (k : ℤ)).toNat : ℤ) := by omega
      rw [this]
      push_cast
      ring
    have hbase := isBigO_gammaSigma_shellSpatialAverage_entry_of_scale_le
      hPrefix hJ1 hJ3 hJ4 k hkh' y i l
    refine hbase.mono_scale ?_
    rw [hmax]
    have hpow : (0 : ℝ) < (3 : ℝ) ^ (-((d : ℝ) / 2) * (((h - (k : ℤ)).toNat : ℕ) : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    exact mul_le_mul_of_nonneg_right (by linarith only []) hpow.le

/-! ## The matrix spatial-average tail -/

private theorem matrixOperatorNorm_le_sum_abs_entry (A : Mat d) :
    matrixOperatorNorm A ≤ ∑ q : Fin d × Fin d, |A q.1 q.2| := by
  have hsum : ∑ q : Fin d × Fin d, |A q.1 q.2| =
      ∑ i : Fin d, ∑ l : Fin d, |A i l| :=
    Fintype.sum_prod_type fun q : Fin d × Fin d ↦ |A q.1 q.2|
  rw [hsum]
  exact (matrixOperatorNorm_le_matrixFrobeniusNorm A).trans
    (matrixFrobeniusNorm_le_sum_abs_entries A)

/-- The explicit dimension-only constant of manuscript display
`e.jk.spatialavg`: one triangle constant for the `d ^ 2` matrix entries, and,
inside, the colour constant of the subcube decomposition. -/
def spatialAverageTailConst (d : ℕ) : ℝ :=
  IndependentSums.gammaTriangleConst 2 * (d : ℝ) ^ 2 *
    (1 + spatialAverageColorConst d)

/-- **Manuscript display `e.jk.spatialavg`.** For every shell index `k`, every
scale `h` and every centre `y`, the Euclidean matrix operator norm of the
spatial average of shell `k` over the translated cube `y + cu_h` has the
symmetric `Γ₂` tail with amplitude
`spatialAverageTailConst d * 3 ^ (-(d / 2) ((h - k) ∨ 0))`.

The inputs are exactly the prefix (dimension and per-shell
stationarity), J1 (range of dependence), J3 (regularity tail) and the negation
half of J4. -/
theorem isBigOWith_gammaSigma_matrixOperatorNorm_shellSpatialAverage
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (k : ℕ) (h : ℤ) (y : Vec d) :
    IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ℕ → ShellField d ↦
        matrixOperatorNorm (shellSpatialAverage h y (omega k)))
      (spatialAverageTailConst d *
        (3 : ℝ) ^ (-((d : ℝ) / 2) * ((max (h - (k : ℤ)) 0 : ℤ) : ℝ))) := by
  classical
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) hPrefix.dimension
  have hconst : 0 ≤ spatialAverageColorConst d := spatialAverageColorConst_nonneg d
  have hpow : (0 : ℝ) <
      (3 : ℝ) ^ (-((d : ℝ) / 2) * ((max (h - (k : ℤ)) 0 : ℤ) : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hAmp : (0 : ℝ) < (1 + spatialAverageColorConst d) *
      (3 : ℝ) ^ (-((d : ℝ) / 2) * ((max (h - (k : ℤ)) 0 : ℤ) : ℝ)) :=
    mul_pos (by linarith only [hconst]) hpow
  have hne : (Finset.univ : Finset (Fin d × Fin d)).Nonempty :=
    ⟨(⟨0, hd⟩, ⟨0, hd⟩), Finset.mem_univ _⟩
  have hentry : ∀ q ∈ (Finset.univ : Finset (Fin d × Fin d)),
      IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
        (fun omega : ℕ → ShellField d ↦
          |shellSpatialAverage h y (omega k) q.1 q.2|)
        ((1 + spatialAverageColorConst d) *
          (3 : ℝ) ^ (-((d : ℝ) / 2) * ((max (h - (k : ℤ)) 0 : ℤ) : ℝ))) := by
    intro q _
    have hq := isBigO_gammaSigma_shellSpatialAverage_entry hPrefix hJ1 hJ3 hJ4 k
      h y q.1 q.2
    simpa only [IndependentSums.IsBigO, abs_abs] using hq
  have hmeas : ∀ q ∈ (Finset.univ : Finset (Fin d × Fin d)),
      Measurable (fun omega : ℕ → ShellField d ↦
        |shellSpatialAverage h y (omega k) q.1 q.2|) := by
    intro q _
    exact
      (measurable_translatedShellCubeAverage_entry_coordinate k y
        (originCube d h) q.1 q.2).norm
  have htriangle := Book.Ch04.isBigO_finset_sum_of_isBigO_gammaSigma
    (μ := P.toMeasure) (Finset.univ : Finset (Fin d × Fin d))
    (X := fun q omega ↦ |shellSpatialAverage h y (omega k) q.1 q.2|)
    (a := fun _ : Fin d × Fin d ↦
      (1 + spatialAverageColorConst d) *
        (3 : ℝ) ^ (-((d : ℝ) / 2) * ((max (h - (k : ℤ)) 0 : ℤ) : ℝ)))
    (σ := 2) (by norm_num) hne (fun _ _ ↦ hAmp) hentry hmeas
  have hamp : IndependentSums.gammaTriangleConst 2 *
        ∑ _q : Fin d × Fin d,
          ((1 + spatialAverageColorConst d) *
            (3 : ℝ) ^ (-((d : ℝ) / 2) * ((max (h - (k : ℤ)) 0 : ℤ) : ℝ))) =
      spatialAverageTailConst d *
        (3 : ℝ) ^ (-((d : ℝ) / 2) * ((max (h - (k : ℤ)) 0 : ℤ) : ℝ)) := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, spatialAverageTailConst]
    push_cast
    ring
  rw [hamp] at htriangle
  refine htriangle.of_le fun omega ↦ ?_
  refine (matrixOperatorNorm_le_sum_abs_entry _).trans (le_abs_self _)

end

end SuperdiffusionCLT.Section2.Estimates.Stream
