/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3CgClose
public import SuperdiffusionCLT.Section3.Terms.CenteredGradientMeasurable
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3IntegLeaves
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3MemFluxB

/-!
# `term3_cgBound_closeB`: the membership half of `_hCgBound`'s residual package

This module is the side-condition block.  The display `term3_cgBound_closeB`
itself, `_hCgBound` of the term-3 final assembly at the reduced package, is stated and
proved in `RHSTerm3CgCloseC`, which imports this module.

`term3_cgBound_close` (in `Section3/Terms/RHSTerm3CgClose.lean`) proves the
printed display `e.RHS.term3.A` from the binders of
`_hCgBound` of the term-3 final assembly plus 26 residual hypotheses.  This
module discharges the largest block of that residual package: the
**integrability and measurability side conditions** of the two Cauchy-Schwarz
steps, of the Hoelder pair, of the `w`-flux decomposition and of the
flux-additivity display.

What is discharged here, with no hypothesis of its own beyond the
binders of `_hCgBound`:

* `hMemDiff`, the `P`-square-integrability of the squared difference of the two
  response-gradient cube means on a coarse pair — `MemLp.mono'` at
  `vecNormSq (a - b) ≤ 2(vecNormSq a + vecNormSq b)`, each summand from
  `memLp_vecNormSq_volumeAverageVec_grad_of_containment`
  (in `RHSTerm3IntegLeaves.lean`);
* `hXmeas`, the sample measurability of the difference half weight
  `translatedBlockHalfWeightDiff`, read as the quadratic form
  `v · (b v)` of the difference vector;
* `hMembCS`, `hMembDiff` — the `L²` membership of the two half-weight square
  roots, equivalent to the `L¹` membership of the half weights themselves, which
  `translatedBlockHalfWeight_le` / `translatedBlockHalfWeightDiff_le` dominate by
  a product of two `L²(P)` functions;
* `hInt1`, `hInt2` — the integrability of the two halves of
  `e.w-flux-indepen-decomp`, by the Cauchy-Schwarz bound
  `|v · w| ≤ |v| |w|` in `L²(P)`;
* `hEnergyCube` — the deterministic `IntegrableOn` clause of the flux-additivity
  display, reduced to the open cube by the null-set equivalence
  `cubeSet_ae_eq_openCubeSet`;
* `hProdCS`, `hProdDiff` — the two Cauchy-Schwarz pairings, as the `L¹` product
  of the two `L²(P)` memberships `hMembCS`/`hMembDiff` and the surviving `hMemf`
  binder, by `MemLp.integrable_mul`.

The flux norm `gluedFluxNorm` is *not* touched: `hMemf` is stated against the
surviving `hMemf` binder, because the printed carrier
`|b_{L'}^{-1/2}(z + cu_n)(a_{L'}∇(u_m − u_{n,z}))_{z+cu_n}|²` has no
sample-measurability lemma here; the two products that consume it are nevertheless
discharged above, from `hMembCS`/`hMembDiff` and `hMemf`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory ProbabilityTheory
open Homogenization
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

noncomputable section

variable {d : ℕ} {nu : ℝ}

/-! ## 1. Elementary carriers -/

/-- The squared norm of a difference is bounded by twice the sum of the two
squared norms.  The two-line expansion is proved here directly. -/
private theorem vecNormSq_sub_le_two_local (e f : Vec d) :
    vecNormSq (e - f) ≤ 2 * (vecNormSq e + vecNormSq f) := by
  have hplus : 0 ≤ vecNormSq (e + f) := vecNormSq_nonneg (e + f)
  have hminus : 0 ≤ vecNormSq (e - f) := vecNormSq_nonneg (e - f)
  simp only [vecNormSq, sub_eq_add_neg, vecDot_add_left, vecDot_add_right,
    vecDot_neg_left, vecDot_neg_right] at hplus hminus ⊢
  linarith only [hplus, hminus]

/-- Cauchy-Schwarz in `Vec d`, in the half-power spelling: `|v · w| ≤
(vecNormSq v)^{1/2} (vecNormSq w)^{1/2}`.  The existing
`Book.Ch02.abs_vecDot_le_vecNorm_mul_vecNorm` is stated for `Book.Ch02.vecNorm`,
which is `sqrt (vecNormSq ·)`, and `Real.sqrt` is `· ^ (1/2)`. -/
private theorem abs_vecDot_le_rpow_half_mul_rpow_half_local (v z : Vec d) :
    |vecDot v z| ≤ vecNormSq v ^ ((1 : ℝ) / 2) * vecNormSq z ^ ((1 : ℝ) / 2) := by
  have h := Book.Ch02.abs_vecDot_le_vecNorm_mul_vecNorm v z
  rw [SuperdiffusionCLT.Frozen.Assumptions.ShellField.vecNorm_eq_sqrt_vecNormSq v,
    SuperdiffusionCLT.Frozen.Assumptions.ShellField.vecNorm_eq_sqrt_vecNormSq z] at h
  rwa [Real.sqrt_eq_rpow (vecNormSq v), Real.sqrt_eq_rpow (vecNormSq z)] at h

/-- `vecNormSq` is measurable as soon as the coordinates are. -/
private theorem measurable_vecNormSq_comp_local {Omega : Type*} [MeasurableSpace Omega]
    {v : Omega → Vec d} (hv : ∀ i : Fin d, Measurable fun omega => v omega i) :
    Measurable fun omega => vecNormSq (v omega) := by
  show Measurable fun omega => vecDot (v omega) (v omega)
  exact Finset.measurable_sum _ fun i _ => (hv i).mul (hv i)

/-- The pairing of a measurable vector through a measurable matrix is
measurable. -/
private theorem measurable_vecDot_matVecMul_self_local {Omega : Type*} [MeasurableSpace Omega]
    {M : Omega → Mat d} {v : Omega → Vec d}
    (hM : ∀ i j, Measurable fun omega => M omega i j)
    (hv : ∀ i : Fin d, Measurable fun omega => v omega i) :
    Measurable fun omega => vecDot (v omega) (matVecMul (M omega) (v omega)) := by
  simp only [vecDot, matVecMul]
  exact Finset.measurable_sum _ fun i _ =>
    (hv i).mul (Finset.measurable_sum _ fun j _ => (hM i j).mul (hv j))

/-- **The square root of a nonnegative integrable function is `L²`.**  The
identity `(f^{1/2})² = f` of `Real.sq_sqrt` turns the `L²` membership into the
`L¹` membership of `f` itself. -/
private theorem memLp_two_rpow_half_of_integrable {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {f : Omega → ℝ} (hf : Measurable f) (hnn : ∀ omega, 0 ≤ f omega)
    (hint : Integrable f mu) :
    MemLp (fun omega => f omega ^ ((1 : ℝ) / 2)) 2 mu := by
  have heq : (fun omega => f omega ^ ((1 : ℝ) / 2)) = fun omega => Real.sqrt (f omega) := by
    funext omega
    rw [Real.sqrt_eq_rpow]
  rw [heq]
  refine (MeasureTheory.memLp_two_iff_integrable_sq hf.sqrt.aestronglyMeasurable).mpr ?_
  refine hint.congr (Filter.Eventually.of_forall fun omega => ?_)
  exact (Real.sq_sqrt (hnn omega)).symm

/-! ## 2. The squared difference of two cube means of `∇w` -/

/-- **`hMemDiff` of `term3_cgBound_close`, discharged.**  On two cubes `z'`, `z`
contained in the large cube `cu_m`, the squared norm of the difference of the
two response-gradient cube means is `P`-square-integrable.  Each cube mean is
covered by the containment form of the fourth-moment engine
(`memLp_vecNormSq_volumeAverageVec_grad_of_containment`), and the difference
costs the factor `2` of `vecNormSq_sub_le_two_local`. -/
private theorem memLp_two_vecNormSq_cubeMeanDiff [NeZero d] (hd : 2 ≤ d) {nu : ℝ}
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ1V2 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (S : ScaleSelection)
    (hSorder : ScalesOrdering S) {e : Vec d} (he : vecNormSq e = 1)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega))
    {z' z : TriadicCube d}
    (hz' : openCubeSet z' ⊆ openCubeSet (originCube d (S.m : ℤ)))
    (hz : openCubeSet z ⊆ openCubeSet (originCube d (S.m : ℤ))) :
    MemLp (fun omega : ShellSeq d =>
      vecNormSq (volumeAverageVec (openCubeSet z) ((w omega).toH1Function.grad) -
        volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad))) 2 P.toMeasure := by
  classical
  have hmz := measurable_volumeAverageVec_grad_subcube (d := d) (m := S.m)
    (LPrime := S.LPrime) (ellPrime := S.ellPrime) (p := testVector nu S.LPrime P S.n e)
    (w := w) hw hz
  have hmz' := measurable_volumeAverageVec_grad_subcube (d := d) (m := S.m)
    (LPrime := S.LPrime) (ellPrime := S.ellPrime) (p := testVector nu S.LPrime P S.n e)
    (w := w) hw hz'
  have hmeas : Measurable (fun omega : ShellSeq d =>
      vecNormSq (volumeAverageVec (openCubeSet z) ((w omega).toH1Function.grad) -
        volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad))) :=
    measurable_vecNormSq_comp_local fun i =>
      ((measurable_pi_apply i).comp hmz).sub ((measurable_pi_apply i).comp hmz')
  have h1 := memLp_vecNormSq_volumeAverageVec_grad_of_containment (d := d) (e := e) hd hnu
    hnu1 hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder he w hw hz
  have h2 := memLp_vecNormSq_volumeAverageVec_grad_of_containment (d := d) (e := e) hd hnu
    hnu1 hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder he w hw hz'
  have hdom : MemLp (fun omega : ShellSeq d => 2 *
      (vecNormSq (volumeAverageVec (openCubeSet z) ((w omega).toH1Function.grad)) +
        vecNormSq (volumeAverageVec (openCubeSet z')
          ((w omega).toH1Function.grad)))) 2 P.toMeasure :=
    (h1.add h2).const_mul 2
  refine MemLp.mono' hdom hmeas.aestronglyMeasurable ?_
  filter_upwards with omega
  rw [Real.norm_of_nonneg (vecNormSq_nonneg _)]
  exact vecNormSq_sub_le_two_local _ _

/-! ## 3. The difference half weight: measurability and integrability -/

/-- **`hXmeas` of `term3_cgBound_close`, discharged.**  The difference half
weight `translatedBlockHalfWeightDiff` is the quadratic form `v · (b v)` of the
difference `v` of the two response-gradient cube means through the coarse block
`b_{L'}(z + cu_n)`, so it is measurable in the sample as soon as the cube means
are. -/
private theorem measurable_translatedBlockHalfWeightDiff_local [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) {e : Vec d}
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega))
    {z' z : TriadicCube d}
    (hz' : openCubeSet z' ⊆ openCubeSet (originCube d (S.m : ℤ)))
    (hz : openCubeSet z ⊆ openCubeSet (originCube d (S.m : ℤ))) :
    Measurable (fun omega : ShellSeq d =>
      translatedBlockHalfWeightDiff nu S.LPrime w omega z' z) := by
  have hmz := measurable_volumeAverageVec_grad_subcube (d := d) (m := S.m)
    (LPrime := S.LPrime) (ellPrime := S.ellPrime) (p := testVector nu S.LPrime P S.n e)
    (w := w) hw hz
  have hmz' := measurable_volumeAverageVec_grad_subcube (d := d) (m := S.m)
    (LPrime := S.LPrime) (ellPrime := S.ellPrime) (p := testVector nu S.LPrime P S.n e)
    (w := w) hw hz'
  have hv : ∀ i : Fin d, Measurable fun omega : ShellSeq d =>
      (volumeAverageVec (openCubeSet z) ((w omega).toH1Function.grad) -
        volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad)) i := fun i =>
    ((measurable_pi_apply i).comp hmz).sub ((measurable_pi_apply i).comp hmz')
  have hEq : (fun omega : ShellSeq d =>
      translatedBlockHalfWeightDiff nu S.LPrime w omega z' z) =
      fun omega : ShellSeq d => vecDot
        (volumeAverageVec (openCubeSet z) ((w omega).toH1Function.grad) -
          volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad))
        (matVecMul (translatedCoarseBlock nu S.LPrime omega z)
          (volumeAverageVec (openCubeSet z) ((w omega).toH1Function.grad) -
            volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad))) := by
    funext omega
    exact SuperdiffusionCLT.Section2.Localization.vecNormSq_sqrt_matVecMul_eq_vecDot_matVecMul
      (posSemidef_translatedCoarseBlock hnu S.LPrime omega z) _
  rw [hEq]
  exact measurable_vecDot_matVecMul_self_local
    (fun i j => measurable_translatedCoarseBlock_apply hnu S.LPrime z i j) hv

/-- **The difference half weight is `P`-integrable.**  Its operator-norm bridge
`translatedBlockHalfWeightDiff_le` dominates it by
`|b_{L'}(z + cu_n)| · |⍍_z ∇w − ⍍_{z'} ∇w|²`, the product of the `L²(P)`
coarse-block norm (`memLp_two_translatedBlockNorm_final`) and the `L²(P)`
squared difference of cube means (`memLp_two_vecNormSq_cubeMeanDiff`). -/
private theorem integrable_translatedBlockHalfWeightDiff_local [NeZero d] (hd : 2 ≤ d) {nu : ℝ}
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ1V2 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (S : ScaleSelection)
    (hSorder : ScalesOrdering S) {e : Vec d} (he : vecNormSq e = 1)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega))
    {z' z : TriadicCube d}
    (hz' : openCubeSet z' ⊆ openCubeSet (originCube d (S.m : ℤ)))
    (hz : openCubeSet z ⊆ openCubeSet (originCube d (S.m : ℤ))) :
    Integrable (fun omega : ShellSeq d =>
      translatedBlockHalfWeightDiff nu S.LPrime w omega z' z) P.toMeasure := by
  have hsq := memLp_two_vecNormSq_cubeMeanDiff (d := d) hd hnu hnu1 hPrefix hJ1V2 hJ2 hJ3
    hJ4 S hSorder he w hw hz' hz
  have hprod : Integrable (fun omega : ShellSeq d =>
      vecNormSq (volumeAverageVec (openCubeSet z) ((w omega).toH1Function.grad) -
        volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad)) *
        translatedBlockNorm nu S.LPrime omega z) P.toMeasure :=
    hsq.integrable_mul (memLp_two_translatedBlockNorm_final hnu hPrefix hJ2 hJ3 hJ4 S.LPrime z)
  have hmeas := measurable_translatedBlockHalfWeightDiff_local hnu P S w hw hz' hz
  refine Integrable.mono' hprod hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun omega => ?_)
  rw [Real.norm_eq_abs,
    abs_of_nonneg (translatedBlockHalfWeightDiff_nonneg S.LPrime w omega z' z), mul_comm]
  exact translatedBlockHalfWeightDiff_le hnu S.LPrime w omega z' z

/-- **`hMembDiff` of `term3_cgBound_close`, discharged.** -/
theorem memLp_two_halfWeightDiff_sqrt_discharged [NeZero d] (hd : 2 ≤ d) {nu : ℝ}
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ1V2 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (S : ScaleSelection)
    (hSorder : ScalesOrdering S) {e : Vec d} (he : vecNormSq e = 1)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega))
    {z' z : TriadicCube d}
    (hz' : openCubeSet z' ⊆ openCubeSet (originCube d (S.m : ℤ)))
    (hz : openCubeSet z ⊆ openCubeSet (originCube d (S.m : ℤ))) :
    MemLp (fun omega : ShellSeq d =>
      translatedBlockHalfWeightDiff nu S.LPrime w omega z' z ^ ((1 : ℝ) / 2)) 2 P.toMeasure :=
  memLp_two_rpow_half_of_integrable
    (measurable_translatedBlockHalfWeightDiff_local hnu P S w hw hz' hz)
    (fun _ => translatedBlockHalfWeightDiff_nonneg S.LPrime w _ _ _)
    (integrable_translatedBlockHalfWeightDiff_local hd hnu hnu1 hPrefix hJ1V2 hJ2 hJ3 hJ4
      S hSorder he w hw hz' hz)

/-- The square root of a nonnegative `L²` function is again `L²`. -/
private theorem memLp_two_sqrt_of_memLp_two {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu] {f : Omega → ℝ} (hf : Measurable f)
    (hnn : ∀ omega, 0 ≤ f omega) (hmem : MemLp f 2 mu) :
    MemLp (fun omega => f omega ^ ((1 : ℝ) / 2)) 2 mu :=
  memLp_two_rpow_half_of_integrable hf hnn (hmem.integrable (by norm_num))

/-- The pairing of two vector-valued maps with measurable coordinates is
measurable. -/
private theorem measurable_vecDot_local {Omega : Type*} [MeasurableSpace Omega]
    {v z : Omega → Vec d} (hv : ∀ i : Fin d, Measurable fun omega => v omega i)
    (hz : ∀ i : Fin d, Measurable fun omega => z omega i) :
    Measurable fun omega => vecDot (v omega) (z omega) := by
  simp only [vecDot]
  exact Finset.measurable_sum _ fun i _ => (hv i).mul (hz i)

/-! ## 4. The single half weight: measurability and `L²` membership of its root -/

/-- The half weight `|b^{1/2}(z+cu_n)v|²` is nonnegative. -/
private theorem translatedBlockHalfWeight_nonneg_local {nu : ℝ} (L : ℕ) {U : Set (Vec d)}
    (w : ShellSeq d → H10Function U) (omega : ShellSeq d) (z' z : TriadicCube d) :
    0 ≤ translatedBlockHalfWeight nu L w omega z' z :=
  vecNormSq_nonneg _

/-- The half weight is the quadratic form `v · (b v)` of the cube mean `v`, so
it is measurable in the sample as soon as that cube mean is. -/
private theorem measurable_translatedBlockHalfWeight_local [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) {e : Vec d}
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega))
    {z' z : TriadicCube d}
    (hz' : openCubeSet z' ⊆ openCubeSet (originCube d (S.m : ℤ))) :
    Measurable (fun omega : ShellSeq d =>
      translatedBlockHalfWeight nu S.LPrime w omega z' z) := by
  have hmz' := measurable_volumeAverageVec_grad_subcube (d := d) (m := S.m)
    (LPrime := S.LPrime) (ellPrime := S.ellPrime) (p := testVector nu S.LPrime P S.n e)
    (w := w) hw hz'
  have hEq : (fun omega : ShellSeq d =>
      translatedBlockHalfWeight nu S.LPrime w omega z' z) =
      fun omega : ShellSeq d => vecDot
        (volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad))
        (matVecMul (translatedCoarseBlock nu S.LPrime omega z)
          (volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad))) := by
    funext omega
    exact SuperdiffusionCLT.Section2.Localization.vecNormSq_sqrt_matVecMul_eq_vecDot_matVecMul
      (posSemidef_translatedCoarseBlock hnu S.LPrime omega z) _
  rw [hEq]
  exact measurable_vecDot_matVecMul_self_local
    (fun i j => measurable_translatedCoarseBlock_apply hnu S.LPrime z i j)
    (fun i => (measurable_pi_apply i).comp hmz')

/-- **`hMembCS` of `term3_cgBound_close`, discharged.**  The square root of the
half weight is `L²(P)`, because the half weight itself is `P`-integrable for
`z'` a large-cube sub-cube (`sideCondition_hbHalfInt_final`). -/
theorem memLp_two_halfWeight_sqrt_discharged [NeZero d] (hd : 2 ≤ d) {nu : ℝ}
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ1V2 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (S : ScaleSelection)
    (hSorder : ScalesOrdering S) {e : Vec d} (he : vecNormSq e = 1)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega))
    {k : ℕ} {z' : TriadicCube d} (hz' : z' ∈ largeCubeSubcubes d k S.m) (z : TriadicCube d) :
    MemLp (fun omega : ShellSeq d =>
      translatedBlockHalfWeight nu S.LPrime w omega z' z ^ ((1 : ℝ) / 2)) 2 P.toMeasure := by
  have hsub : openCubeSet z' ⊆ openCubeSet (originCube d (S.m : ℤ)) := by
    rw [largeCubeSubcubes_eq_descendantsAtDepth] at hz'
    exact openCubeSet_subset_of_mem_descendantsAtDepth hz'
  exact memLp_two_rpow_half_of_integrable
    (measurable_translatedBlockHalfWeight_local hnu P S w hw hsub)
    (fun _ => translatedBlockHalfWeight_nonneg_local S.LPrime w _ _ _)
    (sideCondition_hbHalfInt_final hd hnu hnu1 hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder he w hw
      z' hz' z)

/-! ## 5. Cube means of `∇w`: measurability and `L²` membership of their roots -/

/-- The squared norm of a cube mean of `∇w` is measurable in the sample. -/
private theorem measurable_vecNormSq_cubeMean_local [NeZero d] {nu : ℝ}
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) {e : Vec d}
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega))
    {z : TriadicCube d} (hz : openCubeSet z ⊆ openCubeSet (originCube d (S.m : ℤ))) :
    Measurable (fun omega : ShellSeq d =>
      vecNormSq (volumeAverageVec (openCubeSet z) ((w omega).toH1Function.grad))) :=
  measurable_vecNormSq_comp_local fun i =>
    (measurable_pi_apply i).comp
      (measurable_volumeAverageVec_grad_subcube (d := d) (m := S.m) (LPrime := S.LPrime)
        (ellPrime := S.ellPrime) (p := testVector nu S.LPrime P S.n e) (w := w) hw hz)

/-- The squared norm of a *difference* of two cube means of `∇w` is measurable in
the sample. -/
private theorem measurable_vecNormSq_cubeMeanDiff_local [NeZero d] {nu : ℝ}
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) {e : Vec d}
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega))
    {z' z : TriadicCube d}
    (hz' : openCubeSet z' ⊆ openCubeSet (originCube d (S.m : ℤ)))
    (hz : openCubeSet z ⊆ openCubeSet (originCube d (S.m : ℤ))) :
    Measurable (fun omega : ShellSeq d =>
      vecNormSq (volumeAverageVec (openCubeSet z) ((w omega).toH1Function.grad) -
        volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad))) := by
  have hmz := measurable_volumeAverageVec_grad_subcube (d := d) (m := S.m)
    (LPrime := S.LPrime) (ellPrime := S.ellPrime) (p := testVector nu S.LPrime P S.n e)
    (w := w) hw hz
  have hmz' := measurable_volumeAverageVec_grad_subcube (d := d) (m := S.m)
    (LPrime := S.LPrime) (ellPrime := S.ellPrime) (p := testVector nu S.LPrime P S.n e)
    (w := w) hw hz'
  exact measurable_vecNormSq_comp_local fun i =>
    ((measurable_pi_apply i).comp hmz).sub ((measurable_pi_apply i).comp hmz')

/-- The root of the squared cube mean of `∇w` is `L²(P)`. -/
private theorem memLp_two_sqrt_vecNormSq_cubeMean_local [NeZero d] (hd : 2 ≤ d) {nu : ℝ}
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ1V2 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (S : ScaleSelection)
    (hSorder : ScalesOrdering S) {e : Vec d} (he : vecNormSq e = 1)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega))
    {z : TriadicCube d} (hz : openCubeSet z ⊆ openCubeSet (originCube d (S.m : ℤ))) :
    MemLp (fun omega : ShellSeq d =>
      (vecNormSq (volumeAverageVec (openCubeSet z)
        ((w omega).toH1Function.grad))) ^ ((1 : ℝ) / 2)) 2 P.toMeasure :=
  memLp_two_sqrt_of_memLp_two (measurable_vecNormSq_cubeMean_local P S w hw hz)
    (fun _ => vecNormSq_nonneg _)
    (memLp_vecNormSq_volumeAverageVec_grad_of_containment (d := d) (e := e) hd hnu hnu1
      hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder he w hw hz)

/-- The root of the squared difference of two cube means of `∇w` is `L²(P)`. -/
private theorem memLp_two_sqrt_vecNormSq_cubeMeanDiff_local [NeZero d] (hd : 2 ≤ d) {nu : ℝ}
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ1V2 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (S : ScaleSelection)
    (hSorder : ScalesOrdering S) {e : Vec d} (he : vecNormSq e = 1)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega))
    {z' z : TriadicCube d}
    (hz' : openCubeSet z' ⊆ openCubeSet (originCube d (S.m : ℤ)))
    (hz : openCubeSet z ⊆ openCubeSet (originCube d (S.m : ℤ))) :
    MemLp (fun omega : ShellSeq d =>
      (vecNormSq (volumeAverageVec (openCubeSet z) ((w omega).toH1Function.grad) -
        volumeAverageVec (openCubeSet z')
          ((w omega).toH1Function.grad))) ^ ((1 : ℝ) / 2)) 2 P.toMeasure :=
  memLp_two_sqrt_of_memLp_two
    (measurable_vecNormSq_cubeMeanDiff_local P S w hw hz' hz)
    (fun _ => vecNormSq_nonneg _)
    (memLp_two_vecNormSq_cubeMeanDiff (d := d) hd hnu hnu1 hPrefix hJ1V2 hJ2 hJ3 hJ4 S
      hSorder he w hw hz' hz)

/-! ## 6. The cube mean of the cutoff flux: measurability and root membership -/

/-- The squared norm of the cube mean of the cutoff flux of the glued-field
difference is measurable in the sample. -/
private theorem measurable_vecNormSq_fluxMean_local [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) (e : Vec d)
    {R : TriadicCube d} (hR : R ∈ largeCubeSubcubes d S.n S.m) :
    Measurable (fun omega : ShellSeq d =>
      vecNormSq (volumeAverageVec (openCubeSet R) (fun y =>
        matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
          (gluedGradientField hnu S.LPrime S.m S.m
              (fluxSlot nu S.LPrime P S.n e) omega y -
            gluedGradientField hnu S.LPrime S.n S.m
              (fluxSlot nu S.LPrime P S.n e) omega y)))) :=
  measurable_vecNormSq_comp_local fun i =>
    (measurable_pi_apply i).comp
      (measurable_volumeAverageVec_coefficientCutoff_gluedDifference_final hnu P S e R hR)

/-- The root of the squared cube mean of the cutoff flux is `L²(P)`, by
`hMemFlux_discharged_B`. -/
private theorem memLp_two_sqrt_vecNormSq_fluxMean_local [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (hSorder : ScalesOrdering S) (e : Vec d)
    {R : TriadicCube d} (hR : R ∈ largeCubeSubcubes d S.n S.m) :
    MemLp (fun omega : ShellSeq d =>
      (vecNormSq (volumeAverageVec (openCubeSet R) (fun y =>
        matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
          (gluedGradientField hnu S.LPrime S.m S.m
              (fluxSlot nu S.LPrime P S.n e) omega y -
            gluedGradientField hnu S.LPrime S.n S.m
              (fluxSlot nu S.LPrime P S.n e) omega y)))) ^ ((1 : ℝ) / 2)) 2 P.toMeasure :=
  memLp_two_sqrt_of_memLp_two (measurable_vecNormSq_fluxMean_local hnu P S e hR)
    (fun _ => vecNormSq_nonneg _)
    (hMemFlux_discharged_B hnu hPrefix hJ2 hJ3 hJ4 S hSorder e R hR)

/-! ## 7. Pair algebra on `coarsePairs` -/

/-- Depth composition for the descendant family. -/
private theorem mem_descendantsAtDepth_trans_local {Q R S : TriadicCube d} {m n : ℕ}
    (hR : R ∈ descendantsAtDepth Q m) (hS : S ∈ descendantsAtDepth R n) :
    S ∈ descendantsAtDepth Q (m + n) := by
  induction n generalizing S with
  | zero =>
      simp only [Nat.add_zero, descendantsAtDepth_zero, Finset.mem_singleton] at hS ⊢
      exact hS ▸ hR
  | succ n ih =>
      rw [Nat.add_succ, descendantsAtDepth_succ] at hS ⊢
      rcases Finset.mem_biUnion.mp hS with ⟨T, hT, hST⟩
      exact Finset.mem_biUnion.mpr ⟨T, ih hT, hST⟩

/-- The first coordinate of a coarse pair is a large-cube sub-cube at the coarse
block scale. -/
private theorem fst_mem_largeCubeSubcubes_of_mem_coarsePairs {n k m : ℕ}
    {q : (_ : TriadicCube d) × TriadicCube d} (hq : q ∈ coarsePairs d n k m) :
    q.1 ∈ largeCubeSubcubes d k m :=
  (Finset.mem_sigma.mp hq).1

/-- Both coordinates of a coarse pair sit inside the large cube `cu_m`. -/
private theorem openCubeSet_pair_subset_of_mem_coarsePairs {n k m : ℕ}
    {q : (_ : TriadicCube d) × TriadicCube d} (hq : q ∈ coarsePairs d n k m) :
    openCubeSet q.1 ⊆ openCubeSet (originCube d (m : ℤ)) ∧
      openCubeSet q.2 ⊆ openCubeSet (originCube d (m : ℤ)) := by
  obtain ⟨h1, h2⟩ := Finset.mem_sigma.mp hq
  have hsub1 : openCubeSet q.1 ⊆ openCubeSet (originCube d (m : ℤ)) := by
    rw [largeCubeSubcubes_eq_descendantsAtDepth] at h1
    exact openCubeSet_subset_of_mem_descendantsAtDepth h1
  exact ⟨hsub1, (openCubeSet_subset_of_mem_descendantsAtDepth h2).trans hsub1⟩

/-- The second coordinate of a coarse pair is a large-cube sub-cube at the fine
scale `n`. -/
private theorem snd_mem_largeCubeSubcubes_of_mem_coarsePairs {n k m : ℕ} (hnk : n ≤ k)
    (hkm : k ≤ m) {q : (_ : TriadicCube d) × TriadicCube d} (hq : q ∈ coarsePairs d n k m) :
    q.2 ∈ largeCubeSubcubes d n m := by
  obtain ⟨h1, h2⟩ := Finset.mem_sigma.mp hq
  rw [largeCubeSubcubes_eq_descendantsAtDepth] at h1 ⊢
  have h := mem_descendantsAtDepth_trans_local h1 h2
  rwa [show m - k + (k - n) = m - n by omega] at h

/-- The two scale bounds of the coarse block scale, from the scale ordering. -/
private theorem coarseBlockScale_bounds (S : ScaleSelection) (hSorder : ScalesOrdering S) :
    S.n ≤ coarseBlockScale d S ∧ coarseBlockScale d S ≤ S.m := by
  have hell : S.ell ≤ S.ellPrime := le_of_lt hSorder.ell_lt_ellPrime
  have hnl : S.n ≤ S.ell := le_of_lt hSorder.n_lt_ell
  obtain ⟨hlk, hkp, -, -⟩ := coarse_block_scale_choice d S hell
  exact ⟨le_trans hnl hlk, le_trans hkp (le_of_lt hSorder.ellPrime_lt_m)⟩

/-! ## 7b. The four membership clauses at the `coarsePairs` carrier

These packages assemble the membership lemmas of sections 3-5, each of which is
stated at a raw cube pair, into the exact `∀ q ∈ coarsePairs …` shape of the
`hMemDiff`, `hXmeas`, `hMembCS` and `hMembDiff` binders of
`term3_cgBound_close`.  They are the interface consumed by the display of
section 9. -/

/-- **`hMemDiff` of `term3_cgBound_close`.** -/
theorem memLp_two_vecNormSq_cubeMeanDiff_coarsePairs_discharged [NeZero d] (hd : 2 ≤ d)
    {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1) {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ1V2 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (S : ScaleSelection)
    (hSorder : ScalesOrdering S) {e : Vec d} (he : vecNormSq e = 1)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega)) :
    ∀ q ∈ coarsePairs d S.n (coarseBlockScale d S) S.m,
      MemLp (fun omega : ShellSeq d =>
        vecNormSq (volumeAverageVec (openCubeSet q.2) ((w omega).toH1Function.grad) -
            volumeAverageVec (openCubeSet q.1) ((w omega).toH1Function.grad)))
        (ENNReal.ofReal (2 : ℝ)) P.toMeasure := by
  intro q hq
  obtain ⟨hc1, hc2⟩ := openCubeSet_pair_subset_of_mem_coarsePairs (d := d) hq
  simpa using memLp_two_vecNormSq_cubeMeanDiff (d := d) hd hnu hnu1 hPrefix hJ1V2 hJ2
    hJ3 hJ4 S hSorder he w hw hc1 hc2

/-- **`hXmeas` of `term3_cgBound_close`.** -/
theorem aemeasurable_halfWeightDiff_coarsePairs_discharged [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) {e : Vec d}
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega)) :
    ∀ q ∈ coarsePairs d S.n (coarseBlockScale d S) S.m,
      AEMeasurable (fun omega : ShellSeq d =>
        translatedBlockHalfWeightDiff nu S.LPrime w omega q.1 q.2) P.toMeasure := by
  intro q hq
  obtain ⟨hc1, hc2⟩ := openCubeSet_pair_subset_of_mem_coarsePairs (d := d) hq
  exact (measurable_translatedBlockHalfWeightDiff_local hnu P S w hw hc1 hc2).aemeasurable

/-- **`hMembCS` of `term3_cgBound_close`.** -/
theorem memLp_two_halfWeight_sqrt_coarsePairs_discharged [NeZero d] (hd : 2 ≤ d) {nu : ℝ}
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ1V2 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (S : ScaleSelection)
    (hSorder : ScalesOrdering S) {e : Vec d} (he : vecNormSq e = 1)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega)) :
    ∀ q ∈ coarsePairs d S.n (coarseBlockScale d S) S.m,
      MemLp (fun omega : ShellSeq d =>
        translatedBlockHalfWeight nu S.LPrime w omega q.1 q.2 ^ ((1 : ℝ) / 2))
        (ENNReal.ofReal (2 : ℝ)) P.toMeasure := by
  intro q hq
  simpa using memLp_two_halfWeight_sqrt_discharged (d := d) hd hnu hnu1 hPrefix hJ1V2 hJ2
    hJ3 hJ4 S hSorder he w hw (fst_mem_largeCubeSubcubes_of_mem_coarsePairs (d := d) hq) q.2

/-- **`hMembDiff` of `term3_cgBound_close`.** -/
theorem memLp_two_halfWeightDiff_sqrt_coarsePairs_discharged [NeZero d] (hd : 2 ≤ d)
    {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1) {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ1V2 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (S : ScaleSelection)
    (hSorder : ScalesOrdering S) {e : Vec d} (he : vecNormSq e = 1)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega)) :
    ∀ q ∈ coarsePairs d S.n (coarseBlockScale d S) S.m,
      MemLp (fun omega : ShellSeq d =>
        translatedBlockHalfWeightDiff nu S.LPrime w omega q.1 q.2 ^ ((1 : ℝ) / 2))
        (ENNReal.ofReal (2 : ℝ)) P.toMeasure := by
  intro q hq
  obtain ⟨hc1, hc2⟩ := openCubeSet_pair_subset_of_mem_coarsePairs (d := d) hq
  simpa using memLp_two_halfWeightDiff_sqrt_discharged (d := d) hd hnu hnu1 hPrefix hJ1V2
    hJ2 hJ3 hJ4 S hSorder he w hw hc1 hc2

/-! ## 8. `hInt1`, `hInt2` and `hEnergyCube` -/

/-- **`hInt1` of `term3_cgBound_close`, discharged.**  The integrand is a
normalized sum of pairings `(∇w)_{q.1} · (a∇(u_m − u_{n,z}))_{q.2}`; each is
dominated through `|v · z| ≤ |v||z|` by the product of the two `L²(P)` roots,
which is integrable by the exponent pair `2, 2`. -/
theorem integrable_hInt1_discharged [NeZero d] (hd : 2 ≤ d) {nu : ℝ} (hnu : 0 < nu)
    (hnu1 : nu ≤ 1) {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ1V2 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (S : ScaleSelection) (hSorder : ScalesOrdering S) {e : Vec d}
    (he : vecNormSq e = 1)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega)) :
    Integrable (fun omega : ShellSeq d =>
      ((coarsePairs d S.n (coarseBlockScale d S) S.m).card : ℝ)⁻¹ *
        ∑ q ∈ coarsePairs d S.n (coarseBlockScale d S) S.m,
        vecDot (volumeAverageVec (openCubeSet q.1) ((w omega).toH1Function.grad))
          (volumeAverageVec (openCubeSet q.2)
            (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
              (gluedGradientField hnu S.LPrime S.m S.m
                  (fluxSlot nu S.LPrime P S.n e) omega y -
                gluedGradientField hnu S.LPrime S.n S.m
                  (fluxSlot nu S.LPrime P S.n e) omega y)))) P.toMeasure := by
  obtain ⟨hnk, hkm⟩ := coarseBlockScale_bounds (d := d) S hSorder
  have hpair : ∀ q ∈ coarsePairs d S.n (coarseBlockScale d S) S.m,
      Integrable (fun omega : ShellSeq d =>
        vecDot (volumeAverageVec (openCubeSet q.1) ((w omega).toH1Function.grad))
          (volumeAverageVec (openCubeSet q.2)
            (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
              (gluedGradientField hnu S.LPrime S.m S.m
                  (fluxSlot nu S.LPrime P S.n e) omega y -
                gluedGradientField hnu S.LPrime S.n S.m
                  (fluxSlot nu S.LPrime P S.n e) omega y)))) P.toMeasure := by
    intro q hq
    obtain ⟨hc1, hc2⟩ := openCubeSet_pair_subset_of_mem_coarsePairs (d := d) hq
    have hq2 := snd_mem_largeCubeSubcubes_of_mem_coarsePairs (d := d) hnk hkm hq
    have hA := memLp_two_sqrt_vecNormSq_cubeMean_local (d := d) hd hnu hnu1 hPrefix hJ1V2
      hJ2 hJ3 hJ4 S hSorder he w hw hc1
    have hB := memLp_two_sqrt_vecNormSq_fluxMean_local hnu hPrefix hJ2 hJ3 hJ4 S hSorder e hq2
    have hdom := hA.integrable_mul hB
    have hmeas : AEStronglyMeasurable (fun omega : ShellSeq d =>
        vecDot (volumeAverageVec (openCubeSet q.1) ((w omega).toH1Function.grad))
          (volumeAverageVec (openCubeSet q.2)
            (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
              (gluedGradientField hnu S.LPrime S.m S.m
                  (fluxSlot nu S.LPrime P S.n e) omega y -
                gluedGradientField hnu S.LPrime S.n S.m
                  (fluxSlot nu S.LPrime P S.n e) omega y)))) P.toMeasure :=
      (measurable_vecDot_local
        (fun i => (measurable_pi_apply i).comp
          (measurable_volumeAverageVec_grad_subcube (d := d) (m := S.m) (LPrime := S.LPrime)
            (ellPrime := S.ellPrime) (p := testVector nu S.LPrime P S.n e) (w := w) hw hc1))
        (fun i => (measurable_pi_apply i).comp
          (measurable_volumeAverageVec_coefficientCutoff_gluedDifference_final
            hnu P S e q.2 hq2))).aestronglyMeasurable
    refine Integrable.mono' hdom hmeas (Filter.Eventually.of_forall fun omega => ?_)
    rw [Real.norm_eq_abs]
    simp only [Pi.mul_apply]
    exact abs_vecDot_le_rpow_half_mul_rpow_half_local _ _
  exact (integrable_finsetSum _ hpair).const_mul _

/-- **`hInt2` of `term3_cgBound_close`, discharged.**  Same as `hInt1` with the
first carrier replaced by the difference of the two `∇w` cube means. -/
theorem integrable_hInt2_discharged [NeZero d] (hd : 2 ≤ d) {nu : ℝ} (hnu : 0 < nu)
    (hnu1 : nu ≤ 1) {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ1V2 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (S : ScaleSelection) (hSorder : ScalesOrdering S) {e : Vec d}
    (he : vecNormSq e = 1)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega)) :
    Integrable (fun omega : ShellSeq d =>
      ((coarsePairs d S.n (coarseBlockScale d S) S.m).card : ℝ)⁻¹ *
        ∑ q ∈ coarsePairs d S.n (coarseBlockScale d S) S.m,
        vecDot (volumeAverageVec (openCubeSet q.2) ((w omega).toH1Function.grad) -
            volumeAverageVec (openCubeSet q.1) ((w omega).toH1Function.grad))
          (volumeAverageVec (openCubeSet q.2)
            (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
              (gluedGradientField hnu S.LPrime S.m S.m
                  (fluxSlot nu S.LPrime P S.n e) omega y -
                gluedGradientField hnu S.LPrime S.n S.m
                  (fluxSlot nu S.LPrime P S.n e) omega y)))) P.toMeasure := by
  obtain ⟨hnk, hkm⟩ := coarseBlockScale_bounds (d := d) S hSorder
  have hpair : ∀ q ∈ coarsePairs d S.n (coarseBlockScale d S) S.m,
      Integrable (fun omega : ShellSeq d =>
        vecDot (volumeAverageVec (openCubeSet q.2) ((w omega).toH1Function.grad) -
            volumeAverageVec (openCubeSet q.1) ((w omega).toH1Function.grad))
          (volumeAverageVec (openCubeSet q.2)
            (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
              (gluedGradientField hnu S.LPrime S.m S.m
                  (fluxSlot nu S.LPrime P S.n e) omega y -
                gluedGradientField hnu S.LPrime S.n S.m
                  (fluxSlot nu S.LPrime P S.n e) omega y)))) P.toMeasure := by
    intro q hq
    obtain ⟨hc1, hc2⟩ := openCubeSet_pair_subset_of_mem_coarsePairs (d := d) hq
    have hq2 := snd_mem_largeCubeSubcubes_of_mem_coarsePairs (d := d) hnk hkm hq
    have hA := memLp_two_sqrt_vecNormSq_cubeMeanDiff_local (d := d) hd hnu hnu1 hPrefix
      hJ1V2 hJ2 hJ3 hJ4 S hSorder he w hw hc1 hc2
    have hB := memLp_two_sqrt_vecNormSq_fluxMean_local hnu hPrefix hJ2 hJ3 hJ4 S hSorder e hq2
    have hdom := hA.integrable_mul hB
    have hmeas : AEStronglyMeasurable (fun omega : ShellSeq d =>
        vecDot (volumeAverageVec (openCubeSet q.2) ((w omega).toH1Function.grad) -
            volumeAverageVec (openCubeSet q.1) ((w omega).toH1Function.grad))
          (volumeAverageVec (openCubeSet q.2)
            (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
              (gluedGradientField hnu S.LPrime S.m S.m
                  (fluxSlot nu S.LPrime P S.n e) omega y -
                gluedGradientField hnu S.LPrime S.n S.m
                  (fluxSlot nu S.LPrime P S.n e) omega y)))) P.toMeasure :=
      (measurable_vecDot_local
        (fun i => ((measurable_pi_apply i).comp
          (measurable_volumeAverageVec_grad_subcube (d := d) (m := S.m) (LPrime := S.LPrime)
            (ellPrime := S.ellPrime) (p := testVector nu S.LPrime P S.n e) (w := w) hw hc2)).sub
          ((measurable_pi_apply i).comp
          (measurable_volumeAverageVec_grad_subcube (d := d) (m := S.m) (LPrime := S.LPrime)
            (ellPrime := S.ellPrime) (p := testVector nu S.LPrime P S.n e) (w := w) hw hc1)))
        (fun i => (measurable_pi_apply i).comp
          (measurable_volumeAverageVec_coefficientCutoff_gluedDifference_final
            hnu P S e q.2 hq2))).aestronglyMeasurable
    refine Integrable.mono' hdom hmeas (Filter.Eventually.of_forall fun omega => ?_)
    rw [Real.norm_eq_abs]
    simp only [Pi.mul_apply]
    exact abs_vecDot_le_rpow_half_mul_rpow_half_local _ _
  exact (integrable_finsetSum _ hpair).const_mul _

/-- **`hEnergyCube` of `term3_cgBound_close`, discharged.**  The per-sample
`IntegrableOn` clause is deterministic: `|∇u_m|²` is integrable on every open
cube by `memVectorL2_openCubeSet_gluedGradientField`, and the pairing against the
constant flux `F` by the constant-left pairing lemma; the half-open realization
`cubeSet R` differs from `openCubeSet R` by a null set. -/
theorem integrableOn_energyCube_discharged [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) (e : Vec d) :
    ∀ (omega : ShellSeq d) (R : TriadicCube d), R ∈ largeCubeSubcubes d S.n S.m →
      IntegrableOn (fun y : Vec d => -(nu / 2) * vecNormSq
          (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e) omega y) +
        vecDot (fluxSlot nu S.LPrime P S.n e)
          (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e) omega y))
        (cubeSet R) volume := by
  intro omega R _
  have hsq : IntegrableOn (fun y : Vec d => vecNormSq
      (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e) omega y))
      (openCubeSet R) volume :=
    integrableOn_vecNormSq_gluedGradientField hnu S.LPrime S.m S.m
      (fluxSlot nu S.LPrime P S.n e) omega R
  have hpair : IntegrableOn (fun y : Vec d =>
      vecDot (fluxSlot nu S.LPrime P S.n e)
        (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e) omega y))
      (openCubeSet R) volume :=
    CorrectionFieldData.integrableOn_vecDot_const_left_of_memVectorL2
      (fluxSlot nu S.LPrime P S.n e)
      (memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.m S.m
        (fluxSlot nu S.LPrime P S.n e) omega R)
  have hcomb : IntegrableOn (fun y : Vec d => -(nu / 2) * vecNormSq
        (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e) omega y) +
      vecDot (fluxSlot nu S.LPrime P S.n e)
        (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e) omega y))
      (openCubeSet R) volume :=
    (show Integrable (fun y : Vec d => -(nu / 2) * vecNormSq
        (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e) omega y))
        (volume.restrict (openCubeSet R)) from hsq.const_mul _).add
      (show Integrable (fun y : Vec d => vecDot (fluxSlot nu S.LPrime P S.n e)
        (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e) omega y))
        (volume.restrict (openCubeSet R)) from hpair)
  exact hcomb.congr_set_ae (cubeSet_ae_eq_openCubeSet R)

-- the display `term3_cgBound_closeB` and its proof moved to
-- `SuperdiffusionCLT.Section3.Terms.RHSTerm3CgCloseC`,
-- which imports this module

end

end SuperdiffusionCLT.Section3.Terms
