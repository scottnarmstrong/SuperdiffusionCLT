/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3SideConditions
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3SourceGapsB
public import SuperdiffusionCLT.Section3.ResponseFields.RegboundsWindowB
public import SuperdiffusionCLT.Section3.Terms.GluedFieldDifferenceMeasurable
public import SuperdiffusionCLT.Section3.Terms.MaximizerCoefficientStabilityB

/-!
# The three sample-side residues of `e.RHS.term3`

The obligation binders `_hosc`, `_hcg` and `_hbHalfInt` of the term-3
statement, stated verbatim from the
reduction of the final Term 3 statement and discharged down to the carriers that survive
the fourth-moment route of `l.w.basic.regbounds`.

For `_hcg` and `_hosc` one needs the per-sub-cube family

`hMemGrad : ∀ R ∈ largeCubeSubcubes d S.n S.m, MemLp (ω ↦ ⍍_R |∇w|²) 2 P`

of the *squared* cube mean of `∇w`, and for `_hbHalfInt` the same family at an
arbitrary sub-cube scale.  That family is discharged here.  It is a consequence
of the single finiteness statement `E[‖∇w‖^4_{L4bar(cu_m)}] < ∞`, which is
itself a theorem of `d` and `2 ≤ d`:
`l_w_basic_regbounds_window` supplies the `L^8` envelope of the a priori
estimates and `lintegral_gradFour_pow_ne_top` turns it into the fourth moment.
The per-sub-cube Jensen bound is `ofReal_subcube_fourth_average_le`, general in
the sub-cube scale, so one lemma serves the scale-`n` lattice of the two printed
steps and the scale-`k` lattice of the half-weight carrier.

## Main results

* `memLp_vecNormSq_volumeAverageVec_grad_of_fourthMoment`: the squared cube mean
  of `∇w` on any sub-cube of `cu_m` at any scale is annealed square integrable,
  from the finiteness of the fourth moment on `cu_m` alone.
* `gradFour_finite_of_regbounds`: that finiteness, from `d`, `2 ≤ d` and the
  statement's own binders.
* `sideCondition_hcg_final`: the binder `_hcg`, with `hMemGrad` **and**
  the measurability of the flux cube mean discharged; the only carrier left is
  the annealed square integrability of the cutoff-flux cube mean (`hMemFlux`).
* `sideCondition_hosc_final`: the binder `_hosc`, again with `hMemGrad`
  and the flux-cube-mean measurability discharged; the carriers left are the
  large-cube pairing `hPair` and `hMemFlux`.
* `memLp_two_translatedBlockNorm_final`: the coarse block norm is annealed
  square integrable, from the `Γ₁` envelope.
* `sideCondition_hbHalfInt_final`: the half-weight carrier on the printed range
  of `e.bL.to.bhomell` -- `z'` a sub-cube of `cu_m` at any
  scale and every `z` -- with **every** carrier discharged.

## The printed range is the maximal domain

`w ω` is an `H10Function (openCubeSet cu_m)` whose weak gradient is a class on
`cu_m` only -- `H10Function.grad` is `MemL2On U`, and `U = openCubeSet cu_m`.
The cube mean `⍍_{z'} ∇w` therefore exists only against a cube contained in
`cu_m`; for a sub-cube at scale `k ≤ S.m` containment is
`openCubeSet_subset_of_mem_descendantsAtDepth`, and the family
`largeCubeSubcubes d k S.m`, `k` ranging, is exactly the triadic cubes contained
in `cu_m`.  The statement below is the interface on that maximal domain, which is
the printed `z' ∈ 3^k Z^d ∩ cu_m`; a reading for arbitrary `z'` could not be
discharged, since the cube mean does not exist for cubes not contained in `cu_m`.

## What each residual really is

`hMemFlux` and `hPair` both dominate the cutoff coefficient `a_{L'}`.  The
largest `L^∞` envelope of the cutoff on `cu_m` that carries an annealed
moment is `coeffLinftySupBound nu L m`, and the `Γ₂` tail
`isBigO_gammaSigma_coeffLinftySupBound` -- with it every moment statement
built on it, e.g. `second_moment_coeffLinftySupBound_le` -- requires `L ≤ m`.
The statement reads the cutoff at `L' = m + 2a > m`
(`ScaleSelection.LPrime_eq`), so the envelope moment is simply not available at
that scale.  The residual is a moment of the coefficient envelope at an
enlarged cutoff scale.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory ProbabilityTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Measurability of the cube mean of `∇w` and of its square -/

/-- The identity matrix acts trivially on a vector. -/
private theorem matVecMul_one_mat_final (v : Vec d) : matVecMul (1 : Mat d) v = v := by
  funext i
  simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]

/-- `vecNormSq` is measurable as soon as the coordinates are. -/
private theorem measurable_vecNormSq_of_components_final {Omega : Type*} [MeasurableSpace Omega]
    {v : Omega → Vec d} (hv : ∀ i : Fin d, Measurable fun omega => v omega i) :
    Measurable fun omega => vecNormSq (v omega) := by
  show Measurable fun omega => vecDot (v omega) (v omega)
  exact Finset.measurable_sum _ fun i _ => (hv i).mul (hv i)

/-- Pairing two vector-valued maps with measurable coordinates is measurable. -/
private theorem measurable_vecDot_final {Omega : Type*} [MeasurableSpace Omega]
    {v u : Omega → Vec d}
    (hv : ∀ i : Fin d, Measurable fun omega => v omega i)
    (hu : ∀ i : Fin d, Measurable fun omega => u omega i) :
    Measurable fun omega => vecDot (v omega) (u omega) := by
  simp only [vecDot]
  exact Finset.measurable_sum _ fun i _ => (hv i).mul (hu i)

/-- The pairing of a measurable vector through a measurable matrix is
measurable. -/
private theorem measurable_vecDot_matVecMul_self_final {Omega : Type*}
    [MeasurableSpace Omega] {M : Omega → Mat d} {v : Omega → Vec d}
    (hM : ∀ i j, Measurable fun omega => M omega i j)
    (hv : ∀ i, Measurable fun omega => v omega i) :
    Measurable fun omega => vecDot (v omega) (matVecMul (M omega) (v omega)) := by
  simp only [vecDot, matVecMul]
  exact Finset.measurable_sum _ fun i _ =>
    (hv i).mul (Finset.measurable_sum _ fun j _ => (hM i j).mul (hv j))

/-- **The coordinates of the cube mean of `∇w` are measurable in the sample**,
on any cube contained in `cu_m`.  The canonical-response route: `∇w` carries the
weak-gradient class of the canonical response, so
`measurable_volumeAverageVec_matVecMul_grad_of_canonical` reads the cube mean of
`∇w` off the cube mean of the canonical gradient, which is measurable by
`measurable_volumeAverageVec_matVecMul_grad_dirichletResponse_comp`. -/
private theorem measurable_volumeAverageVec_grad_component_final [NeZero d] {nu : ℝ}
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) {e : Vec d}
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega))
    {z' : TriadicCube d} (hsub : openCubeSet z' ⊆ openCubeSet (originCube d (S.m : ℤ)))
    (i : Fin d) :
    Measurable (fun omega : ShellSeq d =>
      volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad) i) := by
  have hcan : Measurable (fun omega : ShellSeq d =>
      volumeAverageVec (openCubeSet z')
        (fun y => matVecMul ((1 : Mat d))
          ((dirichletResponse omega S.LPrime S.ellPrime S.m
            (testVector nu S.LPrime P S.n e)).toH1Function.grad y))) := by
    refine measurable_volumeAverageVec_matVecMul_grad_dirichletResponse_comp
      (alpha := ShellSeq d) (fun omega => omega) (fun _ _ => (1 : Mat d)) ?_ ?_
      S.LPrime S.ellPrime S.m (testVector nu S.LPrime P S.n e) hsub
      (measurableSet_openCubeSet z') ?_
    · intro a i j
      exact continuous_const
    · intro y i j
      exact measurable_const
    · intro x
      exact measurable_dirichletRhsField_apply S.LPrime S.ellPrime
        (testVector nu S.LPrime P S.n e) x
  have hv1 : Measurable (fun omega : ShellSeq d =>
      volumeAverageVec (openCubeSet z')
        (fun y => matVecMul ((1 : Mat d)) ((w omega).toH1Function.grad y))) :=
    measurable_volumeAverageVec_matVecMul_grad_of_canonical hsub
      (fun _ _ => (1 : Mat d)) hw hcan
  have hEq : (fun omega : ShellSeq d =>
      volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad) i) =
      fun omega : ShellSeq d => volumeAverageVec (openCubeSet z')
        (fun y => matVecMul ((1 : Mat d)) ((w omega).toH1Function.grad y)) i := by
    funext omega
    exact congrArg (fun v : Vec d => v i)
      (congrArg (volumeAverageVec (openCubeSet z'))
        (funext fun y => (matVecMul_one_mat_final _).symm))
  rw [hEq]
  exact (measurable_pi_apply i).comp hv1

/-- **The squared cube mean of `∇w` is measurable in the sample**, on any cube
contained in `cu_m`. -/
private theorem measurable_vecNormSq_volumeAverageVec_grad_final [NeZero d] {nu : ℝ}
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) {e : Vec d}
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega))
    {z' : TriadicCube d} (hsub : openCubeSet z' ⊆ openCubeSet (originCube d (S.m : ℤ))) :
    Measurable (fun omega : ShellSeq d =>
      vecNormSq (volumeAverageVec (openCubeSet z')
        ((w omega).toH1Function.grad))) :=
  measurable_vecNormSq_of_components_final fun i =>
    measurable_volumeAverageVec_grad_component_final P S w hw hsub i

/-- **The pairing of two annealed-`L²` cube means is integrable.**  Cauchy–Schwarz
on the two vectors together with the Young inequality
`abs_le_add_halves_of_sq_le_mul` bounds `|vecDot G Q|` by
`vecNormSq G + vecNormSq Q`, the sum of two `L²(P)` functions. -/
private theorem integrable_vecDot_cubeMeans_final {P : ProbabilityMeasure (ShellSeq d)}
    (G Qf : ShellSeq d → Vec d)
    (hG : MemLp (fun omega : ShellSeq d => vecNormSq (G omega)) 2 P.toMeasure)
    (hQ : MemLp (fun omega : ShellSeq d => vecNormSq (Qf omega)) 2 P.toMeasure)
    (hGm : ∀ i : Fin d, Measurable fun omega : ShellSeq d => G omega i)
    (hQm : ∀ i : Fin d, Measurable fun omega : ShellSeq d => Qf omega i) :
    Integrable (fun omega : ShellSeq d => vecDot (G omega) (Qf omega)) P.toMeasure := by
  have hbound : ∀ omega : ShellSeq d,
      ‖vecDot (G omega) (Qf omega)‖ ≤ vecNormSq (G omega) + vecNormSq (Qf omega) := by
    intro omega
    rw [Real.norm_eq_abs]
    have h1 := Homogenization.abs_le_add_halves_of_sq_le_mul
      (Homogenization.sq_vecDot_le_vecNormSq_mul_vecNormSq (G omega) (Qf omega))
      (Homogenization.vecNormSq_nonneg (G omega)) (Homogenization.vecNormSq_nonneg (Qf omega))
    have h2 : vecNormSq (G omega) / 2 + vecNormSq (Qf omega) / 2 ≤
        vecNormSq (G omega) + vecNormSq (Qf omega) := by
      have hg := Homogenization.vecNormSq_nonneg (G omega)
      have hq := Homogenization.vecNormSq_nonneg (Qf omega)
      linarith only [hg, hq]
    linarith only [h1, h2]
  refine Integrable.mono' ?_ (measurable_vecDot_final hGm hQm).aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)
  exact (MeasureTheory.MemLp.integrable (by norm_num) hG).add
    (MeasureTheory.MemLp.integrable (by norm_num) hQ)

/-! ## The fourth moment of `∇w` gives the squared cube mean, at any scale -/

/-- **The squared cube mean of `∇w` on any sub-cube of `cu_m`, at any scale, is
annealed square integrable**, from the finiteness of the fourth moment
`E[‖∇w‖^4_{L4bar(cu_m)}]` alone.  The two Jensen inequalities
`|⍍_{z'} ∇w|^2 ≤ ⍍_{z'} |∇w|^2 ≤ ⍍_{z'} |∇w|^4` are
`ofReal_subcube_fourth_average_le`, general in the sub-cube scale; the lattice
average is compared to its largest summand, the factor being the number of
sub-cubes at that scale. -/
theorem memLp_vecNormSq_volumeAverageVec_grad_of_fourthMoment [NeZero d] {nu : ℝ}
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) {e : Vec d}
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega))
    (hfin : (∫⁻ omega : ShellSeq d,
        (vecCubeLpENorm (originCube d (S.m : ℤ)) 4 (w omega).toH1Function.grad) ^ (4 : ℕ)
      ∂P.toMeasure) ≠ ⊤)
    {k : ℕ} (z' : TriadicCube d) (hz' : z' ∈ largeCubeSubcubes d k S.m) :
    MemLp (fun omega : ShellSeq d =>
      vecNormSq (volumeAverageVec (openCubeSet z')
        ((w omega).toH1Function.grad))) 2 P.toMeasure := by
  classical
  have hsub : openCubeSet z' ⊆ openCubeSet (originCube d (S.m : ℤ)) := by
    rw [largeCubeSubcubes_eq_descendantsAtDepth] at hz'
    exact openCubeSet_subset_of_mem_descendantsAtDepth hz'
  have hmeas := measurable_vecNormSq_volumeAverageVec_grad_final P S w hw hsub
  have hnn : ∀ omega : ShellSeq d, (0 : ℝ) ≤
      vecNormSq (volumeAverageVec (openCubeSet z')
        ((w omega).toH1Function.grad)) ^ (2 : ℕ) :=
    fun _ => pow_nonneg (vecNormSq_nonneg _) 2
  have hsqmeas : Measurable (fun omega : ShellSeq d =>
      vecNormSq (volumeAverageVec (openCubeSet z')
        ((w omega).toH1Function.grad)) ^ (2 : ℕ)) := hmeas.pow_const 2
  have hint : MeasureTheory.Integrable (fun omega : ShellSeq d =>
      vecNormSq (volumeAverageVec (openCubeSet z')
        ((w omega).toH1Function.grad)) ^ (2 : ℕ)) P.toMeasure := by
    refine ⟨hsqmeas.aestronglyMeasurable, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnn)]
    have hcardnat : 0 < (largeCubeSubcubes d k S.m).card :=
      Finset.card_pos.mpr (largeCubeSubcubes_nonempty d k S.m)
    have hcard : (0 : ℝ) < ((largeCubeSubcubes d k S.m).card : ℝ) := by
      exact_mod_cast hcardnat
    have hsingle : ∀ omega : ShellSeq d,
        vecNormSq (volumeAverageVec (openCubeSet z')
          ((w omega).toH1Function.grad)) ^ (2 : ℕ) ≤
          ((largeCubeSubcubes d k S.m).card : ℝ) *
            ((((largeCubeSubcubes d k S.m).card : ℝ)⁻¹ *
              ∑ R ∈ largeCubeSubcubes d k S.m,
                vecNormSq (volumeAverageVec (openCubeSet R)
                  ((w omega).toH1Function.grad)) ^ (2 : ℕ))) := by
      intro omega
      have h1 : ((largeCubeSubcubes d k S.m).card : ℝ) *
          ((((largeCubeSubcubes d k S.m).card : ℝ)⁻¹ *
            ∑ R ∈ largeCubeSubcubes d k S.m,
              vecNormSq (volumeAverageVec (openCubeSet R)
                ((w omega).toH1Function.grad)) ^ (2 : ℕ))) =
          ∑ R ∈ largeCubeSubcubes d k S.m,
            vecNormSq (volumeAverageVec (openCubeSet R)
              ((w omega).toH1Function.grad)) ^ (2 : ℕ) :=
        mul_inv_cancel_left₀ (ne_of_gt hcard) _
      calc vecNormSq (volumeAverageVec (openCubeSet z')
            ((w omega).toH1Function.grad)) ^ (2 : ℕ)
          ≤ ∑ R ∈ largeCubeSubcubes d k S.m,
              vecNormSq (volumeAverageVec (openCubeSet R)
                ((w omega).toH1Function.grad)) ^ (2 : ℕ) :=
            Finset.single_le_sum (f := fun R : TriadicCube d =>
                vecNormSq (volumeAverageVec (openCubeSet R)
                  ((w omega).toH1Function.grad)) ^ (2 : ℕ))
              (fun _ _ => pow_nonneg (vecNormSq_nonneg _) 2) hz'
        _ = ((largeCubeSubcubes d k S.m).card : ℝ) *
              ((((largeCubeSubcubes d k S.m).card : ℝ)⁻¹ *
                ∑ R ∈ largeCubeSubcubes d k S.m,
                  vecNormSq (volumeAverageVec (openCubeSet R)
                    ((w omega).toH1Function.grad)) ^ (2 : ℕ))) := h1.symm
    have hstep1 : (∫⁻ omega : ShellSeq d, ENNReal.ofReal
        (vecNormSq (volumeAverageVec (openCubeSet z')
          ((w omega).toH1Function.grad)) ^ (2 : ℕ))
        ∂P.toMeasure) ≤
        (∫⁻ omega : ShellSeq d, ENNReal.ofReal
            (((largeCubeSubcubes d k S.m).card : ℝ) *
              ((((largeCubeSubcubes d k S.m).card : ℝ)⁻¹ *
                ∑ R ∈ largeCubeSubcubes d k S.m,
                  vecNormSq (volumeAverageVec (openCubeSet R)
                    ((w omega).toH1Function.grad)) ^ (2 : ℕ))))
          ∂P.toMeasure) :=
      lintegral_mono fun omega => ENNReal.ofReal_le_ofReal (hsingle omega)
    have hmul : ∀ omega : ShellSeq d,
        ENNReal.ofReal (((largeCubeSubcubes d k S.m).card : ℝ) *
            ((((largeCubeSubcubes d k S.m).card : ℝ)⁻¹ *
              ∑ R ∈ largeCubeSubcubes d k S.m,
                vecNormSq (volumeAverageVec (openCubeSet R)
                  ((w omega).toH1Function.grad)) ^ (2 : ℕ)))) =
        ENNReal.ofReal (((largeCubeSubcubes d k S.m).card : ℝ)) *
          ENNReal.ofReal ((((largeCubeSubcubes d k S.m).card : ℝ)⁻¹ *
            ∑ R ∈ largeCubeSubcubes d k S.m,
              vecNormSq (volumeAverageVec (openCubeSet R)
                ((w omega).toH1Function.grad)) ^ (2 : ℕ))) :=
      fun omega => ENNReal.ofReal_mul (le_of_lt hcard)
    have hpull : (∫⁻ omega : ShellSeq d, ENNReal.ofReal
          (((largeCubeSubcubes d k S.m).card : ℝ) *
            ((((largeCubeSubcubes d k S.m).card : ℝ)⁻¹ *
              ∑ R ∈ largeCubeSubcubes d k S.m,
                vecNormSq (volumeAverageVec (openCubeSet R)
                  ((w omega).toH1Function.grad)) ^ (2 : ℕ))))
        ∂P.toMeasure) =
        ENNReal.ofReal (((largeCubeSubcubes d k S.m).card : ℝ)) *
          (∫⁻ omega : ShellSeq d, ENNReal.ofReal
              ((((largeCubeSubcubes d k S.m).card : ℝ)⁻¹ *
                ∑ R ∈ largeCubeSubcubes d k S.m,
                  vecNormSq (volumeAverageVec (openCubeSet R)
                    ((w omega).toH1Function.grad)) ^ (2 : ℕ)))
            ∂P.toMeasure) := by
      rw [MeasureTheory.lintegral_congr_ae (Filter.Eventually.of_forall hmul),
        MeasureTheory.lintegral_const_mul'
          (r := ENNReal.ofReal (((largeCubeSubcubes d k S.m).card : ℝ)))
          (f := fun omega : ShellSeq d => ENNReal.ofReal
            ((((largeCubeSubcubes d k S.m).card : ℝ)⁻¹ *
              ∑ R ∈ largeCubeSubcubes d k S.m,
                vecNormSq (volumeAverageVec (openCubeSet R)
                  ((w omega).toH1Function.grad)) ^ (2 : ℕ))))
          (by exact ENNReal.ofReal_ne_top)]
    have hb : (∫⁻ omega : ShellSeq d, ENNReal.ofReal
          ((((largeCubeSubcubes d k S.m).card : ℝ)⁻¹ *
            ∑ R ∈ largeCubeSubcubes d k S.m,
              vecNormSq (volumeAverageVec (openCubeSet R)
                ((w omega).toH1Function.grad)) ^ (2 : ℕ)))
        ∂P.toMeasure) ≤
        (∫⁻ omega : ShellSeq d,
          (vecCubeLpENorm (originCube d (S.m : ℤ)) 4 (w omega).toH1Function.grad) ^ (4 : ℕ)
          ∂P.toMeasure) :=
      lintegral_mono fun omega =>
        ofReal_subcube_fourth_average_le (w omega).toH1Function.grad_memVectorL2
    have hle : (∫⁻ omega : ShellSeq d, ENNReal.ofReal
          (vecNormSq (volumeAverageVec (openCubeSet z')
            ((w omega).toH1Function.grad)) ^ (2 : ℕ))
        ∂P.toMeasure) ≤
        ENNReal.ofReal (((largeCubeSubcubes d k S.m).card : ℝ)) *
          (∫⁻ omega : ShellSeq d,
            (vecCubeLpENorm (originCube d (S.m : ℤ)) 4
              (w omega).toH1Function.grad) ^ (4 : ℕ)
            ∂P.toMeasure) :=
      le_trans hstep1 (le_trans (le_of_eq hpull) (mul_le_mul_of_nonneg_left hb zero_le))
    exact hle.trans_lt
      (lt_top_iff_ne_top.2 (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin))
  exact (MeasureTheory.memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).mpr hint

/-! ## The fourth moment of the response gradient, from the binders -/

/-- **`E[‖∇w‖^4_{L4bar(cu_m)}] < ∞`**, from `d`, `2 ≤ d` and the
statement's own binders.  The `L^8` envelope of `e.nablaw.Lt` is the first
conjunct of `l_w_basic_regbounds_window`, whose every input is discharged, and
`lintegral_gradFour_pow_ne_top` turns it into the fourth moment. -/
theorem gradFour_finite_of_regbounds [NeZero d] (hd : 2 ≤ d) {nu : ℝ} (hnu : 0 < nu)
    (hnu1 : nu ≤ 1) {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ1V2 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (S : ScaleSelection) (hSorder : ScalesOrdering S)
    {e : Vec d} (he : vecNormSq e = 1)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega)) :
    (∫⁻ omega : ShellSeq d,
        (vecCubeLpENorm (originCube d (S.m : ℤ)) 4 (w omega).toH1Function.grad) ^ (4 : ℕ)
      ∂P.toMeasure) ≠ ⊤ := by
  obtain ⟨Creg, hCreg, hregw⟩ := l_w_basic_regbounds_window d hd
  obtain ⟨Zw, hZwmeas, hZwbigO, hZwbound⟩ :=
    (hregw nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder e he
      (testVector nu S.LPrime P S.n e) rfl w hw).1
  exact lintegral_gradFour_pow_ne_top hnu hPrefix hJ2 hJ3 hJ4 S hSorder he rfl w
    hCreg hZwmeas hZwbigO hZwbound

/-! ## The cutoff-flux cube mean is measurable -/

/-- **The cube mean of the cutoff flux of the glued-field difference is
measurable in the sample.**  On the sub-cube `R ⊆ cu_m`,
`volumeAverageVec_matVecMul_eq_inner` writes the `i`-th coordinate as the inner
product of two `L²(cu_m)` classes: the cutoff `i`-th row, zero-extended off `R`
(`measurable_toHilbertVectorL2OfVecField_of_measurable` at the jointly
measurable cutoff field `measurable_prod_coefficientCutoff`), against the
difference of the two glued gradient fields.  That difference of classes is
measurable: the class map subtracts (`toHilbertVectorL2OfVecField_sub`) and each
glued class is a measurable function of the sample
(`measurable_gluedGradientClass`). -/
theorem measurable_volumeAverageVec_coefficientCutoff_gluedDifference_final [NeZero d]
    {nu : ℝ} (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection)
    (e : Vec d) (R : TriadicCube d) (hR : R ∈ largeCubeSubcubes d S.n S.m) :
    Measurable (fun omega : ShellSeq d =>
      volumeAverageVec (openCubeSet R) (fun y =>
        matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
          (gluedGradientField hnu S.LPrime S.m S.m
              (fluxSlot nu S.LPrime P S.n e) omega y -
            gluedGradientField hnu S.LPrime S.n S.m
              (fluxSlot nu S.LPrime P S.n e) omega y))) := by
  classical
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  set F : Vec d := fluxSlot nu S.LPrime P S.n e with hF
  set Q : TriadicCube d := originCube d (S.m : ℤ) with hQ
  have hVU : openCubeSet R ⊆ openCubeSet Q := by
    rw [largeCubeSubcubes_eq_descendantsAtDepth] at hR
    exact openCubeSet_subset_of_mem_descendantsAtDepth hR
  have hV : MeasurableSet (openCubeSet R) := measurableSet_openCubeSet R
  have hgmem : ∀ omega : ShellSeq d, MemVectorL2 (openCubeSet Q) (fun y : Vec d =>
      gluedGradientField hnu S.LPrime S.m S.m F omega y -
        gluedGradientField hnu S.LPrime S.n S.m F omega y) := fun omega =>
    (memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.m S.m F omega Q).sub
      (memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.n S.m F omega Q)
  have hKmem : ∀ (omega : ShellSeq d) (i : Fin d), MemVectorL2 (openCubeSet Q)
      (Set.indicator (openCubeSet R)
        (fun y : Vec d => (fun j => ((coefficientCutoff nu omega S.LPrime).toCoeffField y) i j
          : Vec d))) := fun omega i =>
    (memVectorL2_of_continuous (S.m : ℤ)
      (continuous_pi fun j => continuous_coefficientCutoff_entry nu omega S.LPrime i j)).indicator hV
  have hgclass : Measurable (fun omega : ShellSeq d =>
      toHilbertVectorL2OfVecField (hgmem omega)) := by
    have heq : (fun omega : ShellSeq d => toHilbertVectorL2OfVecField (hgmem omega)) =
        fun omega : ShellSeq d =>
          toHilbertVectorL2OfVecField
              (memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.m S.m F omega Q) -
            toHilbertVectorL2OfVecField
              (memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.n S.m F omega Q) := by
      funext omega
      exact toHilbertVectorL2OfVecField_sub _ _
    rw [heq]
    exact (measurable_gluedGradientClass (d := d) hnu S.LPrime S.m S.m F).sub
      (measurable_gluedGradientClass (d := d) hnu S.LPrime S.n S.m F)
  have hKclass : ∀ i : Fin d, Measurable (fun omega : ShellSeq d =>
      toHilbertVectorL2OfVecField (hKmem omega i)) := by
    intro i
    refine measurable_toHilbertVectorL2OfVecField_of_measurable ?_ (fun omega => hKmem omega i)
    have hrow : Measurable fun q : ShellSeq d × Vec d =>
        (fun j => ((coefficientCutoff nu q.1 S.LPrime).toCoeffField q.2) i j : Vec d) :=
      Measurable.of_eval fun j =>
        (measurable_pi_apply j).comp ((measurable_pi_apply i).comp
          (measurable_prod_coefficientCutoff nu S.LPrime))
    have hrw : (fun q : ShellSeq d × Vec d => Set.indicator (openCubeSet R)
        (fun y : Vec d => (fun j => ((coefficientCutoff nu q.1 S.LPrime).toCoeffField y) i j
          : Vec d)) q.2) =
        Set.indicator (Prod.snd ⁻¹' (openCubeSet R)) (fun q : ShellSeq d × Vec d =>
          (fun j => ((coefficientCutoff nu q.1 S.LPrime).toCoeffField q.2) i j : Vec d)) := by
      funext q
      by_cases hq : q.2 ∈ openCubeSet R
      · rw [Set.indicator_of_mem hq,
          Set.indicator_of_mem (show q ∈ Prod.snd ⁻¹' (openCubeSet R) from hq)]
      · rw [Set.indicator_of_notMem hq,
          Set.indicator_of_notMem (show q ∉ Prod.snd ⁻¹' (openCubeSet R) from hq)]
    rw [hrw]
    exact hrow.indicator (measurable_snd hV)
  refine Measurable.of_eval fun i => ?_
  have hfun : (fun omega : ShellSeq d => volumeAverageVec (openCubeSet R) (fun y =>
      matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
        (gluedGradientField hnu S.LPrime S.m S.m F omega y -
          gluedGradientField hnu S.LPrime S.n S.m F omega y)) i) =
      fun omega : ShellSeq d => (MeasureTheory.volume (openCubeSet R)).toReal⁻¹ *
        inner ℝ (toHilbertVectorL2OfVecField (hKmem omega i))
          (toHilbertVectorL2OfVecField (hgmem omega)) := by
    funext omega
    exact volumeAverageVec_matVecMul_eq_inner hVU hV
      (fun y => (coefficientCutoff nu omega S.LPrime).toCoeffField y) (hgmem omega) i
      (hKmem omega i)
  rw [hfun]
  exact (continuous_inner.measurable.comp ((hKclass i).prodMk hgclass)).const_mul _

/-! ## The `hcg` residue -/

/-- **The binder `_hcg` of the final Term 3 reduction**, verbatim: the
coarse-grained lattice average `card⁻¹ ∑_R ⍍_R ∇w · ⍍_R (a_{L'}(∇ũ_m − ∇ũ_n))`
is `P`-integrable.  Two of the three carriers of `sideCondition_hcg_final` are
discharged here: the flux-cube-mean measurability by
`measurable_volumeAverageVec_coefficientCutoff_gluedDifference_final`, and the
per-sub-cube family `hMemGrad` by
`memLp_vecNormSq_volumeAverageVec_grad_of_fourthMoment` at
`gradFour_finite_of_regbounds`.  The single carrier left is the annealed square
integrability of the cutoff-flux cube mean. -/
theorem sideCondition_hcg_final [NeZero d] (hd : 2 ≤ d) {nu : ℝ} (hnu : 0 < nu)
    (hnu1 : nu ≤ 1) {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ1V2 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (S : ScaleSelection) (hSorder : ScalesOrdering S)
    {e : Vec d} (he : vecNormSq e = 1)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega))
    (hMemFlux : ∀ R ∈ largeCubeSubcubes d S.n S.m, MemLp (fun omega : ShellSeq d =>
        vecNormSq (volumeAverageVec (openCubeSet R) (fun y =>
          matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
            (gluedGradientField hnu S.LPrime S.m S.m
                (fluxSlot nu S.LPrime P S.n e) omega y -
              gluedGradientField hnu S.LPrime S.n S.m
                (fluxSlot nu S.LPrime P S.n e) omega y)))) 2 P.toMeasure) :
    Integrable (fun omega : ShellSeq d =>
      ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
        ∑ R ∈ largeCubeSubcubes d S.n S.m,
          vecDot (volumeAverageVec (openCubeSet R) ((w omega).toH1Function.grad))
            (volumeAverageVec (openCubeSet R) (fun y =>
              matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
                (gluedGradientField hnu S.LPrime S.m S.m
                    (fluxSlot nu S.LPrime P S.n e) omega y -
                  gluedGradientField hnu S.LPrime S.n S.m
                    (fluxSlot nu S.LPrime P S.n e) omega y)))) P.toMeasure := by
  classical
  have hfin := gradFour_finite_of_regbounds hd hnu hnu1 hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder he w hw
  have hMemGrad : ∀ R ∈ largeCubeSubcubes d S.n S.m, MemLp (fun omega : ShellSeq d =>
      vecNormSq (volumeAverageVec (openCubeSet R)
        ((w omega).toH1Function.grad))) 2 P.toMeasure :=
    fun R hR => memLp_vecNormSq_volumeAverageVec_grad_of_fourthMoment P S w hw hfin R hR
  have hFluxMeas : ∀ R ∈ largeCubeSubcubes d S.n S.m, Measurable (fun omega : ShellSeq d =>
      volumeAverageVec (openCubeSet R) (fun y =>
        matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
          (gluedGradientField hnu S.LPrime S.m S.m
              (fluxSlot nu S.LPrime P S.n e) omega y -
            gluedGradientField hnu S.LPrime S.n S.m
              (fluxSlot nu S.LPrime P S.n e) omega y))) :=
    fun R hR => measurable_volumeAverageVec_coefficientCutoff_gluedDifference_final
      hnu P S e R hR
  have hsub : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      openCubeSet R ⊆ openCubeSet (originCube d (S.m : ℤ)) := by
    intro R hR
    rw [largeCubeSubcubes_eq_descendantsAtDepth] at hR
    exact openCubeSet_subset_of_mem_descendantsAtDepth hR
  have hsummand : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      Integrable (fun omega : ShellSeq d =>
        vecDot (volumeAverageVec (openCubeSet R) ((w omega).toH1Function.grad))
          (volumeAverageVec (openCubeSet R) (fun y =>
            matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
              (gluedGradientField hnu S.LPrime S.m S.m
                  (fluxSlot nu S.LPrime P S.n e) omega y -
                gluedGradientField hnu S.LPrime S.n S.m
                  (fluxSlot nu S.LPrime P S.n e) omega y)))) P.toMeasure := by
    intro R hR
    have hgm : ∀ i : Fin d, Measurable (fun omega : ShellSeq d =>
        volumeAverageVec (openCubeSet R) ((w omega).toH1Function.grad) i) :=
      fun i => measurable_volumeAverageVec_grad_component_final P S w hw (hsub R hR) i
    have hfm : ∀ i : Fin d, Measurable (fun omega : ShellSeq d =>
        volumeAverageVec (openCubeSet R) (fun y =>
          matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
            (gluedGradientField hnu S.LPrime S.m S.m
                (fluxSlot nu S.LPrime P S.n e) omega y -
              gluedGradientField hnu S.LPrime S.n S.m
                (fluxSlot nu S.LPrime P S.n e) omega y)) i) :=
      fun i => (measurable_pi_apply i).comp (hFluxMeas R hR)
    exact integrable_vecDot_cubeMeans_final _ _ (hMemGrad R hR) (hMemFlux R hR) hgm hfm
  have hsum : Integrable (fun omega : ShellSeq d =>
      ∑ R ∈ largeCubeSubcubes d S.n S.m,
        vecDot (volumeAverageVec (openCubeSet R) ((w omega).toH1Function.grad))
          (volumeAverageVec (openCubeSet R) (fun y =>
            matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
              (gluedGradientField hnu S.LPrime S.m S.m
                  (fluxSlot nu S.LPrime P S.n e) omega y -
                gluedGradientField hnu S.LPrime S.n S.m
                  (fluxSlot nu S.LPrime P S.n e) omega y)))) P.toMeasure :=
    MeasureTheory.integrable_finsetSum _ hsummand
  exact hsum.const_mul _

/-! ## The `hosc` residue -/

/-- **The binder `_hosc` of the final Term 3 reduction**, verbatim: the
oscillation lattice average, the pairing of the centred response gradient
`∇w − ⍍_R ∇w` with the cutoff flux of the glued-field difference, is
`P`-integrable.  By the cube-average splitting
`volumeAverage_avsum_centered_splitting` the large-cube pairing is the sum of
this oscillation term and the `hcg` lattice average, so the oscillation
integrand is the difference of the two; both are `P`-integrable -- the lattice
average by `sideCondition_hcg_final` (whose `hMemGrad` and measurability
carriers are discharged), the large-cube pairing by the carrier `hPair`. -/
theorem sideCondition_hosc_final [NeZero d] (hd : 2 ≤ d) {nu : ℝ} (hnu : 0 < nu)
    (hnu1 : nu ≤ 1) {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ1V2 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (S : ScaleSelection) (hSorder : ScalesOrdering S)
    {e : Vec d} (he : vecNormSq e = 1)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega))
    (hMemFlux : ∀ R ∈ largeCubeSubcubes d S.n S.m, MemLp (fun omega : ShellSeq d =>
        vecNormSq (volumeAverageVec (openCubeSet R) (fun y =>
          matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
            (gluedGradientField hnu S.LPrime S.m S.m
                (fluxSlot nu S.LPrime P S.n e) omega y -
              gluedGradientField hnu S.LPrime S.n S.m
                (fluxSlot nu S.LPrime P S.n e) omega y)))) 2 P.toMeasure)
    (hPair : Integrable (fun omega : ShellSeq d =>
      volumeAverage (openCubeSet (originCube d (S.m : ℤ))) (fun y =>
        vecDot ((w omega).toH1Function.grad y)
          (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
            (gluedGradientField hnu S.LPrime S.m S.m
                (fluxSlot nu S.LPrime P S.n e) omega y -
              gluedGradientField hnu S.LPrime S.n S.m
                (fluxSlot nu S.LPrime P S.n e) omega y)))) P.toMeasure) :
    Integrable (fun omega : ShellSeq d =>
      ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
        ∑ R ∈ largeCubeSubcubes d S.n S.m,
          volumeAverage (openCubeSet R)
            (fun y => vecDot ((w omega).toH1Function.grad y -
                volumeAverageVec (openCubeSet R) ((w omega).toH1Function.grad))
              (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
                (gluedGradientField hnu S.LPrime S.m S.m
                    (fluxSlot nu S.LPrime P S.n e) omega y -
                  gluedGradientField hnu S.LPrime S.n S.m
                    (fluxSlot nu S.LPrime P S.n e) omega y)))) P.toMeasure := by
  have hcg := sideCondition_hcg_final hd hnu hnu1 hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder he
    w hw hMemFlux
  refine (hPair.sub hcg).congr (Filter.Eventually.of_forall fun omega => ?_)
  have hF : ∀ R ∈ largeCubeSubcubes d S.n S.m, ∀ i : Fin d,
      IntegrableOn (fun y => (matVecMul
        ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
        (gluedGradientField hnu S.LPrime S.m S.m
            (fluxSlot nu S.LPrime P S.n e) omega y -
          gluedGradientField hnu S.LPrime S.n S.m
            (fluxSlot nu S.LPrime P S.n e) omega y)) i) (cubeSet R) volume :=
    fun R hR i => sideCondition_hF hnu P S e omega R hR i
  have hgF : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      IntegrableOn (fun y => vecDot ((w omega).toH1Function.grad y)
        (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
          (gluedGradientField hnu S.LPrime S.m S.m
              (fluxSlot nu S.LPrime P S.n e) omega y -
            gluedGradientField hnu S.LPrime S.n S.m
              (fluxSlot nu S.LPrime P S.n e) omega y))) (cubeSet R) volume :=
    fun R hR => sideCondition_hgF hnu P S e w omega R hR
  have hsplit := volumeAverage_avsum_centered_splitting (n := S.n) (l := S.m)
    ((w omega).toH1Function.grad)
    (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
      (gluedGradientField hnu S.LPrime S.m S.m
          (fluxSlot nu S.LPrime P S.n e) omega y -
        gluedGradientField hnu S.LPrime S.n S.m
          (fluxSlot nu S.LPrime P S.n e) omega y)) hF hgF
  simp only [Pi.sub_apply]
  rw [hsplit]
  ring

/-! ## The `hbHalfInt` residue -/

/-- **The translated coarse block norm is in `L²(P)`** on every translated cube:
the `Γ₁` envelope `isBigO_gammaSigma_translatedBlockNorm_envelope` at the
exponent `2`, read through
`hasGammaMomentGrowthWith_of_isBigO_gammaSigma`.  This is
`memLp_two_translatedBlockNorm_core` of `RHSTerm3CgInputsB`, restated here
because that module and `RHSTerm3SourceGaps` both declare
`integral_mul_le_sqrt_mul_sqrt`, so no file may import both; the copy keeps the
`Γ₁`-envelope route in the present import graph. -/
theorem memLp_two_translatedBlockNorm_final [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (L : ℕ) (z : TriadicCube d) :
    MemLp (fun omega : ShellSeq d => translatedBlockNorm nu L omega z) 2 P.toMeasure := by
  have hK : (0 : ℝ) < envelopeUpperScalar d nu L :=
    SuperdiffusionCLT.Section2.Annealed.envelopeUpperScalar_pos hnu d L
  have hbig := isBigO_gammaSigma_translatedBlockNorm_envelope hnu hPrefix hJ2 hJ3 hJ4 L z
  have hgrowth := Homogenization.IndependentSums.hasGammaMomentGrowthWith_of_isBigO_gammaSigma
    (μ := P.toMeasure) (show (0 : ℝ) < 1 by norm_num) hK
    (measurable_translatedBlockNorm hnu L z).aemeasurable hbig
  obtain ⟨hint, -⟩ := hgrowth (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)
  have hint' : Integrable (fun omega : ShellSeq d =>
      translatedBlockNorm nu L omega z ^ (2 : ℕ)) P.toMeasure := by
    refine hint.congr (Filter.Eventually.of_forall fun omega => ?_)
    show |translatedBlockNorm nu L omega z| ^ ((2 : ℕ) : ℝ) =
      translatedBlockNorm nu L omega z ^ (2 : ℕ)
    have hznn : (0 : ℝ) ≤ translatedBlockNorm nu L omega z :=
      Homogenization.Book.Ch02.matrixOperatorNorm_nonneg _
    rw [Real.rpow_natCast, abs_of_nonneg hznn]
  exact (MeasureTheory.memLp_two_iff_integrable_sq
    (measurable_translatedBlockNorm hnu L z).aestronglyMeasurable).2 hint'

/-- **The half-weight carrier is measurable in the sample.**  It is the
quadratic form `v · (b v)` of the translated coarse block `b_L(z + cu_n)` at the
cube mean `v` of `∇w` (`vecNormSq_sqrt_matVecMul_eq_vecDot_matVecMul`): the
entries of `b_L(z + cu_n)` are measurable
(`measurable_translatedCoarseBlock_apply`) and the cube mean of `∇w` is
measurable on any cube contained in `cu_m`
(`measurable_volumeAverageVec_grad_component_final`), so the pairing is a finite
sum of products of measurable functions. -/
private theorem measurable_translatedBlockHalfWeight_final [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) {e : Vec d}
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega))
    {z' : TriadicCube d} (hsub : openCubeSet z' ⊆ openCubeSet (originCube d (S.m : ℤ)))
    (z : TriadicCube d) :
    Measurable (fun omega : ShellSeq d =>
      translatedBlockHalfWeight nu S.LPrime w omega z' z) := by
  have hv : ∀ i : Fin d, Measurable (fun omega : ShellSeq d =>
      volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad) i) :=
    fun i => measurable_volumeAverageVec_grad_component_final P S w hw hsub i
  have hEq : (fun omega : ShellSeq d =>
      translatedBlockHalfWeight nu S.LPrime w omega z' z) =
      fun omega : ShellSeq d =>
        vecDot (volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad))
          (matVecMul (translatedCoarseBlock nu S.LPrime omega z)
            (volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad))) := by
    funext omega
    exact SuperdiffusionCLT.Section2.Localization.vecNormSq_sqrt_matVecMul_eq_vecDot_matVecMul
      (posSemidef_translatedCoarseBlock hnu S.LPrime omega z) _
  rw [hEq]
  exact measurable_vecDot_matVecMul_self_final
    (fun i j => measurable_translatedCoarseBlock_apply hnu S.LPrime z i j) hv

/-- **The half-weight carrier `_hbHalfInt` of the final Term 3 reduction**, on
every triadic sub-cube of `cu_m` at any scale -- i.e. for
`z' ∈ largeCubeSubcubes d k S.m`, which as `k` ranges is exactly the triadic
cubes contained in `cu_m` -- and every `z`.  Every carrier vanishes: the
per-sub-cube family `hMemGrad` by `gradFour_finite_of_regbounds`, and the coarse
block norm by `memLp_two_translatedBlockNorm_final`.  The operator-norm bridge
`translatedBlockHalfWeight_le` dominates the carrier by
`⍍_{z'}|∇w|² · |b_{L'}(z + cu_n)|`, the product of two `L²(P)` functions. -/
theorem sideCondition_hbHalfInt_final [NeZero d] (hd : 2 ≤ d) {nu : ℝ} (hnu : 0 < nu)
    (hnu1 : nu ≤ 1) {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ1V2 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (S : ScaleSelection) (hSorder : ScalesOrdering S)
    {e : Vec d} (he : vecNormSq e = 1)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega))
    {k : ℕ} (z' : TriadicCube d) (hz' : z' ∈ largeCubeSubcubes d k S.m) (z : TriadicCube d) :
    Integrable (fun omega : ShellSeq d =>
      translatedBlockHalfWeight nu S.LPrime w omega z' z) P.toMeasure := by
  classical
  have hfin := gradFour_finite_of_regbounds hd hnu hnu1 hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder he w hw
  have hsq := memLp_vecNormSq_volumeAverageVec_grad_of_fourthMoment P S w hw hfin z' hz'
  have hsub : openCubeSet z' ⊆ openCubeSet (originCube d (S.m : ℤ)) := by
    rw [largeCubeSubcubes_eq_descendantsAtDepth] at hz'
    exact openCubeSet_subset_of_mem_descendantsAtDepth hz'
  have hmeas := measurable_translatedBlockHalfWeight_final hnu P S w hw hsub z
  have hprod : Integrable (fun omega : ShellSeq d =>
      vecNormSq (volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad)) *
        translatedBlockNorm nu S.LPrime omega z) P.toMeasure :=
    hsq.integrable_mul (memLp_two_translatedBlockNorm_final hnu hPrefix hJ2 hJ3 hJ4 S.LPrime z)
  refine Integrable.mono' hprod hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun omega => ?_)
  have hnn : 0 ≤ translatedBlockHalfWeight nu S.LPrime w omega z' z :=
    Homogenization.vecNormSq_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact translatedBlockHalfWeight_le hnu S.LPrime w omega z' z

end

end SuperdiffusionCLT.Section3.Terms
