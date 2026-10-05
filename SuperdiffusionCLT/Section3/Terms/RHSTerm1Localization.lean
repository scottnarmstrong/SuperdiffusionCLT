/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm1InputsH
public import SuperdiffusionCLT.Section2.CoarseGraining.SkewShiftCutoff

/-!
# The quenched localization step of Step 1 of `l.RHS.term1`

The proof of `l.RHS.term1` in the paper estimates the cube-wise
difference of the two maximizer gradients

`‖∇u_{n,z'} − ∇ũ_{n,z'}‖²_{L̲²(z'+cu_n)} ≤ C ν^{-3} 3^n ‖∇(k_{L'}−k_ℓ)‖_{L^∞(z'+cu_n)} shom_{L',*}(cu_n)`

(`e.localization.minimizers.applied`).  This file proves that display in its
quenched shape, from the third clause of the conclusion of
`Frozen.Section2.cutoff_localization` (`e.localization.minimizers`) carried
verbatim as the explicit hypothesis `hLocMin`, the constant-skew commutation
`e.commute.k0`, and the translation transport of the Chapter 2 response
maximizer.

## The three mismatches the print's sentence hides, and how they are resolved

1. **The coefficient of `cutoff_localization`.** It compares the maximizers of
   `a_{L'} − (k_{L'}−k_ℓ)_U` and of `a_ℓ`, while the field `∇u_n` of
   `e.u.k.def` is built from the maximizer of `a_{L'}` itself.  The print
   removes the gap in the first display of Step 1 by
   `e.commute.k0`: a constant anti-symmetric shift moves the response
   functional by the sheared load `q ↦ q + k₀p`, and the pure-flux load has
   `p = 0`, so at `(0, F)` neither `J` nor the maximizing property moves and
   the maximizer is literally the same function.  `(k_{L'}−k_ℓ)_U` is
   anti-symmetric because every shell is (`finiteShellIncrement_skew`), so
   `Section2.CoarseGraining.SkewShift` applies:
   `shiftedCubeSolution` is the `a_{L'}`-maximizer read as a maximizer of the
   shifted field, with the same gradient.
2. **The maximizing hypotheses.** The statement quantifies over
   `Homogenization.AHarmonicFunction` maximizers of `scalarResponseIntegrand`
   and asks for the two maximizing properties literally; they are supplied by
   `isResponseMaximizer_shiftedCubeSolution` and by the `isMaximizer` field of
   `GluedField.cubeMaximizer`, the public Chapter 2 predicate being
   `rfl`-equal to the raw one.
3. **The translate.** The domain of `cutoff_localization` must sit inside the
   **centred** cube `cu_n`, so it applies on `cu_n` and the sub-cubes `z + cu_n`
   of the family are reached by the translation transport of
   `RHSTerm1InputsG`, in the difference form
   `volumeAverage_vecNormSq_sub_cubeMaximizerGradient_translate`.

## Main results

* `shiftedCubeCoeffOn`, `shiftedCubeSolution`,
  `isResponseMaximizer_shiftedCubeSolution`, `responseJ_shiftedCubeCoeffOn`:
  the constant-skew removal of mismatch 1 and 2.
* `anchorDerivSup`, `anchorDerivSup_eq`: the `L^∞(cu_n)` window of
  `cutoff_localization` in its literal shape.
* `cubeLinftyTop_facts`,
  `ofReal_anchorDerivSup_le_shellDerivCubeLinftyENorm`: that window, a
  pointwise supremum over the open cube, is at most the
  essential-supremum carrier `RHSTerm1Inputs.shellDerivCubeLinftyENorm` with
  which the annealed moment in the proof is written.
* `localization_minimizers_originCube`: the clause of `cutoff_localization` read on `cu_n` for
  the two cube maximizers of `a_{L'}` and `a_ℓ`, with the two response values
  eliminated by the quenched crude ellipticity bound, in the printed shape
  `≤ C ν^{-3} 3^n ‖∇(k_{L'}−k_ℓ)‖_{L^∞(cu_n)} |F|²`.
* `volumeAverage_vecNormSq_sub_cubeMaximizerGradient_translate`: the
  difference form of the covariance of `RHSTerm1InputsG`.
* `localization_minimizers_gluedSubcube`: `e.localization.minimizers.applied`
  for the glued fields of `e.u.k.def` on a sub-cube of the family, with the
  `L^∞` window evaluated at the translated shell sequence.

## References

The paper: `e.localization.minimizers`, `e.localization.minimizers.applied`, and
the proof of `l.RHS.term1`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.CoarseGraining
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section2.Estimates.Stream
open Homogenization
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The constant anti-symmetric shift `(k_{L'} − k_ℓ)_U` -/

/-- The cube average of the finite shell increment is anti-symmetric: every
shell is (`finiteShellIncrement_skew`), and `matTranspose_volumeAverageMat`
transports the entrywise identity through the average. -/
theorem matTranspose_neg_volumeAverageMat_finiteShellIncrement
    (U : Set (Vec d)) (omega : ShellSeq d) (a b : ℕ) :
    matTranspose (-volumeAverageMat U (fun y => finiteShellIncrement omega a b y)) =
      -(-volumeAverageMat U (fun y => finiteShellIncrement omega a b y)) := by
  have hentry : ∀ (x : Vec d) (i k : Fin d),
      finiteShellIncrement omega a b x i k = -finiteShellIncrement omega a b x k i := by
    intro x i k
    have h := congrFun (congrFun (finiteShellIncrement_skew omega a b x) k) i
    simpa only [Matrix.transpose_apply, Matrix.neg_apply] using h
  have h := matTranspose_volumeAverageMat U
    (fun y => finiteShellIncrement omega a b y) hentry
  have hneg : matTranspose (-volumeAverageMat U
      (fun y => finiteShellIncrement omega a b y)) =
      -matTranspose (volumeAverageMat U (fun y => finiteShellIncrement omega a b y)) := by
    simp only [matTranspose, Matrix.transpose_neg]
  rw [hneg, h, neg_neg]

variable {nu : ℝ}

/-- **The coefficient of the anchor's clause on a triadic cube**: the cutoff
`a_{L'}` shifted by the constant anti-symmetric matrix `−(k_{L'}−k_ℓ)_{z+cu_k}`,
as a Chapter 2 coefficient object. -/
def shiftedCubeCoeffOn (hnu : 0 < nu) (omega : ShellSeq d) (LPrime ell : ℕ)
    (Q : TriadicCube d) : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q) :=
  addConstSkewCoeffOn (cubeCutoffCoeffOn hnu omega LPrime Q)
    (matTranspose_neg_volumeAverageMat_finiteShellIncrement
      ((Book.Ch02.cubeDomain Q : Set (Vec d))) omega ell LPrime)

/-! ## The constant-skew removal, `e.commute.k0` at the pure-flux load -/

/-- `k₀ · 0 = 0`: the pure-flux load `p = 0` makes the sheared load of
`e.commute.k0` the load itself. -/
private theorem matVecMul_zero_right (K : Mat d) : matVecMul K (0 : Vec d) = 0 := by
  funext i
  exact vecDot_zero_right (fun j => K i j)

/-- **The `a_{L'}`-maximizer `u_{k,z}` of `e.u.k.y.def`, read as a maximizer of
the anchor's shifted coefficient.**  A constant anti-symmetric shift does not
move the `a`-harmonic class (`isAHarmonicGradient_add_const_skew`), so this is
the same `H¹` function. -/
def shiftedCubeSolution (hnu : 0 < nu) (omega : ShellSeq d) (LPrime ell : ℕ)
    (F : Vec d) (Q : TriadicCube d) :
    Book.Ch02.Solution (Book.Ch02.cubeDomain Q)
      (shiftedCubeCoeffOn hnu omega LPrime ell Q) :=
  skewShiftSolution
    (matTranspose_neg_volumeAverageMat_finiteShellIncrement
      ((Book.Ch02.cubeDomain Q : Set (Vec d))) omega ell LPrime)
    (fun _ => rfl) (cubeMaximizer hnu omega LPrime F Q).toSolution

/-- **The maximizing property survives the constant-skew shift.**  At the
pure-flux load `(0, F)` the sheared load `q + k₀p` of `e.commute.k0` is `q`
itself, so the two response values agree term by term. -/
theorem isResponseMaximizer_shiftedCubeSolution (hnu : 0 < nu)
    (omega : ShellSeq d) (LPrime ell : ℕ) (F : Vec d) (Q : TriadicCube d) :
    Book.Ch02.IsResponseMaximizer (Book.Ch02.cubeDomain Q)
      (shiftedCubeCoeffOn hnu omega LPrime ell Q) 0 F
      (shiftedCubeSolution hnu omega LPrime ell F Q) := by
  set k0 : Mat d := -volumeAverageMat ((Book.Ch02.cubeDomain Q : Set (Vec d)))
    (fun y => finiteShellIncrement omega ell LPrime y) with hk0def
  have hk0 : matTranspose k0 = -k0 :=
    matTranspose_neg_volumeAverageMat_finiteShellIncrement
      ((Book.Ch02.cubeDomain Q : Set (Vec d))) omega ell LPrime
  have hb : ∀ x : Vec d,
      (shiftedCubeCoeffOn hnu omega LPrime ell Q).toCoeffField x =
        (cubeCutoffCoeffOn hnu omega LPrime Q).toCoeffField x + k0 := fun _ => rfl
  have hshear : F + matVecMul k0 (0 : Vec d) = F := by
    rw [matVecMul_zero_right, add_zero]
  intro w
  have hw := responseValue_add_const_skew hk0 hb 0 F w
    (skewShiftSolutionSymm hk0 hb w) rfl
  have hu := responseValue_add_const_skew hk0 hb 0 F
    (shiftedCubeSolution hnu omega LPrime ell F Q)
    (cubeMaximizer hnu omega LPrime F Q).toSolution rfl
  rw [hshear] at hw hu
  rw [hw, hu]
  exact (cubeMaximizer hnu omega LPrime F Q).isMaximizer _

/-- **`e.commute.k0` for the response functional at the pure-flux load**:
`J(z+cu_k, 0, F; a_{L'} − (k_{L'}−k_ℓ)_{z+cu_k}) = J(z+cu_k, 0, F; a_{L'})`,
the first display of Step 1 of `l.RHS.term1`. -/
theorem responseJ_shiftedCubeCoeffOn (hnu : 0 < nu) (omega : ShellSeq d)
    (LPrime ell : ℕ) (F : Vec d) (Q : TriadicCube d) :
    Book.Ch02.responseJ (Book.Ch02.cubeDomain Q)
        (shiftedCubeCoeffOn hnu omega LPrime ell Q) 0 F =
      Book.Ch02.responseJ (Book.Ch02.cubeDomain Q)
        (cubeCutoffCoeffOn hnu omega LPrime Q) 0 F := by
  set k0 : Mat d := -volumeAverageMat ((Book.Ch02.cubeDomain Q : Set (Vec d)))
    (fun y => finiteShellIncrement omega ell LPrime y) with hk0def
  have hk0 : matTranspose k0 = -k0 :=
    matTranspose_neg_volumeAverageMat_finiteShellIncrement
      ((Book.Ch02.cubeDomain Q : Set (Vec d))) omega ell LPrime
  have hb : ∀ x : Vec d,
      (shiftedCubeCoeffOn hnu omega LPrime ell Q).toCoeffField x =
        (cubeCutoffCoeffOn hnu omega LPrime Q).toCoeffField x + k0 := fun _ => rfl
  have h := responseJ_add_const_skew hk0 hb 0 F
  rwa [matVecMul_zero_right, add_zero] at h

/-! ## The anchor's `L^∞` window -/

/-- **`‖∇(k_b − k_a)‖_{L^∞(cu_n)}`** in the exact pointwise form carried by the
right-hand side of `Frozen.Section2.cutoff_localization`
(`e.nabla.kmn.Linfty`): the supremum over the open cube `cu_n` of
the exact induced norm of the derivative of the finite shell increment, zero
being adjoined to the defining range through the `Option` index, as in
`Section2.Carriers.shellDerivLinftyNorm`. -/
def anchorDerivSup (a b n : ℕ) (omega : ShellSeq d) : ℝ :=
  sSup (Set.range fun o :
      Option {x : Vec d // x ∈ openCubeSet (originCube d (n : ℤ))} =>
    match o with
    | none => 0
    | some x => ShellField.matrixDerivativeNorm
        (∑ k ∈ Finset.Ioc a b, ShellField.deriv (omega k) x.1))

/-- **The carrier is the expression of `cutoff_localization`, literally.**  This
equation exhibits `anchorDerivSup` as the right-hand-side window of
`Frozen.Section2.cutoff_localization`, so that the hypotheses below, which are
stated with the carrier, are its clause verbatim. -/
theorem anchorDerivSup_eq (a b n : ℕ) (omega : ShellSeq d) :
    anchorDerivSup a b n omega =
      sSup (Set.range fun o :
          Option {x : Vec d // x ∈ openCubeSet (originCube d (n : ℤ))} =>
        match o with
        | none => 0
        | some x => ShellField.matrixDerivativeNorm
            (∑ k ∈ Finset.Ioc a b, ShellField.deriv (omega k) x.1)) :=
  rfl

/-- The window is nonnegative: zero belongs to the defining range, and the
unbounded branch returns the junk value `0`. -/
theorem anchorDerivSup_nonneg (a b n : ℕ) (omega : ShellSeq d) :
    0 ≤ anchorDerivSup a b n omega := by
  classical
  set g : Option {x : Vec d // x ∈ openCubeSet (originCube d (n : ℤ))} → ℝ :=
    fun o => match o with
      | none => 0
      | some x => ShellField.matrixDerivativeNorm
          (∑ k ∈ Finset.Ioc a b, ShellField.deriv (omega k) x.1) with hg
  have hmem : (0 : ℝ) ∈ Set.range g := ⟨none, rfl⟩
  by_cases hb : BddAbove (Set.range g)
  · exact le_csSup hb hmem
  · rw [anchorDerivSup, show
      (sSup (Set.range fun o :
          Option {x : Vec d // x ∈ openCubeSet (originCube d (n : ℤ))} =>
        match o with
        | none => 0
        | some x => ShellField.matrixDerivativeNorm
            (∑ k ∈ Finset.Ioc a b, ShellField.deriv (omega k) x.1))) =
        sSup (Set.range g) from rfl, Real.sSup_of_not_bddAbove hb]

/-! ## The pointwise window is the `L^∞` carrier -/

/-- **A continuous nonnegative density is pointwise dominated on the open cube
by its normalized `L^∞` carrier, which is finite.**

The two readings of the `L^∞(cu_n)` norm of `e.nabla.kmn.Linfty` are therefore
comparable in the direction Step 1 needs: the right-hand side of
`cutoff_localization` carries the pointwise supremum over the open cube, and
`RHSTerm1Inputs.shellDerivCubeLinftyENorm` carries the essential supremum
against the normalized cube measure.  Finiteness is continuity on the closed
ball containing the cube; the pointwise domination is again continuity, a
strict violation persisting on a nonempty open subset of the cube, which has
positive volume. -/
theorem cubeLinftyTop_facts {Q : TriadicCube d} {f : Vec d → ℝ}
    (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x) :
    Section2.Norms.cubeLpENorm Q ∞ f ≠ ⊤ ∧
      ∀ x ∈ openCubeSet Q, f x ≤ (Section2.Norms.cubeLpENorm Q ∞ f).toReal := by
  classical
  set E : ℝ≥0∞ := MeasureTheory.eLpNorm f ∞
    (MeasureTheory.volume.restrict (openCubeSet Q)) with hE
  have hvolpos : (0 : ℝ) < cubeVolume Q := cubeVolume_pos Q
  have hne : ENNReal.ofReal (cubeVolume Q)⁻¹ ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact inv_pos.2 hvolpos
  have hfm : MeasureTheory.AEStronglyMeasurable f
      (MeasureTheory.volume.restrict (openCubeSet Q)) := hf.aestronglyMeasurable
  have hfm2 : MeasureTheory.AEStronglyMeasurable f (normalizedCubeMeasure Q) := by
    rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet Q]
    exact hfm.smul_measure _
  have hcarrier : Section2.Norms.cubeLpENorm Q ∞ f = E := by
    rw [Section2.Norms.cubeLpENorm, MeasureTheory.eLpNorm_exponent_top hfm2,
      normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet Q, hE,
      MeasureTheory.eLpNorm_exponent_top hfm,
      MeasureTheory.eLpNormEssSup_eq_essSup_enorm,
      MeasureTheory.eLpNormEssSup_eq_essSup_enorm,
      essSup_ennreal_smul_measure hne]
  have hUopen : IsOpen (openCubeSet Q) := by
    rw [← ball_cubeCenter_eq_openCubeSet]
    exact Metric.isOpen_ball
  have hUmeas : MeasurableSet (openCubeSet Q) := hUopen.measurableSet
  have hKcompact : IsCompact (Metric.closedBall (cubeCenter Q) (cubeRadius Q)) :=
    isCompact_closedBall (cubeCenter Q) (cubeRadius Q)
  obtain ⟨C, hC⟩ := hKcompact.exists_bound_of_continuousOn hf.continuousOn
  have hbound : ∀ x ∈ openCubeSet Q, f x ≤ max 0 C := by
    intro x hx
    have hxK : x ∈ Metric.closedBall (cubeCenter Q) (cubeRadius Q) := by
      refine Metric.ball_subset_closedBall ?_
      rw [ball_cubeCenter_eq_openCubeSet]
      exact hx
    have hfxC : f x ≤ C := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hf0 x)] using hC x hxK
    exact hfxC.trans (le_max_right 0 C)
  have haeS : ∀ᵐ x ∂(MeasureTheory.volume.restrict (openCubeSet Q)),
      ‖f x‖ ≤ max 0 C := by
    filter_upwards [MeasureTheory.ae_restrict_mem hUmeas] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 x)]
    exact hbound x hx
  have hEle : E ≤ ENNReal.ofReal (max 0 C) := by
    rw [hE, MeasureTheory.eLpNorm_exponent_top hfm]
    exact MeasureTheory.eLpNormEssSup_le_of_ae_bound haeS
  have hEtop : E ≠ ⊤ := ne_of_lt (hEle.trans_lt ENNReal.ofReal_lt_top)
  refine ⟨by rw [hcarrier]; exact hEtop, ?_⟩
  intro x hx
  rw [hcarrier]
  by_contra hlt
  have hxlt : E.toReal < f x := lt_of_not_ge hlt
  have hVopen : IsOpen (openCubeSet Q ∩ f ⁻¹' Set.Ioi E.toReal) :=
    hUopen.inter (isOpen_Ioi.preimage hf)
  have hxV : x ∈ openCubeSet Q ∩ f ⁻¹' Set.Ioi E.toReal := ⟨hx, hxlt⟩
  have hVpos : 0 < MeasureTheory.volume
      (openCubeSet Q ∩ f ⁻¹' Set.Ioi E.toReal) :=
    hVopen.measure_pos MeasureTheory.volume ⟨x, hxV⟩
  have hVrestrict : 0 < (MeasureTheory.volume.restrict (openCubeSet Q))
      (openCubeSet Q ∩ f ⁻¹' Set.Ioi E.toReal) := by
    rw [MeasureTheory.Measure.restrict_apply hVopen.measurableSet,
      Set.inter_eq_left.mpr Set.inter_subset_left]
    exact hVpos
  have haeE : ∀ᵐ y ∂(MeasureTheory.volume.restrict (openCubeSet Q)),
      ‖f y‖ₑ ≤ E := by
    rw [hE, MeasureTheory.eLpNorm_exponent_top hfm]
    exact MeasureTheory.enorm_ae_le_eLpNormEssSup f _
  have hnot : ∀ᵐ y ∂(MeasureTheory.volume.restrict (openCubeSet Q)),
      y ∉ openCubeSet Q ∩ f ⁻¹' Set.Ioi E.toReal := by
    filter_upwards [haeE] with y hy
    intro hyV
    have hylt : E.toReal < f y := hyV.2
    have hbad : E < ‖f y‖ₑ := by
      rw [← ENNReal.ofReal_toReal hEtop, Real.enorm_eq_ofReal (hf0 y)]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).2 hylt
    exact (not_lt_of_ge hy) hbad
  have hzero : (MeasureTheory.volume.restrict (openCubeSet Q))
      (openCubeSet Q ∩ f ⁻¹' Set.Ioi E.toReal) = 0 := by
    simpa only [not_not, Set.ofPred_mem_eq] using MeasureTheory.ae_iff.mp hnot
  exact (ne_of_gt hVrestrict) hzero

/-- **`hWindow` of Step 1**: the pointwise `L^∞(cu_n)` window of
`e.nabla.kmn.Linfty` in `cutoff_localization` is at most the essential-supremum
carrier `RHSTerm1Inputs.shellDerivCubeLinftyENorm`, with which the annealed
moment in the proof is written. -/
theorem ofReal_anchorDerivSup_le_shellDerivCubeLinftyENorm (a b n : ℕ)
    (omega : ShellSeq d) :
    ENNReal.ofReal (anchorDerivSup a b n omega) ≤
      shellDerivCubeLinftyENorm a b n omega := by
  classical
  have hcont : Continuous (fun x : Vec d => ShellField.matrixDerivativeNorm
      (∑ k ∈ Finset.Ioc a b, ShellField.deriv (omega k) x)) :=
    ShellField.matrixDerivativeNorm_continuous.comp
      (continuous_finsetSum _ fun k _ => (ShellField.deriv (omega k)).continuous)
  have hnn : ∀ x : Vec d, 0 ≤ ShellField.matrixDerivativeNorm
      (∑ k ∈ Finset.Ioc a b, ShellField.deriv (omega k) x) :=
    fun x => ShellField.matrixDerivativeNorm_nonneg _
  obtain ⟨hne, hdom⟩ := cubeLinftyTop_facts (Q := originCube d (n : ℤ)) hcont hnn
  have hle : anchorDerivSup a b n omega ≤
      (shellDerivCubeLinftyENorm a b n omega).toReal := by
    rw [anchorDerivSup]
    refine csSup_le (Set.range_nonempty _) ?_
    rintro r ⟨o, rfl⟩
    cases o with
    | none => exact ENNReal.toReal_nonneg
    | some x => exact hdom x.1 x.2
  calc ENNReal.ofReal (anchorDerivSup a b n omega)
      ≤ ENNReal.ofReal (shellDerivCubeLinftyENorm a b n omega).toReal :=
        ENNReal.ofReal_le_ofReal hle
    _ = shellDerivCubeLinftyENorm a b n omega := ENNReal.ofReal_toReal hne

/-! ## The response values of the two cube problems -/

/-- **The energy factor of `e.localization.minimizers`**: at the
pure-flux load both response values are at most `(1/2) ν^{-1}|F|²`, by the
quenched crude ellipticity bound `s_{L,*}^{-1}(z + cu_k) ≤ ν^{-1} Id`. -/
theorem responseJ_cubeCutoffCoeffOn_le (hnu : 0 < nu) (omega : ShellSeq d)
    (L : ℕ) (F : Vec d) (Q : TriadicCube d) :
    Book.Ch02.responseJ (Book.Ch02.cubeDomain Q)
        (cubeCutoffCoeffOn hnu omega L Q) 0 F ≤ nu⁻¹ * vecNormSq F / 2 := by
  have hcrude : MatLoewnerLE (Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain Q)
      (cubeCutoffCoeffOn hnu omega L Q)) (nu⁻¹ • (1 : Mat d)) :=
    matLoewnerLE_sigmaStarInvCoarse_cutoffCube hnu omega L Q
  have hbound := two_mul_inv_mul_responseJ_le (Book.Ch02.cubeDomain Q)
    (cubeCutoffCoeffOn hnu omega L Q) F hnu hcrude
  have hnuinv : 0 < nu⁻¹ := inv_pos.2 hnu
  have hhalf : 0 < nu / 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hbound (le_of_lt hhalf)
  have hL : nu / 2 * (2 * nu⁻¹ * Book.Ch02.responseJ (Book.Ch02.cubeDomain Q)
      (cubeCutoffCoeffOn hnu omega L Q) 0 F) =
      Book.Ch02.responseJ (Book.Ch02.cubeDomain Q)
        (cubeCutoffCoeffOn hnu omega L Q) 0 F := by
    field_simp
  have hR : nu / 2 * (nu⁻¹ * nu⁻¹ * vecNormSq F) = nu⁻¹ * vecNormSq F / 2 := by
    field_simp
  rwa [hL, hR] at hmul

/-! ## `e.localization.minimizers` on the centred cube -/

/-- **The clause `e.localization.minimizers` of `cutoff_localization` read on the
centred cube `cu_n`, for the two cube maximizers of `e.u.k.y.def`.**

`hLocMin` is the third clause of the conclusion of
`Frozen.Section2.cutoff_localization` (`e.localization.minimizers`), copied
verbatim at the scale triple `(m, n, L) = (ell, n, LPrime)`,
with the statement's own domain binder.

The two maximizing hypotheses that `cutoff_localization` asks for are supplied here:
`isResponseMaximizer_shiftedCubeSolution` for the shifted coefficient and the
`isMaximizer` field of `GluedField.cubeMaximizer` for `a_ℓ`.  The two response
values on the right are eliminated by `responseJ_shiftedCubeCoeffOn`
(`e.commute.k0`) and `responseJ_cubeCutoffCoeffOn_le`, which is the print's
"both relevant energies are bounded by `ν^{-1}|Q|²`". -/
theorem localization_minimizers_originCube (hnu : 0 < nu) (omega : ShellSeq d)
    {CL : ℝ} (hCL : 0 ≤ CL) {n ell LPrime : ℕ} (F : Vec d)
    (hLocMin : ∀ U : Book.Ch02.Domain d,
        (U : Set (Vec d)) ⊆ openCubeSet (originCube d (n : ℤ)) →
        ∀ (omega' : ShellSeq d) (p q : Vec d)
          (u : AHarmonicFunction
            (fun x : Vec d =>
              (coefficientCutoff nu omega' LPrime).toCoeffField x -
                volumeAverageMat (U : Set (Vec d))
                  (fun y => finiteShellIncrement omega' ell LPrime y))
            (U : Set (Vec d)))
          (v : AHarmonicFunction
            (coefficientCutoff nu omega' ell).toCoeffField (U : Set (Vec d))),
          (∀ w : AHarmonicFunction
              (fun x : Vec d =>
                (coefficientCutoff nu omega' LPrime).toCoeffField x -
                  volumeAverageMat (U : Set (Vec d))
                    (fun y => finiteShellIncrement omega' ell LPrime y))
              (U : Set (Vec d)),
              volumeAverage (U : Set (Vec d))
                  (scalarResponseIntegrand (U : Set (Vec d))
                    (fun x : Vec d =>
                      (coefficientCutoff nu omega' LPrime).toCoeffField x -
                        volumeAverageMat (U : Set (Vec d))
                          (fun y => finiteShellIncrement omega' ell LPrime y))
                    p q w) ≤
                volumeAverage (U : Set (Vec d))
                  (scalarResponseIntegrand (U : Set (Vec d))
                    (fun x : Vec d =>
                      (coefficientCutoff nu omega' LPrime).toCoeffField x -
                        volumeAverageMat (U : Set (Vec d))
                          (fun y => finiteShellIncrement omega' ell LPrime y))
                    p q u)) →
          (∀ w : AHarmonicFunction
              (coefficientCutoff nu omega' ell).toCoeffField (U : Set (Vec d)),
              volumeAverage (U : Set (Vec d))
                  (scalarResponseIntegrand (U : Set (Vec d))
                    (coefficientCutoff nu omega' ell).toCoeffField p q w) ≤
                volumeAverage (U : Set (Vec d))
                  (scalarResponseIntegrand (U : Set (Vec d))
                    (coefficientCutoff nu omega' ell).toCoeffField p q v)) →
            volumeAverage (U : Set (Vec d))
                (fun x => vecNormSq (u.toH1.grad x - v.toH1.grad x)) ≤
              CL * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ n *
                  anchorDerivSup ell LPrime n omega' *
                (ResponseJ (U : Set (Vec d)) p q
                    (fun x : Vec d =>
                      (coefficientCutoff nu omega' LPrime).toCoeffField x -
                        volumeAverageMat (U : Set (Vec d))
                          (fun y => finiteShellIncrement omega' ell LPrime y)) +
                  ResponseJ (U : Set (Vec d)) p q
                    (coefficientCutoff nu omega' ell).toCoeffField +
                  2 * vecDot p q)) :
    volumeAverage (openCubeSet (originCube d (n : ℤ)))
        (fun x => vecNormSq
          (cubeMaximizerGradient hnu omega LPrime F (originCube d (n : ℤ)) x -
            cubeMaximizerGradient hnu omega ell F (originCube d (n : ℤ)) x)) ≤
      CL * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ n * anchorDerivSup ell LPrime n omega *
        (nu⁻¹ * vecNormSq F) := by
  have h : volumeAverage (openCubeSet (originCube d (n : ℤ)))
        (fun x => vecNormSq
          (cubeMaximizerGradient hnu omega LPrime F (originCube d (n : ℤ)) x -
            cubeMaximizerGradient hnu omega ell F (originCube d (n : ℤ)) x)) ≤
      CL * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ n * anchorDerivSup ell LPrime n omega *
        (ResponseJ (openCubeSet (originCube d (n : ℤ))) 0 F
            (fun x : Vec d => (coefficientCutoff nu omega LPrime).toCoeffField x -
              volumeAverageMat (openCubeSet (originCube d (n : ℤ)))
                (fun y => finiteShellIncrement omega ell LPrime y)) +
          ResponseJ (openCubeSet (originCube d (n : ℤ))) 0 F
            (coefficientCutoff nu omega ell).toCoeffField +
          2 * vecDot (0 : Vec d) F) :=
    hLocMin (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
      (Book.Ch02.cubeDomain_coe _).subset omega 0 F
      (shiftedCubeSolution hnu omega LPrime ell F (originCube d (n : ℤ)))
      (cubeMaximizer hnu omega ell F (originCube d (n : ℤ))).toSolution
      (isResponseMaximizer_shiftedCubeSolution hnu omega LPrime ell F
        (originCube d (n : ℤ)))
      (cubeMaximizer hnu omega ell F (originCube d (n : ℤ))).isMaximizer
  refine le_trans h ?_
  have hpre : 0 ≤ CL * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ n *
      anchorDerivSup ell LPrime n omega := by
    have h2 : (0 : ℝ) ≤ nu ^ (-(2 : ℝ)) := Real.rpow_nonneg (le_of_lt hnu) _
    have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ n := by positivity
    have h4 := anchorDerivSup_nonneg ell LPrime n omega
    exact mul_nonneg (mul_nonneg (mul_nonneg hCL h2) h3) h4
  refine mul_le_mul_of_nonneg_left ?_ hpre
  have hJ1 : ResponseJ (openCubeSet (originCube d (n : ℤ))) 0 F
      (fun x : Vec d => (coefficientCutoff nu omega LPrime).toCoeffField x -
        volumeAverageMat (openCubeSet (originCube d (n : ℤ)))
          (fun y => finiteShellIncrement omega ell LPrime y)) ≤
      nu⁻¹ * vecNormSq F / 2 := by
    have hEq : ResponseJ (openCubeSet (originCube d (n : ℤ))) 0 F
        (fun x : Vec d => (coefficientCutoff nu omega LPrime).toCoeffField x -
          volumeAverageMat (openCubeSet (originCube d (n : ℤ)))
            (fun y => finiteShellIncrement omega ell LPrime y)) =
        Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
          (cubeCutoffCoeffOn hnu omega LPrime (originCube d (n : ℤ))) 0 F :=
      responseJ_shiftedCubeCoeffOn hnu omega LPrime ell F (originCube d (n : ℤ))
    rw [hEq]
    exact responseJ_cubeCutoffCoeffOn_le hnu omega LPrime F (originCube d (n : ℤ))
  have hJ2 : ResponseJ (openCubeSet (originCube d (n : ℤ))) 0 F
      (coefficientCutoff nu omega ell).toCoeffField ≤ nu⁻¹ * vecNormSq F / 2 :=
    responseJ_cubeCutoffCoeffOn_le hnu omega ell F (originCube d (n : ℤ))
  have hzero : 2 * vecDot (0 : Vec d) F = 0 := by simp [vecDot]
  rw [hzero]
  linarith only [hJ1, hJ2]

/-! ## The difference form of the translation covariance -/

/-- The normalized cube integral is the cube average. -/
private theorem integralNCM (Q : TriadicCube d) (f : Vec d → ℝ) :
    ∫ x, f x ∂normalizedCubeMeasure Q = volumeAverage (openCubeSet Q) f := by
  rw [integral_normalizedCubeMeasure_eq, volumeAverage, volume_openCubeSet_toReal]

/-- Reading a scalar field on `Q` after the shift `x ↦ x − z` is reading it on
the centred cube of the same scale. -/
private theorem volumeAverageCompSubShift (Q : TriadicCube d) (g : Vec d → ℝ) :
    volumeAverage (openCubeSet Q) (fun x => g (x - triadicCubeShift Q)) =
      volumeAverage (openCubeSet (originCube d Q.scale)) g := by
  rw [← integralNCM, ← integralNCM]
  have hmp := measurePreserving_addRight_normalizedCubeMeasure_originCube Q
  have hemb : MeasurableEmbedding (fun x : Vec d => x + triadicCubeShift Q) :=
    (MeasurableEquiv.addRight (triadicCubeShift Q)).measurableEmbedding
  have h := hmp.integral_comp hemb (fun x : Vec d => g (x - triadicCubeShift Q))
  simpa only [add_sub_cancel_right] using h.symm

/-- **The cube maximizer of a translated cube is the translated cube maximizer,
almost everywhere.**  The two objects are produced by different choices, and
`Book.Ch02.sameGradientAE_of_isResponseMaximizer` identifies their gradients.
This is the pointwise half of
`RHSTerm1InputsG.vecCubeLpENorm_cubeMaximizerGradient_translate`. -/
theorem cubeMaximizerGradient_translate_ae (hnu : 0 < nu) (omega : ShellSeq d)
    (L : ℕ) (F : Vec d) (Q : TriadicCube d) :
    ∀ᵐ x ∂normalizedCubeMeasure Q,
      cubeMaximizerGradient hnu omega L F Q x =
        cubeMaximizerGradient hnu
          (ShellField.translateSequence (triadicCubeShift Q) omega) L F
          (originCube d Q.scale) (x - triadicCubeShift Q) := by
  have hmaxT := isResponseMaximizer_translatedCubeSolution hnu omega L Q 0 F
    (cubeMaximizer hnu (ShellField.translateSequence (triadicCubeShift Q) omega) L F
      (originCube d Q.scale)).toSolution
    (cubeMaximizer hnu (ShellField.translateSequence (triadicCubeShift Q) omega) L F
      (originCube d Q.scale)).isMaximizer
  have hsame := Book.Ch02.sameGradientAE_of_isResponseMaximizer
    (cubeMaximizer hnu omega L F Q).isMaximizer hmaxT
  rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
  refine MeasureTheory.Measure.ae_smul_measure ?_ _
  filter_upwards [hsame] with x hx
  rw [show cubeMaximizerGradient hnu omega L F Q x =
    (cubeMaximizer hnu omega L F Q).toSolution.toH1.grad x from rfl, hx]
  exact translatedCubeSolution_grad nu omega L Q _ x

/-- **The covariance of the localization display.**  The cube average of
`|∇u_{n,z} − ∇ũ_{n,z}|²` on the translated cube `z + cu_n` is the cube average
of the centred display for the translated shell sequence: this is the form in
which the translated version of `e.localization.minimizers` is used. -/
theorem volumeAverage_vecNormSq_sub_cubeMaximizerGradient_translate (hnu : 0 < nu)
    (omega : ShellSeq d) (LPrime ell : ℕ) (F : Vec d) (Q : TriadicCube d) :
    volumeAverage (openCubeSet Q)
        (fun x => vecNormSq (cubeMaximizerGradient hnu omega LPrime F Q x -
          cubeMaximizerGradient hnu omega ell F Q x)) =
      volumeAverage (openCubeSet (originCube d Q.scale))
        (fun y => vecNormSq
          (cubeMaximizerGradient hnu
              (ShellField.translateSequence (triadicCubeShift Q) omega) LPrime F
              (originCube d Q.scale) y -
            cubeMaximizerGradient hnu
              (ShellField.translateSequence (triadicCubeShift Q) omega) ell F
              (originCube d Q.scale) y)) := by
  have h1 := cubeMaximizerGradient_translate_ae hnu omega LPrime F Q
  have h2 := cubeMaximizerGradient_translate_ae hnu omega ell F Q
  have hcong : ∫ x, vecNormSq (cubeMaximizerGradient hnu omega LPrime F Q x -
        cubeMaximizerGradient hnu omega ell F Q x) ∂normalizedCubeMeasure Q =
      ∫ x, vecNormSq
        (cubeMaximizerGradient hnu
            (ShellField.translateSequence (triadicCubeShift Q) omega) LPrime F
            (originCube d Q.scale) (x - triadicCubeShift Q) -
          cubeMaximizerGradient hnu
            (ShellField.translateSequence (triadicCubeShift Q) omega) ell F
            (originCube d Q.scale) (x - triadicCubeShift Q))
        ∂normalizedCubeMeasure Q := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [h1, h2] with x hx1 hx2
    rw [hx1, hx2]
  rw [← integralNCM, hcong, integralNCM]
  exact volumeAverageCompSubShift Q (fun y => vecNormSq
    (cubeMaximizerGradient hnu
        (ShellField.translateSequence (triadicCubeShift Q) omega) LPrime F
        (originCube d Q.scale) y -
      cubeMaximizerGradient hnu
        (ShellField.translateSequence (triadicCubeShift Q) omega) ell F
        (originCube d Q.scale) y))

/-! ## `e.localization.minimizers.applied` for the glued fields -/

/-- **`e.localization.minimizers.applied`**, for the two glued fields of
`e.u.k.def` on one sub-cube `z + cu_n` of the family:

`⨍_{z+cu_n}|∇u_n − ∇ũ_n|² ≤ C ν^{-3} 3^n ‖∇(k_{L'}−k_ℓ)‖_{L^∞(cu_n)}(τ_z ω) |F|²`.

`hCentre` is the conclusion of `localization_minimizers_originCube` at every
shell sequence; the translate is reached by the covariance
`volumeAverage_vecNormSq_sub_cubeMaximizerGradient_translate`, and the `L^∞`
window is therefore evaluated at the translated sequence, which is where the
print's "and stationarity" enters. -/
theorem localization_minimizers_gluedSubcube (hnu : 0 < nu)
    {CL : ℝ} {n m ell LPrime : ℕ} (hnm : n ≤ m) (F : Vec d)
    (hCentre : ∀ omega' : ShellSeq d,
      volumeAverage (openCubeSet (originCube d (n : ℤ)))
          (fun x => vecNormSq
            (cubeMaximizerGradient hnu omega' LPrime F (originCube d (n : ℤ)) x -
              cubeMaximizerGradient hnu omega' ell F (originCube d (n : ℤ)) x)) ≤
        CL * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ n * anchorDerivSup ell LPrime n omega' *
          (nu⁻¹ * vecNormSq F))
    (omega : ShellSeq d) {Q : TriadicCube d}
    (hQ : Q ∈ largeCubeSubcubes d n m) :
    volumeAverage (openCubeSet Q)
        (fun x => vecNormSq (gluedGradientField hnu LPrime n m F omega x -
          gluedGradientField hnu ell n m F omega x)) ≤
      CL * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ n *
          anchorDerivSup ell LPrime n
            (ShellField.translateSequence (triadicCubeShift Q) omega) *
        (nu⁻¹ * vecNormSq F) := by
  have hscale : Q.scale = (n : ℤ) := scale_of_mem_largeCubeSubcubes hnm hQ
  have hglue : volumeAverage (openCubeSet Q)
        (fun x => vecNormSq (gluedGradientField hnu LPrime n m F omega x -
          gluedGradientField hnu ell n m F omega x)) =
      volumeAverage (openCubeSet Q)
        (fun x => vecNormSq (cubeMaximizerGradient hnu omega LPrime F Q x -
          cubeMaximizerGradient hnu omega ell F Q x)) := by
    refine congrArg
      (fun t : ℝ => (MeasureTheory.volume (openCubeSet Q)).toReal⁻¹ * t) ?_
    refine MeasureTheory.setIntegral_congr_fun (measurableSet_openCubeSet Q) ?_
    intro x hx
    show vecNormSq (gluedGradientField hnu LPrime n m F omega x -
        gluedGradientField hnu ell n m F omega x) = _
    rw [gluedGradientField_apply_of_mem_openCubeSet hnu LPrime n m F omega hQ hx,
      gluedGradientField_apply_of_mem_openCubeSet hnu ell n m F omega hQ hx]
  rw [hglue, volumeAverage_vecNormSq_sub_cubeMaximizerGradient_translate hnu
    omega LPrime ell F Q, hscale]
  exact hCentre (ShellField.translateSequence (triadicCubeShift Q) omega)

end

end SuperdiffusionCLT.Section3.Terms
