/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.MixingLoewnerSteps
public import SuperdiffusionCLT.Section2.Estimates.Stream.OriginConcentration
public import SuperdiffusionCLT.Section2.Localization.CutoffLoewnerClauses

/-!
# From entry-level concentration to the operator norm of Step E

The reduction of `hStepE` to the operator norm (in `MixingLoewnerSteps`) removes the
matrix-Loewner content of `hStepE` and leaves the scalar concentration of the operator norm
`|| D omega - shom^-1_{m,*}(cu_h) ||_op` of the descendant-average fluctuation.
The Step-E machinery of `MixingStepEnvelope` is entry-level: it concentrates the entries of the
descendant average (per variable envelope, stationarity centring, finset-average sublattice
concentration).

This module supplies the deterministic bookkeeping between the two:
the passage from entry-level `Gamma_sigma` concentration of the entries of a
matrix observable to the `Gamma_sigma` concentration of its operator norm.  It
is the union bound made explicit — `|M|_op <= sum_{i,j} |M_{i,j}|`
(`matrixOperatorNorm_le_sum_univ_abs_entry`), followed by the finite
family triangle inequality of the stretched-exponential calculus
(`isBigO_finset_sum_of_isBigO_gammaSigma`), at the cost of the dimensional
factor `gammaTriangleConst sigma * d^2` when every entry carries the same
amplitude.

## Main results

* `isBigO_gammaSigma_operatorNorm_of_entrywise`: the operator norm of a matrix
  observable is `O_{Gamma_sigma}` at the sum of the entry amplitudes times the
  universal triangle constant.
* `stepD_scalarGap_of_sandwich_moment`: the Step-D scalar cutoff gap from a
  deterministic relative Loewner bound and the first moment of the witness.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Annealed

open Homogenization MeasureTheory
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.CoarseGraining
open SuperdiffusionCLT.Section2.Localization
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section3.Terms

noncomputable section

variable {d : ℕ}

/-! ## The union bound from entries to the operator norm -/

/-- **The operator norm inherits entry-level `Gamma_sigma` concentration, with
an explicit dimensional factor.**  If every entry `(i,j)` of a matrix
observable `M` is `O_{Gamma_sigma}(a_{ij})`, then `||M||_op` is
`O_{Gamma_sigma}(gammaTriangleConst sigma * sum_{ij} a_{ij})`.  The proof is
the deterministic entry bound `||M||_op <= sum_{ij} |M_{ij}|`
(`matrixOperatorNorm_le_sum_univ_abs_entry`) closed under the proved finite
family triangle inequality (`isBigO_finset_sum_of_isBigO_gammaSigma`); when all
entry amplitudes coincide with `a`, the amplitude is the `d^2`-fold sum
`gammaTriangleConst sigma * (d^2 * a)`. -/
theorem isBigO_gammaSigma_operatorNorm_of_entrywise [NeZero d]
    {μ : Measure (ShellSeq d)} [IsFiniteMeasure μ] {σ : ℝ} (hσ : 0 < σ)
    (M : ShellSeq d → Homogenization.Mat d) (a : Fin d × Fin d → ℝ)
    (hA : ∀ p : Fin d × Fin d, 0 < a p)
    (hmeas : ∀ p : Fin d × Fin d, Measurable (fun ω : ShellSeq d ↦ M ω p.1 p.2))
    (h : ∀ p : Fin d × Fin d,
      IsBigO μ (gammaSigma σ) (fun ω : ShellSeq d ↦ M ω p.1 p.2)
      (a p)) :
    IsBigO μ (gammaSigma σ)
      (fun ω : ShellSeq d ↦ Homogenization.Book.Ch02.matrixOperatorNorm (M ω))
      (gammaTriangleConst σ * ∑ p : Fin d × Fin d, a p) := by
  have hX : ∀ p : Fin d × Fin d, p ∈ (Finset.univ : Finset (Fin d × Fin d)) →
      IsBigO μ (gammaSigma σ) (fun ω : ShellSeq d ↦ |M ω p.1 p.2|) (a p) := by
    intro p _
    simpa only [IsBigO, abs_abs] using h p
  have hXm : ∀ p : Fin d × Fin d, p ∈ (Finset.univ : Finset (Fin d × Fin d)) →
      Measurable (fun ω : ShellSeq d ↦ |M ω p.1 p.2|) :=
    fun p _ ↦ continuous_abs.measurable.comp (hmeas p)
  have hsum := isBigO_finset_sum_of_isBigO_gammaSigma
    (μ := μ) (s := (Finset.univ : Finset (Fin d × Fin d)))
    (X := fun p : Fin d × Fin d ↦ fun ω : ShellSeq d ↦ |M ω p.1 p.2|)
    (a := a) (σ := σ) hσ Finset.univ_nonempty (fun p _ ↦ hA p) hX hXm
  refine hsum.of_abs_le ?_
  intro ω
  rw [abs_of_nonneg
      (Homogenization.Book.Ch02.matrixOperatorNorm_nonneg (M ω)),
    abs_of_nonneg (Finset.sum_nonneg (fun p _ ↦ abs_nonneg (M ω p.1 p.2)))]
  exact SuperdiffusionCLT.Section2.Estimates.Stream.matrixOperatorNorm_le_sum_univ_abs_entry
    (M ω)

/-! ## `hStepE` from entry-level concentration

The descendant average is a matrix observable, so once each of its centred
entries is `O_{Gamma_2}` the operator norm is too
(`isBigO_gammaSigma_operatorNorm_of_entrywise`), and the reduction to the operator norm closes
the Loewner statement.  The
amplitudes `A h n i j` are the entry-level amplitudes of the proved
sublattice concentration of `MixingStepEnvelope`; the hypothesis `hAmpl`
records the only remaining bookkeeping, namely that the summed-and-triangled
amplitude fits inside the printed `CFluc * nu^(-2) * 3^(-((n-h)/4))`. -/

/-! ## Step D: the scalar cutoff gap from the deterministic sandwich

At one origin cube the annealed blocks are scalar matrices
(`sigmaBarStarInv_originCube_eq_smul_one`), so the reduction
`stepD_exists_of_scalar_gap` reduces `hStepD` to the deterministic scalar comparison
`shom^-1_{m,*}(cu_h) <= shom^-1_{l,*}(cu_h) + A`.  The proved
`cutoffLoewnerClauses` compares the two cutoff inverses *deterministically and
per `omega`* about the witness `localizationWitness nu h m l`:

`(1 - W omega) s^-1_{m,*}(cu_h) <= s^-1_{l,*}(cu_h)` for every `omega`.

Taking the `(0,0)` diagonal entry (`diag_le_of_matLoewnerLE`) and integrating in
`omega` turns this into

`E[s^-1_{m,*}(cu_h)_{00}] - E[s^-1_{l,*}(cu_h)_{00}] <= E[W * s^-1_{m,*}(cu_h)_{00}]`,

and the two expectations are the annealed scalars
(`integral_sigmaStarInvCoarse_cubeSet_eq_sigmaBarStarInv`).  So the whole scalar
gap is carried by the single first-moment hypothesis `hMoment`. -/

/-- **The Step-D scalar cutoff gap from a deterministic sandwich and a moment.**
If the cutoff inverses at the origin cube `cu_h` satisfy the per-`omega`
relative Loewner bound with witness `W`, and the first moment of
`W * s^-1_{m,*}(cu_h)_{00}` is at most `A`, then the scalar cutoff gap holds at
amplitude `A`. -/
theorem stepD_scalarGap_of_sandwich_moment [NeZero d] {nu A : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) {h m l : ℕ}
    (W : ShellSeq d → ℝ)
    (hrel : ∀ ω : ShellSeq d,
      Homogenization.MatLoewnerLE
        ((1 - W ω) •
          sigmaStarInvCoarse (Homogenization.openCubeSet (Homogenization.originCube d (h : ℤ)))
            (coefficientCutoff nu ω m).toCoeffField)
        (sigmaStarInvCoarse (Homogenization.openCubeSet (Homogenization.originCube d (h : ℤ)))
          (coefficientCutoff nu ω l).toCoeffField))
    (hIntM : Integrable (fun ω : ShellSeq d ↦
      sigmaStarInvCoarse (Homogenization.openCubeSet (Homogenization.originCube d (h : ℤ)))
        (coefficientCutoff nu ω m).toCoeffField 0 0) P.toMeasure)
    (hIntL : Integrable (fun ω : ShellSeq d ↦
      sigmaStarInvCoarse (Homogenization.openCubeSet (Homogenization.originCube d (h : ℤ)))
        (coefficientCutoff nu ω l).toCoeffField 0 0) P.toMeasure)
    (hIntWX : Integrable (fun ω : ShellSeq d ↦ W ω *
      sigmaStarInvCoarse (Homogenization.openCubeSet (Homogenization.originCube d (h : ℤ)))
        (coefficientCutoff nu ω m).toCoeffField 0 0) P.toMeasure)
    (hMoment : ∫ ω : ShellSeq d, W ω *
      sigmaStarInvCoarse (Homogenization.openCubeSet (Homogenization.originCube d (h : ℤ)))
        (coefficientCutoff nu ω m).toCoeffField 0 0 ∂P.toMeasure ≤ A) :
    sigmaBarStarInvScalar nu m P
        (Homogenization.cubeSet (Homogenization.originCube d (h : ℤ))) ≤
      sigmaBarStarInvScalar nu l P
        (Homogenization.cubeSet (Homogenization.originCube d (h : ℤ))) + A := by
  have hpt : ∀ ω : ShellSeq d,
      sigmaStarInvCoarse (Homogenization.openCubeSet (Homogenization.originCube d (h : ℤ)))
          (coefficientCutoff nu ω m).toCoeffField 0 0 -
        sigmaStarInvCoarse (Homogenization.openCubeSet (Homogenization.originCube d (h : ℤ)))
          (coefficientCutoff nu ω l).toCoeffField 0 0 ≤
      W ω * sigmaStarInvCoarse (Homogenization.openCubeSet (Homogenization.originCube d (h : ℤ)))
          (coefficientCutoff nu ω m).toCoeffField 0 0 := by
    intro ω
    have hd := diag_le_of_matLoewnerLE (hrel ω) (0 : Fin d)
    simp only [Matrix.smul_apply, smul_eq_mul] at hd
    have hring : (1 - W ω) *
        sigmaStarInvCoarse (Homogenization.openCubeSet (Homogenization.originCube d (h : ℤ)))
          (coefficientCutoff nu ω m).toCoeffField 0 0 =
        sigmaStarInvCoarse (Homogenization.openCubeSet (Homogenization.originCube d (h : ℤ)))
          (coefficientCutoff nu ω m).toCoeffField 0 0 -
        W ω * sigmaStarInvCoarse (Homogenization.openCubeSet (Homogenization.originCube d (h : ℤ)))
          (coefficientCutoff nu ω m).toCoeffField 0 0 := by
      ring
    linarith only [hd, hring]
  have hmono : ∫ ω : ShellSeq d,
        (sigmaStarInvCoarse (Homogenization.openCubeSet (Homogenization.originCube d (h : ℤ)))
            (coefficientCutoff nu ω m).toCoeffField 0 0 -
          sigmaStarInvCoarse (Homogenization.openCubeSet (Homogenization.originCube d (h : ℤ)))
            (coefficientCutoff nu ω l).toCoeffField 0 0) ∂P.toMeasure ≤
      ∫ ω : ShellSeq d, W ω *
        sigmaStarInvCoarse (Homogenization.openCubeSet (Homogenization.originCube d (h : ℤ)))
          (coefficientCutoff nu ω m).toCoeffField 0 0 ∂P.toMeasure :=
    integral_mono (hIntM.sub hIntL) hIntWX hpt
  rw [integral_sub hIntM hIntL] at hmono
  have hbM : (fun ω : ShellSeq d ↦
        sigmaStarInvCoarse (Homogenization.openCubeSet (Homogenization.originCube d (h : ℤ)))
          (coefficientCutoff nu ω m).toCoeffField 0 0) =
      (fun ω : ShellSeq d ↦
        sigmaStarInvCoarse (Homogenization.cubeSet (Homogenization.originCube d (h : ℤ)))
          (coefficientCutoff nu ω m).toCoeffField 0 0) := by
    funext ω
    exact (congrArg (fun M : Homogenization.Mat d ↦ M 0 0)
      (sigmaStarInvCoarse_cubeSet_eq_openCubeSet
        (Homogenization.originCube d (h : ℤ))
        (coefficientCutoff nu ω m).toCoeffField)).symm
  have hbL : (fun ω : ShellSeq d ↦
        sigmaStarInvCoarse (Homogenization.openCubeSet (Homogenization.originCube d (h : ℤ)))
          (coefficientCutoff nu ω l).toCoeffField 0 0) =
      (fun ω : ShellSeq d ↦
        sigmaStarInvCoarse (Homogenization.cubeSet (Homogenization.originCube d (h : ℤ)))
          (coefficientCutoff nu ω l).toCoeffField 0 0) := by
    funext ω
    exact (congrArg (fun M : Homogenization.Mat d ↦ M 0 0)
      (sigmaStarInvCoarse_cubeSet_eq_openCubeSet
        (Homogenization.originCube d (h : ℤ))
        (coefficientCutoff nu ω l).toCoeffField)).symm
  rw [hbM, hbL] at hmono
  rw [integral_sigmaStarInvCoarse_cubeSet_eq_sigmaBarStarInv hnu m P
        (Homogenization.originCube d (h : ℤ)) 0 0,
      integral_sigmaStarInvCoarse_cubeSet_eq_sigmaBarStarInv hnu l P
        (Homogenization.originCube d (h : ℤ)) 0 0] at hmono
  simp only [sigmaBarStarInvScalar]
  linarith only [hmono, hMoment]

/-! ## The entry bound of the cutoff inverse, on the open cube

The moment hypothesis `hMoment` of the two Step-D reductions is bounded by
first putting `|s^-1_{m,*}(cu_h)_{00}| <= nu^-1` pointwise and then using the
proved stretched-exponential moment estimate
`integral_abs_rpow_le_of_isBigO_gammaSigma`.  The pointwise entry bound is the
ellipticity bound `s^-1_{L,*}(cu) <= nu^-1 Id` (the public
`matLoewnerLE_sigmaStarInvCoarse_cutoffCube`) combined with symmetry and
positive semidefiniteness; it is restated here on the open cube so that it
applies to the same matrix object as `cutoffLoewnerClauses`. -/

/-- **The entry bound `|s^-1_{L,*}(Q)_{ij}| <= nu^-1` on a triadic cube.** -/
theorem abs_entry_sigmaStarInvCoarse_cubeSet_le [NeZero d]
    {nu : ℝ} (hnu : 0 < nu) (omega : ShellSeq d) (L : ℕ)
    (Q : Homogenization.TriadicCube d) (i j : Fin d) :
    |sigmaStarInvCoarse (Homogenization.cubeSet Q)
      (coefficientCutoff nu omega L).toCoeffField i j| ≤ nu⁻¹ := by
  have hsymm : (sigmaStarInvCoarse (Homogenization.cubeSet Q)
      (coefficientCutoff nu omega L).toCoeffField).IsSymm := by
    rw [sigmaStarInvCoarse_cubeSet_eq_openCubeSet]
    have h := Book.Ch02.sigmaStarInvCoarse_isSymm (Book.Ch02.cubeDomain Q)
      ((Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
        (coefficientCutoff nu omega L)
        (aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega L)).coeffOn Q)
    rw [← sigmaStarInvCoarse_toCoeffField,
      Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField_coeffOn_toCoeffField,
      Book.Ch02.cubeDomain_coe] at h
    exact h
  have hpsd := SuperdiffusionCLT.Section3.Terms.posSemidef_sigmaStarInvCoarse_cutoffCube
    hnu L omega Q
  have hLoew : MatLoewnerLE (sigmaStarInvCoarse (Homogenization.cubeSet Q)
      (coefficientCutoff nu omega L).toCoeffField) (nu⁻¹ • (1 : Homogenization.Mat d)) := by
    rw [sigmaStarInvCoarse_cubeSet_eq_openCubeSet]
    show MatLoewnerLE (sigmaStarInvCoarse (Homogenization.openCubeSet Q)
      (coefficientCutoff nu omega L).toFun) (nu⁻¹ • (1 : Homogenization.Mat d))
    exact matLoewnerLE_sigmaStarInvCoarse_cutoffCube hnu omega L Q
  have hpos : ∀ x : Vec d, 0 ≤ vecDot x (matVecMul (sigmaStarInvCoarse (Homogenization.cubeSet Q)
      (coefficientCutoff nu omega L).toCoeffField) x) := by
    intro x
    simpa only [dotProduct, Matrix.mulVec, vecDot, matVecMul, RCLike.star_def, star_trivial,
      conj_trivial] using hpsd.dotProduct_mulVec_nonneg x
  have hentry := abs_entry_le_of_isSymm_of_nonneg hsymm hpos i j
  have hdiag : ∀ i : Fin d, (nu⁻¹ • (1 : Homogenization.Mat d)) i i = nu⁻¹ := by
    intro i; simp
  have hi := diag_le_of_matLoewnerLE hLoew i
  have hj := diag_le_of_matLoewnerLE hLoew j
  rw [hdiag i] at hi
  rw [hdiag j] at hj
  linarith only [hentry, hi, hj]

/-- **The entry bound `|s^-1_{L,*}(Q)_{ij}| <= nu^-1` on the open cube.** -/
theorem abs_entry_sigmaStarInvCoarse_openCubeSet_le [NeZero d]
    {nu : ℝ} (hnu : 0 < nu) (omega : ShellSeq d) (L : ℕ)
    (Q : Homogenization.TriadicCube d) (i j : Fin d) :
    |sigmaStarInvCoarse (Homogenization.openCubeSet Q)
      (coefficientCutoff nu omega L).toCoeffField i j| ≤ nu⁻¹ := by
  have h := abs_entry_sigmaStarInvCoarse_cubeSet_le hnu omega L Q i j
  rwa [sigmaStarInvCoarse_cubeSet_eq_openCubeSet Q
    (coefficientCutoff nu omega L).toCoeffField] at h

/-- **Measurability of an entry of the cutoff inverse on the open cube.** -/
theorem measurable_entry_sigmaStarInvCoarse_openCubeSet [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (m : ℕ) (R : Homogenization.TriadicCube d) (i j : Fin d) :
    Measurable (fun ω : ShellSeq d ↦
      sigmaStarInvCoarse (Homogenization.openCubeSet R)
        (coefficientCutoff nu ω m).toCoeffField i j) := by
  have hEq : (fun ω : ShellSeq d ↦ sigmaStarInvCoarse (Homogenization.cubeSet R)
        (coefficientCutoff nu ω m).toCoeffField i j) =
      fun ω : ShellSeq d ↦ sigmaStarInvCoarse (Homogenization.openCubeSet R)
        (coefficientCutoff nu ω m).toCoeffField i j := by
    funext ω
    exact congrArg (fun M : Homogenization.Mat d ↦ M i j)
      (sigmaStarInvCoarse_cubeSet_eq_openCubeSet R (coefficientCutoff nu ω m).toCoeffField)
  rw [← hEq]
  exact measurable_entry_sigmaStarInvCoarse_cubeSet hnu m R i j

/-! ## The Step-D scalar cutoff gap, unconditionally

Chaining the two reductions with the moment estimate of the witness gives the
scalar cutoff gap at the *provable* amplitude
`nu^-1 * gammaMomentConst 1 * (localizationConst d * nu^-2 * 3^-(m-h))`, i.e.
`O(nu^-3 3^-(m-h))`.  The printed amplitude of `hStepD` is
`CDet * nu^-2 * 3^-((m-h)/2)`; the exponent here is stronger (`3^-(m-h)` rather
than `3^-((m-h)/2)`) but the `nu`-power is one worse (`nu^-3` rather than
`nu^-2`), and since `nu^-3 >= nu^-2 * 3^((m-h)/2) / 3` for `nu <= 1` and
`m - h = 1`, this provable amplitude does **not** dominate the printed one
uniformly in `nu`. -/

end

end SuperdiffusionCLT.Section2.Annealed
