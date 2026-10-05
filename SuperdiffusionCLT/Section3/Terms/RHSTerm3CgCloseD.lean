/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3CgCloseC

/-!
# `term3_cgBound_closeD`: `_hCgBound` with the amplitude block discharged

`term3_cgBound_closeB` (`RHSTerm3CgCloseC.lean`) proves the display
`e.RHS.term3.A`, i.e. the
binder `_hCgBound` of the term-3 final assembly, from the
binders of that statement together with seventeen residuals.  This module
removes the **largest** block of those residuals, the amplitude block

```
Cp  hCp  Cw  hCw  hessianL4  hPoincare  hNablaw
```

(seven binders: the two-scale Poincaré step and the Hessian
display `e.nablaw.Lt`), and discharges two further residuals — the group-C side
condition `hFluxInt` and the group-E side condition `hMemf` both follow from
`hEnergyIntDiff` through the energy-map bound
`hEnergyMaps_at_gluedMaximizers_fluxSlot`, in sections 3 and 4 of this file.  The
module thus proves the same conclusion — the display `_hCgBound` *verbatim* —
from the eight residuals that remain.

## Why the amplitude block is removable

The display `_hCgBound` itself mentions neither `Cp`, `Cw` nor `hessianL4`:
those three are *free carriers* the printed argument introduces on the way (the
amplitudes produced by the two-scale Poincaré step and by `e.nablaw.Lt`, and the
`L⁴` Hessian density they are stated for).  The two displays `hPoincare`,
`hNablaw` are *inequalities* relating those three carriers to the datum of the
display; `hCp`, `hCw` are their nonnegativities.  So the block is discharged by
fixing the carriers once and for all:

* `hessianL4 := fun _ => 1`, whose `P`-moment is `1` because `P` is a
  probability measure (`integral_one_toMeasure`);
* `Cw := cgBoundAmpW nu S = 3^{ℓ'} ν^{1/2}`, the exact reciprocal of the
  factor `3^{-ℓ'} ν^{-1/2}` on the right of `hNablaw`, so that display holds
  with equality (`cgBoundAmpW_nablaw`);
* `Cp := cgBoundAmpP d P S w = A^{1/4} 3^{-k}`, where `A` is *the left member of
  `hPoincare`* (`cgPoincareCarrier`) and `k = coarseBlockScale d S`; the factor
  `3^{-k}` cancels the `3^k` on the right of `hPoincare`, so that display also
  holds with equality (`cgBoundAmpP_poincare`).

Both displays therefore hold *by construction*, and the entire analytic content
of the block moves into the single numeric comparison

```
hCerr : cgBoundConst (cgBoundAmpP d P S w) (cgBoundAmpW nu S) (bEllipConst d) ≤ Cerr
```

which is the printed `∃ C(d)` of `e.RHS.term3.A` and is *not* discharged here: the
constant `Cerr` of the display is bound outside the `∀ nu … P … S …`
block of the term-3 final assembly, while the amplitudes above are functions of
`ν`, `P` and `S`, so `hCerr` is a scale-dependent comparison against a
scale-free constant.  It is exactly the known obstruction
(the window factor discussed in `RHSTerm3CgAssemblyB.lean`).

## What survives

Eight residuals, all carried verbatim from `term3_cgBound_closeB`:
`hEnergyIntDiff`, `hAnnealedSub`, `hAnnealedBig` (group C);
`hJsubInt`, `hEnergyInt`, `hPigeon` (group D); `hde1`, `hCerr` (group E).
The two side conditions `hFluxInt` and `hMemf` are *not* among them: sections 3
and 4 discharge both from `hEnergyIntDiff`, using the energy-map bound
`hEnergyMaps_at_gluedMaximizers_fluxSlot` (in `EnergyMapsWiring.lean`) and, for
`hMemf`, the depth composition of the `coarsePairs` second coordinate.

The conclusion is the `_hCgBound` conclusion of `term3_cgBound_closeB`
(in `RHSTerm3CgCloseC.lean`), which is the display
of the term-3 final assembly verbatim.
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

/-! ## 1. The Poincaré carrier `A` and the two amplitude carriers

`cgPoincareCarrier` is the left member of the display `hPoincare` *before* its
fourth root — the fourth power of the `∇w`-cube-mean-difference amplitude — and
the two amplitude carriers are the values of `Cp` and `Cw` that make the two
displays hold with equality. -/

/-- **The Poincaré carrier `A`**: the fourth power of the left member of the
two-scale Poincaré display `hPoincare` of `term3_cgBound_closeB`,
at the response `w` and the sample law `P`. -/
def cgPoincareCarrier (d : ℕ) (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ)))) : ℝ :=
  ((coarsePairs d S.n (coarseBlockScale d S) S.m).card : ℝ)⁻¹ *
    ∑ q ∈ coarsePairs d S.n (coarseBlockScale d S) S.m,
      ∫ omega : ShellSeq d,
        vecNormSq (volumeAverageVec (openCubeSet q.2) ((w omega).toH1Function.grad) -
            volumeAverageVec (openCubeSet q.1) ((w omega).toH1Function.grad)) ^ (2 : ℝ)
        ∂P.toMeasure

/-- **The amplitude `Cp` of the display**, fixed so that `hPoincare` holds with
equality: the fourth root of the Poincaré carrier, times the reciprocal of the
window factor `3^k` of the printed right-hand side. -/
def cgBoundAmpP (d : ℕ) (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ)))) : ℝ :=
  cgPoincareCarrier d P S w ^ ((1 : ℝ) / 4) *
    (3 : ℝ) ^ (-((coarseBlockScale d S : ℕ) : ℝ))

/-- **The amplitude `Cw` of the display**, fixed so that `hNablaw` holds with
equality: the reciprocal of the factor `3^{-ℓ'} ν^{-1/2}` of the printed
right-hand side of `e.nablaw.Lt`. -/
def cgBoundAmpW (nu : ℝ) (S : ScaleSelection) : ℝ :=
  (3 : ℝ) ^ ((S.ellPrime : ℕ) : ℝ) * nu ^ ((1 : ℝ) / 2)

/-! ## 2. The probability integral and the two displays at the fixed carriers -/

/-- **The `P`-moment of the constant `1`.**  `P` is a probability measure, so
`∫ 1 ∂P = 1`; this is what makes `hessianL4 := fun _ => 1` produce the moment
`1` in the two displays. -/
theorem integral_one_toMeasure (d : ℕ) (P : ProbabilityMeasure (ShellSeq d)) :
    ∫ _omega : ShellSeq d, (1 : ℝ) ∂P.toMeasure = 1 :=
  MeasureTheory.integral_eq_const (Filter.Eventually.of_forall fun _ => rfl)

/-- The Poincaré carrier is nonnegative: an inverse cardinal times a sum of
integrals of nonnegative functions. -/
theorem cgPoincareCarrier_nonneg (d : ℕ) (P : ProbabilityMeasure (ShellSeq d))
    (S : ScaleSelection)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ)))) :
    0 ≤ cgPoincareCarrier d P S w := by
  rw [cgPoincareCarrier]
  refine mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg fun q _ => ?_)
  exact MeasureTheory.integral_nonneg fun omega => Real.rpow_nonneg (vecNormSq_nonneg _) 2

/-- The amplitude `Cp` is nonnegative. -/
theorem cgBoundAmpP_nonneg (d : ℕ) (P : ProbabilityMeasure (ShellSeq d))
    (S : ScaleSelection)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ)))) :
    0 ≤ cgBoundAmpP d P S w := by
  rw [cgBoundAmpP]
  exact mul_nonneg (Real.rpow_nonneg (cgPoincareCarrier_nonneg d P S w) _)
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)

/-- The amplitude `Cw` is nonnegative, since `0 < nu`. -/
theorem cgBoundAmpW_nonneg (nu : ℝ) (hnu : 0 < nu) (S : ScaleSelection) :
    0 ≤ cgBoundAmpW nu S := by
  rw [cgBoundAmpW]
  exact mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
    (Real.rpow_nonneg hnu.le _)

/-- **`hPoincare` of `term3_cgBound_closeB` at the fixed carriers.**  With
`Cp := cgBoundAmpP d P S w` and `hessianL4 := fun _ => 1` the display holds with
equality: the factor `3^{-k}` of the amplitude cancels the printed window factor
`3^k`, and the Hessian moment is `1` by `integral_one_toMeasure`. -/
theorem cgBoundAmpP_poincare (d : ℕ) (P : ProbabilityMeasure (ShellSeq d))
    (S : ScaleSelection)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ)))) :
    (cgPoincareCarrier d P S w) ^ ((1 : ℝ) / 4) ≤
      cgBoundAmpP d P S w * (3 : ℝ) ^ ((coarseBlockScale d S : ℕ) : ℝ) *
        (∫ _omega : ShellSeq d, (1 : ℝ) ∂P.toMeasure) ^ ((1 : ℝ) / 4) := by
  have hInt : ∫ _omega : ShellSeq d, (1 : ℝ) ∂P.toMeasure = 1 :=
    integral_one_toMeasure d P
  have h3 : (3 : ℝ) ^ (-((coarseBlockScale d S : ℕ) : ℝ)) *
      (3 : ℝ) ^ ((coarseBlockScale d S : ℕ) : ℝ) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3), neg_add_cancel, Real.rpow_zero]
  rw [hInt, Real.one_rpow, mul_one, cgBoundAmpP, mul_assoc, h3, mul_one]

/-- **`hNablaw` of `term3_cgBound_closeB` at the fixed carriers.**  With
`Cw := cgBoundAmpW nu S` and `hessianL4 := fun _ => 1` the display holds with
equality: the amplitude is the exact reciprocal of the printed factor
`3^{-ℓ'} ν^{-1/2}`, and the Hessian moment is `1` by `integral_one_toMeasure`. -/
theorem cgBoundAmpW_nablaw (d : ℕ) (nu : ℝ) (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) :
    (∫ _omega : ShellSeq d, (1 : ℝ) ∂P.toMeasure) ^ ((1 : ℝ) / 4) ≤
      cgBoundAmpW nu S * (3 : ℝ) ^ (-((S.ellPrime : ℕ) : ℝ)) * nu ^ (-(1 : ℝ) / 2) := by
  have hInt : ∫ _omega : ShellSeq d, (1 : ℝ) ∂P.toMeasure = 1 :=
    integral_one_toMeasure d P
  have h3 : (3 : ℝ) ^ ((S.ellPrime : ℕ) : ℝ) *
      (3 : ℝ) ^ (-((S.ellPrime : ℕ) : ℝ)) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3), add_neg_cancel, Real.rpow_zero]
  have hnur : nu ^ ((1 : ℝ) / 2) * nu ^ (-((1 : ℝ) / 2)) = 1 := by
    rw [← Real.rpow_add hnu, add_neg_cancel, Real.rpow_zero]
  have hprod : cgBoundAmpW nu S * (3 : ℝ) ^ (-((S.ellPrime : ℕ) : ℝ)) *
      nu ^ (-(1 : ℝ) / 2) = 1 := by
    have he : -(1 : ℝ) / 2 = -((1 : ℝ) / 2) := by norm_num
    rw [he, cgBoundAmpW]
    calc ((3 : ℝ) ^ ((S.ellPrime : ℕ) : ℝ) * nu ^ ((1 : ℝ) / 2)) *
          (3 : ℝ) ^ (-((S.ellPrime : ℕ) : ℝ)) * nu ^ (-((1 : ℝ) / 2))
        = ((3 : ℝ) ^ ((S.ellPrime : ℕ) : ℝ) * (3 : ℝ) ^ (-((S.ellPrime : ℕ) : ℝ))) *
            (nu ^ ((1 : ℝ) / 2) * nu ^ (-((1 : ℝ) / 2))) := by ring
      _ = 1 := by rw [h3, hnur, mul_one]
  rw [hInt, Real.one_rpow]
  exact le_of_eq hprod.symm

/-! ## 3. The flux-norm integrability side condition

`hFluxInt` of `term3_cgBound_closeB` is not carried below: it follows from
`hEnergyIntDiff` by the energy-map bound
`hEnergyMaps_at_gluedMaximizers_fluxSlot` (in `EnergyMapsWiring.lean`), which is
the printed energy-map step.  The only extra input is
measurability of `gluedFluxNorm` in the sample, which
`measurable_volumeAverageVec_coefficientCutoff_gluedDifference_final`
(in `RHSTerm3SideFinal.lean`) supplies for the cube mean of the cutoff flux and
`translatedBlockHalfWeightInv_eq_vecDot_inv` converts into the quadratic form
`v · b_L^{-1} v` whose entries are measurable
(`measurable_matInv_apply`, `measurable_translatedCoarseBlock_apply`). -/

/-- Pairing a measurable vector with a measurable matrix image of itself is
measurable — here for the *inverse* of a matrix with measurable entries. -/
private theorem measurable_vecDot_matVecMul_inv_self {d : ℕ} {Omega : Type*}
    [MeasurableSpace Omega] {M : Omega → Mat d} {v : Omega → Vec d}
    (hM : ∀ i j, Measurable fun omega => M omega i j)
    (hv : ∀ i, Measurable fun omega => v omega i) :
    Measurable fun omega => vecDot (v omega) (matVecMul ((M omega)⁻¹) (v omega)) := by
  have hMinv : ∀ i j, Measurable fun omega => (M omega)⁻¹ i j :=
    fun i j => SuperdiffusionCLT.Section2.Annealed.measurable_matInv_apply hM i j
  simp only [vecDot, matVecMul]
  exact Finset.measurable_sum _ fun i _ =>
    (hv i).mul (Finset.measurable_sum _ fun j _ => (hMinv i j).mul (hv j))

/-- **The flux norm is measurable in the sample.**  On a sub-cube `R ⊆ cu_m`, the
cube mean of the cutoff flux of the glued-field difference is measurable
(`measurable_volumeAverageVec_coefficientCutoff_gluedDifference_final`), and
`gluedFluxNorm` is the quadratic form `v · b_{L'}^{-1} v` of that cube mean
(`gluedFluxNorm_eq` composed with `translatedBlockHalfWeightInv_eq_vecDot_inv`),
whose entries are measurable in the sample. -/
theorem measurable_gluedFluxNorm_discharged (d : ℕ) [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) (e : Vec d)
    (R : TriadicCube d) (hR : R ∈ largeCubeSubcubes d S.n S.m) :
    Measurable (fun omega : ShellSeq d =>
      gluedFluxNorm hnu S (fluxSlot nu S.LPrime P S.n e) omega R) := by
  set F : Vec d := fluxSlot nu S.LPrime P S.n e with hF
  have hv : ∀ i : Fin d, Measurable (fun omega : ShellSeq d =>
      volumeAverageVec (openCubeSet R)
        (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
          (gluedGradientField hnu S.LPrime S.m S.m F omega y -
            gluedGradientField hnu S.LPrime S.n S.m F omega y)) i) :=
    fun i => (measurable_pi_apply i).comp
      (measurable_volumeAverageVec_coefficientCutoff_gluedDifference_final hnu P S e R hR)
  have hEq : (fun omega : ShellSeq d => gluedFluxNorm hnu S F omega R) =
      fun omega : ShellSeq d =>
        vecDot (volumeAverageVec (openCubeSet R)
            (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
              (gluedGradientField hnu S.LPrime S.m S.m F omega y -
                gluedGradientField hnu S.LPrime S.n S.m F omega y)))
          (matVecMul ((translatedCoarseBlock nu S.LPrime omega R)⁻¹)
            (volumeAverageVec (openCubeSet R)
              (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
                (gluedGradientField hnu S.LPrime S.m S.m F omega y -
                  gluedGradientField hnu S.LPrime S.n S.m F omega y)))) := by
    funext omega
    rw [gluedFluxNorm_eq hnu S F omega R,
      translatedBlockHalfWeightInv_eq_vecDot_inv hnu S.LPrime omega R]
  rw [hEq, hF]
  exact measurable_vecDot_matVecMul_inv_self
    (fun i j => measurable_translatedCoarseBlock_apply hnu S.LPrime R i j) hv

/-- **`hFluxInt` of `term3_cgBound_closeB`, discharged from `hEnergyIntDiff`.**
The energy-map bound `hEnergyMaps_at_gluedMaximizers_fluxSlot` dominates
the flux norm pointwise by the integrand of `hEnergyIntDiff`; the flux norm is
nonnegative and measurable, so integrability transfers. -/
theorem integrable_gluedFluxNorm_discharged (d : ℕ) [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) (e : Vec d)
    (hEnergyIntDiff : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      Integrable (fun omega : ShellSeq d =>
        volumeAverage (openCubeSet R)
          (fun y => nu * vecNormSq
            (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e) omega y -
              gluedSubcubeGrad hnu S (fluxSlot nu S.LPrime P S.n e) omega y)))
        P.toMeasure) :
    ∀ R ∈ largeCubeSubcubes d S.n S.m,
      Integrable (fun omega : ShellSeq d =>
        gluedFluxNorm hnu S (fluxSlot nu S.LPrime P S.n e) omega R) P.toMeasure := by
  intro R hR
  have hmeas := measurable_gluedFluxNorm_discharged d hnu P S e R hR
  refine Integrable.mono' (hEnergyIntDiff R hR) hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun omega => ?_)
  have hnn : 0 ≤ gluedFluxNorm hnu S (fluxSlot nu S.LPrime P S.n e) omega R := by
    rw [gluedFluxNorm_eq hnu S (fluxSlot nu S.LPrime P S.n e) omega R]
    exact translatedBlockHalfWeightInv_nonneg nu S.LPrime omega R _
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact hEnergyMaps_at_gluedMaximizers_fluxSlot hnu P S e omega R hR

/-! ## 4. The square-root flux membership `hMemf`

`hMemf` of `term3_cgBound_closeB` asks for `MemLp` of the *square root* of the
flux norm, at the second coordinate of every coarse pair.  Since the flux norm
is nonnegative, `MemLp (f^{1/2}) 2` is equivalent to `Integrable f`, so the same
energy-map bound settles it: the second coordinate of a coarse pair is a
large-cube sub-cube at scale `S.n` (depth composition below), and there
`hEnergyIntDiff` supplies the integrable dominating function. -/

/-- Depth composition for the descendant family: a descendant of a descendant is
a descendant of the composite depth. -/
private theorem mem_descendantsAtDepth_trans_cgD {d : ℕ} {Q R U : TriadicCube d} {m n : ℕ}
    (hR : R ∈ descendantsAtDepth Q m) (hU : U ∈ descendantsAtDepth R n) :
    U ∈ descendantsAtDepth Q (m + n) := by
  induction n generalizing U with
  | zero =>
      simp only [Nat.add_zero, descendantsAtDepth_zero, Finset.mem_singleton] at hU ⊢
      exact hU ▸ hR
  | succ n ih =>
      rw [Nat.add_succ, descendantsAtDepth_succ] at hU ⊢
      rcases Finset.mem_biUnion.mp hU with ⟨T, hT, hUT⟩
      exact Finset.mem_biUnion.mpr ⟨T, ih hT, hUT⟩

/-- The two scale bounds of the coarse block scale, from the scale ordering. -/
private theorem coarseBlockScale_bounds_cgD (d : ℕ) (S : ScaleSelection)
    (hSorder : ScalesOrdering S) :
    S.n ≤ coarseBlockScale d S ∧ coarseBlockScale d S ≤ S.m := by
  have hell : S.ell ≤ S.ellPrime := le_of_lt hSorder.ell_lt_ellPrime
  have hnl : S.n ≤ S.ell := le_of_lt hSorder.n_lt_ell
  obtain ⟨hlk, hkp, -, -⟩ := coarse_block_scale_choice d S hell
  exact ⟨le_trans hnl hlk, le_trans hkp (le_of_lt hSorder.ellPrime_lt_m)⟩

/-- The second coordinate of a coarse pair is a large-cube sub-cube at the fine
scale `n`. -/
private theorem snd_mem_largeCubeSubcubes_of_mem_coarsePairs_cgD {d n k m : ℕ} (hnk : n ≤ k)
    (hkm : k ≤ m) {q : (_ : TriadicCube d) × TriadicCube d}
    (hq : q ∈ coarsePairs d n k m) : q.2 ∈ largeCubeSubcubes d n m := by
  obtain ⟨h1, h2⟩ := Finset.mem_sigma.mp hq
  rw [largeCubeSubcubes_eq_descendantsAtDepth] at h1 ⊢
  have h := mem_descendantsAtDepth_trans_cgD h1 h2
  rwa [show m - k + (k - n) = m - n by omega] at h

/-- **`hMemf` of `term3_cgBound_closeB`, discharged from `hEnergyIntDiff`.**  The
energy-map bound dominates the flux norm pointwise at the second
coordinate of a coarse pair, which is a large-cube sub-cube at scale `S.n`; there
`hEnergyIntDiff` makes the flux norm integrable, and the square root of a
nonnegative integrable function is `L²`. -/
theorem memLp_two_gluedFluxNorm_sqrt_discharged (d : ℕ) [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) (hSorder : ScalesOrdering S)
    (e : Vec d)
    (hEnergyIntDiff : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      Integrable (fun omega : ShellSeq d =>
        volumeAverage (openCubeSet R)
          (fun y => nu * vecNormSq
            (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e) omega y -
              gluedSubcubeGrad hnu S (fluxSlot nu S.LPrime P S.n e) omega y)))
        P.toMeasure) :
    ∀ q ∈ coarsePairs d S.n (coarseBlockScale d S) S.m,
      MemLp (fun omega : ShellSeq d =>
        gluedFluxNorm hnu S (fluxSlot nu S.LPrime P S.n e) omega q.2 ^ ((1 : ℝ) / 2))
        (ENNReal.ofReal (2 : ℝ)) P.toMeasure := by
  intro q hq
  obtain ⟨hnk, hkm⟩ := coarseBlockScale_bounds_cgD d S hSorder
  have hq2 : q.2 ∈ largeCubeSubcubes d S.n S.m :=
    snd_mem_largeCubeSubcubes_of_mem_coarsePairs_cgD hnk hkm hq
  have hnn : ∀ omega : ShellSeq d,
      0 ≤ gluedFluxNorm hnu S (fluxSlot nu S.LPrime P S.n e) omega q.2 := by
    intro omega
    rw [gluedFluxNorm_eq hnu S (fluxSlot nu S.LPrime P S.n e) omega q.2]
    exact translatedBlockHalfWeightInv_nonneg nu S.LPrime omega q.2 _
  have hmeas := measurable_gluedFluxNorm_discharged d hnu P S e q.2 hq2
  have hInt : Integrable (fun omega : ShellSeq d =>
      gluedFluxNorm hnu S (fluxSlot nu S.LPrime P S.n e) omega q.2) P.toMeasure := by
    refine Integrable.mono' (hEnergyIntDiff q.2 hq2) hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun omega => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn omega)]
    exact hEnergyMaps_at_gluedMaximizers_fluxSlot hnu P S e omega q.2 hq2
  have haes : AEStronglyMeasurable (fun omega : ShellSeq d =>
      gluedFluxNorm hnu S (fluxSlot nu S.LPrime P S.n e) omega q.2 ^ ((1 : ℝ) / 2))
      P.toMeasure :=
    AEStronglyMeasurable.congr
      ((Real.continuous_sqrt.measurable.comp hmeas).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun omega => Real.sqrt_eq_rpow _)
  have hInt' : Integrable (fun omega : ShellSeq d =>
      (gluedFluxNorm hnu S (fluxSlot nu S.LPrime P S.n e) omega q.2 ^ ((1 : ℝ) / 2)) ^ 2)
      P.toMeasure := by
    refine hInt.congr (Filter.Eventually.of_forall fun omega => ?_)
    change gluedFluxNorm hnu S (fluxSlot nu S.LPrime P S.n e) omega q.2 =
      (gluedFluxNorm hnu S (fluxSlot nu S.LPrime P S.n e) omega q.2 ^ ((1 : ℝ) / 2)) ^ 2
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (hnn omega)]
  simpa using (MeasureTheory.memLp_two_iff_integrable_sq haes).mpr hInt'

/-! ## 5. The display at the reduced package

`term3_cgBound_closeD` is `term3_cgBound_closeB` with the whole amplitude block
`Cp hCp Cw hCw hessianL4 hPoincare hNablaw` replaced by the single numeric
comparison `hCerr` at the *fixed* amplitudes of section 1.  Every remaining
binder is copied verbatim from `term3_cgBound_closeB` — with the two
side conditions `hFluxInt` and `hMemf` supplied internally by sections 3 and 4 —
and the conclusion is the `_hCgBound` display of that statement verbatim. -/

/-- **`term3_cgBound_closeD`.**  The printed display `e.RHS.term3.A`
(`_hCgBound` of the term-3 final assembly) — verbatim — from
the binders together with eight residuals: `hEnergyIntDiff`,
`hAnnealedSub`, `hAnnealedBig`, `hJsubInt`, `hEnergyInt`, `hPigeon`, `hde1` and
the single numeric comparison `hCerr`.

Nine of the seventeen residuals of `term3_cgBound_closeB` are *not* hypotheses
here.  The amplitude block `Cp`, `hCp`, `Cw`, `hCw`, `hessianL4`, `hPoincare`,
`hNablaw` is discharged by *fixing* the carriers,
`hessianL4 := fun _ => 1`, `Cw := cgBoundAmpW nu S` and
`Cp := cgBoundAmpP d P S w`, and proving the two displays at those values
(`cgBoundAmpP_poincare`, `cgBoundAmpW_nablaw`); the analytic content of that
block moves into `hCerr`, which is the printed `∃ C(d)` of `e.RHS.term3.A` — the
known obstruction, the window factor discussed in `RHSTerm3CgAssemblyB.lean`.
The two side conditions `hFluxInt` and `hMemf` are discharged from
`hEnergyIntDiff` (`integrable_gluedFluxNorm_discharged`,
`memLp_two_gluedFluxNorm_sqrt_discharged`). -/
theorem term3_cgBound_closeD
    (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (nu : ℝ) (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P) (hJ1V2 : ShellLawJ1Restriction d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (hSorder : ScalesOrdering S)
    (hTwoHLeM : 2 * S.h ≤ S.m) (hHundredALeH : 100 * S.a ≤ S.h)
    (hWindowVsOffset : S.h + 1 ≤ 3 ^ S.a)
    (e : Vec d) (he : vecNormSq e = 1)
    (delta etaL : ℝ) (hdelta : 0 ≤ delta) (hetaL : 0 ≤ etaL)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      SuperdiffusionCLT.Section3.Setup.IsDirichletResponse
        omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega))
    (Cerr : ℝ)
    (hde1 : delta + etaL ≤ 1)
    (hCerr : cgBoundConst (cgBoundAmpP d P S w) (cgBoundAmpW nu S) (bEllipConst d) ≤ Cerr)
    (hEnergyIntDiff : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      Integrable (fun omega : ShellSeq d =>
        volumeAverage (openCubeSet R)
          (fun y => nu * vecNormSq
            (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e) omega y -
              gluedSubcubeGrad hnu S (fluxSlot nu S.LPrime P S.n e) omega y)))
        P.toMeasure)
    (hAnnealedSub : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      ∫ omega : ShellSeq d,
          energySubQCarrier nu P S e (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e))
            (gluedSubcubeGrad hnu S (fluxSlot nu S.LPrime P S.n e)) omega R
        ∂P.toMeasure =
        (1 / 2 : ℝ) * sigmaBarStarInvSeq nu S.LPrime P S.n *
          vecNormSq (fluxSlot nu S.LPrime P S.n e))
    (hAnnealedBig : ∫ omega : ShellSeq d,
          energyBigQCarrier nu P S e
            (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e)) omega
        ∂P.toMeasure =
        (1 / 2 : ℝ) * sigmaBarStarInvSeq nu S.LPrime P S.m *
          vecNormSq (fluxSlot nu S.LPrime P S.n e))
    (hJsubInt : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      Integrable (fun omega : ShellSeq d =>
        energySubQCarrier nu P S e (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e))
          (gluedSubcubeGrad hnu S (fluxSlot nu S.LPrime P S.n e)) omega R) P.toMeasure)
    (hEnergyInt : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      Integrable (fun omega : ShellSeq d =>
        volumeAverage (openCubeSet R)
          (fun y => -(nu / 2) * vecNormSq
              (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e) omega y) +
            vecDot (fluxSlot nu S.LPrime P S.n e)
              (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e) omega y)))
        P.toMeasure)
    (hPigeon : |1 - (sigmaBarStarInvSeq nu S.LPrime P S.n)⁻¹ *
      sigmaBarStarInvSeq nu S.LPrime P S.m| ≤ delta + etaL) :
    ∫ omega : ShellSeq d,
        ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
          ∑ R ∈ largeCubeSubcubes d S.n S.m,
            vecDot (volumeAverageVec (openCubeSet R) ((w omega).toH1Function.grad))
              (volumeAverageVec (openCubeSet R)
                (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
                  (gluedGradientField hnu S.LPrime S.m S.m
                      (fluxSlot nu S.LPrime P S.n e) omega y -
                    gluedGradientField hnu S.LPrime S.n S.m
                      (fluxSlot nu S.LPrime P S.n e) omega y))) ∂P.toMeasure ≤
      (((largeCubeSubcubes d (coarseBlockScale d S) S.m).card : ℝ)⁻¹ *
          ∑ z' ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
            (((descendantsAtDepth z' (coarseBlockScale d S - S.n)).card : ℕ) : ℝ)⁻¹ *
              ∑ z ∈ descendantsAtDepth z' (coarseBlockScale d S - S.n),
                ∫ omega : ShellSeq d,
                  translatedBlockHalfWeight nu S.LPrime w omega z' z
                  ∂P.toMeasure) ^ ((1 : ℝ) / 2) *
          (delta + etaL) ^ ((1 : ℝ) / 2) +
        Cerr * (3 : ℝ) ^ (-(((S.ellPrime - S.ell : ℕ) : ℝ) / 4)) *
          ((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ) * nu ^ (-(5 : ℝ) / 2) := by
  refine term3_cgBound_closeB d hd nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder
    hTwoHLeM hHundredALeH hWindowVsOffset e he delta etaL hdelta hetaL w hw Cerr
    (cgBoundAmpP d P S w) (cgBoundAmpW nu S) (cgBoundAmpP_nonneg d P S w)
    (cgBoundAmpW_nonneg nu hnu S) (fun _ : ShellSeq d => (1 : ℝ)) hde1 hCerr
    (integrable_gluedFluxNorm_discharged d hnu P S e hEnergyIntDiff)
    hEnergyIntDiff hAnnealedSub hAnnealedBig hJsubInt hEnergyInt hPigeon
    (cgBoundAmpP_poincare d P S w) (cgBoundAmpW_nablaw d nu hnu P S)
    (memLp_two_gluedFluxNorm_sqrt_discharged d hnu P S hSorder e hEnergyIntDiff)

end

end SuperdiffusionCLT.Section3.Terms
