/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.GluedField
public import SuperdiffusionCLT.Section2.Annealed.Integrability
public import SuperdiffusionCLT.Section2.Annealed.Measurability

/-!
# The annealed mean defect `p̃ − p = E[(∇ũ_n − ∇u_n)_{cu_n}]`

The proof of `l.RHS.term2` needs the identity

`p̃ − p = E[(∇ũ_n − ∇u_n)_{cu_n}]`,

which the rendered display `e.RHS.term2.proxy.error` carries as its hypothesis `hAvg`:

`p̃ − p = ∫ omega, ⨍_{cu_n} (∇ũ_n − ∇u_n) ∂P`.

It is the definition of `p̃` (`p̃ = E[(∇ũ_n)_{cu_n}]`) against
`e.average.of.vn`.  Both halves are provided by
`GluedField.lean`: `annealedGluedAverage_eq` writes `p̃` as the Bochner integral
of the `cu_n`-average of the glued field at cutoff `ℓ`, and
`integral_volumeAverageVec_gluedGradientField_eq_testVector` identifies
`E[(∇u_n)_{cu_n}]` with the test vector `p` of `e.Sec3.p.q.def` at cutoff `L'`.
The remaining two measure-theoretic steps split the average of
the difference into the difference of the averages:

* the cube average respects differences: `volumeAverageVec_sub` below, from
  Mathlib's `integral_sub` and the componentwise integrability on the open cube
  that `memLp_two_gluedGradientField` supplies (`L²` on every open triadic
  cube, which has finite volume);
* the two cube averages are Bochner-integrable observables in the shell
  sequence: by `volumeAverageVec_gluedGradientField` each is the matrix-vector
  product of the quenched coarse matrix with the flux slot, so integrability in
  `omega` reduces to integrability of the quenched coarse matrix
  `s_{L,*}^{-1}(cu_n)` at the two cutoff levels `L'` and `ℓ`.  That
  integrability is `integrable_coarseBlockMatrix_lowerRight` of
  `Section2/Annealed/Integrability.lean` read through the block identification
  `coarseBlockMatrix_cubeSet_lowerRight_eq` of
  `Section2/Annealed/Measurability.lean`; no
  further hypothesis is carried.

The main theorem `annealedGluedAverage_sub_testVector_eq` is therefore the
input `hAvg` of `e.RHS.term2.proxy.error` at the carriers of `GluedField.lean`:
`pTilde = annealedGluedAverage hnu P S.ell S.n S.m
(fluxSlot nu S.LPrime P S.n e)` — the mean `p̃` of the paper at these
carriers, as in the proof of `l.RHS.term2` — and
`p = testVector nu S.LPrime P S.n e`, the vector of `e.Sec3.p.q.def`.  The
corollary keeps `pTilde` as a free binder linked to that mean by an explicit hypothesis,
in the shape used by `e.RHS.term2.proxy.error`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open Homogenization
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.Setup
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-! ## The cube average respects differences -/

section CubeAverageSub

/-- **The cube average respects differences**: for two vector fields whose
coordinate functions are integrable on the cube, the average of the difference
is the difference of the averages.  This is Mathlib's `integral_sub` at the
coordinate level: `volumeAverageVec` is a coordinate average by definition. -/
theorem volumeAverageVec_sub {s : Set (Vec d)} {f g : Vec d → Vec d}
    (hf : ∀ i : Fin d, MeasureTheory.Integrable (fun x : Vec d => f x i)
      (MeasureTheory.volume.restrict s))
    (hg : ∀ i : Fin d, MeasureTheory.Integrable (fun x : Vec d => g x i)
      (MeasureTheory.volume.restrict s)) :
    volumeAverageVec s (fun x => f x - g x) = volumeAverageVec s f - volumeAverageVec s g := by
  funext i
  show (MeasureTheory.volume s).toReal⁻¹ * ∫ x in s, f x i - g x i ∂MeasureTheory.volume
    = (MeasureTheory.volume s).toReal⁻¹ * ∫ x in s, f x i ∂MeasureTheory.volume -
      (MeasureTheory.volume s).toReal⁻¹ * ∫ x in s, g x i ∂MeasureTheory.volume
  rw [MeasureTheory.integral_sub (hf i) (hg i)]
  ring

end CubeAverageSub

/-! ## Componentwise integrability of the glued field on a cube -/

section ComponentIntegrability

/-- Each coordinate of the glued field is integrable on an open triadic cube:
the `L²` membership of `memLp_two_gluedGradientField` restricts to the cube,
whose volume is finite, and `L²` is contained in `L¹` on a finite measure. -/
theorem integrable_component_gluedGradientField {nu : ℝ} (hnu : 0 < nu) (L k m : ℕ)
    (F : Vec d)
    (omega : ShellSeq d) (Q : TriadicCube d) (i : Fin d) :
    MeasureTheory.Integrable
      (fun x : Vec d => gluedGradientField hnu L k m F omega x i)
      (MeasureTheory.volume.restrict (openCubeSet Q)) := by
  have : MeasureTheory.IsFiniteMeasure
      (MeasureTheory.volume.restrict (openCubeSet Q)) :=
    SuperdiffusionCLT.Section3.ResponseFields.instIsFiniteMeasureVolumeMeasureOnOpenCubeSet
      Q
  exact MeasureTheory.MemLp.integrable (by norm_num)
    (MeasureTheory.MemLp.eval
      ((memLp_two_gluedGradientField hnu L k m F omega).restrict (openCubeSet Q)) i)

end ComponentIntegrability

/-! ## Integrability in the shell sequence of the cube averages -/

section AnnealedIntegrability

/-- **The quenched coarse matrix is an integrable observable.**
`integrable_coarseBlockMatrix_lowerRight` of
`Section2/Annealed/Integrability.lean` integrates the lower-right block of the
block matrix of the cutoff field on the half-open cube; through the block
identification `coarseBlockMatrix_cubeSet_lowerRight_eq` of
`Section2/Annealed/Measurability.lean` that block is the coarse matrix
`s_{L,*}^{-1}` of the open cube. -/
theorem integrable_sigmaStarInvCoarse [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (L : ℕ) (Q : TriadicCube d) :
    MeasureTheory.Integrable (fun omega : ShellSeq d =>
      sigmaStarInvCoarse (openCubeSet Q)
        (coefficientCutoff nu omega L).toCoeffField) P.toMeasure := by
  have h := integrable_coarseBlockMatrix_lowerRight (nu := nu) hnu L Q hPrefix hJ2
    hJ3 hJ4
  refine h.congr ?_
  exact Filter.Eventually.of_forall fun omega =>
    coarseBlockMatrix_cubeSet_lowerRight_eq
      (aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega L) Q

/-- A matrix-valued Bochner-integrable observable, multiplied on the right by a
fixed vector, is a vector-valued Bochner-integrable observable: the coordinates
are the row sums, integrated term by term. -/
private theorem integrableMatVecMul {mu : MeasureTheory.Measure (ShellSeq d)}
    {M : ShellSeq d → Mat d}
    (hM : MeasureTheory.Integrable M mu) (F : Vec d) :
    MeasureTheory.Integrable (fun omega : ShellSeq d => matVecMul (M omega) F) mu := by
  refine MeasureTheory.Integrable.of_eval fun i => ?_
  show MeasureTheory.Integrable
    (fun omega : ShellSeq d => ∑ j, M omega i j * F j) mu
  exact MeasureTheory.integrable_finsetSum _ fun j _ =>
    ((hM.eval i).eval j).mul_const (F j)

/-- **The `cu_k`-average of the glued field is integrable in the shell
sequence**: through `volumeAverageVec_gluedGradientField` at the centred cube
`cu_k` (one of the sub-cubes of `cu_m` whenever `k ≤ m`) it is the
matrix-vector product of the quenched coarse matrix with the flux slot, and
that matrix is integrable by `integrable_sigmaStarInvCoarse`. -/
theorem integrable_annealedGluedAverage [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (L k m : ℕ) (hkm : k ≤ m) (F : Vec d) {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) :
    MeasureTheory.Integrable (fun omega : ShellSeq d =>
      volumeAverageVec (openCubeSet (originCube d (k : ℤ)))
        (gluedGradientField hnu L k m F omega)) P.toMeasure := by
  have hident : (fun omega : ShellSeq d =>
      volumeAverageVec (openCubeSet (originCube d (k : ℤ)))
        (gluedGradientField hnu L k m F omega))
      = fun omega : ShellSeq d =>
        matVecMul (sigmaStarInvCoarse (openCubeSet (originCube d (k : ℤ)))
          (coefficientCutoff nu omega L).toCoeffField) F := by
    funext omega
    exact volumeAverageVec_gluedGradientField hnu L k m F omega
      (originCube_mem_largeCubeSubcubes hkm)
  rw [hident]
  exact integrableMatVecMul
    (integrable_sigmaStarInvCoarse hnu hPrefix hJ2 hJ3 hJ4 L
      (originCube d (k : ℤ))) F

end AnnealedIntegrability

/-! ## The annealed mean defect -/

section MeanDefect

/-- **`p̃ − p = E[(∇ũ_n − ∇u_n)_{cu_n}]`**, the hypothesis `hAvg` of
`e.RHS.term2.proxy.error` at the carriers of `GluedField.lean`
(the definition of `p̃` in the proof of `l.RHS.term2`, against
`e.average.of.vn`).

Here `p̃` is the mean of the paper at these carriers,
`annealedGluedAverage hnu P S.ell S.n S.m
(fluxSlot nu S.LPrime P S.n e)` — the annealed `cu_n`-average of the glued
field at the cutoff-`ℓ` proxy, as in the proof of `l.RHS.term2` — and `p` is the test vector
of `e.Sec3.p.q.def`.  The right side is the Bochner integral in the shell sequence of the
`cu_n`-average of the difference of the two glued fields `∇ũ_n` (cutoff `ℓ`) and `∇u_n`
(cutoff `L'`), in the same flux slot.

The proof is the split of the average of the difference: at each sample
`volumeAverageVec_sub` turns the `cu_n`-average of the difference into the
difference of the `cu_n`-averages, Mathlib's `integral_sub` splits the
annealed integral, the cutoff-`ℓ` half is `p̃` by the definition
`annealedGluedAverage_eq`, and the cutoff-`L'` half is the test vector `p` by
`e.average.of.vn` (`integral_volumeAverageVec_gluedGradientField_eq_testVector`
at the centred cube `cu_n`). -/
theorem annealedGluedAverage_sub_testVector_eq
    (d : ℕ) [NeZero d] (nu : ℝ) (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (S : ScaleSelection) (e : Vec d) :
    annealedGluedAverage hnu P S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e) -
        testVector nu S.LPrime P S.n e =
      ∫ omega : ShellSeq d,
        volumeAverageVec (openCubeSet (originCube d (S.n : ℤ)))
          (fun x => gluedGradientField hnu S.ell S.n S.m
              (fluxSlot nu S.LPrime P S.n e) omega x -
            gluedGradientField hnu S.LPrime S.n S.m
              (fluxSlot nu S.LPrime P S.n e) omega x) ∂P.toMeasure := by
  have hnm : S.n ≤ S.m := by
    have h1 := S.n_add_a
    have h2 := S.ell_add_a
    have h3 := S.ellPrime_add_h
    omega
  have hxT : ∀ (omega : ShellSeq d) (i : Fin d), MeasureTheory.Integrable
      (fun x : Vec d => gluedGradientField hnu S.ell S.n S.m
        (fluxSlot nu S.LPrime P S.n e) omega x i)
      (MeasureTheory.volume.restrict (openCubeSet (originCube d (S.n : ℤ)))) :=
    fun omega i => integrable_component_gluedGradientField hnu S.ell S.n S.m
      (fluxSlot nu S.LPrime P S.n e) omega (originCube d (S.n : ℤ)) i
  have hxN : ∀ (omega : ShellSeq d) (i : Fin d), MeasureTheory.Integrable
      (fun x : Vec d => gluedGradientField hnu S.LPrime S.n S.m
        (fluxSlot nu S.LPrime P S.n e) omega x i)
      (MeasureTheory.volume.restrict (openCubeSet (originCube d (S.n : ℤ)))) :=
    fun omega i => integrable_component_gluedGradientField hnu S.LPrime S.n S.m
      (fluxSlot nu S.LPrime P S.n e) omega (originCube d (S.n : ℤ)) i
  have hsub : ∀ omega : ShellSeq d,
      volumeAverageVec (openCubeSet (originCube d (S.n : ℤ)))
        (fun x => gluedGradientField hnu S.ell S.n S.m
            (fluxSlot nu S.LPrime P S.n e) omega x -
          gluedGradientField hnu S.LPrime S.n S.m
            (fluxSlot nu S.LPrime P S.n e) omega x) =
      volumeAverageVec (openCubeSet (originCube d (S.n : ℤ)))
          (gluedGradientField hnu S.ell S.n S.m
            (fluxSlot nu S.LPrime P S.n e) omega) -
        volumeAverageVec (openCubeSet (originCube d (S.n : ℤ)))
          (gluedGradientField hnu S.LPrime S.n S.m
            (fluxSlot nu S.LPrime P S.n e) omega) :=
    fun omega => volumeAverageVec_sub (hxT omega) (hxN omega)
  have hAT : MeasureTheory.Integrable (fun omega : ShellSeq d =>
      volumeAverageVec (openCubeSet (originCube d (S.n : ℤ)))
        (gluedGradientField hnu S.ell S.n S.m
          (fluxSlot nu S.LPrime P S.n e) omega)) P.toMeasure :=
    integrable_annealedGluedAverage hnu S.ell S.n S.m hnm
      (fluxSlot nu S.LPrime P S.n e) hPrefix hJ2 hJ3 hJ4
  have hAN : MeasureTheory.Integrable (fun omega : ShellSeq d =>
      volumeAverageVec (openCubeSet (originCube d (S.n : ℤ)))
        (gluedGradientField hnu S.LPrime S.n S.m
          (fluxSlot nu S.LPrime P S.n e) omega)) P.toMeasure :=
    integrable_annealedGluedAverage hnu S.LPrime S.n S.m hnm
      (fluxSlot nu S.LPrime P S.n e) hPrefix hJ2 hJ3 hJ4
  have hfun : (fun omega : ShellSeq d => volumeAverageVec
        (openCubeSet (originCube d (S.n : ℤ)))
          (fun x => gluedGradientField hnu S.ell S.n S.m
              (fluxSlot nu S.LPrime P S.n e) omega x -
            gluedGradientField hnu S.LPrime S.n S.m
              (fluxSlot nu S.LPrime P S.n e) omega x))
      = fun omega : ShellSeq d => volumeAverageVec
          (openCubeSet (originCube d (S.n : ℤ)))
          (gluedGradientField hnu S.ell S.n S.m
            (fluxSlot nu S.LPrime P S.n e) omega) -
        volumeAverageVec (openCubeSet (originCube d (S.n : ℤ)))
          (gluedGradientField hnu S.LPrime S.n S.m
            (fluxSlot nu S.LPrime P S.n e) omega) := by
    funext omega
    exact hsub omega
  rw [← integral_volumeAverageVec_gluedGradientField_eq_testVector hnu hPrefix hJ2
    hJ3 hJ4 S.LPrime hnm e (originCube_mem_largeCubeSubcubes hnm)
    (integrable_sigmaStarInvCoarse hnu hPrefix hJ2 hJ3 hJ4 S.LPrime
      (originCube d (S.n : ℤ))), annealedGluedAverage_eq, hfun,
    MeasureTheory.integral_sub hAT hAN]

end MeanDefect

end

end SuperdiffusionCLT.Section3.Terms