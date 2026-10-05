/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.GradientFromBlock
public import SuperdiffusionCLT.Section2.Localization.SlopeBoundRoute
public import SuperdiffusionCLT.Section2.Localization.Conj3BridgeIdentity
public import Homogenization.Sobolev.Foundations.ZeroTraceAverages
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Consuming the deterministic bound: linear at the minimizer's own energy

## The question and the answer

The third conjunct of `Frozen.Section2.cutoff_localization` bounds the
mean squared slope `⍍_U ‖∇u − ∇v‖²` by

`C ν⁻² 3ⁿ W · (R_pert + R_base + 2 p·q)`,

where `R_pert = ResponseJ U p q (centeredPairField …)`,
`R_base = ResponseJ U p q (coefficientCutoff ν ω m)` and `W` is the shell
derivative supremum.  The printed chain in the proof of
`e.minimizers.gradient.from.block` ends at a **linear** bound in the window
amplitude (`e.minimizers.deterministic`).

The linear bound is needed in the right energy reading.  The bound that the
right-hand side consumes is the linear display read at the *minimizer's own*
averaged block energy, `e.minimizers.energy.vs.bfA` composed with
`e.Jaas.matform`.  That is `conj3ShiftedPairLinearMin_cutoff` below.  A bound
that carries the *constant loading* energies
`⍍_U (−p,q)·(−p,q)_{a_m}` and `⍍_U (−p,q)·(−p,q)_{ã}` instead would need the
*reverse* of the printed half of `e.CG.bounds.2`, an identity which is false in
general; the printed direction alone only bounds the right-hand side by half the
sum of the two constant-loading energies, which is the wrong direction.

## Main results

* `linearDisplayMin_of_gap_ratio` — the paper's linear display, in the proof of
  `e.minimizers.gradient.from.block`, at the energies of the two fields
  themselves rather than at a constant loading: the two gap identities, the two
  coefficient-ratio sandwiches and the integrability family give
  `⍍A D·D + ⍍Ã D·D ≤ η (⍍A Z·Z + ⍍Ã Zt·Zt)`.
  It needs no remainder slot and no quadratic input.
* `conj3ShiftedPairLinearMin_cutoff` — the same at the two forward
  maximizers, every premise proved.

Everything is averaged; nothing pointwise is assumed; dimension one is out of
scope. -/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open Homogenization
open Homogenization.Book.Ch02
open MeasureTheory
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

/-! ## Local averaging bookkeeping -/

/-- Pulling a constant multiple out of a volume average, in the additive form
the coefficient-ratio monotonicity needs (`Conj3AveragedClose`'s private copy). -/
private theorem volumeAverage_add_const_mul_dc {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] {f : Vec d → ℝ}
    (hf : IntegrableOn f U) (c : ℝ) :
    volumeAverage U (fun x => f x + c * f x) =
      volumeAverage U f + c * volumeAverage U f := by
  rw [show (fun x : Vec d => f x + c * f x) = f + c • f by
    funext x
    simp]
  calc
    volumeAverage U (f + c • f) =
        volumeAverage U f + volumeAverage U (c • f) :=
      Homogenization.volumeAverage_add hf (hf.const_mul c)
    _ = volumeAverage U f + c * volumeAverage U f := by
      rw [Homogenization.volumeAverage_smul]

/-- The block field of an admissible doubled field is `L²` (`RemShape`'s private
copy, so that the integrability inputs below are discharged rather than assumed). -/
private theorem memBlockL2_eval_of_doubledAdmissible_dc {d : ℕ}
    {U : Book.Ch02.Domain d} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn (U : Set (Vec d)))]
    {P : BlockVec d} {X : Book.Ch02.DoubledField d}
    (hX : Book.Ch02.IsDoubledMuAdmissible U P X) :
    MemBlockL2 (U : Set (Vec d)) (fun x => X.eval x) := by
  have hconst : ∀ v : Vec d, MemVectorL2 (U : Set (Vec d)) (fun _ : Vec d => v) :=
    fun v => MeasureTheory.memLp_const (μ := volumeMeasureOn (U : Set (Vec d)))
      (c := v) (p := 2)
  have hp : MemVectorL2 (U : Set (Vec d)) X.potential := by
    have h := (hconst P.1).add hX.1.1
    have heq : ((fun _ : Vec d => P.1) + fun x => X.potential x - P.1) = X.potential := by
      funext x
      simp only [Pi.add_apply]
      abel
    rwa [heq] at h
  have hq : MemVectorL2 (U : Set (Vec d)) X.flux := by
    have h := (hconst P.2).add hX.2.1
    have heq : ((fun _ : Vec d => P.2) + fun x => X.flux x - P.2) = X.flux := by
      funext x
      simp only [Pi.add_apply]
      abel
    rwa [heq] at h
  exact Homogenization.memBlockL2_blockField hp hq

/-! ## (L1) at the energies of the fields themselves -/

/-- **(L1) with the maximality step removed.**  The two averaged gap identities
(the first variations), the two coefficient-ratio sandwiches
and the four integrability conditions give, *without* weakening
either side through a constant loading,

`⍍_U A D·D + ⍍_U Ã D·D ≤ η (⍍_U A Z·Z + ⍍_U Ã Zt·Zt)`.

This derivation uses no remainder slot, no quadratic input, and no
`hmaxA`/`hmaxAt`.  The right-hand side is read at the fields themselves, which is
what `e.minimizers.energy.vs.bfA` supplies at the route's carriers. -/
theorem linearDisplayMin_of_gap_ratio {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {A At : Vec d → Mat d} {Z Zt D : Vec d → BlockVec d} {eta : ℝ}
    (hU : MeasurableSet U)
    (hgapA : averagedBlockQuadraticOn U A D =
      averagedBlockQuadraticOn U A Zt - averagedBlockQuadraticOn U A Z)
    (hgapAt : averagedBlockQuadraticOn U At D =
      averagedBlockQuadraticOn U At Z - averagedBlockQuadraticOn U At Zt)
    (hratioA : ∀ x ∈ U, ∀ W : BlockVec d,
      averagedBlockQuadratic (A x) W ≤
        averagedBlockQuadratic (At x) W + eta * averagedBlockQuadratic (At x) W)
    (hratioAt : ∀ x ∈ U, ∀ W : BlockVec d,
      averagedBlockQuadratic (At x) W ≤
        averagedBlockQuadratic (A x) W + eta * averagedBlockQuadratic (A x) W)
    (hIntAZ : IntegrableOn (fun x => averagedBlockQuadratic (A x) (Z x)) U)
    (hIntAtZ : IntegrableOn (fun x => averagedBlockQuadratic (At x) (Z x)) U)
    (hIntAZt : IntegrableOn (fun x => averagedBlockQuadratic (A x) (Zt x)) U)
    (hIntAtZt : IntegrableOn (fun x => averagedBlockQuadratic (At x) (Zt x)) U) :
    averagedBlockQuadraticOn U A D + averagedBlockQuadraticOn U At D ≤
      eta * (averagedBlockQuadraticOn U A Z + averagedBlockQuadraticOn U At Zt) := by
  have hRA : averagedBlockQuadraticOn U A Zt ≤
      averagedBlockQuadraticOn U At Zt + eta * averagedBlockQuadraticOn U At Zt := by
    have hmono := Homogenization.volumeAverage_le_volumeAverage_of_le_on hU hIntAZt
      (hIntAtZt.fun_add (hIntAtZt.const_mul eta)) (by
        intro x hx
        simpa [averagedBlockQuadratic] using hratioA x hx (Zt x))
    calc
      averagedBlockQuadraticOn U A Zt ≤
          volumeAverage U (fun x => averagedBlockQuadratic (At x) (Zt x) +
            eta * averagedBlockQuadratic (At x) (Zt x)) := hmono
      _ = averagedBlockQuadraticOn U At Zt +
          eta * averagedBlockQuadraticOn U At Zt :=
        volumeAverage_add_const_mul_dc hIntAtZt eta
  have hRAt : averagedBlockQuadraticOn U At Z ≤
      averagedBlockQuadraticOn U A Z + eta * averagedBlockQuadraticOn U A Z := by
    have hmono := Homogenization.volumeAverage_le_volumeAverage_of_le_on hU hIntAtZ
      (hIntAZ.fun_add (hIntAZ.const_mul eta)) (by
        intro x hx
        simpa [averagedBlockQuadratic] using hratioAt x hx (Z x))
    calc
      averagedBlockQuadraticOn U At Z ≤
          volumeAverage U (fun x => averagedBlockQuadratic (A x) (Z x) +
            eta * averagedBlockQuadratic (A x) (Z x)) := hmono
      _ = averagedBlockQuadraticOn U A Z +
          eta * averagedBlockQuadraticOn U A Z :=
        volumeAverage_add_const_mul_dc hIntAZ eta
  linarith only [hgapA, hgapAt, hRA, hRAt]

/-! ## Route helpers: the two doubled minimizers and (L1) at their energies -/

/-- The level-`m` route doubled field is a doubled minimizer at `(−p, q)`. -/
private theorem routeDoubledFieldM_isDoubledMuMinimizer_dc {d : ℕ}
    (U : Book.Ch02.Domain d) (nu : ℝ) (hnu : 0 < nu) (omega : ShellSeq d) (m : ℕ)
    (p q : Vec d)
    (v : AHarmonicFunction (coefficientCutoff nu omega m).toCoeffField (U : Set (Vec d)))
    (hv : Homogenization.IsResponseMaximizer (U : Set (Vec d)) p q
      (coefficientCutoff nu omega m).toCoeffField v) :
    Book.Ch02.IsDoubledMuMinimizer U (levelMCoeffOn U nu hnu omega m) (-p, q)
      (forwardDoubledField U (levelMCoeffOn U nu hnu omega m) p q v) :=
  doubledFieldOfScalarMaximizers_isDoubledMuMinimizer (levelMCoeffOn U nu hnu omega m) p q v
    (transposeResponseMaximizer U (levelMCoeffOn U nu hnu omega m) p (-q)) hv
    (transposeResponseMaximizer_isMaximizer U (levelMCoeffOn U nu hnu omega m) p (-q))

/-- The centered-pair route doubled field is a doubled minimizer at `(−p, q)`. -/
private theorem routeDoubledFieldL_isDoubledMuMinimizer_dc {d : ℕ}
    (U : Book.Ch02.Domain d) (nu : ℝ) (hnu : 0 < nu) (omega : ShellSeq d) (m L : ℕ)
    (hmL : m ≤ L) (p q : Vec d)
    (u : AHarmonicFunction (centeredPairField nu omega m L (U : Set (Vec d)))
      (U : Set (Vec d)))
    (hu : Homogenization.IsResponseMaximizer (U : Set (Vec d)) p q
      (centeredPairField nu omega m L (U : Set (Vec d))) u) :
    Book.Ch02.IsDoubledMuMinimizer U (centeredPairCoeffOn U nu hnu omega m L hmL) (-p, q)
      (forwardDoubledField U (centeredPairCoeffOn U nu hnu omega m L hmL) p q u) :=
  doubledFieldOfScalarMaximizers_isDoubledMuMinimizer
    (centeredPairCoeffOn U nu hnu omega m L hmL) p q u
    (transposeResponseMaximizer U (centeredPairCoeffOn U nu hnu omega m L hmL) p (-q)) hu
    (transposeResponseMaximizer_isMaximizer U (centeredPairCoeffOn U nu hnu omega m L hmL)
      p (-q))

/-- **(L1) at the route's shifted difference, read at the minimizers' own
energies.**  At the two route doubled fields, the paper's linear display
(in the proof of `e.minimizers.gradient.from.block`) holds with the right-hand
side read at `Z` and `Zt` themselves:

`⍍ (Z − Zt)·(Z − Zt)_{a_m} + ⍍ (Z − Zt)·(Z − Zt)_{ã}
  ≤ η (⍍ Z·Z_{a_m} + ⍍ Zt·Zt_{ã})`.

Every premise is proved: the two first variations by
`conj3ShiftedPairRemainder_gap_cutoff`, the two ratio sandwiches
by the window lemmas of `Conj3RatioSandwich`, and the four
integrability conditions by admissibility of the two doubled minimizers.  No
maximality step, no constant loading and no quadratic remainder is consulted;
`m ≤ L` plus the cube containment are the only structural inputs. -/
theorem conj3ShiftedPairLinearMin_cutoff {d : ℕ} (U : Book.Ch02.Domain d) (nu : ℝ)
    (hnu : 0 < nu) (omega : ShellSeq d) (n m L : ℕ) (hmL : m ≤ L)
    (hU : (U : Set (Vec d)) ⊆ openCubeSet (originCube d (n : ℤ))) (p q : Vec d)
    (v : AHarmonicFunction (coefficientCutoff nu omega m).toCoeffField (U : Set (Vec d)))
    (hv : Homogenization.IsResponseMaximizer (U : Set (Vec d)) p q
      (coefficientCutoff nu omega m).toCoeffField v)
    (u : AHarmonicFunction (centeredPairField nu omega m L (U : Set (Vec d)))
      (U : Set (Vec d)))
    (hu : Homogenization.IsResponseMaximizer (U : Set (Vec d)) p q
      (centeredPairField nu omega m L (U : Set (Vec d))) u) :
    averagedBlockQuadraticOn (U : Set (Vec d))
        (fun x => (coefficientCutoff nu omega m).toCoeffField x)
        (conj3ShiftedPairRemainder U nu hnu omega m L hmL p q v u) +
      averagedBlockQuadraticOn (U : Set (Vec d))
        (fun x => centeredPairField nu omega m L (U : Set (Vec d)) x)
        (conj3ShiftedPairRemainder U nu hnu omega m L hmL p q v u) ≤
      cutoffPairEtaWindow d nu n m L omega *
        (averagedBlockQuadraticOn (U : Set (Vec d))
            (fun x => (coefficientCutoff nu omega m).toCoeffField x)
            (fun x => (forwardDoubledField U (levelMCoeffOn U nu hnu omega m) p q v).eval x) +
          averagedBlockQuadraticOn (U : Set (Vec d))
            (fun x => centeredPairField nu omega m L (U : Set (Vec d)) x)
            (fun x => (forwardDoubledField U
              (centeredPairCoeffOn U nu hnu omega m L hmL) p q u).eval x)) := by
  have hgap := conj3ShiftedPairRemainder_gap_cutoff U nu hnu omega m L hmL p q v hv u hu
  have hZ := routeDoubledFieldM_isDoubledMuMinimizer_dc U nu hnu omega m p q v hv
  have hZt := routeDoubledFieldL_isDoubledMuMinimizer_dc U nu hnu omega m L hmL p q u hu
  have hZmem := memBlockL2_eval_of_doubledAdmissible_dc hZ.1
  have hZtmem := memBlockL2_eval_of_doubledAdmissible_dc hZt.1
  exact linearDisplayMin_of_gap_ratio
    (A := fun x => (coefficientCutoff nu omega m).toCoeffField x)
    (At := fun x => centeredPairField nu omega m L (U : Set (Vec d)) x)
    (Z := fun x => (forwardDoubledField U (levelMCoeffOn U nu hnu omega m) p q v).eval x)
    (Zt := fun x => (forwardDoubledField U
      (centeredPairCoeffOn U nu hnu omega m L hmL) p q u).eval x)
    (D := conj3ShiftedPairRemainder U nu hnu omega m L hmL p q v u)
    (eta := cutoffPairEtaWindow d nu n m L omega)
    U.measurableSet hgap.1 hgap.2
    (hratioA_centeredCutoffPair_window U nu hnu omega n m L hmL hU)
    (hratioAt_centeredCutoffPair_window U nu hnu omega n m L hmL hU)
    (integrableOn_averagedBlockQuadratic_of_memBlockL2 (levelMCoeffOn U nu hnu omega m) hZmem)
    (integrableOn_averagedBlockQuadratic_of_memBlockL2
      (centeredPairCoeffOn U nu hnu omega m L hmL) hZmem)
    (integrableOn_averagedBlockQuadratic_of_memBlockL2 (levelMCoeffOn U nu hnu omega m) hZtmem)
    (integrableOn_averagedBlockQuadratic_of_memBlockL2
      (centeredPairCoeffOn U nu hnu omega m L hmL) hZtmem)

end

end SuperdiffusionCLT.Section2.Localization
