/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.RemShape
public import SuperdiffusionCLT.Section2.Localization.Conj3Assembly
public import SuperdiffusionCLT.Section2.Localization.SkewRemainderVariational
public import SuperdiffusionCLT.Section2.Localization.CutoffComparison

/-!
# The four hypotheses of the printed QUADRATIC bound, discharged

`RemShape` states both printed remainder shapes at our carriers.  The linear
display (L1) is proved outright.  The **quadratic** bound on the pure-skew piece
`Z̃₁ = ½(0, h(∇ũ + ∇ũ*))` was reduced there to **four named
hypotheses**.

This module copies those four shapes at the route's carriers and proves the first
three of them.

## The printed derivation, in full

The paper, read verbatim, splits the perturbed minimizer:

> Now write
> `\tilde Z = ½(∇ũ+∇ũ*, ã∇ũ − ãᵗ∇ũ*) + ½(0, h(∇ũ+∇ũ*))`,

the two summands being `\tilde Z_0` and `\tilde Z_1`, the first slot of `\tilde
Z_1` being literally `0`.  Then

> By the definition of `η`,
> `‖𝐀^{1/2}\tilde Z_1‖²_{L²(U)} ≤ C‖s^{-1/2}h(∇ũ+∇ũ*)‖²_{L²(U)}
> ≤ Cη²(‖s^{1/2}∇ũ‖² + ‖s^{1/2}∇ũ*‖²) ≤ Cη² P·𝐀(U;ã)P`.

The **definition of `η`** is the pointwise relative-ratio estimate
`e.minimizers.pointwise.ratio`, cited there to the proof of
Lemma `l.localization.A`, not reproved:

> `‖𝐀^{-½}Ã𝐀^{-½} − I‖_{L^∞(U)} + ‖Ã^{-½}𝐀Ã^{-½} − I‖_{L^∞(U)} ≤ Cη`.

Correspondence of the four hypotheses to printed steps:

* `hbound` (the relative-skew bilinear estimate
  `2 R·(H x P) ≤ θ(P·s_A x P + R·s_A x R)`).  The paper
  **cites** this (`e.minimizers.pointwise.ratio`); it is the "definition of `η`"
  that the chain below invokes.  At our carriers it is the window operator
  bound on the skew increment and is **proved** by
  `relSkewBound_centeredCutoffPair_window`.
* `hIntR` — the `L²(U)` norm on the first line of the chain.  The paper
  writes an `L²` norm without checking measurability or finiteness; the averaged
  statement must name it.  Proved here from `L²` membership of the route fields.
* `hIntS` — the `L²(U)` norm on `‖s^{1/2}∇ũ‖²` in the middle line of
  the chain.  Same status.  Proved here from `s = ν Id`.
* `henergy` — the last line of the chain, `≤ Cη² P·𝐀(U;ã)P`.  The paper
  derives it from the energy identity `e.minimizers.energy.vs.bfA`, which it
  **proves** earlier.  It is not restated in this module.

## Main results

* `hbound_centeredCutoffPair_window`, `hIntR_centeredCutoffPair_window`,
  `hIntS_centeredCutoffPair_window` — three of the four printed hypotheses, at the
  route's carriers, each proved.

Everything is averaged: every bound is a `volumeAverage` over `U`.  No statement
is pointwise.  Dimension one is out of scope.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open Homogenization
open Homogenization.Book.Ch02
open MeasureTheory
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## `L²` bookkeeping at the route's fields -/

/-- The potential slot of an admissible doubled field is `L²`.  Copied locally
because the corresponding lemma of `AveragedRemainderProof` is private to its
module. -/
private theorem memVectorL2_potential_local {d : ℕ} {U : Book.Ch02.Domain d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn (U : Set (Vec d)))]
    {P : BlockVec d} {X : Book.Ch02.DoubledField d}
    (hX : Book.Ch02.IsDoubledMuAdmissible U P X) :
    MemVectorL2 (U : Set (Vec d)) X.potential := by
  have h := (MeasureTheory.memLp_const (μ := volumeMeasureOn (U : Set (Vec d)))
    (c := P.1) (p := 2)).add hX.1.1
  have heq : ((fun _ : Vec d => P.1) + fun x => X.potential x - P.1) = X.potential := by
    funext x
    simp only [Pi.add_apply]
    abel
  rwa [heq] at h

/-- The route's centered-pair doubled field is a doubled minimizer at `(−p, q)`. -/
private theorem routeDoubledFieldL_minimizer_local {d : ℕ}
    (U : Book.Ch02.Domain d) (nu : ℝ) (hnu : 0 < nu) (omega : ShellSeq d) (m L : ℕ)
    (hmL : m ≤ L) (p q : Vec d)
    (u : AHarmonicFunction (centeredPairField nu omega m L (U : Set (Vec d)))
      (U : Set (Vec d)))
    (hu : Homogenization.IsResponseMaximizer (U : Set (Vec d)) p q
      (centeredPairField nu omega m L (U : Set (Vec d))) u) :
    Book.Ch02.IsDoubledMuMinimizer U (centeredPairCoeffOn U nu hnu omega m L hmL) (-p, q)
      (routeDoubledFieldL U nu hnu omega m L hmL p q u) :=
  doubledFieldOfScalarMaximizers_isDoubledMuMinimizer
    (centeredPairCoeffOn U nu hnu omega m L hmL) p q u
    (transposeResponseMaximizer U (centeredPairCoeffOn U nu hnu omega m L hmL) p (-q)) hu
    (transposeResponseMaximizer_isMaximizer U (centeredPairCoeffOn U nu hnu omega m L hmL) p (-q))

/-- The skew remainder times an `L²` vector field is `L²`: write it as the
difference of the two coefficient fields acting on the field. -/
private theorem memVectorL2_skewRemainder_mul_local {d : ℕ} (U : Book.Ch02.Domain d)
    (nu : ℝ) (hnu : 0 < nu) (omega : ShellSeq d) (m L : ℕ) (hmL : m ≤ L)
    {r : Vec d → Vec d} (hr : MemVectorL2 (U : Set (Vec d)) r) :
    MemVectorL2 (U : Set (Vec d))
      (fun x => matVecMul (conj3SkewRemainderField nu omega m L (U : Set (Vec d)) x) (r x)) := by
  have hAt : MemVectorL2 (U : Set (Vec d))
      (fun x => matVecMul ((centeredPairCoeffOn U nu hnu omega m L hmL).toCoeffField x)
        (r x)) :=
    memVectorL2_matVecMul_coeffOn (centeredPairCoeffOn U nu hnu omega m L hmL) hr
  have hA : MemVectorL2 (U : Set (Vec d))
      (fun x => matVecMul ((levelMCoeffOn U nu hnu omega m).toCoeffField x) (r x)) :=
    memVectorL2_matVecMul_coeffOn (levelMCoeffOn U nu hnu omega m) hr
  have hsub := hAt.sub hA
  have hfun : (fun x => matVecMul
        (conj3SkewRemainderField nu omega m L (U : Set (Vec d)) x) (r x)) =
      (fun x => matVecMul ((centeredPairCoeffOn U nu hnu omega m L hmL).toCoeffField x) (r x) -
        matVecMul ((levelMCoeffOn U nu hnu omega m).toCoeffField x) (r x)) := by
    funext x
    rw [conj3SkewRemainderField, centeredPairCoeffOn_toCoeffField, levelMCoeffOn_toCoeffField]
    exact sub_matVecMul _ _ _
  rw [hfun]
  exact hsub

/-- The pure-skew piece is `L²` when its shift slot is. -/
private theorem memBlockL2_pureSkewPiece_local {d : ℕ} (U : Book.Ch02.Domain d)
    (nu : ℝ) (hnu : 0 < nu) (omega : ShellSeq d) (m L : ℕ) (hmL : m ≤ L) (p q : Vec d)
    (u : AHarmonicFunction (centeredPairField nu omega m L (U : Set (Vec d)))
      (U : Set (Vec d)))
    (hr : MemVectorL2 (U : Set (Vec d))
      (fun x => (routeDoubledFieldL U nu hnu omega m L hmL p q u).potential x)) :
    MemBlockL2 (U : Set (Vec d))
      (fun x => conj3PureSkewPiece U nu hnu omega m L hmL p q u x) := by
  have hHr := memVectorL2_skewRemainder_mul_local U nu hnu omega m L hmL hr
  have h := memBlockL2_blockField
    (MeasureTheory.MemLp.zero : MemVectorL2 (U : Set (Vec d)) (fun _ : Vec d => (0 : Vec d)))
    hHr
  have hfun : blockField (0 : Vec d → Vec d)
      (fun x => matVecMul (conj3SkewRemainderField nu omega m L (U : Set (Vec d)) x)
        ((routeDoubledFieldL U nu hnu omega m L hmL p q u).potential x)) =
      (fun x => conj3PureSkewPiece U nu hnu omega m L hmL p q u x) := by
    funext x
    rfl
  rwa [hfun] at h

/-! ## The four printed hypotheses, proved at the route's carriers -/

/-- **`hbound` at the route's cutoff pair.**  The relative-skew
bilinear estimate with `θ = cutoffPairThetaWindow`, read at the skew remainder
`H = â − a_m` and the base symmetric part `s_A = symmPart a_m = ν Id`.  The paper
cites this step to Lemma `l.localization.A`; here it is the window operator bound
`relSkewBound_centeredCutoffPair_window`. -/
theorem hbound_centeredCutoffPair_window {d : ℕ} (U : Book.Ch02.Domain d) (nu : ℝ)
    (hnu : 0 < nu) (omega : ShellSeq d) (n m L : ℕ) (hmL : m ≤ L)
    (hU : (U : Set (Vec d)) ⊆ openCubeSet (originCube d (n : ℤ))) :
    ∀ x ∈ (U : Set (Vec d)), ∀ P R : Vec d,
      2 * vecDot R
          (matVecMul (conj3SkewRemainderField nu omega m L (U : Set (Vec d)) x) P) ≤
        cutoffPairThetaWindow d nu n m L omega *
          (vecDot P (matVecMul
                (symmPart ((coefficientCutoff nu omega m).toCoeffField x)) P) +
            vecDot R (matVecMul
                (symmPart ((coefficientCutoff nu omega m).toCoeffField x)) R)) := by
  intro x hx P R
  simpa only [conj3SkewRemainderField] using
    relSkewBound_centeredCutoffPair_window nu omega m L n hmL hnu U hU x hx P R

/-- **`hIntR`, first line of the chain, at the route's cutoff pair.**  The
averaged block quadratic of the pure-skew piece against the base field is
integrable.  The paper writes an `L²` norm here without naming the condition;
it is proved from `L²` membership of the route's potential slot. -/
theorem hIntR_centeredCutoffPair_window {d : ℕ} (U : Book.Ch02.Domain d) (nu : ℝ)
    (hnu : 0 < nu) (omega : ShellSeq d) (m L : ℕ) (hmL : m ≤ L) (p q : Vec d)
    (u : AHarmonicFunction (centeredPairField nu omega m L (U : Set (Vec d)))
      (U : Set (Vec d)))
    (hu : Homogenization.IsResponseMaximizer (U : Set (Vec d)) p q
      (centeredPairField nu omega m L (U : Set (Vec d))) u) :
    IntegrableOn (fun x => averagedBlockQuadratic
      ((coefficientCutoff nu omega m).toCoeffField x)
      (conj3PureSkewPiece U nu hnu omega m L hmL p q u x)) (U : Set (Vec d)) := by
  have hZt := routeDoubledFieldL_minimizer_local U nu hnu omega m L hmL p q u hu
  have hr : MemVectorL2 (U : Set (Vec d))
      (fun x => (routeDoubledFieldL U nu hnu omega m L hmL p q u).potential x) :=
    memVectorL2_potential_local hZt.1
  have hY := memBlockL2_pureSkewPiece_local U nu hnu omega m L hmL p q u hr
  simpa only [levelMCoeffOn_toCoeffField] using
    integrableOn_averagedBlockQuadratic_of_memBlockL2 (levelMCoeffOn U nu hnu omega m) hY

/-- **`hIntS`, middle line of the chain, at the route's cutoff pair.**  The
`s`-energy of the shift slot is integrable, `s_A = ν Id` reducing it to
`ν ‖r‖²`.  Same status as `hIntR`: the paper's `L²` norm is made explicit. -/
theorem hIntS_centeredCutoffPair_window {d : ℕ} (U : Book.Ch02.Domain d) (nu : ℝ)
    (hnu : 0 < nu) (omega : ShellSeq d) (m L : ℕ) (hmL : m ≤ L) (p q : Vec d)
    (u : AHarmonicFunction (centeredPairField nu omega m L (U : Set (Vec d)))
      (U : Set (Vec d)))
    (hu : Homogenization.IsResponseMaximizer (U : Set (Vec d)) p q
      (centeredPairField nu omega m L (U : Set (Vec d))) u) :
    IntegrableOn (fun x => vecDot
      ((routeDoubledFieldL U nu hnu omega m L hmL p q u).potential x)
      (matVecMul (symmPart ((coefficientCutoff nu omega m).toCoeffField x))
        ((routeDoubledFieldL U nu hnu omega m L hmL p q u).potential x)))
      (U : Set (Vec d)) := by
  have hZt := routeDoubledFieldL_minimizer_local U nu hnu omega m L hmL p q u hu
  have hr : MemVectorL2 (U : Set (Vec d))
      (fun x => (routeDoubledFieldL U nu hnu omega m L hmL p q u).potential x) :=
    memVectorL2_potential_local hZt.1
  have hfun : (fun x => vecDot
        ((routeDoubledFieldL U nu hnu omega m L hmL p q u).potential x)
        (matVecMul (symmPart ((coefficientCutoff nu omega m).toCoeffField x))
          ((routeDoubledFieldL U nu hnu omega m L hmL p q u).potential x))) =
      (fun x => nu * vecNormSq
        ((routeDoubledFieldL U nu hnu omega m L hmL p q u).potential x)) := by
    funext x
    have hsymm : symmPart ((coefficientCutoff nu omega m).toCoeffField x) =
        nu • (1 : Mat d) := symmPart_coefficientCutoff nu omega m x
    rw [hsymm]
    exact vecDot_smul_one_self nu _
  rw [hfun]
  exact (integrableOn_vecDot_of_memVectorL2 hr hr).const_mul nu

end

end SuperdiffusionCLT.Section2.Localization
