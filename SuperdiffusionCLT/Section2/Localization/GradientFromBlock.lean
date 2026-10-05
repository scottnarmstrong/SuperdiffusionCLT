/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.BlockScalarCorrespondence
public import SuperdiffusionCLT.Section2.Localization.CutoffComparison
public import SuperdiffusionCLT.Section2.Localization.Conj3CoincidentBranch
public import SuperdiffusionCLT.Section2.Localization.CutoffLocalizationAssembly
public import SuperdiffusionCLT.Section2.Localization.SkewQuadratic
public import SuperdiffusionCLT.Section2.Localization.SlopeBoundRoute
public import Homogenization.Sobolev.Foundations.ZeroTraceAverages
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# `e.minimizers.gradient.from.block` at the route's carriers

The printed bridging step of Step 2, `e.minimizers.gradient.from.block`,
applies the algebraic identity `e.iden.AP` to the **split**

`Z − Z̃₀ = (Z − Z̃) + Z̃₁`

of the block difference, where `Z̃ = Z̃₀ + Z̃₁` is the print's decomposition of
the perturbed doubled field into its symmetric part and its pure-skew piece
`Z̃₁ = ½ (0, h(∇ũ + ∇ũ*))`.  With the triangle inequality it
gives

`‖s^{1/2}(∇u − ∇ũ)‖² + ‖s^{1/2}(∇u* − ∇ũ*)‖²
   ≤ C ‖𝐀^{1/2}(Z − Z̃)‖² + C ‖𝐀^{1/2} Z̃₁‖²`.

`BlockScalarCorrespondence.lean` proves the two ingredients of the display
*pointwise and in general*: `e.iden.AP` itself
(`blockVecDot_blockMatrixOfCoeff_adjointPair`) and the two-term Cauchy split
(`blockVecDot_blockMatrixOfCoeff_add_le`).  What it
does not do is name the route's two summands and take the volume average.
That is what this module does.

## Main results

* `conj3SkewFreeField` — the print's `Z̃₀ = ½ (∇ũ + ∇ũ*, a ∇ũ − aᵗ ∇ũ*)` at the
  route's perturbed maximizer: the perturbed doubled field with its pure-skew
  piece removed.  Its second slot is the *base*-coefficient flux, which is why
  `e.iden.AP` applies to `Z − Z̃₀`.
* `conj3SkewFreeDifference` — the display's left-hand block object `Z − Z̃₀`.
* `conj3SkewFreeDifference_eq_split` — the print's split
  `Z − Z̃₀ = (Z − Z̃) + Z̃₁`, at the route's own carriers.
* `averagedBlockQuadraticOn_add_le` — the triangle inequality averaged over `U`.
* `conj3GradientFromBlock_cutoff` — **the printed bridge** at the route's two
  forward maximizers, with every input proved: ellipticity from
  `isEllipticMatrix_coefficientCutoff_domain`, integrability from admissibility.

The bridge bounds the block energy of `Z − Z̃₀`, the *symmetric* field whose block
energy is the gradient energy of the two slopes; it is *linear* at `Z − Z̃₀` and
involves the pure-skew piece `Z̃₁` only through its own quadratic energy.  Note
that `Z − Z̃ = (Z − Z̃₀) − Z̃₁` is a different object from `Z − Z̃₀`.  Everything
here is averaged; nothing is pointwise.
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

/-! ## The averaged triangle inequality for the block form -/

/-- **The triangle inequality of `e.minimizers.gradient.from.block` averaged over
`U`.**  If the coefficient field `A` is pointwise elliptic on `U` and the three
block quadratics are integrable, the volume average of the block form at a sum
is at most twice the sum of the averages of its two summands.  This is
`BlockScalarCorrespondence.blockVecDot_blockMatrixOfCoeff_add_le` under the
integral, and it is the only inequality the printed bridge uses after
`e.iden.AP`. -/
theorem averagedBlockQuadraticOn_add_le {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] {A : Vec d → Mat d} {lam Lam : ℝ}
    (hU : MeasurableSet U) (hell : ∀ x ∈ U, IsEllipticMatrix lam Lam (A x))
    {X Y : Vec d → BlockVec d}
    (hX : IntegrableOn (fun x => averagedBlockQuadratic (A x) (X x)) U)
    (hY : IntegrableOn (fun x => averagedBlockQuadratic (A x) (Y x)) U)
    (hXY : IntegrableOn (fun x => averagedBlockQuadratic (A x) ((X + Y) x)) U) :
    averagedBlockQuadraticOn U A (X + Y) ≤
      2 * averagedBlockQuadraticOn U A X + 2 * averagedBlockQuadraticOn U A Y := by
  have hpoint : ∀ x ∈ U, averagedBlockQuadratic (A x) ((X + Y) x) ≤
      2 * averagedBlockQuadratic (A x) (X x) + 2 * averagedBlockQuadratic (A x) (Y x) := by
    intro x hx
    have h := blockVecDot_blockMatrixOfCoeff_add_le (hell x hx) (X x) (Y x)
    exact h
  have hup : IntegrableOn
      (fun x => 2 * averagedBlockQuadratic (A x) (X x) +
        2 * averagedBlockQuadratic (A x) (Y x)) U :=
    (hX.const_mul 2).add (hY.const_mul 2)
  have hmono := volumeAverage_le_volumeAverage_of_le_on hU hXY hup hpoint
  have hlin : volumeAverage U (fun x => 2 * averagedBlockQuadratic (A x) (X x) +
        2 * averagedBlockQuadratic (A x) (Y x)) =
      2 * volumeAverage U (fun x => averagedBlockQuadratic (A x) (X x)) +
        2 * volumeAverage U (fun x => averagedBlockQuadratic (A x) (Y x)) := by
    have e0 : (fun x : Vec d => 2 * averagedBlockQuadratic (A x) (X x) +
        2 * averagedBlockQuadratic (A x) (Y x)) =
        (fun x => 2 * averagedBlockQuadratic (A x) (X x)) +
          (fun x => 2 * averagedBlockQuadratic (A x) (Y x)) := by
      funext x
      simp only [Pi.add_apply]
    have e1 : (fun x : Vec d => 2 * averagedBlockQuadratic (A x) (X x)) =
        (2 : ℝ) • (fun x => averagedBlockQuadratic (A x) (X x)) := by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
    have e2 : (fun x : Vec d => 2 * averagedBlockQuadratic (A x) (Y x)) =
        (2 : ℝ) • (fun x => averagedBlockQuadratic (A x) (Y x)) := by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
    rw [e0, volumeAverage_add (hX.const_mul 2) (hY.const_mul 2), e1, e2,
      volumeAverage_smul, volumeAverage_smul]
  unfold averagedBlockQuadraticOn
  rw [hlin] at hmono
  exact hmono

/-- **The averaged block form is nonnegative under pointwise ellipticity.** -/
theorem averagedBlockQuadraticOn_nonneg_of_elliptic {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] {A : Vec d → Mat d} {lam Lam : ℝ}
    (hU : MeasurableSet U) (hell : ∀ x ∈ U, IsEllipticMatrix lam Lam (A x))
    {X : Vec d → BlockVec d} :
    0 ≤ averagedBlockQuadraticOn U A X := by
  unfold averagedBlockQuadraticOn
  exact volumeAverage_nonneg_of_nonneg_on hU
    (fun x hx => blockVecDot_blockMatrixOfCoeff_nonneg (hell x hx) (X x))

/-! ## The print's `Z̃₀` and the split at the route's carriers -/

/-- **The print's symmetric part `Z̃₀` of the perturbed doubled field**,
at the route's level-`L` maximizer: the perturbed doubled field with its pure-skew
piece removed.

The print writes `Z̃ = Z̃₀ + Z̃₁` with `Z̃₁ = ½ (0, h(∇ũ + ∇ũ*))` and
`h = a_L − a_m`; removing the skew piece from the second slot rewrites the
*perturbed* flux `ã ∇ũ − ãᵗ ∇ũ*` as the **base** flux `a ∇ũ − aᵗ ∇ũ*`, so
`Z̃₀` is exactly the adjoint pair of the perturbed gradients taken at the *base*
coefficient.  This is why `e.iden.AP` applies to `Z − Z̃₀`. -/
noncomputable def conj3SkewFreeField {d : ℕ} (U : Book.Ch02.Domain d) (nu : ℝ)
    (hnu : 0 < nu) (omega : ShellSeq d) (m L : ℕ) (hmL : m ≤ L) (p q : Vec d)
    (u : AHarmonicFunction (centeredPairField nu omega m L (U : Set (Vec d)))
      (U : Set (Vec d))) : Vec d → BlockVec d :=
  fun x => (routeDoubledFieldL U nu hnu omega m L hmL p q u).eval x -
    conj3PureSkewPiece U nu hnu omega m L hmL p q u x

/-- **The display's left-hand side `Z − Z̃₀`.**  The difference of the two route
doubled fields with the pure-skew piece *removed* from the perturbed one, i.e.
exactly the block vector to which the print applies `e.iden.AP`. -/
noncomputable def conj3SkewFreeDifference {d : ℕ} (U : Book.Ch02.Domain d) (nu : ℝ)
    (hnu : 0 < nu) (omega : ShellSeq d) (m L : ℕ) (hmL : m ≤ L) (p q : Vec d)
    (v : AHarmonicFunction (coefficientCutoff nu omega m).toCoeffField (U : Set (Vec d)))
    (u : AHarmonicFunction (centeredPairField nu omega m L (U : Set (Vec d)))
      (U : Set (Vec d))) : Vec d → BlockVec d :=
  fun x => (routeDoubledFieldM U nu hnu omega m p q v).eval x -
    conj3SkewFreeField U nu hnu omega m L hmL p q u x

/-- **The print's split `Z − Z̃₀ = (Z − Z̃) + Z̃₁`**, at the route's carriers.  A
pure additive rearrangement of the three definitions; it is the step the print
performs before applying the triangle inequality. -/
theorem conj3SkewFreeDifference_eq_split {d : ℕ} (U : Book.Ch02.Domain d) (nu : ℝ)
    (hnu : 0 < nu) (omega : ShellSeq d) (m L : ℕ) (hmL : m ≤ L) (p q : Vec d)
    (v : AHarmonicFunction (coefficientCutoff nu omega m).toCoeffField (U : Set (Vec d)))
    (u : AHarmonicFunction (centeredPairField nu omega m L (U : Set (Vec d)))
      (U : Set (Vec d))) :
    conj3SkewFreeDifference U nu hnu omega m L hmL p q v u =
      conj3ShiftedPairRemainder U nu hnu omega m L hmL p q v u +
        conj3PureSkewPiece U nu hnu omega m L hmL p q u := by
  funext x
  simp only [conj3SkewFreeDifference, conj3SkewFreeField, conj3ShiftedPairRemainder,
    Pi.add_apply]
  abel

/-! ## Local `L²` bookkeeping at the route's fields -/

/-- The potential of an admissible doubled field is `L²`. -/
private theorem memVectorL2_potential_of_doubledAdmissible_gfb {d : ℕ}
    {U : Book.Ch02.Domain d} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn (U : Set (Vec d)))]
    {P : BlockVec d} {X : Book.Ch02.DoubledField d}
    (hX : Book.Ch02.IsDoubledMuAdmissible U P X) :
    MemVectorL2 (U : Set (Vec d)) (fun x => X.potential x) := by
  have h := (MeasureTheory.memLp_const (μ := volumeMeasureOn (U : Set (Vec d)))
    (c := P.1) (p := 2)).add hX.1.1
  have heq : ((fun _ : Vec d => P.1) + fun x => X.potential x - P.1) =
      (fun x : Vec d => X.potential x) := by
    funext x
    simp only [Pi.add_apply]
    abel
  rwa [heq] at h

/-- The block field of an admissible doubled field is `L²`. -/
private theorem memBlockL2_eval_of_doubledAdmissible_gfb {d : ℕ}
    {U : Book.Ch02.Domain d} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn (U : Set (Vec d)))]
    {P : BlockVec d} {X : Book.Ch02.DoubledField d}
    (hX : Book.Ch02.IsDoubledMuAdmissible U P X) :
    MemBlockL2 (U : Set (Vec d)) (fun x => X.eval x) := by
  have hp := memVectorL2_potential_of_doubledAdmissible_gfb hX
  have hq : MemVectorL2 (U : Set (Vec d)) (fun x => X.flux x) := by
    have h := (MeasureTheory.memLp_const (μ := volumeMeasureOn (U : Set (Vec d)))
      (c := P.2) (p := 2)).add hX.2.1
    have heq : ((fun _ : Vec d => P.2) + fun x => X.flux x - P.2) =
        (fun x : Vec d => X.flux x) := by
      funext x
      simp only [Pi.add_apply]
      abel
    rwa [heq] at h
  exact memBlockL2_blockField hp hq

/-- The skew remainder acting on an `L²` vector field is `L²`. -/
private theorem memVectorL2_skewRemainder_mul_gfb {d : ℕ} (U : Book.Ch02.Domain d)
    (nu : ℝ) (hnu : 0 < nu) (omega : ShellSeq d) (m L : ℕ) (hmL : m ≤ L)
    {r : Vec d → Vec d} (hr : MemVectorL2 (U : Set (Vec d)) r) :
    MemVectorL2 (U : Set (Vec d))
      (fun x => matVecMul (conj3SkewRemainderField nu omega m L (U : Set (Vec d)) x) (r x)) := by
  have hAt : MemVectorL2 (U : Set (Vec d))
      (fun x => matVecMul ((centeredPairCoeffOn U nu hnu omega m L hmL).toCoeffField x) (r x)) :=
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

/-- The route's pure-skew piece is `L²`. -/
private theorem memBlockL2_pureSkewPiece_gfb {d : ℕ} (U : Book.Ch02.Domain d) (nu : ℝ)
    (hnu : 0 < nu) (omega : ShellSeq d) (m L : ℕ) (hmL : m ≤ L) (p q : Vec d)
    (u : AHarmonicFunction (centeredPairField nu omega m L (U : Set (Vec d))) (U : Set (Vec d)))
    (hr : MemVectorL2 (U : Set (Vec d))
      (fun x => (routeDoubledFieldL U nu hnu omega m L hmL p q u).potential x)) :
    MemBlockL2 (U : Set (Vec d))
      (fun x => conj3PureSkewPiece U nu hnu omega m L hmL p q u x) := by
  have hHr := memVectorL2_skewRemainder_mul_gfb U nu hnu omega m L hmL hr
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

/-! ## The printed bridge at the route's carriers -/

/-- **`e.minimizers.gradient.from.block` at the route's two
forward maximizers.**  The averaged block energy of `Z − Z̃₀` is at most twice the
sum of the averaged block energies of the two pieces of the print's split
`Z − Z̃₀ = (Z − Z̃) + Z̃₁`, at the base coefficient field `a_m`.

This is the triangle inequality of the display.  The two ingredients are
proved from the route's own data: the pointwise ellipticity of
`coefficientCutoff nu omega m` on `U`
(`isEllipticMatrix_coefficientCutoff_domain`), and the `L²` membership of the
three fields (the shifted pair remainder, the pure-skew piece, and their sum) from
admissibility of the two doubled minimizers.  The only inputs are the two
forward maximizers `v`, `u` that *define* `Z`, `Z̃`. -/
theorem conj3GradientFromBlock_cutoff {d : ℕ} (U : Book.Ch02.Domain d) (nu : ℝ)
    (hnu : 0 < nu) (omega : ShellSeq d) (m L : ℕ) (hmL : m ≤ L) (p q : Vec d)
    (v : AHarmonicFunction (coefficientCutoff nu omega m).toCoeffField (U : Set (Vec d)))
    (hv : Homogenization.IsResponseMaximizer (U : Set (Vec d)) p q
      (coefficientCutoff nu omega m).toCoeffField v)
    (u : AHarmonicFunction (centeredPairField nu omega m L (U : Set (Vec d)))
      (U : Set (Vec d)))
    (hu : Homogenization.IsResponseMaximizer (U : Set (Vec d)) p q
      (centeredPairField nu omega m L (U : Set (Vec d))) u) :
    averagedBlockQuadraticOn (U : Set (Vec d))
        (fun x => (coefficientCutoff nu omega m).toCoeffField x)
        (conj3SkewFreeDifference U nu hnu omega m L hmL p q v u) ≤
      2 * averagedBlockQuadraticOn (U : Set (Vec d))
        (fun x => (coefficientCutoff nu omega m).toCoeffField x)
        (conj3ShiftedPairRemainder U nu hnu omega m L hmL p q v u) +
      2 * averagedBlockQuadraticOn (U : Set (Vec d))
        (fun x => (coefficientCutoff nu omega m).toCoeffField x)
        (conj3PureSkewPiece U nu hnu omega m L hmL p q u) := by
  have hZ : Book.Ch02.IsDoubledMuMinimizer U (levelMCoeffOn U nu hnu omega m) (-p, q)
      (routeDoubledFieldM U nu hnu omega m p q v) :=
    doubledFieldOfScalarMaximizers_isDoubledMuMinimizer (levelMCoeffOn U nu hnu omega m) p q v
      (transposeResponseMaximizer U (levelMCoeffOn U nu hnu omega m) p (-q)) hv
      (transposeResponseMaximizer_isMaximizer U (levelMCoeffOn U nu hnu omega m) p (-q))
  have hZt : Book.Ch02.IsDoubledMuMinimizer U (centeredPairCoeffOn U nu hnu omega m L hmL)
      (-p, q) (routeDoubledFieldL U nu hnu omega m L hmL p q u) :=
    doubledFieldOfScalarMaximizers_isDoubledMuMinimizer
      (centeredPairCoeffOn U nu hnu omega m L hmL) p q u
      (transposeResponseMaximizer U (centeredPairCoeffOn U nu hnu omega m L hmL) p (-q)) hu
      (transposeResponseMaximizer_isMaximizer U (centeredPairCoeffOn U nu hnu omega m L hmL)
        p (-q))
  have hZmem := memBlockL2_eval_of_doubledAdmissible_gfb hZ.1
  have hZtmem := memBlockL2_eval_of_doubledAdmissible_gfb hZt.1
  have hDmem : MemBlockL2 (U : Set (Vec d))
      (conj3ShiftedPairRemainder U nu hnu omega m L hmL p q v u) := by
    have hsub := hZmem.sub hZtmem
    have hfun : conj3ShiftedPairRemainder U nu hnu omega m L hmL p q v u =
        ((fun x : Vec d => (routeDoubledFieldM U nu hnu omega m p q v).eval x) -
          (fun x : Vec d => (routeDoubledFieldL U nu hnu omega m L hmL p q u).eval x)) := by
      funext x
      rfl
    rwa [hfun]
  have hYmem : MemBlockL2 (U : Set (Vec d))
      (conj3PureSkewPiece U nu hnu omega m L hmL p q u) :=
    memBlockL2_pureSkewPiece_gfb U nu hnu omega m L hmL p q u
      (memVectorL2_potential_of_doubledAdmissible_gfb hZt.1)
  have hsum : MemBlockL2 (U : Set (Vec d))
      (conj3ShiftedPairRemainder U nu hnu omega m L hmL p q v u +
        conj3PureSkewPiece U nu hnu omega m L hmL p q u) := hDmem.add hYmem
  have hA := fun x (hx : x ∈ (U : Set (Vec d))) =>
    isEllipticMatrix_coefficientCutoff_domain U nu hnu omega m x hx
  have hbridge := averagedBlockQuadraticOn_add_le (A := fun x =>
      (coefficientCutoff nu omega m).toCoeffField x) U.measurableSet (fun x hx => hA x hx)
    (integrableOn_averagedBlockQuadratic_of_memBlockL2 (levelMCoeffOn U nu hnu omega m) hDmem)
    (integrableOn_averagedBlockQuadratic_of_memBlockL2 (levelMCoeffOn U nu hnu omega m) hYmem)
    (integrableOn_averagedBlockQuadratic_of_memBlockL2 (levelMCoeffOn U nu hnu omega m) hsum)
  rw [conj3SkewFreeDifference_eq_split U nu hnu omega m L hmL p q v u]
  exact hbridge

/-! ## Composing the bridge with (L1) and (Q1) -/

/-! ## The precise residual: the bridge object is not the conjunct's field -/

/-! ## Non-vacuity at `p ≠ 0`, `m < L` -/

end

end SuperdiffusionCLT.Section2.Localization
