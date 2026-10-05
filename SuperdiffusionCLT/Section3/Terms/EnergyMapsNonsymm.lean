/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3CgSteps
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3FluxEnergy
public import SuperdiffusionCLT.Section2.CoarseGraining.CutoffCorrespondence
public import SuperdiffusionCLT.Section2.Localization.BlockScalarCorrespondence
public import SuperdiffusionCLT.Section2.Cutoff.CenteredCoeffOn
public import SuperdiffusionCLT.Section2.Cutoff.StreamCutoffAPI
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementPthMoment
public import SuperdiffusionCLT.Section3.Terms.MaximizerCoefficientStability
public import SuperdiffusionCLT.Section2.Annealed.CutoffRealizationPackage

/-!
# `e.energymaps.nonsymm.flux` at the Section 3 carriers

In the paper the two displays `e.energymaps.nonsymm` and `e.energymaps.nonsymm.flux` are stated back
to back without proof and without citation (unlike the neighbouring `e.v.spatial.averages`, which
cites `[AK.Book, Lemma 5.1]`):

```
[e.energymaps.nonsymm]
     1/2 (⨍_U ∇u) · σ_*(U) (⨍_U ∇u)  <=  ⨍_U 1/2 ∇u · σ ∇u ,  for all u in A(U).
"Similarly, the coarse-grained matrix b(U) gives a lower bound for the
      spatial average of the flux of an arbitrary solution in terms of its
      energy:"
[e.energymaps.nonsymm.flux]
     1/2 (⨍_U a ∇u) · b^{-1}(U) (⨍_U a ∇u)  <=  ⨍_U 1/2 ∇u · σ ∇u ,  for all u in A(U).
```

The second display is used in the proof of `e.flux-additivity-estimate-in-an-lemma` ("by
`e.energymaps.nonsymm.flux` and `e.additivity.error.superdiff`") to justify the **first**
inequality of that lemma, where it is applied to the **difference `u_m - u_{n,z}` of two
maximizers** for the same cutoff field `a_{L'}`.  That application is the binder `hEnergyMaps` of
`flux_additivity_estimate`, which is consumed by `hFluxAdd_of_energyMaps`; it is the last analytic
residual of `_hCgBound` and the surviving residual of `hPointwise`.

## Main results

**The printed display is a theorem at a Chapter 2 carrier.**  It is the field
`average_flux_energy` of `Book.Ch02.ResponseCoarseGrainingEstimatesTheory`, whose canonical proof
`Book.Ch02.responseCoarseGrainingEstimatesTheory U a` has *no* hypotheses beyond the domain and the
coefficient object.  Read against the printed display the two agree term by term:  `⨍_U a∇u` is
`Book.Ch02.averageFlux U a w`, `b(U)` is `Book.Ch02.bCoarse U a`, and `⨍_U (1/2) ∇u·σ∇u` is
`(1/2) Book.Ch02.variationEnergyValue U a w`, the `symmPart` in `variationEnergyValue` being
exactly the printed `σ`.  So the display is **not** a gap in the library.

**The carrier difference.**  The paper quantifies over a bounded Lipschitz domain `U` and over
`u ∈ A(U)` (locally `H¹`, harmonic for `a`), while the Chapter 2 layer quantifies over a
`Book.Ch02.Domain` (bounded, open, convex, nonempty) and over `Book.Ch02.Solution U a`
(`= AHarmonicFunction a.toCoeffField (U : Set (Vec d))`, i.e. `A(U) ∩ H¹(U)`).  Both are
*narrowings* of the printed class, the same two already recorded in
`Section2/CoarseGraining/VariationalIdentities.lean`.  Our `⨍_U` is `volumeAverage` on the raw set
`openCubeSet R`, which is `Book.Ch02.average`/`averageVec` on `Book.Ch02.cubeDomain R`
definitionally; the two coarse blocks agree definitionally by the Chapter 4 bridge
`translatedCoarseBlock_eq_bCoarse`.

**The transport, and the reduction.**  `hEnergyMaps_at_carriers` is the printed display applied to
the difference of two maximizers, at our carriers, with the residual isolated in exactly two named
hypotheses:

* `hentry`, the deterministic entry bound for `a_{L'} = ν Id + k_{L'}` on the cube, which is what
  builds the `Book.Ch02.CoeffOn` object (via `coefficientCutoffCoeffOn`; see also
  `abs_coefficientCutoff_entry_le`);
* `hgrad`, the a.e. gradient identity `w.toH1.grad =ᵐ uMgrad - uNGlued` on `openCubeSet R`, i.e.
  the silent use in the paper of the *linearity of `A(U)`*: the difference of two
  `a_{L'}`-harmonic functions is again `a_{L'}`-harmonic (in the paper `u_m` and `u_{n,z}` are
  maximizers for the same field).

Everything else, namely the identification of the block, the identification of the average flux,
and the reduction of the energy `⨍ (1/2) ∇u·σ∇u` to `ν |∇u|²`, is proved.  The last step uses the
structural fact `symmPart (a_{L'} x) = ν • 1` (`symmPart_coefficientCutoff`), which turns the
`σ`-energy into `ν |∇u|²` (`vecDot_symmPart_eq_mul_vecNormSq`); the skew part `k_{L'}` never
enters the bound.

## Discharging the hypotheses

**`hentry` is not available with one constant `C` for all environments.**  The carrier is
`ShellSeq d = ℕ → ShellField d` and `ShellField d` is an *unbounded* space of `C²` skew matrix
fields, so no single `C` bounds every level-`L'` cutoff entry.  So the transport is stated with
an environment-dependent bound, and the bound is **discharged** outright:

* `largeCubeEntryBound nu S omega` names the constant explicitly, as
  `ν + ∑_{p} |streamCutoffEntryBound … p|` on the large cube `cu_{S.m}`;
* `abs_coefficientCutoff_largeCubeEntryBound` proves `hentry` at that constant
  for every `omega` and every `R ∈ largeCubeSubcubes d S.n S.m`;
* `hEnergyMaps_at_carriers_of_entryBound` is the transport with `hentry` removed.

**`hgrad` too is discharged, and it is not the refuted conjunct-3 identity.**
`Section2/Localization/Conj3Hgrad.lean` refutes a *pointwise slope* identity
`∇u - ∇v = p + w x` for maximizers of *different* fields.  Here both are maximizers of *one* field
`a_{L'}` (in the paper `u_{k,y} = v_{L'}(·, y+cu_k, 0, σ_{L',*}^{1/2}(cu_n)e)`, so `u_m = u_{m,0}`
and `u_{n,z}` share coefficient and loading), so the difference is again `a_{L'}`-harmonic, by the
hypothesis-free `subSolution` (`Section3/Terms/MaximizerCoefficientStability.lean`), with gradient
the difference of gradients (`H1Function.sub_grad`).  Hence
`hEnergyMaps_at_carriers_of_solutions` proves the `hEnergyMaps` shape with no hypothesis beyond
two `a_{L'}`-harmonic functions on the *same* cube `R`.

**The printed pair (section 6).**  Those two objects still share a carrier; in the paper `u_m`
lives on the large cube `cu_m` and `u_{n,z}` on `z + cu_n = R`.  The restriction law
`AHarmonicFunction.restrictToOpenSubcube` carries an `a_{L'}`-harmonic function from `openCubeSet Q`
to `openCubeSet R` for any descendant, with gradient the original one *definitionally*
(`grad_restrictToOpenSubcube`, `rfl`), and its ellipticity input comes from
`exists_isEllipticFieldOn_coefficientCutoff_openCubeSet`.  So
`hEnergyMaps_at_carriers_of_maximizers` is the printed display at the printed pair, with first
argument the maximizer on `cu_{S.m}` (the paper's `u_m`,
`setupMaximizer (cubeDomain (originCube d S.m)) a_{L'} Q`) and second argument the maximizer on `R`
(the paper's `u_{n,z}`, `setupMaximizer (cubeDomain R) a_{L'} Q`), the difference taken on `R`,
with no entry bound and no `hgrad`; `hEnergyMaps_of_maximizers` is its `∀ omega, ∀ R` form.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open Homogenization
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.CoarseGraining
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Localization
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.Setup

noncomputable section

open scoped MatrixOrder Matrix.Norms.Elementwise

variable {d : ℕ}

/-! ## 1. The printed displays at the Chapter 2 carrier -/

/-- Volume averages only see the function through its a.e. class. -/
theorem volumeAverage_congr_ae {d : ℕ} {U : Set (Vec d)} {f g : Vec d → ℝ}
    (hfg : f =ᵐ[volumeMeasureOn U] g) : volumeAverage U f = volumeAverage U g := by
  unfold volumeAverage
  congr 1
  exact MeasureTheory.integral_congr_ae hfg

/-! ## 2. The coarse block on a translated cube is a Chapter 2 `bCoarse` -/

/-- The coarse block `b_L(z + cu_n)` of the Section 3 carriers is the Chapter 2
`bCoarse` of the cutoff field on the public cube domain.  This is the same
rewrite chain as `posSemidef_translatedCoarseBlock`
followed by the identification of the two Chapter 2 coefficient objects up to a.e. equality of
their representatives (their `toCoeffField`s are both `(coefficientCutoff nu omega L).toFun`). -/
theorem translatedCoarseBlock_eq_bCoarse [NeZero d] {nu C : ℝ} (hnu : 0 < nu) (L : ℕ)
    (omega : ShellSeq d) (z : TriadicCube d)
    (hentry : ∀ x ∈ openCubeSet z, ∀ i j,
      |(coefficientCutoff nu omega L).toCoeffField x i j| ≤ C) :
    translatedCoarseBlock nu L omega z =
      Book.Ch02.bCoarse (Book.Ch02.cubeDomain z)
        (coefficientCutoffCoeffOn (Book.Ch02.cubeDomain z) hnu omega L hentry) := by
  have hae : Homogenization.Book.Ch02.CoeffOn.AEEq
      ((Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
        (coefficientCutoff nu omega L)
        (aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega L)).coeffOn z)
      (coefficientCutoffCoeffOn (Book.Ch02.cubeDomain z) hnu omega L hentry) := by
    rw [Homogenization.Book.Ch02.CoeffOn.AEEq,
      Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField_coeffOn_toCoeffField]
    exact Filter.EventuallyEq.rfl
  rw [translatedCoarseBlock, translatedBlockMat,
    ← coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube z,
    show coarseBlockMatrix (cubeSet z) (coefficientCutoff nu omega L).toCoeffField =
      Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain z)
        ((Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
          (coefficientCutoff nu omega L)
          (aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega L)).coeffOn z) from
      Book.Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
        (aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega L) z,
    Book.Ch02.coarseBlockMatrix_upperLeft,
    Book.Ch02.bCoarse_eq_ofAEEq hae]

/-! ## 3. The transport, applied to the difference of two maximizers -/

/-- **`e.energymaps.nonsymm.flux` applied to the difference `u_m - u_{n,z}` of
two maximizers, at the carriers of `e.flux-additivity-estimate-in-an-lemma`.**

The left side is the printed `|b_{L'}^{-1/2}(z+cu_n)
(a_{L'}∇(u_m-u_{n,z}))_{z+cu_n}|²` (`translatedBlockHalfWeightInv` of the
averaged flux field `fluxFieldCarrier`, via
`translatedBlockHalfWeightInv_eq_vecDot_inv`), the right side is the printed
`⨍_{z+cu_n} ∇(u_m-u_{n,z})·σ∇(u_m-u_{n,z})`, i.e. `⨍ ν|∇u_m - ∇u_{n,z}|²`
because `symmPart a_{L'} = ν Id`.

It is proved from the printed display, multiplied by `2` (the display in the proof of
`e.flux-additivity-estimate-in-an-lemma` carries no `1/2`, while `e.energymaps.nonsymm.flux`
carries `1/2` on both sides).
The two hypotheses are the two residuals: `hentry`, the deterministic entry
bound that builds the `Book.Ch02.CoeffOn` object, and `hgrad`, the a.e.
gradient identity saying that `w` *is* the difference of the two maximizers on
the cube, the silent use in the paper of the linearity of `A(U)`. -/
theorem hEnergyMaps_at_carriers [NeZero d] {nu C : ℝ} (hnu : 0 < nu)
    (S : ScaleSelection) (omega : ShellSeq d)
    (uMgrad uNGlued : Vec d → Vec d) (R : TriadicCube d)
    (hentry : ∀ x ∈ openCubeSet R, ∀ i j,
      |(coefficientCutoff nu omega S.LPrime).toCoeffField x i j| ≤ C)
    (w : Book.Ch02.Solution (Book.Ch02.cubeDomain R)
      (coefficientCutoffCoeffOn (Book.Ch02.cubeDomain R) hnu omega S.LPrime hentry))
    (hgrad : w.toH1.grad =ᵐ[volumeMeasureOn (openCubeSet R)]
      (fun y => uMgrad y - uNGlued y)) :
    translatedBlockHalfWeightInv nu S.LPrime omega R
        (volumeAverageVec (openCubeSet R) (fluxFieldCarrier nu S omega uMgrad uNGlued)) ≤
      volumeAverage (openCubeSet R) (fun y => nu * vecNormSq (uMgrad y - uNGlued y)) := by
  have hfl : fluxFieldCarrier nu S omega uMgrad uNGlued =ᵐ[volumeMeasureOn (openCubeSet R)]
      (fun x => matVecMul
        ((coefficientCutoffCoeffOn (Book.Ch02.cubeDomain R) hnu omega S.LPrime hentry).toCoeffField x)
        (w.toH1.grad x)) := by
    refine hgrad.mono fun x hx => ?_
    simp only [fluxFieldCarrier, hx]
    rfl
  have havg : volumeAverageVec (openCubeSet R) (fluxFieldCarrier nu S omega uMgrad uNGlued) =
      Book.Ch02.averageFlux (Book.Ch02.cubeDomain R)
        (coefficientCutoffCoeffOn (Book.Ch02.cubeDomain R) hnu omega S.LPrime hentry) w := by
    funext i
    exact volumeAverage_congr_ae (hfl.mono fun x hx => congrArg (fun v : Vec d => v i) hx)
  have henergy : Book.Ch02.variationEnergyValue (Book.Ch02.cubeDomain R)
        (coefficientCutoffCoeffOn (Book.Ch02.cubeDomain R) hnu omega S.LPrime hentry) w =
      volumeAverage (openCubeSet R) (fun y => nu * vecNormSq (uMgrad y - uNGlued y)) := by
    show volumeAverage (openCubeSet R)
        (fun x => vecDot (w.toH1.grad x)
          (matVecMul (symmPart
            ((coefficientCutoffCoeffOn (Book.Ch02.cubeDomain R) hnu omega S.LPrime hentry).toCoeffField x))
            (w.toH1.grad x)))
      = volumeAverage (openCubeSet R) (fun y => nu * vecNormSq (uMgrad y - uNGlued y))
    refine volumeAverage_congr_ae (hgrad.mono fun y hy => ?_)
    beta_reduce
    rw [hy]
    exact vecDot_symmPart_eq_mul_vecNormSq (symmPart_coefficientCutoff nu omega S.LPrime y) _
  rw [translatedBlockHalfWeightInv_eq_vecDot_inv hnu S.LPrime omega R _, havg,
    translatedCoarseBlock_eq_bCoarse hnu S.LPrime omega R hentry]
  have hup := (Book.Ch02.responseCoarseGrainingEstimatesTheory (Book.Ch02.cubeDomain R)
    (coefficientCutoffCoeffOn (Book.Ch02.cubeDomain R) hnu omega S.LPrime hentry)).average_flux_energy w
  rw [henergy] at hup
  linarith only [hup]

/-! ## 4. The entry bound on the large cube, discharged -/

/-- **The explicit level-`L'` entry bound on the large cube `cu_{S.m}`**, named
as `ν` plus the sum of the entry bounds of the finite stream matrix.  It depends
on the environment `omega`, which is unavoidable because the shell fields are unbounded. -/
noncomputable def largeCubeEntryBound [NeZero d] (nu : ℝ) (S : ScaleSelection)
    (omega : ShellSeq d) : ℝ :=
  nu + ∑ p : Fin d × Fin d,
    |streamCutoffEntryBound (isBounded_cubeSet (originCube d (S.m : ℤ))) omega S.LPrime p|

/-- **`hentry` is a theorem, not a hypothesis.**  For every shell sequence and
every `R ∈ largeCubeSubcubes d S.n S.m`, the level-`L'` cutoff entry is bounded
by the named constant `largeCubeEntryBound nu S omega`.  This is
`abs_coefficientCutoff_entry_le` fed with the unconditional
`abs_streamCutoffEntryBound` on the bounded cube `cu_{S.m}`, which contains
`openCubeSet R`. -/
theorem abs_coefficientCutoff_largeCubeEntryBound [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (S : ScaleSelection) (omega : ShellSeq d) {R : TriadicCube d}
    (hR : R ∈ largeCubeSubcubes d S.n S.m) :
    ∀ x ∈ openCubeSet R, ∀ i j : Fin d,
      |(coefficientCutoff nu omega S.LPrime).toCoeffField x i j| ≤
        largeCubeEntryBound nu S omega := by
  have hR' : R ∈ descendantsAtDepth (originCube d (S.m : ℤ)) (S.m - S.n) := hR
  have hsub : cubeSet R ⊆ cubeSet (originCube d (S.m : ℤ)) :=
    cubeSet_subset_of_mem_descendantsAtDepth (Q := originCube d (S.m : ℤ)) hR'
  intro x hx i j
  have hxb : x ∈ cubeSet (originCube d (S.m : ℤ)) := hsub (openCubeSet_subset_cubeSet R hx)
  refine abs_coefficientCutoff_entry_le hnu.le omega S.LPrime x (fun p q => ?_) i j
  calc |streamCutoff omega S.LPrime x p q|
      ≤ |streamCutoffEntryBound (isBounded_cubeSet (originCube d (S.m : ℤ)))
          omega S.LPrime (p, q)| :=
        (abs_streamCutoffEntryBound (isBounded_cubeSet (originCube d (S.m : ℤ)))
          omega S.LPrime (p, q) x hxb).trans (le_abs_self _)
    _ ≤ ∑ r : Fin d × Fin d,
          |streamCutoffEntryBound (isBounded_cubeSet (originCube d (S.m : ℤ)))
            omega S.LPrime r| :=
        Finset.single_le_sum
          (f := fun r : Fin d × Fin d =>
            |streamCutoffEntryBound (isBounded_cubeSet (originCube d (S.m : ℤ)))
              omega S.LPrime r|)
          (fun r _ => abs_nonneg _) (Finset.mem_univ _)

/-- **`hEnergyMaps` at our carriers with `hentry` discharged.**  Identical to
`hEnergyMaps_at_carriers` but with the entry bound supplied by
`abs_coefficientCutoff_largeCubeEntryBound` at the named constant
`largeCubeEntryBound nu S omega`.  The remaining inputs are the maximizer `sol`
and the gradient identity `hgrad`. -/
theorem hEnergyMaps_at_carriers_of_entryBound [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (S : ScaleSelection) (omega : ShellSeq d) (uMgrad uNGlued : Vec d → Vec d)
    (R : TriadicCube d) (hR : R ∈ largeCubeSubcubes d S.n S.m)
    (w : Book.Ch02.Solution (Book.Ch02.cubeDomain R)
      (coefficientCutoffCoeffOn (Book.Ch02.cubeDomain R) hnu omega S.LPrime
        (abs_coefficientCutoff_largeCubeEntryBound hnu S omega hR)))
    (hgrad : w.toH1.grad =ᵐ[volumeMeasureOn (openCubeSet R)]
      (fun y => uMgrad y - uNGlued y)) :
    translatedBlockHalfWeightInv nu S.LPrime omega R
        (volumeAverageVec (openCubeSet R) (fluxFieldCarrier nu S omega uMgrad uNGlued)) ≤
      volumeAverage (openCubeSet R) (fun y => nu * vecNormSq (uMgrad y - uNGlued y)) :=
  hEnergyMaps_at_carriers hnu S omega uMgrad uNGlued R
    (abs_coefficientCutoff_largeCubeEntryBound hnu S omega hR) w hgrad

/-! ## 5. `hgrad` discharged at the maximizers: the printed statement, unconditionally

Section 4 removed `hentry` from the `hEnergyMaps` shape; the remaining
input was `hgrad`.  It too is discharged, not assumed: in the paper the maximizers
`u_m` and `u_{n,z}` are solutions of the *same* coefficient `a_{L'}`, so on a
common subcube their difference is again a solution of `a_{L'}`, by the
hypothesis-free `subSolution`, with gradient the difference of gradients by
`H1Function.sub_grad`.  So the two theorems below take the two maximizer
families `uM`, `uN` on one cube `R` as their *only* inputs besides `0 < nu`;
section 6 then removes even the shared-carrier hypothesis. -/

/-- **`hEnergyMaps` at the carriers of the maximizers, with no hypothesis
beyond the two maximizer families.**  `uM` and `uN` are any two `a_{L'}`-harmonic
functions on `cu_{S.m}` — instantiate them with `u_m` and `u_{n,z}` of the paper. -/
theorem hEnergyMaps_at_carriers_of_solutions [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (S : ScaleSelection) (omega : ShellSeq d) (R : TriadicCube d)
    (hR : R ∈ largeCubeSubcubes d S.n S.m)
    (uM uN : Book.Ch02.Solution (Book.Ch02.cubeDomain R)
      (coefficientCutoffCoeffOn (Book.Ch02.cubeDomain R) hnu omega S.LPrime
        (abs_coefficientCutoff_largeCubeEntryBound hnu S omega hR))) :
    translatedBlockHalfWeightInv nu S.LPrime omega R
        (volumeAverageVec (openCubeSet R)
          (fluxFieldCarrier nu S omega uM.toH1.grad uN.toH1.grad)) ≤
      volumeAverage (openCubeSet R)
        (fun y => nu * vecNormSq (uM.toH1.grad y - uN.toH1.grad y)) :=
  hEnergyMaps_at_carriers_of_entryBound hnu S omega uM.toH1.grad uN.toH1.grad R hR
    (subSolution uM uN)
    (Filter.EventuallyEq.of_eq (by
      rw [subSolution_toH1]
      exact H1Function.sub_grad uM.toH1 uN.toH1))

/-! ## 6. The printed pair: `u_m` on the big cube, `u_{n,z}` on the subcube

Section 5 still asked for a solution object on `cu_{S.m}`.  But the printed
difference is `u_m - u_{n,z}` where `u_m` is a maximizer on the *large* cube
`cu_m` and `u_{n,z}` one on `z + cu_n = R`, and the display is applied on `R`.
The two live on different carriers, so the second is not literally a
`Book.Ch02.Solution` of `cu_{S.m}`.

That obstruction is removed by the restriction law
`AHarmonicFunction.restrictToOpenSubcube` (`Homogenization.PDE.HarmonicCube`),
which restricts an `a`-harmonic function on `openCubeSet Q` to `openCubeSet R`
for any descendant `R ∈ descendantsAtDepth Q j`, and whose gradient is the
original gradient *definitionally* (`grad_restrictToOpenSubcube`, proved by
`rfl`).  The ellipticity input it needs is supplied by
`exists_isEllipticFieldOn_coefficientCutoff_openCubeSet`
(`Section2/Annealed/CutoffRealizationPackage.lean`), which is available on every
triadic open cube from `symmPart_coefficientCutoff`.

So the theorem below is the printed `e.energymaps.nonsymm.flux` applied to the
printed pair, with **no** entry bound and **no** `hgrad`: the first object is an
`a_{L'}`-harmonic function on the large cube (the paper's `u_m`, i.e.
`setupMaximizer (cubeDomain (originCube d S.m)) a_{L'} Q` of
`Section3/Setup/Scales.lean`), the second a solution on `R` (the paper's
`u_{n,z}`, `setupMaximizer (cubeDomain R) a_{L'} Q`), and the difference is taken
on `R`. -/

/-- **`e.energymaps.nonsymm.flux` at the printed pair.**  No `hgrad`: the first
argument is the maximizer on the *large* cube `cu_{S.m}`, restricted to `R` by
the restriction law, whose gradient is the original one by `rfl`. -/
theorem hEnergyMaps_at_carriers_of_maximizers [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (S : ScaleSelection) (omega : ShellSeq d) (R : TriadicCube d)
    (hR : R ∈ largeCubeSubcubes d S.n S.m)
    (vM : AHarmonicFunction (coefficientCutoff nu omega S.LPrime).toCoeffField
      (openCubeSet (originCube d (S.m : ℤ))))
    (vN : Book.Ch02.Solution (Book.Ch02.cubeDomain R)
      (coefficientCutoffCoeffOn (Book.Ch02.cubeDomain R) hnu omega S.LPrime
        (abs_coefficientCutoff_largeCubeEntryBound hnu S omega hR))) :
    translatedBlockHalfWeightInv nu S.LPrime omega R
        (volumeAverageVec (openCubeSet R)
          (fluxFieldCarrier nu S omega vM.toH1.grad vN.toH1.grad)) ≤
      volumeAverage (openCubeSet R)
        (fun y => nu * vecNormSq (vM.toH1.grad y - vN.toH1.grad y)) := by
  obtain ⟨lam, Lam, hEll⟩ :=
    exists_isEllipticFieldOn_coefficientCutoff_openCubeSet hnu omega S.LPrime
      (originCube d (S.m : ℤ))
  have h := hEnergyMaps_at_carriers_of_solutions hnu S omega R hR
    (vM.restrictToOpenSubcube hEll hR) vN
  exact h

/-- **The `hEnergyMaps` binder shape with both maximizer families named.**  The
`uMgrad`/`uNGlued` of the consumer are `∇vM` (the maximizer on `cu_{S.m}`, in
the environment `omega`) and `∇vN` (the maximizer on `R`, in the same
environment, i.e. the paper's `u_{n,z}`). -/
theorem hEnergyMaps_of_maximizers [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (S : ScaleSelection)
    (vM : ∀ omega : ShellSeq d,
      AHarmonicFunction (coefficientCutoff nu omega S.LPrime).toCoeffField
        (openCubeSet (originCube d (S.m : ℤ))))
    (vN : ∀ (omega : ShellSeq d) (R : TriadicCube d)
        (hR : R ∈ largeCubeSubcubes d S.n S.m),
      Book.Ch02.Solution (Book.Ch02.cubeDomain R)
        (coefficientCutoffCoeffOn (Book.Ch02.cubeDomain R) hnu omega S.LPrime
          (abs_coefficientCutoff_largeCubeEntryBound hnu S omega hR))) :
    ∀ omega : ShellSeq d, ∀ R : TriadicCube d, ∀ hR : R ∈ largeCubeSubcubes d S.n S.m,
      translatedBlockHalfWeightInv nu S.LPrime omega R
          (volumeAverageVec (openCubeSet R)
            (fluxFieldCarrier nu S omega (vM omega).toH1.grad
              (vN omega R hR).toH1.grad)) ≤
        volumeAverage (openCubeSet R)
          (fun y => nu * vecNormSq ((vM omega).toH1.grad y -
            (vN omega R hR).toH1.grad y)) :=
  fun omega R hR => hEnergyMaps_at_carriers_of_maximizers hnu S omega R hR
    (vM omega) (vN omega R hR)

end

end SuperdiffusionCLT.Section3.Terms
