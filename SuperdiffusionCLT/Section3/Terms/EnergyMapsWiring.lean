/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.EnergyMapsNonsymm
public import SuperdiffusionCLT.Section3.Terms.GluedField
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3CgSteps

/-!
# Wiring `e.energymaps.nonsymm.flux` into its consumers

`Section3/Terms/EnergyMapsNonsymm.lean` proves the display
`e.energymaps.nonsymm.flux` applied to the difference of two
maximizers, unconditionally:  `hEnergyMaps_of_maximizers` has as
its only inputs the scale selection `S` and the two maximizer families `vM`, `vN`
— the first an `a_{L'}`-harmonic function on the *large* cube
`openCubeSet (originCube d S.m)`, the second a `Book.Ch02.Solution` on the
sub-cube `R ∈ largeCubeSubcubes d S.n S.m`.  Its conclusion is

```
translatedBlockHalfWeightInv nu S.LPrime omega R
    (volumeAverageVec (openCubeSet R) (fluxFieldCarrier nu S omega
      (vM omega).toH1.grad (vN omega R hR).toH1.grad)) ≤
  volumeAverage (openCubeSet R)
    (fun y => nu * vecNormSq ((vM omega).toH1.grad y - (vN omega R hR).toH1.grad y))
```

pointwise in the environment `omega` and the sub-cube `R`.

## The shape mismatch, character by character

The consumer binder `hEnergyMaps` — the binder of `flux_additivity_estimate`
(the same binder is the first hypothesis of `hFluxAdd_of_energyMaps`) — reads

```
∀ omega : ShellSeq d, ∀ R ∈ largeCubeSubcubes d S.n S.m,
  normFlux omega R ≤
    volumeAverage (openCubeSet R)
      (fun y => nu * vecNormSq (uMgrad omega y - uNGlued omega y))
```

with `uMgrad uNGlued : ShellSeq d → Vec d → Vec d`.  The right-hand sides agree
term for term.  The *left* sides differ in exactly one place:  the consumer's
left member is a free `normFlux omega R`, so both of its gradient arguments are
**functions of `omega` alone**, whereas the second gradient of the theorem above
`(vN omega R hR).toH1.grad` is a function of `omega` **and of the sub-cube `R`**
(the maximizer `u_{n,z}` of the paper lives on `R = z + cu_n`).

That mismatch is not an accident of the statement: it is the reason the consumer
is stated with a *glued* field.  The printed `∇u_n` of `e.u.k.def`
is the piecewise field `∑_z ∇u_{n,z} 1_{z + cu_n}`, i.e. exactly
`gluedGradientField hnu S.LPrime S.n S.m F omega` of `GluedField.lean`, whose
value on the sub-cube `R` is `∇u_{n,z}` a.e. (`gluedGradientField_apply_of_mem_openCubeSet`).
The consumer `term3_cgBound_close` uses the same two fields,
`gluedGradientField hnu S.LPrime S.m S.m …` and `gluedGradientField hnu S.LPrime S.n S.m …`.

## Main results

* `hEnergyMaps_of_maximizers_glued`: the adapter, which takes the maximizer
  families of `hEnergyMaps_of_maximizers` and an arbitrary *R-independent* pair
  `uMgrad uNGlued` agreeing with the maximizer gradients a.e. on each sub-cube, and produces the
  consumer's shape.  This is the shape bridge, with the two a.e. identities
  named as hypotheses.
* `gluedMaximizerGrad`, `gluedSubcubeGrad`, `gluedFluxNorm`:  the pinned glued
  carriers, named.
* `cubeMaximizerGradient_largeCube_aeEq`, `cubeMaximizerGradient_subcube_aeEq`:
  the two a.e. identities at the *actual* maximizers, at **any** scale pair
  `(k, m)` — theorems, not hypotheses.
* `hEnergyMaps_at_gluedMaximizers`:  **the consumer binder, at the pinned glued
  carriers, with no hypothesis besides `0 < nu` and the scale selection** —
  obtained by the direct feed of `hEnergyMaps_of_maximizers`.
* `hEnergyMaps_at_gluedMaximizers_scales`:  **the same display at every scale
  pair `(k, m)`** — the per-scale input at which the printed `ℓ¹` depth sum of the
  `hPointwise` residual applies it, obtained
  from `hEnergyMaps_at_carriers` without any `ScaleSelection`-shaped maximizer
  family.
* `hFluxAdd_of_maximizers`: the consumer binder `hFluxAdd` at the pinned glued
  carriers, reduced to the `e.additivity.error.superdiff` package alone.
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

variable {d : ℕ}

/-! ## 1. The a.e. transport of a volume average of a vector field -/

/-- Volume averages of vector fields only see the a.e. class, componentwise.
This is `volumeAverage_congr_ae` read on
`volumeAverageVec`, whose definition (`Homogenization.volumeAverageVec`) is
componentwise. -/
theorem volumeAverageVec_congr_ae {d : ℕ} {U : Set (Vec d)} {f g : Vec d → Vec d}
    (hfg : f =ᵐ[volumeMeasureOn U] g) :
    volumeAverageVec U f = volumeAverageVec U g := by
  funext i
  exact volumeAverage_congr_ae
    (hfg.mono fun x hx => congrArg (fun v : Vec d => v i) hx)

/-! ## 2. The adapter: from the R-dependent maximizer pair to an R-independent pair -/

/-- **The shape bridge for `hEnergyMaps`.**  `hEnergyMaps_of_maximizers`
produces the consumer's right-hand side but with
an `R`-dependent second gradient; the consumer (`flux_additivity_estimate` and
`hFluxAdd_of_energyMaps`) takes an
`R`-independent pair `uMgrad uNGlued : ShellSeq d → Vec d → Vec d`.  This
theorem converts one into the other, the two a.e. identities on
`openCubeSet R` being its only inputs beyond `hEnergyMaps_of_maximizers`.

At the printed maximizers both identities are theorems
(`cubeMaximizerGradient_largeCube_aeEq`, `cubeMaximizerGradient_subcube_aeEq`),
and instantiate the pair with the glued fields of `e.u.k.def`; see
`hEnergyMaps_at_gluedMaximizers`. -/
theorem hEnergyMaps_of_maximizers_glued [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (S : ScaleSelection)
    (vM : ∀ omega : ShellSeq d,
      AHarmonicFunction (coefficientCutoff nu omega S.LPrime).toCoeffField
        (openCubeSet (originCube d (S.m : ℤ))))
    (vN : ∀ (omega : ShellSeq d) (R : TriadicCube d)
        (hR : R ∈ largeCubeSubcubes d S.n S.m),
      Book.Ch02.Solution (Book.Ch02.cubeDomain R)
        (coefficientCutoffCoeffOn (Book.Ch02.cubeDomain R) hnu omega S.LPrime
          (abs_coefficientCutoff_largeCubeEntryBound hnu S omega hR)))
    (uMgrad uNGlued : ShellSeq d → Vec d → Vec d)
    (hM : ∀ (omega : ShellSeq d) (R : TriadicCube d)
        (_hR : R ∈ largeCubeSubcubes d S.n S.m),
      (vM omega).toH1.grad =ᵐ[volumeMeasureOn (openCubeSet R)] uMgrad omega)
    (hN : ∀ (omega : ShellSeq d) (R : TriadicCube d)
        (hR : R ∈ largeCubeSubcubes d S.n S.m),
      (vN omega R hR).toH1.grad =ᵐ[volumeMeasureOn (openCubeSet R)] uNGlued omega) :
    ∀ (omega : ShellSeq d) (R : TriadicCube d) (_hR : R ∈ largeCubeSubcubes d S.n S.m),
      translatedBlockHalfWeightInv nu S.LPrime omega R
          (volumeAverageVec (openCubeSet R)
            (fluxFieldCarrier nu S omega (uMgrad omega) (uNGlued omega))) ≤
        volumeAverage (openCubeSet R)
          (fun y => nu * vecNormSq (uMgrad omega y - uNGlued omega y)) := by
  intro omega R hR
  have hmain := hEnergyMaps_of_maximizers hnu S vM vN omega R hR
  have hdiff : (fun y : Vec d => (vM omega).toH1.grad y - (vN omega R hR).toH1.grad y)
      =ᵐ[volumeMeasureOn (openCubeSet R)]
      (fun y : Vec d => uMgrad omega y - uNGlued omega y) := by
    filter_upwards [hM omega R hR, hN omega R hR] with y hyM hyN
    rw [hyM, hyN]
  have hfl : fluxFieldCarrier nu S omega (uMgrad omega) (uNGlued omega)
      =ᵐ[volumeMeasureOn (openCubeSet R)]
      fluxFieldCarrier nu S omega (vM omega).toH1.grad (vN omega R hR).toH1.grad :=
    hdiff.mono fun y hy =>
      congrArg (fun v : Vec d =>
        matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y) v) hy.symm
  have havg : volumeAverageVec (openCubeSet R)
      (fluxFieldCarrier nu S omega (uMgrad omega) (uNGlued omega)) =
      volumeAverageVec (openCubeSet R)
        (fluxFieldCarrier nu S omega (vM omega).toH1.grad (vN omega R hR).toH1.grad) :=
    volumeAverageVec_congr_ae hfl
  have henergy : volumeAverage (openCubeSet R)
      (fun y => nu * vecNormSq (uMgrad omega y - uNGlued omega y)) =
      volumeAverage (openCubeSet R)
        (fun y => nu * vecNormSq ((vM omega).toH1.grad y - (vN omega R hR).toH1.grad y)) :=
    volumeAverage_congr_ae (hdiff.mono fun y hy =>
      (congrArg (fun v : Vec d => nu * vecNormSq v) hy).symm)
  rw [havg, henergy]
  exact hmain

/-! ## 3. The two a.e. identities at the printed maximizers

The printed `∇u_m` and `∇u_{n,z}` are the glued fields of `e.u.k.def` on the two
scales; the identification is `gluedGradientField_apply_of_mem_cubeSet` at scale
`S.m` (where `largeCubeSubcubes d S.m S.m` is the single cube `cu_{S.m}`,
`largeCubeSubcubes_self`) and `gluedGradientField_apply_of_mem_openCubeSet` at
scale `S.n`. -/

/-- `∇u_m` — the maximizer on the *large* cube `cu_m` — agrees a.e. on every
sub-cube `R` of any scale pair `(k, m)` with the scale-`m` glued field, i.e. with
`uMgrad` of the consumer.  The pair `(k, m)` is free here: the only place `R` is
used is the value of the glued field, which is the maximizer's own gradient on
every cube of `largeCubeSubcubes d k m`. -/
theorem cubeMaximizerGradient_largeCube_aeEq [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (L k m : ℕ) (F : Vec d) (omega : ShellSeq d) {R : TriadicCube d}
    (hR : R ∈ largeCubeSubcubes d k m) :
    (cubeMaximizer hnu omega L F (originCube d (m : ℤ))).toSolution.toH1.grad
        =ᵐ[volumeMeasureOn (openCubeSet R)]
      gluedGradientField hnu L m m F omega := by
  refine (MeasureTheory.ae_restrict_iff' (measurableSet_openCubeSet R)).2
    (Filter.Eventually.of_forall fun x hx => ?_)
  show cubeMaximizerGradient hnu omega L F (originCube d (m : ℤ)) x = _
  exact (gluedGradientField_apply_of_mem_cubeSet hnu L m m F omega
    (by rw [largeCubeSubcubes_self]; exact Finset.mem_singleton_self _)
    (cubeSet_subset_of_mem_largeCubeSubcubes hR (openCubeSet_subset_cubeSet R hx))).symm

/-- `∇u_{n,z}` — the maximizer on the sub-cube `R` — agrees a.e. on `R` with
the scale-`k` glued field, i.e. with `uNGlued` of the consumer, at any scale pair
`(k, m)` such that `R ∈ largeCubeSubcubes d k m`. -/
theorem cubeMaximizerGradient_subcube_aeEq [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (L k m : ℕ) (F : Vec d) (omega : ShellSeq d) {R : TriadicCube d}
    (hR : R ∈ largeCubeSubcubes d k m) :
    (cubeMaximizer hnu omega L F R).toSolution.toH1.grad
        =ᵐ[volumeMeasureOn (openCubeSet R)]
      gluedGradientField hnu L k m F omega := by
  refine (MeasureTheory.ae_restrict_iff' (measurableSet_openCubeSet R)).2
    (Filter.Eventually.of_forall fun x hx => ?_)
  show cubeMaximizerGradient hnu omega L F R x = _
  exact (gluedGradientField_apply_of_mem_openCubeSet hnu L k m F omega hR hx).symm

/-! ### 3b. The energy-map inequality at *every* scale pair

The printed `hPointwise` residual (see `RHSTerm3FluxEnergy`) applies the
display `e.energymaps.nonsymm.flux` not only at the outer scale pair
`(S.n, S.m)` of the consumer binder but at *every* depth `j` of its `ℓ¹` depth
sum (see `MultiscalePoincareFlux.lean`),
whose terms `vecDepthMoment R j (fluxFieldCarrier …)` average the *same fixed*
flux field over `descendantsAtDepth R j` — the cubes `z'` *finer* than `R`, of
scale `k := S.n - j`, while the carrier pair stays at the scales
`(S.m, S.n)`.

So the general per-cube input is not indexed by a pair of *maximizer scales*
alone: the cube `R'` at which the average is taken may be finer than the scale
`k'` of the maximizer of the second carrier.  The two theorems below supply
exactly that, and both are free of any maximizer-family or entry-bound
hypothesis:

* `hEnergyMaps_at_gluedMaximizers_scales_coarse`:  the display at a cube `R` of
  scale `k` inside the coarse cube `Q` of scale `k'` that carries the second
  carrier — the shape the printed depth sum uses, with the coarse cube and the
  depth `k' - k` passed explicitly;
* `hEnergyMaps_at_gluedMaximizers_scales`:  the case `Q = R`, where the cube and
  the carrier have the same scale.

Neither needs a `ScaleSelection`-shaped maximizer family: the structure carries
the proof fields `ellPrime_add_h`/`ell_add_a`/`n_add_a`/`LPrime_eq`
(`Section3/Setup/Parameters.lean`), so `{S with n := j}` is not
constructible, but the route below avoids it — the only `S`-dependence of the
carrier `hEnergyMaps_at_carriers` is the
cutoff `S.LPrime`, and its entry bound is a free hypothesis, discharged here on
each cube by `exists_entryBound_coefficientCutoff`.  The harmonic function
realizing the difference is `subSolution` of the *restrictions* of the two
maximizers, by the restriction law `AHarmonicFunction.restrictToOpenSubcube`
whose gradient is the original one definitionally. -/

/-! ## 4. The pinned glued carriers, named -/

/-- `∇u_m` of the consumer: the scale-`S.m` glued field
`gluedGradientField hnu S.LPrime S.m S.m F`, i.e. `∇u_m` of `e.u.k.def`. -/
def gluedMaximizerGrad {d : ℕ} {nu : ℝ} (hnu : 0 < nu) (S : ScaleSelection) (F : Vec d) :
    ShellSeq d → Vec d → Vec d :=
  fun omega => gluedGradientField hnu S.LPrime S.m S.m F omega

/-- `∇u_n` of the consumer: the scale-`S.n` glued field
`gluedGradientField hnu S.LPrime S.n S.m F`, i.e. the piecewise `∇u_{n,z}`. -/
def gluedSubcubeGrad {d : ℕ} {nu : ℝ} (hnu : 0 < nu) (S : ScaleSelection) (F : Vec d) :
    ShellSeq d → Vec d → Vec d :=
  fun omega => gluedGradientField hnu S.LPrime S.n S.m F omega

/-- **The printed `normFlux`**: `|b_{L'}^{-1/2}(z + cu_n) (a_{L'}∇(u_m -
u_{n,z}))_{z+cu_n}|²` of the paper, at the glued carriers — the
`translatedBlockHalfWeightInv` of the averaged flux field.  This is exactly the
`normFlux` that the consumer instantiates (see `term3_cgBound_close`). -/
def gluedFluxNorm {d : ℕ} {nu : ℝ} (hnu : 0 < nu) (S : ScaleSelection) (F : Vec d) :
    ShellSeq d → TriadicCube d → ℝ :=
  fun omega R => translatedBlockHalfWeightInv nu S.LPrime omega R
    (volumeAverageVec (openCubeSet R)
      (fluxFieldCarrier nu S omega (gluedMaximizerGrad hnu S F omega)
        (gluedSubcubeGrad hnu S F omega)))

/-! ## 5. The consumer binder, at the pinned glued carriers -/

/-- **The `hEnergyMaps` binder of `flux_additivity_estimate` and `hFluxAdd_of_energyMaps`,
discharged at the printed glued carriers.**

No hypothesis beyond `0 < nu` and the scale selection: the entry bound is
`abs_coefficientCutoff_largeCubeEntryBound`, the two maximizers are the
`cubeMaximizer` family of `e.u.k.def`, and the identification of the
glued fields with their gradients is `gluedGradientField_apply_of_mem_cubeSet` /
`gluedGradientField_apply_of_mem_openCubeSet`.  The forcing `F` is the print's
`Q = shom_{L',*}^{1/2}(cu_n) e`, passed here as an explicit vector.

The proof is the direct feed of
`hEnergyMaps_of_maximizers` through the shape
adapter of section 2.  The *same* binder also follows from the scale-general
`hEnergyMaps_at_gluedMaximizers_scales` at `(k, m) = (S.n, S.m)`, whose route
through `hEnergyMaps_at_carriers` needs no `ScaleSelection`-shaped family and
therefore generalizes; the two proofs are independent. -/
theorem hEnergyMaps_at_gluedMaximizers [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (S : ScaleSelection) (F : Vec d) :
    ∀ (omega : ShellSeq d) (R : TriadicCube d) (_hR : R ∈ largeCubeSubcubes d S.n S.m),
      translatedBlockHalfWeightInv nu S.LPrime omega R
          (volumeAverageVec (openCubeSet R)
            (fluxFieldCarrier nu S omega (gluedMaximizerGrad hnu S F omega)
              (gluedSubcubeGrad hnu S F omega))) ≤
        volumeAverage (openCubeSet R)
          (fun y => nu * vecNormSq (gluedMaximizerGrad hnu S F omega y -
            gluedSubcubeGrad hnu S F omega y)) :=
  hEnergyMaps_of_maximizers_glued hnu S
    (fun omega =>
      (cubeMaximizer hnu omega S.LPrime F (originCube d (S.m : ℤ))).toSolution)
    (fun omega R _ => (cubeMaximizer hnu omega S.LPrime F R).toSolution)
    (gluedMaximizerGrad hnu S F) (gluedSubcubeGrad hnu S F)
    (fun omega _R hR => cubeMaximizerGradient_largeCube_aeEq hnu S.LPrime S.n S.m F omega hR)
    (fun omega _R hR => cubeMaximizerGradient_subcube_aeEq hnu S.LPrime S.n S.m F omega hR)

/-- The same binder with the forcing named as the print's
`Q = shom_{L',*}^{1/2}(cu_n) e` and the left member as `gluedFluxNorm`. -/
theorem hEnergyMaps_at_gluedMaximizers_fluxSlot [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) (e : Vec d) :
    ∀ (omega : ShellSeq d) (R : TriadicCube d) (_hR : R ∈ largeCubeSubcubes d S.n S.m),
      gluedFluxNorm hnu S (fluxSlot nu S.LPrime P S.n e) omega R ≤
        volumeAverage (openCubeSet R)
          (fun y => nu * vecNormSq
            (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e) omega y -
              gluedSubcubeGrad hnu S (fluxSlot nu S.LPrime P S.n e) omega y)) :=
  hEnergyMaps_at_gluedMaximizers hnu S (fluxSlot nu S.LPrime P S.n e)

/-! ## 6. The consumer `hFluxAdd` binder -/

/-- **`hFluxAdd` of the consumer at the
glued carriers, with the energy-map step supplied.**

The conclusion is the `hFluxAdd` binder verbatim, at `normFlux := gluedFluxNorm`
and at the glued fields that the consumer uses.  By
`hFluxAdd_of_energyMaps` the only remaining inputs are those of the
printed `e.additivity.error.superdiff` package, namely the two annealed
identities `hAnnealedSub`/`hAnnealedBig`, the integrability bundle, the pigeonhole
input `hPigeon`, and the shell laws `hPrefix hJ2 hJ3 hJ4` with the unit vector
`he`.  The energy-map input is no longer among them. -/
theorem hFluxAdd_of_maximizers [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (S : ScaleSelection) {e : Vec d} (he : vecNormSq e = 1)
    (hFluxInt : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      Integrable (fun omega : ShellSeq d =>
        gluedFluxNorm hnu S (fluxSlot nu S.LPrime P S.n e) omega R) P.toMeasure)
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
    (hEnergyCube : ∀ omega : ShellSeq d, ∀ R ∈ largeCubeSubcubes d S.n S.m,
      IntegrableOn (fun y => -(nu / 2) * vecNormSq
          (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e) omega y) +
        vecDot (fluxSlot nu S.LPrime P S.n e)
          (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e) omega y))
        (cubeSet R) volume)
    {delta etaL : ℝ}
    (hPigeon : |1 - (sigmaBarStarInvSeq nu S.LPrime P S.n)⁻¹ *
      sigmaBarStarInvSeq nu S.LPrime P S.m| ≤ delta + etaL) :
    ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
        ∑ z ∈ largeCubeSubcubes d S.n S.m,
          ∫ omega : ShellSeq d, gluedFluxNorm hnu S (fluxSlot nu S.LPrime P S.n e) omega z
            ∂P.toMeasure ≤ delta + etaL :=
  hFluxAdd_of_energyMaps hnu hPrefix hJ2 hJ3 hJ4 S he
    (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e))
    (gluedSubcubeGrad hnu S (fluxSlot nu S.LPrime P S.n e))
    (gluedFluxNorm hnu S (fluxSlot nu S.LPrime P S.n e))
    (hEnergyMaps_at_gluedMaximizers hnu S (fluxSlot nu S.LPrime P S.n e))
    hFluxInt hEnergyIntDiff hAnnealedSub hAnnealedBig hJsubInt hEnergyInt hEnergyCube
    hPigeon

/-! ## 7. Witness -/

end

end SuperdiffusionCLT.Section3.Terms
