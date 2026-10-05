/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3FluxEnergy
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1ConcDepthB
public import SuperdiffusionCLT.Section3.ResponseFields.LpEstimates
public import SuperdiffusionCLT.Section3.ResponseFields.Norms
public import SuperdiffusionCLT.Section3.Setup.WholeSpaceEnergyC
public import SuperdiffusionCLT.Section2.Annealed.MixingLoewnerStepsB
public import SuperdiffusionCLT.Section2.Annealed.MixingLoewnerSteps
public import SuperdiffusionCLT.Section2.Annealed.Symmetry
public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.Section2.Annealed.Blocks
public import SuperdiffusionCLT.Section2.Localization.CoarseCentering
public import SuperdiffusionCLT.Assumptions.ShellLaw.Nonvacuity

/-!
# `hEnergy`: the four carrier inputs of `e.additivity.error.superdiff`

Step 1 of the proof of `e.RHS.term3.B`.  The
energy factor of the printed Hölder chain is the display
`e.additivity.error.superdiff`, and the assembly
the term-3.B assembly reads
it as its `hEnergy` binder.  This file pins the assembly's *free* `energyL2`
binder to the printed carrier `energyL2Carrier` of
`RHSTerm3FluxEnergy`, and reduces the inputs of
`additivity_error_superdiff` to the printed objects.

## The display, quoted in full

```
\begin{align}
\label{e.additivity.error.superdiff}
\avsum_{z\in 3^n\Zd\cap \cu_m}
\E\Bigl[ \| \s^{\nf12} ( \nabla u_m {-} \nabla u_{n,z} ) \|_{\underline{L}^2(z+\cu_n)}^2 \Bigr]
\leq
C\bigl| 1-\shom_{L',*}(\cu_n)
\shom_{L',*} ^{-1}(\cu_m)
\bigr|
\leq
C\bigl(\delta {+} \eta_L\bigr)
\,.
\end{align}
```

The left member is `avsum_{z∈3^n Z^d ∩ cu_m} E[‖σ^{1/2}(∇u_m − ∇u_{n,z})‖²_{L̲²(z+cu_n)}]`,
which at `σ = ν Id` is exactly the `hEnergy` integrand `energyL2Carrier`; the
middle member is `C|1 − shom_{L',*}(cu_n) shom_{L',*}^{-1}(cu_m)|`, which
`additivity_error_superdiff` produces *signed* (the absolute value is
redundant by `antitone_sigmaBarStarInvSeq`); the right member is the printed
rate `C(δ+η_L)`.

## The four carrier inputs, quoted

`additivity_error_superdiff` carries the
telescoping of the print as four explicit inputs, each read off a printed
display:

**1. `hSecondVar` — `e.secondvar`:**

```
The second variation, or quadratic response identity, says that, for every~$w\in \A(U)$,
\label{e.secondvar}
&- \fint_U \Bigl ( -\frac12 \nabla w \cdot \s\nabla w -p\cdot \a\nabla w+ q\cdot \nabla w \Bigr )
&=
    \fint_U \frac12 \bigl ( \nabla v(\cdot,U,p,q) - \nabla w \bigr )\cdot
    \s\bigl ( \nabla v(\cdot,U,p,q) - \nabla w \bigr )\,.
```

read at `σ = ν Id`, `p = 0`, `q = Q = shom_{L',*}^{1/2}(cu_n)e`, `v = u_{n,z}`
the maximizer on `z + cu_n` and `w = u_m` the competitor — i.e. the identity is
solved for `J_{L'}(z+cu_n,0,Q)` and multiplied by `2`.

**2. `hJbig` — `e.u.k.y.def`:**

```
For each~$y\in\Rd$ and~$k\in\N$, we let~$u_{k,y}$ denote the maximizer in the variational
problem defining~$J_{L'}(y+\cu_k,0,\shom_{L',*}^{\nf12}(\cu_n) e)$; that is,
u_{k,y} \coloneqq v_{L'}\bigl(\cdot,y+\cu_k,0, \shom_{L',*}^{\nf12}(\cu_n) e \bigr)
\label{e.u.k.y.def}
```

i.e. `u_m` attains `J_{L'}(cu_m, 0, Q)`.

**3-4. `hAnnealedSub`, `hAnnealedBig` — `e.homs.defs.U`** (with
the lower-right block of `e.homs.defs.U.0` and the response
value `e.v.ky.energy`):

```
\label{e.homs.defs.U}
\begin{pmatrix}
 \shom_m(U)
& 0
\\ 0
& \shom_{m,*}^{-1}(U)
\end{pmatrix} \,.
```

the annealed response value `E[J_{L'}(U,0,Q)] = ½ shom_{L',*}^{-1}(U)|Q|²` read
on the translated small cubes `z + cu_n` and on `cu_m`.

**The printed side condition.**  The scale ordering
`e.scales.ordering` is the printed restriction on the scales:

```
\label{e.scales.ordering}
m-2h < n < \ell < \ell' < m<L' < L
```

and the text following it states the pigeonhole use of it:

```
... this implies that across the range of scales~$k \in [m-2h,m]$ the ratio of any
two~$\shom_{L',*}(\cu_k)$ is close to one. In particular, the parameters~$n,\ell$
and~$\ell'$ each represent scales which are within this range, that is,
~$n,\ell,\ell' \in [ m-2h,m]$.
```

and the printed pigeonhole itself, `e.pigeon.scalar`:

```
\label{e.pigeon.scalar}
\bigl| \shom_{L',*}(\cu_m)
\shom_{L',*} ^{-1}(\cu_{m-2h}) - 1
\leq
\delta + \eta_L
\,.
```

The `hPigeon` binder is the printed scalar pigeonhole `e.pigeon.scalar` together with the
printed scale containment of `e.scales.ordering` — no invented side condition.

## Main results

* `vecSqAvg_eq_volumeAverage_vecNormSq`, `energyL2Carrier_eq_volumeAverage_cubeSet`,
  `energyL2Carrier_eq_volumeAverage_openCubeSet`: the `vecSqAvg` carrier of
  `RHSTerm3FluxEnergy` is the printed `‖σ^{1/2}(·)‖²_{L̲²}` cube average, so
  the assembly's free binder `energyL2` can be *pinned* to it.
* `hEnergy_at_carriers`: the assembly's `hEnergy` binder shape at the pinned
  carrier, deduced from `additivity_error_superdiff_at_carriers` of
  `RHSTerm3FluxEnergy`.
* `abs_one_sub_inv_mul_le_of_le_mul`: the scalar core of the reduction of
  `hPigeon` to the printed `e.pigeon.scalar` plus the printed
  scale containment of `e.scales.ordering`.
* `vecDot_matVecMul_smulOne` and `annealedCarrierValue_of_quenched`: the
  annealing of the quadratic response value.  The second reduces a carrier that
  is pointwise the quenched response `½ Q·s^-1_{L',*}(U; a_{L'})Q` to the annealed
  value `½ s̄^-1_{L',*}(U)|Q|²`, with no stochastic input left: the expectation is
  moved through the quadratic form by `vecDot_matVecMul_integral` and
  the entry expectations are
  `integral_sigmaStarInvCoarse_cubeSet_eq_sigmaBarStarInv`.
* `hAnnealedBig_of_quenchedResponseValue`: the reduction of `hAnnealedBig` to the
  *deterministic* per-sample response value `e.v.ky.energy` on
  `cu_m`; the scalarization at the centre is the printed fact
  (`sigmaBarStarInv_originCube_eq_smul_one`), so it costs nothing.
* `hAnnealedSub_of_quenchedResponseValue`: the same reduction on each sub-cube
  `R ∈ largeCubeSubcubes d S.n S.m`, where the scalarization is transported from
  the centre by the stationarity centring of the shell law
  (`sigmaBarStarInv_translateCube_eq_originCube`), again at no extra cost.

The two `hAnnealed*_of_quenchedResponseValue`
wrappers are implications whose hypothesis *is* the residual quoted below; no
instance of that hypothesis is claimed here.

## Residuals (named, unchanged in substance)

The two annealed binders `hAnnealedSub`/`hAnnealedBig` remain the residuals of
`hEnergy`, now isolated to a single deterministic object: the *quenched*
response value `e.v.ky.energy`, `J_{L'}(U,0,Q) = ½ Q·s^-1_{L',*}(U; a_{L'})Q` at
the glued field `∇u_m`.  In `hAnnealedBig_of_quenchedResponseValue` /
`hAnnealedSub_of_quenchedResponseValue` every *stochastic* step is discharged
(the annealing is `vecDot_matVecMul_integral` + the entry identity, and
the scalarization/stationarity is the printed scalarization fact + the translate
centring); what is left is the identification of the glued maximizer gradient
with the Chapter 2 canonical maximizer whose response value is
`Book.Ch02.responseJ`, which is `Setup.responseJ_setupMaximizer`, the remaining
gap in `additivity_error_superdiff_eq`.  The pigeonhole input `hPigeon`
is the printed `e.pigeon.scalar` together with the printed scale ordering.  Neither
estimate is false at these carriers, so
no refutation is reported; `d = 1` is out of scope and no counterexample is
considered.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
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

variable {d : ℕ}

/-! ## Pinning the assembly's free `energyL2` binder

The term-3.B assembly takes `energyL2 : ShellSeq d →
TriadicCube d → ℝ` as a *free* datum; here it is pinned to the printed
`σ^{1/2}`-energy in the carrier `energyL2Carrier`,
whose definition is `ν * vecSqAvg R (∇u_m − ∇u_{n,z})`.
The three lemmas below identify that carrier with the printed normalized cube
average `⨍ ν|∇u_m − ∇u_{n,z}|²`, first over the closed cube of `vecSqAvg` and
then over the open cube used by `additivity_error_superdiff`. -/

/-- **`vecSqAvg` is the normalized `L̲²` square average of `vecNormSq`.**  The
carrier `vecSqAvg` is `cubeSquareAverage` of `hilbertifyVecField`, whose norm is
`vecNorm` (`norm_hilbertifyVecField_apply`) with square `vecNormSq`; the
`L̲²(Q)`-norm reading is the `‖·‖²_{L̲²(Q)}` of the printed display. -/
theorem vecSqAvg_eq_volumeAverage_vecNormSq (R : TriadicCube d) (F : Vec d → Vec d) :
    vecSqAvg R F = volumeAverage (cubeSet R) (fun x => vecNormSq (F x)) := by
  unfold vecSqAvg cubeSquareAverage
  refine congrArg (fun g : Vec d → ℝ => volumeAverage (cubeSet R) g) ?_
  funext x
  rw [norm_hilbertifyVecField_apply]
  exact SuperdiffusionCLT.Section3.Setup.vecNorm_sq_eq_vecNormSq (F x)

/-- **`energyL2Carrier` is the printed cube average over the closed cube.** -/
theorem energyL2Carrier_eq_volumeAverage_cubeSet (nu : ℝ) (F G : Vec d → Vec d)
    (R : TriadicCube d) :
    energyL2Carrier nu F G R =
      volumeAverage (cubeSet R) (fun y => nu * vecNormSq (F y - G y)) := by
  unfold energyL2Carrier
  rw [vecSqAvg_eq_volumeAverage_vecNormSq, volumeAverage, volumeAverage,
    MeasureTheory.integral_const_mul]
  ring

/-- **`energyL2Carrier` is the printed cube average over the open cube.**  This
is the shape in which `additivity_error_superdiff` states its conclusion,
the open cube being the domain on which the printed averages and the
Chapter 2 vocabulary live. -/
theorem energyL2Carrier_eq_volumeAverage_openCubeSet (nu : ℝ) (F G : Vec d → Vec d)
    (R : TriadicCube d) :
    energyL2Carrier nu F G R =
      volumeAverage (openCubeSet R) (fun y => nu * vecNormSq (F y - G y)) := by
  rw [energyL2Carrier_eq_volumeAverage_cubeSet,
    ← volumeAverage_cubeSet_eq_openCubeSet R
      (fun y => nu * vecNormSq (F y - G y))]

/-- The assembly's free binder `energyL2` pinned to the printed carrier: the
`σ^{1/2}`-energy of the difference of the two glued gradient fields, at the
sample `omega` and the small cube `R`. -/
def assemblyEnergyCarrier (nu : ℝ) (uMgrad uNGlued : ShellSeq d → Vec d → Vec d)
    (omega : ShellSeq d) (R : TriadicCube d) : ℝ :=
  energyL2Carrier nu (uMgrad omega) (uNGlued omega) R

/-! ## `hEnergy` at the pinned carrier -/

/-- **`hEnergy` of `e.RHS.term3.B` at the pinned carrier.**

This is *verbatim* the `hEnergy` binder of
the term-3.B assembly with the free `energyL2` fixed to
`assemblyEnergyCarrier nu uMgrad uNGlued`; it is deduced from
`additivity_error_superdiff_at_carriers` by the
open-cube identification `energyL2Carrier_eq_volumeAverage_openCubeSet`.  The
remaining hypotheses are exactly the four printed inputs: `hAnnealedSub`,
`hAnnealedBig` (the annealed response value `e.homs.defs.U`), the integrability
side conditions, and `hPigeon` (reduced below to `e.pigeon.scalar` plus the
scale containment). -/
theorem hEnergy_at_carriers
    {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu) {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (S : ScaleSelection) {e : Vec d} (he : vecNormSq e = 1)
    (uMgrad uNGlued : ShellSeq d → Vec d → Vec d)
    (hAnnealedSub : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      ∫ omega : ShellSeq d,
          energySubQCarrier nu P S e uMgrad uNGlued omega R ∂P.toMeasure =
        (1 / 2 : ℝ) * sigmaBarStarInvSeq nu S.LPrime P S.n *
          vecNormSq (fluxSlot nu S.LPrime P S.n e))
    (hAnnealedBig : ∫ omega : ShellSeq d,
          energyBigQCarrier nu P S e uMgrad omega ∂P.toMeasure =
        (1 / 2 : ℝ) * sigmaBarStarInvSeq nu S.LPrime P S.m *
          vecNormSq (fluxSlot nu S.LPrime P S.n e))
    (hJsubInt : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      Integrable (fun omega : ShellSeq d =>
        energySubQCarrier nu P S e uMgrad uNGlued omega R) P.toMeasure)
    (hEnergyInt : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      Integrable (fun omega : ShellSeq d =>
        volumeAverage (openCubeSet R)
          (fun y => -(nu / 2) * vecNormSq (uMgrad omega y) +
            vecDot (fluxSlot nu S.LPrime P S.n e) (uMgrad omega y))) P.toMeasure)
    (hEnergyCube : ∀ omega : ShellSeq d, ∀ R ∈ largeCubeSubcubes d S.n S.m,
      IntegrableOn (fun y => -(nu / 2) * vecNormSq (uMgrad omega y) +
        vecDot (fluxSlot nu S.LPrime P S.n e) (uMgrad omega y)) (cubeSet R) volume)
    {delta etaL : ℝ}
    (hPigeon : |1 - (sigmaBarStarInvSeq nu S.LPrime P S.n)⁻¹ *
      sigmaBarStarInvSeq nu S.LPrime P S.m| ≤ delta + etaL) :
    ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
        ∑ R ∈ largeCubeSubcubes d S.n S.m,
          ∫ omega : ShellSeq d,
            assemblyEnergyCarrier nu uMgrad uNGlued omega R ∂P.toMeasure ≤
      delta + etaL := by
  have hsum :
      (∑ R ∈ largeCubeSubcubes d S.n S.m,
          ∫ omega : ShellSeq d,
            assemblyEnergyCarrier nu uMgrad uNGlued omega R ∂P.toMeasure) =
        ∑ R ∈ largeCubeSubcubes d S.n S.m,
          ∫ omega : ShellSeq d,
            volumeAverage (openCubeSet R)
              (fun y => nu * vecNormSq (uMgrad omega y - uNGlued omega y))
            ∂P.toMeasure := by
    refine Finset.sum_congr rfl fun R _ => ?_
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun omega => ?_)
    show energyL2Carrier nu (uMgrad omega) (uNGlued omega) R = _
    exact energyL2Carrier_eq_volumeAverage_openCubeSet nu _ _ R
  rw [hsum]
  exact additivity_error_superdiff_at_carriers hnu hPrefix hJ2 hJ3 hJ4 S he uMgrad
    uNGlued hAnnealedSub hAnnealedBig hJsubInt hEnergyInt hEnergyCube hPigeon

/-! ## The pigeonhole input `hPigeon` from the printed scalar pigeonhole

The printed side condition is `e.scales.ordering`:
`m-2h < n < ℓ < ℓ' < m < L' < L`, together with the paragraph following it that
places the parameters in the window: "the parameters~$n,\ell$ and~$\ell'$ each
represent scales which are within this range, that is,~$n,\ell,\ell' \in [ m-2h
,m]$".  Only the containment `m - 2h ≤ n` is used: it puts `shom_{L',*}^{-1}
(cu_n)` between `shom_{L',*}^{-1}(cu_m)` and `shom_{L',*}^{-1}(cu_{m-2h})` by
`antitone_sigmaBarStarInvSeq`, so the printed comparison of the two
endpoint scales, `e.pigeon.scalar`, transfers to the pair
`(n, m)` that the `hPigeon` binder asks for. -/

/-- **Scalar core of the pigeonhole.**  If `0 < a`, `b ≤ a` and
`(1 - eps) * a ≤ b`, then `|1 - a⁻¹ * b| ≤ eps`: with `b / a ∈ [1 - eps, 1]` we
get `1 - b / a ∈ [0, eps]`. -/
theorem abs_one_sub_inv_mul_le_of_le_mul {a b eps : ℝ} (ha : 0 < a) (hb : b ≤ a)
    (h : (1 - eps) * a ≤ b) : |1 - a⁻¹ * b| ≤ eps := by
  have hle : a⁻¹ * b ≤ 1 := by
    calc a⁻¹ * b ≤ a⁻¹ * a :=
          mul_le_mul_of_nonneg_left hb (le_of_lt (inv_pos.mpr ha))
      _ = 1 := inv_mul_cancel₀ (ne_of_gt ha)
  have hge : 1 - eps ≤ a⁻¹ * b := by
    have h1 : (1 - eps) * a * a⁻¹ ≤ b * a⁻¹ :=
      mul_le_mul_of_nonneg_right h (inv_nonneg.mpr (le_of_lt ha))
    have h2 : (1 - eps) * a * a⁻¹ = 1 - eps := by
      rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt ha), mul_one]
    have h3 : b * a⁻¹ = a⁻¹ * b := mul_comm b a⁻¹
    linarith only [h1, h2, h3]
  rw [abs_of_nonneg (by linarith only [hle])]
  linarith only [hge]

/-! ## The annealed inputs `hAnnealedSub`/`hAnnealedBig` from the quenched value

The two remaining binders of `hEnergy` are the annealed response values
`e.homs.defs.U` at the glued carriers.  The reduction below replaces the *stochastic*
identity by the *deterministic* per-sample response value `e.v.ky.energy` at the
quenched block `s^-1_{L',*}(U; a_{L'})`: the annealing is then pure
integration, carried by `vecDot_matVecMul_integral` together with the
entry identity `integral_sigmaStarInvCoarse_cubeSet_eq_sigmaBarStarInv`. -/

/-- The quadratic form of a scalar matrix: `Q · (c Id) Q = c |Q|²`. -/
theorem vecDot_matVecMul_smulOne (c : ℝ) (Q : Vec d) :
    vecDot Q (matVecMul (c • (1 : Mat d)) Q) = c * vecNormSq Q := by
  have hm : matVecMul (c • (1 : Mat d)) Q = c • Q := by
    funext i
    simp only [matVecMul, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, Pi.smul_apply,
      mul_comm, ↓reduceIte]
  rw [hm, Homogenization.vecDot_smul_right]
  rfl

/-- **The annealed response value from the quenched one.**  If the carrier `C` is
pointwise the quenched quadratic response `½ Q·s^-1_{L',*}(U; a_{L'})Q` and the
annealed block `s̄^-1_{L',*}(U)` is the scalar matrix it is printed to be
(proved as `sigmaBarStarInv_originCube_eq_smul_one` at the centre), then
the annealed expectation is `½ s̄^-1_{L',*}(U) |Q|²`.  Nothing stochastic remains:
the expectation is moved through the quadratic form by
`vecDot_matVecMul_integral` and each entry expectation is the annealed entry by
`integral_sigmaStarInvCoarse_cubeSet_eq_sigmaBarStarInv`. -/
theorem annealedCarrierValue_of_quenched
    [NeZero d] {nu : ℝ} (hnu : 0 < nu) (LPrime : ℕ) {P : ProbabilityMeasure (ShellSeq d)}
    (R : TriadicCube d) (Q : Vec d) (C : ShellSeq d → ℝ)
    (hValue : ∀ omega : ShellSeq d, C omega =
      (1 / 2 : ℝ) * vecDot Q (matVecMul (sigmaStarInvCoarse (openCubeSet R)
        (coefficientCutoff nu omega LPrime).toCoeffField) Q))
    (hScale : sigmaBarStarInv nu LPrime P (cubeSet R) =
      sigmaBarStarInvScalar nu LPrime P (cubeSet R) • (1 : Mat d)) :
    ∫ omega : ShellSeq d, C omega ∂P.toMeasure =
      (1 / 2 : ℝ) * sigmaBarStarInvScalar nu LPrime P (cubeSet R) * vecNormSq Q := by
  have hfun : (fun omega : ShellSeq d => C omega) = fun omega : ShellSeq d =>
      (1 / 2 : ℝ) * vecDot Q (matVecMul (sigmaStarInvCoarse (openCubeSet R)
        (coefficientCutoff nu omega LPrime).toCoeffField) Q) := funext hValue
  rw [hfun, MeasureTheory.integral_const_mul]
  have hEq : ∀ i j : Fin d,
      (fun w : ShellSeq d => sigmaStarInvCoarse (openCubeSet R)
          (coefficientCutoff nu w LPrime).toCoeffField i j) =
        fun w : ShellSeq d => sigmaStarInvCoarse (cubeSet R)
          (coefficientCutoff nu w LPrime).toCoeffField i j := by
    intro i j
    funext w
    exact congrArg (fun M : Mat d => M i j)
      (sigmaStarInvCoarse_cubeSet_eq_openCubeSet R
        (coefficientCutoff nu w LPrime).toCoeffField).symm
  have hInt : ∀ i j : Fin d, Integrable (fun w : ShellSeq d =>
      sigmaStarInvCoarse (openCubeSet R)
        (coefficientCutoff nu w LPrime).toCoeffField i j) P.toMeasure := by
    intro i j
    rw [hEq i j]
    refine Integrable.of_bound
      (measurable_entry_sigmaStarInvCoarse_cubeSet hnu LPrime R i j).aestronglyMeasurable
      nu⁻¹ (Filter.Eventually.of_forall fun w => ?_)
    simpa only [Real.norm_eq_abs] using
      abs_entry_sigmaStarInvCoarse_cubeSet_le hnu w LPrime R i j
  rw [← SuperdiffusionCLT.Section2.Annealed.vecDot_matVecMul_integral hInt Q]
  have hmat : (fun i j : Fin d => ∫ w : ShellSeq d, sigmaStarInvCoarse (openCubeSet R)
        (coefficientCutoff nu w LPrime).toCoeffField i j ∂P.toMeasure) =
      sigmaBarStarInv nu LPrime P (cubeSet R) := by
    funext i j
    rw [hEq i j]
    exact SuperdiffusionCLT.Section2.Localization.integral_sigmaStarInvCoarse_cubeSet_eq_sigmaBarStarInv
      hnu LPrime P R i j
  rw [hmat, hScale, vecDot_matVecMul_smulOne]
  ring

/-- **`hAnnealedBig` from the quenched response value on `cu_m`.**  The annealed
identity at the large cube is reduced to the deterministic statement that the
carrier `energyBigQCarrier` is the quenched response value `e.v.ky.energy` on
`cu_m`; the scalarization of the annealed block is the printed fact
`sigmaBarStarInv_originCube_eq_smul_one`, so it costs nothing. -/
theorem hAnnealedBig_of_quenchedResponseValue
    {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu) {P : ProbabilityMeasure (ShellSeq d)}
    (hJ4 : ShellLawJ4 d P) (S : ScaleSelection) {e : Vec d}
    (uMgrad : ShellSeq d → Vec d → Vec d)
    (hValue : ∀ omega : ShellSeq d, energyBigQCarrier nu P S e uMgrad omega =
      (1 / 2 : ℝ) * vecDot (fluxSlot nu S.LPrime P S.n e)
        (matVecMul (sigmaStarInvCoarse (openCubeSet (originCube d (S.m : ℤ)))
          (coefficientCutoff nu omega S.LPrime).toCoeffField)
          (fluxSlot nu S.LPrime P S.n e))) :
    ∫ omega : ShellSeq d, energyBigQCarrier nu P S e uMgrad omega ∂P.toMeasure =
      (1 / 2 : ℝ) * sigmaBarStarInvSeq nu S.LPrime P S.m *
        vecNormSq (fluxSlot nu S.LPrime P S.n e) := by
  have h := annealedCarrierValue_of_quenched hnu S.LPrime (originCube d (S.m : ℤ))
    (fluxSlot nu S.LPrime P S.n e) (fun omega => energyBigQCarrier nu P S e uMgrad omega)
    hValue (sigmaBarStarInv_originCube_eq_smul_one hnu S.LPrime hJ4 (S.m : ℤ))
  simpa only [sigmaBarStarInvSeq] using h

/-- **`hAnnealedSub` from the quenched response value on the small cubes.**  On a
sub-cube `R ∈ largeCubeSubcubes d S.n S.m`, the annealed block is the block at the
centred cube `cu_n` by the stationarity centring of the shell law
(`sigmaBarStarInv_translateCube_eq_originCube`, from the prefix assumption and J2),
and the scalarization is again the printed fact at `cu_n`
(`sigmaBarStarInv_originCube_eq_smul_one`).  So the only remaining input is the
deterministic quenched response value at each small cube; the scale ordering
`n < m` carried here is the printed `e.scales.ordering`. -/
theorem hAnnealedSub_of_quenchedResponseValue
    {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu) {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) {e : Vec d} (hnm : S.n < S.m)
    (uMgrad uNGlued : ShellSeq d → Vec d → Vec d)
    (hValue : ∀ omega : ShellSeq d, ∀ R ∈ largeCubeSubcubes d S.n S.m,
      energySubQCarrier nu P S e uMgrad uNGlued omega R =
        (1 / 2 : ℝ) * vecDot (fluxSlot nu S.LPrime P S.n e)
          (matVecMul (sigmaStarInvCoarse (openCubeSet R)
            (coefficientCutoff nu omega S.LPrime).toCoeffField)
            (fluxSlot nu S.LPrime P S.n e))) :
    ∀ R ∈ largeCubeSubcubes d S.n S.m,
      ∫ omega : ShellSeq d,
          energySubQCarrier nu P S e uMgrad uNGlued omega R ∂P.toMeasure =
        (1 / 2 : ℝ) * sigmaBarStarInvSeq nu S.LPrime P S.n *
          vecNormSq (fluxSlot nu S.LPrime P S.n e) := by
  intro R hR
  have hRdesc : R ∈ descendantsAtDepth (originCube d (S.m : ℤ)) (S.m - S.n) := by
    rw [SuperdiffusionCLT.Section2.Localization.descendantsAtDepth_originCube_eq_largeCubeSubcubes
      (n := S.m) (h := S.n)]
    exact hR
  have htranslate : R =
      translateCube R.index (originCube d (S.n : ℤ)) :=
    SuperdiffusionCLT.Section2.Localization.mem_descendantsAtDepth_originCube_eq_translateCube
      hnm hRdesc
  have hmat : sigmaBarStarInv nu S.LPrime P (cubeSet R) =
      sigmaBarStarInv nu S.LPrime P (cubeSet (originCube d (S.n : ℤ))) := by
    rw [htranslate]
    funext i j
    exact SuperdiffusionCLT.Section2.Localization.sigmaBarStarInv_translateCube_eq_originCube
      hnu S.LPrime P hPrefix hJ2 R.index (originCube d (S.n : ℤ)) i j
  have hscalar : sigmaBarStarInvScalar nu S.LPrime P (cubeSet R) =
      sigmaBarStarInvScalar nu S.LPrime P (cubeSet (originCube d (S.n : ℤ))) := by
    show sigmaBarStarInv nu S.LPrime P (cubeSet R) 0 0 =
      sigmaBarStarInv nu S.LPrime P (cubeSet (originCube d (S.n : ℤ))) 0 0
    rw [hmat]
  have hScale : sigmaBarStarInv nu S.LPrime P (cubeSet R) =
      sigmaBarStarInvScalar nu S.LPrime P (cubeSet R) • (1 : Mat d) := by
    rw [hmat, sigmaBarStarInv_originCube_eq_smul_one hnu S.LPrime hJ4 (S.n : ℤ),
      hscalar]
  have h := annealedCarrierValue_of_quenched hnu S.LPrime R
    (fluxSlot nu S.LPrime P S.n e)
    (fun omega => energySubQCarrier nu P S e uMgrad uNGlued omega R)
    (fun omega => hValue omega R hR) hScale
  rw [hscalar] at h
  simpa only [sigmaBarStarInvSeq] using h

end

end SuperdiffusionCLT.Section3.Terms
