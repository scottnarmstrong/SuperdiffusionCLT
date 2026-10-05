/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.MasterIdentityAssembly

/-!
# The master identity reduced to the annealed testing display

The `hIdentity` conjunct of the term-level residue of the master inequality is the
`e.ellsep.testing` identity.  The four printed testing displays of the paper all
rest on the same two inputs — the equation `e.ellsep` that the
maximizer `u_m` satisfies on `cu_m` and the integration by parts that follows it
in the paper — and `ellsep_testing_decomposition`
combines them into the single pointwise display `e.ellsep.testing`.
`master_identity_of_ellsep` takes that combined display as its only
hypothesis of this kind and carries nothing else but the integrability conditions:
the four printed displays, the cube integrability of the four flux pairings
they feed, and the `L²` clause on `a_ℓ ∇u_n` are all discharged.

## What still has to be carried, and why

* `hEllsep` — the pointwise display `e.ellsep.testing` at
  every shell sequence, in the exact shape `ellsep_testing_decomposition`
  concludes.  Its own inputs are not recorded by the maximizer carrier: the
  equation `e.ellsep` is written for the maximizer `u_m = u_{m,0}`, whose
  gradient is the free binder `uMgrad` here, and `Scales.setupMaximizer` does
  not record it; the four printed displays also use the integration by parts
  that follows it in the paper, which uses the
  antisymmetry of `k_{L'}` and `k_ℓ` and the vanishing of the contraction of an
  antisymmetric matrix with the Hessian of `u_m`.  This is the one hypothesis
  that carries that content, in printed shape.
* `hEnergy` — the `P`-integrability of the cube average of `|∇w|²`, under which
  the expectation of the left side is read through its real part.
* `hI1`, `hI2`, `hI3`, `hI4` — the `P`-integrability of the four terms of the
  display, under which the expectation splits (the print's own side conditions).
* `hIntSub` — per shell and per sub-cube of the lattice
  `largeCubeSubcubes d S.n S.m`, the integrability of the second term on the
  sub-cube: the side condition of the lattice bridge
  `volumeAverage_originCube_eq_subcube_avsum`, i.e. of the rewriting by which
  `l.RHS.term2` reads the printed `⨍_{cu_m}` as a lattice average (unstated in
  the paper).
* `hIntCoord` — per shell and per coordinate, the integrability of
  `(k_{ℓ'} − k_ℓ)∇w` on the cube: the side condition of
  `volumeAverage_vecDot_const_left`, i.e. of the rewriting by which
  `l.RHS.term4` moves the constant `p` inside the cube average (unstated in the
  paper).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Setup

open MeasureTheory ProbabilityTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Probability.Stationary
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Terms
open scoped BigOperators ENNReal

noncomputable section

/-- **The master identity `e.ellsep.testing` in the carrier the term lemmas
read it in, from its annealed pointwise form.**  The display `e.ellsep.testing`
of the paper under the expectation, rewritten by the three carrier
rewritings of the module `MasterIdentityAssembly`: the left side through its
real part, the second term through the scale-`n` lattice average, and the
fourth term with the constant `p` inside the cube average.

The conclusion is the `hIdentity` conjunct of the term-level residue of the master inequality,
verbatim.  The four printed testing displays of the paper are discharged together with the
four cube integrability conditions and the `L²` clause that fed them: all of that is
combined by
`Terms.ellsep_testing_decomposition` into the single pointwise hypothesis
`hEllsep`, the display `e.ellsep.testing`, which is carried
in printed shape because its inputs — the equation `e.ellsep` for
the maximizer `u_m`, and the integration by parts that follows it — are not
recorded by the maximizer carrier.  What remains is exactly the integrability
conditions under which the display is read through the expectation and the two
carrier bridges. -/
theorem master_identity_of_ellsep {d : ℕ} (nu : ℝ) (P : ProbabilityMeasure (ShellSeq d))
    (S : ScaleSelection) (p q : Vec d)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (uMgrad uNGlued : ShellSeq d → Vec d → Vec d)
    (hEllsep : ∀ omega : ShellSeq d,
      volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => vecNormSq ((w omega).toH1Function.grad x)) =
        volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
            (fun x => vecDot ((w omega).toH1Function.grad x)
              (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
                (uNGlued omega x) - q)) +
          volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
            (fun x => vecDot ((w omega).toH1Function.grad x)
              (matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x)
                (uNGlued omega x - p))) +
          volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
            (fun x => vecDot ((w omega).toH1Function.grad x)
              (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x)
                (uMgrad omega x - uNGlued omega x))) -
          vecDot p (volumeAverageVec (openCubeSet (originCube d (S.m : ℤ)))
            (fun x => matVecMul (streamCutoff omega S.ellPrime x - streamCutoff omega S.ell x)
              ((w omega).toH1Function.grad x))))
    (hIntSub : ∀ (omega : ShellSeq d), ∀ R ∈ largeCubeSubcubes d S.n S.m,
      IntegrableOn (fun y => vecDot ((w omega).toH1Function.grad y)
        (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
          (coefficientCutoff nu omega S.ell).toCoeffField y)
          (uNGlued omega y - p))) (cubeSet R) volume)
    (hIntCoord : ∀ (omega : ShellSeq d) (i : Fin d), IntegrableOn
      (fun y => matVecMul (streamCutoff omega S.ellPrime y - streamCutoff omega S.ell y)
        ((w omega).toH1Function.grad y) i)
      (openCubeSet (originCube d (S.m : ℤ))) volume)
    (hEnergy : Integrable (fun omega : ShellSeq d =>
      volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => vecNormSq ((w omega).toH1Function.grad x))) P.toMeasure)
    (hI1 : Integrable (fun omega : ShellSeq d =>
      volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => vecDot ((w omega).toH1Function.grad x)
          (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
            (uNGlued omega x) - q))) P.toMeasure)
    (hI2 : Integrable (fun omega : ShellSeq d =>
      volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => vecDot ((w omega).toH1Function.grad x)
          (matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x)
            (uNGlued omega x - p)))) P.toMeasure)
    (hI3 : Integrable (fun omega : ShellSeq d =>
      volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => vecDot ((w omega).toH1Function.grad x)
          (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x)
            (uMgrad omega x - uNGlued omega x)))) P.toMeasure)
    (hI4 : Integrable (fun omega : ShellSeq d =>
      vecDot p (volumeAverageVec (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => matVecMul (streamCutoff omega S.ellPrime x - streamCutoff omega S.ell x)
          ((w omega).toH1Function.grad x)))) P.toMeasure) :
    (∫⁻ omega : ShellSeq d,
        vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (w omega).toH1Function.grad ^ (2 : ℕ) ∂P.toMeasure : ℝ≥0∞).toReal =
      ((∫ omega : ShellSeq d,
            volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
              (fun x => vecDot ((w omega).toH1Function.grad x)
                (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
                    (uNGlued omega x) - q)) ∂P.toMeasure +
          ∫ omega : ShellSeq d,
            ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
              ∑ z ∈ largeCubeSubcubes d S.n S.m,
                volumeAverage (openCubeSet z)
                  (fun y => vecDot ((w omega).toH1Function.grad y)
                    (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
                      (coefficientCutoff nu omega S.ell).toCoeffField y)
                      (uNGlued omega y - p))) ∂P.toMeasure) +
          ∫ omega : ShellSeq d,
            volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
              (fun y => vecDot ((w omega).toH1Function.grad y)
                (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
                  (uMgrad omega y - uNGlued omega y))) ∂P.toMeasure) -
        ∫ omega : ShellSeq d,
          volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
            (fun y => vecDot p (matVecMul (streamCutoff omega S.ellPrime y -
                streamCutoff omega S.ell y) ((w omega).toH1Function.grad y)))
          ∂P.toMeasure := by
  rw [toReal_lintegral_vecCubeLpENorm_two_sq_eq_integral_volumeAverage
      (originCube d (S.m : ℤ)) (fun omega => (w omega).toH1Function.grad)
      (fun omega => (w omega).toH1Function.grad_memVectorL2) hEnergy,
    ellsep_testing_annealed nu P S p q w uMgrad uNGlued hEllsep hI1 hI2 hI3 hI4,
    integral_congr_ae (Filter.Eventually.of_forall fun omega =>
      volumeAverage_vecDot_streamCutoff_sub_eq_subcube_avsum nu omega S.n S.m S.LPrime
        S.ell p (uNGlued omega) ((w omega).toH1Function.grad) (hIntSub omega)),
    integral_congr_ae (Filter.Eventually.of_forall fun omega =>
      (volumeAverage_vecDot_const_left (U := openCubeSet (originCube d (S.m : ℤ)))
        (F := fun y => matVecMul (streamCutoff omega S.ellPrime y -
          streamCutoff omega S.ell y) ((w omega).toH1Function.grad y)) p
        (hIntCoord omega)).symm)]

end

end SuperdiffusionCLT.Section3.Setup