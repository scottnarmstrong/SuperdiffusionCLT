/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Section2.CoefficientCutoff
public import SuperdiffusionCLT.Section3.Setup.Scales
public import SuperdiffusionCLT.Section3.Setup.Parameters
public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementCubeMomentLocality
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementLinftyLargeCube
public import Homogenization.Probability.IndependentSums.GammaSigma.Basic

/-!
# `l.RHS.term3`, first block: splitting and the additivity-defect energy

The first two steps of the proof of `l.RHS.term3` (`e.RHS.term3`).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open Homogenization
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Frozen.Assumptions

noncomputable section

variable {d : ℕ}

/-! ## Cube-average algebra -/

/-- The two realizations of a triadic cube give the same normalized average of
a scalar integrand: they differ by a Lebesgue-null set. -/
private theorem volumeAverage_openCubeSet_eq_cubeSet (Q : TriadicCube d)
    (f : Vec d → ℝ) :
    volumeAverage (openCubeSet Q) f = volumeAverage (cubeSet Q) f := by
  simp only [volumeAverage, volume_openCubeSet_eq_volume_cubeSet]
  rw [MeasureTheory.setIntegral_congr_set (cubeSet_ae_eq_openCubeSet Q)]

private theorem volumeAverage_add' {U : Set (Vec d)} {f g : Vec d → ℝ}
    (hf : IntegrableOn f U volume) (hg : IntegrableOn g U volume) :
    volumeAverage U (fun y => f y + g y) = volumeAverage U f + volumeAverage U g := by
  simp only [volumeAverage]
  rw [MeasureTheory.integral_add hf hg]
  ring

/-- Pulling a constant vector out of a normalized average: the average of the
pairing of a fixed vector against a field is the pairing against the averaged
field. -/
private theorem volumeAverage_vecDot_const_left {U : Set (Vec d)} (c : Vec d)
    {F : Vec d → Vec d} (hF : ∀ i, IntegrableOn (fun y => F y i) U volume) :
    volumeAverage U (fun y => vecDot c (F y)) = vecDot c (volumeAverageVec U F) := by
  have hint : ∫ y in U, (∑ i, c i * F y i) ∂volume
      = ∑ i, c i * ∫ y in U, F y i ∂volume := by
    rw [MeasureTheory.integral_finsetSum _ (fun i _ => (hF i).const_mul (c i))]
    exact Finset.sum_congr rfl fun i _ => MeasureTheory.integral_const_mul _ _
  show (volume U).toReal⁻¹ * ∫ y in U, (∑ i, c i * F y i) ∂volume
      = ∑ i, c i * volumeAverage U (fun y => F y i)
  rw [hint, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by
    simp only [volumeAverage]
    ring

private theorem vecDot_sub_left' (x y z : Vec d) :
    vecDot (x - y) z = vecDot x z - vecDot y z := by
  simp only [vecDot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- **The add-and-subtract step of `e.additivity.defect.splitting`** on a single
cube: the normalized average of the pairing `g · F` splits into
the pairing of the *centered* field `g − (g)_U` against `F` plus the pairing of
the two cube averages. -/
private theorem volumeAverage_vecDot_split {U : Set (Vec d)} (g F : Vec d → Vec d)
    (hgF : IntegrableOn (fun y => vecDot (g y) (F y)) U volume)
    (hF : ∀ i, IntegrableOn (fun y => F y i) U volume) :
    volumeAverage U (fun y => vecDot (g y) (F y)) =
      volumeAverage U (fun y => vecDot (g y - volumeAverageVec U g) (F y)) +
        vecDot (volumeAverageVec U g) (volumeAverageVec U F) := by
  set c : Vec d := volumeAverageVec U g with hc
  have hcF : IntegrableOn (fun y => vecDot c (F y)) U volume := by
    have : (fun y => vecDot c (F y)) = fun y => ∑ i, c i * F y i := rfl
    rw [this]
    exact MeasureTheory.integrable_finsetSum _ (fun i _ => (hF i).const_mul (c i))
  have hsplit : ∀ y : Vec d,
      vecDot (g y) (F y) = vecDot (g y - c) (F y) + vecDot c (F y) := by
    intro y
    rw [vecDot_sub_left']
    ring
  have hcenter : IntegrableOn (fun y => vecDot (g y - c) (F y)) U volume := by
    have heq : (fun y => vecDot (g y - c) (F y))
        = fun y => vecDot (g y) (F y) - vecDot c (F y) := by
      funext y; rw [vecDot_sub_left']
    rw [heq]
    exact hgF.sub hcF
  calc volumeAverage U (fun y => vecDot (g y) (F y))
      = volumeAverage U (fun y => vecDot (g y - c) (F y) + vecDot c (F y)) := by
        exact congrArg (volumeAverage U) (funext hsplit)
    _ = volumeAverage U (fun y => vecDot (g y - c) (F y))
          + volumeAverage U (fun y => vecDot c (F y)) := volumeAverage_add' hcenter hcF
    _ = volumeAverage U (fun y => vecDot (g y - c) (F y)) + vecDot c (volumeAverageVec U F) := by
        rw [volumeAverage_vecDot_const_left c hF]

/-- **The cube-partition step of `e.additivity.defect.splitting`**: the
normalized average over `cu_l` is the plain average of the normalized averages
over the scale-`n` sub-cubes `z + cu_n`, `z ∈ 3^nℤ^d ∩ cu_l`, carried by
`largeCubeSubcubes`. -/
private theorem volumeAverage_originCube_eq_avsum {n l : ℕ} {f : Vec d → ℝ}
    (hf : ∀ R ∈ largeCubeSubcubes d n l, IntegrableOn f (cubeSet R) volume) :
    volumeAverage (openCubeSet (originCube d (l : ℤ))) f =
      ((largeCubeSubcubes d n l).card : ℝ)⁻¹ *
        ∑ R ∈ largeCubeSubcubes d n l, volumeAverage (openCubeSet R) f := by
  rw [volumeAverage_openCubeSet_eq_cubeSet,
    volumeAverage_cubeSet_eq_inv_card_mul_sum_descendants (originCube d (l : ℤ)) (l - n) hf]
  refine congrArg (fun t => ((largeCubeSubcubes d n l).card : ℝ)⁻¹ * t) ?_
  exact Finset.sum_congr rfl fun R _ => (volumeAverage_openCubeSet_eq_cubeSet R f).symm

/-- Integrability on the half-open realization of a triadic cube transfers to
the open realization. -/
private theorem integrableOn_openCubeSet_of_cubeSet {Q : TriadicCube d} {f : Vec d → ℝ}
    (hf : IntegrableOn f (cubeSet Q) volume) : IntegrableOn f (openCubeSet Q) volume :=
  hf.congr_set_ae (cubeSet_ae_eq_openCubeSet Q).symm

/-- **`e.additivity.defect.splitting`, the cube-average identity**.
Writing `⨍_{cu_l}` as the plain average over the scale-`n`
sub-cubes `z + cu_n`, `z ∈ 3^nℤ^d ∩ cu_l`, and adding and subtracting the
sub-cube average `(g)_{z+cu_n}` of the first factor, the paired average splits
into a *centered* small-cube term and a term in which both factors have been
averaged over the small cube.

This is the purely algebraic content of the printed display; the paper
instantiates it at `g = ∇w` and `F = a_{L'}(∇u_m − ∇u_n)`, where the second
factor is read cube by cube through `e.u.k.def`. -/
theorem volumeAverage_avsum_centered_splitting {n l : ℕ} (g F : Vec d → Vec d)
    (hF : ∀ R ∈ largeCubeSubcubes d n l, ∀ i,
      IntegrableOn (fun y => F y i) (cubeSet R) volume)
    (hgF : ∀ R ∈ largeCubeSubcubes d n l,
      IntegrableOn (fun y => vecDot (g y) (F y)) (cubeSet R) volume) :
    volumeAverage (openCubeSet (originCube d (l : ℤ))) (fun y => vecDot (g y) (F y)) =
      ((largeCubeSubcubes d n l).card : ℝ)⁻¹ *
          ∑ R ∈ largeCubeSubcubes d n l,
            volumeAverage (openCubeSet R)
              (fun y => vecDot (g y - volumeAverageVec (openCubeSet R) g) (F y)) +
        ((largeCubeSubcubes d n l).card : ℝ)⁻¹ *
          ∑ R ∈ largeCubeSubcubes d n l,
            vecDot (volumeAverageVec (openCubeSet R) g)
              (volumeAverageVec (openCubeSet R) F) := by
  rw [volumeAverage_originCube_eq_avsum hgF, ← mul_add, ← Finset.sum_add_distrib]
  refine congrArg (fun t => ((largeCubeSubcubes d n l).card : ℝ)⁻¹ * t) ?_
  refine Finset.sum_congr rfl fun R hR => ?_
  exact volumeAverage_vecDot_split g F
    (integrableOn_openCubeSet_of_cubeSet (hgF R hR))
    (fun i => integrableOn_openCubeSet_of_cubeSet (hF R hR i))

/-! ## `e.additivity.defect.splitting` -/

/-- **`e.additivity.defect.splitting`**.  The additivity defect tested against `∇w` on `cu_m` splits
into

* the small-cube oscillation term `E[avsum_z ⨍_{z+cu_n}(∇w − (∇w)_{z+cu_n})·
  a_{L'}(∇u_m − ∇u_{n,z})]`, estimated in Step 1 (`e.RHS.term3.B`), and
* the coarse-grained average term `E[avsum_z (∇w)_{z+cu_n}·
  (a_{L'}(∇u_m − ∇u_{n,z}))_{z+cu_n}]`, estimated in Steps 2 and 3.

The glued field `∇u_n` of `e.u.k.def` is a free binder
`uNGlued` here: on the sub-cube `z + cu_n` it *is* the piece `∇u_{n,z}`, which
is what makes the printed rewriting an identity rather than a definition (the
paper does not remark on this).  `uMgrad` is
`∇u_m = ∇u_{m,0}`.

The hypotheses are the integrability of the flux difference and of its pairing
with `∇w` on each sub-cube, and the `P`-integrability of the two resulting
terms; no proof step of the paper is carried in a hypothesis. -/
theorem additivity_defect_splitting
    (nu : ℝ) (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (uMgrad uNGlued : ShellSeq d → Vec d → Vec d)
    (hF : ∀ omega : ShellSeq d, ∀ R ∈ largeCubeSubcubes d S.n S.m, ∀ i : Fin d,
      IntegrableOn (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
        (uMgrad omega y - uNGlued omega y) i) (cubeSet R) volume)
    (hgF : ∀ omega : ShellSeq d, ∀ R ∈ largeCubeSubcubes d S.n S.m,
      IntegrableOn (fun y => vecDot ((w omega).toH1Function.grad y)
        (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
          (uMgrad omega y - uNGlued omega y))) (cubeSet R) volume)
    (hosc : Integrable (fun omega : ShellSeq d =>
      ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
        ∑ R ∈ largeCubeSubcubes d S.n S.m,
          volumeAverage (openCubeSet R)
            (fun y => vecDot ((w omega).toH1Function.grad y -
                volumeAverageVec (openCubeSet R) ((w omega).toH1Function.grad))
              (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
                (uMgrad omega y - uNGlued omega y)))) P.toMeasure)
    (hcg : Integrable (fun omega : ShellSeq d =>
      ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
        ∑ R ∈ largeCubeSubcubes d S.n S.m,
          vecDot (volumeAverageVec (openCubeSet R) ((w omega).toH1Function.grad))
            (volumeAverageVec (openCubeSet R)
              (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
                (uMgrad omega y - uNGlued omega y)))) P.toMeasure) :
    ∫ omega : ShellSeq d,
        volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun y => vecDot ((w omega).toH1Function.grad y)
            (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
              (uMgrad omega y - uNGlued omega y))) ∂P.toMeasure =
      (∫ omega : ShellSeq d,
        ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
          ∑ R ∈ largeCubeSubcubes d S.n S.m,
            volumeAverage (openCubeSet R)
              (fun y => vecDot ((w omega).toH1Function.grad y -
                  volumeAverageVec (openCubeSet R) ((w omega).toH1Function.grad))
                (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
                  (uMgrad omega y - uNGlued omega y))) ∂P.toMeasure) +
      (∫ omega : ShellSeq d,
        ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
          ∑ R ∈ largeCubeSubcubes d S.n S.m,
            vecDot (volumeAverageVec (openCubeSet R) ((w omega).toH1Function.grad))
              (volumeAverageVec (openCubeSet R)
                (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
                  (uMgrad omega y - uNGlued omega y))) ∂P.toMeasure) := by
  have hpt : ∀ omega : ShellSeq d,
      volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun y => vecDot ((w omega).toH1Function.grad y)
            (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
              (uMgrad omega y - uNGlued omega y))) =
        ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
            ∑ R ∈ largeCubeSubcubes d S.n S.m,
              volumeAverage (openCubeSet R)
                (fun y => vecDot ((w omega).toH1Function.grad y -
                    volumeAverageVec (openCubeSet R) ((w omega).toH1Function.grad))
                  (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
                    (uMgrad omega y - uNGlued omega y))) +
          ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
            ∑ R ∈ largeCubeSubcubes d S.n S.m,
              vecDot (volumeAverageVec (openCubeSet R) ((w omega).toH1Function.grad))
                (volumeAverageVec (openCubeSet R)
                  (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
                    (uMgrad omega y - uNGlued omega y))) := fun omega =>
    volumeAverage_avsum_centered_splitting (n := S.n) (l := S.m)
      ((w omega).toH1Function.grad)
      (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
        (uMgrad omega y - uNGlued omega y)) (hF omega) (hgF omega)
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
    MeasureTheory.integral_add hosc hcg]

/-! ## `e.additivity.error.superdiff`: the second-variation telescoping -/

/-- **The telescoping identity behind `e.additivity.error.superdiff`**,
The paper compresses into one sentence the passage from the second-variation
identity `e.secondvar` to the displayed averaged energy defect (which requires
`u_m` restricted to `z+cu_n` to be admissible in the variational problem on
`z+cu_n`, and the resulting telescoping of `J` over the subcubes).  This is the
quantitative heart of the section.  The identity below is exactly that
telescoping, carried out in full.

The two inputs of the paper that have no Lean carrier are explicit hypotheses, each
in the shape the paper prints it in:

* `hSecondVar` is `e.secondvar` at `σ = ν Id`, `p = 0`,
  `q = Q = shom_{L',*}^{1/2}(cu_n) e`, with `v = u_{n,z}` the maximizer on
  `z + cu_n` and `w = u_m` the competitor, multiplied by `2`.  Its use
  presupposes that `u_m` restricted to `z + cu_n` is admissible there, which is
  the first point the paper compresses.
* `hJbig` says that `u_m` attains `J_{L'}(cu_m, 0, Q)`, i.e. that `u_{m,0}` is
  the maximizer of `e.J.def` on `cu_m` (`e.u.k.y.def`).
* `hAnnealedSub`, `hAnnealedBig` are `e.homs.defs.U` read on the translated
  small cubes and on `cu_m`: the annealed response value of the pure-flux slot
  is `E[J_{L'}(U,0,Q)] = ½ shom_{L',*}^{-1}(U) |Q|²`, which on `z + cu_n` is
  independent of `z` by stationarity.  This is the second point the paper
  compresses (it never displays the annealed response value; it telescopes `J`
  directly).

The conclusion is the exact printed middle member
`C|1 − shom_{L',*}(cu_n) shom_{L',*}^{-1}(cu_m)|` with `C = 1` and with the
absolute value removed, because the telescoping produces the signed quantity;
the annealed lower blocks are `sigmaBarStarInvSeq` and
`shom_{L',*}(cu_n) = (shom_{L',*}^{-1}(cu_n))⁻¹`. -/
theorem additivity_error_superdiff_eq
    [NeZero d] {nu : ℝ} (hnu : 0 < nu) {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (S : ScaleSelection) {e : Vec d} (he : vecNormSq e = 1)
    (uMgrad uNGlued : ShellSeq d → Vec d → Vec d)
    (JsubQ : ShellSeq d → TriadicCube d → ℝ) (JbigQ : ShellSeq d → ℝ)
    (hSecondVar : ∀ omega : ShellSeq d, ∀ R ∈ largeCubeSubcubes d S.n S.m,
      volumeAverage (openCubeSet R)
          (fun y => nu * vecNormSq (uMgrad omega y - uNGlued omega y)) =
        2 * JsubQ omega R -
          2 * volumeAverage (openCubeSet R)
            (fun y => -(nu / 2) * vecNormSq (uMgrad omega y) +
              vecDot (fluxSlot nu S.LPrime P S.n e) (uMgrad omega y)))
    (hJbig : ∀ omega : ShellSeq d,
      volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun y => -(nu / 2) * vecNormSq (uMgrad omega y) +
            vecDot (fluxSlot nu S.LPrime P S.n e) (uMgrad omega y)) = JbigQ omega)
    (hAnnealedSub : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      ∫ omega : ShellSeq d, JsubQ omega R ∂P.toMeasure =
        (1 / 2 : ℝ) * sigmaBarStarInvSeq nu S.LPrime P S.n *
          vecNormSq (fluxSlot nu S.LPrime P S.n e))
    (hAnnealedBig : ∫ omega : ShellSeq d, JbigQ omega ∂P.toMeasure =
      (1 / 2 : ℝ) * sigmaBarStarInvSeq nu S.LPrime P S.m *
        vecNormSq (fluxSlot nu S.LPrime P S.n e))
    (hJsubInt : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      Integrable (fun omega : ShellSeq d => JsubQ omega R) P.toMeasure)
    (hEnergyInt : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      Integrable (fun omega : ShellSeq d =>
        volumeAverage (openCubeSet R)
          (fun y => -(nu / 2) * vecNormSq (uMgrad omega y) +
            vecDot (fluxSlot nu S.LPrime P S.n e) (uMgrad omega y))) P.toMeasure)
    (hEnergyCube : ∀ omega : ShellSeq d, ∀ R ∈ largeCubeSubcubes d S.n S.m,
      IntegrableOn (fun y => -(nu / 2) * vecNormSq (uMgrad omega y) +
        vecDot (fluxSlot nu S.LPrime P S.n e) (uMgrad omega y)) (cubeSet R) volume) :
    ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
        ∑ R ∈ largeCubeSubcubes d S.n S.m,
          ∫ omega : ShellSeq d,
            volumeAverage (openCubeSet R)
              (fun y => nu * vecNormSq (uMgrad omega y - uNGlued omega y))
            ∂P.toMeasure =
      1 - (sigmaBarStarInvSeq nu S.LPrime P S.n)⁻¹ *
        sigmaBarStarInvSeq nu S.LPrime P S.m := by
  classical
  set D : Finset (TriadicCube d) := largeCubeSubcubes d S.n S.m with hD
  set Q : Vec d := fluxSlot nu S.LPrime P S.n e with hQ
  set g : ShellSeq d → Vec d → ℝ := fun omega y =>
    -(nu / 2) * vecNormSq (uMgrad omega y) + vecDot Q (uMgrad omega y) with hg
  have hcard0 : (0 : ℝ) < (D.card : ℝ) := by
    exact_mod_cast Finset.card_pos.2 (largeCubeSubcubes_nonempty d S.n S.m)
  -- the per-cube expectation of the energy defect
  have hstep : ∀ R ∈ D,
      ∫ omega : ShellSeq d,
          volumeAverage (openCubeSet R)
            (fun y => nu * vecNormSq (uMgrad omega y - uNGlued omega y)) ∂P.toMeasure =
        2 * (∫ omega : ShellSeq d, JsubQ omega R ∂P.toMeasure) -
          2 * ∫ omega : ShellSeq d, volumeAverage (openCubeSet R) (g omega) ∂P.toMeasure := by
    intro R hR
    have hfun : (fun omega : ShellSeq d =>
        volumeAverage (openCubeSet R)
          (fun y => nu * vecNormSq (uMgrad omega y - uNGlued omega y))) =
        fun omega : ShellSeq d =>
          2 * JsubQ omega R - 2 * volumeAverage (openCubeSet R) (g omega) :=
      funext fun omega => hSecondVar omega R hR
    rw [hfun, MeasureTheory.integral_sub ((hJsubInt R hR).const_mul 2)
      ((hEnergyInt R hR).const_mul 2), MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
  rw [Finset.sum_congr rfl hstep, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  -- the annealed response values on the small cubes
  have hsum1 : ∑ R ∈ D, ∫ omega : ShellSeq d, JsubQ omega R ∂P.toMeasure =
      (D.card : ℝ) * ((1 / 2 : ℝ) * sigmaBarStarInvSeq nu S.LPrime P S.n * vecNormSq Q) := by
    rw [Finset.sum_congr rfl hAnnealedSub, Finset.sum_const, nsmul_eq_mul]
  -- the small-cube averages of the `u_m` energy reassemble to the `cu_m` average
  have hsum2 : ∑ R ∈ D, ∫ omega : ShellSeq d,
      volumeAverage (openCubeSet R) (g omega) ∂P.toMeasure =
      (D.card : ℝ) * ∫ omega : ShellSeq d, JbigQ omega ∂P.toMeasure := by
    rw [← MeasureTheory.integral_finsetSum _ (fun R hR => hEnergyInt R hR),
      ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun omega => ?_)
    have hpart := volumeAverage_originCube_eq_avsum (n := S.n) (l := S.m)
      (f := g omega) (hEnergyCube omega)
    rw [hJbig omega, ← hD] at hpart
    show ∑ R ∈ D, volumeAverage (openCubeSet R) (g omega) = (D.card : ℝ) * JbigQ omega
    rw [hpart, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hcard0), one_mul]
  rw [hsum1, hsum2, hAnnealedBig]
  have hQnorm : vecNormSq Q = (sigmaBarStarInvSeq nu S.LPrime P S.n)⁻¹ :=
    vecNormSq_fluxSlot hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n he
  have hpos : 0 < sigmaBarStarInvSeq nu S.LPrime P S.n :=
    sigmaBarStarInvSeq_pos hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n
  rw [hQnorm]
  field_simp


/-- **`e.additivity.error.superdiff`**, in the printed form

`avsum_{z ∈ 3^nℤ^d ∩ cu_m} E[‖σ^{1/2}(∇u_m − ∇u_{n,z})‖²_{L̲²(z+cu_n)}]
   ≤ C|1 − shom_{L',*}(cu_n) shom_{L',*}^{-1}(cu_m)| ≤ C(δ + η_L)`

with `C = 1`.  The telescoping in fact produces the *signed* quantity
`1 − shom_{L',*}(cu_n) shom_{L',*}^{-1}(cu_m)`, which is nonnegative because
`shom_{L',*}^{-1}(cu_k)` is nonincreasing in `k` (`antitone_sigmaBarStarInvSeq`)
and `n < m`, so the printed absolute value is redundant.  The first inequality
is the identity
`additivity_error_superdiff_eq` (the second-variation telescoping); the second
is `e.pigeon.scalar` transported from the printed pair of
scales `(m, m−2h)` to the pair `(n, m)` by
`p.sstar.lower.bound#pigeon-range-comparability`, which is the
hypothesis `hPigeon`.  The transport also reverses the orientation of the
printed ratio: `e.pigeon.scalar` bounds
`|shom_{L',*}(cu_m) shom_{L',*}^{-1}(cu_{m−2h}) − 1|`, a ratio of the coarser
scale to the finer one, whereas the display here needs the reciprocal
orientation `shom_{L',*}(cu_n) shom_{L',*}^{-1}(cu_m)`; the comparability statement licenses this
only through the comparability of all `shom_{L',*}(cu_k)`, `k ∈ [m−2h, m]`.
Neither `δ` nor `η_L` is a Lean object of this development: `δ` is the constant
of `e.pigeon.scalar` and `η_L` the localization
error `Cν^{-5}L3^{-(L'-m)}` carried by the annealed
cutoff comparison, so both enter as the explicit binders
`delta`, `etaL` through `hPigeon` — not as outputs of the averaged gauged
comparison `localization_average` (`Frozen/Section2/LocalizationAverage.lean`),
which supplies nothing here. -/
theorem additivity_error_superdiff
    [NeZero d] {nu : ℝ} (hnu : 0 < nu) {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (S : ScaleSelection) {e : Vec d} (he : vecNormSq e = 1)
    (uMgrad uNGlued : ShellSeq d → Vec d → Vec d)
    (JsubQ : ShellSeq d → TriadicCube d → ℝ) (JbigQ : ShellSeq d → ℝ)
    (hSecondVar : ∀ omega : ShellSeq d, ∀ R ∈ largeCubeSubcubes d S.n S.m,
      volumeAverage (openCubeSet R)
          (fun y => nu * vecNormSq (uMgrad omega y - uNGlued omega y)) =
        2 * JsubQ omega R -
          2 * volumeAverage (openCubeSet R)
            (fun y => -(nu / 2) * vecNormSq (uMgrad omega y) +
              vecDot (fluxSlot nu S.LPrime P S.n e) (uMgrad omega y)))
    (hJbig : ∀ omega : ShellSeq d,
      volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun y => -(nu / 2) * vecNormSq (uMgrad omega y) +
            vecDot (fluxSlot nu S.LPrime P S.n e) (uMgrad omega y)) = JbigQ omega)
    (hAnnealedSub : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      ∫ omega : ShellSeq d, JsubQ omega R ∂P.toMeasure =
        (1 / 2 : ℝ) * sigmaBarStarInvSeq nu S.LPrime P S.n *
          vecNormSq (fluxSlot nu S.LPrime P S.n e))
    (hAnnealedBig : ∫ omega : ShellSeq d, JbigQ omega ∂P.toMeasure =
      (1 / 2 : ℝ) * sigmaBarStarInvSeq nu S.LPrime P S.m *
        vecNormSq (fluxSlot nu S.LPrime P S.n e))
    (hJsubInt : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      Integrable (fun omega : ShellSeq d => JsubQ omega R) P.toMeasure)
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
            volumeAverage (openCubeSet R)
              (fun y => nu * vecNormSq (uMgrad omega y - uNGlued omega y))
            ∂P.toMeasure ≤ delta + etaL := by
  rw [additivity_error_superdiff_eq hnu hPrefix hJ2 hJ3 hJ4 S he uMgrad uNGlued
    JsubQ JbigQ hSecondVar hJbig hAnnealedSub hAnnealedBig hJsubInt hEnergyInt hEnergyCube]
  exact le_of_abs_le hPigeon

/-! ## The fourth moment of a `Γ₁`-tailed observable -/

/-- **From a `Γ₁` envelope to a fourth moment.**  If a nonnegative observable
satisfies the weak-Orlicz relation `Y = O_{Γ₁}(A)` of the manuscript's
`e.O.notation`, then `E[Y⁴]^{1/4} ≤ 4 C_{Γ₁} A`.

This is the Chapter 4 moment calculus
(`Homogenization.IndependentSums.hasGammaMomentGrowthWith_of_isBigO_gammaSigma`)
at `σ = 1` and `p = 4`; the local `Probability/OrliczMoments.lean` covers only
`σ = 2`. -/
theorem rpow_four_moment_le_of_isBigO_gammaSigma_one {Omega : Type*}
    [MeasurableSpace Omega] {mu : Measure Omega}
    [MeasureTheory.IsProbabilityMeasure mu] {Y : Omega → ℝ} {A : ℝ} (hA : 0 < A)
    (hYnonneg : ∀ omega, 0 ≤ Y omega) (hYm : AEMeasurable Y mu)
    (hY : IndependentSums.IsBigO mu (IndependentSums.gammaSigma 1) Y A) :
    (∫ omega, Y omega ^ (4 : ℝ) ∂mu) ^ ((1 : ℝ) / 4) ≤
      4 * (IndependentSums.gammaMomentConst 1 * A) := by
  set M : ℝ := IndependentSums.gammaMomentConst 1 * A with hM
  have hMpos : 0 < M :=
    mul_pos (IndependentSums.gammaMomentConst_pos (σ := 1) one_pos) hA
  have hgrowth := IndependentSums.hasGammaMomentGrowthWith_of_isBigO_gammaSigma
    (μ := mu) (X := Y) (K := A) (σ := 1) one_pos hA hYm hY
  obtain ⟨-, hbound⟩ := hgrowth (p := (4 : ℝ)) (by norm_num)
  have habs : (fun omega => |Y omega| ^ (4 : ℝ)) = fun omega => Y omega ^ (4 : ℝ) :=
    funext fun omega => by rw [abs_of_nonneg (hYnonneg omega)]
  rw [habs] at hbound
  have hpow : (M * (4 : ℝ) ^ ((1 : ℝ)⁻¹)) = M * 4 := by
    rw [inv_one, Real.rpow_one]
  rw [hpow] at hbound
  have hnn : (0 : ℝ) ≤ ∫ omega, Y omega ^ (4 : ℝ) ∂mu :=
    MeasureTheory.integral_nonneg fun omega => Real.rpow_nonneg (hYnonneg omega) _
  have hM4 : (0 : ℝ) ≤ M * 4 := by positivity
  have hmono := Real.rpow_le_rpow hnn hbound (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 4)
  have hcollapse : ((M * 4) ^ (4 : ℝ)) ^ ((1 : ℝ) / 4) = M * 4 := by
    rw [← Real.rpow_mul hM4]
    norm_num
  rw [hcollapse] at hmono
  calc (∫ omega, Y omega ^ (4 : ℝ) ∂mu) ^ ((1 : ℝ) / 4) ≤ M * 4 := hmono
    _ = 4 * M := by ring

/-! ## `l.RHS.term3#multiscale-poincare-flux` -/

/-- **`l.RHS.term3#multiscale-poincare-flux`**,
the flux estimate in the proof of `l.RHS.term3`:

`E[‖a_{L'}(∇u_m − ∇u_{n,z})‖^{3/2}_{H̲^{-1}(z+cu_n)}]
   ≤ C 3^{3n/2}(L'ν⁻¹)^{3/4} E[‖σ^{1/2}(∇u_m − ∇u_{n,z})‖²_{L̲²(z+cu_n)}]^{3/4}`.

The three quantities of the display are free binders, because none of them has
a carrier on the translated cube `z + cu_n`:

* `fluxNegNorm ω R` is `‖a_{L'}(∇u_m − ∇u_{n,z})‖_{H̲^{-1}(z+cu_n)}`;
* `energyL2 ω R` is `‖σ^{1/2}(∇u_m − ∇u_{n,z})‖²_{L̲²(z+cu_n)}` at `σ = ν Id`;
* `blockWeight ω R` is the printed weight
  `∑_{j ≤ n} 3^{j−n} max_{z' ∈ z + 3^jℤ^d ∩ cu_n} |b_{L'}(z'+cu_j)|^{3/4}`.

Two hypotheses carry the two steps of the printed chain that the paper does
not supply in a form this development can apply:

* `hPointwise` is the first two inequalities of the chain — the multiscale
  Poincaré inequality `ext.AK.HC.multiscale.Poincare` at `s = 1`, `p = 2`
  followed by `e.energymaps.nonsymm.flux` — in their quenched, `3/2`-power
  form.  Note that the paper's second display is not literally the `3/2`
  power of the first: it carries the exponent `3/4` *inside* the depth sum
  (`∑_j 3^{j−n} max_{z'}|b_{L'}(z'+cu_j)|^{3/4}`), which is the convexity
  rearrangement `(∑ w_j x_j)^{3/2} ≤ (∑ w_j)^{1/2} ∑ w_j x_j^{3/2}` for the
  weights `w_j = 3^{j−n}`, `∑_{j ≤ n} w_j = 3/2`; the paper performs it
  silently, and it is part of what this hypothesis carries.  The
  multiscale-Poincaré bridge
  `matHatNegENorm_le_cubeMultiscaleDepthSum`
  (`Section2/Norms/MultiscalePoincareFullGradient.lean`) proves exactly this direction,
  but only for *matrix* fields and only for a `FractionalOrder` exponent
  `0 < s < 1`; the paper uses it at `s = 1` on the *vector* flux field
  `a_{L'}(∇u_m − ∇u_{n,z})`, and the required vector/`s = 1` specialization,
  together with the linearity of the admissible class `A(U)` that makes the
  difference of two maximizers admissible, is not available here.
* `hBlockOrlicz` is the maximum-of-Orlicz envelope of the printed proof.  The
  paper simply asserts the maximum envelope; the passage needs a uniform-in-`j`,
  uniform-in-`z'` Orlicz bound for the coarse blocks over the infinite family of
  scales `j ∈ (−∞, n]`, and
  neither `l.maximums.Gamma.s` nor the minimal-scale statement of
  `l.bfAm.ellip` is cited for it.  It is taken here in the `O_{Γ₁}` shape of
  `e.Enaught.mixing` (compare `envelopeRescale_ellipticity`), and
  converted to the fourth moment the Hölder step needs by
  `rpow_four_moment_le_of_isBigO_gammaSigma_one`.

Everything else — the Hölder decoupling with exponents `(4/3, 4)` and the
`Γ₁`-tail-to-moment conversion — is proved. -/
theorem multiscale_poincare_flux
    {nu : ℝ} (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d))
    {S : ScaleSelection} (hSorder : ScalesOrdering S)
    (fluxNegNorm energyL2 blockWeight : ShellSeq d → TriadicCube d → ℝ)
    (R : TriadicCube d) {C1 Cb : ℝ} (hC1 : 0 ≤ C1) (hCb : 0 < Cb)
    (hEnergyNonneg : ∀ omega : ShellSeq d, 0 ≤ energyL2 omega R)
    (hBlockNonneg : ∀ omega : ShellSeq d, 0 ≤ blockWeight omega R)
    (hPointwise : ∀ omega : ShellSeq d,
      fluxNegNorm omega R ^ ((3 : ℝ) / 2) ≤
        C1 * (3 : ℝ) ^ ((3 * (S.n : ℝ)) / 2) *
          (energyL2 omega R ^ ((3 : ℝ) / 4) * blockWeight omega R))
    (hBlockOrlicz : IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 1)
      (fun omega : ShellSeq d => blockWeight omega R)
      (Cb * (((S.LPrime : ℕ) : ℝ) * nu⁻¹) ^ ((3 : ℝ) / 4)))
    (hBlockMeas : AEMeasurable (fun omega : ShellSeq d => blockWeight omega R) P.toMeasure)
    (hFluxInt : Integrable
      (fun omega : ShellSeq d => fluxNegNorm omega R ^ ((3 : ℝ) / 2)) P.toMeasure)
    (hProdInt : Integrable (fun omega : ShellSeq d =>
      energyL2 omega R ^ ((3 : ℝ) / 4) * blockWeight omega R) P.toMeasure)
    (hMemE : MemLp (fun omega : ShellSeq d => energyL2 omega R ^ ((3 : ℝ) / 4))
      (ENNReal.ofReal ((4 : ℝ) / 3)) P.toMeasure)
    (hMemB : MemLp (fun omega : ShellSeq d => blockWeight omega R)
      (ENNReal.ofReal (4 : ℝ)) P.toMeasure) :
    ∫ omega : ShellSeq d, fluxNegNorm omega R ^ ((3 : ℝ) / 2) ∂P.toMeasure ≤
      C1 * (4 * IndependentSums.gammaMomentConst 1 * Cb) *
        (3 : ℝ) ^ ((3 * (S.n : ℝ)) / 2) *
        (((S.LPrime : ℕ) : ℝ) * nu⁻¹) ^ ((3 : ℝ) / 4) *
        (∫ omega : ShellSeq d, energyL2 omega R ∂P.toMeasure) ^ ((3 : ℝ) / 4) := by
  have hLPrime : (0 : ℝ) < ((S.LPrime : ℕ) : ℝ) := by
    have h : 0 < S.LPrime := lt_of_le_of_lt (Nat.zero_le S.m) hSorder.m_lt_LPrime
    exact_mod_cast h
  have hApos : (0 : ℝ) < Cb * (((S.LPrime : ℕ) : ℝ) * nu⁻¹) ^ ((3 : ℝ) / 4) := by
    have : (0 : ℝ) < ((S.LPrime : ℕ) : ℝ) * nu⁻¹ := mul_pos hLPrime (inv_pos.2 hnu)
    exact mul_pos hCb (Real.rpow_pos_of_pos this _)
  -- Hölder with the conjugate pair `(4/3, 4)`
  have hconj : Real.HolderConjugate ((4 : ℝ) / 3) 4 :=
    ⟨by norm_num, by norm_num, by norm_num⟩
  have hholder := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := P.toMeasure) hconj
    (f := fun omega : ShellSeq d => energyL2 omega R ^ ((3 : ℝ) / 4))
    (g := fun omega : ShellSeq d => blockWeight omega R)
    (Filter.Eventually.of_forall fun omega => Real.rpow_nonneg (hEnergyNonneg omega) _)
    (Filter.Eventually.of_forall hBlockNonneg) hMemE hMemB
  have hpow : ∀ omega : ShellSeq d,
      (energyL2 omega R ^ ((3 : ℝ) / 4)) ^ ((4 : ℝ) / 3) = energyL2 omega R := by
    intro omega
    rw [← Real.rpow_mul (hEnergyNonneg omega)]
    norm_num
  have hEint : (∫ omega : ShellSeq d,
      (energyL2 omega R ^ ((3 : ℝ) / 4)) ^ ((4 : ℝ) / 3) ∂P.toMeasure) =
      ∫ omega : ShellSeq d, energyL2 omega R ∂P.toMeasure :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpow)
  have hexp : (1 : ℝ) / ((4 : ℝ) / 3) = (3 : ℝ) / 4 := by norm_num
  rw [hEint, hexp] at hholder
  -- the fourth moment of the block weight
  have hmoment := rpow_four_moment_le_of_isBigO_gammaSigma_one hApos
    (fun omega => hBlockNonneg omega) hBlockMeas hBlockOrlicz
  -- the pointwise bound, integrated
  have hstep1 : ∫ omega : ShellSeq d, fluxNegNorm omega R ^ ((3 : ℝ) / 2) ∂P.toMeasure ≤
      C1 * (3 : ℝ) ^ ((3 * (S.n : ℝ)) / 2) *
        ∫ omega : ShellSeq d,
          energyL2 omega R ^ ((3 : ℝ) / 4) * blockWeight omega R ∂P.toMeasure := by
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_mono hFluxInt
      (hProdInt.const_mul (C1 * (3 : ℝ) ^ ((3 * (S.n : ℝ)) / 2))) hPointwise
  have hcoeff : (0 : ℝ) ≤ C1 * (3 : ℝ) ^ ((3 * (S.n : ℝ)) / 2) :=
    mul_nonneg hC1 (Real.rpow_nonneg (by norm_num) _)
  have hEnn : (0 : ℝ) ≤
      (∫ omega : ShellSeq d, energyL2 omega R ∂P.toMeasure) ^ ((3 : ℝ) / 4) :=
    Real.rpow_nonneg (MeasureTheory.integral_nonneg hEnergyNonneg) _
  have hprod : (∫ omega : ShellSeq d, energyL2 omega R ∂P.toMeasure) ^ ((3 : ℝ) / 4) *
        (∫ omega : ShellSeq d, blockWeight omega R ^ (4 : ℝ) ∂P.toMeasure) ^
          ((1 : ℝ) / 4) ≤
      (∫ omega : ShellSeq d, energyL2 omega R ∂P.toMeasure) ^ ((3 : ℝ) / 4) *
        (4 * (IndependentSums.gammaMomentConst 1 *
          (Cb * (((S.LPrime : ℕ) : ℝ) * nu⁻¹) ^ ((3 : ℝ) / 4)))) :=
    mul_le_mul_of_nonneg_left hmoment hEnn
  have hfinal : C1 * (3 : ℝ) ^ ((3 * (S.n : ℝ)) / 2) *
      ((∫ omega : ShellSeq d, energyL2 omega R ∂P.toMeasure) ^ ((3 : ℝ) / 4) *
        (4 * (IndependentSums.gammaMomentConst 1 *
          (Cb * (((S.LPrime : ℕ) : ℝ) * nu⁻¹) ^ ((3 : ℝ) / 4))))) =
      C1 * (4 * IndependentSums.gammaMomentConst 1 * Cb) *
        (3 : ℝ) ^ ((3 * (S.n : ℝ)) / 2) *
        (((S.LPrime : ℕ) : ℝ) * nu⁻¹) ^ ((3 : ℝ) / 4) *
        (∫ omega : ShellSeq d, energyL2 omega R ∂P.toMeasure) ^ ((3 : ℝ) / 4) := by
    ring
  calc ∫ omega : ShellSeq d, fluxNegNorm omega R ^ ((3 : ℝ) / 2) ∂P.toMeasure
      ≤ C1 * (3 : ℝ) ^ ((3 * (S.n : ℝ)) / 2) *
        ∫ omega : ShellSeq d,
          energyL2 omega R ^ ((3 : ℝ) / 4) * blockWeight omega R ∂P.toMeasure := hstep1
    _ ≤ C1 * (3 : ℝ) ^ ((3 * (S.n : ℝ)) / 2) *
        ((∫ omega : ShellSeq d, energyL2 omega R ∂P.toMeasure) ^ ((3 : ℝ) / 4) *
          (∫ omega : ShellSeq d, blockWeight omega R ^ (4 : ℝ) ∂P.toMeasure) ^
            ((1 : ℝ) / 4)) := mul_le_mul_of_nonneg_left hholder hcoeff
    _ ≤ C1 * (3 : ℝ) ^ ((3 * (S.n : ℝ)) / 2) *
        ((∫ omega : ShellSeq d, energyL2 omega R ∂P.toMeasure) ^ ((3 : ℝ) / 4) *
          (4 * (IndependentSums.gammaMomentConst 1 *
            (Cb * (((S.LPrime : ℕ) : ℝ) * nu⁻¹) ^ ((3 : ℝ) / 4))))) :=
        mul_le_mul_of_nonneg_left hprod hcoeff
    _ = C1 * (4 * IndependentSums.gammaMomentConst 1 * Cb) *
        (3 : ℝ) ^ ((3 * (S.n : ℝ)) / 2) *
        (((S.LPrime : ℕ) : ℝ) * nu⁻¹) ^ ((3 : ℝ) / 4) *
        (∫ omega : ShellSeq d, energyL2 omega R ∂P.toMeasure) ^ ((3 : ℝ) / 4) := hfinal

end

end SuperdiffusionCLT.Section3.Terms
