/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.MasterIdentityAssembly
public import SuperdiffusionCLT.Section3.Terms.MaximizerGradientL2
public import SuperdiffusionCLT.Section3.Terms.SkewWeakDivergenceB
public import SuperdiffusionCLT.Section3.ResponseFields.RegboundsWindowB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1AnchorsConstFirst
public import SuperdiffusionCLT.Section3.Setup.ResponseMeasurabilityD
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1InputsF
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2Displays
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1Steps
public import SuperdiffusionCLT.Section2.Estimates.Stream.CoefficientLinftyMoments
public import SuperdiffusionCLT.Section2.Estimates.Stream.ShellHminusEndpointOrderOneC
public import SuperdiffusionCLT.Section2.Norms.NegativeNormPairing
public import SuperdiffusionCLT.Section3.ResponseFields.LpEstimates
public import Homogenization.CoarseGraining.ResponseIdentities.Foundations.Algebra

/-!
# The master-identity residue of the root's term-level data

The final assembly of Section 3 carries, as the last eight conjuncts of its
term-level residue `hData` (named `hEllsep`, `hIntSub`, `hIntCoord`, `hEnergy`,
`hI1`-`hI4`), the pointwise display `e.ellsep.testing` and the seven
integrability side conditions under which the master identity is read through
the expectation and the two carrier bridges.  None of the six term bounds
subsumes them, so the root composition keeps them as hypotheses.  This module
discharges what the available theory supplies, at the data carried around them.

* `hIntCoord` and `hIntSub` are the two silent carrier-rewriting side
  conditions; both close from the `L²` membership of the glued field alone.
* `hEllsep` closes at the maximizer carrier `uMgrad omega =
  cubeMaximizerGradient hnu omega S.LPrime Fdir (originCube d (S.m : ℤ))`
  through `Terms.ellsep_testing_of_h1_field`, whose three skew-flux carriers
  are available and whose solenoidality input is
  `Terms.isSolenoidalOn_coefficientCutoff_cubeMaximizerGradient`; the five
  integrability side conditions it asks for close from the same `L²` data.
* `hEnergy` closes from the `W^{8,2}` response estimate through the
  second-moment display `Terms.gradW_l2_second_moment_explicit`.
* `hI4`, the `P`-integrability of the scalar pairing of the test vector `p`
  with the cube mean of the stream-increment flux, closes from the two private
  carriers proved here: the sample-measurability of the cube mean of the flux
  (the canonical-response carrier of `ResponseMeasurabilityD`, moved to every
  selection `w`), and the finiteness of the annealed second moment of the flux
  (the `L^∞(cu_m)` envelope of the increment times the `L̲²(cu_m)` norm of
  `∇w`, bounded by the sum of the two fourth moments, both finite by the
  `Γ₂` tails).  On each cube the pairing is dominated by the product of
  the `L̲²(cu_m)` norm of the flux and the length of `p` (Cauchy–Schwarz on the
  cube in the `MemLp` form of `ShellHminusEndpointOrderOneC`), and the extended
  integral of a product of nonnegative observables is bounded by the sum of the
  squares of the factors (`a · b ≤ a² + b²` on `ℝ≥0∞`).

The three annealed binders `hI1`-`hI3` are not discharged here: each is the
`P`-integrability of the cube average of a pairing whose second slot is built
from the glued or maximizer field, and the measurability in the sample of such
a pairing reduces to the measurability of the `L²(cu_m)` class of
`gluedGradientField` (or of the cube-maximizer gradient family) at mixed
scales — the pairing field of the statement has the cutoff at `ℓ` against
the glued field at `L'` — which no available carrier produces.
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

/-! ## The scale orderings and the sub-cube restriction -/

/-- `ℓ ≤ ℓ'` from the recorded identities of `e.scale.selection`. -/
private theorem scaleSelection_ell_le_ellPrime (S : ScaleSelection) : S.ell ≤ S.ellPrime := by
  have h := S.ell_add_a
  omega

/-- `ℓ ≤ L'` from the recorded identities of `e.scale.selection`. -/
private theorem scaleSelection_ell_le_LPrime (S : ScaleSelection) : S.ell ≤ S.LPrime := by
  have h1 := S.ell_add_a
  have h2 := S.ellPrime_add_h
  have h3 := S.LPrime_eq
  omega

/-- Integrability on the scale-`l` open cube descends to integrability on the
closed form of any of its scale-`n` sub-cubes: the open sub-cube is contained
in the open parent cube, and the two realizations of a sub-cube differ by a
null set. -/
private theorem integrableOn_cubeSet_of_openCubeSet {d : ℕ} {n l : ℕ} {f : Vec d → ℝ}
    (hbig : MeasureTheory.IntegrableOn f (openCubeSet (originCube d (l : ℤ))) volume)
    {R : TriadicCube d} (hR : R ∈ largeCubeSubcubes d n l) :
    MeasureTheory.IntegrableOn f (cubeSet R) volume := by
  have hR' : R ∈ descendantsAtDepth (originCube d (l : ℤ)) (l - n) := hR
  have hsub : openCubeSet R ⊆ openCubeSet (originCube d (l : ℤ)) :=
    openCubeSet_subset_of_mem_descendantsAtDepth hR'
  exact (hbig.mono_set hsub).congr_set_ae (cubeSet_ae_eq_openCubeSet R)

/-! ## The coordinate side condition -/

/-- **`hIntCoord`, the fourth-term carrier rewriting of the master identity.**
Per shell and per coordinate, the integrability on `cu_m` of
`(k_{ℓ'} − k_ℓ)∇w`, the side condition of
`volumeAverage_vecDot_const_left`.  Only the ordering `ℓ ≤ ℓ'` enters. -/
theorem master_residue_intCoord {d : ℕ} (S : ScaleSelection)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ)))) :
    ∀ (omega : ShellSeq d) (i : Fin d), IntegrableOn
      (fun y => matVecMul (streamCutoff omega S.ellPrime y - streamCutoff omega S.ell
        y)
        ((w omega).toH1Function.grad y) i)
      (openCubeSet (originCube d (S.m : ℤ))) volume :=
  fun omega i =>
    integrableOn_coord_streamCutoff_grad omega (scaleSelection_ell_le_ellPrime S)
      (originCube d (S.m : ℤ)) (w omega) i

/-! ## The sub-cube side condition -/

/-- **`hIntSub`, the second-term carrier rewriting of the master identity.**
Per shell and per sub-cube of the lattice `largeCubeSubcubes d S.n S.m`, the
integrability on `cubeSet R` of the pairing of `∇w` with
`(k_{L'} − k_ℓ)(∇u_n − p)`, the side condition of
`volumeAverage_originCube_eq_subcube_avsum`.  On `cu_m` the coefficient
increment is the stream increment, and the pairing is integrable there because
`∇w` is `L²` and `(k_{L'} − k_ℓ)(∇u_n − p)` is `L²` on the cube: the stream
increment is continuous and `∇u_n − p` is `L²` from the glued-field datum. -/
theorem master_residue_intSub {d : ℕ} (nu : ℝ) (S : ScaleSelection) (p : Vec d)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (uNGlued : ShellSeq d → Vec d → Vec d)
    (hUL2 : ∀ omega : ShellSeq d,
      MemVectorL2 (openCubeSet (originCube d (S.m : ℤ))) (uNGlued omega)) :
    ∀ (omega : ShellSeq d), ∀ R ∈ largeCubeSubcubes d S.n S.m,
      IntegrableOn (fun y => vecDot ((w omega).toH1Function.grad y)
        (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
          (coefficientCutoff nu omega S.ell).toCoeffField y)
          (uNGlued omega y - p))) (cubeSet R) volume := by
  have hle2 : S.ell ≤ S.LPrime := scaleSelection_ell_le_LPrime S
  intro omega R hR
  have hpt : (fun y : Vec d => vecDot ((w omega).toH1Function.grad y)
        (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
          (coefficientCutoff nu omega S.ell).toCoeffField y) (uNGlued omega y - p)))
      = fun y : Vec d => vecDot ((w omega).toH1Function.grad y)
        (matVecMul (streamCutoff omega S.LPrime y - streamCutoff omega S.ell y)
          (uNGlued omega y - p)) := by
    funext y
    rw [coefficientCutoff_toCoeffField_sub_eq_streamCutoff_sub]
  rw [hpt]
  exact integrableOn_cubeSet_of_openCubeSet
    (integrableOn_vecDot_of_memVectorL2 (w omega).toH1Function.grad_memVectorL2
      (memVectorL2_matVecMul_of_continuous (originCube d (S.m : ℤ))
        (continuous_streamCutoff_sub_entries omega hle2)
        ((hUL2 omega).sub (memVectorL2_const p)))) hR

/-! ## The pointwise display `e.ellsep.testing` -/

/-- **`hEllsep`, the pointwise display `e.ellsep.testing`** at the maximizer
carrier `uMgrad omega = cubeMaximizerGradient hnu omega S.LPrime Fdir
(originCube d (S.m : ℤ))`.

The three skew-flux carriers of the testing display are available
(`Terms.memL2On_streamSubGrad`, `Terms.memL2On_driftSubGrad`,
`Terms.hasWeakDivergenceOn_streamGrad` inside
`Terms.ellsep_testing_of_h1_field`), and the weak form `hEll` of `e.ellsep` is
`Terms.isSolenoidalOn_coefficientCutoff_cubeMaximizerGradient`, which holds at
this carrier with no input beyond `0 < nu`; the route goes through the `H¹`
field `u = (cubeMaximizer …).toSolution.toH1` whose gradient is the carrier.
The five integrability side conditions the display asks for close from
the `L²` memberships of `∇w` (the response's own) and of the glued field. -/
theorem master_residue_ellsep {d : ℕ} (nu : ℝ) (hnu : 0 < nu)
    (S : ScaleSelection) (p q : Vec d) (Fdir : Vec d)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (uMgrad uNGlued : ShellSeq d → Vec d → Vec d)
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m p (w omega))
    (hUL2 : ∀ omega : ShellSeq d,
      MemVectorL2 (openCubeSet (originCube d (S.m : ℤ))) (uNGlued omega))
    (hUgrad : ∀ omega : ShellSeq d, uMgrad omega =
      cubeMaximizerGradient hnu omega S.LPrime Fdir (originCube d (S.m : ℤ))) :
    ∀ omega : ShellSeq d, volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
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
          (fun x => matVecMul (streamCutoff omega S.ellPrime x - streamCutoff omega
            S.ell x)
            ((w omega).toH1Function.grad x))) := by
  have hle2 : S.ell ≤ S.LPrime := scaleSelection_ell_le_LPrime S
  intro omega
  rw [hUgrad omega]
  have hInt1 : MeasureTheory.IntegrableOn (fun x => vecDot ((w omega).toH1Function.grad x)
      (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
        (uNGlued omega x) - q))
      (openCubeSet (originCube d (S.m : ℤ))) volume :=
    integrableOn_vecDot_of_memVectorL2 (w omega).toH1Function.grad_memVectorL2
      ((memVectorL2_matVecMul_coefficientCutoff hnu omega S.ell
          (originCube d (S.m : ℤ)) (hUL2 omega)).sub (memVectorL2_const q))
  have hInt2 : MeasureTheory.IntegrableOn (fun x => vecDot ((w omega).toH1Function.grad x)
      (matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x)
        (uNGlued omega x - p)))
      (openCubeSet (originCube d (S.m : ℤ))) volume :=
    integrableOn_vecDot_of_memVectorL2 (w omega).toH1Function.grad_memVectorL2
      (memVectorL2_matVecMul_of_continuous (originCube d (S.m : ℤ))
        (continuous_streamCutoff_sub_entries omega hle2)
        ((hUL2 omega).sub (memVectorL2_const p)))
  have hInt3 : MeasureTheory.IntegrableOn (fun x => vecDot ((w omega).toH1Function.grad x)
      (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x)
        (cubeMaximizerGradient hnu omega S.LPrime Fdir (originCube d (S.m : ℤ)) x -
          uNGlued omega x)))
      (openCubeSet (originCube d (S.m : ℤ))) volume :=
    integrableOn_vecDot_of_memVectorL2 (w omega).toH1Function.grad_memVectorL2
      (memVectorL2_matVecMul_coefficientCutoff hnu omega S.LPrime
        (originCube d (S.m : ℤ))
        ((memVectorL2_cubeMaximizerGradient hnu omega S.LPrime Fdir
          (originCube d (S.m : ℤ))).sub (hUL2 omega)))
  exact ellsep_testing_of_h1_field nu omega S p q (w omega)
    ((cubeMaximizer hnu omega S.LPrime Fdir (originCube d (S.m : ℤ))).toSolution.toH1)
    (uNGlued omega) (hw omega)
    (isSolenoidalOn_coefficientCutoff_cubeMaximizerGradient hnu omega S.LPrime Fdir
      (originCube d (S.m : ℤ)))
    (integrableOn_vecDot_coefficientCutoff_cubeMaximizerGradient hnu omega S.LPrime
      S.ell Fdir (originCube d (S.m : ℤ)) (w omega))
    (integrableOn_vecDot_streamCutoff_cubeMaximizerGradient hnu omega hle2 S.LPrime
      Fdir p (originCube d (S.m : ℤ)) (w omega))
    hInt1 hInt2 hInt3

/-! ## The energy side condition -/

/-- **`hEnergy`, the `P`-integrability of the cube average of `|∇w|²`.**
Measurability in the sample is the statement's own `L̲²` norm clause;
finiteness is the second-moment display
`Terms.gradW_l2_second_moment_explicit`, fed by the `W^{8,2}` response
estimate `l.w.basic.regbounds` (its constant is quantified before the data) —
the same two inputs the root theorem uses for its finiteness clause. -/
theorem master_residue_energy {d : ℕ} [NeZero d] (hd : 2 ≤ d) (nu : ℝ) (hnu : 0 < nu)
    (hnu1 : nu ≤ 1) (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P) (hJ1V2 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (hSorder : ScalesOrdering S)
    (ee : Vec d) (he : vecNormSq ee = 1) (p : Vec d)
    (hp : p = testVector nu S.LPrime P S.n ee)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m p (w omega))
    (hmeas : AEMeasurable (fun omega : ShellSeq d =>
      vecCubeLpENorm (originCube d (S.m : ℤ)) 2 (w omega).toH1Function.grad)
      P.toMeasure) :
    Integrable (fun omega : ShellSeq d =>
      volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => vecNormSq ((w omega).toH1Function.grad x))) P.toMeasure := by
  obtain ⟨Creg, hCreg, hregw⟩ := l_w_basic_regbounds_window d hd
  have hregA := hregw nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder ee he p hp
    w hw
  have hsecond := gradW_l2_second_moment_explicit hnu hPrefix hJ2 hJ3 hJ4 S hSorder
    ee he p hp w Creg hCreg hregA.1
  have hpt : ∀ omega : ShellSeq d, ENNReal.ofReal
      (volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => vecNormSq ((w omega).toH1Function.grad x))) =
      vecCubeLpENorm (originCube d (S.m : ℤ)) 2 (w omega).toH1Function.grad ^
        (2 : ℕ) := by
    intro omega
    rw [vecCubeLpENorm_two_sq_eq_ofReal (w omega).toH1Function.grad_memVectorL2,
      integral_normalizedCubeMeasure_eq_volumeAverage]
  have hnn : ∀ omega : ShellSeq d, 0 ≤ volumeAverage
      (openCubeSet (originCube d (S.m : ℤ)))
      (fun x => vecNormSq ((w omega).toH1Function.grad x)) := fun omega =>
    mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) (integral_nonneg fun x =>
      vecNormSq_nonneg _)
  have hfun : (fun omega : ShellSeq d =>
        volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => vecNormSq ((w omega).toH1Function.grad x))) =
      fun omega : ShellSeq d =>
        (vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (w omega).toH1Function.grad ^ (2 : ℕ)).toReal := by
    funext omega
    calc volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => vecNormSq ((w omega).toH1Function.grad x)) =
        (ENNReal.ofReal (volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => vecNormSq ((w omega).toH1Function.grad x)))).toReal :=
          (ENNReal.toReal_ofReal (hnn omega)).symm
      _ = (vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (w omega).toH1Function.grad ^ (2 : ℕ)).toReal := by
          rw [hpt omega]
  have hmeasF : AEMeasurable (fun omega : ShellSeq d =>
      volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => vecNormSq ((w omega).toH1Function.grad x))) P.toMeasure := by
    rw [hfun]
    exact hmeas.pow_const 2 |>.ennreal_toReal
  have hbound : ∀ omega : ShellSeq d, ‖volumeAverage
      (openCubeSet (originCube d (S.m : ℤ)))
      (fun x => vecNormSq ((w omega).toH1Function.grad x))‖ₑ ≤
      vecCubeLpENorm (originCube d (S.m : ℤ)) 2 (w omega).toH1Function.grad ^
        (2 : ℕ) := by
    intro omega
    have habs : ‖volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => vecNormSq ((w omega).toH1Function.grad x))‖ₑ =
        ENNReal.ofReal (volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => vecNormSq ((w omega).toH1Function.grad x))) := by
      rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hnn omega)]
    rw [habs, hpt omega]
  refine ⟨hmeasF.aestronglyMeasurable, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_def]
  refine lt_of_le_of_lt (lintegral_mono hbound)
    (lt_of_le_of_lt hsecond ENNReal.ofReal_lt_top)

/-! ## Arithmetic helpers of the annealed residue -/

/-- `ℓ' ≤ L'` from the recorded identities of `e.scale.selection`. -/
private theorem scaleSelection_ellPrime_le_LPrime (S : ScaleSelection) :
    S.ellPrime ≤ S.LPrime := by
  have h1 := S.ellPrime_add_h
  have h2 := S.LPrime_eq
  omega

private theorem sq_le_sq_add_sq_ennreal (a b : ℝ≥0∞) :
    a * b ≤ a ^ (2 : ℕ) + b ^ (2 : ℕ) := by
  rcases le_total a b with h | h
  · calc a * b ≤ b * b := mul_le_mul' h le_rfl
      _ = b ^ (2 : ℕ) := (pow_two b).symm
      _ ≤ a ^ (2 : ℕ) + b ^ (2 : ℕ) := le_add_self
  · calc a * b ≤ a * a := mul_le_mul' le_rfl h
      _ = a ^ (2 : ℕ) := (pow_two a).symm
      _ ≤ a ^ (2 : ℕ) + b ^ (2 : ℕ) := le_self_add

private theorem sq_mul_sq_le_sq_add_sq_ennreal (a b : ℝ≥0∞) :
    a ^ (2 : ℕ) * b ^ (2 : ℕ) ≤ a ^ (4 : ℕ) + b ^ (4 : ℕ) := by
  have h := sq_le_sq_add_sq_ennreal (a ^ (2 : ℕ)) (b ^ (2 : ℕ))
  rw [← pow_mul a 2 2, ← pow_mul b 2 2] at h
  exact h

/-! ## Measurability of the stream-increment cube mean -/

/-- The cube mean over the large cube `cu_m` of the stream-increment flux
`(k_{ℓ'} − k_ℓ) ∇w` is measurable in the sample: the underlying composition
(`measurable_volumeAverageVec_matVecMul_grad_dirichletResponse_comp`) is stated
for the canonical Dirichlet response, and choice independence
(`measurable_volumeAverageVec_matVecMul_grad_of_canonical`) moves the observable
to every selection `w` of the response. -/
private theorem measurable_volumeAverageVec_streamCutoff_sub_grad {d : ℕ} [NeZero d]
    (S : ScaleSelection)
    {p : Vec d} {w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ)))}
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m p (w omega)) :
    Measurable (fun omega : ShellSeq d =>
      volumeAverageVec (openCubeSet (originCube d (S.m : ℤ)))
        (fun y => matVecMul (streamCutoff omega S.ellPrime y - streamCutoff omega
          S.ell y)
          ((w omega).toH1Function.grad y))) := by
  have hle2 : S.ell ≤ S.ellPrime := scaleSelection_ell_le_ellPrime S
  have hle3 : S.ellPrime ≤ S.LPrime := scaleSelection_ellPrime_le_LPrime S
  have hVU : openCubeSet (originCube d (S.m : ℤ)) ⊆
      openCubeSet (originCube d (S.m : ℤ)) := le_rfl
  have hint := measurable_volumeAverageVec_matVecMul_grad_dirichletResponse_comp
    (F := fun omega : ShellSeq d => omega)
    (fun omega y => streamCutoff omega S.ellPrime y - streamCutoff omega S.ell y)
    (fun omega i j => continuous_streamCutoff_sub_entries omega hle2 i j)
    (fun y i j => ((measurable_apply_entry y i j).comp
        (measurable_streamCutoff S.ellPrime)).sub
      ((measurable_apply_entry y i j).comp (measurable_streamCutoff S.ell)))
    S.LPrime S.ellPrime S.m p hVU
    (isOpen_openCubeSet (originCube d (S.m : ℤ))).measurableSet
    (fun x => Measurable.mono
      (measurable_dirichletRhsField_apply_highShellSigma hle2 hle3 p x)
      (highShellSigma_le d S.ell) le_rfl)
  exact measurable_volumeAverageVec_matVecMul_grad_of_canonical hVU
    (fun omega y => streamCutoff omega S.ellPrime y - streamCutoff omega S.ell y) hw hint

/-! ## The annealed second moment of the stream-increment flux -/

/-- The annealed second moment of the stream-increment flux
`(k_{ℓ'} − k_ℓ) ∇w` over the large cube `cu_m` is finite: the cube norm is
dominated by the `L^∞(cu_m)` envelope of the increment times the `L̲²(cu_m)`
norm of `∇w`, and the squared product is bounded by the sum of the two fourth
moments (`a · b ≤ a² + b²` on `ℝ≥0∞`), both finite — the gradient's through the
`W^{8,2}` response estimate `l.w.basic.regbounds` at a `Γ₂` envelope,
the envelope's through the `Γ₂` tail of `e.kmn.Linfty`. -/
private theorem streamIncrement_second_moment {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (nu : ℝ) (hnu : 0 < nu) (hnu1 : nu ≤ 1) (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P) (hJ1V2 : ShellLawJ1Restriction d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (hSorder : ScalesOrdering S)
    (ee : Vec d) (he : vecNormSq ee = 1) (p : Vec d)
    (hp : p = testVector nu S.LPrime P S.n ee)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m p (w omega)) :
    (∫⁻ omega : ShellSeq d,
        vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (fun x => matVecMul (streamCutoff omega S.ellPrime x -
            streamCutoff omega S.ell x) ((w omega).toH1Function.grad x)) ^ (2 : ℕ)
        ∂P.toMeasure) ≠ ⊤ := by
  have hle2 : S.ell ≤ S.ellPrime := scaleSelection_ell_le_ellPrime S
  -- the pointwise `L^∞` envelope of the increment on the half-open cube
  have henv : ∀ omega : ShellSeq d, ∀ x ∈ cubeSet (originCube d (S.m : ℤ)),
      matrixOperatorNorm (streamCutoff omega S.ellPrime x - streamCutoff omega
        S.ell x) ≤
        largeCubeIncrementSupBound S.ell S.ellPrime S.m omega := by
    intro omega x hx
    have hinc : finiteShellIncrement omega S.ell S.ellPrime x =
        streamCutoff omega S.ellPrime x - streamCutoff omega S.ell x :=
      finiteShellIncrement_apply_eq_streamCutoff_sub omega hle2 x
    rw [← hinc]
    exact matrixOperatorNorm_finiteShellIncrement_le_largeCubeIncrementSupBound
      omega (le_trans hle2 (le_of_lt hSorder.ellPrime_lt_m)) hx
  have hae : ∀ omega : ShellSeq d, ∀ᵐ x ∂normalizedCubeMeasure
      (originCube d (S.m : ℤ)),
      matrixOperatorNorm (streamCutoff omega S.ellPrime x - streamCutoff omega
        S.ell x) ≤
        largeCubeIncrementSupBound S.ell S.ellPrime S.m omega := by
    intro omega
    have hmem : ∀ᵐ x ∂normalizedCubeMeasure (originCube d (S.m : ℤ)),
        x ∈ cubeSet (originCube d (S.m : ℤ)) :=
      MeasureTheory.Measure.ae_smul_measure
        (MeasureTheory.ae_restrict_mem (measurableSet_cubeSet _)) _
    exact hmem.mono fun x hx => henv omega x hx
  have hc : ∀ omega : ShellSeq d, 0 ≤ largeCubeIncrementSupBound S.ell S.ellPrime S.m
      omega := fun omega => largeCubeIncrementSupBound_nonneg _ _ _ omega
  have hnorm : ∀ omega : ShellSeq d,
      vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        (fun x => matVecMul (streamCutoff omega S.ellPrime x - streamCutoff omega
          S.ell x) ((w omega).toH1Function.grad x)) ≤
        ENNReal.ofReal (largeCubeIncrementSupBound S.ell S.ellPrime S.m omega) *
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            ((w omega).toH1Function.grad) :=
    fun omega => by
      have hgm : AEStronglyMeasurable (hilbertifyVecField (w omega).toH1Function.grad)
          (normalizedCubeMeasure (originCube d (S.m : ℤ))) := by
        have h : AEStronglyMeasurable (hilbertifyVecField (w omega).toH1Function.grad)
            (MeasureTheory.volume.restrict (openCubeSet (originCube d (S.m : ℤ)))) :=
          (memHilbertVectorL2_hilbertifyVecField
            (w omega).toH1Function.grad_memVectorL2).aestronglyMeasurable
        rw [normalizedCubeMeasure, cubeMeasure,
          volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
        exact h.smul_measure _
      exact vecCubeLpENorm_matVecMul_le 2
        (fun x => streamCutoff omega S.ellPrime x - streamCutoff omega S.ell x) _ (hc omega)
        (aestronglyMeasurable_hilbertifyVecField_matVecMul
          ((continuous_streamCutoff_apply omega S.ellPrime).sub
            (continuous_streamCutoff_apply omega S.ell)) hgm)
        (hae omega)
  -- the `W^{8,2}` response estimate and its `Γ₂` envelope
  obtain ⟨Creg, hCreg, hregw⟩ := l_w_basic_regbounds_window d hd
  have hregA := hregw nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder ee he p hp
    w hw
  obtain ⟨Z, hZmeas, hZbigO, hZbound⟩ := hregA.1
  have hC0 : (0 : ℝ) < Creg := lt_of_lt_of_le (by norm_num) hCreg
  have hh1 : 1 ≤ S.h := by
    have h1 := hSorder.ellPrime_lt_m
    have h2 := S.ellPrime_add_h
    omega
  have hhR : (0 : ℝ) < (S.h : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hh1
  have hpn : (0 : ℝ) < vecNormSq p := by
    rw [hp, vecNormSq_testVector hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n he]
    exact sigmaBarStarInvSeq_pos hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n
  have hhalf : (0 : ℝ) < (S.h : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hhR _
  have hA : (0 : ℝ) < Creg * (Real.sqrt (vecNormSq p) * (S.h : ℝ) ^ ((1 : ℝ) / 2)) :=
    mul_pos hC0 (mul_pos (Real.sqrt_pos.2 hpn) hhalf)
  have hdown : ∀ omega : ShellSeq d,
      vecCubeLpENorm (originCube d (S.m : ℤ)) 2 ((w omega).toH1Function.grad) ≤
        ENNReal.ofReal (Z omega) := by
    intro omega
    refine le_trans ?_ (hZbound omega)
    exact vecCubeLpENorm_mono_exponent (originCube d (S.m : ℤ)) (by norm_num)
      (aestronglyMeasurable_hilbertifyVecField_of_memVectorL2
        (w omega).toH1Function.grad_memVectorL2)
  have hZ4 : (∫⁻ omega : ShellSeq d,
      ENNReal.ofReal (|Z omega| ^ ((4 : ℕ) : ℝ)) ∂P.toMeasure) < ⊤ := by
    have hint := integrable_abs_rpow_of_isBigO_gammaSigma_two hA
      hZmeas.aemeasurable hZbigO 4
    have hhint := hint.hasFiniteIntegral
    rw [MeasureTheory.hasFiniteIntegral_def] at hhint
    refine lt_of_le_of_lt (lintegral_mono fun omega => ?_) hhint
    exact le_of_eq (by rw [← ofReal_norm, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg (Z omega)) _)])
  have hg4 : (∫⁻ omega : ShellSeq d,
      vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        ((w omega).toH1Function.grad) ^ (4 : ℕ) ∂P.toMeasure) < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono fun omega => ?_) hZ4
    have hup : vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        ((w omega).toH1Function.grad) ≤ ENNReal.ofReal (|Z omega|) :=
      le_trans (hdown omega) (ENNReal.ofReal_le_ofReal (le_abs_self (Z omega)))
    calc vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          ((w omega).toH1Function.grad) ^ (4 : ℕ) ≤
        (ENNReal.ofReal (|Z omega|)) ^ (4 : ℕ) :=
          pow_le_pow_left' hup 4
      _ = ENNReal.ofReal (|Z omega| ^ (4 : ℕ)) :=
          (ENNReal.ofReal_pow (abs_nonneg _) 4).symm
      _ = ENNReal.ofReal (|Z omega| ^ ((4 : ℕ) : ℝ)) :=
          by rw [Real.rpow_natCast]
  -- the `Γ₂` tail of the increment envelope
  have hLPm : S.ellPrime ≤ S.m := le_of_lt hSorder.ellPrime_lt_m
  have hellm : (0 : ℕ) < S.m - S.ell :=
    Nat.sub_pos_of_lt (lt_of_lt_of_le hSorder.ell_lt_ellPrime hLPm)
  have hellp : (0 : ℕ) < S.ellPrime - S.ell :=
    Nat.sub_pos_of_lt hSorder.ell_lt_ellPrime
  have hamp : 0 < largeCubeLinftyConst d * ((√ (((S.ellPrime - S.ell : ℕ) : ℝ))) *
      √ (((S.m - S.ell : ℕ) : ℝ))) :=
    mul_pos (largeCubeLinftyConst_pos hPrefix)
      (mul_pos (Real.sqrt_pos.2 (by exact_mod_cast hellp))
        (Real.sqrt_pos.2 (by exact_mod_cast hellm)))
  have hmeasC : Measurable (fun omega : ShellSeq d =>
      largeCubeIncrementSupBound S.ell S.ellPrime S.m omega) :=
    measurable_largeCubeIncrementSupBound S.ell S.ellPrime S.m
  have hbigInc := (isBigOWith_iff_isBigO_of_nonneg
    (fun omega => largeCubeIncrementSupBound_nonneg S.ell S.ellPrime S.m omega)).1
    (isBigOWith_gammaSigma_largeCubeIncrementSupBound hPrefix hJ2 hJ3 hJ4
      hSorder.ell_lt_ellPrime hLPm)
  have hC4 : (∫⁻ omega : ShellSeq d,
      (ENNReal.ofReal (largeCubeIncrementSupBound S.ell S.ellPrime S.m omega)) ^
        (4 : ℕ) ∂P.toMeasure) < ⊤ := by
    have hint := integrable_abs_rpow_of_isBigO_gammaSigma_two hamp
      hmeasC.aemeasurable hbigInc 4
    have hhint := hint.hasFiniteIntegral
    rw [MeasureTheory.hasFiniteIntegral_def] at hhint
    refine lt_of_le_of_lt (lintegral_mono fun omega => ?_) hhint
    have hab : |largeCubeIncrementSupBound S.ell S.ellPrime S.m omega| =
        largeCubeIncrementSupBound S.ell S.ellPrime S.m omega :=
      abs_of_nonneg (hc omega)
    refine le_of_eq ?_
    rw [← ENNReal.ofReal_pow (hc omega) 4, ← Real.rpow_natCast, hab,
      ← ofReal_norm, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (hc omega) _)]
  -- the squared product is bounded by the sum of the fourth moments
  refine ne_of_lt ?_
  have hpw : ∀ omega : ShellSeq d,
      (vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (fun x => matVecMul (streamCutoff omega S.ellPrime x -
            streamCutoff omega S.ell x) ((w omega).toH1Function.grad x))) ^ (2 : ℕ) ≤
      (ENNReal.ofReal (largeCubeIncrementSupBound S.ell S.ellPrime S.m omega)) ^
        (4 : ℕ) +
        (vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          ((w omega).toH1Function.grad)) ^ (4 : ℕ) := by
    intro omega
    calc (vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (fun x => matVecMul (streamCutoff omega S.ellPrime x - streamCutoff omega
            S.ell x) ((w omega).toH1Function.grad x))) ^ (2 : ℕ) ≤
        (ENNReal.ofReal (largeCubeIncrementSupBound S.ell S.ellPrime S.m omega) *
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            ((w omega).toH1Function.grad)) ^ (2 : ℕ) :=
          pow_le_pow_left' (hnorm omega) 2
      _ = (ENNReal.ofReal (largeCubeIncrementSupBound S.ell S.ellPrime S.m omega)) ^
            (2 : ℕ) *
            (vecCubeLpENorm (originCube d (S.m : ℤ)) 2
              ((w omega).toH1Function.grad)) ^ (2 : ℕ) := by
          rw [mul_pow]
      _ ≤ (ENNReal.ofReal (largeCubeIncrementSupBound S.ell S.ellPrime S.m omega)) ^
            (4 : ℕ) +
            (vecCubeLpENorm (originCube d (S.m : ℤ)) 2
              ((w omega).toH1Function.grad)) ^ (4 : ℕ) :=
            sq_mul_sq_le_sq_add_sq_ennreal _ _
  refine lt_of_le_of_lt (lintegral_mono hpw) ?_
  rw [lintegral_add_left' (hmeasC.ennreal_ofReal.aemeasurable.pow_const 4)]
  exact ENNReal.add_lt_top.2 ⟨hC4, hg4⟩

/-! ## The fourth annealed binder -/

/-- **`hI4`, the fourth annealed integrability binder of the master identity:**
the scalar pairing of the fixed test vector `p` with the cube mean of the
stream-increment flux `(k_{ℓ'} − k_ℓ) ∇w` is `P`-integrable.

The cube mean is measurable in the sample (the canonical-response carrier of
`ResponseMeasurabilityD`, moved to every selection `w` of the response).
Finiteness is read from the annealed second moment of the flux: on each cube
the pairing against the constant `p` is dominated by the product of the
`L̲²(cu_m)` norm of the flux and the length of `p` (Cauchy–Schwarz on the cube,
`abs_volumeAverage_vecDot_le_sqrt_mul_sqrt_memLp`), and the extended integral
of a product of nonnegative observables is bounded by the sum of the squares of
the factors (`a · b ≤ a² + b²` on `ℝ≥0∞`) — the flux's fourth moment is finite
by `streamIncrement_second_moment` above, the test vector's is a fixed real. -/
theorem master_residue_hI4 {d : ℕ} [NeZero d] (hd : 2 ≤ d) (nu : ℝ) (hnu : 0 < nu)
    (hnu1 : nu ≤ 1) (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P) (hJ1V2 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (hSorder : ScalesOrdering S)
    (ee : Vec d) (he : vecNormSq ee = 1) (p : Vec d)
    (hp : p = testVector nu S.LPrime P S.n ee)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m p (w omega)) :
    Integrable (fun omega : ShellSeq d =>
      vecDot p (volumeAverageVec (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => matVecMul (streamCutoff omega S.ellPrime x - streamCutoff omega
          S.ell x)
          ((w omega).toH1Function.grad x)))) P.toMeasure := by
  have hle2 : S.ell ≤ S.ellPrime := scaleSelection_ell_le_ellPrime S
  -- the annealed second moment of the flux
  have hsm := streamIncrement_second_moment hd nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3
    hJ4 S hSorder ee he p hp w hw
  -- the `L²` membership of the flux field, and its `L̲²` reading on the cube
  have hmem : ∀ omega : ShellSeq d,
      MemVectorL2 (openCubeSet (originCube d (S.m : ℤ))) (fun x : Vec d =>
        matVecMul (streamCutoff omega S.ellPrime x - streamCutoff omega S.ell x)
          ((w omega).toH1Function.grad x)) := fun omega =>
    memVectorL2_matVecMul_of_continuous (originCube d (S.m : ℤ))
      (continuous_streamCutoff_sub_entries omega hle2)
      (w omega).toH1Function.grad_memVectorL2
  have hlp : ∀ omega : ShellSeq d,
      MemLp (hilbertifyVecField (fun x : Vec d =>
          matVecMul (streamCutoff omega S.ellPrime x - streamCutoff omega S.ell x)
            ((w omega).toH1Function.grad x))) 2
        (normalizedCubeMeasure (originCube d (S.m : ℤ))) := fun omega =>
    memLp_hilbertifyVecField_of_memVectorL2 (hmem omega)
  have hlpC : MemLp (hilbertifyVecField (fun _ : Vec d => p)) 2
      (normalizedCubeMeasure (originCube d (S.m : ℤ))) :=
    memLp_hilbertifyVecField_of_memVectorL2 (memVectorL2_const p)
  -- the display rewriting the integrand to a cube average
  have havg : ∀ omega : ShellSeq d,
      vecDot p (volumeAverageVec (openCubeSet (originCube d (S.m : ℤ))) (fun x : Vec d =>
          matVecMul (streamCutoff omega S.ellPrime x - streamCutoff omega S.ell x)
            ((w omega).toH1Function.grad x))) =
        volumeAverage (cubeSet (originCube d (S.m : ℤ))) (fun x : Vec d =>
          vecDot (matVecMul (streamCutoff omega S.ellPrime x - streamCutoff omega
            S.ell x)
            ((w omega).toH1Function.grad x)) p) := by
    intro omega
    rw [← volumeAverageVec_cubeSet_eq_openCubeSet (originCube d (S.m : ℤ))
        (fun x : Vec d =>
        matVecMul (streamCutoff omega S.ellPrime x - streamCutoff omega S.ell x)
          ((w omega).toH1Function.grad x)),
      ResponseFields.vecDot_comm' p (volumeAverageVec (cubeSet (originCube d (S.m : ℤ)))
        (fun x : Vec d =>
        matVecMul (streamCutoff omega S.ellPrime x - streamCutoff omega S.ell x)
          ((w omega).toH1Function.grad x))),
      ← volumeAverage_vecDot_const_right_memLp (originCube d (S.m : ℤ)) (hlp omega) p]
  -- the volume of the open cube, for the constant square average
  have hvol : (0 : ℝ) < (MeasureTheory.volume
      (openCubeSet (originCube d (S.m : ℤ)))).toReal :=
    ENNReal.toReal_pos (ResponseFields.volume_openCubeSet_ne_zero _)
      (ne_top_of_lt (volume_openCubeSet_lt_top _))
  -- the square average of the constant test vector is its squared length
  have hconstAvg : Real.sqrt (vecSqAvg (originCube d (S.m : ℤ)) (fun _ : Vec d => p)) =
      vecNorm p := by
    have h1 : vecSqAvg (originCube d (S.m : ℤ)) (fun _ : Vec d => p)
        = ‖HilbertVec.ofVec p‖ ^ (2 : ℕ) := by
      have h2 : vecSqAvg (originCube d (S.m : ℤ)) (fun _ : Vec d => p) =
          volumeAverage (cubeSet (originCube d (S.m : ℤ))) (fun x : Vec d =>
            ‖HilbertVec.ofVec ((fun _ : Vec d => p) x)‖ ^ (2 : ℕ)) := rfl
      rw [h2, volumeAverage_cubeSet_eq_openCubeSet,
        show (fun x : Vec d => ‖HilbertVec.ofVec ((fun _ : Vec d => p) x)‖ ^ (2 : ℕ))
            = fun _ : Vec d => ‖HilbertVec.ofVec p‖ ^ (2 : ℕ) from rfl,
        volumeAverage_const (ne_of_gt hvol)]
    rw [h1, Real.sqrt_sq (norm_nonneg (HilbertVec.ofVec p)), vecNorm_eq_norm_ofVec p]
  -- Cauchy–Schwarz on the cube against the constant test vector
  have hbound : ∀ omega : ShellSeq d,
      |vecDot p (volumeAverageVec (openCubeSet (originCube d (S.m : ℤ))) (fun x : Vec d =>
          matVecMul (streamCutoff omega S.ellPrime x - streamCutoff omega S.ell x)
            ((w omega).toH1Function.grad x)))| ≤
      (vecCubeLpENorm (originCube d (S.m : ℤ)) 2 (fun x : Vec d =>
          matVecMul (streamCutoff omega S.ellPrime x - streamCutoff omega S.ell x)
            ((w omega).toH1Function.grad x))).toReal * vecNorm p := by
    intro omega
    rw [havg omega]
    have hcs : |volumeAverage (cubeSet (originCube d (S.m : ℤ))) (fun x : Vec d =>
          vecDot (matVecMul (streamCutoff omega S.ellPrime x - streamCutoff omega
            S.ell x)
            ((w omega).toH1Function.grad x)) p)| ≤
        Real.sqrt (vecSqAvg (originCube d (S.m : ℤ)) (fun x : Vec d =>
            matVecMul (streamCutoff omega S.ellPrime x - streamCutoff omega S.ell x)
              ((w omega).toH1Function.grad x))) *
          Real.sqrt (vecSqAvg (originCube d (S.m : ℤ)) (fun _ : Vec d => p)) :=
      abs_volumeAverage_vecDot_le_sqrt_mul_sqrt_memLp (originCube d (S.m : ℤ))
        (hlp omega) hlpC
    rw [← toReal_vecCubeLpENorm_eq_sqrt_memLp (originCube d (S.m : ℤ)) (hlp omega),
      hconstAvg] at hcs
    exact hcs
  refine ⟨?_, ?_⟩
  · have hM : Measurable (fun omega : ShellSeq d =>
      vecDot p (volumeAverageVec (openCubeSet (originCube d (S.m : ℤ))) (fun x : Vec d =>
        matVecMul (streamCutoff omega S.ellPrime x - streamCutoff omega S.ell x)
          ((w omega).toH1Function.grad x)))) :=
      (continuous_vecDot continuous_const continuous_id).measurable.comp
        (measurable_volumeAverageVec_streamCutoff_sub_grad S hw)
    exact hM.aemeasurable.aestronglyMeasurable
  · rw [MeasureTheory.hasFiniteIntegral_def]
    have hpw : ∀ omega : ShellSeq d,
        ‖vecDot p (volumeAverageVec (openCubeSet (originCube d (S.m : ℤ))) (fun x : Vec d
            => matVecMul (streamCutoff omega S.ellPrime x - streamCutoff omega S.ell x)
              ((w omega).toH1Function.grad x)))‖ₑ ≤
        (ENNReal.ofReal (vecNorm p)) ^ (2 : ℕ) +
          (vecCubeLpENorm (originCube d (S.m : ℤ)) 2 (fun x : Vec d =>
              matVecMul (streamCutoff omega S.ellPrime x - streamCutoff omega S.ell x)
                ((w omega).toH1Function.grad x))) ^ (2 : ℕ) := by
      intro omega
      rw [← ofReal_norm, Real.norm_eq_abs]
      have hsplit : ENNReal.ofReal ((vecCubeLpENorm (originCube d (S.m : ℤ)) 2
              (fun x : Vec d => matVecMul (streamCutoff omega S.ellPrime x -
                streamCutoff omega S.ell x)
                ((w omega).toH1Function.grad x))).toReal * vecNorm p) =
          ENNReal.ofReal ((vecCubeLpENorm (originCube d (S.m : ℤ)) 2 (fun x : Vec d
                => matVecMul (streamCutoff omega S.ellPrime x - streamCutoff omega
                  S.ell x)
                  ((w omega).toH1Function.grad x))).toReal) *
            ENNReal.ofReal (vecNorm p) :=
        ENNReal.ofReal_mul ENNReal.toReal_nonneg
      calc ENNReal.ofReal |vecDot p (volumeAverageVec (openCubeSet (originCube d
                (S.m : ℤ)))
              (fun x : Vec d => matVecMul (streamCutoff omega S.ellPrime x -
                streamCutoff omega S.ell x)
                ((w omega).toH1Function.grad x)))| ≤
          ENNReal.ofReal ((vecCubeLpENorm (originCube d (S.m : ℤ)) 2 (fun x : Vec d =>
                matVecMul (streamCutoff omega S.ellPrime x - streamCutoff omega S.ell
                  x)
                  ((w omega).toH1Function.grad x))).toReal * vecNorm p) :=
            ENNReal.ofReal_le_ofReal (hbound omega)
        _ = ENNReal.ofReal (vecNorm p) *
              ENNReal.ofReal ((vecCubeLpENorm (originCube d (S.m : ℤ)) 2 (fun x : Vec d
                => matVecMul (streamCutoff omega S.ellPrime x - streamCutoff omega
                  S.ell x)
                  ((w omega).toH1Function.grad x))).toReal) :=
            by rw [hsplit, mul_comm]
        _ ≤ ENNReal.ofReal (vecNorm p) * vecCubeLpENorm (originCube d (S.m : ℤ)) 2
              (fun x : Vec d => matVecMul (streamCutoff omega S.ellPrime x -
                streamCutoff omega S.ell x)
                ((w omega).toH1Function.grad x)) :=
            mul_le_mul_right ENNReal.ofReal_toReal_le _
        _ ≤ (ENNReal.ofReal (vecNorm p)) ^ (2 : ℕ) +
            (vecCubeLpENorm (originCube d (S.m : ℤ)) 2 (fun x : Vec d =>
              matVecMul (streamCutoff omega S.ellPrime x - streamCutoff omega S.ell x)
                ((w omega).toH1Function.grad x))) ^ (2 : ℕ) :=
            sq_le_sq_add_sq_ennreal _ _
    refine lt_of_le_of_lt (lintegral_mono hpw) ?_
    rw [lintegral_add_left' (measurable_const.pow_const 2).aemeasurable,
      lintegral_const, MeasureTheory.measure_univ, mul_one]
    refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
    · rw [← ENNReal.ofReal_pow (vecNorm_nonneg p) 2]
      exact ENNReal.ofReal_lt_top
    · exact lt_of_le_of_ne le_top hsm

end

end SuperdiffusionCLT.Section3.Setup