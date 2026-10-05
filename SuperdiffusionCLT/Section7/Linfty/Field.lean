/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.L2AssemblyG
public import SuperdiffusionCLT.Section7.Prereq.LinftyReductionC
public import SuperdiffusionCLT.Section7.Root.InteriorApproxE
public import SuperdiffusionCLT.Section7.Root.FirstRootB
public import SuperdiffusionCLT.Section7.Analytic.DeGiorgi.BoundaryLocalizedC
public import SuperdiffusionCLT.Section7.Analytic.Geometry.IndicatorMultiscaleB
public import SuperdiffusionCLT.Section7.Prereq.RootCarriersApiC
public import SuperdiffusionCLT.Section7.MinimalScale.GridMaxEnlargeB
public import SuperdiffusionCLT.Section7.Lipschitz.Carriers
public import Homogenization.Sobolev.H1.LocalizedZeroTrace
public import SuperdiffusionCLT.Frozen.Section6.SharpScaleInputs
public import SuperdiffusionCLT.Section6.Root.CenteredRecenteredBridge
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementMoreoverBlockB
public import SuperdiffusionCLT.Section2.Cutoff.DerivativeSummabilityAllScales
public import SuperdiffusionCLT.Section7.Prereq.CaccioppoliH
public import SuperdiffusionCLT.Section7.Prereq.RhsLemmaB
public import SuperdiffusionCLT.Section8.Common.Regularity.Freezing.BoundaryFreezingRadius
public import SuperdiffusionCLT.Section8.DivergenceForm.Decay.LocalizedSkewAlgebra
public import SuperdiffusionCLT.Section7.Analytic.Geometry.SmoothingD
public import Mathlib.Order.CompletePartialOrder

/-!
# The centred field of a cube

For the recentred field `ν Id + (k - k(0))` of a sample and a good scale `m`, the field minus the
cube average of its stream matrix is `ν Id + (k - (k)_{□_m})`, the centred field of the cube; it is
elliptic on `□_m` with ratio a power of `ν⁻¹ m`, by the `L^∞` clause of `e.Dir.new.k.bounds`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff (ShellSeq)
open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)
open SuperdiffusionCLT.Section2.Carriers
open scoped ENNReal Pointwise
open scoped Matrix.Norms.L2Operator

variable {d : ℕ}

/-- The average of a continuous matrix field plus a constant. -/
theorem linf_field_avg_add_const {f : Vec d → Mat d} (hf : Continuous f) {S : Set (Vec d)}
    (hb : Bornology.IsBounded S) (hpos : volume S ≠ 0) (K : Mat d) :
    volumeAverageMat S (fun x => f x + K) = volumeAverageMat S f + K := by
  have hfin : volume S ≠ ⊤ := SuperdiffusionCLT.Section2.Cutoff.volume_ne_top_of_isBounded hb
  have hvol : (volume S).toReal ≠ 0 := by
    simp only [ne_eq, ENNReal.toReal_eq_zero_iff, hpos, hfin, or_self, not_false_eq_true]
  ext i k
  have hint : IntegrableOn (fun x => f x i k) S volume :=
    ((((continuous_apply k).comp ((continuous_apply i).comp hf)).continuousOn).integrableOn_compact
      hb.isCompact_closure).mono_set subset_closure
  have hconst : IntegrableOn (fun _ : Vec d => K i k) S volume :=
    integrableOn_const (C := K i k) hfin
  simp only [volumeAverageMat, volumeAverage, Matrix.add_apply]
  rw [MeasureTheory.integral_add hint hconst, MeasureTheory.setIntegral_const,
    MeasureTheory.Measure.real, smul_eq_mul, mul_add]
  field_simp

/-- The centred field has zero average over its cube. -/
theorem linf_field_avg_centered (omega : ShellSeq d) (m : ℕ)
    (hguard : ∀ i : ℕ, Summable fun k : ℕ =>
      shellDerivLinftyNorm (openCubeSet (originCube d (i : ℤ))) (omega k)) :
    volumeAverageMat (cubeSet (originCube d (m : ℤ)))
      (centeredStreamField omega (cubeSet (originCube d (m : ℤ)))) = 0 := by
  ext i j
  have h := SuperdiffusionCLT.Section2.Estimates.Stream.volumeAverage_centeredStreamField_eq_tsum
    (U := cubeSet (originCube d (m : ℤ))) (V := cubeSet (originCube d (m : ℤ)))
    (Homogenization.isBounded_cubeSet _)
    (SuperdiffusionCLT.Section2.Estimates.Stream.convex_cubeSet _)
    (SuperdiffusionCLT.Section2.Estimates.Stream.volume_cubeSet_ne_zero _)
    (R := (3 : ℝ) ^ m)
    (fun _ ha _ hb => SuperdiffusionCLT.Section2.Estimates.Stream.dist_le_of_mem_cubeSet_originCube ha hb)
    (measurableSet_cubeSet _) subset_rfl omega
    (SuperdiffusionCLT.Section2.Estimates.Stream.summable_shellDerivLinftyNorm_cubeSet_originCube
      (hguard m)) i j
  have hterm : ∀ k : ℕ, volumeAverage (cubeSet (originCube d (m : ℤ)))
      (fun y => centeredShellTerm omega (cubeSet (originCube d (m : ℤ))) k y i j) = 0 := by
    intro k
    have h2 := congrFun (congrFun
      (SuperdiffusionCLT.Section2.Estimates.Stream.volumeAverageMat_centeredShellTerm
        (U := cubeSet (originCube d (m : ℤ))) (V := cubeSet (originCube d (m : ℤ)))
        (Homogenization.isBounded_cubeSet _)
        (SuperdiffusionCLT.Section2.Estimates.Stream.volume_cubeSet_ne_zero _) omega k) i) j
    simpa only [volumeAverageMat, Matrix.sub_apply, sub_self] using h2
  show volumeAverage _ (fun y => centeredStreamField omega _ y i j) = 0
  rw [h]
  simp only [hterm, tsum_zero]

/-- **The centred field**: almost surely, at every good scale `m`, the recentred field minus
the average of the stream matrix over `□_m` is `ν Id + (k - (k)_{□_m})`, and it is elliptic on
`□_m` with upper constant `(ν + C m^{1+ρ})²/ν`, a power of `ν⁻¹ m` times `ν`, by the `L^∞` clause
of `e.Dir.new.k.bounds`. -/
theorem linf_field (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hInputs :
        ∃ C : ℝ, 1 ≤ C ∧
        ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
        ∀ cStar : ℝ, 0 < cStar →
        ∀ K : ℝ,
        ∀ ε ρ M : ℝ, 0 < ε → ε ≤ 1 → 0 < ρ → ρ < 1 → C ≤ M →
        ∃ Lhat : ℝ, 1 ≤ Lhat ∧
        ∀ (P : MeasureTheory.ProbabilityMeasure
        (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
        (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
        (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
        (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K
        hPrefix hJ2 hJ3 →
        ∃ X0 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
        Measurable X0 ∧ (∀ omega, 1 ≤ X0 omega) ∧
        Homogenization.IndependentSums.IsBigO P.toMeasure
        (Homogenization.IndependentSums.gammaSigma ρ)
        (fun omega => Real.log (X0 omega)) Lhat ∧
        ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
        ∀ m n : ℕ,
        X0 omega ≤ (3 : ℝ) ^ m →
        Lhat ≤ (m : ℝ) →
        (m : ℤ) - ⌈M * Real.log (m : ℝ)⌉ ≤ (n : ℤ) →
        n ≤ m →
        (∀ k : Fin d → ℤ,
        (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
        Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)) ⊆
        Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)) →
        -- e.Dir.new.full.good
        Homogenization.HomogenizationErrorOnCube
        (Homogenization.originCube d (n : ℤ)) (1 / 9)
        Homogenization.MultiscaleExponent.infinity
        (Homogenization.MultiscaleExponent.finite 2)
        (fun x => nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
        (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))
        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))
        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P •
        (1 : Homogenization.Mat d)) ≤
        ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ) ∧
        -- e.Dir.new.reg.ellipticity
        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ *
        Homogenization.LambdaSq (Homogenization.originCube d (n : ℤ))
        (1 / 4) (Homogenization.MultiscaleExponent.finite 1)
        (fun x => nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField
        omega
        (Homogenization.cubeSet
        (Homogenization.originCube d (m : ℤ)))
        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)) +
        SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P *
        (Homogenization.lambdaSq (Homogenization.originCube d (n : ℤ))
        (1 / 4) (Homogenization.MultiscaleExponent.finite 1)
        (fun x => nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField
        omega
        (Homogenization.cubeSet
        (Homogenization.originCube d (m : ℤ)))
        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)))⁻¹ ≤
        C ∧
        -- e.Dir.new.weak.flux, e.Dir.new.weak.grad, e.Dir.new.harmonic.approx
        (∀ u : Homogenization.AHarmonicFunction
        (fun x => nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
        (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))
        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))
        (Homogenization.openCubeSet (Homogenization.originCube d (n : ℤ))),
        ENNReal.ofReal
        (Homogenization.Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
        (Homogenization.originCube d (n : ℤ)) (1 / 4)
        (fun x => Homogenization.matVecMul
        (nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField
        omega
        (Homogenization.cubeSet
        (Homogenization.originCube d (m : ℤ)))
        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) -
        SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
        nu m P • (1 : Homogenization.Mat d))
        (u.toH1.grad x))) ≤
        ENNReal.ofReal
        (C *
        Real.sqrt
        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
        nu m P) *
        (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)) *
        Real.sqrt nu) *
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm
        (Homogenization.originCube d (n : ℤ)) 2
        (fun x => Real.sqrt (Homogenization.vecNormSq (u.toH1.grad x))) ∧
        ENNReal.ofReal
        (Homogenization.Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
        (Homogenization.originCube d (n : ℤ)) (1 / 4) u.toH1.grad) ≤
        ENNReal.ofReal
        (C *
        (Real.sqrt
        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
        nu m P))⁻¹ *
        Real.sqrt nu) *
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm
        (Homogenization.originCube d (n : ℤ)) 2
        (fun x => Real.sqrt (Homogenization.vecNormSq (u.toH1.grad x))) ∧
        ∃ w : Homogenization.AHarmonicFunction
        (fun _ => (1 : Homogenization.Mat d))
        (Homogenization.openCubeSet
        (Homogenization.originCube d ((n : ℤ) - 1))),
        ENNReal.ofReal ((3 : ℝ) ^ (-(n : ℝ))) *
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm
        (Homogenization.originCube d ((n : ℤ) - 1)) 2
        (fun x => u.toH1.toFun x - w.toH1.toFun x) ≤
        ENNReal.ofReal
        (C * (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)) *
        (Real.sqrt
        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
        nu m P))⁻¹ *
        Real.sqrt nu) *
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm
        (Homogenization.originCube d (n : ℤ)) 2
        (fun x =>
        Real.sqrt (Homogenization.vecNormSq (u.toH1.grad x)))) ∧
        -- e.Dir.new.sstar.close
        Homogenization.matNorm
        ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
        nu m P)⁻¹ •
        Homogenization.sigmaCoarse
        (Homogenization.cubeSet
        (Homogenization.originCube d (n : ℤ)))
        (fun x => nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField
        omega
        (Homogenization.cubeSet
        (Homogenization.originCube d (m : ℤ)))
        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)) -
        1) +
        Homogenization.matNorm
        ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
        nu m P)⁻¹ •
        Homogenization.sigmaStarCoarse
        (Homogenization.cubeSet
        (Homogenization.originCube d (n : ℤ)))
        (fun x => nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField
        omega
        (Homogenization.cubeSet
        (Homogenization.originCube d (m : ℤ)))
        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)) -
        1) ≤
        C * (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ))) ∧
        -- e.Dir.new.k.bounds
        ENNReal.ofReal ((m : ℝ)⁻¹) *
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm
        (Homogenization.originCube d (m : ℤ)) ∞
        (SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
        (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))) +
        ENNReal.ofReal ((3 : ℝ) ^ (-((1 / 4 : ℝ) * (m : ℝ)))) *
        SuperdiffusionCLT.Section2.Norms.matHatNegENorm
        (Homogenization.originCube d (m : ℤ)) (1 / 4) 2
        (SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
        (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))) ≤
        ENNReal.ofReal ((m : ℝ) ^ ρ)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ nu : ℝ, 0 < nu → nu ≤ 1 → ∀ cStar : ℝ, 0 < cStar → ∀ K : ℝ,
      ∀ ε ρ M : ℝ, 0 < ε → ε ≤ 1 → 0 < ρ → ρ < 1 → C ≤ M →
      ∃ Lhat : ℝ, 1 ≤ Lhat ∧ ∀ (P : ProbabilityMeasure (ShellSeq d)) (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
        (hJ3 : ShellLawJ3 d P), ShellLawJ1Restriction d P → ShellLawJ4 d P →
        ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
        ∃ X0 : ShellSeq d → ℝ, Measurable X0 ∧ (∀ omega, 1 ≤ X0 omega) ∧
        Homogenization.IndependentSums.IsBigO P.toMeasure
          (Homogenization.IndependentSums.gammaSigma ρ) (fun omega => Real.log (X0 omega)) Lhat ∧
        ∀ᵐ omega ∂P.toMeasure, ∀ m : ℕ, X0 omega ≤ (3 : ℝ) ^ m → Lhat ≤ (m : ℝ) →
          (∀ x : Vec d, Section6.fullCoefficientRecentered nu omega x -
              volumeAverageMat (cubeSet (originCube d (m : ℤ)))
                (Section6.fullStreamRecentered omega) =
            nu • (1 : Mat d) + SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
              (cubeSet (originCube d (m : ℤ))) x) ∧
          IsEllipticFieldOn nu ((nu + C * (m : ℝ) ^ (1 + ρ)) ^ 2 / nu) (openCubeSet (originCube d (m : ℤ)))
            (fun x => nu • (1 : Mat d) +
              SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
                (cubeSet (originCube d (m : ℤ))) x) := by
  have _hd := hd
  obtain ⟨C, hC1, hI⟩ := hInputs
  refine ⟨C, hC1, ?_⟩
  intro nu hnu hnu1 cStar hc K ε ρ M hε hε1 hρ hρ1 hCM
  obtain ⟨Lhat, hL1, hP⟩ := hI nu hnu hnu1 cStar hc K ε ρ M hε hε1 hρ hρ1 hCM
  refine ⟨Lhat, hL1, ?_⟩
  intro P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨X0, hX0m, hX01, hbig, hae⟩ := hP P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  refine ⟨X0, hX0m, hX01, hbig, ?_⟩
  filter_upwards [hae, SuperdiffusionCLT.Section2.Cutoff.ae_forall_summable_shellDerivLinftyNorm_originCube hJ3,
    Section6.ae_continuous_fullStreamRecentered hJ3] with omega hω hguard hcont m hX hL
  have hm1 : (1 : ℝ) ≤ m := le_trans hL1 hL
  have hMpos : 0 ≤ M * Real.log (m : ℝ) :=
    mul_nonneg (by linarith only [hC1, hCM]) (Real.log_nonneg hm1)
  have hwin : (m : ℤ) - ⌈M * Real.log (m : ℝ)⌉ ≤ (m : ℤ) := by
    have : 0 ≤ ⌈M * Real.log (m : ℝ)⌉ := Int.ceil_nonneg hMpos
    omega
  have hkb := (hω m m hX hL hwin le_rfl).2
  -- the identity
  obtain ⟨K0, hK0skew, hK0⟩ := Section6.centered_eq_recentered_add_skew omega hguard nu m
  have hcentered : ∀ x, centeredStreamField omega (cubeSet (originCube d (m : ℤ))) x =
      Section6.fullStreamRecentered omega x + K0 := by
    intro x
    have := hK0 x
    simp only [Section6.fullCoefficientRecentered] at this
    exact add_left_cancel (by rw [this, add_assoc])
  have hcontc : Continuous (centeredStreamField omega (cubeSet (originCube d (m : ℤ)))) := by
    have : centeredStreamField omega (cubeSet (originCube d (m : ℤ))) =
        fun x => Section6.fullStreamRecentered omega x + K0 := funext hcentered
    rw [this]
    exact hcont.add continuous_const
  have havg : volumeAverageMat (cubeSet (originCube d (m : ℤ))) (Section6.fullStreamRecentered omega)
      = -K0 := by
    have h1 := linf_field_avg_add_const hcont (S := cubeSet (originCube d (m : ℤ)))
      (Homogenization.isBounded_cubeSet _)
      (SuperdiffusionCLT.Section2.Estimates.Stream.volume_cubeSet_ne_zero _) K0
    have h2 : (fun x => Section6.fullStreamRecentered omega x + K0) =
        centeredStreamField omega (cubeSet (originCube d (m : ℤ))) := (funext hcentered).symm
    rw [h2, linf_field_avg_centered omega m hguard] at h1
    exact eq_neg_of_add_eq_zero_left h1.symm
  refine ⟨fun x => ?_, ?_⟩
  · rw [havg]
    have := hK0 x
    rw [sub_neg_eq_add, ← this]
  · -- ellipticity
    have hae' := SuperdiffusionCLT.Section7.r1_ae_opnorm_k (originCube d (m : ℤ)) hm1 _ hkb
    have hpt := ca1w_opnorm_pointwise (originCube d (m : ℤ)) hcontc hae'
    have hent : ∀ i j : Fin d, Continuous fun x : Vec d =>
        centeredStreamField omega (cubeSet (originCube d (m : ℤ))) x i j :=
      fun i j => (continuous_apply j).comp ((continuous_apply i).comp hcontc)
    classical
    refine ⟨?_, fun x hx => ?_⟩
    · refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
      refine Measurable.ite (isOpen_openCubeSet _).measurableSet ?_ measurable_const
      simp only [Matrix.add_apply]
      exact measurable_const.add (hent i j).measurable
    · have hnu0 : 0 < nu := hnu
      have hsymm := SuperdiffusionCLT.Section8.DivergenceForm.Decay.symmPart_scalar_add_skew
        (A := nu • (1 : Mat d) + centeredStreamField omega (cubeSet (originCube d (m : ℤ))) x)
        rfl (centeredStreamField_skew omega _ x)
      have hB : ‖HilbertVec.applyMat ((nu • (1 : Mat d) +
          centeredStreamField omega (cubeSet (originCube d (m : ℤ))) x) - nu • (1 : Mat d))‖ ≤
            C * (m : ℝ) ^ (1 + ρ) := by
        rw [add_sub_cancel_left]
        change Book.Ch02.matrixOperatorNorm _ ≤ _
        refine (hpt x hx).trans ?_
        have : (1 : ℝ) ≤ (m : ℝ) ^ (1 + ρ) :=
          Real.one_le_rpow hm1 (by linarith only [hρ])
        have hmp : 0 ≤ (m : ℝ) ^ (1 + ρ) := by linarith only [this]
        nlinarith only [hC1, hmp]
      have hell := SuperdiffusionCLT.Section8.Common.Regularity.Freezing.isEllipticMatrix_of_symmPart_eq_of_opNorm_le
        hnu0 hsymm hB
      refine hell.mono hnu0 le_rfl ?_
      have hB0 : 0 ≤ C * (m : ℝ) ^ (1 + ρ) := by
        have : (0 : ℝ) ≤ (m : ℝ) ^ (1 + ρ) := Real.rpow_nonneg (by linarith only [hm1]) _
        nlinarith only [hC1, this]
      rw [div_le_div_iff_of_pos_right hnu0]
      nlinarith only [hB0, hnu0]

/-- Witness: the hypothesis is `sharp_scale_inputs`, so the theorem applies. -/
example [NeZero d] (hd : 2 ≤ d) : ∃ C : ℝ, 1 ≤ C :=
  (linf_field d hd (SuperdiffusionCLT.Frozen.Section6.sharp_scale_inputs d hd)).imp
    fun _ h => h.1

end SuperdiffusionCLT.Section7
