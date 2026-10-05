/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm1Localization
public import SuperdiffusionCLT.Section3.Terms.TranslatedBlocks

/-!
# The annealed localization line `hLocalized` of Step 1 of `l.RHS.term1`

The proof of `l.RHS.term1` in the paper averages the quenched
cube-wise display `e.localization.minimizers.applied` over the scale-`n`
sub-cubes of the large cube and takes expectations:

`E[‖a_ℓ(∇u_n − ∇ũ_n)‖²_{L̲²(cu_m)}]
   = avsum_{z} E[‖a_ℓ(∇u_n − ∇ũ_n)‖²_{L̲²(z+cu_n)}]
   ≤ C ν^{-3} E[‖a_ℓ‖⁴_{L^∞(cu_ℓ)}]^{1/2} shom_{L',*}(cu_n)
       avsum_z 3^n E[‖∇(k_{L'}−k_ℓ)‖²_{L^∞(z+cu_n)}]^{1/2}`.

This file assembles that line in the exact `ℝ≥0∞` shape of the localization line
`hLocalized` of Step 1 of `l.RHS.term1`.

## Main results

* `openCubeSetOriginMono`,
  `ae_matrixOperatorNorm_le_coeffCubeLinftyENorm_translate`: `e.kmn.Linfty`
  together with stationarity, namely
  `‖a_ℓ‖_{L^∞(z+cu_n)}(ω) ≤ ‖a_ℓ‖_{L^∞(cu_ℓ)}(τ_z ω)`, from the
  covariance `RHSTerm1InputsG.translateCoeffField_coefficientCutoff` and the
  pointwise domination `RHSTerm1Localization.cubeLinftyTop_facts`.
* `lintegral_sq_mul_le_of_measurable`: the `ℝ≥0∞` Cauchy-Schwarz inequality in
  the sample, `E[X²Y] ≤ E[X⁴]^{1/2}E[Y²]^{1/2}`.
* `subcube_flux_sq_le`: the quenched sub-cube display, the quenched
  localization estimate of `RHSTerm1Localization` multiplied by the `L^∞`
  size of `a_ℓ` on the sub-cube.
* `localization_bridge`: `hLocalized` on the cube scales `[S.n, S.m]`, by the
  `ℝ≥0∞` sub-cube decomposition `cubeLpENorm_two_sq_eq_inv_card_mul_sum`, the
  stationarity of the shell law (`J2`) and that Cauchy-Schwarz inequality.

## The three inputs that stay explicit, and why

* `hLocMin`: the third clause of the conclusion of
  `Frozen.Section2.cutoff_localization` (`e.localization.minimizers`), at the
  scale triple `(m, n, L) = (S.ell, S.n, S.LPrime)`, with its own domain binder;
  the `L^∞` window of that statement is written through the carrier
  `RHSTerm1Localization.anchorDerivSup`, which
  `RHSTerm1Localization.anchorDerivSup_eq` exhibits as its literal supremum.
* `hMeasCoeff`, `hMeasDeriv`: the measurability in the sample of the two
  annealed `L^∞` carriers.  They are typing data of the same class as the five
  measurability binders that the assembly of `l.RHS.term1` already carries: without them
  the two `∫⁻` of the conclusion are Mathlib's lower integrals of possibly
  non-measurable integrands, the stationarity transport
  (`MeasurePreserving.lintegral_comp`) does not apply, and neither does the
  `ℝ≥0∞` Cauchy-Schwarz inequality.  Both carriers are essential suprema over a
  cube of a field built from the shell sequence through a choice-free but
  uncountable supremum, and their measurability is carried as a hypothesis.

## References

The paper: `e.localization.minimizers.applied` and the proof of `l.RHS.term1`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section2.Estimates.Stream
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The `ℝ≥0∞` Cauchy-Schwarz inequality in the sample -/

/-- **Cauchy-Schwarz in `ω`** in the shape the proof uses it:
`E[X² Y] ≤ E[X⁴]^{1/2} E[Y²]^{1/2}`.  This is Mathlib's Hölder inequality for
the lower integral at the conjugate pair `(2, 2)`. -/
theorem lintegral_sq_mul_le_of_measurable {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) {X Y : Omega → ℝ≥0∞} (hX : Measurable X)
    (hY : Measurable Y) :
    (∫⁻ omega, X omega ^ (2 : ℕ) * Y omega ∂mu) ≤
      (∫⁻ omega, X omega ^ (4 : ℕ) ∂mu) ^ ((1 : ℝ) / 2) *
        (∫⁻ omega, Y omega ^ (2 : ℕ) ∂mu) ^ ((1 : ℝ) / 2) := by
  have hconj : (2 : ℝ).HolderConjugate 2 := by constructor <;> norm_num
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq mu hconj
    (f := fun omega => X omega ^ (2 : ℕ)) (g := Y)
    ((hX.pow_const 2).aemeasurable) hY.aemeasurable
  have hfour : ∀ omega : Omega, (X omega ^ (2 : ℕ)) ^ (2 : ℝ) = X omega ^ (4 : ℕ) := by
    intro omega
    rw [← ENNReal.rpow_natCast (X omega) 2, ← ENNReal.rpow_mul,
      ← ENNReal.rpow_natCast (X omega) 4]
    norm_num
  have htwo : ∀ omega : Omega, Y omega ^ (2 : ℝ) = Y omega ^ (2 : ℕ) := by
    intro omega
    rw [← ENNReal.rpow_natCast (Y omega) 2]
    norm_num
  simp only [Pi.mul_apply] at h
  rw [lintegral_congr hfour, lintegral_congr htwo] at h
  simpa only [one_div] using h

/-! ## The `L^∞` window of the coefficient on a sub-cube -/

/-- The centred open cubes increase with the scale. -/
private theorem openCubeSetOriginMono {n ell : ℕ} (h : n ≤ ell) :
    openCubeSet (originCube d (n : ℤ)) ⊆ openCubeSet (originCube d (ell : ℤ)) := by
  have hnl : (n : ℤ) ≤ (ell : ℤ) := by exact_mod_cast h
  have hpow : (3 : ℝ) ^ (n : ℤ) ≤ (3 : ℝ) ^ (ell : ℤ) :=
    zpow_le_zpow_right₀ (by norm_num) hnl
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (n : ℤ) := by positivity
  intro x hx
  rw [openCubeSet_eq_pi_Ioo] at hx
  rw [openCubeSet_eq_pi_Ioo]
  intro i _
  have hxi := hx i (Set.mem_univ i)
  have hidx : ∀ k : ℤ, (((originCube d k).index i : ℝ)) = 0 := by
    intro k
    norm_num [originCube]
  have hsf : ∀ k : ℤ, cubeScaleFactor (originCube d k) = (3 : ℝ) ^ k := fun _ => rfl
  simp only [Set.mem_Ioo, hidx, hsf] at hxi ⊢
  constructor
  · linarith only [hxi.1, hpow]
  · linarith only [hxi.2, hpow]

/-- **`e.kmn.Linfty` on a sub-cube, together with stationarity**:
the `L^∞` size of `a_ℓ` on the sub-cube `z + cu_n` is at most its `L^∞` size on
the centred cube `cu_ℓ` for the translated shell sequence.  The coefficient is
continuous, so its pointwise size on the open cube is dominated by the
essential-supremum carrier `RHSTerm1Inputs.coeffCubeLinftyENorm`
(`RHSTerm1Localization.cubeLinftyTop_facts`); the translation is the
covariance `RHSTerm1InputsG.translateCoeffField_coefficientCutoff`, and the
enlargement from `cu_n` to `cu_ℓ` is `openCubeSetOriginMono`. -/
theorem ae_matrixOperatorNorm_le_coeffCubeLinftyENorm_translate {nu : ℝ}
    (omega : ShellSeq d) {n ell m : ℕ} (hnl : n ≤ ell) (hnm : n ≤ m)
    {R : TriadicCube d} (hR : R ∈ largeCubeSubcubes d n m) :
    ∀ᵐ x ∂normalizedCubeMeasure R,
      matrixOperatorNorm ((coefficientCutoff nu omega ell).toCoeffField x) ≤
        (coeffCubeLinftyENorm nu ell ell
          (ShellField.translateSequence (triadicCubeShift R) omega)).toReal := by
  classical
  have hscale : R.scale = (n : ℤ) := scale_of_mem_largeCubeSubcubes hnm hR
  have hcont : Continuous (fun y : Vec d => matrixOperatorNorm
      ((coefficientCutoff nu (ShellField.translateSequence (triadicCubeShift R) omega)
        ell).toCoeffField y)) :=
    ShellField.continuous_matrixOperatorNorm.comp
      (continuous_coefficientCutoff_apply nu
        (ShellField.translateSequence (triadicCubeShift R) omega) ell)
  have hnn : ∀ y : Vec d, 0 ≤ matrixOperatorNorm
      ((coefficientCutoff nu (ShellField.translateSequence (triadicCubeShift R) omega)
        ell).toCoeffField y) := fun _ => matrixOperatorNorm_nonneg _
  obtain ⟨_, hdom⟩ := cubeLinftyTop_facts (Q := originCube d (ell : ℤ)) hcont hnn
  have hae : ∀ᵐ x ∂normalizedCubeMeasure R, x ∈ openCubeSet R := by
    rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
    exact MeasureTheory.Measure.ae_smul_measure
      (MeasureTheory.ae_restrict_mem (measurableSet_openCubeSet R)) _
  filter_upwards [hae] with x hx
  have hxsub : x - triadicCubeShift R ∈ openCubeSet (originCube d (n : ℤ)) := by
    rw [openCubeSet_eq_translateSet_originCube_of_triadicCube R, hscale] at hx
    exact mem_translateSet_iff_sub_mem.mp hx
  have hxell : x - triadicCubeShift R ∈ openCubeSet (originCube d (ell : ℤ)) :=
    openCubeSetOriginMono hnl hxsub
  have hpt : (coefficientCutoff nu omega ell).toCoeffField x =
      (coefficientCutoff nu (ShellField.translateSequence (triadicCubeShift R) omega)
        ell).toCoeffField (x - triadicCubeShift R) := by
    have h := congrFun
      (translateCoeffField_coefficientCutoff nu (triadicCubeShift R) omega ell)
      (x - triadicCubeShift R)
    rw [← h]
    show (coefficientCutoff nu omega ell).toCoeffField x =
      (coefficientCutoff nu omega ell).toCoeffField
        (fun i => (x - triadicCubeShift R) i + triadicCubeShift R i)
    congr 1
    funext i
    show x i = x i - triadicCubeShift R i + triadicCubeShift R i
    ring
  rw [hpt]
  exact hdom (x - triadicCubeShift R) hxell

/-! ## The quenched sub-cube display -/

variable {nu : ℝ}

/-- **The quenched display on one sub-cube.**  The localization
estimate `RHSTerm1Localization.localization_minimizers_gluedSubcube` multiplied
by the `L^∞` size of `a_ℓ` on that sub-cube, in the `ℝ≥0∞` cube carriers.
Both random factors are read at the translated shell sequence, which is where
`e.kmn.Linfty` and stationarity enter. -/
theorem subcube_flux_sq_le (hnu : 0 < nu) (S : ScaleSelection) (F : Vec d)
    {Cloc : ℝ} (hCloc0 : 0 ≤ Cloc)
    (hCentre : ∀ omega' : ShellSeq d,
      volumeAverage (openCubeSet (originCube d (S.n : ℤ)))
          (fun x => vecNormSq
            (cubeMaximizerGradient hnu omega' S.LPrime F (originCube d (S.n : ℤ)) x -
              cubeMaximizerGradient hnu omega' S.ell F (originCube d (S.n : ℤ)) x)) ≤
        Cloc * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ S.n *
            anchorDerivSup S.ell S.LPrime S.n omega' * (nu⁻¹ * vecNormSq F))
    (hnl : S.n ≤ S.ell) (hnm : S.n ≤ S.m) (omega : ShellSeq d)
    {R : TriadicCube d} (hR : R ∈ largeCubeSubcubes d S.n S.m) :
    (vecCubeLpENorm R 2
        (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
          (gluedGradientField hnu S.LPrime S.n S.m F omega x -
            gluedGradientField hnu S.ell S.n S.m F omega x))) ^ (2 : ℕ) ≤
      (coeffCubeLinftyENorm nu S.ell S.ell
          (ShellField.translateSequence (triadicCubeShift R) omega)) ^ (2 : ℕ) *
        (ENNReal.ofReal (Cloc * nu ^ (-(3 : ℝ)) * (3 : ℝ) ^ ((S.n : ℝ)) *
            vecNormSq F) *
          shellDerivCubeLinftyENorm S.ell S.LPrime S.n
            (ShellField.translateSequence (triadicCubeShift R) omega)) := by
  set om : ShellSeq d := ShellField.translateSequence (triadicCubeShift R) omega with hom
  -- the coefficient factor
  have hAle := coeffCubeLinftyENorm_le_ofReal nu (le_of_lt hnu) om S.ell S.ell
  have hAfin : coeffCubeLinftyENorm nu S.ell S.ell om ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hAle
  have hmemV : MemVectorL2 (openCubeSet R)
      (fun x => gluedGradientField hnu S.LPrime S.n S.m F omega x -
        gluedGradientField hnu S.ell S.n S.m F omega x) :=
    (memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.n S.m F omega R).sub
      (memVectorL2_openCubeSet_gluedGradientField hnu S.ell S.n S.m F omega R)
  have hmul := vecCubeLpENorm_matVecMul_le (Q := R) 2
    (fun x => (coefficientCutoff nu omega S.ell).toCoeffField x)
    (fun x => gluedGradientField hnu S.LPrime S.n S.m F omega x -
      gluedGradientField hnu S.ell S.n S.m F omega x)
    ENNReal.toReal_nonneg
    (aestronglyMeasurable_hilbertifyVecField_matVecMul
      (continuous_coefficientCutoff_apply nu omega S.ell)
      (Section2.Norms.memLp_hilbertifyVecField_of_memVectorL2 hmemV).aestronglyMeasurable)
    (ae_matrixOperatorNorm_le_coeffCubeLinftyENorm_translate omega hnl hnm hR)
  rw [ENNReal.ofReal_toReal hAfin] at hmul
  have hV2 : (vecCubeLpENorm R 2
        (fun x => gluedGradientField hnu S.LPrime S.n S.m F omega x -
          gluedGradientField hnu S.ell S.n S.m F omega x)) ^ (2 : ℕ) ≤
      ENNReal.ofReal (Cloc * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ S.n *
        anchorDerivSup S.ell S.LPrime S.n om * (nu⁻¹ * vecNormSq F)) :=
    vecCubeLpENorm_two_sq_le_of_volumeAverage_le hmemV
      (localization_minimizers_gluedSubcube hnu hnm F hCentre omega hR)
  -- the real bookkeeping of the two constants
  have hpow3 : (3 : ℝ) ^ S.n = (3 : ℝ) ^ ((S.n : ℝ)) := by
    rw [Real.rpow_natCast]
  have hpownu : nu ^ (-(2 : ℝ)) * nu⁻¹ = nu ^ (-(3 : ℝ)) := by
    rw [show nu⁻¹ = nu ^ (-(1 : ℝ)) from by rw [Real.rpow_neg (le_of_lt hnu), Real.rpow_one],
      ← Real.rpow_add hnu]
    norm_num
  have hKsplit : Cloc * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ S.n *
        anchorDerivSup S.ell S.LPrime S.n om * (nu⁻¹ * vecNormSq F) =
      (Cloc * nu ^ (-(3 : ℝ)) * (3 : ℝ) ^ ((S.n : ℝ)) * vecNormSq F) *
        anchorDerivSup S.ell S.LPrime S.n om := by
    rw [← hpow3, ← hpownu]
    ring
  have hK0 : (0 : ℝ) ≤ Cloc * nu ^ (-(3 : ℝ)) * (3 : ℝ) ^ ((S.n : ℝ)) * vecNormSq F := by
    have h1 : (0 : ℝ) ≤ nu ^ (-(3 : ℝ)) := Real.rpow_nonneg (le_of_lt hnu) _
    have h2 : (0 : ℝ) ≤ (3 : ℝ) ^ ((S.n : ℝ)) := Real.rpow_nonneg (by norm_num) _
    have h3 : (0 : ℝ) ≤ vecNormSq F := vecNormSq_nonneg F
    exact mul_nonneg (mul_nonneg (mul_nonneg hCloc0 h1) h2) h3
  calc (vecCubeLpENorm R 2
        (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
          (gluedGradientField hnu S.LPrime S.n S.m F omega x -
            gluedGradientField hnu S.ell S.n S.m F omega x))) ^ (2 : ℕ)
      ≤ (coeffCubeLinftyENorm nu S.ell S.ell om *
            vecCubeLpENorm R 2
              (fun x => gluedGradientField hnu S.LPrime S.n S.m F omega x -
                gluedGradientField hnu S.ell S.n S.m F omega x)) ^ (2 : ℕ) :=
        pow_le_pow_left' hmul 2
    _ = (coeffCubeLinftyENorm nu S.ell S.ell om) ^ (2 : ℕ) *
          (vecCubeLpENorm R 2
            (fun x => gluedGradientField hnu S.LPrime S.n S.m F omega x -
              gluedGradientField hnu S.ell S.n S.m F omega x)) ^ (2 : ℕ) :=
        mul_pow _ _ 2
    _ ≤ (coeffCubeLinftyENorm nu S.ell S.ell om) ^ (2 : ℕ) *
          ENNReal.ofReal (Cloc * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ S.n *
            anchorDerivSup S.ell S.LPrime S.n om * (nu⁻¹ * vecNormSq F)) :=
        mul_le_mul' le_rfl hV2
    _ = (coeffCubeLinftyENorm nu S.ell S.ell om) ^ (2 : ℕ) *
          (ENNReal.ofReal (Cloc * nu ^ (-(3 : ℝ)) * (3 : ℝ) ^ ((S.n : ℝ)) *
              vecNormSq F) *
            ENNReal.ofReal (anchorDerivSup S.ell S.LPrime S.n om)) := by
        rw [hKsplit, ENNReal.ofReal_mul hK0]
    _ ≤ (coeffCubeLinftyENorm nu S.ell S.ell om) ^ (2 : ℕ) *
          (ENNReal.ofReal (Cloc * nu ^ (-(3 : ℝ)) * (3 : ℝ) ^ ((S.n : ℝ)) *
              vecNormSq F) *
            shellDerivCubeLinftyENorm S.ell S.LPrime S.n om) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl
          (ofReal_anchorDerivSup_le_shellDerivCubeLinftyENorm S.ell S.LPrime S.n om))

/-! ## `hLocalized` -/

/-- **The localization line `hLocalized` of Step 1 of `l.RHS.term1`**,
on the cube scales
`[S.n, S.m]` and in the exact shape
that the assembly of `l.RHS.term1` consumes it.

`hLocMin` is the third clause of the conclusion of
`Frozen.Section2.cutoff_localization` (`e.localization.minimizers`), at the
scale triple `(m, n, L) = (S.ell, S.n, S.LPrime)`.  The two remaining explicit inputs
`hMeasCoeff` and `hMeasDeriv` are documented in the module header. -/
theorem localization_bridge (d : ℕ) [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (S : ScaleSelection) (hSorder : ScalesOrdering S)
    (e : Vec d) {Cloc : ℝ} (hCloc0 : 0 ≤ Cloc)
    (hLocMin : ∀ U : Book.Ch02.Domain d,
        (U : Set (Vec d)) ⊆ openCubeSet (originCube d (S.n : ℤ)) →
        ∀ (omega' : ShellSeq d) (p q : Vec d)
          (u : AHarmonicFunction
            (fun x : Vec d =>
              (coefficientCutoff nu omega' S.LPrime).toCoeffField x -
                volumeAverageMat (U : Set (Vec d))
                  (fun y => finiteShellIncrement omega' S.ell S.LPrime y))
            (U : Set (Vec d)))
          (v : AHarmonicFunction
            (coefficientCutoff nu omega' S.ell).toCoeffField (U : Set (Vec d))),
          (∀ w : AHarmonicFunction
              (fun x : Vec d =>
                (coefficientCutoff nu omega' S.LPrime).toCoeffField x -
                  volumeAverageMat (U : Set (Vec d))
                    (fun y => finiteShellIncrement omega' S.ell S.LPrime y))
              (U : Set (Vec d)),
              volumeAverage (U : Set (Vec d))
                  (scalarResponseIntegrand (U : Set (Vec d))
                    (fun x : Vec d =>
                      (coefficientCutoff nu omega' S.LPrime).toCoeffField x -
                        volumeAverageMat (U : Set (Vec d))
                          (fun y => finiteShellIncrement omega' S.ell S.LPrime y))
                    p q w) ≤
                volumeAverage (U : Set (Vec d))
                  (scalarResponseIntegrand (U : Set (Vec d))
                    (fun x : Vec d =>
                      (coefficientCutoff nu omega' S.LPrime).toCoeffField x -
                        volumeAverageMat (U : Set (Vec d))
                          (fun y => finiteShellIncrement omega' S.ell S.LPrime y))
                    p q u)) →
          (∀ w : AHarmonicFunction
              (coefficientCutoff nu omega' S.ell).toCoeffField (U : Set (Vec d)),
              volumeAverage (U : Set (Vec d))
                  (scalarResponseIntegrand (U : Set (Vec d))
                    (coefficientCutoff nu omega' S.ell).toCoeffField p q w) ≤
                volumeAverage (U : Set (Vec d))
                  (scalarResponseIntegrand (U : Set (Vec d))
                    (coefficientCutoff nu omega' S.ell).toCoeffField p q v)) →
            volumeAverage (U : Set (Vec d))
                (fun x => vecNormSq (u.toH1.grad x - v.toH1.grad x)) ≤
              Cloc * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ S.n *
                  anchorDerivSup S.ell S.LPrime S.n omega' *
                (ResponseJ (U : Set (Vec d)) p q
                    (fun x : Vec d =>
                      (coefficientCutoff nu omega' S.LPrime).toCoeffField x -
                        volumeAverageMat (U : Set (Vec d))
                          (fun y => finiteShellIncrement omega' S.ell S.LPrime y)) +
                  ResponseJ (U : Set (Vec d)) p q
                    (coefficientCutoff nu omega' S.ell).toCoeffField +
                  2 * vecDot p q))
    (hMeasCoeff : Measurable fun omega : ShellSeq d =>
      coeffCubeLinftyENorm nu S.ell S.ell omega)
    (hMeasDeriv : Measurable fun omega : ShellSeq d =>
      shellDerivCubeLinftyENorm S.ell S.LPrime S.n omega) :
    ∀ r : ℕ, S.n ≤ r → r ≤ S.m → (∫⁻ omega : ShellSeq d,
        (vecCubeLpENorm (originCube d (r : ℤ)) 2
          (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
            (gluedGradientField hnu S.LPrime S.n S.m
                (fluxSlot nu S.LPrime P S.n e) omega x -
              gluedGradientField hnu S.ell S.n S.m
                (fluxSlot nu S.LPrime P S.n e) omega x))) ^ (2 : ℕ)
      ∂P.toMeasure : ℝ≥0∞) ≤
      ENNReal.ofReal (Cloc * nu ^ (-(3 : ℝ)) * (3 : ℝ) ^ ((S.n : ℝ)) *
          vecNormSq (fluxSlot nu S.LPrime P S.n e)) *
        ((∫⁻ omega : ShellSeq d,
            (coeffCubeLinftyENorm nu S.ell S.ell omega) ^ (4 : ℕ)
          ∂P.toMeasure : ℝ≥0∞) ^ ((1 : ℝ) / 2)) *
        ((∫⁻ omega : ShellSeq d,
            (shellDerivCubeLinftyENorm S.ell S.LPrime S.n omega) ^ (2 : ℕ)
          ∂P.toMeasure : ℝ≥0∞) ^ ((1 : ℝ) / 2)) := by
  classical
  intro r hnr hrm
  have hnl : S.n ≤ S.ell := le_of_lt hSorder.n_lt_ell
  have hnm : S.n ≤ S.m := le_trans hnr hrm
  set F : Vec d := fluxSlot nu S.LPrime P S.n e with hFdef
  set K : ℝ := Cloc * nu ^ (-(3 : ℝ)) * (3 : ℝ) ^ ((S.n : ℝ)) * vecNormSq F with hKdef
  set G : ShellSeq d → ℝ≥0∞ := fun om =>
    (coeffCubeLinftyENorm nu S.ell S.ell om) ^ (2 : ℕ) *
      (ENNReal.ofReal K * shellDerivCubeLinftyENorm S.ell S.LPrime S.n om) with hGdef
  have hGmeas : Measurable G :=
    (hMeasCoeff.pow_const 2).mul (measurable_const.mul hMeasDeriv)
  have hCentre : ∀ omega' : ShellSeq d,
      volumeAverage (openCubeSet (originCube d (S.n : ℤ)))
          (fun x => vecNormSq
            (cubeMaximizerGradient hnu omega' S.LPrime F (originCube d (S.n : ℤ)) x -
              cubeMaximizerGradient hnu omega' S.ell F (originCube d (S.n : ℤ)) x)) ≤
        Cloc * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ S.n *
          anchorDerivSup S.ell S.LPrime S.n omega' * (nu⁻¹ * vecNormSq F) :=
    fun omega' => localization_minimizers_originCube hnu omega' hCloc0 F hLocMin
  -- the quenched sub-cube decomposition
  have hptw : ∀ omega : ShellSeq d,
      (vecCubeLpENorm (originCube d (r : ℤ)) 2
        (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
          (gluedGradientField hnu S.LPrime S.n S.m F omega x -
            gluedGradientField hnu S.ell S.n S.m F omega x))) ^ (2 : ℕ) ≤
      ENNReal.ofReal (((largeCubeSubcubes d S.n r).card : ℝ))⁻¹ *
        ∑ R ∈ largeCubeSubcubes d S.n r,
          G (ShellField.translateSequence (triadicCubeShift R) omega) := by
    intro omega
    have hsplit := cubeLpENorm_two_sq_eq_inv_card_mul_sum
      (Q := originCube d (r : ℤ)) (r - S.n)
      (hilbertifyVecField (fun x =>
        matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
          (gluedGradientField hnu S.LPrime S.n S.m F omega x -
            gluedGradientField hnu S.ell S.n S.m F omega x)))
    rw [show descendantsAtDepth (originCube d (r : ℤ)) (r - S.n) =
      largeCubeSubcubes d S.n r from rfl] at hsplit
    rw [show vecCubeLpENorm (originCube d (r : ℤ)) 2
        (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
          (gluedGradientField hnu S.LPrime S.n S.m F omega x -
            gluedGradientField hnu S.ell S.n S.m F omega x)) ^ (2 : ℕ) =
      Section2.Norms.cubeLpENorm (originCube d (r : ℤ)) 2
          (hilbertifyVecField (fun x =>
            matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
              (gluedGradientField hnu S.LPrime S.n S.m F omega x -
                gluedGradientField hnu S.ell S.n S.m F omega x))) ^ (2 : ℕ) from rfl,
      hsplit]
    refine mul_le_mul' le_rfl (Finset.sum_le_sum ?_)
    intro R hR
    exact subcube_flux_sq_le hnu S F hCloc0 hCentre hnl hnm omega
      (mem_largeCubeSubcubes_of_mem_largeCubeSubcubes_le hnr hrm hR)
  -- the annealed assembly
  have hcardpos : (0 : ℝ) < ((largeCubeSubcubes d S.n r).card : ℝ) := by
    exact_mod_cast Finset.card_pos.2 (largeCubeSubcubes_nonempty d S.n r)
  have hcancel : ENNReal.ofReal (((largeCubeSubcubes d S.n r).card : ℝ))⁻¹ *
      (((largeCubeSubcubes d S.n r).card : ℕ) : ℝ≥0∞) = 1 := by
    rw [← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (le_of_lt (inv_pos.2 hcardpos)),
      inv_mul_cancel₀ (ne_of_gt hcardpos), ENNReal.ofReal_one]
  refine le_trans (lintegral_mono hptw) ?_
  calc ∫⁻ omega : ShellSeq d,
        ENNReal.ofReal (((largeCubeSubcubes d S.n r).card : ℝ))⁻¹ *
          ∑ R ∈ largeCubeSubcubes d S.n r,
            G (ShellField.translateSequence (triadicCubeShift R) omega) ∂P.toMeasure
      = ENNReal.ofReal (((largeCubeSubcubes d S.n r).card : ℝ))⁻¹ *
          ∫⁻ omega : ShellSeq d, ∑ R ∈ largeCubeSubcubes d S.n r,
            G (ShellField.translateSequence (triadicCubeShift R) omega)
          ∂P.toMeasure := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (((largeCubeSubcubes d S.n r).card : ℝ))⁻¹ *
          ∑ R ∈ largeCubeSubcubes d S.n r, ∫⁻ omega : ShellSeq d,
            G (ShellField.translateSequence (triadicCubeShift R) omega)
          ∂P.toMeasure := by
        refine congrArg (fun t => ENNReal.ofReal
          (((largeCubeSubcubes d S.n r).card : ℝ))⁻¹ * t) ?_
        exact lintegral_finsetSum _ (fun R _ =>
          hGmeas.comp (ShellField.measurable_translateSequence (triadicCubeShift R)))
    _ = ENNReal.ofReal (((largeCubeSubcubes d S.n r).card : ℝ))⁻¹ *
          ∑ _R ∈ largeCubeSubcubes d S.n r,
            ∫⁻ omega : ShellSeq d, G omega ∂P.toMeasure := by
        refine congrArg (fun t => ENNReal.ofReal
          (((largeCubeSubcubes d S.n r).card : ℝ))⁻¹ * t) ?_
        refine Finset.sum_congr rfl fun R _ => ?_
        exact (measurePreserving_translateSequence hPrefix hJ2
          (triadicCubeShift R)).lintegral_comp hGmeas
    _ = ENNReal.ofReal (((largeCubeSubcubes d S.n r).card : ℝ))⁻¹ *
          ((((largeCubeSubcubes d S.n r).card : ℕ) : ℝ≥0∞) *
            ∫⁻ omega : ShellSeq d, G omega ∂P.toMeasure) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = ∫⁻ omega : ShellSeq d, G omega ∂P.toMeasure := by
        rw [← mul_assoc, hcancel, one_mul]
    _ = ENNReal.ofReal K * ∫⁻ omega : ShellSeq d,
          (coeffCubeLinftyENorm nu S.ell S.ell omega) ^ (2 : ℕ) *
            shellDerivCubeLinftyENorm S.ell S.LPrime S.n omega ∂P.toMeasure := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun omega => ?_
        rw [hGdef]
        ring
    _ ≤ ENNReal.ofReal K *
          ((∫⁻ omega : ShellSeq d,
              (coeffCubeLinftyENorm nu S.ell S.ell omega) ^ (4 : ℕ)
            ∂P.toMeasure) ^ ((1 : ℝ) / 2) *
            (∫⁻ omega : ShellSeq d,
              (shellDerivCubeLinftyENorm S.ell S.LPrime S.n omega) ^ (2 : ℕ)
            ∂P.toMeasure) ^ ((1 : ℝ) / 2)) :=
        mul_le_mul' le_rfl (lintegral_sq_mul_le_of_measurable P.toMeasure
          hMeasCoeff hMeasDeriv)
    _ = ENNReal.ofReal K *
          ((∫⁻ omega : ShellSeq d,
              (coeffCubeLinftyENorm nu S.ell S.ell omega) ^ (4 : ℕ)
            ∂P.toMeasure) ^ ((1 : ℝ) / 2)) *
          ((∫⁻ omega : ShellSeq d,
              (shellDerivCubeLinftyENorm S.ell S.LPrime S.n omega) ^ (2 : ℕ)
            ∂P.toMeasure) ^ ((1 : ℝ) / 2)) := (mul_assoc _ _ _).symm

/-! ## `l.RHS.term1` without the localization line -/

end

end SuperdiffusionCLT.Section3.Terms
