/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.MasterIdentityResidueB
public import SuperdiffusionCLT.Section3.Terms.MaximizerCoefficientStabilityB
public import SuperdiffusionCLT.Section3.Terms.GluedFieldL2Class
public import SuperdiffusionCLT.Section3.Terms.GluedFieldEnergyObservable
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1InputsF
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1InputsG
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1AnchorsConstFirst
public import SuperdiffusionCLT.Section3.ResponseFields.RegboundsWindowB
public import SuperdiffusionCLT.Section3.ResponseFields.Norms
public import SuperdiffusionCLT.Section3.Setup.ResponseMeasurabilityB
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementLinftyLargeCube
public import SuperdiffusionCLT.Section2.Estimates.Stream.CoefficientLinftyMoments

/-!
# The three mixed-scale `hData` binders `hI1`, `hI2`, `hI3`

The three annealed integrability binders of the master identity that pair the
response gradient `∇w` against a mixed-scale field — the level-`ℓ` cutoff
coefficient against the glued field of level `L'` (`hI1`), the cutoff increment
`a_{L'} − a_ℓ` against the glued field shifted by `p` (`hI2`), and the level-`L'`
cutoff coefficient against the maximizer-gradient difference (`hI3`) — are the
`hData` conjuncts no term bound produces and that
`MasterIdentityResidueB` reduced only to its measurability engine.

This module closes them.  The single engine
`aemeasurable_volumeAverage_vecDot_grad_of_class` of `MasterIdentityResidueB.lean`
supplies the measurability of the signed cube average from the `L²(cu_m)` class
measurability of the second slot; the remaining content is the finiteness of the
annealed second cube norm of that slot, which here is read off a single
measurable envelope: the slot is dominated by the cutoff envelope `Y` times one
real constant, so its squared cube norm is dominated by `Y²` times that
constant, and the annealed integral of `Y²` is a `Γ₂` moment
(`second_moment_coeffLinftySupBound_le` for the level-`ℓ` and level-`L'`
coefficient envelopes, the `Γ₂` tail of `e.kmn.Linfty` for the increment
envelope).  The response's own second moment is
`gradW_l2_second_moment_explicit`.

## Main results

* `master_residue_hI1`, `master_residue_hI2`, `master_residue_hI3`.
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

variable {d : ℕ}

/-! ## Elementary `ℝ≥0∞` arithmetic -/

/-- The product of two nonnegative extended reals is bounded by the sum of their
squares. -/
private theorem residueC_mul_le_sq_add_sq (a b : ℝ≥0∞) :
    a * b ≤ a ^ (2 : ℕ) + b ^ (2 : ℕ) := by
  rcases le_total a b with h | h
  · calc a * b ≤ b * b := mul_le_mul' h le_rfl
      _ = b ^ (2 : ℕ) := (pow_two b).symm
      _ ≤ a ^ (2 : ℕ) + b ^ (2 : ℕ) := le_add_self
  · calc a * b ≤ a * a := mul_le_mul' le_rfl h
      _ = a ^ (2 : ℕ) := (pow_two a).symm
      _ ≤ a ^ (2 : ℕ) + b ^ (2 : ℕ) := le_self_add

/-- The square of a sum of two nonnegative extended reals is bounded by four
times the sum of the squares. -/
private theorem residueC_add_sq_le (a b : ℝ≥0∞) :
    (a + b) ^ (2 : ℕ) ≤ 4 * (a ^ (2 : ℕ) + b ^ (2 : ℕ)) := by
  have haa : a * a ≤ a ^ (2 : ℕ) + b ^ (2 : ℕ) := by
    simp only [pow_two]
    exact le_self_add (a := a * a) (b := b * b)
  have hbb : b * b ≤ a ^ (2 : ℕ) + b ^ (2 : ℕ) := by
    simp only [pow_two]
    exact le_add_self (a := b * b) (b := a * a)
  have hab : a * b ≤ a ^ (2 : ℕ) + b ^ (2 : ℕ) := residueC_mul_le_sq_add_sq a b
  have hba : b * a ≤ a ^ (2 : ℕ) + b ^ (2 : ℕ) := by
    rw [mul_comm]; exact hab
  calc (a + b) ^ (2 : ℕ) = (a + b) * (a + b) := pow_two _
    _ = (a * a + b * a) + (a * b + b * b) := by
        rw [add_mul, mul_add, mul_add]; abel
    _ ≤ ((a ^ (2 : ℕ) + b ^ (2 : ℕ)) + (a ^ (2 : ℕ) + b ^ (2 : ℕ))) +
        ((a ^ (2 : ℕ) + b ^ (2 : ℕ)) + (a ^ (2 : ℕ) + b ^ (2 : ℕ))) :=
        add_le_add (add_le_add haa hba) (add_le_add hab hbb)
    _ = 4 * (a ^ (2 : ℕ) + b ^ (2 : ℕ)) := by ring

/-! ## The integrability engine -/

/-- **The cube average of the pairing of the response gradient against an
annealed-`L²` field is integrable in the sample**, from the `L²(cu_m)` class
measurability of the second slot and the finiteness of the two annealed squared
cube norms.

Measurability is the engine `aemeasurable_volumeAverage_vecDot_grad_of_class`.
Finiteness is Cauchy–Schwarz on the cube (`abs_volumeAverage_vecDot_le_mul`),
the pointwise bound `a · b ≤ a² + b²` on `ℝ≥0∞`, and the two annealed squared
cube norms. -/
private theorem master_residue_integrable_pairing [NeZero d]
    {LPrime ellPrime m : ℕ} {p : Vec d}
    {P : ProbabilityMeasure (ShellSeq d)}
    {w : ShellSeq d → H10Function (openCubeSet (originCube d (m : ℤ)))}
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega LPrime ellPrime m p (w omega))
    {Vfield : ShellSeq d → Vec d → Vec d}
    (hVmem : ∀ omega : ShellSeq d,
      MemVectorL2 (openCubeSet (originCube d (m : ℤ))) (Vfield omega))
    (hVclass : AEMeasurable (fun omega : ShellSeq d =>
      toHilbertVectorL2OfVecField (hVmem omega)) P.toMeasure)
    (hfinV : (∫⁻ omega : ShellSeq d,
      vecCubeLpENorm (originCube d (m : ℤ)) 2 (Vfield omega) ^ (2 : ℕ)
        ∂P.toMeasure) ≠ ⊤)
    (hfinG : (∫⁻ omega : ShellSeq d,
      vecCubeLpENorm (originCube d (m : ℤ)) 2
        ((w omega).toH1Function.grad) ^ (2 : ℕ) ∂P.toMeasure) ≠ ⊤) :
    Integrable (fun omega : ShellSeq d =>
      volumeAverage (openCubeSet (originCube d (m : ℤ)))
        (fun x => vecDot ((w omega).toH1Function.grad x) (Vfield omega x)))
      P.toMeasure := by
  classical
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  have hcs : ∀ omega : ShellSeq d,
      |volumeAverage (openCubeSet (originCube d (m : ℤ)))
        (fun x => vecDot ((w omega).toH1Function.grad x) (Vfield omega x))| ≤
        (vecCubeLpENorm (originCube d (m : ℤ)) 2
            ((w omega).toH1Function.grad)).toReal *
          (vecCubeLpENorm (originCube d (m : ℤ)) 2 (Vfield omega)).toReal := by
    intro omega
    rw [← volumeAverage_cubeSet_eq_openCubeSet]
    exact SuperdiffusionCLT.Section2.Norms.abs_volumeAverage_vecDot_le_mul
      (memLp_hilbertifyVecField_of_memVectorL2
        (w omega).toH1Function.grad_memVectorL2)
      (memLp_hilbertifyVecField_of_memVectorL2 (hVmem omega))
  have hbound : ∀ omega : ShellSeq d,
      ‖volumeAverage (openCubeSet (originCube d (m : ℤ)))
        (fun x => vecDot ((w omega).toH1Function.grad x) (Vfield omega x))‖ₑ ≤
        vecCubeLpENorm (originCube d (m : ℤ)) 2
            ((w omega).toH1Function.grad) ^ (2 : ℕ) +
          vecCubeLpENorm (originCube d (m : ℤ)) 2 (Vfield omega) ^ (2 : ℕ) := by
    intro omega
    have h0 : ‖volumeAverage (openCubeSet (originCube d (m : ℤ)))
        (fun x => vecDot ((w omega).toH1Function.grad x) (Vfield omega x))‖ₑ =
        ENNReal.ofReal |volumeAverage (openCubeSet (originCube d (m : ℤ)))
          (fun x => vecDot ((w omega).toH1Function.grad x) (Vfield omega x))| :=
      Real.enorm_eq_ofReal_abs _
    have h1 := hcs omega
    have hxf : vecCubeLpENorm (originCube d (m : ℤ)) 2
        ((w omega).toH1Function.grad) ≠ ⊤ :=
      (memLp_hilbertifyVecField_of_memVectorL2
        (w omega).toH1Function.grad_memVectorL2).eLpNorm_lt_top.ne
    have hyf : vecCubeLpENorm (originCube d (m : ℤ)) 2 (Vfield omega) ≠ ⊤ :=
      (memLp_hilbertifyVecField_of_memVectorL2 (hVmem omega)).eLpNorm_lt_top.ne
    have h2 : ENNReal.ofReal ((vecCubeLpENorm (originCube d (m : ℤ)) 2
          ((w omega).toH1Function.grad)).toReal *
        (vecCubeLpENorm (originCube d (m : ℤ)) 2 (Vfield omega)).toReal) =
        vecCubeLpENorm (originCube d (m : ℤ)) 2 ((w omega).toH1Function.grad) *
          vecCubeLpENorm (originCube d (m : ℤ)) 2 (Vfield omega) := by
      rw [ENNReal.ofReal_mul (vecCubeLpENorm _ 2 _).toReal_nonneg,
        ENNReal.ofReal_toReal hxf, ENNReal.ofReal_toReal hyf]
    refine le_trans (le_trans (le_of_eq h0) ?_) (residueC_mul_le_sq_add_sq _ _)
    refine le_trans (ENNReal.ofReal_le_ofReal h1) ?_
    rw [h2]
  have hmeas : AEMeasurable (fun omega : ShellSeq d =>
      volumeAverage (openCubeSet (originCube d (m : ℤ)))
        (fun x => vecDot ((w omega).toH1Function.grad x) (Vfield omega x)))
      P.toMeasure :=
    aemeasurable_volumeAverage_vecDot_grad_of_class hw hVmem hVclass
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_def]
  refine lt_of_le_of_lt (lintegral_mono hbound) ?_
  have hGN : (∫⁻ omega : ShellSeq d,
      vecCubeLpENorm (originCube d (m : ℤ)) 2
        ((w omega).toH1Function.grad) ^ (2 : ℕ) ∂P.toMeasure) < ⊤ :=
    lt_of_le_of_ne le_top hfinG
  have hGNm : AEMeasurable (fun omega : ShellSeq d =>
      vecCubeLpENorm (originCube d (m : ℤ)) 2
        ((w omega).toH1Function.grad) ^ (2 : ℕ)) P.toMeasure :=
    (aemeasurable_vecCubeLpENorm_grad (m := m) (p := p) hw).pow_const 2
  rw [lintegral_add_left' hGNm]
  exact ENNReal.add_lt_top.2 ⟨hGN, lt_of_le_of_ne le_top hfinV⟩

/-! ## `hI1`: the level-`ℓ` coefficient against the level-`L'` glued field -/

/-- **`hI1`, the first annealed integrability condition of the master identity
display**: the sample
integrability of the cube average of the pairing of the response gradient `∇w`
with `a_ℓ(∇u_n) − q`, the level-`ℓ` cutoff coefficient applied to the
*level-`L'`* glued field.

The carrier is carried in the pinned shape of the root's data,
`uNGlued = ∇u_n = gluedGradientField ν L' n m (fluxSlot ν L' P n seed)`, the
`uNGlued` conjunct of `hData`.  Measurability of the `L²(cu_m)` class of the
pairing field is the multiplication map on classes (`measurable_matFieldMulClass_family`,
fed by the level-`L'` glued class `measurable_gluedGradientClass`) — this is the
*only* place where the two levels differ from the pairing-field
identities, which pair a coefficient and a glued field at a single level.
Finiteness is read from two uniform envelopes: the glued field's squared cube
norm is bounded on every sample by `ν⁻² |σ_{L'}(cu_n)|²`
(`vecCubeLpENorm_two_sq_gluedGradientField_le`), and the level-ℓ coefficient
envelope carries the second `L^∞` moment
(`second_moment_coeffLinftySupBound_le`, which needs `ℓ ≤ m`). -/
theorem master_residue_hI1 {d : ℕ} [NeZero d] (hd : 2 ≤ d) (nu : ℝ) (hnu : 0 < nu)
    (hnu1 : nu ≤ 1) (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P) (hJ1V2 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (hSorder : ScalesOrdering S)
    (ee : Vec d) (he : vecNormSq ee = 1) (p : Vec d)
    (hp : p = testVector nu S.LPrime P S.n ee) (q : Vec d)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (uNGlued : ShellSeq d → Vec d → Vec d)
    (huN : uNGlued = gluedGradientField hnu S.LPrime S.n S.m
      (fluxSlot nu S.LPrime P S.n ee))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m p (w omega)) :
    Integrable (fun omega : ShellSeq d =>
      volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => vecDot ((w omega).toH1Function.grad x)
          (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
            (uNGlued omega x) - q))) P.toMeasure := by
  rw [huN]
  have hn_le_m : S.n ≤ S.m := (ScalesOrdering.mem_pigeon_range hSorder).1.2
  have he_le_m : S.ell ≤ S.m := (ScalesOrdering.mem_pigeon_range hSorder).2.1.2
  have hVmem : ∀ omega : ShellSeq d,
      MemVectorL2 (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
          (gluedGradientField hnu S.LPrime S.n S.m (fluxSlot nu S.LPrime P S.n ee)
            omega x) - q) :=
    fun omega => (memVectorL2_matVecMul_coefficientCutoff hnu omega S.ell
        (originCube d (S.m : ℤ))
        (memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.n S.m
          (fluxSlot nu S.LPrime P S.n ee) omega (originCube d (S.m : ℤ)))).sub
      (memVectorL2_const q)
  have hVclass : AEMeasurable (fun omega : ShellSeq d =>
      toHilbertVectorL2OfVecField (hVmem omega)) P.toMeasure := by
    have hgluedClass : AEMeasurable (fun omega : ShellSeq d =>
        toHilbertVectorL2OfVecField
          (memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.n S.m
            (fluxSlot nu S.LPrime P S.n ee) omega (originCube d (S.m : ℤ))))
        P.toMeasure :=
      (measurable_gluedGradientClass hnu S.LPrime S.n S.m
        (fluxSlot nu S.LPrime P S.n ee)).aemeasurable
    have hbd : ∀ omega : ShellSeq d, ∃ C : ℝ, 0 ≤ C ∧
        ∀ x ∈ openCubeSet (originCube d (S.m : ℤ)), ∀ v : Vec d,
          vecNormSq (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x) v) ≤
            C ^ 2 * vecNormSq v :=
      fun omega => exists_matVecMul_bound_openCubeSet (originCube d (S.m : ℤ))
        (fun i j => continuous_coefficientCutoff_entry nu omega S.ell i j)
    have hmain := measurable_matFieldMulClass_family
      (measurableSet_openCubeSet (originCube d (S.m : ℤ)))
      (fun omega x => (coefficientCutoff nu omega S.ell).toCoeffField x)
      (measurable_prod_coefficientCutoff nu S.ell)
      (fun omega _ hf => memVectorL2_matVecMul_coefficientCutoff hnu omega S.ell
        (originCube d (S.m : ℤ)) hf) hbd hgluedClass
    have hfun : (fun omega : ShellSeq d => toHilbertVectorL2OfVecField (hVmem omega)) =
        fun omega : ShellSeq d =>
          matFieldMulClass
              (fun x : Vec d => (coefficientCutoff nu omega S.ell).toCoeffField x)
              (fun _ hf => memVectorL2_matVecMul_coefficientCutoff hnu omega S.ell
                (originCube d (S.m : ℤ)) hf)
              (toHilbertVectorL2OfVecField
                (memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.n S.m
                  (fluxSlot nu S.LPrime P S.n ee) omega (originCube d (S.m : ℤ)))) -
            toHilbertVectorL2OfVecField (memVectorL2_const q) := by
      funext omega
      rw [matFieldMulClass_toHilbertVectorL2OfVecField _ _
        (memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.n S.m
          (fluxSlot nu S.LPrime P S.n ee) omega (originCube d (S.m : ℤ))),
        ← toHilbertVectorL2OfVecField_sub
          (memVectorL2_matVecMul_coefficientCutoff hnu omega S.ell
            (originCube d (S.m : ℤ))
            (memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.n S.m
              (fluxSlot nu S.LPrime P S.n ee) omega (originCube d (S.m : ℤ))))
          (memVectorL2_const q)]
    rw [hfun]
    have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
    exact continuous_sub.measurable.comp_aemeasurable
      (hmain.prodMk (measurable_const :
        Measurable (fun _ : ShellSeq d =>
          toHilbertVectorL2OfVecField (memVectorL2_const q))).aemeasurable)
  have hfinV : (∫⁻ omega : ShellSeq d,
      vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
          (gluedGradientField hnu S.LPrime S.n S.m (fluxSlot nu S.LPrime P S.n ee)
            omega x) - q) ^ (2 : ℕ) ∂P.toMeasure) ≠ ⊤ := by
    have hXt : Measurable (fun omega : ShellSeq d =>
        (ENNReal.ofReal (coeffLinftySupBound nu S.ell S.m omega)) ^ (2 : ℕ)) :=
      (ENNReal.measurable_ofReal.comp
        (measurable_coeffLinftySupBound nu S.ell S.m)).pow_const 2
    have hXm : AEMeasurable (fun omega : ShellSeq d =>
        ENNReal.ofReal (nu⁻¹ * nu⁻¹ * vecNormSq (fluxSlot nu S.LPrime P S.n ee)) *
          (ENNReal.ofReal (coeffLinftySupBound nu S.ell S.m omega)) ^ (2 : ℕ))
        P.toMeasure := (hXt.const_mul _).aemeasurable
    have hIntc : (∫⁻ omega : ShellSeq d,
        (ENNReal.ofReal (coeffLinftySupBound nu S.ell S.m omega)) ^ (2 : ℕ)
          ∂P.toMeasure) ≤ ENNReal.ofReal (coeffCubeLinftySecondMomentConst d *
            ((1 + (S.ell : ℝ)) * (1 + (S.m : ℝ)))) :=
      second_moment_coeffLinftySupBound_le hPrefix hJ2 hJ3 hJ4 (le_of_lt hnu) hnu1 he_le_m
    have hptw : ∀ omega : ShellSeq d,
        vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
            (gluedGradientField hnu S.LPrime S.n S.m (fluxSlot nu S.LPrime P S.n ee)
              omega x) - q) ^ (2 : ℕ) ≤
        (4 : ℝ≥0∞) * (ENNReal.ofReal (nu⁻¹ * nu⁻¹ * vecNormSq (fluxSlot nu S.LPrime P S.n ee)) *
            (ENNReal.ofReal (coeffLinftySupBound nu S.ell S.m omega)) ^ (2 : ℕ) +
          (ENNReal.ofReal (vecNorm q)) ^ (2 : ℕ)) := by
      intro omega
      have hmemG := memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.n S.m
        (fluxSlot nu S.LPrime P S.n ee) omega (originCube d (S.m : ℤ))
      have hmemAG := memVectorL2_matVecMul_coefficientCutoff hnu omega S.ell
        (originCube d (S.m : ℤ)) hmemG
      have htri : vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
              (gluedGradientField hnu S.LPrime S.n S.m (fluxSlot nu S.LPrime P S.n ee)
                omega x) - q) ≤
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2
              (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
                (gluedGradientField hnu S.LPrime S.n S.m (fluxSlot nu S.LPrime P S.n ee)
                  omega x)) +
            vecCubeLpENorm (originCube d (S.m : ℤ)) 2 (fun _ : Vec d => -q) := by
        have h := vecCubeLpENorm_add_le (Q := originCube d (S.m : ℤ)) (q := (2 : ℝ≥0∞))
          (F := fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
            (gluedGradientField hnu S.LPrime S.n S.m (fluxSlot nu S.LPrime P S.n ee)
              omega x)) (G := fun _ : Vec d => -q) (by norm_num)
          (memLp_hilbertifyVecField_of_memVectorL2 hmemAG).aestronglyMeasurable
          (memLp_hilbertifyVecField_of_memVectorL2
            (memVectorL2_const (-q))).aestronglyMeasurable
        simpa only [Pi.sub_apply, Pi.add_apply, sub_eq_add_neg] using h
      have hCq : vecCubeLpENorm (originCube d (S.m : ℤ)) 2 (fun _ : Vec d => -q) =
          ENNReal.ofReal (vecNorm q) := by
        rw [vecCubeLpENorm_const (originCube d (S.m : ℤ)) (by norm_num) (-q),
          ← HilbertVec.ofVecL_apply (-q), map_neg (HilbertVec.ofVecL d) q, enorm_neg,
          HilbertVec.ofVecL_apply q, ← ofReal_norm, ← vecNorm_eq_norm_ofVec]
      have hmul := vecCubeLpENorm_matVecMul_le (Q := originCube d (S.m : ℤ)) 2
        (fun x => (coefficientCutoff nu omega S.ell).toCoeffField x)
        (gluedGradientField hnu S.LPrime S.n S.m (fluxSlot nu S.LPrime P S.n ee) omega)
        (coeffLinftySupBound_nonneg nu (le_of_lt hnu) S.ell S.m omega)
        (memLp_hilbertifyVecField_of_memVectorL2 hmemAG).aestronglyMeasurable
        (ae_matrixOperatorNorm_coefficientCutoff_le (le_of_lt hnu) omega S.ell S.m)
      have hg2 := vecCubeLpENorm_two_sq_gluedGradientField_le hnu hn_le_m le_rfl
        S.LPrime (fluxSlot nu S.LPrime P S.n ee) omega
      have hA2 : (vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
              (gluedGradientField hnu S.LPrime S.n S.m (fluxSlot nu S.LPrime P S.n ee)
                omega x))) ^ (2 : ℕ) ≤
          ENNReal.ofReal (nu⁻¹ * nu⁻¹ * vecNormSq (fluxSlot nu S.LPrime P S.n ee)) *
            (ENNReal.ofReal (coeffLinftySupBound nu S.ell S.m omega)) ^ (2 : ℕ) := by
        refine le_trans (pow_le_pow_left' hmul 2) ?_
        rw [mul_pow]
        exact le_trans (mul_le_mul' le_rfl hg2) (le_of_eq (mul_comm _ _))
      refine le_trans (pow_le_pow_left'
        (le_trans htri (add_le_add le_rfl (le_of_eq hCq))) 2) ?_
      refine le_trans (residueC_add_sq_le _ _) ?_
      exact mul_le_mul' le_rfl (add_le_add hA2 le_rfl)
    have hsplit : (∫⁻ omega : ShellSeq d,
        ENNReal.ofReal (nu⁻¹ * nu⁻¹ * vecNormSq (fluxSlot nu S.LPrime P S.n ee)) *
            (ENNReal.ofReal (coeffLinftySupBound nu S.ell S.m omega)) ^ (2 : ℕ) +
          (ENNReal.ofReal (vecNorm q)) ^ (2 : ℕ) ∂P.toMeasure) =
        ENNReal.ofReal (nu⁻¹ * nu⁻¹ * vecNormSq (fluxSlot nu S.LPrime P S.n ee)) *
            (∫⁻ omega : ShellSeq d,
              (ENNReal.ofReal (coeffLinftySupBound nu S.ell S.m omega)) ^ (2 : ℕ)
                ∂P.toMeasure) +
          (ENNReal.ofReal (vecNorm q)) ^ (2 : ℕ) := by
      rw [lintegral_add_left' hXm, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const, MeasureTheory.measure_univ, mul_one]
    have hlt : (∫⁻ omega : ShellSeq d,
        vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
            (gluedGradientField hnu S.LPrime S.n S.m (fluxSlot nu S.LPrime P S.n ee)
              omega x) - q) ^ (2 : ℕ) ∂P.toMeasure) < ⊤ := by
      refine lt_of_le_of_lt (lintegral_mono hptw) ?_
      rw [lintegral_const_mul' _ _ (by norm_num : (4 : ℝ≥0∞) ≠ ⊤), hsplit]
      refine ENNReal.mul_lt_top (by norm_num) ?_
      refine ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_,
        ENNReal.pow_lt_top ENNReal.ofReal_lt_top⟩
      exact lt_of_le_of_lt hIntc ENNReal.ofReal_lt_top
    exact hlt.ne
  have hfinG : (∫⁻ omega : ShellSeq d,
      vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        ((w omega).toH1Function.grad) ^ (2 : ℕ) ∂P.toMeasure) ≠ ⊤ := by
    obtain ⟨Creg, hCreg, hregw⟩ := l_w_basic_regbounds_window d hd
    have hregA := hregw nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder ee he p hp
      w hw
    have hsecond := gradW_l2_second_moment_explicit hnu hPrefix hJ2 hJ3 hJ4 S hSorder
      ee he p hp w Creg hCreg hregA.1
    exact (lt_of_le_of_lt hsecond ENNReal.ofReal_lt_top).ne
  exact master_residue_integrable_pairing hw hVmem hVclass hfinV hfinG

end

end SuperdiffusionCLT.Section3.Setup
