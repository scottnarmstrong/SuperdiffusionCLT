/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm2MeasurabilityB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2AnchorsConstFirst
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2Decoupling
public import SuperdiffusionCLT.Section3.Terms.GluedFieldL2Class
public import SuperdiffusionCLT.Section3.Terms.MaximizerCoefficientStabilityB
public import SuperdiffusionCLT.Section3.Setup.MasterIdentityAssembly
public import SuperdiffusionCLT.Section2.Norms.NegativeNormPairing
public import SuperdiffusionCLT.Section3.Terms.MasterIdentity
public import SuperdiffusionCLT.Section3.Terms.GluedFieldAnnealedFiniteness
public import SuperdiffusionCLT.Section3.Terms.GluedFieldDifferenceMeasurable

/-!
# `l.RHS.term2`: the three annealed pairing integrals

The statement `SuperdiffusionCLT.Frozen.Section3.rhs_term2` needs, among other
ingredients, the integrability in the sample of the three summands into which the
paper's proof splits the display.  This module proves it.

## The route

Each summand is the cube average of the pairing of the response flux
`R = (k_{L'} − k_ℓ)ᵗ ∇w` with one of the three proxy fields.  The first two are
discharged by Cauchy–Schwarz and AM–GM: the cube average of a pairing of two
`L²(cu_m)` fields is the inner product of their classes
(`volumeAverage_vecDot_eq_inner`), so it is a measurable observable; the
Cauchy–Schwarz bound on the cube (`abs_volumeAverage_vecDot_le_mul`) and the
pointwise inequality `a · b ≤ a² + b²` on `ℝ≥0∞` bound its `enorm` by the sum of
the two annealed squared cube norms, whose integrals are finite by
the finiteness of the annealed norm of `R` and of the proxy fields.  The third summand has a
constant second slot, so the cube
average is `vecDot (⨍ R) (p̃ − p)`, a finite sum of coordinates of the cube mean
of `R`; the coordinates are integrable by Jensen on the large cube itself
(`ofReal_vecNormSq_volumeAverageVec_le` applies on every cube, not only on the
scale-`n` sub-cubes).

## Measurability at the large cube

The field half of the printed measurability sentence
(`measurable_volumeAverageVec_matVecMul_coefficientCutoff_sub_grad_highShellSigma`)
is stated on the scale-`n` sub-cubes of `cu_m`, which are not the large cube
itself.  The underlying composition
(`measurable_volumeAverageVec_matVecMul_grad_dirichletResponse_comp`) is stated
for an arbitrary measurable `V ⊆ openCubeSet (originCube d (m : ℤ))`, so the
same two steps, with `V = openCubeSet (originCube d (m : ℤ))`, give the cube
mean of `R` at the large cube
(`measurable_volumeAverageVec_coefficientCutoff_sub_grad_cube` below).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section2.Estimates.Stream
open Homogenization
open Homogenization.Book.Ch02
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Small arithmetic helpers -/

private theorem le_one_add_sq (a : ℝ≥0∞) : a ≤ 1 + a ^ (2 : ℕ) := by
  rcases le_total a 1 with h | h
  · exact le_trans h le_self_add
  · calc a = a * 1 := (mul_one a).symm
      _ ≤ a * a := mul_le_mul' le_rfl h
      _ = a ^ (2 : ℕ) := (pow_two a).symm
      _ ≤ 1 + a ^ (2 : ℕ) := le_add_self

private theorem mul_le_sq_add_sq_ennreal (a b : ℝ≥0∞) :
    a * b ≤ a ^ (2 : ℕ) + b ^ (2 : ℕ) := by
  rcases le_total a b with h | h
  · calc a * b ≤ b * b := mul_le_mul' h le_rfl
      _ = b ^ (2 : ℕ) := (pow_two b).symm
      _ ≤ a ^ (2 : ℕ) + b ^ (2 : ℕ) := le_add_self
  · calc a * b ≤ a * a := mul_le_mul' le_rfl h
      _ = a ^ (2 : ℕ) := (pow_two a).symm
      _ ≤ a ^ (2 : ℕ) + b ^ (2 : ℕ) := le_self_add

/-- The cube average reads the open and the half-open realization of a triadic
cube alike. -/
private theorem volumeAverage_openCubeSet_eq_cubeSet (Q : TriadicCube d)
    {f : Vec d → ℝ} :
    volumeAverage (openCubeSet Q) f = volumeAverage (cubeSet Q) f := by
  simp only [volumeAverage, volume_openCubeSet_eq_volume_cubeSet]
  rw [MeasureTheory.setIntegral_congr_set (Homogenization.cubeSet_ae_eq_openCubeSet Q)]

/-! ## Measurability and integrability of the cube mean at the large cube -/

/-- **The cube mean of the response flux at the large cube is measurable in the
sample.**  This is the measurability of
`measurable_volumeAverageVec_matVecMul_coefficientCutoff_sub_grad_highShellSigma`
lifted from the scale-`n` sub-cubes to the large cube `cu_m` itself: the
underlying composition is stated for an arbitrary measurable `V` inside
`openCubeSet (originCube d (m : ℤ))`, and the large cube is one, so the two-step
route of that theorem runs verbatim with `V = cu_m`; the `σ`-field
`F_> = σ(j_r : r > ℓ)` is coarser than the ambient one (`highShellSigma_le`). -/
private theorem measurable_volumeAverageVec_coefficientCutoff_sub_grad_cube
    [NeZero d] (nu : ℝ) {ell ellPrime LPrime m : ℕ} (hell : ell ≤ ellPrime)
    (hlL : ellPrime ≤ LPrime)
    {p : Vec d} {w : ShellSeq d → H10Function (openCubeSet (originCube d (m : ℤ)))}
    (hw : ∀ omega : ShellSeq d, IsDirichletResponse omega LPrime ellPrime m p (w omega)) :
    Measurable (fun omega : ShellSeq d =>
      volumeAverageVec (openCubeSet (originCube d (m : ℤ)))
        (fun y => matVecMul ((coefficientCutoff nu omega LPrime).toCoeffField y -
            (coefficientCutoff nu omega ell).toCoeffField y)
          ((w omega).toH1Function.grad y))) := by
  have hVU : openCubeSet (originCube d (m : ℤ)) ⊆
      openCubeSet (originCube d (m : ℤ)) := le_rfl
  have hint := measurable_volumeAverageVec_matVecMul_grad_dirichletResponse_comp
    (mAlpha := Terms.highShellSigma d ell) (fun omega : ShellSeq d => omega)
    (fun omega y => (coefficientCutoff nu omega LPrime).toCoeffField y -
      (coefficientCutoff nu omega ell).toCoeffField y)
    (fun omega i j => continuous_coefficientCutoff_sub_entry nu omega LPrime ell i j)
    (fun y i j => measurable_coefficientCutoff_sub_entry_highShellSigma nu
      (le_trans hell hlL) y i j)
    LPrime ellPrime m p hVU (isOpen_openCubeSet (originCube d (m : ℤ))).measurableSet
    (fun x => measurable_dirichletRhsField_apply_highShellSigma hell hlL p x)
  have hcan := measurable_volumeAverageVec_matVecMul_grad_of_canonical hVU
    (fun omega y => (coefficientCutoff nu omega LPrime).toCoeffField y -
      (coefficientCutoff nu omega ell).toCoeffField y) hw hint
  exact hcan.mono (highShellSigma_le d ell) le_rfl

/-- **The coordinates of the cube mean of an annealed-`L²` field are integrable
in the sample, at an arbitrary cube.**  The bound is Jensen on the cube itself
(`ofReal_vecNormSq_volumeAverageVec_le` holds on every cube), so no sub-cube
membership enters; this is the large-cube companion of
`integrable_volumeAverageVec_apply`. -/
private theorem integrable_volumeAverageVec_apply_cube {P : ProbabilityMeasure (ShellSeq d)}
    {Q : TriadicCube d} {Rf : ShellSeq d → Vec d → Vec d}
    (hRL2 : ∀ omega : ShellSeq d, MemVectorL2 (openCubeSet Q) (Rf omega))
    (hfin : (∫⁻ omega : ShellSeq d,
      vecCubeLpENorm Q 2 (Rf omega) ^ (2 : ℕ) ∂P.toMeasure) ≠ ⊤)
    (hmeas : Measurable (fun omega : ShellSeq d =>
      volumeAverageVec (openCubeSet Q) (Rf omega)))
    (i : Fin d) :
    Integrable
      (fun omega : ShellSeq d => volumeAverageVec (openCubeSet Q) (Rf omega) i)
      P.toMeasure := by
  classical
  have hbound : ∀ omega : ShellSeq d,
      ‖volumeAverageVec (openCubeSet Q) (Rf omega) i‖ₑ ≤
        1 + vecCubeLpENorm Q 2 (Rf omega) ^ (2 : ℕ) := by
    intro omega
    set v : Vec d := volumeAverageVec (openCubeSet Q) (Rf omega) with hv
    have hsq : ‖v i‖ₑ ^ (2 : ℕ) ≤ ENNReal.ofReal (vecNormSq v) := by
      have hle : |v i| ≤ vecNorm v := abs_apply_le_vecNorm v i
      calc ‖v i‖ₑ ^ (2 : ℕ) = ENNReal.ofReal (|v i|) ^ (2 : ℕ) := by
            rw [← ofReal_norm, Real.norm_eq_abs]
        _ = ENNReal.ofReal (|v i| ^ (2 : ℕ)) :=
            (ENNReal.ofReal_pow (abs_nonneg _) 2).symm
        _ ≤ ENNReal.ofReal (vecNorm v ^ (2 : ℕ)) :=
            ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (abs_nonneg _) hle 2)
        _ = ENNReal.ofReal (vecNormSq v) := by
            rw [Homogenization.Book.Ch02.vecNorm_sq_eq_vecNormSq]
    have hjen : ENNReal.ofReal (vecNormSq v) ≤
        vecCubeLpENorm Q 2 (Rf omega) ^ (2 : ℕ) :=
      ofReal_vecNormSq_volumeAverageVec_le (hRL2 omega)
    exact le_trans (le_one_add_sq _) (add_le_add le_rfl (le_trans hsq hjen))
  refine ⟨((measurable_pi_apply i).comp hmeas).aestronglyMeasurable, ?_⟩
  have hmono : (∫⁻ omega : ShellSeq d,
        ‖volumeAverageVec (openCubeSet Q) (Rf omega) i‖ₑ ∂P.toMeasure) ≤
      ∫⁻ omega : ShellSeq d,
        (1 + vecCubeLpENorm Q 2 (Rf omega) ^ (2 : ℕ)) ∂P.toMeasure := lintegral_mono hbound
  have hsplit : (∫⁻ omega : ShellSeq d,
        (1 + vecCubeLpENorm Q 2 (Rf omega) ^ (2 : ℕ)) ∂P.toMeasure) =
      1 + ∫⁻ omega : ShellSeq d, vecCubeLpENorm Q 2 (Rf omega) ^ (2 : ℕ)
        ∂P.toMeasure := by
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
  refine lt_of_le_of_lt hmono ?_
  rw [hsplit]
  exact ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, lt_of_le_of_ne le_top hfin⟩

/-! ## The pairing summands -/

/-- **The cube average of the pairing of two annealed-`L²` fields is
integrable in the sample.**  Measurability comes from the inner product of the
two `L²` classes (`volumeAverage_vecDot_eq_inner`), the bound from
Cauchy–Schwarz on the cube (`abs_volumeAverage_vecDot_le_mul`) and the pointwise
inequality `a · b ≤ a² + b²` on `ℝ≥0∞`; finiteness is the two annealed squared
cube norms. -/
private theorem integrable_volumeAverage_pairing {P : ProbabilityMeasure (ShellSeq d)}
    {Q : TriadicCube d} {Rf gf : ShellSeq d → Vec d → Vec d}
    (hRL2 : ∀ omega : ShellSeq d, MemVectorL2 (openCubeSet Q) (Rf omega))
    (hRclass : AEMeasurable (fun omega : ShellSeq d =>
      toHilbertVectorL2OfVecField (hRL2 omega)) P.toMeasure)
    (hGL2 : ∀ omega : ShellSeq d, MemVectorL2 (openCubeSet Q) (gf omega))
    (hGclass : AEMeasurable (fun omega : ShellSeq d =>
      toHilbertVectorL2OfVecField (hGL2 omega)) P.toMeasure)
    (hRmeas : AEMeasurable (fun omega : ShellSeq d =>
      vecCubeLpENorm Q 2 (Rf omega)) P.toMeasure)
    (hfinR : (∫⁻ omega : ShellSeq d,
      vecCubeLpENorm Q 2 (Rf omega) ^ (2 : ℕ) ∂P.toMeasure) ≠ ⊤)
    (hfinG : (∫⁻ omega : ShellSeq d,
      vecCubeLpENorm Q 2 (gf omega) ^ (2 : ℕ) ∂P.toMeasure) ≠ ⊤) :
    Integrable (fun omega : ShellSeq d =>
      volumeAverage (openCubeSet Q) (fun y => vecDot (Rf omega y) (gf omega y)))
      P.toMeasure := by
  classical
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  have hcs : ∀ omega : ShellSeq d,
      |volumeAverage (openCubeSet Q) (fun y => vecDot (Rf omega y) (gf omega y))| ≤
        (vecCubeLpENorm Q 2 (Rf omega)).toReal *
          (vecCubeLpENorm Q 2 (gf omega)).toReal := by
    intro omega
    rw [volumeAverage_openCubeSet_eq_cubeSet]
    exact SuperdiffusionCLT.Section2.Norms.abs_volumeAverage_vecDot_le_mul
      (SuperdiffusionCLT.Section2.Norms.memLp_hilbertifyVecField_of_memVectorL2
        (hRL2 omega))
      (SuperdiffusionCLT.Section2.Norms.memLp_hilbertifyVecField_of_memVectorL2
        (hGL2 omega))
  have hbound : ∀ omega : ShellSeq d,
      ‖volumeAverage (openCubeSet Q) (fun y => vecDot (Rf omega y) (gf omega y))‖ₑ ≤
        vecCubeLpENorm Q 2 (Rf omega) ^ (2 : ℕ) +
          vecCubeLpENorm Q 2 (gf omega) ^ (2 : ℕ) := by
    intro omega
    have h0 : ‖volumeAverage (openCubeSet Q)
        (fun y => vecDot (Rf omega y) (gf omega y))‖ₑ =
        ENNReal.ofReal |volumeAverage (openCubeSet Q)
          (fun y => vecDot (Rf omega y) (gf omega y))| := by
      rw [← ofReal_norm, Real.norm_eq_abs]
    have h1 := hcs omega
    have hxf : vecCubeLpENorm Q 2 (Rf omega) ≠ ⊤ :=
      (SuperdiffusionCLT.Section2.Norms.memLp_hilbertifyVecField_of_memVectorL2
        (hRL2 omega)).eLpNorm_lt_top.ne
    have hyf : vecCubeLpENorm Q 2 (gf omega) ≠ ⊤ :=
      (SuperdiffusionCLT.Section2.Norms.memLp_hilbertifyVecField_of_memVectorL2
        (hGL2 omega)).eLpNorm_lt_top.ne
    have h2 : ENNReal.ofReal ((vecCubeLpENorm Q 2 (Rf omega)).toReal *
        (vecCubeLpENorm Q 2 (gf omega)).toReal) =
        vecCubeLpENorm Q 2 (Rf omega) * vecCubeLpENorm Q 2 (gf omega) := by
      rw [ENNReal.ofReal_mul (vecCubeLpENorm Q 2 (Rf omega)).toReal_nonneg,
        ENNReal.ofReal_toReal hxf, ENNReal.ofReal_toReal hyf]
    refine le_trans (le_trans (le_of_eq h0) ?_) (mul_le_sq_add_sq_ennreal _ _)
    refine le_trans (ENNReal.ofReal_le_ofReal h1) ?_
    rw [h2]
  have hmeas : AEMeasurable (fun omega : ShellSeq d =>
      volumeAverage (openCubeSet Q) (fun y => vecDot (Rf omega y) (gf omega y)))
      P.toMeasure := by
    have hfun : (fun omega : ShellSeq d =>
        volumeAverage (openCubeSet Q) (fun y => vecDot (Rf omega y) (gf omega y))) =
      fun omega : ShellSeq d => (MeasureTheory.volume (openCubeSet Q)).toReal⁻¹ *
        inner ℝ (toHilbertVectorL2OfVecField (hRL2 omega))
          (toHilbertVectorL2OfVecField (hGL2 omega)) := by
      funext omega
      exact volumeAverage_vecDot_eq_inner (hRL2 omega) (hGL2 omega)
    rw [hfun]
    exact (continuous_inner.measurable.comp_aemeasurable
      (hRclass.prodMk hGclass)).const_mul _
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_def]
  refine lt_of_le_of_lt (lintegral_mono hbound) ?_
  have hNR : (∫⁻ omega : ShellSeq d,
      vecCubeLpENorm Q 2 (Rf omega) ^ (2 : ℕ) ∂P.toMeasure) < ⊤ :=
    lt_of_le_of_ne le_top hfinR
  have hNG : (∫⁻ omega : ShellSeq d,
      vecCubeLpENorm Q 2 (gf omega) ^ (2 : ℕ) ∂P.toMeasure) < ⊤ :=
    lt_of_le_of_ne le_top hfinG
  rw [lintegral_add_left' (hRmeas.pow_const 2)]
  exact ENNReal.add_lt_top.2 ⟨hNR, hNG⟩

/-- **The cube average of the pairing of an annealed-`L²` field with a constant
vector is integrable in the sample.**  The cube average is the pairing of the
constant with the cube mean of the field (`volumeAverage_vecDot_const_right`), a
finite sum of coordinates of the cube mean times constants; the coordinates are
integrable by `integrable_volumeAverageVec_apply_cube`. -/
private theorem integrable_volumeAverage_pairing_const {P : ProbabilityMeasure (ShellSeq d)}
    {Q : TriadicCube d} {Rf : ShellSeq d → Vec d → Vec d} (c : Vec d)
    (hRL2 : ∀ omega : ShellSeq d, MemVectorL2 (openCubeSet Q) (Rf omega))
    (hmeas : Measurable (fun omega : ShellSeq d =>
      volumeAverageVec (openCubeSet Q) (Rf omega)))
    (hfin : (∫⁻ omega : ShellSeq d,
      vecCubeLpENorm Q 2 (Rf omega) ^ (2 : ℕ) ∂P.toMeasure) ≠ ⊤) :
    Integrable (fun omega : ShellSeq d =>
      volumeAverage (openCubeSet Q) (fun y => vecDot (Rf omega y) c)) P.toMeasure := by
  classical
  have hfun : (fun omega : ShellSeq d =>
      volumeAverage (openCubeSet Q) (fun y => vecDot (Rf omega y) c)) =
    fun omega : ShellSeq d => vecDot (volumeAverageVec (openCubeSet Q) (Rf omega)) c := by
    funext omega
    exact volumeAverage_vecDot_const_right c
      (fun i => integrableOn_component_of_memVectorL2 (hRL2 omega) i)
  rw [hfun]
  show Integrable (fun omega : ShellSeq d =>
    ∑ i, volumeAverageVec (openCubeSet Q) (Rf omega) i * c i) P.toMeasure
  exact MeasureTheory.integrable_finsetSum Finset.univ
    (fun i _ => (integrable_volumeAverageVec_apply_cube hRL2 hfin hmeas i).mul_const (c i))

/-! ## The third summand -/

/-- **`l.RHS.term2`, integrability of the third summand**: the pairing of the
response flux `R = (k_{L'} − k_ℓ)ᵗ ∇w` with the constant `p̃ − p` is integrable
in the sample.  The cube average is the pairing of the constant with the cube
mean of `R` (`volumeAverage_vecDot_const_right`), a finite sum of coordinates
of the cube mean of `R` times constants, and the coordinates are integrable by
`integrable_volumeAverageVec_apply_cube`.  The only carried hypothesis beyond
the statement's binders is the finiteness of the annealed squared cube
norm of `R`. -/
theorem term2_ob6_intMean [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection)
    (hS : ScalesOrdering S) (e : Vec d)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega))
    (hfinR : (∫⁻ omega : ShellSeq d,
      vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
            (coefficientCutoff nu omega S.ell).toCoeffField y)
          ((w omega).toH1Function.grad y)) ^ (2 : ℕ) ∂P.toMeasure) ≠ ⊤) :
    Integrable (fun omega : ShellSeq d =>
      volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun y => vecDot (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
              (coefficientCutoff nu omega S.ell).toCoeffField y)
            ((w omega).toH1Function.grad y))
          (annealedGluedAverage hnu P S.ell S.n S.m
              (fluxSlot nu S.LPrime P S.n e) -
            testVector nu S.LPrime P S.n e))) P.toMeasure := by
  classical
  set F : Vec d := fluxSlot nu S.LPrime P S.n e with hFdef
  have hell : S.ell ≤ S.ellPrime := le_of_lt hS.ell_lt_ellPrime
  have hlL : S.ellPrime ≤ S.LPrime := by
    have h1 := hS.ellPrime_lt_m
    have h2 := hS.m_lt_LPrime
    omega
  have hmeas := measurable_volumeAverageVec_coefficientCutoff_sub_grad_cube nu hell hlL hw
  exact integrable_volumeAverage_pairing_const
    (annealedGluedAverage hnu P S.ell S.n S.m F - testVector nu S.LPrime P S.n e)
    (fun omega => memVectorL2_matVecMul_coefficientCutoff_sub hnu omega S.LPrime S.ell
      (originCube d (S.m : ℤ)) ((w omega).toH1Function.grad_memVectorL2))
    hmeas hfinR

/-! ## The first summand -/

/-- The `L²(cu_m)` class of the response flux `R = (k_{L₁} − k_{L₂})ᵗ ∇w` is a
measurable function of the sample.  The class is the multiplication of the
weak-gradient class of the selection by the cutoff-difference coefficient
field; the gradient class of the selection equals that of the canonical
response (both are the cube Dirichlet solution operator read on the flux
class), which is measurable, and the multiplication map on classes is
Carathéodory in (class, sample). -/
private theorem aemeasurable_class_responseFlux [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L1 L2 : ℕ)
    {LPrime ellPrime m : ℕ} {p : Vec d}
    {w : ShellSeq d → H10Function (openCubeSet (originCube d (m : ℤ)))}
    (hw : ∀ omega : ShellSeq d, IsDirichletResponse omega LPrime ellPrime m p (w omega))
    {mu : MeasureTheory.Measure (ShellSeq d)} :
    AEMeasurable (fun omega : ShellSeq d => toHilbertVectorL2OfVecField
      (memVectorL2_matVecMul_coefficientCutoff_sub hnu omega L1 L2
        (originCube d (m : ℤ)) ((w omega).toH1Function.grad_memVectorL2))) mu := by
  classical
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  have hU : MeasurableSet (openCubeSet (originCube d (m : ℤ))) :=
    (isOpen_openCubeSet (originCube d (m : ℤ))).measurableSet
  -- the weak-gradient class of the selection is the canonical one, measurable
  have hgrad : Measurable (fun omega : ShellSeq d =>
      toHilbertVectorL2OfVecField ((w omega).toH1Function.grad_memVectorL2)) := by
    have hcan : Measurable (fun omega : ShellSeq d =>
        (dirichletResponse omega LPrime ellPrime m p).toH1Function.gradToHilbertVectorL2) :=
      measurable_gradToHilbertVectorL2_dirichletResponse (d := d)
    have heq : (fun omega : ShellSeq d =>
        toHilbertVectorL2OfVecField ((w omega).toH1Function.grad_memVectorL2)) =
      fun omega : ShellSeq d =>
        (dirichletResponse omega LPrime ellPrime m p).toH1Function.gradToHilbertVectorL2 := by
      funext omega
      show (w omega).toH1Function.gradToHilbertVectorL2 = _
      rw [gradToHilbertVectorL2_eq_cubeDirichletGradClass_of_isDirichletResponse omega
        (hw omega), gradToHilbertVectorL2_eq_cubeDirichletGradClass_of_isDirichletResponse
        omega (isDirichletResponse_dirichletResponse omega LPrime ellPrime m p)]
    rw [heq]
    exact hcan
  have hmul : ∀ (omega : ShellSeq d) (f : Vec d → Vec d),
      MemVectorL2 (openCubeSet (originCube d (m : ℤ))) f →
      MemVectorL2 (openCubeSet (originCube d (m : ℤ)))
        (fun x => matVecMul ((coefficientCutoff nu omega L1).toCoeffField x -
          (coefficientCutoff nu omega L2).toCoeffField x) (f x)) :=
    fun omega _ hf => memVectorL2_matVecMul_coefficientCutoff_sub hnu omega L1 L2
      (originCube d (m : ℤ)) hf
  have hbd : ∀ omega : ShellSeq d, ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ openCubeSet (originCube d (m : ℤ)), ∀ v : Vec d,
      vecNormSq (matVecMul ((coefficientCutoff nu omega L1).toCoeffField x -
        (coefficientCutoff nu omega L2).toCoeffField x) v) ≤ C ^ (2 : ℕ) * vecNormSq v :=
    fun omega => exists_matVecMul_bound_openCubeSet (originCube d (m : ℤ))
      (fun i j => continuous_coefficientCutoff_sub_entry nu omega L1 L2 i j)
  have heq : (fun omega : ShellSeq d => toHilbertVectorL2OfVecField
      (memVectorL2_matVecMul_coefficientCutoff_sub hnu omega L1 L2
        (originCube d (m : ℤ)) ((w omega).toH1Function.grad_memVectorL2))) =
    fun omega : ShellSeq d => matFieldMulClass
      (fun y => (coefficientCutoff nu omega L1).toCoeffField y -
        (coefficientCutoff nu omega L2).toCoeffField y) (hmul omega)
      (toHilbertVectorL2OfVecField ((w omega).toH1Function.grad_memVectorL2)) := by
    funext omega
    exact (matFieldMulClass_toHilbertVectorL2OfVecField
      (fun y => (coefficientCutoff nu omega L1).toCoeffField y -
        (coefficientCutoff nu omega L2).toCoeffField y) (hmul omega) _).symm
  rw [heq]
  exact measurable_matFieldMulClass_family hU
    (fun omega y => (coefficientCutoff nu omega L1).toCoeffField y -
      (coefficientCutoff nu omega L2).toCoeffField y)
    (measurable_prod_coefficientCutoff_sub nu L1 L2) hmul hbd hgrad.aemeasurable

/-! ## The second summand -/

/-- **`l.RHS.term2`, integrability of the second summand**: the pairing of the
response flux `R = (k_{L'} − k_ℓ)ᵗ ∇w` with the difference `∇ũ_n − p̃` of the
glued field at `ℓ` and its annealed average is integrable in the sample.
Cauchy–Schwarz and AM–GM on the cube bound the pairing by the sum of the two
annealed squared cube norms (`integrable_volumeAverage_pairing`), finite by
the finiteness of the annealed norms of `R` and of the proxy fields.  The class of the second
field is the difference of the
measurable glued class at `ℓ` (`measurable_gluedGradientClass`) and the
constant class of the annealed average.  The only carried hypothesis beyond the
statement's binders is the finiteness of the annealed squared cube norm
of `R`. -/
theorem term2_ob6_intProxy [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection)
    (hS : ScalesOrdering S) (e : Vec d)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega))
    (hfinR : (∫⁻ omega : ShellSeq d,
      vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
            (coefficientCutoff nu omega S.ell).toCoeffField y)
          ((w omega).toH1Function.grad y)) ^ (2 : ℕ) ∂P.toMeasure) ≠ ⊤) :
    Integrable (fun omega : ShellSeq d =>
      volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun y => vecDot (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
              (coefficientCutoff nu omega S.ell).toCoeffField y)
            ((w omega).toH1Function.grad y))
          (gluedGradientField hnu S.ell S.n S.m
              (fluxSlot nu S.LPrime P S.n e) omega y -
            annealedGluedAverage hnu P S.ell S.n S.m
              (fluxSlot nu S.LPrime P S.n e)))) P.toMeasure := by
  classical
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  set F : Vec d := fluxSlot nu S.LPrime P S.n e with hFdef
  have hRL2 : ∀ omega : ShellSeq d, MemVectorL2 (openCubeSet (originCube d (S.m : ℤ)))
      (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
          (coefficientCutoff nu omega S.ell).toCoeffField y)
        ((w omega).toH1Function.grad y)) :=
    fun omega => memVectorL2_matVecMul_coefficientCutoff_sub hnu omega S.LPrime S.ell
      (originCube d (S.m : ℤ)) ((w omega).toH1Function.grad_memVectorL2)
  have hGL2 : ∀ omega : ShellSeq d, MemVectorL2 (openCubeSet (originCube d (S.m : ℤ)))
      (fun y => gluedGradientField hnu S.ell S.n S.m F omega y -
        annealedGluedAverage hnu P S.ell S.n S.m F) :=
    fun omega => (memVectorL2_openCubeSet_gluedGradientField hnu S.ell S.n S.m F omega
      (originCube d (S.m : ℤ))).sub
      (memVectorL2_const (U := openCubeSet (originCube d (S.m : ℤ)))
        (annealedGluedAverage hnu P S.ell S.n S.m F))
  have hRclass := aemeasurable_class_responseFlux (d := d) hnu S.LPrime S.ell
    (LPrime := S.LPrime) (ellPrime := S.ellPrime) (m := S.m)
    (p := testVector nu S.LPrime P S.n e) hw (mu := P.toMeasure)
  have hGclass : AEMeasurable (fun omega : ShellSeq d =>
      toHilbertVectorL2OfVecField (hGL2 omega)) P.toMeasure := by
    have hsub : (fun omega : ShellSeq d =>
        toHilbertVectorL2OfVecField (hGL2 omega)) =
      fun omega : ShellSeq d =>
        toHilbertVectorL2OfVecField (memVectorL2_openCubeSet_gluedGradientField hnu
            S.ell S.n S.m F omega (originCube d (S.m : ℤ))) -
          toHilbertVectorL2OfVecField (memVectorL2_const
            (U := openCubeSet (originCube d (S.m : ℤ)))
            (annealedGluedAverage hnu P S.ell S.n S.m F)) := by
      funext omega
      exact toHilbertVectorL2OfVecField_sub _ _
    rw [hsub]
    have hpair : AEMeasurable (fun omega : ShellSeq d =>
        (toHilbertVectorL2OfVecField (memVectorL2_openCubeSet_gluedGradientField hnu
            S.ell S.n S.m F omega (originCube d (S.m : ℤ))),
          toHilbertVectorL2OfVecField (memVectorL2_const
            (U := openCubeSet (originCube d (S.m : ℤ)))
            (annealedGluedAverage hnu P S.ell S.n S.m F)))) P.toMeasure :=
      (measurable_gluedGradientClass hnu S.ell S.n S.m F).aemeasurable.prodMk
        (measurable_const : Measurable (fun _ : ShellSeq d =>
          toHilbertVectorL2OfVecField (memVectorL2_const
            (U := openCubeSet (originCube d (S.m : ℤ)))
            (annealedGluedAverage hnu P S.ell S.n S.m F)))).aemeasurable
    exact continuous_sub.measurable.comp_aemeasurable hpair
  have hRmeas := aemeasurable_vecCubeLpENorm_matVecMul_coefficientCutoff_sub_grad
    (d := d) hnu S.LPrime S.ell (LPrime := S.LPrime) (ellPrime := S.ellPrime) (m := S.m)
    (p := testVector nu S.LPrime P S.n e) (mu := P.toMeasure) (w := w) hw
  have hfinProxy : (∫⁻ omega : ShellSeq d,
      vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        (fun x => gluedGradientField hnu S.ell S.n S.m F omega x -
          annealedGluedAverage hnu P S.ell S.n S.m F) ^ (2 : ℕ)
      ∂P.toMeasure) ≠ ⊤ := (term2_ob4_finite hnu P S hS e).2
  exact integrable_volumeAverage_pairing hRL2 hRclass hGL2 hGclass hRmeas hfinR hfinProxy

/-- **`l.RHS.term2`, integrability of the first summand**: the pairing of the
response flux `R = (k_{L'} − k_ℓ)ᵗ ∇w` with the difference `∇u_n − ∇ũ_n` of
the two glued fields is integrable in the sample.  Cauchy–Schwarz and AM–GM on
the cube bound the pairing by the sum of the two annealed squared cube norms
(`integrable_volumeAverage_pairing`), finite by the finiteness of the annealed norms of `R`
and of the proxy fields.  The only carried hypothesis beyond the statement's binders is
the finiteness of the annealed squared cube norm of `R`. -/
theorem term2_ob6_intDiff [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection)
    (hS : ScalesOrdering S) (e : Vec d)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega))
    (hfinR : (∫⁻ omega : ShellSeq d,
      vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
            (coefficientCutoff nu omega S.ell).toCoeffField y)
          ((w omega).toH1Function.grad y)) ^ (2 : ℕ) ∂P.toMeasure) ≠ ⊤) :
    Integrable (fun omega : ShellSeq d =>
      volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun y => vecDot (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
              (coefficientCutoff nu omega S.ell).toCoeffField y)
            ((w omega).toH1Function.grad y))
          (gluedGradientField hnu S.LPrime S.n S.m
              (fluxSlot nu S.LPrime P S.n e) omega y -
            gluedGradientField hnu S.ell S.n S.m
              (fluxSlot nu S.LPrime P S.n e) omega y))) P.toMeasure := by
  classical
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  set F : Vec d := fluxSlot nu S.LPrime P S.n e with hFdef
  have hRL2 : ∀ omega : ShellSeq d, MemVectorL2 (openCubeSet (originCube d (S.m : ℤ)))
      (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
          (coefficientCutoff nu omega S.ell).toCoeffField y)
        ((w omega).toH1Function.grad y)) :=
    fun omega => memVectorL2_matVecMul_coefficientCutoff_sub hnu omega S.LPrime S.ell
      (originCube d (S.m : ℤ)) ((w omega).toH1Function.grad_memVectorL2)
  have hGL2 : ∀ omega : ShellSeq d, MemVectorL2 (openCubeSet (originCube d (S.m : ℤ)))
      (fun y => gluedGradientField hnu S.LPrime S.n S.m F omega y -
        gluedGradientField hnu S.ell S.n S.m F omega y) :=
    fun omega => (memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.n S.m F omega
      (originCube d (S.m : ℤ))).sub
      (memVectorL2_openCubeSet_gluedGradientField hnu S.ell S.n S.m F omega
        (originCube d (S.m : ℤ)))
  have hRclass := aemeasurable_class_responseFlux (d := d) hnu S.LPrime S.ell
    (LPrime := S.LPrime) (ellPrime := S.ellPrime) (m := S.m)
    (p := testVector nu S.LPrime P S.n e) hw (mu := P.toMeasure)
  have hGclass : AEMeasurable (fun omega : ShellSeq d =>
      toHilbertVectorL2OfVecField (hGL2 omega)) P.toMeasure := by
    have hsub : (fun omega : ShellSeq d =>
        toHilbertVectorL2OfVecField (hGL2 omega)) =
      fun omega : ShellSeq d =>
        toHilbertVectorL2OfVecField (memVectorL2_openCubeSet_gluedGradientField hnu
            S.LPrime S.n S.m F omega (originCube d (S.m : ℤ))) -
          toHilbertVectorL2OfVecField (memVectorL2_openCubeSet_gluedGradientField hnu
            S.ell S.n S.m F omega (originCube d (S.m : ℤ))) := by
      funext omega
      exact toHilbertVectorL2OfVecField_sub _ _
    rw [hsub]
    have hpair : AEMeasurable (fun omega : ShellSeq d =>
        (toHilbertVectorL2OfVecField (memVectorL2_openCubeSet_gluedGradientField hnu
            S.LPrime S.n S.m F omega (originCube d (S.m : ℤ))),
          toHilbertVectorL2OfVecField (memVectorL2_openCubeSet_gluedGradientField hnu
            S.ell S.n S.m F omega (originCube d (S.m : ℤ))))) P.toMeasure :=
      (measurable_gluedGradientClass hnu S.LPrime S.n S.m F).aemeasurable.prodMk
        ((measurable_gluedGradientClass hnu S.ell S.n S.m F).aemeasurable)
    exact continuous_sub.measurable.comp_aemeasurable hpair
  have hRmeas := aemeasurable_vecCubeLpENorm_matVecMul_coefficientCutoff_sub_grad
    (d := d) hnu S.LPrime S.ell (LPrime := S.LPrime) (ellPrime := S.ellPrime) (m := S.m)
    (p := testVector nu S.LPrime P S.n e) (mu := P.toMeasure) (w := w) hw
  have hfinDiff : (∫⁻ omega : ShellSeq d,
      vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        (fun x => gluedGradientField hnu S.LPrime S.n S.m F omega x -
          gluedGradientField hnu S.ell S.n S.m F omega x) ^ (2 : ℕ)
      ∂P.toMeasure) ≠ ⊤ := (term2_ob4_finite hnu P S hS e).1
  exact integrable_volumeAverage_pairing hRL2 hRclass hGL2 hGclass hRmeas hfinR hfinDiff

/-! ## The three integrals together -/

/-- **Integrability of the three annealed pairing integrals of `l.RHS.term2`**: the
summands of the display are integrable in the sample.  The conjuncts are `term2_ob6_intDiff`,
`term2_ob6_intProxy` and `term2_ob6_intMean`.  The only carried hypothesis
beyond the statement's binders is the finiteness of the annealed
squared cube norm of the response flux `R`. -/
theorem term2_ob6_int [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection)
    (hS : ScalesOrdering S) (e : Vec d)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega))
    (hfinR : (∫⁻ omega : ShellSeq d,
      vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
            (coefficientCutoff nu omega S.ell).toCoeffField y)
          ((w omega).toH1Function.grad y)) ^ (2 : ℕ) ∂P.toMeasure) ≠ ⊤) :
    (Integrable (fun omega : ShellSeq d =>
        volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun y => vecDot (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
                (coefficientCutoff nu omega S.ell).toCoeffField y)
              ((w omega).toH1Function.grad y))
            (gluedGradientField hnu S.LPrime S.n S.m
                (fluxSlot nu S.LPrime P S.n e) omega y -
              gluedGradientField hnu S.ell S.n S.m
                (fluxSlot nu S.LPrime P S.n e) omega y))) P.toMeasure) ∧
    (Integrable (fun omega : ShellSeq d =>
        volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun y => vecDot (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
                (coefficientCutoff nu omega S.ell).toCoeffField y)
              ((w omega).toH1Function.grad y))
            (gluedGradientField hnu S.ell S.n S.m
                (fluxSlot nu S.LPrime P S.n e) omega y -
              annealedGluedAverage hnu P S.ell S.n S.m
                (fluxSlot nu S.LPrime P S.n e)))) P.toMeasure) ∧
    (Integrable (fun omega : ShellSeq d =>
        volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun y => vecDot (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
                (coefficientCutoff nu omega S.ell).toCoeffField y)
              ((w omega).toH1Function.grad y))
            (annealedGluedAverage hnu P S.ell S.n S.m
                (fluxSlot nu S.LPrime P S.n e) -
              testVector nu S.LPrime P S.n e))) P.toMeasure) :=
  ⟨term2_ob6_intDiff hnu P S hS e w hw hfinR,
    term2_ob6_intProxy hnu P S hS e w hw hfinR,
    term2_ob6_intMean hnu P S hS e w hw hfinR⟩

end

end SuperdiffusionCLT.Section3.Terms