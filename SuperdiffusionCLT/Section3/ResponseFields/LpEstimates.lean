/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.ResponseFields.Definitions
public import SuperdiffusionCLT.Section3.ResponseFields.Norms
public import Homogenization.Sobolev.Foundations.CubeCalderonZygmund.DirichletNeumannEndpoint

/-!
# `L̲^p` a priori estimates for the cube response fields

The display `e.abstract.response.L8` of the paper asserts that with a constant `C(d) < ∞`

> `‖∇w_D‖_{L̲⁸(cu_M)} + ‖∇w_N‖_{L̲⁸(cu_M)} ≤ C ‖F‖_{L̲⁸(cu_M)}`,

and Step 4 of the proof uses the same bound at the exponent
`4` for the difference of the two responses. Step 2 records
that both are the constant-coefficient Dirichlet and prescribed-flux Neumann
Calderón-Zygmund estimates in a cube.

CoarseGraining proves exactly that endpoint:
`Homogenization.CubeCalderonZygmund.exists_cubeDirichletNeumannDivergence_cz`
supplies, for `2 ≤ d` and every finite exponent `1 < p < ∞`, one positive real
constant that bounds the normalized `L^p` norm of the gradient of *both* the
zero-trace Dirichlet and the mean-zero Neumann weak solution of
`-div(∇u) = div f` by `C ‖f‖`. This file transports that estimate across the
two bridges of `Definitions.lean` and into the carrier `vecCubeLpENorm` of
`Norms.lean`.

## Two normalizations, one measure

The upstream `Homogenization.cubeLpNorm Q p f` is
`(eLpNorm f p (normalizedCubeMeasure Q)).toReal`, against the *same*
normalized cube measure that `vecCubeLpENorm` uses, so the volume
normalization needs no adjustment at all. Two conversions remain.

1. **The pointwise norm.** `cubeLpNorm` reads a vector field through the
   ambient `Vec d = Fin d → ℝ`, whose norm is the *supremum* norm; the
   manuscript's `|·|`, and hence `vecCubeLpENorm`, is the
   Euclidean one. The two are comparable with `‖x‖ ≤ |x| ≤ d ‖x‖`
   (`Homogenization.HilbertVec.norm_le_norm_ofVec` and
   `norm_ofVec_le_mul_norm`), so the transport costs one factor `d`, which the
   manuscript's `C(d)` absorbs.
2. **The value.** `cubeLpNorm` is `ENNReal.toReal` of the quantity, so it
   returns `0` on a field that is not `p`-integrable. The upstream statement
   carries `MemLp` witnesses on both sides, and those make the `toReal`
   inequality lift back to `ℝ≥0∞` without loss.

## The constant

Everything below is stated as `∃ C : ℝ≥0∞, C < ⊤ ∧ …` with `C` quantified
before the cube and the flux, exactly as `C(d)` of the paper requires: the
constant depends on `d` and on the exponent only. It is opaque, because the
upstream endpoint is itself existential (its good-λ parameters are chosen
inside its proof); the manuscript asserts only `C(d) < ∞`.

## Main results

* `memLp_hilbertifyVecField_iff`, `eLpNorm_le_vecCubeLpENorm`,
  `vecCubeLpENorm_le_dim_mul_eLpNorm`: the conversion between the ambient
  supremum norm and the manuscript's Euclidean magnitude.
* `exists_cubeResponseGradientLpEstimate`: the gradient bound for both
  responses at every finite exponent `1 < p < ∞`, with one constant.
* `exists_cubeResponseGradientL8Estimate`: `e.abstract.response.L8`, the sum
  form at `p = 8`.
* `exists_cubeResponseDifferenceL4Estimate`: the `L̲⁴` half of the two
  displays of Step 4, for `∇w_N - ∇w_D`.
* `vecGradientPairingDensity_eq_vecDot`: the pairing density as a
  plain dot product.
* `volumeAverage_cubeSet_eq_openCubeSet`,
  `volumeAverageVec_cubeSet_eq_openCubeSet`,
  `normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet`,
  `vecCubeLpENorm_congr_openCubeSet_ae`: the open-cube/half-open bridge.
* `volumeAverage_vecGradientPairingDensity_eq_of_isCubeNeumannResponse`: the
  gradient pairing against a smooth test function, evaluated
  through the Neumann equation.
* `vecHatNegENorm_le_of_isCubeNeumannResponse`: `‖F‖_{Ĥ̲^{-1}(Q)}` is at most
  `‖∇w_N‖_{L̲²(Q)}`.

## The two sides of the `Ĥ̲^{-1}` estimate

The `Ĥ̲^{-1}` standard estimate of Step 4 needs
`3^{-M}‖v-(v)_{cu_M}‖_{L̲²} ≤ C‖F_0‖_{Ĥ̲^{-1}}`, whose analytic core is the
energy estimate `‖∇w_N‖_{L̲²} ≤ ‖F‖_{Ĥ̲^{-1}}`. That direction tests the
supremum defining the norm against the *solution*, which is only `H¹`, whereas the
test class `IsVecHatTestField` is smooth by definition; it therefore needs a
smooth approximation of an `H¹` function on a cube in the gradient `L²` norm,
and is proved in `HminusOneDuality.lean`. The opposite inequality
needs no approximation, and it is what this file proves: every admissible test
function *is* an admissible Neumann test function, so the pairing is exactly
minus the Dirichlet form of the response against it, and Cauchy-Schwarz on the
normalized cube measure bounds it by `‖∇w_N‖_{L̲²(Q)}`. The Dirichlet response
admits no such statement, because its test class is `H¹₀` and a smooth
mean-zero function on the cube is not in it.

## What is treated elsewhere

The `W^{2,8}` display `e.abstract.response.W28` and the `H̲^{1/2}` display
`e.abstract.response.Hhalf` are treated in `AprioriAssembly.lean` and
`HhalfDilationB.lean`.
-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Section3
namespace ResponseFields

open Homogenization
open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The supremum norm and the Euclidean magnitude -/

/-- Reading a vector field in the Euclidean carrier does not change its `L^q`
membership: the two carriers are continuously linearly isomorphic. -/
theorem memLp_hilbertifyVecField_iff {μ : Measure (Vec d)} {q : ℝ≥0∞}
    {F : Vec d → Vec d} :
    MemLp (hilbertifyVecField F) q μ ↔ MemLp F q μ := by
  constructor
  · intro h
    exact ((HilbertVec.continuousLinearEquivVec d).toContinuousLinearMap).comp_memLp' h
  · intro h
    exact (HilbertVec.ofVecL d).comp_memLp' h

/-- The ambient supremum norm is dominated by the Euclidean magnitude, hence so
are the corresponding normalized cube norms. -/
theorem eLpNorm_le_vecCubeLpENorm (Q : TriadicCube d) (q : ℝ≥0∞)
    (F : Vec d → Vec d) :
    eLpNorm F q (normalizedCubeMeasure Q) ≤ vecCubeLpENorm Q q F := by
  by_cases hF : AEStronglyMeasurable F (normalizedCubeMeasure Q)
  · exact Section2.Norms.cubeLpENorm_mono_enorm hF
      (fun x => HilbertVec.norm_le_norm_ofVec (F x))
  · have hH : ¬ AEStronglyMeasurable (hilbertifyVecField F) (normalizedCubeMeasure Q) := by
      intro h
      exact hF (memLp_zero_iff_aestronglyMeasurable.mp
        ((memLp_hilbertifyVecField_iff (q := 0)).mp
          (memLp_zero_iff_aestronglyMeasurable.mpr h)))
    rw [eLpNorm_of_not_aestronglyMeasurable hF]
    refine le_of_eq ?_
    rw [vecCubeLpENorm, Section2.Norms.cubeLpENorm]
    exact (eLpNorm_of_not_aestronglyMeasurable hH).symm

/-- The Euclidean magnitude is dominated by `d` times the ambient supremum
norm, hence so are the corresponding normalized cube norms. -/
theorem vecCubeLpENorm_le_dim_mul_eLpNorm (Q : TriadicCube d) (q : ℝ≥0∞)
    (F : Vec d → Vec d)
    (hF : AEStronglyMeasurable (hilbertifyVecField F) (normalizedCubeMeasure Q)) :
    vecCubeLpENorm Q q F ≤
      ENNReal.ofReal (d : ℝ) * eLpNorm F q (normalizedCubeMeasure Q) := by
  have h : vecCubeLpENorm Q q F ≤ Section2.Norms.cubeLpENorm Q q ((d : ℝ) • F) := by
    refine Section2.Norms.cubeLpENorm_mono_enorm hF (fun x => ?_)
    have h1 := HilbertVec.norm_ofVec_le_mul_norm (F x)
    simp only [Pi.smul_apply, norm_smul, Real.norm_natCast]
    exact h1
  rw [Section2.Norms.cubeLpENorm_const_smul] at h
  refine h.trans_eq ?_
  congr 1
  simp

/-- The upstream real-valued inequality between two finite `eLpNorm`s lifts to
the extended reals. -/
private theorem eLpNorm_le_ofReal_mul_eLpNorm {Q : TriadicCube d} {q : ℝ≥0∞}
    {C : ℝ} (hC : 0 ≤ C) {G F : Vec d → Vec d}
    (hG : MemLp G q (normalizedCubeMeasure Q))
    (hF : MemLp F q (normalizedCubeMeasure Q))
    (h : cubeLpNorm Q q G ≤ C * cubeLpNorm Q q F) :
    eLpNorm G q (normalizedCubeMeasure Q) ≤
      ENNReal.ofReal C * eLpNorm F q (normalizedCubeMeasure Q) := by
  calc eLpNorm G q (normalizedCubeMeasure Q)
      = ENNReal.ofReal (eLpNorm G q (normalizedCubeMeasure Q)).toReal :=
        (ENNReal.ofReal_toReal hG.eLpNorm_ne_top).symm
    _ ≤ ENNReal.ofReal (C * (eLpNorm F q (normalizedCubeMeasure Q)).toReal) :=
        ENNReal.ofReal_le_ofReal h
    _ = ENNReal.ofReal C * ENNReal.ofReal (eLpNorm F q (normalizedCubeMeasure Q)).toReal :=
        ENNReal.ofReal_mul hC
    _ = ENNReal.ofReal C * eLpNorm F q (normalizedCubeMeasure Q) := by
        rw [ENNReal.ofReal_toReal hF.eLpNorm_ne_top]

/-- The identity coefficient field of `Definitions.lean` is the constant field
with value the identity matrix, the shape the upstream endpoint uses. -/
private theorem identityCoeffField_eq (d : ℕ) :
    identityCoeffField d = fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ) := by
  funext x
  simp [identityCoeffField]

/-! ## The gradient estimate at a general finite exponent -/

/-- **The `L̲^p` gradient estimate for both cube responses.** For `2 ≤ d` and
every finite exponent `1 < p < ∞` there is one finite constant, depending on
`d` and `p` alone, with

> `‖∇w‖_{L̲^p(Q)} ≤ C ‖F‖_{L̲^p(Q)}`

for every triadic cube `Q`, every flux `F ∈ L̲^p(Q)`, and both the Dirichlet
and the prescribed-flux Neumann response `w` of `F` on `Q`. This is Step 2 of
the proof, imported from CoarseGraining's cube
Calderón-Zygmund endpoint and converted to the Euclidean magnitude. The `L̲^p`
membership of the gradient is part of the conclusion. -/
theorem exists_cubeResponseGradientLpEstimate (hd : 2 ≤ d) (p : ℝ≥0∞)
    (hp_one : 1 < p) (hp_top : p < ∞) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ (Q : TriadicCube d) (F : Vec d → Vec d),
        MemLp (hilbertifyVecField F) p (normalizedCubeMeasure Q) →
        (∀ w : H10Function (openCubeSet Q), IsCubeDirichletResponse Q F w →
            MemLp (hilbertifyVecField w.toH1Function.grad) p
                (normalizedCubeMeasure Q) ∧
              vecCubeLpENorm Q p w.toH1Function.grad ≤
                C * vecCubeLpENorm Q p F) ∧
        (∀ w : H1MeanZeroFunction (openCubeSet Q), IsCubeNeumannResponse Q F w →
            MemLp (hilbertifyVecField w.toH1Function.grad) p
                (normalizedCubeMeasure Q) ∧
              vecCubeLpENorm Q p w.toH1Function.grad ≤
                C * vecCubeLpENorm Q p F) := by
  obtain ⟨C, hCpos, hC⟩ :=
    CubeCalderonZygmund.exists_cubeDirichletNeumannDivergence_cz hd p hp_one hp_top
  refine ⟨ENNReal.ofReal ((d : ℝ) * C), ENNReal.ofReal_lt_top, ?_⟩
  intro Q F hF
  have hFv : MemLp F p (normalizedCubeMeasure Q) :=
    memLp_hilbertifyVecField_iff.1 hF
  -- The two branches differ only in the carrier of the solution.
  have hmain : ∀ G : Vec d → Vec d,
      MemLp G p (normalizedCubeMeasure Q) →
      cubeLpNorm Q p G ≤ C * cubeLpNorm Q p F →
      MemLp (hilbertifyVecField G) p (normalizedCubeMeasure Q) ∧
        vecCubeLpENorm Q p G ≤ ENNReal.ofReal ((d : ℝ) * C) * vecCubeLpENorm Q p F := by
    intro G hG hbound
    refine ⟨memLp_hilbertifyVecField_iff.2 hG, ?_⟩
    calc vecCubeLpENorm Q p G
        ≤ ENNReal.ofReal (d : ℝ) * eLpNorm G p (normalizedCubeMeasure Q) :=
          vecCubeLpENorm_le_dim_mul_eLpNorm Q p G
            (memLp_hilbertifyVecField_iff.2 hG).aestronglyMeasurable
      _ ≤ ENNReal.ofReal (d : ℝ) *
            (ENNReal.ofReal C * eLpNorm F p (normalizedCubeMeasure Q)) := by
          gcongr
          exact eLpNorm_le_ofReal_mul_eLpNorm hCpos.le hG hFv hbound
      _ = ENNReal.ofReal ((d : ℝ) * C) * eLpNorm F p (normalizedCubeMeasure Q) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal ((d : ℝ) * C) * vecCubeLpENorm Q p F := by
          gcongr
          exact eLpNorm_le_vecCubeLpENorm Q p F
  constructor
  · intro w hw
    have hup := (hC Q F hFv).1 w (by
      have hb := (isCubeDirichletResponse_iff Q F w).1 hw
      rwa [identityCoeffField_eq d] at hb)
    exact hmain _ hup.1 hup.2
  · intro w hw
    have hup := (hC Q F hFv).2 w (by
      have hb := (isCubeNeumannResponse_iff Q F w).1 hw
      rwa [identityCoeffField_eq d] at hb)
    exact hmain _ hup.1 hup.2

/-! ## `e.abstract.response.L8` -/

/-- **`e.abstract.response.L8`**: with a constant depending
on `d` alone,

> `‖∇w_D‖_{L̲⁸(cu_M)} + ‖∇w_N‖_{L̲⁸(cu_M)} ≤ C ‖F‖_{L̲⁸(cu_M)}`

for every triadic cube, every flux in `L̲⁸` of the cube, and every pair of
Dirichlet and prescribed-flux Neumann responses of that flux. -/
theorem exists_cubeResponseGradientL8Estimate (hd : 2 ≤ d) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ (Q : TriadicCube d) (F : Vec d → Vec d),
        MemLp (hilbertifyVecField F) 8 (normalizedCubeMeasure Q) →
        ∀ (wD : H10Function (openCubeSet Q)) (wN : H1MeanZeroFunction (openCubeSet Q)),
          IsCubeDirichletResponse Q F wD → IsCubeNeumannResponse Q F wN →
            vecCubeLpENorm Q 8 wD.toH1Function.grad +
                vecCubeLpENorm Q 8 wN.toH1Function.grad ≤
              C * vecCubeLpENorm Q 8 F := by
  obtain ⟨C, hCtop, hC⟩ :=
    exists_cubeResponseGradientLpEstimate hd 8 (by norm_num) (by norm_num)
  refine ⟨2 * C, ENNReal.mul_lt_top (by norm_num) hCtop, ?_⟩
  intro Q F hF wD wN hD hN
  have hDb := ((hC Q F hF).1 wD hD).2
  have hNb := ((hC Q F hF).2 wN hN).2
  calc vecCubeLpENorm Q 8 wD.toH1Function.grad +
        vecCubeLpENorm Q 8 wN.toH1Function.grad
      ≤ C * vecCubeLpENorm Q 8 F + C * vecCubeLpENorm Q 8 F := add_le_add hDb hNb
    _ = 2 * C * vecCubeLpENorm Q 8 F := by ring

/-! ## The `L̲⁴` estimate of Step 4 -/

/-- **The `L̲⁴` half of the two standard estimates of Step 4.** With a constant
depending on `d` alone,

> `‖∇w_N - ∇w_D‖_{L̲⁴(cu_M)} ≤ C ‖F‖_{L̲⁴(cu_M)}`,

by the triangle inequality from the gradient estimate at the exponent `4`
applied to each response separately. In Step 4 the flux is the centred
`F_0 = F - (F)_{cu_M}` and the difference is read on the harmonic function
`v`; the estimate here is the deterministic input, stated for an arbitrary
flux. -/
theorem exists_cubeResponseDifferenceL4Estimate (hd : 2 ≤ d) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ (Q : TriadicCube d) (F : Vec d → Vec d),
        MemLp (hilbertifyVecField F) 4 (normalizedCubeMeasure Q) →
        ∀ (wD : H10Function (openCubeSet Q)) (wN : H1MeanZeroFunction (openCubeSet Q)),
          IsCubeDirichletResponse Q F wD → IsCubeNeumannResponse Q F wN →
            vecCubeLpENorm Q 4
                (fun x => wN.toH1Function.grad x - wD.toH1Function.grad x) ≤
              C * vecCubeLpENorm Q 4 F := by
  obtain ⟨C, hCtop, hC⟩ :=
    exists_cubeResponseGradientLpEstimate hd 4 (by norm_num) (by norm_num)
  refine ⟨2 * C, ENNReal.mul_lt_top (by norm_num) hCtop, ?_⟩
  intro Q F hF wD wN hD hN
  obtain ⟨hDmem, hDb⟩ := (hC Q F hF).1 wD hD
  obtain ⟨hNmem, hNb⟩ := (hC Q F hF).2 wN hN
  have hDneg : AEStronglyMeasurable
      (hilbertifyVecField (fun x => -wD.toH1Function.grad x))
      (normalizedCubeMeasure Q) := by
    have h : hilbertifyVecField (fun x => -wD.toH1Function.grad x)
        = -hilbertifyVecField wD.toH1Function.grad := by
      funext x
      exact map_neg (HilbertVec.linearEquivVec d).symm _
    rw [h]
    exact hDmem.aestronglyMeasurable.neg
  have htri : vecCubeLpENorm Q 4
        (fun x => wN.toH1Function.grad x - wD.toH1Function.grad x) ≤
      vecCubeLpENorm Q 4 wN.toH1Function.grad +
        vecCubeLpENorm Q 4 (fun x => -wD.toH1Function.grad x) := by
    have := vecCubeLpENorm_add_le (Q := Q) (q := 4)
      (F := wN.toH1Function.grad) (G := fun x => -wD.toH1Function.grad x)
      (by norm_num) hNmem.aestronglyMeasurable hDneg
    simpa only [sub_eq_add_neg] using this
  rw [vecCubeLpENorm_neg] at htri
  calc vecCubeLpENorm Q 4
        (fun x => wN.toH1Function.grad x - wD.toH1Function.grad x)
      ≤ vecCubeLpENorm Q 4 wN.toH1Function.grad +
          vecCubeLpENorm Q 4 wD.toH1Function.grad := htri
    _ ≤ C * vecCubeLpENorm Q 4 F + C * vecCubeLpENorm Q 4 F := add_le_add hNb hDb
    _ = 2 * C * vecCubeLpENorm Q 4 F := by ring


/-! ## The gradient pairing of the hatted negative norm -/

/-- The pairing density is the plain dot product of the field with
the Euclidean gradient of the test function. -/
theorem vecGradientPairingDensity_eq_vecDot (F : Vec d → Vec d) (g : Vec d → ℝ)
    (x : Vec d) :
    vecGradientPairingDensity F g x = vecDot (F x) (euclideanGradient g x) := by
  rw [vecGradientPairingDensity_eq_sum]
  rfl

/-! ## The open-cube/half-open bridge

`l.abstract.response.fields` puts its function spaces and its two response
predicates on the **open** cube `openCubeSet Q`, while the normalized norms of
`Norms.lean` and the cube averages `(F)_{cu_M}` are taken over the **half-open**
`cubeSet Q`. The two conventions are interchangeable, because
`Homogenization.volume_restrict_cubeSet_eq_volume_restrict_openCubeSet`
identifies the two restricted volume measures and the two sets have the same
volume. The four public statements below are that bridge. -/

/-- **The bridge for normalized cube averages.** The two normalized averages of
a triadic cube agree: the half-open cube and the open cube differ by a Lebesgue
null set and have the same volume. -/
theorem volumeAverage_cubeSet_eq_openCubeSet (Q : TriadicCube d)
    (f : Vec d → ℝ) :
    volumeAverage (cubeSet Q) f = volumeAverage (openCubeSet Q) f := by
  rw [volumeAverage, volumeAverage,
    show (volume (cubeSet Q)).toReal = (volume (openCubeSet Q)).toReal by
      rw [volume_cubeSet_toReal, volume_openCubeSet_toReal],
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]

/-- **The bridge for the vector cube average `(F)_{cu_M}`**, coordinatewise from
`volumeAverage_cubeSet_eq_openCubeSet`. -/
theorem volumeAverageVec_cubeSet_eq_openCubeSet (Q : TriadicCube d)
    (F : Vec d → Vec d) :
    volumeAverageVec (cubeSet Q) F = volumeAverageVec (openCubeSet Q) F := by
  funext i
  exact volumeAverage_cubeSet_eq_openCubeSet Q (fun x => F x i)

/-- **The bridge for the normalized cube measure.** The measure against which
`cubeLpENorm`, `vecCubeLpENorm` and `cubeHsENorm` are taken is the normalized
volume measure of the *open* cube just as much as of the half-open cube. -/
theorem normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet
    (Q : TriadicCube d) :
    normalizedCubeMeasure Q =
      ENNReal.ofReal ((cubeVolume Q)⁻¹) • volume.restrict (openCubeSet Q) := by
  rw [normalizedCubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]

/-- **The bridge for the normalized `L̲^q` norm.** Two fields that agree almost
everywhere on the *open* cube have the same `‖·‖_{L̲^q(Q)}`, which is defined
over the half-open cube. This is the form the response-field estimates need: the
gradient of an `H¹` function on `openCubeSet Q` is determined only up to a null
set of that open cube. -/
theorem vecCubeLpENorm_congr_openCubeSet_ae {Q : TriadicCube d} {q : ℝ≥0∞}
    {F G : Vec d → Vec d}
    (h : F =ᵐ[volume.restrict (openCubeSet Q)] G) :
    vecCubeLpENorm Q q F = vecCubeLpENorm Q q G := by
  have hH : hilbertifyVecField F =ᵐ[normalizedCubeMeasure Q]
      hilbertifyVecField G := by
    rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
    exact Measure.ae_smul_measure (h.mono (fun x hx => by
      simp only [hilbertifyVecField, hx])) _
  exact eLpNorm_congr_ae hH

/-- The normalized cube average is the integral against the normalized cube
measure. -/
private theorem volumeAverage_eq_integral_normalizedCubeMeasure (Q : TriadicCube d)
    (f : Vec d → ℝ) :
    volumeAverage (cubeSet Q) f = ∫ x, f x ∂normalizedCubeMeasure Q := by
  rw [volumeAverage, normalizedCubeMeasure, cubeMeasure, integral_smul_measure,
    volume_cubeSet_toReal]
  congr 1
  simp [ENNReal.toReal_ofReal, inv_nonneg, cubeVolume_nonneg]

/-- The gradient of an `H¹` function on the open cube is strongly measurable for
the normalized cube measure. -/
private theorem aestronglyMeasurable_hilbertifyVecField_grad {Q : TriadicCube d}
    (u : H1Function (openCubeSet Q)) :
    AEStronglyMeasurable (hilbertifyVecField u.grad) (normalizedCubeMeasure Q) := by
  have h : AEStronglyMeasurable (hilbertifyVecField u.grad)
      (volume.restrict (openCubeSet Q)) :=
    (memHilbertVectorL2_hilbertifyVecField u.grad_memVectorL2).aestronglyMeasurable
  rw [normalizedCubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  exact h.smul_measure _

/-- The Euclidean gradient of a smooth function is continuous, hence strongly
measurable for every measure. -/
private theorem aestronglyMeasurable_hilbertifyVecField_euclideanGradient
    {g : Vec d → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (μ : Measure (Vec d)) :
    AEStronglyMeasurable (hilbertifyVecField (euclideanGradient g)) μ := by
  have hfd : Continuous (fun x : Vec d => fderiv ℝ g x) :=
    hg.continuous_fderiv (by simp)
  have hcont : Continuous (fun x : Vec d => euclideanGradient g x) :=
    continuous_pi fun i => hfd.clm_apply continuous_const
  exact ((HilbertVec.ofVecL d).continuous.comp hcont).aestronglyMeasurable

/-- Cauchy-Schwarz for the normalized cube average of a dot product, in the
Euclidean magnitude. -/
private theorem ofReal_volumeAverage_vecDot_le {Q : TriadicCube d}
    {a b : Vec d → Vec d}
    (ha : AEStronglyMeasurable (hilbertifyVecField a) (normalizedCubeMeasure Q))
    (hb : AEStronglyMeasurable (hilbertifyVecField b) (normalizedCubeMeasure Q)) :
    ENNReal.ofReal (volumeAverage (cubeSet Q) (fun x => vecDot (a x) (b x))) ≤
      vecCubeLpENorm Q 2 a * vecCubeLpENorm Q 2 b := by
  have hbound : ENNReal.ofReal
        (∫ x, vecDot (a x) (b x) ∂normalizedCubeMeasure Q) ≤
      ∫⁻ x, ‖vecDot (a x) (b x)‖ₑ ∂normalizedCubeMeasure Q := by
    by_cases hint : Integrable (fun x => vecDot (a x) (b x)) (normalizedCubeMeasure Q)
    · calc ENNReal.ofReal (∫ x, vecDot (a x) (b x) ∂normalizedCubeMeasure Q)
          ≤ ENNReal.ofReal (∫ x, ‖vecDot (a x) (b x)‖ ∂normalizedCubeMeasure Q) :=
            ENNReal.ofReal_le_ofReal
              (le_trans (le_abs_self _)
                (norm_integral_le_integral_norm (fun x => vecDot (a x) (b x))))
        _ = ∫⁻ x, ‖vecDot (a x) (b x)‖ₑ ∂normalizedCubeMeasure Q :=
            ofReal_integral_norm_eq_lintegral_enorm hint
    · rw [integral_undef hint]
      simp
  have hptr : ∀ x : Vec d, ‖vecDot (a x) (b x)‖ₑ ≤
      ‖hilbertifyVecField a x‖ₑ * ‖hilbertifyVecField b x‖ₑ := by
    intro x
    have h : |vecDot (a x) (b x)| ≤
        ‖hilbertifyVecField a x‖ * ‖hilbertifyVecField b x‖ := by
      simpa [hilbertifyVecField, HilbertVec.inner_def] using
        abs_real_inner_le_norm (hilbertifyVecField a x) (hilbertifyVecField b x)
    calc ‖vecDot (a x) (b x)‖ₑ = ENNReal.ofReal |vecDot (a x) (b x)| := by
          rw [Real.enorm_eq_ofReal_abs]
      _ ≤ ENNReal.ofReal (‖hilbertifyVecField a x‖ * ‖hilbertifyVecField b x‖) :=
          ENNReal.ofReal_le_ofReal h
      _ = ‖hilbertifyVecField a x‖ₑ * ‖hilbertifyVecField b x‖ₑ := by
          rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm,
            ofReal_norm]
  rw [volumeAverage_eq_integral_normalizedCubeMeasure]
  calc ENNReal.ofReal (∫ x, vecDot (a x) (b x) ∂normalizedCubeMeasure Q)
      ≤ ∫⁻ x, ‖vecDot (a x) (b x)‖ₑ ∂normalizedCubeMeasure Q := hbound
    _ ≤ ∫⁻ x, ‖hilbertifyVecField a x‖ₑ * ‖hilbertifyVecField b x‖ₑ
          ∂normalizedCubeMeasure Q := lintegral_mono hptr
    _ ≤ (∫⁻ x, ‖hilbertifyVecField a x‖ₑ ^ (2 : ℝ) ∂normalizedCubeMeasure Q) ^
            (1 / (2 : ℝ)) *
          (∫⁻ x, ‖hilbertifyVecField b x‖ₑ ^ (2 : ℝ) ∂normalizedCubeMeasure Q) ^
            (1 / (2 : ℝ)) :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq (normalizedCubeMeasure Q)
          Real.HolderConjugate.two_two ha.enorm hb.enorm
    _ = vecCubeLpENorm Q 2 a * vecCubeLpENorm Q 2 b := by
        rw [vecCubeLpENorm, vecCubeLpENorm, Section2.Norms.cubeLpENorm,
          Section2.Norms.cubeLpENorm,
          eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) ha,
          eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hb]
        norm_num

/-- **The gradient pairing through the Neumann equation.** A smooth test
function is, after subtraction of its average, an admissible test
function for the prescribed-flux Neumann problem, whose test class is all of
`H¹(Q)` and whose formulation only sees the gradient. Hence the pairing
`⨍_Q F·∇g` of the hatted negative norm equals minus the Dirichlet form of the
Neumann response against `g`. -/
theorem volumeAverage_vecGradientPairingDensity_eq_of_isCubeNeumannResponse
    {Q : TriadicCube d} {F : Vec d → Vec d} {w : H1MeanZeroFunction (openCubeSet Q)}
    (hw : IsCubeNeumannResponse Q F w) {g : Vec d → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    volumeAverage (cubeSet Q) (vecGradientPairingDensity F g) =
      -volumeAverage (cubeSet Q)
        (fun x => vecDot (w.toH1Function.grad x) (euclideanGradient g x)) := by
  have hweak : ∫ x in openCubeSet Q,
      vecDot (w.toH1Function.grad x) (euclideanGradient g x) =
        -∫ x in openCubeSet Q, vecDot (F x) (euclideanGradient g x) := by
    have hw' := hw (H1Function.toMeanZero
        (H1Function.ofContDiffOnIsOpenBoundedConvexDomain
          (isOpenBoundedConvexDomain_openCubeSet Q)
          (hg.of_le (by simp))))
    simp only [H1Function.toMeanZero_grad] at hw'
    exact hw'
  have hdens : vecGradientPairingDensity F g
      = fun x => vecDot (F x) (euclideanGradient g x) :=
    funext (vecGradientPairingDensity_eq_vecDot F g)
  rw [hdens, volumeAverage_cubeSet_eq_openCubeSet,
    volumeAverage_cubeSet_eq_openCubeSet, volumeAverage, volumeAverage, hweak]
  ring

/-- **The hatted negative norm of a flux is at most the `L̲²` norm of the
gradient of its Neumann response.** Every admissible test function
pairs against `F` exactly as it pairs against `-∇w_N`, so
Cauchy-Schwarz on the normalized cube measure and the constraint
`‖∇g‖_{L̲²(Q)} ≤ 1` bound the supremum defining `‖F‖_{Ĥ̲^{-1}(Q)}`. -/
theorem vecHatNegENorm_le_of_isCubeNeumannResponse {Q : TriadicCube d}
    {F : Vec d → Vec d} {w : H1MeanZeroFunction (openCubeSet Q)}
    (hw : IsCubeNeumannResponse Q F w) :
    vecHatNegENorm Q F ≤ vecCubeLpENorm Q 2 w.toH1Function.grad := by
  refine vecHatNegENorm_le (fun g hg => ?_)
  have hgradNeg : hilbertifyVecField (fun x => -euclideanGradient g x)
      = -hilbertifyVecField (euclideanGradient g) := by
    funext x
    exact map_neg (HilbertVec.linearEquivVec d).symm _
  have hb : AEStronglyMeasurable
      (hilbertifyVecField (fun x => -euclideanGradient g x))
      (normalizedCubeMeasure Q) := by
    rw [hgradNeg]
    exact (aestronglyMeasurable_hilbertifyVecField_euclideanGradient hg.contDiff _).neg
  have hpair : volumeAverage (cubeSet Q) (vecGradientPairingDensity F g) =
      volumeAverage (cubeSet Q)
        (fun x => vecDot (w.toH1Function.grad x) (-euclideanGradient g x)) := by
    rw [volumeAverage_vecGradientPairingDensity_eq_of_isCubeNeumannResponse hw hg.contDiff,
      volumeAverage, volumeAverage]
    have hpt : ∀ x : Vec d,
        vecDot (w.toH1Function.grad x) (-euclideanGradient g x) =
          -vecDot (w.toH1Function.grad x) (euclideanGradient g x) := by
      intro x
      simp only [vecDot, Pi.neg_apply, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [setIntegral_congr_fun (measurableSet_cubeSet Q) (fun x _ => hpt x),
      integral_neg]
    ring
  rw [hpair]
  calc ENNReal.ofReal (volumeAverage (cubeSet Q)
        (fun x => vecDot (w.toH1Function.grad x) (-euclideanGradient g x)))
      ≤ vecCubeLpENorm Q 2 w.toH1Function.grad *
          vecCubeLpENorm Q 2 (fun x => -euclideanGradient g x) :=
        ofReal_volumeAverage_vecDot_le
          (aestronglyMeasurable_hilbertifyVecField_grad w.toH1Function) hb
    _ = vecCubeLpENorm Q 2 w.toH1Function.grad *
          vecCubeLpENorm Q 2 (euclideanGradient g) := by
        rw [vecCubeLpENorm_neg]
    _ ≤ vecCubeLpENorm Q 2 w.toH1Function.grad * 1 := by
        gcongr
        exact hg.gradient_le_one
    _ = vecCubeLpENorm Q 2 w.toH1Function.grad := mul_one _

end

end ResponseFields
end Section3
end SuperdiffusionCLT
