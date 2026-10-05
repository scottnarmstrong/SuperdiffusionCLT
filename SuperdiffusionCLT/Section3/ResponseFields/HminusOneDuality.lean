/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.ResponseFields.LpEstimates
public import SuperdiffusionCLT.Sobolev.CubeSmoothDensity

/-!
# The `Ĥ̲^{-1}` duality of the prescribed-flux Neumann response

The paper reads `‖F‖_{Ĥ̲^{-1}(U)}` as the
supremum of `⨍_U F·∇g` over smooth mean-zero `g` with `‖∇g‖_{L̲²(U)} ≤ 1`.
`Section3/ResponseFields/LpEstimates.lean` proves one half of the
duality, `vecHatNegENorm_le_of_isCubeNeumannResponse`:

> `‖F‖_{Ĥ̲^{-1}(Q)} ≤ ‖∇w_N‖_{L̲²(Q)}`,

by Cauchy-Schwarz. This file proves the reverse inequality and hence the exact
identity used by `e.abstract.response.ND.weak` and by Step 4
of the proof of `l.abstract.response.fields`.

## Why a density statement is needed

The reverse inequality is obtained by testing the supremum at `-w_N` itself,
renormalized. That candidate is only `H¹`, while the test class is
smooth, so the missing input is the smooth density of `H¹` on a cube in the
gradient norm. It is supplied here by
`SuperdiffusionCLT.Sobolev.exists_cubeH1MeanZeroSmoothGradientApprox`.

## The quantitative form

Write `n := ‖∇w_N‖_{L̲²(Q)}` and fix `δ > 0`. A smooth mean-zero `g₀` with
`‖∇g₀ - ∇w_N‖_{L̲²(Q)} < δ` has `‖∇g₀‖_{L̲²(Q)} ≤ n + δ`, so
`g := -(n + δ)⁻¹ g₀` is admissible, and the Neumann equation together with
Cauchy-Schwarz gives

`⨍_Q F·∇g = (n + δ)⁻¹ ⨍_Q ∇w_N·∇g₀ ≥ (n + δ)⁻¹ (n² - n δ) ≥ n - 2δ`.

Letting `δ → 0` gives `‖F‖_{Ĥ̲^{-1}(Q)} ≥ n`. All the Hilbert-space algebra is
carried out in `L²(normalizedCubeMeasure Q; HilbertVec d)`, whose inner product
is exactly the normalized cube average of the coordinate dot product.

## Step 4 of the response-field lemma

The first standard estimate of Step 4 is
`3^{-M}‖v − (v)_{cu_M}‖_{L̲²(cu_M)} ≤ C‖F₀‖_{Ĥ̲^{-1}(cu_M)}` for the difference
`v` of the two responses of the centered flux `F₀`. Its two remaining inputs are
the exact energy gap `volumeAverage_energy_gap` of `Definitions.lean`, which
bounds `‖∇v‖_{L̲²}` by `‖∇w_N‖_{L̲²}`, and CoarseGraining's scale-correct cube
Poincaré-Wirtinger estimate `scaledTranslatedCubeMeanZeroH1CoerciveEstimate`,
whose constant is `3^{scale} C(d)`; the file assembles both into
`cubeScaleFactor_inv_mul_cubeLpENorm_subAverage_le`.

## Main results

* `vecCubeLpENorm_le_vecHatNegENorm_of_isCubeNeumannResponse`: the reverse
  inequality `‖∇w_N‖_{L̲²(Q)} ≤ ‖F‖_{Ĥ̲^{-1}(Q)}`.
* `vecHatNegENorm_eq_of_isCubeNeumannResponse`: the identity
  `‖F‖_{Ĥ̲^{-1}(Q)} = ‖∇w_N‖_{L̲²(Q)}`.
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

/-! ## The `L²` realization against the normalized cube measure -/

private theorem volumeAverage_cubeSet_eq_cubeAverage' (Q : TriadicCube d)
    (f : Vec d → ℝ) : volumeAverage (cubeSet Q) f = cubeAverage Q f := by
  rw [volumeAverage, cubeAverage, volume_cubeSet_toReal]

private theorem memLp_hilbertifyVecField_normalizedCubeMeasure {Q : TriadicCube d}
    {F : Vec d → Vec d} (hF : MemVectorL2 (openCubeSet Q) F) :
    MemLp (hilbertifyVecField F) 2 (normalizedCubeMeasure Q) := by
  rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
  exact (memHilbertVectorL2_hilbertifyVecField hF).smul_measure ENNReal.ofReal_ne_top

private theorem norm_toLp_hilbertifyVecField {Q : TriadicCube d} {F : Vec d → Vec d}
    (hF : MemLp (hilbertifyVecField F) 2 (normalizedCubeMeasure Q)) :
    ‖hF.toLp (hilbertifyVecField F)‖ = (vecCubeLpENorm Q 2 F).toReal :=
  Lp.norm_toLp _ hF

/-- The inner product of the two `L²` realizations is the normalized cube
average of the coordinate dot product, which is the manuscript's `⨍_Q a·b`. -/
private theorem inner_toLp_hilbertifyVecField {Q : TriadicCube d} {a b : Vec d → Vec d}
    (ha : MemLp (hilbertifyVecField a) 2 (normalizedCubeMeasure Q))
    (hb : MemLp (hilbertifyVecField b) 2 (normalizedCubeMeasure Q)) :
    (inner ℝ (ha.toLp (hilbertifyVecField a)) (hb.toLp (hilbertifyVecField b)) : ℝ) =
      volumeAverage (cubeSet Q) (fun x => vecDot (a x) (b x)) := by
  rw [L2.inner_def, volumeAverage_cubeSet_eq_cubeAverage',
    cubeAverage_eq_integral_normalizedCubeMeasure]
  refine integral_congr_ae ?_
  filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with x hxa hxb
  rw [hxa, hxb]
  exact HilbertVec.inner_def _ _

/-! ## Elementary rewriting of the test function -/

private theorem euclideanGradient_const_mul {g : Vec d → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (c : ℝ) (x : Vec d) :
    euclideanGradient (fun y => c * g y) x = c • euclideanGradient g x := by
  funext i
  have hdiff : DifferentiableAt ℝ g x := (hg.differentiable (by simp)) x
  simp only [euclideanGradient, euclideanCoordDeriv, Pi.smul_apply, smul_eq_mul]
  rw [fderiv_const_mul hdiff]
  rfl

private theorem volumeAverage_const_mul (Q : TriadicCube d) (c : ℝ) (f : Vec d → ℝ) :
    volumeAverage (cubeSet Q) (fun x => c * f x) =
      c * volumeAverage (cubeSet Q) f := by
  simp only [volumeAverage, integral_const_mul]
  ring

private theorem vecDot_const_smul_right (a b : Vec d) (c : ℝ) :
    vecDot a (c • b) = c * vecDot a b := by
  simp only [vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ## The reverse inequality -/

/-- **The `L̲²` energy of the Neumann response is at most the hatted negative
norm of its flux.** Testing the supremum at a smooth approximation
of `-w_N/‖∇w_N‖_{L̲²(Q)}`, which the cube density theorem supplies, and letting
the approximation error tend to zero. -/
theorem vecCubeLpENorm_le_vecHatNegENorm_of_isCubeNeumannResponse {Q : TriadicCube d}
    {F : Vec d → Vec d} {w : H1MeanZeroFunction (openCubeSet Q)}
    (hw : IsCubeNeumannResponse Q F w) :
    vecCubeLpENorm Q 2 w.toH1Function.grad ≤ vecHatNegENorm Q F := by
  have hAmem : MemLp (hilbertifyVecField w.toH1Function.grad) 2 (normalizedCubeMeasure Q) :=
    memLp_hilbertifyVecField_normalizedCubeMeasure w.toH1Function.grad_memVectorL2
  set A := hAmem.toLp (hilbertifyVecField w.toH1Function.grad) with hAdef
  have hNtop : vecCubeLpENorm Q 2 w.toH1Function.grad ≠ ⊤ := hAmem.eLpNorm_lt_top.ne
  set n : ℝ := (vecCubeLpENorm Q 2 w.toH1Function.grad).toReal with hndef
  have hn0 : 0 ≤ n := ENNReal.toReal_nonneg
  have hNn : vecCubeLpENorm Q 2 w.toH1Function.grad = ENNReal.ofReal n :=
    (ENNReal.ofReal_toReal hNtop).symm
  have hAnorm : ‖A‖ = n := norm_toLp_hilbertifyVecField hAmem
  have key : ∀ δ : ℝ, 0 < δ → ENNReal.ofReal (n - 2 * δ) ≤ vecHatNegENorm Q F := by
    intro δ hδ
    obtain ⟨g₀, hg₀smooth, hg₀mean, hg₀close⟩ :=
      Sobolev.exists_cubeH1MeanZeroSmoothGradientApprox Q w (ENNReal.ofReal δ)
        (ENNReal.ofReal_pos.2 hδ)
    -- the approximant and the error field, realized in `L²`
    have hGcont : Continuous (fun x : Vec d => hilbertifyVecField (euclideanGradient g₀) x) := by
      have hfd : Continuous (fun x : Vec d => fderiv ℝ g₀ x) :=
        hg₀smooth.continuous_fderiv (by simp)
      have hcont : Continuous (fun x : Vec d => euclideanGradient g₀ x) :=
        continuous_pi fun i => hfd.clm_apply continuous_const
      exact (HilbertVec.ofVecL d).continuous.comp hcont
    have hEfun : hilbertifyVecField
          (fun x => euclideanGradient g₀ x - w.toH1Function.grad x)
        = hilbertifyVecField (euclideanGradient g₀) -
            hilbertifyVecField w.toH1Function.grad := by
      funext x
      exact map_sub (HilbertVec.linearEquivVec d).symm _ _
    have hEtop : eLpNorm (hilbertifyVecField
        (fun x => euclideanGradient g₀ x - w.toH1Function.grad x)) 2
        (normalizedCubeMeasure Q) < ⊤ := lt_of_lt_of_le hg₀close le_top
    have hEmem : MemLp (hilbertifyVecField
        (fun x => euclideanGradient g₀ x - w.toH1Function.grad x)) 2
        (normalizedCubeMeasure Q) := by
      exact MeasureTheory.memLp_iff.mpr hEtop
    have hGmem : MemLp (hilbertifyVecField (euclideanGradient g₀)) 2
        (normalizedCubeMeasure Q) := by
      have hsum : hilbertifyVecField (euclideanGradient g₀)
          = hilbertifyVecField
              (fun x => euclideanGradient g₀ x - w.toH1Function.grad x) +
            hilbertifyVecField w.toH1Function.grad := by
        rw [hEfun]
        abel
      rw [hsum]
      exact hEmem.add hAmem
    set G := hGmem.toLp (hilbertifyVecField (euclideanGradient g₀)) with hGdef
    set E := hEmem.toLp (hilbertifyVecField
      (fun x => euclideanGradient g₀ x - w.toH1Function.grad x)) with hEdef
    have hEeq : E = G - A := by
      rw [hEdef, hGdef, hAdef, ← MemLp.toLp_sub]
      exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall (fun x => congrFun hEfun x))
    have hEnorm : ‖E‖ ≤ δ := by
      have h := norm_toLp_hilbertifyVecField hEmem
      rw [← hEdef] at h
      rw [h, vecCubeLpENorm]
      exact le_of_lt (by
        have := (ENNReal.toReal_lt_toReal hEtop.ne ENNReal.ofReal_ne_top).2 hg₀close
        rwa [ENNReal.toReal_ofReal hδ.le] at this)
    -- the normalization constant
    have hden : 0 < n + δ := by linarith only [hn0, hδ]
    set c : ℝ := (n + δ)⁻¹ with hcdef
    have hcpos : 0 < c := inv_pos.2 hden
    -- the admissible test function
    have hgsmooth : ContDiff ℝ (⊤ : ℕ∞) (fun x => -c * g₀ x) :=
      contDiff_const.mul hg₀smooth
    have hgmeanzero : volumeAverage (cubeSet Q) (fun x => -c * g₀ x) = 0 := by
      rw [volumeAverage_const_mul, volumeAverage_cubeSet_eq_cubeAverage', hg₀mean, mul_zero]
    have hGle : vecCubeLpENorm Q 2 (euclideanGradient g₀) ≤ ENNReal.ofReal (n + δ) := by
      have hnorm : ‖G‖ ≤ n + δ := by
        have hGA : G = A + E := by rw [hEeq]; abel
        calc ‖G‖ = ‖A + E‖ := by rw [hGA]
          _ ≤ ‖A‖ + ‖E‖ := norm_add_le _ _
          _ ≤ n + δ := by rw [hAnorm]; linarith only [hEnorm]
      have hGtoReal : (vecCubeLpENorm Q 2 (euclideanGradient g₀)).toReal ≤ n + δ := by
        rw [← norm_toLp_hilbertifyVecField hGmem, ← hGdef]
        exact hnorm
      have hGne : vecCubeLpENorm Q 2 (euclideanGradient g₀) ≠ ⊤ := hGmem.eLpNorm_lt_top.ne
      rw [← ENNReal.ofReal_toReal hGne]
      exact ENNReal.ofReal_le_ofReal hGtoReal
    have hgrad : ∀ x : Vec d, euclideanGradient (fun y => -c * g₀ y) x
        = (-c) • euclideanGradient g₀ x :=
      euclideanGradient_const_mul hg₀smooth (-c)
    have hgradle : vecCubeLpENorm Q 2 (euclideanGradient (fun x => -c * g₀ x)) ≤ 1 := by
        have hfun : euclideanGradient (fun y => -c * g₀ y)
            = fun x => (-c) • euclideanGradient g₀ x := funext hgrad
        rw [hfun, vecCubeLpENorm_const_smul]
        have hcnorm : ‖(-c : ℝ)‖ₑ = ENNReal.ofReal c := by
          rw [Real.enorm_eq_ofReal_abs, abs_neg, abs_of_nonneg hcpos.le]
        rw [hcnorm]
        calc ENNReal.ofReal c * vecCubeLpENorm Q 2 (euclideanGradient g₀)
            ≤ ENNReal.ofReal c * ENNReal.ofReal (n + δ) := mul_le_mul_right hGle _
          _ = ENNReal.ofReal (c * (n + δ)) := (ENNReal.ofReal_mul hcpos.le).symm
          _ = 1 := by
              rw [hcdef, inv_mul_cancel₀ hden.ne', ENNReal.ofReal_one]
    have htest : IsVecHatTestField Q (fun x => -c * g₀ x) :=
      { contDiff := hgsmooth
        meanZero := hgmeanzero
        gradient_le_one := hgradle }
    -- the pairing at the test function
    have hpair : volumeAverage (cubeSet Q)
        (vecGradientPairingDensity F (fun x => -c * g₀ x)) =
        c * volumeAverage (cubeSet Q)
          (fun x => vecDot (w.toH1Function.grad x) (euclideanGradient g₀ x)) := by
      rw [volumeAverage_vecGradientPairingDensity_eq_of_isCubeNeumannResponse hw hgsmooth]
      have hpt : ∀ x : Vec d,
          vecDot (w.toH1Function.grad x) (euclideanGradient (fun y => -c * g₀ y) x) =
            (-c) * vecDot (w.toH1Function.grad x) (euclideanGradient g₀ x) := by
        intro x
        rw [hgrad x, vecDot_const_smul_right]
      rw [funext hpt, volumeAverage_const_mul]
      ring
    have hinner : volumeAverage (cubeSet Q)
        (fun x => vecDot (w.toH1Function.grad x) (euclideanGradient g₀ x))
        = (inner ℝ A G : ℝ) := (inner_toLp_hilbertifyVecField hAmem hGmem).symm
    have hlower : n * n - n * δ ≤ (inner ℝ A G : ℝ) := by
      have hsplit : (inner ℝ A G : ℝ) = (inner ℝ A A : ℝ) + (inner ℝ A E : ℝ) := by
        rw [hEeq, inner_sub_right]
        ring
      have hAA : (inner ℝ A A : ℝ) = n * n := by
        rw [real_inner_self_eq_norm_mul_norm, hAnorm]
      have hAE : -(n * δ) ≤ (inner ℝ A E : ℝ) := by
        have hcs : |(inner ℝ A E : ℝ)| ≤ ‖A‖ * ‖E‖ := abs_real_inner_le_norm A E
        have hle : ‖A‖ * ‖E‖ ≤ n * δ := by
          rw [hAnorm]
          exact mul_le_mul_of_nonneg_left hEnorm hn0
        have habs := abs_le.1 (le_trans hcs hle)
        linarith only [habs.1]
      rw [hsplit, hAA]
      linarith only [hAE]
    have hfinal : n - 2 * δ ≤ volumeAverage (cubeSet Q)
        (vecGradientPairingDensity F (fun x => -c * g₀ x)) := by
      rw [hpair, hinner]
      have hstep : n - 2 * δ ≤ c * (n * n - n * δ) := by
        have hdiv : c * (n * n - n * δ) = (n * n - n * δ) / (n + δ) := by
          rw [hcdef, div_eq_inv_mul]
        have hsq : 0 ≤ 2 * (δ * δ) := by positivity
        have hexp : n * n - n * δ - (n - 2 * δ) * (n + δ) = 2 * (δ * δ) := by ring
        rw [hdiv, le_div_iff₀ hden]
        linarith only [hsq, hexp]
      exact le_trans hstep (mul_le_mul_of_nonneg_left hlower hcpos.le)
    calc ENNReal.ofReal (n - 2 * δ)
        ≤ ENNReal.ofReal (volumeAverage (cubeSet Q)
            (vecGradientPairingDensity F (fun x => -c * g₀ x))) :=
          ENNReal.ofReal_le_ofReal hfinal
      _ ≤ vecHatNegENorm Q F := le_vecHatNegENorm F htest
  by_contra hcon
  push Not at hcon
  have hHtop : vecHatNegENorm Q F ≠ ⊤ := by
    intro htop
    rw [htop] at hcon
    exact absurd hNtop (by simp [top_le_iff.1 (le_of_lt hcon)])
  set h : ℝ := (vecHatNegENorm Q F).toReal with hhdef
  have hh0 : 0 ≤ h := ENNReal.toReal_nonneg
  have hhn : h < n := by
    rw [hhdef, hndef]
    exact (ENNReal.toReal_lt_toReal hHtop hNtop).2 hcon
  have hδpos : 0 < (n - h) / 3 := by linarith only [hhn]
  have hk := key ((n - h) / 3) hδpos
  rw [← ENNReal.ofReal_toReal hHtop, ← hhdef] at hk
  have := (ENNReal.ofReal_le_ofReal_iff hh0).1 hk
  linarith only [this, hhn]

/-- **The exact `Ĥ̲^{-1}` identity for a prescribed-flux Neumann response**, the
form used by `e.abstract.response.ND.weak`. -/
theorem vecHatNegENorm_eq_of_isCubeNeumannResponse {Q : TriadicCube d}
    {F : Vec d → Vec d} {w : H1MeanZeroFunction (openCubeSet Q)}
    (hw : IsCubeNeumannResponse Q F w) :
    vecHatNegENorm Q F = vecCubeLpENorm Q 2 w.toH1Function.grad :=
  le_antisymm (vecHatNegENorm_le_of_isCubeNeumannResponse hw)
    (vecCubeLpENorm_le_vecHatNegENorm_of_isCubeNeumannResponse hw)

/-! ## The energy gap in the hatted negative norm -/

private theorem hilbertifyVecField_sub (a b : Vec d → Vec d) :
    hilbertifyVecField (fun x => a x - b x)
      = hilbertifyVecField a - hilbertifyVecField b := by
  funext x
  exact map_sub (HilbertVec.linearEquivVec d).symm _ _

/-- **The gradient of the difference of the two responses is dominated in
`L̲²(Q)` by the hatted negative norm of the flux.** The mixed term of Step 1
gives `⟪∇w_N, ∇w_D⟫ = ‖∇w_D‖²`, so the exact gap identity
`e.energy.quadratic.N.D` reads `‖∇w_N − ∇w_D‖² = ‖∇w_N‖² − ‖∇w_D‖²`; dropping
the subtracted energy and applying the `Ĥ̲^{-1}` identity finishes. -/
theorem vecCubeLpENorm_grad_sub_le_vecHatNegENorm {Q : TriadicCube d}
    {F : Vec d → Vec d} {wN : H1MeanZeroFunction (openCubeSet Q)}
    {wD : H10Function (openCubeSet Q)}
    (hN : IsCubeNeumannResponse Q F wN) (hD : IsCubeDirichletResponse Q F wD) :
    vecCubeLpENorm Q 2 (fun x => wN.toH1Function.grad x - wD.toH1Function.grad x) ≤
      vecHatNegENorm Q F := by
  have hNmem : MemLp (hilbertifyVecField wN.toH1Function.grad) 2 (normalizedCubeMeasure Q) :=
    memLp_hilbertifyVecField_normalizedCubeMeasure wN.toH1Function.grad_memVectorL2
  have hDmem : MemLp (hilbertifyVecField wD.toH1Function.grad) 2 (normalizedCubeMeasure Q) :=
    memLp_hilbertifyVecField_normalizedCubeMeasure wD.toH1Function.grad_memVectorL2
  have hVmem : MemLp (hilbertifyVecField
      (fun x => wN.toH1Function.grad x - wD.toH1Function.grad x)) 2
      (normalizedCubeMeasure Q) := by
    rw [hilbertifyVecField_sub]
    exact hNmem.sub hDmem
  set AN := hNmem.toLp (hilbertifyVecField wN.toH1Function.grad) with hANdef
  set AD := hDmem.toLp (hilbertifyVecField wD.toH1Function.grad) with hADdef
  set AV := hVmem.toLp (hilbertifyVecField
    (fun x => wN.toH1Function.grad x - wD.toH1Function.grad x)) with hAVdef
  have hAVeq : AV = AN - AD := by
    rw [hAVdef, hANdef, hADdef, ← MemLp.toLp_sub]
    exact MemLp.toLp_congr _ _
      (Filter.Eventually.of_forall
        (congrFun (hilbertifyVecField_sub wN.toH1Function.grad wD.toH1Function.grad)))
  -- the mixed term of Step 1
  have hmixed : (inner ℝ AN AD : ℝ) = (inner ℝ AD AD : ℝ) := by
    rw [inner_toLp_hilbertifyVecField hNmem hDmem,
      inner_toLp_hilbertifyVecField hDmem hDmem,
      volumeAverage_cubeSet_eq_openCubeSet, volumeAverage_cubeSet_eq_openCubeSet,
      volumeAverage, volumeAverage, setIntegral_vecDot_grad_neumann_dirichlet hN hD]
  have hsq : ‖AV‖ ^ 2 ≤ ‖AN‖ ^ 2 := by
    have hexp : ‖AN - AD‖ ^ 2 = ‖AN‖ ^ 2 - 2 * (inner ℝ AN AD : ℝ) + ‖AD‖ ^ 2 :=
      norm_sub_sq_real AN AD
    have hADsq : (inner ℝ AD AD : ℝ) = ‖AD‖ ^ 2 := real_inner_self_eq_norm_sq AD
    have hnonneg : (0 : ℝ) ≤ ‖AD‖ ^ 2 := sq_nonneg _
    rw [hAVeq, hexp, hmixed, hADsq]
    linarith only [hnonneg]
  have hnorm : ‖AV‖ ≤ ‖AN‖ := by
    calc ‖AV‖ = Real.sqrt (‖AV‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (‖AN‖ ^ 2) := Real.sqrt_le_sqrt hsq
      _ = ‖AN‖ := Real.sqrt_sq (norm_nonneg _)
  rw [norm_toLp_hilbertifyVecField hVmem, norm_toLp_hilbertifyVecField hNmem] at hnorm
  rw [vecHatNegENorm_eq_of_isCubeNeumannResponse hN]
  exact (ENNReal.toReal_le_toReal hVmem.eLpNorm_lt_top.ne hNmem.eLpNorm_lt_top.ne).1 hnorm


/-! ## The scale-correct normalized Poincaré-Wirtinger estimate -/

private theorem cubeLpENorm_eq_smul_openCube {E : Type*} [NormedAddCommGroup E]
    (Q : TriadicCube d) (f : Vec d → E) :
    Section2.Norms.cubeLpENorm Q 2 f
      = ENNReal.ofReal ((cubeVolume Q)⁻¹) ^ (1 / (2 : ℝ≥0∞)).toReal *
        eLpNorm f 2 (volumeMeasureOn (openCubeSet Q)) := by
  rw [Section2.Norms.cubeLpENorm,
    normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet,
    eLpNorm_smul_measure_of_ne_zero (ENNReal.ofReal_pos.mpr (inv_pos.mpr (cubeVolume_pos Q))).ne', smul_eq_mul]

/-- **The normalized cube Poincaré-Wirtinger estimate with its explicit
dimensional constant.** CoarseGraining's `scaledTranslatedCubeMeanZeroH1CoerciveEstimate`
has constant `3^{scale} C(d)` for the *unnormalized* `L²(Q)` norms; both sides of
that estimate carry the same volume normalization, so dividing by the side length
`3^{scale}` leaves the dimensional constant
`(originCubeMeanZeroH1CoerciveEstimate d 0).constant` alone. This is the factor
`3^{-M}` of the first standard estimate of Step 4. -/
theorem cubeScaleFactor_inv_mul_cubeLpENorm_subAverage_le (Q : TriadicCube d)
    (v : H1Function (openCubeSet Q)) :
    ENNReal.ofReal ((cubeScaleFactor Q)⁻¹) *
        Section2.Norms.cubeLpENorm Q 2 v.subAverage.toFun ≤
      ENNReal.ofReal ((originCubeMeanZeroH1CoerciveEstimate d 0).constant) *
        vecCubeLpENorm Q 2 v.grad := by
  have hs : 0 < cubeScaleFactor Q := by
    rw [cubeScaleFactor]
    positivity
  have hK : ENNReal.ofReal ((cubeVolume Q)⁻¹) ^ (1 / (2 : ℝ≥0∞)).toReal ≠ ⊤ :=
    (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top).ne
  have hK0 : ENNReal.ofReal ((cubeVolume Q)⁻¹) ^ (1 / (2 : ℝ≥0∞)).toReal ≠ 0 := by
    refine (ENNReal.rpow_pos ?_ ENNReal.ofReal_ne_top).ne'
    exact ENNReal.ofReal_pos.2 (inv_pos.2 (cubeVolume_pos Q))
  have hXmem : MemLp v.subAverage.toFun 2 (volumeMeasureOn (openCubeSet Q)) :=
    v.subAverage.memL2
  have hYmem : MemLp (hilbertifyVecField v.grad) 2 (volumeMeasureOn (openCubeSet Q)) :=
    memHilbertVectorL2_hilbertifyVecField v.grad_memVectorL2
  set X := eLpNorm v.subAverage.toFun 2 (volumeMeasureOn (openCubeSet Q)) with hXdef
  set Y := eLpNorm (hilbertifyVecField v.grad) 2 (volumeMeasureOn (openCubeSet Q)) with hYdef
  have hXtop : X ≠ ⊤ := hXmem.eLpNorm_lt_top.ne
  have hYtop : Y ≠ ⊤ := hYmem.eLpNorm_lt_top.ne
  -- the upstream coercive estimate, read through the Euclidean magnitude
  have hpoincare : X.toReal ≤
      cubeScaleFactor Q * (originCubeMeanZeroH1CoerciveEstimate d 0).constant * Y.toReal := by
    have hbound := (scaledTranslatedCubeMeanZeroH1CoerciveEstimate Q).bound_subAverage v
    rw [scaledTranslatedCubeMeanZeroH1CoerciveEstimate_constant] at hbound
    have hgrad : ‖v.gradToVectorL2‖ ≤ Y.toReal := by
      refine le_trans (v.norm_gradToVectorL2_le_norm_gradToHilbertVectorL2) ?_
      rw [hYdef]
      exact le_of_eq (Lp.norm_toLp _ hYmem)
    have hvalue : X.toReal = v.toMeanZero.valueL2Norm := by
      rw [hXdef]
      exact (Lp.norm_toLp _ hXmem).symm
    have hcnn : 0 ≤ cubeScaleFactor Q * (originCubeMeanZeroH1CoerciveEstimate d 0).constant :=
      mul_nonneg hs.le (originCubeMeanZeroH1CoerciveEstimate d 0).constant_nonneg
    rw [hvalue]
    exact le_trans hbound (mul_le_mul_of_nonneg_left hgrad hcnn)
  have hreal : (cubeScaleFactor Q)⁻¹ * X.toReal ≤
      (originCubeMeanZeroH1CoerciveEstimate d 0).constant * Y.toReal := by
    have hmul := mul_le_mul_of_nonneg_left hpoincare (le_of_lt (inv_pos.2 hs))
    have hid : (cubeScaleFactor Q)⁻¹ *
        (cubeScaleFactor Q * (originCubeMeanZeroH1CoerciveEstimate d 0).constant * Y.toReal)
        = (originCubeMeanZeroH1CoerciveEstimate d 0).constant * Y.toReal := by
      field_simp
    rw [hid] at hmul
    exact hmul
  have hENN : ENNReal.ofReal ((cubeScaleFactor Q)⁻¹) * X ≤
      ENNReal.ofReal ((originCubeMeanZeroH1CoerciveEstimate d 0).constant) * Y := by
    rw [← ENNReal.ofReal_toReal hXtop, ← ENNReal.ofReal_toReal hYtop,
      ← ENNReal.ofReal_mul (le_of_lt (inv_pos.2 hs)),
      ← ENNReal.ofReal_mul (originCubeMeanZeroH1CoerciveEstimate d 0).constant_nonneg]
    exact ENNReal.ofReal_le_ofReal hreal
  rw [cubeLpENorm_eq_smul_openCube, vecCubeLpENorm, cubeLpENorm_eq_smul_openCube,
    ← hXdef, ← hYdef]
  calc ENNReal.ofReal ((cubeScaleFactor Q)⁻¹) *
        (ENNReal.ofReal ((cubeVolume Q)⁻¹) ^ (1 / (2 : ℝ≥0∞)).toReal * X)
      = ENNReal.ofReal ((cubeVolume Q)⁻¹) ^ (1 / (2 : ℝ≥0∞)).toReal *
          (ENNReal.ofReal ((cubeScaleFactor Q)⁻¹) * X) := by ring
    _ ≤ ENNReal.ofReal ((cubeVolume Q)⁻¹) ^ (1 / (2 : ℝ≥0∞)).toReal *
          (ENNReal.ofReal ((originCubeMeanZeroH1CoerciveEstimate d 0).constant) * Y) :=
        mul_le_mul_right hENN _
    _ = ENNReal.ofReal ((originCubeMeanZeroH1CoerciveEstimate d 0).constant) *
          (ENNReal.ofReal ((cubeVolume Q)⁻¹) ^ (1 / (2 : ℝ≥0∞)).toReal * Y) := by ring

/-- **The `Ĥ̲^{-1}` half of Step 4 of `l.abstract.response.fields`**:
with `v` the difference of the prescribed-flux Neumann and the
Dirichlet responses of the same flux,
`3^{-M}‖v − (v)_{cu_M}‖_{L̲²(cu_M)} ≤ C(d) ‖F‖_{Ĥ̲^{-1}(cu_M)}`. The constant is
the dimensional Poincaré-Wirtinger constant of the unit centered cube. Step 4
applies this at the centered flux `F₀ = F − (F)_{cu_M}`. -/
theorem cubeScaleFactor_inv_mul_cubeLpENorm_response_difference_le_vecHatNegENorm
    {Q : TriadicCube d} {F : Vec d → Vec d} {wN : H1MeanZeroFunction (openCubeSet Q)}
    {wD : H10Function (openCubeSet Q)}
    (hN : IsCubeNeumannResponse Q F wN) (hD : IsCubeDirichletResponse Q F wD) :
    ENNReal.ofReal ((cubeScaleFactor Q)⁻¹) *
        Section2.Norms.cubeLpENorm Q 2
          (wN.toH1Function - wD.toH1Function).subAverage.toFun ≤
      ENNReal.ofReal ((originCubeMeanZeroH1CoerciveEstimate d 0).constant) *
        vecHatNegENorm Q F := by
  refine le_trans
    (cubeScaleFactor_inv_mul_cubeLpENorm_subAverage_le Q
      (wN.toH1Function - wD.toH1Function)) ?_
  refine mul_le_mul_right (le_trans (le_of_eq ?_)
    (vecCubeLpENorm_grad_sub_le_vecHatNegENorm hN hD)) _
  refine congrArg (vecCubeLpENorm Q 2) ?_
  rw [H1Function.sub_grad]

end

end ResponseFields
end Section3
end SuperdiffusionCLT
