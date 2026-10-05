/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.ResponseFields.AprioriAssembly

/-!
# The weak Neumann-Dirichlet comparison, and the a priori anchor from its bridges

The last of the four
deterministic estimates of `l.abstract.response.fields` in the paper is:

> `‖∇w_N − ∇w_D‖_{L̲²(cu_M)} ≤ C ‖F − (F)_{cu_M}‖_{Ĥ̲^{-1}(cu_M)}^{1/5}
> ‖F − (F)_{cu_M}‖_{L̲⁴(cu_M)}^{4/5} + C |(F)_{cu_M}|`,

and Step 4 of its proof derives it from Step 3's harmonic
interpolation `e.abstract.harmonic.interpolation` together
with two "standard estimates".

## What is assembled here

`exists_responseDifferenceL2Clause` performs Step 4 in full:

* the centring `F₀ = F − (F)_{cu_M}`, whose Dirichlet response is `w_D`
  (`isCubeDirichletResponse_sub_const`) and whose prescribed-flux Neumann
  response is `w_N + (F)_{cu_M}·x` (`isCubeNeumannResponse_sub_const`);
* the harmonicity of `v = w_N + (F)_{cu_M}·x − w_D` in the weak form the
  interpolation consumes, `∫_{cu_M} ∇v·∇φ = 0` for every `φ ∈ H¹₀(cu_M)`
  (`setIntegral_vecDot_grad_responseDifference_eq_zero`);
* the `Ĥ̲^{-1}` half of the standard estimates,
  `cubeScaleFactor_inv_mul_cubeLpENorm_response_difference_le_vecHatNegENorm`;
* the `L̲⁴` half of the same display,
  `exists_cubeResponseDifferenceL4Estimate` at the centred flux; and
* the algebra of the last display of Step 4,
  `∇w_N − ∇w_D = ∇v − (F)_{cu_M}`.

Step 3 itself enters as the explicit hypothesis `hharm`, in the printed shape.

`exists_dirichletHsClause` carries the `H̲^{1/2}` clause
(`e.abstract.response.Hhalf`) at the scale `M` and discharges
its `⊤` branch; `Sobolev/ResponseHalfInterpolation.lean` proves the estimate on
the unit cube only, and the dilation to `cu_M` is not available here.

The four clauses, supplied by `exists_responseGradientL8Clause`,
`exists_dirichletHessianL8Clause'`, `exists_dirichletHsClause` and
`exists_responseDifferenceL2Clause`, are assembled under a single constant `C` in
`responseFields_apriori_orderZero_of_clauses` of `AprioriAssemblyE.lean`.
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

/-! ## Bookkeeping -/

private theorem add_one_ne_zero' (C : ℝ≥0∞) : C + 1 ≠ 0 := by
  intro h
  rw [add_eq_zero] at h
  exact one_ne_zero h.2

private theorem one_le_add_one (C : ℝ≥0∞) : (1 : ℝ≥0∞) ≤ C + 1 := le_add_self

/-- The `L̲²(Q)` realization of an `L²` field of the open cube. -/
private theorem memLp_two_hilbertify {Q : TriadicCube d} {F : Vec d → Vec d}
    (hF : MemVectorL2 (openCubeSet Q) F) :
    MemLp (hilbertifyVecField F) 2 (normalizedCubeMeasure Q) := by
  rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
  exact (memHilbertVectorL2_hilbertifyVecField hF).smul_measure ENNReal.ofReal_ne_top

/-- The `L̲^q(Q)` size of a constant field is the Euclidean magnitude of the
constant, the cube measure being a probability measure. -/
theorem vecCubeLpENorm_const (Q : TriadicCube d) {q : ℝ≥0∞} (hq0 : q ≠ 0)
    (c : Vec d) :
    vecCubeLpENorm Q q (fun _ => c) = ‖HilbertVec.ofVec c‖ₑ := by
  have := isProbabilityMeasure_normalizedCubeMeasure Q
  have h : hilbertifyVecField (fun _ : Vec d => c) =
      fun _ : Vec d => HilbertVec.ofVec c := rfl
  rw [vecCubeLpENorm, Section2.Norms.cubeLpENorm, h,
    eLpNorm_const _ hq0 (NeZero.ne' (normalizedCubeMeasure Q)).symm]
  simp

private theorem setIntegral_vecDot_sub_left {Q : TriadicCube d}
    {a b psi : Vec d → Vec d}
    (ha : MemVectorL2 (openCubeSet Q) a) (hb : MemVectorL2 (openCubeSet Q) b)
    (hpsi : MemVectorL2 (openCubeSet Q) psi) :
    ∫ x in openCubeSet Q, vecDot (a x - b x) (psi x) =
      (∫ x in openCubeSet Q, vecDot (a x) (psi x)) -
        ∫ x in openCubeSet Q, vecDot (b x) (psi x) := by
  have hsplit : ∀ x : Vec d,
      vecDot (a x - b x) (psi x) = vecDot (a x) (psi x) - vecDot (b x) (psi x) := by
    intro x
    simp only [vecDot, Pi.sub_apply, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [setIntegral_congr_fun (measurableSet_openCubeSet Q) (fun x _ => hsplit x),
    integral_sub (integrableOn_vecDot_of_memVectorL2 ha hpsi)
      (integrableOn_vecDot_of_memVectorL2 hb hpsi)]

/-! ## The harmonicity of the difference of the two responses -/

/-- **`v = w_N − w_D` is harmonic in the cube**: the difference of
the prescribed-flux Neumann and the Dirichlet response of one flux solves
`Δv = 0` in the weak form the interpolation of Step 3 consumes, namely
`∫_Q ∇v·∇φ = 0` for every `φ ∈ H¹₀(Q)`.

Both response equations have right-hand side `−∫_Q F·∇φ` at the same test
gradient: an `H¹₀` test function is an admissible Neumann test after its cube
average is subtracted, which does not change its gradient. -/
theorem setIntegral_vecDot_grad_responseDifference_eq_zero {Q : TriadicCube d}
    {F : Vec d → Vec d} {wD : H10Function (openCubeSet Q)}
    {wN : H1MeanZeroFunction (openCubeSet Q)}
    (hD : IsCubeDirichletResponse Q F wD) (hN : IsCubeNeumannResponse Q F wN)
    (φ : H10Function (openCubeSet Q)) :
    ∫ x in openCubeSet Q,
        vecDot ((wN.toH1Function - wD.toH1Function).grad x)
          (φ.toH1Function.grad x) = 0 := by
  have hgradeq : (φ.toH1Function.toMeanZero).toH1Function.grad =
      φ.toH1Function.grad := funext fun x => H1Function.toMeanZero_grad _ x
  have hNphi := hN φ.toH1Function.toMeanZero
  rw [hgradeq] at hNphi
  rw [H1Function.sub_grad,
    setIntegral_vecDot_sub_left wN.toH1Function.grad_memVectorL2
      wD.toH1Function.grad_memVectorL2 φ.toH1Function.grad_memVectorL2,
    hNphi, hD φ, sub_self]

/-! ## Step 4 of the proof, at one cube -/

/-- **Step 4 of the proof of `l.abstract.response.fields`** at
one triadic cube, with the harmonic interpolation of Step 3 and the `L̲⁴`
endpoint of Step 2 as hypotheses.

The centred flux `F₀ = F − (F)_Q` has `w_D` as its Dirichlet response and
`w_N + (F)_Q·x` as its prescribed-flux Neumann response; their difference `v` is
harmonic, the interpolation applies to it, the two standard estimates
bound the two factors, and `∇w_N − ∇w_D = ∇v − (F)_Q` transfers the
bound to the left-hand side of `e.abstract.response.ND.weak`. -/
private theorem responseDifference_step4 {Q : TriadicCube d} {Cint C4 : ℝ≥0∞}
    {F : Vec d → Vec d} {wD : H10Function (openCubeSet Q)}
    {wN : H1MeanZeroFunction (openCubeSet Q)}
    (hD : IsCubeDirichletResponse Q F wD) (hN : IsCubeNeumannResponse Q F wN)
    (hmem : MemLp
      (hilbertifyVecField (fun x => F x - volumeAverageVec (cubeSet Q) F)) 4
      (normalizedCubeMeasure Q))
    (hharm : ∀ v : H1Function (openCubeSet Q),
      (∀ φ : H10Function (openCubeSet Q),
        ∫ x in openCubeSet Q, vecDot (v.grad x) (φ.toH1Function.grad x) = 0) →
      vecCubeLpENorm Q 2 v.grad ≤
        Cint * (ENNReal.ofReal ((cubeScaleFactor Q)⁻¹) *
            Section2.Norms.cubeLpENorm Q 2 v.subAverage.toFun) ^ ((1 : ℝ) / 5) *
          (vecCubeLpENorm Q 4 v.grad) ^ ((4 : ℝ) / 5))
    (hC4 : ∀ G : Vec d → Vec d,
      MemLp (hilbertifyVecField G) 4 (normalizedCubeMeasure Q) →
      ∀ (u : H10Function (openCubeSet Q)) (w : H1MeanZeroFunction (openCubeSet Q)),
        IsCubeDirichletResponse Q G u → IsCubeNeumannResponse Q G w →
        vecCubeLpENorm Q 4
            (fun x => w.toH1Function.grad x - u.toH1Function.grad x) ≤
          C4 * vecCubeLpENorm Q 4 G) :
    vecCubeLpENorm Q 2
        (fun x => wN.toH1Function.grad x - wD.toH1Function.grad x) ≤
      Cint * (ENNReal.ofReal ((originCubeMeanZeroH1CoerciveEstimate d 0).constant)) ^
              ((1 : ℝ) / 5) * C4 ^ ((4 : ℝ) / 5) *
          (vecHatNegENorm Q (fun x => F x - volumeAverageVec (cubeSet Q) F)) ^
            ((1 : ℝ) / 5) *
          (vecCubeLpENorm Q 4 (fun x => F x - volumeAverageVec (cubeSet Q) F)) ^
            ((4 : ℝ) / 5) +
        ‖HilbertVec.ofVec (volumeAverageVec (cubeSet Q) F)‖ₑ := by
  set c : Vec d := volumeAverageVec (cubeSet Q) F with hc
  set F0 : Vec d → Vec d := fun x => F x - c with hF0
  set Cpw : ℝ≥0∞ :=
    ENNReal.ofReal ((originCubeMeanZeroH1CoerciveEstimate d 0).constant) with hCpw
  -- the centred flux and its two responses
  have hF04 : MemLp F0 4 (normalizedCubeMeasure Q) := memLp_hilbertifyVecField_iff.1 hmem
  have hF02 : MemLp F0 2 (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_mono (by norm_num) hF04
  have hF0L2 : MemVectorL2 (openCubeSet Q) F0 :=
    memVectorL2_of_memLp_two_normalizedCubeMeasure hF02
  have hFL2 : MemVectorL2 (openCubeSet Q) F := by
    have hsum := hF0L2.add (memVectorL2_const (U := openCubeSet Q) c)
    have hfun : (F0 + fun _ : Vec d => c) = F := by
      funext x
      simp [hF0]
    rwa [hfun] at hsum
  have hD0 : IsCubeDirichletResponse Q F0 wD :=
    isCubeDirichletResponse_sub_const hFL2 hD c
  have hN0 : IsCubeNeumannResponse Q F0 (wN + linearH1MeanZeroFunction Q c) :=
    isCubeNeumannResponse_sub_const hFL2 hN c
  have hvgrad : (((wN + linearH1MeanZeroFunction Q c).toH1Function -
        wD.toH1Function).grad) =
      fun x => (wN + linearH1MeanZeroFunction Q c).toH1Function.grad x -
        wD.toH1Function.grad x := H1Function.sub_grad _ _
  -- Step 3 at the harmonic difference
  have hstep3 := hharm ((wN + linearH1MeanZeroFunction Q c).toH1Function - wD.toH1Function)
    (fun φ => setIntegral_vecDot_grad_responseDifference_eq_zero hD0 hN0 φ)
  -- the `Ĥ̲^{-1}` half of the standard estimates
  have hHm1 :=
    cubeScaleFactor_inv_mul_cubeLpENorm_response_difference_le_vecHatNegENorm hN0 hD0
  -- the `L̲⁴` half of the standard estimates
  have hL4 := hC4 F0 hmem wD (wN + linearH1MeanZeroFunction Q c) hD0 hN0
  rw [← hvgrad] at hL4
  have h1 : (ENNReal.ofReal ((cubeScaleFactor Q)⁻¹) *
        Section2.Norms.cubeLpENorm Q 2
          (((wN + linearH1MeanZeroFunction Q c).toH1Function -
            wD.toH1Function)).subAverage.toFun) ^ ((1 : ℝ) / 5) ≤
      (Cpw * vecHatNegENorm Q F0) ^ ((1 : ℝ) / 5) :=
    ENNReal.rpow_le_rpow hHm1 (by norm_num)
  have h2 : (vecCubeLpENorm Q 4
        (((wN + linearH1MeanZeroFunction Q c).toH1Function -
          wD.toH1Function)).grad) ^ ((4 : ℝ) / 5) ≤
      (C4 * vecCubeLpENorm Q 4 F0) ^ ((4 : ℝ) / 5) :=
    ENNReal.rpow_le_rpow hL4 (by norm_num)
  have hmain : vecCubeLpENorm Q 2
        (((wN + linearH1MeanZeroFunction Q c).toH1Function - wD.toH1Function)).grad ≤
      Cint * Cpw ^ ((1 : ℝ) / 5) * C4 ^ ((4 : ℝ) / 5) *
        (vecHatNegENorm Q F0) ^ ((1 : ℝ) / 5) *
        (vecCubeLpENorm Q 4 F0) ^ ((4 : ℝ) / 5) := by
    refine le_trans hstep3 (le_trans (mul_le_mul' (mul_le_mul' (le_refl Cint) h1) h2)
      (le_of_eq ?_))
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 5),
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ (4 : ℝ) / 5)]
    ring
  -- the last display of Step 4, `∇w_N − ∇w_D = ∇v − (F)_Q`
  have hdiff : (fun x => wN.toH1Function.grad x - wD.toH1Function.grad x) =
      fun x => ((wN + linearH1MeanZeroFunction Q c).toH1Function -
        wD.toH1Function).grad x + (-c) := by
    funext x
    rw [hvgrad]
    simp only [add_linearH1MeanZeroFunction_grad]
    abel
  have hmeasv : AEStronglyMeasurable
      (hilbertifyVecField (((wN + linearH1MeanZeroFunction Q c).toH1Function -
        wD.toH1Function)).grad) (normalizedCubeMeasure Q) :=
    (memLp_two_hilbertify (((wN + linearH1MeanZeroFunction Q c).toH1Function -
      wD.toH1Function)).grad_memVectorL2).aestronglyMeasurable
  have hmeasc : AEStronglyMeasurable (hilbertifyVecField (fun _ : Vec d => -c))
      (normalizedCubeMeasure Q) :=
    (memLp_two_hilbertify
      (memVectorL2_const (U := openCubeSet Q) (-c))).aestronglyMeasurable
  have htri : vecCubeLpENorm Q 2
        (fun x => wN.toH1Function.grad x - wD.toH1Function.grad x) ≤
      vecCubeLpENorm Q 2 (((wN + linearH1MeanZeroFunction Q c).toH1Function -
        wD.toH1Function)).grad + ‖HilbertVec.ofVec c‖ₑ := by
    rw [hdiff]
    refine le_trans (vecCubeLpENorm_add_le (by norm_num) hmeasv hmeasc) ?_
    rw [vecCubeLpENorm_const Q (by norm_num) (-c)]
    simp
  exact le_trans htri (add_le_add hmain le_rfl)

/-! ## `e.abstract.response.ND.weak` -/

/-- **The weak Neumann-Dirichlet comparison of `l.abstract.response.fields`**
(`e.abstract.response.ND.weak`), in the shape of the fourth
conjunct of the statement `responseFields_apriori_orderZero`.

`hharm` is Step 3 of the proof, `e.abstract.harmonic.interpolation`, stated at the
scale `M` for a function harmonic in the weak sense of
`setIntegral_vecDot_grad_responseDifference_eq_zero`, with `3^{-M}` written
as `(cubeScaleFactor (cu_M))⁻¹` and `v − (v)_{cu_M}` as `v.subAverage.toFun`.

`hjunk` is the branch of the conjunct on which Step 4 does not run: the centred
flux is not `L̲⁴(cu_M)`-measurable while the right-hand side is not forced to
be `⊤`, that is, either its `L̲⁴(cu_M)` size is finite or its `Ĥ̲^{-1}(cu_M)`
size vanishes. The complementary branch, an infinite `L̲⁴` size against a
non-zero `Ĥ̲^{-1}` size, is discharged in the proof. -/
theorem exists_responseDifferenceL2Clause (hd : 2 ≤ d)
    (Cint : ℝ≥0∞) (hCint : Cint < ⊤)
    (hharm : ∀ (M : ℕ) (v : H1Function (openCubeSet (originCube d (M : ℤ)))),
      (∀ φ : H10Function (openCubeSet (originCube d (M : ℤ))),
        ∫ x in openCubeSet (originCube d (M : ℤ)),
          vecDot (v.grad x) (φ.toH1Function.grad x) = 0) →
      vecCubeLpENorm (originCube d (M : ℤ)) 2 v.grad ≤
        Cint *
            (ENNReal.ofReal ((cubeScaleFactor (originCube d (M : ℤ)))⁻¹) *
              Section2.Norms.cubeLpENorm (originCube d (M : ℤ)) 2
                v.subAverage.toFun) ^ ((1 : ℝ) / 5) *
            (vecCubeLpENorm (originCube d (M : ℤ)) 4 v.grad) ^ ((4 : ℝ) / 5))
    (hjunk : ∀ (M : ℕ) (F : Vec d → Vec d)
      (wD : H10Function (openCubeSet (originCube d (M : ℤ))))
      (wN : H1MeanZeroFunction (openCubeSet (originCube d (M : ℤ)))),
      IsCubeDirichletResponse (originCube d (M : ℤ)) F wD →
      IsCubeNeumannResponse (originCube d (M : ℤ)) F wN →
      ¬ MemLp (hilbertifyVecField (fun x => F x -
            volumeAverageVec (cubeSet (originCube d (M : ℤ))) F)) 4
          (normalizedCubeMeasure (originCube d (M : ℤ))) →
      (vecCubeLpENorm (originCube d (M : ℤ)) 4
            (fun x => F x -
              volumeAverageVec (cubeSet (originCube d (M : ℤ))) F) < ⊤ ∨
          vecHatNegENorm (originCube d (M : ℤ))
            (fun x => F x -
              volumeAverageVec (cubeSet (originCube d (M : ℤ))) F) = 0) →
      vecCubeLpENorm (originCube d (M : ℤ)) 2
          (fun x => wN.toH1Function.grad x - wD.toH1Function.grad x) ≤
        (vecHatNegENorm (originCube d (M : ℤ))
              (fun x => F x -
                volumeAverageVec (cubeSet (originCube d (M : ℤ))) F)) ^ ((1 : ℝ) / 5) *
            (vecCubeLpENorm (originCube d (M : ℤ)) 4
              (fun x => F x -
                volumeAverageVec (cubeSet (originCube d (M : ℤ))) F)) ^ ((4 : ℝ) / 5) +
          ‖HilbertVec.ofVec (volumeAverageVec (cubeSet (originCube d (M : ℤ))) F)‖ₑ) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ (M : ℕ) (F : Vec d → Vec d)
        (wD : H10Function (openCubeSet (originCube d (M : ℤ))))
        (wN : H1MeanZeroFunction (openCubeSet (originCube d (M : ℤ)))),
        IsCubeDirichletResponse (originCube d (M : ℤ)) F wD →
        IsCubeNeumannResponse (originCube d (M : ℤ)) F wN →
        vecCubeLpENorm (originCube d (M : ℤ)) 2
            (fun x => wN.toH1Function.grad x - wD.toH1Function.grad x) ≤
          C * (vecHatNegENorm (originCube d (M : ℤ))
                (fun x => F x -
                  volumeAverageVec (cubeSet (originCube d (M : ℤ))) F)) ^ ((1 : ℝ) / 5) *
              (vecCubeLpENorm (originCube d (M : ℤ)) 4
                (fun x => F x -
                  volumeAverageVec (cubeSet (originCube d (M : ℤ))) F)) ^ ((4 : ℝ) / 5) +
            C * ‖HilbertVec.ofVec
              (volumeAverageVec (cubeSet (originCube d (M : ℤ))) F)‖ₑ := by
  obtain ⟨C4, hC4top, hC4⟩ := exists_cubeResponseDifferenceL4Estimate hd
  refine ⟨Cint *
      (ENNReal.ofReal ((originCubeMeanZeroH1CoerciveEstimate d 0).constant)) ^
        ((1 : ℝ) / 5) * C4 ^ ((4 : ℝ) / 5) + 1, ?_, ?_⟩
  · refine ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (ENNReal.mul_lt_top hCint ?_) ?_,
      ENNReal.one_lt_top⟩
    · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
    · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hC4top.ne
  intro M F wD wN hD hN
  by_cases hmem : MemLp (hilbertifyVecField (fun x => F x -
      volumeAverageVec (cubeSet (originCube d (M : ℤ))) F)) 4
      (normalizedCubeMeasure (originCube d (M : ℤ)))
  · refine le_trans (responseDifference_step4 (Cint := Cint) (C4 := C4) hD hN hmem
      (hharm M) (fun G hG u w hu hw => hC4 (originCube d (M : ℤ)) G hG u w hu hw)) ?_
    refine add_le_add ?_ (le_mul_of_one_le_left (zero_le) (one_le_add_one _))
    gcongr
    exact le_self_add
  · by_cases hguard : vecCubeLpENorm (originCube d (M : ℤ)) 4
        (fun x => F x - volumeAverageVec (cubeSet (originCube d (M : ℤ))) F) < ⊤ ∨
      vecHatNegENorm (originCube d (M : ℤ))
        (fun x => F x - volumeAverageVec (cubeSet (originCube d (M : ℤ))) F) = 0
    · refine le_trans (hjunk M F wD wN hD hN hmem hguard) ?_
      refine add_le_add ?_ (le_mul_of_one_le_left (zero_le) (one_le_add_one _))
      exact mul_le_mul' (le_mul_of_one_le_left (zero_le) (one_le_add_one _)) le_rfl
    · push Not at hguard
      obtain ⟨hL4top, hhat⟩ := hguard
      have hL4eq : vecCubeLpENorm (originCube d (M : ℤ)) 4
          (fun x => F x - volumeAverageVec (cubeSet (originCube d (M : ℤ))) F) = ⊤ :=
        top_le_iff.1 hL4top
      have hrpow : (vecHatNegENorm (originCube d (M : ℤ))
          (fun x => F x -
            volumeAverageVec (cubeSet (originCube d (M : ℤ))) F)) ^ ((1 : ℝ) / 5) ≠ 0 := by
        rw [Ne, ENNReal.rpow_eq_zero_iff]
        push Not
        exact ⟨fun h => absurd h hhat, fun _ => by norm_num⟩
      have htop : (Cint *
            (ENNReal.ofReal ((originCubeMeanZeroH1CoerciveEstimate d 0).constant)) ^
              ((1 : ℝ) / 5) * C4 ^ ((4 : ℝ) / 5) + 1) *
          (vecHatNegENorm (originCube d (M : ℤ))
            (fun x => F x -
              volumeAverageVec (cubeSet (originCube d (M : ℤ))) F)) ^ ((1 : ℝ) / 5) *
          (vecCubeLpENorm (originCube d (M : ℤ)) 4
            (fun x => F x -
              volumeAverageVec (cubeSet (originCube d (M : ℤ))) F)) ^ ((4 : ℝ) / 5) = ⊤ := by
        rw [hL4eq, ENNReal.top_rpow_of_pos (by norm_num), ENNReal.mul_top]
        exact mul_ne_zero (add_one_ne_zero' _) hrpow
      rw [htop]
      simp

/-! ## `e.abstract.response.Hhalf`, the Dirichlet summand -/

/-- **The `H̲^{1/2}` clause of `l.abstract.response.fields`**
(`e.abstract.response.Hhalf`), for the
Dirichlet response alone, in the shape of the third conjunct of the
statement `responseFields_apriori_orderZero`.

The estimate itself is the hypothesis `hHalf`, at the scale `M` and for a flux
of finite `H̲^{1/2}(cu_M)` size; only the branch of infinite size, where the
right-hand side is `⊤`, is discharged here.
`Sobolev/ResponseHalfInterpolation.lean` proves the estimate on the unit cube
`originCube d 0` — `cubeHsENorm_unitCubeDirichletResponseGradient_le` — from a
differentiated endpoint carried at the competitor level; the dilation from
scale `0` to scale `M` is not available in this repository. -/
theorem exists_dirichletHsClause (Chalf : ℝ≥0∞) (hChalf : Chalf < ⊤)
    (hHalf : ∀ (M : ℕ) (F : Vec d → Vec d)
      (wD : H10Function (openCubeSet (originCube d (M : ℤ)))),
      IsCubeDirichletResponse (originCube d (M : ℤ)) F wD →
      Section2.Norms.cubeHsENorm (originCube d (M : ℤ)) (1 / 2)
          (hilbertifyVecField F) < ⊤ →
      Section2.Norms.cubeHsENorm (originCube d (M : ℤ)) (1 / 2)
          (hilbertifyVecField wD.toH1Function.grad) ≤
        Chalf * Section2.Norms.cubeHsENorm (originCube d (M : ℤ)) (1 / 2)
          (hilbertifyVecField F)) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ (M : ℕ) (F : Vec d → Vec d)
        (wD : H10Function (openCubeSet (originCube d (M : ℤ)))),
        IsCubeDirichletResponse (originCube d (M : ℤ)) F wD →
        Section2.Norms.cubeHsENorm (originCube d (M : ℤ)) (1 / 2)
            (hilbertifyVecField wD.toH1Function.grad) ≤
          C * Section2.Norms.cubeHsENorm (originCube d (M : ℤ)) (1 / 2)
            (hilbertifyVecField F) := by
  refine ⟨Chalf + 1, ENNReal.add_lt_top.2 ⟨hChalf, ENNReal.one_lt_top⟩, ?_⟩
  intro M F wD hD
  by_cases htop : Section2.Norms.cubeHsENorm (originCube d (M : ℤ)) (1 / 2)
      (hilbertifyVecField F) = ⊤
  · rw [htop, ENNReal.mul_top (add_one_ne_zero' Chalf)]
    exact le_top
  · refine le_trans (hHalf M F wD hD (lt_top_iff_ne_top.2 htop)) ?_
    gcongr
    exact le_self_add

/-! ## The a priori anchor from its bridges -/

end

end ResponseFields
end Section3
end SuperdiffusionCLT
