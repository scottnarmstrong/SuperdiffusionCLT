/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Lemma.WeakFlux
public import SuperdiffusionCLT.Section6.Prereq.HarmonicApproxB
public import SuperdiffusionCLT.Section2.Norms.CubeLp
public import Homogenization.Book.Ch03.Theorems.PublicInternalBridges.EndPoints

/-!
# Weak flux estimate

This is Lemma `l.sharp.scale.inputs`, display `e.Dir.new.weak.flux`.
For a field `a` with symmetric part `ν Id`, elliptic on the cube `cu_n`, with
`𝓔_{1/9,∞,2}(cu_n; a, σ Id) ≤ δ`, every `a`-harmonic `u` on `cu_n` satisfies
`3^{-n/4} ‖(a - σ Id) ∇u‖_{H̲^{-1/4}(cu_n)} ≤ C σ^{1/2} δ ν^{1/2} ‖∇u‖_{L̲²(cu_n)}`.
The seminorm is the unhatted dual norm, so the depth-zero average of the flux defect is part of
the left-hand side; it is covered by the circ seminorm of the coarse-graining black box.

## Main results

* `weak_flux_circ_bound`: the circ seminorm at exponent `1/4`.
* `weak_flux_cube`: the dual-norm statement on `cu_n`.
* `weak_flux_minimal_scales`: the statement for the full centered stream field, in the shape
  consumed by the assembly of `l.sharp.scale.inputs`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6.WeakFlux

open Homogenization
open SuperdiffusionCLT.Section6.HarmonicApprox

noncomputable section

variable {d : ℕ} [NeZero d]

theorem l6_error_two_nonneg (Q : TriadicCube d) (a : Book.Ch02.TriadicCoeffFamily d) (a0 : Mat d)
    {s : ℝ} (hs : 0 < s) :
    0 ≤ Book.Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) a a0 := by
  unfold Book.Ch02.HomogenizationErrorOnCube Book.Ch02.HomogenizationError
    Book.Ch02.HomogenizationErrorFinite
  apply Real.rpow_nonneg
  refine tsum_nonneg fun n => mul_nonneg ?_ ?_
  · simpa [Book.Ch02.geometricWeight_eq_old] using
      (Homogenization.geometricWeight_nonneg (s := s) (q := (2 : ℝ)) n (by positivity))
  · exact Real.rpow_nonneg
      (Book.Ch02.scaleResponseAtScale_infinity_nonneg Q (k := Q.scale - (n : ℤ))
        (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a a0) _

/-- The circ seminorm at exponent `1/4` of the flux defect `(a - σ) ∇u`. -/
theorem weak_flux_circ_bound (d : ℕ) [NeZero d] :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ (Q : TriadicCube d) {lam Lam : ℝ} {a : CoeffField d}
      (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a) (h0 : 0 < lam) (hle : lam ≤ Lam)
      {sigma nu : ℝ}, 0 < sigma → 0 < nu →
      (∀ x ∈ cubeSet Q, symmPart (a x) = nu • (1 : Mat d)) →
      ∀ (u : AHarmonicFunction a (openCubeSet Q)),
      cubeBesovNegativeVectorSeminormTwo Q (1 / 4)
          (fun x => matVecMul (a x - sigma • (1 : Mat d)) (u.toH1.grad x)) ≤
        C₂ * Real.sqrt sigma * Real.sqrt nu *
          Book.Ch02.HomogenizationErrorOnCube Q (1 / 9) Book.Ch02.MultiscaleExponent.infinity
            (Book.Ch02.MultiscaleExponent.finite 2) (paddedFamily Q hEll h0 hle) (sigma • 1) *
          cubeLpNorm Q 2 (fun x => Real.sqrt (vecNormSq (u.toH1.grad x))) := by
  obtain ⟨C₁, hC₁, hth⟩ :=
    (Book.Ch03.homogenizationBlackBoxesTheory d).generalCoarseGrainingL2TwoExponent.exists_constant
  set r : ℝ := 17 / 144 with hr
  set K : ℝ := Real.sqrt ((Book.Ch02.geometricDiscount r 1) ^ 2 /
          (Book.Ch02.geometricDiscount (1 / 9) 2 * (1 - (3 : ℝ) ^ (-(2 * (r - 1 / 9)))))) with hK
  set B : ℝ := (1 / 4 : ℝ)⁻¹ * (r⁻¹) ^ (2 : ℕ) * ((1 / 2 : ℝ) - r)⁻¹ * (C₁ * (r⁻¹ * K)) with hB
  have hBnn : 0 ≤ B := by
    have hKnn : 0 ≤ K := Real.sqrt_nonneg _
    have : (0 : ℝ) < 1 / 2 - r := by rw [hr]; norm_num
    rw [hB]
    have hr0 : 0 < r := by rw [hr]; norm_num
    positivity
  refine ⟨Real.sqrt 2 * B + 1, by positivity, ?_⟩
  intro Q lam Lam a hEll h0 hle sigma nu hs hnu hsym u
  obtain ⟨w, hw⟩ := exists_zeroTrace_remainder Q one_pos u.toH1
  have hcirc := l6_circ_le_comparison_lhs Q hEll h0 hle hs u w hw (s := 1 / 4) (by norm_num)
  have h1 := hth (Q := Q) (a := paddedFamily Q hEll h0 hle) (a0 := constMat d hs)
    (s := 1 / 4) (r := r) (r₂ := r) (j := 0) (g := 0) ⟨sigma, hs, rfl⟩
    (comparisonDatum Q hEll h0 hle hs u w hw) (by norm_num) (by rw [hr]; norm_num)
    (by rw [hr]; norm_num) (by norm_num) le_rfl (forceBesovRegularity_zero Q _)
  have hen : Book.Ch03.h1EnergyNormOnCube Q (paddedFamily Q hEll h0 hle)
      (comparisonDatum Q hEll h0 hle hs u w hw).u =
      Real.sqrt nu * cubeLpNorm Q 2 (fun x => Real.sqrt (vecNormSq (u.toH1.grad x))) :=
    h1EnergyNormOnCube_paddedFamily Q hEll h0 hle hnu hsym u.toH1
  rw [rhs_zero_force, errorAtDepth_zero, hen] at h1
  have hE1 : 0 ≤ Book.Ch02.HomogenizationErrorOnCube Q r Book.Ch02.MultiscaleExponent.infinity
      (Book.Ch02.MultiscaleExponent.finite 1) (paddedFamily Q hEll h0 hle) (constMat d hs).matrix :=
    Book.Ch02.HomogenizationErrorOnCube_infinity_one_nonneg Q _ _ (by rw [hr]; norm_num)
  have hq : Book.Ch02.HomogenizationErrorOnCube Q r Book.Ch02.MultiscaleExponent.infinity
      (Book.Ch02.MultiscaleExponent.finite 1) (paddedFamily Q hEll h0 hle) (constMat d hs).matrix ≤
      K * Book.Ch02.HomogenizationErrorOnCube Q (1 / 9) Book.Ch02.MultiscaleExponent.infinity
        (Book.Ch02.MultiscaleExponent.finite 2) (paddedFamily Q hEll h0 hle) (sigma • 1) :=
    l6_error_one_le_two_of_lt Q _ (sigma • (1 : Mat d)) (by norm_num) (by rw [hr]; norm_num)
  have hnorm : Book.Ch03.constantCoeffMatrixNormHalf (constMat d hs) ≤ Real.sqrt sigma := by
    unfold Book.Ch03.constantCoeffMatrixNormHalf
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow (norm_nonneg _) (matrixNorm_scalar_le hs.le) (by norm_num)
  have hM0 : 0 ≤ Book.Ch03.constantCoeffMatrixNormHalf (constMat d hs) :=
    Real.rpow_nonneg (norm_nonneg _) _
  have hG : 0 ≤ cubeLpNorm Q 2 (fun x => Real.sqrt (vecNormSq (u.toH1.grad x))) :=
    cubeLpNorm_nonneg _ _ _
  have hsqnu : 0 ≤ Real.sqrt nu := Real.sqrt_nonneg _
  have hKnn : 0 ≤ K := Real.sqrt_nonneg _
  have hEnn : 0 ≤ Book.Ch02.HomogenizationErrorOnCube Q (1 / 9)
      Book.Ch02.MultiscaleExponent.infinity (Book.Ch02.MultiscaleExponent.finite 2)
      (paddedFamily Q hEll h0 hle) (sigma • 1) := l6_error_two_nonneg Q _ _ (by norm_num)
  have hr0 : 0 < r := by rw [hr]; norm_num
  have hpre : 0 ≤ (1 / 4 : ℝ)⁻¹ * (r⁻¹) ^ (2 : ℕ) * ((1 / 2 : ℝ) - r)⁻¹ * C₁ := by
    have : (0 : ℝ) < 1 / 2 - r := by rw [hr]; norm_num
    positivity
  have key : (1 / 4 : ℝ)⁻¹ * (r⁻¹) ^ (2 : ℕ) * ((1 / 2 : ℝ) - r)⁻¹ *
      (C₁ * (r⁻¹ * Book.Ch03.constantCoeffMatrixNormHalf (constMat d hs) *
        Book.Ch02.HomogenizationErrorOnCube Q r Book.Ch02.MultiscaleExponent.infinity
          (Book.Ch02.MultiscaleExponent.finite 1) (paddedFamily Q hEll h0 hle)
          (constMat d hs).matrix *
        (Real.sqrt nu * cubeLpNorm Q 2 (fun x => Real.sqrt (vecNormSq (u.toH1.grad x)))))) ≤
      B * Real.sqrt sigma * Real.sqrt nu *
        Book.Ch02.HomogenizationErrorOnCube Q (1 / 9) Book.Ch02.MultiscaleExponent.infinity
          (Book.Ch02.MultiscaleExponent.finite 2) (paddedFamily Q hEll h0 hle) (sigma • 1) *
        cubeLpNorm Q 2 (fun x => Real.sqrt (vecNormSq (u.toH1.grad x))) := by
    have hstep : Book.Ch03.constantCoeffMatrixNormHalf (constMat d hs) *
        Book.Ch02.HomogenizationErrorOnCube Q r Book.Ch02.MultiscaleExponent.infinity
          (Book.Ch02.MultiscaleExponent.finite 1) (paddedFamily Q hEll h0 hle)
          (constMat d hs).matrix ≤
        Real.sqrt sigma * (K * Book.Ch02.HomogenizationErrorOnCube Q (1 / 9)
          Book.Ch02.MultiscaleExponent.infinity (Book.Ch02.MultiscaleExponent.finite 2)
          (paddedFamily Q hEll h0 hle) (sigma • 1)) :=
      mul_le_mul hnorm hq hE1 (Real.sqrt_nonneg _)
    have hmul := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hstep (mul_nonneg hsqnu hG)) hpre
    calc _ = (1 / 4 : ℝ)⁻¹ * (r⁻¹) ^ (2 : ℕ) * ((1 / 2 : ℝ) - r)⁻¹ * C₁ * r⁻¹ *
          ((Book.Ch03.constantCoeffMatrixNormHalf (constMat d hs) *
            Book.Ch02.HomogenizationErrorOnCube Q r Book.Ch02.MultiscaleExponent.infinity
              (Book.Ch02.MultiscaleExponent.finite 1) (paddedFamily Q hEll h0 hle)
              (constMat d hs).matrix) *
            (Real.sqrt nu * cubeLpNorm Q 2 (fun x => Real.sqrt (vecNormSq (u.toH1.grad x))))) := by
          ring
      _ ≤ (1 / 4 : ℝ)⁻¹ * (r⁻¹) ^ (2 : ℕ) * ((1 / 2 : ℝ) - r)⁻¹ * C₁ * r⁻¹ *
          ((Real.sqrt sigma * (K * Book.Ch02.HomogenizationErrorOnCube Q (1 / 9)
            Book.Ch02.MultiscaleExponent.infinity (Book.Ch02.MultiscaleExponent.finite 2)
            (paddedFamily Q hEll h0 hle) (sigma • 1))) *
            (Real.sqrt nu * cubeLpNorm Q 2 (fun x => Real.sqrt (vecNormSq (u.toH1.grad x))))) := by
          refine mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hstep (mul_nonneg hsqnu hG)) ?_
          positivity
      _ = _ := by rw [hB]; ring
  have h2 := hcirc.trans (mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg 2))
  refine h2.trans ?_
  have h3 := mul_le_mul_of_nonneg_left key (Real.sqrt_nonneg 2)
  have hpos : 0 ≤ Real.sqrt sigma * Real.sqrt nu *
      Book.Ch02.HomogenizationErrorOnCube Q (1 / 9) Book.Ch02.MultiscaleExponent.infinity
        (Book.Ch02.MultiscaleExponent.finite 2) (paddedFamily Q hEll h0 hle) (sigma • 1) *
      cubeLpNorm Q 2 (fun x => Real.sqrt (vecNormSq (u.toH1.grad x))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hsqnu) hEnn) hG
  refine h3.trans ?_
  nlinarith only [hpos]


theorem l6_memVectorL2_flux_defect (Q : TriadicCube d) {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a) (h0 : 0 < lam) (hle : lam ≤ Lam)
    {sigma : ℝ} (hs : 0 < sigma) (u : AHarmonicFunction a (openCubeSet Q)) :
    MemVectorL2 (cubeSet Q)
      (fun x => matVecMul (a x - sigma • (1 : Mat d)) (u.toH1.grad x)) := by
  have hF : MemVectorL2 (cubeSet Q)
      (fluxDefect (Book.Ch03.publicCoeffField Q (paddedFamily Q hEll h0 hle))
        (constMat d hs).matrix u.toH1.grad) :=
    Book.Ch03.publicH1_fluxDefect_memVectorL2_descendant_cubeSet (Q := Q) (R := Q)
      (a := paddedFamily Q hEll h0 hle) (a0 := constMat d hs) (j := 0) u.toH1 (by simp)
  have h : (fluxDefect (Book.Ch03.publicCoeffField Q (paddedFamily Q hEll h0 hle))
      (constMat d hs).matrix u.toH1.grad) =ᵐ[volumeMeasureOn (cubeSet Q)]
      (fun x => matVecMul (a x - sigma • (1 : Mat d)) (u.toH1.grad x)) := by
    filter_upwards [Book.Ch03.publicCoeffField_ae_eq_cubeSet Q (paddedFamily Q hEll h0 hle),
      MeasureTheory.ae_restrict_mem (measurableSet_cubeSet Q)] with x hx hxm
    simp only [fluxDefect, constMat, sub_matVecMul, hx]
    rw [paddedFamily_coeffOn_toCoeffField, padField_apply_of_mem hxm]
  exact MeasureTheory.MemLp.ae_eq h hF

/-- **Weak flux estimate on a cube** (the unhatted dual norm). -/
theorem weak_flux_cube (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (Q : TriadicCube d) {lam Lam : ℝ} {a : CoeffField d}
      {sigma nu delta : ℝ},
      IsEllipticFieldOn lam Lam (cubeSet Q) a → 0 < sigma → 0 < nu →
      (∀ x ∈ cubeSet Q, symmPart (a x) = nu • (1 : Mat d)) →
      HomogenizationErrorOnCube Q (1 / 9) MultiscaleExponent.infinity
        (MultiscaleExponent.finite 2) a (sigma • (1 : Mat d)) ≤ delta →
      ∀ u : AHarmonicFunction a (openCubeSet Q),
        ENNReal.ofReal
            (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo Q (1 / 4)
              (fun x => matVecMul (a x - sigma • (1 : Mat d)) (u.toH1.grad x))) ≤
          ENNReal.ofReal (C * Real.sqrt sigma * delta * Real.sqrt nu) *
            SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2
              (fun x => Real.sqrt (vecNormSq (u.toH1.grad x))) := by
  obtain ⟨C₂, hC₂, hcirc⟩ := weak_flux_circ_bound d
  have hKd0' : 0 ≤ (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1 / 4) :=
    mul_nonneg (Nat.cast_nonneg d) (Real.rpow_nonneg (by norm_num) _)
  refine ⟨(d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1 / 4) * C₂ + 1, by
    have := mul_nonneg hKd0' hC₂.le
    linarith only [this], ?_⟩
  intro Q lam Lam a sigma nu delta hEll hs hnu hsym hE u
  obtain ⟨x0, hx0⟩ := Book.Ch02.openCubeSet_nonempty Q
  have hell0 := hEll.2 x0 (openCubeSet_subset_cubeSet _ hx0)
  have h0 : 0 < lam := hell0.1
  have hle : lam ≤ Lam := hell0.2.1
  have hbridge :=
    Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo_le_note_constant_mul_cubeBesovNegativeVectorSeminormTwo
      Q (1 / 4)
      (fun x => matVecMul (a x - sigma • (1 : Mat d)) (u.toH1.grad x)) (by norm_num)
      (l6_memVectorL2_flux_defect Q hEll h0 hle hs u)
  have hc := hcirc Q hEll h0 hle hs hnu hsym u
  have hE' := hE
  rw [homogenizationErrorOnCube_eq_ch02 hEll h0 hle (1 / 9) 2 (sigma • (1 : Mat d))] at hE'
  have hGL2 := memLp_sqrt_vecNormSq_grad u.toH1
  have hGE : SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2
      (fun x => Real.sqrt (vecNormSq (u.toH1.grad x))) = ENNReal.ofReal (cubeLpNorm Q 2
        (fun x => Real.sqrt (vecNormSq (u.toH1.grad x)))) := by
    unfold SuperdiffusionCLT.Section2.Norms.cubeLpENorm cubeLpNorm
    rw [ENNReal.ofReal_toReal hGL2.eLpNorm_lt_top.ne]
  have hG0 : 0 ≤ cubeLpNorm Q 2 (fun x => Real.sqrt (vecNormSq (u.toH1.grad x))) :=
    cubeLpNorm_nonneg _ _ _
  set Kd : ℝ := (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1 / 4) with hKd
  have hKd0 : 0 ≤ Kd := by
    rw [hKd]
    exact mul_nonneg (Nat.cast_nonneg d) (Real.rpow_nonneg (by norm_num) _)
  have hs0 := Real.sqrt_nonneg sigma
  have hn0 := Real.sqrt_nonneg nu
  have hreal : Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo Q (1 / 4)
      (fun x => matVecMul (a x - sigma • (1 : Mat d)) (u.toH1.grad x)) ≤
      (Kd * C₂ + 1) * Real.sqrt sigma * delta * Real.sqrt nu *
        cubeLpNorm Q 2 (fun x => Real.sqrt (vecNormSq (u.toH1.grad x))) := by
    refine hbridge.trans ?_
    have h1 := mul_le_mul_of_nonneg_left hc hKd0
    refine h1.trans ?_
    have hpre : 0 ≤ Kd * C₂ * Real.sqrt sigma * Real.sqrt nu *
        cubeLpNorm Q 2 (fun x => Real.sqrt (vecNormSq (u.toH1.grad x))) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hKd0 hC₂.le) hs0) hn0) hG0
    have hmono := mul_le_mul_of_nonneg_left hE' hpre
    have hdel : 0 ≤ delta := (l6_error_two_nonneg Q (paddedFamily Q hEll h0 hle) (sigma • 1)
      (by norm_num)).trans hE'
    nlinarith only [hmono, mul_nonneg (mul_nonneg (mul_nonneg hs0 hn0) hdel) hG0]
  rw [hGE, ← ENNReal.ofReal_mul' hG0]
  exact ENNReal.ofReal_le_ofReal hreal


/-- **Weak flux estimate for the full centered field**, in the shape consumed by the assembly of
`l.sharp.scale.inputs`. The cube `z + cu_n` is rendered by translating the field to the origin
cube; `sigma` is `σ̄_m` and `delta` the bound of `e.Dir.new.full.good`. -/
theorem weak_flux_minimal_scales (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (nu sigma delta : ℝ) (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
      (m n : ℕ) (k : Fin d → ℤ), 0 < nu → 0 < sigma →
      (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
          cubeSet (originCube d (n : ℤ)) ⊆ cubeSet (originCube d (m : ℤ)) →
      (∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (cubeSet (originCube d (n : ℤ)))
        (fun x => nu • (1 : Mat d) +
          SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
            (cubeSet (originCube d (m : ℤ)))
            ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))) →
      HomogenizationErrorOnCube (originCube d (n : ℤ)) (1 / 9) MultiscaleExponent.infinity
        (MultiscaleExponent.finite 2)
        (fun x => nu • (1 : Mat d) +
          SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
            (cubeSet (originCube d (m : ℤ)))
            ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)) (sigma • (1 : Mat d)) ≤ delta →
      ∀ u : AHarmonicFunction
          (fun x => nu • (1 : Mat d) +
            SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
              (cubeSet (originCube d (m : ℤ)))
              ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))
          (openCubeSet (originCube d (n : ℤ))),
        ENNReal.ofReal
            (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo (originCube d (n : ℤ)) (1 / 4)
              (fun x => matVecMul
                (nu • (1 : Mat d) +
                  SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
                    (cubeSet (originCube d (m : ℤ)))
                    ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) - sigma • (1 : Mat d))
                (u.toH1.grad x))) ≤
          ENNReal.ofReal (C * Real.sqrt sigma * delta * Real.sqrt nu) *
            SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (n : ℤ)) 2
              (fun x => Real.sqrt (vecNormSq (u.toH1.grad x))) := by
  obtain ⟨C, hC, h⟩ := weak_flux_cube d
  refine ⟨C, hC, ?_⟩
  intro nu sigma delta omega m n k hnu hs _ hEll hE u
  exact h (originCube d (n : ℤ)) hEll.choose_spec.choose_spec hs hnu
    (fun x _ => symmPart_centeredStreamField_add nu omega _ _) hE u

/-- Witness (satisfiability): all non-law hypotheses of `weak_flux_cube` hold together
(constant identity field, `σ = ν = 1`, `δ` the error itself, `u = 0`). -/
example (d : ℕ) [NeZero d] (Q : TriadicCube d) :
    ∃ (a : CoeffField d) (lam Lam sigma nu delta : ℝ),
      IsEllipticFieldOn lam Lam (cubeSet Q) a ∧ 0 < sigma ∧ 0 < nu ∧
      (∀ x ∈ cubeSet Q, symmPart (a x) = nu • (1 : Mat d)) ∧
      HomogenizationErrorOnCube Q (1 / 9) MultiscaleExponent.infinity
        (MultiscaleExponent.finite 2) a (sigma • (1 : Mat d)) ≤ delta ∧
      Nonempty (AHarmonicFunction a (openCubeSet Q)) := by
  classical
  refine ⟨fun _ => (1 : Mat d), 1, 1, 1, 1, _, ?_, one_pos, one_pos, ?_, le_rfl, ?_⟩
  · refine ⟨?_, fun x _ => ?_⟩
    · exact Measurable.of_eval fun i => Measurable.of_eval fun j =>
        Measurable.ite (measurableSet_cubeSet _) measurable_const measurable_const
    · simpa using isEllipticMatrix_scalarMatrix (d := d) (sigma := 1) one_pos
  · intro x _
    ext i j
    by_cases h : i = j
    · subst h
      simp [symmPart]
    · simp [symmPart, h, Ne.symm h]
  · exact ⟨⟨0, isAHarmonicGradient_zero⟩⟩

end

end SuperdiffusionCLT.Section6.WeakFlux
