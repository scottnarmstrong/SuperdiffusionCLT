/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Lemma.SstarClose
public import SuperdiffusionCLT.Section6.Prereq.HarmonicApproxB

/-!
# The coarse-grained matrices of a cube are close to a scalar matrix: the cube theorem

This is Lemma `l.sharp.scale.inputs`, display `e.Dir.new.sstar.close`.
If `𝓔_{1/9,∞,2}(cu_n; a, σ Id) ≤ δ ≤ 1` for a field `a` elliptic on the cube, then
`|σ⁻¹ s(cu_n; a) - Id| + |σ⁻¹ s_*(cu_n; a) - Id| ≤ C δ`. The proof reads off the top-scale term
of the homogenization error, which bounds the normalised block response of the cube, and then
converts it into the matrices `s`, `s_*` (see `SstarClose.lean`).

## Main results

* `sstar_close_cube`: the estimate for a field elliptic on the cube.
* `sstar_close_minimal_scales`: the form fed by the sharp-scale assembly.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6

open Homogenization SuperdiffusionCLT.Section6.HarmonicApprox

open scoped MatrixOrder

noncomputable section

variable {d : ℕ}

/-- The top-scale term of the homogenization error (`q = 2`, `p = ∞`) bounds the normalised
block response of the cube. -/
theorem l8_top_response_le [NeZero d] (Q : TriadicCube d) (F : Book.Ch02.TriadicCoeffFamily d)
    {s : ℝ} (hs : 0 < s) (a0 : Mat d) :
    Book.Ch02.geometricDiscount s 2 * Book.Ch02.normalizedBlockResponseMax Q F a0 ≤
      (Book.Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) F a0) ^ 2 := by
  rw [Book.Ch02.homogenizationErrorOnCube_infinity_two_sq_eq_tsum Q hs F a0]
  have hM : ∀ n : ℕ,
      0 ≤ Book.Ch02.maxDescendantNormalizedBlockResponseAtScale Q (Q.scale - (n : ℤ)) F a0 :=
    fun n => Book.Ch02.maxDescendantNormalizedBlockResponseAtScale_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) F a0
  have hw : ∀ n : ℕ, 0 ≤ Book.Ch02.geometricWeight s 2 n := fun n => by
    simpa [Book.Ch02.geometricWeight_eq_old] using
      (Homogenization.geometricWeight_nonneg (s := s) (q := (2 : ℝ)) n (by positivity))
  refine le_trans ?_ ((Book.Ch02.summable_geometricWeight_two_mul_maxDescendantNormalizedBlockResponseAtScale
    Q F a0 hs).le_tsum 0 fun n _ => mul_nonneg (hw n) (hM n))
  have h0 := Book.Ch02.normalizedBlockResponseMax_le_maxDescendantNormalizedBlockResponseAtScale
    (Q := Q) (R := Q) (k := Q.scale) F a0 (by simp [descendantsAtScale_self])
  have h30 : Real.rpow (3 : ℝ) 0 = 1 := Real.rpow_zero 3
  have hd : 0 ≤ Book.Ch02.geometricDiscount s 2 := by
    have := hw 0
    simp only [Book.Ch02.geometricWeight, Nat.cast_zero, mul_zero, h30, mul_one] at this
    exact this
  simp only [Book.Ch02.geometricWeight, Nat.cast_zero, mul_zero, h30, mul_one, sub_zero]
  exact mul_le_mul_of_nonneg_left h0 hd

section RawCongruence

variable {U V : Set (Vec d)} {a b : CoeffField d}

theorem l8_sigmaStarInv_congr (h : ∀ p q : Vec d, ResponseJ U p q a = ResponseJ V p q b) :
    sigmaStarInvCoarse U a = sigmaStarInvCoarse V b := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [h]
  · rw [sigmaStarInvCoarse_apply_of_ne U a hij, sigmaStarInvCoarse_apply_of_ne V b hij]
    simp only [h]

theorem l8_sigmaStar_congr (h : ∀ p q : Vec d, ResponseJ U p q a = ResponseJ V p q b) :
    sigmaStarCoarse U a = sigmaStarCoarse V b := by
  unfold sigmaStarCoarse
  rw [l8_sigmaStarInv_congr h]

theorem l8_kappa_congr (h : ∀ p q : Vec d, ResponseJ U p q a = ResponseJ V p q b) :
    kappaCoarse U a = kappaCoarse V b := by
  unfold kappaCoarse
  rw [l8_sigmaStar_congr h]
  congr 1
  ext i j
  simp only [sigmaStarInvKappaCoarse, h]

theorem l8_sigma_congr (h : ∀ p q : Vec d, ResponseJ U p q a = ResponseJ V p q b) :
    sigmaCoarse U a = sigmaCoarse V b := by
  have hc : ∀ p : Vec d, sigmaCorrectedResponse U a p = sigmaCorrectedResponse V b p := by
    intro p
    unfold sigmaCorrectedResponse
    rw [h, l8_kappa_congr h, l8_sigmaStarInv_congr h]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [hc]
  · rw [sigmaCoarse_apply_of_ne U a hij, sigmaCoarse_apply_of_ne V b hij]
    simp only [hc]

end RawCongruence

/-- The raw `ResponseJ` of the closed cube for `a` is the one of the open cube for the padded
field. -/
theorem l8_responseJ_pad [NeZero d] (Q : TriadicCube d) {lam : ℝ} (a : CoeffField d)
    (p q : Vec d) :
    ResponseJ (cubeSet Q) p q a = ResponseJ (openCubeSet Q) p q (padField Q lam a) := by
  rw [ResponseJ_cubeSet_eq_openCubeSet_of_triadicCube Q p q a]
  refine responseJ_congr_ae ?_ p q
  have h1 : ∀ᵐ x ∂ volumeMeasureOn (openCubeSet Q), x ∈ openCubeSet Q := by
    unfold volumeMeasureOn
    exact MeasureTheory.ae_restrict_mem (measurableSet_openCubeSet Q)
  filter_upwards [h1] with x hx
  rw [padField_apply_of_mem (openCubeSet_subset_cubeSet Q hx)]

theorem l8_sigmaCoarse_eq [NeZero d] (Q : TriadicCube d) {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a) (h0 : 0 < lam) (hle : lam ≤ Lam) :
    Homogenization.sigmaCoarse (cubeSet Q) a =
      Book.Ch02.sigmaCoarse (Book.Ch02.cubeDomain Q) ((paddedFamily Q hEll h0 hle).coeffOn Q) :=
  l8_sigma_congr (l8_responseJ_pad Q (lam := lam) a)

theorem l8_sigmaStarCoarse_eq [NeZero d] (Q : TriadicCube d) {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a) (h0 : 0 < lam) (hle : lam ≤ Lam) :
    Homogenization.sigmaStarCoarse (cubeSet Q) a =
      Book.Ch02.sigmaStarCoarse (Book.Ch02.cubeDomain Q)
        ((paddedFamily Q hEll h0 hle).coeffOn Q) :=
  l8_sigmaStar_congr (l8_responseJ_pad Q (lam := lam) a)

theorem l8_discount_pos : 0 < Book.Ch02.geometricDiscount (1 / 9 : ℝ) 2 := by
  unfold Book.Ch02.geometricDiscount
  have : Real.rpow (3 : ℝ) (-(1 / 9 : ℝ) * 2) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  linarith only [this]

/-- **`sstar.close` on a cube.** The coarse-grained matrices of a cube, on which the field is
elliptic and `𝓔_{1/9,∞,2}(cu_n; a, σ Id) ≤ δ ≤ 1`, are within `C δ` of `σ Id`. -/
theorem sstar_close_cube (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (Q : TriadicCube d) {lam Lam : ℝ} {a : CoeffField d} {sigma delta : ℝ},
      IsEllipticFieldOn lam Lam (cubeSet Q) a → 0 < sigma →
      HomogenizationErrorOnCube Q (1 / 9) MultiscaleExponent.infinity
        (MultiscaleExponent.finite 2) a (sigma • (1 : Mat d)) ≤ delta → delta ≤ 1 →
      matNorm (sigma⁻¹ • Homogenization.sigmaCoarse (cubeSet Q) a - 1) +
        matNorm (sigma⁻¹ • Homogenization.sigmaStarCoarse (cubeSet Q) a - 1) ≤ C * delta := by
  set Bc : ℝ := (Book.Ch02.geometricDiscount (1 / 9 : ℝ) 2)⁻¹ with hBc
  have hBc0 : 0 < Bc := inv_pos.2 l8_discount_pos
  set K1 : ℝ := Real.sqrt ((d : ℝ) * ((4 + 4 * Bc) * Bc)) with hK1
  have hK10 : 0 ≤ K1 := Real.sqrt_nonneg _
  refine ⟨1 + 2 * K1 + 4 * (d : ℝ) * Bc, ?_, ?_⟩
  · have : 0 ≤ 4 * (d : ℝ) * Bc := by positivity
    linarith only [hK10, this]
  intro Q lam Lam a sigma delta hEll hs hE hdel
  obtain ⟨x0, hx0⟩ := Book.Ch02.openCubeSet_nonempty Q
  have hell0 := hEll.2 x0 (openCubeSet_subset_cubeSet _ hx0)
  have h0 : 0 < lam := hell0.1
  have hle : lam ≤ Lam := hell0.2.1
  set F := paddedFamily Q hEll h0 hle with hF
  have hE9 : Book.Ch02.HomogenizationErrorOnCube Q (1 / 9)
      Book.Ch02.MultiscaleExponent.infinity (Book.Ch02.MultiscaleExponent.finite 2) F
      (scalarMatrix (d := d) sigma) ≤ delta := by
    rw [← homogenizationErrorOnCube_eq_ch02 hEll h0 hle (1 / 9) 2 (sigma • (1 : Mat d))]
    exact hE
  have hE0 : 0 ≤ Book.Ch02.HomogenizationErrorOnCube Q (1 / 9)
      Book.Ch02.MultiscaleExponent.infinity (Book.Ch02.MultiscaleExponent.finite 2) F
      (scalarMatrix (d := d) sigma) := by
    unfold Book.Ch02.HomogenizationErrorOnCube Book.Ch02.HomogenizationError
      Book.Ch02.HomogenizationErrorFinite
    apply Real.rpow_nonneg
    refine tsum_nonneg fun n => mul_nonneg ?_ ?_
    · simpa [Book.Ch02.geometricWeight_eq_old] using
        (Homogenization.geometricWeight_nonneg (s := (1 / 9 : ℝ)) (q := (2 : ℝ)) n
          (by norm_num))
    · exact Real.rpow_nonneg
        (Book.Ch02.scaleResponseAtScale_infinity_nonneg Q (k := Q.scale - (n : ℤ))
          (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) F _) _
  have hdel0 : 0 ≤ delta := hE0.trans hE9
  have hdsq : delta ^ 2 ≤ 1 := by nlinarith only [hdel, hdel0]
  have hEsq : (Book.Ch02.HomogenizationErrorOnCube Q (1 / 9)
      Book.Ch02.MultiscaleExponent.infinity (Book.Ch02.MultiscaleExponent.finite 2) F
      (scalarMatrix (d := d) sigma)) ^ 2 ≤ delta ^ 2 := pow_le_pow_left₀ hE0 hE9 2
  have htop := l8_top_response_le Q F (s := (1 / 9 : ℝ)) (by norm_num) (scalarMatrix (d := d) sigma)
  set M := Book.Ch02.normalizedBlockResponseMax Q F (scalarMatrix (d := d) sigma) with hM
  have hM0 : 0 ≤ M := Book.Ch02.normalizedBlockResponseMax_nonneg Q F _
  have hMd : M ≤ Bc * delta ^ 2 := by
    rw [hBc, ← div_eq_inv_mul, le_div_iff₀ l8_discount_pos]
    linarith only [htop, hEsq]
  have hMB : M ≤ Bc := by nlinarith only [hMd, hdsq, hBc0]
  obtain ⟨h1, h2⟩ := l8_ch02_close Q F hs hMB
  rw [← l8_sigmaStarCoarse_eq Q hEll h0 hle] at h1
  rw [← l8_sigmaCoarse_eq Q hEll h0 hle] at h2
  have hsq : Real.sqrt ((d : ℝ) * ((4 + 4 * Bc) * M)) ≤ K1 * delta := by
    rw [Real.sqrt_le_iff]
    refine ⟨mul_nonneg hK10 hdel0, ?_⟩
    have e : (K1 * delta) ^ 2 = (d : ℝ) * ((4 + 4 * Bc) * Bc) * delta ^ 2 := by
      rw [mul_pow, hK1, Real.sq_sqrt (by positivity)]
    rw [e]
    have : (4 + 4 * Bc) * M ≤ (4 + 4 * Bc) * (Bc * delta ^ 2) :=
      mul_le_mul_of_nonneg_left hMd (by positivity)
    have := mul_le_mul_of_nonneg_left this (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
    nlinarith only [this]
  have hcard : (Fintype.card (Fin d) : ℝ) = d := by simp
  rw [hcard] at h2
  have hdd : delta ^ 2 ≤ delta := by nlinarith only [hdel, hdel0]
  have h3 : 2 * (d : ℝ) * (2 * M) ≤ 4 * (d : ℝ) * Bc * delta := by
    have h4 : M ≤ Bc * delta := hMd.trans (by nlinarith only [hdd, hBc0])
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    nlinarith only [h4, this]
  nlinarith only [h1, h2, hsq, h3, hdel0]

variable [NeZero d]

theorem l8_const_full_one :
    Book.Ch02.constantFullBlockMatrix (scalarMatrix (d := d) 1) = 1 := by
  unfold Book.Ch02.constantFullBlockMatrix
  rw [Book.Ch02.constantBlockMatrix_scalarMatrix one_pos]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [toFullBlockMat, scalarMatrix, Matrix.one_apply]

theorem l8_normalized_identity_le (Q : TriadicCube d) (F : Book.Ch02.TriadicCoeffFamily d)
    (hF : ∀ (R : TriadicCube d) (x : Vec d), (F.coeffOn R).toCoeffField x = 1) :
    Book.Ch02.normalizedBlockResponseMax Q F (scalarMatrix (d := d) 1) ≤ 0 := by
  unfold Book.Ch02.normalizedBlockResponseMax
  refine Real.sSup_nonpos ?_
  rintro y ⟨e, he, rfl⟩
  have hs : Book.Ch02.constantFullBlockMatrixSqrt (scalarMatrix (d := d) 1) = 1 := by
    unfold Book.Ch02.constantFullBlockMatrixSqrt
    rw [l8_const_full_one]
    exact CFC.sqrt_one
  have hi : Book.Ch02.constantFullBlockMatrixInvSqrt (scalarMatrix (d := d) 1) = 1 := by
    unfold Book.Ch02.constantFullBlockMatrixInvSqrt
    rw [hs, inv_one]
  rw [hs, hi, Matrix.one_mulVec]
  refine Real.sSup_nonpos ?_
  rintro m ⟨X, hX, rfl⟩
  unfold Book.Ch02.doubledResponseValue Book.Ch02.average
  refine mul_nonpos_of_nonneg_of_nonpos (by positivity) ?_
  refine MeasureTheory.setIntegral_nonpos (Book.Ch02.cubeDomain Q).measurableSet fun x _ => ?_
  have hB : ∀ Y : BlockVec d, blockMatVecMul (Book.Ch02.blockMatrixField (F.coeffOn Q) x) Y = Y := by
    intro Y
    have e1 : symmPart (1 : Mat d) = 1 := by
      simpa [scalarMatrix] using Book.Ch02.symmPart_scalarMatrix (d := d) 1
    have e2 : skewPart (1 : Mat d) = 0 := by
      simpa [scalarMatrix] using Book.Ch02.skewPart_scalarMatrix (d := d) 1
    have h1 : ∀ v : Vec d, matVecMul (1 : Mat d) v = v := fun v => by
      funext i
      simp [matVecMul, Matrix.one_apply]
    have h0 : ∀ v : Vec d, matVecMul (0 : Mat d) v = 0 := fun v => by
      funext i
      simp [matVecMul]
    have h2 : matTranspose (0 : Mat d) = 0 := by simp [matTranspose]
    simp [Book.Ch02.blockMatrixField, hF, e1, e2, blockMatVecMul, h1, h0, h2]
  have hnn : ∀ Y : BlockVec d, 0 ≤ blockVecDot Y Y := fun Y => by
    unfold blockVecDot vecDot
    exact add_nonneg (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
      (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
  show -Book.Ch02.blockEnergyDensityAt (F.coeffOn Q) (X.eval x) x -
      blockVecDot (ofFullBlockVec e)
        (blockMatVecMul (Book.Ch02.blockMatrixField (F.coeffOn Q) x) (X.eval x)) +
      blockVecDot (ofFullBlockVec e) (X.eval x) ≤ 0
  unfold Book.Ch02.blockEnergyDensityAt
  rw [hB]
  have := hnn (X.eval x)
  linarith only [this]

theorem l8_error_identity_le (Q : TriadicCube d) (F : Book.Ch02.TriadicCoeffFamily d)
    (hF : ∀ (R : TriadicCube d) (x : Vec d), (F.coeffOn R).toCoeffField x = 1) :
    Book.Ch02.HomogenizationErrorOnCube Q (1 / 9) Book.Ch02.MultiscaleExponent.infinity
      (Book.Ch02.MultiscaleExponent.finite 2) F (scalarMatrix (d := d) 1) ≤ 0 := by
  have hsq : (Book.Ch02.HomogenizationErrorOnCube Q (1 / 9)
      Book.Ch02.MultiscaleExponent.infinity (Book.Ch02.MultiscaleExponent.finite 2) F
      (scalarMatrix (d := d) 1)) ^ 2 ≤ 0 := by
    rw [Book.Ch02.homogenizationErrorOnCube_infinity_two_sq_eq_tsum Q (by norm_num) F _]
    refine tsum_nonpos fun n => mul_nonpos_of_nonneg_of_nonpos ?_ ?_
    · simpa [Book.Ch02.geometricWeight_eq_old] using
        (Homogenization.geometricWeight_nonneg (s := (1 / 9 : ℝ)) (q := (2 : ℝ)) n
          (by norm_num))
    · unfold Book.Ch02.maxDescendantNormalizedBlockResponseAtScale Book.Ch02.finsetSupReal
      refine Real.sSup_nonpos ?_
      rintro y ⟨R, _, rfl⟩
      exact l8_normalized_identity_le R F hF
  nlinarith only [hsq]

/-- **`sstar.close` for the full centered field**, in the shape consumed by the assembly of
`l.sharp.scale.inputs`. The cube `z + cu_n` is rendered by translating the field to the origin
cube; `sigma` is `σ̄_m` and `delta` the bound of `e.Dir.new.full.good`, assumed at most `1`. -/
theorem sstar_close_minimal_scales (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (nu sigma delta : ℝ)
      (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
      (m n : ℕ) (k : Fin d → ℤ), 0 < sigma →
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
      delta ≤ 1 →
      matNorm (sigma⁻¹ • Homogenization.sigmaCoarse (cubeSet (originCube d (n : ℤ)))
          (fun x => nu • (1 : Mat d) +
            SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
              (cubeSet (originCube d (m : ℤ)))
              ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)) - 1) +
        matNorm (sigma⁻¹ • Homogenization.sigmaStarCoarse (cubeSet (originCube d (n : ℤ)))
          (fun x => nu • (1 : Mat d) +
            SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
              (cubeSet (originCube d (m : ℤ)))
              ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)) - 1) ≤ C * delta := by
  obtain ⟨C, hC, h⟩ := sstar_close_cube d
  refine ⟨C, hC, ?_⟩
  intro nu sigma delta omega m n k hs hEll hE hdel
  exact h (originCube d (n : ℤ)) hEll.choose_spec.choose_spec hs hE hdel

end

end SuperdiffusionCLT.Section6
