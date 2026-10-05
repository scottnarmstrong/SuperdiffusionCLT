/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Engine.Carriers
public import SuperdiffusionCLT.Section6.Lemma.WeakGrad
public import SuperdiffusionCLT.Section6.Lemma.RegEllipticityB
public import Homogenization.Book.Ch03.Theorems.CoarseCaccioppoliRHS.ZeroTraceValue
public import Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Finite.Properties

/-!
# The coarse-grained Poincare inequality on an origin cube

For a field elliptic on `□_n` with symmetric part `ν Id` and `σ⁻¹ Λ_{1/4,1} + σ λ_{1/4,1}⁻¹ ≤ B`,
every solution `u` of `□_n` satisfies `√(σ/ν) 3^{-n} ‖u - (u)‖_{L̲²(□_n)} ≤ C ‖∇u‖_{L̲²(□_n)}`
with `C = C(d, B)`.

The route: the fluctuation-to-negative-Besov bound at `t = 1/8`, the coarse Poincare inequality of
the public development at `s = 1/4`, `q = 2`, the comparison `λ_{1/4,2}⁻¹ ≤ C λ_{1/4,1}⁻¹`, and the
transfer of the lower ellipticity from the public family to the field. The Poincare constant
`fullVectorPoincareConstant Q = d · C_CZ(d)` does not depend on the scale.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory

noncomputable section

variable {d : ℕ}

theorem ea2_cubeAverage_congr_ae {Q : TriadicCube d} {f g : Vec d → ℝ}
    (h : f =ᵐ[volume.restrict (openCubeSet Q)] g) : cubeAverage Q f = cubeAverage Q g := by
  unfold cubeAverage
  congr 1
  apply MeasureTheory.integral_congr_ae
  rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  exact h

theorem ea2_cubeLpNorm_congr_ae {E : Type*} [NormedAddCommGroup E] (Q : TriadicCube d)
    (p : ENNReal) {f g : Vec d → E} (h : f =ᵐ[volume.restrict (openCubeSet Q)] g) :
    cubeLpNorm Q p f = cubeLpNorm Q p g := by
  unfold cubeLpNorm
  rw [MeasureTheory.eLpNorm_congr_ae]
  rw [normalizedCubeMeasure, Filter.EventuallyEq]
  refine MeasureTheory.Measure.ae_smul_measure ?_ _
  rw [cubeMeasure, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  exact h

/-- The cube flatness depends on the function only up to a.e. equality on the open cube. -/
theorem ea2_cubeFlat_congr_ae (n : ℕ) {f g : Vec d → ℝ}
    (h : f =ᵐ[volume.restrict (engCube d n)] g) : cubeFlat n f = cubeFlat n g := by
  unfold cubeFlat cubeL2
  rw [ea2_cubeAverage_congr_ae h]
  congr 1
  refine ea2_cubeLpNorm_congr_ae _ _ ?_
  filter_upwards [h] with x hx
  rw [hx]

theorem ea2_cubeGradL2_congr_ae (n : ℕ) {f g : Vec d → Vec d}
    (h : f =ᵐ[volume.restrict (engCube d n)] g) : cubeGradL2 n f = cubeGradL2 n g := by
  unfold cubeGradL2 cubeL2
  refine ea2_cubeLpNorm_congr_ae _ _ ?_
  filter_upwards [h] with x hx
  rw [hx]

/-- The negative Besov norm of the gradient of a solution at `s = 1/4`. -/
theorem ea2_besov_le [NeZero d] (Q : TriadicCube d) {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a) (h0 : 0 < lam) (hle : lam ≤ Lam)
    {nu : ℝ} (hnu : 0 < nu) (hsym : ∀ x ∈ cubeSet Q, symmPart (a x) = nu • (1 : Mat d))
    (u : AHarmonicFunction a (openCubeSet Q)) :
    cubeBesovNegativeVectorSeminormTwo Q (1 / 4) u.toH1.grad ≤
      Book.Ch03.poincareDiscountFactor (1 / 4) (Book.Ch02.MultiscaleExponent.finite 2) *
        (Real.rpow (Book.Ch02.lambdaSq Q (1 / 4)
          (Book.Ch02.MultiscaleExponent.finite 2)
          (HarmonicApprox.paddedFamily Q hEll h0 hle)) (-(1 / 2 : ℝ))) *
        (Real.sqrt nu * cubeLpNorm Q 2 (fun x => Real.sqrt (vecNormSq (u.toH1.grad x)))) := by
  obtain ⟨v, hv⟩ := WeakGrad.weakGrad_exists_solution Q hEll h0 hle u
  have hgrad : v.toH1.grad = u.toH1.grad := by rw [hv]
  have hpo := Book.Ch03.coarsePoincareGradient_negativeBesov_le Q
    (HarmonicApprox.paddedFamily Q hEll h0 hle) (s := 1 / 4)
    (q := Book.Ch02.MultiscaleExponent.finite 2) v (by norm_num) (by norm_num)
  have hcirc_eq :=
    Book.Ch03.scaleNormalizedNegativeBesovVectorNorm_finite_two_eq_cubeBesovNegativeVectorSeminormTwo
      Q (1 / 4) u.toH1.grad
  have hG0 : 0 ≤ cubeLpNorm Q 2 (fun x => Real.sqrt (vecNormSq (u.toH1.grad x))) :=
    cubeLpNorm_nonneg _ _ _
  have hen := WeakGrad.weakGrad_energy Q hEll h0 hle hsym v
  rw [hgrad] at hen
  have hsqrt_en : Book.Ch03.solutionEnergyNorm Q
      (HarmonicApprox.paddedFamily Q hEll h0 hle) v =
      Real.sqrt nu * cubeLpNorm Q 2 (fun x => Real.sqrt (vecNormSq (u.toH1.grad x))) := by
    unfold Book.Ch03.solutionEnergyNorm
    rw [hen, Real.sqrt_mul hnu.le, Real.sqrt_sq hG0]
  have h := hpo
  unfold Book.Ch03.coarsePoincareGradientRHS Book.Ch03.poincareLowerEllipticityFactor at h
  rw [hsqrt_en] at h
  have e : Book.Ch03.solutionGradientField v = u.toH1.grad := hgrad
  rw [e, hcirc_eq] at h
  exact h

/-- A positive `x ^ (-1/2)` bounded by `L ^ (-1/2)` forces `L > 0`. -/
theorem ea2_pos_of_rpow_le {x L : ℝ} (hx : 0 < Real.rpow x (-(1 / 2 : ℝ)))
    (h : Real.rpow x (-(1 / 2 : ℝ)) ≤ Real.rpow L (-(1 / 2 : ℝ))) : 0 < L := by
  by_contra hL
  replace hL : L ≤ 0 := not_lt.mp hL
  rcases hL.lt_or_eq with hlt | heq
  · have : Real.rpow L (-(1 / 2 : ℝ)) = 0 := by
      rw [Real.rpow_eq_pow, Real.rpow_def_of_neg hlt]
      have : Real.cos (-(1 / 2 : ℝ) * Real.pi) = 0 := by
        rw [show -(1 / 2 : ℝ) * Real.pi = -(Real.pi / 2) by ring, Real.cos_neg,
          Real.cos_pi_div_two]
      rw [this, mul_zero]
    linarith only [this, h, hx]
  · rw [heq] at h
    have : Real.rpow 0 (-(1 / 2 : ℝ)) = 0 := Real.zero_rpow (by norm_num)
    linarith only [this, h, hx]

/-- Lower ellipticity: the public family at `(1/4, q = 2)` is controlled by the field's
`λ_{1/4,1}`, which is positive. -/
theorem ea2_lower [NeZero d] (Q : TriadicCube d) {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a) (h0 : 0 < lam) (hle : lam ≤ Lam) :
    0 < lambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) a ∧
      (Book.Ch02.lambdaSq Q (1 / 4) (Book.Ch02.MultiscaleExponent.finite 2)
          (HarmonicApprox.paddedFamily Q hEll h0 hle))⁻¹ ≤
        (25 * Real.exp 4 * Real.rpow (1 / 4) (2 / 2 - 2 / 1)) *
          (lambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) a)⁻¹ := by
  set F := HarmonicApprox.paddedFamily Q hEll h0 hle with hF
  have hg : Book.Ch03.publicCoeffField Q F =ᵐ[volumeMeasureOn (cubeSet Q)] a :=
    HarmonicApprox.publicCoeffField_paddedFamily_ae_eq hEll h0 hle (subset_refl _)
  have hq4 : (0 : ℝ) < 1 / 4 := by norm_num
  have el : lambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) (Book.Ch03.publicCoeffField Q F) =
      lambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) a :=
    l5_lambdaSq_congr_ae Q _ _ hg
  have hLpos : 0 < Book.Ch02.lambdaSq Q (1 / 4) (Book.Ch02.MultiscaleExponent.finite 1) F :=
    Book.Ch02.lambdaSq_pos Q F hq4 (by simp)
  have hold := Book.Ch02.lambdaSq_one_rpow_neg_half_le_old_pointwiseCoeffField Q F hq4
  have hpt : Homogenization.lambdaSq Q (1 / 4) (Homogenization.MultiscaleExponent.finite 1)
      (Internal.Ch02.BookCh02.pointwiseCoeffField (Book.Ch02.cubeDomain Q) (F.coeffOn Q)) =
      lambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) a := by
    rw [← el]
  rw [hpt] at hold
  have hexp : (-1 / 2 : ℝ) = -(1 / 2 : ℝ) := by norm_num
  rw [hexp] at hold
  have hxpos : 0 < Real.rpow (Book.Ch02.lambdaSq Q (1 / 4)
      (Book.Ch02.MultiscaleExponent.finite 1) F) (-(1 / 2 : ℝ)) :=
    Real.rpow_pos_of_pos hLpos _
  have hpos := ea2_pos_of_rpow_le hxpos hold
  refine ⟨hpos, ?_⟩
  have hsq : ∀ {y : ℝ}, 0 < y → (Real.rpow y (-(1 / 2 : ℝ))) ^ 2 = y⁻¹ := by
    intro y hy
    rw [Real.rpow_eq_pow, ← Real.rpow_natCast, ← Real.rpow_mul hy.le]
    norm_num [Real.rpow_neg_one]
  have h1 : (Book.Ch02.lambdaSq Q (1 / 4) (Book.Ch02.MultiscaleExponent.finite 1) F)⁻¹ ≤
      (lambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) a)⁻¹ := by
    rw [← hsq hLpos, ← hsq hpos]
    exact pow_le_pow_left₀ hxpos.le hold 2
  have h2 := Book.Ch02.lambdaSqFinite_inv_le_change_exponent Q F (s := 1 / 4) (p := 1) (q := 2)
    hq4 (by norm_num) le_rfl (by norm_num)
  have h3 : (Book.Ch02.lambdaSq Q (1 / 4) (Book.Ch02.MultiscaleExponent.finite 2) F)⁻¹ ≤
      25 * Real.exp 4 * Real.rpow (1 / 4) (2 / 2 - 2 / 1) *
        (Book.Ch02.lambdaSq Q (1 / 4) (Book.Ch02.MultiscaleExponent.finite 1) F)⁻¹ := h2
  refine h3.trans ?_
  exact mul_le_mul_of_nonneg_left h1
    (mul_nonneg (by positivity) (Real.rpow_nonneg (by norm_num) _))

/-- **E-A2 (coarse-grained Poincaré on an origin cube)**, `e.sharp.Cone.poincare`. -/
theorem eng_poinc_cube (d : ℕ) [NeZero d] (B : ℝ) (hB : 1 ≤ B) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (n : ℕ) {lam Lam : ℝ} {a : CoeffField d} {sigma nu : ℝ},
        IsEllipticFieldOn lam Lam (cubeSet (originCube d (n : ℤ))) a → 0 < lam → lam ≤ Lam →
        0 < sigma → 0 < nu →
        (∀ x ∈ cubeSet (originCube d (n : ℤ)), symmPart (a x) = nu • (1 : Mat d)) →
        sigma⁻¹ * LambdaSq (originCube d (n : ℤ)) (1 / 4) (MultiscaleExponent.finite 1) a +
            sigma * (lambdaSq (originCube d (n : ℤ)) (1 / 4)
              (MultiscaleExponent.finite 1) a)⁻¹ ≤ B →
        ∀ (u : Vec d → ℝ) (g : Vec d → Vec d), IsSolOn a (engCube d n) u g →
          Real.sqrt (sigma / nu) * cubeFlat n u ≤ C * cubeGradL2 n g := by
  classical
  set Kc : ℝ := (d : ℝ) * Legacy.cubeNeumannW22CalderonZygmundConstant d *
    (3 : ℝ) ^ ((d : ℝ) + 1) * ((d : ℝ) * Real.sqrt
      ((1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - 1 / 8)))⁻¹)) with hKc
  set pdf : ℝ := Book.Ch03.poincareDiscountFactor (1 / 4)
    (Book.Ch02.MultiscaleExponent.finite 2) with hpdf
  set c2 : ℝ := 25 * Real.exp 4 * Real.rpow (1 / 4) (2 / 2 - 2 / 1) with hc2
  have hc2n : 0 ≤ c2 := mul_nonneg (by positivity) (Real.rpow_nonneg (by norm_num) _)
  have hpdf0 : 0 ≤ pdf := by
    rw [hpdf]
    unfold Book.Ch03.poincareDiscountFactor
    refine Real.rpow_nonneg ?_ _
    unfold Book.Ch02.geometricDiscount
    have : Real.rpow (3 : ℝ) (-(1 / 4 : ℝ) * 2) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    linarith only [this]
  have hP : 0 ≤ (d : ℝ) * Legacy.cubeNeumannW22CalderonZygmundConstant d := by
    have h := Homogenization.fullVectorPoincareCubeConstant_nonneg (originCube d 0)
    rwa [fullVectorPoincareCubeConstant_eq_dimensionConstant] at h
  have hKc0 : 0 ≤ Kc := by
    rw [hKc]
    exact mul_nonneg (mul_nonneg hP (Real.rpow_nonneg (by norm_num) _))
      (mul_nonneg (Nat.cast_nonneg d) (Real.sqrt_nonneg _))
  refine ⟨max 1 (Kc * pdf * Real.sqrt (c2 * B)), le_max_left _ _, ?_⟩
  intro n lam Lam a sigma nu hEll h0 hle hs hnu hsym hB' u g hsol
  obtain ⟨v, hvu, hvg⟩ := hsol
  have hflat : cubeFlat n u = cubeFlat n v.toH1.toFun := ea2_cubeFlat_congr_ae n hvu.symm
  have hgr : cubeGradL2 n g = cubeLpNorm (originCube d (n : ℤ)) 2
      (fun x => Real.sqrt (vecNormSq (v.toH1.grad x))) := by
    rw [ea2_cubeGradL2_congr_ae n hvg.symm]
    rfl
  rw [hflat, hgr]
  set Q := originCube d (n : ℤ) with hQdef
  set G : ℝ := cubeLpNorm Q 2 (fun x => Real.sqrt (vecNormSq (v.toH1.grad x))) with hG
  have hG0 : 0 ≤ G := cubeLpNorm_nonneg _ _ _
  -- fluctuation to negative Besov
  have hfl := Book.Ch03.cubeBesovScaleWeight_one_mul_cubeLpNorm_fluctuation_le_grad_negativeBesovTwo
    (Q := Q) (t := 1 / 8) v.toH1 (by norm_num) (by norm_num)
  have hPoinc : Book.Ch01.Legacy.fullVectorPoincareConstant Q =
      (d : ℝ) * Legacy.cubeNeumannW22CalderonZygmundConstant d := by
    simp only [Book.Ch01.Legacy.fullVectorPoincareConstant,
      fullVectorPoincareCubeConstant_eq_dimensionConstant]
  rw [hPoinc, show (2 : ℝ) * (1 / 8) = 1 / 4 by norm_num] at hfl
  have hweight : cubeBesovScaleWeight (1 : ℝ) Q = ((3 : ℝ)⁻¹) ^ n := by
    simp [cubeBesovScaleWeight, hQdef, Real.rpow_neg_one]
  rw [hweight] at hfl
  have hKc' : ((d : ℝ) * Legacy.cubeNeumannW22CalderonZygmundConstant d *
      (3 : ℝ) ^ ((d : ℝ) + 1)) * ((d : ℝ) * Real.sqrt
        ((1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - 1 / 8)))⁻¹)) = Kc := rfl
  rw [hKc'] at hfl
  have hfluct : cubeFlat n v.toH1.toFun ≤
      Kc * cubeBesovNegativeVectorSeminormTwo Q (1 / 4) v.toH1.grad := hfl
  -- the Poincare step
  have hbes := ea2_besov_le Q hEll h0 hle hnu hsym v
  -- ellipticity
  obtain ⟨hLpos, hL2⟩ := ea2_lower Q hEll h0 hle
  have hU0 : 0 ≤ LambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) a := by
    unfold LambdaSq LambdaSqFinite
    refine Real.rpow_nonneg (tsum_nonneg fun k => mul_nonneg
      (geometricWeight_nonneg k (by norm_num)) (Real.rpow_nonneg
        (maxDescendantBBlockNormAtScale_nonneg Q (by omega) a) _)) _
  have hlow : sigma * (lambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) a)⁻¹ ≤ B := by
    have : 0 ≤ sigma⁻¹ * LambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) a :=
      mul_nonneg (inv_nonneg.2 hs.le) hU0
    linarith only [hB', this]
  have hL2pos : 0 < Book.Ch02.lambdaSq Q (1 / 4) (Book.Ch02.MultiscaleExponent.finite 2)
      (HarmonicApprox.paddedFamily Q hEll h0 hle) :=
    Book.Ch02.lambdaSq_pos _ _ (by norm_num) (by norm_num)
  have hLinv : (Book.Ch02.lambdaSq Q (1 / 4) (Book.Ch02.MultiscaleExponent.finite 2)
      (HarmonicApprox.paddedFamily Q hEll h0 hle))⁻¹ ≤ c2 * B / sigma := by
    rw [le_div_iff₀ hs]
    have h1 : sigma * (lambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) a)⁻¹ ≤ B := hlow
    calc _ ≤ (c2 * (lambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) a)⁻¹) * sigma :=
          mul_le_mul_of_nonneg_right hL2 hs.le
      _ = c2 * (sigma * (lambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) a)⁻¹) := by ring
      _ ≤ c2 * B := mul_le_mul_of_nonneg_left h1 hc2n
  have hrpow : Real.rpow (Book.Ch02.lambdaSq Q (1 / 4) (Book.Ch02.MultiscaleExponent.finite 2)
      (HarmonicApprox.paddedFamily Q hEll h0 hle)) (-(1 / 2 : ℝ)) ≤
      Real.sqrt (c2 * B) * (Real.sqrt sigma)⁻¹ := by
    change (Book.Ch02.lambdaSq Q (1 / 4) (Book.Ch02.MultiscaleExponent.finite 2)
      (HarmonicApprox.paddedFamily Q hEll h0 hle)) ^ (-(1 / 2 : ℝ)) ≤ _
    rw [Real.rpow_neg hL2pos.le, ← Real.sqrt_eq_rpow, ← Real.sqrt_inv]
    calc _ ≤ Real.sqrt (c2 * B / sigma) := Real.sqrt_le_sqrt hLinv
      _ = _ := by rw [Real.sqrt_div (by positivity), div_eq_mul_inv]
  have hsn : 0 ≤ Real.sqrt nu := Real.sqrt_nonneg _
  have hN : cubeBesovNegativeVectorSeminormTwo Q (1 / 4) v.toH1.grad ≤
      pdf * (Real.sqrt (c2 * B) * (Real.sqrt sigma)⁻¹) * (Real.sqrt nu * G) :=
    hbes.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hrpow hpdf0) (mul_nonneg hsn hG0))
  have hsq : 0 < Real.sqrt sigma := Real.sqrt_pos.2 hs
  have hsnp : 0 < Real.sqrt nu := Real.sqrt_pos.2 hnu
  have hmain : Real.sqrt (sigma / nu) * cubeFlat n v.toH1.toFun ≤
      Kc * pdf * Real.sqrt (c2 * B) * G := by
    calc Real.sqrt (sigma / nu) * cubeFlat n v.toH1.toFun
        ≤ Real.sqrt (sigma / nu) * (Kc * (pdf * (Real.sqrt (c2 * B) * (Real.sqrt sigma)⁻¹) *
            (Real.sqrt nu * G))) :=
          mul_le_mul_of_nonneg_left (hfluct.trans (mul_le_mul_of_nonneg_left hN hKc0))
            (Real.sqrt_nonneg _)
      _ = Kc * pdf * Real.sqrt (c2 * B) * G := by
          rw [Real.sqrt_div hs.le]
          field_simp
  exact hmain.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hG0)


/-- Witness: for the identity field with `σ = ν = 1` and a suitable `B ≥ 1`, all hypotheses of
`eng_poinc_cube` hold, with the zero solution. -/
example (d : ℕ) [NeZero d] (n : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧
      IsEllipticFieldOn 1 1 (cubeSet (originCube d (n : ℤ))) (constantCoeffField (1 : Mat d)) ∧
      (∀ x ∈ cubeSet (originCube d (n : ℤ)),
        symmPart (constantCoeffField (1 : Mat d) x) = (1 : ℝ) • (1 : Mat d)) ∧
      (1 : ℝ)⁻¹ * LambdaSq (originCube d (n : ℤ)) (1 / 4) (MultiscaleExponent.finite 1)
            (constantCoeffField (1 : Mat d)) +
          1 * (lambdaSq (originCube d (n : ℤ)) (1 / 4) (MultiscaleExponent.finite 1)
            (constantCoeffField (1 : Mat d)))⁻¹ ≤ B ∧
      IsSolOn (constantCoeffField (1 : Mat d)) (engCube d n) (fun _ => 0) (fun _ => 0) := by
  refine ⟨max 1 ((4 * (d : ℝ) ^ 3 * ((1 - (3 : ℝ) ^ (-(1 / 9 : ℝ) * 2))⁻¹ + 1)) *
        ((HomogenizationErrorOnCube (originCube d (n : ℤ)) (1 / 9) MultiscaleExponent.infinity
          (MultiscaleExponent.finite 2) (constantCoeffField (1 : Mat d))
          ((1 : ℝ) • (1 : Mat d))) ^ 2 + 1)), le_max_left _ _,
    regEllipticity_witness _, ?_,
    (regEllipticity_of_error _ (regEllipticity_witness _) one_pos le_rfl one_pos).trans
      (le_max_right _ _), ⟨⟨0, isAHarmonicGradient_zero⟩, Filter.EventuallyEq.rfl,
        Filter.EventuallyEq.rfl⟩⟩
  intro x _
  ext i j
  by_cases h : i = j
  · subst h
    simp [symmPart, constantCoeffField]
  · simp [symmPart, constantCoeffField, h, Ne.symm h]

end
end SuperdiffusionCLT.Section6
