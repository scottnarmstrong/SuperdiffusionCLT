/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Prereq.HarmonicApprox
public import Homogenization.Book.Ch03.Theorems.CoarsePoincare
public import Homogenization.Book.Ch03.Theorems.PublicInternalBridges.EndPoints

/-!
# The weak-gradient bound on a cube

Deterministic form of the weak-gradient bullet of the sharp-scale inputs: if a field `a` is
elliptic on `cu_n` with symmetric part `ν Id` and the homogenization error
`𝓔_{1/9,∞,2}(cu_n; a, σ Id)` is at most `δ`, then every `a`-harmonic function `u` on the open
cube satisfies
`3^{-n/4}‖∇u‖_{H̲^{-1/4}(cu_n)} ≤ C (1 + δ) σ^{-1/2} ν^{1/2} ‖∇u‖_{L̲²(cu_n)}`.

The route is the coarse-grained Poincaré inequality of `CoarseGraining` at `s = 1/4`, `q = 2`
(public circ seminorm), the bound of `λ_{1/4,2}` by `𝓔_{1/4,∞,2}`, the comparison of `𝓔` at
`s = 1/4` with `s = 1/9`, and the dual-to-circ bridge `dual ≤ C · circ` of the public norms.

## Main results

* `weakGrad_deterministic`: the estimate with a general bound `δ` of the error.
* `weakGrad_deterministic_of_le_one`: the estimate for `δ = 1`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6.WeakGrad

open Homogenization SuperdiffusionCLT.Section6.HarmonicApprox

noncomputable section

variable {d : ℕ}

/-- An `a`-harmonic function on the open cube is a public solution for the padded family,
with the same gradient. -/
theorem weakGrad_exists_solution [NeZero d] (Q : TriadicCube d) {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a) (h0 : 0 < lam) (hle : lam ≤ Lam)
    (u : AHarmonicFunction a (openCubeSet Q)) :
    ∃ v : Book.Ch03.CubeSolution Q (paddedFamily Q hEll h0 hle),
      v.toH1 = u.toH1 := by
  have hae : a =ᵐ[volumeMeasureOn (openCubeSet Q)] padField Q lam a := by
    have h1 : ∀ᵐ x ∂ volumeMeasureOn (openCubeSet Q), x ∈ openCubeSet Q := by
      unfold volumeMeasureOn
      exact MeasureTheory.ae_restrict_mem (measurableSet_openCubeSet Q)
    filter_upwards [h1] with x hx
    rw [padField_apply_of_mem (openCubeSet_subset_cubeSet Q hx)]
  exact ⟨⟨u.toH1, IsAHarmonicGradient.of_ae_eq_coeff hae u.isHarmonic⟩, rfl⟩

/-- The coefficient energy of a public solution for a field with symmetric part `nu • Id`. -/
theorem weakGrad_energy [NeZero d] (Q : TriadicCube d) {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a) (h0 : 0 < lam) (hle : lam ≤ Lam)
    {nu : ℝ}
    (hsym : ∀ x ∈ cubeSet Q, symmPart (a x) = nu • (1 : Mat d))
    (v : Book.Ch03.CubeSolution Q (paddedFamily Q hEll h0 hle)) :
    Book.Ch02.variationEnergyValue (Book.Ch02.cubeDomain Q)
        ((paddedFamily Q hEll h0 hle).coeffOn Q) v =
      nu * (cubeLpNorm Q 2 (fun x => Real.sqrt (vecNormSq (v.toH1.grad x)))) ^ 2 := by
  have hsq : (cubeLpNorm Q 2 (fun x => Real.sqrt (vecNormSq (v.toH1.grad x)))) ^ 2 =
      Book.Ch03.normalizedL2SqOnSet (openCubeSet Q)
        (fun x => Real.sqrt (vecNormSq (v.toH1.grad x))) :=
    (Book.Ch03.normalizedL2SqOnSet_openCubeSet_eq_cubeLpNorm_two_sq Q _
      (memLp_sqrt_vecNormSq_grad v.toH1)).symm
  rw [hsq]
  unfold Book.Ch02.variationEnergyValue Book.Ch03.normalizedL2SqOnSet
    Book.Ch03.normalizedSetAverage
  rw [Internal.Ch02.book_average_eq_volumeAverage]
  have hpt : ∀ x ∈ openCubeSet Q,
      Book.Ch02.variationEnergyIntegrand (Book.Ch02.cubeDomain Q)
        ((paddedFamily Q hEll h0 hle).coeffOn Q) v x =
      nu * (Real.sqrt (vecNormSq (v.toH1.grad x))) ^ 2 := by
    intro x hx
    have hxc := openCubeSet_subset_cubeSet Q hx
    unfold Book.Ch02.variationEnergyIntegrand
    change vecDot (v.toH1.grad x) (matVecMul (symmPart (padField Q lam a x)) (v.toH1.grad x)) = _
    rw [padField_apply_of_mem hxc, hsym x hxc, Real.sq_sqrt (vecNormSq_nonneg _)]
    show vecDot (v.toH1.grad x) (matVecMul (scalarMatrix nu) (v.toH1.grad x)) = nu * vecNormSq (v.toH1.grad x)
    rw [matVecMul_scalarMatrix, vecDot_smul_right]
    rfl
  unfold volumeAverage
  change (MeasureTheory.volume (openCubeSet Q)).toReal⁻¹ * ∫ x in openCubeSet Q,
    Book.Ch02.variationEnergyIntegrand (Book.Ch02.cubeDomain Q)
        ((paddedFamily Q hEll h0 hle).coeffOn Q) v x = _
  rw [MeasureTheory.setIntegral_congr_fun (measurableSet_openCubeSet Q) hpt,
    MeasureTheory.integral_const_mul]
  ring

/-- Monotonicity of `𝓔² + 1` in the exponent `s`, up to the geometric normalization. -/
theorem weakGrad_errorSq_mono [NeZero d] (Q : TriadicCube d) (a : Book.Ch03.CoeffFamily d)
    (a0 : Mat d) {s s' : ℝ} (hs : 0 < s) (hss : s ≤ s') :
    Book.Ch02.HomogenizationErrorOnCube Q s' Book.Ch02.MultiscaleExponent.infinity
        (Book.Ch02.MultiscaleExponent.finite 2) a a0 ^ 2 + 1 ≤
      (Book.Ch02.geometricDiscount s 2)⁻¹ *
        (Book.Ch02.HomogenizationErrorOnCube Q s Book.Ch02.MultiscaleExponent.infinity
          (Book.Ch02.MultiscaleExponent.finite 2) a a0 ^ 2 + 1) := by
  have hs' : 0 < s' := lt_of_lt_of_le hs hss
  let M : ℕ → ℝ := fun n =>
    Book.Ch02.maxDescendantNormalizedBlockResponseAtScale Q (Q.scale - (n : ℤ)) a a0
  have hM : ∀ n, 0 ≤ M n := fun n =>
    Book.Ch02.maxDescendantNormalizedBlockResponseAtScale_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a a0
  have hsumR : ∀ {t : ℝ}, 0 < t →
      Summable (fun n : ℕ => Book.Ch02.geometricWeight t 2 n * (M n + 1)) := by
    intro t ht
    have hsumM : Summable (fun n : ℕ => Book.Ch02.geometricWeight t 2 n * M n) :=
      Book.Ch02.summable_geometricWeight_two_mul_maxDescendantNormalizedBlockResponseAtScale
        Q a a0 ht
    have hsumW : Summable (fun n : ℕ => Book.Ch02.geometricWeight t 2 n) := by
      simpa [Book.Ch02.geometricWeight_eq_old] using
        Homogenization.summable_geometricWeight (s := t) (q := 2)
          (by nlinarith only [ht] : 0 < t * (2 : ℝ))
    simpa [mul_add] using hsumM.add hsumW
  have hdisc : 0 < Book.Ch02.geometricDiscount s 2 := by
    unfold Book.Ch02.geometricDiscount
    have : Real.rpow (3 : ℝ) (-s * 2) < 1 := by
      apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      nlinarith only [hs]
    linarith only [this]
  have hterm : ∀ n : ℕ, Book.Ch02.geometricWeight s' 2 n * (M n + 1) ≤
      (Book.Ch02.geometricDiscount s 2)⁻¹ *
        (Book.Ch02.geometricWeight s 2 n * (M n + 1)) := by
    intro n
    have hw : Book.Ch02.geometricWeight s' 2 n ≤
        (Book.Ch02.geometricDiscount s 2)⁻¹ * Book.Ch02.geometricWeight s 2 n := by
      unfold Book.Ch02.geometricWeight
      have hd' : Book.Ch02.geometricDiscount s' 2 ≤ 1 := by
        unfold Book.Ch02.geometricDiscount
        have : 0 < Real.rpow (3 : ℝ) (-s' * 2) := Real.rpow_pos_of_pos (by norm_num) _
        linarith only [this]
      have hp : Real.rpow (3 : ℝ) (-s' * 2 * (n : ℝ)) ≤ Real.rpow (3 : ℝ) (-s * 2 * (n : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        nlinarith only [hss, this]
      have hp0 : 0 < Real.rpow (3 : ℝ) (-s' * 2 * (n : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
      rw [← mul_assoc, inv_mul_cancel₀ hdisc.ne', one_mul]
      calc Book.Ch02.geometricDiscount s' 2 * Real.rpow (3 : ℝ) (-s' * 2 * (n : ℝ))
          ≤ 1 * Real.rpow (3 : ℝ) (-s' * 2 * (n : ℝ)) :=
            mul_le_mul_of_nonneg_right hd' hp0.le
        _ ≤ _ := by rw [one_mul]; exact hp
    calc Book.Ch02.geometricWeight s' 2 n * (M n + 1)
        ≤ ((Book.Ch02.geometricDiscount s 2)⁻¹ * Book.Ch02.geometricWeight s 2 n) * (M n + 1) :=
          mul_le_mul_of_nonneg_right hw (by linarith only [hM n])
      _ = _ := by ring
  rw [← Book.Ch02.tsum_geometricWeight_two_mul_maxResponse_add_one_eq_homogenizationError_sq_add_one
      Q a a0 hs',
    ← Book.Ch02.tsum_geometricWeight_two_mul_maxResponse_add_one_eq_homogenizationError_sq_add_one
      Q a a0 hs, ← tsum_mul_left]
  exact (hsumR hs').tsum_le_tsum hterm ((hsumR hs).mul_left _)

theorem weakGrad_error_nonneg [NeZero d] (Q : TriadicCube d) (a : Book.Ch03.CoeffFamily d)
    (a0 : Mat d) {s : ℝ} (hs : 0 < s) :
    0 ≤ Book.Ch02.HomogenizationErrorOnCube Q s Book.Ch02.MultiscaleExponent.infinity
      (Book.Ch02.MultiscaleExponent.finite 2) a a0 := by
  unfold Book.Ch02.HomogenizationErrorOnCube Book.Ch02.HomogenizationError
    Book.Ch02.HomogenizationErrorFinite
  refine Real.rpow_nonneg (tsum_nonneg fun n => ?_) _
  change 0 ≤ _ * ((_ : ℝ) ^ (2 : ℝ))
  rw [Real.rpow_two]
  exact mul_nonneg (by
    unfold Book.Ch02.geometricWeight Book.Ch02.geometricDiscount
    have h1 : Real.rpow (3 : ℝ) (-s * 2) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by nlinarith only [hs])
    exact mul_nonneg (by linarith only [h1]) (Real.rpow_nonneg (by norm_num) _)) (sq_nonneg _)

/-- **Weak gradient bound (deterministic form).** For a field `a`, elliptic on `cu_n`, with
symmetric part `ν Id`, and `σ > 0` with `𝓔_{1/9,∞,2}(cu_n; a, σ Id) ≤ 1`, every `a`-harmonic
function `u` on the open cube satisfies
`3^{-n/4}‖∇u‖_{H̲^{-1/4}(cu_n)} ≤ C σ^{-1/2} ν^{1/2} ‖∇u‖_{L̲²(cu_n)}`, with `C = C(d)`. -/
theorem weakGrad_deterministic (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℤ) {lam Lam : ℝ} {a : CoeffField d} {sigma nu delta : ℝ},
      IsEllipticFieldOn lam Lam (cubeSet (originCube d n)) a → 0 < sigma → 0 < nu →
      (∀ x ∈ cubeSet (originCube d n), symmPart (a x) = nu • (1 : Mat d)) →
      HomogenizationErrorOnCube (originCube d n) (1 / 9) MultiscaleExponent.infinity
        (MultiscaleExponent.finite 2) a (sigma • (1 : Mat d)) ≤ delta →
      ∀ u : AHarmonicFunction a (openCubeSet (originCube d n)),
        ENNReal.ofReal
            (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo (originCube d n) (1 / 4)
              u.toH1.grad) ≤
          ENNReal.ofReal (C * (1 + delta) * (Real.sqrt sigma)⁻¹ * Real.sqrt nu) *
            SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d n) 2
              (fun x => Real.sqrt (vecNormSq (u.toH1.grad x))) := by
  let c : ℝ := (Book.Ch02.geometricDiscount (1 / 9) 2)⁻¹
  let K : ℝ := (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1 / 4) *
    Book.Ch03.poincareDiscountFactor (1 / 4) (Book.Ch02.MultiscaleExponent.finite 2) *
    Real.sqrt (2 * (d : ℝ) * c)
  have hdisc : 0 < Book.Ch02.geometricDiscount (1 / 9) 2 := by
    unfold Book.Ch02.geometricDiscount
    have : Real.rpow (3 : ℝ) (-(1 / 9 : ℝ) * 2) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    linarith only [this]
  have hc : 0 < c := inv_pos.2 hdisc
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hpd : 0 < Book.Ch03.poincareDiscountFactor (1 / 4) (Book.Ch02.MultiscaleExponent.finite 2) := by
    unfold Book.Ch03.poincareDiscountFactor
    refine Real.rpow_pos_of_pos ?_ _
    unfold Book.Ch02.geometricDiscount
    have : Real.rpow (3 : ℝ) (-(1 / 4 : ℝ) * 2) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    linarith only [this]
  have hK : 0 < K := by
    have : 0 < Real.sqrt (2 * (d : ℝ) * c) := Real.sqrt_pos.2 (by positivity)
    have h3 : 0 < Real.rpow (3 : ℝ) ((d : ℝ) + 1 / 4) := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  refine ⟨K, hK, ?_⟩
  intro n lam Lam a sigma nu delta hEll hs hnu hsym hE u
  obtain ⟨x0, hx0⟩ := Book.Ch02.openCubeSet_nonempty (originCube d n)
  have hell0 := hEll.2 x0 (openCubeSet_subset_cubeSet _ hx0)
  have h0 : 0 < lam := hell0.1
  have hle : lam ≤ Lam := hell0.2.1
  obtain ⟨v, hv⟩ := weakGrad_exists_solution (originCube d n) hEll h0 hle u
  have hgrad : v.toH1.grad = u.toH1.grad := by rw [hv]
  have hpo := Book.Ch03.coarsePoincareGradient_negativeBesov_le (originCube d n)
    (paddedFamily (originCube d n) hEll h0 hle) (s := 1 / 4)
    (q := Book.Ch02.MultiscaleExponent.finite 2) v (by norm_num) (by norm_num)
  have hmem : MemVectorL2 (cubeSet (originCube d n)) u.toH1.grad := by
    simpa [MemVectorL2, volumeMeasureOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using u.toH1.grad_memVectorL2
  have hdual :=
    Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo_le_note_constant_mul_cubeBesovNegativeVectorSeminormTwo
      (originCube d n) (1 / 4) u.toH1.grad (by norm_num) hmem
  have hcirc_eq :=
    Book.Ch03.scaleNormalizedNegativeBesovVectorNorm_finite_two_eq_cubeBesovNegativeVectorSeminormTwo
      (originCube d n) (1 / 4) u.toH1.grad
  have hG0 : 0 ≤ cubeLpNorm (originCube d n) 2 (fun x => Real.sqrt (vecNormSq (u.toH1.grad x))) :=
    cubeLpNorm_nonneg _ _ _
  have hen := weakGrad_energy (originCube d n) hEll h0 hle hsym v
  rw [hgrad] at hen
  have hsqrt_en : Book.Ch03.solutionEnergyNorm (originCube d n)
      (paddedFamily (originCube d n) hEll h0 hle) v =
      Real.sqrt nu * cubeLpNorm (originCube d n) 2
        (fun x => Real.sqrt (vecNormSq (u.toH1.grad x))) := by
    unfold Book.Ch03.solutionEnergyNorm
    rw [hen, Real.sqrt_mul hnu.le, Real.sqrt_sq hG0]
  have hpo' : cubeBesovNegativeVectorSeminormTwo (originCube d n) (1 / 4) u.toH1.grad ≤
      Book.Ch03.poincareDiscountFactor (1 / 4) (Book.Ch02.MultiscaleExponent.finite 2) *
        (Real.rpow (Book.Ch02.lambdaSq (originCube d n) (1 / 4)
          (Book.Ch02.MultiscaleExponent.finite 2) (paddedFamily (originCube d n) hEll h0 hle))
          (-(1 / 2 : ℝ))) *
        (Real.sqrt nu * cubeLpNorm (originCube d n) 2
          (fun x => Real.sqrt (vecNormSq (u.toH1.grad x)))) := by
    have h := hpo
    unfold Book.Ch03.coarsePoincareGradientRHS Book.Ch03.poincareLowerEllipticityFactor at h
    rw [hsqrt_en] at h
    have e : Book.Ch03.solutionGradientField v = u.toH1.grad := hgrad
    rw [e, hcirc_eq] at h
    exact h
  -- the ellipticity bound
  have hLpos : 0 < Book.Ch02.lambdaSq (originCube d n) (1 / 4)
      (Book.Ch02.MultiscaleExponent.finite 2) (paddedFamily (originCube d n) hEll h0 hle) :=
    Book.Ch02.lambdaSq_pos _ _ (by norm_num) (by norm_num)
  have hlam := Book.Ch02.sigma_mul_lambdaSq_finite_two_inv_le_card_mul_homogenizationError_sq_add_one
    (originCube d n) (paddedFamily (originCube d n) hEll h0 hle) (s := 1 / 4) (σ := sigma)
    (by norm_num) hs
  have hE9 : Book.Ch02.HomogenizationErrorOnCube (originCube d n) (1 / 9)
      Book.Ch02.MultiscaleExponent.infinity (Book.Ch02.MultiscaleExponent.finite 2)
      (paddedFamily (originCube d n) hEll h0 hle) (scalarMatrix (d := d) sigma) ≤ delta := by
    rw [← homogenizationErrorOnCube_eq_ch02 hEll h0 hle (1 / 9) 2 (sigma • (1 : Mat d))]
    exact hE
  have hE90 := weakGrad_error_nonneg (originCube d n) (paddedFamily (originCube d n) hEll h0 hle)
    (scalarMatrix (d := d) sigma) (s := 1 / 9) (by norm_num)
  have hmono := weakGrad_errorSq_mono (originCube d n) (paddedFamily (originCube d n) hEll h0 hle)
    (scalarMatrix (d := d) sigma) (s := 1 / 9) (s' := 1 / 4) (by norm_num) (by norm_num)
  have hdelta : 0 ≤ delta := hE90.trans hE9
  have hsq1 : Book.Ch02.HomogenizationErrorOnCube (originCube d n) (1 / 9)
      Book.Ch02.MultiscaleExponent.infinity (Book.Ch02.MultiscaleExponent.finite 2)
      (paddedFamily (originCube d n) hEll h0 hle) (scalarMatrix (d := d) sigma) ^ 2 + 1 ≤
      (1 + delta) ^ 2 := by
    nlinarith only [hE9, hE90]
  have hcard : (Fintype.card (Fin d) : ℝ) = d := by simp
  rw [hcard] at hlam
  have hLinv : (Book.Ch02.lambdaSq (originCube d n) (1 / 4)
      (Book.Ch02.MultiscaleExponent.finite 2) (paddedFamily (originCube d n) hEll h0 hle))⁻¹ ≤
      2 * (d : ℝ) * c * (1 + delta) ^ 2 / sigma := by
    rw [le_div_iff₀ hs]
    have h2 : 2 * (d : ℝ) * (Book.Ch02.HomogenizationErrorOnCube (originCube d n) (1 / 4)
        Book.Ch02.MultiscaleExponent.infinity (Book.Ch02.MultiscaleExponent.finite 2)
        (paddedFamily (originCube d n) hEll h0 hle) (scalarMatrix (d := d) sigma) ^ 2 + 1) ≤
        2 * (d : ℝ) * (c * (1 + delta) ^ 2) := by
      refine mul_le_mul_of_nonneg_left (hmono.trans ?_) (by positivity)
      exact mul_le_mul_of_nonneg_left hsq1 hc.le
    nlinarith only [hlam, h2]
  have hrpow : Real.rpow (Book.Ch02.lambdaSq (originCube d n) (1 / 4)
      (Book.Ch02.MultiscaleExponent.finite 2) (paddedFamily (originCube d n) hEll h0 hle))
      (-(1 / 2 : ℝ)) ≤ Real.sqrt (2 * (d : ℝ) * c) * (1 + delta) * (Real.sqrt sigma)⁻¹ := by
    change (Book.Ch02.lambdaSq (originCube d n) (1 / 4)
      (Book.Ch02.MultiscaleExponent.finite 2) (paddedFamily (originCube d n) hEll h0 hle)) ^
      (-(1 / 2 : ℝ)) ≤ _
    rw [Real.rpow_neg hLpos.le, ← Real.sqrt_eq_rpow, ← Real.sqrt_inv]
    calc _ ≤ Real.sqrt (2 * (d : ℝ) * c * (1 + delta) ^ 2 / sigma) := Real.sqrt_le_sqrt hLinv
      _ = _ := by
        rw [Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity),
          Real.sqrt_sq (by linarith only [hdelta]), div_eq_mul_inv]
  have hGL2 := memLp_sqrt_vecNormSq_grad u.toH1
  have hGE : SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d n) 2
      (fun x => Real.sqrt (vecNormSq (u.toH1.grad x))) = ENNReal.ofReal (cubeLpNorm (originCube d n) 2
        (fun x => Real.sqrt (vecNormSq (u.toH1.grad x)))) := by
    unfold SuperdiffusionCLT.Section2.Norms.cubeLpENorm cubeLpNorm
    rw [ENNReal.ofReal_toReal hGL2.eLpNorm_lt_top.ne]
  have hsn : 0 ≤ Real.sqrt nu := Real.sqrt_nonneg _
  have hK3 : 0 ≤ (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1 / 4) :=
    mul_nonneg hd.le (Real.rpow_nonneg (by norm_num) _)
  have hmain : Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo (originCube d n) (1 / 4)
      u.toH1.grad ≤ K * (1 + delta) * (Real.sqrt sigma)⁻¹ * Real.sqrt nu *
        cubeLpNorm (originCube d n) 2 (fun x => Real.sqrt (vecNormSq (u.toH1.grad x))) := by
    calc _ ≤ (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1 / 4) *
          cubeBesovNegativeVectorSeminormTwo (originCube d n) (1 / 4) u.toH1.grad := hdual
      _ ≤ (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1 / 4) *
          (Book.Ch03.poincareDiscountFactor (1 / 4) (Book.Ch02.MultiscaleExponent.finite 2) *
            (Real.sqrt (2 * (d : ℝ) * c) * (1 + delta) * (Real.sqrt sigma)⁻¹) *
            (Real.sqrt nu * cubeLpNorm (originCube d n) 2
              (fun x => Real.sqrt (vecNormSq (u.toH1.grad x))))) := by
        refine mul_le_mul_of_nonneg_left (hpo'.trans ?_) hK3
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hrpow hpd.le) (mul_nonneg hsn hG0)
      _ = _ := by simp only [K]; ring
  rw [hGE, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hmain

/-- The form fed by the sharp-scale assembly: the homogenization error is at most `1`. -/
theorem weakGrad_deterministic_of_le_one (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℤ) {lam Lam : ℝ} {a : CoeffField d} {sigma nu : ℝ},
      IsEllipticFieldOn lam Lam (cubeSet (originCube d n)) a → 0 < sigma → 0 < nu →
      (∀ x ∈ cubeSet (originCube d n), symmPart (a x) = nu • (1 : Mat d)) →
      HomogenizationErrorOnCube (originCube d n) (1 / 9) MultiscaleExponent.infinity
        (MultiscaleExponent.finite 2) a (sigma • (1 : Mat d)) ≤ 1 →
      ∀ u : AHarmonicFunction a (openCubeSet (originCube d n)),
        ENNReal.ofReal
            (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo (originCube d n) (1 / 4)
              u.toH1.grad) ≤
          ENNReal.ofReal (C * (Real.sqrt sigma)⁻¹ * Real.sqrt nu) *
            SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d n) 2
              (fun x => Real.sqrt (vecNormSq (u.toH1.grad x))) := by
  obtain ⟨K, hK, h⟩ := weakGrad_deterministic d
  refine ⟨2 * K, by positivity, ?_⟩
  intro n lam Lam a sigma nu hEll hs hnu hsym hE u
  simpa only [show K * (1 + 1) = 2 * K by ring] using
    h n (delta := 1) hEll hs hnu hsym hE u

end
end SuperdiffusionCLT.Section6.WeakGrad
