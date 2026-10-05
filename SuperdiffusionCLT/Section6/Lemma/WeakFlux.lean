/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Prereq.HarmonicApprox
public import SuperdiffusionCLT.Section6.Prereq.HarmonicApproxBridge

/-!
# Weak flux estimate: the circ seminorm of the flux defect

This is Lemma `l.sharp.scale.inputs`, bullet `e.Dir.new.weak.flux`.
The coarse-graining black box of `CoarseGraining` bounds the circ seminorm (which contains the
depth-zero average of the field over the cube) of `a ∇u - σ ∇u`. This file proves the two inputs:

* `l6_error_one_le_two_of_lt`: the `q = 1` error at order `s` is bounded by the `q = 2` error at
  any smaller order `t < s` (weighted Cauchy-Schwarz). With `s = 17/144` and `t = 1/9` this turns
  the `𝓔_{1/9,∞,2}` of the good event into the `𝓔_{r,∞,1}` that the black box consumes at
  exponent `1/4` (which needs `r < 1/8`).
* `l6_circ_le_comparison_lhs`: the circ seminorm of `(a - σ) ∇u` is at most `√2` times the
  left-hand side of the comparison estimate.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6.WeakFlux

open Homogenization
open SuperdiffusionCLT.Section6.HarmonicApprox

noncomputable section

variable {d : ℕ} [NeZero d]

theorem l6_rpow_split (t s : ℝ) (n : ℕ) :
    Real.rpow (3 : ℝ) (-s * 1 * (n : ℝ)) =
      Real.rpow (3 : ℝ) (-(s - t) * (n : ℝ)) * Real.rpow (3 : ℝ) (-t * (n : ℝ)) := by
  show (3 : ℝ) ^ (-s * 1 * (n : ℝ)) = (3 : ℝ) ^ (-(s - t) * (n : ℝ)) * (3 : ℝ) ^ (-t * (n : ℝ))
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  ring

theorem l6_rpow_sq (t : ℝ) (n : ℕ) :
    Real.rpow (3 : ℝ) (-t * 2 * (n : ℝ)) = (Real.rpow (3 : ℝ) (-t * (n : ℝ))) ^ 2 := by
  have h : Real.rpow (3 : ℝ) (-t * 2 * (n : ℝ)) = (3 : ℝ) ^ ((-t * (n : ℝ)) * 2) := by
    show (3 : ℝ) ^ (-t * 2 * (n : ℝ)) = _
    congr 1
    ring
  rw [h, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  show ((3 : ℝ) ^ (-t * (n : ℝ))) ^ (2 : ℝ) = _
  rw [Real.rpow_two]
  rfl

theorem l6_rpow_pow (x : ℝ) (n : ℕ) :
    (Real.rpow (3 : ℝ) x) ^ n = Real.rpow (3 : ℝ) (x * (n : ℝ)) := by
  show ((3 : ℝ) ^ x) ^ n = (3 : ℝ) ^ (x * (n : ℝ))
  rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_natCast]

/-- The `q = 1` error at order `s` is bounded by the `q = 2` error at any strictly smaller
order `t`, with an explicit geometric constant (weighted Cauchy--Schwarz). -/
theorem l6_error_one_le_two_of_lt (R : TriadicCube d) (a : Book.Ch02.TriadicCoeffFamily d)
    (a0 : Mat d) {t s : ℝ} (ht : 0 < t) (hts : t < s) :
    Book.Ch02.HomogenizationErrorOnCube R s .infinity (.finite 1) a a0 ≤
      Real.sqrt ((Book.Ch02.geometricDiscount s 1) ^ 2 /
          (Book.Ch02.geometricDiscount t 2 * (1 - (3 : ℝ) ^ (-(2 * (s - t)))))) *
        Book.Ch02.HomogenizationErrorOnCube R t .infinity (.finite 2) a a0 := by
  have hs : 0 < s := ht.trans hts
  set M : ℕ → ℝ := fun n =>
    Book.Ch02.maxDescendantNormalizedBlockResponseAtScale R (R.scale - (n : ℤ)) a a0 with hMdef
  have hM_nonneg : ∀ n, 0 ≤ M n := fun n =>
    Book.Ch02.maxDescendantNormalizedBlockResponseAtScale_nonneg R
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a a0
  have hc2 : 0 < Book.Ch02.geometricDiscount t 2 := by
    unfold Book.Ch02.geometricDiscount
    have : Real.rpow (3 : ℝ) (-t * 2) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [ht])
    linarith only [this]
  have hc1 : 0 ≤ Book.Ch02.geometricDiscount s 1 := by
    unfold Book.Ch02.geometricDiscount
    have : Real.rpow (3 : ℝ) (-s * 1) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hs])
    linarith only [this]
  set c1 := Book.Ch02.geometricDiscount s 1 with hc1def
  set c2 := Book.Ch02.geometricDiscount t 2 with hc2def
  set rho : ℝ := Real.rpow (3 : ℝ) (-(s - t)) with hrho
  have hrho_pos : 0 < rho := Real.rpow_pos_of_pos (by norm_num) _
  have hrho_lt : rho < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hts])
  have hrho2 : rho ^ 2 = (3 : ℝ) ^ (-(2 * (s - t))) := by
    rw [hrho, l6_rpow_pow]
    show (3 : ℝ) ^ (-(s - t) * ((2 : ℕ) : ℝ)) = _
    congr 1
    push_cast
    ring
  have hrho2_lt : rho ^ 2 < 1 := by
    have := pow_lt_one₀ hrho_pos.le hrho_lt (by norm_num : (2 : ℕ) ≠ 0)
    exact this
  set K0 : ℝ := c1 / Real.sqrt c2 with hK0
  let f : ℕ → ℝ := fun n => K0 * rho ^ n
  let g : ℕ → ℝ := fun n => Real.sqrt (Book.Ch02.geometricWeight t 2 n * M n)
  have hf_nonneg : ∀ n, 0 ≤ f n := fun n =>
    mul_nonneg (div_nonneg hc1 (Real.sqrt_nonneg _)) (pow_nonneg hrho_pos.le _)
  have hg_nonneg : ∀ n, 0 ≤ g n := fun n => Real.sqrt_nonneg _
  have hw2 : ∀ n, 0 ≤ Book.Ch02.geometricWeight t 2 n := by
    intro n
    simpa [Book.Ch02.geometricWeight_eq_old] using
      (Homogenization.geometricWeight_nonneg (s := t) (q := (2 : ℝ)) n (by positivity))
  have hf_sq : ∀ n, f n ^ (2 : ℝ) = c1 ^ 2 / c2 * (rho ^ 2) ^ n := by
    intro n
    dsimp only [f]
    rw [Real.rpow_two, mul_pow, hK0, div_pow, Real.sq_sqrt hc2.le, ← pow_mul, ← pow_mul,
      mul_comm 2 n]
  have hg_sq : ∀ n, g n ^ (2 : ℝ) = Book.Ch02.geometricWeight t 2 n * M n := by
    intro n
    dsimp only [g]
    rw [Real.rpow_two, Real.sq_sqrt (mul_nonneg (hw2 n) (hM_nonneg n))]
  have hfsum : Summable fun n => f n ^ (2 : ℝ) := by
    have h := (summable_geometric_of_lt_one (sq_nonneg rho) hrho2_lt).mul_left (c1 ^ 2 / c2)
    refine h.congr fun n => ?_
    exact (hf_sq n).symm
  have hsumWM : Summable (fun n => Book.Ch02.geometricWeight t 2 n * M n) :=
    Book.Ch02.summable_geometricWeight_two_mul_maxDescendantNormalizedBlockResponseAtScale
      R a a0 ht
  have hgsum : Summable fun n => g n ^ (2 : ℝ) := by
    refine hsumWM.congr fun n => ?_
    exact (hg_sq n).symm
  have hholder : Real.HolderConjugate (2 : ℝ) (2 : ℝ) := by
    refine ⟨by norm_num, by norm_num, by norm_num⟩
  have hcs := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg hholder hf_nonneg hg_nonneg hfsum hgsum
  have hfg : ∀ n, f n * g n =
      Book.Ch02.geometricWeight s 1 n * Real.sqrt (M n) := by
    intro n
    dsimp only [f, g]
    have hw : Book.Ch02.geometricWeight t 2 n = c2 * (Real.rpow (3 : ℝ) (-t * (n : ℝ))) ^ 2 := by
      unfold Book.Ch02.geometricWeight
      rw [l6_rpow_sq]
    have hw1 : Book.Ch02.geometricWeight s 1 n =
        c1 * (rho ^ n * Real.rpow (3 : ℝ) (-t * (n : ℝ))) := by
      unfold Book.Ch02.geometricWeight
      rw [l6_rpow_split t s n, hrho, l6_rpow_pow]
    have hsc2 : 0 < Real.sqrt c2 := Real.sqrt_pos.2 hc2
    have hpos : 0 < Real.rpow (3 : ℝ) (-t * (n : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    rw [hw, hw1, Real.sqrt_mul (mul_nonneg hc2.le (sq_nonneg _)), Real.sqrt_mul hc2.le,
      Real.sqrt_sq hpos.le, hK0]
    field_simp
  have hleft : ∑' n, f n * g n =
      Book.Ch02.HomogenizationErrorOnCube R s .infinity (.finite 1) a a0 := by
    rw [Book.Ch02.homogenizationErrorOnCube_infinity_one_eq_tsum]
    apply tsum_congr
    intro n
    rw [hfg]
    congr 1
    rw [show Book.Ch02.scaleResponseAtScale R (R.scale - (n : ℤ)) .infinity a a0 =
      Real.rpow (M n) (1 / 2 : ℝ) from rfl, Real.sqrt_eq_rpow]
    rfl
  have hright : (∑' n, g n ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) =
      Book.Ch02.HomogenizationErrorOnCube R t .infinity (.finite 2) a a0 := by
    unfold Book.Ch02.HomogenizationErrorOnCube Book.Ch02.HomogenizationError
      Book.Ch02.HomogenizationErrorFinite
    change (∑' n, g n ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) =
      (∑' n, Book.Ch02.geometricWeight t 2 n *
        (Book.Ch02.scaleResponseAtScale R (R.scale - (n : ℤ)) .infinity a a0) ^ (2 : ℝ)) ^
        (1 / (2 : ℝ))
    congr 1
    apply tsum_congr
    intro n
    rw [hg_sq]
    have hk : R.scale - (n : ℤ) ≤ R.scale :=
      sub_le_self _ (by exact_mod_cast Nat.zero_le n)
    have hresponse : M n =
        (Book.Ch02.scaleResponseAtScale R (R.scale - (n : ℤ)) .infinity a a0) ^ (2 : ℝ) := by
      calc
        M n = (Book.Ch02.scaleResponseAtScale R (R.scale - (n : ℤ)) .infinity a a0) ^ 2 :=
          (Book.Ch02.scaleResponseAtScale_infinity_sq_eq R hk a a0).symm
        _ = _ := (Real.rpow_two _).symm
    exact congrArg (fun x : ℝ => Book.Ch02.geometricWeight t 2 n * x) hresponse
  have hfs : (∑' n, f n ^ (2 : ℝ)) =
      c1 ^ 2 / (c2 * (1 - (3 : ℝ) ^ (-(2 * (s - t))))) := by
    have h1 : ∑' n, f n ^ (2 : ℝ) = c1 ^ 2 / c2 * ∑' n : ℕ, (rho ^ 2) ^ n := by
      rw [← tsum_mul_left]
      exact tsum_congr hf_sq
    rw [h1, tsum_geometric_of_lt_one (sq_nonneg rho) hrho2_lt, hrho2]
    have hne : (1 - (3 : ℝ) ^ (-(2 * (s - t)))) ≠ 0 := by
      rw [← hrho2]
      linarith only [hrho2_lt]
    field_simp
  rw [← hleft]
  calc ∑' n, f n * g n
      ≤ (∑' n, f n ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) * (∑' n, g n ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := hcs
    _ = _ := by
      rw [hright, hfs, ← Real.sqrt_eq_rpow]

/-- The circ seminorm of the flux defect `(a - σ) ∇u` is controlled by the left-hand side of
the comparison estimate (this includes the top-scale average, the depth-zero term). -/
theorem l6_circ_le_comparison_lhs (Q : TriadicCube d) {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a) (h0 : 0 < lam) (hle : lam ≤ Lam)
    {sigma : ℝ} (hs : 0 < sigma) (u : AHarmonicFunction a (openCubeSet Q))
    (w : H10Function (openCubeSet Q))
    (hw : ∀ ψ : H10Function (openCubeSet Q),
      ∫ x in openCubeSet Q, vecDot (w.toH1Function.grad x) (ψ.toH1Function.grad x) =
        ∫ x in openCubeSet Q, vecDot (u.toH1.grad x) (ψ.toH1Function.grad x))
    {s : ℝ} (hspos : 0 < s) :
    cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul (a x - sigma • (1 : Mat d)) (u.toH1.grad x)) ≤
      Real.sqrt 2 * Book.Ch03.homogenizationComparisonNegativeBesovLHS Q
        (paddedFamily Q hEll h0 hle) (constMat d hs) s
        (comparisonDatum Q hEll h0 hle hs u w hw).u
        (comparisonDatum Q hEll h0 hle hs u w hw).v := by
  set A := paddedFamily Q hEll h0 hle with hA
  set D := comparisonDatum Q hEll h0 hle hs u w hw with hD
  set G : Vec d → Vec d := fun x => sigma • w.toH1Function.grad x with hG
  have hF : MemVectorL2 (cubeSet Q)
      (fluxDefect (Book.Ch03.publicCoeffField Q A) (constMat d hs).matrix u.toH1.grad) :=
    Book.Ch03.publicH1_fluxDefect_memVectorL2_descendant_cubeSet (Q := Q) (R := Q) (a := A)
      (a0 := constMat d hs) (j := 0) u.toH1 (by simp)
  have hGm : MemVectorL2 (cubeSet Q) G := by
    have h1 : MemVectorL2 (cubeSet Q) w.toH1Function.grad :=
      Book.Ch03.publicH1ToCubeSet_grad_memVectorL2_descendant_cubeSet (Q := Q) (R := Q) (j := 0)
        w.toH1Function (by simp)
    exact MeasureTheory.MemLp.const_smul h1 sigma
  set F1 : Vec d → Vec d := fun x =>
    matVecMul ((A.coeffOn Q).toCoeffField x - sigma • (1 : Mat d)) (u.toH1.grad x) with hF1
  have hF1m : MemVectorL2 (cubeSet Q) F1 := by
    have h : (fluxDefect (Book.Ch03.publicCoeffField Q A) (constMat d hs).matrix u.toH1.grad) =ᵐ[
        volumeMeasureOn (cubeSet Q)] F1 := by
      filter_upwards [Book.Ch03.publicCoeffField_ae_eq_cubeSet Q A] with x hx
      simp only [fluxDefect, hF1, constMat, sub_matVecMul, hx]
    exact MeasureTheory.MemLp.ae_eq h hF
  have hflux : ∀ x, Book.Ch03.homogenizationComparisonFluxField Q A (constMat d hs) D.u D.v x =
      F1 x + G x := by
    intro x
    simp only [Book.Ch03.homogenizationComparisonFluxField, hF1, hD, comparisonDatum,
      constMat, matVecMul_scalarMatrix, H1Function.sub_grad, hG, sub_matVecMul, smul_sub]
    abel
  have hFlm : MemVectorL2 (cubeSet Q)
      (Book.Ch03.homogenizationComparisonFluxField Q A (constMat d hs) D.u D.v) := by
    have : Book.Ch03.homogenizationComparisonFluxField Q A (constMat d hs) D.u D.v =
        fun x => F1 x + G x := funext hflux
    rw [this]
    exact MeasureTheory.MemLp.add hF1m hGm
  have hfield : Book.Ch03.homogenizationComparisonConstantGradientField (constMat d hs) D.u D.v =
      G := by
    funext x
    show matVecMul (sigma • (1 : Mat d)) (u.toH1.grad x - (u.toH1 - w.toH1Function).grad x) = _
    rw [H1Function.sub_grad, matVecMul_scalarMatrix]
    simp [hG]
  have hbF := cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memLp Q hspos _
    (memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q hFlm)
  have hbG := cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memLp Q hspos _
    (memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q hGm)
  have hsub := cubeBesovNegativeVectorSeminormTwo_sub_le_sqrtTwo_mul_add_of_bddAbove Q s _ _
    hFlm hGm hbF hbG
  have heq1 : cubeBesovNegativeVectorSeminormTwo Q s
      (fun x => matVecMul (a x - sigma • (1 : Mat d)) (u.toH1.grad x)) =
      cubeBesovNegativeVectorSeminormTwo Q s (fun x =>
        Book.Ch03.homogenizationComparisonFluxField Q A (constMat d hs) D.u D.v x - G x) := by
    refine cubeBesovNegativeVectorSeminormTwo_eq_of_eq_on_cubeSet s fun x hx => ?_
    rw [hflux x, add_sub_cancel_right]
    simp only [hF1]
    rw [paddedFamily_coeffOn_toCoeffField, padField_apply_of_mem hx]
  rw [heq1]
  refine hsub.trans ?_
  unfold Book.Ch03.homogenizationComparisonNegativeBesovLHS
  rw [hfield, add_comm]

end

end SuperdiffusionCLT.Section6.WeakFlux
