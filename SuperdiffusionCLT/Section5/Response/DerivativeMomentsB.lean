/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Response.DerivativeMoments
public import SuperdiffusionCLT.Section3.ResponseFields.Regbounds

/-!
# The Jacobian of the shell flux in `L⁸(P; L̲⁸(cu_K))`

For the flux `(k_b - k_a) p` the Jacobian is dominated pointwise by `√d |p|` times the sum of the
shell derivative sizes (`norm_hilbertMat_streamFluxWeakGradient_le_derivNorm`), so the stationary
moment bound of `DerivativeMoments` and Minkowski's inequality in `x` and in `ω` give
`E‖∇ flux‖_{L̲⁸(cu_K)}⁸ ^{1/8} ≤ 2 √d |p| ∑_{k ∈ (a,b]} 3^{-k}` with no dependence on `K`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open MeasureTheory Homogenization Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open scoped ENNReal Matrix.Norms.Elementwise

variable {d : ℕ}

/-- The Frobenius size of the Jacobian of `(k_b - k_a) p` at `x` is at most
`√d |p|` times any bound on the exact induced norm of `∑_{k ∈ (a,b]} ∇ j_k (x)`. -/
theorem norm_hilbertMat_streamFluxWeakGradient_le_derivNorm (omega : ShellSeq d) {a b : ℕ}
    (hab : a ≤ b) (p x : Vec d) {G : ℝ}
    (hDG : ShellField.matrixDerivativeNorm (∑ k ∈ Finset.Ioc a b, ShellField.deriv (omega k) x) ≤ G) :
    ‖HilbertMat.ofMat (fun i j => streamFluxWeakGradient omega a b p i x j)‖ ≤
      Real.sqrt d * vecNorm p * G := by
  have hGnonneg : 0 ≤ G := (ShellField.matrixDerivativeNorm_nonneg _).trans hDG
  have hcol : ∀ j : Fin d, matrixOperatorNorm
      ((∑ k ∈ Finset.Ioc a b, ShellField.deriv (omega k) x) (basisVec j)) ≤ G := by
    intro j
    refine le_trans ?_ hDG
    have h := matrixOperatorNorm_apply_le_matrixDerivativeNorm_mul_vecNorm
      (∑ k ∈ Finset.Ioc a b, ShellField.deriv (omega k) x) (basisVec j)
    rwa [vecNorm_basisVec, mul_one] at h
  have hsum : ∑ i : Fin d, ∑ j : Fin d,
      streamFluxWeakGradient omega a b p i x j * streamFluxWeakGradient omega a b p i x j ≤
      (d : ℝ) * (G ^ 2 * vecNormSq p) := by
    have hswap : ∑ i : Fin d, ∑ j : Fin d,
        streamFluxWeakGradient omega a b p i x j * streamFluxWeakGradient omega a b p i x j =
        ∑ j : Fin d, vecNormSq (matVecMul
          ((∑ k ∈ Finset.Ioc a b, ShellField.deriv (omega k) x) (basisVec j)) p) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [streamFluxWeakGradient_apply omega hab p i x j]
    rw [hswap]
    calc ∑ j : Fin d, vecNormSq (matVecMul
          ((∑ k ∈ Finset.Ioc a b, ShellField.deriv (omega k) x) (basisVec j)) p)
        ≤ ∑ _j : Fin d, (G ^ 2 * vecNormSq p) := by
          refine Finset.sum_le_sum fun j _ => ?_
          refine
            (vecNormSq_matVecMul_le_matrixOperatorNorm_sq_mul_vecNormSq _ _).trans ?_
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (matrixOperatorNorm_nonneg _) (hcol j) 2)
            (vecNormSq_nonneg p)
      _ = (d : ℝ) * (G ^ 2 * vecNormSq p) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hB : 0 ≤ Real.sqrt d * vecNorm p * G :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (vecNorm_nonneg p)) hGnonneg
  have hsq : ‖HilbertMat.ofMat
      (fun i j => streamFluxWeakGradient omega a b p i x j)‖ ^ 2 ≤
      (Real.sqrt d * vecNorm p * G) ^ 2 := by
    refine ((norm_sq_hilbertMat_ofMat
      (fun i j => streamFluxWeakGradient omega a b p i x j)).trans_le hsum).trans_eq ?_
    rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg d), vecNorm_sq_eq_vecNormSq]
    ring
  have hfin := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hB] at hfin

/-- The Jacobian of `(k_b - k_a) p` in `L̲⁸(Q)` is at most `√d |p|` times the sum of the
`L̲⁸(Q)` norms of the shell derivative sizes. -/
theorem cubeLpENorm_streamFluxWeakGradient_le (omega : ShellSeq d) {a b : ℕ} (hab : a ≤ b)
    (p : Vec d) (Q : TriadicCube d) :
    SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 8
        (fun x => HilbertMat.ofMat (fun i j => streamFluxWeakGradient omega a b p i x j)) ≤
      ENNReal.ofReal (Real.sqrt d * vecNorm p) *
        ∑ k ∈ Finset.Ioc a b,
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 8 (shellDerivSize k omega) := by
  set c : ℝ := Real.sqrt d * vecNorm p with hc
  have hcnn : 0 ≤ c := mul_nonneg (Real.sqrt_nonneg _) (vecNorm_nonneg p)
  have hmeas : AEStronglyMeasurable (fun x => HilbertMat.ofMat
      (fun i j => streamFluxWeakGradient omega a b p i x j)) (normalizedCubeMeasure Q) :=
    (continuous_streamFluxJacobian omega hab p).aestronglyMeasurable
  have hpt : ∀ x, ‖HilbertMat.ofMat (fun i j => streamFluxWeakGradient omega a b p i x j)‖ ≤
      ‖(c • ∑ k ∈ Finset.Ioc a b, shellDerivSize k omega) x‖ := by
    intro x
    have hsum : 0 ≤ ∑ k ∈ Finset.Ioc a b, shellDerivSize k omega x :=
      Finset.sum_nonneg fun k _ => shellDerivSize_nonneg k omega x
    have h1 := norm_hilbertMat_streamFluxWeakGradient_le_derivNorm omega hab p x
      (G := ∑ k ∈ Finset.Ioc a b, shellDerivSize k omega x)
      (matrixDerivativeNorm_finset_sum_le (Finset.Ioc a b)
        (fun k => ShellField.deriv (omega k) x))
    rw [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hcnn hsum)]
    exact h1
  refine (SuperdiffusionCLT.Section2.Norms.cubeLpENorm_mono_enorm hmeas hpt).trans ?_
  rw [SuperdiffusionCLT.Section2.Norms.cubeLpENorm_const_smul,
    Real.enorm_eq_ofReal hcnn]
  refine mul_le_mul_right ?_ _
  exact eLpNorm_sum_le (by norm_num)

/-! ## Measurability of the normalized `L̲⁸` norm of the derivative size -/

theorem cubeLpENorm_shellDerivSize_pow_eq (k : ℕ) (omega : ShellSeq d) (Q : TriadicCube d) :
    (SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 8 (shellDerivSize k omega)) ^ (8 : ℕ) =
      ∫⁻ x, ENNReal.ofReal (shellDerivSize k omega x) ^ (8 : ℕ) ∂normalizedCubeMeasure Q := by
  rw [SuperdiffusionCLT.Section2.Norms.cubeLpENorm,
    eLpNorm_eight_pow _ (continuous_shellDerivSize k omega).aestronglyMeasurable]
  exact lintegral_congr fun x => by
    rw [Real.enorm_eq_ofReal (shellDerivSize_nonneg k omega x)]

theorem measurable_cubeLpENorm_shellDerivSize (k : ℕ) (Q : TriadicCube d) :
    Measurable (fun omega : ShellSeq d =>
      SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 8 (shellDerivSize k omega)) := by
  have : IsProbabilityMeasure (normalizedCubeMeasure Q) := ⟨normalizedCubeMeasure_apply_univ Q⟩
  have hF : Measurable (fun q : ShellSeq d × Vec d =>
      ENNReal.ofReal (shellDerivSize k q.1 q.2) ^ (8 : ℕ)) := by
    have h := (measurable_shellDerivSize_uncurry (d := d) k).comp measurable_swap
    exact (ENNReal.measurable_ofReal.comp h).pow_const 8
  have hint : Measurable (fun omega : ShellSeq d =>
      ∫⁻ x, ENNReal.ofReal (shellDerivSize k omega x) ^ (8 : ℕ) ∂normalizedCubeMeasure Q) :=
    hF.lintegral_prod_right'
  have heq : (fun omega : ShellSeq d =>
      SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 8 (shellDerivSize k omega)) =
      fun omega => (∫⁻ x, ENNReal.ofReal (shellDerivSize k omega x) ^ (8 : ℕ)
        ∂normalizedCubeMeasure Q) ^ (((8 : ℕ) : ℝ)⁻¹) := by
    funext omega
    rw [← cubeLpENorm_shellDerivSize_pow_eq k omega Q, ENNReal.pow_rpow_inv_natCast (by norm_num)]
  rw [heq]
  exact hint.pow_const _

/-! ## The `L⁸(P; L̲⁸(Q))` bound for the flux Jacobian -/

/-- **Stationary `L⁸` bound of the Jacobian of `(k_b - k_a) p` on a cube `Q`**, with no
dependence on the size of `Q`. -/
theorem lintegral_cubeLpENorm_streamFluxWeakGradient_le {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) {a b : ℕ} (hab : a ≤ b) (p : Vec d)
    (Q : TriadicCube d) :
    (∫⁻ omega, (SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 8
        (fun x => HilbertMat.ofMat (fun i j => streamFluxWeakGradient omega a b p i x j))) ^ (8 : ℕ)
        ∂P.toMeasure) ^ ((1 : ℝ) / 8) ≤
      ENNReal.ofReal (2 * (Real.sqrt d * vecNorm p) * ∑ k ∈ Finset.Ioc a b, ((3 : ℝ) ^ k)⁻¹) := by
  set c : ℝ := Real.sqrt d * vecNorm p with hc
  have hcnn : 0 ≤ c := mul_nonneg (Real.sqrt_nonneg _) (vecNorm_nonneg p)
  set f : ℕ → ShellSeq d → ℝ≥0∞ := fun k omega =>
    ENNReal.ofReal c * SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 8
      (shellDerivSize k omega) with hf
  have hrpow : ∀ x : ℝ≥0∞, x ^ (8 : ℝ) = x ^ (8 : ℕ) := fun x => by
    exact_mod_cast ENNReal.rpow_natCast x 8
  have hpt : ∀ omega,
      SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 8
        (fun x => HilbertMat.ofMat (fun i j => streamFluxWeakGradient omega a b p i x j)) ≤
      ∑ k ∈ Finset.Ioc a b, f k omega := fun omega =>
    (cubeLpENorm_streamFluxWeakGradient_le omega hab p Q).trans_eq (Finset.mul_sum _ _ _)
  have hone : (1 : ℝ) / 8 = (((8 : ℕ) : ℝ))⁻¹ := by norm_num
  calc (∫⁻ omega, (SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 8
        (fun x => HilbertMat.ofMat (fun i j => streamFluxWeakGradient omega a b p i x j))) ^ (8 : ℕ)
        ∂P.toMeasure) ^ ((1 : ℝ) / 8)
      ≤ (∫⁻ omega, (∑ k ∈ Finset.Ioc a b, f k omega) ^ (8 : ℝ) ∂P.toMeasure) ^ ((1 : ℝ) / 8) := by
        refine ENNReal.rpow_le_rpow ?_ (by norm_num)
        refine lintegral_mono fun omega => ?_
        rw [hrpow]
        exact pow_le_pow_left₀ bot_le (hpt omega) 8
    _ ≤ ∑ k ∈ Finset.Ioc a b, (∫⁻ omega, (f k omega) ^ (8 : ℝ) ∂P.toMeasure) ^ ((1 : ℝ) / 8) :=
        lintegral_rpow_finsetSum_le _ f
          (fun k _ => measurable_const.mul (measurable_cubeLpENorm_shellDerivSize k Q))
          (by norm_num)
    _ ≤ ∑ k ∈ Finset.Ioc a b, ENNReal.ofReal (c * (2 * ((3 : ℝ) ^ k)⁻¹)) := by
        refine Finset.sum_le_sum fun k _ => ?_
        have h1 : ∫⁻ omega, (f k omega) ^ (8 : ℝ) ∂P.toMeasure ≤
            (ENNReal.ofReal c * ENNReal.ofReal (2 * ((3 : ℝ) ^ k)⁻¹)) ^ (8 : ℕ) := by
          simp_rw [hrpow, hf, mul_pow]
          rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
          exact mul_le_mul_right (lintegral_cubeLpENorm_shellDerivSize_pow_le hPrefix hJ3 k Q) _
        rw [ENNReal.ofReal_mul hcnn, hone]
        calc (∫⁻ omega, (f k omega) ^ (8 : ℝ) ∂P.toMeasure) ^ (((8 : ℕ) : ℝ)⁻¹)
            ≤ ((ENNReal.ofReal c * ENNReal.ofReal (2 * ((3 : ℝ) ^ k)⁻¹)) ^ (8 : ℕ)) ^
                (((8 : ℕ) : ℝ)⁻¹) :=
              ENNReal.rpow_le_rpow h1 (by positivity)
          _ = _ := by
              rw [ENNReal.pow_rpow_inv_natCast (by norm_num)]
    _ = ENNReal.ofReal (2 * c * ∑ k ∈ Finset.Ioc a b, ((3 : ℝ) ^ k)⁻¹) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity), ← Finset.mul_sum]
        congr 1
        rw [← Finset.mul_sum]
        ring

end SuperdiffusionCLT.Section5
