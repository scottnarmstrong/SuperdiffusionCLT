/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Norms.CubeLp
public import SuperdiffusionCLT.Section7.Analytic.MollifierC
public import SuperdiffusionCLT.Section7.Prereq.RhsLemma
public import SuperdiffusionCLT.Section7.Prereq.RhsLemma
public import Homogenization.Besov.Duality.GlobalComparison
public import Homogenization.Besov.Duality.CaccioppoliBridge
public import Homogenization.Book.Ch03.Theorems.PublicInternalBridges.EndPoints
public import SuperdiffusionCLT.Section7.Analytic.DeGiorgi.Sobolev

/-!
# Calculus of the scale-normalized `H̲^{-1/4}` norm

The scale-normalized genuine dual Besov norm of order `1/4` of CoarseGraining
(`scaleNormalizedDualNegativeBesovVectorNormTwo`), for vector fields in `L²` of a cube, is
subadditive (`r1_dual_vec_add_le`) and bounded by a dimensional constant times the normalized `L²`
norm (`r1_ofReal_dual_le`): the elementary embedding `L̲² ↪ H̲^{-1/4}` after rescaling.
-/

@[expose] public section

open scoped ENNReal
open scoped Matrix.Norms.L2Operator

namespace SuperdiffusionCLT.Section7

open Homogenization MeasureTheory

variable {d : ℕ}

theorem r1_conj_two : cubeBesovConjExponent (2 : ℝ≥0∞) = 2 := by
  simpa [cubeBesovConjExponent] using
    (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))

theorem r1_dualFull_add_le (Q : TriadicCube d) {f g : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) (hg : MemLp g 2 (normalizedCubeMeasure Q)) :
    cubeBesovDualFullNorm Q (1 / 4) 2 2 (fun x => f x + g x) ≤
      cubeBesovDualFullNorm Q (1 / 4) 2 2 f + cubeBesovDualFullNorm Q (1 / 4) 2 2 g := by
  have hc := r1_conj_two
  refine cubeBesovDualFullNorm_le_of_forall_fullTest_pairing_le Q _ 2 2 _
    (cubeBesovConjExponent_ne_zero _) (by rw [hc]; norm_num) ?_
  intro t ht
  have ht2 : MemLp t 2 (normalizedCubeMeasure Q) := by
    have := ht.memLp
    rwa [hc] at this
  have hpair : cubeBesovPairing Q (fun x => f x + g x) t =
      cubeBesovPairing Q f t + cubeBesovPairing Q g t := by
    unfold cubeBesovPairing
    rw [cubeAverage_eq_integral_normalizedCubeMeasure, cubeAverage_eq_integral_normalizedCubeMeasure,
      cubeAverage_eq_integral_normalizedCubeMeasure]
    have h1 : Integrable (fun x => f x * t x) (normalizedCubeMeasure Q) := hf.integrable_mul ht2
    have h2 : Integrable (fun x => g x * t x) (normalizedCubeMeasure Q) := hg.integrable_mul ht2
    rw [← integral_add h1 h2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [add_mul]
  rw [hpair]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · exact abs_cubeBesovPairing_le_cubeBesovDualFullNorm_of_full_test_of_memLp Q _ 2 2 f t
      (by norm_num) hf (by norm_num) (by norm_num) (by rw [hc]; norm_num) (by norm_num) ht
  · exact abs_cubeBesovPairing_le_cubeBesovDualFullNorm_of_full_test_of_memLp Q _ 2 2 g t
      (by norm_num) hg (by norm_num) (by norm_num) (by rw [hc]; norm_num) (by norm_num) ht


theorem r1_dual_vec_add_le (Q : TriadicCube d) {F G : Vec d → Vec d}
    (hF : ∀ i, MemLp (fun y => F y i) 2 (normalizedCubeMeasure Q))
    (hG : ∀ i, MemLp (fun y => G y i) 2 (normalizedCubeMeasure Q)) :
    Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo Q (1 / 4) (fun x => F x + G x) ≤
      Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo Q (1 / 4) F +
        Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo Q (1 / 4) G := by
  unfold Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
  rw [← mul_add, ← Finset.sum_add_distrib]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_)
    (Real.rpow_nonneg (by norm_num) _)
  exact r1_dualFull_add_le Q (hF i) (hG i)

theorem r1_dualFull_le_cubeLp (Q : TriadicCube d) {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    Real.rpow (3 : ℝ) (-(1 / 4 : ℝ) * ((Q.scale : ℤ) : ℝ)) *
        cubeBesovDualFullNorm Q (1 / 4) 2 2 f ≤
      (3 : ℝ) ^ ((d : ℝ) + 1 / 4) * (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹ * cubeLpNorm Q 2 f := by
  have hc := r1_conj_two
  have h1 := cubeBesovDualFullNorm_le_note_constant_mul_cubeBesovCircNorm Q (1 / 4) 2 2 f
    (by norm_num) hf (by norm_num) (by norm_num) (by rw [hc]; norm_num) (by norm_num)
  have h2 := cubeBesovCircNorm_le_geometric_constant_of_memLp Q (1 / 4) 2 2 f (by norm_num) hf
    (by norm_num) (by norm_num) (by norm_num)
  rw [Book.Ch03.publicDualBesovScaleWeight_eq_cubeBesovScaleWeight]
  have hw0 : 0 ≤ cubeBesovScaleWeight (1 / 4) Q := cubeBesovScaleWeight_nonneg _ Q
  have hmul : cubeBesovScaleWeight (1 / 4) Q * cubeBesovScaleWeight (-(1 / 4)) Q = 1 := by
    simpa [mul_comm] using cubeBesovScaleWeight_neg_mul_cubeBesovScaleWeight Q (1 / 4)
  have h3 : cubeBesovDualFullNorm Q (1 / 4) 2 2 f ≤ (3 : ℝ) ^ ((d : ℝ) + 1 / 4) *
      ((cubeBesovScaleWeight (-(1 / 4)) Q * cubeLpNorm Q 2 f) *
        (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹) :=
    h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
  calc cubeBesovScaleWeight (1 / 4) Q * cubeBesovDualFullNorm Q (1 / 4) 2 2 f
      ≤ cubeBesovScaleWeight (1 / 4) Q * ((3 : ℝ) ^ ((d : ℝ) + 1 / 4) *
      ((cubeBesovScaleWeight (-(1 / 4)) Q * cubeLpNorm Q 2 f) *
        (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹)) := mul_le_mul_of_nonneg_left h3 hw0
    _ = (3 : ℝ) ^ ((d : ℝ) + 1 / 4) * (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹ * cubeLpNorm Q 2 f := by
        have hrew : cubeBesovScaleWeight (1 / 4) Q * ((3 : ℝ) ^ ((d : ℝ) + 1 / 4) *
            ((cubeBesovScaleWeight (-(1 / 4)) Q * cubeLpNorm Q 2 f) *
              (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹)) =
            (cubeBesovScaleWeight (1 / 4) Q * cubeBesovScaleWeight (-(1 / 4)) Q) *
              ((3 : ℝ) ^ ((d : ℝ) + 1 / 4) * (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹ *
                cubeLpNorm Q 2 f) := by ring
        rw [hrew, hmul, one_mul]

theorem r1_dual_vec_le (Q : TriadicCube d) {F : Vec d → Vec d}
    (hF : ∀ i, MemLp (fun y => F y i) 2 (normalizedCubeMeasure Q)) :
    Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo Q (1 / 4) F ≤
      ∑ i : Fin d, (3 : ℝ) ^ ((d : ℝ) + 1 / 4) * (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹ *
        cubeLpNorm Q 2 (fun y => F y i) := by
  unfold Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => r1_dualFull_le_cubeLp Q (hF i)


theorem r1_ofReal_dual_le (d : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (Q : TriadicCube d) (F : Vec d → Vec d),
      (∀ i, MemLp (fun y => F y i) 2 (normalizedCubeMeasure Q)) →
      MemLp (fun x => Real.sqrt (vecNormSq (F x))) 2 (normalizedCubeMeasure Q) →
      ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo Q (1 / 4) F) ≤
        ENNReal.ofReal K * SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2
          (fun x => Real.sqrt (vecNormSq (F x))) := by
  have hKc : 0 ≤ (3 : ℝ) ^ ((d : ℝ) + 1 / 4) * (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹ := by
    have h1 : (3 : ℝ) ^ (-(1 / 4 : ℝ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    have : 0 < 1 - (3 : ℝ) ^ (-(1 / 4 : ℝ)) := by linarith only [h1]
    positivity
  refine ⟨d * ((3 : ℝ) ^ ((d : ℝ) + 1 / 4) * (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹),
    by positivity, fun Q F hF hFn => ?_⟩
  set Kc : ℝ := (3 : ℝ) ^ ((d : ℝ) + 1 / 4) * (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹ with hKc_def
  set N : ℝ≥0∞ := SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2 (fun x => Real.sqrt (vecNormSq (F x))) with hN
  have hNtop : N ≠ ⊤ := hFn.eLpNorm_ne_top
  have hcomp : ∀ i, cubeLpNorm Q 2 (fun y => F y i) ≤ N.toReal := by
    intro i
    unfold cubeLpNorm
    refine ENNReal.toReal_mono hNtop ?_
    refine eLpNorm_mono (hF i).aestronglyMeasurable (fun x => ?_)
    rw [Real.norm_eq_abs, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact abs_le_eucNorm (F x) i
  have h1 := r1_dual_vec_le Q hF
  have h2 : Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo Q (1 / 4) F ≤
      (d : ℝ) * Kc * N.toReal := by
    refine h1.trans ?_
    calc ∑ i : Fin d, Kc * cubeLpNorm Q 2 (fun y => F y i)
        ≤ ∑ _i : Fin d, Kc * N.toReal :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hcomp i) hKc
      _ = (d : ℝ) * Kc * N.toReal := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  calc ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo Q (1 / 4) F)
      ≤ ENNReal.ofReal ((d : ℝ) * Kc * N.toReal) := ENNReal.ofReal_le_ofReal h2
    _ = ENNReal.ofReal ((d : ℝ) * Kc) * N := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hNtop]


theorem r1_matVecMul_sub_smul_one (A : Mat d) (S : ℝ) (ξ : Vec d) :
    matVecMul (A - S • (1 : Mat d)) ξ = matVecMul A ξ - S • ξ := by
  funext i
  simp [matVecMul, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib, Matrix.one_apply,
    Finset.sum_ite_eq]

theorem r1_eucNorm_neg (v : Vec d) : eucNorm (-v) = eucNorm v := by
  unfold eucNorm vecNormSq vecDot
  simp

theorem r1_eucNorm_eq_vecNorm (v : Vec d) : eucNorm v = Book.Ch02.vecNorm v := by
  unfold eucNorm
  rw [← Book.Ch02.vecNorm_sq_eq_vecNormSq, Real.sqrt_sq (Book.Ch02.vecNorm_nonneg v)]

theorem r1_eucNorm_add_le (v w : Vec d) : eucNorm (v + w) ≤ eucNorm v + eucNorm w := by
  rw [r1_eucNorm_eq_vecNorm, r1_eucNorm_eq_vecNorm, r1_eucNorm_eq_vecNorm]
  unfold Book.Ch02.vecNorm
  rw [WithLp.toLp_add]
  exact norm_add_le _ _

theorem r1_eucNorm_matVecMul_le (A : Mat d) (ξ : Vec d) :
    eucNorm (matVecMul A ξ) ≤ Book.Ch02.matrixOperatorNorm A * eucNorm ξ := by
  rw [r1_eucNorm_eq_vecNorm, r1_eucNorm_eq_vecNorm]
  exact Book.Ch02.vecNorm_matVecMul_le_matrixOperatorNorm_mul_vecNorm A ξ


theorem r1_continuous_eucNorm : Continuous (fun v : Vec d => eucNorm v) := by
  unfold eucNorm vecNormSq vecDot
  exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ =>
    ((continuous_apply i).mul (continuous_apply i)))

theorem r1_eucNorm_le_mul_norm [NeZero d] (v : Vec d) : eucNorm v ≤ d * ‖v‖ := by
  have hd : (1 : ℝ) ≤ d := by
    have : 1 ≤ d := Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
    exact_mod_cast this
  have hn := norm_nonneg v
  unfold eucNorm
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  unfold vecNormSq vecDot
  calc ∑ i, v i * v i ≤ ∑ _i : Fin d, ‖v‖ ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have := norm_le_pi_norm v i
        rw [Real.norm_eq_abs] at this
        calc v i * v i = |v i| ^ 2 := by rw [sq_abs]; ring
          _ ≤ ‖v‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
    _ = d * ‖v‖ ^ 2 := by simp
    _ ≤ (d * ‖v‖) ^ 2 := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right (by rw [sq]; exact le_mul_of_one_le_right (by positivity) hd) (by positivity)

theorem r1_memLp_eucNorm_of_memLp [NeZero d] {μ : Measure (Vec d)} {F : Vec d → Vec d}
    (hF : MemLp F 2 μ) : MemLp (fun x => eucNorm (F x)) 2 μ := by
  refine MemLp.of_le_mul (c := (d : ℝ)) hF.norm
    (r1_continuous_eucNorm.comp_aestronglyMeasurable hF.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (by unfold eucNorm; positivity), norm_norm]
  exact r1_eucNorm_le_mul_norm _


theorem r1_memLp_grad_comp (Q : TriadicCube d) (z : H1Function (openCubeSet Q)) (i : Fin d) :
    MemLp (fun y => z.grad y i) 2 (normalizedCubeMeasure Q) := by
  rw [normalizedCubeMeasure_eq_smul]
  exact (z.gradMemL2 i).smul_measure ENNReal.ofReal_ne_top

theorem r1_memLp_grad_eucNorm [NeZero d] (Q : TriadicCube d) (z : H1Function (openCubeSet Q)) :
    MemLp (fun x => eucNorm (z.grad x)) 2 (normalizedCubeMeasure Q) := by
  rw [normalizedCubeMeasure_eq_smul]
  exact (memLp_eucNorm_grad z).smul_measure ENNReal.ofReal_ne_top

theorem r1_memLp_flux (Q : TriadicCube d) {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (S : ℝ) (z : H1Function (openCubeSet Q)) :
    MemLp (fun x => matVecMul (a x - S • (1 : Mat d)) (z.grad x)) 2 (normalizedCubeMeasure Q) := by
  have h1 : MemVectorL2 (openCubeSet Q) (fun x => matVecMul (a x) (z.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll z.grad_memVectorL2
  have h2 : MemVectorL2 (openCubeSet Q) (fun x => S • z.grad x) :=
    z.grad_memVectorL2.const_smul S
  have h3 := h1.sub h2
  have h4 : (fun x => matVecMul (a x - S • (1 : Mat d)) (z.grad x)) =
      (fun x => matVecMul (a x) (z.grad x)) - fun x => S • z.grad x := by
    funext x
    exact r1_matVecMul_sub_smul_one _ _ _
  rw [h4]
  exact memLp_normalized_of_memVectorL2 Q h3


theorem r1_enorm_flux_le [NeZero d] (Q : TriadicCube d) {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (S B : ℝ) (hB : 0 ≤ B)
    (hAB : ∀ᵐ x ∂normalizedCubeMeasure Q,
      Book.Ch02.matrixOperatorNorm (a x - S • (1 : Mat d)) ≤ B)
    (z : H1Function (openCubeSet Q)) :
    SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2
        (fun x => Real.sqrt (vecNormSq (matVecMul (a x - S • (1 : Mat d)) (z.grad x)))) ≤
      ENNReal.ofReal B * SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2
        (fun x => Real.sqrt (vecNormSq (z.grad x))) := by
  have hm := (r1_memLp_eucNorm_of_memLp (r1_memLp_flux Q hEll S z)).aestronglyMeasurable
  have h1 : SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2
      (fun x => Real.sqrt (vecNormSq (matVecMul (a x - S • (1 : Mat d)) (z.grad x)))) ≤
      SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2
        (B • fun x => Real.sqrt (vecNormSq (z.grad x))) := by
    refine eLpNorm_mono_ae hm ?_
    filter_upwards [hAB] with x hx
    have h2 := r1_eucNorm_matVecMul_le (a x - S • (1 : Mat d)) (z.grad x)
    have h3 : eucNorm (matVecMul (a x - S • (1 : Mat d)) (z.grad x)) ≤ B * eucNorm (z.grad x) :=
      h2.trans (mul_le_mul_of_nonneg_right hx (by unfold eucNorm; positivity))
    have h4 : 0 ≤ eucNorm (matVecMul (a x - S • (1 : Mat d)) (z.grad x)) := by
      unfold eucNorm; positivity
    have h5 : 0 ≤ eucNorm (z.grad x) := by unfold eucNorm; positivity
    show ‖eucNorm (matVecMul (a x - S • (1 : Mat d)) (z.grad x))‖ ≤ ‖B * eucNorm (z.grad x)‖
    rw [Real.norm_of_nonneg h4, Real.norm_of_nonneg (mul_nonneg hB h5)]
    exact h3
  refine h1.trans (le_of_eq ?_)
  rw [SuperdiffusionCLT.Section2.Norms.cubeLpENorm_const_smul, Real.enorm_of_nonneg hB]


theorem r1_ae_normalized (Q : TriadicCube d) {P : Vec d → Prop}
    (h : ∀ᵐ x ∂(volume.restrict (openCubeSet Q)), P x) :
    ∀ᵐ x ∂normalizedCubeMeasure Q, P x := by
  rw [normalizedCubeMeasure_eq_smul]
  exact Measure.ae_smul_measure h _

theorem r1_ae_cubeSet (Q : TriadicCube d) {P : Vec d → Prop}
    (h : ∀ᵐ x ∂(volume.restrict (openCubeSet Q)), P x) :
    ∀ᵐ x ∂(volume.restrict (cubeSet Q)), P x := by
  rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  exact h

theorem r1_N2_add_le [NeZero d] (Q : TriadicCube d) {z1 z2 z3 : H1Function (openCubeSet Q)}
    (h : z1.grad =ᵐ[volume.restrict (openCubeSet Q)] fun x => z2.grad x + z3.grad x) :
    SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2
        (fun x => Real.sqrt (vecNormSq (z1.grad x))) ≤
      SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2
          (fun x => Real.sqrt (vecNormSq (z2.grad x))) +
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2
          (fun x => Real.sqrt (vecNormSq (z3.grad x))) := by
  have h2 := (r1_memLp_grad_eucNorm Q z2).aestronglyMeasurable
  have h3 := (r1_memLp_grad_eucNorm Q z3).aestronglyMeasurable
  have h1 := (r1_memLp_grad_eucNorm Q z1).aestronglyMeasurable
  have hadd := SuperdiffusionCLT.Section2.Norms.cubeLpENorm_add_le (Q := Q) (q := 2)
    (f := fun x => eucNorm (z2.grad x)) (g := fun x => eucNorm (z3.grad x)) (by norm_num) h2 h3
  refine le_trans ?_ hadd
  refine eLpNorm_mono_ae h1 ?_
  filter_upwards [r1_ae_normalized Q h] with x hx
  have e1 : 0 ≤ eucNorm (z1.grad x) := by unfold eucNorm; positivity
  have e2 : 0 ≤ eucNorm (z2.grad x) := by unfold eucNorm; positivity
  have e3 : 0 ≤ eucNorm (z3.grad x) := by unfold eucNorm; positivity
  show ‖eucNorm (z1.grad x)‖ ≤ ‖eucNorm (z2.grad x) + eucNorm (z3.grad x)‖
  rw [Real.norm_of_nonneg e1, Real.norm_of_nonneg (add_nonneg e2 e3), hx]
  exact r1_eucNorm_add_le _ _


theorem r1_sqrt_neg (v : Vec d) : Real.sqrt (vecNormSq (-v)) = Real.sqrt (vecNormSq v) :=
  r1_eucNorm_neg v

theorem r1_ofReal_coef (Af K B X : ℝ) (hAf : 0 ≤ Af) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (Ew G : ℝ≥0∞) (hEw : Ew ≤ ENNReal.ofReal X * G) :
    ENNReal.ofReal Af * Ew + ENNReal.ofReal K * (ENNReal.ofReal B * Ew) ≤
      ENNReal.ofReal ((Af + K * B) * X) * G := by
  have hX : ENNReal.ofReal ((Af + K * B) * X) =
      (ENNReal.ofReal Af + ENNReal.ofReal K * ENNReal.ofReal B) * ENNReal.ofReal X := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add hAf (by positivity),
      ENNReal.ofReal_mul hK]
  rw [hX]
  calc ENNReal.ofReal Af * Ew + ENNReal.ofReal K * (ENNReal.ofReal B * Ew)
      = (ENNReal.ofReal Af + ENNReal.ofReal K * ENNReal.ofReal B) * Ew := by ring
    _ ≤ (ENNReal.ofReal Af + ENNReal.ofReal K * ENNReal.ofReal B) * (ENNReal.ofReal X * G) :=
        mul_le_mul_right hEw _
    _ = _ := by ring


theorem r1_ae_norm_le_of_eLpNorm_top {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {g : α → E} {c : ℝ} (hc : 0 ≤ c) (h : eLpNorm g ∞ μ ≤ ENNReal.ofReal c) :
    ∀ᵐ x ∂μ, ‖g x‖ ≤ c := by
  have hm : AEStronglyMeasurable g μ := by
    by_contra hn
    rw [eLpNorm_of_not_aestronglyMeasurable hn] at h
    exact ENNReal.ofReal_ne_top (top_le_iff.1 h)
  rw [eLpNorm_exponent_top hm] at h
  filter_upwards [enorm_ae_le_eLpNormEssSup g μ] with x hx
  have h2 := hx.trans h
  rwa [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff hc] at h2

/-- The `L^∞` part of `e.Dir.new.k.bounds` gives an almost-everywhere bound `m^{1+ρ}`. -/
theorem r1_ae_opnorm_k [NeZero d] (Q : TriadicCube d) {g : Vec d → Mat d} {m ρ : ℝ} (hm : 1 ≤ m)
    (X : ℝ≥0∞)
    (h : ENNReal.ofReal (m⁻¹) * SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q ∞ g + X ≤
      ENNReal.ofReal (m ^ ρ)) :
    ∀ᵐ x ∂normalizedCubeMeasure Q, Book.Ch02.matrixOperatorNorm (g x) ≤ m ^ (1 + ρ) := by
  have hm0 : 0 < m := by linarith only [hm]
  have h1 : ENNReal.ofReal (m⁻¹) * SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q ∞ g ≤
      ENNReal.ofReal (m ^ ρ) := le_trans le_self_add h
  have hX : SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q ∞ g ≤
      ENNReal.ofReal (m ^ (1 + ρ)) := by
    calc SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q ∞ g
        = ENNReal.ofReal m * (ENNReal.ofReal (m⁻¹) *
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q ∞ g) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hm0.le, mul_inv_cancel₀ hm0.ne',
            ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal m * ENNReal.ofReal (m ^ ρ) := mul_le_mul_right h1 _
      _ = _ := by
          rw [← ENNReal.ofReal_mul hm0.le, Real.rpow_add hm0, Real.rpow_one]
  have hae := r1_ae_norm_le_of_eLpNorm_top (by positivity) hX
  filter_upwards [hae] with x hx
  rwa [Book.Ch02.matrixOperatorNorm_eq_l2_opNorm]

/-- Pushing an almost-everywhere statement through a translation between cubes. -/
theorem r1_ae_translate (Q R : TriadicCube d) (z : Vec d)
    (hsub : (fun x => z + x) '' cubeSet R ⊆ cubeSet Q) {P : Vec d → Prop}
    (h : ∀ᵐ x' ∂normalizedCubeMeasure Q, P x') :
    ∀ᵐ x ∂normalizedCubeMeasure R, P (z + x) := by
  have h1 : ∀ᵐ x' ∂(volume.restrict (cubeSet Q)), P x' := by
    have : normalizedCubeMeasure Q = ENNReal.ofReal (cubeVolume Q)⁻¹ • volume.restrict (cubeSet Q) := by
      rw [normalizedCubeMeasure, cubeMeasure]
    rw [this] at h
    have hne : ENNReal.ofReal (cubeVolume Q)⁻¹ ≠ 0 := by
      have : 0 < cubeVolume Q := by
        unfold cubeVolume
        exact pow_pos (r1_scaleFactor_pos Q) d
      exact (ENNReal.ofReal_pos.2 (inv_pos.2 this)).ne'
    exact (Measure.absolutelyContinuous_smul hne).ae_le h
  have h2 : ∀ᵐ x' ∂(volume : Measure (Vec d)), x' ∈ cubeSet Q → P x' :=
    (ae_restrict_iff' (measurableSet_cubeSet Q)).1 h1
  have h3 : ∀ᵐ x ∂(volume : Measure (Vec d)), z + x ∈ cubeSet Q → P (z + x) :=
    (measurePreserving_add_left volume z).quasiMeasurePreserving.ae h2
  have h4 : ∀ᵐ x ∂(volume.restrict (cubeSet R)), P (z + x) := by
    rw [ae_restrict_iff' (measurableSet_cubeSet R)]
    filter_upwards [h3] with x hx hxR
    exact hx (hsub ⟨x, hxR, rfl⟩)
  have : normalizedCubeMeasure R = ENNReal.ofReal (cubeVolume R)⁻¹ • volume.restrict (cubeSet R) := by
    rw [normalizedCubeMeasure, cubeMeasure]
  rw [this]
  exact Measure.ae_smul_measure h4 _

theorem r1_ae_opnorm_field [NeZero d] (Q R : TriadicCube d) (z : Vec d)
    (hsub : (fun x => z + x) '' cubeSet R ⊆ cubeSet Q) (g : Vec d → Mat d) (nu S c : ℝ)
    (hg : ∀ᵐ x' ∂normalizedCubeMeasure Q, Book.Ch02.matrixOperatorNorm (g x') ≤ c) :
    ∀ᵐ x ∂normalizedCubeMeasure R,
      Book.Ch02.matrixOperatorNorm (nu • (1 : Mat d) + g (z + x) - S • (1 : Mat d)) ≤
        |nu - S| + c := by
  filter_upwards [r1_ae_translate Q R z hsub hg] with x hx
  have e1 : nu • (1 : Mat d) + g (z + x) - S • (1 : Mat d) = (nu - S) • (1 : Mat d) + g (z + x) := by
    rw [sub_smul]
    abel
  rw [e1, Book.Ch02.matrixOperatorNorm_eq_l2_opNorm]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, ← Book.Ch02.matrixOperatorNorm_eq_l2_opNorm, Book.Ch02.matrixOperatorNorm_one,
      Real.norm_eq_abs, mul_one]
  · rw [← Book.Ch02.matrixOperatorNorm_eq_l2_opNorm]
    exact hx



end SuperdiffusionCLT.Section7
