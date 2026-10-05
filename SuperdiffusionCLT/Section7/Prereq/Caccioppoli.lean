/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Sobolev.Foundations.CubeBesovPoincare.W12Embedding
public import Homogenization.Besov.Duality.CaccioppoliBridge
public import Homogenization.Deterministic.CoarseCaccioppoli.CutoffProduct.Geometry
public import Homogenization.Book.Ch03.Definitions
public import SuperdiffusionCLT.Section7.Prereq.RhsLemmaB
public import SuperdiffusionCLT.Section6.Engine.WitnessLaplace
public import Homogenization.Deterministic.CoarseCaccioppoli.CutoffProduct.VectorProduct
public import Homogenization.Besov.Localization

/-!
# The weak test on one cube (interior Caccioppoli, step 1)

For an `H¹` function `ξ` on a triadic cube `Q`, the scale-normalized genuine dual negative Besov
norm of order `1/4` of a vector field `F` controls the pairing of `F` with `ξ`:
`|avg_Q F · ξ| ≤ ‖F‖_{H̲^{-1/4}(Q)} · (‖ξ‖_{L̲²(Q)} + C 3^n ‖∇ξ‖_{L̲²(Q)})` (display
`e.Dir.new.Cacc.weak.test`, the pairing step).  The proof tests `ξ` against the
finite-depth partition seminorms: the oscillation of `ξ` on a descendant of depth `j` is bounded by
the local Poincare inequality of CoarseGraining, and the depths sum geometrically.

## Main results

* `Section7.ca1_testNorm_le`: the finite-depth dual test norm of order `1/4` of an `H¹` function.
* `Section7.ca1_pairing_scalar`, `Section7.ca1_pairing_vector`: the pairing bound.
* `Section7.ca1_cube_weak_test`: the weak test for `A ∇u` on one cube, from the two weak bounds
  (flux defect and gradient) of the right-hand-side lemma.
-/

@[expose] public section

open scoped ENNReal
open Homogenization MeasureTheory

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- An `H¹` function regarded as a `W^{1,2}` function. -/
noncomputable def ca1_toW12 {U : Set (Vec d)} (u : H1Function U) : W1pFunction U (2 : ℝ≥0∞) where
  toFun := u.toFun
  grad := u.grad
  memLp := u.memL2
  gradMemLp := u.gradMemL2
  hasWeakGradient := u.hasWeakGradient

/-- Depth bound for the order-`s` partition seminorm of an `H¹` function. -/
theorem ca1_depth_le [NeZero d] (Q : TriadicCube d) (u : H1Function (openCubeSet Q)) (s : ℝ)
    (j : ℕ) :
    cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u.toFun j ≤
      cubeBesovW12EmbeddingConstant d * cubeLpNorm Q (2 : ℝ≥0∞) (fun x => euclideanNorm (u.grad x)) *
        (cubeScaleFactor Q / (3 : ℝ) ^ j) ^ (1 - s) := by
  classical
  let uW : W1pFunction (openCubeSet Q) (2 : ℝ≥0∞) := ca1_toW12 u
  let K : ℝ := cubeBesovW12EmbeddingConstant d
  let G : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) (fun x => euclideanNorm (u.grad x))
  let a : ℝ := cubeScaleFactor Q / (3 : ℝ) ^ j
  let E : TriadicCube d → ℝ := fun R =>
    cubeLpNorm R (2 : ℝ≥0∞) (fun x => euclideanNorm (u.grad x))
  let A : TriadicCube d → ℝ := fun R => K * cubeScaleFactor R * E R
  have hK : 0 ≤ K := cubeBesovW12EmbeddingConstant_nonneg d
  have hG : 0 ≤ G := cubeLpNorm_nonneg Q (2 : ℝ≥0∞) _
  have ha_pos : 0 < a := div_pos (cubeScaleFactor_pos' Q) (by positivity)
  have hA : ∀ R ∈ descendantsAtDepth Q j, 0 ≤ A R := fun R _ =>
    mul_nonneg (mul_nonneg hK (cubeScaleFactor_pos' R).le) (cubeLpNorm_nonneg R _ _)
  have hosc : ∀ R ∈ descendantsAtDepth Q j,
      cubeBesovOscillation R (2 : ℝ≥0∞) u.toFun ≤ A R := by
    intro R hR
    let uR : W1pFunction (openCubeSet R) (2 : ℝ≥0∞) := uW.restrictToOpenSubcube hR
    have hlocal := cubeBesovOscillation_two_le_cubeScaleFactor_mul_normalizedW1pSeminorm R uR
    rw [openCubeSet_normalizedW1pSeminorm_two_eq_cubeLpNorm_euclideanGrad R uR] at hlocal
    simpa [uR, A, E, K, cubeBesovW12EmbeddingConstant, mul_assoc, uW, ca1_toW12] using hlocal
  have hdepth := cubeBesovDepthSeminorm_two_le_depthWeight_mul_descendantsAverage_sq_rpow_half
    Q s u.toFun j A hA hosc
  have hscaled : descendantsAverage Q j (fun R => (A R) ^ 2) =
      (K * a) ^ 2 * descendantsAverage Q j (fun R => E R ^ 2) := by
    have hsum : ∑ R ∈ descendantsAtDepth Q j, (A R) ^ 2 =
        ∑ R ∈ descendantsAtDepth Q j, (K * a) ^ 2 * E R ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro R hR
      dsimp only [A]
      rw [show cubeScaleFactor R = a from cubeScaleFactor_eq_div_pow_of_mem_descendantsAtDepth hR]
      ring
    change ((descendantsAtDepth Q j).card : ℝ)⁻¹ * ∑ R ∈ descendantsAtDepth Q j, (A R) ^ 2 =
      (K * a) ^ 2 * (((descendantsAtDepth Q j).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth Q j, E R ^ 2)
    rw [hsum, ← Finset.mul_sum]
    ring
  have havg : descendantsAverage Q j (fun R => E R ^ 2) = G ^ 2 :=
    descendantsAverage_cubeLpNorm_euclideanGrad_two_sq_eq Q uW j
  have hroot : (descendantsAverage Q j (fun R => (A R) ^ 2)) ^ (1 / 2 : ℝ) = K * a * G := by
    rw [hscaled, havg, ← mul_pow]
    exact sq_rpow_half_eq_of_nonneg (mul_nonneg (mul_nonneg hK ha_pos.le) hG)
  have hw : cubeBesovDepthWeight Q s j = a ^ (-s) := rfl
  calc cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u.toFun j
      ≤ cubeBesovDepthWeight Q s j * (K * a * G) := hdepth.trans_eq (by rw [hroot])
    _ = K * G * (a ^ (-s) * a) := by rw [hw]; ring
    _ = K * G * a ^ (1 - s) := by
        rw [show (1 - s) = -s + 1 by ring, Real.rpow_add ha_pos, Real.rpow_one]


theorem ca1_conj_two : cubeBesovConjExponent (2 : ℝ≥0∞) = 2 := by
  simpa [cubeBesovConjExponent] using
    (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))

theorem ca1_rho_sq_le : (((3 : ℝ) ^ (-(3 / 4 : ℝ))) ^ 2) ≤ 1 / 3 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  calc (3 : ℝ) ^ (-(3 / 4 : ℝ) * ((2 : ℕ) : ℝ)) ≤ (3 : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ = 1 / 3 := by rw [Real.rpow_neg_one]; norm_num

/-- The finite-depth dual test norm of order `1/4` of an `H¹` function. -/
theorem ca1_testNorm_le [NeZero d] (Q : TriadicCube d) (u : H1Function (openCubeSet Q)) (N : ℕ) :
    cubeBesovDualTestNorm Q (1 / 4 : ℝ) 2 2 N u.toFun ≤
      cubeScaleFactor Q ^ (-(1 / 4 : ℝ)) *
        (cubeLpNorm Q (2 : ℝ≥0∞) u.toFun +
          2 * cubeBesovW12EmbeddingConstant d * cubeScaleFactor Q *
            cubeLpNorm Q (2 : ℝ≥0∞) (fun x => euclideanNorm (u.grad x))) := by
  classical
  set K : ℝ := cubeBesovW12EmbeddingConstant d with hKdef
  set G : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) (fun x => euclideanNorm (u.grad x)) with hGdef
  set L : ℝ := cubeScaleFactor Q with hLdef
  have hK : 0 ≤ K := cubeBesovW12EmbeddingConstant_nonneg d
  have hG : 0 ≤ G := cubeLpNorm_nonneg Q (2 : ℝ≥0∞) _
  have hL : 0 < L := cubeScaleFactor_pos' Q
  set T : ℝ := K * G * L ^ (3 / 4 : ℝ) with hT
  have hT0 : 0 ≤ T := by positivity
  set ρ : ℝ := (3 : ℝ) ^ (-(3 / 4 : ℝ)) with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hdep : ∀ j : ℕ, cubeBesovDepthSeminorm Q (1 / 4 : ℝ) 2 u.toFun j ≤ T * ρ ^ j := by
    intro j
    have h := ca1_depth_le Q u (1 / 4 : ℝ) j
    refine h.trans (le_of_eq ?_)
    have h3 : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
    rw [show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num, Real.div_rpow hL.le h3.le,
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), hρ, hT,
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    rw [show (-(3 / 4 : ℝ) * (j : ℝ)) = -((j : ℝ) * (3 / 4)) by ring,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), div_eq_mul_inv]
    simp only [hKdef, hGdef]
    ring
  have hsq : ∀ j : ℕ, (cubeBesovDepthSeminorm Q (1 / 4 : ℝ) 2 u.toFun j) ^ (2 : ℝ) ≤
      T ^ 2 * (1 / 3 : ℝ) ^ j := by
    intro j
    have h0 : 0 ≤ cubeBesovDepthSeminorm Q (1 / 4 : ℝ) 2 u.toFun j :=
      cubeBesovDepthSeminorm_nonneg Q _ _ _ j
    calc (cubeBesovDepthSeminorm Q (1 / 4 : ℝ) 2 u.toFun j) ^ (2 : ℝ)
        = (cubeBesovDepthSeminorm Q (1 / 4 : ℝ) 2 u.toFun j) ^ 2 := by
          rw [← Real.rpow_natCast]; norm_num
      _ ≤ (T * ρ ^ j) ^ 2 := pow_le_pow_left₀ h0 (hdep j) 2
      _ = T ^ 2 * (ρ ^ 2) ^ j := by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 j]
      _ ≤ T ^ 2 * (1 / 3 : ℝ) ^ j :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ca1_rho_sq_le j) (by positivity)
  have hsum : ∑ j ∈ Finset.range (N + 1), (cubeBesovDepthSeminorm Q (1 / 4 : ℝ) 2 u.toFun j) ^ (2 : ℝ)
      ≤ (2 * T) ^ 2 := by
    calc _ ≤ ∑ j ∈ Finset.range (N + 1), T ^ 2 * (1 / 3 : ℝ) ^ j := Finset.sum_le_sum fun j _ => hsq j
      _ = T ^ 2 * ∑ j ∈ Finset.range (N + 1), (1 / 3 : ℝ) ^ j := by rw [Finset.mul_sum]
      _ ≤ T ^ 2 * 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have := geom_sum_Ico_le_of_lt_one (m := 0) (n := N + 1) (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num)
          rw [← Finset.range_eq_Ico] at this
          refine this.trans ?_
          norm_num
      _ ≤ (2 * T) ^ 2 := by
          have : (2 * T) ^ 2 = 4 * T ^ 2 := by ring
          rw [this]; linarith only [sq_nonneg T]
  have hsem : cubeBesovPartialSeminorm Q (1 / 4 : ℝ) 2 2 N u.toFun ≤ 2 * T := by
    unfold cubeBesovPartialSeminorm
    simp only [ENNReal.toReal_ofNat]
    have := Real.rpow_le_rpow (Finset.sum_nonneg fun j _ =>
      Real.rpow_nonneg (cubeBesovDepthSeminorm_nonneg Q (1 / 4 : ℝ) 2 u.toFun j) _) hsum
      (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    exact this.trans (le_of_eq (sq_rpow_half_eq_of_nonneg (show 0 ≤ 2 * T by positivity)))
  have hmean : cubeBesovScaleWeight (1 / 4 : ℝ) Q * ‖cubeAverage Q u.toFun‖ ≤
      L ^ (-(1 / 4 : ℝ)) * cubeLpNorm Q (2 : ℝ≥0∞) u.toFun :=
    mul_le_mul_of_nonneg_left (norm_cubeAverage_le_cubeLpNorm_two Q _ u.memL2_normalizedCubeMeasure)
      (cubeBesovScaleWeight_nonneg _ Q)
  rw [cubeBesovDualTestNorm_of_conjExponent_ne_top _ _ _ _ _ _ (by rw [ca1_conj_two]; norm_num),
    ca1_conj_two, cubeBesovPartialNorm]
  have hT' : T = K * G * L * L ^ (-(1 / 4 : ℝ)) := by
    rw [hT, show (3 / 4 : ℝ) = 1 + -(1 / 4 : ℝ) by norm_num, Real.rpow_add hL, Real.rpow_one]
    ring
  calc _ ≤ 2 * T + L ^ (-(1 / 4 : ℝ)) * cubeLpNorm Q (2 : ℝ≥0∞) u.toFun := add_le_add hsem hmean
    _ = _ := by rw [hT']; ring

theorem ca1_localMem [NeZero d] (Q : TriadicCube d) (u : H1Function (openCubeSet Q)) :
    CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) u.toFun := by
  intro j R hR
  rw [ca1_conj_two]
  exact (memLp_on_descendant_of_memLp hR u.memL2_normalizedCubeMeasure).sub (memLp_const _)

/-- **Pairing of the dual negative Besov norm of order `1/4` with an `H¹` function** (scalar). -/
theorem ca1_pairing_scalar [NeZero d] (Q : TriadicCube d) (F : Vec d → ℝ)
    (hF : MemLp F 2 (normalizedCubeMeasure Q)) (u : H1Function (openCubeSet Q)) :
    |cubeBesovPairing Q F u.toFun| ≤ cubeBesovDualFullNorm Q (1 / 4 : ℝ) 2 2 F *
      (cubeScaleFactor Q ^ (-(1 / 4 : ℝ)) *
        (cubeLpNorm Q (2 : ℝ≥0∞) u.toFun +
          2 * cubeBesovW12EmbeddingConstant d * cubeScaleFactor Q *
            cubeLpNorm Q (2 : ℝ≥0∞) (fun x => euclideanNorm (u.grad x)))) := by
  set B0 : ℝ := cubeScaleFactor Q ^ (-(1 / 4 : ℝ)) *
        (cubeLpNorm Q (2 : ℝ≥0∞) u.toFun +
          2 * cubeBesovW12EmbeddingConstant d * cubeScaleFactor Q *
            cubeLpNorm Q (2 : ℝ≥0∞) (fun x => euclideanNorm (u.grad x))) with hB0
  set D : ℝ := cubeBesovDualFullNorm Q (1 / 4 : ℝ) 2 2 F with hD
  have hD0 : 0 ≤ D := cubeBesovDualFullNorm_nonneg Q _ _ _ _ (by rw [ca1_conj_two]; norm_num)
    (by rw [ca1_conj_two]; norm_num)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hε' : 0 < ε / (D + 1) := by positivity
  have h := abs_cubeBesovPairing_le_mul_cubeBesovDualFullNorm_of_uniform_bound_two_two Q (1 / 4 : ℝ)
    F u.toFun (B := B0 + ε / (D + 1)) (by norm_num) hF
    (by
      have : 0 ≤ B0 := by
        have := cubeBesovW12EmbeddingConstant_nonneg d
        have := cubeScaleFactor_pos' Q
        have := cubeLpNorm_nonneg Q (2 : ℝ≥0∞) u.toFun
        have := cubeLpNorm_nonneg Q (2 : ℝ≥0∞) (fun x => euclideanNorm (u.grad x))
        positivity
      linarith only [this, hε'])
    (fun N => (ca1_testNorm_le Q u N).trans (by linarith only [hε'])) (ca1_localMem Q u)
  refine h.trans ?_
  have : D * (B0 + ε / (D + 1)) = D * B0 + D * (ε / (D + 1)) := by ring
  rw [this]
  have h2 : D * (ε / (D + 1)) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    have : D * ε ≤ ε * (D + 1) := by linarith only [hε]
    linarith only [this, mul_comm D ε]
  linarith only [h2]

theorem ca1_scale_factor_eq (Q : TriadicCube d) :
    Real.rpow (3 : ℝ) (-(1 / 4 : ℝ) * ((Q.scale : ℤ) : ℝ)) =
      cubeScaleFactor Q ^ (-(1 / 4 : ℝ)) := by
  unfold cubeScaleFactor
  rw [← Real.rpow_intCast, ← Real.rpow_mul (by norm_num)]
  show (3 : ℝ) ^ (-(1 / 4 : ℝ) * ((Q.scale : ℤ) : ℝ)) = (3 : ℝ) ^ (((Q.scale : ℤ) : ℝ) * (-(1 / 4 : ℝ)))
  rw [mul_comm]

theorem ca1_cubeAverage_sum (Q : TriadicCube d) {f : Fin d → Vec d → ℝ}
    (hf : ∀ i, IntegrableOn (f i) (cubeSet Q) volume) :
    cubeAverage Q (fun x => ∑ i, f i x) = ∑ i, cubeAverage Q (f i) := by
  unfold cubeAverage
  rw [integral_finsetSum _ fun i _ => hf i, Finset.mul_sum]

/-- **Pairing of a vector field with an `H¹` vector field**, bounded by the scale-normalized dual
negative Besov norm of order `1/4` (the pairing step behind the display
`e.Dir.new.Cacc.weak.test`). -/
theorem ca1_pairing_vector [NeZero d] (Q : TriadicCube d) (F : Vec d → Vec d)
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (ξ : Fin d → H1Function (openCubeSet Q)) {Λ : ℝ}
    (hΛ : ∀ i, cubeLpNorm Q (2 : ℝ≥0∞) (ξ i).toFun +
      2 * cubeBesovW12EmbeddingConstant d * cubeScaleFactor Q *
        cubeLpNorm Q (2 : ℝ≥0∞) (fun x => euclideanNorm ((ξ i).grad x)) ≤ Λ) :
    |cubeAverage Q (fun x => vecDot (F x) (fun i => (ξ i).toFun x))| ≤
      Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo Q (1 / 4 : ℝ) F * Λ := by
  have hint : ∀ i, IntegrableOn (fun x => F x i * (ξ i).toFun x) (cubeSet Q) volume := fun i =>
    integrableOn_of_integrable_normalizedCubeMeasure (Q := Q)
      ((hF i).integrable_mul (ξ i).memL2_normalizedCubeMeasure)
  have hsum := ca1_cubeAverage_sum Q hint
  have hD : ∀ i, 0 ≤ cubeBesovDualFullNorm Q (1 / 4 : ℝ) 2 2 (fun x => F x i) := fun i =>
    cubeBesovDualFullNorm_nonneg Q _ _ _ _ (by rw [ca1_conj_two]; norm_num)
      (by rw [ca1_conj_two]; norm_num)
  have hs0 : 0 ≤ cubeScaleFactor Q ^ (-(1 / 4 : ℝ)) :=
    Real.rpow_nonneg (cubeScaleFactor_pos' Q).le _
  have hΛ0 : 0 ≤ Λ := le_trans (by
    have := cubeBesovW12EmbeddingConstant_nonneg d
    have := cubeScaleFactor_pos' Q
    have := cubeLpNorm_nonneg Q (2 : ℝ≥0∞) (ξ ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩).toFun
    have := cubeLpNorm_nonneg Q (2 : ℝ≥0∞)
      (fun x => euclideanNorm ((ξ ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩).grad x))
    positivity) (hΛ ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩)
  unfold Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
  rw [ca1_scale_factor_eq, Finset.mul_sum, Finset.sum_mul]
  have hv : (fun x => vecDot (F x) (fun i => (ξ i).toFun x)) = fun x => ∑ i, F x i * (ξ i).toFun x := rfl
  rw [hv, hsum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  have h1 := ca1_pairing_scalar Q (fun x => F x i) (hF i) (ξ i)
  have h2 : cubeScaleFactor Q ^ (-(1 / 4 : ℝ)) *
      cubeBesovDualFullNorm Q (1 / 4 : ℝ) 2 2 (fun x => F x i) * Λ ≥
      cubeBesovDualFullNorm Q (1 / 4 : ℝ) 2 2 (fun x => F x i) *
        (cubeScaleFactor Q ^ (-(1 / 4 : ℝ)) * (cubeLpNorm Q (2 : ℝ≥0∞) (ξ i).toFun +
          2 * cubeBesovW12EmbeddingConstant d * cubeScaleFactor Q *
            cubeLpNorm Q (2 : ℝ≥0∞) (fun x => euclideanNorm ((ξ i).grad x)))) := by
    have := mul_le_mul_of_nonneg_left (hΛ i) (mul_nonneg (hD i) hs0)
    linarith only [this]
  exact h1.trans (by linarith only [h2])


theorem ca1_ofReal_le_toReal {r α β : ℝ} {E G : ℝ≥0∞} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hE : E ≠ ⊤)
    (hG : G ≠ ⊤) (h : ENNReal.ofReal r ≤ ENNReal.ofReal α * E + ENNReal.ofReal β * G) :
    r ≤ α * E.toReal + β * G.toReal := by
  have hfin : ENNReal.ofReal α * E + ENNReal.ofReal β * G ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hE,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hG⟩
  have h1 := ENNReal.toReal_mono hfin h
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hE)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hG), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hα, ENNReal.toReal_ofReal hβ] at h1
  rcases le_or_gt 0 r with hr | hr
  · rwa [ENNReal.toReal_ofReal hr] at h1
  · have : 0 ≤ α * E.toReal + β * G.toReal := by positivity
    linarith only [hr, this]


theorem ca1_cubeAverage_add (Q : TriadicCube d) {f g : Vec d → ℝ}
    (hf : IntegrableOn f (cubeSet Q) volume) (hg : IntegrableOn g (cubeSet Q) volume) (c : ℝ) :
    cubeAverage Q (fun x => f x + c * g x) = cubeAverage Q f + c * cubeAverage Q g := by
  unfold cubeAverage
  rw [integral_add hf (hg.const_mul c), integral_const_mul]
  ring

/-- **The weak test on one cube** (display `e.Dir.new.Cacc.weak.test`, before the
simplification of the coefficients): pairing the field `A ∇u` with an `H¹` vector field `ξ`,
splitting `A = S Id + (A - S Id)`, the two weak bounds of the right-hand-side lemma. -/
theorem ca1_cube_weak_test [NeZero d] (Q : TriadicCube d) {lam Lam : ℝ} {A : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) A) {S α1 β1 α2 β2 Λ : ℝ} (hS : 0 ≤ S)
    (hα1 : 0 ≤ α1) (hβ1 : 0 ≤ β1) (hα2 : 0 ≤ α2) (hβ2 : 0 ≤ β2)
    (u : H1Function (openCubeSet Q)) (f : Vec d → ℝ)
    (hf : SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q (ENNReal.ofReal (sobStar d)).conjExponent f
      ≠ ⊤)
    (ξ : Fin d → H1Function (openCubeSet Q))
    (hflux : ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo Q (1 / 4 : ℝ)
        (fun x => matVecMul (A x - S • (1 : Mat d)) (u.grad x))) ≤
      ENNReal.ofReal α1 * SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2
          (fun x => Real.sqrt (vecNormSq (u.grad x))) +
        ENNReal.ofReal β1 * SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q
          (ENNReal.ofReal (sobStar d)).conjExponent f)
    (hgrad : ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo Q (1 / 4 : ℝ)
        u.grad) ≤
      ENNReal.ofReal α2 * SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2
          (fun x => Real.sqrt (vecNormSq (u.grad x))) +
        ENNReal.ofReal β2 * SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q
          (ENNReal.ofReal (sobStar d)).conjExponent f)
    (hΛ : ∀ i, cubeLpNorm Q (2 : ℝ≥0∞) (ξ i).toFun +
      2 * cubeBesovW12EmbeddingConstant d * cubeScaleFactor Q *
        cubeLpNorm Q (2 : ℝ≥0∞) (fun x => euclideanNorm ((ξ i).grad x)) ≤ Λ) :
    |cubeAverage Q (fun x => vecDot (matVecMul (A x) (u.grad x)) (fun i => (ξ i).toFun x))| ≤
      (S * (α2 * cubeLpNorm Q (2 : ℝ≥0∞) (fun x => Real.sqrt (vecNormSq (u.grad x))) +
          β2 * cubeLpNorm Q (ENNReal.ofReal (sobStar d)).conjExponent f) +
        (α1 * cubeLpNorm Q (2 : ℝ≥0∞) (fun x => Real.sqrt (vecNormSq (u.grad x))) +
          β1 * cubeLpNorm Q (ENNReal.ofReal (sobStar d)).conjExponent f)) * Λ := by
  have hF1 : ∀ i, MemLp (fun x => matVecMul (A x - S • (1 : Mat d)) (u.grad x) i) 2
      (normalizedCubeMeasure Q) := fun i => ((memLp_pi_iff).1 (r1_memLp_flux Q hEll S u)) i
  have hF2 : ∀ i, MemLp (fun x => u.grad x i) 2 (normalizedCubeMeasure Q) :=
    fun i => r1_memLp_grad_comp Q u i
  have hp1 := ca1_pairing_vector Q (fun x => matVecMul (A x - S • (1 : Mat d)) (u.grad x)) hF1 ξ hΛ
  have hp2 := ca1_pairing_vector Q u.grad hF2 ξ hΛ
  have hEfin : SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2
      (fun x => Real.sqrt (vecNormSq (u.grad x))) ≠ ⊤ :=
    (r1_memLp_grad_eucNorm Q u).eLpNorm_ne_top
  have hb1 := ca1_ofReal_le_toReal hα1 hβ1 hEfin hf hflux
  have hb2 := ca1_ofReal_le_toReal hα2 hβ2 hEfin hf hgrad
  rw [SuperdiffusionCLT.Section2.Norms.cubeLpENorm_toReal_eq_cubeLpNorm,
    SuperdiffusionCLT.Section2.Norms.cubeLpENorm_toReal_eq_cubeLpNorm] at hb1 hb2
  have hint : ∀ (G : Vec d → Vec d), (∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q)) →
      IntegrableOn (fun x => vecDot (G x) (fun i => (ξ i).toFun x)) (cubeSet Q) volume := by
    intro G hG
    have : (fun x => vecDot (G x) (fun i => (ξ i).toFun x)) = fun x => ∑ i, G x i * (ξ i).toFun x :=
      rfl
    rw [this]
    refine MeasureTheory.integrable_finsetSum _ fun i _ => ?_
    exact integrableOn_of_integrable_normalizedCubeMeasure (Q := Q)
      ((hG i).integrable_mul (ξ i).memL2_normalizedCubeMeasure)
  have hid : (fun x => vecDot (matVecMul (A x) (u.grad x)) (fun i => (ξ i).toFun x)) =
      fun x => vecDot (matVecMul (A x - S • (1 : Mat d)) (u.grad x)) (fun i => (ξ i).toFun x) +
        S * vecDot (u.grad x) (fun i => (ξ i).toFun x) := by
    funext x
    rw [r1_matVecMul_sub_smul_one, sub_eq_add_neg, vecDot_add_left, vecDot_neg_left,
      vecDot_smul_left]
    ring
  have hΛ0 : 0 ≤ Λ := le_trans (by
    have := cubeBesovW12EmbeddingConstant_nonneg d
    have := cubeScaleFactor_pos' Q
    have := cubeLpNorm_nonneg Q (2 : ℝ≥0∞) (ξ ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩).toFun
    have := cubeLpNorm_nonneg Q (2 : ℝ≥0∞)
      (fun x => euclideanNorm ((ξ ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩).grad x))
    positivity) (hΛ ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩)
  rw [hid, ca1_cubeAverage_add Q (hint _ hF1) (hint _ hF2) S]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_nonneg hS]
  have h1 := mul_le_mul_of_nonneg_right hb1 hΛ0
  have h2 := mul_le_mul_of_nonneg_right hb2 hΛ0
  have h3 := mul_le_mul_of_nonneg_left (hp2.trans h2) hS
  linarith only [hp1, h1, h3]


/-- Witness for `ca1_pairing_vector`: the zero field and the zero test field on the unit square. -/
example : |cubeAverage (originCube 2 0) (fun x => vecDot ((fun _ : Vec 2 => (0 : Vec 2)) x)
      (fun i => ((0 : Fin 2 → H1Function (openCubeSet (originCube 2 0))) i).toFun x))| ≤
    Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo (originCube 2 0) (1 / 4 : ℝ)
      (fun _ : Vec 2 => (0 : Vec 2)) * 0 :=
  ca1_pairing_vector (originCube 2 0) (fun _ => (0 : Vec 2)) (fun i => memLp_const 0)
    (0 : Fin 2 → H1Function (openCubeSet (originCube 2 0))) (Λ := 0) (fun i => by
      simp [cubeLpNorm, euclideanNorm, vecNormSq, vecDot])


/-- Witness for the non-law hypotheses of `ca1_cube_weak_test`: identity field, zero solution,
zero data, zero test field. -/
example : ∃ (Q : TriadicCube 2) (A : CoeffField 2) (lam Lam S α1 β1 α2 β2 : ℝ)
    (u : H1Function (openCubeSet Q)) (f : Vec 2 → ℝ)
    (ξ : Fin 2 → H1Function (openCubeSet Q)) (Λ : ℝ),
    IsEllipticFieldOn lam Lam (openCubeSet Q) A ∧ 0 ≤ S ∧ 0 ≤ α1 ∧ 0 ≤ β1 ∧ 0 ≤ α2 ∧ 0 ≤ β2 ∧
    SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q (ENNReal.ofReal (sobStar 2)).conjExponent f ≠ ⊤ ∧
    ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo Q (1 / 4 : ℝ)
        (fun x => matVecMul (A x - S • (1 : Mat 2)) (u.grad x))) ≤
      ENNReal.ofReal α1 * SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2
          (fun x => Real.sqrt (vecNormSq (u.grad x))) +
        ENNReal.ofReal β1 * SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q
          (ENNReal.ofReal (sobStar 2)).conjExponent f ∧
    ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo Q (1 / 4 : ℝ) u.grad) ≤
      ENNReal.ofReal α2 * SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2
          (fun x => Real.sqrt (vecNormSq (u.grad x))) +
        ENNReal.ofReal β2 * SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q
          (ENNReal.ofReal (sobStar 2)).conjExponent f ∧
    ∀ i, cubeLpNorm Q (2 : ℝ≥0∞) (ξ i).toFun +
      2 * cubeBesovW12EmbeddingConstant 2 * cubeScaleFactor Q *
        cubeLpNorm Q (2 : ℝ≥0∞) (fun x => euclideanNorm ((ξ i).grad x)) ≤ Λ := by
  obtain ⟨K, hK, hD⟩ := r1_ofReal_dual_le 2
  have hz : ∀ S : ℝ, ((fun x : Vec 2 => matVecMul ((fun _ : Vec 2 => (1 : Mat 2)) x - S • (1 : Mat 2))
      ((0 : H1Function (openCubeSet (originCube 2 0))).grad x)) = fun _ => (0 : Vec 2)) := by
    intro S; funext x i; simp [matVecMul]
  have hz2 : ((0 : H1Function (openCubeSet (originCube 2 0))).grad) = fun _ => (0 : Vec 2) := by
    funext x; simp
  have hdz : ∀ F : Vec 2 → Vec 2, F = (fun _ => (0 : Vec 2)) →
      ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo (originCube 2 0)
        (1 / 4 : ℝ) F) ≤ 0 := by
    intro F hF
    subst hF
    refine (hD (originCube 2 0) _ (fun i => memLp_const 0) (by simp [vecNormSq, vecDot])).trans ?_
    simp [SuperdiffusionCLT.Section2.Norms.cubeLpENorm, vecNormSq, vecDot]
  refine ⟨originCube 2 0, fun _ => 1, 1, 1, 1, 0, 0, 0, 0, 0, fun _ => 0, 0, 0,
    Section6.ew1_ellip _ (measurableSet_openCubeSet _), zero_le_one, le_rfl, le_rfl, le_rfl, le_rfl,
    ?_, ?_, ?_, fun i => ?_⟩
  · simp [SuperdiffusionCLT.Section2.Norms.cubeLpENorm]
  · simpa [hz] using hdz _ (hz 1)
  · rw [hz2]; simpa using hdz _ rfl
  · simp [cubeLpNorm, euclideanNorm, vecNormSq, vecDot]


theorem ca1_cubeAverage_eq (Q : TriadicCube d) (g : Vec d → ℝ) :
    cubeAverage Q g = (cubeVolume Q)⁻¹ * ∫ x in openCubeSet Q, g x := by
  unfold cubeAverage
  rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]

theorem ca1_cubeLpNorm_sq (Q : TriadicCube d) {g : Vec d → ℝ} (hg : MemLp g 2 (normalizedCubeMeasure Q)) :
    cubeLpNorm Q (2 : ℝ≥0∞) g ^ 2 = cubeAverage Q (fun x => g x ^ 2) := by
  have h := cubeLpNorm_rpow_eq_cubeAverage_norm_rpow Q (2 : ℝ≥0∞) g (by norm_num) (by norm_num) hg
  simpa [sq_abs] using h

theorem ca1_desc_sq (Q : TriadicCube d) {g : Vec d → ℝ} (hg : MemLp g 2 (normalizedCubeMeasure Q))
    (j : ℕ) :
    descendantsAverage Q j (fun R => cubeLpNorm R (2 : ℝ≥0∞) g ^ 2) = cubeLpNorm Q (2 : ℝ≥0∞) g ^ 2 :=
  cubeL2ScalarDepthAverage_eq_cubeLpNorm_two_sq Q g j hg

theorem ca1_avg_mul_le (Q : TriadicCube d) {g h : Vec d → ℝ} (hg : MemLp g 2 (normalizedCubeMeasure Q))
    (hh : MemLp h 2 (normalizedCubeMeasure Q)) :
    |cubeAverage Q (fun x => g x * h x)| ≤ cubeLpNorm Q (2 : ℝ≥0∞) g * cubeLpNorm Q (2 : ℝ≥0∞) h := by
  have := abs_cubeAverage_mul_le_mul_cubeLpNorm_conjExponent Q (2 : ℝ≥0∞) g h hg
    (by rw [show ENNReal.conjExponent (2 : ℝ≥0∞) = 2 by
      simpa [cubeBesovConjExponent] using
        (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))]; exact hh)
    (by norm_num)
  rwa [show ENNReal.conjExponent (2 : ℝ≥0∞) = 2 by
      simpa [cubeBesovConjExponent] using
        (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))] at this

/-- A pointwise bound `|T| ≤ C g h` gives a bound on the average of `T`. -/
theorem ca1_avg_le_of_bound (Q : TriadicCube d) {T g h : Vec d → ℝ}
    (hT : AEStronglyMeasurable T (normalizedCubeMeasure Q))
    (hg : MemLp g 2 (normalizedCubeMeasure Q)) (hh : MemLp h 2 (normalizedCubeMeasure Q)) {C : ℝ}
    (hC : 0 ≤ C)
    (hb : ∀ᵐ x ∂(normalizedCubeMeasure Q), |T x| ≤ C * (g x * h x)) :
    |cubeAverage Q T| ≤ C * (cubeLpNorm Q (2 : ℝ≥0∞) g * cubeLpNorm Q (2 : ℝ≥0∞) h) := by
  have hgh : Integrable (fun x => g x * h x) (normalizedCubeMeasure Q) := hg.integrable_mul hh
  have hTint : Integrable T (normalizedCubeMeasure Q) :=
    (hgh.const_mul C).mono' hT (hb.mono fun x hx => by simpa [Real.norm_eq_abs] using hx)
  rw [cubeAverage_eq_integral_normalizedCubeMeasure]
  calc |∫ x, T x ∂normalizedCubeMeasure Q| ≤ ∫ x, |T x| ∂normalizedCubeMeasure Q :=
        abs_integral_le_integral_abs
    _ ≤ ∫ x, C * (g x * h x) ∂normalizedCubeMeasure Q :=
        integral_mono_ae hTint.abs (hgh.const_mul C) hb
    _ = C * cubeAverage Q (fun x => g x * h x) := by
        rw [integral_const_mul, cubeAverage_eq_integral_normalizedCubeMeasure]
    _ ≤ C * (cubeLpNorm Q (2 : ℝ≥0∞) g * cubeLpNorm Q (2 : ℝ≥0∞) h) := by
        refine mul_le_mul_of_nonneg_left ?_ hC
        exact (le_abs_self _).trans (ca1_avg_mul_le Q hg hh)

theorem ca1_prob (Q : TriadicCube d) : IsProbabilityMeasure (normalizedCubeMeasure Q) :=
  ⟨by simp [normalizedCubeMeasure_apply_univ]⟩

theorem ca1_cubeLpNorm_mono_exp (Q : TriadicCube d) {p : ℝ≥0∞} (hp : p ≤ 2) {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    cubeLpNorm Q p f ≤ cubeLpNorm Q (2 : ℝ≥0∞) f := by
  have := ca1_prob Q
  unfold cubeLpNorm
  exact ENNReal.toReal_mono hf.eLpNorm_ne_top (eLpNorm_le_eLpNorm_of_exponent_le hp)



theorem ca1_conj_le_two (hd : 2 ≤ d) : (ENNReal.ofReal (sobStar d)).conjExponent ≤ 2 := by
  have h1 := r1_conj_real hd
  have h2 := two_lt_sobStar hd
  have h3 := r1_conj_ne_top hd
  have hpos : 0 < (ENNReal.ofReal (sobStar d)).conjExponent.toReal := by
    have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (sobStar d) := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by linarith only [h2])
    have := (ENNReal.HolderConjugate.conjExponent hq1).symm
    have h0 := ENNReal.HolderConjugate.ne_zero (ENNReal.ofReal (sobStar d)).conjExponent
      (ENNReal.ofReal (sobStar d))
    exact ENNReal.toReal_pos h0 h3
  have h4 : (ENNReal.ofReal (sobStar d)).conjExponent.toReal ≤ 2 := by
    have h5 : (sobStar d)⁻¹ < 1 / 2 := by
      rw [one_div]; exact inv_strictAnti₀ (by norm_num) h2
    have h6 : (1 : ℝ) / 2 < ((ENNReal.ofReal (sobStar d)).conjExponent.toReal)⁻¹ := by
      linarith only [h1, h5]
    rw [lt_inv_comm₀ (by norm_num) hpos] at h6
    linarith only [h6]
  have h7 : (ENNReal.ofReal (sobStar d)).conjExponent.toReal ≤ (2 : ℝ≥0∞).toReal := by simpa using h4
  exact (ENNReal.toReal_le_toReal h3 (by norm_num)).1 h7

theorem ca1_young {r p q : ℝ} (hr : 0 < r) : p * q ≤ r / 2 * p ^ 2 + q ^ 2 / (2 * r) := by
  have h : 0 ≤ (r * p - q) ^ 2 := sq_nonneg _
  have e : r / 2 * p ^ 2 + q ^ 2 / (2 * r) - p * q = (r * p - q) ^ 2 / (2 * r) := by
    field_simp
    ring
  have : 0 ≤ (r * p - q) ^ 2 / (2 * r) :=
    div_nonneg (sq_nonneg _) (mul_nonneg zero_le_two hr.le)
  linarith only [e, this]

/-- **The final algebra** of the interior Caccioppoli inequality: from the sum bound and the crude
bound to `ν g² ≤ C (S w² + S⁻¹ f²)`, under the scale separation `τ s² ≤ 1`, `τ Ξ ≤ 1`. -/
theorem ca1_alg {ν S α b τ Λ D Cα c1 c2 c3 c4 c5 c6 c7 c8 g k w f : ℝ} (hν : 0 < ν) (hνS : ν ≤ S)
    (hα : α ^ 2 ≤ Cα * S * ν) (hb : b ≤ 1) (hτ0 : 0 ≤ τ)
    (hD : 1 ≤ D) (hτs : τ * (S / ν) ^ 2 ≤ 1) (hτΞ : τ * (1 + D * Λ ^ 2 / ν ^ 2) ≤ 1)
    (hCα : 0 ≤ Cα) (hc4 : 0 ≤ c4) (hc5 : 0 ≤ c5)
    (hc6 : 0 ≤ c6) (hc7 : 0 ≤ c7) (hc8 : 0 ≤ c8) (hk : 0 ≤ k) (hw : 0 ≤ w)
    (hf : 0 ≤ f)
    (hI : ν * g ^ 2 ≤ f * w + c1 * α * g * w + c2 * τ * α * g * k + c3 * τ * α * k * w +
      c4 * b * f * w + c5 * τ * b * f * k + c6 * τ * b * f * w + c7 * Λ * τ ^ 5 * k * w)
    (hII : ν * k ^ 2 ≤ c8 * (ν⁻¹ * f ^ 2 + ν * w ^ 2 + D * Λ ^ 2 * ν⁻¹ * w ^ 2)) :
    ν * g ^ 2 ≤ (4 / 3 * (1 / 2 + 2 * c1 ^ 2 * Cα + 2 * c2 ^ 2 * Cα * c8 + (c8 + c3 ^ 2 * Cα) / 2 +
      c4 / 2 + c5 * (1 + c8) / 2 + c6 / 2 + c7 * (1 + c8) / 2)) * (S * w ^ 2 + S⁻¹ * f ^ 2) := by
  have hS : 0 < S := lt_of_lt_of_le hν hνS
  have hSinv : 0 < S⁻¹ := inv_pos.2 hS
  set T : ℝ := S * w ^ 2 + S⁻¹ * f ^ 2 with hT
  set Ξ : ℝ := 1 + D * Λ ^ 2 / ν ^ 2 with hΞ
  have hSS : S * S⁻¹ = 1 := mul_inv_cancel₀ hS.ne'
  have hνν : ν⁻¹ * ν = 1 := inv_mul_cancel₀ hν.ne'
  have hD0 : 0 ≤ D := by linarith only [hD]
  have hSw : 0 ≤ S * w ^ 2 := mul_nonneg hS.le (sq_nonneg w)
  have hSf : 0 ≤ S⁻¹ * f ^ 2 := mul_nonneg hSinv.le (sq_nonneg f)
  have hν4 : 0 < ν / 4 := div_pos hν (by norm_num)
  have hΞ1 : 1 ≤ Ξ := by
    have : 0 ≤ D * Λ ^ 2 / ν ^ 2 := div_nonneg (mul_nonneg hD0 (sq_nonneg Λ)) (sq_nonneg ν)
    linarith only [this]
  have hτ1 : τ ≤ 1 := by
    have h1 : 1 ≤ (S / ν) ^ 2 := by
      have : 1 ≤ S / ν := by rw [le_div_iff₀ hν]; linarith only [hνS]
      exact one_le_pow₀ this
    exact (le_mul_of_one_le_right hτ0 h1).trans hτs
  have hτ2 : τ ^ 2 ≤ τ := by rw [sq]; exact mul_le_of_le_one_right hτ0 hτ1
  have hT0 : 0 ≤ T := add_nonneg hSw hSf
  -- the crude bound in the form `k² ≤ c8 (ν⁻² f² + Ξ w²)`
  have hk2 : k ^ 2 ≤ c8 * (ν⁻¹ ^ 2 * f ^ 2 + Ξ * w ^ 2) := by
    have h1 := mul_le_mul_of_nonneg_left hII (inv_nonneg.2 hν.le)
    have e1 : ν⁻¹ * (ν * k ^ 2) = k ^ 2 := by rw [← mul_assoc, hνν, one_mul]
    have e2 : ν⁻¹ * (c8 * (ν⁻¹ * f ^ 2 + ν * w ^ 2 + D * Λ ^ 2 * ν⁻¹ * w ^ 2)) =
        c8 * (ν⁻¹ ^ 2 * f ^ 2 + Ξ * w ^ 2) := by
      rw [hΞ]; linear_combination (c8 * w ^ 2) * hνν
    rw [e1, e2] at h1
    exact h1
  -- Q3: τ S k² ≤ c8 T
  have hQ3 : τ * S * k ^ 2 ≤ c8 * T := by
    have h1 := mul_le_mul_of_nonneg_left hk2 (mul_nonneg hτ0 hS.le)
    have e1 : τ * S * (c8 * (ν⁻¹ ^ 2 * f ^ 2 + Ξ * w ^ 2)) =
        c8 * ((τ * (S / ν) ^ 2) * (S⁻¹ * f ^ 2) + (τ * Ξ) * (S * w ^ 2)) := by
      linear_combination (-(c8 * τ * ν⁻¹ ^ 2 * f ^ 2 * S)) * hSS
    rw [e1] at h1
    refine h1.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hc8
    have a1 : (τ * (S / ν) ^ 2) * (S⁻¹ * f ^ 2) ≤ 1 * (S⁻¹ * f ^ 2) :=
      mul_le_mul_of_nonneg_right hτs hSf
    have a2 : (τ * Ξ) * (S * w ^ 2) ≤ 1 * (S * w ^ 2) :=
      mul_le_mul_of_nonneg_right hτΞ hSw
    rw [hT]; linarith only [a1, a2]
  have hQ2 : τ ^ 2 * ν * k ^ 2 ≤ c8 * T := by
    have : τ ^ 2 * ν * k ^ 2 ≤ τ * S * k ^ 2 := by
      have h1 : τ ^ 2 * ν ≤ τ * S := by
        exact calc τ ^ 2 * ν ≤ τ * ν := mul_le_mul_of_nonneg_right hτ2 hν.le
          _ ≤ τ * S := mul_le_mul_of_nonneg_left hνS hτ0
      exact mul_le_mul_of_nonneg_right h1 (sq_nonneg k)
    exact this.trans hQ3
  -- (a)
  have ta : f * w ≤ T / 2 := by
    have := ca1_young (r := S⁻¹) (p := f) (q := w) hSinv
    have e : w ^ 2 / (2 * S⁻¹) = S * w ^ 2 / 2 := by
      rw [div_eq_mul_inv, mul_inv, inv_inv]; ring
    rw [e] at this
    rw [hT]; linarith only [this]
  -- (b)
  have tb : c1 * α * g * w ≤ ν / 8 * g ^ 2 + 2 * c1 ^ 2 * Cα * T := by
    have := ca1_young (r := ν / 4) (p := g) (q := c1 * α * w) hν4
    have e : (c1 * α * w) ^ 2 / (2 * (ν / 4)) = 2 * c1 ^ 2 * (α ^ 2 / ν) * w ^ 2 := by ring
    rw [e] at this
    have h1 : α ^ 2 / ν ≤ Cα * S := by rw [div_le_iff₀ hν]; linarith only [hα]
    have h2 : 2 * c1 ^ 2 * (α ^ 2 / ν) * w ^ 2 ≤ 2 * c1 ^ 2 * (Cα * S) * w ^ 2 := by
      have := mul_le_mul_of_nonneg_left h1 (mul_nonneg zero_le_two (sq_nonneg c1))
      exact mul_le_mul_of_nonneg_right this (sq_nonneg w)
    have h3 : 2 * c1 ^ 2 * (Cα * S) * w ^ 2 ≤ 2 * c1 ^ 2 * Cα * T := by
      rw [hT]
      have : 0 ≤ 2 * c1 ^ 2 * Cα * (S⁻¹ * f ^ 2) :=
        mul_nonneg (mul_nonneg (mul_nonneg zero_le_two (sq_nonneg c1)) hCα) hSf
      linarith only [this]
    have e2 : c1 * α * g * w = g * (c1 * α * w) := by ring
    rw [e2]
    have e3 : ν / 4 / 2 * g ^ 2 = ν / 8 * g ^ 2 := by ring
    rw [e3] at this
    linarith only [this, h2, h3]
  -- (c)
  have tc : c2 * τ * α * g * k ≤ ν / 8 * g ^ 2 + 2 * c2 ^ 2 * Cα * c8 * T := by
    have := ca1_young (r := ν / 4) (p := g) (q := c2 * τ * α * k) hν4
    have e : (c2 * τ * α * k) ^ 2 / (2 * (ν / 4)) = 2 * c2 ^ 2 * (α ^ 2 / ν) * (τ ^ 2 * k ^ 2) := by
      ring
    rw [e] at this
    have h1 : α ^ 2 / ν ≤ Cα * S := by rw [div_le_iff₀ hν]; linarith only [hα]
    have h2 : 2 * c2 ^ 2 * (α ^ 2 / ν) * (τ ^ 2 * k ^ 2) ≤ 2 * c2 ^ 2 * (Cα * S) * (τ ^ 2 * k ^ 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (mul_nonneg zero_le_two (sq_nonneg c2)))
        (mul_nonneg (sq_nonneg τ) (sq_nonneg k))
    have h3 : τ ^ 2 * S * k ^ 2 ≤ c8 * T := by
      exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hτ2 hS.le) (sq_nonneg k)).trans hQ3
    have h4 : 2 * c2 ^ 2 * (Cα * S) * (τ ^ 2 * k ^ 2) ≤ 2 * c2 ^ 2 * Cα * c8 * T := by
      have := mul_le_mul_of_nonneg_left h3 (mul_nonneg (mul_nonneg zero_le_two (sq_nonneg c2)) hCα)
      exact calc 2 * c2 ^ 2 * (Cα * S) * (τ ^ 2 * k ^ 2) = 2 * c2 ^ 2 * Cα * (τ ^ 2 * S * k ^ 2) := by ring
        _ ≤ 2 * c2 ^ 2 * Cα * (c8 * T) := this
        _ = _ := by ring
    have e2 : c2 * τ * α * g * k = g * (c2 * τ * α * k) := by ring
    rw [e2]
    have e3 : ν / 4 / 2 * g ^ 2 = ν / 8 * g ^ 2 := by ring
    rw [e3] at this
    linarith only [this, h2, h4]
  -- (d)
  have td : c3 * τ * α * k * w ≤ (c8 + c3 ^ 2 * Cα) / 2 * T := by
    have := ca1_young (r := ν) (p := τ * k) (q := c3 * α * w) hν
    have e : (c3 * α * w) ^ 2 / (2 * ν) = c3 ^ 2 * (α ^ 2 / ν) * w ^ 2 / 2 := by ring
    rw [e] at this
    have h1 : α ^ 2 / ν ≤ Cα * S := by rw [div_le_iff₀ hν]; linarith only [hα]
    have h2 : c3 ^ 2 * (α ^ 2 / ν) * w ^ 2 ≤ c3 ^ 2 * (Cα * S) * w ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (sq_nonneg c3)) (sq_nonneg w)
    have h3 : c3 ^ 2 * (Cα * S) * w ^ 2 ≤ c3 ^ 2 * Cα * T := by
      rw [hT]
      have : 0 ≤ c3 ^ 2 * Cα * (S⁻¹ * f ^ 2) := mul_nonneg (mul_nonneg (sq_nonneg c3) hCα) hSf
      linarith only [this]
    have e2 : c3 * τ * α * k * w = (τ * k) * (c3 * α * w) := by ring
    rw [e2]
    have e3 : ν / 2 * (τ * k) ^ 2 = τ ^ 2 * ν * k ^ 2 / 2 := by ring
    rw [e3] at this
    linarith only [this, h2, h3, hQ2]
  -- (e), (g)
  have te : c4 * b * f * w ≤ c4 / 2 * T := by
    have h1 : c4 * b * f * w ≤ c4 * (f * w) := by
      have : b * (f * w) ≤ 1 * (f * w) := mul_le_mul_of_nonneg_right hb (mul_nonneg hf hw)
      have := mul_le_mul_of_nonneg_left this hc4
      linarith only [this]
    have := mul_le_mul_of_nonneg_left ta hc4
    linarith only [h1, this]
  have tg : c6 * τ * b * f * w ≤ c6 / 2 * T := by
    have h0 : τ * b ≤ 1 :=
      (mul_le_mul_of_nonneg_left hb hτ0).trans (by rw [mul_one]; exact hτ1)
    have h1 : c6 * τ * b * f * w ≤ c6 * (f * w) := by
      have : (τ * b) * (f * w) ≤ 1 * (f * w) := mul_le_mul_of_nonneg_right h0 (mul_nonneg hf hw)
      have := mul_le_mul_of_nonneg_left this hc6
      linarith only [this]
    have := mul_le_mul_of_nonneg_left ta hc6
    linarith only [h1, this]
  -- (f)
  have tf : c5 * τ * b * f * k ≤ c5 * (1 + c8) / 2 * T := by
    have := ca1_young (r := S⁻¹) (p := f) (q := k) hSinv
    have e : k ^ 2 / (2 * S⁻¹) = S * k ^ 2 / 2 := by
      rw [div_eq_mul_inv, mul_inv, inv_inv]; ring
    rw [e] at this
    have h0 : τ * b ≤ τ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hb hτ0
    have h1 : c5 * τ * b * f * k ≤ c5 * τ * (f * k) := by
      have : (τ * b) * (f * k) ≤ τ * (f * k) := mul_le_mul_of_nonneg_right h0 (mul_nonneg hf hk)
      have := mul_le_mul_of_nonneg_left this hc5
      linarith only [this]
    have h2 : τ * (f * k) ≤ τ * (S⁻¹ / 2 * f ^ 2 + S * k ^ 2 / 2) := mul_le_mul_of_nonneg_left this hτ0
    have h3 : τ * (S⁻¹ / 2 * f ^ 2 + S * k ^ 2 / 2) ≤ T / 2 + c8 * T / 2 := by
      have a1 : τ * (S⁻¹ * f ^ 2) ≤ 1 * (S⁻¹ * f ^ 2) := mul_le_mul_of_nonneg_right hτ1 hSf
      have a2 : S⁻¹ * f ^ 2 ≤ T := by
        rw [hT]; linarith only [hSw]
      have e1 : τ * (S⁻¹ / 2 * f ^ 2 + S * k ^ 2 / 2) = (τ * (S⁻¹ * f ^ 2)) / 2 + (τ * S * k ^ 2) / 2 := by
        ring
      rw [e1]
      linarith only [a1, a2, hQ3]
    have h4 := mul_le_mul_of_nonneg_left (h2.trans h3) hc5
    linarith only [h1, h4]
  -- (h)
  have th : c7 * Λ * τ ^ 5 * k * w ≤ c7 * (1 + c8) / 2 * T := by
    have := ca1_young (r := ν) (p := τ * k) (q := Λ * τ ^ 4 * w) hν
    have e : (Λ * τ ^ 4 * w) ^ 2 / (2 * ν) = Λ ^ 2 / ν * τ ^ 8 * w ^ 2 / 2 := by ring
    rw [e] at this
    have h1 : Λ ^ 2 / ν ≤ ν * Ξ := by
      rw [div_le_iff₀ hν, hΞ]
      have : D * Λ ^ 2 / ν ^ 2 * ν ^ 2 = D * Λ ^ 2 := div_mul_cancel₀ _ (pow_ne_zero 2 hν.ne')
      have h9 := mul_nonneg (sub_nonneg.2 hD) (sq_nonneg Λ)
      linarith only [this, h9, sq_nonneg ν]
    have h2 : Λ ^ 2 / ν * τ ^ 8 * w ^ 2 ≤ S * w ^ 2 := by
      have a1 : τ ^ 8 * Ξ ≤ 1 := by
        have e1 : τ ^ 8 ≤ τ := by
          have : τ ^ 8 ≤ τ ^ 1 := pow_le_pow_of_le_one hτ0 hτ1 (by norm_num)
          simpa only [pow_one] using this
        exact (mul_le_mul_of_nonneg_right e1 (by linarith only [hΞ1])).trans hτΞ
      exact calc Λ ^ 2 / ν * τ ^ 8 * w ^ 2 ≤ (ν * Ξ) * τ ^ 8 * w ^ 2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (pow_nonneg hτ0 8)) (sq_nonneg w)
        _ = ν * (τ ^ 8 * Ξ) * w ^ 2 := by ring
        _ ≤ ν * 1 * w ^ 2 := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left a1 hν.le) (sq_nonneg w)
        _ ≤ S * w ^ 2 := by
            rw [mul_one]; exact mul_le_mul_of_nonneg_right hνS (sq_nonneg w)
    have e2 : c7 * Λ * τ ^ 5 * k * w = c7 * ((τ * k) * (Λ * τ ^ 4 * w)) := by ring
    rw [e2]
    have e3 : ν / 2 * (τ * k) ^ 2 = τ ^ 2 * ν * k ^ 2 / 2 := by ring
    rw [e3] at this
    have h5 : (τ * k) * (Λ * τ ^ 4 * w) ≤ (1 + c8) / 2 * T := by
      have h6 : S * w ^ 2 ≤ T := by rw [hT]; linarith only [hSf]
      linarith only [this, h2, hQ2, h6]
    have := mul_le_mul_of_nonneg_left h5 hc7
    linarith only [this]
  -- the sum
  have hfinal : ν * g ^ 2 ≤ T / 2 + (c1 * α * g * w) + c2 * τ * α * g * k + c3 * τ * α * k * w +
      c4 * b * f * w + c5 * τ * b * f * k + c6 * τ * b * f * w + c7 * Λ * τ ^ 5 * k * w := by
    linarith only [hI, ta]
  linarith only [hfinal, tb, tc, td, te, tf, tg, th, hT0]

theorem ca1_rhs_eq {d : ℕ} {L ℓ K K0 c0 D S α1 α2 β1 β2 Λ W Fg G Gc : ℝ} (hL : 0 < L) (hc0 : 0 < c0) :
    Fg * W +
      ((S * α2 + α1) * (12 * 64 ^ d * 64 ^ d * (L / 4)⁻¹ * G) * W +
        2 * K * ℓ * (S * α2 + α1) * ((12 * 64 ^ d * 64 ^ d * (L / 4)⁻¹ * G) * (c0⁻¹ * Gc)) +
        2 * K * ℓ * (Real.sqrt D * (K0 * (L / 4)⁻¹ ^ 2)) * (S * α2 + α1) * (c0⁻¹ * Gc * W) +
        (S * β2 + β1) * (12 * 64 ^ d * (L / 4)⁻¹) * (Fg * W) +
        2 * K * ℓ * (S * β2 + β1) * (12 * 64 ^ d * (L / 4)⁻¹) * (Fg * (c0⁻¹ * Gc)) +
        2 * K * ℓ * (Real.sqrt D * (K0 * (L / 4)⁻¹ ^ 2)) * (S * β2 + β1) * (Fg * W) +
        (Λ * (Real.sqrt D * (12 * (L / 4)⁻¹ * (4 * ℓ / (L / 4)) ^ 5))) * (c0⁻¹ * Gc * W)) =
    (L * Fg) * (W / L) + (4 * (12 * 64 ^ d * 64 ^ d)) * (S * α2 + α1) * G * (W / L) +
      (8 * K * (12 * 64 ^ d * 64 ^ d) * c0⁻¹) * (ℓ / L) * (S * α2 + α1) * G * Gc +
      (32 * K * Real.sqrt D * K0 * c0⁻¹) * (ℓ / L) * (S * α2 + α1) * Gc * (W / L) +
      (48 * 64 ^ d) * ((S * β2 + β1) / L) * (L * Fg) * (W / L) +
      (96 * 64 ^ d * K * c0⁻¹) * (ℓ / L) * ((S * β2 + β1) / L) * (L * Fg) * Gc +
      (32 * K * Real.sqrt D * K0) * (ℓ / L) * ((S * β2 + β1) / L) * (L * Fg) * (W / L) +
      (48 * Real.sqrt D * 16 ^ 5 * c0⁻¹) * Λ * (ℓ / L) ^ 5 * Gc * (W / L) := by
  field_simp
  ring

theorem ca1_scale_facts (m : ℤ) (h : ℕ) (hh : 3 ≤ h) : 27 * (3 : ℝ) ^ (m - (h : ℤ)) ≤ (3 : ℝ) ^ m := by
  have h1 : (3 : ℝ) ^ m = (3 : ℝ) ^ (m - (h : ℤ)) * 3 ^ h := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]; congr 1; ring
  have h2 : (27 : ℝ) ≤ 3 ^ h := by
    calc (27 : ℝ) = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ h := pow_le_pow_right₀ (by norm_num) hh
  have h3 : 0 < (3 : ℝ) ^ (m - (h : ℤ)) := zpow_pos (by norm_num) _
  rw [h1]
  nlinarith only [h2, h3]

end SuperdiffusionCLT.Section7
