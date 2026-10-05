/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.WeakNorms.WeakNormSqA
public import Homogenization.Book.Ch05.Theorems.Section53.WeakNormsMaximizer.AssemblyFinal

/-!
# Squared weak norms, part B: the gradient maximizer right-hand side is linear in `1 + W·M⁺`

Samplewise and law-free. Fix a positive-definite reference `E`, scales `k < m`, exponents
`0 < s' < s` with `ρ/2 < s'`, `0 ≤ ρ`, and a sample `a` that is a.e. locally elliptic, has
symmetric positive-semidefinite coarse block matrices on every triadic cube, and whose event
quantity `M⁺ := M⁺_{m,ρ}(E; a)` has a bounded index set. With `W := 3^{ρ·(m-k)}`, every term of
CG's gradient maximizer right-hand side `gradientRHSAtScale` is at most a constant depending only
on `(E, m, k, s, s', ρ, C, p, q, p0)` times `1 + W·M⁺`:

* the average term, through `akhcWNSq_gradientAverage_self_le` (quadratic in `1 + c`, then a
  square root);
* the mismatch and low-scale terms, through `√(λ⁻¹)·√J` with `λ⁻¹ ≤ C·|E_{LR}|·(1 + M⁺)`
  (`MaximizerBridgeD.lean`) and `J ≤ (1 + W·M⁺)·(½(−p,q)·E(−p,q) + |p·q|)`;
* the constant tail, trivially.

The point is the power: the squared weak norm is at most **quadratic** in `M⁺`, so its
expectation is finite as soon as `E[(M⁺)²] < ∞`. Main result: `akhcWNSq_gradientRHSAtScale_le`.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.WeakNorms

noncomputable section

open Homogenization
open Homogenization.Book

variable {d : ℕ}

/-! ## Reference-matrix facts -/

theorem akhcWNSq_quadratic_nonneg_of_posDef {E : BlockMat d} (hE : (toFullBlockMat E).PosDef)
    (Z : BlockVec d) : 0 ≤ blockVecDot Z (blockMatVecMul E Z) := by
  have hstep :
      0 ≤ dotProduct (toFullBlockVec Z) (Matrix.mulVec (toFullBlockMat E) (toFullBlockVec Z)) := by
    simpa using hE.posSemidef.dotProduct_mulVec_nonneg (toFullBlockVec Z)
  rwa [← toFullBlockVec_blockMatVecMul, dotProduct_toFullBlockVec] at hstep

/-- Loewner bounds against a positive-semidefinite reference are monotone in the factor. -/
theorem akhcWNSq_loewnerLE_mono {A E : BlockMat d} (hE : (toFullBlockMat E).PosDef) {c c' : ℝ}
    (hcc : c ≤ c') (h : BlockMatLoewnerLE A ((1 + c) • E)) : BlockMatLoewnerLE A ((1 + c') • E) := by
  intro Z
  have h1 := h Z
  rw [blockMatVecMul_blockSMul, blockVecDot_smul_right] at h1 ⊢
  have h0 := akhcWNSq_quadratic_nonneg_of_posDef hE Z
  have h2 : (1 + c) * blockVecDot Z (blockMatVecMul E Z) ≤
      (1 + c') * blockVecDot Z (blockMatVecMul E Z) :=
    mul_le_mul_of_nonneg_right (by linarith only [hcc]) h0
  linarith only [h1, h2]

/-! ## The uniform Loewner bound on every descendant up to depth `m - k` -/

/-- The factor `W := 3^{ρ·(m-k)}`. -/
def akhcWNSq_W (ρ : ℝ) (m k : ℤ) : ℝ := Real.rpow (3 : ℝ) (ρ * (Int.toNat (m - k) : ℝ))

theorem akhcWNSq_one_le_W {ρ : ℝ} (hρ : 0 ≤ ρ) (m k : ℤ) : 1 ≤ akhcWNSq_W ρ m k :=
  Real.one_le_rpow (by norm_num) (mul_nonneg hρ (Nat.cast_nonneg _))

/-- Every descendant `R` of `cu_m` of depth `j ≤ m - k` satisfies
`bfA(R; a) ≤ (1 + W·M⁺)·E`. -/
theorem akhcWNSq_loewner_descendant [NeZero d] {E : BlockMat d}
    (hE : (toFullBlockMat E).PosDef) {a : RegCoeffField d} {m k : ℤ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hBdd :
      BddAbove
        {M : ℝ |
          ∃ Q : TriadicCube d,
            Q.scale ≤ m ∧
              cubeCenter Q ∈ cubeSet (originCube d m) ∧
              M =
                Real.rpow (3 : ℝ) (-ρ * ((m : ℝ) - (Q.scale : ℝ))) *
                  SuperdiffusionCLT.AKHC61.Tails.akhcTailEll_excess E
                    (coarseBlockMatrix (cubeSet Q) a.toFun)})
    {j : ℕ} (hj : j ≤ Int.toNat (m - k)) {R : TriadicCube d}
    (hR : R ∈ descendantsAtDepth (originCube d m) j) :
    BlockMatLoewnerLE (coarseBlockMatrix (cubeSet R) a.toFun)
      ((1 + akhcWNSq_W ρ m k * akhcWeakC_eventMoreprotoPlus m ρ E a.toFun) • E) := by
  have hscale : R.scale = m - (j : ℤ) := scale_eq_sub_of_mem_descendantsAtDepth hR
  have hRscale : R.scale ≤ m := by omega
  have hopen : cubeCenter R ∈ openCubeSet R := by
    rw [← ball_cubeCenter_eq_openCubeSet]
    exact Metric.mem_ball_self (cubeRadius_pos R)
  have hcenter : cubeCenter R ∈ cubeSet (originCube d m) :=
    cubeSet_subset_of_mem_descendantsAtDepth hR (openCubeSet_subset_cubeSet R hopen)
  have h := akhcWeakD_blockMatLoewnerLE_of_mem hE hBdd hRscale hcenter
  refine akhcWNSq_loewnerLE_mono hE ?_ h
  have hexp : (m : ℝ) - (R.scale : ℝ) = (j : ℝ) := by
    rw [hscale]; push_cast; ring
  rw [hexp]
  have hM := akhcWeakD_eventMoreprotoPlus_nonneg m ρ E a.toFun
  refine mul_le_mul_of_nonneg_right ?_ hM
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hj) hρ)

/-! ## Elementary summation and weight facts -/

theorem akhcWNSq_rpow_neg_le_one {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    Real.rpow (3 : ℝ) (-s * t) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by nlinarith only [hs, ht])

theorem akhcWNSq_sum_le_card_mul {ι : Type*} (S : Finset ι) (f : ι → ℝ) {g : ℝ}
    (h : ∀ n ∈ S, f n ≤ g) : ∑ n ∈ S, f n ≤ (S.card : ℝ) * g := by
  have := Finset.sum_le_card_nsmul S f g h
  rwa [nsmul_eq_mul] at this

theorem akhcWNSq_sqrt_mul_self_mul {x y N : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hN : 0 ≤ N) :
    Real.sqrt (x * N) * Real.sqrt (N * y) = Real.sqrt (x * y) * N := by
  rw [← Real.sqrt_mul (mul_nonneg hx hN)]
  have : x * N * (N * y) = x * y * N ^ 2 := by ring
  rw [this, Real.sqrt_mul (mul_nonneg hx hy), Real.sqrt_sq hN]

theorem akhcWNSq_toNat_le {m k n : ℤ} (hn : n ∈ Finset.Icc (k + 1) m) :
    Int.toNat (m - n) ≤ Int.toNat (m - k) := by
  rw [Finset.mem_Icc] at hn
  omega

/-! ## The four gradient terms -/

/-- `J`'s `E`-constant `½(−p,q)·E(−p,q) + |p·q|`. -/
def akhcWNSq_Bj (E : BlockMat d) (p q : Vec d) : ℝ :=
  (1 / 2 : ℝ) * blockVecDot (-p, q) (blockMatVecMul E (-p, q)) + |vecDot p q|

theorem akhcWNSq_Bj_nonneg {E : BlockMat d} (hE : (toFullBlockMat E).PosDef) (p q : Vec d) :
    0 ≤ akhcWNSq_Bj E p q := by
  have h := akhcWNSq_quadratic_nonneg_of_posDef hE (-p, q)
  unfold akhcWNSq_Bj
  have := abs_nonneg (vecDot p q)
  positivity

/-- The squared-average constant of the gradient. -/
def akhcWNSq_Bg (E : BlockMat d) (p q p0 : Vec d) : ℝ :=
  2 * (akhcWNSq_lowerTrace E * blockVecDot (-p, q) (blockMatVecMul E (-p, q)) +
    vecNormSq (p + p0))

/-- The explicit constant of `akhcWNSq_gradientRHSAtScale_le`. -/
def akhcWNSq_gradConst (E : BlockMat d) (m k : ℤ) (s s' ρ C : ℝ) (p q p0 : Vec d) : ℝ :=
  ((Finset.Icc (k + 1) m).card : ℝ) * Real.sqrt (akhcWNSq_Bg E p q p0) +
    C * (((Finset.Icc (k + 1) m).card : ℝ) *
      Real.sqrt (akhcWeakC2_maximizerConst s' ρ * Ch02.matrixNorm E.lowerRight *
        akhcWNSq_Bj E p q)) +
    C * ((s - s')⁻¹ *
      Real.sqrt (akhcWeakC2_maximizerConst s' ρ * Ch02.matrixNorm E.lowerRight *
        akhcWNSq_Bj E p q)) +
    C * (s⁻¹ * ‖p0‖)

/-- **The gradient maximizer RHS is linear in `1 + W·M⁺`.** -/
theorem akhcWNSq_gradientRHSAtScale_le [NeZero d] {E : BlockMat d}
    (hE : (toFullBlockMat E).PosDef) {a : RegCoeffField d}
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (hsym : ∀ R : TriadicCube d, IsSymmetricBlockMat (coarseBlockMatrix (cubeSet R) a.toFun))
    (hpsd : ∀ (R : TriadicCube d) (Z : BlockVec d),
      0 ≤ blockVecDot Z (blockMatVecMul (coarseBlockMatrix (cubeSet R) a.toFun) Z))
    {m k : ℤ} {s s' ρ C : ℝ} (hs' : 0 < s') (hs's : s' < s) (hgap : ρ / 2 < s') (hρ : 0 ≤ ρ)
    (hC : 0 ≤ C)
    (hBdd :
      BddAbove
        {M : ℝ |
          ∃ Q : TriadicCube d,
            Q.scale ≤ m ∧
              cubeCenter Q ∈ cubeSet (originCube d m) ∧
              M =
                Real.rpow (3 : ℝ) (-ρ * ((m : ℝ) - (Q.scale : ℝ))) *
                  SuperdiffusionCLT.AKHC61.Tails.akhcTailEll_excess E
                    (coarseBlockMatrix (cubeSet Q) a.toFun)})
    (p q p0 : Vec d) :
    Ch05.Section53.WeakNormsMaximizer.gradientRHSAtScale C m k s s' p q p0 a ≤
      akhcWNSq_gradConst E m k s s' ρ C p q p0 *
        (1 + akhcWNSq_W ρ m k * akhcWeakC_eventMoreprotoPlus m ρ E a.toFun) := by
  set M := akhcWeakC_eventMoreprotoPlus m ρ E a.toFun with hMdef
  set W := akhcWNSq_W ρ m k with hWdef
  set N := 1 + W * M with hNdef
  have hM0 : 0 ≤ M := akhcWeakD_eventMoreprotoPlus_nonneg m ρ E a.toFun
  have hW1 : 1 ≤ W := akhcWNSq_one_le_W hρ m k
  have hWM : 0 ≤ W * M := mul_nonneg (by linarith only [hW1]) hM0
  have hN1 : 1 ≤ N := by linarith only [hWM]
  have hN0 : 0 ≤ N := by linarith only [hN1]
  have hs : 0 < s := lt_trans hs' hs's
  have hss : 0 ≤ s - s' := by linarith only [hs's]
  set S := Finset.Icc (k + 1) m with hSdef
  set Bj := akhcWNSq_Bj E p q with hBjdef
  set Bg := akhcWNSq_Bg E p q p0 with hBgdef
  set Kl := akhcWeakC2_maximizerConst s' ρ * Ch02.matrixNorm E.lowerRight with hKldef
  have hBj0 : 0 ≤ Bj := akhcWNSq_Bj_nonneg hE p q
  have hKl0 : 0 ≤ Kl :=
    mul_nonneg (by unfold akhcWeakC2_maximizerConst; positivity) (Book.Ch02.matrixNorm_nonneg _)
  -- λ⁻¹ ≤ Kl·N
  have hlam : (Ch04.lambdaSqCoeffField (originCube d m) s' (.finite 1) a)⁻¹ ≤ Kl * N := by
    have h := akhcWeakD_lambdaSqCoeffField_inv_le hE ha hs' hgap hBdd
    have h1 : 1 + M ≤ N := by nlinarith only [hW1, hM0]
    calc _ ≤ Kl * (1 + M) := h
      _ ≤ Kl * N := mul_le_mul_of_nonneg_left h1 hKl0
  have hsqlam : Real.sqrt ((Ch04.lambdaSqCoeffField (originCube d m) s' (.finite 1) a)⁻¹) ≤
      Real.sqrt (Kl * N) := Real.sqrt_le_sqrt hlam
  -- J on every descendant of depth ≤ m - k
  have hJdesc : ∀ j : ℕ, j ≤ Int.toNat (m - k) → ∀ R ∈ descendantsAtDepth (originCube d m) j,
      Ch04.restrictionResponseJObservableCubeSet R p q a ≤ N * Bj := by
    intro j hj R hR
    exact akhcWNSq_responseJ_le a ha R p q hWM
      (akhcWNSq_loewner_descendant hE hρ hBdd hj hR)
  have hJQ : Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q a ≤ N * Bj :=
    hJdesc 0 (Nat.zero_le _) (originCube d m) (by simp)
  have hsqJQ : Real.sqrt (Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q a) ≤
      Real.sqrt (N * Bj) := Real.sqrt_le_sqrt hJQ
  -- the average term
  have hAvg : Ch05.Section53.WeakNormsMaximizer.gradientAverageTermAtScale m k s p q p0 a ≤
      (S.card : ℝ) * Real.sqrt Bg * N := by
    unfold Ch05.Section53.WeakNormsMaximizer.gradientAverageTermAtScale
    rw [mul_assoc]
    refine akhcWNSq_sum_le_card_mul S _ fun n hn => ?_
    have hj := akhcWNSq_toNat_le hn
    have hinner : descendantsAverage (originCube d m) (Int.toNat (m - n))
        (fun R => vecNormSq
          (Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q a.toFun - p0)) ≤
        N ^ 2 * Bg := by
      have h := descendantsAverage_le_descendantsAverage (originCube d m) (Int.toNat (m - n))
        (F := fun R => vecNormSq
          (Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q a.toFun - p0))
        (G := fun _ => N ^ 2 * Bg) fun R hR =>
          akhcWNSq_gradientAverage_self_le a ha R p q p0 hWM (hsym R) (hpsd R)
            (akhcWNSq_loewner_descendant hE hρ hBdd (hj.trans le_rfl) hR)
      rwa [descendantsAverage_const] at h
    have hsq : Real.sqrt (descendantsAverage (originCube d m) (Int.toNat (m - n))
        (fun R => vecNormSq
          (Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q a.toFun - p0))) ≤
        Real.sqrt Bg * N := by
      calc _ ≤ Real.sqrt (N ^ 2 * Bg) := Real.sqrt_le_sqrt hinner
        _ = Real.sqrt Bg * N := by
          rw [Real.sqrt_mul (sq_nonneg N), Real.sqrt_sq hN0, mul_comm]
    have hw := akhcWNSq_rpow_neg_le_one hs.le (Nat.cast_nonneg (Int.toNat (m - n)))
    have hw0 : 0 ≤ Real.rpow (3 : ℝ) (-s * (Int.toNat (m - n) : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    have hB0 : 0 ≤ Real.sqrt Bg * N := mul_nonneg (Real.sqrt_nonneg _) hN0
    calc _ ≤ Real.rpow (3 : ℝ) (-s * (Int.toNat (m - n) : ℝ)) * (Real.sqrt Bg * N) :=
          mul_le_mul_of_nonneg_left hsq hw0
      _ ≤ 1 * (Real.sqrt Bg * N) := mul_le_mul_of_nonneg_right hw hB0
      _ = Real.sqrt Bg * N := one_mul _
  -- the mismatch term
  have hMis : Ch05.Section53.WeakNormsMaximizer.gradientMismatchTermAtScale m k s s' p q a ≤
      (S.card : ℝ) * Real.sqrt (Kl * Bj) * N := by
    unfold Ch05.Section53.WeakNormsMaximizer.gradientMismatchTermAtScale
    have hsum : ∑ n ∈ S, Real.rpow (3 : ℝ) (-(s - s') * (Int.toNat (m - n) : ℝ)) *
          Real.sqrt (Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale m n p q a) ≤
        (S.card : ℝ) * Real.sqrt (N * Bj) := by
      refine akhcWNSq_sum_le_card_mul S _ fun n hn => ?_
      have hj := akhcWNSq_toNat_le hn
      have hdef : Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale m n p q a ≤
          N * Bj := by
        unfold Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
        have h := descendantsAverage_le_descendantsAverage (originCube d m) (Int.toNat (m - n))
          (F := fun R => Ch04.restrictionResponseJObservableCubeSet R p q a)
          (G := fun _ => N * Bj) fun R hR => hJdesc _ hj R hR
        rw [descendantsAverage_const] at h
        have hQ0 := Ch04.restrictionResponseJObservableCubeSet_nonneg (originCube d m) p q a
        linarith only [h, hQ0]
      have hw := akhcWNSq_rpow_neg_le_one hss (Nat.cast_nonneg (Int.toNat (m - n)))
      have hw0 : 0 ≤ Real.rpow (3 : ℝ) (-(s - s') * (Int.toNat (m - n) : ℝ)) :=
        Real.rpow_nonneg (by norm_num) _
      calc _ ≤ Real.rpow (3 : ℝ) (-(s - s') * (Int.toNat (m - n) : ℝ)) * Real.sqrt (N * Bj) :=
            mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hdef) hw0
        _ ≤ 1 * Real.sqrt (N * Bj) := mul_le_mul_of_nonneg_right hw (Real.sqrt_nonneg _)
        _ = Real.sqrt (N * Bj) := one_mul _
    have hsum0 : 0 ≤ ∑ n ∈ S, Real.rpow (3 : ℝ) (-(s - s') * (Int.toNat (m - n) : ℝ)) *
          Real.sqrt (Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale m n p q a) :=
      Finset.sum_nonneg fun n _ =>
        mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.sqrt_nonneg _)
    calc _ ≤ Real.sqrt (Kl * N) * ((S.card : ℝ) * Real.sqrt (N * Bj)) :=
          mul_le_mul hsqlam hsum hsum0 (Real.sqrt_nonneg _)
      _ = (S.card : ℝ) * (Real.sqrt (Kl * N) * Real.sqrt (N * Bj)) := by ring
      _ = (S.card : ℝ) * Real.sqrt (Kl * Bj) * N := by
        rw [akhcWNSq_sqrt_mul_self_mul hKl0 hBj0 hN0]; ring
  -- the low-scale tail
  have hLow : Ch05.Section53.WeakNormsMaximizer.gradientLowScaleTailAtScale m k s s' p q a ≤
      (s - s')⁻¹ * Real.sqrt (Kl * Bj) * N := by
    unfold Ch05.Section53.WeakNormsMaximizer.gradientLowScaleTailAtScale
    have hw := akhcWNSq_rpow_neg_le_one hss (Nat.cast_nonneg (Int.toNat (m - k)))
    have hw0 : 0 ≤ Real.rpow (3 : ℝ) (-(s - s') * (Int.toNat (m - k) : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    have hinv : 0 ≤ (s - s')⁻¹ := inv_nonneg.mpr hss
    have hprod : Real.sqrt ((Ch04.lambdaSqCoeffField (originCube d m) s' (.finite 1) a)⁻¹) *
        Real.sqrt (Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q a) ≤
        Real.sqrt (Kl * Bj) * N := by
      rw [← akhcWNSq_sqrt_mul_self_mul hKl0 hBj0 hN0]
      exact mul_le_mul hsqlam hsqJQ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hprod0 : 0 ≤ Real.sqrt ((Ch04.lambdaSqCoeffField (originCube d m) s' (.finite 1) a)⁻¹) *
        Real.sqrt (Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q a) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    calc _ = (s - s')⁻¹ * Real.rpow (3 : ℝ) (-(s - s') * (Int.toNat (m - k) : ℝ)) *
          (Real.sqrt ((Ch04.lambdaSqCoeffField (originCube d m) s' (.finite 1) a)⁻¹) *
            Real.sqrt (Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q a)) := by
          ring
      _ ≤ (s - s')⁻¹ * 1 * (Real.sqrt (Kl * Bj) * N) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hw hinv) hprod hprod0 (by positivity)
      _ = (s - s')⁻¹ * Real.sqrt (Kl * Bj) * N := by ring
  -- the constant tail
  have hConst : Ch05.Section53.WeakNormsMaximizer.gradientConstantTailAtScale m k s p0 ≤
      s⁻¹ * ‖p0‖ * N := by
    unfold Ch05.Section53.WeakNormsMaximizer.gradientConstantTailAtScale
    have hw := akhcWNSq_rpow_neg_le_one hs.le (Nat.cast_nonneg (Int.toNat (m - k)))
    have hinv : 0 ≤ s⁻¹ := inv_nonneg.mpr hs.le
    have hp : 0 ≤ s⁻¹ * ‖p0‖ := mul_nonneg hinv (norm_nonneg _)
    calc _ = s⁻¹ * ‖p0‖ * Real.rpow (3 : ℝ) (-s * (Int.toNat (m - k) : ℝ)) := by ring
      _ ≤ s⁻¹ * ‖p0‖ * 1 := mul_le_mul_of_nonneg_left hw hp
      _ ≤ s⁻¹ * ‖p0‖ * N := mul_le_mul_of_nonneg_left hN1 hp
  -- assembly
  unfold Ch05.Section53.WeakNormsMaximizer.gradientRHSAtScale akhcWNSq_gradConst
  rw [← hSdef, ← hBjdef, ← hBgdef, ← hKldef]
  have e2 := mul_le_mul_of_nonneg_left hMis hC
  have e3 := mul_le_mul_of_nonneg_left hLow hC
  have e4 := mul_le_mul_of_nonneg_left hConst hC
  nlinarith only [hAvg, e2, e3, e4]

end

end SuperdiffusionCLT.AKHC61.WeakNorms
