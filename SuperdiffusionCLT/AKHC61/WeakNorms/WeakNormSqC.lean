/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.WeakNorms.WeakNormSqB

/-!
# Squared weak norms, part C: the flux maximizer right-hand side is linear in `1 + W·M⁺`

The flux twin of `WeakNormSqB.lean` (`akhcWNSq_gradientRHSAtScale_le`): the same argument with
the upper half of `bfA(R)(−p, q)`, the upper ellipticity quantity `Λ ≤ C·|E_{UL}|·(1 + M⁺)`
(`MaximizerBridgeD.lean`) in place of `λ⁻¹`, and `q0` in place of `p0`. The exponents are named
`s, s'` as in part B; the consumer instantiates them with `t, t'`. Main result:
`akhcWNSq_fluxRHSAtScale_le`.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.WeakNorms

noncomputable section

open Homogenization
open Homogenization.Book

variable {d : ℕ}

/-- The squared-average constant of the flux. -/
def akhcWNSq_Bf (E : BlockMat d) (p q q0 : Vec d) : ℝ :=
  2 * (akhcWNSq_upperTrace E * blockVecDot (-p, q) (blockMatVecMul E (-p, q)) +
    vecNormSq (q - q0))

/-- The explicit constant of `akhcWNSq_fluxRHSAtScale_le`. -/
def akhcWNSq_fluxConst (E : BlockMat d) (m k : ℤ) (s s' ρ C : ℝ) (p q q0 : Vec d) : ℝ :=
  ((Finset.Icc (k + 1) m).card : ℝ) * Real.sqrt (akhcWNSq_Bf E p q q0) +
    C * (((Finset.Icc (k + 1) m).card : ℝ) *
      Real.sqrt (akhcWeakC2_maximizerConst s' ρ * Ch02.matrixNorm E.upperLeft *
        akhcWNSq_Bj E p q)) +
    C * ((s - s')⁻¹ *
      Real.sqrt (akhcWeakC2_maximizerConst s' ρ * Ch02.matrixNorm E.upperLeft *
        akhcWNSq_Bj E p q)) +
    C * (s⁻¹ * ‖q0‖)

/-- **The flux maximizer RHS is linear in `1 + W·M⁺`.** -/
theorem akhcWNSq_fluxRHSAtScale_le [NeZero d] {E : BlockMat d}
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
    (p q q0 : Vec d) :
    Ch05.Section53.WeakNormsMaximizer.fluxRHSAtScale C m k s s' p q q0 a ≤
      akhcWNSq_fluxConst E m k s s' ρ C p q q0 *
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
  set Bg := akhcWNSq_Bf E p q q0 with hBgdef
  set Kl := akhcWeakC2_maximizerConst s' ρ * Ch02.matrixNorm E.upperLeft with hKldef
  have hBj0 : 0 ≤ Bj := akhcWNSq_Bj_nonneg hE p q
  have hKl0 : 0 ≤ Kl :=
    mul_nonneg (by unfold akhcWeakC2_maximizerConst; positivity) (Book.Ch02.matrixNorm_nonneg _)
  -- λ⁻¹ ≤ Kl·N
  have hLam : Ch04.LambdaSqCoeffField (originCube d m) s' (.finite 1) a ≤ Kl * N := by
    have h := akhcWeakD_LambdaSqCoeffField_le hE ha hs' hgap hBdd
    have h1 : 1 + M ≤ N := by nlinarith only [hW1, hM0]
    calc _ ≤ Kl * (1 + M) := h
      _ ≤ Kl * N := mul_le_mul_of_nonneg_left h1 hKl0
  have hsqLam : Real.sqrt (Ch04.LambdaSqCoeffField (originCube d m) s' (.finite 1) a) ≤
      Real.sqrt (Kl * N) := Real.sqrt_le_sqrt hLam
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
  have hAvg : Ch05.Section53.WeakNormsMaximizer.fluxAverageTermAtScale m k s p q q0 a ≤
      (S.card : ℝ) * Real.sqrt Bg * N := by
    unfold Ch05.Section53.WeakNormsMaximizer.fluxAverageTermAtScale
    rw [mul_assoc]
    refine akhcWNSq_sum_le_card_mul S _ fun n hn => ?_
    have hj := akhcWNSq_toNat_le hn
    have hinner : descendantsAverage (originCube d m) (Int.toNat (m - n))
        (fun R => vecNormSq
          (Ch04.canonicalScalarResponseFluxAverageCubeSet R R p q a.toFun - q0)) ≤
        N ^ 2 * Bg := by
      have h := descendantsAverage_le_descendantsAverage (originCube d m) (Int.toNat (m - n))
        (F := fun R => vecNormSq
          (Ch04.canonicalScalarResponseFluxAverageCubeSet R R p q a.toFun - q0))
        (G := fun _ => N ^ 2 * Bg) fun R hR =>
          akhcWNSq_fluxAverage_self_le a ha R p q q0 hWM (hsym R) (hpsd R)
            (akhcWNSq_loewner_descendant hE hρ hBdd (hj.trans le_rfl) hR)
      rwa [descendantsAverage_const] at h
    have hsq : Real.sqrt (descendantsAverage (originCube d m) (Int.toNat (m - n))
        (fun R => vecNormSq
          (Ch04.canonicalScalarResponseFluxAverageCubeSet R R p q a.toFun - q0))) ≤
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
  have hMis : Ch05.Section53.WeakNormsMaximizer.fluxMismatchTermAtScale m k s s' p q a ≤
      (S.card : ℝ) * Real.sqrt (Kl * Bj) * N := by
    unfold Ch05.Section53.WeakNormsMaximizer.fluxMismatchTermAtScale
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
          mul_le_mul hsqLam hsum hsum0 (Real.sqrt_nonneg _)
      _ = (S.card : ℝ) * (Real.sqrt (Kl * N) * Real.sqrt (N * Bj)) := by ring
      _ = (S.card : ℝ) * Real.sqrt (Kl * Bj) * N := by
        rw [akhcWNSq_sqrt_mul_self_mul hKl0 hBj0 hN0]; ring
  -- the low-scale tail
  have hLow : Ch05.Section53.WeakNormsMaximizer.fluxLowScaleTailAtScale m k s s' p q a ≤
      (s - s')⁻¹ * Real.sqrt (Kl * Bj) * N := by
    unfold Ch05.Section53.WeakNormsMaximizer.fluxLowScaleTailAtScale
    have hw := akhcWNSq_rpow_neg_le_one hss (Nat.cast_nonneg (Int.toNat (m - k)))
    have hw0 : 0 ≤ Real.rpow (3 : ℝ) (-(s - s') * (Int.toNat (m - k) : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    have hinv : 0 ≤ (s - s')⁻¹ := inv_nonneg.mpr hss
    have hprod : Real.sqrt (Ch04.LambdaSqCoeffField (originCube d m) s' (.finite 1) a) *
        Real.sqrt (Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q a) ≤
        Real.sqrt (Kl * Bj) * N := by
      rw [← akhcWNSq_sqrt_mul_self_mul hKl0 hBj0 hN0]
      exact mul_le_mul hsqLam hsqJQ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hprod0 : 0 ≤ Real.sqrt (Ch04.LambdaSqCoeffField (originCube d m) s' (.finite 1) a) *
        Real.sqrt (Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q a) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    calc _ = (s - s')⁻¹ * Real.rpow (3 : ℝ) (-(s - s') * (Int.toNat (m - k) : ℝ)) *
          (Real.sqrt (Ch04.LambdaSqCoeffField (originCube d m) s' (.finite 1) a) *
            Real.sqrt (Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q a)) := by
          ring
      _ ≤ (s - s')⁻¹ * 1 * (Real.sqrt (Kl * Bj) * N) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hw hinv) hprod hprod0 (by positivity)
      _ = (s - s')⁻¹ * Real.sqrt (Kl * Bj) * N := by ring
  -- the constant tail
  have hConst : Ch05.Section53.WeakNormsMaximizer.fluxConstantTailAtScale m k s q0 ≤
      s⁻¹ * ‖q0‖ * N := by
    unfold Ch05.Section53.WeakNormsMaximizer.fluxConstantTailAtScale
    have hw := akhcWNSq_rpow_neg_le_one hs.le (Nat.cast_nonneg (Int.toNat (m - k)))
    have hinv : 0 ≤ s⁻¹ := inv_nonneg.mpr hs.le
    have hp : 0 ≤ s⁻¹ * ‖q0‖ := mul_nonneg hinv (norm_nonneg _)
    calc _ = s⁻¹ * ‖q0‖ * Real.rpow (3 : ℝ) (-s * (Int.toNat (m - k) : ℝ)) := by ring
      _ ≤ s⁻¹ * ‖q0‖ * 1 := mul_le_mul_of_nonneg_left hw hp
      _ ≤ s⁻¹ * ‖q0‖ * N := mul_le_mul_of_nonneg_left hN1 hp
  -- assembly
  unfold Ch05.Section53.WeakNormsMaximizer.fluxRHSAtScale akhcWNSq_fluxConst
  rw [← hSdef, ← hBjdef, ← hBgdef, ← hKldef]
  have e2 := mul_le_mul_of_nonneg_left hMis hC
  have e3 := mul_le_mul_of_nonneg_left hLow hC
  have e4 := mul_le_mul_of_nonneg_left hConst hC
  nlinarith only [hAvg, e2, e3, e4]

end

end SuperdiffusionCLT.AKHC61.WeakNorms
