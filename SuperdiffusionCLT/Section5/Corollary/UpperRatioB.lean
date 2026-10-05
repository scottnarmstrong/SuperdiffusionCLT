/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Corollary.UpperRatio

/-!
# `cor.upper.ratio`: the left side and the pointwise gluing

The expectation of `P · bfA_m(cu_K) P` for `P = (p, 0)` is at least `shom_m |p|²`, and the pointwise
form of the basic split: `P · bfA_m(cu_K) P` is at most the subcube average of the principal term
plus any majorant of the cell errors.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization MeasureTheory Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff SuperdiffusionCLT.Section2.Annealed
open scoped ENNReal

variable {d : ℕ}

theorem upperRatio_lintegral_ge [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (m Kc : ℕ) (p : Vec d) :
    ENNReal.ofReal (sigmaBarSeq nu m P Kc * vecNormSq p) ≤
      ∫⁻ omega, ENNReal.ofReal (blockVecDot (p, (0 : Vec d))
        (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d (Kc : ℤ)))
          (coefficientCutoff nu omega m).toCoeffField) (p, (0 : Vec d)))) ∂P.toMeasure := by
  set c : ShellSeq d → ℝ := fun omega => blockVecDot (p, (0 : Vec d))
    (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d (Kc : ℤ)))
      (coefficientCutoff nu omega m).toCoeffField) (p, (0 : Vec d))) with hc
  have hint : ∀ i j, Integrable (fun omega : ShellSeq d => (coarseBlockMatrix
      (cubeSet (originCube d (Kc : ℤ))) (coefficientCutoff nu omega m).toFun).upperLeft i j)
      P.toMeasure := fun i j =>
    integrable_blockMatEntry_coarseBlockMatrix hnu m (originCube d (Kc : ℤ)) hPrefix hJ2 hJ3 hJ4
      (Sum.inl i) (Sum.inl j)
  have hform : c = fun omega => ∑ i, p i * ∑ j, (coarseBlockMatrix (cubeSet (originCube d (Kc : ℤ)))
      (coefficientCutoff nu omega m).toFun).upperLeft i j * p j := by
    funext omega
    rw [hc]
    simp only
    rw [blockQuadratic_eq]
    simp [vecDot, matVecMul]
    rfl
  have hci : Integrable c P.toMeasure := by
    rw [hform]
    exact integrable_finsetSum _ fun i _ => (integrable_finsetSum _ fun j _ =>
      (hint i j).mul_const (p j)).const_mul (p i)
  have hann := principal_Ahom_fv hnu m hPrefix hJ2 hJ4 Kc (originCube d (Kc : ℤ)) rfl
  have hI : ∫ omega, c omega ∂P.toMeasure = sigmaBarSeq nu m P Kc * vecNormSq p := by
    rw [hform]
    simp only
    rw [integral_finsetSum _ fun i _ => (integrable_finsetSum _ fun j _ =>
      (hint i j).mul_const (p j)).const_mul (p i)]
    have h2 : ∀ i, ∫ omega, p i * ∑ j, (coarseBlockMatrix (cubeSet (originCube d (Kc : ℤ)))
        (coefficientCutoff nu omega m).toFun).upperLeft i j * p j ∂P.toMeasure =
        p i * ∑ j, (annealedBlockMatrix nu m P (cubeSet (originCube d (Kc : ℤ)))).upperLeft i j * p j := by
      intro i
      rw [integral_const_mul, integral_finsetSum _ fun j _ => (hint i j).mul_const (p j)]
      simp only [integral_mul_const, annealedBlockMatrix_upperLeft_apply]
    simp only [h2, hann]
    simp [vecNormSq, vecDot, blockDiag, Matrix.one_apply]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  have h1 := loc_ofReal_integral_le_lintegral hci
  rw [hI] at h1
  exact h1


theorem upperRatio_ofReal_subcubeMean {Kc n : ℕ} (hn : n ≤ Kc) (g : TriadicCube d → ℝ)
    (hg : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ), 0 ≤ g Q) :
    ENNReal.ofReal (subcubeMean (originCube d (Kc : ℤ)) (n : ℤ) g) =
      subcubeAvg Kc n (fun Q => ENNReal.ofReal (g Q)) := by
  have hk : (n : ℤ) ≤ (originCube d (Kc : ℤ)).scale := by
    show (n : ℤ) ≤ (Kc : ℤ)
    exact_mod_cast hn
  have hne : (descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ)).card ≠ 0 :=
    (Finset.card_pos.2 (descendantsAtScale_nonempty _ hk)).ne'
  unfold subcubeMean subcubeAvg
  rw [ENNReal.ofReal_mul (inv_nonneg.2 (Nat.cast_nonneg _)), ENNReal.ofReal_sum_of_nonneg hg,
    ENNReal.ofReal_inv_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hne), ENNReal.ofReal_natCast]

theorem upperRatio_coarse_quad_nonneg [NeZero d] {lam Lam : ℝ} {a : CoeffField d} (Q : TriadicCube d)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a) (P : BlockVec d) :
    0 ≤ blockVecDot P (blockMatVecMul (coarseBlockMatrix (cubeSet Q) a) P) := by
  obtain ⟨S, hS, -⟩ := exists_isBlockOffsetMinimizer_cubeSet Q hEll (F := constBlockState P)
    (memVectorL2_const _) (memVectorL2_const _)
  rw [← blockPairingAverage_self_eq_coarseBlockMatrix Q hEll P hS]
  exact blockPairingAverage_self_nonneg hEll S

theorem upperRatio_pointwise [NeZero d] {lam Lam : ℝ} {a : CoeffField d} {Kc n : ℕ} (hn : n ≤ Kc)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet (originCube d (Kc : ℤ))) a)
    (hEllQ : ∀ Q, ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (cubeSet Q) a)
    {P : BlockVec d} {G : BlockState d}
    (hG : IsBlockMuAdmissible (cubeSet (originCube d (Kc : ℤ))) P G)
    {Pz : TriadicCube d → BlockVec d} {Fz : TriadicCube d → BlockState d}
    (hagree : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ), ∀ x ∈ cubeSet Q,
      G.potential x = (Pz Q).1 + (Fz Q).potential x ∧ G.flux x = (Pz Q).2 + (Fz Q).flux x)
    {S St : TriadicCube d → BlockState d}
    (hS : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
      IsBlockOffsetMinimizer a (cubeSet Q) (constBlockState (Pz Q)) (S Q))
    (hSt : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
      IsBlockOffsetMinimizer a (cubeSet Q) (Fz Q) (St Q))
    {B : TriadicCube d → ℝ≥0∞}
    (hB : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
      ENNReal.ofReal |volumeAverage (cubeSet Q) (fun x => blockVecDot
        ((2 : ℝ) • Pz Q + (St Q).eval x)
        (blockMatVecMul (blockCoeffField a x) ((St Q).eval x)))| ≤ B Q) :
    ENNReal.ofReal (blockVecDot P (blockMatVecMul
        (coarseBlockMatrix (cubeSet (originCube d (Kc : ℤ))) a) P)) ≤
      subcubeAvg Kc n (fun Q => ENNReal.ofReal (blockVecDot (Pz Q)
        (blockMatVecMul (coarseBlockMatrix (cubeSet Q) a) (Pz Q))) + B Q) := by
  obtain ⟨h1, h2⟩ := basic_split hn hEll hG hagree hS hSt
  set b : TriadicCube d → ℝ := fun Q => volumeAverage (cubeSet Q) (fun x => blockVecDot
        ((2 : ℝ) • Pz Q + (St Q).eval x)
        (blockMatVecMul (blockCoeffField a x) ((St Q).eval x))) with hb
  set q : TriadicCube d → ℝ := fun Q => blockVecDot (Pz Q)
        (blockMatVecMul (coarseBlockMatrix (cubeSet Q) a) (Pz Q)) with hq
  have hq0 : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ), 0 ≤ q Q := fun Q _ => by
    obtain ⟨l, L, hE⟩ := hEllQ Q
    exact upperRatio_coarse_quad_nonneg Q hE (Pz Q)
  have h3 : blockVecDot P (blockMatVecMul
      (coarseBlockMatrix (cubeSet (originCube d (Kc : ℤ))) a) P) ≤
      subcubeMean (originCube d (Kc : ℤ)) (n : ℤ) (fun Q => q Q + |b Q|) := by
    refine h1.trans ?_
    rw [h2]
    unfold subcubeMean
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun Q _ => ?_) (inv_nonneg.2 (Nat.cast_nonneg _))
    exact add_le_add le_rfl (le_abs_self _)
  refine (ENNReal.ofReal_le_ofReal h3).trans ?_
  rw [upperRatio_ofReal_subcubeMean hn _ (fun Q hQ => add_nonneg (hq0 Q hQ) (abs_nonneg _))]
  refine subcubeAvg_mono_on fun Q hQ => ?_
  rw [ENNReal.ofReal_add (hq0 Q hQ) (abs_nonneg _)]
  exact add_le_add le_rfl (hB Q hQ)

end SuperdiffusionCLT.Section5
