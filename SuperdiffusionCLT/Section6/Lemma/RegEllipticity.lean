/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Book.Ch03.Theorems.PublicInternalBridges.CoeffField
public import Homogenization.Book.Ch02.Theorems.HomogenizationError.EllipticityControl
public import Homogenization.Deterministic.MultiscaleQuantities

/-!
# Ellipticity from the homogenization error: raw and public ellipticity quantities

* `l5_coarseBlockMatrix_congr_ae`, `l5_LambdaSq_congr_ae`, `l5_lambdaSq_congr_ae`: the raw
  coarse-grained ellipticities of a cube depend on the field only almost everywhere on the cube.
* `l5_LambdaSq_one_le_two_half`, `l5_lambdaSq_one_inv_le_two_half`: `Λ_{s,1} ≤ Λ_{s/2,2}` and
  `λ_{s,1}⁻¹ ≤ λ_{s/2,2}⁻¹` for the public carriers (`e.ellipticities.qone.by.qtwo`).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6

open Homogenization

noncomputable section

section RawCongruence

variable {d : ℕ}

theorem l5_muValueSet_congr_ae {U : Set (Vec d)} {a b : CoeffField d}
    (h : a =ᵐ[volumeMeasureOn U] b) (P : BlockVec d) :
    muValueSet U P a = muValueSet U P b := by
  have key : ∀ {a b : CoeffField d}, a =ᵐ[volumeMeasureOn U] b →
      muValueSet U P a ⊆ muValueSet U P b := by
    intro a b h m hm
    obtain ⟨X, hX, rfl⟩ := hm
    refine ⟨X, hX, ?_⟩
    unfold volumeAverage
    congr 1
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [h] with x hx
    simp only [blockEnergyDensity, blockCoeffField, hx]
  exact Set.Subset.antisymm (key h) (key h.symm)

theorem l5_coarseBlockMatrix_congr_ae {U : Set (Vec d)} {a b : CoeffField d}
    (h : a =ᵐ[volumeMeasureOn U] b) :
    coarseBlockMatrix U a = coarseBlockMatrix U b :=
  coarseBlockMatrix_eq_of_mu_eq fun P => by
    unfold Mu
    rw [l5_muValueSet_congr_ae h P]

theorem l5_maxDescBBlock_congr_ae [NeZero d] (Q : TriadicCube d) {a b : CoeffField d}
    (h : a =ᵐ[volumeMeasureOn (cubeSet Q)] b) (n : ℕ) :
    maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a =
      maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) b := by
  have hk : Q.scale - (n : ℤ) ≤ Q.scale := sub_le_self _ (by exact_mod_cast Nat.zero_le n)
  unfold maxDescendantBBlockNormAtScale finsetSsup
  refine congrArg sSup (Set.image_congr fun R hR => ?_)
  have hsub : cubeSet R ⊆ cubeSet Q := cubeSet_subset_of_mem_descendantsAtScale hk hR
  have h2 : volumeMeasureOn (cubeSet R) ≤ volumeMeasureOn (cubeSet Q) := by
    unfold volumeMeasureOn
    exact MeasureTheory.Measure.restrict_mono hsub le_rfl
  unfold coarseBBlockNorm
  rw [l5_coarseBlockMatrix_congr_ae (MeasureTheory.ae_mono h2 h)]

theorem l5_maxDescSigmaStarInv_congr_ae [NeZero d] (Q : TriadicCube d) {a b : CoeffField d}
    (h : a =ᵐ[volumeMeasureOn (cubeSet Q)] b) (n : ℕ) :
    maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a =
      maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) b := by
  have hk : Q.scale - (n : ℤ) ≤ Q.scale := sub_le_self _ (by exact_mod_cast Nat.zero_le n)
  unfold maxDescendantSigmaStarInvNormAtScale finsetSsup
  refine congrArg sSup (Set.image_congr fun R hR => ?_)
  have hsub : cubeSet R ⊆ cubeSet Q := cubeSet_subset_of_mem_descendantsAtScale hk hR
  have h2 : volumeMeasureOn (cubeSet R) ≤ volumeMeasureOn (cubeSet Q) := by
    unfold volumeMeasureOn
    exact MeasureTheory.Measure.restrict_mono hsub le_rfl
  unfold coarseSigmaStarInvBlockNorm
  rw [l5_coarseBlockMatrix_congr_ae (MeasureTheory.ae_mono h2 h)]

theorem l5_LambdaSq_congr_ae [NeZero d] (Q : TriadicCube d) (s : ℝ) (q : MultiscaleExponent)
    {a b : CoeffField d} (h : a =ᵐ[volumeMeasureOn (cubeSet Q)] b) :
    LambdaSq Q s q a = LambdaSq Q s q b := by
  cases q with
  | finite q =>
    simp only [LambdaSq, LambdaSqFinite, l5_maxDescBBlock_congr_ae Q h]
  | infinity =>
    simp only [LambdaSq, LambdaSqInfinity, l5_maxDescBBlock_congr_ae Q h]

theorem l5_lambdaSq_congr_ae [NeZero d] (Q : TriadicCube d) (s : ℝ) (q : MultiscaleExponent)
    {a b : CoeffField d} (h : a =ᵐ[volumeMeasureOn (cubeSet Q)] b) :
    lambdaSq Q s q a = lambdaSq Q s q b := by
  cases q with
  | finite q =>
    simp only [lambdaSq, lambdaSqFinite, l5_maxDescSigmaStarInv_congr_ae Q h]
  | infinity =>
    simp only [lambdaSq, lambdaSqInfinity, l5_maxDescSigmaStarInv_congr_ae Q h]

end RawCongruence

/-- Weighted Cauchy--Schwarz for a probability weight. -/
theorem l5_tsum_sqrt_sq_le {w f : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) (hf : ∀ n, 0 ≤ f n)
    (hw1 : ∑' n, w n = 1) (hsw : Summable w) (hswf : Summable fun n => w n * f n) :
    (∑' n, w n * Real.sqrt (f n)) ^ 2 ≤ ∑' n, w n * f n := by
  let a : ℕ → ℝ := fun n => Real.sqrt (w n)
  let b : ℕ → ℝ := fun n => Real.sqrt (w n * f n)
  have ha_nonneg : ∀ n, 0 ≤ a n := fun n => Real.sqrt_nonneg _
  have hb_nonneg : ∀ n, 0 ≤ b n := fun n => Real.sqrt_nonneg _
  have ha_sq : ∀ n, a n ^ (2 : ℝ) = w n := fun n => by
    dsimp [a]; rw [Real.rpow_two, Real.sq_sqrt (hw n)]
  have hb_sq : ∀ n, b n ^ (2 : ℝ) = w n * f n := fun n => by
    dsimp [b]; rw [Real.rpow_two, Real.sq_sqrt (mul_nonneg (hw n) (hf n))]
  have hab : ∀ n, a n * b n = w n * Real.sqrt (f n) := fun n => by
    dsimp [a, b]
    rw [Real.sqrt_mul (hw n)]
    calc Real.sqrt (w n) * (Real.sqrt (w n) * Real.sqrt (f n))
        = (Real.sqrt (w n)) ^ 2 * Real.sqrt (f n) := by ring
      _ = w n * Real.sqrt (f n) := by rw [Real.sq_sqrt (hw n)]
  have hasum : Summable fun n => a n ^ (2 : ℝ) := by
    convert hsw using 1; ext n; exact ha_sq n
  have hbsum : Summable fun n => b n ^ (2 : ℝ) := by
    convert hswf using 1; ext n; exact hb_sq n
  have hholder : Real.HolderConjugate (2 : ℝ) (2 : ℝ) := ⟨by norm_num, by norm_num, by norm_num⟩
  have hcs := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg hholder ha_nonneg hb_nonneg hasum hbsum
  have hfs : ∑' n, a n ^ (2 : ℝ) = 1 := by
    rw [← hw1]; exact tsum_congr ha_sq
  have hbs : ∑' n, b n ^ (2 : ℝ) = ∑' n, w n * f n := tsum_congr hb_sq
  rw [hfs, hbs, Real.one_rpow, one_mul] at hcs
  have hnn : 0 ≤ ∑' n, w n * f n := tsum_nonneg fun n => mul_nonneg (hw n) (hf n)
  have h2 : (∑' n, w n * Real.sqrt (f n)) = ∑' n, a n * b n := tsum_congr fun n => (hab n).symm
  rw [h2]
  have hx : 0 ≤ ∑' n, a n * b n := tsum_nonneg fun n => mul_nonneg (ha_nonneg n) (hb_nonneg n)
  calc (∑' n, a n * b n) ^ 2 ≤ ((∑' n, w n * f n) ^ (1 / (2 : ℝ))) ^ 2 := by gcongr
    _ = ∑' n, w n * f n := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hnn]; norm_num

section QOneQTwo

variable {d : ℕ} [NeZero d]

private theorem l5_weights {s : ℝ} (hs : 0 < s) :
    (∀ n, 0 ≤ Book.Ch02.geometricWeight s 1 n) ∧
      ∑' n, Book.Ch02.geometricWeight s 1 n = 1 ∧
      Summable (fun n => Book.Ch02.geometricWeight s 1 n) ∧
      ∀ n, Book.Ch02.geometricWeight s 1 n = Book.Ch02.geometricWeight (s / 2) 2 n := by
  have hs1 : 0 < s * (1 : ℝ) := by rw [mul_one]; exact hs
  refine ⟨fun n => ?_, ?_, ?_, fun n => ?_⟩
  · simpa [Book.Ch02.geometricWeight_eq_old] using
      Homogenization.geometricWeight_nonneg (s := s) (q := (1 : ℝ)) n hs1.le
  · simpa [Book.Ch02.geometricWeight_eq_old] using
      Homogenization.tsum_geometricWeight_eq_one (s := s) (q := (1 : ℝ)) hs1
  · simpa [Book.Ch02.geometricWeight_eq_old] using
      Homogenization.summable_geometricWeight (s := s) (q := (1 : ℝ)) hs1
  · unfold Book.Ch02.geometricWeight Book.Ch02.geometricDiscount
    congr 1 <;> ring_nf

/-- `Λ_{s,1} ≤ Λ_{s/2,2}` for the public coarse-grained upper ellipticity
(`e.ellipticities.qone.by.qtwo`). -/
theorem l5_LambdaSq_one_le_two_half (Q : TriadicCube d) (a : Book.Ch02.TriadicCoeffFamily d)
    {s : ℝ} (hs : 0 < s) :
    Book.Ch02.LambdaSq Q s (.finite 1) a ≤ Book.Ch02.LambdaSq Q (s / 2) (.finite 2) a := by
  obtain ⟨hw0, hw1, hsw, hweq⟩ := l5_weights hs
  have h1 := Book.Ch02.LambdaSqFinite_rpow_q_div_two_eq_tsum Q s 1 a one_pos
    (by rw [mul_one]; exact hs.le)
  have h2 := Book.Ch02.LambdaSqFinite_rpow_q_div_two_eq_tsum Q (s / 2) 2 a two_pos
    (by positivity)
  have hnn := Book.Ch02.LambdaSq_nonneg Q a hs (q := .finite 1) (by simp)
  have hB : ∀ n : ℕ, 0 ≤ Book.Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a :=
    fun n => Book.Ch02.maxDescendantBMatrixNormAtScale_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a
  have hsum := Book.Ch02.summable_B_series_pointwiseCoeffField Q a (s := s / 2) (q := 2)
    (by positivity) two_pos
  have e2 : Book.Ch02.LambdaSq Q (s / 2) (.finite 2) a =
      ∑' n : ℕ, Book.Ch02.geometricWeight s 1 n *
        Book.Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a := by
    have := h2
    rw [show (2 / 2 : ℝ) = 1 by norm_num] at this
    simp only [Real.rpow_eq_pow, Real.rpow_one] at this
    rw [this]
    exact tsum_congr fun n => by rw [hweq n]
  have e1 : Real.sqrt (Book.Ch02.LambdaSq Q s (.finite 1) a) =
      ∑' n : ℕ, Book.Ch02.geometricWeight s 1 n *
        Real.sqrt (Book.Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a) := by
    rw [Real.sqrt_eq_rpow]
    simpa [Real.sqrt_eq_rpow] using h1
  have key := l5_tsum_sqrt_sq_le (w := fun n => Book.Ch02.geometricWeight s 1 n)
    (f := fun n => Book.Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
    hw0 hB hw1 hsw (by
      simpa [Real.rpow_one, hweq, div_self (two_ne_zero' ℝ)] using hsum)
  calc Book.Ch02.LambdaSq Q s (.finite 1) a
      = (Real.sqrt (Book.Ch02.LambdaSq Q s (.finite 1) a)) ^ 2 := (Real.sq_sqrt hnn).symm
    _ ≤ _ := by rw [e1]; exact key
    _ = _ := e2.symm

/-- `λ_{s,1}⁻¹ ≤ λ_{s/2,2}⁻¹` for the public lower ellipticity. -/
theorem l5_lambdaSq_one_inv_le_two_half (Q : TriadicCube d) (a : Book.Ch02.TriadicCoeffFamily d)
    {s : ℝ} (hs : 0 < s) :
    (Book.Ch02.lambdaSq Q s (.finite 1) a)⁻¹ ≤
      (Book.Ch02.lambdaSq Q (s / 2) (.finite 2) a)⁻¹ := by
  obtain ⟨hw0, hw1, hsw, hweq⟩ := l5_weights hs
  have h1 := Book.Ch02.lambdaSqFinite_rpow_neg_q_div_two_eq_tsum Q s 1 a one_pos
    (by rw [mul_one]; exact hs.le)
  have h2 := Book.Ch02.lambdaSqFinite_rpow_neg_q_div_two_eq_tsum Q (s / 2) 2 a two_pos
    (by positivity)
  have hpos := Book.Ch02.lambdaSq_pos Q a hs (q := .finite 1) (by simp)
  have hS : ∀ n : ℕ,
      0 ≤ Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a :=
    fun n => Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a
  have hsum := Book.Ch02.summable_sigmaStarInv_series_pointwiseCoeffField Q a (s := s / 2)
    (q := 2) (by positivity) two_pos
  have e2 : (Book.Ch02.lambdaSq Q (s / 2) (.finite 2) a)⁻¹ =
      ∑' n : ℕ, Book.Ch02.geometricWeight s 1 n *
        Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a := by
    have := h2
    rw [show (-2 / 2 : ℝ) = -1 by norm_num, show (2 / 2 : ℝ) = 1 by norm_num] at this
    simp only [Real.rpow_eq_pow, Real.rpow_neg_one, Real.rpow_one] at this
    rw [this]
    exact tsum_congr fun n => by rw [hweq n]
  have e1 : (Book.Ch02.lambdaSq Q s (.finite 1) a)⁻¹ =
      (∑' n : ℕ, Book.Ch02.geometricWeight s 1 n *
        Real.sqrt (Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
          (Q.scale - (n : ℤ)) a)) ^ 2 := by
    have h1' : Real.rpow (Book.Ch02.lambdaSq Q s (.finite 1) a) (-1 / 2) =
        ∑' n : ℕ, Book.Ch02.geometricWeight s 1 n *
          Real.sqrt (Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
            (Q.scale - (n : ℤ)) a) := by
      simpa [Real.sqrt_eq_rpow] using h1
    rw [← h1', Real.rpow_eq_pow, ← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    norm_num [Real.rpow_neg_one]
  have key := l5_tsum_sqrt_sq_le (w := fun n => Book.Ch02.geometricWeight s 1 n)
    (f := fun n => Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
    hw0 hS hw1 hsw (by
      simpa [Real.rpow_one, hweq, div_self (two_ne_zero' ℝ)] using hsum)
  rw [e1, e2]
  exact key

end QOneQTwo

end

end SuperdiffusionCLT.Section6
