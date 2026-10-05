/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.CoarseGraining.SkewShiftCutoff
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementLinftyLargeCube
public import Homogenization.Internal.Ch02.Representatives
public import Homogenization.PDE.DirichletRHS

/-!
# Comparing solutions of two infrared cutoffs on a bounded domain

This module proves the deterministic core of the manuscript's cutoff
approximation lemma (`l.cutoff.approximation` of the paper) at the level of two
*finite* cutoffs. The manuscript compares the limiting centered field `a^U` with the
level-`L` cutoff `a_L`; here `a` and `b` are two coefficient fields on the same
bounded domain, the solved field `b` has symmetric part `nu Id` almost
everywhere (`a` is unconstrained beyond admissibility), and `u_b` is the
solution of the `b`-Dirichlet problem with boundary data `u`.

The energy-testing argument in the proof of `l.cutoff.approximation` is reproduced
exactly. Writing
`w := u_b - u` for the zero-trace correction, testing the `a`-equation for `u`
and the `b`-equation for `u_b` with `w` and subtracting gives

`∫_U (b ∇w) · ∇w = ∫_U ((a - b) ∇u) · ∇w`,

whose left side is `nu ∫_U |∇w|²` because the symmetric part of `b` is
`nu Id`. The printed proof then applies Cauchy-Schwarz; the proof below uses
instead the square-root-free bound `2 z · v ≤ nu⁻¹ |z|² + nu |v|²`, which turns
the identity into `nu² ∫|∇w|² ≤ M² ∫|∇u|²` and gives the printed conclusion
after one square root. That route needs no `L²` Cauchy-Schwarz inequality and
no case split on `M`.

## Carrier and boundary data

The domain is CoarseGraining's `Homogenization.Book.Ch02.Domain d`, a nonempty
bounded open convex subset of `Vec d`; the manuscript's bounded Lipschitz
domain is narrowed to this class, which contains every triadic cube. The
coefficient fields are `Homogenization.Book.Ch02.CoeffOn U`, and the harmonic
class is `Homogenization.IsAHarmonicGradient`, that is, `∇u` is a potential
field on `U` and `a ∇u` is solenoidal on `U`.

The membership `u_b ∈ u + H¹₀(U)` is expressed by an explicit
`w : H10Function U` together with `ub = u + w.toH1Function`, using the additive
structure of `Homogenization.H1Function`. The `L∞(U)` norm of the manuscript is
an essential supremum, so the size hypothesis is stated as
`∀ᵐ x ∂(volumeMeasureOn U), matrixOperatorNorm (a x - b x) ≤ M` with the
CoarseGraining library's exact Euclidean matrix operator norm; the entry bounds
inherited from `coefficientCutoffCoeffOn` remain in the everywhere form.

## Main results

* `isSolenoidalOn_add_iff_isZeroTraceDirichletRhsWeakSolution`: the `b`-Dirichlet
  problem with boundary data `u` is the zero-trace right-hand-side problem for
  the forcing `-b ∇u`.
* `exists_isAHarmonicGradient_add_zeroTraceGrad`: solvability of the
  `b`-Dirichlet problem with boundary data `u`, for a general (non-symmetric)
  `CoeffOn U` on a bounded open convex domain.
* `dirichlet_comparison_of_skew_perturbation`: the estimate
  `nu ‖∇u - ∇u_b‖_{L²(U)} ≤ M ‖∇u‖_{L²(U)}`, the final display in the proof of
  `l.cutoff.approximation`.
* `coefficientCutoff_toCoeffField_sub`: the difference of two cutoff coefficient fields is
  the finite shell increment `k_{L₂} - k_{L₁}`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open Homogenization
open Homogenization.Book.Ch02
open MeasureTheory
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.CoarseGraining
open SuperdiffusionCLT.Section2.Estimates.Stream

noncomputable section

variable {d : ℕ}

/-! ## Ambient algebra

Three elementary identities and one inequality. The inequality is the
square-root-free Young bound that replaces the printed Cauchy-Schwarz step. -/

private theorem vecNormSq_neg (x : Vec d) : vecNormSq (-x) = vecNormSq x := by
  simp only [vecNormSq, vecDot, Pi.neg_apply, neg_mul_neg]

private theorem matVecMul_sub_left (A B : Mat d) (x : Vec d) :
    matVecMul (A - B) x = matVecMul A x - matVecMul B x := by
  change (A - B).mulVec x = A.mulVec x - B.mulVec x
  exact Matrix.sub_mulVec A B x

private theorem vecDot_sub_left (x y z : Vec d) :
    vecDot (x - y) z = vecDot x z - vecDot y z := by
  simp [vecDot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- `ξ · a ξ = nu |ξ|²` for a coefficient matrix whose symmetric part is
`nu Id`, the identity used in the proof of `l.cutoff.approximation` for `a^U = nu Id + k^U`. -/
private theorem vecDot_matVecMul_self_of_symmPart {A : Mat d} {nu : ℝ}
    (h : symmPart A = nu • (1 : Mat d)) (v : Vec d) :
    vecDot (matVecMul A v) v = nu * vecNormSq v := by
  have hone : matVecMul (1 : Mat d) v = v := by
    funext i
    simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]
  calc vecDot (matVecMul A v) v = vecDot v (matVecMul A v) := vecDot_comm _ _
    _ = vecDot v (matVecMul (symmPart A) v) := (vecDot_matVecMul_symmPart A v).symm
    _ = nu * vecNormSq v := by
        rw [h, smul_matVecMul, hone, vecDot_smul_right]
        rfl

/-- The square-root-free form of Young's inequality at the molecular
diffusivity: `2 z · v ≤ nu⁻¹ |z|² + nu |v|²`, obtained by expanding
`0 ≤ |z - nu v|²`. -/
private theorem two_mul_vecDot_le {nu : ℝ} (hnu : 0 < nu) (z v : Vec d) :
    2 * vecDot z v ≤ nu⁻¹ * vecNormSq z + nu * vecNormSq v := by
  have hexp : vecNormSq (z + (-(nu • v))) =
      vecNormSq z - 2 * nu * vecDot z v + nu ^ 2 * vecNormSq v := by
    simp only [vecNormSq, vecDot_add_left, vecDot_add_right, vecDot_neg_left,
      vecDot_neg_right, vecDot_smul_left, vecDot_smul_right]
    rw [vecDot_comm v z]
    ring
  have hkey : 2 * nu * vecDot z v ≤ vecNormSq z + nu ^ 2 * vecNormSq v := by
    have h0 := vecNormSq_nonneg (z + (-(nu • v)))
    rw [hexp] at h0
    linarith only [h0]
  have hinv : (0 : ℝ) ≤ nu⁻¹ := le_of_lt (inv_pos.mpr hnu)
  have hmul := mul_le_mul_of_nonneg_left hkey hinv
  have hl : nu⁻¹ * (2 * nu * vecDot z v) = 2 * vecDot z v := by field_simp
  have hr : nu⁻¹ * (vecNormSq z + nu ^ 2 * vecNormSq v) =
      nu⁻¹ * vecNormSq z + nu * vecNormSq v := by field_simp
  rw [hl, hr] at hmul
  exact hmul

/-! ## Coefficient objects and `L²` bookkeeping -/

private theorem isAEEllipticFieldOn_coeffOn {U : Domain d} (a : CoeffOn U) :
    IsAEEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField :=
  ⟨U.measurableSet, a.aeStronglyMeasurable, a.aeElliptic⟩

/-- The flux of a square-integrable field against a Chapter 2 coefficient
object is square integrable. -/
theorem memVectorL2_matVecMul_coeffOn {U : Domain d} (a : CoeffOn U)
    {f : Vec d → Vec d} (hf : MemVectorL2 (U : Set (Vec d)) f) :
    MemVectorL2 (U : Set (Vec d)) fun x => matVecMul (a.toCoeffField x) (f x) :=
  (isAEEllipticFieldOn_coeffOn a).memVectorL2_matVecMul hf

/-- A nonnegative essential-supremum bound over a nonempty bounded open convex
domain forces the bounding constant to be nonnegative. -/
private theorem nonneg_of_ae_matrixOperatorNorm_le {U : Domain d} {M : ℝ}
    {K : Vec d → Mat d}
    (hM : ∀ᵐ x ∂(volumeMeasureOn (U : Set (Vec d))), matrixOperatorNorm (K x) ≤ M) :
    0 ≤ M := by
  have hpos : 0 < MeasureTheory.volume (U : Set (Vec d)) :=
    IsOpen.measure_pos MeasureTheory.volume U.isOpen U.nonempty
  have hne : volumeMeasureOn (U : Set (Vec d)) ≠ 0 := by
    intro hzero
    have hUzero : MeasureTheory.volume (U : Set (Vec d)) = 0 := by
      have := congrArg (fun mu : MeasureTheory.Measure (Vec d) =>
        mu (U : Set (Vec d))) hzero
      simpa [volumeMeasureOn, MeasureTheory.Measure.restrict_apply_self] using this
    exact absurd hUzero hpos.ne'
  have : (MeasureTheory.ae (volumeMeasureOn (U : Set (Vec d)))).NeBot :=
    MeasureTheory.ae_neBot.2 hne
  obtain ⟨x, hx⟩ := hM.exists
  exact le_trans (matrixOperatorNorm_nonneg (K x)) hx

/-! ## The `b`-Dirichlet problem with boundary data `u`

The manuscript's `u_L ∈ u + H^1_0(U)` solving the `a_L`-equation in `U` is, after subtracting `u`,
the zero-trace problem
`-∇·(b ∇w) = ∇·(b ∇u)` for the correction `w`. That is CoarseGraining's
`IsZeroTraceDirichletRhsWeakSolution` with forcing `-b ∇u`, which is solvable
for a general, not necessarily symmetric, elliptic coefficient field on a
bounded open convex domain. -/

/-- `u + w` is `c`-harmonic on `U` exactly when the zero-trace correction `w`
solves the right-hand-side Dirichlet problem with forcing `-c ∇u`. -/
theorem isSolenoidalOn_add_iff_isZeroTraceDirichletRhsWeakSolution
    {U : Set (Vec d)} {c : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U c) (u : H1Function U) (w : H10Function U) :
    IsSolenoidalOn U
        (fun x => matVecMul (c x) (u.grad x + w.toH1Function.grad x)) ↔
      IsZeroTraceDirichletRhsWeakSolution c U w
        (fun x => -matVecMul (c x) (u.grad x)) := by
  have hcu : MemVectorL2 U fun x => matVecMul (c x) (u.grad x) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.grad_memVectorL2
  have hcw : MemVectorL2 U fun x => matVecMul (c x) (w.toH1Function.grad x) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll
      w.toH1Function.grad_memVectorL2
  have hkey : ∀ φ : H10Function U,
      (∫ x in U, vecDot (matVecMul (c x) (u.grad x + w.toH1Function.grad x))
          (φ.toH1Function.grad x) ∂MeasureTheory.volume) =
        (∫ x in U, vecDot (matVecMul (c x) (u.grad x))
          (φ.toH1Function.grad x) ∂MeasureTheory.volume) +
        (∫ x in U, vecDot (matVecMul (c x) (w.toH1Function.grad x))
          (φ.toH1Function.grad x) ∂MeasureTheory.volume) := by
    intro φ
    have hI1 : MeasureTheory.IntegrableOn
        (fun x => vecDot (matVecMul (c x) (u.grad x)) (φ.toH1Function.grad x)) U :=
      integrableOn_vecDot_of_memVectorL2 hcu φ.toH1Function.grad_memVectorL2
    have hI2 : MeasureTheory.IntegrableOn
        (fun x => vecDot (matVecMul (c x) (w.toH1Function.grad x))
          (φ.toH1Function.grad x)) U :=
      integrableOn_vecDot_of_memVectorL2 hcw φ.toH1Function.grad_memVectorL2
    rw [← MeasureTheory.integral_add hI1 hI2]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [matVecMul_add, vecDot_add_left]
  have hneg : ∀ φ : H10Function U,
      (∫ x in U, vecDot (-matVecMul (c x) (u.grad x)) (φ.toH1Function.grad x)
        ∂MeasureTheory.volume) =
        -∫ x in U, vecDot (matVecMul (c x) (u.grad x)) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume := by
    intro φ
    rw [← MeasureTheory.integral_neg]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [vecDot_neg_left]
  constructor
  · intro h φ
    have hφ := h φ
    rw [hkey φ] at hφ
    rw [hneg φ]
    linarith only [hφ]
  · intro h φ
    have hφ := h φ
    rw [hneg φ] at hφ
    rw [hkey φ, hφ]
    ring

/-- Solvability of the `b`-Dirichlet problem with boundary data `u`: for every
`u ∈ H¹(U)` there is a zero-trace `w` with `u + w ∈ A(U; b)`. The coefficient
field is a general Chapter 2 coefficient object; no symmetry is assumed. -/
theorem exists_isAHarmonicGradient_add_zeroTraceGrad [NeZero d] (U : Domain d)
    (b : CoeffOn U) (u : H1Function (U : Set (Vec d))) :
    ∃ w : H10Function (U : Set (Vec d)),
      IsAHarmonicGradient b.toCoeffField (U : Set (Vec d))
        (fun x => u.grad x + w.toH1Function.grad x) := by
  classical
  have hEll := Internal.Ch02.BookCh02.pointwiseCoeffOn_isEllipticFieldOn U b
  have hg : MemVectorL2 (U : Set (Vec d))
      fun x => -matVecMul
        ((Internal.Ch02.BookCh02.pointwiseCoeffOn U b).toCoeffField x) (u.grad x) :=
    (memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.grad_memVectorL2).neg
  have hRealize :
      PotentialSolenoidalL2Data.HasPotentialZeroTraceClosureRealization
        (U : Set (Vec d)) :=
    PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_isOpenBoundedConvexDomain
      U.isDomain
  obtain ⟨w, hw⟩ :=
    exists_isZeroTraceDirichletRhsWeakSolution_of_potentialZeroTraceClosureRealization
      hg hRealize U.nonempty hEll
  refine ⟨w, ?_⟩
  refine IsAHarmonicGradient.of_ae_eq_coeff
    (Internal.Ch02.BookCh02.pointwiseCoeffOn_ae_eq U b) ⟨⟨u + w.toH1Function, rfl⟩, ?_⟩
  exact (isSolenoidalOn_add_iff_isZeroTraceDirichletRhsWeakSolution hEll u w).2 hw

/-! ## The energy comparison

The final display of the proof of `l.cutoff.approximation`, for two coefficient fields on the same
domain. Only the solved field `b` is required to have symmetric part `nu Id`;
the reference field `a` enters through its own equation and through the size of
`a - b`, which for `a = nu Id + k` and `b = nu Id + k'` is exactly `k - k'`. -/

/-- The cutoff comparison estimate:

`nu ‖∇u - ∇u_b‖_{L²(U)} ≤ M ‖∇u‖_{L²(U)}`,

for `u` `a`-harmonic on `U`, `u_b ∈ u + H¹₀(U)` `b`-harmonic on `U`, `b` with
symmetric part `nu Id`, and `M` an essential-supremum bound for the operator
norm of `a - b` on `U`. This is the final display in the proof of `l.cutoff.approximation`, and its
consequence `e.cutoff.approximation`, with the two finite cutoffs in place of the
limiting field. -/
theorem dirichlet_comparison_of_skew_perturbation {U : Domain d} {a b : CoeffOn U}
    {nu M : ℝ} (hnu : 0 < nu)
    (hbsymm : ∀ᵐ x ∂(volumeMeasureOn (U : Set (Vec d))),
      symmPart (b.toCoeffField x) = nu • (1 : Mat d))
    (hM : ∀ᵐ x ∂(volumeMeasureOn (U : Set (Vec d))),
      matrixOperatorNorm (a.toCoeffField x - b.toCoeffField x) ≤ M)
    {u ub : H1Function (U : Set (Vec d))} {w : H10Function (U : Set (Vec d))}
    (hbc : ub = u + w.toH1Function)
    (hu : IsAHarmonicGradient a.toCoeffField (U : Set (Vec d)) u.grad)
    (hub : IsAHarmonicGradient b.toCoeffField (U : Set (Vec d)) ub.grad) :
    nu * Real.sqrt (∫ x in (U : Set (Vec d)), vecNormSq (u.grad x - ub.grad x)
        ∂MeasureTheory.volume) ≤
      M * Real.sqrt (∫ x in (U : Set (Vec d)), vecNormSq (u.grad x)
        ∂MeasureTheory.volume) := by
  classical
  have hgradub : ub.grad = fun x => u.grad x + w.toH1Function.grad x := by
    rw [hbc]
    rfl
  have hvL2 : MemVectorL2 (U : Set (Vec d)) w.toH1Function.grad :=
    w.toH1Function.grad_memVectorL2
  have huL2 : MemVectorL2 (U : Set (Vec d)) u.grad := u.grad_memVectorL2
  have hbu : MemVectorL2 (U : Set (Vec d))
      fun x => matVecMul (b.toCoeffField x) (u.grad x) :=
    memVectorL2_matVecMul_coeffOn b huL2
  have hbv : MemVectorL2 (U : Set (Vec d))
      fun x => matVecMul (b.toCoeffField x) (w.toH1Function.grad x) :=
    memVectorL2_matVecMul_coeffOn b hvL2
  have hau : MemVectorL2 (U : Set (Vec d))
      fun x => matVecMul (a.toCoeffField x) (u.grad x) :=
    memVectorL2_matVecMul_coeffOn a huL2
  have hIbu : MeasureTheory.IntegrableOn
      (fun x => vecDot (matVecMul (b.toCoeffField x) (u.grad x))
        (w.toH1Function.grad x)) (U : Set (Vec d)) :=
    integrableOn_vecDot_of_memVectorL2 hbu hvL2
  have hIbv : MeasureTheory.IntegrableOn
      (fun x => vecDot (matVecMul (b.toCoeffField x) (w.toH1Function.grad x))
        (w.toH1Function.grad x)) (U : Set (Vec d)) :=
    integrableOn_vecDot_of_memVectorL2 hbv hvL2
  have hIau : MeasureTheory.IntegrableOn
      (fun x => vecDot (matVecMul (a.toCoeffField x) (u.grad x))
        (w.toH1Function.grad x)) (U : Set (Vec d)) :=
    integrableOn_vecDot_of_memVectorL2 hau hvL2
  have hsolb : ∫ x in (U : Set (Vec d)),
      vecDot (matVecMul (b.toCoeffField x) (u.grad x + w.toH1Function.grad x))
        (w.toH1Function.grad x) ∂MeasureTheory.volume = 0 := by
    have h := hub.2 w
    rw [hgradub] at h
    exact h
  have hsola : ∫ x in (U : Set (Vec d)),
      vecDot (matVecMul (a.toCoeffField x) (u.grad x))
        (w.toH1Function.grad x) ∂MeasureTheory.volume = 0 := hu.2 w
  have hsplit :
      (fun x => vecDot (matVecMul (b.toCoeffField x)
          (u.grad x + w.toH1Function.grad x)) (w.toH1Function.grad x))
      = fun x => vecDot (matVecMul (b.toCoeffField x) (u.grad x))
            (w.toH1Function.grad x) +
          vecDot (matVecMul (b.toCoeffField x) (w.toH1Function.grad x))
            (w.toH1Function.grad x) := by
    funext x
    rw [matVecMul_add, vecDot_add_left]
  have h1 : (∫ x in (U : Set (Vec d)),
        vecDot (matVecMul (b.toCoeffField x) (u.grad x)) (w.toH1Function.grad x)
        ∂MeasureTheory.volume) +
      (∫ x in (U : Set (Vec d)),
        vecDot (matVecMul (b.toCoeffField x) (w.toH1Function.grad x))
          (w.toH1Function.grad x) ∂MeasureTheory.volume) = 0 := by
    rw [← MeasureTheory.integral_add hIbu hIbv, ← hsplit]
    exact hsolb
  have h2 : (∫ x in (U : Set (Vec d)),
        vecDot (matVecMul (b.toCoeffField x) (w.toH1Function.grad x))
          (w.toH1Function.grad x) ∂MeasureTheory.volume) =
      nu * ∫ x in (U : Set (Vec d)), vecNormSq (w.toH1Function.grad x)
        ∂MeasureTheory.volume := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hbsymm] with x hx
    exact vecDot_matVecMul_self_of_symmPart hx (w.toH1Function.grad x)
  have hab : MemVectorL2 (U : Set (Vec d))
      fun x => matVecMul (a.toCoeffField x - b.toCoeffField x) (u.grad x) := by
    have hfun :
        (fun x => matVecMul (a.toCoeffField x - b.toCoeffField x) (u.grad x))
        = fun x => matVecMul (a.toCoeffField x) (u.grad x) -
            matVecMul (b.toCoeffField x) (u.grad x) := by
      funext x
      exact matVecMul_sub_left _ _ _
    rw [hfun]
    exact hau.sub hbu
  have hIab : MeasureTheory.IntegrableOn
      (fun x => vecDot (matVecMul (a.toCoeffField x - b.toCoeffField x) (u.grad x))
        (w.toH1Function.grad x)) (U : Set (Vec d)) :=
    integrableOn_vecDot_of_memVectorL2 hab hvL2
  have h3 : (∫ x in (U : Set (Vec d)),
        vecDot (matVecMul (a.toCoeffField x - b.toCoeffField x) (u.grad x))
          (w.toH1Function.grad x) ∂MeasureTheory.volume) =
      nu * ∫ x in (U : Set (Vec d)), vecNormSq (w.toH1Function.grad x)
        ∂MeasureTheory.volume := by
    have hfun :
        (fun x => vecDot (matVecMul (a.toCoeffField x - b.toCoeffField x) (u.grad x))
            (w.toH1Function.grad x))
        = fun x => vecDot (matVecMul (a.toCoeffField x) (u.grad x))
              (w.toH1Function.grad x) -
            vecDot (matVecMul (b.toCoeffField x) (u.grad x))
              (w.toH1Function.grad x) := by
      funext x
      rw [matVecMul_sub_left, vecDot_sub_left]
    rw [hfun, MeasureTheory.integral_sub hIau hIbu, hsola]
    linarith only [h1, h2]
  have hMnonneg : 0 ≤ M := nonneg_of_ae_matrixOperatorNorm_le (U := U) hM
  have hIuInt : MeasureTheory.IntegrableOn (fun x => vecNormSq (u.grad x))
      (U : Set (Vec d)) := integrableOn_vecNormSq_h1Grad u
  have hIwInt : MeasureTheory.IntegrableOn
      (fun x => vecNormSq (w.toH1Function.grad x)) (U : Set (Vec d)) :=
    integrableOn_vecNormSq_zeroTraceGrad w
  have hbound : ∀ᵐ x ∂(volumeMeasureOn (U : Set (Vec d))),
      2 * vecDot (matVecMul (a.toCoeffField x - b.toCoeffField x) (u.grad x))
          (w.toH1Function.grad x) ≤
        nu⁻¹ * M ^ 2 * vecNormSq (u.grad x) +
          nu * vecNormSq (w.toH1Function.grad x) := by
    filter_upwards [hM] with x hx
    have hyoung := two_mul_vecDot_le hnu
      (matVecMul (a.toCoeffField x - b.toCoeffField x) (u.grad x))
      (w.toH1Function.grad x)
    have hop := vecNormSq_matVecMul_le_matrixOperatorNorm_sq_mul_vecNormSq
      (a.toCoeffField x - b.toCoeffField x) (u.grad x)
    have hsq : matrixOperatorNorm (a.toCoeffField x - b.toCoeffField x) ^ 2 ≤ M ^ 2 :=
      pow_le_pow_left₀ (matrixOperatorNorm_nonneg _) hx 2
    have hmul : matrixOperatorNorm (a.toCoeffField x - b.toCoeffField x) ^ 2 *
        vecNormSq (u.grad x) ≤ M ^ 2 * vecNormSq (u.grad x) :=
      mul_le_mul_of_nonneg_right hsq (vecNormSq_nonneg _)
    have hinv : (0 : ℝ) ≤ nu⁻¹ := le_of_lt (inv_pos.mpr hnu)
    have hscaled := mul_le_mul_of_nonneg_left (hop.trans hmul) hinv
    rw [← mul_assoc] at hscaled
    linarith only [hyoung, hscaled]
  have hRHSint : MeasureTheory.IntegrableOn
      (fun x => nu⁻¹ * M ^ 2 * vecNormSq (u.grad x) +
        nu * vecNormSq (w.toH1Function.grad x)) (U : Set (Vec d)) := by
    exact ((hIuInt.const_mul (nu⁻¹ * M ^ 2)).fun_add (hIwInt.const_mul nu))
  have hmono := MeasureTheory.integral_mono_ae (hIab.const_mul 2) hRHSint hbound
  rw [MeasureTheory.integral_add (hIuInt.const_mul (nu⁻¹ * M ^ 2))
      (hIwInt.const_mul nu), MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, h3] at hmono
  have hstep : nu * ∫ x in (U : Set (Vec d)), vecNormSq (w.toH1Function.grad x)
        ∂MeasureTheory.volume ≤
      nu⁻¹ * M ^ 2 * ∫ x in (U : Set (Vec d)), vecNormSq (u.grad x)
        ∂MeasureTheory.volume := by
    linarith only [hmono]
  have hfinal : nu ^ 2 * ∫ x in (U : Set (Vec d)),
        vecNormSq (w.toH1Function.grad x) ∂MeasureTheory.volume ≤
      M ^ 2 * ∫ x in (U : Set (Vec d)), vecNormSq (u.grad x) ∂MeasureTheory.volume := by
    have h := mul_le_mul_of_nonneg_left hstep hnu.le
    have hl : nu * (nu * ∫ x in (U : Set (Vec d)),
        vecNormSq (w.toH1Function.grad x) ∂MeasureTheory.volume) =
        nu ^ 2 * ∫ x in (U : Set (Vec d)),
          vecNormSq (w.toH1Function.grad x) ∂MeasureTheory.volume := by ring
    have hr : nu * (nu⁻¹ * M ^ 2 * ∫ x in (U : Set (Vec d)),
        vecNormSq (u.grad x) ∂MeasureTheory.volume) =
        M ^ 2 * ∫ x in (U : Set (Vec d)), vecNormSq (u.grad x)
          ∂MeasureTheory.volume := by
      field_simp
    rw [hl, hr] at h
    exact h
  have hgoalfun : (fun x => vecNormSq (u.grad x - ub.grad x))
      = fun x => vecNormSq (w.toH1Function.grad x) := by
    funext x
    have hx : u.grad x - ub.grad x = -(w.toH1Function.grad x) := by
      rw [hgradub]
      show u.grad x - (u.grad x + w.toH1Function.grad x) = -(w.toH1Function.grad x)
      abel
    rw [hx, vecNormSq_neg]
  rw [hgoalfun]
  have hleft : nu * Real.sqrt (∫ x in (U : Set (Vec d)),
      vecNormSq (w.toH1Function.grad x) ∂MeasureTheory.volume) =
      Real.sqrt (nu ^ 2 * ∫ x in (U : Set (Vec d)),
        vecNormSq (w.toH1Function.grad x) ∂MeasureTheory.volume) := by
    rw [Real.sqrt_mul (sq_nonneg nu), Real.sqrt_sq hnu.le]
  have hright : M * Real.sqrt (∫ x in (U : Set (Vec d)),
      vecNormSq (u.grad x) ∂MeasureTheory.volume) =
      Real.sqrt (M ^ 2 * ∫ x in (U : Set (Vec d)),
        vecNormSq (u.grad x) ∂MeasureTheory.volume) := by
    rw [Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hMnonneg]
  rw [hleft, hright]
  exact Real.sqrt_le_sqrt hfinal

/-! ## The two-cutoff instances

`a_L = nu Id + k_L` has symmetric part `nu Id` at every point, and for
`L₁ ≤ L₂` the difference `a_{L₂} - a_{L₁}` is the finite shell increment
`k_{L₂} - k_{L₁}` of `SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement`.
The quantitative ellipticity constants of the two cutoff fields are supplied,
as everywhere in this development, by entry bounds on the domain. -/

/-- The difference of two cutoff coefficient fields is the finite shell
increment: `a_{L₂}(x) - a_{L₁}(x) = k_{L₂}(x) - k_{L₁}(x)`. -/
theorem coefficientCutoff_toCoeffField_sub (nu : ℝ) (omega : ShellSeq d)
    {L₁ L₂ : ℕ} (hL : L₁ ≤ L₂) (x : Vec d) :
    (coefficientCutoff nu omega L₂).toCoeffField x -
        (coefficientCutoff nu omega L₁).toCoeffField x =
      finiteShellIncrement omega L₁ L₂ x := by
  rw [coefficientCutoff_toCoeffField_apply, coefficientCutoff_toCoeffField_apply,
    finiteShellIncrement_apply_eq_streamCutoff_sub omega hL]
  abel

/-! ### On a triadic cube

On `cu_l` the constant of the estimate is the `L∞(cu_l)` carrier of the
shell increment, whose `Γ₂` tail is
`isBigOWith_gammaSigma_finiteShellIncrementLinftyNormLargeCube` for `L₁ < L₂ ≤ l`
(and `isBigOWith_gammaSigma_largeCubeIncrementSupBound` for the measurable
envelope). No further work is needed to compose the two: the constant appearing
below is literally the random variable those tail estimates bound. -/

end

end SuperdiffusionCLT.Section2.Localization
