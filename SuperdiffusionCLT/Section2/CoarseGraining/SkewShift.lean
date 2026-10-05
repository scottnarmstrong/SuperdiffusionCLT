/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.CoarseGraining.Correspondence
public import Homogenization.Book.Ch02.Theorems.SolutionIntegrability
public import Homogenization.Sobolev.Foundations.EuclideanL2CZ

/-!
# Commutation of coarse graining with constant anti-symmetric matrices

The manuscript's `e.commute.k0` and `e.commute.coarse.grained.k0` record that the
coarse-grained matrices see the coefficient field only modulo the addition of a
constant anti-symmetric matrix `k_0`:

`s(U; a + k_0) = s(U; a)`, `s_*(U; a + k_0) = s_*(U; a)` and
`k(U; a + k_0) = k(U; a) + k_0`,

and, in block form, `bfA(U; a + k_0) = G_{-k_0}^t bfA(U; a) G_{-k_0}` with the
gauge matrix `G_h` of `e.G`.

The argument has two halves. The algebraic half, from the transformation law of
the response functional to the matrix identities, is proved in
`SuperdiffusionCLT.Section2.CoarseGraining.Correspondence`, conditionally
on that transformation law. This module proves the analytic half and then
discharges the condition, so that `e.commute.k0` becomes unconditional.

The analytic half is the null Lagrangian: for a constant anti-symmetric `k_0`
and `u` in `H^1(U)` the field `k_0 grad u` is weakly divergence free, because
`sum_{i,j} (k_0)_{ij} int_U d_j u d_i phi = 0` once the array
`int_U d_j u d_i phi` is symmetric in `(i,j)`, which is two integrations by
parts against a smooth test together with the symmetry of second derivatives.
Hence the `a`-harmonic class does not move, the response integrand of
`a + k_0` at the load `(p,q)` is the response integrand of `a` at the sheared
load `(p, q + k_0 p)`, and therefore `J(U,p,q; a + k_0) = J(U,p,q + k_0 p; a)`.

Throughout, the shifted field is carried as a second Chapter 2 coefficient
object `b` with `b = a + k_0` pointwise; that is how the ellipticity constants
of the shifted field are supplied. The canonical such `b`, and the marginal
instance for the centered cutoff representative, are in the companion module
`SuperdiffusionCLT.Section2.CoarseGraining.SkewShiftCutoff`.

## Main results

* `isSolenoidalOn_matVecMul_const_skew`: the constant-skew null Lagrangian.
* `integral_grad_mul_euclideanCoordDeriv_comm`: the weak cross-derivative symmetry
  `int_U d_j u d_i phi = int_U d_i u d_j phi` against a smooth compactly supported test.
* `isAHarmonicGradient_add_const_skew`,
  `isAHarmonicGradient_add_const_skew_iff`: `A(U; a) = A(U; a + k_0)`.
* `responseJ_add_const_skew`: `J(U,p,q; a + k_0) = J(U,p,q + k_0 p; a)`.
* `sigmaCoarse_add_const_skew`, `sigmaStarInvCoarse_add_const_skew`,
  `kappaCoarse_add_const_skew`: `e.commute.k0`.
* `coarseBlockMatrix_add_const_skew_blocks`,
  `coarseBlockMatrix_add_const_skew`: `e.commute.coarse.grained.k0`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.CoarseGraining

open Homogenization

noncomputable section

variable {d : ℕ}

/-! ## Elementary consequences of anti-symmetry -/

/-- Pairing two vectors across a constant anti-symmetric matrix is
anti-symmetric in the two slots. -/
theorem vecDot_matVecMul_swap_of_skew {k0 : Mat d} (hk0 : matTranspose k0 = -k0)
    (x y : Vec d) :
    vecDot x (matVecMul k0 y) = -vecDot (matVecMul k0 x) y := by
  have h := vecDot_matVecMul_transpose x y k0
  rw [hk0, neg_matVecMul, vecDot_neg_right] at h
  linarith only [h]

/-- The quadratic form of a constant anti-symmetric matrix vanishes. -/
theorem vecDot_matVecMul_self_of_skew {k0 : Mat d}
    (hk0 : matTranspose k0 = -k0) (p : Vec d) :
    vecDot p (matVecMul k0 p) = 0 := by
  have h := vecDot_matVecMul_swap_of_skew hk0 p p
  rw [vecDot_comm (matVecMul k0 p) p] at h
  linarith only [h]

/-- A constant anti-symmetric shift does not change the symmetric part. -/
theorem symmPart_add_const_skew {k0 : Mat d} (hk0 : matTranspose k0 = -k0)
    (A : Mat d) : symmPart (A + k0) = symmPart A := by
  ext i j
  have h : k0 j i = -k0 i j := congrFun (congrFun hk0 i) j
  simp only [symmPart, Matrix.add_apply, h]
  ring

/-! ## `L²` bookkeeping -/

/-- A constant matrix applied to an `L²` vector field stays in `L²`. -/
theorem memVectorL2_matVecMul_const {U : Set (Vec d)} (K : Mat d)
    {w : Vec d → Vec d} (hw : MemVectorL2 U w) :
    MemVectorL2 U (fun x => matVecMul K (w x)) := by
  refine MeasureTheory.MemLp.of_eval ?_
  intro i
  have hcoord :
      (fun x => matVecMul K (w x) i) = fun x => ∑ j : Fin d, K i j * w x j := rfl
  rw [hcoord]
  exact MeasureTheory.memLp_finsetSum _ fun j _ => (hw.eval j).const_mul (K i j)

/-- An `L²` vector field pairs integrably with every `H¹₀` test gradient. -/
theorem h10FluxIntegrable_of_memVectorL2 {U : Set (Vec d)} {F : Vec d → Vec d}
    (hF : MemVectorL2 U F) : h10FluxIntegrable U F := by
  intro φ
  have hcoord : ∀ i : Fin d,
      MeasureTheory.IntegrableOn
        (fun x => F x i * φ.toH1Function.grad x i) U := by
    intro i
    exact
      (hF.eval i).integrable_mul (φ.toH1Function.gradMemL2 i)
  have hsum :
      (fun x => vecDot (F x) (φ.toH1Function.grad x)) =
        fun x => ∑ i : Fin d, F x i * φ.toH1Function.grad x i := rfl
  rw [hsum]
  exact MeasureTheory.integrable_finsetSum _ fun i _ => hcoord i

/-- The sum of two weakly divergence-free fields with integrable pairings is
weakly divergence free. -/
theorem isSolenoidalOn_add {U : Set (Vec d)} {F G : Vec d → Vec d}
    (hF : IsSolenoidalOn U F) (hG : IsSolenoidalOn U G)
    (hFint : h10FluxIntegrable U F) (hGint : h10FluxIntegrable U G) :
    IsSolenoidalOn U (fun x => F x + G x) := by
  intro φ
  have hsplit :
      (fun x => vecDot (F x + G x) (φ.toH1Function.grad x)) =
        fun x => vecDot (F x) (φ.toH1Function.grad x) +
          vecDot (G x) (φ.toH1Function.grad x) := by
    funext x
    rw [vecDot_add_left]
  rw [hsplit, MeasureTheory.integral_add (hFint φ) (hGint φ), hF φ, hG φ,
    add_zero]

/-! ## The cross-derivative symmetry -/

/-- Contracting a constant anti-symmetric matrix against a symmetric array of
reals gives zero. -/
private theorem sum_sum_mul_eq_zero_of_skew {k0 : Mat d}
    (hk0 : matTranspose k0 = -k0) (I : Fin d → Fin d → ℝ)
    (hI : ∀ i j, I i j = I j i) :
    ∑ i : Fin d, ∑ j : Fin d, k0 i j * I i j = 0 := by
  have hskew : ∀ i j : Fin d, k0 j i = -k0 i j := fun i j =>
    congrFun (congrFun hk0 i) j
  have hswap :
      ∑ i : Fin d, ∑ j : Fin d, k0 i j * I i j =
        ∑ i : Fin d, ∑ j : Fin d, k0 j i * I j i :=
    Finset.sum_comm
  have hneg :
      ∑ i : Fin d, ∑ j : Fin d, k0 j i * I j i =
        -∑ i : Fin d, ∑ j : Fin d, k0 i j * I i j := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hskew i j, hI j i]
    ring
  have hself := hswap.trans hneg
  linarith only [hself]

/-- The weak cross-derivative symmetry against a smooth compactly supported
test function: for `u ∈ H¹(U)` and `ψ ∈ C_c^∞(U)`,
`∫_U ∂_j u ∂_i ψ = ∫_U ∂_i u ∂_j ψ`.

Both sides equal `−∫_U u ∂_i∂_j ψ` by the weak-gradient identity, and the two
second derivatives agree because `ψ` is smooth. -/
theorem integral_grad_mul_euclideanCoordDeriv_comm {U : Set (Vec d)}
    (u : H1Function U) {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψs : HasCompactSupport ψ) (hψsub : tsupport ψ ⊆ U) (i j : Fin d) :
    (∫ x in U, u.grad x j * euclideanCoordDeriv i ψ x ∂MeasureTheory.volume) =
      ∫ x in U, u.grad x i * euclideanCoordDeriv j ψ x
        ∂MeasureTheory.volume := by
  have hIBP : ∀ a b : Fin d,
      (∫ x in U, u.grad x b * euclideanCoordDeriv a ψ x
          ∂MeasureTheory.volume) =
        -∫ x in U, u.toFun x * euclideanCoordSecondDeriv a b ψ x
          ∂MeasureTheory.volume := by
    intro a b
    have hweak :
        (∫ x in U, u.toFun x * euclideanCoordSecondDeriv a b ψ x
            ∂MeasureTheory.volume) =
          -∫ x in U, u.grad x b * euclideanCoordDeriv a ψ x
            ∂MeasureTheory.volume :=
      u.hasWeakGradient b (euclideanCoordDeriv a ψ)
        (contDiff_euclideanCoordDeriv hψ a)
        (hasCompactSupport_euclideanCoordDeriv hψs a)
        ((tsupport_euclideanCoordDeriv_subset_tsupport a ψ).trans hψsub)
    rw [hweak]
    ring
  rw [hIBP i j, hIBP j i, euclideanCoordSecondDeriv_comm_fun hψ i j]

/-! ## The constant-skew null Lagrangian -/

/-- The null Lagrangian of `e.commute.k0`: for a constant anti-symmetric `k₀`
and a potential field `f = ∇u` on `U`, the field `k₀ f` is weakly divergence
free on `U`.

This is the analytic half of the manuscript's assertion
`A(U; a) = A(U; a + k₀)`. -/
theorem isSolenoidalOn_matVecMul_const_skew {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] (hU : IsOpen U)
    {k0 : Mat d} (hk0 : matTranspose k0 = -k0) {f : Vec d → Vec d}
    (hf : IsPotentialOn U f) :
    IsSolenoidalOn U (fun x => matVecMul k0 (f x)) := by
  obtain ⟨u, rfl⟩ := hf
  have hmem : MemVectorL2 U (fun x => matVecMul k0 (u.grad x)) :=
    memVectorL2_matVecMul_const k0 u.grad_memVectorL2
  refine IsSolenoidalOn.of_test_of_contDiff_of_memVectorL2 hmem hU ?_
  intro ψ hψ hψs hψsub
  have hDL2 : ∀ i : Fin d,
      MeasureTheory.MemLp (euclideanCoordDeriv i ψ) 2 (volumeMeasureOn U) :=
    fun i =>
      (((contDiff_euclideanCoordDeriv hψ i).continuous).memLp_of_hasCompactSupport
        (hasCompactSupport_euclideanCoordDeriv hψs i)).restrict U
  have hInt : ∀ i j : Fin d,
      MeasureTheory.IntegrableOn
        (fun x => u.grad x j * euclideanCoordDeriv i ψ x) U := fun i j => by
    exact (u.gradMemL2 j).integrable_mul (hDL2 i)
  have hpoint : ∀ x : Vec d,
      vecDot (matVecMul k0 (u.grad x)) (fun i => (fderiv ℝ ψ x) (basisVec i)) =
        ∑ i : Fin d, ∑ j : Fin d,
          k0 i j * (u.grad x j * euclideanCoordDeriv i ψ x) := by
    intro x
    simp only [vecDot, matVecMul, euclideanCoordDeriv, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by ring
  calc
    (∫ x in U,
        vecDot (matVecMul k0 (u.grad x))
            (fun i => (fderiv ℝ ψ x) (basisVec i)) ∂MeasureTheory.volume)
        = ∫ x in U,
            (∑ i : Fin d, ∑ j : Fin d,
              k0 i j * (u.grad x j * euclideanCoordDeriv i ψ x))
              ∂MeasureTheory.volume :=
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = ∑ i : Fin d, ∫ x in U,
            (∑ j : Fin d, k0 i j * (u.grad x j * euclideanCoordDeriv i ψ x))
              ∂MeasureTheory.volume := by
          refine MeasureTheory.integral_finsetSum _ fun i _ => ?_
          exact MeasureTheory.integrable_finsetSum _
            fun j _ => (hInt i j).const_mul (k0 i j)
    _ = ∑ i : Fin d, ∑ j : Fin d,
            k0 i j *
              ∫ x in U, u.grad x j * euclideanCoordDeriv i ψ x
                ∂MeasureTheory.volume := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [MeasureTheory.integral_finsetSum _
            fun j _ => (hInt i j).const_mul (k0 i j)]
          exact Finset.sum_congr rfl fun j _ =>
            MeasureTheory.integral_const_mul _ _
    _ = 0 :=
        sum_sum_mul_eq_zero_of_skew hk0
          (fun i j => ∫ x in U, u.grad x j * euclideanCoordDeriv i ψ x
            ∂MeasureTheory.volume)
          (fun i j => integral_grad_mul_euclideanCoordDeriv_comm u hψ hψs
            hψsub i j)

/-! ## The harmonic class under a constant anti-symmetric shift -/

/-- Adding a constant anti-symmetric matrix to the coefficient field does not
move the `a`-harmonic class. -/
theorem isAHarmonicGradient_add_const_skew {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] (hU : IsOpen U)
    {k0 : Mat d} (hk0 : matTranspose k0 = -k0) {c : CoeffField d}
    {f : Vec d → Vec d}
    (hflux : MemVectorL2 U (fun x => matVecMul (c x) (f x)))
    (hf : IsAHarmonicGradient c U f) :
    IsAHarmonicGradient (fun x => c x + k0) U f := by
  obtain ⟨hpot, hsol⟩ := hf
  refine ⟨hpot, ?_⟩
  have hfL2 : MemVectorL2 U f := by
    obtain ⟨u, hu⟩ := hpot
    rw [← hu]
    exact u.grad_memVectorL2
  have hadd :
      IsSolenoidalOn U
        (fun x => matVecMul (c x) (f x) + matVecMul k0 (f x)) :=
    isSolenoidalOn_add hsol (isSolenoidalOn_matVecMul_const_skew hU hk0 hpot)
      (h10FluxIntegrable_of_memVectorL2 hflux)
      (h10FluxIntegrable_of_memVectorL2 (memVectorL2_matVecMul_const k0 hfL2))
  have hfun : (fun x => matVecMul (c x + k0) (f x)) =
      fun x => matVecMul (c x) (f x) + matVecMul k0 (f x) := by
    funext x
    rw [add_matVecMul]
  rw [hfun]
  exact hadd

/-- The invariance of the `a`-harmonic class under a constant anti-symmetric
shift, in both directions. -/
theorem isAHarmonicGradient_add_const_skew_iff {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] (hU : IsOpen U)
    {k0 : Mat d} (hk0 : matTranspose k0 = -k0) {c : CoeffField d}
    {f : Vec d → Vec d}
    (hflux : MemVectorL2 U (fun x => matVecMul (c x) (f x))) :
    IsAHarmonicGradient (fun x => c x + k0) U f ↔ IsAHarmonicGradient c U f := by
  have hneg : matTranspose (-k0) = -(-k0) := by
    rw [matTranspose, Matrix.transpose_neg, ← matTranspose, hk0]
  constructor
  · intro hshift
    have hfL2 : MemVectorL2 U f := by
      obtain ⟨u, hu⟩ := hshift.1
      rw [← hu]
      exact u.grad_memVectorL2
    have hfluxShift :
        MemVectorL2 U (fun x => matVecMul (c x + k0) (f x)) := by
      have hfun : (fun x => matVecMul (c x + k0) (f x)) =
          fun x => matVecMul (c x) (f x) + matVecMul k0 (f x) := by
        funext x
        rw [add_matVecMul]
      rw [hfun]
      exact hflux.add (memVectorL2_matVecMul_const k0 hfL2)
    have h := isAHarmonicGradient_add_const_skew hU hneg hfluxShift hshift
    have hfun : (fun x => c x + k0 + -k0) = c := by
      funext x
      rw [add_neg_cancel_right]
    rwa [hfun] at h
  · exact isAHarmonicGradient_add_const_skew hU hk0 hflux

/-! ## The weak cross-derivative symmetry -/

/-! ## The response functional under a constant anti-symmetric shift -/

section ResponseShift

variable {U : Book.Ch02.Domain d} {a b : Book.Ch02.CoeffOn U} {k0 : Mat d}

/-- An `a`-harmonic function, read as an `(a + k₀)`-harmonic function. -/
def skewShiftSolution (hk0 : matTranspose k0 = -k0)
    (hb : ∀ x, b.toCoeffField x = a.toCoeffField x + k0)
    (u : Book.Ch02.Solution U a) : Book.Ch02.Solution U b where
  toH1 := u.toH1
  isHarmonic := by
    have h := isAHarmonicGradient_add_const_skew (U := (U : Set (Vec d)))
      U.isOpen hk0 (Book.Ch02.Solution.flux_memVectorL2 u) u.isHarmonic
    have hfun : b.toCoeffField = fun x => a.toCoeffField x + k0 := funext hb
    rw [hfun]
    exact h

/-- An `(a + k₀)`-harmonic function, read as an `a`-harmonic function. -/
def skewShiftSolutionSymm (hk0 : matTranspose k0 = -k0)
    (hb : ∀ x, b.toCoeffField x = a.toCoeffField x + k0)
    (v : Book.Ch02.Solution U b) : Book.Ch02.Solution U a where
  toH1 := v.toH1
  isHarmonic := by
    have hneg : matTranspose (-k0) = -(-k0) := by
      rw [matTranspose, Matrix.transpose_neg, ← matTranspose, hk0]
    have h := isAHarmonicGradient_add_const_skew (U := (U : Set (Vec d)))
      U.isOpen hneg (Book.Ch02.Solution.flux_memVectorL2 v) v.isHarmonic
    have hfun : a.toCoeffField = fun x => b.toCoeffField x + -k0 := by
      funext x
      rw [hb x, add_neg_cancel_right]
    rw [hfun]
    exact h

/-- The response integrand of `a + k₀` at the load `(p, q)` is the response
integrand of `a` at the sheared load `(p, q + k₀ p)`: the symmetric part is
unchanged, and `-p·(a + k₀)∇v = -p·a∇v + (k₀p)·∇v`. -/
theorem responseIntegrand_add_const_skew (hk0 : matTranspose k0 = -k0)
    (hb : ∀ x, b.toCoeffField x = a.toCoeffField x + k0) (p q : Vec d)
    (v : Book.Ch02.Solution U b) (u : Book.Ch02.Solution U a)
    (hgrad : v.toH1.grad = u.toH1.grad) :
    Book.Ch02.responseIntegrand U b p q v =
      Book.Ch02.responseIntegrand U a p (q + matVecMul k0 p) u := by
  funext x
  simp only [Book.Ch02.responseIntegrand]
  rw [hgrad, hb x, symmPart_add_const_skew hk0, add_matVecMul, vecDot_add_right,
    vecDot_matVecMul_swap_of_skew hk0 p, vecDot_add_left]
  ring

/-- The sheared-load identity for one admissible solution. -/
theorem responseValue_add_const_skew (hk0 : matTranspose k0 = -k0)
    (hb : ∀ x, b.toCoeffField x = a.toCoeffField x + k0) (p q : Vec d)
    (v : Book.Ch02.Solution U b) (u : Book.Ch02.Solution U a)
    (hgrad : v.toH1.grad = u.toH1.grad) :
    Book.Ch02.responseValue U b p q v =
      Book.Ch02.responseValue U a p (q + matVecMul k0 p) u := by
  unfold Book.Ch02.responseValue
  rw [responseIntegrand_add_const_skew hk0 hb p q v u hgrad]

/-- The transformation law of the response functional:
`J(U, p, q; a + k₀) = J(U, p, q + k₀ p; a)`. -/
theorem responseJ_add_const_skew (hk0 : matTranspose k0 = -k0)
    (hb : ∀ x, b.toCoeffField x = a.toCoeffField x + k0) (p q : Vec d) :
    Book.Ch02.responseJ U b p q =
      Book.Ch02.responseJ U a p (q + matVecMul k0 p) := by
  unfold Book.Ch02.responseJ
  congr 1
  ext m
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨skewShiftSolutionSymm hk0 hb v,
      responseValue_add_const_skew hk0 hb p q v
        (skewShiftSolutionSymm hk0 hb v) rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨skewShiftSolution hk0 hb u,
      (responseValue_add_const_skew hk0 hb p q
        (skewShiftSolution hk0 hb u) u rfl).symm⟩

/-- The transformation law on the raw carrier, in the exact shape consumed by
the conditional coarse-matrix theorems of
`SuperdiffusionCLT.Section2.CoarseGraining.Correspondence`. -/
theorem responseJ_toCoeffField_add_const_skew (hk0 : matTranspose k0 = -k0)
    (hb : ∀ x, b.toCoeffField x = a.toCoeffField x + k0) (p q : Vec d) :
    Homogenization.ResponseJ (U : Set (Vec d)) p q b.toCoeffField =
      Homogenization.ResponseJ (U : Set (Vec d)) p (q + matVecMul k0 p)
        a.toCoeffField := by
  rw [responseJ_toCoeffField U b p q,
    responseJ_toCoeffField U a p (q + matVecMul k0 p),
    responseJ_add_const_skew hk0 hb]

end ResponseShift

/-! ## `e.commute.k0` and `e.commute.coarse.grained.k0` -/

section CommuteK0

variable {U : Book.Ch02.Domain d} {a b : Book.Ch02.CoeffOn U} {k0 : Mat d}

/-- `e.commute.k0`, first identity: `s(U; a + k₀) = s(U; a)`. -/
theorem sigmaCoarse_add_const_skew (hk0 : matTranspose k0 = -k0)
    (hb : ∀ x, b.toCoeffField x = a.toCoeffField x + k0) :
    Book.Ch02.sigmaCoarse U b = Book.Ch02.sigmaCoarse U a :=
  sigmaCoarse_eq_of_responseJ_skewShift hk0
    (responseJ_toCoeffField_add_const_skew hk0 hb)

/-- The primitive coarse matrix `s_*^{-1}(U)` is likewise unchanged. -/
theorem sigmaStarInvCoarse_add_const_skew (hk0 : matTranspose k0 = -k0)
    (hb : ∀ x, b.toCoeffField x = a.toCoeffField x + k0) :
    Book.Ch02.sigmaStarInvCoarse U b = Book.Ch02.sigmaStarInvCoarse U a :=
  coarseBlockMatrix_lowerRight_eq_of_responseJ_skewShift
    (responseJ_toCoeffField_add_const_skew hk0 hb)

/-- `e.commute.k0`, third identity: `k(U; a + k₀) = k(U; a) + k₀`. -/
theorem kappaCoarse_add_const_skew (hk0 : matTranspose k0 = -k0)
    (hb : ∀ x, b.toCoeffField x = a.toCoeffField x + k0) :
    Book.Ch02.kappaCoarse U b = Book.Ch02.kappaCoarse U a + k0 :=
  kappaCoarse_eq_of_responseJ_skewShift hk0
    (responseJ_toCoeffField_add_const_skew hk0 hb)

/-- `e.commute.coarse.grained.k0`, first display: the blocks
of `bfA(U; a + k₀)` are those of `bfA(U; a)` with `k(U)` replaced by
`k(U) + k₀`. -/
theorem coarseBlockMatrix_add_const_skew_blocks (hk0 : matTranspose k0 = -k0)
    (hb : ∀ x, b.toCoeffField x = a.toCoeffField x + k0) :
    Book.Ch02.coarseBlockMatrix U b =
      { upperLeft := Book.Ch02.sigmaCoarse U a +
          matTranspose (Book.Ch02.kappaCoarse U a + k0) *
            Book.Ch02.sigmaStarInvCoarse U a *
            (Book.Ch02.kappaCoarse U a + k0)
        upperRight := -(matTranspose (Book.Ch02.kappaCoarse U a + k0) *
          Book.Ch02.sigmaStarInvCoarse U a)
        lowerLeft := -(Book.Ch02.sigmaStarInvCoarse U a *
          (Book.Ch02.kappaCoarse U a + k0))
        lowerRight := Book.Ch02.sigmaStarInvCoarse U a } := by
  refine blockMat_ext ?_ ?_ ?_ ?_ <;>
    simp only [Book.Ch02.coarseBlockMatrix,
      Book.Ch02.blockMatrixOfCoarseMatrices, Book.Ch02.CoarseMatrices.b,
      Book.Ch02.coarseMatrices_sigma, Book.Ch02.coarseMatrices_sigmaStarInv,
      Book.Ch02.coarseMatrices_kappa,
      sigmaCoarse_add_const_skew hk0 hb,
      sigmaStarInvCoarse_add_const_skew hk0 hb,
      kappaCoarse_add_const_skew hk0 hb]

/-- `e.commute.coarse.grained.k0`, second display:
`bfA(U; a + k₀) = G_{-k₀}^t bfA(U; a) G_{-k₀}`, with the gauge matrix `G_h`
of `e.G`. -/
theorem coarseBlockMatrix_add_const_skew (hk0 : matTranspose k0 = -k0)
    (hb : ∀ x, b.toCoeffField x = a.toCoeffField x + k0) :
    Book.Ch02.coarseBlockMatrix U b =
      Book.Ch02.blockMatMul
        (Book.Ch02.blockMatTranspose (Book.Ch02.blockG (-k0)))
        (Book.Ch02.blockMatMul (Book.Ch02.coarseBlockMatrix U a)
          (Book.Ch02.blockG (-k0))) := by
  have hk0' : Matrix.transpose k0 = -k0 := hk0
  rw [coarseBlockMatrix_add_const_skew_blocks hk0 hb]
  refine blockMat_ext ?_ ?_ ?_ ?_ <;>
    simp only [Book.Ch02.blockMatMul, Book.Ch02.blockMatTranspose,
      Book.Ch02.blockG, Book.Ch02.coarseBlockMatrix,
      Book.Ch02.blockMatrixOfCoarseMatrices, Book.Ch02.CoarseMatrices.b,
      Book.Ch02.coarseMatrices_sigma, Book.Ch02.coarseMatrices_sigmaStarInv,
      Book.Ch02.coarseMatrices_kappa, matTranspose, Matrix.transpose_add,
      Matrix.transpose_one, Matrix.transpose_zero, Matrix.transpose_neg,
      hk0'] <;>
    noncomm_ring

end CommuteK0

end

end SuperdiffusionCLT.Section2.CoarseGraining
