/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.ResponseFields.RegboundsInputsB
public import SuperdiffusionCLT.Section2.Cutoff.Finite
public import SuperdiffusionCLT.Section2.Cutoff.StreamCutoffAPI
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2Analytic
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2FinalB

/-!
# The last two binders of the named-witness reduction of `l.RHS.term2`

## Summary

**Neither binder of the named-witness reduction of `l.RHS.term2` can be read literally off
the paper, and in each case the missing object is *not* supplied by the paper.**  For `hFinDR` the
paper states no inequality at all — it writes only

> `Combining this with~\eqref{e.nablaw.Lt} and the product rule gives`
>,

immediately followed by the display `e.RHS.term2.R.bounds`;
the density the formalization fixes for the first summand of that product rule
is `ShellField.matrixDerivativeNorm` — an *operator* norm — and the pointwise
inequality `hDRpt` at that density is **false in dimension three**.  It
fails for an explicit skew witness in dimension three (`√2` against `1`; this counterexample is
not formalized here).  For `hDispDR`
the paper prints only

> `\E\bigl[\|R\|_{\underline L^2(\cu_m)}^2\bigr]^{\nf12} + 3^\ell
> \E\bigl[\|\nabla R\|_{\underline L^2(\cu_m)}^2\bigr]^{\nf12} \leq C L' |p|`
> (`\label{e.RHS.term2.R.bounds}`),

with the same unspecified `C = C(d)` as in the statement of Lemma
`l.RHS.term2` (`There exists~$C(d)<\infty$`); the literal `C₁ = 1`
that the binder demands is written nowhere.

## Main results

* `derivContraction_norm_le` — the pointwise product rule for the `∂K`
  contraction block at the **Hilbert–Schmidt** density
  `√d · matrixDerivativeNorm D`.  This is the form the paper's "product
  rule" must mean: its input is `3^\ell \E[\|\nabla(\k_{L'}-\k_\ell)\|^4]^{1/4}
  \leq C`, an *integral* norm of the full gradient tensor, and
  `norm_hilbertMat_streamFluxWeakGradient_le` pays exactly the same `√d`.
* `streamGradJacobian_norm_le` — the product rule for the canonical Jacobian at the
  Hilbert–Schmidt density.

Every declaration below is unconditional: beyond the objects named in their
binders there is no hypothesis — in particular no `[NeZero d]`, no `2 ≤ d`, no
finiteness or measurability input — so nothing here is discharged by assumption.

## The two binders, at the exact binder shapes of the named-witness reduction

`hFinDR` — the finiteness of the Jacobian norm, at the named witness
`canonicalRJacobian d hd S hSorder (testVector nu S.LPrime P S.n e) w hw`:

```
(hFinDR : (∫⁻ omega : ShellSeq d,
    cubeLpENorm (originCube d (S.m : ℤ)) 2
      (fun x => HilbertMat.ofMat (fun i j =>
        canonicalRJacobian d hd S hSorder (testVector nu S.LPrime P S.n e)
          w hw omega i x j)) ^ (2 : ℕ)
    ∂P.toMeasure) ≠ ⊤)
```

`hDispDR` — the display `e.RHS.term2.R.bounds` at `C₁ = 1`:

```
(hDispDR :
  (∫⁻ omega : ShellSeq d,
        vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
              (coefficientCutoff nu omega S.ell).toCoeffField y)
            ((w omega).toH1Function.grad y)) ^
          (2 : ℕ) ∂P.toMeasure : ℝ≥0∞).toReal ^ ((1 : ℝ) / 2) +
    (3 : ℝ) ^ ((S.ell : ℕ) : ℝ) *
      (∫⁻ omega : ShellSeq d,
          cubeLpENorm (originCube d (S.m : ℤ)) 2
            (fun x => HilbertMat.ofMat (fun i j =>
              canonicalRJacobian d hd S hSorder (testVector nu S.LPrime P S.n e)
                w hw omega i x j)) ^
            (2 : ℕ) ∂P.toMeasure : ℝ≥0∞).toReal ^ ((1 : ℝ) / 2) ≤
    1 * ((S.LPrime : ℕ) : ℝ) *
      Real.sqrt (vecNormSq (testVector nu S.LPrime P S.n e)))
```

Both are quoted verbatim from the named-witness reduction; neither is
restated as a theorem here, because a restatement discharges nothing.

* **`hFinDR`** is the finiteness of the annealed squared `L̲²` norm of the weak
  Jacobian of `R = (k_{L'} − k_ℓ)^t ∇w`.  Its only route is the pointwise
  product rule, i.e. the hypothesis `hDRpt` carried (not proved) by the displays of
  `RHSTerm2RBounds` and `RHSTerm2RFinite`, together with the four
  factor-finiteness inputs.  The `∂K` half of `hDRpt` is
  `‖∂K ⋅ ∇w‖ ≤ GN ⋅ |∇w|` with `GN ≤ ShellField.matrixDerivativeNorm D`,
  `D = ∑_{k ∈ (ℓ,L']} ShellField.deriv (ω k) x`; that inequality is false.
* **`hDispDR`** demands the display at the literal `C₁ = 1`.
  the full display of `RHSTerm2RFinite` produces it existentially, at a realised constant
  `≥ 3`; no parameter of the display absorbs the factor and the paper
  never claims the value `1`.

## Why the `∂K` half of `hDRpt` cannot be proved from the stated densities

The canonical `∂K` block is, by
`SuperdiffusionCLT.Section3.ResponseFields.streamFluxWeakGradient_apply`,
exactly

`streamFluxWeakGradient omega a b p i x j = matVecMul (D (basisVec j)) p i`,
with `D = ∑_{k ∈ Finset.Ioc a b} ShellField.deriv (omega k) x`,

i.e. the `derivContraction D p` of this file.  So the first summand of `hDRpt`
is the claim

`‖HilbertMat.ofMat (derivContraction D p)‖ ≤ matrixDerivativeNorm D * vecNorm p`.

In dimension three there is a `D` and a `p` for which this fails (this
counterexample is not formalized here); the witness takes skew values,
which is what makes it admissible: the value field of a shell field is pointwise
skew (`Frozen/Assumptions/ShellField.lean`), so every `ShellField.deriv (ω k) x`
is skew, and conversely any skew-valued linear `D : Vec d →L[ℝ] Mat d` is the
derivative at the origin of the honest pointwise-skew map `x ↦ D x`.  The
refutation is in dimension three, not one.

Consequently `hDRpt` at the operator-norm density cannot be supplied from the
definitions: any proof needs either a different (Hilbert–Schmidt-type) density,
or the factor `√d` that `derivContraction_norm_le` and
`norm_hilbertMat_streamFluxWeakGradient_le` both pay, or coupling information
between `∇w` and the shell fields that is not present in the definitions.  The
same `√d` factor also blocks the route from the `∂K` half to the display at
`C₁ = 1`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section3.ResponseFields
open scoped BigOperators Matrix

noncomputable section

variable {d : ℕ}

/-! ## The `∂K` contraction block and its Hilbert–Schmidt density -/

/-- The `∂K` contraction block of the transported-field Jacobian: the matrix
whose column `j` is `(∂_j K) g`, i.e. `matVecMul (D (basisVec j)) g` when
`D = ∇K`.  For the canonical data this is `streamFluxWeakGradient`
(`streamFluxWeakGradient_apply`). -/
def derivContraction (D : Vec d →L[ℝ] Mat d) (g : Vec d) : Mat d :=
  fun i j => matVecMul (D (basisVec j)) g i

/-- **The product rule for the `∂K` block, at the Hilbert–Schmidt density.**
The `HilbertMat` (Frobenius) norm of the contraction block is at most
`√d · |g| · ‖D‖`, where `‖D‖` is the exact induced operator norm
`ShellField.matrixDerivativeNorm`.  The factor `√d` is the number of columns;
it cannot be removed in general. -/
theorem derivContraction_norm_le (D : Vec d →L[ℝ] Mat d) (g : Vec d) :
    ‖HilbertMat.ofMat (derivContraction D g)‖ ≤
      Real.sqrt d * vecNorm g * ShellField.matrixDerivativeNorm D := by
  have hG := ShellField.matrixDerivativeNorm_nonneg D
  have hcol : ∀ j : Fin d, matrixOperatorNorm (D (basisVec j)) ≤
      ShellField.matrixDerivativeNorm D := fun j =>
    ShellField.matrixOperatorNorm_apply_le_matrixDerivativeNorm D
      (basisVec j) (le_of_eq (vecNorm_basisVec j))
  have hswap : (∑ i : Fin d, ∑ j : Fin d,
      derivContraction D g i j * derivContraction D g i j) =
      ∑ j : Fin d, vecNormSq (matVecMul (D (basisVec j)) g) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [vecNormSq, vecDot]
    rfl
  have hsum : (∑ i : Fin d, ∑ j : Fin d,
      derivContraction D g i j * derivContraction D g i j) ≤
      (d : ℝ) * (ShellField.matrixDerivativeNorm D ^ 2 * vecNormSq g) := by
    rw [hswap]
    calc
      (∑ j : Fin d, vecNormSq (matVecMul (D (basisVec j)) g)) ≤
          ∑ _j : Fin d, ShellField.matrixDerivativeNorm D ^ 2 * vecNormSq g := by
        refine Finset.sum_le_sum fun j _ => ?_
        refine (vecNormSq_matVecMul_le_matrixOperatorNorm_sq_mul_vecNormSq _ _).trans ?_
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (matrixOperatorNorm_nonneg _) (hcol j) 2)
          (vecNormSq_nonneg g)
      _ = (d : ℝ) * (ShellField.matrixDerivativeNorm D ^ 2 * vecNormSq g) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hB : 0 ≤ Real.sqrt d * vecNorm g * ShellField.matrixDerivativeNorm D :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (vecNorm_nonneg g)) hG
  have hsq : ‖HilbertMat.ofMat (derivContraction D g)‖ ^ 2 ≤
      (Real.sqrt d * vecNorm g * ShellField.matrixDerivativeNorm D) ^ 2 := by
    rw [norm_sq_hilbertMat_ofMat]
    refine hsum.trans_eq ?_
    rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg d), vecNorm_sq_eq_vecNormSq]
    ring
  have hfin := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hB] at hfin

/-! ## The product rule for the canonical Jacobian, at the Hilbert–Schmidt density

The paper writes "Combining this with~\eqref{e.nablaw.Lt} and the
product rule gives", followed by the display `e.RHS.term2.R.bounds`.  The
`∂K` half of that product rule fails at the operator density in dimension three; what is
proved here is the *Hilbert–Schmidt* product rule for the canonical Jacobian
`streamGradJacobian`, paying the factor `√d` on the `∂K` block.  It is the
honest replacement for the carried hypothesis `hDRpt` of the display in
`RHSTerm2RBounds`. -/

/-- **Linearity of the derivative in the vector slot.**  Differentiating the
`i`-th entry of the matrix-vector product `M y · g` and evaluating in the
coordinate direction `basisVec k` is the same as summing `g j` against the
directional derivatives of the matrix entries `M y i j`.  This is the
`p`-linearity step that lets `streamFluxWeakGradient_apply` — which
differentiates the whole product `matVecMul K p i` — be read entrywise.

The hypothesis is not vacuous: `hasFDerivAt_streamCutoff_sub` supplies it with
`M = streamCutoff omega b · − streamCutoff omega a ·` and
`D = ∑_{k ∈ (a,b]} ShellField.deriv (omega k) x`, which is how it is used
below. -/
theorem fderiv_matVecMul_entry (M : Vec d → Mat d) (D : Vec d →L[ℝ] Mat d)
    (x : Vec d) (h : HasFDerivAt M D x) (g : Vec d) (i k : Fin d) :
    (fderiv ℝ (fun y : Vec d => matVecMul (M y) g i) x) (basisVec k) =
      ∑ j : Fin d, g j * (fderiv ℝ (fun y : Vec d => M y i j) x) (basisVec k) := by
  have h1 : HasFDerivAt (fun y : Vec d => M y i)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => (Fin d → ℝ)) i).comp D) x :=
    (hasFDerivAt_pi'.1 h) i
  have h2 : ∀ j : Fin d, HasFDerivAt (fun y : Vec d => M y i j)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j).comp
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => (Fin d → ℝ)) i).comp D)) x :=
    fun j => (hasFDerivAt_pi'.1 h1) j
  have hsum : HasFDerivAt (∑ j : Fin d, fun y : Vec d => g j * M y i j)
      (∑ j : Fin d, g j • ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j).comp
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => (Fin d → ℝ)) i).comp D))) x :=
    HasFDerivAt.sum fun j _ => (h2 j).const_mul (g j)
  have hfun : (fun y : Vec d => matVecMul (M y) g i) =
      ∑ j : Fin d, fun y : Vec d => g j * M y i j := by
    funext y
    rw [Finset.sum_apply, matVecMul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hfun, hsum.fderiv, sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_apply, smul_eq_mul, (h2 j).fderiv]

/-- **The `K · Hess` half of the product rule.**  If the matrix `A` multiplies
the columns of `Hs`, the Frobenius norm of the result is at most
`matrixOperatorNorm A` times the Frobenius norm of `Hs`.  No factor `√d`
appears here: the multiplication is by a fixed matrix on the left, and the
operator norm is the exact Euclidean operator norm. -/
theorem hilbertMat_ofMat_mulVec_column_le (A : Mat d) (Hs : Fin d → Fin d → ℝ) :
    ‖HilbertMat.ofMat (fun i k => matVecMul A (fun j => Hs j k) i)‖ ≤
      matrixOperatorNorm A * ‖HilbertMat.ofMat (fun j k => Hs j k)‖ := by
  have hA := matrixOperatorNorm_nonneg A
  have hB : 0 ≤ matrixOperatorNorm A * ‖HilbertMat.ofMat (fun j k => Hs j k)‖ :=
    mul_nonneg hA (norm_nonneg _)
  have hswap : (∑ i : Fin d, ∑ k : Fin d,
      matVecMul A (fun j => Hs j k) i * matVecMul A (fun j => Hs j k) i) =
      ∑ k : Fin d, vecNormSq (matVecMul A (fun j => Hs j k)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [vecNormSq, vecDot]
  have hHs : ‖HilbertMat.ofMat (fun j k => Hs j k)‖ ^ 2 =
      ∑ k : Fin d, vecNormSq (fun j => Hs j k) := by
    refine (norm_sq_hilbertMat_ofMat _).trans ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [vecNormSq, vecDot]
  have hsum : (∑ k : Fin d, vecNormSq (matVecMul A (fun j => Hs j k))) ≤
      matrixOperatorNorm A ^ 2 * (∑ k : Fin d, vecNormSq (fun j => Hs j k)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    exact vecNormSq_matVecMul_le_matrixOperatorNorm_sq_mul_vecNormSq A (fun j => Hs j k)
  have hsq : ‖HilbertMat.ofMat (fun i k => matVecMul A (fun j => Hs j k) i)‖ ^ 2 ≤
      (matrixOperatorNorm A * ‖HilbertMat.ofMat (fun j k => Hs j k)‖) ^ 2 := by
    refine ((norm_sq_hilbertMat_ofMat _).trans hswap).le.trans ?_
    refine hsum.trans ?_
    rw [mul_pow, ← hHs]
  have hfin := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hB] at hfin

/-- **The pointwise product rule for the canonical Jacobian of `(k_b − k_a)∇u`,
at the Hilbert–Schmidt density.**  The Frobenius norm of
`streamGradJacobian omega a b H` at `x` is at most

`‖k_b − k_a‖(x) · ‖Hess u‖(x) + √d · ‖∑_{k ∈ (a,b]} ∇j_k (x)‖ · |∇u (x)|`,

where `‖·‖` on the second summand is the exact induced operator norm
`ShellField.matrixDerivativeNorm` and `√d` is the number of columns.  This is
the "product rule" of the paper in the only
form in which it is true: the first summand is
`hilbertMat_ofMat_mulVec_column_le`, the second is
`derivContraction_norm_le`, and the two halves are separated by
`fderiv_matVecMul_entry`.  The factor `√d` cannot be dropped in general.

The hypotheses are not vacuous: any `omega`, `a = b`, and any H1 function with
a weak Hessian on the cube (for instance `u = 0`) satisfy them. -/
theorem streamGradJacobian_norm_le (omega : ShellSeq d) {a b : ℕ} (hab : a ≤ b)
    {Q : TriadicCube d} {u : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) u) (x : Vec d) :
    ‖HilbertMat.ofMat (fun i k => streamGradJacobian omega a b H i x k)‖ ≤
      matrixOperatorNorm (streamCutoff omega b x - streamCutoff omega a x) *
          ‖HilbertMat.ofMat (fun j k =>
            (hasWeakHessianOnSymm (isOpen_openCubeSet Q) H).hess j k x)‖ +
        Real.sqrt d *
          ShellField.matrixDerivativeNorm
            (∑ k ∈ Finset.Ioc a b, ShellField.deriv (omega k) x) *
          vecNorm (u.grad x) := by
  set D : Vec d →L[ℝ] Mat d := ∑ k ∈ Finset.Ioc a b, ShellField.deriv (omega k) x with hDdef
  have hDfd : HasFDerivAt (fun y : Vec d => streamCutoff omega b y - streamCutoff omega a y)
      D x := by
    rw [hDdef]
    exact hasFDerivAt_streamCutoff_sub omega hab x
  have hentry : ∀ i k, streamGradJacobian omega a b H i x k =
      matVecMul (streamCutoff omega b x - streamCutoff omega a x) (fun j =>
          (hasWeakHessianOnSymm (isOpen_openCubeSet Q) H).hess j k x) i +
        matVecMul (D (basisVec k)) (u.grad x) i := by
    intro i k
    have hprod := fderiv_matVecMul_entry
      (fun y : Vec d => streamCutoff omega b y - streamCutoff omega a y) D x hDfd
      (u.grad x) i k
    have hflux := streamFluxWeakGradient_apply omega hab (u.grad x) i x k
    have hflux' : (fderiv ℝ (fun y : Vec d =>
        matVecMul (streamCutoff omega b y - streamCutoff omega a y) (u.grad x) i) x)
        (basisVec k) = matVecMul (D (basisVec k)) (u.grad x) i := by
      simpa only [streamFluxWeakGradient] using hflux
    simp only [streamGradJacobian, Finset.sum_add_distrib]
    refine congrArg₂ (· + ·) ?_ ?_
    · rw [matVecMul]
    · rw [← hprod]
      exact hflux'
  have hsplit : HilbertMat.ofMat (fun i k => streamGradJacobian omega a b H i x k) =
      HilbertMat.ofMat (fun i k => matVecMul (streamCutoff omega b x - streamCutoff omega a x)
          (fun j => (hasWeakHessianOnSymm (isOpen_openCubeSet Q) H).hess j k x) i) +
        HilbertMat.ofMat (fun i k => matVecMul (D (basisVec k)) (u.grad x) i) := by
    have hfun : (fun i k => streamGradJacobian omega a b H i x k) =
        (fun i k => matVecMul (streamCutoff omega b x - streamCutoff omega a x)
            (fun j => (hasWeakHessianOnSymm (isOpen_openCubeSet Q) H).hess j k x) i +
          matVecMul (D (basisVec k)) (u.grad x) i) := by
      funext i k
      exact hentry i k
    rw [hfun]
    ext i k
    simp [HilbertMat.ofMat]
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  refine add_le_add ?_ ?_
  · exact hilbertMat_ofMat_mulVec_column_le _ _
  · refine (derivContraction_norm_le D (u.grad x)).trans (le_of_eq ?_)
    ring

end

end SuperdiffusionCLT.Section3.Terms
