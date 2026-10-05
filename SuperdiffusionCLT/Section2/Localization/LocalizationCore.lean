/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.BlockScalarCorrespondence
public import SuperdiffusionCLT.Section2.Localization.Conj3AveragedData2
public import SuperdiffusionCLT.Section2.Localization.Conj3AveragedRoute
public import SuperdiffusionCLT.Section2.Localization.Conj3AveragedClose

/-!
# The doubled-field bridge for the localization statement

The printed route to the localization clause compares the doubled field `Z` of `a` with the
doubled field `Z̃` of `ã`, through the following steps.

* `e.minimizers.energy.vs.bfA`: the block form of a doubled field is half the sum of the two
  `s`-energies of its slopes, `P·𝐀(U;a)P = ‖𝐀^½ Z‖² = ½(‖s^½ ∇u‖² + ‖s^½ ∇u*‖²)`.
* first variation with the ratio estimate gives `e.minimizers.block.diff`:
  `‖𝐀^½(Z−Z̃)‖² + ‖Ã^½(Z−Z̃)‖² ≤ Cη(P·𝐀(U;a)P + P·𝐀(U;ã)P)`.
* the split `Z̃ = Z̃₀ + Z̃₁`, with `Z̃₀ = ½ (∇ũ+∇ũ*, a ∇ũ − aᵗ ∇ũ*)` and
  `Z̃₁ = ½ (0, h(∇ũ+∇ũ*))`.
* `e.iden.AP`:
  `(e+e*, a e − aᵗ e*)·𝐀(e+e*, a e − aᵗ e*) = 2 e·s e + 2 e*·s e*`.
* `e.minimizers.gradient.from.block`, applying `e.iden.AP` to `Z − Z̃₀ = (Z − Z̃) + Z̃₁`:
  `‖s^½(∇u−∇ũ)‖² + ‖s^½(∇u*−∇ũ*)‖² ≤ C‖𝐀^½(Z−Z̃)‖² + C‖𝐀^½Z̃₁‖²`.
* `e.minimizers.deterministic`:
  `‖s^½(∇u−∇ũ)‖²_{L²(U)} ≤ Cη(P·𝐀(U;a)P + P·𝐀(U;ã)P)`.

This module proves the pointwise algebraic bridge that the split step needs.  It exposes the
two slots of the forward doubled field, defines the skew correction slot `Z̃₁`, and proves that
the adjoint pair of the two slope differences is twice `(Z − Z̃) + Z̃₁`, i.e. twice the print's
`Z − Z̃₀`.

## Main results

* `forwardDoubledField_potential`, `forwardDoubledField_flux`: the slots of the forward
  doubled field.
* `skewCorrectionField`: the print's `Z̃₁` slot.
* `adjointPair_gradDiff_eq_two_smul_split`: the bridge identity.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open Homogenization
open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## Linear algebra of the block slots -/

private theorem matVecMul_sub_vec (A : Mat d) (x y : Vec d) :
    matVecMul A (x - y) = matVecMul A x - matVecMul A y := by
  rw [sub_eq_add_neg, matVecMul_add, matVecMul_neg, sub_eq_add_neg]

private theorem matVecMul_add_mat (A B : Mat d) (x : Vec d) :
    matVecMul (A + B) x = matVecMul A x + matVecMul B x := by
  funext i
  simp only [matVecMul, Matrix.add_apply, Pi.add_apply]
  rw [show (∑ j, (A i j + B i j) * x j) = ∑ j, (A i j * x j + B i j * x j) from
    Finset.sum_congr rfl (fun j _ => by ring)]
  rw [Finset.sum_add_distrib]

private theorem matVecMul_sub_mat (A B : Mat d) (x : Vec d) :
    matVecMul (A - B) x = matVecMul A x - matVecMul B x := by
  funext i
  simp only [matVecMul, Matrix.sub_apply, Pi.sub_apply]
  rw [show (∑ j, (A i j - B i j) * x j) = ∑ j, (A i j * x j - B i j * x j) from
    Finset.sum_congr rfl (fun j _ => by ring)]
  rw [Finset.sum_sub_distrib]

private theorem matTranspose_sub_mat (A B : Mat d) :
    matTranspose (A - B) = matTranspose A - matTranspose B := by
  simp [matTranspose, Matrix.transpose_sub]

private theorem two_smul_half {E : Type*} [AddCommMonoid E] [Module ℝ E] (x : E) :
    (2 : ℝ) • ((1 / 2 : ℝ) • x) = x := by
  rw [smul_smul]
  norm_num

/-! ## The slots of the forward doubled field

`Conj3AveragedData2.forwardDoubledField` is the print's `Z = ½ (∇u+∇u*, a ∇u −
aᵗ ∇u*)` built from a scalar maximizer `u` and the transpose response maximizer.
These two `rfl` lemmas expose its slots, which the bridge identity below rewrites
in terms of the two `Solution` objects. -/

theorem forwardDoubledField_potential {U : Book.Ch02.Domain d}
    (b : Book.Ch02.CoeffOn U) (p q : Vec d) (w : Book.Ch02.Solution U b) (x : Vec d) :
    (forwardDoubledField U b p q w).potential x =
      (1 / 2 : ℝ) • (w.toH1.grad x +
        (transposeResponseMaximizer U b p (-q)).toH1.grad x) :=
  rfl

theorem forwardDoubledField_flux {U : Book.Ch02.Domain d}
    (b : Book.Ch02.CoeffOn U) (p q : Vec d) (w : Book.Ch02.Solution U b) (x : Vec d) :
    (forwardDoubledField U b p q w).flux x =
      (1 / 2 : ℝ) • (matVecMul (b.toCoeffField x) (w.toH1.grad x) -
        matVecMul (matTranspose (b.toCoeffField x))
          ((transposeResponseMaximizer U b p (-q)).toH1.grad x)) :=
  rfl

/-! ## The skew correction slot

The print's `Z̃₁`: the second slot of the difference between
the doubled field of `ã` and the doubled field of `a` at the same solutions. -/

/-- The print's `Z̃₁` slot, `½ (0, h(∇ũ+∇ũ*))` with `h = ã − a`: recorded here in
the un-halved form in which it enters the bridge identity, so that the `2`
of the doubled block representation stands in for the print's `½`. -/
def skewCorrectionField (U : Book.Ch02.Domain d) (a aT : Book.Ch02.CoeffOn U)
    (p q : Vec d) (v : Book.Ch02.Solution U aT) (x : Vec d) : BlockVec d :=
  (0, matVecMul (aT.toCoeffField x - a.toCoeffField x)
    ((forwardDoubledField U aT p q v).potential x))

/-! ## The bridge identity

The print's split `Z − Z̃₀ = (Z − Z̃) + Z̃₁`, made into an
identity of the adjoint pairs of the two slope differences.  The pair
`(e + e*, a e − aᵗ e*)` of `e.iden.AP` is built, at each point, from
`e = ∇u − ∇v` and `e* = ∇u* − ∇v*`, where `u*`, `v*` are the transpose response
maximizers of the two fields; its first slot is the potential slot of `2 (Z − Z̃₀)`
and its second slot the flux slot. -/

/-- **The bridge identity.**  With `Z = forwardDoubledField U a p q u`,
`Zt = forwardDoubledField U aT p q v`, `u* = transposeResponseMaximizer U a p (−q)`
and `v* = transposeResponseMaximizer U aT p (−q)`, and with `h = aT − a`
antisymmetric, the adjoint pair of `(e, e*) = (∇u−∇v, ∇u*−∇v*)` is twice
`(Z − Zt) + Z̃₁`, i.e. twice the print's `Z − Z̃₀`. -/
theorem adjointPair_gradDiff_eq_two_smul_split {U : Book.Ch02.Domain d}
    (a aT : Book.Ch02.CoeffOn U) (p q : Vec d)
    (u : Book.Ch02.Solution U a) (v : Book.Ch02.Solution U aT)
    (hskew : ∀ x : Vec d, matTranspose (aT.toCoeffField x - a.toCoeffField x) =
      -(aT.toCoeffField x - a.toCoeffField x)) (x : Vec d) :
    (((u.toH1.grad x - v.toH1.grad x) +
        ((transposeResponseMaximizer U a p (-q)).toH1.grad x -
          (transposeResponseMaximizer U aT p (-q)).toH1.grad x),
      matVecMul (a.toCoeffField x) (u.toH1.grad x - v.toH1.grad x) -
        matVecMul (matTranspose (a.toCoeffField x))
          ((transposeResponseMaximizer U a p (-q)).toH1.grad x -
            (transposeResponseMaximizer U aT p (-q)).toH1.grad x)) : BlockVec d) =
      (2 : ℝ) • (((forwardDoubledField U a p q u).eval x -
            (forwardDoubledField U aT p q v).eval x) +
          skewCorrectionField U a aT p q v x) := by
  have hAB : matTranspose (a.toCoeffField x) - matTranspose (aT.toCoeffField x)
      = aT.toCoeffField x - a.toCoeffField x := by
    have h1 : matTranspose (aT.toCoeffField x) - matTranspose (a.toCoeffField x)
        = a.toCoeffField x - aT.toCoeffField x := by
      rw [← matTranspose_sub_mat]
      simpa [neg_sub] using hskew x
    have h2 := congrArg Neg.neg h1
    simpa [neg_sub] using h2
  simp only [Book.Ch02.DoubledField.eval, skewCorrectionField]
  rw [forwardDoubledField_potential, forwardDoubledField_potential,
    forwardDoubledField_flux, forwardDoubledField_flux]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_sub, Prod.fst_add, Prod.smul_fst, add_zero]
    rw [smul_sub]
    simp only [two_smul_half]
    abel
  · simp only [Prod.snd_sub, Prod.snd_add, Prod.smul_snd]
    have hAvec : ∀ w : Vec d, matVecMul (matTranspose (a.toCoeffField x)) w
        = matVecMul (matTranspose (aT.toCoeffField x)) w +
            matVecMul (aT.toCoeffField x - a.toCoeffField x) w := by
      intro w
      have hmat : matTranspose (a.toCoeffField x)
          = matTranspose (aT.toCoeffField x) + (aT.toCoeffField x - a.toCoeffField x) := by
        rw [← hAB]
        abel
      rw [hmat, matVecMul_add_mat]
    simp only [matVecMul_sub_vec, hAvec, matVecMul_smul, matVecMul_add, matVecMul_sub_mat]
    rw [smul_add, smul_sub]
    simp only [two_smul_half]
    abel

end

end SuperdiffusionCLT.Section2.Localization
