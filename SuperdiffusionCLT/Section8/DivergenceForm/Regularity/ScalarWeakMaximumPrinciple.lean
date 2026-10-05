/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.DivergenceForm.ScalarWeakSolution
public import Homogenization.Sobolev.Truncation.MatchedTrace
public import Homogenization.Sobolev.Foundations.PoincareZeroTrace
public import Homogenization.HighContrast.Coupled.Stampacchia.LevelEnergy

/-!
# The weak maximum principle for the divergence-form equation

Let `Y` solve `-div (a grad Y) = 0` weakly on a bounded convex domain `U` and let `q` be an
`H¹` function of `U` with `Y - q ∈ H¹₀(U)`; that is, `Y` and `q` have the same trace.  Then `Y`
is almost everywhere bounded by the pointwise bounds of `q`.

The proof is the standard energy test at the truncation `(Y - M)₊`.  Three inputs are used:

* the truncation itself, `exists_h1_max_sub_const`, whose gradient is `1_{Y > M} grad Y`;
* the matched-trace truncation `memH10_max_sub_matched`, which places `(Y - M)₊ - (q - M)₊` in
  `H¹₀(U)`; the second summand vanishes identically because `q ≤ M` everywhere, so the
  truncation is itself an admissible test function;
* the zero-trace Poincare inequality, which turns a vanishing gradient into a vanishing value.

Testing the equation against the truncation `w` gives `∫ (a grad Y) · grad w = 0`, and
`grad w = 1_{Y > M} grad Y` makes the integrand equal to `(a grad w) · grad w` pointwise, whose
integral is at least `lam ∫ |grad w|²` by ellipticity.  Hence `grad w = 0` almost everywhere,
hence `w = 0` almost everywhere, which is `Y ≤ M` almost everywhere.

No shift, no symmetry of the coefficient field and no continuity of any representative is used.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.DivergenceForm

open Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} {U : Set (Vec d)}

/-! ## Two structural facts -/

/-- **The scalar-forced weak equation is odd.**  Negating the solution negates the forcing. -/
theorem IsScalarForcedWeakSolution.neg {a : CoeffField d} {g : Vec d → ℝ} {u : H1Function U}
    (h : IsScalarForcedWeakSolution a U g u) :
    IsScalarForcedWeakSolution a U (fun x ↦ -g x) (-u) := by
  refine ⟨h.1.neg, fun phi ↦ ?_⟩
  calc
    ∫ x in U, vecDot (matVecMul (a x) ((-u).grad x))
        (phi.toH1Function.grad x) ∂volume =
        ∫ x in U, -vecDot (matVecMul (a x) (u.grad x))
          (phi.toH1Function.grad x) ∂volume := by
      refine integral_congr_ae ?_
      filter_upwards with x
      rw [H1Function.neg_grad]
      simp only [vecDot, matVecMul, Pi.neg_apply, mul_neg, neg_mul, Finset.sum_neg_distrib]
    _ = -∫ x in U, vecDot (matVecMul (a x) (u.grad x))
          (phi.toH1Function.grad x) ∂volume := integral_neg _
    _ = -∫ x in U, g x * phi.toH1Function.toFun x ∂volume := by rw [h.2 phi]
    _ = ∫ x in U, (-g x) * phi.toH1Function.toFun x ∂volume := by
      rw [← integral_neg]
      refine integral_congr_ae ?_
      filter_upwards with x
      ring

/-! ## The one-sided maximum principle -/

/-! ## The two-sided maximum principle -/

end

end SuperdiffusionCLT.Section8.DivergenceForm
