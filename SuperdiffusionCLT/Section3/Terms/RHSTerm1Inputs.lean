/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm1Steps
public import SuperdiffusionCLT.Section2.Estimates.Stream.ShellDerivLargeCubeB

/-!
# The Step 1 displays of `l.RHS.term1`

`RHSTerm1Steps` proves the two step theorems of the proof of `l.RHS.term1` in the
paper, carrying the printed displays of their proofs as hypotheses.  This file
and its companions supply those hypotheses.

The three displays carried by the first decomposition step are

* `E[‖a_ℓ(∇u_n − ∇ũ_n)‖²_{L̲²(cu_m)}] ≤ Cν^{-3}ℓ²3^{-(ℓ-n)}σ` (`hFluxL2Sq`);
* `|q̃ − q|² ≤ Cν^{-3}ℓ²3^{-(ℓ-n)}σ` (`hqSq`);
* `E[‖∇w‖²_{L̲²(cu_m)}] ≤ C h |p|²` (`hGradWL2Sq`), which `RHSTerm1Steps` already
  derives from the first conjunct of `l.w.basic.regbounds`; it is not restated here.

## What is derived and what is carried

The printed derivation of the first display runs as follows:
the translated localization estimate `e.localization.minimizers.applied` on
`z' + cu_n`, the annealed stationarity identity that turns
`E[‖·‖²_{L̲²(cu_m)}]` into the `avsum` over the `3^n`-lattice of `cu_m`, the
Cauchy-Schwarz splitting of the product `a_ℓ ⊗ ∇(k_{L'} − k_ℓ)`, and finally
the two annealed moments `E[‖a_ℓ‖⁴_{L^∞(cu_ℓ)}]^{1/2}` and
`E[‖∇(k_{L'} − k_ℓ)‖²_{L^∞(z + cu_n)}]^{1/2}`.

Of these, the **last factor** is proved: it follows from the large-cube
shell-derivative bound of the `Section2` stream estimates, which turns its `Γ₂` tail into
the printed second moment `C 3^{-a} (1 + (m - a))^{1/2}` through the moment
bound of `l.moments.gamma.psi`.  This is the display `e.nabla.kmn.Linfty` on the
large cube.

Everything above it is carried, each as one explicit hypothesis in the exact
printed shape:

* `hLocalized`: the combination of `e.localization.minimizers.applied` with the
  annealed `avsum` stationarity identity and the Cauchy-Schwarz splitting of
  the proof.  The *translated* instance of `Frozen.Section2.cutoff_localization`
  on `z' + cu_n` cannot be reached from the available carriers: the glued-field
  development gives the lattice-translation
  covariance only for the coarse matrix
  (`sigmaStarInvCoarse_openCubeSet_coefficientCutoff`,
  `integral_sigmaStarInvCoarse_openCubeSet_eq`), not for a cube `L²` norm of the
  maximizer gradient, which is not jointly measurable in the sample
  (`GluedField.qVector_apply` records the same obstruction).
* `hMoment`: the annealed fourth `L^∞` moment of `a_ℓ` in the same proof.
* `hDerivHigh`: the shells above the cube scale.  The large-cube route
  is available only for shells `k ≤ m`, and `L' = m + 2a` exceeds `m`; the
  shells in `(m, L']` are the small-cube regime `cu_m ⊆ cu_k`, for which no
  bound on the *raw derivative* norm is proved here.

## The Jensen step of the second display

The paper derives `|q̃ − q|² ≤ Cν^{-3}ℓ²3^{-(ℓ-n)}σ` from the first display by
"we therefore also get", that is by Jensen and Cauchy-Schwarz applied to
`q̃ − q = E[(a_ℓ(∇ũ_n − ∇u_n))_{cu_ℓ}]` (`e.Sec3.p.q.def`, whose
cube is `cu_ℓ`).  That passage is `hJensen`; the `cu_ℓ` instance of the first
display is obtained from the same bound, at the cube scale `r = ℓ`.

## References

The paper: `l.RHS.term1`, `e.localization.minimizers.applied`,
`e.nabla.kmn.Linfty`, and the norm conventions of Section 1.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Estimates.Stream
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The volume-normalized `H̲¹` norm of a vector field on a cube -/

/-- **`‖F‖_{H̲¹(Q)}`** for a vector field `F` with Jacobian `J`: the volume-normalized
first-order norm

`‖F‖_{H̲¹(Q)} = |Q|^{-1/d} ‖F‖_{L̲²(Q)} + ‖J‖_{L̲²(Q)}`,

with `|Q|^{-1/d} = 3^{-scale Q}` on a triadic cube and with the Frobenius
reading `HilbertMat.ofMat` of the Jacobian.  The printed definition takes the
`ℓ²` combination of the two terms; the sum used here differs from it by a
factor in `[1, √2]` and is the shape in which the two printed displays that use
it (in Step 2 of the proof of `l.RHS.term1`) are stated.

This is the carrier of the free `H̲¹` norm binder of the second flux decomposition
step in `RHSTerm1Steps`: the `ResponseFields` norms module
gives the normalized `L̲^q` norms and the order-one hatted `Ĥ̲^{-1}` seminorm
of a vector field, but no order-one positive `H̲¹` norm. -/
def vecCubeH1ENorm (Q : TriadicCube d) (F : Vec d → Vec d)
    (J : Vec d → Mat d) : ℝ≥0∞ :=
  ENNReal.ofReal ((3 : ℝ) ^ (-((Q.scale : ℝ)))) * vecCubeLpENorm Q 2 F +
    Section2.Norms.cubeLpENorm Q 2 (fun x => HilbertMat.ofMat (J x))

theorem vecCubeH1ENorm_eq (Q : TriadicCube d) (F : Vec d → Vec d)
    (J : Vec d → Mat d) :
    vecCubeH1ENorm Q F J =
      ENNReal.ofReal ((3 : ℝ) ^ (-((Q.scale : ℝ)))) * vecCubeLpENorm Q 2 F +
        Section2.Norms.cubeLpENorm Q 2 (fun x => HilbertMat.ofMat (J x)) :=
  rfl

/-! ## `e.nabla.kmn.Linfty` on the large cube -/

/-- **`‖∇(k_b − k_a)‖_{L^∞(cu_m)}`**, the quantity of
`e.nabla.kmn.Linfty` and of the right-hand side
of `Frozen.Section2.cutoff_localization`: the volume
normalized `L^∞(cu_m)` norm of the exact induced derivative norm of the
reconstructed derivative `∇(k_b − k_a) = ∑_{k ∈ (a, b]} ∇ j_k`. -/
def shellDerivCubeLinftyENorm (a b m : ℕ) (omega : ShellSeq d) : ℝ≥0∞ :=
  Section2.Norms.cubeLpENorm (originCube d (m : ℤ)) ∞
    (fun x : Vec d => ShellField.matrixDerivativeNorm
      (∑ k ∈ Finset.Ioc a b, ShellField.deriv (omega k) x))

/-- The explicit constant of the annealed second moment of
`shellDerivCubeLinftyENorm`: the `Γ₂` amplitude constant of the
finite-sum envelope times the square root of the printed moment constant
`1 + γ(2)` of `l.moments.gamma.psi`. -/
def shellDerivLargeCubeMomentConst (d : ℕ) : ℝ :=
  shellDerivLargeCubeSumConst d * Real.sqrt (1 + Real.Gamma 2)

theorem shellDerivLargeCubeMomentConst_pos
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P) :
    0 < shellDerivLargeCubeMomentConst d := by
  have h1 : 0 < shellDerivLargeCubeSumConst d :=
    shellDerivLargeCubeSumConst_pos hPrefix
  have hG : (0 : ℝ) < Real.Gamma 2 := Real.Gamma_pos_of_pos (by norm_num)
  have h2 : 0 < Real.sqrt (1 + Real.Gamma 2) := Real.sqrt_pos.2 (by linarith only [hG])
  exact mul_pos h1 h2

/-! ## The annealed `L^∞` moment carrier of the cutoff coefficient -/

/-- **`‖a_L‖_{L^∞(cu_r)}`**: the volume-normalized `L^∞(cu_r)` norm of the Euclidean
operator norm of the infrared cutoff coefficient `a_L = ν Id + k_L`. -/
def coeffCubeLinftyENorm (nu : ℝ) (L r : ℕ) (omega : ShellSeq d) : ℝ≥0∞ :=
  Section2.Norms.cubeLpENorm (originCube d (r : ℤ)) ∞
    (fun x : Vec d =>
      matrixOperatorNorm ((coefficientCutoff nu omega L).toCoeffField x))

/-! ## The scale bookkeeping of the closing arithmetic -/

/-! ## The first display of Step 1 -/

/-! ## The second display of Step 1 -/

end

end SuperdiffusionCLT.Section3.Terms
