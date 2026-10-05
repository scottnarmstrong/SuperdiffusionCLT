/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Probability.OrbitMollification
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# The orbit divergence of a stationary field, against one test function

Let `Ω := ShellSeq d` carry the measure-preserving translation action of `Vec d` and the
law `μ := P.toMeasure`.  Let `G : Ω → Vec d` be square integrable and let
`θ : Vec d → ℝ` be a test function.  The orbit divergence of `G` against `θ` is

`Ψ_θ ω = ∫ x, G (x +ᵥ ω) · ∇θ x ∂x`.

## Main results

* `orbitDivergenceField`: the orbit divergence `Ψ_θ`.
* `orbitDivergenceField_ae_sum`: `Ψ_θ` is almost everywhere the sum, over the coordinates `i`,
  of the `i`-th coordinate of the orbit mollification of `G` against the coordinate-derivative
  kernel `∂ᵢθ`.
* `memLp_orbitDivergenceField`: `Ψ_θ` is square integrable, by this decomposition and
  `memLp_mollify` (`OrbitMollification.lean`).
-/

@[expose] public section

open MeasureTheory Homogenization
open SuperdiffusionCLT.Section2.Cutoff
open scoped ENNReal InnerProductSpace

noncomputable section

namespace SuperdiffusionCLT.Probability.Stationary

variable {d : ℕ}

/-! ## The orbit divergence field -/

/-- The printed orbit divergence of a stationary field against a test function:
`Ψ_θ ω = ∫ x, G (x +ᵥ ω) · ∇θ x ∂x`. -/
def orbitDivergenceField (G : ShellSeq d → Vec d) (θ : Vec d → ℝ) (ω : ShellSeq d) : ℝ :=
  ∫ x, vecDot (G (x +ᵥ ω)) (euclideanGradient θ x)

/-! ## `Ψ_θ` as a sum of coordinates of orbit mollifications

The orbit divergence field is the sum, over the coordinates `i`, of the `i`-th coordinate of the
orbit mollification of the field against the coordinate-derivative kernel `∂ᵢθ`.  This is what
puts `Ψ_θ` in `L²(μ)`, and it is a purely pointwise identification (no Fubini). -/

/-- The Hilbert-vector realization of a `Vec d`-valued map. -/
def vecField (G : ShellSeq d → Vec d) : ShellSeq d → HilbertVec d :=
  fun ω => HilbertVec.ofVec (G ω)

/-- The coordinate-derivative kernel `∂ᵢθ` of the test function, in the project's
`basisVec` convention. -/
def coordKernel (θ : Vec d → ℝ) (i : Fin d) : Vec d → ℝ :=
  fun y => fderiv ℝ θ y (basisVec i)

@[simp] theorem vecField_apply (G : ShellSeq d → Vec d) (ω : ShellSeq d) (i : Fin d) :
    vecField G ω i = G ω i := rfl

@[simp] theorem coordKernel_apply (θ : Vec d → ℝ) (i : Fin d) (y : Vec d) :
    coordKernel θ i y = fderiv ℝ θ y (basisVec i) := rfl

/-- The dot product of a vector against a Euclidean gradient is the finite sum against the
coordinate-derivative kernels. -/
theorem vecDot_euclideanGradient_eq_sum (v : Vec d) (θ : Vec d → ℝ) (y : Vec d) :
    vecDot v (euclideanGradient θ y) = ∑ i, coordKernel θ i y * v i := by
  simp only [Homogenization.vecDot, Homogenization.euclideanGradient,
    Homogenization.euclideanCoordDeriv, coordKernel]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- Almost everywhere, the orbit divergence field is the sum of the coordinates of the orbit
mollifications of the field against the coordinate-derivative kernels. -/
theorem orbitDivergenceField_ae_sum {P : ProbabilityMeasure (ShellSeq d)}
    [VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure]
    {G : ShellSeq d → Vec d} {θ : Vec d → ℝ}
    (hGm : StronglyMeasurable (vecField G)) (hG : MemLp (vecField G) 2 P.toMeasure)
    (hθc : ∀ i, Continuous (coordKernel θ i))
    (hθi : ∀ i, Integrable (coordKernel θ i) volume) :
    orbitDivergenceField G θ
      =ᵐ[P.toMeasure] fun ω => ∑ i, mollify (coordKernel θ i) (vecField G) ω i := by
  have hpoint : ∀ᵐ ω ∂P.toMeasure, ∀ i,
      Integrable (fun y => coordKernel θ i y • vecField G (y +ᵥ ω)) volume :=
    Filter.eventually_all.mpr fun i =>
      ae_integrable_smul_realize (P := P) (hθc i) (hθi i) hGm hG
  filter_upwards [hpoint] with ω hω
  have hcoord : ∀ i, mollify (coordKernel θ i) (vecField G) ω i
      = ∫ y, coordKernel θ i y * G (y +ᵥ ω) i ∂volume := by
    intro i
    calc mollify (coordKernel θ i) (vecField G) ω i
        = (∫ y, coordKernel θ i y • vecField G (y +ᵥ ω) ∂volume) i := by rw [mollify]
      _ = ∫ y, (coordKernel θ i y • vecField G (y +ᵥ ω)) i ∂volume :=
          MeasureTheory.eval_integral_piLp
            (f := fun y => coordKernel θ i y • vecField G (y +ᵥ ω))
            (fun j => (hω i).eval_piLp j) i
      _ = ∫ y, coordKernel θ i y * G (y +ᵥ ω) i ∂volume := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          simp only [PiLp.smul_apply, smul_eq_mul, vecField_apply]
  calc orbitDivergenceField G θ ω
      = ∫ y, ∑ i, coordKernel θ i y * G (y +ᵥ ω) i ∂volume := by
        rw [orbitDivergenceField]
        exact integral_congr_ae (Filter.Eventually.of_forall fun y =>
          vecDot_euclideanGradient_eq_sum (G (y +ᵥ ω)) θ y)
    _ = ∑ i, ∫ y, coordKernel θ i y * G (y +ᵥ ω) i ∂volume :=
        integral_finsetSum Finset.univ fun i _ => by
          simpa only [PiLp.smul_apply, smul_eq_mul, vecField_apply] using (hω i).eval_piLp i
    _ = ∑ i, mollify (coordKernel θ i) (vecField G) ω i :=
        Finset.sum_congr rfl fun i _ => (hcoord i).symm

/-- **`Ψ_θ` is square integrable.**  Immediate from the coordinate decomposition and
`memLp_mollify`, with no Fubini step. -/
theorem memLp_orbitDivergenceField {P : ProbabilityMeasure (ShellSeq d)}
    [VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure]
    {G : ShellSeq d → Vec d} {θ : Vec d → ℝ}
    (hGm : StronglyMeasurable (vecField G)) (hG : MemLp (vecField G) 2 P.toMeasure)
    (hθc : ∀ i, Continuous (coordKernel θ i))
    (hθi : ∀ i, Integrable (coordKernel θ i) volume) :
    MemLp (orbitDivergenceField G θ) 2 P.toMeasure :=
  MeasureTheory.MemLp.ae_eq (orbitDivergenceField_ae_sum (P := P) hGm hG hθc hθi).symm
    (MeasureTheory.memLp_finsetSum Finset.univ fun i _ =>
      (memLp_mollify (P := P) (hθc i) (hθi i) hGm hG).eval_piLp i)

/-! ## Plumbing: coordinates of assembled vector classes -/

@[simp] theorem ofVec_apply (v : Vec d) (i : Fin d) : (HilbertVec.ofVec v) i = v i := rfl

end SuperdiffusionCLT.Probability.Stationary

end
