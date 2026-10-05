/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Ambient.Euclidean
public import Homogenization.Sobolev.Fractional.Definitions

/-!
# The volume-normalized Gagliardo seminorm `[f]_{W̲^{s,q}(U)}`

The paper defers the fractional Sobolev
spaces to `[AKMBook, Appendix B]` and does not repeat their definition, while
`l.ellip.k.scales.estimates` and its proof
use `[·]_{W̲^{s,q}}` and `[·]_{H̲^{s}}` freely. The reading used in this
repository is:

> `[f]_{W̲^{s,q}(U)}` is the volume-normalized Gagliardo seminorm
> `(⨍_U ∫_U |f(x) − f(y)|^q / |x − y|^{d + sq} dy dx)^{1/q}`.

This module supplies that quantity for fields with values in any real normed
space, in particular for the scalar test fields of the hatted negative
seminorm and for the matrix stream fields of `l.ellip.k.scales.estimates`.

## Honesty of the value

**Every quantity in this file is valued in `ℝ≥0∞`, and `⊤` is a legitimate
outcome**: a field whose difference quotient is not `q`-integrable over the
cube has an infinite seminorm, exactly as in the source. No real-valued
conversion, no `sSup` of a possibly unbounded set of reals, and no junk branch
occurs, so a bound on any of these quantities is a genuine bound on every
event. Consumers that want a real number must supply their own finiteness
proof.

## The distance in the kernel

The kernel uses `Homogenization.euclideanDist`, the explicit Euclidean
magnitude on `Vec d`, because the paper's `|·|` is the Euclidean norm.
This differs from the ambient sup-metric kernel of
`Homogenization.Gagliardo.gagliardoKernel`; no comparison between the two is
asserted here.

## The `⨍∫` normalization

The manuscript's outer average and inner integral are carried by the product
measure `Homogenization.Gagliardo.gagliardoCubeMeasure Q`, normalized in the
first slot and plain in the second, exactly as in the CoarseGraining library.

## Main definitions

* `euclideanGagliardoKernel`: the difference quotient
  `|x − y|^{-(s + d/q)} (f x − f y)`.
* `cubeEuclideanGagliardoESeminorm`: `[f]_{W̲^{s,q}(Q)}`, volume-normalized.

## Main results

* `cubeEuclideanGagliardoESeminorm_zero`, `cubeEuclideanGagliardoESeminorm_const_smul`,
  `cubeEuclideanGagliardoESeminorm_add_le`: the seminorm laws.
* `cubeEuclideanGagliardoESeminorm_mono_enorm`: monotonicity under pointwise
  domination of increments.
-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Section2
namespace Norms

open Homogenization
open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Gagliardo difference quotient `|x − y|^{-(s + d/q)} (f x − f y)` with
the Euclidean distance. -/
noncomputable def euclideanGagliardoKernel (s : ℝ) (q : ℝ≥0∞) (f : Vec d → E) :
    Vec d × Vec d → E :=
  fun z =>
    (euclideanDist z.1 z.2 ^ (-(s + (d : ℝ) / q.toReal))) • (f z.1 - f z.2)

theorem euclideanGagliardoKernel_apply (s : ℝ) (q : ℝ≥0∞) (f : Vec d → E)
    (z : Vec d × Vec d) :
    euclideanGagliardoKernel s q f z =
      (euclideanDist z.1 z.2 ^ (-(s + (d : ℝ) / q.toReal))) • (f z.1 - f z.2) :=
  rfl

theorem norm_euclideanGagliardoKernel (s : ℝ) (q : ℝ≥0∞) (f : Vec d → E)
    (z : Vec d × Vec d) :
    ‖euclideanGagliardoKernel s q f z‖ =
      euclideanDist z.1 z.2 ^ (-(s + (d : ℝ) / q.toReal)) * ‖f z.1 - f z.2‖ := by
  rw [euclideanGagliardoKernel_apply, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (euclideanDist_nonneg _ _) _)]

@[simp] theorem euclideanGagliardoKernel_zero (s : ℝ) (q : ℝ≥0∞) :
    euclideanGagliardoKernel s q (0 : Vec d → E) = 0 := by
  funext z
  simp [euclideanGagliardoKernel]

theorem euclideanGagliardoKernel_add (s : ℝ) (q : ℝ≥0∞) (f g : Vec d → E) :
    euclideanGagliardoKernel s q (f + g) =
      euclideanGagliardoKernel s q f + euclideanGagliardoKernel s q g := by
  funext z
  simp only [euclideanGagliardoKernel, Pi.add_apply]
  rw [show f z.1 + g z.1 - (f z.2 + g z.2)
      = (f z.1 - f z.2) + (g z.1 - g z.2) by abel, smul_add]

theorem euclideanGagliardoKernel_const_smul (s : ℝ) (q : ℝ≥0∞) (c : ℝ)
    (f : Vec d → E) :
    euclideanGagliardoKernel s q (c • f) =
      c • euclideanGagliardoKernel s q f := by
  funext z
  simp only [euclideanGagliardoKernel, Pi.smul_apply]
  rw [← smul_sub, smul_smul, smul_smul, mul_comm]

/-- `[f]_{W̲^{s,q}(Q)}`, the volume-normalized Gagliardo seminorm valued in `ℝ≥0∞`. -/
noncomputable def cubeEuclideanGagliardoESeminorm (Q : TriadicCube d) (s : ℝ)
    (q : ℝ≥0∞) (f : Vec d → E) : ℝ≥0∞ :=
  eLpNorm (euclideanGagliardoKernel s q f) q (Gagliardo.gagliardoCubeMeasure Q)

@[simp] theorem cubeEuclideanGagliardoESeminorm_zero (Q : TriadicCube d) (s : ℝ)
    (q : ℝ≥0∞) :
    cubeEuclideanGagliardoESeminorm Q s q (0 : Vec d → E) = 0 := by
  rw [cubeEuclideanGagliardoESeminorm, euclideanGagliardoKernel_zero]
  exact eLpNorm_zero

theorem cubeEuclideanGagliardoESeminorm_const_smul (Q : TriadicCube d) (s : ℝ)
    (q : ℝ≥0∞) (c : ℝ) (f : Vec d → E) :
    cubeEuclideanGagliardoESeminorm Q s q (c • f) =
      ‖c‖ₑ * cubeEuclideanGagliardoESeminorm Q s q f := by
  rw [cubeEuclideanGagliardoESeminorm, cubeEuclideanGagliardoESeminorm,
    euclideanGagliardoKernel_const_smul]
  exact eLpNorm_const_smul c _ q _

/-- The triangle inequality, in the form the sum over shells uses.
Both summands must have an almost everywhere strongly
measurable kernel; no finiteness is required. -/
theorem cubeEuclideanGagliardoESeminorm_add_le {Q : TriadicCube d} {s : ℝ}
    {q : ℝ≥0∞} {f g : Vec d → E} (hq : 1 ≤ q)
    (_hf : AEStronglyMeasurable (euclideanGagliardoKernel s q f)
      (Gagliardo.gagliardoCubeMeasure Q))
    (_hg : AEStronglyMeasurable (euclideanGagliardoKernel s q g)
      (Gagliardo.gagliardoCubeMeasure Q)) :
    cubeEuclideanGagliardoESeminorm Q s q (f + g) ≤
      cubeEuclideanGagliardoESeminorm Q s q f +
        cubeEuclideanGagliardoESeminorm Q s q g := by
  simp only [cubeEuclideanGagliardoESeminorm, euclideanGagliardoKernel_add]
  exact eLpNorm_add_le hq

/-- Monotonicity under pointwise domination of the increments. -/
theorem cubeEuclideanGagliardoESeminorm_mono_enorm {Q : TriadicCube d} {s : ℝ}
    {q : ℝ≥0∞} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Vec d → E} {g : Vec d → F}
    (hf : AEStronglyMeasurable (euclideanGagliardoKernel s q f)
      (Gagliardo.gagliardoCubeMeasure Q))
    (h : ∀ x y : Vec d, ‖f x - f y‖ ≤ ‖g x - g y‖) :
    cubeEuclideanGagliardoESeminorm Q s q f ≤
      cubeEuclideanGagliardoESeminorm Q s q g := by
  refine eLpNorm_mono_enorm hf (fun z => ?_)
  simp only [← ofReal_norm, norm_euclideanGagliardoKernel]
  exact ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left (h z.1 z.2)
      (Real.rpow_nonneg (euclideanDist_nonneg _ _) _))

end

end Norms
end Section2
end SuperdiffusionCLT
