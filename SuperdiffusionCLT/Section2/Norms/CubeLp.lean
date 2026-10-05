/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Multiscale.NormalizedNorms

/-!
# The volume-normalized `L̲^q(Q)` norm, valued in `ℝ≥0∞`

The paper defines

> `‖f‖_{L̲^p(U)} := (⨍_U |f(x)|^p dx)^{1/p}`

and uses it (for example in `e.kmn.Lp`) on the triadic cubes
`cu_l`. This module supplies that norm as an `eLpNorm` against the normalized
cube measure.

## Honesty of the value

**The value lies in `ℝ≥0∞` and `⊤` is a legitimate outcome.** The upstream
real-valued `Homogenization.cubeLpNorm` is `ENNReal.toReal` of the same
quantity and therefore returns `0` on a field that is not `q`-integrable on the
cube; that junk branch makes an upper bound vacuous exactly on the fields the
estimates exclude, so this file keeps the extended-real value and exports the
identification `cubeLpENorm_toReal_eq_cubeLpNorm` for the places where
finiteness is already known.

## Main definitions

* `cubeLpENorm`: `‖f‖_{L̲^q(Q)}` in `ℝ≥0∞`.

## Main results

* `cubeLpENorm_zero`, `cubeLpENorm_neg`, `cubeLpENorm_const_smul`,
  `cubeLpENorm_add_le`: the norm laws.
* `cubeLpENorm_mono_enorm`: monotonicity under pointwise domination.
* `cubeLpENorm_le_of_forall_le`: the `L̲^q ≤ L^∞` comparison on a cube.
* `cubeLpENorm_toReal_eq_cubeLpNorm`: the bridge to the upstream real value.
-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Section2
namespace Norms

open Homogenization
open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E]

/-- `‖f‖_{L̲^q(Q)}`, the volume-normalized `L^q` norm on a triadic
cube, valued in `ℝ≥0∞`. -/
noncomputable def cubeLpENorm (Q : TriadicCube d) (q : ℝ≥0∞) (f : Vec d → E) :
    ℝ≥0∞ :=
  eLpNorm f q (normalizedCubeMeasure Q)

theorem cubeLpENorm_toReal_eq_cubeLpNorm (Q : TriadicCube d) (q : ℝ≥0∞)
    (f : Vec d → E) :
    (cubeLpENorm Q q f).toReal = cubeLpNorm Q q f :=
  rfl

@[simp] theorem cubeLpENorm_zero (Q : TriadicCube d) (q : ℝ≥0∞) :
    cubeLpENorm Q q (0 : Vec d → E) = 0 :=
  eLpNorm_zero

theorem cubeLpENorm_neg (Q : TriadicCube d) (q : ℝ≥0∞) (f : Vec d → E) :
    cubeLpENorm Q q (-f) = cubeLpENorm Q q f :=
  eLpNorm_neg _ _ _

theorem cubeLpENorm_const_smul [NormedSpace ℝ E] (Q : TriadicCube d) (q : ℝ≥0∞)
    (c : ℝ) (f : Vec d → E) :
    cubeLpENorm Q q (c • f) = ‖c‖ₑ * cubeLpENorm Q q f :=
  eLpNorm_const_smul c _ q _

theorem cubeLpENorm_add_le {Q : TriadicCube d} {q : ℝ≥0∞} {f g : Vec d → E}
    (hq : 1 ≤ q) (_hf : AEStronglyMeasurable f (normalizedCubeMeasure Q))
    (_hg : AEStronglyMeasurable g (normalizedCubeMeasure Q)) :
    cubeLpENorm Q q (f + g) ≤ cubeLpENorm Q q f + cubeLpENorm Q q g :=
  eLpNorm_add_le hq

theorem cubeLpENorm_mono_enorm {Q : TriadicCube d} {q : ℝ≥0∞}
    {F : Type*} [NormedAddCommGroup F] {f : Vec d → E} {g : Vec d → F}
    (hf : MeasureTheory.AEStronglyMeasurable f (normalizedCubeMeasure Q))
    (h : ∀ x : Vec d, ‖f x‖ ≤ ‖g x‖) :
    cubeLpENorm Q q f ≤ cubeLpENorm Q q g := by
  refine eLpNorm_mono_enorm hf (fun x => ?_)
  simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal (h x)

/-- On a cube the normalized `L^q` norm is bounded by any uniform pointwise
bound, because the normalized cube measure is a probability measure. -/
theorem cubeLpENorm_le_of_forall_le {Q : TriadicCube d} {q : ℝ≥0∞}
    {f : Vec d → E} {c : ℝ≥0∞}
    (hf : MeasureTheory.AEStronglyMeasurable f (normalizedCubeMeasure Q))
    (h : ∀ x : Vec d, ‖f x‖ₑ ≤ c) :
    cubeLpENorm Q q f ≤ c := by
  have hbound := eLpNorm_le_of_ae_enorm_bound (μ := normalizedCubeMeasure Q)
    (p := q) (f := f) (C := c) hf (Filter.Eventually.of_forall h)
  simpa [cubeLpENorm, normalizedCubeMeasure_apply_univ Q] using hbound

end

end Norms
end Section2
end SuperdiffusionCLT
