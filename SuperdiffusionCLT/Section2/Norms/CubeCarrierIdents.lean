/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Norms.CubeLp
public import SuperdiffusionCLT.Section2.Norms.NegativeHat
public import Homogenization.Geometry.CubeMeasure

/-!
# The carrier identifications of the volume-normalized cube norms

The paper's notation section fixes the reading of the
underlined norms of the estimates block: `‖f‖_{L̲^p(U)} := (⨍_U |f(x)|^p dx)^{1/p}`,
with `|f(x)|` the operator norm of the matrix value and `⨍` the
normalized volume average over the triadic cube. This module supplies the two
deterministic identifications that turn that reading into the `eLpNorm`
carrier `cubeLpENorm`:

* the pointwise coincidence of the `Mat d` norm (and its `ℝ≥0∞`-valued enorm)
  with `Book.Ch02.matrixOperatorNorm` of the CoarseGraining library, and
* the equality of the normalized `L^p` enorm of a matrix field on a cube with
  the `p`-th root of the normalized volume average of the `p`-th power of the
  pointwise operator norm, which is the carrier of the moment displays
  (`volumeAverage (cubeSet Q) (fun x => ‖M x‖ ^ p)`).

Under `open scoped Matrix.Norms.L2Operator` the only `NormedAddCommGroup (Mat d)`
instance in scope is the `ℓ²` operator norm, so the size used by `cubeLpENorm`
cannot silently drift; see the docstring of
`Frozen.Section2.streamIncrement_scale_estimates`.

## Main results

* `norm_eq_matrixOperatorNorm`, `enorm_matrixOperatorNorm`: the pointwise
  coincidences.
* `integrableOn_norm_rpow_of_continuous`,
  `integrable_norm_rpow_of_continuous`: the integrability of the `p`-th power
  of the pointwise size of a continuous matrix field on the cube.
* `eLpNorm_eq_ofReal_rpow_volumeAverage`: the volume-average identification for
  an abstract normed group.
* `cubeLpENorm_eq_rpow_volumeAverage_matrixOperatorNorm`: the carrier
  identification for matrix fields on a cube.
-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Section2
namespace Norms

open Homogenization
open Homogenization.Book.Ch02
open MeasureTheory
open scoped ENNReal
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## The pointwise coincidences -/

/-- **The pointwise norm coincidence.** Under
`open scoped Matrix.Norms.L2Operator` the only `NormedAddCommGroup (Mat d)`
instance in scope has norm `Book.Ch02.matrixOperatorNorm`; the
identification is definitional. -/
theorem norm_eq_matrixOperatorNorm (A : Mat d) :
    (‖A‖ : ℝ) = Book.Ch02.matrixOperatorNorm A :=
  rfl

/-- **The pointwise enorm coincidence.** The `ℝ≥0∞`-valued enorm of a matrix is
the `ofReal` of the matrix operator norm. Together with
`norm_eq_matrixOperatorNorm` this is the pointwise clause of the
`L^p` / `L∞` statements. -/
theorem enorm_matrixOperatorNorm (M : Vec d → Mat d) (x : Vec d) :
    ‖M x‖ₑ = ENNReal.ofReal (Book.Ch02.matrixOperatorNorm (M x)) :=
  (ofReal_norm (M x)).symm

/-! ## The volume-average identification -/

/-- The normalized volume average of a pointwise nonnegative field is
nonnegative. -/
theorem volumeAverage_cubeSet_nonneg (Q : TriadicCube d) {g : Vec d → ℝ}
    (hgnn : ∀ x : Vec d, 0 ≤ g x) : 0 ≤ volumeAverage (cubeSet Q) g := by
  rw [volumeAverage]
  exact mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) (integral_nonneg fun x => hgnn x)

/-- The `p`-th power of the pointwise operator norm of a continuous matrix
field is integrable on the volume restricted to the half-open cube: the
continuous pointwise size is bounded on the closed ball around the cube
center. -/
theorem integrableOn_norm_rpow_of_continuous (Q : TriadicCube d) {p : ℝ}
    (hp : (1 : ℝ) ≤ p) (M : Vec d → Mat d) (hM : Continuous M) :
    Integrable (fun x : Vec d => ‖M x‖ ^ p) (volume.restrict (cubeSet Q)) := by
  have hp0 : (0 : ℝ) ≤ p := zero_le_one.trans hp
  have hgc : Continuous (fun x : Vec d => ‖M x‖ ^ p) :=
    (hM.norm).rpow_const fun _ => Or.inr hp0
  have hgm : AEStronglyMeasurable (fun x : Vec d => ‖M x‖ ^ p)
      (volume.restrict (cubeSet Q)) := hgc.aestronglyMeasurable
  have hcomp : IsCompact (Metric.closedBall (cubeCenter Q) (cubeRadius Q)) :=
    isCompact_closedBall _ _
  obtain ⟨x₀, hx₀mem, hx₀max⟩ := hcomp.exists_isMaxOn
    ⟨cubeCenter Q, Metric.mem_closedBall_self (cubeRadius_nonneg Q)⟩
    (f := fun x : Vec d => ‖M x‖) (hM.norm).continuousOn
  have hCnn : 0 ≤ ‖M x₀‖ := norm_nonneg _
  have hfin : IsFiniteMeasure (volume.restrict (cubeSet Q)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact volume_cubeSet_lt_top Q⟩
  refine Integrable.mono' (integrable_const (‖M x₀‖ ^ p)) hgm ?_
  filter_upwards [ae_restrict_mem (measurableSet_cubeSet Q)] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) p)]
  exact Real.rpow_le_rpow (norm_nonneg _)
    (hx₀max (cubeSet_subset_closedBall Q hx)) hp0

/-- The `p`-th power of the pointwise operator norm of a continuous matrix
field is integrable on the normalized cube measure. -/
theorem integrable_norm_rpow_of_continuous (Q : TriadicCube d) {p : ℝ}
    (hp : (1 : ℝ) ≤ p) (M : Vec d → Mat d) (hM : Continuous M) :
    Integrable (fun x : Vec d => ‖M x‖ ^ p) (normalizedCubeMeasure Q) := by
  have hint := integrableOn_norm_rpow_of_continuous Q hp M hM
  have hctop : (ENNReal.ofReal ((cubeVolume Q)⁻¹)) ≠ ∞ :=
    ENNReal.ofReal_ne_top
  have hsm : normalizedCubeMeasure Q =
      ENNReal.ofReal ((cubeVolume Q)⁻¹) • (volume.restrict (cubeSet Q)) := rfl
  rw [hsm]
  exact hint.smul_measure hctop

/-- **The volume-average identification.** The normalized `L^p` enorm of a
field whose pointwise size carries the norm `g` is the `p`-th root of the
normalized volume average of `g`:
`‖f‖_{L̲^p(U)} := (⨍_U |f(x)|^p dx)^{1/p}`. This is the bridge between the
`eLpNorm` carrier `cubeLpENorm` and the carrier
of the moment displays, `volumeAverage (cubeSet Q) (fun x => g x)`. -/
theorem eLpNorm_eq_ofReal_rpow_volumeAverage {E : Type*} [NormedAddCommGroup E]
    (Q : TriadicCube d) {p : ℝ} (hp : (1 : ℝ) ≤ p) (f : Vec d → E) (g : Vec d → ℝ)
    (hf : MeasureTheory.AEStronglyMeasurable f (normalizedCubeMeasure Q))
    (hpow : ∀ x : Vec d, ‖f x‖ₑ ^ p = ENNReal.ofReal (g x))
    (hgnn : ∀ x : Vec d, 0 ≤ g x)
    (hgi : Integrable g (normalizedCubeMeasure Q)) :
    eLpNorm f (ENNReal.ofReal p) (normalizedCubeMeasure Q) =
      ENNReal.ofReal ((volumeAverage (cubeSet Q) g) ^ ((p : ℝ)⁻¹)) := by
  have hp0 : (0 : ℝ) ≤ p := zero_le_one.trans hp
  have hqne : ENNReal.ofReal p ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.2 (lt_of_lt_of_le zero_lt_one hp)
  have hqtop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hqtoReal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0
  have havg : ∫ x, g x ∂(normalizedCubeMeasure Q) = volumeAverage (cubeSet Q) g := by
    rw [normalizedCubeMeasure, integral_smul_measure, smul_eq_mul,
      ENNReal.toReal_ofReal (inv_nonneg.2 (cubeVolume_nonneg Q)), cubeMeasure,
      volumeAverage, volume_cubeSet_toReal Q]
  have hl : ∫⁻ x, ‖f x‖ₑ ^ p ∂(normalizedCubeMeasure Q) =
      ENNReal.ofReal (volumeAverage (cubeSet Q) g) := by
    rw [lintegral_congr hpow, ← ofReal_integral_eq_lintegral_ofReal hgi
      (Filter.Eventually.of_forall hgnn), havg]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hqne hqtop hf, hqtoReal, hl,
    ENNReal.ofReal_rpow_of_nonneg (volumeAverage_cubeSet_nonneg Q hgnn)
      (div_nonneg zero_le_one hp0), inv_eq_one_div]

/-- **The carrier identification.** The normalized `L^p` enorm of a matrix
field on a triadic cube is the `p`-th root of the normalized volume average of
the `p`-th power of the pointwise operator norm:

`cubeLpENorm Q (ofReal p) M = ofReal ((volumeAverage (cubeSet Q) (‖M ·‖ ^ p))^{1/p})`.

This is the deterministic bridge between the carrier
`cubeLpENorm Q (ofReal p) M` of the statements and the carrier of the displays
(`volumeAverage (cubeSet Q) (fun x => ‖M x‖ ^ p)`). Continuity of `M` supplies
the integrability of the pointwise size; the fields in the statements are
continuous, so the hypothesis is available there. The pointwise size is read in
the `ℓ²` operator norm: `‖M x‖ = Book.Ch02.matrixOperatorNorm (M x)` is
definitional (`norm_eq_matrixOperatorNorm`). -/
theorem cubeLpENorm_eq_rpow_volumeAverage_matrixOperatorNorm
    (Q : TriadicCube d) {p : ℝ} (hp : (1 : ℝ) ≤ p) (M : Vec d → Mat d)
    (hM : Continuous M) :
    cubeLpENorm Q (ENNReal.ofReal p) M =
      ENNReal.ofReal ((volumeAverage (cubeSet Q)
        (fun x => ‖M x‖ ^ p)) ^ ((p : ℝ)⁻¹)) := by
  have hp0 : (0 : ℝ) ≤ p := zero_le_one.trans hp
  refine eLpNorm_eq_ofReal_rpow_volumeAverage Q hp M (fun x => ‖M x‖ ^ p) ?_ ?_ ?_ ?_
  · exact hM.aestronglyMeasurable
  · intro x
    show ‖M x‖ₑ ^ p = ENNReal.ofReal (‖M x‖ ^ p)
    rw [enorm_matrixOperatorNorm M x, ENNReal.ofReal_rpow_of_nonneg
      (matrixOperatorNorm_nonneg (M x)) hp0]
    exact congrArg ENNReal.ofReal (congrArg (fun r : ℝ => r ^ p)
      (norm_eq_matrixOperatorNorm (M x)))
  · intro x
    exact Real.rpow_nonneg (norm_nonneg _) p
  · exact integrable_norm_rpow_of_continuous Q hp M hM

end

end Norms
end Section2
end SuperdiffusionCLT