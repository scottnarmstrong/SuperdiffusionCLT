/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Norms.CubeLp
public import SuperdiffusionCLT.Section2.Norms.Gagliardo

/-!
# The normalized fractional norm `‖·‖_{H̲^s(cu_l)}`

The paper's display `e.kmn.Hs` uses
`‖k_m − k_n‖_{H̲^s(cu_l)}`, and its proof uses it in the
form

> `‖j_k‖_{H̲^s(cu_l)} ≤ (3^{-2sl} ‖j_k‖²_{L̲²(cu_l)} + [j_k]²_{H̲^s(cu_l)})^{1/2}`.

The reading used in this repository is:

> `‖f‖²_{H̲^s(cu_l)} = (3^{-sl} ‖f‖_{L̲²(cu_l)})² + [f]²_{H̲^s(cu_l)}`,

the pattern of the printed `W̲^{1,p}` norm with the volume
weight `|U|^{-s/d} = 3^{-sl}`.

## Honesty of the value

**The value lies in `ℝ≥0∞` and `⊤` is a legitimate outcome.** Both summands are
`ℝ≥0∞`-valued (`cubeLpENorm`, `cubeEuclideanGagliardoESeminorm`), and the sum
and square root are taken with `ENNReal` arithmetic, so an infinite `L̲²` part
or an infinite Gagliardo part is carried through instead of being silently
dropped by a real-valued conversion.

## Main definitions

* `cubeHsWeight`: the scale weight `3^{-sl}` of clause (b).
* `cubeHsENorm`: `‖f‖_{H̲^s(Q)}`.

## Main results

* `cubeHsENorm_weighted_le`, `cubeHsENorm_gagliardo_le`: each of the two
  printed pieces is dominated by the norm.
* `cubeHsENorm_le_add`: the norm is dominated by the sum of the two pieces;
  this is the direction used to sum over shells.
* `cubeHsENorm_zero`.
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

/-- The weight `|Q|^{-s/d} = 3^{-s l}` attached to the `L̲²` part of the
normalized fractional norm, `Q` of scale `l`. -/
noncomputable def cubeHsWeight (Q : TriadicCube d) (s : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (cubeScaleFactor Q ^ (-s))

/-- `‖f‖_{H̲^s(Q)}`:
the square root of `(3^{-sl} ‖f‖_{L̲²(Q)})² + [f]²_{H̲^s(Q)}`. -/
noncomputable def cubeHsENorm (Q : TriadicCube d) (s : ℝ) (f : Vec d → E) :
    ℝ≥0∞ :=
  ((cubeHsWeight Q s * cubeLpENorm Q 2 f) ^ (2 : ℝ) +
      (cubeEuclideanGagliardoESeminorm Q s 2 f) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)

private theorem rpow_two_eq_sq (a : ℝ≥0∞) : a ^ (2 : ℝ) = a ^ (2 : ℕ) := by
  rw [← ENNReal.rpow_natCast a 2]
  norm_num

private theorem sq_rpow_half (a : ℝ≥0∞) : (a ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) = a := by
  rw [← ENNReal.rpow_mul]
  norm_num

private theorem rpow_half_mono {a b : ℝ≥0∞} (h : a ≤ b) :
    a ^ ((1 : ℝ) / 2) ≤ b ^ ((1 : ℝ) / 2) :=
  ENNReal.rpow_le_rpow h (by norm_num)

private theorem sq_add_sq_rpow_half_le (a b : ℝ≥0∞) :
    (a ^ (2 : ℝ) + b ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) ≤ a + b := by
  have hsum : a ^ (2 : ℝ) + b ^ (2 : ℝ) ≤ (a + b) ^ (2 : ℝ) := by
    rw [rpow_two_eq_sq, rpow_two_eq_sq, rpow_two_eq_sq]
    have hexpand : (a + b) ^ (2 : ℕ) = a ^ (2 : ℕ) + (a * b + (b * a + b ^ (2 : ℕ))) := by
      ring
    rw [hexpand]
    have h1 : b ^ (2 : ℕ) ≤ b * a + b ^ (2 : ℕ) := le_add_self
    have h2 : b * a + b ^ (2 : ℕ) ≤ a * b + (b * a + b ^ (2 : ℕ)) := le_add_self
    exact add_le_add (le_refl (a ^ (2 : ℕ))) (h1.trans h2)
  exact (rpow_half_mono hsum).trans (le_of_eq (sq_rpow_half _))

theorem cubeHsENorm_weighted_le (Q : TriadicCube d) (s : ℝ) (f : Vec d → E) :
    cubeHsWeight Q s * cubeLpENorm Q 2 f ≤ cubeHsENorm Q s f :=
  (le_of_eq (sq_rpow_half _).symm).trans (rpow_half_mono le_self_add)

theorem cubeHsENorm_gagliardo_le (Q : TriadicCube d) (s : ℝ) (f : Vec d → E) :
    cubeEuclideanGagliardoESeminorm Q s 2 f ≤ cubeHsENorm Q s f :=
  (le_of_eq (sq_rpow_half _).symm).trans (rpow_half_mono le_add_self)

/-- The norm is at most the sum of its two pieces; this is the form in which
the printed proof sums the shell contributions. -/
theorem cubeHsENorm_le_add (Q : TriadicCube d) (s : ℝ) (f : Vec d → E) :
    cubeHsENorm Q s f ≤
      cubeHsWeight Q s * cubeLpENorm Q 2 f +
        cubeEuclideanGagliardoESeminorm Q s 2 f :=
  sq_add_sq_rpow_half_le _ _

@[simp] theorem cubeHsENorm_zero (Q : TriadicCube d) (s : ℝ) :
    cubeHsENorm Q s (0 : Vec d → E) = 0 := by
  rw [cubeHsENorm, cubeLpENorm_zero, cubeEuclideanGagliardoESeminorm_zero,
    mul_zero]
  simp [ENNReal.zero_rpow_of_pos]

/-! ## Measurability of the Gagliardo kernel -/

instance instSFiniteCubeMeasure (Q : TriadicCube d) : SFinite (cubeMeasure Q) := by
  unfold cubeMeasure
  infer_instance

private theorem aestronglyMeasurable_cubeMeasure_of_normalized {Q : TriadicCube d}
    {E : Type*} [NormedAddCommGroup E] {f : Vec d → E}
    (hf : AEStronglyMeasurable f (normalizedCubeMeasure Q)) :
    AEStronglyMeasurable f (cubeMeasure Q) := by
  obtain ⟨g, hg, hfg⟩ := hf
  refine ⟨g, hg, ?_⟩
  have hc : ENNReal.ofReal (cubeVolume Q)⁻¹ ≠ 0 := by
    simp [(cubeVolume_pos Q)]
  have hsm : normalizedCubeMeasure Q
      = ENNReal.ofReal (cubeVolume Q)⁻¹ • cubeMeasure Q := rfl
  rw [hsm] at hfg
  exact (Measure.ae_ennreal_smul_measure_iff hc).1 hfg

/-- The Gagliardo kernel of an a.e. strongly measurable field is a.e. strongly
measurable for the Gagliardo product measure. -/
theorem aestronglyMeasurable_euclideanGagliardoKernel {Q : TriadicCube d} {s : ℝ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Vec d → E}
    (hf : AEStronglyMeasurable f (normalizedCubeMeasure Q)) :
    AEStronglyMeasurable (euclideanGagliardoKernel s 2 f)
      (Gagliardo.gagliardoCubeMeasure Q) := by
  have hsf : SFinite (cubeMeasure Q) := by
    unfold cubeMeasure
    infer_instance
  have hmu : Gagliardo.gagliardoCubeMeasure Q
      = (normalizedCubeMeasure Q).prod (cubeMeasure Q) := rfl
  have h1 : AEStronglyMeasurable (fun z : Vec d × Vec d => f z.1)
      (Gagliardo.gagliardoCubeMeasure Q) := by
    rw [hmu]
    exact hf.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have h2 : AEStronglyMeasurable (fun z : Vec d × Vec d => f z.2)
      (Gagliardo.gagliardoCubeMeasure Q) := by
    rw [hmu]
    exact (aestronglyMeasurable_cubeMeasure_of_normalized hf).comp_quasiMeasurePreserving
      Measure.quasiMeasurePreserving_snd
  have h3 : Measurable (fun z : Vec d × Vec d =>
      euclideanDist z.1 z.2 ^ (-(s + (d : ℝ) / (2 : ℝ≥0∞).toReal))) := by
    unfold euclideanDist euclideanNorm vecNormSq vecDot
    fun_prop
  exact (h3.aestronglyMeasurable).smul (h1.sub h2)

end

end Norms
end Section2
end SuperdiffusionCLT
