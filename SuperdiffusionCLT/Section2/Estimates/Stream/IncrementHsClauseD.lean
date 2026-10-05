/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementHsClauseC

/-!
# The `H̲^s` clause of the estimates on the finite shell increment

This module proves clause (d) of the statement
`Frozen.Section2.streamIncrement_scale_estimates`, following the printed
proof: for `n < m ≤ l` a measurable witness `X` with

`X = O_{Γ₂}(C 3^{−sn})`  and  `‖k_m − k_n‖_{H̲^s(cu_l)} ≤ X(ω)` at every sample,

the constant `C` depending on `d` and `s` only — in particular uniform in the
cube scale `l`, in `n`, `m` and in the law `P`.

## The three pieces

* the **`L̲²` piece** `3^{−sl} ‖k_m − k_n‖_{L̲²(cu_l)}` is
  `IncrementHsClauseB.exists_witness_cubeHsWeightLtwo_finiteShellIncrement`;
* the **one-shell Gagliardo display** is assembled here from the step majorant
  and the pointwise kernel bound of `IncrementHsClauseC`, at the amplitude
  `shellGagliardoConst d s · 3^{−sk}` for the shell of index `k = r + 1`,
  uniformly in `l`;
* the **shell sum** over `k ∈ (n, m]` uses the subadditivity of the Gagliardo
  seminorm, the finite `Γ₂` triangle inequality and the geometric sum
  `sum_Ioc_shellWeight_le` of `IncrementHsClauseB`.

The two pieces are joined by `cubeHsENorm_le_add`, the direction of the printed
two-piece bound that the shell summation consumes.

## Main definitions

* `shellGagliardoConst`: the explicit constant of the one-shell display.
* `shellGagliardoWitness`: the one-shell Gagliardo witness.
* `hsClauseConst`: the explicit constant of clause (d).

## Main results

* `cubeEuclideanGagliardoESeminorm_shell_le`: at every sample the Gagliardo
  seminorm of one shell on `cu_l` is at most the one-shell witness.
* `isBigO_gammaSigma_shellGagliardoWitness`: its `Γ₂` tail, uniform in `l`.
* `exists_witness_cubeEuclideanGagliardoESeminorm_finiteShellIncrement`: the
  shell sum, the Gagliardo half of the clause.
* `hsClause_of_shellLaws`: **clause (d)**.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Estimates.Stream

open MeasureTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open scoped ENNReal
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}
variable {P : ProbabilityMeasure (ShellSeq d)}

private theorem rpow_two_eq_sq (t : ℝ) : t ^ (2 : ℝ) = t ^ (2 : ℕ) := by
  rw [← Real.rpow_natCast t 2]
  norm_num

/-! ## The Gagliardo integral against the radial majorant -/

private theorem gagliardoOscillationConst_pos (dim : ℕ) {s : ℝ} (hs : 0 < s)
    (hs1 : s < 1) : 0 < gagliardoOscillationConst dim s := by
  have hnear : (2 : ℝ) ^ (2 * s - 2) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith only [hs1])
  have hfar : (2 : ℝ) ^ (-(2 * s)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith only [hs])
  rw [gagliardoOscillationConst]
  refine mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (add_pos ?_ ?_)
  · exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
      (inv_pos.2 (by linarith only [hnear]))
  · exact inv_pos.2 (by linarith only [hfar])

private theorem gagliardoOscillationConst_nonneg (dim : ℕ) {s : ℝ} (hs : 0 < s)
    (hs1 : s < 1) : 0 ≤ gagliardoOscillationConst dim s :=
  (gagliardoOscillationConst_pos dim hs hs1).le

/-- **The Gagliardo integral of a majorant split over the two slots.** A
nonnegative integrand dominated almost everywhere by
`2 (g x + g y) · min{1, b|x−y|}² |x−y|^{−d−2s}` has its
`⨍_{cu_l} ∫_{cu_l}` integral bounded by `4 C(d,s) b^{2s}` times the normalized
average of `g`. Both slots are estimated by the same deterministic kernel
integral `lintegral_shifted_le`, the outer one after the Tonelli exchange
`lintegral_prod_symm` and the rescaling of the normalized measure. -/
private theorem lintegral_le_of_ae_radial_bound {l : ℕ} {s b : ℝ} (hs : 0 < s)
    (hs1 : s < 1) (hb : 0 < b) {g : Vec d → ℝ} (hg0 : ∀ x, 0 ≤ g x)
    (hgm : Measurable g) {F : Vec d × Vec d → ℝ≥0∞}
    (hF : ∀ᵐ z ∂(Gagliardo.gagliardoCubeMeasure (originCube d (l : ℤ))),
      F z ≤ ENNReal.ofReal (2 * (g z.1 + g z.2)) *
        radialIntegrand d s 1 b (z.1 - z.2))
    {A : ℝ}
    (hgA : ∫⁻ x, ENNReal.ofReal (g x)
        ∂(normalizedCubeMeasure (originCube d (l : ℤ))) ≤ ENNReal.ofReal A) :
    ∫⁻ z, F z ∂(Gagliardo.gagliardoCubeMeasure (originCube d (l : ℤ))) ≤
      ENNReal.ofReal (4 * (gagliardoOscillationConst d s * b ^ (2 * s)) * A) := by
  have : SFinite (cubeMeasure (originCube d (l : ℤ))) := by
    rw [cubeMeasure]; infer_instance
  have hK0 : 0 ≤ gagliardoOscillationConst d s * b ^ (2 * s) :=
    mul_nonneg (gagliardoOscillationConst_nonneg d hs hs1)
      (Real.rpow_nonneg hb.le _)
  have hradm : Measurable fun z : Vec d × Vec d =>
      radialIntegrand d s 1 b (z.1 - z.2) := measurable_radialIntegrand_sub d s 1 b
  have hgofm : Measurable fun x : Vec d => ENNReal.ofReal (g x) :=
    ENNReal.measurable_ofReal.comp hgm
  have hshift : ∀ (x : Vec d) (U : Set (Vec d)),
      ∫⁻ y in U, radialIntegrand d s 1 b (x - y) ≤
        ENNReal.ofReal (gagliardoOscillationConst d s * b ^ (2 * s)) := by
    intro x U
    have h := lintegral_shifted_le d hs hs1 one_pos hb x U
    rwa [Real.one_rpow, one_mul] at h
  have hAm : Measurable fun z : Vec d × Vec d =>
      ENNReal.ofReal (g z.1) * radialIntegrand d s 1 b (z.1 - z.2) :=
    (hgofm.comp measurable_fst).mul hradm
  have hBm : Measurable fun z : Vec d × Vec d =>
      ENNReal.ofReal (g z.2) * radialIntegrand d s 1 b (z.1 - z.2) :=
    (hgofm.comp measurable_snd).mul hradm
  have htermA :
      ∫⁻ z, ENNReal.ofReal (g z.1) * radialIntegrand d s 1 b (z.1 - z.2)
          ∂(Gagliardo.gagliardoCubeMeasure (originCube d (l : ℤ)))
        ≤ ENNReal.ofReal A *
            ENNReal.ofReal (gagliardoOscillationConst d s * b ^ (2 * s)) := by
    rw [Gagliardo.gagliardoCubeMeasure, lintegral_prod _ hAm.aemeasurable]
    have hinner : ∀ x : Vec d,
        ∫⁻ y, ENNReal.ofReal (g x) * radialIntegrand d s 1 b (x - y)
            ∂(cubeMeasure (originCube d (l : ℤ)))
          ≤ ENNReal.ofReal (g x) *
              ENNReal.ofReal (gagliardoOscillationConst d s * b ^ (2 * s)) := by
      intro x
      have hy : Measurable fun y : Vec d => radialIntegrand d s 1 b (x - y) := by
        show Measurable fun y : Vec d =>
          ENNReal.ofReal
            (min 1 (b * ‖x - y‖) ^ 2 * ‖x - y‖ ^ (-(2 * s + (d : ℝ))))
        fun_prop
      rw [lintegral_const_mul _ hy, cubeMeasure]
      exact mul_le_mul_right (hshift x _) _
    calc ∫⁻ x, ∫⁻ y, ENNReal.ofReal (g x) * radialIntegrand d s 1 b (x - y)
            ∂(cubeMeasure (originCube d (l : ℤ)))
            ∂(normalizedCubeMeasure (originCube d (l : ℤ)))
        ≤ ∫⁻ x, ENNReal.ofReal (g x) *
              ENNReal.ofReal (gagliardoOscillationConst d s * b ^ (2 * s))
              ∂(normalizedCubeMeasure (originCube d (l : ℤ))) :=
          lintegral_mono hinner
      _ = (∫⁻ x, ENNReal.ofReal (g x)
              ∂(normalizedCubeMeasure (originCube d (l : ℤ)))) *
            ENNReal.ofReal (gagliardoOscillationConst d s * b ^ (2 * s)) :=
          lintegral_mul_const _ hgofm
      _ ≤ ENNReal.ofReal A *
            ENNReal.ofReal (gagliardoOscillationConst d s * b ^ (2 * s)) :=
          mul_le_mul_left hgA _
  have htermB :
      ∫⁻ z, ENNReal.ofReal (g z.2) * radialIntegrand d s 1 b (z.1 - z.2)
          ∂(Gagliardo.gagliardoCubeMeasure (originCube d (l : ℤ)))
        ≤ ENNReal.ofReal A *
            ENNReal.ofReal (gagliardoOscillationConst d s * b ^ (2 * s)) := by
    rw [Gagliardo.gagliardoCubeMeasure, lintegral_prod_symm _ hBm.aemeasurable]
    have hinner : ∀ y : Vec d,
        ∫⁻ x, ENNReal.ofReal (g y) * radialIntegrand d s 1 b (x - y)
            ∂(normalizedCubeMeasure (originCube d (l : ℤ)))
          ≤ ENNReal.ofReal (g y) *
              (ENNReal.ofReal (cubeVolume (originCube d (l : ℤ)))⁻¹ *
                ENNReal.ofReal (gagliardoOscillationConst d s * b ^ (2 * s))) := by
      intro y
      have hxm : Measurable fun x : Vec d => radialIntegrand d s 1 b (x - y) := by
        show Measurable fun x : Vec d =>
          ENNReal.ofReal
            (min 1 (b * ‖x - y‖) ^ 2 * ‖x - y‖ ^ (-(2 * s + (d : ℝ))))
        fun_prop
      rw [lintegral_const_mul _ hxm]
      refine mul_le_mul_right ?_ _
      rw [normalizedCubeMeasure, lintegral_smul_measure, cubeMeasure]
      refine mul_le_mul_right ?_ _
      have hcomm : ∫⁻ x in cubeSet (originCube d (l : ℤ)),
            radialIntegrand d s 1 b (x - y)
          = ∫⁻ x in cubeSet (originCube d (l : ℤ)),
            radialIntegrand d s 1 b (y - x) :=
        lintegral_congr fun x => radialIntegrand_comm d s 1 b x y
      rw [hcomm]
      exact hshift y _
    calc ∫⁻ y, ∫⁻ x, ENNReal.ofReal (g y) * radialIntegrand d s 1 b (x - y)
            ∂(normalizedCubeMeasure (originCube d (l : ℤ)))
            ∂(cubeMeasure (originCube d (l : ℤ)))
        ≤ ∫⁻ y, ENNReal.ofReal (g y) *
              (ENNReal.ofReal (cubeVolume (originCube d (l : ℤ)))⁻¹ *
                ENNReal.ofReal (gagliardoOscillationConst d s * b ^ (2 * s)))
              ∂(cubeMeasure (originCube d (l : ℤ))) := lintegral_mono hinner
      _ = ((ENNReal.ofReal (cubeVolume (originCube d (l : ℤ)))⁻¹) *
            ∫⁻ y, ENNReal.ofReal (g y) ∂(cubeMeasure (originCube d (l : ℤ)))) *
            ENNReal.ofReal (gagliardoOscillationConst d s * b ^ (2 * s)) := by
          rw [← lintegral_const_mul _ hgofm, ← lintegral_mul_const _
            (hgofm.const_mul _)]
          exact lintegral_congr fun y => by ring
      _ = (∫⁻ y, ENNReal.ofReal (g y)
              ∂(normalizedCubeMeasure (originCube d (l : ℤ)))) *
            ENNReal.ofReal (gagliardoOscillationConst d s * b ^ (2 * s)) := by
          rw [normalizedCubeMeasure, lintegral_smul_measure, smul_eq_mul]
      _ ≤ ENNReal.ofReal A *
            ENNReal.ofReal (gagliardoOscillationConst d s * b ^ (2 * s)) :=
          mul_le_mul_left hgA _
  have hsplit : ∀ z : Vec d × Vec d,
      ENNReal.ofReal (2 * (g z.1 + g z.2)) * radialIntegrand d s 1 b (z.1 - z.2)
        = 2 * (ENNReal.ofReal (g z.1) * radialIntegrand d s 1 b (z.1 - z.2)) +
          2 * (ENNReal.ofReal (g z.2) * radialIntegrand d s 1 b (z.1 - z.2)) := by
    intro z
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_add (hg0 z.1) (hg0 z.2),
      show ENNReal.ofReal (2 : ℝ) = 2 by simp]
    ring
  calc ∫⁻ z, F z ∂(Gagliardo.gagliardoCubeMeasure (originCube d (l : ℤ)))
      ≤ ∫⁻ z, ENNReal.ofReal (2 * (g z.1 + g z.2)) *
            radialIntegrand d s 1 b (z.1 - z.2)
            ∂(Gagliardo.gagliardoCubeMeasure (originCube d (l : ℤ))) :=
        lintegral_mono_ae hF
    _ = (∫⁻ z, 2 * (ENNReal.ofReal (g z.1) * radialIntegrand d s 1 b (z.1 - z.2))
            ∂(Gagliardo.gagliardoCubeMeasure (originCube d (l : ℤ)))) +
          ∫⁻ z, 2 * (ENNReal.ofReal (g z.2) * radialIntegrand d s 1 b (z.1 - z.2))
            ∂(Gagliardo.gagliardoCubeMeasure (originCube d (l : ℤ))) := by
        rw [lintegral_congr hsplit]
        exact lintegral_add_left (measurable_const.mul hAm) _
    _ = 2 * (∫⁻ z, ENNReal.ofReal (g z.1) * radialIntegrand d s 1 b (z.1 - z.2)
            ∂(Gagliardo.gagliardoCubeMeasure (originCube d (l : ℤ)))) +
          2 * ∫⁻ z, ENNReal.ofReal (g z.2) * radialIntegrand d s 1 b (z.1 - z.2)
            ∂(Gagliardo.gagliardoCubeMeasure (originCube d (l : ℤ))) := by
        rw [lintegral_const_mul _ hAm, lintegral_const_mul _ hBm]
    _ ≤ 2 * (ENNReal.ofReal A *
            ENNReal.ofReal (gagliardoOscillationConst d s * b ^ (2 * s))) +
          2 * (ENNReal.ofReal A *
            ENNReal.ofReal (gagliardoOscillationConst d s * b ^ (2 * s))) :=
        add_le_add (mul_le_mul_right htermA 2) (mul_le_mul_right htermB 2)
    _ = ENNReal.ofReal (4 * (gagliardoOscillationConst d s * b ^ (2 * s)) * A) := by
        rw [ENNReal.ofReal_mul (by linarith only [hK0] :
            (0 : ℝ) ≤ 4 * (gagliardoOscillationConst d s * b ^ (2 * s))),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
          show ENNReal.ofReal (4 : ℝ) = 4 by simp]
        ring

/-! ## The one-shell witness -/

/-- The explicit constant of the one-shell Gagliardo display. It collects the
square root `256` of the two `Γ₂` prefactors `16384` and the factor `4` of the
two Gagliardo slots, the pair-envelope amplitude `16384 (d + 3)` of
`IncrementHsClauseB`, the square root of the kernel constant of
`IncrementHsClause`, and the scale-shift `(6 (d + 1))^s` produced by reading
the truncated Lipschitz profile at scale `r = k − 1` and comparing the
Euclidean magnitude with the ambient sup norm. It depends on `d` and `s`
only. -/
def shellGagliardoConst (d : ℕ) (s : ℝ) : ℝ :=
  4194304 * ((d : ℝ) + 3) * Real.sqrt (gagliardoOscillationConst d s) *
    (6 * ((d : ℝ) + 1)) ^ s

/-- **The one-shell Gagliardo witness.** The square root of the volume-ratio
weighted sum of the squared diagonal two-point envelopes of the `3^{d(l-r)}`
scale-`r` subcubes of `cu_l`, scaled by the deterministic kernel constant of
the truncated Lipschitz profile of scale `r`. -/
def shellGagliardoWitness (s : ℝ) (r l : ℕ) (omega : ShellSeq d) : ℝ :=
  Real.sqrt
    (4 * (gagliardoOscillationConst d s *
        (2 * ((d : ℝ) + 1) * ((3 : ℝ) ^ r)⁻¹) ^ (2 * s)) *
      ((((3 : ℝ) ^ l) ^ d)⁻¹ * (((3 : ℝ) ^ r) ^ d) *
        ∑ R ∈ largeCubeSubcubes d r l,
          shellPairEnvelope (r + 1) (cubeCenter R) (cubeCenter R) omega ^ 2))

theorem shellGagliardoWitness_nonneg (s : ℝ) (r l : ℕ) (omega : ShellSeq d) :
    0 ≤ shellGagliardoWitness s r l omega :=
  Real.sqrt_nonneg _

theorem measurable_shellGagliardoWitness (s : ℝ) (r l : ℕ) :
    Measurable (fun omega : ShellSeq d => shellGagliardoWitness s r l omega) := by
  refine Real.continuous_sqrt.measurable.comp ?_
  refine measurable_const.mul (measurable_const.mul ?_)
  exact Finset.measurable_sum _ fun R _ =>
    (measurable_shellPairEnvelope (r + 1) (cubeCenter R) (cubeCenter R)).pow_const 2

/-- The Gagliardo kernel of a shell field is almost everywhere strongly
measurable for the Gagliardo product measure: the radial factor is measurable
and the increment factor is continuous. -/
private theorem aestronglyMeasurable_euclideanGagliardoKernel_shell
    (Q : TriadicCube d) (s : ℝ) (j : ShellField d) :
    AEStronglyMeasurable
      (euclideanGagliardoKernel s 2 (fun x : Vec d => j x))
      (Gagliardo.gagliardoCubeMeasure Q) := by
  refine Measurable.aestronglyMeasurable ?_
  have hrad : Measurable fun z : Vec d × Vec d =>
      euclideanDist z.1 z.2 ^ (-(s + (d : ℝ) / ((2 : ℝ≥0∞)).toReal)) := by
    show Measurable fun z : Vec d × Vec d =>
      Real.sqrt (∑ i, (z.1 - z.2) i * (z.1 - z.2) i) ^
        (-(s + (d : ℝ) / ((2 : ℝ≥0∞)).toReal))
    fun_prop
  have hc : Continuous fun z : Vec d × Vec d =>
      (j : Vec d → Mat d) z.1 - (j : Vec d → Mat d) z.2 :=
    (j.1.1.continuous.comp continuous_fst).sub (j.1.1.continuous.comp continuous_snd)
  show Measurable fun z : Vec d × Vec d =>
    (euclideanDist z.1 z.2 ^ (-(s + (d : ℝ) / ((2 : ℝ≥0∞)).toReal))) •
      ((j : Vec d → Mat d) z.1 - (j : Vec d → Mat d) z.2)
  exact hrad.smul hc.measurable

/-! ## The one-shell Gagliardo display -/

/-- **The deterministic half of the one-shell display.** At every sample the
Gagliardo seminorm of the shell of index `r + 1` on the large cube `cu_l` is at
most the one-shell witness. The estimate is uniform in `l`: the subdivision of
`cu_l` enters only through the finite convex combination
`lintegral_shellStepSq_le`, whose weights sum to one. -/
theorem cubeEuclideanGagliardoESeminorm_shell_le {r l : ℕ} (hrl : r ≤ l)
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) (omega : ShellSeq d) :
    cubeEuclideanGagliardoESeminorm (originCube d (l : ℤ)) s 2
        (fun x => (omega (r + 1)) x) ≤
      ENNReal.ofReal (shellGagliardoWitness s r l omega) := by
  have hbpos : (0 : ℝ) < 2 * ((d : ℝ) + 1) * ((3 : ℝ) ^ r)⁻¹ := by positivity
  have hae : ∀ᵐ z ∂(Gagliardo.gagliardoCubeMeasure (originCube d (l : ℤ))),
      ‖euclideanGagliardoKernel s 2 (fun x => (omega (r + 1)) x) z‖ₑ ^ (2 : ℝ) ≤
        ENNReal.ofReal
            (2 * (shellStepSq r l omega z.1 + shellStepSq r l omega z.2)) *
          radialIntegrand d s 1 (2 * ((d : ℝ) + 1) * ((3 : ℝ) ^ r)⁻¹)
            (z.1 - z.2) := by
    filter_upwards [ae_mem_cubeSet_prod (originCube d (l : ℤ))] with z hz
    exact enorm_euclideanGagliardoKernel_shell_sq_le hrl hs omega hz.1 hz.2
  have hint := lintegral_le_of_ae_radial_bound hs hs1 hbpos
    (shellStepSq_nonneg r l omega) (measurable_shellStepSq r l omega) hae
    (lintegral_shellStepSq_le r l omega)
  have hnn : (0 : ℝ) ≤ 4 * (gagliardoOscillationConst d s *
        (2 * ((d : ℝ) + 1) * ((3 : ℝ) ^ r)⁻¹) ^ (2 * s)) *
      ((((3 : ℝ) ^ l) ^ d)⁻¹ * (((3 : ℝ) ^ r) ^ d) *
        ∑ R ∈ largeCubeSubcubes d r l,
          shellPairEnvelope (r + 1) (cubeCenter R) (cubeCenter R) omega ^ 2) := by
    refine mul_nonneg (mul_nonneg (by norm_num)
      (mul_nonneg (gagliardoOscillationConst_nonneg d hs hs1)
        (Real.rpow_nonneg hbpos.le _)))
      (mul_nonneg (by positivity) (Finset.sum_nonneg fun _R _ => sq_nonneg _))
  have h2 : ((2 : ℝ≥0∞)).toReal = 2 := by norm_num
  rw [cubeEuclideanGagliardoESeminorm,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      (aestronglyMeasurable_euclideanGagliardoKernel_shell
        (originCube d (l : ℤ)) s (omega (r + 1))), h2]
  calc (∫⁻ z, ‖euclideanGagliardoKernel s 2 (fun x => (omega (r + 1)) x) z‖ₑ ^ (2 : ℝ)
          ∂(Gagliardo.gagliardoCubeMeasure (originCube d (l : ℤ)))) ^ ((1 : ℝ) / 2)
      ≤ (ENNReal.ofReal (4 * (gagliardoOscillationConst d s *
            (2 * ((d : ℝ) + 1) * ((3 : ℝ) ^ r)⁻¹) ^ (2 * s)) *
          ((((3 : ℝ) ^ l) ^ d)⁻¹ * (((3 : ℝ) ^ r) ^ d) *
            ∑ R ∈ largeCubeSubcubes d r l,
              shellPairEnvelope (r + 1) (cubeCenter R) (cubeCenter R) omega ^ 2)))
          ^ ((1 : ℝ) / 2) := ENNReal.rpow_le_rpow hint (by norm_num)
    _ = ENNReal.ofReal (shellGagliardoWitness s r l omega) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hnn (by norm_num), shellGagliardoWitness,
          Real.sqrt_eq_rpow]

/-- The scale bookkeeping of the one-shell amplitude: the truncated Lipschitz
profile is read at scale `r`, and its kernel amplitude `2 (d+1) 3^{−r}` raised
to `2s` is exactly `(6 (d+1))^{2s}` times the shell weight `3^{−2s(r+1)}` at
the shell's own scale `r + 1`. -/
private theorem shellAmplitude_identity (dim r : ℕ) (s : ℝ) :
    (2 * ((dim : ℝ) + 1) * ((3 : ℝ) ^ r)⁻¹) ^ (2 * s)
      = (6 * ((dim : ℝ) + 1)) ^ (2 * s) *
        (3 : ℝ) ^ (-(2 * s * (((r + 1 : ℕ)) : ℝ))) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hr : ((3 : ℝ) ^ r)⁻¹ = (3 : ℝ) ^ (-(r : ℝ)) := by
    rw [Real.rpow_neg h3.le, Real.rpow_natCast]
  have hleft : (2 * ((dim : ℝ) + 1) * ((3 : ℝ) ^ r)⁻¹) ^ (2 * s)
      = (2 * ((dim : ℝ) + 1)) ^ (2 * s) * ((3 : ℝ) ^ (-(r : ℝ))) ^ (2 * s) := by
    rw [hr, Real.mul_rpow (by positivity) (Real.rpow_nonneg h3.le _)]
  have hpow : ((3 : ℝ) ^ (-(r : ℝ))) ^ (2 * s) = (3 : ℝ) ^ (-(r : ℝ) * (2 * s)) :=
    (Real.rpow_mul h3.le _ _).symm
  have hright : (6 * ((dim : ℝ) + 1)) ^ (2 * s)
      = (3 : ℝ) ^ (2 * s) * (2 * ((dim : ℝ) + 1)) ^ (2 * s) := by
    rw [show (6 : ℝ) * ((dim : ℝ) + 1) = 3 * (2 * ((dim : ℝ) + 1)) by ring,
      Real.mul_rpow (by norm_num) (by positivity)]
  have hcombine : (3 : ℝ) ^ (2 * s) * (3 : ℝ) ^ (-(2 * s * (((r + 1 : ℕ)) : ℝ)))
      = (3 : ℝ) ^ (-(r : ℝ) * (2 * s)) := by
    rw [← Real.rpow_add h3]
    congr 1
    push_cast
    ring
  rw [hleft, hpow, hright,
    show (3 : ℝ) ^ (2 * s) * (2 * ((dim : ℝ) + 1)) ^ (2 * s) *
        (3 : ℝ) ^ (-(2 * s * (((r + 1 : ℕ)) : ℝ)))
      = (2 * ((dim : ℝ) + 1)) ^ (2 * s) *
        ((3 : ℝ) ^ (2 * s) * (3 : ℝ) ^ (-(2 * s * (((r + 1 : ℕ)) : ℝ)))) from by ring,
    hcombine]

/-- **The `Γ₂` tail of the one-shell display.** The witness has the tail at
`shellGagliardoConst d s · 3^{−s(r+1)}`, uniformly in the cube scale `l`: the
`3^{d(l−r)}` diagonal envelopes all have the same amplitude
`shellPairEnvelopeConst d`, their squares have the `Γ₁` tail at its square, and
the finite `Γ₁` triangle inequality multiplies that by the number of subcubes,
which the volume ratio cancels exactly. -/
theorem isBigO_gammaSigma_shellGagliardoWitness
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) {s : ℝ} (hs : 0 < s)
    (hs1 : s < 1) {r l : ℕ} (hrl : r ≤ l) :
    IsBigO P.toMeasure (gammaSigma 2) (shellGagliardoWitness s r l)
      (shellGagliardoConst d s * (3 : ℝ) ^ (-(s * (((r + 1 : ℕ)) : ℝ)))) := by
  have hG := gagliardoOscillationConst_nonneg d hs hs1
  have hApos : (0 : ℝ) < shellPairEnvelopeConst d := by
    rw [shellPairEnvelopeConst]; positivity
  have hbpos : (0 : ℝ) < 2 * ((d : ℝ) + 1) * ((3 : ℝ) ^ r)⁻¹ := by positivity
  have hbrp : (0 : ℝ) ≤ (2 * ((d : ℝ) + 1) * ((3 : ℝ) ^ r)⁻¹) ^ (2 * s) :=
    Real.rpow_nonneg hbpos.le _
  have hrho : (0 : ℝ) ≤ (((3 : ℝ) ^ l) ^ d)⁻¹ * (((3 : ℝ) ^ r) ^ d) := by positivity
  have h4K : (0 : ℝ) ≤ 4 * (gagliardoOscillationConst d s *
      (2 * ((d : ℝ) + 1) * ((3 : ℝ) ^ r)⁻¹) ^ (2 * s)) := by
    have hmul := mul_nonneg hG hbrp
    linarith only [hmul]
  have hnn : ∀ omega : ShellSeq d, (0 : ℝ) ≤ 4 * (gagliardoOscillationConst d s *
        (2 * ((d : ℝ) + 1) * ((3 : ℝ) ^ r)⁻¹) ^ (2 * s)) *
      ((((3 : ℝ) ^ l) ^ d)⁻¹ * (((3 : ℝ) ^ r) ^ d) *
        ∑ R ∈ largeCubeSubcubes d r l,
          shellPairEnvelope (r + 1) (cubeCenter R) (cubeCenter R) omega ^ 2) :=
    fun _ => mul_nonneg h4K
      (mul_nonneg hrho (Finset.sum_nonneg fun _R _ => sq_nonneg _))
  have hBnn : (0 : ℝ) ≤
      shellGagliardoConst d s * (3 : ℝ) ^ (-(s * (((r + 1 : ℕ)) : ℝ))) := by
    have hconst : (0 : ℝ) ≤ shellGagliardoConst d s := by
      rw [shellGagliardoConst]
      exact mul_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
        (Real.rpow_nonneg (by positivity) _)
    exact mul_nonneg hconst (Real.rpow_nonneg (by norm_num) _)
  have hsqR : ∀ R : TriadicCube d,
      IsBigO P.toMeasure (gammaSigma 1)
        (fun omega : ShellSeq d =>
          shellPairEnvelope (r + 1) (cubeCenter R) (cubeCenter R) omega ^ (2 : ℕ))
        (shellPairEnvelopeConst d ^ (2 : ℕ)) := by
    intro R
    have hbase := isBigO_gammaSigma_shellPairEnvelope hPrefix hJ3 (r + 1)
      (cubeCenter R) (cubeCenter R)
    have hfwd := isBigO_gammaSigma_rpow_fwd (p := 2) (σ := 2)
      (by norm_num : (0 : ℝ) < 2) hApos.le
      (fun omega => shellPairEnvelope_nonneg (r + 1) (cubeCenter R)
        (cubeCenter R) omega) hbase
    rw [show ((2 : ℝ) / 2) = 1 by norm_num] at hfwd
    simpa only [rpow_two_eq_sq] using hfwd
  have hsum := isBigO_gammaSigma_finset_sum_of_one_le (mu := P.toMeasure)
    (largeCubeSubcubes d r l)
    (X := fun (R : TriadicCube d) (omega : ShellSeq d) =>
      shellPairEnvelope (r + 1) (cubeCenter R) (cubeCenter R) omega ^ (2 : ℕ))
    (a := fun _ : TriadicCube d => shellPairEnvelopeConst d ^ (2 : ℕ))
    (sigma := 1) le_rfl (largeCubeSubcubes_nonempty d r l)
    (fun _R _ => pow_pos hApos 2) (fun R _ => hsqR R)
    (fun R _ =>
      (measurable_shellPairEnvelope (r + 1) (cubeCenter R) (cubeCenter R)).pow_const 2)
  have hconst : ∑ _R ∈ largeCubeSubcubes d r l, shellPairEnvelopeConst d ^ (2 : ℕ)
      = ((largeCubeSubcubes d r l).card : ℝ) * shellPairEnvelopeConst d ^ (2 : ℕ) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [hconst] at hsum
  have hstep1 := hsum.const_mul
    (c := (((3 : ℝ) ^ l) ^ d)⁻¹ * (((3 : ℝ) ^ r) ^ d)) hrho
  have hstep2 := hstep1.const_mul
    (c := 4 * (gagliardoOscillationConst d s *
      (2 * ((d : ℝ) + 1) * ((3 : ℝ) ^ r)⁻¹) ^ (2 * s))) h4K
  have hB2 : (shellGagliardoConst d s *
        (3 : ℝ) ^ (-(s * (((r + 1 : ℕ)) : ℝ)))) ^ (2 : ℕ)
      = 17592186044416 * (((d : ℝ) + 3) ^ 2 * (gagliardoOscillationConst d s *
          ((6 * ((d : ℝ) + 1)) ^ (2 * s) *
            (3 : ℝ) ^ (-(2 * s * (((r + 1 : ℕ)) : ℝ)))))) := by
    have h1 : (Real.sqrt (gagliardoOscillationConst d s)) ^ (2 : ℕ)
        = gagliardoOscillationConst d s := Real.sq_sqrt hG
    have h2 : ((6 * ((d : ℝ) + 1)) ^ s) ^ (2 : ℕ) = (6 * ((d : ℝ) + 1)) ^ (2 * s) := by
      rw [← Real.rpow_natCast ((6 * ((d : ℝ) + 1)) ^ s) 2,
        ← Real.rpow_mul (by positivity)]
      congr 1
      push_cast
      ring
    have h3 : ((3 : ℝ) ^ (-(s * (((r + 1 : ℕ)) : ℝ)))) ^ (2 : ℕ)
        = (3 : ℝ) ^ (-(2 * s * (((r + 1 : ℕ)) : ℝ))) := by
      rw [← Real.rpow_natCast ((3 : ℝ) ^ (-(s * (((r + 1 : ℕ)) : ℝ)))) 2,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      push_cast
      ring
    rw [shellGagliardoConst, mul_pow, mul_pow, mul_pow, h1, h2, h3]
    ring
  have hamp : 4 * (gagliardoOscillationConst d s *
        (2 * ((d : ℝ) + 1) * ((3 : ℝ) ^ r)⁻¹) ^ (2 * s)) *
      ((((3 : ℝ) ^ l) ^ d)⁻¹ * (((3 : ℝ) ^ r) ^ d) *
        (16384 * (((largeCubeSubcubes d r l).card : ℝ) *
          shellPairEnvelopeConst d ^ (2 : ℕ))))
      = (shellGagliardoConst d s *
          (3 : ℝ) ^ (-(s * (((r + 1 : ℕ)) : ℝ)))) ^ (2 : ℕ) := by
    have hL : 4 * (gagliardoOscillationConst d s *
          (2 * ((d : ℝ) + 1) * ((3 : ℝ) ^ r)⁻¹) ^ (2 * s)) *
        ((((3 : ℝ) ^ l) ^ d)⁻¹ * (((3 : ℝ) ^ r) ^ d) *
          (16384 * (((largeCubeSubcubes d r l).card : ℝ) *
            shellPairEnvelopeConst d ^ (2 : ℕ))))
        = (((largeCubeSubcubes d r l).card : ℝ) *
            ((((3 : ℝ) ^ l) ^ d)⁻¹ * (((3 : ℝ) ^ r) ^ d))) *
          (4 * 16384 * shellPairEnvelopeConst d ^ (2 : ℕ) *
            (gagliardoOscillationConst d s *
              (2 * ((d : ℝ) + 1) * ((3 : ℝ) ^ r)⁻¹) ^ (2 * s))) := by
      ring
    rw [hL, card_mul_subcubeRatio hrl, one_mul, shellAmplitude_identity,
      shellPairEnvelopeConst, hB2]
    ring
  refine isBigO_gammaSigma_rpow_rev (p := 2) (σ := 2) (by norm_num : (0 : ℝ) < 2)
    hBnn (fun omega => shellGagliardoWitness_nonneg s r l omega) ?_
  rw [show ((2 : ℝ) / 2) = 1 by norm_num]
  have hwsq : (fun omega : ShellSeq d => shellGagliardoWitness s r l omega ^ (2 : ℝ))
      = fun omega : ShellSeq d =>
        4 * (gagliardoOscillationConst d s *
          (2 * ((d : ℝ) + 1) * ((3 : ℝ) ^ r)⁻¹) ^ (2 * s)) *
          ((((3 : ℝ) ^ l) ^ d)⁻¹ * (((3 : ℝ) ^ r) ^ d) *
            ∑ R ∈ largeCubeSubcubes d r l,
              shellPairEnvelope (r + 1) (cubeCenter R) (cubeCenter R) omega ^ 2) := by
    funext omega
    rw [shellGagliardoWitness, rpow_two_eq_sq, Real.sq_sqrt (hnn omega)]
  rw [hwsq, rpow_two_eq_sq, ← hamp]
  exact hstep2

/-! ## The shell sum -/

theorem shellGagliardoConst_pos {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    0 < shellGagliardoConst d s := by
  rw [shellGagliardoConst]
  refine mul_pos (mul_pos (by positivity) ?_) (Real.rpow_pos_of_pos (by positivity) _)
  exact Real.sqrt_pos.2 (gagliardoOscillationConst_pos d hs hs1)


/-- The Gagliardo kernel is additive in the field, so the kernel of a finite
shell increment is the sum of the kernels of its shells. -/
private theorem euclideanGagliardoKernel_finiteShellIncrement (s : ℝ)
    (omega : ShellSeq d) (n m : ℕ) :
    euclideanGagliardoKernel s 2 (fun x => finiteShellIncrement omega n m x)
      = ∑ k ∈ Finset.Ioc n m,
        euclideanGagliardoKernel s 2 (fun x : Vec d => (omega k) x) := by
  funext z
  rw [Finset.sum_apply]
  show (euclideanDist z.1 z.2 ^ (-(s + (d : ℝ) / ((2 : ℝ≥0∞)).toReal))) •
      (finiteShellIncrement omega n m z.1 - finiteShellIncrement omega n m z.2)
    = ∑ k ∈ Finset.Ioc n m,
      (euclideanDist z.1 z.2 ^ (-(s + (d : ℝ) / ((2 : ℝ≥0∞)).toReal))) •
        ((omega k) z.1 - (omega k) z.2)
  rw [← Finset.smul_sum]
  congr 1
  have h1 : finiteShellIncrement omega n m z.1
      = ∑ k ∈ Finset.Ioc n m, (omega k) z.1 := by
    rw [finiteShellIncrement_apply]
    rfl
  have h2 : finiteShellIncrement omega n m z.2
      = ∑ k ∈ Finset.Ioc n m, (omega k) z.2 := by
    rw [finiteShellIncrement_apply]
    rfl
  rw [h1, h2, Finset.sum_sub_distrib]

/-- **The Gagliardo half of clause (d).** Summing the one-shell display over
the shells of `(n, m]` gives a measurable witness at the amplitude
`C 3^{−sn}`, uniformly in `l`: the seminorm is subadditive, the finite `Γ₂`
triangle inequality adds the one-shell amplitudes, and the geometric sum
`sum_Ioc_shellWeight_le` collapses them to `3^{−sn}(1 − 3^{−s})^{-1}`. -/
theorem exists_witness_cubeEuclideanGagliardoESeminorm_finiteShellIncrement
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) {s : ℝ} (hs : 0 < s)
    (hs1 : s < 1) {n m l : ℕ} (hnm : n < m) (hml : m ≤ l) {C : ℝ}
    (hC : 16384 * (shellGagliardoConst d s * (1 - (3 : ℝ) ^ (-s))⁻¹) ≤ C) :
    ∃ X : ShellSeq d → ℝ, Measurable X ∧
      IsBigO P.toMeasure (gammaSigma 2) X (C * (3 : ℝ) ^ (-(s * (n : ℝ)))) ∧
      ∀ omega : ShellSeq d,
        cubeEuclideanGagliardoESeminorm (originCube d (l : ℤ)) s 2
            (fun x => finiteShellIncrement omega n m x) ≤
          ENNReal.ofReal (X omega) := by
  have hCpos := shellGagliardoConst_pos (d := d) hs hs1
  have hratio : (0 : ℝ) < 1 - (3 : ℝ) ^ (-s) := by
    have h1 : (3 : ℝ) ^ (-s) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hs])
    linarith only [h1]
  have hsucc : ∀ k ∈ Finset.Ioc n m, k - 1 + 1 = k := by
    intro k hk
    have hkpos : 0 < k := lt_of_le_of_lt (Nat.zero_le n) (Finset.mem_Ioc.mp hk).1
    omega
  have hkl : ∀ k ∈ Finset.Ioc n m, k - 1 ≤ l := by
    intro k hk
    have := (Finset.mem_Ioc.mp hk).2
    omega
  refine ⟨fun omega => ∑ k ∈ Finset.Ioc n m, shellGagliardoWitness s (k - 1) l omega,
    Finset.measurable_sum _ fun k _ => measurable_shellGagliardoWitness s (k - 1) l,
    ?_, ?_⟩
  · have htails : ∀ k ∈ Finset.Ioc n m,
        IsBigO P.toMeasure (gammaSigma 2) (shellGagliardoWitness s (k - 1) l)
          (shellGagliardoConst d s * (3 : ℝ) ^ (-(s * (k : ℝ)))) := by
      intro k hk
      have h := isBigO_gammaSigma_shellGagliardoWitness hPrefix hJ3 hs hs1 (hkl k hk)
      rwa [hsucc k hk] at h
    have hsum := isBigO_gammaSigma_finset_sum_of_one_le (mu := P.toMeasure)
      (Finset.Ioc n m)
      (X := fun (k : ℕ) (omega : ShellSeq d) => shellGagliardoWitness s (k - 1) l omega)
      (a := fun k : ℕ => shellGagliardoConst d s * (3 : ℝ) ^ (-(s * (k : ℝ))))
      (sigma := 2) (by norm_num) (Finset.nonempty_Ioc.mpr hnm)
      (fun _k _ => mul_pos hCpos (Real.rpow_pos_of_pos (by norm_num) _))
      htails (fun k _ => measurable_shellGagliardoWitness s (k - 1) l)
    refine hsum.mono_scale ?_
    have hgeom : ∑ k ∈ Finset.Ioc n m,
          shellGagliardoConst d s * (3 : ℝ) ^ (-(s * (k : ℝ)))
        ≤ shellGagliardoConst d s *
          ((3 : ℝ) ^ (-(s * (n : ℝ))) * (1 - (3 : ℝ) ^ (-s))⁻¹) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_Ioc_shellWeight_le hs n m) hCpos.le
    have hnpow : (0 : ℝ) < (3 : ℝ) ^ (-(s * (n : ℝ))) :=
      Real.rpow_pos_of_pos (by norm_num) _
    calc (16384 : ℝ) * ∑ k ∈ Finset.Ioc n m,
            shellGagliardoConst d s * (3 : ℝ) ^ (-(s * (k : ℝ)))
        ≤ 16384 * (shellGagliardoConst d s *
            ((3 : ℝ) ^ (-(s * (n : ℝ))) * (1 - (3 : ℝ) ^ (-s))⁻¹)) :=
          mul_le_mul_of_nonneg_left hgeom (by norm_num)
      _ = 16384 * (shellGagliardoConst d s * (1 - (3 : ℝ) ^ (-s))⁻¹) *
            (3 : ℝ) ^ (-(s * (n : ℝ))) := by ring
      _ ≤ C * (3 : ℝ) ^ (-(s * (n : ℝ))) :=
          mul_le_mul_of_nonneg_right hC hnpow.le
  · intro omega
    calc cubeEuclideanGagliardoESeminorm (originCube d (l : ℤ)) s 2
            (fun x => finiteShellIncrement omega n m x)
        = eLpNorm (∑ k ∈ Finset.Ioc n m,
              euclideanGagliardoKernel s 2 (fun x : Vec d => (omega k) x)) 2
            (Gagliardo.gagliardoCubeMeasure (originCube d (l : ℤ))) := by
          rw [cubeEuclideanGagliardoESeminorm,
            euclideanGagliardoKernel_finiteShellIncrement]
      _ ≤ ∑ k ∈ Finset.Ioc n m,
            eLpNorm (euclideanGagliardoKernel s 2 (fun x : Vec d => (omega k) x)) 2
              (Gagliardo.gagliardoCubeMeasure (originCube d (l : ℤ))) :=
          eLpNorm_sum_le (by norm_num)
      _ ≤ ∑ k ∈ Finset.Ioc n m,
            ENNReal.ofReal (shellGagliardoWitness s (k - 1) l omega) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have h := cubeEuclideanGagliardoESeminorm_shell_le (hkl k hk) hs hs1 omega
          rw [hsucc k hk] at h
          exact h
      _ = ENNReal.ofReal (∑ k ∈ Finset.Ioc n m,
            shellGagliardoWitness s (k - 1) l omega) :=
          (ENNReal.ofReal_sum_of_nonneg
            (fun k _ => shellGagliardoWitness_nonneg s (k - 1) l omega)).symm

/-! ## Clause (d) -/

private theorem abs_max_zero_le_abs (a : ℝ) : |max a 0| ≤ |a| := by
  rcases le_or_gt 0 a with h | h
  · rw [max_eq_left h]
  · rw [max_eq_right h.le, abs_zero]
    exact abs_nonneg a

/-- The `Γ₂` triangle inequality for two summands, in the shape the two pieces
of the `H̲^s` norm need. -/
private theorem isBigO_gammaSigma_add_two {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu] {X Y : Omega → ℝ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hXm : Measurable X) (hYm : Measurable Y)
    (hX : IsBigO mu (gammaSigma 2) X a) (hY : IsBigO mu (gammaSigma 2) Y b) :
    IsBigO mu (gammaSigma 2) (fun omega => X omega + Y omega)
      (16384 * (a + b)) := by
  have hsum := isBigO_gammaSigma_finset_sum_of_one_le (mu := mu)
    (Finset.univ : Finset (Fin 2)) (X := ![X, Y]) (a := ![a, b])
    (sigma := 2) (by norm_num) ⟨0, Finset.mem_univ _⟩
    (by
      intro i _
      fin_cases i
      · simpa using ha
      · simpa using hb)
    (by
      intro i _
      fin_cases i
      · simpa using hX
      · simpa using hY)
    (by
      intro i _
      fin_cases i
      · simpa using hXm
      · simpa using hYm)
  have hfun : (fun omega ↦ ∑ i : Fin 2, (![X, Y]) i omega)
      = fun omega ↦ X omega + Y omega := by
    funext omega
    simp [Fin.sum_univ_two]
  have hamp : ∑ i : Fin 2, (![a, b]) i = a + b := by
    simp [Fin.sum_univ_two]
  rw [hfun, hamp] at hsum
  exact hsum

/-- The explicit constant of clause (d): the `Γ₂` triangle prefactor `16384`
times the sum of the `L̲²` constant
`largeCubeLinftyConst d · hsWeightGrowthConst s` of `IncrementHsClauseB` and the
summed Gagliardo constant `16384 · shellGagliardoConst d s (1 − 3^{−s})^{-1}`.
It depends on `d` and `s` only, and in particular not on `l`, `n`, `m`, `p` or
the law. -/
def hsClauseConst (d : ℕ) (s : ℝ) : ℝ :=
  16384 * (largeCubeLinftyConst d * hsWeightGrowthConst s +
    16384 * (shellGagliardoConst d s * (1 - (3 : ℝ) ^ (-s))⁻¹))

/-- **Clause (d) of the scale estimates**, the `H̲^s` clause
`e.kmn.Hs`: for `n < m ≤ l` there is a measurable witness with a `Γ₂` tail at the
amplitude `C 3^{−sn}` dominating `‖k_m − k_n‖_{H̲^s(cu_l)}` at every sample.

The constant `hsClauseConst d s` depends on `d` and `s` only, so the
quantifier order — `C` chosen after `s` and `p` and before `P` — is respected
with room to spare; the `L^p` datum `p` and the `J1` law are
carried in the signature for shape compatibility and are not used.

The witness is the sum of the two pieces of the printed two-piece bound,
truncated at zero so that the two `ENNReal.ofReal` values add: the
`L̲²` piece `3^{−sl}‖k_m − k_n‖_{L̲²(cu_l)}` of
`exists_witness_cubeHsWeightLtwo_finiteShellIncrement`, whose amplitude is
`l`-uniform because `(l−n) 3^{−s(l−n)}` is bounded, and the Gagliardo piece
`exists_witness_cubeEuclideanGagliardoESeminorm_finiteShellIncrement`, whose
amplitude is `l`-uniform because the pair bound is taken pointwise in the pair
and averaged over the subdivision of `cu_l`. -/
theorem hsClause_of_shellLaws
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (s p : ℝ)
    (hs : 0 < s) (hs1 : s < 1) (hp : (1 : ℝ) ≤ p) (C : ℝ)
    (hC : hsClauseConst d s ≤ C) {n m l : ℕ} (hnm : n < m) (hml : m ≤ l) :
    ∃ X : ShellSeq d → ℝ, Measurable X ∧
      IsBigO P.toMeasure (gammaSigma 2) X (C * (3 : ℝ) ^ (-(s * (n : ℝ)))) ∧
      ∀ omega : ShellSeq d,
        cubeHsENorm (originCube d (l : ℤ)) s
            (fun x : Vec d => finiteShellIncrement omega n m x) ≤
          ENNReal.ofReal (X omega) := by
  -- The `J1` law and the `L^p` datum `p` are referenced here only
  -- so that the signature carries the quantifier shape of clause (d).
  have _shapeJ1 := hJ1
  have _shapeP := hp
  have hLpos : 0 < largeCubeLinftyConst d := largeCubeLinftyConst_pos hPrefix
  have hWpos : 0 < hsWeightGrowthConst s := by
    rw [hsWeightGrowthConst]
    have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have hexp : 0 < Real.exp 1 := Real.exp_pos 1
    exact inv_pos.2 (by positivity)
  have hGpos := shellGagliardoConst_pos (d := d) hs hs1
  have hratio : (0 : ℝ) < 1 - (3 : ℝ) ^ (-s) := by
    have h1 : (3 : ℝ) ^ (-s) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hs])
    linarith only [h1]
  have hnpow : (0 : ℝ) < (3 : ℝ) ^ (-(s * (n : ℝ))) :=
    Real.rpow_pos_of_pos (by norm_num) _
  obtain ⟨X₁, hX₁meas, hX₁tail, hX₁pt⟩ :=
    exists_witness_cubeHsWeightLtwo_finiteShellIncrement hPrefix hJ2 hJ3 hJ4 hs
      hnm hml (C := largeCubeLinftyConst d * hsWeightGrowthConst s) le_rfl
  obtain ⟨X₂, hX₂meas, hX₂tail, hX₂pt⟩ :=
    exists_witness_cubeEuclideanGagliardoESeminorm_finiteShellIncrement hPrefix hJ3
      hs hs1 hnm hml
      (C := 16384 * (shellGagliardoConst d s * (1 - (3 : ℝ) ^ (-s))⁻¹)) le_rfl
  refine ⟨fun omega => max (X₁ omega) 0 + max (X₂ omega) 0,
    (hX₁meas.max measurable_const).add (hX₂meas.max measurable_const), ?_, ?_⟩
  · have h₁ : IsBigO P.toMeasure (gammaSigma 2) (fun omega => max (X₁ omega) 0)
        (largeCubeLinftyConst d * hsWeightGrowthConst s *
          (3 : ℝ) ^ (-(s * (n : ℝ)))) :=
      hX₁tail.of_abs_le fun omega => abs_max_zero_le_abs (X₁ omega)
    have h₂ : IsBigO P.toMeasure (gammaSigma 2) (fun omega => max (X₂ omega) 0)
        (16384 * (shellGagliardoConst d s * (1 - (3 : ℝ) ^ (-s))⁻¹) *
          (3 : ℝ) ^ (-(s * (n : ℝ)))) :=
      hX₂tail.of_abs_le fun omega => abs_max_zero_le_abs (X₂ omega)
    have hsum := isBigO_gammaSigma_add_two
      (mu := P.toMeasure)
      (mul_pos (mul_pos hLpos hWpos) hnpow)
      (mul_pos (mul_pos (by norm_num) (mul_pos hGpos (inv_pos.2 hratio))) hnpow)
      (hX₁meas.max measurable_const) (hX₂meas.max measurable_const) h₁ h₂
    refine hsum.mono_scale ?_
    calc (16384 : ℝ) * (largeCubeLinftyConst d * hsWeightGrowthConst s *
            (3 : ℝ) ^ (-(s * (n : ℝ))) +
          16384 * (shellGagliardoConst d s * (1 - (3 : ℝ) ^ (-s))⁻¹) *
            (3 : ℝ) ^ (-(s * (n : ℝ))))
        = hsClauseConst d s * (3 : ℝ) ^ (-(s * (n : ℝ))) := by
          rw [hsClauseConst]
          ring
      _ ≤ C * (3 : ℝ) ^ (-(s * (n : ℝ))) := mul_le_mul_of_nonneg_right hC hnpow.le
  · intro omega
    have h₁ : ENNReal.ofReal (X₁ omega) = ENNReal.ofReal (max (X₁ omega) 0) := by
      rcases le_or_gt 0 (X₁ omega) with h | h
      · rw [max_eq_left h]
      · rw [max_eq_right h.le, ENNReal.ofReal_zero,
          ENNReal.ofReal_eq_zero.2 h.le]
    have h₂ : ENNReal.ofReal (X₂ omega) = ENNReal.ofReal (max (X₂ omega) 0) := by
      rcases le_or_gt 0 (X₂ omega) with h | h
      · rw [max_eq_left h]
      · rw [max_eq_right h.le, ENNReal.ofReal_zero,
          ENNReal.ofReal_eq_zero.2 h.le]
    calc cubeHsENorm (originCube d (l : ℤ)) s
            (fun x : Vec d => finiteShellIncrement omega n m x)
        ≤ cubeHsWeight (originCube d (l : ℤ)) s *
              cubeLpENorm (originCube d (l : ℤ)) 2
                (fun x : Vec d => finiteShellIncrement omega n m x) +
            cubeEuclideanGagliardoESeminorm (originCube d (l : ℤ)) s 2
              (fun x : Vec d => finiteShellIncrement omega n m x) :=
          cubeHsENorm_le_add _ _ _
      _ ≤ ENNReal.ofReal (X₁ omega) + ENNReal.ofReal (X₂ omega) :=
          add_le_add (hX₁pt omega) (hX₂pt omega)
      _ = ENNReal.ofReal (max (X₁ omega) 0 + max (X₂ omega) 0) := by
          rw [h₁, h₂, ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)]

end

end SuperdiffusionCLT.Section2.Estimates.Stream
