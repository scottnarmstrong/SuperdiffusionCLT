/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Norms.NegativeHatOrderOne
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementCubeMomentLocality
public import SuperdiffusionCLT.Section3.ResponseFields.StationaryComparison
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2
public import SuperdiffusionCLT.Section3.Setup.WholeSpaceEnergyC
public import Homogenization.Sobolev.Foundations.CubeCoerciveH1

/-!
# The centering bound: centering at the cube mean costs a factor two

This is the `L̲⁴` display inside the proof of `l.LHS.term1` (and, through
`vecHatNegENormOrderOne_le_vecCubeLpENorm`, the `r > m` half of the `e.jk.Hminus.endpoint`
clause): for every field on the pigeonhole cube `cu_m`,

> `‖F - (F)_{cu_m}‖_{L̲^q(cu_m)} ≤ 2 ‖F‖_{L̲^q(cu_m)}`.

The proof is the triangle inequality plus Jensen: the constant field
`(F)_{cu_m}` has `L̲^q` norm exactly its Euclidean magnitude, and that
magnitude is at most the `L̲^q` norm of `F` itself, because the normalized cube
measure is a probability measure (`eLpNorm_le_eLpNorm_of_exponent_le`).

This module carries the deterministic centering statement at a general
exponent `1 ≤ q` for a general vector field that is square integrable on the
open cube, together with its specialization to the single-shell flux
`j_r p` (`Section3.Setup.shellFlux`) at `q = 4`, in the exact
shape the pointwise clause of the `Zl4` pair consumes
(`Section3/Setup/WholeSpaceEnergyOrderOneB.lean`, binder `hZl4Bound`).

The `L̲²` instance of the general statement is already proved as
`SuperdiffusionCLT.Section3.Terms.vecCubeLpENorm_sub_average_le`
(`Section3/Terms/RHSTerm2Displays.lean`); that statement reads the centering
against an arbitrary constant, which is a different (weaker) shape, and no
other declaration covers `q > 2`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Estimates.Stream

open Homogenization MeasureTheory
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section3.Terms
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The two deterministic ingredients -/

/-- The Euclidean magnitude of a vector is the norm of its reading in the
Euclidean Hilbert carrier. -/
private theorem vecNorm_eq_norm_ofVec' (v : Vec d) : vecNorm v = ‖HilbertVec.ofVec v‖ :=
  rfl

/-- The `L̲^q` norm of a constant field is the Euclidean magnitude of the
constant: the normalized cube measure is a probability measure. -/
private theorem vecCubeLpENorm_const_eq {Q : TriadicCube d} {q : ℝ≥0∞} (hq : q ≠ 0)
    (c : Vec d) :
    vecCubeLpENorm Q q (fun _ : Vec d => c) = ENNReal.ofReal (vecNorm c) := by
  have : IsProbabilityMeasure (normalizedCubeMeasure Q) :=
    ⟨normalizedCubeMeasure_apply_univ Q⟩
  have hμ0 : normalizedCubeMeasure Q ≠ 0 := fun h =>
    absurd (normalizedCubeMeasure_apply_univ Q) (by rw [h]; simp)
  show eLpNorm (fun _ : Vec d => HilbertVec.ofVec c) q (normalizedCubeMeasure Q) = _
  rw [eLpNorm_const _ hq hμ0, measure_univ, ENNReal.one_rpow, mul_one,
    ← ofReal_norm, vecNorm_eq_norm_ofVec']

/-- **Jensen on the cube**: the Euclidean magnitude of the cube average of a
vector field is at most its `L̲^q` norm, for every `1 ≤ q`.  The average is the
Bochner integral of the Hilbert reading against the probability measure
`normalizedCubeMeasure Q`, the norm is dominated by the mean of the magnitudes,
and the mean is at most the `L̲^q` norm because the measure is a probability
measure. -/
theorem ofReal_vecNorm_volumeAverageVec_le {Q : TriadicCube d} {q : ℝ≥0∞}
    {G : Vec d → Vec d} (hq : 1 ≤ q) (hG : MemVectorL2 (openCubeSet Q) G) :
    ENNReal.ofReal (vecNorm (volumeAverageVec (openCubeSet Q) G)) ≤
      vecCubeLpENorm Q q G := by
  classical
  have : IsProbabilityMeasure (normalizedCubeMeasure Q) :=
    ⟨normalizedCubeMeasure_apply_univ Q⟩
  -- the Hilbert reading of the field is `L²`, hence integrable
  have hmemH : MemLp (hilbertifyVecField G) 2 (normalizedCubeMeasure Q) := by
    rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
    exact (memHilbertVectorL2_hilbertifyVecField hG).smul_measure ENNReal.ofReal_ne_top
  have hintH : Integrable (hilbertifyVecField G) (normalizedCubeMeasure Q) :=
    hmemH.integrable (by norm_num)
  have hmeasH : AEStronglyMeasurable (hilbertifyVecField G) (normalizedCubeMeasure Q) :=
    hmemH.aestronglyMeasurable
  have hintHnorm : Integrable (fun x : Vec d => ‖hilbertifyVecField G x‖)
      (normalizedCubeMeasure Q) := hintH.norm
  -- component integrability, from the scalar `L²` membership
  have hintComp : ∀ i : Fin d, Integrable (fun x : Vec d => G x i)
      (normalizedCubeMeasure Q) := by
    intro i
    have hm : MemLp (fun x : Vec d => G x i) 2 (normalizedCubeMeasure Q) := by
      rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
      exact Section3.Terms.memL2On_component_of_memVectorL2 hG i |>.smul_measure
        ENNReal.ofReal_ne_top
    exact hm.integrable (by norm_num)
  -- the cube average is the Bochner integral of the field itself, and the
  -- Bochner integral commutes with the Hilbert reading
  have havgScalar : volumeAverageVec (openCubeSet Q) G
      = ∫ x : Vec d, G x ∂(normalizedCubeMeasure Q) := by
    funext i
    rw [MeasureTheory.eval_integral hintComp i]
    exact volumeAverage_openCubeSet_eq_integral_normalizedCubeMeasure Q
      (fun x : Vec d => G x i)
  have hcomm : ∫ x : Vec d, hilbertifyVecField G x ∂(normalizedCubeMeasure Q)
      = HilbertVec.ofVec (∫ x : Vec d, G x ∂(normalizedCubeMeasure Q)) :=
    ContinuousLinearEquiv.integral_comp_comm ((HilbertVec.continuousLinearEquivVec d).symm)
      (fun x : Vec d => G x)
  have havg : HilbertVec.ofVec (volumeAverageVec (openCubeSet Q) G)
      = ∫ x : Vec d, hilbertifyVecField G x ∂(normalizedCubeMeasure Q) := by
    rw [hcomm, havgScalar]
  have hnormstep : ENNReal.ofReal (vecNorm (volumeAverageVec (openCubeSet Q) G)) ≤
      ENNReal.ofReal
        (∫ x : Vec d, ‖hilbertifyVecField G x‖ ∂(normalizedCubeMeasure Q)) := by
    rw [vecNorm_eq_norm_ofVec', havg]
    exact ENNReal.ofReal_le_ofReal (norm_integral_le_integral_norm _)
  calc
    ENNReal.ofReal (vecNorm (volumeAverageVec (openCubeSet Q) G)) ≤
        ENNReal.ofReal
          (∫ x : Vec d, ‖hilbertifyVecField G x‖ ∂(normalizedCubeMeasure Q)) := hnormstep
    _ = ∫⁻ x : Vec d, ENNReal.ofReal (‖hilbertifyVecField G x‖) ∂(normalizedCubeMeasure Q) :=
      ofReal_integral_eq_lintegral_ofReal hintHnorm
        (Filter.Eventually.of_forall fun x => norm_nonneg _)
    _ = ∫⁻ x : Vec d, ‖hilbertifyVecField G x‖ₑ ∂(normalizedCubeMeasure Q) :=
      lintegral_congr fun x => ofReal_norm (hilbertifyVecField G x)
    _ = eLpNorm (hilbertifyVecField G) 1 (normalizedCubeMeasure Q) :=
      (eLpNorm_one_eq_lintegral_enorm hmeasH).symm
    _ ≤ eLpNorm (hilbertifyVecField G) q (normalizedCubeMeasure Q) :=
      eLpNorm_le_eLpNorm_of_exponent_le hq
    _ = vecCubeLpENorm Q q G := rfl

/-! ## The centering bound -/

/-- **Centring at the cube mean costs a factor two, in every `L̲^q` norm**
(the `L̲^q` definition together with the
display in the proof of `l.LHS.term1`): for a vector field on the triadic cube `Q` that is square
integrable on the open cube,

> `‖F − (F)_Q‖_{L̲^q(Q)} ≤ 2 ‖F‖_{L̲^q(Q)}`  for `1 ≤ q`.

The proof is the triangle inequality plus Jensen: the constant field `(F)_Q`
has `L̲^q` norm exactly its Euclidean magnitude
(`vecCubeLpENorm_const_eq`), and that magnitude is at most the `L̲^q` norm of
`F` itself (`ofReal_vecNorm_volumeAverageVec_le`), because the normalized cube
measure is a probability measure.  The related `L̲²` statement
`SuperdiffusionCLT.Section3.Terms.vecCubeLpENorm_sub_average_le`
reads the centering against an arbitrary constant instead. -/
theorem vecCubeLpENorm_sub_volumeAverageVec_le {Q : TriadicCube d} {q : ℝ≥0∞}
    {G : Vec d → Vec d} (hq : 1 ≤ q) (hG : MemVectorL2 (openCubeSet Q) G) :
    vecCubeLpENorm Q q (fun x => G x - volumeAverageVec (openCubeSet Q) G) ≤
      2 * vecCubeLpENorm Q q G := by
  classical
  have : IsProbabilityMeasure (normalizedCubeMeasure Q) :=
    ⟨normalizedCubeMeasure_apply_univ Q⟩
  set c : Vec d := volumeAverageVec (openCubeSet Q) G with hc
  have hmeas : AEStronglyMeasurable (hilbertifyVecField G) (normalizedCubeMeasure Q) :=
    aestronglyMeasurable_hilbertifyVecField_of_memVectorL2 hG
  have hq0 : q ≠ 0 := by
    intro h
    rw [h] at hq
    simp at hq
  have hrw : (fun x : Vec d => G x - c) = fun x => G x + (fun _ : Vec d => -c) x := by
    funext x
    show G x - c = G x + -c
    abel
  have htri : vecCubeLpENorm Q q (fun x : Vec d => G x + (fun _ : Vec d => -c) x) ≤
      vecCubeLpENorm Q q G + vecCubeLpENorm Q q (fun _ : Vec d => -c) := by
    refine vecCubeLpENorm_add_le hq hmeas ?_
    show AEStronglyMeasurable (fun _ : Vec d => HilbertVec.ofVec (-c)) _
    exact aestronglyMeasurable_const
  have hneg : vecCubeLpENorm Q q (fun _ : Vec d => -c)
      = ENNReal.ofReal (vecNorm c) := by
    rw [vecCubeLpENorm_neg Q q (fun _ : Vec d => c), vecCubeLpENorm_const_eq hq0 c]
  rw [hrw, two_mul]
  exact htri.trans (add_le_add le_rfl
    (hneg.trans_le (ofReal_vecNorm_volumeAverageVec_le hq hG)))

/-! ## The specialization to the shell flux at `q = 4` -/

/-- The two normalized cube averages of a triadic cube agree: the half-open
cube and the open cube differ by a Lebesgue null set.  Private repetition of
`Section3.ResponseFields.LpEstimates.volumeAverageVec_cubeSet_eq_openCubeSet`,
which is declared in the same namespace in two modules of this directory. -/
private theorem volumeAverageVec_cubeSet_eq_openCubeSet' (Q : TriadicCube d)
    (F : Vec d → Vec d) :
    volumeAverageVec (cubeSet Q) F = volumeAverageVec (openCubeSet Q) F := by
  funext i
  exact volumeAverage_cubeSet_eq_openCubeSet Q (fun x => F x i)

/-- **The `L̲⁴` centering bound for the shell flux** (the deterministic half of
the pointwise clause of the `Zl4` pair, `Section3/Setup/WholeSpaceEnergyOrderOneB.lean`
binder `hZl4Bound`): for
the single-shell flux `j_r p = matVecMul (shellReg omega r x) p` on the triadic
cube `Q`,

> `‖j_r p − (j_r p)_Q‖_{L̲⁴(Q)} ≤ 2 ‖j_r p‖_{L̲⁴(Q)}`.

The square integrability of the shell flux on the open cube is
`Section3.Setup.memVectorL2_shellFlux`. -/
theorem vecCubeLpENorm4_sub_volumeAverageVec_le_shellFlux {Q : TriadicCube d}
    {r : ℕ} {omega : ShellSeq d} {p : Vec d} :
    vecCubeLpENorm Q 4
      (fun x => shellFlux omega r p x -
        volumeAverageVec (cubeSet Q) (shellFlux omega r p)) ≤
      2 * vecCubeLpENorm Q 4 (shellFlux omega r p) := by
  rw [volumeAverageVec_cubeSet_eq_openCubeSet' Q (shellFlux omega r p)]
  exact vecCubeLpENorm_sub_volumeAverageVec_le (by norm_num)
    (memVectorL2_shellFlux Q r omega p)

end

end SuperdiffusionCLT.Section2.Estimates.Stream