/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm1InputsG
public import SuperdiffusionCLT.Section3.Terms.GluedFieldEnergyObservable
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2MeasurabilityB

/-!
# Finiteness and measurability for `l.RHS.term2`: the annealed squared norms of the proxy fields

The statement `SuperdiffusionCLT.Frozen.Section3.rhs_term2` needs the finiteness and the
`AEMeasurable` property of the two annealed squared cube norms of the proxy
fields.  This module proves them, at the data of that statement:

* `term2_ob4_finite`: the two extended integrals
  `∫⁻ omega, ‖∇u_n − ∇ũ_n‖²_{L̲²(cu_m)} ∂P` and
  `∫⁻ omega, ‖∇ũ_n − p̃‖²_{L̲²(cu_m)} ∂P` are finite.
* `term2_ob5_measurableProxy`: the observable
  `omega ↦ ‖∇ũ_n − p̃‖_{L̲²(cu_m)}` is `P`-a.e. measurable.  The
  measurability of the observable of `‖∇u_n − ∇ũ_n‖_{L̲²(cu_m)}` is **not** proved here
  — see the measurability section below.

## The finiteness

The per-sample energy of the glued field is bounded uniformly in the sample:
`volumeAverage_vecNormSq_gluedGradientField_le` of `RHSTerm1InputsG.lean` gives
`⨍_{cu_r} |∇u_k|² ≤ nu^{-2} |F|²` for every intermediate scale `k ≤ r ≤ m`, in
particular for `r = m`.  With `vecNormSq_sub_le` the squared norm of either
proxy field is dominated pointwise in `x` by `2|∇u|² + 2|v|²` with `v` a fixed
vector of the display (the second proxy field `∇ũ_n − p̃` compares the cutoff-`ℓ`
glued field with the constant `p̃`), so
`vecCubeLpENorm cu_m 2 (·)² ≤ ℝ≥0∞.ofReal (constant)` for every sample
(`vecCubeLpENorm_two_sq_le_of_volumeAverage_le`), and the integral over the
probability measure `P` of an `ℝ≥0∞`-valued function dominated by a constant is
dominated by that constant, hence is `≠ ⊤`.  No shell law enters.

## The measurability

The cube energy of the glued field is an explicit measurable quantity:
`measurable_volumeAverage_vecNormSq_gluedGradientField` of
`GluedFieldEnergyObservable.lean` proves
`omega ↦ ⨍_{cu_r} |∇u_k|²` measurable with no selection entering, because it
equals `(1/nu) F · s_{L,*}^{-1}(z + cu_k) F` on every sub-cube
(`volumeAverage_vecNormSq_cubeMaximizerGradient_eq`).  For the second proxy
field `∇ũ_n − p̃` the squared norm expands into the cube mean of the squared
norm of `∇ũ_n`, the pairing of the cube mean of `∇ũ_n` with the constant `p̃`,
and the constant `|p̃|²`.  The cube mean of `∇ũ_n` over `cu_m` is the plain
average of the sub-cube coarse matrices `s_{ℓ,*}^{-1}(z) F`
(`volumeAverageVec_gluedGradientField` read through
`volumeAverage_avsum_openCubeSet`), so every term is measurable in the sample,
and the `AEMeasurable` of the observable itself follows from the squared one by
the identity `‖·‖ = (‖·‖²)^{1/2}` in `ℝ≥0∞`.

For the first proxy field the cube mean of the squared norm of the difference
`∇u_n − ∇ũ_n` contains the cross cube average of the two maximizers
`∇u_{n,z}(a_{L'})` and `∇u_{n,z}(a_ℓ)`, which no identity available here expresses
through the coarse matrices: see the module docstring of `RHSTerm2Glued.lean`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open Homogenization
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section3.ResponseFields
open scoped ENNReal
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-! ## Elementary helpers -/

/-- Pointwise domination lifts to the volume average of an open cube. -/
private theorem volumeAverage_mono_openCubeSet {Q : TriadicCube d} {f g : Vec d → ℝ}
    (hf : IntegrableOn f (openCubeSet Q)) (hg : IntegrableOn g (openCubeSet Q))
    (hfg : ∀ x ∈ openCubeSet Q, f x ≤ g x) :
    volumeAverage (openCubeSet Q) f ≤ volumeAverage (openCubeSet Q) g := by
  refine mul_le_mul_of_nonneg_left ?_
    (inv_nonneg.2 ENNReal.toReal_nonneg)
  exact setIntegral_mono_on hf hg (measurableSet_openCubeSet Q) hfg

/-- The squared norm of the difference of two glued fields of `e.u.k.def` over
the same sub-cube family, averaged over an intermediate cube: bounded uniformly
in the sample by `4 nu^{-2} |F|²`, the pointwise split `vecNormSq_sub_le` applied
to the per-sample energy bound
`volumeAverage_vecNormSq_gluedGradientField_le`. -/
private theorem volumeAverage_vecNormSq_glued_sub_glued_le {nu : ℝ} (hnu : 0 < nu)
    {k m : ℕ} (L₁ L₂ : ℕ) (F : Vec d) (omega : ShellSeq d) {r : ℕ} (hkr : k ≤ r)
    (hrm : r ≤ m) :
    volumeAverage (openCubeSet (originCube d (r : ℤ)))
        (fun x => vecNormSq (gluedGradientField hnu L₁ k m F omega x -
          gluedGradientField hnu L₂ k m F omega x)) ≤
      4 * (nu⁻¹ * nu⁻¹ * vecNormSq F) := by
  classical
  set Q : TriadicCube d := originCube d (r : ℤ) with hQ
  set c : ℝ := nu⁻¹ * nu⁻¹ * vecNormSq F with hc
  have hbound : ∀ L : ℕ, volumeAverage (openCubeSet Q)
      (fun x => vecNormSq (gluedGradientField hnu L k m F omega x)) ≤ c :=
    fun L => volumeAverage_vecNormSq_gluedGradientField_le hnu hkr hrm L F omega
  have hpt : ∀ (x : Vec d), vecNormSq
      (gluedGradientField hnu L₁ k m F omega x -
        gluedGradientField hnu L₂ k m F omega x) ≤
      2 * vecNormSq (gluedGradientField hnu L₁ k m F omega x) +
        2 * vecNormSq (gluedGradientField hnu L₂ k m F omega x) := by
    intro x
    exact (vecNormSq_sub_le _ _).trans (by ring_nf; linarith only [])
  have hint1 : IntegrableOn (fun x => vecNormSq
      (gluedGradientField hnu L₁ k m F omega x -
        gluedGradientField hnu L₂ k m F omega x)) (openCubeSet Q) volume := by
    have hmem : MemVectorL2 (openCubeSet Q)
        (fun x => gluedGradientField hnu L₁ k m F omega x -
          gluedGradientField hnu L₂ k m F omega x) :=
      (memVectorL2_openCubeSet_gluedGradientField hnu L₁ k m F omega Q).sub
        (memVectorL2_openCubeSet_gluedGradientField hnu L₂ k m F omega Q)
    exact integrableOn_vecDot_of_memVectorL2 hmem hmem
  have hint2 : IntegrableOn (fun x => 2 *
      vecNormSq (gluedGradientField hnu L₁ k m F omega x) +
      2 * vecNormSq (gluedGradientField hnu L₂ k m F omega x)) (openCubeSet Q) volume :=
    ((integrableOn_vecNormSq_gluedGradientField hnu L₁ k m F omega Q).const_mul 2).add
      ((integrableOn_vecNormSq_gluedGradientField hnu L₂ k m F omega Q).const_mul 2)
  have hsmul : ∀ (f : Vec d → ℝ), volumeAverage (openCubeSet Q) (fun x => 2 * f x)
      = 2 * volumeAverage (openCubeSet Q) f := by
    intro f
    rw [show (fun x => 2 * f x) = (2 : ℝ) • f from rfl, volumeAverage_smul]
  have hsum : volumeAverage (openCubeSet Q)
      (fun x => 2 * vecNormSq (gluedGradientField hnu L₁ k m F omega x) +
        2 * vecNormSq (gluedGradientField hnu L₂ k m F omega x))
      = 2 * volumeAverage (openCubeSet Q)
          (fun x => vecNormSq (gluedGradientField hnu L₁ k m F omega x)) +
        2 * volumeAverage (openCubeSet Q)
          (fun x => vecNormSq (gluedGradientField hnu L₂ k m F omega x)) := by
    have hA := (integrableOn_vecNormSq_gluedGradientField hnu L₁ k m F omega Q).const_mul 2
    have hB := (integrableOn_vecNormSq_gluedGradientField hnu L₂ k m F omega Q).const_mul 2
    rw [show (fun x => 2 * vecNormSq (gluedGradientField hnu L₁ k m F omega x) +
        2 * vecNormSq (gluedGradientField hnu L₂ k m F omega x))
        = (fun x => 2 * vecNormSq (gluedGradientField hnu L₁ k m F omega x)) +
          (fun x => 2 * vecNormSq (gluedGradientField hnu L₂ k m F omega x)) from rfl,
      volumeAverage_add hA hB, hsmul, hsmul]
  refine le_trans (volumeAverage_mono_openCubeSet hint1 hint2 (fun x _ => hpt x)) ?_
  rw [hsum]
  have h1 := hbound L₁
  have h2 := hbound L₂
  have hc0 : (0 : ℝ) ≤ c := by
    rw [hc]
    have := vecNormSq_nonneg F
    have hi : (0 : ℝ) ≤ nu⁻¹ := le_of_lt (inv_pos.2 hnu)
    positivity
  rw [hc] at h1 h2
  linarith only [h1, h2, hc0]

/-- The squared norm of the glued field of `e.u.k.def` shifted by a constant
vector, averaged over an intermediate cube: bounded uniformly in the sample by
`2 nu^{-2} |F|² + 2 |c|²`. -/
private theorem volumeAverage_vecNormSq_glued_sub_const_le {nu : ℝ} (hnu : 0 < nu)
    (L k m : ℕ) (F : Vec d) (omega : ShellSeq d) (c : Vec d) {r : ℕ} (hkr : k ≤ r)
    (hrm : r ≤ m) :
    volumeAverage (openCubeSet (originCube d (r : ℤ)))
        (fun x => vecNormSq (gluedGradientField hnu L k m F omega x - c)) ≤
      2 * (nu⁻¹ * nu⁻¹ * vecNormSq F) + 2 * vecNormSq c := by
  classical
  set Q : TriadicCube d := originCube d (r : ℤ) with hQ
  set cE : ℝ := nu⁻¹ * nu⁻¹ * vecNormSq F with hcE
  have hbound : volumeAverage (openCubeSet Q)
      (fun x => vecNormSq (gluedGradientField hnu L k m F omega x)) ≤ cE :=
    volumeAverage_vecNormSq_gluedGradientField_le hnu hkr hrm L F omega
  have hpt : ∀ (x : Vec d), vecNormSq
      (gluedGradientField hnu L k m F omega x - c) ≤
      2 * vecNormSq (gluedGradientField hnu L k m F omega x) + 2 * vecNormSq c := by
    intro x
    exact (vecNormSq_sub_le _ _).trans (by ring_nf; linarith only [])
  have hint1 : IntegrableOn (fun x => vecNormSq
      (gluedGradientField hnu L k m F omega x - c)) (openCubeSet Q) volume := by
    have hfin : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) := by
      refine ⟨?_⟩
      rw [MeasureTheory.Measure.restrict_apply_univ]
      exact volume_openCubeSet_lt_top Q
    have hmem : MemVectorL2 (openCubeSet Q)
        (fun x => gluedGradientField hnu L k m F omega x - c) :=
      (memVectorL2_openCubeSet_gluedGradientField hnu L k m F omega Q).sub
        (memVectorL2_const c)
    exact integrableOn_vecDot_of_memVectorL2 hmem hmem
  have hint2 : IntegrableOn (fun x => 2 *
      vecNormSq (gluedGradientField hnu L k m F omega x) + 2 * vecNormSq c)
      (openCubeSet Q) volume :=
    ((integrableOn_vecNormSq_gluedGradientField hnu L k m F omega Q).const_mul 2).add
      (integrableOn_const (μ := volume) (s := openCubeSet Q)
        (ne_of_lt (volume_openCubeSet_lt_top Q)))
  have hsmul : ∀ (f : Vec d → ℝ), volumeAverage (openCubeSet Q) (fun x => 2 * f x)
      = 2 * volumeAverage (openCubeSet Q) f := by
    intro f
    rw [show (fun x => 2 * f x) = (2 : ℝ) • f from rfl, volumeAverage_smul]
  have hsum : volumeAverage (openCubeSet Q)
      (fun x => 2 * vecNormSq (gluedGradientField hnu L k m F omega x) + 2 * vecNormSq c)
      = 2 * volumeAverage (openCubeSet Q)
          (fun x => vecNormSq (gluedGradientField hnu L k m F omega x)) + 2 * vecNormSq c := by
    have hA := (integrableOn_vecNormSq_gluedGradientField hnu L k m F omega Q).const_mul 2
    have hB : IntegrableOn (fun _ : Vec d => 2 * vecNormSq c) (openCubeSet Q) volume :=
      integrableOn_const (μ := volume) (s := openCubeSet Q)
        (ne_of_lt (volume_openCubeSet_lt_top Q))
    have hvolR : (0 : ℝ) < (volume (openCubeSet Q)).toReal :=
      ENNReal.toReal_pos (SuperdiffusionCLT.Section3.ResponseFields.volume_openCubeSet_ne_zero Q)
        (ne_top_of_lt (volume_openCubeSet_lt_top Q))
    rw [show (fun x => 2 * vecNormSq (gluedGradientField hnu L k m F omega x) + 2 * vecNormSq c)
        = (fun x => 2 * vecNormSq (gluedGradientField hnu L k m F omega x)) +
          (fun _ : Vec d => 2 * vecNormSq c) from rfl,
      volumeAverage_add hA hB, hsmul,
      show volumeAverage (openCubeSet Q) (fun _ : Vec d => 2 * vecNormSq c)
        = 2 * vecNormSq c from volumeAverage_const hvolR.ne']
  refine le_trans (volumeAverage_mono_openCubeSet hint1 hint2 (fun x _ => hpt x)) ?_
  rw [hsum]
  have hcE0 : (0 : ℝ) ≤ cE := by
    rw [hcE]
    have := vecNormSq_nonneg F
    have hi : (0 : ℝ) ≤ nu⁻¹ := le_of_lt (inv_pos.2 hnu)
    positivity
  rw [hcE] at hbound
  have hcn : (0 : ℝ) ≤ vecNormSq c := vecNormSq_nonneg c
  linarith only [hbound, hcE0, hcn]

/-- A squared cube norm dominated uniformly in the sample gives a finite
extended integral over a probability measure: the uniform real bound `c` reads
as the constant `ℝ≥0∞.ofReal c`, whose integral over a probability measure is
itself. -/
private theorem lintegral_vecCubeLpENorm_sq_ne_top {P : ProbabilityMeasure (ShellSeq d)}
    {Q : TriadicCube d} {V : ShellSeq d → Vec d → Vec d} {c : ℝ}
    (hmem : ∀ omega : ShellSeq d, MemVectorL2 (openCubeSet Q) (V omega))
    (h : ∀ omega : ShellSeq d, volumeAverage (openCubeSet Q)
        (fun x => vecNormSq (V omega x)) ≤ c) :
    (∫⁻ omega : ShellSeq d, vecCubeLpENorm Q 2 (V omega) ^ (2 : ℕ) ∂P.toMeasure) ≠ ⊤ := by
  have hstep : ∀ omega : ShellSeq d, vecCubeLpENorm Q 2 (V omega) ^ (2 : ℕ)
      ≤ ENNReal.ofReal c := fun omega =>
    vecCubeLpENorm_two_sq_le_of_volumeAverage_le (hmem omega) (h omega)
  have hdom : (∫⁻ omega : ShellSeq d, vecCubeLpENorm Q 2 (V omega) ^ (2 : ℕ)
      ∂P.toMeasure) ≤ (∫⁻ omega : ShellSeq d, (ENNReal.ofReal c : ℝ≥0∞) ∂P.toMeasure) :=
    lintegral_mono hstep
  have hconst : (∫⁻ omega : ShellSeq d, (ENNReal.ofReal c : ℝ≥0∞) ∂P.toMeasure)
      = ENNReal.ofReal c := by
    rw [lintegral_const, MeasureTheory.measure_univ, mul_one]
  have hlt : (∫⁻ omega : ShellSeq d, (ENNReal.ofReal c : ℝ≥0∞) ∂P.toMeasure) < ⊤ := by
    rw [hconst]
    exact ENNReal.ofReal_lt_top
  exact (lt_of_le_of_lt hdom hlt).ne_top

/-! ## Elementary algebra of the Euclidean pairing -/

/-- The Euclidean pairing is symmetric. -/
private theorem vecDot_comm (x y : Vec d) : vecDot x y = vecDot y x := by
  show ∑ i, x i * y i = ∑ i, y i * x i
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The squared Euclidean norm of a shifted vector, in terms of the pairing of
the vector with the shift. -/
private theorem vecNormSq_sub_const (u c : Vec d) :
    vecNormSq (u - c) = vecNormSq u - 2 * vecDot u c + vecNormSq c := by
  have h1 : vecDot u (u - c) = vecDot u u - vecDot u c := by
    rw [vecDot_comm, vecDot_sub_left', vecDot_comm c u]
  have h2 : vecDot c (u - c) = vecDot u c - vecDot c c := by
    rw [vecDot_comm, vecDot_sub_left', vecDot_comm u c]
  show vecDot (u - c) (u - c) = _
  rw [vecDot_sub_left', h2, h1, vecNormSq, vecNormSq]
  ring

/-- The cube average of the squared norm of a shifted `L²` field, in terms of
the three cube observables of the field and of the shift: the polarization
`|g − c|² = |g|² − 2 g · c + |c|²`, with the cross cube average read as the
pairing of the cube mean of `g` with `c`. -/
private theorem volumeAverage_vecNormSq_sub_const_eq {Q : TriadicCube d}
    (g : Vec d → Vec d) (c : Vec d) (hmem : MemVectorL2 (openCubeSet Q) g)
    (hvol : (MeasureTheory.volume (openCubeSet Q)).toReal ≠ 0) :
    volumeAverage (openCubeSet Q) (fun x => vecNormSq (g x - c)) =
      volumeAverage (openCubeSet Q) (fun x => vecNormSq (g x))
        - 2 * vecDot (volumeAverageVec (openCubeSet Q) g) c + vecNormSq c := by
  classical
  have hintComp : ∀ i : Fin d, IntegrableOn (fun x => g x i) (openCubeSet Q) volume :=
    fun i => (memL2On_component_of_memVectorL2 hmem i).integrable
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hint1 : IntegrableOn (fun x => vecNormSq (g x)) (openCubeSet Q) volume :=
    integrableOn_vecDot_of_memVectorL2 hmem hmem
  have hint2 : IntegrableOn (fun x => vecDot (g x) c) (openCubeSet Q) volume :=
    integrableOn_vecDot_of_memVectorL2 hmem (memVectorL2_const c)
  have hint3 : IntegrableOn (fun _ : Vec d => vecNormSq c) (openCubeSet Q) volume :=
    integrableOn_const (μ := volume) (s := openCubeSet Q)
      (ne_of_lt (volume_openCubeSet_lt_top Q))
  have hcross : vecDot (volumeAverageVec (openCubeSet Q) g) c =
      volumeAverage (openCubeSet Q) (fun x => vecDot (g x) c) := by
    rw [show (fun x : Vec d => vecDot (g x) c) = fun x => vecDot c (g x) from
        funext fun x => vecDot_comm (g x) c,
      volumeAverage_vecDot_const_left c hintComp,
      vecDot_comm c (volumeAverageVec (openCubeSet Q) g)]
  have hsmul : IntegrableOn ((2 : ℝ) • (fun x => vecDot (g x) c)) (openCubeSet Q) volume := by
    exact hint2.const_mul 2
  have hf' : IntegrableOn (fun x => vecNormSq (g x) - 2 * vecDot (g x) c)
      (openCubeSet Q) volume := hint1.sub (hint2.const_mul 2)
  have hmain : volumeAverage (openCubeSet Q)
      (fun x => vecNormSq (g x) - 2 * vecDot (g x) c + vecNormSq c) =
      volumeAverage (openCubeSet Q) (fun x => vecNormSq (g x))
        - 2 * volumeAverage (openCubeSet Q) (fun x => vecDot (g x) c) + vecNormSq c := by
    calc volumeAverage (openCubeSet Q)
          (fun x => vecNormSq (g x) - 2 * vecDot (g x) c + vecNormSq c)
        = volumeAverage (openCubeSet Q) (fun x => vecNormSq (g x) - 2 * vecDot (g x) c) +
            volumeAverage (openCubeSet Q) (fun _ : Vec d => vecNormSq c) :=
          volumeAverage_add hf' hint3
      _ = (volumeAverage (openCubeSet Q) (fun x => vecNormSq (g x)) -
            2 * volumeAverage (openCubeSet Q) (fun x => vecDot (g x) c)) +
            volumeAverage (openCubeSet Q) (fun _ : Vec d => vecNormSq c) := by
          rw [show volumeAverage (openCubeSet Q)
                (fun x => vecNormSq (g x) - 2 * vecDot (g x) c) =
              volumeAverage (openCubeSet Q) (fun x => vecNormSq (g x)) -
                volumeAverage (openCubeSet Q) ((2 : ℝ) • (fun x => vecDot (g x) c)) from
            volumeAverage_sub hint1 hsmul,
            show volumeAverage (openCubeSet Q) ((2 : ℝ) • (fun x => vecDot (g x) c)) =
              2 * volumeAverage (openCubeSet Q) (fun x => vecDot (g x) c) from
            volumeAverage_smul (openCubeSet Q) (2 : ℝ) (fun x => vecDot (g x) c)]
      _ = _ := by
          rw [volumeAverage_const hvol]
  calc volumeAverage (openCubeSet Q) (fun x => vecNormSq (g x - c))
      = volumeAverage (openCubeSet Q)
          (fun x => vecNormSq (g x) - 2 * vecDot (g x) c + vecNormSq c) := by
        refine congrArg (volumeAverage (openCubeSet Q)) ?_
        exact funext fun x => vecNormSq_sub_const (g x) c
    _ = volumeAverage (openCubeSet Q) (fun x => vecNormSq (g x))
          - 2 * vecDot (volumeAverageVec (openCubeSet Q) g) c + vecNormSq c := by
        rw [hmain, hcross]

/-! ## The finiteness of the two annealed squared cube norms -/

/-- **Finiteness for `l.RHS.term2`**: the two annealed squared cube norms
of the proxy fields are finite.  Each squared cube norm is dominated uniformly
in the sample (`volumeAverage_vecNormSq_glued_sub_glued_le`, resp.
`volumeAverage_vecNormSq_glued_sub_const_le`), and a uniformly dominated
squared cube norm integrates over a probability measure to a finite value
(`lintegral_vecCubeLpENorm_sq_ne_top`). -/
theorem term2_ob4_finite [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection)
    (hS : ScalesOrdering S) (e : Vec d) :
    ((∫⁻ omega : ShellSeq d,
            vecCubeLpENorm (originCube d (S.m : ℤ)) 2
                (fun x => gluedGradientField hnu S.LPrime S.n S.m
                    (fluxSlot nu S.LPrime P S.n e) omega x -
                  gluedGradientField hnu S.ell S.n S.m
                    (fluxSlot nu S.LPrime P S.n e) omega x) ^ (2 : ℕ)
          ∂P.toMeasure) ≠ ⊤) ∧
        ((∫⁻ omega : ShellSeq d,
            vecCubeLpENorm (originCube d (S.m : ℤ)) 2
                (fun x => gluedGradientField hnu S.ell S.n S.m
                    (fluxSlot nu S.LPrime P S.n e) omega x -
                  annealedGluedAverage hnu P S.ell S.n S.m
                    (fluxSlot nu S.LPrime P S.n e)) ^ (2 : ℕ)
          ∂P.toMeasure) ≠ ⊤) := by
  classical
  set F : Vec d := fluxSlot nu S.LPrime P S.n e
  have hnm : S.n ≤ S.m := by
    have h1 := hS.n_lt_ell
    have h2 := hS.ell_lt_ellPrime
    have h3 := hS.ellPrime_lt_m
    omega
  refine ⟨?_, ?_⟩
  · exact lintegral_vecCubeLpENorm_sq_ne_top
      (P := P) (Q := originCube d (S.m : ℤ))
      (V := fun omega x => gluedGradientField hnu S.LPrime S.n S.m F omega x -
        gluedGradientField hnu S.ell S.n S.m F omega x)
      (c := 4 * (nu⁻¹ * nu⁻¹ * vecNormSq F))
      (fun omega => (memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.n S.m F omega
          (originCube d (S.m : ℤ))).sub
        (memVectorL2_openCubeSet_gluedGradientField hnu S.ell S.n S.m F omega
          (originCube d (S.m : ℤ))))
      (fun omega => volumeAverage_vecNormSq_glued_sub_glued_le hnu S.LPrime S.ell F omega
        hnm (le_refl S.m))
  · exact lintegral_vecCubeLpENorm_sq_ne_top
      (P := P) (Q := originCube d (S.m : ℤ))
      (V := fun omega x => gluedGradientField hnu S.ell S.n S.m F omega x -
        annealedGluedAverage hnu P S.ell S.n S.m F)
      (c := 2 * (nu⁻¹ * nu⁻¹ * vecNormSq F) +
        2 * vecNormSq (annealedGluedAverage hnu P S.ell S.n S.m F))
      (fun omega => (memVectorL2_openCubeSet_gluedGradientField hnu S.ell S.n S.m F omega
          (originCube d (S.m : ℤ))).sub
        (memVectorL2_const (annealedGluedAverage hnu P S.ell S.n S.m F)))
      (fun omega => volumeAverage_vecNormSq_glued_sub_const_le hnu S.ell S.n S.m F omega
        (annealedGluedAverage hnu P S.ell S.n S.m F) hnm (le_refl S.m))

/-! ## Measurability of the proxy norm: the machinery -/

/-- One component of the matrix action on a fixed vector is measurable when the
matrix entries are. -/
private theorem measurable_matVecMul_apply_of_entries {Omega : Type*}
    [MeasurableSpace Omega] {M : Omega → Mat d}
    (hM : ∀ i j, Measurable fun omega => M omega i j) (F : Vec d) (i : Fin d) :
    Measurable fun omega => matVecMul (M omega) F i := by
  simp only [matVecMul]
  exact Finset.measurable_sum _ fun j _ => (hM i j).mul_const (F j)

/-- Pairing a fixed vector with a vector-valued map with measurable components
is measurable. -/
private theorem measurable_vecDot_const_left {Omega : Type*} [MeasurableSpace Omega]
    (F : Vec d) {v : Omega → Vec d} (hv : ∀ i, Measurable fun omega => v omega i) :
    Measurable fun omega => vecDot F (v omega) := by
  simp only [vecDot]
  exact Finset.measurable_sum _ fun i _ => (hv i).const_mul (F i)

/-- One component of the coarse matrix of the cutoff field applied to a fixed
vector is measurable in the sample: the measurability of the entries of
`s_{L,*}^{-1}(z + cu_k)` (`measurable_sigmaStarInvCoarse_apply` at the cutoff
field) read through the matrix action. -/
private theorem measurable_matVecMul_apply_sigmaStarInvCoarse [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (L : ℕ) (F : Vec d) (z : TriadicCube d) (i : Fin d) :
    Measurable (fun omega : ShellSeq d =>
      matVecMul (sigmaStarInvCoarse (openCubeSet z)
        (coefficientCutoff nu omega L).toCoeffField) F i) := by
  have hM : ∀ r c : Fin d, Measurable (fun omega : ShellSeq d =>
      sigmaStarInvCoarse (openCubeSet z)
        (coefficientCutoff nu omega L).toCoeffField r c) := by
    intro r c
    exact @measurable_sigmaStarInvCoarse_apply d _ (ShellSeq d) _
      (fun omega : ShellSeq d => coefficientCutoff nu omega L)
      (measurable_coefficientCutoff nu L)
      (fun omega => aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega L) z r c
  exact measurable_matVecMul_apply_of_entries hM F i

/-- The square root in `ℝ≥0∞`: `y = (y²)^{1/2}`. -/
private theorem ennreal_sqrt_sq (y : ℝ≥0∞) : (y ^ (2 : ℕ)) ^ ((1 : ℝ) / 2) = y := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
    show ((2 : ℕ) : ℝ) * ((1 : ℝ) / 2) = 1 from by norm_num, ENNReal.rpow_one]

/-! ## Measurability of `‖∇ũ_n − p̃‖` -/

/-- **Measurability for `l.RHS.term2`, proxy half**: the observable
`omega ↦ ‖∇ũ_n − p̃‖_{L̲²(cu_m)}` is `P`-a.e. measurable.  The squared observable
is the `ℝ≥0∞.ofReal` of the polarized cube energy
`⨍|∇ũ_n|² − 2 (⨍∇ũ_n)·p̃ + |p̃|²` (`volumeAverage_vecNormSq_sub_const_eq`); the
first summand is measurable
(`measurable_volumeAverage_vecNormSq_gluedGradientField`), the pairing is
measurable because the cube mean of `∇ũ_n` is the plain average of the
sub-cube coarse matrices applied to the flux slot
(`volumeAverageVec_gluedGradientField` through
`volumeAverage_avsum_openCubeSet`), and the last summand is constant.  The
observable itself is the square root of the squared one in `ℝ≥0∞`
(`ennreal_sqrt_sq`).  No selection of a solution enters.

The measurability of the observable of `‖∇u_n − ∇ũ_n‖_{L̲²(cu_m)}` is not
proved here: its squared observable contains the cross cube average of the
two maximizers `∇u_{n,z}(a_{L'})` and `∇u_{n,z}(a_ℓ)`, which no identity available here
expresses through the coarse matrices (see the module docstring of
`RHSTerm2Glued.lean`). -/
theorem term2_ob5_measurableProxy [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection)
    (hS : ScalesOrdering S) (e : Vec d) :
    AEMeasurable (fun omega : ShellSeq d =>
        vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (fun x => gluedGradientField hnu S.ell S.n S.m
                (fluxSlot nu S.LPrime P S.n e) omega x -
              annealedGluedAverage hnu P S.ell S.n S.m
                (fluxSlot nu S.LPrime P S.n e))) P.toMeasure := by
  classical
  set F : Vec d := fluxSlot nu S.LPrime P S.n e
  set A : Vec d := annealedGluedAverage hnu P S.ell S.n S.m F
  set Q : TriadicCube d := originCube d (S.m : ℤ)
  have hnm : S.n ≤ S.m := by
    have h1 := hS.n_lt_ell
    have h2 := hS.ell_lt_ellPrime
    have h3 := hS.ellPrime_lt_m
    omega
  have hvol : (MeasureTheory.volume (openCubeSet Q)).toReal ≠ 0 :=
    ne_of_gt (ENNReal.toReal_pos
      (SuperdiffusionCLT.Section3.ResponseFields.volume_openCubeSet_ne_zero Q)
      (ne_top_of_lt (volume_openCubeSet_lt_top Q)))
  -- the two measurable ingredients: the energy and the pairing with `p̃`
  have h1 : Measurable (fun omega : ShellSeq d =>
      volumeAverage (openCubeSet Q)
        (fun x => vecNormSq (gluedGradientField hnu S.ell S.n S.m F omega x))) :=
    measurable_volumeAverage_vecNormSq_gluedGradientField hnu hnm (le_refl S.m) S.ell F
  have hcomp : ∀ i : Fin d, Measurable (fun omega : ShellSeq d =>
      volumeAverageVec (openCubeSet Q)
        (fun x => gluedGradientField hnu S.ell S.n S.m F omega x) i) := by
    intro i
    have hint : ∀ (omega : ShellSeq d) (R : TriadicCube d),
        R ∈ largeCubeSubcubes d S.n S.m →
        IntegrableOn (fun x => gluedGradientField hnu S.ell S.n S.m F omega x i)
          (openCubeSet R) volume :=
      fun omega R hR =>
        (memL2On_component_of_memVectorL2
          (memVectorL2_openCubeSet_gluedGradientField hnu S.ell S.n S.m F omega R) i).integrable
          (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hEq : (fun omega : ShellSeq d =>
        volumeAverageVec (openCubeSet Q)
          (fun x => gluedGradientField hnu S.ell S.n S.m F omega x) i) =
      fun omega : ShellSeq d => ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
        ∑ R ∈ largeCubeSubcubes d S.n S.m,
          volumeAverage (openCubeSet R)
            (fun x => gluedGradientField hnu S.ell S.n S.m F omega x i) := by
      funext omega
      show volumeAverage (openCubeSet Q)
        (fun x => gluedGradientField hnu S.ell S.n S.m F omega x i) = _
      exact volumeAverage_avsum_openCubeSet (hint omega)
    rw [hEq]
    refine (Finset.measurable_sum _ ?_).const_mul _
    intro R hR
    have hkey : (fun omega : ShellSeq d =>
        volumeAverage (openCubeSet R)
          (fun x => gluedGradientField hnu S.ell S.n S.m F omega x i)) =
      fun omega : ShellSeq d =>
        (matVecMul (sigmaStarInvCoarse (openCubeSet R)
          (coefficientCutoff nu omega S.ell).toCoeffField) F) i := by
      funext omega
      show volumeAverage (openCubeSet R)
        (fun x => gluedGradientField hnu S.ell S.n S.m F omega x i) = _
      rw [show volumeAverage (openCubeSet R)
          (fun x => gluedGradientField hnu S.ell S.n S.m F omega x i) =
        volumeAverageVec (openCubeSet R)
          (fun x => gluedGradientField hnu S.ell S.n S.m F omega x) i from rfl,
        volumeAverageVec_gluedGradientField hnu S.ell S.n S.m F omega hR]
    rw [hkey]
    exact measurable_matVecMul_apply_sigmaStarInvCoarse hnu S.ell F R i
  have h2 : Measurable (fun omega : ShellSeq d =>
      vecDot (volumeAverageVec (openCubeSet Q)
        (fun x => gluedGradientField hnu S.ell S.n S.m F omega x)) A) := by
    rw [show (fun omega : ShellSeq d =>
        vecDot (volumeAverageVec (openCubeSet Q)
          (fun x => gluedGradientField hnu S.ell S.n S.m F omega x)) A) =
      fun omega : ShellSeq d => vecDot A (volumeAverageVec (openCubeSet Q)
        (fun x => gluedGradientField hnu S.ell S.n S.m F omega x)) from
      funext fun omega => vecDot_comm _ _]
    exact measurable_vecDot_const_left A hcomp
  -- the squared observable is the `ofReal` of the polarized cube energy
  have hEmeas : Measurable (fun omega : ShellSeq d =>
      volumeAverage (openCubeSet Q)
        (fun x => vecNormSq (gluedGradientField hnu S.ell S.n S.m F omega x - A))) := by
    have hmemG : ∀ omega : ShellSeq d, MemVectorL2 (openCubeSet Q)
        (fun x => gluedGradientField hnu S.ell S.n S.m F omega x) :=
      fun omega => memVectorL2_openCubeSet_gluedGradientField hnu S.ell S.n S.m F omega Q
    rw [show (fun omega : ShellSeq d =>
        volumeAverage (openCubeSet Q)
          (fun x => vecNormSq (gluedGradientField hnu S.ell S.n S.m F omega x - A))) =
      fun omega : ShellSeq d =>
        volumeAverage (openCubeSet Q)
          (fun x => vecNormSq (gluedGradientField hnu S.ell S.n S.m F omega x)) -
        2 * vecDot (volumeAverageVec (openCubeSet Q)
          (fun x => gluedGradientField hnu S.ell S.n S.m F omega x)) A + vecNormSq A from
      funext fun omega => volumeAverage_vecNormSq_sub_const_eq _ _ (hmemG omega) hvol]
    exact (h1.sub (h2.const_mul 2)).add_const (vecNormSq A)
  have hsqMeas : Measurable (fun omega : ShellSeq d =>
      vecCubeLpENorm Q 2
        (fun x => gluedGradientField hnu S.ell S.n S.m F omega x - A) ^ (2 : ℕ)) := by
    have hmemV : ∀ omega : ShellSeq d, MemVectorL2 (openCubeSet Q)
        (fun x => gluedGradientField hnu S.ell S.n S.m F omega x - A) :=
      fun omega => (memVectorL2_openCubeSet_gluedGradientField hnu S.ell S.n S.m F omega Q).sub
        (memVectorL2_const A)
    have hEq : (fun omega : ShellSeq d =>
        vecCubeLpENorm Q 2
          (fun x => gluedGradientField hnu S.ell S.n S.m F omega x - A) ^ (2 : ℕ)) =
      fun omega : ShellSeq d =>
        ENNReal.ofReal (volumeAverage (openCubeSet Q)
          (fun x => vecNormSq (gluedGradientField hnu S.ell S.n S.m F omega x - A))) := by
      funext omega
      rw [vecCubeLpENorm_two_sq_eq_ofReal (hmemV omega)]
      exact congrArg ENNReal.ofReal
        (volumeAverage_openCubeSet_eq_integral_normalizedCubeMeasure Q
          (fun x => vecNormSq (gluedGradientField hnu S.ell S.n S.m F omega x - A))).symm
    rw [hEq]
    exact (ENNReal.measurable_ofReal).comp hEmeas
  -- the observable is the square root of the squared one in `ℝ≥0∞`
  rw [show (fun omega : ShellSeq d =>
      vecCubeLpENorm Q 2
        (fun x => gluedGradientField hnu S.ell S.n S.m F omega x - A)) =
    fun omega : ShellSeq d =>
      (vecCubeLpENorm Q 2
        (fun x => gluedGradientField hnu S.ell S.n S.m F omega x - A) ^ (2 : ℕ)) ^
        ((1 : ℝ) / 2) from
    funext fun omega => (ennreal_sqrt_sq _).symm]
  exact ((ENNReal.continuous_rpow_const (y := (1 : ℝ) / 2)).measurable.comp
    hsqMeas).aemeasurable

end

end SuperdiffusionCLT.Section3.Terms