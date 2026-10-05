/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Norms.MultiscalePoincareFullGradient
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementMoreoverBlockC

/-!
# The joint scale-and-centre maximum and the negative-norm term

`IncrementMoreoverBlockC` bounds
the coarse-average envelope of the limiting centered field over a scale-`n`
sub-cube of `cu_m`, at **one** scale `n`. The
"Moreover" block quantifies over the whole logarithmic window of scales
`n ∈ [m - h, m]` as well as over the centres, and its third term is the
negative norm of the same field. This module supplies both.

## The joint maximum

The window is one `Finset (ℕ × TriadicCube d)`, the disjoint union
`centeredScaleWindow` of the scale-`n` families over `n ∈ Icc (m-h) m`, and the
maximum is a **single** `Finset.sup'` over it. Composing two finite maxima —
first over the centres at each scale and then over the scales — would cost a
second factor `(3 log (h+1))^{1/2}`; one maximum over the union costs only the
logarithm of the total cardinality,

`log N ≤ log (h+1) + d h log 3 ≤ (1 + d log 3) h`,

so the union bound is at `(3 (1 + d log 3))^{1/2} h^{1/2}` times the common
one-element amplitude `C(d) h^{1/2}`, that is at `C(d) h`. This is the printed
`O_{Γ₂}(C h)` of `e.bounding.the.diff.of.k.union`.

The common one-element amplitude needs the scale `n = m`, which
`IncrementMoreoverBlockC` excludes (its tail hypothesis is `n < m`). At that
scale the window has the single member `cu_m`, whose centre is the origin, and
the coarse-average difference of the infrared cutoff vanishes identically, so
the envelope is exactly `d √d` times the derivative tail gauge, whose uniform
`Γ₂` amplitude is bounded in `ShellDerivTailGauge`.

## The negative-norm term

The depth sums of `MultiscalePoincareFullGradient` have as depth
averages exactly the coarse averages above: the depth-`j` descendants of `cu_m`
are its scale-`(m-j)` sub-cubes. Inside the window `j ≤ h` every one of them is
below the joint maximum; below the window the coarse averages are bounded by
the `L∞` datum of the same block, at the dimension factor of
`matrixOperatorNorm_le_of_entry_bound`. The geometric weight `3^{-sj}` sums the
two into one bound on `cubeMultiscaleDepthSum`, which is the input the printed
negative-norm estimate of the "Moreover" block takes.

The multiscale Poincaré bridge for the printed **un-normalized** negative-norm carrier is
**not** proved here: `MultiscalePoincareFullGradient` proves the bridge for the normalized carrier and for
a continuous field.

## Main definitions and results

* `centeredScaleWindow`, `centeredScaleCubeMax`: the joint index set and the
  joint maximum.
* `matrixOperatorNorm_volumeAverageMat_centeredStreamField_le_scaleMax`: one
  random variable dominates every coarse average of the window at once.
* `cubeDepthPthMoment_rpow_le_centeredScaleCubeMax`,
  `cubeDepthPthMoment_rpow_le_of_entry_bound`: the depth moments fed by the
  joint maximum and by the `L∞` datum.

## References

* `e.Xm.deff`, `e.bounding.the.diff.of.k.union`.
-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Section2
namespace Estimates
namespace Stream

open Homogenization MeasureTheory
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Carriers
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open scoped ENNReal
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}
variable {P : ProbabilityMeasure (ℕ → ShellField d)}

/-! ## The joint window of scales and centres -/

/-- The joint index set of the printed union bound: all pairs `(n, Q)` with
`n` in the window `[m - h, m]` and `Q` a scale-`n` sub-cube of `cu_m`. -/
def centeredScaleWindow (d h m : ℕ) : Finset (ℕ × TriadicCube d) :=
  (Finset.Icc (m - h) m).biUnion fun n =>
    (largeCubeSubcubes d n m).image fun Q => (n, Q)

theorem mem_centeredScaleWindow {d h m n : ℕ} {Q : TriadicCube d}
    (hn : n ∈ Finset.Icc (m - h) m) (hQ : Q ∈ largeCubeSubcubes d n m) :
    (n, Q) ∈ centeredScaleWindow d h m :=
  Finset.mem_biUnion.2 ⟨n, hn, Finset.mem_image.2 ⟨Q, hQ, rfl⟩⟩

theorem centeredScaleWindow_nonempty (d h m : ℕ) :
    (centeredScaleWindow d h m).Nonempty := by
  obtain ⟨Q, hQ⟩ := largeCubeSubcubes_nonempty d m m
  exact ⟨(m, Q), mem_centeredScaleWindow (Finset.mem_Icc.2 ⟨Nat.sub_le m h, le_rfl⟩) hQ⟩

theorem mem_Icc_of_mem_centeredScaleWindow {d h m n : ℕ} {Q : TriadicCube d}
    (hp : (n, Q) ∈ centeredScaleWindow d h m) :
    n ∈ Finset.Icc (m - h) m ∧ Q ∈ largeCubeSubcubes d n m := by
  obtain ⟨n', hn', hQ'⟩ := Finset.mem_biUnion.1 hp
  obtain ⟨R, hR, hRe⟩ := Finset.mem_image.1 hQ'
  have h1 : n' = n := congrArg Prod.fst hRe
  have h2 : R = Q := congrArg Prod.snd hRe
  subst h1
  subst h2
  exact ⟨hn', hR⟩

/-! ## The top scale of the window -/

/-- The centre of a natural origin cube is the spatial origin. -/
theorem cubeCenter_originCube_eq_zero (d : ℕ) (k : ℤ) :
    cubeCenter (originCube d k) = (0 : Vec d) := by
  funext i
  simp [cubeCenter, originCube]

/-- At the top scale the sub-cube family of `cu_m` is the singleton `{cu_m}`. -/
theorem largeCubeSubcubes_self (d m : ℕ) :
    largeCubeSubcubes d m m = {originCube d (m : ℤ)} := by
  rw [largeCubeSubcubes, Nat.sub_self]
  rfl

/-- At the top scale the coarse-average difference of the infrared cutoff
vanishes, so the envelope is exactly the weighted derivative tail gauge. -/
theorem centeredCubeAverageEnvelope_self (m : ℕ) (omega : ShellSeq d) :
    centeredCubeAverageEnvelope m m (0 : Vec d) omega
      = (d : ℝ) * Real.sqrt d * shellDerivTailGauge m omega := by
  rw [centeredCubeAverageEnvelope, translateSet_zero, sub_self,
    matrixOperatorNorm_zero, zero_add]

/-- **The `Γ₂` tail of the envelope at the top scale of the window.** The
hypothesis `n < m` of `isBigO_gammaSigma_centeredCubeAverageEnvelope` excludes
`n = m`, where the amplitude `(m-n)^{1/2}` degenerates; there the envelope is
the derivative tail gauge alone and its uniform amplitude is
`streamDerivTailConst`. -/
theorem isBigO_gammaSigma_centeredCubeAverageEnvelope_self (hJ3 : ShellLawJ3 d P)
    (m : ℕ) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
      (centeredCubeAverageEnvelope (d := d) m m (0 : Vec d))
      ((d : ℝ) * Real.sqrt d * streamDerivTailConst) := by
  have hbase := (isBigO_gammaSigma_shellDerivTailGauge hJ3 m).const_mul
    (c := (d : ℝ) * Real.sqrt d) (by positivity)
  have hfun : (fun omega : ShellSeq d =>
      (d : ℝ) * Real.sqrt d * shellDerivTailGauge m omega)
      = centeredCubeAverageEnvelope (d := d) m m (0 : Vec d) := by
    funext omega
    exact (centeredCubeAverageEnvelope_self m omega).symm
  rwa [hfun] at hbase

/-! ## The joint maximum -/

/-- **The joint maximum over the scales of the window and over the centres**:
one `Finset.sup'` over `centeredScaleWindow`, the carrier of the printed
display `e.bounding.the.diff.of.k.union` in the form clause (ii)
consumes. -/
def centeredScaleCubeMax (h m : ℕ) (omega : ShellSeq d) : ℝ :=
  (centeredScaleWindow d h m).sup' (centeredScaleWindow_nonempty d h m)
    fun p => centeredCubeAverageEnvelope p.1 m (cubeCenter p.2) omega

theorem centeredScaleCubeMax_nonneg (h m : ℕ) (omega : ShellSeq d) :
    0 ≤ centeredScaleCubeMax (d := d) h m omega := by
  obtain ⟨p, hp⟩ := centeredScaleWindow_nonempty d h m
  exact (centeredCubeAverageEnvelope_nonneg p.1 m (cubeCenter p.2) omega).trans
    (Finset.le_sup'
      (fun q : ℕ × TriadicCube d =>
        centeredCubeAverageEnvelope q.1 m (cubeCenter q.2) omega) hp)

/-- **The deterministic part of the joint union bound**: one random variable
dominates the coarse average of `k - (k)_{cu_m}` over *every* cube of *every*
scale of the window at once. -/
theorem matrixOperatorNorm_volumeAverageMat_centeredStreamField_le_scaleMax
    (omega : ShellSeq d) {h m n : ℕ} (hwin : m - h ≤ n) (hnm : n ≤ m)
    {Q : TriadicCube d} (hQscale : Q.scale = (n : ℤ))
    (hQmem : cubeCenter Q ∈ cubeSet (originCube d (m : ℤ)))
    (hsum : Summable fun k : ℕ ↦
      shellDerivLinftyNorm (openCubeSet (originCube d (m : ℤ))) (omega k)) :
    matrixOperatorNorm
        (volumeAverageMat (cubeSet Q)
          (centeredStreamField omega (cubeSet (originCube d (m : ℤ))))) ≤
      centeredScaleCubeMax h m omega :=
  (matrixOperatorNorm_volumeAverageMat_centeredStreamField_le_envelope omega hnm
      hQscale hQmem hsum).trans
    (Finset.le_sup'
      (fun q : ℕ × TriadicCube d =>
        centeredCubeAverageEnvelope q.1 m (cubeCenter q.2) omega)
      (mem_centeredScaleWindow (Finset.mem_Icc.2 ⟨hwin, hnm⟩)
        (mem_largeCubeSubcubes_of_cubeCenter_mem hnm hQscale hQmem)))

/-! ## The union bound over scales and centres -/

/-! ## The negative-norm term of `e.Xm.deff` -/

/-- The depth-`j` descendants of `cu_m` are its scale-`(m - j)` sub-cube
family. -/
theorem descendantsAtDepth_originCube_eq (d : ℕ) {j m : ℕ} (hjm : j ≤ m) :
    descendantsAtDepth (originCube d (m : ℤ)) j = largeCubeSubcubes d (m - j) m := by
  rw [largeCubeSubcubes]
  congr 1
  omega

/-- **The depth moments inside the window are dominated by the joint
maximum.** For a depth `j ≤ h` the depth-`j` sub-cubes of `cu_m` are the
scale-`(m-j)` cubes of the window, so every one of their coarse averages is
below the single random variable `centeredScaleCubeMax`. -/
theorem cubeDepthPthMoment_rpow_le_centeredScaleCubeMax (omega : ShellSeq d)
    {h m j : ℕ} (hjh : j ≤ h) (hhm : h ≤ m) {p : ℝ} (hp : 0 < p)
    (hsum : Summable fun k : ℕ ↦
      shellDerivLinftyNorm (openCubeSet (originCube d (m : ℤ))) (omega k)) :
    cubeDepthPthMoment (originCube d (m : ℤ)) j p
        (centeredStreamField omega (cubeSet (originCube d (m : ℤ)))) ^ p⁻¹ ≤
      centeredScaleCubeMax h m omega := by
  refine cubeDepthPthMoment_rpow_le_of_bound _ _ hp
    (centeredScaleCubeMax_nonneg h m omega) fun R hR => ?_
  have hjm : j ≤ m := le_trans hjh hhm
  have hRmem : R ∈ largeCubeSubcubes d (m - j) m := by
    rwa [descendantsAtDepth_originCube_eq d hjm] at hR
  have hscale : R.scale = ((m - j : ℕ) : ℤ) :=
    scale_of_mem_largeCubeSubcubes (by omega) hRmem
  have hcenter : cubeCenter R ∈ cubeSet (originCube d (m : ℤ)) :=
    cubeSet_subset_of_mem_descendantsAtDepth hR (cubeCenter_mem_cubeSet R)
  have hle := matrixOperatorNorm_volumeAverageMat_centeredStreamField_le_scaleMax
    omega (h := h) (by omega : m - h ≤ m - j) (by omega : m - j ≤ m) hscale
    hcenter hsum
  rwa [← matrixOperatorNorm_eq_l2_opNorm]

/-- **The depth moments below the window are dominated by the `L∞` datum.** A
uniform entrywise bound on the field over `cu_m` bounds every coarse average
over every sub-cube, at the cost of the dimension factor of
`matrixOperatorNorm_le_of_entry_bound`. This is the printed absorption of the
scales `n < m - h` by the `L∞` term of `e.Xm.deff`. -/
theorem cubeDepthPthMoment_rpow_le_of_entry_bound (M : Vec d → Mat d) (m j : ℕ)
    {p : ℝ} (hp : 0 < p) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ y ∈ cubeSet (originCube d (m : ℤ)), ∀ i k : Fin d, |M y i k| ≤ L) :
    cubeDepthPthMoment (originCube d (m : ℤ)) j p M ^ p⁻¹ ≤ (d : ℝ) * L := by
  refine cubeDepthPthMoment_rpow_le_of_bound _ _ hp (by positivity) fun R hR => ?_
  have hsub := cubeSet_subset_of_mem_descendantsAtDepth hR
  have hle := matrixOperatorNorm_volumeAverageMat_le
    (volume_cubeSet_lt_top R).ne hL0 fun y hy i k => hL y (hsub hy) i k
  rwa [← matrixOperatorNorm_eq_l2_opNorm]

end

end Stream
end Estimates
end Section2
end SuperdiffusionCLT
