/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Estimates.Stream.StreamCutoffCoarseAverage
public import SuperdiffusionCLT.Section2.Estimates.Stream.ShellDerivTailGauge
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementLinftyLargeCube
public import SuperdiffusionCLT.Section2.Cutoff.DerivativeSummabilityAllScales
public import SuperdiffusionCLT.Section2.Norms.CubeLp
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementCubeMomentLocality

/-!
# The limiting stream field in the coarse-average and supremum displays

`IncrementMoreoverBlock` and
`StreamCutoffCoarseAverage` prove the display
`e.bounding.something.that.is.more.complicated.than.it.seems` for the **infrared
cutoff** `k_m`. The printed display is stated for the **limiting field** `k`.
This module supplies the two deterministic steps that carry the cutoff
statements to the limit on the summability guard of
`DerivativeSummabilityAllScales`:

1. the exchange of a normalized average with the defining series of
   `Section2.Carriers.centeredStreamField`,
   `volumeAverage_centeredStreamField_eq_tsum`, which is
   `MeasureTheory.integral_tsum` applied entrywise to the shell terms; and
2. the estimate of the resulting tail `∑_{k > m}` by the derivative tail gauge
   `shellDerivTailGauge`, whose `Γ₂` amplitude is
   uniform in `m`.

Both the coarse averages (clause (ii) of the "Moreover" block) and the
`L∞(cu_m)` norm of `k - (k)_{cu_m}` (the first term of `e.Xm.deff`)
are reduced here to their cutoff counterparts plus `d √d` times that gauge.

## The two matrix norms

`Section2.Carriers.centeredStreamField` states its mean-value bounds in
the **elementwise** matrix norm; the "Moreover" block measures everything in the
Euclidean operator norm `Homogenization.Book.Ch02.matrixOperatorNorm`. The two
scoped instances coexist here, but every statement of this module is written
with the explicit function `matrixOperatorNorm`, never with `‖·‖`; the
elementwise norm appears only inside `section Elementwise`, and the conversion
is `matrixOperatorNorm_le_of_entry_bound`, at the cost of the factor `d`.

## Main definitions

* `shellDerivTailOn`: the tail `∑_{k > L} ‖∇ j_k‖_{L∞(U)}` on a set `U`.

## Main results

* `matrixOperatorNorm_le_of_entry_bound`, `abs_volumeAverage_le_of_entry_bound`,
  `matrixOperatorNorm_volumeAverageMat_le`: the two elementary bounds used
  throughout.
* `convex_cubeSet`, `dist_le_of_mem_cubeSet`: the half-open triadic cube is a
  bounded convex set with diameter its side length; `volume_cubeSet_ne_zero`
  is provided by `IncrementCubeMomentLocality`.
* `matrixOperatorNorm_centeredStreamField_sub_centeredStreamCutoff_le`: the
  pointwise distance between `k^U` and its level-`L` cutoff on `U`.
* `volumeAverage_centeredStreamField_eq_tsum`: the series exchange.
* `matrixOperatorNorm_volumeAverageMat_centeredStreamField_sub_le`: the
  coarse-average difference of `k^U` over `V ⊆ U` equals the one of `k_L` up
  to the tail.
* `shellDerivLinftyNorm_cubeSet_originCube`: the derivative norm does not see
  the cube boundary, so the guard and the gauge are the same on both cube
  realizations.
* `mem_largeCubeSubcubes_of_cubeCenter_mem`: a scale-`n` cube centred in `cu_m`
  is one of the `3^{d(m-n)}` sub-cubes.
* `matrixOperatorNorm_volumeAverageMat_centeredStreamField_cubeSet_le`: the
  limiting-field form of the coarse-average display.
* `cubeLpENorm_infty_centeredStreamField_le`: the limiting-field form of the
  `L∞` term of `e.Xm.deff`.
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
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Matrix and cube helpers -/

/-- A uniform bound on the entries bounds the Euclidean operator norm, at the
cost of the dimensional factor `d`. -/
theorem matrixOperatorNorm_le_of_entry_bound (A : Mat d) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ i j, |A i j| ≤ M) :
    matrixOperatorNorm A ≤ (d : ℝ) * M := by
  refine (matrixOperatorNorm_le_matrixFrobeniusNorm A).trans ?_
  have hsq : matrixFrobeniusNormSq A ≤ ((d : ℝ) * M) ^ 2 := by
    have hterm : ∀ i : Fin d, ∑ j : Fin d, A i j ^ 2 ≤ (d : ℝ) * M ^ 2 := by
      intro i
      calc ∑ j : Fin d, A i j ^ 2 ≤ ∑ _j : Fin d, M ^ 2 := by
            refine Finset.sum_le_sum fun j _ ↦ ?_
            nlinarith only [h i j, abs_nonneg (A i j), sq_abs (A i j)]
        _ = (d : ℝ) * M ^ 2 := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul]
    calc matrixFrobeniusNormSq A = ∑ i : Fin d, ∑ j : Fin d, A i j ^ 2 := rfl
      _ ≤ ∑ _i : Fin d, (d : ℝ) * M ^ 2 := Finset.sum_le_sum fun i _ ↦ hterm i
      _ = (d : ℝ) * ((d : ℝ) * M ^ 2) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
      _ = ((d : ℝ) * M) ^ 2 := by ring
  rw [matrixFrobeniusNorm]
  exact (Real.sqrt_le_sqrt hsq).trans
    (le_of_eq (Real.sqrt_sq (mul_nonneg (Nat.cast_nonneg d) hM)))

/-- The half-open realization of a triadic cube is convex. -/
theorem convex_cubeSet (Q : TriadicCube d) : Convex ℝ (cubeSet Q) := by
  rw [cubeSet_eq_pi_Ico]
  exact convex_pi fun i _ ↦ convex_Ico _ _

/-- The diameter of a triadic cube is its side length. -/
theorem dist_le_of_mem_cubeSet (Q : TriadicCube d) {a b : Vec d}
    (ha : a ∈ cubeSet Q) (hb : b ∈ cubeSet Q) :
    dist a b ≤ (3 : ℝ) ^ Q.scale := by
  have ha' := cubeSet_subset_closedBall Q ha
  have hb' := cubeSet_subset_closedBall Q hb
  rw [Metric.mem_closedBall] at ha' hb'
  calc dist a b ≤ dist a (cubeCenter Q) + dist (cubeCenter Q) b :=
        dist_triangle _ _ _
    _ ≤ cubeRadius Q + cubeRadius Q := by
        rw [dist_comm (cubeCenter Q) b]
        exact add_le_add ha' hb'
    _ = (3 : ℝ) ^ Q.scale := by
        simp only [cubeRadius, cubeScaleFactor]; ring

/-! ## The tail of the centered series -/

/-- The tail `∑_{k > L} ‖∇ j_k‖_{L∞(U)}` of the shell derivative norms on a
set `U`. -/
def shellDerivTailOn (U : Set (Vec d)) (omega : ShellSeq d) (L : ℕ) : ℝ :=
  ∑' k : ℕ, shellDerivLinftyNorm U (omega (L + 1 + k))

theorem shellDerivTailOn_nonneg (U : Set (Vec d)) (omega : ShellSeq d) (L : ℕ) :
    0 ≤ shellDerivTailOn U omega L :=
  tsum_nonneg fun _ ↦ shellDerivLinftyNorm_nonneg _ _

/-- The shifted series of shell derivative norms is summable whenever the full
one is. -/
theorem summable_shellDerivLinftyNorm_shift {U : Set (Vec d)}
    {omega : ShellSeq d}
    (hsum : Summable fun k : ℕ ↦ shellDerivLinftyNorm U (omega k)) (L : ℕ) :
    Summable fun k : ℕ ↦ shellDerivLinftyNorm U (omega (L + 1 + k)) := by
  have hshift : Summable fun k : ℕ ↦ shellDerivLinftyNorm U (omega (k + (L + 1))) :=
    (summable_nat_add_iff (f := fun k : ℕ ↦ shellDerivLinftyNorm U (omega k))
      (L + 1)).2 hsum
  refine hshift.congr fun k ↦ ?_
  congr 2
  omega

section Elementwise

open scoped Matrix.Norms.Elementwise

/-- **The limiting centered field is uniformly close to its infrared cutoff on
`U`.** On the summability event the difference is the tail of the defining
series, whose terms carry the mean-value bound; this is the passage from
`k_L - (k_L)_U` to `k - (k)_U` used in the printed proof of the passage to the limit. -/
theorem matrixOperatorNorm_centeredStreamField_sub_centeredStreamCutoff_le
    {U : Set (Vec d)} (hUb : Bornology.IsBounded U) (hUconv : Convex ℝ U)
    (hUpos : MeasureTheory.volume U ≠ 0) {R : ℝ}
    (hR : ∀ ⦃a : Vec d⦄, a ∈ U → ∀ ⦃b : Vec d⦄, b ∈ U → dist a b ≤ R)
    (omega : ShellSeq d)
    (hsum : Summable fun k : ℕ ↦ shellDerivLinftyNorm U (omega k)) (L : ℕ)
    {x : Vec d} (hx : x ∈ U) :
    matrixOperatorNorm
        (centeredStreamField omega U x - centeredStreamCutoff omega L U x) ≤
      (d : ℝ) * (Real.sqrt d * R * shellDerivTailOn U omega L) := by
  have hR0 : (0 : ℝ) ≤ R := le_trans dist_nonneg (hR hx hx)
  have hterm : Summable fun k : ℕ ↦ centeredShellTerm omega U k x :=
    summable_centeredShellTerm hUb hUconv hUpos omega hsum hx
  have hshift := summable_shellDerivLinftyNorm_shift hsum L
  have hmajor : Summable fun k : ℕ ↦
      Real.sqrt d * R * shellDerivLinftyNorm U (omega (L + 1 + k)) :=
    hshift.mul_left _
  have hnormle : ∀ k : ℕ, ‖centeredShellTerm omega U (L + 1 + k) x‖ ≤
      Real.sqrt d * R * shellDerivLinftyNorm U (omega (L + 1 + k)) :=
    fun k ↦ norm_centeredShellTerm_le hUb hUconv hUpos hR omega (L + 1 + k) hx
  have hnormsum : Summable fun k : ℕ ↦
      ‖centeredShellTerm omega U (L + 1 + k) x‖ :=
    Summable.of_nonneg_of_le (fun k ↦ norm_nonneg _) hnormle hmajor
  rw [centeredStreamField_sub_centeredStreamCutoff hUb omega hterm L]
  refine matrixOperatorNorm_le_of_entry_bound _ ?_ ?_
  · exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hR0)
      (shellDerivTailOn_nonneg U omega L)
  · intro i j
    have hentry : |(∑' k : ℕ, centeredShellTerm omega U (L + 1 + k) x) i j| ≤
        ‖∑' k : ℕ, centeredShellTerm omega U (L + 1 + k) x‖ := by
      simpa only [Real.norm_eq_abs] using
        Matrix.norm_entry_le_entrywise_sup_norm
          (∑' k : ℕ, centeredShellTerm omega U (L + 1 + k) x) (i := i) (j := j)
    refine hentry.trans ((norm_tsum_le_tsum_norm hnormsum).trans ?_)
    calc ∑' k : ℕ, ‖centeredShellTerm omega U (L + 1 + k) x‖
        ≤ ∑' k : ℕ,
            Real.sqrt d * R * shellDerivLinftyNorm U (omega (L + 1 + k)) :=
          hnormsum.tsum_le_tsum hnormle hmajor
      _ = Real.sqrt d * R * shellDerivTailOn U omega L := by
          rw [shellDerivTailOn, ← tsum_mul_left]

end Elementwise

/-! ## The averaging bound and the exchange with the defining series -/

/-- A uniform bound on a scalar field over a set of finite measure bounds its
normalized average, with no integrability hypothesis: the junk value of a
divergent integral is `0`. -/
theorem abs_volumeAverage_le_of_entry_bound {V : Set (Vec d)}
    (hVfin : MeasureTheory.volume V ≠ ⊤) {g : Vec d → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hg : ∀ y ∈ V, |g y| ≤ M) :
    |volumeAverage V g| ≤ M := by
  have hbound : |∫ y in V, g y ∂MeasureTheory.volume| ≤
      M * (MeasureTheory.volume V).toReal := by
    have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const
      (μ := MeasureTheory.volume) (s := V) (f := g) (C := M)
      (lt_of_le_of_ne le_top hVfin)
      (fun y hy ↦ by simpa only [Real.norm_eq_abs] using hg y hy)
    simpa only [Real.norm_eq_abs, MeasureTheory.Measure.real] using h
  rcases eq_or_lt_of_le (ENNReal.toReal_nonneg
      (a := MeasureTheory.volume V)) with h0 | hpos
  · simp only [volumeAverage, ← h0, inv_zero, zero_mul, abs_zero]
    exact hM
  · rw [volumeAverage, abs_mul, abs_of_nonneg (inv_nonneg.2 hpos.le)]
    calc (MeasureTheory.volume V).toReal⁻¹ *
          |∫ y in V, g y ∂MeasureTheory.volume|
        ≤ (MeasureTheory.volume V).toReal⁻¹ *
            (M * (MeasureTheory.volume V).toReal) :=
          mul_le_mul_of_nonneg_left hbound (inv_nonneg.2 hpos.le)
      _ = M := by field_simp

/-- The matrix form of `abs_volumeAverage_le_of_entry_bound`. -/
theorem matrixOperatorNorm_volumeAverageMat_le {V : Set (Vec d)}
    (hVfin : MeasureTheory.volume V ≠ ⊤) {f : Vec d → Mat d} {M : ℝ}
    (hM : 0 ≤ M) (hf : ∀ y ∈ V, ∀ i j : Fin d, |f y i j| ≤ M) :
    matrixOperatorNorm (volumeAverageMat V f) ≤ (d : ℝ) * M :=
  matrixOperatorNorm_le_of_entry_bound _ hM fun i j ↦
    abs_volumeAverage_le_of_entry_bound hVfin hM fun y hy ↦ hf y hy i j

section Elementwise

open scoped Matrix.Norms.Elementwise

/-- The entrywise form of the mean-value bound on one centered shell term. -/
theorem abs_entry_centeredShellTerm_le {U : Set (Vec d)}
    (hUb : Bornology.IsBounded U) (hUconv : Convex ℝ U)
    (hUpos : MeasureTheory.volume U ≠ 0) {R : ℝ}
    (hR : ∀ ⦃a : Vec d⦄, a ∈ U → ∀ ⦃b : Vec d⦄, b ∈ U → dist a b ≤ R)
    (omega : ShellSeq d) (k : ℕ) {y : Vec d} (hy : y ∈ U) (i j : Fin d) :
    |centeredShellTerm omega U k y i j| ≤
      Real.sqrt d * R * shellDerivLinftyNorm U (omega k) := by
  refine le_trans ?_ (norm_centeredShellTerm_le hUb hUconv hUpos hR omega k hy)
  simpa only [Real.norm_eq_abs] using
    Matrix.norm_entry_le_entrywise_sup_norm
      (centeredShellTerm omega U k y) (i := i) (j := j)

/-- **The normalized average of the limiting centered field is the series of
the normalized averages of its shell terms.** This is the exchange
`MeasureTheory.integral_tsum` of the printed proof: on the summability event
the series of shell terms is dominated on `U` by the summable sequence
`√d diam(U) ‖∇ j_k‖_{L∞(U)}`, so the average over a measurable subset `V ⊆ U`
of finite measure may be taken term by term. -/
theorem volumeAverage_centeredStreamField_eq_tsum {U V : Set (Vec d)}
    (hUb : Bornology.IsBounded U) (hUconv : Convex ℝ U)
    (hUpos : MeasureTheory.volume U ≠ 0) {R : ℝ}
    (hR : ∀ ⦃a : Vec d⦄, a ∈ U → ∀ ⦃b : Vec d⦄, b ∈ U → dist a b ≤ R)
    (hVmeas : MeasurableSet V) (hVU : V ⊆ U) (omega : ShellSeq d)
    (hsum : Summable fun k : ℕ ↦ shellDerivLinftyNorm U (omega k))
    (i j : Fin d) :
    volumeAverage V (fun y ↦ centeredStreamField omega U y i j) =
      ∑' k : ℕ, volumeAverage V (fun y ↦ centeredShellTerm omega U k y i j) := by
  classical
  set b : ℕ → ℝ := fun k ↦
    Real.sqrt d * R * shellDerivLinftyNorm U (omega k) with hb
  have hR0 : (0 : ℝ) ≤ R := by
    obtain ⟨y0, hy0⟩ : U.Nonempty := by
      rcases Set.eq_empty_or_nonempty U with h | h
      · exact absurd (by rw [h]; exact MeasureTheory.measure_empty) hUpos
      · exact h
    exact le_trans dist_nonneg (hR hy0 hy0)
  have hb0 : ∀ k, 0 ≤ b k := fun k ↦
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hR0)
      (shellDerivLinftyNorm_nonneg _ _)
  have hbsum : Summable b := hsum.mul_left _
  have hVfin : MeasureTheory.volume V ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (MeasureTheory.measure_mono hVU)
      (lt_of_le_of_ne le_top (volume_ne_top_of_isBounded hUb)))
  have hentry : ∀ (k : ℕ) (y : Vec d), y ∈ U →
      |centeredShellTerm omega U k y i j| ≤ b k := fun k y hy ↦
    abs_entry_centeredShellTerm_le hUb hUconv hUpos hR omega k hy i j
  have hmeask : ∀ k : ℕ, MeasureTheory.AEStronglyMeasurable
      (fun y : Vec d ↦ centeredShellTerm omega U k y i j)
      (MeasureTheory.volume.restrict V) := by
    intro k
    have hshell : MeasureTheory.AEStronglyMeasurable
        (fun y : Vec d ↦ shellReg omega k y i j)
        (MeasureTheory.volume.restrict V) :=
      ((integrableOn_entry_of_isBounded (shellReg omega k) hUb i j).mono_set
        hVU).aestronglyMeasurable
    have hsub := hshell.sub (MeasureTheory.aestronglyMeasurable_const
        (b := (volumeAverageMat U fun y ↦ shellReg omega k y) i j))
    simp only [centeredShellTerm, Matrix.sub_apply]
    exact hsub
  have hlint : ∀ k : ℕ,
      (∫⁻ y in V, ‖centeredShellTerm omega U k y i j‖ₑ ∂MeasureTheory.volume) ≤
        ENNReal.ofReal (b k) * MeasureTheory.volume V := by
    intro k
    calc (∫⁻ y in V, ‖centeredShellTerm omega U k y i j‖ₑ ∂MeasureTheory.volume)
        ≤ ∫⁻ _y in V, ENNReal.ofReal (b k) ∂MeasureTheory.volume := by
          refine MeasureTheory.setLIntegral_mono_ae
            measurable_const.aemeasurable ?_
          refine Filter.Eventually.of_forall ?_
          intro y hy
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal
            (by simpa only [Real.norm_eq_abs] using hentry k y (hVU hy))
      _ = ENNReal.ofReal (b k) * MeasureTheory.volume V := by
          rw [MeasureTheory.setLIntegral_const]
  have hfin : (∑' k : ℕ,
      ∫⁻ y in V, ‖centeredShellTerm omega U k y i j‖ₑ ∂MeasureTheory.volume)
      ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hlint)
    rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg hb0 hbsum]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVfin
  have hsplit :
      (∫ y in V, centeredStreamField omega U y i j ∂MeasureTheory.volume) =
        ∑' k : ℕ,
          ∫ y in V, centeredShellTerm omega U k y i j ∂MeasureTheory.volume := by
    rw [MeasureTheory.setIntegral_congr_fun hVmeas
      (g := fun y ↦ ∑' k : ℕ, centeredShellTerm omega U k y i j) ?_]
    · exact MeasureTheory.integral_tsum hmeask hfin
    · intro y hy
      exact tsum_matrix_apply
        (summable_centeredShellTerm hUb hUconv hUpos omega hsum (hVU hy)) i j
  simp only [volumeAverage, hsplit]
  rw [tsum_mul_left]

end Elementwise

/-! ## The coarse averages of the limiting field -/

/-- The normalized average of one centered shell term is the difference of the
two shell averages. -/
theorem volumeAverageMat_centeredShellTerm {U V : Set (Vec d)}
    (hVb : Bornology.IsBounded V) (hVpos : MeasureTheory.volume V ≠ 0)
    (omega : ShellSeq d) (k : ℕ) :
    volumeAverageMat V (centeredShellTerm omega U k) =
      volumeAverageMat V (fun y ↦ shellReg omega k y) -
        volumeAverageMat U (fun y ↦ shellReg omega k y) :=
  volumeAverageMat_sub_const (shellReg omega k) hVb hVpos _

/-- The finite sum of the shell coarse-average differences is the
coarse-average difference of the infrared cutoff. -/
theorem sum_volumeAverageMat_shellReg_sub {U V : Set (Vec d)}
    (hUb : Bornology.IsBounded U) (hVb : Bornology.IsBounded V)
    (omega : ShellSeq d) (L : ℕ) :
    ∑ k ∈ Finset.range (L + 1),
        (volumeAverageMat V (fun y ↦ shellReg omega k y) -
          volumeAverageMat U (fun y ↦ shellReg omega k y)) =
      volumeAverageMat V (Frozen.Section2.streamCutoff omega L) -
        volumeAverageMat U (Frozen.Section2.streamCutoff omega L) := by
  rw [Finset.sum_sub_distrib, volumeAverageMat_streamCutoff_eq_sum hVb omega L,
    volumeAverageMat_streamCutoff_eq_sum hUb omega L]

/-- **The coarse average of the limiting centered field is the coarse-average
difference of the infrared cutoff, up to the derivative tail.** This is the
passage from `(k_L)_V - (k_L)_U` to `(k)_V - (k)_U` of the printed proof:
the exchange with the defining series leaves the tail
`∑_{k > L}`, and each of its terms is dominated on `U` by the mean-value bound
`√d diam(U) ‖∇ j_k‖_{L∞(U)}`. -/
theorem matrixOperatorNorm_volumeAverageMat_centeredStreamField_sub_le
    {U V : Set (Vec d)} (hUb : Bornology.IsBounded U) (hUconv : Convex ℝ U)
    (hUpos : MeasureTheory.volume U ≠ 0) {R : ℝ}
    (hR : ∀ ⦃a : Vec d⦄, a ∈ U → ∀ ⦃b : Vec d⦄, b ∈ U → dist a b ≤ R)
    (hVb : Bornology.IsBounded V) (hVmeas : MeasurableSet V)
    (hVpos : MeasureTheory.volume V ≠ 0) (hVU : V ⊆ U) (omega : ShellSeq d)
    (hsum : Summable fun k : ℕ ↦ shellDerivLinftyNorm U (omega k)) (L : ℕ) :
    matrixOperatorNorm
        (volumeAverageMat V (centeredStreamField omega U) -
          (volumeAverageMat V (Frozen.Section2.streamCutoff omega L) -
            volumeAverageMat U (Frozen.Section2.streamCutoff omega L))) ≤
      (d : ℝ) * (Real.sqrt d * R * shellDerivTailOn U omega L) := by
  classical
  set b : ℕ → ℝ := fun k ↦
    Real.sqrt d * R * shellDerivLinftyNorm U (omega k) with hb
  have hR0 : (0 : ℝ) ≤ R := by
    obtain ⟨y0, hy0⟩ : U.Nonempty := by
      rcases Set.eq_empty_or_nonempty U with h | h
      · exact absurd (by rw [h]; exact MeasureTheory.measure_empty) hUpos
      · exact h
    exact le_trans dist_nonneg (hR hy0 hy0)
  have hb0 : ∀ k, 0 ≤ b k := fun k ↦
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hR0)
      (shellDerivLinftyNorm_nonneg _ _)
  have hbsum : Summable b := hsum.mul_left _
  have hVfin : MeasureTheory.volume V ≠ ⊤ := volume_ne_top_of_isBounded hVb
  have hshift := summable_shellDerivLinftyNorm_shift hsum L
  rw [← sum_volumeAverageMat_shellReg_sub hUb hVb omega L]
  refine matrixOperatorNorm_le_of_entry_bound _
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hR0)
      (shellDerivTailOn_nonneg U omega L)) ?_
  intro i j
  set c : ℕ → ℝ := fun k ↦
    volumeAverage V (fun y ↦ centeredShellTerm omega U k y i j) with hc
  have hceq : ∀ k : ℕ, c k =
      (volumeAverageMat V (fun y ↦ shellReg omega k y) -
        volumeAverageMat U (fun y ↦ shellReg omega k y)) i j := by
    intro k
    rw [hc, ← volumeAverageMat_centeredShellTerm (U := U) hVb hVpos omega k]
    rfl
  have hcb : ∀ k : ℕ, |c k| ≤ b k := by
    intro k
    exact abs_volumeAverage_le_of_entry_bound hVfin (hb0 k) fun y hy ↦
      abs_entry_centeredShellTerm_le hUb hUconv hUpos hR omega k (hVU hy) i j
  have hcsum : Summable c :=
    Summable.of_norm_bounded (g := b) hbsum fun k ↦ by
      simpa only [Real.norm_eq_abs] using hcb k
  have hexch : volumeAverage V (fun y ↦ centeredStreamField omega U y i j) =
      ∑' k : ℕ, c k :=
    volumeAverage_centeredStreamField_eq_tsum hUb hUconv hUpos hR hVmeas hVU
      omega hsum i j
  have hsplit := hcsum.sum_add_tsum_nat_add (L + 1)
  have hshiftfun : (fun k : ℕ ↦ c (k + (L + 1))) = fun k : ℕ ↦ c (L + 1 + k) := by
    funext k
    congr 1
    omega
  rw [hshiftfun] at hsplit
  have hentrytarget :
      (volumeAverageMat V (centeredStreamField omega U) -
          ∑ k ∈ Finset.range (L + 1),
            (volumeAverageMat V (fun y ↦ shellReg omega k y) -
              volumeAverageMat U (fun y ↦ shellReg omega k y))) i j =
        ∑' k : ℕ, c (L + 1 + k) := by
    have hsum_apply :
        (∑ k ∈ Finset.range (L + 1),
            (volumeAverageMat V (fun y ↦ shellReg omega k y) -
              volumeAverageMat U (fun y ↦ shellReg omega k y))) i j =
          ∑ k ∈ Finset.range (L + 1), c k := by
      rw [Matrix.sum_apply]
      exact Finset.sum_congr rfl fun k _ ↦ (hceq k).symm
    have hlhs : (volumeAverageMat V (centeredStreamField omega U)) i j =
        ∑' k : ℕ, c k := hexch
    rw [Matrix.sub_apply, hlhs, hsum_apply, ← hsplit]
    ring
  rw [hentrytarget]
  have htailb : Summable fun k : ℕ ↦ b (L + 1 + k) := hshift.mul_left _
  have habssum : Summable fun k : ℕ ↦ |c (L + 1 + k)| :=
    Summable.of_nonneg_of_le (fun k ↦ abs_nonneg _)
      (fun k ↦ hcb (L + 1 + k)) htailb
  have habs : |∑' k : ℕ, c (L + 1 + k)| ≤ ∑' k : ℕ, b (L + 1 + k) := by
    have hnorm : ‖∑' k : ℕ, c (L + 1 + k)‖ ≤ ∑' k : ℕ, ‖c (L + 1 + k)‖ :=
      norm_tsum_le_tsum_norm (by simpa only [Real.norm_eq_abs] using habssum)
    rw [Real.norm_eq_abs] at hnorm
    refine hnorm.trans ?_
    simp only [Real.norm_eq_abs]
    exact Summable.tsum_le_tsum (fun k ↦ hcb (L + 1 + k)) habssum htailb
  refine habs.trans (le_of_eq ?_)
  rw [hb, shellDerivTailOn, ← tsum_mul_left]

/-! ## The natural cubes -/

section OperatorNormAlgebra

open scoped Matrix.Norms.L2Operator

theorem matrixOperatorNorm_le_add_sub (A B : Mat d) :
    matrixOperatorNorm A ≤ matrixOperatorNorm (A - B) + matrixOperatorNorm B := by
  simp only [matrixOperatorNorm_eq_l2_opNorm]
  simpa only [sub_add_cancel] using norm_add_le (A - B) B

end OperatorNormAlgebra

/-- The two realizations of a triadic cube give the same normalized average:
they differ by a Lebesgue-null set. -/
theorem volumeAverageMat_cubeSet_eq_openCubeSet (Q : TriadicCube d)
    (f : Vec d → Mat d) :
    volumeAverageMat (cubeSet Q) f = volumeAverageMat (openCubeSet Q) f := by
  ext i j
  simp only [volumeAverageMat, volumeAverage,
    volume_openCubeSet_eq_volume_cubeSet]
  rw [MeasureTheory.setIntegral_congr_set (cubeSet_ae_eq_openCubeSet Q)]

/-- **The shell derivative norm does not see the cube boundary.** The stored
derivative is continuous, so its supremum over the half-open realization
agrees with the supremum over the open one. -/
theorem shellDerivLinftyNorm_cubeSet_originCube (m : ℕ) (j : ShellField d) :
    shellDerivLinftyNorm (cubeSet (originCube d (m : ℤ))) j =
      ShellField.shellCubeDerivNorm m j := by
  refine le_antisymm ?_ ?_
  · refine shellDerivLinftyNorm_le (ShellField.shellCubeDerivNorm_nonneg m j) ?_
    intro x hx
    have hclosed : IsClosed {y : Vec d |
        ShellField.matrixDerivativeNorm (ShellField.deriv j y) ≤
          ShellField.shellCubeDerivNorm m j} :=
      isClosed_le
        (ShellField.matrixDerivativeNorm_continuous.comp
          (ShellField.deriv j).continuous)
        continuous_const
    have hsub : openCubeSet (originCube d (m : ℤ)) ⊆ {y : Vec d |
        ShellField.matrixDerivativeNorm (ShellField.deriv j y) ≤
          ShellField.shellCubeDerivNorm m j} := fun _ hy ↦
      ShellField.matrixDerivativeNorm_deriv_le_shellCubeDerivNorm m j hy
    exact (hclosed.closure_subset_iff.2 hsub)
      (cubeSet_subset_closure_openCubeSet _ hx)
  · rw [← shellDerivLinftyNorm_openCubeSet]
    exact shellDerivLinftyNorm_mono (isBounded_cubeSet _)
      (openCubeSet_subset_cubeSet _) j

/-- The summability guard on the open cube is the guard on the half-open
cube. -/
theorem summable_shellDerivLinftyNorm_cubeSet_originCube {m : ℕ}
    {omega : ShellSeq d}
    (hsum : Summable fun k : ℕ ↦
      shellDerivLinftyNorm (openCubeSet (originCube d (m : ℤ))) (omega k)) :
    Summable fun k : ℕ ↦
      shellDerivLinftyNorm (cubeSet (originCube d (m : ℤ))) (omega k) := by
  simpa only [shellDerivLinftyNorm_cubeSet_originCube,
    shellDerivLinftyNorm_openCubeSet] using hsum

/-- The weighted derivative tail on the half-open cube is the gauge `shellDerivTailGauge`. -/
theorem mul_shellDerivTailOn_cubeSet_originCube (m : ℕ) (omega : ShellSeq d) :
    (3 : ℝ) ^ m * shellDerivTailOn (cubeSet (originCube d (m : ℤ))) omega m =
      shellDerivTailGauge m omega := by
  rw [shellDerivTailGauge_eq_tsum, shellDerivTailOn]
  simp only [shellDerivLinftyNorm_cubeSet_originCube,
    shellDerivLinftyNorm_openCubeSet]

/-- The side length bound on the half-open natural cube. -/
theorem dist_le_of_mem_cubeSet_originCube {m : ℕ} {a b : Vec d}
    (ha : a ∈ cubeSet (originCube d (m : ℤ)))
    (hb : b ∈ cubeSet (originCube d (m : ℤ))) :
    dist a b ≤ (3 : ℝ) ^ m := by
  have h := dist_le_of_mem_cubeSet (originCube d (m : ℤ)) ha hb
  have hs : (originCube d (m : ℤ)).scale = (m : ℤ) := rfl
  rw [hs, zpow_natCast] at h
  exact h

/-- **A triadic cube of scale `n ≤ m` whose centre lies in `cu_m` is one of the
`3^{d(m-n)}` scale-`n` sub-cubes of `cu_m`.** The scale-`n` cubes tile the
plane, so the one containing the centre is the cube itself. -/
theorem mem_largeCubeSubcubes_of_cubeCenter_mem {n m : ℕ} (hnm : n ≤ m)
    {Q : TriadicCube d} (hQscale : Q.scale = (n : ℤ))
    (hQmem : cubeCenter Q ∈ cubeSet (originCube d (m : ℤ))) :
    Q ∈ largeCubeSubcubes d n m := by
  obtain ⟨R, hR, hdiff⟩ := exists_mem_largeCubeSubcubes hnm hQmem
  have hRscale : R.scale = (n : ℤ) := scale_of_mem_largeCubeSubcubes hnm hR
  have hQR : Q = R := by
    have hindex : Q.index = R.index := by
      funext i
      rw [mem_cubeSet_originCube_iff] at hdiff
      have hi := hdiff i
      have hval : (cubeCenter Q - cubeCenter R) i =
          ((Q.index i : ℝ) - (R.index i : ℝ)) * (3 : ℝ) ^ (n : ℤ) := by
        simp only [Pi.sub_apply, cubeCenter, cubeScaleFactor, hQscale, hRscale]
        ring
      rw [hval] at hi
      have hpow : (0 : ℝ) < (3 : ℝ) ^ (n : ℤ) := by positivity
      have hlow : -(1 / 2 : ℝ) ≤ (Q.index i : ℝ) - (R.index i : ℝ) :=
        le_of_mul_le_mul_right (by linarith only [hi.1]) hpow
      have hhigh : (Q.index i : ℝ) - (R.index i : ℝ) < (1 / 2 : ℝ) :=
        lt_of_mul_lt_mul_right (by linarith only [hi.2]) hpow.le
      have hzero : Q.index i - R.index i = 0 := by
        have hcast : |((Q.index i - R.index i : ℤ) : ℝ)| < 1 := by
          rw [Int.cast_sub, abs_lt]
          exact ⟨by linarith only [hlow], by linarith only [hhigh]⟩
        exact Int.abs_lt_one_iff.1 (by exact_mod_cast hcast)
      omega
    have hs : Q.scale = R.scale := by rw [hQscale, hRscale]
    obtain ⟨qs, qi⟩ := Q
    obtain ⟨rs, ri⟩ := R
    exact congrArg₂ TriadicCube.mk hs hindex
  rw [hQR]
  exact hR

/-! ## The coarse-average display for the limiting field -/

private theorem triadicCubeShift_eq_cubeCenter (Q : TriadicCube d) :
    triadicCubeShift Q = cubeCenter Q := rfl

/-- **The limiting-field form of the coarse-average display
`e.bounding.something.that.is.more.complicated.than.it.seems`**, deterministic
part: on the summability guard the coarse average of `k - (k)_{cu_m}` over a
scale-`n` sub-cube of `cu_m` differs from the coarse-average difference of the
infrared cutoff `k_m` by at most `d √d` times the derivative tail gauge. -/
theorem matrixOperatorNorm_volumeAverageMat_centeredStreamField_cubeSet_le
    (omega : ShellSeq d) {n m : ℕ} (hnm : n ≤ m) {Q : TriadicCube d}
    (hQscale : Q.scale = (n : ℤ))
    (hQmem : cubeCenter Q ∈ cubeSet (originCube d (m : ℤ)))
    (hsum : Summable fun k : ℕ ↦
      shellDerivLinftyNorm (openCubeSet (originCube d (m : ℤ))) (omega k)) :
    matrixOperatorNorm
        (volumeAverageMat (cubeSet Q)
          (centeredStreamField omega (cubeSet (originCube d (m : ℤ))))) ≤
      matrixOperatorNorm
          (volumeAverageMat
              (translateSet (cubeCenter Q) (openCubeSet (originCube d (n : ℤ))))
              (Frozen.Section2.streamCutoff omega m) -
            volumeAverageMat (openCubeSet (originCube d (m : ℤ)))
              (Frozen.Section2.streamCutoff omega m)) +
        (d : ℝ) * Real.sqrt d * shellDerivTailGauge m omega := by
  have hQsub : cubeSet Q ⊆ cubeSet (originCube d (m : ℤ)) :=
    cubeSet_subset_of_mem_descendantsAtDepth
      (mem_largeCubeSubcubes_of_cubeCenter_mem hnm hQscale hQmem)
  have hopen : openCubeSet Q =
      translateSet (cubeCenter Q) (openCubeSet (originCube d (n : ℤ))) := by
    rw [openCubeSet_eq_translateSet_originCube_of_triadicCube Q, hQscale,
      triadicCubeShift_eq_cubeCenter]
  have hcut :
      volumeAverageMat (cubeSet Q) (Frozen.Section2.streamCutoff omega m) -
          volumeAverageMat (cubeSet (originCube d (m : ℤ)))
            (Frozen.Section2.streamCutoff omega m) =
        volumeAverageMat
            (translateSet (cubeCenter Q) (openCubeSet (originCube d (n : ℤ))))
            (Frozen.Section2.streamCutoff omega m) -
          volumeAverageMat (openCubeSet (originCube d (m : ℤ)))
            (Frozen.Section2.streamCutoff omega m) := by
    rw [volumeAverageMat_cubeSet_eq_openCubeSet Q,
      volumeAverageMat_cubeSet_eq_openCubeSet (originCube d (m : ℤ)), hopen]
  have hbase := matrixOperatorNorm_volumeAverageMat_centeredStreamField_sub_le
    (U := cubeSet (originCube d (m : ℤ))) (V := cubeSet Q)
    (isBounded_cubeSet _) (convex_cubeSet _) (volume_cubeSet_ne_zero _)
    (R := (3 : ℝ) ^ m)
    (fun _ ha _ hb ↦ dist_le_of_mem_cubeSet_originCube ha hb)
    (isBounded_cubeSet Q) (measurableSet_cubeSet Q) (volume_cubeSet_ne_zero Q)
    hQsub omega (summable_shellDerivLinftyNorm_cubeSet_originCube hsum) m
  have hcoeff : (d : ℝ) *
      (Real.sqrt d * (3 : ℝ) ^ m *
        shellDerivTailOn (cubeSet (originCube d (m : ℤ))) omega m) =
      (d : ℝ) * Real.sqrt d * shellDerivTailGauge m omega := by
    rw [← mul_shellDerivTailOn_cubeSet_originCube m omega]
    ring
  rw [hcoeff, hcut] at hbase
  refine le_trans (matrixOperatorNorm_le_add_sub _
    (volumeAverageMat
        (translateSet (cubeCenter Q) (openCubeSet (originCube d (n : ℤ))))
        (Frozen.Section2.streamCutoff omega m) -
      volumeAverageMat (openCubeSet (originCube d (m : ℤ)))
        (Frozen.Section2.streamCutoff omega m))) ?_
  linarith only [hbase]

/-! ## The `L∞` term of the printed smallness -/

section CubeLinfty

open scoped Matrix.Norms.L2Operator

/-- **The limiting centered field is uniformly close to its centered cutoff on
`cu_m`**, at the derivative tail gauge weighted by `d √d`. -/
theorem matrixOperatorNorm_centeredStreamField_sub_cutoff_cubeSet_le
    (omega : ShellSeq d) (m : ℕ)
    (hsum : Summable fun k : ℕ ↦
      shellDerivLinftyNorm (openCubeSet (originCube d (m : ℤ))) (omega k))
    {x : Vec d} (hx : x ∈ cubeSet (originCube d (m : ℤ))) :
    matrixOperatorNorm
        (centeredStreamField omega (cubeSet (originCube d (m : ℤ))) x -
          centeredStreamCutoff omega m (cubeSet (originCube d (m : ℤ))) x) ≤
      (d : ℝ) * Real.sqrt d * shellDerivTailGauge m omega := by
  have hbase := matrixOperatorNorm_centeredStreamField_sub_centeredStreamCutoff_le
    (U := cubeSet (originCube d (m : ℤ))) (isBounded_cubeSet _)
    (convex_cubeSet _) (volume_cubeSet_ne_zero _) (R := (3 : ℝ) ^ m)
    (fun _ ha _ hb ↦ dist_le_of_mem_cubeSet_originCube ha hb) omega
    (summable_shellDerivLinftyNorm_cubeSet_originCube hsum) m hx
  refine hbase.trans (le_of_eq ?_)
  rw [← mul_shellDerivTailOn_cubeSet_originCube m omega]
  ring

/-- Essential-supremum reading of the normalized `L∞` carrier: an a.e. norm bound on a
strongly measurable field bounds `cubeLpENorm … ∞`. -/
private theorem cubeLpENorm_infty_le_ofReal_of_ae_norm_le
    {E : Type*} [NormedAddCommGroup E] {Q : TriadicCube d} {f : Vec d → E} {B : ℝ}
    (hf : AEStronglyMeasurable f (normalizedCubeMeasure Q))
    (h : ∀ᵐ x ∂normalizedCubeMeasure Q, ‖f x‖ ≤ B) :
    Norms.cubeLpENorm Q ∞ f ≤ ENNReal.ofReal B := by
  unfold Norms.cubeLpENorm
  rw [eLpNorm_exponent_top hf]
  exact eLpNormEssSup_le_of_ae_bound h

/-- **The limiting-field form of the `L∞` term of `e.Xm.deff`**: the normalized `L∞(cu_m)`
norm of `k - (k)_{cu_m}` is bounded by any uniform bound on the centered
infrared cutoff `k_m - (k_m)_{cu_m}` over `cu_m`, plus `d √d` times the
derivative tail gauge. This is the printed passage "applied to finite cutoffs
and then passed to the limit". -/
theorem cubeLpENorm_infty_centeredStreamField_le
    (omega : ShellSeq d) (m : ℕ)
    (hsum : Summable fun k : ℕ ↦
      shellDerivLinftyNorm (openCubeSet (originCube d (m : ℤ))) (omega k))
    {C : ℝ}
    (hbound : ∀ x ∈ cubeSet (originCube d (m : ℤ)),
      matrixOperatorNorm
        (centeredStreamCutoff omega m (cubeSet (originCube d (m : ℤ))) x) ≤ C) :
    Norms.cubeLpENorm (originCube d (m : ℤ)) ∞
        (centeredStreamField omega (cubeSet (originCube d (m : ℤ)))) ≤
      ENNReal.ofReal
        (C + (d : ℝ) * Real.sqrt d * shellDerivTailGauge m omega) := by
  have hmeasf : AEStronglyMeasurable
      (centeredStreamField omega (cubeSet (originCube d (m : ℤ))))
      (normalizedCubeMeasure (originCube d (m : ℤ))) := by
    have hUb := isBounded_cubeSet (originCube d (m : ℤ))
    have hUconv := convex_cubeSet (originCube d (m : ℤ))
    have hUpos := volume_cubeSet_ne_zero (originCube d (m : ℤ))
    have hsumU := summable_shellDerivLinftyNorm_cubeSet_originCube hsum
    have hmemU : ∀ᵐ x ∂normalizedCubeMeasure (originCube d (m : ℤ)),
        x ∈ cubeSet (originCube d (m : ℤ)) :=
      MeasureTheory.Measure.ae_smul_measure
        (MeasureTheory.ae_restrict_mem (measurableSet_cubeSet _)) _
    have hcont : ∀ N : ℕ, Continuous (fun x : Vec d ↦
        ∑ k ∈ Finset.range N,
          centeredShellTerm omega (cubeSet (originCube d (m : ℤ))) k x) := by
      intro N
      refine continuous_finsetSum _ fun k _ ↦ ?_
      exact ((omega k).1.1.continuous).sub continuous_const
    refine aestronglyMeasurable_of_tendsto_ae (u := Filter.atTop)
      (f := fun N : ℕ ↦ fun x : Vec d ↦
        ∑ k ∈ Finset.range N,
          centeredShellTerm omega (cubeSet (originCube d (m : ℤ))) k x)
      (fun N ↦ (hcont N).aestronglyMeasurable) ?_
    filter_upwards [hmemU] with x hx
    have hterm := summable_centeredShellTerm hUb hUconv hUpos omega hsumU hx
    rw [centeredStreamField_eq_tsum]
    exact hterm.hasSum.tendsto_sum_nat
  have hmem : ∀ᵐ x ∂normalizedCubeMeasure (originCube d (m : ℤ)),
      x ∈ cubeSet (originCube d (m : ℤ)) :=
    MeasureTheory.Measure.ae_smul_measure
      (MeasureTheory.ae_restrict_mem (measurableSet_cubeSet _)) _
  refine cubeLpENorm_infty_le_ofReal_of_ae_norm_le hmeasf (hmem.mono fun x hx ↦ ?_)
  have hpoint : matrixOperatorNorm
      (centeredStreamField omega (cubeSet (originCube d (m : ℤ))) x) ≤
        C + (d : ℝ) * Real.sqrt d * shellDerivTailGauge m omega := by
    have hsplit := matrixOperatorNorm_le_add_sub
      (centeredStreamField omega (cubeSet (originCube d (m : ℤ))) x)
      (centeredStreamCutoff omega m (cubeSet (originCube d (m : ℤ))) x)
    have htail :=
      matrixOperatorNorm_centeredStreamField_sub_cutoff_cubeSet_le omega m
        hsum hx
    linarith only [hsplit, htail, hbound x hx]
  rw [← matrixOperatorNorm_eq_l2_opNorm]
  exact hpoint

end CubeLinfty

end

end Stream
end Estimates
end Section2
end SuperdiffusionCLT
