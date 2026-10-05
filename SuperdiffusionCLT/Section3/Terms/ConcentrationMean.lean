/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.TranslatedBlockCentering
public import SuperdiffusionCLT.Section3.Terms.ConcentrationComparison

/-!
# Centring of the block averages of the depth-observable field

The concentration clause `_hConcDepth` (`ConcDepthClause` in
`SuperdiffusionCLT.Section3.Terms.RHSTerm1ConcDepth`) is reached, after the
reductions of that file, from the per-cube concentration `hconc` on the depth-`j`
descendants of `cu_m`.  The printed argument splits each of those cubes into the
aligned scale-`ℓ` blocks `3^{k}ℤ^d ∩ cu_m` and applies concentration to the block
averages.  Proposition `p.concentration` needs those block averages to be
centred, and the printed proof obtains the centring from the definition of `q̃`
by stationarity.

The comparison of part (b), in
`SuperdiffusionCLT.Section3.Terms.ConcentrationComparison`, carries that
centring as the residual hypothesis `hmean`: the mean over the sample of the
coordinate cube average of the field on each block of the family vanishes.

This file discharges `hmean` at the depth-observable field
`concDepthField hnu P S e = a_ℓ ∇ũ_n − q̃`.  The engine is the block
centring `integral_fluxBlockObservable_eq_zero_of_mem_le_scale`; the carrier
mismatch between the sample of `concDepthField` and the observable
`fluxBlockObservable` is removed by
`volumeAverage_coord_concDepthField_eq_fluxBlockObservable`.

Two block regimes occur, since the block family of a cube `R` at depth `j` is
`descendantsAtDepth R (m − j − ℓ)`, of cardinal `3^{d(m−j−ℓ)}`:

* `j + ℓ ≤ m`.  Here the blocks are the aligned scale-`ℓ` subcubes of `cu_m`, the
  centring applies to each of them, and the scale condition it needs
  (`S.n` at most the block scale) is automatic from `n ≤ ℓ ≤ m − j`.
* `j + ℓ > m`.  Here the exponent is `0`,
  the family collapses to the single cube `R`, whose scale is `m − j`, and the
  centring applies to it if and only if the block scale is still at least
  the gluing scale `S.n`.

So the discharge is unconditional in the first regime and carries the single
scale condition `S.n ≤ S.m − j` in the second; equivalently, it is unconditional
whenever `j + ℓ ≤ m`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open Homogenization
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section2.Estimates.Stream
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The carrier identity -/

/-- **The cube average of a coordinate of the depth observable is the block
observable** `fluxBlockObservable`.  The observable field is
`a_ℓ ∇ũ_n − q̃`, whose average over the cube differs from the average of the
pairing `a_ℓ ∇ũ_n` by the constant `q̃` (`volumeAverage_cubeSet_sub_const`). -/
theorem volumeAverage_coord_concDepthField_eq_fluxBlockObservable [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) (e : Vec d)
    (omega : ShellSeq d) (i : Fin d) (Q : TriadicCube d) :
    volumeAverage (cubeSet Q) (fun x => concDepthField hnu P S e omega x i) =
      fluxBlockObservable hnu P S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e) i Q omega := by
  have hG : MemVectorL2 (openCubeSet Q)
      (gluedGradientField hnu S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e) omega) :=
    memVectorL2_openCubeSet_gluedGradientField hnu S.ell S.n S.m _ omega Q
  have hA : MemVectorL2 (openCubeSet Q) (fun x => matVecMul
      ((coefficientCutoff nu omega S.ell).toCoeffField x)
      (gluedGradientField hnu S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e) omega x)) :=
    memVectorL2_matVecMul_coefficientCutoff hnu omega S.ell Q hG
  have hF : MemLp (hilbertifyVecField (fun x => matVecMul
      ((coefficientCutoff nu omega S.ell).toCoeffField x)
      (gluedGradientField hnu S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e) omega x))) 2
      (normalizedCubeMeasure Q) :=
    SuperdiffusionCLT.Section2.Norms.memLp_hilbertifyVecField_of_memVectorL2 hA
  have hint : IntegrableOn (fun x => matVecMul
      ((coefficientCutoff nu omega S.ell).toCoeffField x)
      (gluedGradientField hnu S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e) omega x) i)
      (cubeSet Q) volume :=
    integrableOn_coord_of_memLp Q hF i
  simp only [concDepthField, Pi.sub_apply]
  rw [volumeAverage_cubeSet_sub_const Q hint]
  rfl

/-! ## The centring, block by block and on the block family -/

/-- **Block centring at the depth observable.**  On an aligned scale-`q` subcube
`Q` of `cu_m` with `n ≤ q ≤ m`, the sample mean of the coordinate cube average
of `a_ℓ ∇ũ_n − q̃` vanishes.  This is
`integral_fluxBlockObservable_eq_zero_of_mem_le_scale` after the carrier
identity, at the pinned glued data `F = fluxSlot nu S.LPrime P S.n e`, gluing
scale `S.n` and pairing scale `S.ell`. -/
theorem integral_concDepthField_block_eq_zero [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) (e : Vec d)
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) {q : ℕ} (hnq : S.n ≤ q) (hqm : q ≤ S.m)
    (i : Fin d) {Q : TriadicCube d} (hQ : Q ∈ largeCubeSubcubes d q S.m) :
    ∫ omega : ShellSeq d, volumeAverage (cubeSet Q)
      (fun x => concDepthField hnu P S e omega x i) ∂P.toMeasure = 0 := by
  have hnℓ : S.n ≤ S.ell := by have := S.n_add_a; omega
  have hℓm : S.ell ≤ S.m := by have := S.ell_add_a; have := S.ellPrime_add_h; omega
  rw [funext fun omega =>
    volumeAverage_coord_concDepthField_eq_fluxBlockObservable hnu P S e omega i Q]
  exact integral_fluxBlockObservable_eq_zero_of_mem_le_scale hnu P hPrefix hJ2 hJ3 hJ4
    hnℓ hℓm hnq hqm (fluxSlot nu S.LPrime P S.n e) i hQ

/-- **The centring `hmean` of the concentration comparison, discharged at the
depth observable.**  For every depth `j` with `j ≤ m` and `n ≤ m − j`, and every
depth-`j` descendant `R` of `cu_m`, the sample mean of the coordinate cube
average of `a_ℓ ∇ũ_n − q̃` vanishes on every block of the family
`descendantsAtDepth R (m − j − ℓ)`.  This is exactly the binder `hmean` of the concentration
comparison at `F = concDepthField hnu P S e`, `μ = P.toMeasure`. -/
theorem integral_concDepthField_descendantsAtDepth_eq_zero [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) (e : Vec d)
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) {j : ℕ} {R : TriadicCube d}
    (hjm : j ≤ S.m) (hR : R ∈ descendantsAtDepth (originCube d (S.m : ℤ)) j)
    (hnj : S.n ≤ S.m - j) :
    ∀ i : Fin d, ∀ B ∈ descendantsAtDepth R (S.m - j - S.ell),
      ∫ omega : ShellSeq d, volumeAverage (cubeSet B)
        (fun x => concDepthField hnu P S e omega x i) ∂P.toMeasure = 0 := by
  intro i B hB
  by_cases hcase : j + S.ell ≤ S.m
  · have hBmem : B ∈ largeCubeSubcubes d S.ell S.m := by
      rw [largeCubeSubcubes_eq_descendantsAtDepth]
      have htrans := mem_descendantsAtDepth_trans hR hB
      rw [show j + (S.m - j - S.ell) = S.m - S.ell from by omega] at htrans
      exact htrans
    exact integral_concDepthField_block_eq_zero hnu P S e hPrefix hJ2 hJ3 hJ4
      (by have := S.n_add_a; omega)
      (by have := S.ell_add_a; have := S.ellPrime_add_h; omega) i hBmem
  · have hzero : S.m - j - S.ell = 0 := by omega
    have hBeq : B = R := by
      rw [hzero, descendantsAtDepth_zero, Finset.mem_singleton] at hB
      exact hB
    rw [hBeq]
    have hRmem : R ∈ largeCubeSubcubes d (S.m - j) S.m := by
      rw [largeCubeSubcubes_eq_descendantsAtDepth, Nat.sub_sub_self hjm]
      exact hR
    exact integral_concDepthField_block_eq_zero hnu P S e hPrefix hJ2 hJ3 hJ4
      hnj (Nat.sub_le _ _) i hRmem

/-! ## The comparison at the depth observable

The `L̲²` membership hypothesis of the comparison is discharged here at the depth
observable. -/

/-- The depth observable is `L̲²` on every triadic cube, so the `L̲²` membership
hypothesis of the comparison holds at the field. -/
theorem memLp_hilbertifyVecField_concDepthField_of_cube [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) (e : Vec d)
    (omega : ShellSeq d) (Q : TriadicCube d) :
    MemLp (hilbertifyVecField (concDepthField hnu P S e omega)) 2 (normalizedCubeMeasure Q) := by
  have hG : MemVectorL2 (openCubeSet Q)
      (gluedGradientField hnu S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e) omega) :=
    memVectorL2_openCubeSet_gluedGradientField hnu S.ell S.n S.m _ omega Q
  have hA : MemVectorL2 (openCubeSet Q) (fun x => matVecMul
      ((coefficientCutoff nu omega S.ell).toCoeffField x)
      (gluedGradientField hnu S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e) omega x)) :=
    memVectorL2_matVecMul_coefficientCutoff hnu omega S.ell Q hG
  have hsub : MemVectorL2 (openCubeSet Q) (fun x => matVecMul
      ((coefficientCutoff nu omega S.ell).toCoeffField x)
      (gluedGradientField hnu S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e) omega x)
        - qVector hnu P S.ell S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e)) :=
    memVectorL2_sub_const _ hA
  exact SuperdiffusionCLT.Section2.Norms.memLp_hilbertifyVecField_of_memVectorL2 hsub

end

end SuperdiffusionCLT.Section3.Terms
