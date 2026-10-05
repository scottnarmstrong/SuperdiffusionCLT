/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3InputsB
public import SuperdiffusionCLT.Section3.Terms.CoarseBlockLocalityB
public import SuperdiffusionCLT.Section3.Setup.RootLocalizationBridgesB
public import SuperdiffusionCLT.Section3.Setup.ScaleAssembly
public import Homogenization.Sobolev.Fractional.PairCapture

/-!
# The pigeonhole comparability and the sublattice partition of `l.RHS.term3`

The proof of `e.RHS.term3` (Step 3).  Two of its
bridges are supplied here.

## `hPigeon`

`averaged_quadratic_tail` consumes the pigeonhole comparability
`e.pigeon.scalar` in the *ratio* form
`shom_{L',*}^{-1}(cu_{m−2h}) ≤ C shom_{L',*}^{-1}(cu_n)`, while
the pigeonhole step of the paper gives the printed *relative* form
`|shom_{L',*}(cu_m) shom_{L',*}^{-1}(cu_{m−2h}) − 1| ≤ δ + 6η_L`.  The two are
bridged by `sigmaBarStarInvSeq_le_of_abs_pigeon`: the relative form gives the
ratio at the pigeonhole scale `m`, and the *antitonicity* of
`k ↦ shom_{L',*}^{-1}(cu_k)` carries it from `m` down to the cube scale `n`
(`n ≤ m`).  The comparability constant is `Cpig = 1 + δ + 6η_L`.

## The sublattice partition

The paper's partition: *"We partition the lattice `3^nℤ^d ∩ cu_k` into
`O(3^{d(ℓ−n)})` sublattices with spacing at least `C3^ℓ`, so that within each
sublattice the variables `{Y_z}` are independent."*  The partition is built
here as an explicit `Finset` family: the class of a scale-`n` cube `z` is the
pair

* its **slot** inside the scale-`ℓ` cube that contains it, an element of
  `Fin d → Fin (3^{ℓ−n})`, and
* the **colour** `cubeShellColor` of that scale-`ℓ` cube, an element of
  `ShellCubeColor d`.

Two cubes of one class have distinct same-colour scale-`ℓ` enclosing cubes
(distinct because the slot and the enclosing cube determine the cube), hence
observation regions separated at the `J1` range of scale `ℓ`; so
`iIndepFun_blockDeviation` applies.  The number of classes is exactly
`3^{d(ℓ−n)}(√d+2)^d`, which is the printed `O(3^{d(ℓ−n)})`.

## Main results

* `sigmaBarStarInvSeq_le_of_abs_pigeon`: `hPigeon`, from the relative form.
* `coarseAncestor`, `blockClassIndex`, `blockSublattice`: the partition.
* `blockDeviation_concentration`: `block_concentration` at `blockDeviation`,
  with `hUnion`, `hDisj`, `hIndep`, `hYmean`, `hYtail`,
  `hDcard` and `hJcard` all discharged.

## References

* The proof of `e.RHS.term3` (Step 3).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory ProbabilityTheory
open Homogenization
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section3.Setup

noncomputable section

variable {d : ℕ}

/-! ## `hPigeon`: the ratio form of `e.pigeon.scalar` at the cube scale -/

section Pigeon

variable [NeZero d] {nu : ℝ} {P : ProbabilityMeasure (ShellSeq d)}

/-- **From the relative form of `e.pigeon.scalar` to the ratio form at a
smaller cube scale.**  The printed comparability at the pigeonhole scale `m`,
`|shom_{L',*}(cu_m) shom_{L',*}^{-1}(cu_k) − 1| ≤ ε`, gives
`shom_{L',*}^{-1}(cu_k) ≤ (1+ε) shom_{L',*}^{-1}(cu_m)`, and the sequence
`n ↦ shom_{L',*}^{-1}(cu_n)` is nonincreasing, so the right-hand side only
grows when `m` is replaced by any `n ≤ m`.  This is the shape
`averaged_quadratic_tail` consumes. -/
theorem sigmaBarStarInvSeq_le_of_abs_pigeon (hnu : 0 < nu) (LPrime : ℕ)
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) {kk nn mm : ℕ} {eps : ℝ}
    (hnm : nn ≤ mm) (heps : 0 ≤ eps)
    (hpig : |sigmaBarStarScalar nu LPrime P (cubeSet (originCube d (mm : ℤ))) *
        sigmaBarStarInvScalar nu LPrime P (cubeSet (originCube d (kk : ℤ))) - 1| ≤ eps) :
    sigmaBarStarInvSeq nu LPrime P kk ≤
      (1 + eps) * sigmaBarStarInvSeq nu LPrime P nn := by
  have ham : 0 < sigmaBarStarInvScalar nu LPrime P (cubeSet (originCube d (mm : ℤ))) :=
    sigmaBarStarInvScalar_pos_cutoff hnu LPrime hPrefix hJ2 hJ3 hJ4 (mm : ℤ)
  rw [sigmaBarStarScalar_eq_inv hnu LPrime hJ4 (mm : ℤ) ham] at hpig
  set Am : ℝ := sigmaBarStarInvScalar nu LPrime P (cubeSet (originCube d (mm : ℤ)))
    with hAm
  set Ak : ℝ := sigmaBarStarInvScalar nu LPrime P (cubeSet (originCube d (kk : ℤ)))
    with hAk
  have hub : Am⁻¹ * Ak ≤ 1 + eps := by
    have := (abs_le.1 hpig).2
    linarith only [this]
  have hmul := mul_le_mul_of_nonneg_left hub ham.le
  have hid : Am * (Am⁻¹ * Ak) = Ak := by
    rw [← mul_assoc, mul_inv_cancel₀ ham.ne', one_mul]
  have hkm : Ak ≤ (1 + eps) * Am := by
    rw [hid] at hmul
    linarith only [hmul]
  have hmono : sigmaBarStarInvSeq nu LPrime P mm ≤ sigmaBarStarInvSeq nu LPrime P nn :=
    antitone_sigmaBarStarInvSeq hnu LPrime hPrefix hJ2 hJ3 hJ4 hnm
  have hmono' : Am ≤ sigmaBarStarInvSeq nu LPrime P nn := by
    rw [hAm]
    simpa only [sigmaBarStarInvSeq] using hmono
  have hfin : (1 + eps) * Am ≤ (1 + eps) * sigmaBarStarInvSeq nu LPrime P nn :=
    mul_le_mul_of_nonneg_left hmono' (by linarith only [heps])
  show Ak ≤ (1 + eps) * sigmaBarStarInvSeq nu LPrime P nn
  linarith only [hkm, hfin]

end Pigeon

/-! ## The sublattice partition of `3^nℤ^d ∩ cu_k` -/

section Partition

/-- The window identity of the triadic index arithmetic: writing
`x + H = M q + r` with `0 ≤ r < M` and `2H = M − 1`, the index `x` lies in the
window of radius `H` around `M q`.  This is the statement that
`q = (x+H)/M` is the index of the scale-`ℓ` cube containing the scale-`n` cube
of index `x`, in the parametrization of
`Gagliardo.mem_descendantsAtDepth_of_index_range`. -/
private theorem index_window_of_ediv {M H x : ℤ} (hM : 0 < M) (h2H : 2 * H = M - 1) :
    M * ((x + H) / M) - H ≤ x ∧ x ≤ M * ((x + H) / M) + H := by
  have hdm : M * ((x + H) / M) + (x + H) % M = x + H := Int.mul_ediv_add_emod (x + H) M
  have hr0 : 0 ≤ (x + H) % M := Int.emod_nonneg _ hM.ne'
  have hrlt : (x + H) % M < M := Int.emod_lt_of_pos _ hM
  generalize hQ : M * ((x + H) / M) = Q at hdm ⊢
  generalize hR : (x + H) % M = R at hdm hr0 hrlt
  omega

/-- The quotient and the remainder of `x + H` by `M` determine `x`: this is the
injectivity of `z ↦ (its scale-ℓ ancestor, its slot inside that ancestor)` at
the level of one coordinate. -/
private theorem index_eq_of_ediv_emod_eq {M H x y : ℤ}
    (hq : (x + H) / M = (y + H) / M) (hr : (x + H) % M = (y + H) % M) : x = y := by
  have hx : M * ((x + H) / M) + (x + H) % M = x + H := Int.mul_ediv_add_emod (x + H) M
  have hy : M * ((y + H) / M) + (y + H) % M = y + H := Int.mul_ediv_add_emod (y + H) M
  rw [hq, hr] at hx
  have h : x + H = y + H := hx.symm.trans hy
  linarith only [h]

/-- Two triadic cubes with the same scale and the same index are equal. -/
private theorem triadicCube_eq {T R : TriadicCube d} (hs : T.scale = R.scale)
    (hi : T.index = R.index) : T = R := by
  cases T
  cases R
  simp only [TriadicCube.mk.injEq]
  exact ⟨hs, hi⟩

/-- **The scale-`ℓ` triadic cube containing a scale-`n` cube.**  Depth-`j`
descendants of a cube `Q` are exactly the cubes whose index lies in the window
of radius `halfRange j = (3^j − 1)/2` around `3^j Q.index`
(`Gagliardo.index_range_of_mem_descendantsAtDepth`), so the ancestor's index is
the Euclidean quotient of the shifted index by `3^j`.  The scale is *fixed* to
`ℓ`, so the map is defined on all of `TriadicCube d`; it is the enclosing-cube
assignment only on the scale-`n` cubes. -/
def coarseAncestor (nn ell : ℕ) (z : TriadicCube d) : TriadicCube d where
  scale := (ell : ℤ)
  index := fun i =>
    (z.index i + Gagliardo.halfRange (ell - nn)) / (3 : ℤ) ^ (ell - nn)

@[simp] theorem coarseAncestor_scale (nn ell : ℕ) (z : TriadicCube d) :
    (coarseAncestor nn ell z).scale = (ell : ℤ) := rfl

/-- **A scale-`n` cube is a depth-`(ℓ−n)` descendant of its scale-`ℓ`
ancestor.** -/
theorem mem_descendantsAtDepth_coarseAncestor {nn ell : ℕ} (hnl : nn ≤ ell)
    {z : TriadicCube d} (hz : z.scale = (nn : ℤ)) :
    z ∈ descendantsAtDepth (coarseAncestor nn ell z) (ell - nn) := by
  have hM : (0 : ℤ) < 3 ^ (ell - nn) := by positivity
  have h2H : 2 * Gagliardo.halfRange (ell - nn) = (3 : ℤ) ^ (ell - nn) - 1 :=
    Gagliardo.two_mul_halfRange (ell - nn)
  refine Gagliardo.mem_descendantsAtDepth_of_index_range ?_ fun i => ?_
  · rw [hz, coarseAncestor_scale]
    have hcast : ((ell - nn : ℕ) : ℤ) = (ell : ℤ) - (nn : ℤ) := by
      rw [Nat.cast_sub hnl]
    omega
  · exact index_window_of_ediv (x := z.index i) hM h2H

/-- **The cube of a scale-`n` cube sits inside the cube of its scale-`ℓ`
ancestor.** -/
theorem cubeSet_subset_coarseAncestor {nn ell : ℕ} (hnl : nn ≤ ell)
    {z : TriadicCube d} (hz : z.scale = (nn : ℤ)) :
    cubeSet z ⊆ cubeSet (coarseAncestor nn ell z) :=
  cubeSet_subset_of_mem_descendantsAtDepth
    (mem_descendantsAtDepth_coarseAncestor hnl hz)

/-- **The slot of a scale-`n` cube inside its scale-`ℓ` ancestor**: the
coordinatewise remainder of the shifted index modulo `3^{ℓ−n}`.  Together with
the ancestor it determines the cube. -/
def blockSlot (nn ell : ℕ) (z : TriadicCube d) (i : Fin d) :
    Fin (3 ^ (ell - nn)) :=
  ⟨((z.index i + Gagliardo.halfRange (ell - nn)) %
      (3 : ℤ) ^ (ell - nn)).toNat, by
    have hM : (0 : ℤ) < 3 ^ (ell - nn) := by positivity
    have h0 := Int.emod_nonneg
      (z.index i + Gagliardo.halfRange (ell - nn)) hM.ne'
    have hlt := Int.emod_lt_of_pos
      (z.index i + Gagliardo.halfRange (ell - nn)) hM
    have hcast : ((3 : ℤ) ^ (ell - nn)) = ((3 ^ (ell - nn) : ℕ) : ℤ) := by
      push_cast
      ring
    omega⟩

/-- **The class of a scale-`n` cube in the printed sublattice partition**: its
slot inside its scale-`ℓ` ancestor together with the colour of that ancestor.
The slot makes the ancestor assignment injective on a class, and the colour
makes two distinct ancestors of a class separated at the `J1` range of scale
`ℓ`. -/
def blockClassIndex (nn ell : ℕ) (z : TriadicCube d) :
    (Fin d → Fin (3 ^ (ell - nn))) × ShellField.ShellCubeColor d :=
  (blockSlot nn ell z, ShellField.cubeShellColor (coarseAncestor nn ell z))

/-- **One sublattice of the printed partition.** -/
def blockSublattice (nn ell : ℕ) (D : Finset (TriadicCube d))
    (c : (Fin d → Fin (3 ^ (ell - nn))) × ShellField.ShellCubeColor d) :
    Finset (TriadicCube d) :=
  D.filter fun z => blockClassIndex nn ell z = c

theorem blockSublattice_subset (nn ell : ℕ) (D : Finset (TriadicCube d))
    (c : (Fin d → Fin (3 ^ (ell - nn))) × ShellField.ShellCubeColor d) :
    blockSublattice nn ell D c ⊆ D :=
  Finset.filter_subset _ _

theorem blockClassIndex_of_mem_blockSublattice {nn ell : ℕ}
    {D : Finset (TriadicCube d)}
    {c : (Fin d → Fin (3 ^ (ell - nn))) × ShellField.ShellCubeColor d}
    {z : TriadicCube d} (hz : z ∈ blockSublattice nn ell D c) :
    blockClassIndex nn ell z = c :=
  (Finset.mem_filter.1 hz).2

/-- **`hUnion` of `block_concentration`**: the sublattices exhaust the fine
lattice. -/
theorem biUnion_blockSublattice (nn ell : ℕ) (D : Finset (TriadicCube d)) :
    D = (Finset.univ :
        Finset ((Fin d → Fin (3 ^ (ell - nn))) × ShellField.ShellCubeColor d)).biUnion
      (blockSublattice nn ell D) := by
  ext z
  constructor
  · intro hz
    exact Finset.mem_biUnion.2 ⟨blockClassIndex nn ell z, Finset.mem_univ _,
      Finset.mem_filter.2 ⟨hz, rfl⟩⟩
  · intro hz
    obtain ⟨c, -, hzc⟩ := Finset.mem_biUnion.1 hz
    exact blockSublattice_subset nn ell D c hzc

/-- **`hDisj` of `block_concentration`**: distinct classes give disjoint
sublattices. -/
theorem disjoint_blockSublattice (nn ell : ℕ) (D : Finset (TriadicCube d))
    {c c' : (Fin d → Fin (3 ^ (ell - nn))) × ShellField.ShellCubeColor d}
    (hcc : c ≠ c') :
    Disjoint (blockSublattice nn ell D c) (blockSublattice nn ell D c') := by
  refine Finset.disjoint_left.2 fun z hz hz' => ?_
  exact hcc ((blockClassIndex_of_mem_blockSublattice hz).symm.trans
    (blockClassIndex_of_mem_blockSublattice hz'))

/-- **Injectivity of the ancestor assignment on one sublattice**: two cubes of
one class with the same scale and the same scale-`ℓ` ancestor are equal. -/
theorem eq_of_coarseAncestor_eq_of_blockClassIndex_eq {nn ell : ℕ}
    {z z' : TriadicCube d} (hz : z.scale = (nn : ℤ)) (hz' : z'.scale = (nn : ℤ))
    (hcls : blockClassIndex nn ell z = blockClassIndex nn ell z')
    (hanc : coarseAncestor nn ell z = coarseAncestor nn ell z') : z = z' := by
  have hslot : blockSlot nn ell z = blockSlot nn ell z' :=
    congrArg Prod.fst hcls
  refine triadicCube_eq (hz.trans hz'.symm) (funext fun i => ?_)
  have hq : (z.index i + Gagliardo.halfRange (ell - nn)) / (3 : ℤ) ^ (ell - nn) =
      (z'.index i + Gagliardo.halfRange (ell - nn)) / (3 : ℤ) ^ (ell - nn) :=
    congrFun (congrArg TriadicCube.index hanc) i
  have hM : (0 : ℤ) < 3 ^ (ell - nn) := by positivity
  have h0 := Int.emod_nonneg (z.index i + Gagliardo.halfRange (ell - nn)) hM.ne'
  have h0' := Int.emod_nonneg (z'.index i + Gagliardo.halfRange (ell - nn)) hM.ne'
  have hnat : ((z.index i + Gagliardo.halfRange (ell - nn)) %
        (3 : ℤ) ^ (ell - nn)).toNat =
      ((z'.index i + Gagliardo.halfRange (ell - nn)) %
        (3 : ℤ) ^ (ell - nn)).toNat :=
    congrArg Fin.val (congrFun hslot i)
  have hr : (z.index i + Gagliardo.halfRange (ell - nn)) % (3 : ℤ) ^ (ell - nn) =
      (z'.index i + Gagliardo.halfRange (ell - nn)) % (3 : ℤ) ^ (ell - nn) := by
    omega
  exact index_eq_of_ediv_emod_eq hq hr

/-- **`hJcard` of `block_concentration`**: the number of classes is exactly
`3^{d(ℓ−n)}(√d+2)^d`, the printed `O(3^{d(ℓ−n)})`. -/
theorem card_univ_blockClass (nn ell : ℕ) :
    ((Finset.univ :
        Finset ((Fin d → Fin (3 ^ (ell - nn))) ×
          ShellField.ShellCubeColor d)).card : ℕ) =
      (3 ^ (ell - nn)) ^ d * (ShellField.shellColorPeriod d) ^ d := by
  rw [Finset.card_univ]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]

end Partition

/-! ## `l.RHS.term3#block-concentration` at the centred coarse block -/

section Concentration

private theorem rpow_mul_natCast_eq (a : ℝ) (m j : ℕ) :
    a ^ ((m : ℝ) * ((j : ℕ) : ℝ)) = (a ^ m) ^ j := by
  rw [show ((m : ℝ) * ((j : ℕ) : ℝ)) = ((m * j : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast, pow_mul]

variable [NeZero d] {nu : ℝ} {P : ProbabilityMeasure (ShellSeq d)}

/-- **`l.RHS.term3#block-concentration` at the centred coarse block.**

The fine lattice is the family `descendantsAtDepth z' (k−n)` of scale-`n`
sub-cubes of a scale-`k` cube `z'`, i.e. the printed `3^nℤ^d ∩ cu_k`; the
observable is `blockDeviation`, i.e. the printed
`Y_z = e·(b_ℓ(z+cu_n) − shom_ℓ(cu_n))e`.  Every hypothesis of
`block_concentration` is discharged:

* `hUnion`, `hDisj` by `biUnion_blockSublattice`, `disjoint_blockSublattice`;
* `hIndep` by `iIndepFun_blockDeviation`, whose observation region for a
  scale-`n` cube is the cube of its scale-`ℓ` ancestor and whose separation is
  the colouring of `Assumptions/ShellField/SpatialAverageColoring`;
* `hYmean` by `integral_blockDeviation_eq_zero`;
* `hYtail` by `isBigO_gammaSigma_blockDeviation_of_shellLaws`, at the printed
  amplitude `bfE_ℓ + shom_ℓ(cu_n)`;
* `hDcard`, `hJcard` by `descendantsAtDepth_card` and `card_univ_blockClass`,
  the second with the explicit colour count `CJ = (√d+2)^d`. -/
theorem blockDeviation_concentration (hnu : 0 < nu)
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    {nn ell kk : ℕ} (hnl : nn ≤ ell) (hlk : ell ≤ kk)
    {e : Vec d} (he : vecNormSq e = 1)
    {z' : TriadicCube d} (hz' : z'.scale = (kk : ℤ)) :
    Real.sqrt (∫ omega : ShellSeq d,
        |(((descendantsAtDepth z' (kk - nn)).card : ℝ))⁻¹ *
            ∑ z ∈ descendantsAtDepth z' (kk - nn),
              blockDeviation nu ell P nn e omega z| ^ (2 : ℕ) ∂P.toMeasure) ≤
      blockConcentrationConst *
          Real.sqrt (((ShellField.shellColorPeriod d : ℕ) : ℝ) ^ d) *
          (envelopeUpperScalar d nu ell + sigmaBarSeq nu ell P nn) *
        (3 : ℝ) ^ (-((d : ℝ) * ((kk - ell : ℕ) : ℝ)) / 2) := by
  classical
  set D : Finset (TriadicCube d) := descendantsAtDepth z' (kk - nn) with hD
  have hscale : ∀ z ∈ D, z.scale = (nn : ℤ) := by
    intro z hz
    have h := scale_eq_sub_of_mem_descendantsAtDepth (hD ▸ hz)
    rw [hz'] at h
    rw [h, Nat.cast_sub (le_trans hnl hlk)]
    ring
  set nbhd : TriadicCube d → Set (Vec d) := fun z =>
    if z.scale = (nn : ℤ) then cubeSet (coarseAncestor nn ell z) else Set.univ
    with hnbhddef
  have hnbhd : ∀ z : TriadicCube d, MeasurableSet (nbhd z) := by
    intro z
    rw [hnbhddef]
    by_cases h : z.scale = (nn : ℤ)
    · simp only [h, ite_eq_left]
      exact measurableSet_cubeSet _
    · simp only [h, ite_false]
      exact MeasurableSet.univ
  have hsubn : ∀ z : TriadicCube d, cubeSet z ⊆ nbhd z := by
    intro z
    rw [hnbhddef]
    by_cases h : z.scale = (nn : ℤ)
    · simp only [h, ite_eq_left]
      exact cubeSet_subset_coarseAncestor hnl h
    · simp only [h, ite_false]
      exact Set.subset_univ _
  have hnbhd_eq : ∀ z : TriadicCube d, z.scale = (nn : ℤ) →
      nbhd z = cubeSet (coarseAncestor nn ell z) := by
    intro z h
    rw [hnbhddef]
    simp only [h, ite_eq_left]
  have hsep : ∀ c ∈ (Finset.univ :
        Finset ((Fin d → Fin (3 ^ (ell - nn))) × ShellField.ShellCubeColor d)),
      ∀ z ∈ blockSublattice nn ell D c, ∀ z2 ∈ blockSublattice nn ell D c, z ≠ z2 →
        ShellField.AreShellSeparated ell (nbhd z) (nbhd z2) := by
    intro c _ z hz z2 hz2 hne
    have hzs : z.scale = (nn : ℤ) :=
      hscale z (blockSublattice_subset nn ell D c hz)
    have hz2s : z2.scale = (nn : ℤ) :=
      hscale z2 (blockSublattice_subset nn ell D c hz2)
    have hcls : blockClassIndex nn ell z = blockClassIndex nn ell z2 :=
      (blockClassIndex_of_mem_blockSublattice hz).trans
        (blockClassIndex_of_mem_blockSublattice hz2).symm
    rw [hnbhd_eq z hzs, hnbhd_eq z2 hz2s]
    refine areShellSeparated_of_subset_cubeSet (kk := ell) le_rfl
      (coarseAncestor_scale nn ell z) (coarseAncestor_scale nn ell z2)
      (congrArg Prod.snd hcls) ?_ subset_rfl subset_rfl
    intro hcon
    exact hne (eq_of_coarseAncestor_eq_of_blockClassIndex_eq hzs hz2s hcls hcon)
  have hKpos : (0 : ℝ) < envelopeUpperScalar d nu ell + sigmaBarSeq nu ell P nn := by
    have h1 := envelopeUpperScalar_pos hnu d ell
    have h2 := sigmaBarSeq_pos hnu ell hPrefix hJ2 hJ3 hJ4 nn
    linarith only [h1, h2]
  have hCJ : (0 : ℝ) ≤ ((ShellField.shellColorPeriod d : ℕ) : ℝ) ^ d := by positivity
  have hDcard : ((D.card : ℝ)) = (3 : ℝ) ^ ((d : ℝ) * ((kk - nn : ℕ) : ℝ)) := by
    rw [hD, descendantsAtDepth_card, rpow_mul_natCast_eq]
    push_cast
    ring
  have hJcard : (((Finset.univ :
        Finset ((Fin d → Fin (3 ^ (ell - nn))) ×
          ShellField.ShellCubeColor d)).card : ℕ) : ℝ) ≤
      ((ShellField.shellColorPeriod d : ℕ) : ℝ) ^ d *
        (3 : ℝ) ^ ((d : ℝ) * ((ell - nn : ℕ) : ℝ)) := by
    rw [card_univ_blockClass, rpow_mul_natCast_eq]
    have hswap : ((3 : ℝ) ^ (ell - nn)) ^ d = ((3 : ℝ) ^ d) ^ (ell - nn) := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    push_cast
    rw [hswap]
    ring_nf
    exact le_rfl
  exact block_concentration P D Finset.univ (blockSublattice nn ell D)
    (fun omega z => blockDeviation nu ell P nn e omega z) hKpos hCJ
    (hD ▸ descendantsAtDepth_nonempty z' (kk - nn))
    (biUnion_blockSublattice nn ell D)
    (fun c _ c' _ hcc => disjoint_blockSublattice nn ell D hcc)
    (fun z => measurable_blockDeviation hnu ell nn e z)
    (fun z hz => integral_blockDeviation_eq_zero hnu hPrefix hJ2 hJ3 hJ4 ell nn he
      (hscale z hz))
    (fun z hz => isBigO_gammaSigma_blockDeviation_of_shellLaws hnu hPrefix hJ2 hJ3
      hJ4 ell nn he (hscale z hz))
    (iIndepFun_blockDeviation (ell := ell) (L := ell) hnu hJ1 hJ2 le_rfl nn e
      Finset.univ (blockSublattice nn ell D) hnbhd hsubn hsep)
    hnl hlk hDcard hJcard

end Concentration

end

end SuperdiffusionCLT.Section3.Terms
