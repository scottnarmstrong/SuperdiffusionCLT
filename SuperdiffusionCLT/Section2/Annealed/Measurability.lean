/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.CoarseGraining.CutoffCorrespondence
public import SuperdiffusionCLT.Section2.Cutoff.Size
public import Homogenization.Book.Ch04.Theorems.Scalarization
public import Homogenization.HighContrast.Corridor.PhaseComparison.Measurability

/-!
# Measurability of the coarse-grained matrices of the cutoff field

The annealed matrices of display `e.homs.defs.U.0` are expectations of the coarse-grained
matrices of the infrared cutoff `a_m = nu Id + k_m`. Before those expectations
can be written down, the coarse-grained matrices have to be measurable
functions of the shell sequence. This module supplies that measurability.

## The carrier and the admissibility question

`CoarseGraining` defines the coarse matrices twice: on a bare `Set (Vec d)`
with a bare `CoeffField d`, and on the Chapter 2 pair `Domain d`, `CoeffOn U`
where the unconditional theorems live (see the companion module
`SuperdiffusionCLT.Section2.CoarseGraining.Correspondence`). Passing from
the first to the second needs quantitative ellipticity, which for the marginal
cutoff comes from an entry bound on the domain and is therefore *random*.

The entry bound is nevertheless available for **every** sample: each shell of
the `ShellField` carrier stores a continuous value map, so `a_m(omega)`
is continuous, hence bounded on every bounded set, and its symmetric part is
the constant `nu Id`. Consequently `a_m(omega)` is a locally a.e. uniformly
elliptic field for every `omega` (`aeLocallyUniformlyEllipticField_coefficientCutoff`),
with a sample-dependent upper constant and the deterministic lower constant
`nu`. There is therefore **no admissible event**: the coarse matrices of the
cutoff field are the genuine Chapter 2 objects at every sample, and every
statement below is unconditional in `omega`.

The measurability itself is genuine, not merely law-relative: the countable
`AEE` quantitative ellipticity slices of `CoarseGraining` cover the whole
shell-sequence carrier, each slice is measurable, and on each slice the
coarse-grained energy `Mu` is measurable by the `CoarseGraining` slice engine
`measurable_Mu_comp_aeeSlice_of_measurable_entryTest`.

## Main results

* `exists_entryBound_coefficientCutoff`: the cutoff field is bounded on every
  triadic cube, with a sample-dependent constant.
* `aeLocallyUniformlyEllipticField_coefficientCutoff`: the cutoff field is
  locally a.e. uniformly elliptic at every sample.
* `measurable_Mu_cubeSet_of_source`: the coarse-grained energy of a measurable
  locally elliptic source is measurable.
* `measurable_coarseBlockMatrix_upperLeft_apply` and its three companions: the
  four blocks of `bfA_m(cu)` are measurable in the shell sequence.
* `coarseBlockMatrix_cubeSet_lowerRight_eq`, `..._lowerLeft_eq`,
  `..._upperLeft_eq`: the blocks of the half-open-cube block matrix are the
  raw coarse matrices on the open cube.
* `measurable_sigmaStarInvCoarse_apply`, `measurable_sigmaStarCoarse_apply`,
  `measurable_kappaCoarse_apply`: measurability of the coarse matrices themselves.
* `cutoffLaw`, `restrictionLawCarrier_cutoffLaw`: the law of the cutoff field
  on `CoarseGraining`'s coefficient carrier, and its Chapter 4 law carrier.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Annealed

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.CoarseGraining

noncomputable section

variable {d : ℕ}

/-! ## The cutoff field is admissible at every sample -/

/-- The cutoff coefficient field is bounded on every triadic cube, with a
constant depending on the sample. The proof is compactness: every shell of the
carrier stores a continuous value map. -/
theorem exists_entryBound_coefficientCutoff (nu : ℝ) (omega : ShellSeq d) (m : ℕ)
    (Q : TriadicCube d) :
    ∃ C : ℝ, ∀ x ∈ cubeSet Q, ∀ i j : Fin d,
      |(coefficientCutoff nu omega m).toCoeffField x i j| ≤ C := by
  classical
  set a : Vec d → Mat d := (coefficientCutoff nu omega m).toCoeffField with ha
  set g : Vec d → ℝ := fun x ↦ ∑ i : Fin d, ∑ j : Fin d, |a x i j| with hg
  have hcoef : Continuous a :=
    Continuous.add (M := Mat d) continuous_const (continuous_streamCutoff_apply omega m)
  have hcont : Continuous g := by
    refine continuous_finsetSum _ fun i _ ↦ continuous_finsetSum _ fun j _ ↦ ?_
    refine continuous_abs.comp ?_
    exact (continuous_apply j).comp ((continuous_apply i).comp hcoef)
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (cubeCenter Q) (cubeRadius Q)).exists_bound_of_continuousOn
      hcont.continuousOn
  refine ⟨C, fun x hx i j ↦ ?_⟩
  have hle : ‖g x‖ ≤ C := hC x (cubeSet_subset_closedBall Q hx)
  rw [Real.norm_eq_abs] at hle
  have hsingle : |a x i j| ≤ g x := by
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun i' : Fin d ↦ ∑ j' : Fin d, |a x i' j'|)
      (fun i' _ ↦ Finset.sum_nonneg fun j' _ ↦ abs_nonneg _) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j' : Fin d ↦ |a x i j'|)
      (fun j' _ ↦ abs_nonneg _) (Finset.mem_univ j)
  exact hsingle.trans ((le_abs_self (g x)).trans hle)

/-- **The cutoff field is admissible at every sample.** For every shell
sequence the infrared cutoff `a_m = nu Id + k_m` is a locally a.e. uniformly
elliptic coefficient field: its symmetric part is the constant `nu Id`, and its
entries are bounded on every triadic cube by continuity. The lower ellipticity
constant is the deterministic `nu`; only the upper one depends on the sample. -/
theorem aeLocallyUniformlyEllipticField_coefficientCutoff {nu : ℝ} (hnu : 0 < nu)
    (omega : ShellSeq d) (m : ℕ) :
    Book.Ch04.AELocallyUniformlyEllipticField (coefficientCutoff nu omega m) := by
  classical
  intro Q
  obtain ⟨C, hC⟩ := exists_entryBound_coefficientCutoff nu omega m Q
  refine ⟨nu, ((d : ℝ) * (d : ℝ) * C ^ 2 + nu ^ 2) / nu, hnu, ?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hnu, ← pow_two]
    linarith only [show (0 : ℝ) ≤ (d : ℝ) * (d : ℝ) * C ^ 2 by positivity]
  · exact measurableSet_openCubeSet Q
  · intro i j
    have hEq : (fun x : Vec d ↦
        restrictCoeffField (openCubeSet Q)
          (coefficientCutoff nu omega m).toFun x i j) =
        fun x : Vec d ↦ if x ∈ openCubeSet Q
          then (coefficientCutoff nu omega m).toFun x i j else 0 := by
      funext x
      by_cases hx : x ∈ openCubeSet Q <;> simp [restrictCoeffField, hx]
    rw [hEq]
    exact (((coefficientCutoff nu omega m).entry_measurable i j).ite
      (measurableSet_openCubeSet Q) measurable_const).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
    exact isEllipticMatrix_of_symmPart_eq_smul_one hnu
      (symmPart_coefficientCutoff nu omega m x)
      (hC x (openCubeSet_subset_cubeSet Q hx))

/-! ## Measurability of the coarse-grained energy -/

/-- **The coarse-grained energy of a measurable admissible source is
measurable.** The countable `AEE` quantitative ellipticity slices cover the
whole parameter space, each is measurable because the slice event is
`LocalSigmaR`-measurable, and on each slice `CoarseGraining`'s slice engine
makes `Mu` measurable from the localized entry tests. -/
theorem measurable_Mu_cubeSet_of_source {Omega : Type*} [MeasurableSpace Omega]
    {A : Omega → RegCoeffField d} (hA : Measurable A)
    (hEll : ∀ omega, Book.Ch04.AELocallyUniformlyEllipticField (A omega))
    (Q : TriadicCube d) (P0 : BlockVec d) :
    Measurable (fun omega ↦ Mu (cubeSet Q) P0 (A omega).toFun) := by
  classical
  set S : ℕ → Set Omega :=
    fun k ↦ A ⁻¹' {a : RegCoeffField d | AEEQuantitativeEllipticSlice (cubeSet Q) k a.toFun}
    with hS
  have hSmeas : ∀ k, MeasurableSet (S k) := fun k ↦
    hA (LocalSigmaR_le (cubeSet Q) _
      (Book.Ch04.measurableSet_localSigmaR_aeeQuantitativeEllipticSlice Q k))
  have hSunion : (⋃ k, S k) = Set.univ := by
    ext omega
    refine ⟨fun _ ↦ Set.mem_univ _, fun _ ↦ ?_⟩
    obtain ⟨k, hk⟩ := (hEll omega).exists_aeeQuantitativeEllipticSlice_cubeSet Q
    exact Set.mem_iUnion.mpr ⟨k, hk⟩
  set F : (k : ℕ) → S k → ℝ :=
    fun _k x ↦ Mu (cubeSet Q) P0 (A (x : Omega)).toFun with hF
  have hFagree : ∀ (i j : ℕ) (x : Omega) (hxi : x ∈ S i) (hxj : x ∈ S j),
      F i ⟨x, hxi⟩ = F j ⟨x, hxj⟩ := fun _ _ _ _ _ ↦ rfl
  have hFmeas : ∀ k, Measurable (F k) := by
    intro k
    refine measurable_Mu_comp_aeeSlice_of_measurable_entryTest (k := k) Q
      (A := fun x : S k ↦ A (x : Omega)) (fun x ↦ x.2) ?_ P0
    intro i j phi hphi hcs _hsupp
    exact (measurable_entryTestR i j (IsProbeR.of_smooth hphi hcs)).comp
      (hA.comp measurable_subtype_coe)
  have hEq : (fun omega ↦ Mu (cubeSet Q) P0 (A omega).toFun) =
      Set.liftCover S F hFagree hSunion := by
    funext omega
    have hmem : omega ∈ ⋃ k, S k := by rw [hSunion]; exact Set.mem_univ _
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hmem
    rw [Set.liftCover_coe (S := S) (f := F) (x := (⟨omega, hk⟩ : S k))]
  rw [hEq]
  exact measurable_liftCover S hSmeas F hFmeas hFagree hSunion

/-! ## Measurability of the four blocks

The blocks of `bfA(U; a)` are the polarization combinations of `Mu` recorded in
`Homogenization.coarseBlockMatrix_upperLeft_apply` and its companions, so the
previous theorem makes each of them measurable. -/

section Blocks

variable {Omega : Type*} [MeasurableSpace Omega] {A : Omega → RegCoeffField d}

/-- The upper-left block `b(U; a)` is measurable in the source. -/
theorem measurable_coarseBlockMatrix_upperLeft_apply (hA : Measurable A)
    (hEll : ∀ omega, Book.Ch04.AELocallyUniformlyEllipticField (A omega))
    (Q : TriadicCube d) (i j : Fin d) :
    Measurable (fun omega ↦
      (coarseBlockMatrix (cubeSet Q) (A omega).toFun).upperLeft i j) := by
  classical
  have hMu : ∀ P0 : BlockVec d,
      Measurable (fun omega ↦ Mu (cubeSet Q) P0 (A omega).toFun) := fun P0 ↦
    measurable_Mu_cubeSet_of_source hA hEll Q P0
  by_cases hij : i = j
  · subst hij
    have hEq : (fun omega ↦ (coarseBlockMatrix (cubeSet Q) (A omega).toFun).upperLeft i i) =
        fun omega ↦ (2 : ℝ) * Mu (cubeSet Q) (Pi.single i 1, 0) (A omega).toFun := by
      funext omega
      simp [coarseBlockMatrix_upperLeft_apply]
    rw [hEq]
    exact (hMu _).const_mul (2 : ℝ)
  · have hEq : (fun omega ↦ (coarseBlockMatrix (cubeSet Q) (A omega).toFun).upperLeft i j) =
        fun omega ↦
          Mu (cubeSet Q) ((Pi.single i 1, 0) + (Pi.single j 1, 0)) (A omega).toFun
            - Mu (cubeSet Q) (Pi.single i 1, 0) (A omega).toFun
            - Mu (cubeSet Q) (Pi.single j 1, 0) (A omega).toFun := by
      funext omega
      simp [coarseBlockMatrix_upperLeft_apply, hij]
    rw [hEq]
    exact ((hMu _).sub (hMu _)).sub (hMu _)

/-- The lower-right block `s_*^{-1}(U; a)` is measurable in the source. -/
theorem measurable_coarseBlockMatrix_lowerRight_apply (hA : Measurable A)
    (hEll : ∀ omega, Book.Ch04.AELocallyUniformlyEllipticField (A omega))
    (Q : TriadicCube d) (i j : Fin d) :
    Measurable (fun omega ↦
      (coarseBlockMatrix (cubeSet Q) (A omega).toFun).lowerRight i j) := by
  classical
  have hMu : ∀ P0 : BlockVec d,
      Measurable (fun omega ↦ Mu (cubeSet Q) P0 (A omega).toFun) := fun P0 ↦
    measurable_Mu_cubeSet_of_source hA hEll Q P0
  by_cases hij : i = j
  · subst hij
    have hEq : (fun omega ↦ (coarseBlockMatrix (cubeSet Q) (A omega).toFun).lowerRight i i) =
        fun omega ↦ (2 : ℝ) * Mu (cubeSet Q) (0, Pi.single i 1) (A omega).toFun := by
      funext omega
      simp [coarseBlockMatrix_lowerRight_apply]
    rw [hEq]
    exact (hMu _).const_mul (2 : ℝ)
  · have hEq : (fun omega ↦ (coarseBlockMatrix (cubeSet Q) (A omega).toFun).lowerRight i j) =
        fun omega ↦
          Mu (cubeSet Q) ((0, Pi.single i 1) + (0, Pi.single j 1)) (A omega).toFun
            - Mu (cubeSet Q) (0, Pi.single i 1) (A omega).toFun
            - Mu (cubeSet Q) (0, Pi.single j 1) (A omega).toFun := by
      funext omega
      simp [coarseBlockMatrix_lowerRight_apply, hij]
    rw [hEq]
    exact ((hMu _).sub (hMu _)).sub (hMu _)

/-- The upper-right block `-(k^t s_*^{-1})(U; a)` is measurable in the
source. -/
theorem measurable_coarseBlockMatrix_upperRight_apply (hA : Measurable A)
    (hEll : ∀ omega, Book.Ch04.AELocallyUniformlyEllipticField (A omega))
    (Q : TriadicCube d) (i j : Fin d) :
    Measurable (fun omega ↦
      (coarseBlockMatrix (cubeSet Q) (A omega).toFun).upperRight i j) := by
  have hMu : ∀ P0 : BlockVec d,
      Measurable (fun omega ↦ Mu (cubeSet Q) P0 (A omega).toFun) := fun P0 ↦
    measurable_Mu_cubeSet_of_source hA hEll Q P0
  have hEq : (fun omega ↦ (coarseBlockMatrix (cubeSet Q) (A omega).toFun).upperRight i j) =
      fun omega ↦
        Mu (cubeSet Q) ((Pi.single i 1, 0) + (0, Pi.single j 1)) (A omega).toFun
          - Mu (cubeSet Q) (Pi.single i 1, 0) (A omega).toFun
          - Mu (cubeSet Q) (0, Pi.single j 1) (A omega).toFun := by
    funext omega
    rw [coarseBlockMatrix_upperRight_apply]
  rw [hEq]
  exact ((hMu _).sub (hMu _)).sub (hMu _)

/-- The lower-left block `-(s_*^{-1} k)(U; a)` is measurable in the source. -/
theorem measurable_coarseBlockMatrix_lowerLeft_apply (hA : Measurable A)
    (hEll : ∀ omega, Book.Ch04.AELocallyUniformlyEllipticField (A omega))
    (Q : TriadicCube d) (i j : Fin d) :
    Measurable (fun omega ↦
      (coarseBlockMatrix (cubeSet Q) (A omega).toFun).lowerLeft i j) := by
  have hMu : ∀ P0 : BlockVec d,
      Measurable (fun omega ↦ Mu (cubeSet Q) P0 (A omega).toFun) := fun P0 ↦
    measurable_Mu_cubeSet_of_source hA hEll Q P0
  have hEq : (fun omega ↦ (coarseBlockMatrix (cubeSet Q) (A omega).toFun).lowerLeft i j) =
      fun omega ↦
        Mu (cubeSet Q) ((0, Pi.single i 1) + (Pi.single j 1, 0)) (A omega).toFun
          - Mu (cubeSet Q) (0, Pi.single i 1) (A omega).toFun
          - Mu (cubeSet Q) (Pi.single j 1, 0) (A omega).toFun := by
    funext omega
    rw [coarseBlockMatrix_lowerLeft_apply]
  rw [hEq]
  exact ((hMu _).sub (hMu _)).sub (hMu _)

end Blocks

/-! ## Matrix algebra and measurability

Small entrywise helpers: products, transposes, determinants and inverses of
entrywise measurable matrix-valued maps are entrywise measurable. -/

section MatrixAlgebra

variable {Omega : Type*} [MeasurableSpace Omega]

theorem measurable_matMul_apply {M N : Omega → Mat d}
    (hM : ∀ i j, Measurable fun omega ↦ M omega i j)
    (hN : ∀ i j, Measurable fun omega ↦ N omega i j) (i j : Fin d) :
    Measurable fun omega ↦ (M omega * N omega) i j := by
  have hEq : (fun omega ↦ (M omega * N omega) i j) =
      fun omega ↦ ∑ k : Fin d, M omega i k * N omega k j := by
    funext omega; rw [Matrix.mul_apply]
  rw [hEq]
  exact Finset.measurable_sum _ fun k _ ↦ (hM i k).mul (hN k j)

theorem measurable_matTranspose_apply {M : Omega → Mat d}
    (hM : ∀ i j, Measurable fun omega ↦ M omega i j) (i j : Fin d) :
    Measurable fun omega ↦ matTranspose (M omega) i j :=
  hM j i

theorem measurable_det {M : Omega → Mat d}
    (hM : ∀ i j, Measurable fun omega ↦ M omega i j) :
    Measurable fun omega ↦ (M omega).det := by
  classical
  have hEq : (fun omega ↦ (M omega).det) =
      fun omega ↦ ∑ sigma : Equiv.Perm (Fin d),
        (Equiv.Perm.sign sigma : ℤ) * ∏ i : Fin d, M omega (sigma i) i := by
    funext omega
    rw [Matrix.det_apply']
  rw [hEq]
  refine Finset.measurable_sum _ fun sigma _ ↦ ?_
  exact measurable_const.mul (Finset.measurable_prod _ fun i _ ↦ hM (sigma i) i)

theorem measurable_matInv_apply {M : Omega → Mat d}
    (hM : ∀ i j, Measurable fun omega ↦ M omega i j) (i j : Fin d) :
    Measurable fun omega ↦ (M omega)⁻¹ i j := by
  classical
  have hEq : (fun omega ↦ (M omega)⁻¹ i j) =
      fun omega ↦ ((M omega).det)⁻¹ *
        ((M omega).updateRow j (Pi.single i 1)).det := by
    funext omega
    rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_apply, smul_eq_mul,
      Ring.inverse_eq_inv']
  rw [hEq]
  refine ((measurable_det hM).inv).mul (measurable_det ?_)
  intro r c
  by_cases hr : r = j
  · subst hr
    simp [Matrix.updateRow_self]
  · simpa only [Matrix.updateRow_ne hr] using hM r c

end MatrixAlgebra

/-! ## The blocks of `bfA(U)` are the coarse matrices

`CoarseGraining`'s measurability engine works on the half-open cube `cubeSet Q`,
while the unconditional Chapter 2 theorems live on the open cube
`(cubeDomain Q : Set (Vec d)) = openCubeSet Q`. For an admissible field the two
agree, and the blocks of the half-open block matrix are exactly the raw coarse
matrices of the open cube. -/

section BlockIdentification

variable [NeZero d] {a : RegCoeffField d}

/-- The lower-right block of `bfA(U)` is `s_*^{-1}(U)`. -/
theorem coarseBlockMatrix_cubeSet_lowerRight_eq
    (ha : Book.Ch04.AELocallyUniformlyEllipticField a) (Q : TriadicCube d) :
    (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight =
      sigmaStarInvCoarse (openCubeSet Q) a.toFun := by
  rw [Book.Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
      ha Q, Book.Ch02.coarseBlockMatrix_lowerRight,
    ← sigmaStarInvCoarse_toCoeffField (Book.Ch02.cubeDomain Q)
      ((Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q),
    Book.Ch02.cubeDomain_coe]
  rfl

/-- The lower-left block of `bfA(U)` is `-(s_*^{-1} k)(U)`. -/
theorem coarseBlockMatrix_cubeSet_lowerLeft_eq
    (ha : Book.Ch04.AELocallyUniformlyEllipticField a) (Q : TriadicCube d) :
    (coarseBlockMatrix (cubeSet Q) a.toFun).lowerLeft =
      -(sigmaStarInvCoarse (openCubeSet Q) a.toFun *
        kappaCoarse (openCubeSet Q) a.toFun) := by
  rw [Book.Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
      ha Q, Book.Ch02.coarseBlockMatrix_lowerLeft,
    ← sigmaStarInvCoarse_toCoeffField (Book.Ch02.cubeDomain Q)
      ((Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q),
    ← kappaCoarse_toCoeffField (Book.Ch02.cubeDomain Q)
      ((Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q),
    Book.Ch02.cubeDomain_coe]
  rfl

/-- `s_*(U)` recovers `k(U)` from the lower-left block. -/
theorem kappaCoarse_eq_sigmaStarCoarse_mul_neg_lowerLeft
    (ha : Book.Ch04.AELocallyUniformlyEllipticField a) (Q : TriadicCube d) :
    kappaCoarse (openCubeSet Q) a.toFun =
      sigmaStarCoarse (openCubeSet Q) a.toFun *
        (-(coarseBlockMatrix (cubeSet Q) a.toFun).lowerLeft) := by
  have hcoe : ((Book.Ch02.cubeDomain Q : Book.Ch02.Domain d) : Set (Vec d)) =
      openCubeSet Q := Book.Ch02.cubeDomain_coe Q
  have hunit : IsUnit (sigmaStarInvCoarse (openCubeSet Q) a.toFun).det := by
    have := Book.Ch02.isUnit_det_sigmaStarInvCoarse (Book.Ch02.cubeDomain Q)
      ((Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
    rwa [← sigmaStarInvCoarse_toCoeffField, hcoe] at this
  rw [coarseBlockMatrix_cubeSet_lowerLeft_eq ha Q, neg_neg, sigmaStarCoarse,
    ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mul]

end BlockIdentification

/-! ## Measurability of the coarse matrices

`e.homs.defs.U.0` averages `s_*^{-1}(U)`, `k(U)` and `s(U)`; each of them is
now a measurable function of the source. -/

section CoarseMatrices

variable [NeZero d] {Omega : Type*} [MeasurableSpace Omega] {A : Omega → RegCoeffField d}
  (hA : Measurable A)
  (hEll : ∀ omega, Book.Ch04.AELocallyUniformlyEllipticField (A omega))

include hA hEll

/-- `s_*^{-1}(U)` is measurable in the source. -/
theorem measurable_sigmaStarInvCoarse_apply (Q : TriadicCube d) (i j : Fin d) :
    Measurable fun omega ↦ sigmaStarInvCoarse (openCubeSet Q) (A omega).toFun i j := by
  have hEq : (fun omega ↦ sigmaStarInvCoarse (openCubeSet Q) (A omega).toFun i j) =
      fun omega ↦ (coarseBlockMatrix (cubeSet Q) (A omega).toFun).lowerRight i j := by
    funext omega
    rw [coarseBlockMatrix_cubeSet_lowerRight_eq (hEll omega) Q]
  rw [hEq]
  exact measurable_coarseBlockMatrix_lowerRight_apply hA hEll Q i j

/-- `s_*(U)` is measurable in the source. -/
theorem measurable_sigmaStarCoarse_apply (Q : TriadicCube d) (i j : Fin d) :
    Measurable fun omega ↦ sigmaStarCoarse (openCubeSet Q) (A omega).toFun i j :=
  measurable_matInv_apply
    (M := fun omega ↦ sigmaStarInvCoarse (openCubeSet Q) (A omega).toFun)
    (fun r c ↦ measurable_sigmaStarInvCoarse_apply hA hEll Q r c) i j

/-- `k(U)` is measurable in the source. -/
theorem measurable_kappaCoarse_apply (Q : TriadicCube d) (i j : Fin d) :
    Measurable fun omega ↦ kappaCoarse (openCubeSet Q) (A omega).toFun i j := by
  have hEq : (fun omega ↦ kappaCoarse (openCubeSet Q) (A omega).toFun i j) =
      fun omega ↦ (sigmaStarCoarse (openCubeSet Q) (A omega).toFun *
        (-(coarseBlockMatrix (cubeSet Q) (A omega).toFun).lowerLeft)) i j := by
    funext omega
    rw [kappaCoarse_eq_sigmaStarCoarse_mul_neg_lowerLeft (hEll omega) Q]
  rw [hEq]
  refine measurable_matMul_apply
    (fun r c ↦ measurable_sigmaStarCoarse_apply hA hEll Q r c) (fun r c ↦ ?_) i j
  exact (measurable_coarseBlockMatrix_lowerLeft_apply hA hEll Q r c).neg

end CoarseMatrices

/-! ## The law of the cutoff field on the coefficient carrier

Pushing the shell-sequence law forward along `omega ↦ a_m(omega)` turns it into
a `CoarseGraining` Chapter 4 coefficient law, which is where the annealed and
scalarization theory of that library is stated. Admissibility at every sample
makes this pushforward a Chapter 4 law carrier with no extra hypothesis. -/

section Law

variable (nu : ℝ) (m : ℕ) (P : ProbabilityMeasure (ShellSeq d))

/-- The law of the infrared cutoff field `a_m = nu Id + k_m` on
`CoarseGraining`'s coefficient carrier. -/
def cutoffLaw : Book.Ch04.RestrictionCoeffLaw d :=
  Measure.map (fun omega : ShellSeq d ↦ coefficientCutoff nu omega m) P.toMeasure

instance isProbabilityMeasure_cutoffLaw :
    IsProbabilityMeasure (cutoffLaw (d := d) nu m P) :=
  by unfold cutoffLaw; infer_instance

/-- Every field in the support of the cutoff law is locally a.e. uniformly
elliptic. The property holds at every sample, and the set of locally a.e.
uniformly elliptic fields is measurable, so the a.s. statement follows. -/
theorem aeLocallyUniformlyEllipticLaw_cutoffLaw {nu : ℝ} (hnu : 0 < nu) (m : ℕ)
    (P : ProbabilityMeasure (ShellSeq d)) :
    Book.Ch04.AELocallyUniformlyEllipticLaw (cutoffLaw (d := d) nu m P) := by
  rw [Book.Ch04.AELocallyUniformlyEllipticLaw, cutoffLaw,
    ae_map_iff (measurable_coefficientCutoff nu m).aemeasurable
      measurableSet_aeLocallyUniformlyEllipticField]
  exact Filter.Eventually.of_forall fun omega ↦
    aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega m

/-- The cutoff law is a Chapter 4 law carrier. -/
theorem restrictionLawCarrier_cutoffLaw {nu : ℝ} (hnu : 0 < nu) (m : ℕ)
    (P : ProbabilityMeasure (ShellSeq d)) :
    Book.Ch04.RestrictionLawCarrier (cutoffLaw (d := d) nu m P) :=
  Book.Ch04.lawCarrier_of_aeLocallyUniformlyElliptic
    (aeLocallyUniformlyEllipticLaw_cutoffLaw hnu m P)

end Law

end

end SuperdiffusionCLT.Section2.Annealed
