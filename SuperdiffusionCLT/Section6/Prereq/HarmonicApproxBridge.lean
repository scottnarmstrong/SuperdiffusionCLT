/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Book.Ch03.Theorems.HomogenizationBlackBoxes
public import Homogenization.Book.Ch03.Theorems.PublicInternalBridges.CoeffField

/-!
# Raw and public homogenization error of a cube field

The harmonic-approximation black box of `CoarseGraining` is stated for the public
Chapter 2 carriers (`TriadicCoeffFamily`), whereas the minimal-scale statement of
Section 4 speaks about the raw field (`CoeffField`) and the raw
`HomogenizationErrorOnCube`. This file builds, from a raw field that is elliptic
on one triadic cube, a public family and proves that the two homogenization
errors of the cube agree.

## Main results

* `padField`: the raw field, modified outside the cube so as to be elliptic on all of space.
* `paddedFamily`: the public family with the same representative on every cube.
* `homogenizationErrorOnCube_eq_ch02`: raw error of the field equals public error of the family.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6.HarmonicApprox

open Homogenization

noncomputable section

variable {d : ℕ}

/-! ## Almost-everywhere invariance of the raw response functional -/

theorem responseJ_congr_ae {U : Set (Vec d)} {a b : CoeffField d}
    (h : a =ᵐ[volumeMeasureOn U] b) (p q : Vec d) :
    ResponseJ U p q a = ResponseJ U p q b := by
  have key : ∀ {a b : CoeffField d}, a =ᵐ[volumeMeasureOn U] b →
      responseJValueSet U p q a ⊆ responseJValueSet U p q b := by
    intro a b h m hm
    obtain ⟨u, rfl⟩ := hm
    refine ⟨⟨u.toH1, IsAHarmonicGradient.of_ae_eq_coeff h u.isHarmonic⟩, ?_⟩
    unfold volumeAverage
    congr 1
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [h] with x hx
    simp only [scalarResponseIntegrand, hx]
  unfold ResponseJ
  exact congrArg sSup (Set.Subset.antisymm (key h) (key h.symm))

theorem adjointCoeffField_ae_eq {U : Set (Vec d)} {a b : CoeffField d}
    (h : a =ᵐ[volumeMeasureOn U] b) :
    adjointCoeffField a =ᵐ[volumeMeasureOn U] adjointCoeffField b := by
  filter_upwards [h] with x hx
  simp only [adjointCoeffField, hx]

/-- The block response of a cube is invariant under changing the field on a null set,
for fields elliptic on the cube. -/
theorem blockJ_cubeSet_congr_ae [NeZero d] (R : TriadicCube d) {a b : CoeffField d}
    {lam Lam : ℝ} (ha : IsEllipticFieldOn lam Lam (cubeSet R) a)
    (hb : IsEllipticFieldOn lam Lam (cubeSet R) b)
    (h : a =ᵐ[volumeMeasureOn (cubeSet R)] b) (P Q : BlockVec d) :
    BlockJ (cubeSet R) P Q a = BlockJ (cubeSet R) P Q b := by
  let := isFiniteMeasureVolumeMeasureOnCubeSet R
  have hvol : (MeasureTheory.volume (cubeSet R)).toReal ≠ 0 := by
    rw [volume_cubeSet_toReal]
    exact (cubeVolume_pos R).ne'
  obtain ⟨p, q⟩ := P
  obtain ⟨qs, ps⟩ := Q
  rw [blockJ_eq_half_responseJ_adjoint_sum_of_isEllipticFieldOn (a := a)
      (U := cubeSet R) (measurableSet_cubeSet R) ha hvol,
    blockJ_eq_half_responseJ_adjoint_sum_of_isEllipticFieldOn (a := b)
      (U := cubeSet R) (measurableSet_cubeSet R) hb hvol,
    responseJ_congr_ae h, responseJ_congr_ae (adjointCoeffField_ae_eq h)]

/-! ## A public family with prescribed representative on one cube -/

theorem isEllipticMatrix_scalar_of_le {lam Lam : ℝ} (h0 : 0 < lam) (hle : lam ≤ Lam) :
    IsEllipticMatrix lam Lam (lam • (1 : Mat d)) := by
  have base : IsEllipticMatrix lam lam (scalarMatrix (d := d) lam) :=
    isEllipticMatrix_scalarMatrix h0
  refine ⟨h0, hle, base.2.2.1, ?_⟩
  intro ξ
  have h4 := base.2.2.2 ξ
  have hLam : Lam⁻¹ ≤ lam⁻¹ := inv_anti₀ h0 hle
  have hnn := vecNormSq_nonneg ξ
  have : Lam⁻¹ * vecNormSq ξ ≤ lam⁻¹ * vecNormSq ξ :=
    mul_le_mul_of_nonneg_right hLam hnn
  exact this.trans h4

/-- The raw field on the cube `Q`, and the scalar matrix `lam • Id` elsewhere. -/
def padField (Q : TriadicCube d) (lam : ℝ) (a : CoeffField d) : CoeffField d := by
  classical
  exact fun x => if x ∈ cubeSet Q then a x else lam • (1 : Mat d)

theorem padField_apply_of_mem {Q : TriadicCube d} {lam : ℝ} {a : CoeffField d} {x : Vec d}
    (hx : x ∈ cubeSet Q) : padField Q lam a x = a x := by
  simp [padField, hx]

theorem isEllipticMatrix_padField {Q : TriadicCube d} {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a) (h0 : 0 < lam) (hle : lam ≤ Lam)
    (x : Vec d) : IsEllipticMatrix lam Lam (padField Q lam a x) := by
  by_cases hx : x ∈ cubeSet Q
  · rw [padField_apply_of_mem hx]
    exact hEll.2 x hx
  · have : padField Q lam a x = lam • (1 : Mat d) := by simp [padField, hx]
    rw [this]
    exact isEllipticMatrix_scalar_of_le h0 hle

theorem measurable_padField_entry {Q : TriadicCube d} {lam lam' Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam' Lam (cubeSet Q) a) (i j : Fin d) :
    Measurable (fun x => padField Q lam a x i j) := by
  classical
  have h1 : Measurable fun x => (if x ∈ cubeSet Q then a x i j else 0) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hEll.1)
  have h2 : Measurable fun x : Vec d =>
      (cubeSet Q)ᶜ.indicator (fun _ => (lam • (1 : Mat d)) i j) x :=
    measurable_const.indicator (measurableSet_cubeSet Q).compl
  have e : (fun x => padField Q lam a x i j) = fun x =>
      (if x ∈ cubeSet Q then a x i j else 0) +
        (cubeSet Q)ᶜ.indicator (fun _ => (lam • (1 : Mat d)) i j) x := by
    funext x
    by_cases hx : x ∈ cubeSet Q
    · simp [padField, hx]
    · simp [padField, hx]
  rw [e]
  exact h1.add h2

/-- The public coefficient object carrying the padded field. -/
def paddedCoeffOn (Q : TriadicCube d) {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a) (h0 : 0 < lam) (hle : lam ≤ Lam)
    (U : Book.Ch02.Domain d) : Book.Ch02.CoeffOn U where
  toCoeffField := padField Q lam a
  lam := lam
  Lam := Lam
  lam_pos := h0
  lam_le_Lam := hle
  aeStronglyMeasurable := by
    intro i j
    classical
    refine Measurable.aestronglyMeasurable ?_
    have e : (fun x => restrictCoeffField (U : Set (Vec d)) (padField Q lam a) x i j) =
        fun x => if x ∈ (U : Set (Vec d)) then padField Q lam a x i j else 0 := by
      funext x
      by_cases hx : x ∈ (U : Set (Vec d)) <;> simp [restrictCoeffField, hx]
    rw [e]
    exact Measurable.ite U.measurableSet (measurable_padField_entry hEll i j) measurable_const
  aeElliptic := Filter.Eventually.of_forall (isEllipticMatrix_padField hEll h0 hle)

/-- The public family with the padded representative on every cube. -/
def paddedFamily (Q : TriadicCube d) {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a) (h0 : 0 < lam) (hle : lam ≤ Lam) :
    Book.Ch03.CoeffFamily d where
  coeffOn R := paddedCoeffOn Q hEll h0 hle (Book.Ch02.cubeDomain R)
  restrictsTo_of_subset := fun _ => Filter.EventuallyEq.rfl

/-! ## The homogenization error of the cube agrees with that of the family -/

section Comparison

variable [NeZero d] {Q : TriadicCube d} {lam Lam : ℝ} {a : CoeffField d}

omit [NeZero d] in
theorem paddedFamily_coeffOn_toCoeffField (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (h0 : 0 < lam) (hle : lam ≤ Lam) (R : TriadicCube d) :
    ((paddedFamily Q hEll h0 hle).coeffOn R).toCoeffField = padField Q lam a :=
  rfl

omit [NeZero d] in
theorem publicCoeffField_paddedFamily_ae_eq (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (h0 : 0 < lam) (hle : lam ≤ Lam) {R : TriadicCube d}
    (hR : cubeSet R ⊆ cubeSet Q) :
    Book.Ch03.publicCoeffField Q (paddedFamily Q hEll h0 hle) =ᵐ[volumeMeasureOn (cubeSet R)] a := by
  have h1 := Book.Ch03.publicCoeffField_ae_eq_cubeSet Q (paddedFamily Q hEll h0 hle)
  have h2 : volumeMeasureOn (cubeSet R) ≤ volumeMeasureOn (cubeSet Q) := by
    unfold volumeMeasureOn
    exact MeasureTheory.Measure.restrict_mono hR le_rfl
  have h3 : ∀ᵐ x ∂ volumeMeasureOn (cubeSet R),
      Book.Ch03.publicCoeffField Q (paddedFamily Q hEll h0 hle) x =
        ((paddedFamily Q hEll h0 hle).coeffOn Q).toCoeffField x :=
    MeasureTheory.ae_mono h2 h1
  have h4 : ∀ᵐ x ∂ volumeMeasureOn (cubeSet R), x ∈ cubeSet R := by
    unfold volumeMeasureOn
    exact MeasureTheory.ae_restrict_mem (measurableSet_cubeSet R)
  filter_upwards [h3, h4] with x hx hxR
  rw [hx, paddedFamily_coeffOn_toCoeffField, padField_apply_of_mem (hR hxR)]

theorem normalizedBlockResponseMax_eq_ch02 (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (h0 : 0 < lam) (hle : lam ≤ Lam) {k : ℤ} (hk : k ≤ Q.scale)
    {R : TriadicCube d} (hR : R ∈ descendantsAtScale Q k) (a0 : Mat d) :
    normalizedBlockResponseMax R a a0 =
      Book.Ch02.normalizedBlockResponseMax R (paddedFamily Q hEll h0 hle) a0 := by
  have hsub : cubeSet R ⊆ cubeSet Q := cubeSet_subset_of_mem_descendantsAtScale hk hR
  have hae := publicCoeffField_paddedFamily_ae_eq hEll h0 hle hsub
  have ha : IsEllipticFieldOn lam Lam (cubeSet R) a := hEll.mono (measurableSet_cubeSet R) hsub
  have hb : IsEllipticFieldOn lam Lam (cubeSet R)
      (Book.Ch03.publicCoeffField Q (paddedFamily Q hEll h0 hle)) :=
    (Book.Ch03.publicCoeffField_isEllipticFieldOn_cubeSet Q (paddedFamily Q hEll h0 hle)).mono
      (measurableSet_cubeSet R) hsub
  rw [← Book.Ch03.normalizedBlockResponseMax_publicCoeffField_eq_ch02
    (paddedFamily Q hEll h0 hle) hk hR a0]
  unfold normalizedBlockResponseMax normalizedBlockResponseValueSet
  congr 1
  ext m
  constructor
  · rintro ⟨e, he, hm⟩
    exact ⟨e, he, hm.trans (blockJ_cubeSet_congr_ae R ha hb hae.symm _ _)⟩
  · rintro ⟨e, he, hm⟩
    exact ⟨e, he, hm.trans (blockJ_cubeSet_congr_ae R ha hb hae.symm _ _).symm⟩

theorem scaleResponseAtScale_infinity_eq_ch02 (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (h0 : 0 < lam) (hle : lam ≤ Lam) {k : ℤ} (hk : k ≤ Q.scale) (a0 : Mat d) :
    scaleResponseAtScale Q k MultiscaleExponent.infinity a a0 =
      Book.Ch02.scaleResponseAtScale Q k Book.Ch02.MultiscaleExponent.infinity
        (paddedFamily Q hEll h0 hle) a0 := by
  rw [scaleResponseAtScale_infinity_eq, Book.Ch02.scaleResponseAtScale_infinity_eq]
  congr 1
  unfold maxDescendantNormalizedBlockResponseAtScale Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
  rw [Book.Ch02.finsetSupReal_eq_finsetSsup]
  unfold finsetSsup
  congr 1
  exact Set.image_congr fun R hR => normalizedBlockResponseMax_eq_ch02 hEll h0 hle hk hR a0

/-- The raw homogenization error of a cube field is the public error of the padded family. -/
theorem homogenizationErrorOnCube_eq_ch02 (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (h0 : 0 < lam) (hle : lam ≤ Lam) (s q : ℝ) (a0 : Mat d) :
    HomogenizationErrorOnCube Q s MultiscaleExponent.infinity (MultiscaleExponent.finite q) a a0 =
      Book.Ch02.HomogenizationErrorOnCube Q s Book.Ch02.MultiscaleExponent.infinity
        (Book.Ch02.MultiscaleExponent.finite q) (paddedFamily Q hEll h0 hle) a0 := by
  unfold HomogenizationErrorOnCube HomogenizationError HomogenizationErrorFinite
    Book.Ch02.HomogenizationErrorOnCube Book.Ch02.HomogenizationError
    Book.Ch02.HomogenizationErrorFinite
  dsimp only
  congr 2
  funext l
  have hk : Q.scale - (l : ℤ) ≤ Q.scale := sub_le_self _ (by exact_mod_cast Nat.zero_le l)
  rw [Book.Ch02.geometricWeight_eq_old, scaleResponseAtScale_infinity_eq_ch02 hEll h0 hle hk]

end Comparison

/-! ## The `q = 1` error is bounded by the `q = 2` error at half the exponent -/

section QOneQTwo

variable [NeZero d]


/-- The `q=1` response error at order `s` is bounded by the `q=2` response
error at order `s/2`.  Both errors use the same geometric probability weights
after this order/exponent change, so this is weighted Cauchy--Schwarz. -/
theorem ch02_error_infinity_one_le_infinity_two_half
    (R : TriadicCube d) (a : Book.Ch02.TriadicCoeffFamily d)
    (a0 : Mat d) {s : ℝ} (hs : 0 < s) :
    Book.Ch02.HomogenizationErrorOnCube R s .infinity (.finite 1) a a0 ≤
      Book.Ch02.HomogenizationErrorOnCube R (s / 2) .infinity (.finite 2) a a0 := by
  let w : ℕ → ℝ := fun n => Book.Ch02.geometricWeight s 1 n
  let M : ℕ → ℝ := fun n =>
    Book.Ch02.maxDescendantNormalizedBlockResponseAtScale R (R.scale - (n : ℤ)) a a0
  have hw_nonneg : ∀ n, 0 ≤ w n := by
    intro n
    dsimp [w]
    simpa [Book.Ch02.geometricWeight_eq_old] using
      (Homogenization.geometricWeight_nonneg (s := s) (q := (1 : ℝ)) n
        (by rw [mul_one]; exact hs.le))
  have hM_nonneg : ∀ n, 0 ≤ M n := by
    intro n
    dsimp [M]
    exact Book.Ch02.maxDescendantNormalizedBlockResponseAtScale_nonneg R
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a a0
  have hw_eq : ∀ n, w n = Book.Ch02.geometricWeight (s / 2) 2 n := by
    intro n
    dsimp [w]
    unfold Book.Ch02.geometricWeight Book.Ch02.geometricDiscount
    congr 1 <;> ring_nf
  have hsumw : Summable w := by
    simpa only [w, Book.Ch02.geometricWeight_eq_old] using
      (Homogenization.summable_geometricWeight (s := s) (q := (1 : ℝ))
        (by rw [mul_one]; exact hs))
  have hsumWM : Summable (fun n => w n * M n) := by
    simpa only [M, hw_eq] using
      (Book.Ch02.summable_geometricWeight_two_mul_maxDescendantNormalizedBlockResponseAtScale
        R a a0 (by positivity : 0 < s / 2))
  let f : ℕ → ℝ := fun n => Real.sqrt (w n)
  let g : ℕ → ℝ := fun n => Real.sqrt (w n * M n)
  have hf_nonneg : ∀ n, 0 ≤ f n := fun n => Real.sqrt_nonneg _
  have hg_nonneg : ∀ n, 0 ≤ g n := fun n => Real.sqrt_nonneg _
  have hf_sq : ∀ n, f n ^ (2 : ℝ) = w n := by
    intro n
    dsimp [f]
    rw [Real.rpow_two, Real.sq_sqrt (hw_nonneg n)]
  have hg_sq : ∀ n, g n ^ (2 : ℝ) = w n * M n := by
    intro n
    dsimp [g]
    rw [Real.rpow_two, Real.sq_sqrt (mul_nonneg (hw_nonneg n) (hM_nonneg n))]
  have hfg : ∀ n, f n * g n = w n * Real.sqrt (M n) := by
    intro n
    dsimp [f, g]
    rw [Real.sqrt_mul (hw_nonneg n)]
    calc
      Real.sqrt (w n) * (Real.sqrt (w n) * Real.sqrt (M n)) =
          (Real.sqrt (w n)) ^ 2 * Real.sqrt (M n) := by ring
      _ = w n * Real.sqrt (M n) := by rw [Real.sq_sqrt (hw_nonneg n)]
  have hfsum : Summable fun n => f n ^ (2 : ℝ) := by
    convert hsumw using 1
    ext n
    exact hf_sq n
  have hgsum : Summable fun n => g n ^ (2 : ℝ) := by
    convert hsumWM using 1
    ext n
    exact hg_sq n
  have hholder : Real.HolderConjugate (2 : ℝ) (2 : ℝ) := by
    refine ⟨by norm_num, by norm_num, by norm_num⟩
  have hcs := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg hholder hf_nonneg hg_nonneg hfsum hgsum
  have hweights : ∑' n, w n = 1 := by
    simpa only [w, Book.Ch02.geometricWeight_eq_old] using
      (Homogenization.tsum_geometricWeight_eq_one (s := s) (q := (1 : ℝ))
        (by rw [mul_one]; exact hs))
  have hleft : ∑' n, f n * g n =
      Book.Ch02.HomogenizationErrorOnCube R s .infinity (.finite 1) a a0 := by
    rw [Book.Ch02.homogenizationErrorOnCube_infinity_one_eq_tsum]
    apply tsum_congr
    intro n
    rw [hfg]
    dsimp [w, M]
    rw [Real.sqrt_eq_rpow]
  have hright : (∑' n, g n ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) =
      Book.Ch02.HomogenizationErrorOnCube R (s / 2) .infinity (.finite 2) a a0 := by
    unfold Book.Ch02.HomogenizationErrorOnCube Book.Ch02.HomogenizationError
      Book.Ch02.HomogenizationErrorFinite
    change (∑' n, g n ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) =
      (∑' n, Book.Ch02.geometricWeight (s / 2) 2 n *
        (Book.Ch02.scaleResponseAtScale R (R.scale - (n : ℤ)) .infinity a a0) ^ (2 : ℝ)) ^
        (1 / (2 : ℝ))
    congr 1
    apply tsum_congr
    intro n
    rw [hg_sq, hw_eq]
    have hk : R.scale - (n : ℤ) ≤ R.scale :=
      sub_le_self _ (by exact_mod_cast Nat.zero_le n)
    have hresponse : M n =
        (Book.Ch02.scaleResponseAtScale R (R.scale - (n : ℤ)) .infinity a a0) ^ (2 : ℝ) := by
      dsimp [M]
      calc
        Book.Ch02.maxDescendantNormalizedBlockResponseAtScale R (R.scale - (n : ℤ)) a a0 =
            (Book.Ch02.scaleResponseAtScale R (R.scale - (n : ℤ)) .infinity a a0) ^ 2 :=
          (Book.Ch02.scaleResponseAtScale_infinity_sq_eq R hk a a0).symm
        _ = (Book.Ch02.scaleResponseAtScale R (R.scale - (n : ℤ)) .infinity a a0) ^ (2 : ℝ) :=
          (Real.rpow_two _).symm
    exact congrArg (fun x : ℝ => Book.Ch02.geometricWeight (s / 2) 2 n * x)
      hresponse
  rw [← hleft]
  calc
    ∑' n, f n * g n ≤
        (∑' n, f n ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
          (∑' n, g n ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := hcs
    _ = Book.Ch02.HomogenizationErrorOnCube R (s / 2) .infinity (.finite 2) a a0 := by
      have hfs : ∑' n, f n ^ (2 : ℝ) = 1 := by
        calc
          ∑' n, f n ^ (2 : ℝ) = ∑' n, w n := by
            apply tsum_congr
            exact hf_sq
          _ = 1 := hweights
      rw [hfs, Real.one_rpow, one_mul, hright]


end QOneQTwo

end

end SuperdiffusionCLT.Section6.HarmonicApprox
