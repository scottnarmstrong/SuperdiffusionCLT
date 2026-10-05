/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Prereq.FullFieldB
public import SuperdiffusionCLT.Section2.CoarseGraining.CutoffCorrespondence

/-!
# The gradient of the infinite-volume recentered stream

Almost surely `k - k(0) = ∑_n (j_n - j_n(0))` is `C¹` with gradient
`∑_n ∇ j_n`, and the cutoff gradients `∇ k_L` converge to it locally uniformly.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory Filter Topology
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Carriers
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-- The gradient of the infinite-volume stream, `∑_n ∇ j_n`. -/
def fullStreamDeriv (omega : ShellSeq d) (x : Vec d) : Vec d →L[ℝ] Mat d :=
  ∑' n : ℕ, ShellField.deriv (omega n) x

theorem norm_shellDeriv_le_originCube (omega : ShellSeq d) (n i : ℕ) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d (i : ℤ))) :
    ‖ShellField.deriv (omega n) x‖ ≤
      Real.sqrt d * shellDerivLinftyNorm (openCubeSet (originCube d (i : ℤ))) (omega n) :=
  norm_deriv_le_shellDerivLinftyNorm (isBounded_openCubeSet_originCube (d := d) (i : ℤ))
    (omega n) hx

/-- Differentiability of the recentered stream on `cu_i`, with the gradient `∑ ∇ j_n`. -/
theorem hasFDerivAt_fullStreamRecentered {omega : ShellSeq d} {i : ℕ}
    (hsum : Summable fun k : ℕ =>
      shellDerivLinftyNorm (openCubeSet (originCube d (i : ℤ))) (omega k))
    {x : Vec d} (hx : x ∈ openCubeSet (originCube d (i : ℤ))) :
    HasFDerivAt (fullStreamRecentered omega) (fullStreamDeriv omega x) x := by
  have h := hasFDerivAt_tsum_of_isPreconnected
    (f := fun (n : ℕ) (y : Vec d) => shellRecentered omega n y)
    (f' := fun (n : ℕ) (y : Vec d) => ShellField.deriv (omega n) y)
    (hsum.mul_left (Real.sqrt d)) (isOpen_openCubeSet (originCube d (i : ℤ)))
    (convex_openCubeSet (originCube d (i : ℤ))).isPreconnected
    (fun n y _ => by
      have := (omega n).hasFDerivAt y
      simpa only [shellRecentered, shellReg, ShellField.forgetShell_apply] using
        this.sub_const ((omega n) 0))
    (fun n y hy => norm_shellDeriv_le_originCube omega n i hy)
    (zero_mem_openCubeSet_originCube i)
    (summable_shellRecentered hsum (zero_mem_openCubeSet_originCube i)) hx
  exact h

/-- Almost surely the recentered stream is differentiable everywhere, with gradient
`fullStreamDeriv`. -/
theorem ae_hasFDerivAt_fullStreamRecentered {P : ProbabilityMeasure (ShellSeq d)}
    (hJ3 : ShellLawJ3 d P) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure, ∀ x : Vec d,
      HasFDerivAt (fullStreamRecentered omega) (fullStreamDeriv omega x) x := by
  filter_upwards [ae_forall_summable_shellDerivLinftyNorm_originCube hJ3] with omega hω x
  obtain ⟨i, hi⟩ := exists_openCubeSet_superset (Bornology.isBounded_singleton (x := x))
  exact hasFDerivAt_fullStreamRecentered (hω i) (hi rfl)

/-- On `cu_i` the cutoff gradients converge uniformly to `fullStreamDeriv`. -/
theorem tendstoUniformlyOn_streamCutoffDeriv {omega : ShellSeq d} {i : ℕ}
    (hsum : Summable fun k : ℕ =>
      shellDerivLinftyNorm (openCubeSet (originCube d (i : ℤ))) (omega k)) :
    TendstoUniformlyOn (fun (L : ℕ) (x : Vec d) => streamCutoffDeriv omega L x)
      (fullStreamDeriv omega) atTop (openCubeSet (originCube d (i : ℤ))) := by
  have h0 : TendstoUniformlyOn
      (fun (t : Finset ℕ) (x : Vec d) => ∑ n ∈ t, ShellField.deriv (omega n) x)
      (fullStreamDeriv omega) atTop (openCubeSet (originCube d (i : ℤ))) :=
    tendstoUniformlyOn_tsum (hsum.mul_left (Real.sqrt d))
      fun n _ hx => norm_shellDeriv_le_originCube omega n i hx
  have h := h0.seq_tendstoUniformlyOn
    (fun L : ℕ => Finset.range (L + 1))
    (tendsto_finset_range.comp (tendsto_add_atTop_nat 1))
  exact h

/-- Almost surely, for every bounded set, the cutoff gradients converge uniformly. -/
theorem ae_tendstoUniformlyOn_streamCutoffDeriv {P : ProbabilityMeasure (ShellSeq d)}
    (hJ3 : ShellLawJ3 d P) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure, ∀ S : Set (Vec d), Bornology.IsBounded S →
      TendstoUniformlyOn (fun (L : ℕ) (x : Vec d) => streamCutoffDeriv omega L x)
        (fullStreamDeriv omega) atTop S := by
  filter_upwards [ae_forall_summable_shellDerivLinftyNorm_originCube hJ3] with omega hω S hS
  obtain ⟨i, hi⟩ := exists_openCubeSet_superset hS
  exact (tendstoUniformlyOn_streamCutoffDeriv (hω i)).mono hi

/-- Almost surely the gradient is continuous, so the recentered stream is `C¹`. -/
theorem ae_continuous_fullStreamDeriv {P : ProbabilityMeasure (ShellSeq d)}
    (hJ3 : ShellLawJ3 d P) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure, Continuous (fullStreamDeriv omega) := by
  filter_upwards [ae_forall_summable_shellDerivLinftyNorm_originCube hJ3] with omega hω
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨i, hi⟩ := exists_openCubeSet_superset (Bornology.isBounded_singleton (x := x))
  have hcont : ContinuousOn (fullStreamDeriv omega)
      (openCubeSet (originCube d (i : ℤ))) := by
    refine (tendstoUniformlyOn_streamCutoffDeriv (hω i)).continuousOn
      (Frequently.of_forall fun L => ?_)
    exact (continuous_finsetSum _ fun n _ => (ShellField.deriv (omega n)).continuous).continuousOn
  exact hcont.continuousAt
    ((isOpen_openCubeSet (originCube d (i : ℤ))).mem_nhds (hi rfl))

/-- Almost surely the recentered stream is `C¹`. -/
theorem ae_contDiff_fullStreamRecentered {P : ProbabilityMeasure (ShellSeq d)}
    (hJ3 : ShellLawJ3 d P) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure, ContDiff ℝ 1 (fullStreamRecentered omega) := by
  filter_upwards [ae_hasFDerivAt_fullStreamRecentered hJ3, ae_continuous_fullStreamDeriv hJ3]
    with omega h1 h2
  exact contDiff_one_iff_hasFDerivAt.mpr ⟨fullStreamDeriv omega, h2, h1⟩

/-- Almost surely the gradient is the Fréchet derivative of the recentered stream. -/
theorem ae_fderiv_fullStreamRecentered {P : ProbabilityMeasure (ShellSeq d)}
    (hJ3 : ShellLawJ3 d P) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure,
      fderiv ℝ (fullStreamRecentered omega) = fullStreamDeriv omega := by
  filter_upwards [ae_hasFDerivAt_fullStreamRecentered hJ3] with omega h
  exact funext fun x => (h x).fderiv

/-! ## Skewness of the gradient -/

/-- Almost surely each directional derivative of the recentered stream is skew. -/
theorem ae_fullStreamDeriv_skew_entry {P : ProbabilityMeasure (ShellSeq d)}
    (hJ3 : ShellLawJ3 d P) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure, ∀ (x v : Vec d) (i k : Fin d),
      fullStreamDeriv omega x v i k = -fullStreamDeriv omega x v k i := by
  filter_upwards [ae_forall_summable_shellDerivLinftyNorm_originCube hJ3] with omega hω x v i k
  obtain ⟨j, hj⟩ := exists_openCubeSet_superset (Bornology.isBounded_singleton (x := x))
  have hs : Summable fun n : ℕ => ShellField.deriv (omega n) x :=
    Summable.of_norm_bounded ((hω j).mul_left (Real.sqrt d))
      fun n => norm_shellDeriv_le_originCube omega n j (hj rfl)
  have hv : fullStreamDeriv omega x v = ∑' n, ShellField.deriv (omega n) x v := by
    rw [fullStreamDeriv]
    exact (ContinuousLinearMap.apply ℝ (Mat d) v).map_tsum hs
  have hsv : Summable fun n : ℕ => ShellField.deriv (omega n) x v :=
    (ContinuousLinearMap.apply ℝ (Mat d) v).summable hs
  rw [hv]
  refine tsum_skew_entry _ (fun n a b => ?_) i k
  have hder := (omega n).hasFDerivAt x
  have hline : HasDerivAt (fun t : ℝ => (omega n) (x + t • v)) (ShellField.deriv (omega n) x v) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
    have := (show HasFDerivAt (omega n) (ShellField.deriv (omega n) x) (x + (0 : ℝ) • v) by
      simpa using hder).comp_hasDerivAt 0 h1
    exact this
  have hab := hasDerivAt_pi.mp (hasDerivAt_pi.mp hline a) b
  have hba := hasDerivAt_pi.mp (hasDerivAt_pi.mp hline b) a
  have hneg : HasDerivAt (fun t : ℝ => -(omega n) (x + t • v) b a)
      (-ShellField.deriv (omega n) x v b a) 0 := hba.neg
  have heq : (fun t : ℝ => (omega n) (x + t • v) a b) =
      fun t : ℝ => -(omega n) (x + t • v) b a :=
    funext fun t => ShellField.skew_entry (omega n) (x + t • v) a b
  rw [heq] at hab
  exact hab.unique hneg

/-! ## The coefficient field -/

theorem measurable_fullCoefficientRecentered (nu : ℝ) (omega : ShellSeq d) :
    Measurable (fullCoefficientRecentered nu omega) := by
  have hpair : Measurable (fun x : Vec d => (x, omega)) :=
    measurable_id.prodMk measurable_const
  have hcomp := (measurable_fullCoefficientRecentered_uncurry (d := d) nu).comp hpair
  exact hcomp

theorem continuous_fullCoefficientRecentered {nu : ℝ} {omega : ShellSeq d}
    (h : Continuous (fullStreamRecentered omega)) :
    Continuous (fullCoefficientRecentered nu omega) :=
  continuous_const.add h

/-- Almost surely the coefficient field is locally bounded: its entries are bounded on every
bounded set. -/
theorem ae_exists_entryBound_fullCoefficientRecentered {P : ProbabilityMeasure (ShellSeq d)}
    (hJ3 : ShellLawJ3 d P) (nu : ℝ) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure, ∀ S : Set (Vec d), Bornology.IsBounded S →
      ∃ C : ℝ, ∀ x ∈ S, ∀ i j : Fin d, |fullCoefficientRecentered nu omega x i j| ≤ C := by
  filter_upwards [ae_continuous_fullStreamRecentered hJ3] with omega hc S hS
  have hcoef := continuous_fullCoefficientRecentered (nu := nu) hc
  set g : Vec d → ℝ := fun x => ∑ i : Fin d, ∑ j : Fin d, |fullCoefficientRecentered nu omega x i j|
    with hg
  have hcont : Continuous g := by
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact continuous_abs.comp ((continuous_apply j).comp ((continuous_apply i).comp hcoef))
  obtain ⟨C, hC⟩ := hS.isCompact_closure.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨C, fun x hx i j => ?_⟩
  have hle : ‖g x‖ ≤ C := hC x (subset_closure hx)
  rw [Real.norm_eq_abs] at hle
  have hsingle : |fullCoefficientRecentered nu omega x i j| ≤ g x := by
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun i' : Fin d => ∑ j' : Fin d, |fullCoefficientRecentered nu omega x i' j'|)
      (fun i' _ => Finset.sum_nonneg fun j' _ => abs_nonneg _) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j' : Fin d => |fullCoefficientRecentered nu omega x i j'|)
      (fun j' _ => abs_nonneg _) (Finset.mem_univ j)
  exact hsingle.trans ((le_abs_self (g x)).trans hle)

theorem symmPart_fullCoefficientRecentered (nu : ℝ) (omega : ShellSeq d) (x : Vec d) :
    symmPart (fullCoefficientRecentered nu omega x) = nu • (1 : Mat d) := by
  ext i k
  have hskew := fullStreamRecentered_skew_entry omega x k i
  simp only [symmPart, fullCoefficientRecentered, Matrix.add_apply, Matrix.smul_apply]
  rw [hskew]
  by_cases hik : i = k
  · subst k
    simp only [Matrix.one_apply, smul_eq_mul]
    ring
  · have hki : k ≠ i := Ne.symm hik
    simp only [Matrix.one_apply, hik, hki, ite_false, smul_eq_mul]
    ring

/-- The coefficient object of the recentered full field on a domain, with the same
ellipticity constants as the cutoff fields: lower `nu`, upper `(d² C² + nu²)/nu`, for an
entry bound `C` on the domain. -/
def fullCoeffOn (U : Book.Ch02.Domain d) {nu C : ℝ} (hnu : 0 < nu) (omega : ShellSeq d)
    (hentry : ∀ x ∈ (U : Set (Vec d)), ∀ i j,
      |fullCoefficientRecentered nu omega x i j| ≤ C) : Book.Ch02.CoeffOn U where
  toCoeffField := fullCoefficientRecentered nu omega
  lam := nu
  Lam := ((d : ℝ) * (d : ℝ) * C ^ 2 + nu ^ 2) / nu
  lam_pos := hnu
  lam_le_Lam := by
    rw [le_div_iff₀ hnu, ← pow_two]
    linarith only [show (0 : ℝ) ≤ (d : ℝ) * (d : ℝ) * C ^ 2 by positivity]
  aeStronglyMeasurable := by
    classical
    intro i j
    have hEq : (fun x : Vec d =>
        restrictCoeffField (U : Set (Vec d)) (fullCoefficientRecentered nu omega) x i j) =
        fun x : Vec d => if x ∈ (U : Set (Vec d))
          then fullCoefficientRecentered nu omega x i j else 0 := by
      funext x
      by_cases hx : x ∈ (U : Set (Vec d)) <;> simp [restrictCoeffField, hx]
    rw [hEq]
    have hm : Measurable fun x : Vec d => fullCoefficientRecentered nu omega x i j :=
      (measurable_pi_apply j).comp ((measurable_pi_apply i).comp
        (measurable_fullCoefficientRecentered nu omega))
    exact (hm.ite U.measurableSet measurable_const).aestronglyMeasurable
  aeElliptic := by
    filter_upwards [MeasureTheory.ae_restrict_mem U.measurableSet] with x hx
    exact SuperdiffusionCLT.Section2.CoarseGraining.isEllipticMatrix_of_symmPart_eq_smul_one
      hnu (symmPart_fullCoefficientRecentered nu omega x) (hentry x hx)

@[simp] theorem fullCoeffOn_toCoeffField (U : Book.Ch02.Domain d) {nu C : ℝ} (hnu : 0 < nu)
    (omega : ShellSeq d)
    (hentry : ∀ x ∈ (U : Set (Vec d)), ∀ i j,
      |fullCoefficientRecentered nu omega x i j| ≤ C) :
    (fullCoeffOn U hnu omega hentry).toCoeffField = fullCoefficientRecentered nu omega :=
  rfl

/-- Almost surely, every domain carries the coefficient object of the full field. -/
theorem ae_exists_fullCoeffOn {P : ProbabilityMeasure (ShellSeq d)}
    (hJ3 : ShellLawJ3 d P) {nu : ℝ} (hnu : 0 < nu) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure, ∀ U : Book.Ch02.Domain d, ∃ C : ℝ,
      ∃ hentry : (∀ x ∈ (U : Set (Vec d)), ∀ i j,
        |fullCoefficientRecentered nu omega x i j| ≤ C),
        (fullCoeffOn U hnu omega hentry).toCoeffField = fullCoefficientRecentered nu omega := by
  filter_upwards [ae_exists_entryBound_fullCoefficientRecentered hJ3 nu] with omega h U
  obtain ⟨C, hC⟩ := h _ U.isDomain.isBoundedDomain.isBounded
  exact ⟨C, hC, rfl⟩

/-! ## Satisfiability witnesses -/

example :
    ∀ᵐ omega : ShellSeq d ∂(SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw d).toMeasure,
      ∀ x : Vec d, HasFDerivAt (fullStreamRecentered omega) (fullStreamDeriv omega x) x :=
  ae_hasFDerivAt_fullStreamRecentered
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ3_diracZeroLaw

example :
    ∀ᵐ omega : ShellSeq d ∂(SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw d).toMeasure,
      ContDiff ℝ 1 (fullStreamRecentered omega) :=
  ae_contDiff_fullStreamRecentered
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ3_diracZeroLaw

example :
    ∀ᵐ omega : ShellSeq d ∂(SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw d).toMeasure,
      ∀ S : Set (Vec d), Bornology.IsBounded S →
        TendstoUniformlyOn (fun (L : ℕ) (x : Vec d) => streamCutoffDeriv omega L x)
          (fullStreamDeriv omega) atTop S :=
  ae_tendstoUniformlyOn_streamCutoffDeriv
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ3_diracZeroLaw

example :
    ∀ᵐ omega : ShellSeq d ∂(SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw d).toMeasure,
      ∀ (x v : Vec d) (i k : Fin d),
        fullStreamDeriv omega x v i k = -fullStreamDeriv omega x v k i :=
  ae_fullStreamDeriv_skew_entry
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ3_diracZeroLaw

example {nu : ℝ} (hnu : 0 < nu) :
    ∀ᵐ omega : ShellSeq d ∂(SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw d).toMeasure,
      ∀ U : Book.Ch02.Domain d, ∃ C : ℝ,
        ∃ hentry : (∀ x ∈ (U : Set (Vec d)), ∀ i j,
          |fullCoefficientRecentered nu omega x i j| ≤ C),
          (fullCoeffOn U hnu omega hentry).toCoeffField = fullCoefficientRecentered nu omega :=
  ae_exists_fullCoeffOn
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ3_diracZeroLaw hnu

end

end SuperdiffusionCLT.Section6
