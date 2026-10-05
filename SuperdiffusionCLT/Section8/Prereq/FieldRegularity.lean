/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Prereq.FullFieldGrad
public import SuperdiffusionCLT.Section2.Cutoff.DerivativeSummability
public import SuperdiffusionCLT.Assumptions.ShellLaw.J3Consequences
public import SuperdiffusionCLT.Assumptions.ShellLaw.Nonvacuity

/-!
# Local `C^{1,1}` regularity of the recentred full field

Under `ShellLawJ3` alone, almost surely `fullStreamRecentered omega` is `C²` with second
derivative the series `∑_n ∇² j_n`, locally uniformly convergent: on the natural cube `cu_i`
the weight `d 3^{2n}` of the third term of the J3 observable and Borel-Cantelli at the scale
`3^{n/2}` give `d ‖∇² j_n‖_{L∞(cu_i)} ≤ (√3/9)^n` for large `n`.  Consequently the derivative is
Lipschitz on every ball, hence `α`-Hölder for every `α ∈ (0, 1]`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization Homogenization.Book.Ch02 MeasureTheory Filter Topology
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Carriers
open SuperdiffusionCLT.Section6
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

theorem fieldReg_norm_mat_le_matrixOperatorNorm (A : Mat d) :
    ‖A‖ ≤ matrixOperatorNorm A := by
  rw [Matrix.norm_le_iff (matrixOperatorNorm_nonneg A)]
  intro i l
  simpa only [Real.norm_eq_abs] using abs_entry_le_matrixOperatorNorm A i l

theorem fieldReg_vecNorm_le_sqrt_dim_mul_norm (v : Vec d) :
    vecNorm v ≤ Real.sqrt d * ‖v‖ := by
  have hsq : vecNormSq v ≤ (d : ℝ) * ‖v‖ ^ 2 := by
    have hterm : ∀ i : Fin d, v i * v i ≤ ‖v‖ ^ 2 := by
      intro i
      have hvi : |v i| ≤ ‖v‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i
      have := mul_self_le_mul_self (abs_nonneg (v i)) hvi
      rw [abs_mul_abs_self] at this
      simpa only [pow_two] using this
    calc
      vecNormSq v = ∑ i : Fin d, v i * v i := rfl
      _ ≤ ∑ _i : Fin d, ‖v‖ ^ 2 := Finset.sum_le_sum fun i _ => hterm i
      _ = (d : ℝ) * ‖v‖ ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
  calc
    vecNorm v = Real.sqrt (vecNormSq v) := by
      rw [← vecNorm_sq_eq_vecNormSq, Real.sqrt_sq (vecNorm_nonneg v)]
    _ ≤ Real.sqrt ((d : ℝ) * ‖v‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt d * ‖v‖ := by
        rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq (norm_nonneg v)]

theorem fieldReg_vecNorm_smul (c : ℝ) (v : Vec d) :
    vecNorm (c • v) = |c| * vecNorm v := by
  simp only [vecNorm, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]

theorem fieldReg_matrixOperatorNorm_smul (c : ℝ) (A : Mat d) :
    matrixOperatorNorm (c • A) = |c| * matrixOperatorNorm A := by
  simp only [matrixOperatorNorm, map_smul, norm_smul, Real.norm_eq_abs]

theorem fieldReg_vecNorm_eq_zero {v : Vec d} (h : vecNorm v = 0) : v = 0 := by
  have hsq : vecNormSq v = 0 := by
    rw [← vecNorm_sq_eq_vecNormSq, h]
    ring
  funext i
  have hle : v i ^ 2 ≤ 0 := by
    rw [← hsq]
    exact sq_apply_le_vecNormSq v i
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
    (le_antisymm hle (sq_nonneg (v i)))

theorem fieldReg_matrixOperatorNorm_apply_le_mul (D : ShellField.MatrixDerivative d)
    (v : Vec d) :
    matrixOperatorNorm (D v) ≤ ShellField.matrixDerivativeNorm D * vecNorm v := by
  rcases eq_or_lt_of_le (vecNorm_nonneg v) with hzero | hpos
  · have hv : v = 0 := fieldReg_vecNorm_eq_zero hzero.symm
    rw [← hzero, mul_zero, hv, map_zero]
    exact le_of_eq (matrixOperatorNorm_zero (d := d))
  · set t : ℝ := vecNorm v with ht
    have htne : t ≠ 0 := ne_of_gt hpos
    have hw : vecNorm (t⁻¹ • v) ≤ 1 := by
      rw [fieldReg_vecNorm_smul, ← ht, abs_of_nonneg (inv_nonneg.2 hpos.le),
        inv_mul_cancel₀ htne]
    have hle := ShellField.matrixOperatorNorm_apply_le_matrixDerivativeNorm D (t⁻¹ • v) hw
    rw [map_smul, fieldReg_matrixOperatorNorm_smul,
      abs_of_nonneg (inv_nonneg.2 hpos.le)] at hle
    have hmul := mul_le_mul_of_nonneg_left hle hpos.le
    rwa [← mul_assoc, mul_inv_cancel₀ htne, one_mul, mul_comm] at hmul

/-- The ambient operator norm of a matrix-valued derivative is at most `√d` times its
induced norm. -/
theorem fieldReg_norm_le_sqrt_mul_mdn (D : ShellField.MatrixDerivative d) :
    ‖D‖ ≤ Real.sqrt d * ShellField.matrixDerivativeNorm D := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (Real.sqrt_nonneg _) (ShellField.matrixDerivativeNorm_nonneg D)) ?_
  intro v
  calc
    ‖D v‖ ≤ matrixOperatorNorm (D v) := fieldReg_norm_mat_le_matrixOperatorNorm _
    _ ≤ ShellField.matrixDerivativeNorm D * vecNorm v := fieldReg_matrixOperatorNorm_apply_le_mul _ _
    _ ≤ ShellField.matrixDerivativeNorm D * (Real.sqrt d * ‖v‖) :=
        mul_le_mul_of_nonneg_left (fieldReg_vecNorm_le_sqrt_dim_mul_norm v)
          (ShellField.matrixDerivativeNorm_nonneg D)
    _ = Real.sqrt d * ShellField.matrixDerivativeNorm D * ‖v‖ := by ring

/-- The ambient operator norm of a second derivative is at most `d` times its twice-induced
norm. -/
theorem fieldReg_norm_le_dim_mul_msn (H : ShellField.MatrixSecondDerivative d) :
    ‖H‖ ≤ (d : ℝ) * ShellField.matrixSecondDerivativeNorm H := by
  have hsd : Real.sqrt d * Real.sqrt d = (d : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg d)
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (Nat.cast_nonneg d) (ShellField.matrixSecondDerivativeNorm_nonneg H)) ?_
  intro v
  have hpt : ‖H v‖ ≤ Real.sqrt d * ShellField.matrixSecondDerivativeNorm H * vecNorm v := by
    rcases eq_or_lt_of_le (vecNorm_nonneg v) with hzero | hpos
    · have hv : v = 0 := fieldReg_vecNorm_eq_zero hzero.symm
      rw [← hzero, mul_zero, hv, map_zero, norm_zero]
    · set t : ℝ := vecNorm v with ht
      have htne : t ≠ 0 := ne_of_gt hpos
      have hw : vecNorm (t⁻¹ • v) ≤ 1 := by
        rw [fieldReg_vecNorm_smul, ← ht, abs_of_nonneg (inv_nonneg.2 hpos.le),
          inv_mul_cancel₀ htne]
      have h1 := ShellField.matrixDerivativeNorm_apply_le_matrixSecondDerivativeNorm H _ hw
      have h2 := (fieldReg_norm_le_sqrt_mul_mdn (H (t⁻¹ • v))).trans
        (mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _))
      have h3 : H v = t • H (t⁻¹ • v) := by
        rw [map_smul, smul_smul, mul_inv_cancel₀ htne, one_smul]
      rw [h3, norm_smul, Real.norm_eq_abs, abs_of_nonneg hpos.le]
      calc t * ‖H (t⁻¹ • v)‖ ≤ t * (Real.sqrt d * ShellField.matrixSecondDerivativeNorm H) :=
            mul_le_mul_of_nonneg_left h2 hpos.le
        _ = _ := by ring
  calc ‖H v‖ ≤ Real.sqrt d * ShellField.matrixSecondDerivativeNorm H * vecNorm v := hpt
    _ ≤ Real.sqrt d * ShellField.matrixSecondDerivativeNorm H * (Real.sqrt d * ‖v‖) :=
        mul_le_mul_of_nonneg_left (fieldReg_vecNorm_le_sqrt_dim_mul_norm v)
          (mul_nonneg (Real.sqrt_nonneg _) (ShellField.matrixSecondDerivativeNorm_nonneg H))
    _ = (Real.sqrt d * Real.sqrt d) * ShellField.matrixSecondDerivativeNorm H * ‖v‖ := by ring
    _ = (d : ℝ) * ShellField.matrixSecondDerivativeNorm H * ‖v‖ := by rw [hsd]

/-! ## The second-derivative cube norm and the J3 observable -/

theorem fieldReg_msn_le_scs (n : ℕ) (j : ShellField d) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d (n : ℤ))) :
    ShellField.matrixSecondDerivativeNorm (ShellField.secondDeriv j x) ≤
      ShellField.shellCubeSecondDerivNorm n j :=
  ((ShellField.shellCubeSecondDerivNorm_le_iff n j _).1 le_rfl).2 ⟨x, hx⟩

theorem fieldReg_scs_mono {i n : ℕ} (h : i ≤ n) (j : ShellField d) :
    ShellField.shellCubeSecondDerivNorm i j ≤ ShellField.shellCubeSecondDerivNorm n j := by
  refine (ShellField.shellCubeSecondDerivNorm_le_iff i j _).2
    ⟨ShellField.shellCubeSecondDerivNorm_nonneg n j, fun x => ?_⟩
  exact fieldReg_msn_le_scs n j (openCubeSet_originCube_subset h x.2)

theorem fieldReg_dim_mul_scs_le_j3 (n : ℕ) (j : ShellField d) :
    ((d : ℝ) * (3 : ℝ) ^ (2 * n)) * ShellField.shellCubeSecondDerivNorm n j ≤
      ShellField.j3Observable d n j := by
  have h1 := ShellField.shellCubeValueNorm_nonneg n j
  have h2 : 0 ≤ (Real.sqrt d * (3 : ℝ) ^ n) * ShellField.shellCubeDerivNorm n j :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg (by norm_num) n))
      (ShellField.shellCubeDerivNorm_nonneg n j)
  unfold ShellField.j3Observable
  linarith only [h1, h2]

/-- The decay ratio `√3 / 9` of the second-derivative cube norms. -/
def fieldReg_ratio : ℝ := Real.sqrt 3 / 9

theorem fieldReg_ratio_nonneg : 0 ≤ fieldReg_ratio := by
  unfold fieldReg_ratio; positivity

theorem fieldReg_ratio_lt_one : fieldReg_ratio < 1 := by
  unfold fieldReg_ratio
  have h3 : Real.sqrt (3 : ℝ) < 3 :=
    (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 3)).mpr (by norm_num)
  rw [div_lt_one (by norm_num : (0 : ℝ) < 9)]
  linarith only [h3]

theorem fieldReg_dim_mul_scs_le_of_j3 (n : ℕ) (j : ShellField d)
    (h : ShellField.j3Observable d n j ≤ (Real.sqrt 3) ^ n) :
    (d : ℝ) * ShellField.shellCubeSecondDerivNorm n j ≤ fieldReg_ratio ^ n := by
  have h1 := (fieldReg_dim_mul_scs_le_j3 n j).trans h
  have h9 : (0 : ℝ) < 9 ^ n := by positivity
  have h2 : ((d : ℝ) * ShellField.shellCubeSecondDerivNorm n j) * 9 ^ n ≤ (Real.sqrt 3) ^ n := by
    have : ((d : ℝ) * (3 : ℝ) ^ (2 * n)) * ShellField.shellCubeSecondDerivNorm n j =
        ((d : ℝ) * ShellField.shellCubeSecondDerivNorm n j) * 9 ^ n := by
      rw [pow_mul]; norm_num; ring
    linarith only [h1, this]
  unfold fieldReg_ratio
  rw [div_pow, le_div_iff₀ h9]
  exact h2

/-! ## Borel-Cantelli for the J3 observable at the scale `3^{n/2}` -/

theorem fieldReg_measure_j3_gt {P : ProbabilityMeasure (ShellSeq d)} (hJ3 : ShellLawJ3 d P)
    (n : ℕ) :
    P.toMeasure {omega : ShellSeq d | (Real.sqrt 3) ^ n < ShellField.j3Observable d n (omega n)} ≤
      ENNReal.ofReal (Real.exp (-((3 : ℝ) ^ n))) := by
  have h1 : 1 ≤ (Real.sqrt 3) ^ n := one_le_pow₀ (by
    have : (1 : ℝ) ≤ Real.sqrt 3 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by norm_num)
    exact this)
  have hsq : ((Real.sqrt 3) ^ n) ^ 2 = (3 : ℝ) ^ n := by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]
  have h := hJ3.gaussian_tail n ((Real.sqrt 3) ^ n) h1
  rw [hsq] at h
  exact h

theorem fieldReg_eventually_j3_le {P : ProbabilityMeasure (ShellSeq d)}
    (hJ3 : ShellLawJ3 d P) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure,
      ∀ᶠ n in atTop, ShellField.j3Observable d n (omega n) ≤ (Real.sqrt 3) ^ n := by
  have hne : (∑' n : ℕ, P.toMeasure {omega : ShellSeq d |
      (Real.sqrt 3) ^ n < ShellField.j3Observable d n (omega n)}) ≠ ⊤ := by
    have hle : (∑' n : ℕ, P.toMeasure {omega : ShellSeq d |
        (Real.sqrt 3) ^ n < ShellField.j3Observable d n (omega n)}) ≤
        ENNReal.ofReal (∑' n : ℕ, Real.exp (-((3 : ℝ) ^ n))) :=
      calc _ ≤ ∑' n : ℕ, ENNReal.ofReal (Real.exp (-((3 : ℝ) ^ n))) :=
            ENNReal.tsum_le_tsum fun n => fieldReg_measure_j3_gt hJ3 n
        _ = _ := (ENNReal.ofReal_tsum_of_nonneg (fun _ => Real.exp_nonneg _)
            summable_exp_neg_three_pow).symm
    exact ne_of_lt (lt_of_le_of_lt hle ENNReal.ofReal_lt_top)
  have hmem := MeasureTheory.ae_eventually_notMem (μ := P.toMeasure)
    (s := fun n : ℕ => {omega : ShellSeq d |
      (Real.sqrt 3) ^ n < ShellField.j3Observable d n (omega n)}) hne
  filter_upwards [hmem] with omega homega
  filter_upwards [homega] with n hn
  exact le_of_not_gt hn

/-- Almost surely, on every natural cube the series of the second-derivative cube norms is
summable (weighted by `d`). -/
theorem fieldReg_ae_summable_scs {P : ProbabilityMeasure (ShellSeq d)}
    (hJ3 : ShellLawJ3 d P) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure, ∀ i : ℕ,
      Summable fun n : ℕ => (d : ℝ) * ShellField.shellCubeSecondDerivNorm i (omega n) := by
  filter_upwards [fieldReg_eventually_j3_le hJ3] with omega hω i
  have hgeo : Summable fun n : ℕ => fieldReg_ratio ^ n :=
    summable_geometric_of_lt_one fieldReg_ratio_nonneg fieldReg_ratio_lt_one
  refine Summable.of_norm_bounded_eventually_nat hgeo ?_
  filter_upwards [hω, eventually_ge_atTop i] with n hn hin
  have hnn : 0 ≤ (d : ℝ) * ShellField.shellCubeSecondDerivNorm i (omega n) :=
    mul_nonneg (Nat.cast_nonneg d) (ShellField.shellCubeSecondDerivNorm_nonneg i _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact (mul_le_mul_of_nonneg_left (fieldReg_scs_mono hin (omega n)) (Nat.cast_nonneg d)).trans
    (fieldReg_dim_mul_scs_le_of_j3 n (omega n) hn)

/-! ## The second derivative of the recentred stream -/

/-- The candidate second derivative of the recentred stream, `∑_n ∇² j_n`. -/
def fieldReg_secondSeries (omega : ShellSeq d) (x : Vec d) :
    Vec d →L[ℝ] (Vec d →L[ℝ] Mat d) :=
  ∑' n : ℕ, ShellField.secondDeriv (omega n) x

theorem fieldReg_norm_secondDeriv_le {omega : ShellSeq d} {i : ℕ} (n : ℕ)
    {x : Vec d} (hx : x ∈ openCubeSet (originCube d (i : ℤ))) :
    ‖ShellField.secondDeriv (omega n) x‖ ≤
      (d : ℝ) * ShellField.shellCubeSecondDerivNorm i (omega n) :=
  (fieldReg_norm_le_dim_mul_msn _).trans
    (mul_le_mul_of_nonneg_left (fieldReg_msn_le_scs i (omega n) hx) (Nat.cast_nonneg d))

theorem fieldReg_summable_deriv_zero {omega : ShellSeq d} {i : ℕ}
    (hsum : Summable fun k : ℕ =>
      shellDerivLinftyNorm (openCubeSet (originCube d (i : ℤ))) (omega k)) :
    Summable fun n : ℕ => ShellField.deriv (omega n) 0 :=
  Summable.of_norm_bounded ((hsum).mul_left (Real.sqrt d))
    fun n => norm_shellDeriv_le_originCube omega n i (zero_mem_openCubeSet_originCube i)

theorem fieldReg_hasFDerivAt_fullStreamDeriv {omega : ShellSeq d} {i : ℕ}
    (hsum : Summable fun k : ℕ =>
      shellDerivLinftyNorm (openCubeSet (originCube d (i : ℤ))) (omega k))
    (hs2 : Summable fun n : ℕ => (d : ℝ) * ShellField.shellCubeSecondDerivNorm i (omega n))
    {x : Vec d} (hx : x ∈ openCubeSet (originCube d (i : ℤ))) :
    HasFDerivAt (fullStreamDeriv omega) (fieldReg_secondSeries omega x) x :=
  hasFDerivAt_tsum_of_isPreconnected
    (f := fun (n : ℕ) (y : Vec d) => ShellField.deriv (omega n) y)
    (f' := fun (n : ℕ) (y : Vec d) => ShellField.secondDeriv (omega n) y)
    hs2 (isOpen_openCubeSet (originCube d (i : ℤ)))
    (convex_openCubeSet (originCube d (i : ℤ))).isPreconnected
    (fun n y _ => ShellField.deriv_hasFDerivAt (omega n) y)
    (fun n _ hy => fieldReg_norm_secondDeriv_le n hy)
    (zero_mem_openCubeSet_originCube i) (fieldReg_summable_deriv_zero hsum) hx

theorem fieldReg_norm_secondSeries_le {omega : ShellSeq d} {i : ℕ}
    (hs2 : Summable fun n : ℕ => (d : ℝ) * ShellField.shellCubeSecondDerivNorm i (omega n))
    {x : Vec d} (hx : x ∈ openCubeSet (originCube d (i : ℤ))) :
    ‖fieldReg_secondSeries omega x‖ ≤
      ∑' n : ℕ, (d : ℝ) * ShellField.shellCubeSecondDerivNorm i (omega n) :=
  tsum_of_norm_bounded (hs2.hasSum) fun n => fieldReg_norm_secondDeriv_le n hx

theorem fieldReg_continuousOn_secondSeries {omega : ShellSeq d} {i : ℕ}
    (hs2 : Summable fun n : ℕ => (d : ℝ) * ShellField.shellCubeSecondDerivNorm i (omega n)) :
    ContinuousOn (fieldReg_secondSeries omega) (openCubeSet (originCube d (i : ℤ))) := by
  have h0 : TendstoUniformlyOn
      (fun (t : Finset ℕ) (x : Vec d) => ∑ n ∈ t, ShellField.secondDeriv (omega n) x)
      (fieldReg_secondSeries omega) atTop (openCubeSet (originCube d (i : ℤ))) :=
    tendstoUniformlyOn_tsum hs2 fun n _ hx => fieldReg_norm_secondDeriv_le n hx
  exact h0.continuousOn (Frequently.of_forall fun t =>
    (continuous_finsetSum _ fun n _ => (ShellField.secondDeriv (omega n)).continuous).continuousOn)

/-- Almost surely the recentred stream is differentiable with differentiable gradient, whose
derivative is the series of shell second derivatives. -/
theorem fieldReg_ae_hasFDerivAt_fullStreamDeriv {P : ProbabilityMeasure (ShellSeq d)}
    (hJ3 : ShellLawJ3 d P) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure, ∀ x : Vec d,
      HasFDerivAt (fullStreamDeriv omega) (fieldReg_secondSeries omega x) x := by
  filter_upwards [ae_forall_summable_shellDerivLinftyNorm_originCube hJ3,
    fieldReg_ae_summable_scs hJ3] with omega h1 h2 x
  obtain ⟨i, hi⟩ := exists_openCubeSet_superset (Bornology.isBounded_singleton (x := x))
  exact fieldReg_hasFDerivAt_fullStreamDeriv (h1 i) (h2 i) (hi rfl)

theorem fieldReg_ae_continuous_secondSeries {P : ProbabilityMeasure (ShellSeq d)}
    (hJ3 : ShellLawJ3 d P) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure, Continuous (fieldReg_secondSeries omega) := by
  filter_upwards [fieldReg_ae_summable_scs hJ3] with omega h2
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨i, hi⟩ := exists_openCubeSet_superset (Bornology.isBounded_singleton (x := x))
  exact (fieldReg_continuousOn_secondSeries (h2 i)).continuousAt
    ((isOpen_openCubeSet (originCube d (i : ℤ))).mem_nhds (hi rfl))

/-- **Almost surely the recentred stream is `C²`.** -/
theorem fieldReg_ae_contDiff_two_fullStreamRecentered {P : ProbabilityMeasure (ShellSeq d)}
    (hJ3 : ShellLawJ3 d P) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure, ContDiff ℝ 2 (fullStreamRecentered omega) := by
  filter_upwards [fieldReg_ae_hasFDerivAt_fullStreamDeriv hJ3,
    fieldReg_ae_continuous_secondSeries hJ3, ae_hasFDerivAt_fullStreamRecentered hJ3,
    ae_continuous_fullStreamDeriv hJ3] with omega h1 h2 h3 h4
  have hd : ContDiff ℝ 1 (fullStreamDeriv omega) :=
    contDiff_one_iff_hasFDerivAt.mpr ⟨fieldReg_secondSeries omega, h2, h1⟩
  exact (contDiff_succ_iff_hasFDerivAt (n := 1)).mpr ⟨fullStreamDeriv omega, hd, h3⟩

/-! ## `C^{1,1}_loc` and the Hölder corollary -/

/-- The gradient is Lipschitz on every natural open cube on which both series are summable. -/
theorem fieldReg_lipschitz_on_cube {omega : ShellSeq d} {i : ℕ}
    (hsum : Summable fun k : ℕ =>
      shellDerivLinftyNorm (openCubeSet (originCube d (i : ℤ))) (omega k))
    (hs2 : Summable fun n : ℕ => (d : ℝ) * ShellField.shellCubeSecondDerivNorm i (omega n))
    {x y : Vec d} (hx : x ∈ openCubeSet (originCube d (i : ℤ)))
    (hy : y ∈ openCubeSet (originCube d (i : ℤ))) :
    ‖fullStreamDeriv omega x - fullStreamDeriv omega y‖ ≤
      (∑' n : ℕ, (d : ℝ) * ShellField.shellCubeSecondDerivNorm i (omega n)) * ‖x - y‖ := by
  have h := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fullStreamDeriv omega) (f' := fieldReg_secondSeries omega)
    (s := openCubeSet (originCube d (i : ℤ)))
    (C := ∑' n : ℕ, (d : ℝ) * ShellField.shellCubeSecondDerivNorm i (omega n))
    (fun z hz => (fieldReg_hasFDerivAt_fullStreamDeriv hsum hs2 hz).hasFDerivWithinAt)
    (fun z hz => fieldReg_norm_secondSeries_le hs2 hz)
    (convex_openCubeSet (originCube d (i : ℤ))) hy hx
  exact h

/-- **Almost surely the recentred stream is `C^{1,1}_loc`**: it is `C²`, and on every ball
the derivative is Lipschitz. -/
theorem fieldReg_ae_c11loc_fullStreamRecentered {P : ProbabilityMeasure (ShellSeq d)}
    (hJ3 : ShellLawJ3 d P) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure,
      ContDiff ℝ 2 (fullStreamRecentered omega) ∧
      ∀ R : ℝ, ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ Metric.ball (0 : Vec d) R,
        ∀ y ∈ Metric.ball (0 : Vec d) R,
          ‖fderiv ℝ (fullStreamRecentered omega) x - fderiv ℝ (fullStreamRecentered omega) y‖ ≤
            L * ‖x - y‖ := by
  filter_upwards [ae_forall_summable_shellDerivLinftyNorm_originCube hJ3,
    fieldReg_ae_summable_scs hJ3, ae_fderiv_fullStreamRecentered hJ3,
    fieldReg_ae_contDiff_two_fullStreamRecentered hJ3] with omega h1 h2 h3 h4
  refine ⟨h4, fun R => ?_⟩
  obtain ⟨i, hi⟩ := exists_openCubeSet_superset (Metric.isBounded_ball (x := (0 : Vec d)) (r := R))
  refine ⟨∑' n : ℕ, (d : ℝ) * ShellField.shellCubeSecondDerivNorm i (omega n),
    tsum_nonneg fun n => mul_nonneg (Nat.cast_nonneg d)
      (ShellField.shellCubeSecondDerivNorm_nonneg i _), fun x hx y hy => ?_⟩
  rw [h3]
  exact fieldReg_lipschitz_on_cube (h1 i) (h2 i) (hi hx) (hi hy)

/-! ## Satisfiability witnesses -/

example :
    ∀ᵐ omega : ShellSeq d ∂(SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw d).toMeasure,
      ContDiff ℝ 2 (fullStreamRecentered omega) :=
  fieldReg_ae_contDiff_two_fullStreamRecentered
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ3_diracZeroLaw

example :
    ∀ᵐ omega : ShellSeq d ∂(SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw d).toMeasure,
      ContDiff ℝ 2 (fullStreamRecentered omega) ∧
      ∀ R : ℝ, ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ Metric.ball (0 : Vec d) R,
        ∀ y ∈ Metric.ball (0 : Vec d) R,
          ‖fderiv ℝ (fullStreamRecentered omega) x - fderiv ℝ (fullStreamRecentered omega) y‖ ≤
            L * ‖x - y‖ :=
  fieldReg_ae_c11loc_fullStreamRecentered
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ3_diracZeroLaw

end

end SuperdiffusionCLT.Section8
