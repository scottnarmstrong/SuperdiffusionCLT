/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.DeepCrudeEllipticity
public import SuperdiffusionCLT.Section2.Carriers.CenteredStreamField
public import SuperdiffusionCLT.Section2.Estimates.Stream.ShellValueLargeCube
public import SuperdiffusionCLT.Section2.Estimates.Stream.ShellDerivTailGauge
public import SuperdiffusionCLT.Section2.Cutoff.DerivativeSummabilityAllScales
public import Homogenization.Sobolev.Fractional.GagliardoLeBesov
public import Homogenization.Book.Ch05.Theorems.Section57.HomogenizationErrorControl

/-!
# srootD4: the deep-scale response bound and the uniform stream envelope

Two deterministic ingredients for the deep-scale crude bound on the squared response of the
centered, shifted cutoff field `srootE_field` against the scalar comparator `σ • 1`:

* the response bound: if `a` is `(nu, Lam)`-elliptic on `cu_n`, then at every scale `k ≤ n` the
  squared scale response is at most `2 nu⁻¹ (Lam² σ⁻¹ + σ)`, through the half-sum identity of
  `BlockJ` and the plain upper bound of `ResponseJ`;
* the uniform envelope: every entry of `srootE_field` on `cu_n`, for every cutoff `L`, is bounded
  by `1 + srootD4_T m ω`, a measurable random variable built from the large-cube value envelopes
  of the shells `0, …, m + 1` and the derivative tail gauge of the shells beyond `m + 1`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

open Homogenization MeasureTheory
open Homogenization.Book.Ch02 (matrixOperatorNorm matrixOperatorNorm_nonneg abs_entry_le_matrixOperatorNorm)
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Assumptions.ShellField
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Carriers
open SuperdiffusionCLT.Section2.Estimates.Stream
open scoped Matrix.Norms.Elementwise

section Response

variable {d : ℕ} [NeZero d]

theorem srootD4_constantSqrt_scalar {σ : ℝ} (hσ : 0 < σ) :
    Homogenization.constantFullBlockMatrixSqrt (σ • (1 : Mat d)) =
      Matrix.diagonal (Homogenization.Book.Ch05.Section56.scalarFullBlockSqrtDiag (d := d) σ σ) :=
  Homogenization.Book.Ch05.Section57.constantFullBlockMatrixSqrt_scalarMatrix_eq_scalarFullBlockSqrt hσ

theorem srootD4_constantInvSqrt_scalar {σ : ℝ} (hσ : 0 < σ) :
    Homogenization.constantFullBlockMatrixInvSqrt (σ • (1 : Mat d)) =
      Matrix.diagonal (Homogenization.Book.Ch04.scalarFullBlockInvSqrtDiag (d := d) σ σ) :=
  Homogenization.Book.Ch05.Section57.constantFullBlockMatrixInvSqrt_scalarMatrix_eq_scalarFullBlockInvSqrt hσ

omit [NeZero d] in
theorem srootD4_vecNormSq_sub_le (x y : Vec d) :
    vecNormSq (x - y) ≤ 2 * (vecNormSq x + vecNormSq y) := by
  unfold vecNormSq vecDot
  have : ∀ i : Fin d, (x - y) i * (x - y) i ≤ 2 * (x i * x i + y i * y i) := by
    intro i
    simp only [Pi.sub_apply]
    nlinarith only [sq_nonneg (x i + y i)]
  calc ∑ i, (x - y) i * (x - y) i ≤ ∑ i, 2 * (x i * x i + y i * y i) :=
        Finset.sum_le_sum fun i _ => this i
    _ = 2 * (∑ i, x i * x i + ∑ i, y i * y i) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]

omit [NeZero d] in
theorem srootD4_vecNormSq_add_le (x y : Vec d) :
    vecNormSq (x + y) ≤ 2 * (vecNormSq x + vecNormSq y) := by
  unfold vecNormSq vecDot
  have : ∀ i : Fin d, (x + y) i * (x + y) i ≤ 2 * (x i * x i + y i * y i) := by
    intro i
    simp only [Pi.add_apply]
    nlinarith only [sq_nonneg (x i - y i)]
  calc ∑ i, (x + y) i * (x + y) i ≤ ∑ i, 2 * (x i * x i + y i * y i) :=
        Finset.sum_le_sum fun i _ => this i
    _ = 2 * (∑ i, x i * x i + ∑ i, y i * y i) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]

omit [NeZero d] in
/-- Norms of the two test-vector halves. -/
theorem srootD4_probe_norms {σ : ℝ} (hσ : 0 < σ) (e : FullBlockVec d)
    (he : fullBlockVecNormSq e = 1) :
    let p : Vec d := fun i => (Real.sqrt σ)⁻¹ * e (Sum.inl i)
    let q : Vec d := fun i => Real.sqrt σ * e (Sum.inr i)
    let qS : Vec d := fun i => Real.sqrt σ * e (Sum.inl i)
    let pS : Vec d := fun i => (Real.sqrt σ)⁻¹ * e (Sum.inr i)
    vecNormSq p + vecNormSq pS = σ⁻¹ ∧ vecNormSq q + vecNormSq qS = σ := by
  intro p q qS pS
  have hsum : (∑ i : Fin d, e (Sum.inl i) ^ 2) + (∑ i : Fin d, e (Sum.inr i) ^ 2) = 1 := by
    have h := he
    unfold fullBlockVecNormSq at h
    rw [Fintype.sum_sum_type] at h
    exact h
  have hs : Real.sqrt σ ^ 2 = σ := Real.sq_sqrt hσ.le
  have hs0 : Real.sqrt σ ≠ 0 := (Real.sqrt_pos.2 hσ).ne'
  have h1 : ∀ (c : ℝ) (f : Fin d → ℝ), vecNormSq (fun i => c * f i) = c ^ 2 * ∑ i, f i ^ 2 := by
    intro c f
    unfold vecNormSq vecDot
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  constructor
  · show vecNormSq (fun i => (Real.sqrt σ)⁻¹ * e (Sum.inl i)) +
      vecNormSq (fun i => (Real.sqrt σ)⁻¹ * e (Sum.inr i)) = σ⁻¹
    rw [h1, h1, ← mul_add, hsum, inv_pow, hs, mul_one]
  · show vecNormSq (fun i => Real.sqrt σ * e (Sum.inr i)) +
      vecNormSq (fun i => Real.sqrt σ * e (Sum.inl i)) = σ
    rw [h1, h1, ← mul_add, add_comm, hsum, hs, mul_one]

/-- One normalized test vector is bounded by `2 nu⁻¹ (Lam² σ⁻¹ + σ)`. -/
theorem srootD4_blockJ_probe_le {nu Lam σ : ℝ} (hnu : 0 < nu) (hσ : 0 < σ)
    {a : CoeffField d} (R : TriadicCube d)
    (hEll : IsEllipticFieldOn nu Lam (cubeSet R) a) (e : FullBlockVec d)
    (he : fullBlockVecNormSq e = 1) :
    BlockJ (cubeSet R)
        (ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixInvSqrt (σ • (1 : Mat d))) e))
        (ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixSqrt (σ • (1 : Mat d))) e)) a ≤
      2 * nu⁻¹ * (Lam ^ 2 * σ⁻¹ + σ) := by
  let := isFiniteMeasureVolumeMeasureOnCubeSet R
  have hvol : (MeasureTheory.volume (cubeSet R)).toReal ≠ 0 := by
    rw [volume_cubeSet_toReal]
    exact (cubeVolume_pos R).ne'
  rw [srootD4_constantSqrt_scalar hσ, srootD4_constantInvSqrt_scalar hσ]
  set p : Vec d := fun i => (Real.sqrt σ)⁻¹ * e (Sum.inl i) with hp
  set q : Vec d := fun i => Real.sqrt σ * e (Sum.inr i) with hq
  set qS : Vec d := fun i => Real.sqrt σ * e (Sum.inl i) with hqS
  set pS : Vec d := fun i => (Real.sqrt σ)⁻¹ * e (Sum.inr i) with hpS
  have hP : ofFullBlockVec (Matrix.mulVec (Matrix.diagonal
      (Homogenization.Book.Ch04.scalarFullBlockInvSqrtDiag (d := d) σ σ)) e) = (p, q) := by
    refine Prod.ext ?_ ?_ <;> funext i <;>
      simp [ofFullBlockVec, Matrix.mulVec_diagonal, Homogenization.Book.Ch04.scalarFullBlockInvSqrtDiag,
        hp, hq]
  have hQ : ofFullBlockVec (Matrix.mulVec (Matrix.diagonal
      (Homogenization.Book.Ch05.Section56.scalarFullBlockSqrtDiag (d := d) σ σ)) e) = (qS, pS) := by
    refine Prod.ext ?_ ?_ <;> funext i <;>
      simp [ofFullBlockVec, Matrix.mulVec_diagonal,
        Homogenization.Book.Ch05.Section56.scalarFullBlockSqrtDiag, hqS, hpS]
  rw [hP, hQ]
  rw [blockJ_eq_half_responseJ_adjoint_sum_of_isEllipticFieldOn (a := a)
    (measurableSet_cubeSet R) hEll hvol]
  have hEllA := isEllipticFieldOn_adjointCoeffField hEll
  have hb1 := responseJ_le_plainUpperBound_of_isEllipticFieldOn hEll hvol (p - pS) (qS - q)
  have hb2 := responseJ_le_plainUpperBound_of_isEllipticFieldOn hEllA hvol (pS + p) (qS + q)
  obtain ⟨hn1, hn2⟩ := srootD4_probe_norms hσ e he
  have hLam0 : 0 ≤ Lam ^ 2 := sq_nonneg _
  have hninv : 0 ≤ nu⁻¹ := inv_nonneg.2 hnu.le
  have hs1 : vecNormSq (p - pS) ≤ 2 * σ⁻¹ := by
    have := srootD4_vecNormSq_sub_le p pS
    linarith only [this, hn1]
  have hs2 : vecNormSq (pS + p) ≤ 2 * σ⁻¹ := by
    have := srootD4_vecNormSq_add_le pS p
    linarith only [this, hn1, add_comm (vecNormSq pS) (vecNormSq p)]
  have hs3 : vecNormSq (qS - q) ≤ 2 * σ := by
    have := srootD4_vecNormSq_sub_le qS q
    linarith only [this, hn2, add_comm (vecNormSq q) (vecNormSq qS)]
  have hs4 : vecNormSq (qS + q) ≤ 2 * σ := by
    have := srootD4_vecNormSq_add_le qS q
    linarith only [this, hn2, add_comm (vecNormSq q) (vecNormSq qS)]
  have hc1 : Lam ^ 2 * vecNormSq (p - pS) + vecNormSq (qS - q) ≤ 2 * (Lam ^ 2 * σ⁻¹ + σ) := by
    have := mul_le_mul_of_nonneg_left hs1 hLam0
    linarith only [this, hs3]
  have hc2 : Lam ^ 2 * vecNormSq (pS + p) + vecNormSq (qS + q) ≤ 2 * (Lam ^ 2 * σ⁻¹ + σ) := by
    have := mul_le_mul_of_nonneg_left hs2 hLam0
    linarith only [this, hs4]
  have h1 := mul_le_mul_of_nonneg_left hc1 hninv
  have h2 := mul_le_mul_of_nonneg_left hc2 hninv
  have h1' := hb1.trans h1
  have h2' := hb2.trans h2
  have e1 : nu⁻¹ * (2 * (Lam ^ 2 * σ⁻¹ + σ)) = 2 * nu⁻¹ * (Lam ^ 2 * σ⁻¹ + σ) := by ring
  linarith only [h1', h2', e1]

omit [NeZero d] in
theorem srootD4_rpow_half_sq_le {F B : ℝ} (hF : F ≤ B) (hB : 0 ≤ B) :
    Real.rpow (Real.rpow F (1 / 2)) 2 ≤ B := by
  by_cases h0 : 0 ≤ F
  · show (F ^ (1 / 2 : ℝ)) ^ (2 : ℝ) ≤ B
    rw [← Real.rpow_mul h0]
    norm_num
    exact hF
  · have hneg : F < 0 := lt_of_not_ge h0
    have : Real.rpow F (1 / 2) = 0 := by
      show F ^ (1 / 2 : ℝ) = 0
      rw [Real.rpow_def_of_neg hneg]
      have : Real.cos ((1 / 2 : ℝ) * Real.pi) = 0 := by
        rw [show (1 / 2 : ℝ) * Real.pi = Real.pi / 2 by ring]
        exact Real.cos_pi_div_two
      rw [this, mul_zero]
    rw [this]
    show (0 : ℝ) ^ (2 : ℝ) ≤ B
    rw [Real.zero_rpow (by norm_num)]
    exact hB

/-- **The response bound at one scale.** If `a` is `(nu, Lam)`-elliptic on `cu_n`, the
squared scale response against the scalar comparator `σ • 1` at any scale `k ≤ n` is at most
`2 nu⁻¹ (Lam² σ⁻¹ + σ)`. -/
theorem srootD4_scaleResponse_sq_le {nu Lam σ : ℝ} (hnu : 0 < nu) (hσ : 0 < σ)
    {a : CoeffField d} (n k : ℤ) (hk : k ≤ n)
    (hEll : IsEllipticFieldOn nu Lam (cubeSet (originCube d n)) a) :
    Real.rpow (scaleResponseAtScale (originCube d n) k MultiscaleExponent.infinity a
        (σ • (1 : Mat d))) 2 ≤ 2 * nu⁻¹ * (Lam ^ 2 * σ⁻¹ + σ) := by
  have hB : 0 ≤ 2 * nu⁻¹ * (Lam ^ 2 * σ⁻¹ + σ) := by
    have := inv_nonneg.2 hnu.le
    have := inv_nonneg.2 hσ.le
    positivity
  have hmax : ∀ R ∈ descendantsAtScale (originCube d n) k,
      normalizedBlockResponseMax R a (σ • (1 : Mat d)) ≤ 2 * nu⁻¹ * (Lam ^ 2 * σ⁻¹ + σ) := by
    intro R hR
    have hEllR : IsEllipticFieldOn nu Lam (cubeSet R) a :=
      hEll.mono (measurableSet_cubeSet R) (cubeSet_subset_of_mem_descendantsAtScale hk hR)
    unfold normalizedBlockResponseMax
    refine Real.sSup_le ?_ hB
    rintro x ⟨e, he, rfl⟩
    exact srootD4_blockJ_probe_le hnu hσ R hEllR e he
  have hF : maxDescendantNormalizedBlockResponseAtScale (originCube d n) k a (σ • (1 : Mat d)) ≤
      2 * nu⁻¹ * (Lam ^ 2 * σ⁻¹ + σ) := by
    unfold maxDescendantNormalizedBlockResponseAtScale finsetSsup
    refine Real.sSup_le ?_ hB
    rintro x ⟨R, hR, rfl⟩
    exact hmax R hR
  exact srootD4_rpow_half_sq_le hF hB

end Response

section Envelope

variable {d : ℕ}

theorem srootD4_cubeSet_subset_openCube_succ (m : ℕ) :
    cubeSet (originCube d (m : ℤ)) ⊆ openCubeSet (originCube d ((m + 1 : ℕ) : ℤ)) := by
  intro x hx
  rw [mem_cubeSet_originCube_iff] at hx
  rw [mem_openCubeSet_originCube_iff]
  intro i
  obtain ⟨h1, h2⟩ := hx i
  have h3 : (3 : ℝ) ^ ((m + 1 : ℕ) : ℤ) = 3 * (3 : ℝ) ^ (m : ℤ) := by
    rw [zpow_natCast, zpow_natCast, pow_succ]; ring
  have hp : 0 < (3 : ℝ) ^ (m : ℤ) := zpow_pos (by norm_num) _
  rw [h3]
  constructor <;> nlinarith only [h1, h2, hp]

theorem srootD4_volume_cubeSet_ne_zero (Q : TriadicCube d) :
    volume (cubeSet Q) ≠ 0 := by
  have hpos : 0 < (volume (cubeSet Q)).toReal := by
    rw [volume_cubeSet_toReal]; exact cubeVolume_pos Q
  exact (ENNReal.toReal_pos_iff.1 hpos).1.ne'

theorem srootD4_norm_le_matrixOperatorNorm (A : Mat d) :
    ‖A‖ ≤ matrixOperatorNorm A := by
  rw [Matrix.norm_le_iff (matrixOperatorNorm_nonneg A)]
  intro i l
  simpa only [Real.norm_eq_abs] using abs_entry_le_matrixOperatorNorm A i l

/-- Early shells: the centered term is bounded by twice the large-cube value envelope. -/
theorem srootD4_centeredShellTerm_early_le (omega : ShellSeq d) (m k : ℕ) (hk : k ≤ m + 1)
    {y : Vec d} (hy : y ∈ cubeSet (originCube d (m : ℤ))) :
    ‖centeredShellTerm omega (cubeSet (originCube d (m : ℤ))) k y‖ ≤
      2 * shellValueLargeCubeSupBound k (m + 1) omega := by
  have hsub : cubeSet (originCube d (m : ℤ)) ⊆ cubeSet (originCube d ((m + 1 : ℕ) : ℤ)) :=
    (srootD4_cubeSet_subset_openCube_succ m).trans (openCubeSet_subset_cubeSet _)
  have hV : ∀ z ∈ cubeSet (originCube d (m : ℤ)),
      ‖shellReg omega k z‖ ≤ shellValueLargeCubeSupBound k (m + 1) omega := by
    intro z hz
    have h1 := matrixOperatorNorm_shellValue_le_shellValueLargeCubeSupBound omega hk (hsub hz)
    have h2 : shellReg omega k z = (omega k) z := by
      simp only [shellReg, ShellField.forgetShell_apply]
    rw [h2]
    exact (srootD4_norm_le_matrixOperatorNorm _).trans h1
  unfold centeredShellTerm
  refine norm_sub_volumeAverageMat_le (isBounded_cubeSet _) (srootD4_volume_cubeSet_ne_zero _)
    (fun i l => integrableOn_entry_of_isBounded (shellReg omega k) (isBounded_cubeSet _) i l) ?_
  intro z hz
  calc ‖shellReg omega k y - shellReg omega k z‖ ≤ ‖shellReg omega k y‖ + ‖shellReg omega k z‖ :=
        norm_sub_le _ _
    _ ≤ shellValueLargeCubeSupBound k (m + 1) omega + shellValueLargeCubeSupBound k (m + 1) omega :=
        add_le_add (hV y hy) (hV z hz)
    _ = 2 * shellValueLargeCubeSupBound k (m + 1) omega := by ring

/-- Late shells: the centered term is bounded by the derivative norm on the next cube. -/
theorem srootD4_centeredShellTerm_late_le (omega : ShellSeq d) (m k : ℕ)
    {y : Vec d} (hy : y ∈ cubeSet (originCube d (m : ℤ))) :
    ‖centeredShellTerm omega (cubeSet (originCube d (m : ℤ))) k y‖ ≤
      Real.sqrt d * (3 : ℝ) ^ m *
        shellDerivLinftyNorm (openCubeSet (originCube d ((m + 1 : ℕ) : ℤ))) (omega k) := by
  have hsub := srootD4_cubeSet_subset_openCube_succ (d := d) m
  have hD0 := shellDerivLinftyNorm_nonneg (openCubeSet (originCube d ((m + 1 : ℕ) : ℤ))) (omega k)
  unfold centeredShellTerm
  refine norm_sub_volumeAverageMat_le (isBounded_cubeSet _) (srootD4_volume_cubeSet_ne_zero _)
    (fun i l => integrableOn_entry_of_isBounded (shellReg omega k) (isBounded_cubeSet _) i l) ?_
  intro z hz
  have h1 := norm_shell_sub_le (isBounded_openCubeSet_originCube (d := d) ((m + 1 : ℕ) : ℤ))
    (Homogenization.convex_openCubeSet (originCube d ((m + 1 : ℕ) : ℤ))) (omega k) (hsub hz) (hsub hy)
  have h2 : ‖y - z‖ ≤ (3 : ℝ) ^ m := by
    rw [← dist_eq_norm]
    have := Homogenization.Gagliardo.dist_le_cubeScaleFactor_of_mem_cubeSet hy hz
    have e : cubeScaleFactor (originCube d (m : ℤ)) = (3 : ℝ) ^ m := by
      simp [cubeScaleFactor, originCube]
    rwa [e] at this
  have h3 : shellReg omega k y - shellReg omega k z = (omega k) y - (omega k) z := by
    simp only [shellReg, ShellField.forgetShell_apply]
  rw [h3]
  calc ‖(omega k) y - (omega k) z‖ ≤
        Real.sqrt d * shellDerivLinftyNorm (openCubeSet (originCube d ((m + 1 : ℕ) : ℤ))) (omega k) *
          ‖y - z‖ := by
        have := h1
        rwa [show (omega k) y - (omega k) z = (omega k) y - (omega k) z from rfl] at this
    _ ≤ Real.sqrt d * shellDerivLinftyNorm (openCubeSet (originCube d ((m + 1 : ℕ) : ℤ))) (omega k) *
          (3 : ℝ) ^ m :=
        mul_le_mul_of_nonneg_left h2 (mul_nonneg (Real.sqrt_nonneg _) hD0)
    _ = Real.sqrt d * (3 : ℝ) ^ m *
        shellDerivLinftyNorm (openCubeSet (originCube d ((m + 1 : ℕ) : ℤ))) (omega k) := by ring

/-- The random envelope of the centered stream matrix on `cu_m`, uniform in the cutoff. -/
noncomputable def srootD4_T (m : ℕ) (omega : ShellSeq d) : ℝ :=
  2 * ∑ l ∈ Finset.range (m + 2), shellValueLargeCubeSupBound l (m + 1) omega +
    Real.sqrt d * shellDerivTailGauge (m + 1) omega

theorem srootD4_norm_centeredStreamCutoff_le (omega : ShellSeq d) (m : ℕ)
    (hsum : Summable fun k : ℕ =>
      shellDerivLinftyNorm (openCubeSet (originCube d ((m + 1 : ℕ) : ℤ))) (omega k))
    (L : ℕ) {y : Vec d} (hy : y ∈ cubeSet (originCube d (m : ℤ))) :
    ‖centeredStreamCutoff omega L (cubeSet (originCube d (m : ℤ))) y‖ ≤ srootD4_T m omega := by
  set U := cubeSet (originCube d (m : ℤ)) with hU
  set c : ℝ := Real.sqrt d * (3 : ℝ) ^ m with hc
  set D : ℕ → ℝ := fun k =>
    shellDerivLinftyNorm (openCubeSet (originCube d ((m + 1 : ℕ) : ℤ))) (omega k) with hD
  set V : ℕ → ℝ := fun k => shellValueLargeCubeSupBound k (m + 1) omega with hV
  have hc0 : 0 ≤ c := by positivity
  have hD0 : ∀ k, 0 ≤ D k := fun k => shellDerivLinftyNorm_nonneg _ _
  have hV0 : ∀ k, 0 ≤ V k := fun k => shellValueLargeCubeSupBound_nonneg _ _ _
  set u : ℕ → ℝ := fun k => if k ≤ m + 1 then 2 * V k else 0 with hu
  set w : ℕ → ℝ := fun k => if k ≤ m + 1 then 0 else c * D k with hw
  have hu0 : ∀ k, 0 ≤ u k := fun k => by
    simp only [hu]; split_ifs <;> [exact mul_nonneg (by norm_num) (hV0 k); exact le_rfl]
  have hw0 : ∀ k, 0 ≤ w k := fun k => by
    simp only [hw]; split_ifs <;> [exact le_rfl; exact mul_nonneg hc0 (hD0 k)]
  have hterm : ∀ k, ‖centeredShellTerm omega U k y‖ ≤ u k + w k := by
    intro k
    by_cases hk : k ≤ m + 1
    · have e : u k + w k = 2 * V k := by simp [hu, hw, hk]
      rw [e]
      exact srootD4_centeredShellTerm_early_le omega m k hk hy
    · have e : u k + w k = c * D k := by simp [hu, hw, hk]
      rw [e]
      exact srootD4_centeredShellTerm_late_le omega m k hy
  have hbd : Bornology.IsBounded U := isBounded_cubeSet _
  rw [← sum_centeredShellTerm_eq_centeredStreamCutoff hbd omega L y]
  have h1 : ‖∑ k ∈ Finset.range (L + 1), centeredShellTerm omega U k y‖ ≤
      ∑ k ∈ Finset.range (L + 1), (u k + w k) :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => hterm k)
  rw [Finset.sum_add_distrib] at h1
  have hu_sum : ∑ k ∈ Finset.range (L + 1), u k ≤ 2 * ∑ l ∈ Finset.range (m + 2), V l := by
    have e1 : ∑ k ∈ Finset.range (L + 1), u k =
        ∑ k ∈ (Finset.range (L + 1)).filter (· ≤ m + 1), 2 * V k := by
      rw [Finset.sum_filter]
    rw [e1, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => hV0 k)
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
    omega
  have hDsum : Summable fun j : ℕ => D (j + (m + 2)) :=
    (summable_nat_add_iff (m + 2)).2 hsum
  have hwshift : ∀ j : ℕ, w (j + (m + 2)) = c * D (j + (m + 2)) := by
    intro j
    have h : ¬ (j + (m + 2) ≤ m + 1) := by omega
    simp [hw, h]
  have hwsum : Summable w := by
    rw [← summable_nat_add_iff (m + 2)]
    have : (fun j : ℕ => w (j + (m + 2))) = fun j => c * D (j + (m + 2)) := funext hwshift
    rw [this]
    exact hDsum.mul_left c
  have hw_sum : ∑ k ∈ Finset.range (L + 1), w k ≤ c * ∑' j : ℕ, D (j + (m + 2)) := by
    refine (hwsum.sum_le_tsum _ (fun k _ => hw0 k)).trans ?_
    have hsplit := hwsum.sum_add_tsum_nat_add (m + 2)
    have hz : ∑ i ∈ Finset.range (m + 2), w i = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      have h : i ≤ m + 1 := by simp only [Finset.mem_range] at hi; omega
      simp [hw, h]
    have hshift : (fun j : ℕ => w (j + (m + 2))) = fun j => c * D (j + (m + 2)) := funext hwshift
    rw [hz, zero_add, hshift, tsum_mul_left] at hsplit
    exact hsplit.ge
  have hgauge : c * ∑' j : ℕ, D (j + (m + 2)) ≤ Real.sqrt d * shellDerivTailGauge (m + 1) omega := by
    rw [shellDerivTailGauge_eq_tsum]
    have hts : ∑' j : ℕ, D (j + (m + 2)) =
        ∑' k : ℕ, shellDerivLinftyNorm (openCubeSet (originCube d ((m + 1 : ℕ) : ℤ)))
          (omega (m + 1 + 1 + k)) := by
      refine tsum_congr fun j => ?_
      simp only [hD]
      congr 2
      omega
    rw [hts]
    have hnn : 0 ≤ ∑' k : ℕ, shellDerivLinftyNorm (openCubeSet (originCube d ((m + 1 : ℕ) : ℤ)))
          (omega (m + 1 + 1 + k)) := tsum_nonneg fun k => shellDerivLinftyNorm_nonneg _ _
    have h3 : (3 : ℝ) ^ m ≤ (3 : ℝ) ^ (m + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    rw [hc]
    have := mul_le_mul_of_nonneg_right h3 hnn
    have hsd := Real.sqrt_nonneg (d : ℝ)
    nlinarith only [this, hsd]
  unfold srootD4_T
  linarith only [h1, hu_sum, hw_sum, hgauge]

end Envelope

section Field

variable {d : ℕ} [NeZero d]

/-- Every entry of the shifted centered field on `cu_n` is at most `1 + T`. -/
theorem srootD4_entry_le (nu : ℝ) (hnu0 : 0 ≤ nu) (hnu1 : nu ≤ 1) (omega : ShellSeq d)
    (L m n : ℕ) (k : Fin d → ℤ)
    (hk : (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
        cubeSet (originCube d (n : ℤ)) ⊆ cubeSet (originCube d (m : ℤ)))
    (hsum : Summable fun j : ℕ =>
      shellDerivLinftyNorm (openCubeSet (originCube d ((m + 1 : ℕ) : ℤ))) (omega j))
    {x : Vec d} (hx : x ∈ cubeSet (originCube d (n : ℤ))) (i j : Fin d) :
    |srootE_field nu omega L m n k x i j| ≤ 1 + srootD4_T m omega := by
  have hy : ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ∈ cubeSet (originCube d (m : ℤ)) :=
    hk ⟨x, hx, rfl⟩
  have h1 := srootD4_norm_centeredStreamCutoff_le omega m hsum L hy
  have hfield : srootE_field nu omega L m n k x =
      nu • (1 : Mat d) + centeredStreamCutoff omega L (cubeSet (originCube d (m : ℤ)))
        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) := by
    rw [srootD2_srootE_field_eq, centeredStreamCutoff_apply]
  rw [hfield, Matrix.add_apply]
  have h2 : |(centeredStreamCutoff omega L (cubeSet (originCube d (m : ℤ)))
      ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)) i j| ≤ srootD4_T m omega := by
    have := Matrix.norm_entry_le_entrywise_sup_norm
      (centeredStreamCutoff omega L (cubeSet (originCube d (m : ℤ)))
        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)) (i := i) (j := j)
    rw [Real.norm_eq_abs] at this
    exact this.trans h1
  have h3 : |(nu • (1 : Mat d)) i j| ≤ nu := by
    by_cases hij : i = j
    · subst hij; simp [abs_of_nonneg hnu0]
    · simp [hij, hnu0]
  calc |(nu • (1 : Mat d)) i j + (centeredStreamCutoff omega L (cubeSet (originCube d (m : ℤ)))
        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)) i j|
      ≤ |(nu • (1 : Mat d)) i j| + |(centeredStreamCutoff omega L (cubeSet (originCube d (m : ℤ)))
        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)) i j| := abs_add_le _ _
    _ ≤ 1 + srootD4_T m omega := by linarith only [h2, h3, hnu1]

/-- **Explicit-bound ellipticity.** -/
theorem srootD4_isEllipticFieldOn_of_entryBound (nu : ℝ) (hnu : 0 < nu)
    (omega : ShellSeq d) (L m n : ℕ) (k : Fin d → ℤ) {C : ℝ}
    (hC : ∀ x ∈ cubeSet (originCube d (n : ℤ)), ∀ i j : Fin d,
      |srootE_field nu omega L m n k x i j| ≤ C) :
    IsEllipticFieldOn nu (((d : ℝ) * (d : ℝ) * C ^ 2 + nu ^ 2) / nu)
      (cubeSet (originCube d (n : ℤ))) (srootE_field nu omega L m n k) := by
  classical
  refine ⟨?_, fun x hx => ?_⟩
  · refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
    have hcontij : Continuous (fun x : Vec d => srootE_field nu omega L m n k x i j) :=
      (continuous_apply j).comp ((continuous_apply i).comp
        (srootD2_continuous_srootE_field nu omega L m n k))
    exact hcontij.measurable.ite (measurableSet_cubeSet (originCube d (n : ℤ))) measurable_const
  · exact SuperdiffusionCLT.Section2.CoarseGraining.isEllipticMatrix_of_symmPart_eq_smul_one
      hnu (srootD2_symmPart_srootE_field nu omega L m n k x) (hC x hx)

/-- The deterministic response majorant `2 nu⁻¹ (Lam² σ⁻¹ + σ)` evaluated at the explicit
ellipticity constant `Lam = (d² (1 + T)² + nu²) / nu`. -/
noncomputable def srootD4_R (d : ℕ) (nu σ T : ℝ) : ℝ :=
  2 * nu⁻¹ * ((((d : ℝ) * (d : ℝ) * (1 + T) ^ 2 + nu ^ 2) / nu) ^ 2 * σ⁻¹ + σ)

/-- **The crude response bound, deterministic form.** On the event that the shell derivative
series on `cu_{m+1}` is summable, the squared deep-scale response of `srootE_field` against
`σ • 1` is at most `srootD4_R d nu σ (srootD4_T m ω)`, for every cutoff `L` and every scale
`n - j`. -/
theorem srootD4_scaleResponse_sq_le_envelope (nu σ : ℝ) (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (hσ : 0 < σ) (omega : ShellSeq d) (L m n : ℕ) (k : Fin d → ℤ)
    (hk : (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
        cubeSet (originCube d (n : ℤ)) ⊆ cubeSet (originCube d (m : ℤ)))
    (hsum : Summable fun j : ℕ =>
      shellDerivLinftyNorm (openCubeSet (originCube d ((m + 1 : ℕ) : ℤ))) (omega j))
    (j : ℕ) :
    Real.rpow (scaleResponseAtScale (originCube d (n : ℤ)) ((n : ℤ) - (j : ℤ))
        MultiscaleExponent.infinity (srootE_field nu omega L m n k) (σ • (1 : Mat d))) 2 ≤
      srootD4_R d nu σ (srootD4_T m omega) := by
  have hEll := srootD4_isEllipticFieldOn_of_entryBound nu hnu omega L m n k
    (C := 1 + srootD4_T m omega)
    (fun x hx i j => srootD4_entry_le nu hnu.le hnu1 omega L m n k hk hsum hx i j)
  exact srootD4_scaleResponse_sq_le hnu hσ (n : ℤ) ((n : ℤ) - (j : ℤ)) (by omega) hEll

/-! ## Satisfiability witnesses -/

end Field

end SuperdiffusionCLT.Section4.MinimalScales
