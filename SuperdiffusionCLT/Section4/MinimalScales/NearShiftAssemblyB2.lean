/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.NearShiftAssemblyG2
public import SuperdiffusionCLT.Section4.MinimalScales.NearShiftTail
public import SuperdiffusionCLT.Section4.MinimalScales.LimitLocDescendant

/-!
# The far-cutoff comparison on a descendant cube

For a cutoff `L > mm` the centered field `srootE_field nu ω L m n k` on a descendant cube `R` of
`cu_n` is compared with the same field at the cutoff `mm`, through the near-tail comparison
`srootNS_nearTail_J_comparison_shift_sigmaBar` on the translated open cube `U = (R + z)°` and
`V = cu_m`. With `V = cu_m` the shift of the tail field is exactly `h_0 = -(k_mm)_{cu_m}`, so the
reference field is the centered field at level `mm` itself.

* `srootNS_translatedCubeDomain`: the domain `U`;
* `srootNS_translate_openCube_subset_openCube`: `U ⊆ cu_m`;
* `srootNS_caseB_pathwise`: the pathwise bound `Φ^{(L)}_R ≤ Φ^{(mm)}_R + X1 + ‖h_0‖² X2`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

noncomputable section

/-- The translate `z + (R)°` of an open triadic cube, as a Chapter 2 domain. -/
def srootNS_translatedCubeDomain {d : ℕ} (R : Homogenization.TriadicCube d)
    (z : Homogenization.Vec d) : Homogenization.Book.Ch02.Domain d where
  carrier := Homogenization.translateSet z (Homogenization.openCubeSet R)
  isDomain :=
    Homogenization.IsOpenBoundedConvexDomain.translateSet
      (Homogenization.isOpenBoundedConvexDomain_openCubeSet R) z
  nonempty := by
    obtain ⟨x, hx⟩ := Homogenization.Book.Ch02.openCubeSet_nonempty R
    exact ⟨x + z, x, hx, rfl⟩

@[simp] theorem srootNS_translatedCubeDomain_coe {d : ℕ} (R : Homogenization.TriadicCube d)
    (z : Homogenization.Vec d) :
    ((srootNS_translatedCubeDomain R z : Homogenization.Book.Ch02.Domain d) :
        Set (Homogenization.Vec d)) =
      Homogenization.translateSet z (Homogenization.openCubeSet R) :=
  rfl

/-- An open set inside the half-open cube `cu_m` lies in the open cube. -/
theorem srootNS_translate_openCube_subset_openCube {d : ℕ} (R : Homogenization.TriadicCube d)
    (z : Homogenization.Vec d) (m : ℕ)
    (h : (fun x => z + x) '' Homogenization.openCubeSet R ⊆
      Homogenization.cubeSet (Homogenization.originCube d (m : ℤ))) :
    Homogenization.translateSet z (Homogenization.openCubeSet R) ⊆
      Homogenization.openCubeSet (Homogenization.originCube d (m : ℤ)) := by
  have hopen : IsOpen (Homogenization.translateSet z (Homogenization.openCubeSet R)) :=
    (srootNS_translatedCubeDomain R z).isDomain.isOpen
  have hmem : ∀ y ∈ Homogenization.translateSet z (Homogenization.openCubeSet R),
      y ∈ Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)) := by
    intro y hy
    rw [Homogenization.mem_translateSet_iff_sub_mem] at hy
    exact h ⟨y - z, hy, add_sub_cancel z y⟩
  intro x hx i
  obtain ⟨hlo, hhi⟩ := hmem x hx i
  refine ⟨?_, hhi⟩
  by_contra hcon
  have heq : ((((Homogenization.originCube d (m : ℤ)).index i : ℝ) - (1 / 2 : ℝ)) *
      Homogenization.cubeScaleFactor (Homogenization.originCube d (m : ℤ))) = x i :=
    le_antisymm hlo (not_lt.1 hcon)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen x hx
  have hy : (x - (ε / 2) • (Pi.single i 1 : Homogenization.Vec d)) ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro j
    by_cases hj : j = i
    · subst hj
      simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one,
        Real.dist_eq, sub_sub_cancel_left, abs_neg]
      rw [abs_of_pos (by linarith only [hε])]
      linarith only [hε]
    · simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_of_ne hj, smul_zero, sub_zero,
        dist_self]
      exact hε
  obtain ⟨hlo', -⟩ := hmem _ (hball hy) i
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at hlo'
  linarith only [hlo', heq, hε]

/-- `srootE_field` is the translate by `z = 3^{n-3} k` of the centered cutoff field. -/
theorem srootNS_srootE_field_eq_translate {d : ℕ} [NeZero d] (nu : ℝ)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (L m n : ℕ) (k : Fin d → ℤ) :
    srootE_field nu omega L m n k =
      Homogenization.translateCoeffField (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ))
        (SuperdiffusionCLT.Section2.Cutoff.centeredCoefficientCutoff nu omega L
          (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))).toCoeffField := by
  funext x
  unfold srootE_field Homogenization.translateCoeffField
  congr 1
  funext i
  exact add_comm _ _

/-- The centered cutoff field is `a_L + h_0`, `h_0 = -(k_L)_{cu_m}`, as fields on all of space. -/
theorem srootNS_centered_toCoeffField_eq_add_h0 {d : ℕ} [NeZero d] (nu : ℝ)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (L m : ℕ) :
    (SuperdiffusionCLT.Section2.Cutoff.centeredCoefficientCutoff nu omega L
        (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))).toCoeffField =
      fun x => (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField x +
        srootNS_h0 m L omega :=
  SuperdiffusionCLT.Section2.CoarseGraining.centeredCoefficientCutoff_toCoeffField nu omega L _

/-- The average of the stream increment over a bounded set is the difference of the averages. -/
theorem srootNS_volumeAverageMat_finiteShellIncrement_eq {d : ℕ}
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) {mm L : ℕ} (h : mm ≤ L)
    {V : Set (Homogenization.Vec d)} (hV : Bornology.IsBounded V) :
    Homogenization.volumeAverageMat V
        (fun y => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega mm L y) =
      Homogenization.volumeAverageMat V (SuperdiffusionCLT.Frozen.Section2.streamCutoff omega L) -
        Homogenization.volumeAverageMat V
          (SuperdiffusionCLT.Frozen.Section2.streamCutoff omega mm) := by
  ext i j
  have hL := SuperdiffusionCLT.Section2.Cutoff.integrableOn_entry_of_isBounded
    (SuperdiffusionCLT.Frozen.Section2.streamCutoff omega L) hV i j
  have hm := SuperdiffusionCLT.Section2.Cutoff.integrableOn_entry_of_isBounded
    (SuperdiffusionCLT.Frozen.Section2.streamCutoff omega mm) hV i j
  simp only [Homogenization.volumeAverageMat, Homogenization.volumeAverage, Matrix.sub_apply]
  have hfun : ∀ y, SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega mm L y i j =
      SuperdiffusionCLT.Frozen.Section2.streamCutoff omega L y i j -
        SuperdiffusionCLT.Frozen.Section2.streamCutoff omega mm y i j := fun y => by
    rw [SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement_apply_eq_streamCutoff_sub
      omega h y, Matrix.sub_apply]
  simp only [hfun]
  rw [MeasureTheory.integral_sub hL hm, mul_sub]

/-- The average of the stream increment over any set is skew. -/
theorem srootNS_skew_volumeAverage_finiteShellIncrement {d : ℕ}
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (mm L : ℕ)
    (V : Set (Homogenization.Vec d)) :
    Homogenization.matTranspose
        (Homogenization.volumeAverageMat V
          (fun y => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega mm L y)) =
      -Homogenization.volumeAverageMat V
          (fun y => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega mm L y) := by
  have h := SuperdiffusionCLT.Section2.Cutoff.matTranspose_volumeAverageMat V
    (fun y => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega mm L y)
    (fun y i k => congrFun (congrFun
      (SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement_skew omega mm L y) k) i)
  simpa only [Homogenization.matTranspose, Matrix.transpose_neg, neg_neg] using h

/-- The `BlockJ` of the translate of a field on the cube `R` is the doubled response on the
translated open cube. -/
theorem srootNS_BlockJ_translate_eq_doubledResponseJ {d : ℕ} [NeZero d]
    (R : Homogenization.TriadicCube d) (z : Homogenization.Vec d)
    (f : Homogenization.CoeffField d) (U : Homogenization.Book.Ch02.Domain d)
    (hU : (U : Set (Homogenization.Vec d)) =
      Homogenization.translateSet z (Homogenization.openCubeSet R))
    (b : Homogenization.Book.Ch02.CoeffOn U) (hb : b.toCoeffField = f)
    (hEll : Homogenization.IsEllipticFieldOn b.lam b.Lam (U : Set (Homogenization.Vec d))
      b.toCoeffField)
    (P Q : Homogenization.BlockVec d) :
    Homogenization.BlockJ (Homogenization.cubeSet R) P Q (Homogenization.translateCoeffField z f) =
      Homogenization.Book.Ch02.doubledResponseJ U b P Q := by
  subst hb
  rw [Homogenization.BlockJ_cubeSet_eq_openCubeSet_of_triadicCube,
    ← Homogenization.BlockJ_translateSet_eq_translateCoeffField, ← hU]
  exact (Homogenization.Book.Ch02.doubledResponseJ_eq_BlockJ_of_isEllipticFieldOn U b hEll P Q).symm

/-- A test-vector value is at most the normalized block response maximum (the value set is
bounded). -/
theorem srootNS_blockJ_probe_le_normalizedBlockResponseMax {d : ℕ} [NeZero d]
    (Q : Homogenization.TriadicCube d) (a : Homogenization.CoeffField d) {c : ℝ} (hc : 0 < c)
    (hbdd : BddAbove (Homogenization.normalizedBlockResponseValueSet Q a
      (c • (1 : Homogenization.Mat d))))
    (eta : Homogenization.BlockVec d)
    (heta : SuperdiffusionCLT.Section2.Carriers.blockVecNorm eta = 1) :
    Homogenization.BlockJ (Homogenization.cubeSet Q)
        (c ^ (-(1 : ℝ) / 2) • eta.1, c ^ ((1 : ℝ) / 2) • eta.2)
        (c ^ ((1 : ℝ) / 2) • eta.1, c ^ (-(1 : ℝ) / 2) • eta.2) a ≤
      Homogenization.normalizedBlockResponseMax Q a (c • (1 : Homogenization.Mat d)) := by
  unfold Homogenization.normalizedBlockResponseMax
  refine le_csSup hbdd ⟨Homogenization.toFullBlockVec eta, ?_, ?_⟩
  · have h1 := SuperdiffusionCLT.Section2.Carriers.blockVecNorm_eq_sqrt_blockVecDot eta
    have h2 := Homogenization.blockVecDot_ofFullBlockVec_self_eq_fullBlockVecNormSq
      (Homogenization.toFullBlockVec eta)
    rw [Homogenization.ofFullBlockVec_toFullBlockVec] at h2
    rw [← h2]
    rw [heta] at h1
    have h3 := Real.sqrt_eq_one.1 h1.symm
    exact h3
  · rw [srootN_ofFullBlockVec_mulVec_invSqrt_smul_one d hc,
      srootN_ofFullBlockVec_mulVec_sqrt_smul_one d hc,
      Homogenization.ofFullBlockVec_toFullBlockVec]

/-- **Case B, pathwise** (the recentering step, far cutoffs `L > mm`). For the descendant `R`
of `cu_n` read at the shift `z = 3^{n-3} k` (with `z + cu_n ⊆ cu_m`), the maximal normalized block
response of the centered field at the cutoff `L` is at most that at the cutoff `mm`, plus
`X1 + ‖h_0‖² X2` with `h_0 = -(k_mm)_{cu_m}`. The witnesses `X1`, `X2` are `Γ_{1/3}`, do not
depend on `L`, and come from `srootNS_nearTail_J_comparison_shift_sigmaBar`. -/
theorem srootNS_caseB_pathwise (d : ℕ) [NeZero d]
    {P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)}
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    {nu : ℝ} (hnu : 0 < nu) {m mm : ℕ} (hmm : m ≤ mm + 1) (r : ℕ) (n : ℕ) (k : Fin d → ℤ)
    (hk : (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
        Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)) ⊆
      Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))
    (R : Homogenization.TriadicCube d)
    (hRn : Homogenization.cubeSet R ⊆ Homogenization.cubeSet (Homogenization.originCube d (n : ℤ))) :
    ∃ X1 X2 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
      Measurable X1 ∧ Measurable X2 ∧
      Homogenization.IndependentSums.IsBigO P.toMeasure
        (Homogenization.IndependentSums.gammaSigma (1 / 3)) X1
        ((SuperdiffusionCLT.Section2.Annealed.envelopeUpperScalar d nu mm *
              (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu r P)⁻¹ +
            2 * SuperdiffusionCLT.Section2.Annealed.envelopeLowerScalar d nu *
              SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu r P) *
          (srootN3_tailConst d *
            (nu⁻¹ * ((3 : ℝ) ^ m * ((3 : ℝ) ^ mm)⁻¹) +
              nu⁻¹ ^ 2 * ((3 : ℝ) ^ m * ((3 : ℝ) ^ mm)⁻¹) ^ 2))) ∧
      Homogenization.IndependentSums.IsBigO P.toMeasure
        (Homogenization.IndependentSums.gammaSigma (1 / 3)) X2
        ((2 * SuperdiffusionCLT.Section2.Annealed.envelopeLowerScalar d nu *
              (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu r P)⁻¹) *
          (srootN3_tailConst d *
            (nu⁻¹ * ((3 : ℝ) ^ m * ((3 : ℝ) ^ mm)⁻¹) +
              nu⁻¹ ^ 2 * ((3 : ℝ) ^ m * ((3 : ℝ) ^ mm)⁻¹) ^ 2))) ∧
      ∀ᵐ omega ∂P.toMeasure, ∀ L : ℕ, mm < L →
        Homogenization.normalizedBlockResponseMax R (srootE_field nu omega L m n k)
            (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu r P •
              (1 : Homogenization.Mat d)) ≤
          Homogenization.normalizedBlockResponseMax R (srootE_field nu omega mm m n k)
              (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu r P •
                (1 : Homogenization.Mat d)) + X1 omega +
            Homogenization.Book.Ch02.matrixOperatorNorm (srootNS_h0 m mm omega) ^ 2 * X2 omega := by
  set z : Homogenization.Vec d := fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ) with hz
  have hsub : (fun x => z + x) '' Homogenization.openCubeSet R ⊆
      Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)) :=
    (Set.image_mono ((Homogenization.openCubeSet_subset_cubeSet R).trans hRn)).trans hk
  have hUsub := srootNS_translate_openCube_subset_openCube R z m hsub
  set V : Homogenization.Book.Ch02.Domain d :=
    Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d (m : ℤ)) with hVdef
  set U : Homogenization.Book.Ch02.Domain d := srootNS_translatedCubeDomain R z with hUdef
  have hV : (V : Set (Homogenization.Vec d)) ⊆
      Homogenization.openCubeSet (Homogenization.originCube d (m : ℤ)) := by
    rw [hVdef, Homogenization.Book.Ch02.cubeDomain_coe]
  have hUV : (U : Set (Homogenization.Vec d)) ⊆ (V : Set (Homogenization.Vec d)) := by
    rw [hVdef, Homogenization.Book.Ch02.cubeDomain_coe]
    exact hUsub
  obtain ⟨X1, X2, hm1, hm2, hb1, hb2, hae⟩ :=
    srootNS_nearTail_J_comparison_shift_sigmaBar hPrefix hJ2 hJ3 hJ4 hnu hmm r V U hV hUV
  refine ⟨X1, X2, hm1, hm2, hb1, hb2, ?_⟩
  filter_upwards [hae] with omega hom L hL
  have hsg := SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite_pos hnu r hPrefix hJ2 hJ3 hJ4
  set sg : ℝ := SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu r P with hsgdef
  have hh0 := srootNS_h0_skew (d := d) m mm omega
  have hkV := srootNS_skew_volumeAverage_finiteShellIncrement omega mm L (V : Set (Homogenization.Vec d))
  have hkV' : Homogenization.matTranspose
      (-Homogenization.volumeAverageMat (V : Set (Homogenization.Vec d))
        (fun y => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega mm L y)) =
      -(-Homogenization.volumeAverageMat (V : Set (Homogenization.Vec d))
        (fun y => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega mm L y)) := by
    simp only [Homogenization.matTranspose, Matrix.transpose_neg] at hkV ⊢
    rw [hkV]
  -- the coefficient objects
  have hentry : ∀ (l : ℕ) (x : Homogenization.Vec d), x ∈ (U : Set (Homogenization.Vec d)) →
      ∀ i j, |(SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega l).toCoeffField x i j| ≤
        SuperdiffusionCLT.Section4.NewMixing.newMixParam_entryBound U nu omega l :=
    fun l x hx i j =>
      SuperdiffusionCLT.Section4.NewMixing.newMixParam_entryBound_holds U nu hnu omega l x hx i j
  set b0 : Homogenization.Book.Ch02.CoeffOn U :=
    SuperdiffusionCLT.Section2.CoarseGraining.addConstSkewCoeffOn
      (SuperdiffusionCLT.Section2.CoarseGraining.coefficientCutoffCoeffOn U hnu omega L
        (hentry L)) hkV' with hb0
  have hb0field : ∀ x ∈ (U : Set (Homogenization.Vec d)), b0.toCoeffField x =
      (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField x -
        Homogenization.volumeAverageMat (V : Set (Homogenization.Vec d))
          (fun y => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega mm L y) := by
    intro x _
    simp [hb0, sub_eq_add_neg]
  have hVb : Bornology.IsBounded (V : Set (Homogenization.Vec d)) :=
    V.isDomain.isBoundedDomain.isBounded
  have havg : ∀ f : Homogenization.Vec d → Homogenization.Mat d,
      Homogenization.volumeAverageMat (V : Set (Homogenization.Vec d)) f =
        Homogenization.volumeAverageMat
          (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ))) f :=
    fun f => (srootNS_volumeAverageMat_cubeSet_origin_eq_cubeDomain m f).symm
  have hid : srootNS_h0 m L omega =
      -Homogenization.volumeAverageMat (V : Set (Homogenization.Vec d))
          (fun y => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega mm L y) +
        srootNS_h0 m mm omega := by
    unfold srootNS_h0
    rw [srootNS_volumeAverageMat_finiteShellIncrement_eq omega hL.le hVb, havg, havg]
    abel
  have hF6 := hom L hL b0 hb0field (srootNS_h0 m mm omega) hh0
  have e1 := srootNS_srootE_field_eq_translate nu omega L m n k
  have e2 := srootNS_srootE_field_eq_translate nu omega mm m n k
  obtain ⟨LamM, -, hEllM⟩ :=
    srootL4_exists_ellipticOn_field_cube nu hnu omega mm m n k hk R hRn
  have hbdd := Homogenization.normalizedBlockResponseValueSet_bddAbove_of_isEllipticFieldOn R _
    (sg • (1 : Homogenization.Mat d)) hEllM
  set bL : Homogenization.Book.Ch02.CoeffOn U :=
    SuperdiffusionCLT.Section2.CoarseGraining.addConstSkewCoeffOn
      (SuperdiffusionCLT.Section2.CoarseGraining.coefficientCutoffCoeffOn U hnu omega L
        (hentry L)) (srootNS_h0_skew m L omega) with hbL
  set bR : Homogenization.Book.Ch02.CoeffOn U :=
    SuperdiffusionCLT.Section2.CoarseGraining.addConstSkewCoeffOn
      (SuperdiffusionCLT.Section2.CoarseGraining.coefficientCutoffCoeffOn U hnu omega mm
        (hentry mm)) hh0 with hbR
  have hEllL : Homogenization.IsEllipticFieldOn bL.lam bL.Lam (U : Set (Homogenization.Vec d))
      bL.toCoeffField :=
    SuperdiffusionCLT.Section4.NewMixing.newMixAsm_isEllipticFieldOn_aLplusH0 hnu omega L
      (srootNS_h0 m L omega) (srootNS_h0_skew m L omega) U
  have hEllR : Homogenization.IsEllipticFieldOn bR.lam bR.Lam (U : Set (Homogenization.Vec d))
      bR.toCoeffField :=
    SuperdiffusionCLT.Section4.NewMixing.newMixAsm_isEllipticFieldOn_aLplusH0 hnu omega mm
      (srootNS_h0 m mm omega) hh0 U
  have hbLf : bL.toCoeffField = (SuperdiffusionCLT.Section2.Cutoff.centeredCoefficientCutoff nu
      omega L (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))).toCoeffField := by
    rw [srootNS_centered_toCoeffField_eq_add_h0]
    rfl
  have hbRf : bR.toCoeffField = (SuperdiffusionCLT.Section2.Cutoff.centeredCoefficientCutoff nu
      omega mm (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))).toCoeffField := by
    rw [srootNS_centered_toCoeffField_eq_add_h0]
    rfl
  have hAE1 : Homogenization.Book.Ch02.CoeffOn.AEEq bL
      (SuperdiffusionCLT.Section2.CoarseGraining.addConstSkewCoeffOn b0 hh0) := by
    refine Filter.Eventually.of_forall fun x => ?_
    show (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField x +
        srootNS_h0 m L omega =
      ((SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField x +
        -Homogenization.volumeAverageMat (V : Set (Homogenization.Vec d))
          (fun y => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega mm L y)) +
        srootNS_h0 m mm omega
    rw [hid]
    abel
  have hAE2 : Homogenization.Book.Ch02.CoeffOn.AEEq
      (SuperdiffusionCLT.Section2.CoarseGraining.addConstSkewCoeffOn
        (SuperdiffusionCLT.Section2.Annealed.cutoffDomainCoeffOn U hnu omega mm) hh0) bR :=
    Filter.Eventually.of_forall fun x => rfl
  rw [e1]
  refine srootN_normalizedBlockResponseMax_le_of_forall_probe R _ hsg ?_
  intro eta heta
  have h6 := hF6 eta heta
  rw [srootN3_bfAhomPow_neg_half, srootN3_bfAhomPow_half] at h6
  have h6' := (abs_sub_le_iff.1 h6).1
  rw [srootNS_BlockJ_translate_eq_doubledResponseJ R z _ U rfl bL hbLf hEllL,
    Homogenization.Book.Ch02.doubledResponseJ_eq_ofAEEq hAE1]
  rw [Homogenization.Book.Ch02.doubledResponseJ_eq_ofAEEq hAE2] at h6'
  have href := srootNS_BlockJ_translate_eq_doubledResponseJ R z _ U rfl bR hbRf hEllR
    (sg ^ (-(1 : ℝ) / 2) • eta.1, sg ^ ((1 : ℝ) / 2) • eta.2)
    (sg ^ ((1 : ℝ) / 2) • eta.1, sg ^ (-(1 : ℝ) / 2) • eta.2)
  rw [← e2] at href
  have hle := srootNS_blockJ_probe_le_normalizedBlockResponseMax R
    (srootE_field nu omega mm m n k) hsg hbdd eta heta
  linarith only [h6', href, hle]

/-- Witness for the geometric hypotheses of `srootNS_caseB_pathwise`: `d = 1`, `m = n = 0`,
`k = 0`, `R = cu_0`, and `m ≤ mm + 1` with `mm = 0`. -/
example :
    (fun x : Homogenization.Vec 1 => (fun i : Fin 1 => (3 : ℝ) ^ (((0 : ℕ) : ℤ) - 3) *
          (((fun _ : Fin 1 => (0 : ℤ)) i : ℤ) : ℝ)) + x) ''
        Homogenization.cubeSet (Homogenization.originCube 1 (((0 : ℕ) : ℕ) : ℤ)) ⊆
      Homogenization.cubeSet (Homogenization.originCube 1 (((0 : ℕ) : ℕ) : ℤ)) ∧
    Homogenization.cubeSet (Homogenization.originCube 1 (0 : ℤ)) ⊆
      Homogenization.cubeSet (Homogenization.originCube 1 (((0 : ℕ) : ℕ) : ℤ)) ∧ 0 ≤ 0 + 1 := by
  refine ⟨?_, subset_rfl, by norm_num⟩
  rintro _ ⟨x, hx, rfl⟩
  simpa using hx

end

end SuperdiffusionCLT.Section4.MinimalScales
