/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.CaccioppoliBdryM

/-!
# The energy identity split over the grid

`ν ‖φ ∇u‖² = ∫ f Φ (u - γ) + Σ_{good R} ∫_R h + ∫_B h`, with `h = (A∇u)·(Φ ∇γ - (u - γ) ∇Φ)`.
The first term is bounded by Cauchy-Schwarz, the sum by `ca2_sum_good`, and the last term is kept
for the edge-and-layer estimate.
-/

@[expose] public section

open scoped ENNReal NNReal
open MeasureTheory Filter Topology Homogenization

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem ca2_vanish_off_ball {a : ℝ} (ha : 0 < a) {x : Vec d} (hx : x ∉ Metric.ball (0 : Vec d) a)
    {γ : Vec d → ℝ} (w : ℝ) : ca2_G (ca1_Phi a) γ (fun _ => w) x = 0 := by
  have hk : ∃ k, a ≤ |x k| := by
    by_contra hcon
    push Not at hcon
    exact hx ((ca2_mem_ball_iff ha x).2 hcon)
  obtain ⟨k, hk⟩ := hk
  have h0 : ca1_phi a x = 0 := ca1_phi_eq_zero ha hk
  have hΦ : ca1_Phi a x = 0 := by rw [ca1_Phi_eq, h0]; ring
  funext i
  have hE : ca1_E a i x = 0 := by
    have := ca1_E_abs_le ha i x
    rw [h0, mul_zero] at this
    exact abs_nonpos_iff.1 this
  simp only [ca2_G, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  rw [show p12_grad (ca1_Phi (d := d) a) x i = ca1_E a i x from ca1_Phi_fderiv a i x, hΦ, hE]
  ring

theorem ca2_main [NeZero d] (hd : 2 ≤ d) (m : ℤ) (h : ℕ) {W : Set (Vec d)} (hWo : IsOpen W)
    {lam Lam : ℝ} {A : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d m) ∩ W) A)
    {ν S α1 β1 α2 β2 : ℝ} (hsym : ∀ x ∈ openCubeSet (originCube d m) ∩ W, symmPart (A x) = ν • (1 : Mat d)) (hS : 0 ≤ S) (hα1 : 0 ≤ α1) (hβ1 : 0 ≤ β1) (hα2 : 0 ≤ α2) (hβ2 : 0 ≤ β2)
    (u : H1Function (openCubeSet (originCube d m) ∩ W)) {f : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict (openCubeSet (originCube d m) ∩ W)))
    (hu : IsWeakSolutionOn A (openCubeSet (originCube d m) ∩ W) u f (fun _ => 0))
    (hBB : ∀ R ∈ descendantsAtDepth (originCube d m) h, openCubeSet R ⊆ W →
      ∀ (u' : H1Function (openCubeSet (originCube d R.scale))) (f' : Vec d → ℝ),
      IsWeakSolutionOn (fun x => A (x + triadicCubeShift R)) (openCubeSet (originCube d R.scale)) u' f'
        (fun _ => 0) →
      ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo (originCube d R.scale)
          (1 / 4 : ℝ) (fun x => matVecMul (A (x + triadicCubeShift R) - S • (1 : Mat d)) (u'.grad x))) ≤
        ENNReal.ofReal α1 * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d R.scale) 2
            (fun x => Real.sqrt (vecNormSq (u'.grad x))) +
          ENNReal.ofReal β1 * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d R.scale)
            (ENNReal.ofReal (sobStar d)).conjExponent f' ∧
      ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo (originCube d R.scale)
          (1 / 4 : ℝ) u'.grad) ≤
        ENNReal.ofReal α2 * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d R.scale) 2
            (fun x => Real.sqrt (vecNormSq (u'.grad x))) +
          ENNReal.ofReal β2 * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d R.scale)
            (ENNReal.ofReal (sobStar d)).conjExponent f')
    {a ac ℓ : ℝ} (ha : 0 < a) (hat : a < 3 ^ m / 2) (hac0 : 0 < ac) (hℓ0 : 0 < ℓ)
    (hℓ : ∀ R ∈ descendantsAtDepth (originCube d m) h, cubeScaleFactor R = ℓ)
    (hac : a + ℓ ≤ 2 / 3 * ac) {γ : Vec d → ℝ} (hγ : ContDiff ℝ 2 γ) {G1 G2 : ℝ} (hG1 : 0 ≤ G1)
    (hG2 : 0 ≤ G2) (hb1 : ∀ x ∈ openCubeSet (originCube d m) ∩ W, ‖fderiv ℝ γ x‖ ≤ G1)
    (hb2 : ∀ x ∈ openCubeSet (originCube d m) ∩ W, ‖fderiv ℝ (fderiv ℝ γ) x‖ ≤ G2) {Kη : ℝ≥0}
    (hKη : ∀ i, LipschitzWith Kη (ca1_E (d := d) a i)) {G Gc Wn Fn : ℝ} (hG0 : 0 ≤ G)
    (hGc0 : 0 ≤ Gc) (hWn0 : 0 ≤ Wn) (hFn0 : 0 ≤ Fn)
    (hGs : (cubeVolume (originCube d m))⁻¹ * ∫ x in openCubeSet (originCube d m) ∩ W,
      ca1_Phi a x * vecNormSq (u.grad x) = G ^ 2)
    (hZ : LocalizedZeroTraceFunctionOn (openCubeSet (originCube d m) ∩ W) (openCubeSet (originCube d m))
      (fun x => u.toFun x - γ x))
    (hGcs : (cubeVolume (originCube d m))⁻¹ * ∫ x in openCubeSet (originCube d m) ∩ W,
      (ca1_phi ac x * Real.sqrt (vecNormSq (u.grad x))) ^ 2 ≤ Gc ^ 2)
    (hWs : (cubeVolume (originCube d m))⁻¹ * ∫ x in openCubeSet (originCube d m) ∩ W,
      (u.toFun x - γ x) ^ 2 ≤ Wn ^ 2)
    (hFs : (cubeVolume (originCube d m))⁻¹ * ∫ x in openCubeSet (originCube d m) ∩ W, f x ^ 2 ≤ Fn ^ 2)     : ν * G ^ 2 ≤ Fn * Wn +
        ((S * α2 + α1) * ((12 * 64 ^ d * 64 ^ d * a⁻¹ * G) * (Wn + ca2_gp d a ℓ G1 G2)) +
        2 * cubeBesovW12EmbeddingConstant d * ℓ * (S * α2 + α1) *
          ((12 * 64 ^ d * 64 ^ d * a⁻¹ * G) * (((125 / 729 : ℝ) ^ d)⁻¹ * Gc)) +
        2 * cubeBesovW12EmbeddingConstant d * ℓ * (Real.sqrt d * Kη) * (S * α2 + α1) *
          ((((125 / 729 : ℝ) ^ d)⁻¹ * Gc) * (Wn + ca2_gp d a ℓ G1 G2)) +
        (S * β2 + β1) * (12 * 64 ^ d * a⁻¹) * (Fn * (Wn + ca2_gp d a ℓ G1 G2)) +
        2 * cubeBesovW12EmbeddingConstant d * ℓ * (S * β2 + β1) * (12 * 64 ^ d * a⁻¹) *
          (Fn * (((125 / 729 : ℝ) ^ d)⁻¹ * Gc)) +
        2 * cubeBesovW12EmbeddingConstant d * ℓ * (Real.sqrt d * Kη) * (S * β2 + β1) *
          (Fn * (Wn + ca2_gp d a ℓ G1 G2))) +
        (cubeVolume (originCube d m))⁻¹ * |∫ x in ca2_Bset m h a W, vecDot (matVecMul (A x) (u.grad x))
          (ca2_G (ca1_Phi a) γ (fun y => u.toFun y - γ y) x)| := by
  classical
  have hDo : IsOpen (openCubeSet (originCube d m) ∩ W) := (isOpen_openCubeSet _).inter hWo
  have hDb : Bornology.IsBounded (openCubeSet (originCube d m) ∩ W) :=
    (isBounded_openCubeSet (originCube d m)).subset Set.inter_subset_left
  have hγ1 : ContDiff ℝ 1 γ := hγ.of_le (by norm_num)
  have hΦ1 := ca2_contDiff_Phi (d := d) a
  have hΦc := ca1_hasCompactSupport_Phi (d := d) ha
  have hΦT : tsupport (ca1_Phi (d := d) a) ⊆ openCubeSet (originCube d m) :=
    (ca1_tsupport_Phi_subset ha).trans (ca1_closedBall_subset_openCube m hat)
  have hid := ca2_energy_identity hDo (isOpen_openCubeSet _) hEll hsym u hu hγ hZ hΦ1 hΦc hΦT
  have hint := ca2_integrable_cross hEll u hγ hΦ1 hΦc
  have hdec := ca2_integral_decomp m h hWo ha hint (fun x hx hxn => by
    show vecDot (matVecMul (A x) (u.grad x))
      (ca2_G (ca1_Phi a) γ (fun y => u.toFun y - γ y) x) = 0
    rw [show ca2_G (ca1_Phi a) γ (fun y => u.toFun y - γ y) x =
      ca2_G (ca1_Phi a) γ (fun _ => u.toFun x - γ x) x from rfl, ca2_vanish_off_ball ha hxn]
    exact vecDot_zero_right _)
  have hV0 : 0 < cubeVolume (originCube d m) := cubeVolume_pos _
  have hwL' : MemLp (fun x => u.toFun x - γ x) 2 (volume.restrict (openCubeSet (originCube d m) ∩ W)) :=
    u.memL2.sub (lip_witness_bdry_memLp_cont hDo hDb hγ1.continuous)
  have hN : 0 < ((descendantsAtDepth (originCube d m) h).card : ℝ) :=
    Nat.cast_pos.2 (Finset.card_pos.2 (descendantsAtDepth_nonempty _ h))
  -- the sum over the good cubes
  have hGs' : (cubeVolume (originCube d m))⁻¹ * ∫ x in openCubeSet (originCube d m) ∩ W,
      (ca1_phi a x * Real.sqrt (vecNormSq (u.grad x))) ^ 2 ≤ G ^ 2 := by
    rw [← hGs]
    refine le_of_eq (congrArg _ (integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)))
    simp only
    rw [mul_pow, Real.sq_sqrt (by unfold vecNormSq vecDot; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _),
      ← ca1_Phi_eq]
  have hsum := ca2_sum_good hd m h hWo hEll hS hα1 hβ1 hα2 hβ2 u hf hu hBB ha hac0 hℓ0 hℓ hac hγ hG1 hG2
    hb1 hb2 hKη hG0 hGc0 hWn0 hFn0 hGs' hGcs hWs hFs
  -- the cube integrals
  have hcube : ∀ R ∈ ca2_Zi m h a W, (cubeVolume (originCube d m))⁻¹ *
      ∫ x in openCubeSet R, vecDot (matVecMul (A x) (u.grad x))
        (ca2_G (ca1_Phi a) γ (fun y => u.toFun y - γ y) x) =
      ((descendantsAtDepth (originCube d m) h).card : ℝ)⁻¹ * cubeAverage R (fun x =>
        vecDot (matVecMul (A x) (u.grad x)) (ca2_G (ca1_Phi a) γ (fun y => u.toFun y - γ y) x)) := by
    intro R hR
    have hRs := (Finset.mem_filter.1 hR).1
    have hvol := cubeVolume_eq_card_mul_cubeVolume_of_mem_descendantsAtDepth hRs
    rw [ca1_cubeAverage_eq]
    have hR0 := cubeVolume_pos R
    rw [hvol]
    field_simp
  have hsumcube : (cubeVolume (originCube d m))⁻¹ * ∑ R ∈ ca2_Zi m h a W, ∫ x in openCubeSet R,
      vecDot (matVecMul (A x) (u.grad x)) (ca2_G (ca1_Phi a) γ (fun y => u.toFun y - γ y) x) ≤
      ((descendantsAtDepth (originCube d m) h).card : ℝ)⁻¹ * ∑ R ∈ ca2_Zi m h a W,
        |cubeAverage R (fun x => vecDot (matVecMul (A x) (u.grad x))
          (ca2_G (ca1_Phi a) γ (fun y => u.toFun y - γ y) x))| := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun R hR => ?_
    rw [hcube R hR]
    exact mul_le_mul_of_nonneg_left (le_abs_self _) (inv_nonneg.2 hN.le)
  -- the term with `f`
  have hΦ0 : ∀ x, 0 ≤ ca1_Phi (d := d) a x := fun x => by rw [ca1_Phi_eq]; exact sq_nonneg _
  have hfΦ : |∫ x in openCubeSet (originCube d m) ∩ W, f x * (ca1_Phi a x * (u.toFun x - γ x))| ≤
      Real.sqrt ((cubeVolume (originCube d m)) * Fn ^ 2) *
        Real.sqrt ((cubeVolume (originCube d m)) * Wn ^ 2) := by
    have hΦw : MemLp (fun x => ca1_Phi a x * (u.toFun x - γ x)) 2
        (volume.restrict (openCubeSet (originCube d m) ∩ W)) := by
      refine MemLp.of_le_mul (c := 1) hwL' ((hΦ1.continuous.aestronglyMeasurable).mul
        hwL'.aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
      rw [norm_mul, one_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (by rw [Real.norm_eq_abs]; exact ca1_Phi_abs_le a x)
    refine (ca2_cs_integral hf hΦw).trans ?_
    refine mul_le_mul (Real.sqrt_le_sqrt ?_) (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    · have := mul_le_mul_of_nonneg_left hFs hV0.le
      rwa [← mul_assoc, mul_inv_cancel₀ hV0.ne', one_mul] at this
    · have h1 : ∫ x in openCubeSet (originCube d m) ∩ W, (ca1_Phi a x * (u.toFun x - γ x)) ^ 2 ≤
          ∫ x in openCubeSet (originCube d m) ∩ W, (u.toFun x - γ x) ^ 2 := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _)
          hwL'.integrable_sq (Filter.Eventually.of_forall fun x => ?_)
        simp only
        rw [mul_pow]
        have h2 := ca1_Phi_abs_le a x
        have h3 : ca1_Phi a x ^ 2 ≤ 1 := by
          have := hΦ0 x
          have h4 := (abs_le.1 h2).2
          nlinarith only [this, h4]
        nlinarith only [h3, sq_nonneg (u.toFun x - γ x)]
      have := mul_le_mul_of_nonneg_left hWs hV0.le
      rw [← mul_assoc, mul_inv_cancel₀ hV0.ne', one_mul] at this
      exact h1.trans this
  have hFW : (cubeVolume (originCube d m))⁻¹ * (Real.sqrt ((cubeVolume (originCube d m)) * Fn ^ 2) *
      Real.sqrt ((cubeVolume (originCube d m)) * Wn ^ 2)) = Fn * Wn := by
    rw [Real.sqrt_mul hV0.le, Real.sqrt_mul hV0.le, Real.sqrt_sq hFn0, Real.sqrt_sq hWn0]
    have : Real.sqrt (cubeVolume (originCube d m)) * Real.sqrt (cubeVolume (originCube d m)) =
        cubeVolume (originCube d m) := Real.mul_self_sqrt hV0.le
    calc (cubeVolume (originCube d m))⁻¹ * (Real.sqrt (cubeVolume (originCube d m)) * Fn *
          (Real.sqrt (cubeVolume (originCube d m)) * Wn))
        = (cubeVolume (originCube d m))⁻¹ * (Real.sqrt (cubeVolume (originCube d m)) *
          Real.sqrt (cubeVolume (originCube d m))) * (Fn * Wn) := by ring
      _ = Fn * Wn := by rw [this, inv_mul_cancel₀ hV0.ne', one_mul]
  have hFterm : (cubeVolume (originCube d m))⁻¹ *
      (∫ x in openCubeSet (originCube d m) ∩ W, f x * (ca1_Phi a x * (u.toFun x - γ x))) ≤ Fn * Wn := by
    rw [← hFW]
    exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans hfΦ) (inv_nonneg.2 hV0.le)
  have hBterm : (cubeVolume (originCube d m))⁻¹ * (∫ x in ca2_Bset m h a W, vecDot (matVecMul (A x) (u.grad x))
      (ca2_G (ca1_Phi a) γ (fun y => u.toFun y - γ y) x)) ≤
      (cubeVolume (originCube d m))⁻¹ * |∫ x in ca2_Bset m h a W, vecDot (matVecMul (A x) (u.grad x))
      (ca2_G (ca1_Phi a) γ (fun y => u.toFun y - γ y) x)| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) (inv_nonneg.2 hV0.le)
  have hνG : ν * G ^ 2 = (cubeVolume (originCube d m))⁻¹ * (ν * ∫ x in openCubeSet (originCube d m) ∩ W,
      ca1_Phi a x * vecNormSq (u.grad x)) := by
    rw [← hGs]; ring
  rw [hνG, hid, hdec]
  have e : (cubeVolume (originCube d m))⁻¹ * ((∫ x in openCubeSet (originCube d m) ∩ W,
        f x * (ca1_Phi a x * (u.toFun x - γ x))) +
      ((∑ R ∈ ca2_Zi m h a W, ∫ x in openCubeSet R, vecDot (matVecMul (A x) (u.grad x))
          (ca2_G (ca1_Phi a) γ (fun y => u.toFun y - γ y) x)) +
        ∫ x in ca2_Bset m h a W, vecDot (matVecMul (A x) (u.grad x))
          (ca2_G (ca1_Phi a) γ (fun y => u.toFun y - γ y) x))) =
      (cubeVolume (originCube d m))⁻¹ * (∫ x in openCubeSet (originCube d m) ∩ W,
        f x * (ca1_Phi a x * (u.toFun x - γ x))) +
      (cubeVolume (originCube d m))⁻¹ * (∑ R ∈ ca2_Zi m h a W, ∫ x in openCubeSet R,
          vecDot (matVecMul (A x) (u.grad x))
          (ca2_G (ca1_Phi a) γ (fun y => u.toFun y - γ y) x)) +
      (cubeVolume (originCube d m))⁻¹ * (∫ x in ca2_Bset m h a W, vecDot (matVecMul (A x) (u.grad x))
          (ca2_G (ca1_Phi a) γ (fun y => u.toFun y - γ y) x)) := by ring
  rw [e]
  linarith only [hFterm, hsumcube, hsum, hBterm]

end SuperdiffusionCLT.Section7
