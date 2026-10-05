/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Engine.CaccCube
public import SuperdiffusionCLT.Section6.Engine.PoincCube
public import SuperdiffusionCLT.Section6.Engine.CubeNorms
public import SuperdiffusionCLT.Section6.Engine.Solutions
public import SuperdiffusionCLT.Section6.Prereq.EuclidBall
public import Homogenization.Book.Ch04.Theorems.DilationLaw

/-! ## Satisfiability of the one-block inputs (E-W1): the Laplace field -/

@[expose] public section

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory

variable {d : ℕ}

noncomputable def ew1_reg (d : ℕ) : RegCoeffField d where
  toFun := fun _ => (1 : Mat d)
  entry_measurable := fun _ _ => measurable_const
  entry_locInt := fun _ _ => locallyIntegrable_const _

theorem ew1_ae (Q : TriadicCube d) :
    Book.Ch04.AEEllipticOn 1 1 (openCubeSet Q) (ew1_reg d) := by
  have hE : IsEllipticFieldOn 1 1 (openCubeSet Q) (fun _ : Vec d => (1 : Mat d)) :=
    isEllipticFieldOn_constantCoeffField (measurableSet_openCubeSet Q)
      (by simpa using isEllipticMatrix_scalarMatrix (d := d) (sigma := 1) one_pos)
  refine ⟨measurableSet_openCubeSet Q, fun i j => ?_, ?_⟩
  · have := (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hE.1)
    refine (this.aestronglyMeasurable (μ := volumeMeasureOn (openCubeSet Q))).congr
      (ae_of_all _ fun x => ?_)
    by_cases hx : x ∈ openCubeSet Q <;> simp [restrictCoeffField, ew1_reg, hx]
  · exact (ae_restrict_iff' (measurableSet_openCubeSet Q)).mpr (ae_of_all _ hE.2)

theorem ew1_loc : Book.Ch04.AELocallyUniformlyEllipticField (ew1_reg d) :=
  fun Q => ⟨1, 1, one_pos, le_rfl, ew1_ae Q⟩

theorem ew1_rescale (k : ℕ) : rescaleReg k (ew1_reg d) = ew1_reg d := by
  apply RegCoeffField.ext
  intro x
  rfl

theorem ew1_x_const [NeZero d] (n : ℕ) (s : ℝ) (q : Book.Ch02.MultiscaleExponent) :
    Book.Ch04.LambdaSqCoeffField (originCube d (n : ℤ)) s q (ew1_reg d) =
      Book.Ch04.LambdaSqCoeffField (originCube d ((0 : ℕ) : ℤ)) s q (ew1_reg d) := by
  have h := Book.Ch04.LambdaSqCoeffField_originCube_rescaleCoeffField_of_aelocallyUniformlyElliptic
    (ew1_loc (d := d)) n 0 s q
  rw [ew1_rescale] at h
  simpa using h.symm

theorem ew1_l_const [NeZero d] (n : ℕ) (s : ℝ) (q : Book.Ch02.MultiscaleExponent) :
    Book.Ch04.lambdaSqCoeffField (originCube d (n : ℤ)) s q (ew1_reg d) =
      Book.Ch04.lambdaSqCoeffField (originCube d ((0 : ℕ) : ℤ)) s q (ew1_reg d) := by
  have h := Book.Ch04.lambdaSqCoeffField_originCube_rescaleCoeffField_of_aelocallyUniformlyElliptic
    (ew1_loc (d := d)) n 0 s q
  rw [ew1_rescale] at h
  simpa using h.symm

theorem ew1_le_sq_sqrt (x : ℝ) : x ≤ Real.sqrt x ^ 2 := by
  by_cases h : 0 ≤ x
  · rw [Real.sq_sqrt h]
  · have := Real.sqrt_nonneg x
    nlinarith only [this, not_le.mp h]

theorem ew1_ellip_bound [NeZero d] (n : ℕ) :
    ∃ X Y : ℝ, X = ((d : ℝ) * Real.rpow (Book.Ch04.LambdaSqCoeffField (originCube d ((0 : ℕ) : ℤ))
        (1 / 4) (Book.Ch02.MultiscaleExponent.finite 1) (ew1_reg d)) (1 / 2 : ℝ)) ^ 2 ∧
      Y = ((d : ℝ) * Real.rpow (Book.Ch04.lambdaSqCoeffField (originCube d ((0 : ℕ) : ℤ))
        (1 / 4) (Book.Ch02.MultiscaleExponent.finite 1) (ew1_reg d)) (-(1 / 2 : ℝ))) ^ 2 ∧
      LambdaSq (originCube d (n : ℤ)) (1 / 4) (MultiscaleExponent.finite 1)
        (constantCoeffField (1 : Mat d)) ≤ X ∧
      (lambdaSq (originCube d (n : ℤ)) (1 / 4) (MultiscaleExponent.finite 1)
        (constantCoeffField (1 : Mat d)))⁻¹ ≤ Y := by
  refine ⟨_, _, rfl, rfl, ?_, ?_⟩
  all_goals
    set F := Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField (ew1_reg d) ew1_loc
      with hF
    have hg : Book.Ch03.publicCoeffField (originCube d (n : ℤ)) F =ᵐ[volumeMeasureOn
        (cubeSet (originCube d (n : ℤ)))] (constantCoeffField (1 : Mat d)) :=
      Book.Ch03.publicCoeffField_ae_eq_cubeSet _ F
  · rw [← l5_LambdaSq_congr_ae _ _ _ hg]
    refine (ew1_le_sq_sqrt _).trans ?_
    gcongr
    have h := Book.Ch03.sqrt_LambdaSq_publicCoeffField_finite_one_le_dim_mul_poincareUpperEllipticityFactor
      (originCube d (n : ℤ)) F (s := 1 / 4) (by norm_num)
    refine h.trans ?_
    unfold Book.Ch03.poincareUpperEllipticityFactor
    rw [show Book.Ch02.LambdaSq (originCube d (n : ℤ)) (1 / 4) (Book.Ch02.MultiscaleExponent.finite 1) F =
      Book.Ch04.LambdaSqCoeffField (originCube d (n : ℤ)) (1 / 4)
        (Book.Ch02.MultiscaleExponent.finite 1) (ew1_reg d) by
      simp [Book.Ch04.LambdaSqCoeffField, ew1_loc, hF], ew1_x_const]
  · rw [← l5_lambdaSq_congr_ae _ _ _ hg]
    refine (ew1_le_sq_sqrt _).trans ?_
    gcongr
    have h := Book.Ch03.sqrt_lambdaSq_publicCoeffField_finite_one_inv_le_dim_mul_poincareLowerEllipticityFactor
      (originCube d (n : ℤ)) F (s := 1 / 4) (by norm_num)
    refine h.trans ?_
    unfold Book.Ch03.poincareLowerEllipticityFactor
    rw [show Book.Ch02.lambdaSq (originCube d (n : ℤ)) (1 / 4) (Book.Ch02.MultiscaleExponent.finite 1) F =
      Book.Ch04.lambdaSqCoeffField (originCube d (n : ℤ)) (1 / 4)
        (Book.Ch02.MultiscaleExponent.finite 1) (ew1_reg d) by
      simp [Book.Ch04.lambdaSqCoeffField, ew1_loc, hF], ew1_l_const]

theorem ew1_B (d : ℕ) [NeZero d] :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ n : ℕ,
      (1 : ℝ)⁻¹ * LambdaSq (originCube d (n : ℤ)) (1 / 4) (MultiscaleExponent.finite 1)
          (constantCoeffField (1 : Mat d)) +
        1 * (lambdaSq (originCube d (n : ℤ)) (1 / 4) (MultiscaleExponent.finite 1)
          (constantCoeffField (1 : Mat d)))⁻¹ ≤ B := by
  obtain ⟨X, Y, hX, hY, -, -⟩ := ew1_ellip_bound (d := d) 0
  refine ⟨max 1 (X + Y), le_max_left _ _, fun n => ?_⟩
  obtain ⟨X', Y', hX', hY', h1, h2⟩ := ew1_ellip_bound (d := d) n
  rw [hX'] at h1
  rw [hY'] at h2
  rw [← hX] at h1
  rw [← hY] at h2
  rw [inv_one, one_mul, one_mul]
  exact (add_le_add h1 h2).trans (le_max_right _ _)

theorem ew1_symm (x : Vec d) :
    symmPart ((fun _ : Vec d => (1 : Mat d)) x) = (1 : ℝ) • (1 : Mat d) := by
  show symmPart (1 : Mat d) = _
  ext i j
  by_cases h : i = j
  · subst h
    simp [symmPart]
  · simp [symmPart, h, Ne.symm h]

theorem ew1_engCube_mono {a b : ℕ} (h : a ≤ b) : engCube d a ⊆ engCube d b := by
  induction b, h using Nat.le_induction with
  | base => exact Set.Subset.rfl
  | succ m _ ih =>
    refine ih.trans ?_
    have h := HarmonicApprox.originCube_pred_openCubeSet_subset (d := d) ((m + 1 : ℕ) : ℤ)
    have e : ((m + 1 : ℕ) : ℤ) - 1 = (m : ℤ) := by push_cast; ring
    rw [e] at h
    exact h

theorem ew1_ellip (U : Set (Vec d)) (hU : MeasurableSet U) :
    IsEllipticFieldOn 1 1 U (fun _ : Vec d => (1 : Mat d)) :=
  isEllipticFieldOn_constantCoeffField hU
    (by simpa using isEllipticMatrix_scalarMatrix (d := d) (sigma := 1) one_pos)

/-- `e ↦ (x ↦ e · x)` as a linear map. -/
def engLin (d : ℕ) : Vec d →ₗ[ℝ] (Vec d → ℝ) where
  toFun e := fun x => vecDot e x
  map_add' e e' := by
    funext x
    simp [vecDot, add_mul, Finset.sum_add_distrib]
  map_smul' c e := by
    funext x
    simp [vecDot, mul_assoc, Finset.mul_sum]

/-- **E-W1.** The hypotheses of `eng_deterministic` are met by the Laplace field, the affine
family, the zero rate and `s = 1`, for every block length and every `mstar`. -/
theorem eng_witness_laplace (d : ℕ) [NeZero d] :
    ∃ Cw : ℝ, 1 ≤ Cw ∧
      GrowthElliptic (fun _ : Vec d => (1 : Mat d)) ∧
      (∀ n : ℕ, ∃ lam Lam : ℝ,
        IsEllipticFieldOn lam Lam (engCube d n) (fun _ : Vec d => (1 : Mat d))) ∧
      ∀ j : ℕ, 3 ≤ j →
        (∀ t : ℕ, 3 ≤ t → t ≤ j →
          ∀ (u : Vec d → ℝ) (g : Vec d → Vec d),
            IsSolOn (fun _ => (1 : Mat d)) (engCube d t) u g →
            ∃ (w : Vec d → ℝ) (gw : Vec d → Vec d),
              IsSolOn (fun _ => (1 : Mat d)) (engCube d (t - 3)) w gw ∧
                cubeL2 (t - 3) (fun x => u x - w x) ≤
                  Cw * (0 : ℝ) * (3 : ℝ) ^ t * cubeFlat t u) ∧
        (∀ (u : Vec d → ℝ) (g : Vec d → Vec d),
          IsSolOn (fun _ => (1 : Mat d)) (engCube d j) u g →
            cubeGradL2 (j - 2) g ≤ Cw * Real.sqrt 1 * cubeFlat j u ∧
              Real.sqrt 1 * cubeFlat j u ≤ Cw * cubeGradL2 j g) ∧
        ∀ e : Vec d,
          (∃ g : Vec d → Vec d,
            IsSolOn (fun _ => (1 : Mat d)) (engCube d j) (engLin d e) g) ∧
            cubeFlat j (fun x => engLin d e x - vecDot e x) ≤ Cw * (0 : ℝ) * engNorm e := by
  obtain ⟨B, hB1, hB⟩ := ew1_B d
  obtain ⟨C1, hC1, hcacc⟩ := eng_cacc_cube d B hB1
  obtain ⟨C2, hC2, hpoinc⟩ := eng_poinc_cube d B hB1
  have hC1' : C1 ≤ max C1 C2 := le_max_left _ _
  have hC2' : C2 ≤ max C1 C2 := le_max_right _ _
  refine ⟨max C1 C2, hC1.trans hC1', ?_, ?_, ?_⟩
  · intro R _
    exact ⟨1, 1, ew1_ellip _ (measurableSet_euclidBall R)⟩
  · intro n
    exact ⟨1, 1, ew1_ellip _ (measurableSet_openCubeSet _)⟩
  intro j hj
  refine ⟨?_, ?_, ?_⟩
  · intro t ht3 htj u g hsol
    refine ⟨u, g, hsol.mono (isOpen_openCubeSet _) (isOpen_openCubeSet _)
      (ew1_engCube_mono (by omega)) (volume_openCubeSet_lt_top _).ne
      ⟨1, 1, ew1_ellip _ (measurableSet_openCubeSet _)⟩, ?_⟩
    have h0 : (fun x => u x - u x) = fun x => (0 : ℝ) * u x := by
      funext x
      ring
    rw [h0, cubeL2_const_mul]
    simp
  · intro u g hsol
    have h1 := hcacc j (by omega) (regEllipticity_witness _) one_pos le_rfl one_pos one_pos
      (fun x _ => ew1_symm x) (hB j) u g hsol
    have h2 := hpoinc j (regEllipticity_witness _) one_pos le_rfl one_pos one_pos
      (fun x _ => ew1_symm x) (hB j) u g hsol
    have hf := cubeFlat_nonneg (d := d) j u
    have hg := cubeL2_nonneg (d := d) j (fun x => engNorm (g x))
    simp only [div_one, Real.sqrt_one, mul_one, one_mul] at h1 h2 ⊢
    refine ⟨h1.trans ?_, h2.trans ?_⟩
    · exact mul_le_mul_of_nonneg_right hC1' hf
    · exact mul_le_mul_of_nonneg_right hC2' hg
  · intro e
    refine ⟨⟨fun _ => e, ?_⟩, ?_⟩
    · have h : engLin d e = fun x => 0 + vecDot e x := by
        funext x
        simp [engLin]
      rw [h]
      exact isSolOn_one_affine j 0 e
    · have h0 : (fun x => engLin d e x - vecDot e x) = fun x => (0 : ℝ) * vecDot e x := by
        funext x
        simp [engLin]
      rw [h0, cubeFlat_const_mul]
      simp

end SuperdiffusionCLT.Section6
