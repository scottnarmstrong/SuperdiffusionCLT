/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Engine.WitnessLaplace
public import SuperdiffusionCLT.Section6.Engine.CorrectorCube
public import SuperdiffusionCLT.Section6.Engine.AffineSlope
public import SuperdiffusionCLT.Section6.Lemma.SstarCloseB

/-! ## Second witness: a positive, scale-dependent rate -/

@[expose] public section

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory SuperdiffusionCLT.Section6.HarmonicApprox

variable {d : ℕ}

/-- The `hs` block for `s = 1`. -/
theorem ew1b_hs (Cs κ : ℝ) (hCs : 1 ≤ Cs) (hκ : 0 < κ) (mstar : ℕ) :
    ∀ k m : ℕ, mstar ≤ k → k ≤ m →
      0 < (fun _ : ℕ => (1 : ℝ)) m ∧ (fun _ : ℕ => (1 : ℝ)) (m + 1) ≤ 2 * (fun _ : ℕ => (1 : ℝ)) m ∧
        (fun _ : ℕ => (1 : ℝ)) k ≤ Cs * (9 : ℝ) ^ (κ * ((m : ℝ) - (k : ℝ))) *
          (fun _ : ℕ => (1 : ℝ)) m := by
  intro k m _ hkm
  have hk : (0 : ℝ) ≤ κ * ((m : ℝ) - (k : ℝ)) :=
    mul_nonneg hκ.le (sub_nonneg.mpr (by exact_mod_cast hkm))
  have h9 : (1 : ℝ) ≤ (9 : ℝ) ^ (κ * ((m : ℝ) - (k : ℝ))) :=
    Real.one_le_rpow (by norm_num) hk
  refine ⟨one_pos, by norm_num, ?_⟩
  simp only [mul_one]
  nlinarith only [h9, hCs]

theorem ew1b_error [NeZero d] (n : ℕ) :
    HomogenizationErrorOnCube (originCube d (n : ℤ)) (1 / 9) MultiscaleExponent.infinity
      (MultiscaleExponent.finite 2) (fun _ : Vec d => (1 : Mat d)) ((1 : ℝ) • (1 : Mat d)) ≤ 0 := by
  have hEll : IsEllipticFieldOn 1 1 (cubeSet (originCube d (n : ℤ))) (fun _ => (1 : Mat d)) := by
    refine ⟨?_, fun x _ => ?_⟩
    · exact Measurable.of_eval fun i => Measurable.of_eval fun j =>
        Measurable.ite (measurableSet_cubeSet _) measurable_const measurable_const
    · simpa using isEllipticMatrix_scalarMatrix (d := d) (sigma := 1) one_pos
  rw [homogenizationErrorOnCube_eq_ch02 hEll one_pos le_rfl (1 / 9) 2 ((1 : ℝ) • (1 : Mat d))]
  refine l8_error_identity_le _ _ fun R x => ?_
  simp [paddedFamily, paddedCoeffOn, padField]

/-- Joint satisfiability of the hypotheses of `eng_corrector_cube` for the identity field. -/
example [NeZero d] (n : ℕ) :
    IsEllipticFieldOn 1 1 (cubeSet (originCube d (n : ℤ))) (fun _ : Vec d => (1 : Mat d)) ∧
      (0 : ℝ) < 1 ∧ (1 : ℝ) ≤ 1 ∧ (0 : ℝ) < 1 ∧ (0 : ℝ) < 1 ∧
      (∀ x ∈ cubeSet (originCube d (n : ℤ)),
        symmPart ((fun _ : Vec d => (1 : Mat d)) x) = (1 : ℝ) • (1 : Mat d)) ∧
      HomogenizationErrorOnCube (originCube d (n : ℤ)) (1 / 9) MultiscaleExponent.infinity
        (MultiscaleExponent.finite 2) (fun _ : Vec d => (1 : Mat d)) ((1 : ℝ) • (1 : Mat d)) ≤ 0 ∧
      (0 : ℝ) ≤ 1 := by
  refine ⟨?_, one_pos, le_rfl, one_pos, one_pos, fun x _ => ew1_symm x, ew1b_error n, zero_le_one⟩
  refine ⟨?_, fun x _ => ?_⟩
  · exact Measurable.of_eval fun i => Measurable.of_eval fun j =>
      Measurable.ite (measurableSet_cubeSet _) measurable_const measurable_const
  · simpa using isEllipticMatrix_scalarMatrix (d := d) (sigma := 1) one_pos

/-- **E-W1b.** Second witness, with a nonzero rate: the Laplace field with the rescaled affine
family `V j = (1 + ε j) • engLin d` and `δ = ε`. -/
theorem eng_witness_scaled (d : ℕ) [NeZero d] :
    ∃ Cw : ℝ, 1 ≤ Cw ∧
      ∀ ε : ℕ → ℝ, (∀ j : ℕ, 0 ≤ ε j ∧ ε j ≤ 1) →
      ∀ j : ℕ, 3 ≤ j →
        (∀ t : ℕ, 3 ≤ t → t ≤ j →
          ∀ (u : Vec d → ℝ) (g : Vec d → Vec d),
            IsSolOn (fun _ => (1 : Mat d)) (engCube d t) u g →
            ∃ (w : Vec d → ℝ) (gw : Vec d → Vec d),
              IsSolOn (fun _ => (1 : Mat d)) (engCube d (t - 3)) w gw ∧
                cubeL2 (t - 3) (fun x => u x - w x) ≤
                  Cw * ε j * (3 : ℝ) ^ t * cubeFlat t u) ∧
        (∀ (u : Vec d → ℝ) (g : Vec d → Vec d),
          IsSolOn (fun _ => (1 : Mat d)) (engCube d j) u g →
            cubeGradL2 (j - 2) g ≤ Cw * Real.sqrt 1 * cubeFlat j u ∧
              Real.sqrt 1 * cubeFlat j u ≤ Cw * cubeGradL2 j g) ∧
        ∀ e : Vec d,
          (∃ g : Vec d → Vec d,
            IsSolOn (fun _ => (1 : Mat d)) (engCube d j) (((1 + ε j) • engLin d) e) g) ∧
            cubeFlat j (fun x => ((1 + ε j) • engLin d) e x - vecDot e x) ≤
              Cw * ε j * engNorm e := by
  obtain ⟨Cw, hCw, -, -, h⟩ := eng_witness_laplace d
  refine ⟨Cw, hCw, fun ε hε j hj => ?_⟩
  obtain ⟨-, hCP, -⟩ := h j hj
  have hCw0 : 0 ≤ Cw := by linarith only [hCw]
  have hε0 := (hε j).1
  refine ⟨fun t ht htj u g hsol => ?_, hCP, fun e => ?_⟩
  · refine ⟨u, g, hsol.mono (isOpen_openCubeSet _) (isOpen_openCubeSet _)
      (ew1_engCube_mono (by omega)) (volume_openCubeSet_lt_top _).ne
      ⟨1, 1, ew1_ellip _ (measurableSet_openCubeSet _)⟩, ?_⟩
    have h0 : (fun x => u x - u x) = fun x => (0 : ℝ) * u x := by
      funext x
      ring
    rw [h0, cubeL2_const_mul]
    have hf := cubeFlat_nonneg (d := d) t u
    have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ t := by positivity
    rw [abs_zero, zero_mul]
    exact mul_nonneg (mul_nonneg (mul_nonneg hCw0 hε0) h3) hf
  · have hfun : ((1 + ε j) • engLin d) e = fun x => (1 + ε j) * (0 + vecDot e x) := by
      funext x
      simp [engLin]
    refine ⟨⟨fun _ => (1 + ε j) • e, ?_⟩, ?_⟩
    · rw [hfun]
      exact isSolOn_one_affine j 0 e |>.smul (1 + ε j) |> fun h => by simpa using h
    · have h1 : (fun x => ((1 + ε j) • engLin d) e x - vecDot e x) =
          fun x => ε j * vecDot e x := by
        funext x
        simp [engLin]
        ring
      rw [h1, cubeFlat_const_mul, cubeFlat_vecDot, abs_of_nonneg hε0]
      have hn := engNorm_nonneg e
      have hs3 : (1 : ℝ) ≤ 2 * Real.sqrt 3 := by
        have : (1 : ℝ) ≤ Real.sqrt 3 := by
          rw [Real.le_sqrt' (by norm_num)]
          norm_num
        linarith only [this]
      have : engNorm e / (2 * Real.sqrt 3) ≤ engNorm e :=
        div_le_self hn hs3
      calc ε j * (engNorm e / (2 * Real.sqrt 3)) ≤ ε j * engNorm e :=
            mul_le_mul_of_nonneg_left this hε0
        _ ≤ Cw * ε j * engNorm e := by
            have := mul_nonneg hε0 hn
            nlinarith only [this, hCw]



end SuperdiffusionCLT.Section6
