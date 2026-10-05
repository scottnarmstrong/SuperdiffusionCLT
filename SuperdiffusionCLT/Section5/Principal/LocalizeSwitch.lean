/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.LocalizationDisplayE
public import SuperdiffusionCLT.Section2.Localization.LocalizationDisplayK
public import SuperdiffusionCLT.Section5.Carriers.BlockOffset

/-!
# The localization and switch displays of the principal term

Displays `e.principal.localize`, `e.principal.Dz`, `e.principal.hbar` and `e.principal.switch`.
With the lower cutoff `l = m - h` and the upper cutoff `L = m`, the shell
increment `k_m - k_{m-h}` is the shell field `hshell`, and the printed boxwise gauge `h̄_z` is
`principalGauge`, that is `localizationGaugeAverage (m - h) m R`. The deterministic per-cube
comparison `localization_display_e_hpoint` of `Section2.Localization` is the whole content;
this file only specializes it, removes the gauge conjugation, and states `D_z` against the
derivative gauge.

All statements are deterministic and hold for every shell sequence and every triadic cube.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization Homogenization.Book.Ch02
open SuperdiffusionCLT.Section2.Localization

variable {d : ℕ}

/-! ## The boxwise gauge and the gauged slope (`e.principal.hbar`) -/

/-- The boxwise gauge `hbar_z := (hshell)_{z+cu_n}`, `hshell = k_m - k_{m-h}`. -/
noncomputable def principalGauge (m h : ℕ) (R : TriadicCube d)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) : Mat d :=
  localizationGaugeAverage (m - h) m R omega

/-- `principalGauge` is the volume average over the cube of `k_m - k_{m-h}`. -/
theorem principalGauge_eq_average (m h : ℕ) (R : TriadicCube d)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) :
    principalGauge m h R omega =
      volumeAverageMat (cubeSet R) (fun y =>
        SuperdiffusionCLT.Frozen.Section2.streamCutoff omega m y -
          SuperdiffusionCLT.Frozen.Section2.streamCutoff omega (m - h) y) := by
  unfold principalGauge localizationGaugeAverage
  congr 1
  funext y
  exact SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement_apply_eq_streamCutoff_sub
    omega (Nat.sub_le m h) y

/-- `P̂_z := G_{-hbar_z} P_z`. -/
noncomputable def principalPhat (m h : ℕ) (R : TriadicCube d)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (P : BlockVec d) : BlockVec d :=
  blockMatVecMul (gaugeMat (-principalGauge m h R omega)) P

/-! ## `e.principal.localize` -/

/-- **`e.principal.localize`**, in the two-sided quadratic form equivalent to the printed
`|A_{m-h}^{-1/2} G^t A_m G A_{m-h}^{-1/2} - I| ≤ D_z`: for every block vector `Q`,
`|Q · (G_{hbar}^t A_m G_{hbar} - A_{m-h}) Q| ≤ D_z · Q · A_{m-h} Q`. -/
theorem principal_localize [NeZero d] {nu : ℝ} (hnu : 0 < nu) (m h : ℕ) (R : TriadicCube d)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (Q : BlockVec d) :
    |blockVecDot Q (blockMatVecMul
        (ofFullBlockMat
          (toFullBlockMat
              (blockMatMul (blockMatTranspose (blockG (principalGauge m h R omega)))
                (blockMatMul (localizationCoarseAt nu m R omega)
                  (blockG (principalGauge m h R omega)))) -
            toFullBlockMat (localizationCoarseAt nu (m - h) R omega))) Q)| ≤
      localizationDz nu (m - h) m R omega *
        blockVecDot Q (blockMatVecMul (localizationCoarseAt nu (m - h) R omega) Q) := by
  have hP : blockMatVecMul (blockG (-principalGauge m h R omega))
      (blockMatVecMul (blockG (principalGauge m h R omega)) Q) = Q := by
    rw [← Homogenization.blockMatVecMul_blockMatMul, blockG_neg_mul,
      SuperdiffusionCLT.Section2.Carriers.blockMatVecMul_blockIdentity]
  have h0 := localization_display_e_hpoint hnu (Nat.sub_le m h) R
    (blockMatVecMul (blockG (principalGauge m h R omega)) Q) omega
  have e1 : localizationGaugeVector (m - h) m R
      (blockMatVecMul (blockG (principalGauge m h R omega)) Q) omega = Q := by
    change blockMatVecMul (blockG (-principalGauge m h R omega))
      (blockMatVecMul (blockG (principalGauge m h R omega)) Q) = Q
    exact hP
  unfold localizationT1CubeError localizationB at h0
  rw [e1] at h0
  exact h0

/-! ## `e.principal.Dz` -/

/-- The printed error `D_z`, `ν⁻¹ M + ν⁻² M²` with `M = ‖hshell - hbar_z‖_{L∞(z+cu_n)}`. -/
noncomputable def principalDz (nu : ℝ) (m h : ℕ) (R : TriadicCube d)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) : ℝ :=
  localizationDz nu (m - h) m R omega

theorem principalDz_nonneg {nu : ℝ} (hnu : 0 < nu) (m h : ℕ) (R : TriadicCube d)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) :
    0 ≤ principalDz nu m h R omega :=
  localizationD_nonneg hnu (m - h) m R omega

/-- **`e.principal.Dz`**: for a cube `R = z + cu_n` of scale `n ≤ m - h`,
`D_z ≤ C ν⁻¹ 3^n g + C² ν⁻² 3^{2n} g²` with `C = d √d` and `g` the derivative gauge
`∑_{k ∈ (m-h, m]} ‖∇ j_k‖_{L∞(z + cu_{m-h})}` of the shell field (translated to the cube). The gauge
`g` dominates the printed `‖∇ hshell‖_{L∞(z+cu_n)}`
(`localizationDisplayK_derivative_le`), and the same `g` is the observable of `e.nabla.kmn.Linfty`. -/
theorem principal_Dz_le {nu : ℝ} (hnu : 0 < nu) {n m h : ℕ} (hn : n ≤ m - h)
    (R : TriadicCube d) (hR : R.scale = (n : ℤ))
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) :
    principalDz nu m h R omega ≤
      nu⁻¹ * ((d : ℝ) * Real.sqrt d) * (3 : ℝ) ^ n *
          SuperdiffusionCLT.Section2.Estimates.Stream.finiteShellDerivGauge (m - h) m
            (SuperdiffusionCLT.Frozen.Assumptions.ShellField.translateSequence
              (cubeCenter R) omega) +
        nu⁻¹ ^ 2 * ((d : ℝ) * Real.sqrt d) ^ 2 * (3 : ℝ) ^ (2 * n) *
          SuperdiffusionCLT.Section2.Estimates.Stream.finiteShellDerivGauge (m - h) m
            (SuperdiffusionCLT.Frozen.Assumptions.ShellField.translateSequence
              (cubeCenter R) omega) ^ 2 := by
  have hM := localizationDisplayK_perturbSize_le hn m R hR omega
  have hM0 := localizationPerturbSize_nonneg (m - h) m R omega
  have hnu1 : 0 ≤ nu⁻¹ := (inv_pos.mpr hnu).le
  unfold principalDz localizationDz
  have h1 : nu⁻¹ * localizationPerturbSize (m - h) m R omega ≤
      nu⁻¹ * ((d : ℝ) * (Real.sqrt d * (3 : ℝ) ^ n *
        SuperdiffusionCLT.Section2.Estimates.Stream.finiteShellDerivGauge (m - h) m
          (SuperdiffusionCLT.Frozen.Assumptions.ShellField.translateSequence
            (cubeCenter R) omega))) := mul_le_mul_of_nonneg_left hM hnu1
  have h2 : localizationPerturbSize (m - h) m R omega ^ 2 ≤
      ((d : ℝ) * (Real.sqrt d * (3 : ℝ) ^ n *
        SuperdiffusionCLT.Section2.Estimates.Stream.finiteShellDerivGauge (m - h) m
          (SuperdiffusionCLT.Frozen.Assumptions.ShellField.translateSequence
            (cubeCenter R) omega))) ^ 2 := pow_le_pow_left₀ hM0 hM 2
  have h3 := mul_le_mul_of_nonneg_left h2 (pow_nonneg hnu1 2)
  have e2 : (3 : ℝ) ^ (2 * n) = ((3 : ℝ) ^ n) ^ 2 := by rw [pow_mul']
  rw [e2]
  linarith only [h1, h3]

/-! ## `e.principal.switch` -/

/-- **`e.principal.switch`**: pointwise in the environment,
`P · A_m(z+cu_n) P ≤ (1 + D_z) P̂ · A_{m-h}(z+cu_n) P̂` with `P̂ = G_{-hbar_z} P`. -/
theorem principal_switch [NeZero d] {nu : ℝ} (hnu : 0 < nu) (m h : ℕ) (R : TriadicCube d)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (P : BlockVec d) :
    blockVecDot P (blockMatVecMul (localizationCoarseAt nu m R omega) P) ≤
      (1 + principalDz nu m h R omega) *
        blockVecDot (principalPhat m h R omega P)
          (blockMatVecMul (localizationCoarseAt nu (m - h) R omega)
            (principalPhat m h R omega P)) := by
  have hid := blockVecDot_blockG_conj_eq (localizationCoarseAt nu m R omega)
    (principalGauge m h R omega) P
  have hloc := principal_localize hnu m h R omega (principalPhat m h R omega P)
  have hs := blockVecDot_blockMatVecMul_ofFullBlockMat_sub (blockMatMul (blockMatTranspose (blockG (principalGauge m h R omega)))
    (blockMatMul (localizationCoarseAt nu m R omega) (blockG (principalGauge m h R omega))))
    (localizationCoarseAt nu (m - h) R omega) (principalPhat m h R omega P)
  have hpe : principalPhat m h R omega P =
      blockMatVecMul (blockG (-principalGauge m h R omega)) P := rfl
  rw [hs] at hloc
  rw [hid]
  rw [hpe] at hloc ⊢
  have := (abs_le.mp hloc).2
  unfold principalDz
  linarith only [this]

/-! ## Satisfiability -/

/-- The hypotheses are met: `d = 1`, `ν = 1`, `m = h = 1`, `n = 0`, the unit origin cube and the
zero shell sequence. -/
example :
    principalDz (1 : ℝ) 1 1 (originCube 1 (0 : ℤ))
        (SuperdiffusionCLT.Assumptions.ShellLaw.zeroShellSeq 1) ≤
      (1 : ℝ)⁻¹ * ((1 : ℝ) * Real.sqrt 1) * (3 : ℝ) ^ 0 *
          SuperdiffusionCLT.Section2.Estimates.Stream.finiteShellDerivGauge (1 - 1) 1
            (SuperdiffusionCLT.Frozen.Assumptions.ShellField.translateSequence
              (cubeCenter (originCube 1 (0 : ℤ)))
              (SuperdiffusionCLT.Assumptions.ShellLaw.zeroShellSeq 1)) +
        (1 : ℝ)⁻¹ ^ 2 * ((1 : ℝ) * Real.sqrt 1) ^ 2 * (3 : ℝ) ^ (2 * 0) *
          SuperdiffusionCLT.Section2.Estimates.Stream.finiteShellDerivGauge (1 - 1) 1
            (SuperdiffusionCLT.Frozen.Assumptions.ShellField.translateSequence
              (cubeCenter (originCube 1 (0 : ℤ)))
              (SuperdiffusionCLT.Assumptions.ShellLaw.zeroShellSeq 1)) ^ 2 :=
  by
  exact_mod_cast principal_Dz_le (d := 1) one_pos (n := 0) (m := 1) (h := 1) (Nat.zero_le _)
    (originCube 1 (0 : ℤ)) rfl (SuperdiffusionCLT.Assumptions.ShellLaw.zeroShellSeq 1)

end SuperdiffusionCLT.Section5
