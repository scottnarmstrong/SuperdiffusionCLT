/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Principal.LocalizeSwitch
public import SuperdiffusionCLT.Section5.Neumann.NeumannInput

/-!
# The pre-average and `P̂` displays of the principal term

Displays `e.principal.Phat` and `e.principal.pre.average`, for one subcube
`Q = z + cu_n`. The expectation `E` is the Lebesgue integral in `ℝ≥0∞` of the positive part, so no
integrability is needed; the sample space is `ShellSeq d` with law `P`.

* `ahomSqrtApply_principalPhat`: `bfAhom^{1/2} P̂_z = (e_{D,z}, e_{N,z} - shom^{-1} hbar_z e_{D,z})`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization Homogenization.Book.Ch02 MeasureTheory
open SuperdiffusionCLT.Section2.Localization
open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)

variable {d : ℕ}

/-- `e_{D,z} = e' + (∇w_D)_{z+cu_n}`. -/
noncomputable def principalED (Q : TriadicCube d) (e' : Vec d) (gD : Vec d → Vec d) : Vec d :=
  e' + volumeAverageVec (cubeSet Q) gD

/-- `e_{N,z} = e + (∇w_N + shom^{-1} hshell e')_{z+cu_n}`, with `gN` the whole field
`∇w_N + shom^{-1} hshell e'`. -/
noncomputable def principalEN (Q : TriadicCube d) (e : Vec d) (gN : Vec d → Vec d) : Vec d :=
  e + volumeAverageVec (cubeSet Q) gN

theorem blockSlope_eq_ahomInvSqrtApply [NeZero d] (nu : ℝ) (L : ℕ)
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (Q : TriadicCube d) (e e' : Vec d) (gD gN : Vec d → Vec d) :
    blockSlope nu L P Q e e' gD gN =
      ahomInvSqrtApply nu L P (principalED Q e' gD, principalEN Q e gN) := rfl

private theorem matVecMul_one_pm (x : Vec d) : matVecMul (1 : Mat d) x = x := by
  funext i; simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]

private theorem matVecMul_zero_pm (x : Vec d) : matVecMul (0 : Mat d) x = 0 := by
  funext i; simp [matVecMul]

private theorem matVecMul_vec_zero_pm (g : Mat d) : matVecMul g (0 : Vec d) = 0 := by
  funext i; simp [matVecMul]

private theorem matVecMul_neg_pm (g : Mat d) (x : Vec d) :
    matVecMul (-g) x = -matVecMul g x := by
  funext i; simp [matVecMul, Finset.sum_neg_distrib]

private theorem matVecMul_smul_pm (g : Mat d) (c : ℝ) (x : Vec d) :
    matVecMul g (c • x) = c • matVecMul g x := by
  funext i
  simp only [matVecMul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **`e.principal.Phat`**: `bfAhom^{1/2} P̂_z = (e_{D,z}, e_{N,z} - shom^{-1} hbar_z e_{D,z})`,
for every sample and every pair of gradient fields. -/
theorem ahomSqrtApply_principalPhat [NeZero d] (nu : ℝ) (m h : ℕ)
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (hσ : 0 < sigmaBarInfinite nu (m - h) P) (Q : TriadicCube d)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (e e' : Vec d)
    (gD gN : Vec d → Vec d) :
    ahomSqrtApply nu (m - h) P
        (principalPhat m h Q omega (blockSlope nu (m - h) P Q e e' gD gN)) =
      (principalED Q e' gD,
        principalEN Q e gN - (sigmaBarInfinite nu (m - h) P)⁻¹ •
          matVecMul (principalGauge m h Q omega) (principalED Q e' gD)) := by
  set s := sigmaBarInfinite nu (m - h) P with hs
  have h1 : s ^ ((1 : ℝ) / 2) * s ^ (-(1 : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add hσ]; norm_num
  have h2 : s ^ (-(1 : ℝ) / 2) * s ^ (-(1 : ℝ) / 2) = s⁻¹ := by
    rw [← Real.rpow_add hσ, show -(1 : ℝ) / 2 + -(1 : ℝ) / 2 = -1 by norm_num,
      Real.rpow_neg_one]
  have h3 : s ^ (-(1 : ℝ) / 2) * s ^ ((1 : ℝ) / 2) = 1 := by rw [mul_comm]; exact h1
  unfold ahomSqrtApply principalPhat
  rw [blockSlope_eq_ahomInvSqrtApply]
  unfold ahomInvSqrtApply gaugeMat blockMatVecMul
  simp only [matVecMul_one_pm, matVecMul_zero_pm, matVecMul_neg_pm, matVecMul_smul_pm,
    ← hs]
  refine Prod.ext ?_ ?_
  · simp only [smul_zero, add_zero, smul_smul, h1, one_smul]
  · simp only [smul_add, smul_neg, smul_smul, h3, one_smul]
    rw [h2]
    abel

/-- `|bfAhom^{1/2} P̂_z|²`, the squared Euclidean length of a block vector. -/
noncomputable def blockLenSq (X : BlockVec d) : ℝ := vecNormSq X.1 + vecNormSq X.2

/-! ## Satisfiability -/

private theorem blockSlope_zero [NeZero d] (nu : ℝ) (L : ℕ)
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (Q : TriadicCube d) :
    blockSlope nu L P Q 0 0 (fun _ => 0) (fun _ => 0) = (0, 0) := by
  have h0 : volumeAverageVec (cubeSet Q) (fun _ : Vec d => (0 : Vec d)) = 0 := by
    funext i; simp [volumeAverageVec, volumeAverage]
  unfold blockSlope ahomInvSqrtApply
  rw [h0]
  simp

/-- The hypothesis of the pre-average display `e.principal.pre.average` is met, by the zero slope
(`e = e' = 0`, zero gradient fields, `ε = 0`): then `P̂_z = 0` and both sides vanish. -/
example [NeZero d] {nu : ℝ} (m h : ℕ)
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (Q : TriadicCube d) :
    ∫⁻ omega, ENNReal.ofReal ((1 + principalDz nu m h Q omega) *
          blockVecDot
            (principalPhat m h Q omega
              (blockSlope nu (m - h) P Q 0 0 ((fun _ _ => 0) omega) ((fun _ _ => 0) omega)))
            (blockMatVecMul (localizationCoarseAt nu (m - h) Q omega)
              (principalPhat m h Q omega
                (blockSlope nu (m - h) P Q 0 0 ((fun _ _ => 0) omega)
                  ((fun _ _ => 0) omega))))) ∂P.toMeasure ≤
        ENNReal.ofReal (1 + 0) *
          ∫⁻ omega, ENNReal.ofReal ((1 + principalDz nu m h Q omega) *
            blockLenSq (ahomSqrtApply nu (m - h) P
              (principalPhat m h Q omega
                (blockSlope nu (m - h) P Q 0 0 ((fun _ _ => 0) omega)
                  ((fun _ _ => 0) omega))))) ∂P.toMeasure := by
  have hz : ∀ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
      principalPhat m h Q omega (blockSlope nu (m - h) P Q 0 0 (fun _ => 0) (fun _ => 0)) =
        (0, 0) := by
    intro omega
    rw [blockSlope_zero]
    unfold principalPhat blockMatVecMul gaugeMat
    simp only [matVecMul_vec_zero_pm, add_zero]
  simp only [hz, blockVecDot, vecDot, blockMatVecMul]
  simp

end SuperdiffusionCLT.Section5
