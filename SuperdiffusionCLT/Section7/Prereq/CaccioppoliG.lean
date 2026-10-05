/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.CaccioppoliF
public import SuperdiffusionCLT.Section7.Prereq.CaccioppoliE

/-!
# The interior Caccioppoli core at one scale

The deterministic core `ca1_interior_det` for the field `ν Id + kf (y + ·)` on `□_m`, with the grid
depth `h = m - n` and the coefficients of the shifted blackbox bounds; the scale-separation
inequalities are derived from `τ (m/ν)^4 ≤ 1/m`.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem ca1w_scale [NeZero d] (hd : 2 ≤ d) {C1 ν S ρ δ : ℝ} (m n h : ℕ) (hnh : n + h = m)
    (hh : 3 ≤ h) (kf : Vec d → Mat d) (y : Vec d) (hC1 : 1 ≤ C1) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hνS : ν ≤ S) (hSm : S ≤ m) (hρ1 : ρ ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hm : 1 + 4 * (d : ℝ) ≤ m) (hm5 : 5 * C1 ^ 2 ≤ m)
    (hmaster : (3 : ℝ) ^ (n : ℤ) / (3 : ℝ) ^ (m : ℤ) * ((m : ℝ) / ν) ^ 4 ≤ (m : ℝ)⁻¹)
    (hell : ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (openCubeSet (originCube d (m : ℤ)))
      (fun x => ν • (1 : Mat d) + kf (y + x)))
    (hsym : ∀ x, symmPart (ν • (1 : Mat d) + kf x) = ν • (1 : Mat d))
    (hop : ∀ x ∈ openCubeSet (originCube d (m : ℤ)), ∀ v : Vec d,
      eucNorm (matVecMul (ν • (1 : Mat d) + kf (y + x)) v) ≤ (ν + (m : ℝ) ^ (1 + ρ)) * eucNorm v)
    (hBB0 : ∀ k : Fin d → ℤ,
      (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) '' cubeSet (originCube d (n : ℤ)) ⊆
        cubeSet (originCube d (m : ℤ)) →
      ∀ (u : H1Function (openCubeSet (originCube d (n : ℤ)))) (f : Vec d → ℝ),
      IsWeakSolutionOn (fun x => ν • (1 : Mat d) +
          kf (y + (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))
        (openCubeSet (originCube d (n : ℤ))) u f (fun _ => 0) →
      ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo (originCube d (n : ℤ))
          (1 / 4 : ℝ) (fun x => matVecMul (ν • (1 : Mat d) +
            kf (y + (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) - S • (1 : Mat d)) (u.grad x))) ≤
        ENNReal.ofReal (C1 * Real.sqrt S * δ * Real.sqrt ν) *
            SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (n : ℤ)) 2
            (fun x => Real.sqrt (vecNormSq (u.grad x))) +
          ENNReal.ofReal ((C1 * Real.sqrt S * δ * Real.sqrt ν + C1 * (|ν - S| + (m : ℝ) ^ (1 + ρ))) *
              (C1 * (3 : ℝ) ^ (n : ℤ) / ν)) *
            SuperdiffusionCLT.Section2.Norms.cubeLpENorm
            (originCube d (n : ℤ)) (ENNReal.ofReal (sobStar d)).conjExponent f ∧
      ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo (originCube d (n : ℤ))
          (1 / 4 : ℝ) u.grad) ≤
        ENNReal.ofReal (C1 * (Real.sqrt S)⁻¹ * Real.sqrt ν) *
            SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (n : ℤ)) 2
            (fun x => Real.sqrt (vecNormSq (u.grad x))) +
          ENNReal.ofReal ((C1 * (Real.sqrt S)⁻¹ * Real.sqrt ν + C1) * (C1 * (3 : ℝ) ^ (n : ℤ) / ν)) *
            SuperdiffusionCLT.Section2.Norms.cubeLpENorm
            (originCube d (n : ℤ)) (ENNReal.ofReal (sobStar d)).conjExponent f)
    (u : H1Function (openCubeSet (originCube d (m : ℤ)))) {f : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict (openCubeSet (originCube d (m : ℤ)))))
    (hu : IsWeakSolutionOn (fun x => ν • (1 : Mat d) + kf (y + x))
      (openCubeSet (originCube d (m : ℤ))) u f (fun _ => 0)) (c : ℝ) :
    ν * cubeLpNorm (originCube d ((m : ℤ) - 1)) (2 : ℝ≥0∞) (fun x => Real.sqrt (vecNormSq (u.grad x))) ^ 2 ≤
      ca1_Cfin d (4 * C1 ^ 2) * (S * (3 : ℝ) ^ (-2 * (m : ℤ)) *
          cubeLpNorm (originCube d (m : ℤ)) (2 : ℝ≥0∞) (fun x => u.toFun x - c) ^ 2 +
        S⁻¹ * (3 : ℝ) ^ (2 * (m : ℤ)) * cubeLpNorm (originCube d (m : ℤ)) (2 : ℝ≥0∞) f ^ 2) := by
  have hC0 : 0 < C1 := by linarith only [hC1]
  have hS0 : 0 < S := lt_of_lt_of_le hν hνS
  have hm1 : (1 : ℝ) ≤ m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith only [hm, this]
  have hm0 : (0 : ℝ) < m := by linarith only [hm1]
  have hx : 0 ≤ (3 : ℝ) ^ (n : ℤ) / (3 : ℝ) ^ (m : ℤ) := by positivity
  have hT : (0 : ℝ) < (3 : ℝ) ^ (m : ℤ) := by positivity
  have hTn : (3 : ℝ) ^ (n : ℤ) = (3 : ℝ) ^ (n : ℤ) / (3 : ℝ) ^ (m : ℤ) * (3 : ℝ) ^ (m : ℤ) := by
    field_simp
  have hnm : (m : ℤ) - (h : ℤ) = (n : ℤ) := by
    have : (m : ℤ) = n + h := by exact_mod_cast hnh.symm
    omega
  obtain ⟨hcoef1, hcoef2⟩ := ca1w_coef_ineq (C1 := C1) (ν := ν) (S := S) (m := m)
    (x := (3 : ℝ) ^ (n : ℤ) / (3 : ℝ) ^ (m : ℤ)) (δ := δ) (ρ := ρ) (T := (3 : ℝ) ^ (m : ℤ))
    (Tn := (3 : ℝ) ^ (n : ℤ)) hC1 hν hν1 hνS hSm hm5 hm1 hx hmaster hδ0 hδ1 hρ1 hT hTn
  have hρm : (0 : ℝ) ≤ (m : ℝ) ^ (1 + ρ) := by positivity
  obtain ⟨htau1, htau2⟩ := ca1w_tau_ineq d (S := S) (m := m)
    (x := (3 : ℝ) ^ (n : ℤ) / (3 : ℝ) ^ (m : ℤ)) (Λ := ν + (m : ℝ) ^ (1 + ρ)) (ρ := ρ) hν hν1 hSm hS0.le hm hx hmaster
    (by positivity) le_rfl hρ1
  obtain ⟨lam, Lam, hEll⟩ := hell
  have hτs : (3 : ℝ) ^ ((m : ℤ) - (h : ℤ)) / (3 : ℝ) ^ (m : ℤ) * (S / ν) ^ 2 ≤ 1 := by
    rw [hnm]; exact htau1
  have hτΞ : (3 : ℝ) ^ ((m : ℤ) - (h : ℤ)) / (3 : ℝ) ^ (m : ℤ) *
      (1 + d * (ν + (m : ℝ) ^ (1 + ρ)) ^ 2 / ν ^ 2) ≤ 1 := by
    rw [hnm]; exact htau2
  have hBB := ca1w_hBB m n h hnh (ν := ν) (S := S)
    (α1 := C1 * Real.sqrt S * δ * Real.sqrt ν)
    (β1 := (C1 * Real.sqrt S * δ * Real.sqrt ν + C1 * (|ν - S| + (m : ℝ) ^ (1 + ρ))) *
      (C1 * (3 : ℝ) ^ (n : ℤ) / ν))
    (α2 := C1 * (Real.sqrt S)⁻¹ * Real.sqrt ν)
    (β2 := (C1 * (Real.sqrt S)⁻¹ * Real.sqrt ν + C1) * (C1 * (3 : ℝ) ^ (n : ℤ) / ν)) kf y hBB0
  exact ca1_interior_det hd (m : ℤ) h hh hEll hν (by positivity) (fun x _ => hsym (y + x)) hop hνS
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) hcoef1 hcoef2 hτs hτΞ
    u hf hu hBB c

end SuperdiffusionCLT.Section7
