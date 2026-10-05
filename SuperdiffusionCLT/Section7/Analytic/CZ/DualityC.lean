/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.CZ.DualityB

/-!
# The adjoint identity and the `W^{-1,p}` bound

For `φ` solving `∫∇φ·∇v = ∫ h v + ∫ F·∇v` and `ψ` solving `∫∇ψ·∇v = ∫ G·∇v` (both tested
against `H¹₀(U)`), symmetry of the Laplacian gives `∫ G·∇φ = ∫ h ψ + ∫ F·∇ψ`. The scalar pairing
is bounded by `wMinusOneBar`; no integrability of `h·ψ` is needed because the definition of
`wMinusOneBar` uses the same (possibly zero) Bochner integral on both sides.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem p14_matVecMul_one (v : Vec d) : matVecMul (1 : Mat d) v = v := by
  funext i
  simp [matVecMul, Matrix.one_apply]

theorem p14_vecDot_comm (a b : Vec d) : vecDot a b = vecDot b a := by
  simp only [vecDot]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- **Adjoint identity** for the Laplacian. -/
theorem p14_adjoint_identity {U : Set (Vec d)} {h : Vec d → ℝ} {F G : Vec d → Vec d}
    (φ ψ : H10Function U)
    (hφ : IsWeakSolutionOn (fun _ => (1 : Mat d)) U φ.toH1Function h F)
    (hψ : IsWeakSolutionOn (fun _ => (1 : Mat d)) U ψ.toH1Function 0 G) :
    ∫ x in U, vecDot (G x) (φ.toH1Function.grad x) =
      (∫ x in U, h x * ψ.toH1Function.toFun x) +
        ∫ x in U, vecDot (F x) (ψ.toH1Function.grad x) := by
  have h1 := hψ φ
  have h2 := hφ ψ
  simp only [p14_matVecMul_one, Pi.zero_apply, zero_mul, integral_zero, zero_add] at h1 h2
  rw [← h1, ← h2]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => p14_vecDot_comm _ _)

theorem p14_lpBar_smul (V : Set (Vec d)) (q : ℝ≥0∞) (t : ℝ) (g : Vec d → Vec d) :
    lpBar V q (fun x => t • g x) = ENNReal.ofReal |t| * lpBar V q g := by
  unfold lpBar
  have := eLpNorm_const_smul (μ := ((volume V)⁻¹) • volume.restrict V) (p := q) t g
  rw [show (fun x => t • g x) = t • g from rfl, this, ← ofReal_norm, Real.norm_eq_abs]

/-- The pairing with `h` is bounded by `wMinusOneBar`. -/
theorem p14_wMinusOne_bound (U : Set (Vec d)) (p : ℝ≥0∞) (h : Vec d → ℝ) (ψ : H10Function U)
    (hw : wMinusOneBar U p h ≠ ∞) (hL : lpBar U p.conjExponent ψ.toH1Function.grad ≠ ∞) :
    ENNReal.ofReal |(volume U).toReal⁻¹ * ∫ x in U, h x * ψ.toH1Function.toFun x| ≤
      wMinusOneBar U p h * lpBar U p.conjExponent ψ.toH1Function.grad := by
  set a := (volume U).toReal⁻¹ * ∫ x in U, h x * ψ.toH1Function.toFun x with ha
  set L := lpBar U p.conjExponent ψ.toH1Function.grad with hLdef
  set w := wMinusOneBar U p h with hwdef
  have hscale : ∀ t : ℝ, ENNReal.ofReal |t| * L ≤ 1 → ENNReal.ofReal |t * a| ≤ w := by
    intro t ht
    have hl : lpBar U p.conjExponent (t • ψ).toH1Function.grad ≤ 1 := by
      have : (t • ψ).toH1Function.grad = fun x => t • ψ.toH1Function.grad x := rfl
      rw [this, p14_lpBar_smul]
      exact ht
    have hle := le_iSup₂ (f := fun (ψ' : H10Function U)
      (_ : lpBar U p.conjExponent ψ'.toH1Function.grad ≤ 1) =>
        ENNReal.ofReal |(volume U).toReal⁻¹ * ∫ x in U, h x * ψ'.toH1Function.toFun x|)
      (t • ψ) hl
    have e : (volume U).toReal⁻¹ * ∫ x in U, h x * (t • ψ).toH1Function.toFun x = t * a := by
      have : (t • ψ).toH1Function.toFun = fun x => t * ψ.toH1Function.toFun x := rfl
      rw [this, ha]
      have : ∫ x in U, h x * (t * ψ.toH1Function.toFun x) =
          t * ∫ x in U, h x * ψ.toH1Function.toFun x := by
        rw [← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
      rw [this]
      ring
    rw [e] at hle
    exact hle
  by_cases hL0 : L = 0
  · have : a = 0 := by
      by_contra hne
      have hpos : 0 < |a| := abs_pos.mpr hne
      have h1 := hscale ((w.toReal + 1) / |a|) (by rw [hL0, mul_zero]; exact zero_le)
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (w.toReal + 1) / |a|),
        div_mul_cancel₀ _ hpos.ne'] at h1
      have h2 : ENNReal.ofReal (w.toReal + 1) ≤ ENNReal.ofReal w.toReal := by
        rw [ENNReal.ofReal_toReal hw]
        exact h1
      have h3 := (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).1 h2
      linarith only [h3]
    rw [this]
    simp
  · have hLpos : 0 < L.toReal := ENNReal.toReal_pos hL0 hL
    have ht : ENNReal.ofReal |L.toReal⁻¹| * L ≤ 1 := by
      rw [abs_of_pos (inv_pos.2 hLpos), ENNReal.ofReal_inv_of_pos hLpos,
        ENNReal.ofReal_toReal hL, ENNReal.inv_mul_cancel hL0 hL]
    have h1 := hscale _ ht
    rw [abs_mul, abs_of_pos (inv_pos.2 hLpos), ENNReal.ofReal_mul (inv_pos.2 hLpos).le,
      ENNReal.ofReal_inv_of_pos hLpos, ENNReal.ofReal_toReal hL] at h1
    calc ENNReal.ofReal |a| = L * (L⁻¹ * ENNReal.ofReal |a|) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel hL0 hL, one_mul]
      _ ≤ L * w := by gcongr
      _ = w * L := mul_comm _ _

end SuperdiffusionCLT.Section7
