/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.CaccioppoliBdryP

/-!
# The deterministic boundary Caccioppoli inequality

On the cube `□_m` cut by an open set `W`, a weak solution `u` of `-∇·(A∇u) = f` in `D = □_m ∩ W`
whose difference with a `C²` datum `γ` has a localized zero trace satisfies
`ν ∫_{□_{m-1} ∩ W} |∇u|² ≤ C |□_m| (S 3^{-2m} ‖u - γ‖² + S⁻¹ 3^{2m} ‖f‖² + S G1² + S ℓ² G2²)`
(norms normalized by `|□_m|`), under the hypotheses of the interior inequality, the pointwise bounds
`G1`, `G2` of `∇γ` and `∇²γ`, and the smallness of the part `B` of the support zone not covered by
good grid cubes.
-/

@[expose] public section

open scoped ENNReal NNReal
open MeasureTheory Filter Topology Homogenization

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The constant of the algebra of the boundary Caccioppoli inequality. -/
noncomputable def ca2_Cal (d : ℕ) (Cα : ℝ) : ℝ :=
  16 / 11 * (1 / 2 + 2 * (4 * (12 * 64 ^ d * 64 ^ d)) ^ 2 * Cα +
    2 * (8 * cubeBesovW12EmbeddingConstant d * (12 * 64 ^ d * 64 ^ d) * ((125 / 729 : ℝ) ^ d)⁻¹) ^ 2 * Cα *
      ca2_c8 +
    (ca2_c8 + (32 * cubeBesovW12EmbeddingConstant d * Real.sqrt d * (ca1_K0 d : ℝ) *
      ((125 / 729 : ℝ) ^ d)⁻¹) ^ 2 * Cα) / 2 + 48 * 64 ^ d / 2 +
    96 * 64 ^ d * cubeBesovW12EmbeddingConstant d * ((125 / 729 : ℝ) ^ d)⁻¹ * (1 + ca2_c8) / 2 +
    32 * cubeBesovW12EmbeddingConstant d * Real.sqrt d * (ca1_K0 d : ℝ) / 2 +
    48 * Real.sqrt d * 16 ^ 5 * ((125 / 729 : ℝ) ^ d)⁻¹ * (1 + ca2_c8) / 2 + 1 * ca2_c8 + 1 / 8)

/-- The constant of the deterministic boundary Caccioppoli inequality. -/
noncomputable def ca2_Cdet (d : ℕ) (Cα : ℝ) : ℝ :=
  (((125 / 729 : ℝ) ^ d)⁻¹) ^ 2 * ca2_Cal d Cα *
    (3 + 4 * (1 + 192 * cubeBesovW12EmbeddingConstant d * Real.sqrt d) ^ 2 +
      16 * cubeBesovW12EmbeddingConstant d ^ 2 * d)

/-- The algebra of the deterministic boundary Caccioppoli inequality, in normalized variables. -/
theorem ca2_assemble (d : ℕ) (hd : 1 ≤ d) (Cα : ℝ) (hCα : 0 ≤ Cα) {L ℓ ν Λ S α1 β1 α2 β2 τ G1 Kη : ℝ}
    {G Gc Wn Fn gp Bq : ℝ} (hL : 0 < L) (hν : 0 < ν) (hΛ : 0 ≤ Λ) (hνS : ν ≤ S) (hα1 : 0 ≤ α1)
    (hβ1 : 0 ≤ β1) (hα2 : 0 ≤ α2) (hβ2 : 0 ≤ β2) (hα : (S * α2 + α1) ^ 2 ≤ Cα * S * ν)
    (hb : S * β2 + β1 ≤ L) (hℓ0 : 0 < ℓ) (hτ : ℓ / L ≤ τ) (hτs : τ * (S / ν) ^ 2 ≤ 1)
    (hτΞ : τ * (1 + d * Λ ^ 2 / ν ^ 2) ≤ 1) (hKη : Kη = (ca1_K0 d : ℝ) * ((L / 4)⁻¹) ^ 2)
    (hG0 : 0 ≤ G) (hGc0 : 0 ≤ Gc) (hWn0 : 0 ≤ Wn) (hFn0 : 0 ≤ Fn) (hgp0 : 0 ≤ gp) (hG1 : 0 ≤ G1)
    (hgp : L * G1 ≤ 48 * gp)
    (hM1 : ν * G ^ 2 ≤ Fn * Wn +
        ((S * α2 + α1) * ((12 * 64 ^ d * 64 ^ d * (L / 4)⁻¹ * G) * (Wn + gp)) +
        2 * cubeBesovW12EmbeddingConstant d * ℓ * (S * α2 + α1) *
          ((12 * 64 ^ d * 64 ^ d * (L / 4)⁻¹ * G) * (((125 / 729 : ℝ) ^ d)⁻¹ * Gc)) +
        2 * cubeBesovW12EmbeddingConstant d * ℓ * (Real.sqrt d * Kη) * (S * α2 + α1) *
          ((((125 / 729 : ℝ) ^ d)⁻¹ * Gc) * (Wn + gp)) +
        (S * β2 + β1) * (12 * 64 ^ d * (L / 4)⁻¹) * (Fn * (Wn + gp)) +
        2 * cubeBesovW12EmbeddingConstant d * ℓ * (S * β2 + β1) * (12 * 64 ^ d * (L / 4)⁻¹) *
          (Fn * (((125 / 729 : ℝ) ^ d)⁻¹ * Gc)) +
        2 * cubeBesovW12EmbeddingConstant d * ℓ * (Real.sqrt d * Kη) * (S * β2 + β1) *
          (Fn * (Wn + gp))) + Bq)
    (hB : Bq ≤ ν * τ * Gc ^ 2 + ν / 16 * (G ^ 2 + G1 ^ 2 + (Wn / L) ^ 2))
    (hcr : ν * Gc ^ 2 ≤ ca2_c8 * (ν⁻¹ * (L * Fn) ^ 2 + ν * ((Wn + 48 * gp) / L) ^ 2 +
      d * Λ ^ 2 * ν⁻¹ * ((Wn + 48 * gp) / L) ^ 2)) :
    ν * G ^ 2 ≤ ca2_Cal d Cα * (S * ((Wn + 48 * gp) / L) ^ 2 + S⁻¹ * (L * Fn) ^ 2) := by
  have hS0 : 0 ≤ S := hν.le.trans hνS
  have hc0 : 0 < ((125 / 729 : ℝ) ^ d) := by positivity
  have hKb := cubeBesovW12EmbeddingConstant_nonneg d
  have hKη0 : 0 ≤ Kη := by rw [hKη]; positivity
  have hd0 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hτpos : 0 < τ := lt_of_lt_of_le (by positivity) hτ
  have hα0 : 0 ≤ S * α2 + α1 := by positivity
  have hβ0 : 0 ≤ S * β2 + β1 := by positivity
  have hmono : Fn * Wn +
        ((S * α2 + α1) * ((12 * 64 ^ d * 64 ^ d * (L / 4)⁻¹ * G) * (Wn + gp)) +
        2 * cubeBesovW12EmbeddingConstant d * ℓ * (S * α2 + α1) *
          ((12 * 64 ^ d * 64 ^ d * (L / 4)⁻¹ * G) * (((125 / 729 : ℝ) ^ d)⁻¹ * Gc)) +
        2 * cubeBesovW12EmbeddingConstant d * ℓ * (Real.sqrt d * Kη) * (S * α2 + α1) *
          ((((125 / 729 : ℝ) ^ d)⁻¹ * Gc) * (Wn + gp)) +
        (S * β2 + β1) * (12 * 64 ^ d * (L / 4)⁻¹) * (Fn * (Wn + gp)) +
        2 * cubeBesovW12EmbeddingConstant d * ℓ * (S * β2 + β1) * (12 * 64 ^ d * (L / 4)⁻¹) *
          (Fn * (((125 / 729 : ℝ) ^ d)⁻¹ * Gc)) +
        2 * cubeBesovW12EmbeddingConstant d * ℓ * (Real.sqrt d * Kη) * (S * β2 + β1) *
          (Fn * (Wn + gp))) ≤
      Fn * (Wn + 48 * gp) +
        ((S * α2 + α1) * ((12 * 64 ^ d * 64 ^ d * (L / 4)⁻¹ * G) * (Wn + 48 * gp)) +
        2 * cubeBesovW12EmbeddingConstant d * ℓ * (S * α2 + α1) *
          ((12 * 64 ^ d * 64 ^ d * (L / 4)⁻¹ * G) * (((125 / 729 : ℝ) ^ d)⁻¹ * Gc)) +
        2 * cubeBesovW12EmbeddingConstant d * ℓ * (Real.sqrt d * Kη) * (S * α2 + α1) *
          ((((125 / 729 : ℝ) ^ d)⁻¹ * Gc) * (Wn + 48 * gp)) +
        (S * β2 + β1) * (12 * 64 ^ d * (L / 4)⁻¹) * (Fn * (Wn + 48 * gp)) +
        2 * cubeBesovW12EmbeddingConstant d * ℓ * (S * β2 + β1) * (12 * 64 ^ d * (L / 4)⁻¹) *
          (Fn * (((125 / 729 : ℝ) ^ d)⁻¹ * Gc)) +
        2 * cubeBesovW12EmbeddingConstant d * ℓ * (Real.sqrt d * Kη) * (S * β2 + β1) *
          (Fn * (Wn + 48 * gp))) := by
    have h1 : Wn ≤ Wn + 48 * gp := by linarith only [hgp0]
    have h2 : Wn + gp ≤ Wn + 48 * gp := by linarith only [hgp0]
    gcongr
  have hEq := ca1_rhs_eq (d := d) (L := L) (ℓ := ℓ) (K := cubeBesovW12EmbeddingConstant d)
    (K0 := (ca1_K0 d : ℝ)) (c0 := ((125 / 729 : ℝ) ^ d)) (D := (d : ℝ)) (S := S) (α1 := α1) (α2 := α2)
    (β1 := β1) (β2 := β2) (Λ := Λ) (W := Wn + 48 * gp) (Fg := Fn) (G := G) (Gc := Gc) hL hc0
  rw [← hKη] at hEq
  have hΛt : 0 ≤ (Λ * (Real.sqrt d * (12 * (L / 4)⁻¹ * (4 * ℓ / (L / 4)) ^ 5))) *
      (((125 / 729 : ℝ) ^ d)⁻¹ * Gc * (Wn + 48 * gp)) := by positivity
  have hLℓ : 0 ≤ ℓ / L := by positivity
  have hw0 : 0 ≤ (Wn + 48 * gp) / L := by positivity
  -- the normalized form with `τ`
  have hEτ : (L * Fn) * ((Wn + 48 * gp) / L) + (4 * (12 * 64 ^ d * 64 ^ d)) * (S * α2 + α1) * G * ((Wn + 48 * gp) / L) +
      (8 * cubeBesovW12EmbeddingConstant d * (12 * 64 ^ d * 64 ^ d) * ((125 / 729 : ℝ) ^ d)⁻¹) * (ℓ / L) *
        (S * α2 + α1) * G * Gc +
      (32 * cubeBesovW12EmbeddingConstant d * Real.sqrt d * (ca1_K0 d : ℝ) * ((125 / 729 : ℝ) ^ d)⁻¹) * (ℓ / L) *
        (S * α2 + α1) * Gc * ((Wn + 48 * gp) / L) +
      (48 * 64 ^ d) * ((S * β2 + β1) / L) * (L * Fn) * ((Wn + 48 * gp) / L) +
      (96 * 64 ^ d * cubeBesovW12EmbeddingConstant d * ((125 / 729 : ℝ) ^ d)⁻¹) * (ℓ / L) *
        ((S * β2 + β1) / L) * (L * Fn) * Gc +
      (32 * cubeBesovW12EmbeddingConstant d * Real.sqrt d * (ca1_K0 d : ℝ)) * (ℓ / L) * ((S * β2 + β1) / L) *
        (L * Fn) * ((Wn + 48 * gp) / L) +
      (48 * Real.sqrt d * 16 ^ 5 * ((125 / 729 : ℝ) ^ d)⁻¹) * Λ * (ℓ / L) ^ 5 * Gc * ((Wn + 48 * gp) / L) ≤
      (L * Fn) * ((Wn + 48 * gp) / L) + (4 * (12 * 64 ^ d * 64 ^ d)) * (S * α2 + α1) * G * ((Wn + 48 * gp) / L) +
      (8 * cubeBesovW12EmbeddingConstant d * (12 * 64 ^ d * 64 ^ d) * ((125 / 729 : ℝ) ^ d)⁻¹) * τ *
        (S * α2 + α1) * G * Gc +
      (32 * cubeBesovW12EmbeddingConstant d * Real.sqrt d * (ca1_K0 d : ℝ) * ((125 / 729 : ℝ) ^ d)⁻¹) * τ *
        (S * α2 + α1) * Gc * ((Wn + 48 * gp) / L) +
      (48 * 64 ^ d) * ((S * β2 + β1) / L) * (L * Fn) * ((Wn + 48 * gp) / L) +
      (96 * 64 ^ d * cubeBesovW12EmbeddingConstant d * ((125 / 729 : ℝ) ^ d)⁻¹) * τ *
        ((S * β2 + β1) / L) * (L * Fn) * Gc +
      (32 * cubeBesovW12EmbeddingConstant d * Real.sqrt d * (ca1_K0 d : ℝ)) * τ * ((S * β2 + β1) / L) *
        (L * Fn) * ((Wn + 48 * gp) / L) +
      (48 * Real.sqrt d * 16 ^ 5 * ((125 / 729 : ℝ) ^ d)⁻¹) * Λ * τ ^ 5 * Gc * ((Wn + 48 * gp) / L) := by
    have hb0 : 0 ≤ (S * β2 + β1) / L := by positivity
    have h5 : (ℓ / L) ^ 5 ≤ τ ^ 5 := pow_le_pow_left₀ hLℓ hτ 5
    gcongr
  have hGw : G1 ≤ (Wn + 48 * gp) / L := by
    rw [le_div_iff₀ hL]; linarith only [hgp, hWn0]
  have hWw : Wn / L ≤ (Wn + 48 * gp) / L := by
    gcongr; linarith only [hgp0]
  have hsm : ν / 16 * (G1 ^ 2 + (Wn / L) ^ 2) ≤ 1 / 8 * S * ((Wn + 48 * gp) / L) ^ 2 := by
    have h1 : G1 ^ 2 ≤ ((Wn + 48 * gp) / L) ^ 2 := pow_le_pow_left₀ hG1 hGw 2
    have h2 : (Wn / L) ^ 2 ≤ ((Wn + 48 * gp) / L) ^ 2 := pow_le_pow_left₀ (by positivity) hWw 2
    have h3 : ν / 16 * (G1 ^ 2 + (Wn / L) ^ 2) ≤ ν / 16 * (2 * ((Wn + 48 * gp) / L) ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith only [h1, h2]) (by positivity)
    have h4 : ν / 8 * ((Wn + 48 * gp) / L) ^ 2 ≤ S / 8 * ((Wn + 48 * gp) / L) ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith only [hνS]) (sq_nonneg _)
    nlinarith only [h3, h4]
  have hI : ν * G ^ 2 ≤ (L * Fn) * ((Wn + 48 * gp) / L) + (4 * (12 * 64 ^ d * 64 ^ d)) * (S * α2 + α1) * G * ((Wn + 48 * gp) / L) +
      (8 * cubeBesovW12EmbeddingConstant d * (12 * 64 ^ d * 64 ^ d) * ((125 / 729 : ℝ) ^ d)⁻¹) * τ *
        (S * α2 + α1) * G * Gc +
      (32 * cubeBesovW12EmbeddingConstant d * Real.sqrt d * (ca1_K0 d : ℝ) * ((125 / 729 : ℝ) ^ d)⁻¹) * τ *
        (S * α2 + α1) * Gc * ((Wn + 48 * gp) / L) +
      (48 * 64 ^ d) * ((S * β2 + β1) / L) * (L * Fn) * ((Wn + 48 * gp) / L) +
      (96 * 64 ^ d * cubeBesovW12EmbeddingConstant d * ((125 / 729 : ℝ) ^ d)⁻¹) * τ *
        ((S * β2 + β1) / L) * (L * Fn) * Gc +
      (32 * cubeBesovW12EmbeddingConstant d * Real.sqrt d * (ca1_K0 d : ℝ)) * τ * ((S * β2 + β1) / L) *
        (L * Fn) * ((Wn + 48 * gp) / L) +
      (48 * Real.sqrt d * 16 ^ 5 * ((125 / 729 : ℝ) ^ d)⁻¹) * Λ * τ ^ 5 * Gc * ((Wn + 48 * gp) / L) +
      1 * ν * τ * Gc ^ 2 + 1 / 8 * S * ((Wn + 48 * gp) / L) ^ 2 + ν / 16 * G ^ 2 := by
    nlinarith only [hM1, hmono, hEq, hΛt, hEτ, hB, hsm]
  have hb1' : (S * β2 + β1) / L ≤ 1 := by rw [div_le_one hL]; exact hb
  have hcr' : ν * Gc ^ 2 ≤ ca2_c8 * (ν⁻¹ * (L * Fn) ^ 2 + ν * ((Wn + 48 * gp) / L) ^ 2 +
      d * Λ ^ 2 * ν⁻¹ * ((Wn + 48 * gp) / L) ^ 2) := hcr
  have hc8 : 0 ≤ ca2_c8 := by unfold ca2_c8; positivity
  have key := ca2_alg (ν := ν) (S := S) (α := S * α2 + α1) (b := (S * β2 + β1) / L) (τ := τ) (Λ := Λ)
    (D := (d : ℝ)) (Cα := Cα) (c1 := 4 * (12 * 64 ^ d * 64 ^ d))
    (c2 := 8 * cubeBesovW12EmbeddingConstant d * (12 * 64 ^ d * 64 ^ d) * ((125 / 729 : ℝ) ^ d)⁻¹)
    (c3 := 32 * cubeBesovW12EmbeddingConstant d * Real.sqrt d * (ca1_K0 d : ℝ) * ((125 / 729 : ℝ) ^ d)⁻¹)
    (c4 := 48 * 64 ^ d) (c5 := 96 * 64 ^ d * cubeBesovW12EmbeddingConstant d * ((125 / 729 : ℝ) ^ d)⁻¹)
    (c6 := 32 * cubeBesovW12EmbeddingConstant d * Real.sqrt d * (ca1_K0 d : ℝ))
    (c7 := 48 * Real.sqrt d * 16 ^ 5 * ((125 / 729 : ℝ) ^ d)⁻¹) (c8 := ca2_c8) (c13 := 1) (c14 := 1 / 8)
    (g := G) (k := Gc) (w := (Wn + 48 * gp) / L) (f := L * Fn) hν hνS hα hb1' hτpos.le hd0 hτs hτΞ hCα
    (by positivity) (by positivity) (by positivity) (by positivity) hc8 zero_le_one (by norm_num) hGc0 hw0
    (by positivity) hI hcr'
  refine key.trans (le_of_eq ?_)
  unfold ca2_Cal
  ring


theorem ca2_boundary_det [NeZero d] (hd : 2 ≤ d) (Cα : ℝ) (hCα : 0 ≤ Cα) (m : ℤ) (h : ℕ)
    {W : Set (Vec d)} (hWo : IsOpen W) {lam Lam : ℝ} {A : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d m) ∩ W) A)
    {ν Λ S α1 β1 α2 β2 ϑ τ ℓ : ℝ} (hν : 0 < ν) (hΛ : 0 ≤ Λ)
    (hsym : ∀ x ∈ openCubeSet (originCube d m) ∩ W, symmPart (A x) = ν • (1 : Mat d))
    (hop : ∀ x ∈ openCubeSet (originCube d m) ∩ W, ∀ v : Vec d,
      eucNorm (matVecMul (A x) v) ≤ Λ * eucNorm v)
    (hνS : ν ≤ S) (hα1 : 0 ≤ α1) (hβ1 : 0 ≤ β1) (hα2 : 0 ≤ α2) (hβ2 : 0 ≤ β2)
    (hα : (S * α2 + α1) ^ 2 ≤ Cα * S * ν) (hb : S * β2 + β1 ≤ (3 : ℝ) ^ m)
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
    (hℓ0 : 0 < ℓ) (hℓ : ∀ R ∈ descendantsAtDepth (originCube d m) h, cubeScaleFactor R = ℓ)
    (hℓL : 27 * ℓ ≤ (3 : ℝ) ^ m) {γ : Vec d → ℝ} (hγ : ContDiff ℝ 2 γ) {G1 G2 : ℝ} (hG1 : 0 ≤ G1)
    (hG2 : 0 ≤ G2) (hb1 : ∀ x ∈ openCubeSet (originCube d m) ∩ W, ‖fderiv ℝ γ x‖ ≤ G1)
    (hb2 : ∀ x ∈ openCubeSet (originCube d m) ∩ W, ‖fderiv ℝ (fderiv ℝ γ) x‖ ≤ G2)
    (hZ : LocalizedZeroTraceFunctionOn (openCubeSet (originCube d m) ∩ W) (openCubeSet (originCube d m))
      (fun x => u.toFun x - γ x))
    (hϑ0 : 0 ≤ ϑ) (hϑ1 : ϑ ≤ 1)
    (hB : (volume (ca2_Bset m h ((3 : ℝ) ^ m / 4) W)).toReal ≤ ϑ * cubeVolume (originCube d m))
    (hτ : ℓ / (3 : ℝ) ^ m ≤ τ) (hτs : τ * (S / ν) ^ 2 ≤ 1)
    (hτΞ : τ * (1 + d * Λ ^ 2 / ν ^ 2) ≤ 1)
    (hεB : ca2_CB d * Λ ^ 2 * ϑ ^ (1 / (d : ℝ)) ≤ ν ^ 2 * τ) :
    ν * ∫ x in openCubeSet (originCube d (m - 1)) ∩ W, vecNormSq (u.grad x) ≤
      ca2_Cdet d Cα * cubeVolume (originCube d m) *
        (S * (((3 : ℝ) ^ m)⁻¹) ^ 2 * ((cubeVolume (originCube d m))⁻¹ *
            ∫ x in openCubeSet (originCube d m) ∩ W, (u.toFun x - γ x) ^ 2) +
          S⁻¹ * ((3 : ℝ) ^ m) ^ 2 * ((cubeVolume (originCube d m))⁻¹ *
            ∫ x in openCubeSet (originCube d m) ∩ W, f x ^ 2) +
          S * G1 ^ 2 + S * ℓ ^ 2 * G2 ^ 2) := by
  classical
  have hL : 0 < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  have hS0 : 0 ≤ S := hν.le.trans hνS
  have hSpos : 0 < S := lt_of_lt_of_le hν hνS
  have hτpos : 0 < τ := lt_of_lt_of_le (by positivity) hτ
  have hV0 : 0 < cubeVolume (originCube d m) := cubeVolume_pos _
  have hDo : IsOpen (openCubeSet (originCube d m) ∩ W) := (isOpen_openCubeSet _).inter hWo
  have hDb : Bornology.IsBounded (openCubeSet (originCube d m) ∩ W) :=
    (isBounded_openCubeSet (originCube d m)).subset Set.inter_subset_left
  have hγ1 : ContDiff ℝ 1 γ := hγ.of_le (by norm_num)
  have ha : 0 < (3 : ℝ) ^ m / 4 := by positivity
  have hat : (3 : ℝ) ^ m / 4 < 3 ^ m / 2 := by linarith only [hL]
  have hac0 : 0 < 23 / 50 * (3 : ℝ) ^ m := by positivity
  have hac : (3 : ℝ) ^ m / 4 + ℓ ≤ 2 / 3 * (23 / 50 * (3 : ℝ) ^ m) := by linarith only [hℓL, hL]
  have hnn : ∀ x : Vec d, 0 ≤ vecNormSq (u.grad x) := fun x => by
    unfold vecNormSq vecDot; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hΦ0 : ∀ (b : ℝ) (x : Vec d), 0 ≤ ca1_Phi b x := fun b x => by rw [ca1_Phi_eq]; exact sq_nonneg _
  -- the normalized quantities
  have hX1nn : 0 ≤ (cubeVolume (originCube d m))⁻¹ * ∫ x in openCubeSet (originCube d m) ∩ W,
      ca1_Phi ((3 : ℝ) ^ m / 4) x * vecNormSq (u.grad x) :=
    mul_nonneg (inv_nonneg.2 hV0.le) (integral_nonneg fun x => mul_nonneg (hΦ0 _ x) (hnn x))
  have hXcnn : 0 ≤ (cubeVolume (originCube d m))⁻¹ * ∫ x in openCubeSet (originCube d m) ∩ W,
      ca1_Phi (23 / 50 * (3 : ℝ) ^ m) x * vecNormSq (u.grad x) :=
    mul_nonneg (inv_nonneg.2 hV0.le) (integral_nonneg fun x => mul_nonneg (hΦ0 _ x) (hnn x))
  have hXWnn : 0 ≤ (cubeVolume (originCube d m))⁻¹ * ∫ x in openCubeSet (originCube d m) ∩ W,
      (u.toFun x - γ x) ^ 2 := mul_nonneg (inv_nonneg.2 hV0.le) (integral_nonneg fun x => sq_nonneg _)
  have hXFnn : 0 ≤ (cubeVolume (originCube d m))⁻¹ * ∫ x in openCubeSet (originCube d m) ∩ W, f x ^ 2 :=
    mul_nonneg (inv_nonneg.2 hV0.le) (integral_nonneg fun x => sq_nonneg _)
  obtain ⟨G, hG0, hGeq⟩ : ∃ G : ℝ, 0 ≤ G ∧ (cubeVolume (originCube d m))⁻¹ *
      ∫ x in openCubeSet (originCube d m) ∩ W, ca1_Phi ((3 : ℝ) ^ m / 4) x * vecNormSq (u.grad x) = G ^ 2 :=
    ⟨Real.sqrt _, Real.sqrt_nonneg _, (Real.sq_sqrt hX1nn).symm⟩
  obtain ⟨Gc, hGc0, hGceq⟩ : ∃ G : ℝ, 0 ≤ G ∧ (cubeVolume (originCube d m))⁻¹ *
      ∫ x in openCubeSet (originCube d m) ∩ W, ca1_Phi (23 / 50 * (3 : ℝ) ^ m) x * vecNormSq (u.grad x) = G ^ 2 :=
    ⟨Real.sqrt _, Real.sqrt_nonneg _, (Real.sq_sqrt hXcnn).symm⟩
  obtain ⟨Wn, hWn0, hWneq⟩ : ∃ G : ℝ, 0 ≤ G ∧ (cubeVolume (originCube d m))⁻¹ *
      ∫ x in openCubeSet (originCube d m) ∩ W, (u.toFun x - γ x) ^ 2 = G ^ 2 :=
    ⟨Real.sqrt _, Real.sqrt_nonneg _, (Real.sq_sqrt hXWnn).symm⟩
  obtain ⟨Fn, hFn0, hFneq⟩ : ∃ G : ℝ, 0 ≤ G ∧ (cubeVolume (originCube d m))⁻¹ *
      ∫ x in openCubeSet (originCube d m) ∩ W, f x ^ 2 = G ^ 2 :=
    ⟨Real.sqrt _, Real.sqrt_nonneg _, (Real.sq_sqrt hXFnn).symm⟩
  have hGcle : (cubeVolume (originCube d m))⁻¹ * ∫ x in openCubeSet (originCube d m) ∩ W,
      (ca1_phi (23 / 50 * (3 : ℝ) ^ m) x * Real.sqrt (vecNormSq (u.grad x))) ^ 2 ≤ Gc ^ 2 := by
    rw [← hGceq]
    refine le_of_eq (congrArg _ (integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)))
    simp only
    rw [mul_pow, Real.sq_sqrt (hnn x), ← ca1_Phi_eq]
  -- the constants of the datum
  have hKb := cubeBesovW12EmbeddingConstant_nonneg d
  have hgp0 : 0 ≤ ca2_gp d ((3 : ℝ) ^ m / 4) ℓ G1 G2 := by unfold ca2_gp; positivity
  have hgpeq : 48 * ca2_gp d ((3 : ℝ) ^ m / 4) ℓ G1 G2 =
      (3 : ℝ) ^ m * (G1 + 2 * cubeBesovW12EmbeddingConstant d * ℓ * Real.sqrt d *
        (24 * ((3 : ℝ) ^ m / 4)⁻¹ * G1 + G2)) := by
    unfold ca2_gp
    have h64 : (0 : ℝ) < 64 ^ d := by positivity
    field_simp
    ring
  have hgp : (3 : ℝ) ^ m * G1 ≤ 48 * ca2_gp d ((3 : ℝ) ^ m / 4) ℓ G1 G2 := by
    have hK : 0 ≤ 2 * cubeBesovW12EmbeddingConstant d * ℓ * Real.sqrt d * (24 * ((3 : ℝ) ^ m / 4)⁻¹ * G1 + G2) := by
      positivity
    rw [hgpeq]
    nlinarith only [mul_nonneg hL.le hK]
  have hKηdef : (((ca1_K0 d * Real.toNNReal ((3 : ℝ) ^ m / 4)⁻¹ ^ 2 : ℝ≥0)) : ℝ) =
      (ca1_K0 d : ℝ) * (((3 : ℝ) ^ m / 4)⁻¹) ^ 2 := by
    push_cast
    rw [Real.coe_toNNReal _ (by positivity)]
  have hKη := (ca1_K0_spec d ((3 : ℝ) ^ m / 4) ha).2
  -- the main inequality
  have hM1 := ca2_main hd m h hWo hEll hsym hS0 hα1 hβ1 hα2 hβ2 u hf hu hBB ha hat hac0 hℓ0 hℓ hac hγ
    hG1 hG2 hb1 hb2 hKη hG0 hGc0 hWn0 hFn0 hGeq hZ hGcle (le_of_eq hWneq) (le_of_eq hFneq)
  rw [hKηdef] at hM1
  have hB1 := ca2_Bnorm hd m h hWo hν hΛ hop u hγ hZ rfl rfl hKη hKηdef hb1 hGeq hGceq hWneq hϑ0 hϑ1 hB hτpos hεB
  have hcr := ca2_crude_norm m hWo hEll hν hΛ hsym hop u hf hu hγ hZ hG1 hb1 hGceq hFneq hWneq
    (w2 := (Wn + 48 * ca2_gp d ((3 : ℝ) ^ m / 4) ℓ G1 G2) / (3 : ℝ) ^ m)
    (by gcongr; linarith only [hgp0]) (by rw [le_div_iff₀ hL]; linarith only [hgp, hWn0]) hWn0
  have hfin := ca2_assemble d (by omega) Cα hCα (L := (3 : ℝ) ^ m) (ℓ := ℓ) (ν := ν) (Λ := Λ) (S := S)
    (α1 := α1) (β1 := β1) (α2 := α2) (β2 := β2) (τ := τ) (G1 := G1) (Kη := (ca1_K0 d : ℝ) * (((3 : ℝ) ^ m / 4)⁻¹) ^ 2)
    hL hν hΛ hνS hα1 hβ1 hα2 hβ2 hα hb hℓ0 hτ hτs hτΞ rfl hG0 hGc0 hWn0 hFn0 hgp0 hG1 hgp hM1 hB1 hcr
  -- the left-hand side
  have hD'sub : openCubeSet (originCube d (m - 1)) ∩ W ⊆ openCubeSet (originCube d m) ∩ W :=
    Set.inter_subset_inter_left _ (ca1_openCube_pred_subset m)
  have hZg := ca2_Z_gen m hWo u ha (S := openCubeSet (originCube d (m - 1)) ∩ W)
    ((isOpen_openCubeSet _).inter hWo).measurableSet hD'sub (fun x hx k => by
      have := (mem_openCubeSet_originCube_iff.1 hx.1) k
      have h3 : (3 : ℝ) ^ (m - 1) = 3 ^ m / 3 := by rw [zpow_sub₀ (by norm_num)]; simp
      rw [abs_le]
      constructor <;> nlinarith only [this.1, this.2, h3, hL])
  have hV0' := hV0.ne'
  have hX1 : ∫ x in openCubeSet (originCube d m) ∩ W, ca1_Phi ((3 : ℝ) ^ m / 4) x * vecNormSq (u.grad x) =
      cubeVolume (originCube d m) * G ^ 2 := by
    rw [← hGeq, ← mul_assoc, mul_inv_cancel₀ hV0', one_mul]
  rw [hX1] at hZg
  -- the datum
  have hd0 : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hℓL' : ℓ / (3 : ℝ) ^ m ≤ 1 := by rw [div_le_one hL]; linarith only [hℓL, hℓ0]
  have hPle : (Wn + 48 * ca2_gp d ((3 : ℝ) ^ m / 4) ℓ G1 G2) / (3 : ℝ) ^ m ≤
      Wn / (3 : ℝ) ^ m + (1 + 192 * cubeBesovW12EmbeddingConstant d * Real.sqrt d) * G1 +
        2 * cubeBesovW12EmbeddingConstant d * Real.sqrt d * ℓ * G2 := by
    have e1 : (Wn + 48 * ca2_gp d ((3 : ℝ) ^ m / 4) ℓ G1 G2) / (3 : ℝ) ^ m =
        Wn / (3 : ℝ) ^ m + (G1 + 192 * cubeBesovW12EmbeddingConstant d * Real.sqrt d * (ℓ / (3 : ℝ) ^ m) * G1 +
          2 * cubeBesovW12EmbeddingConstant d * Real.sqrt d * ℓ * G2) := by
      rw [add_div, hgpeq]; field_simp; ring
    rw [e1]
    have : 192 * cubeBesovW12EmbeddingConstant d * Real.sqrt d * (ℓ / (3 : ℝ) ^ m) * G1 ≤
        192 * cubeBesovW12EmbeddingConstant d * Real.sqrt d * G1 := by
      have := mul_le_mul_of_nonneg_left hℓL' (by positivity : 0 ≤ 192 * cubeBesovW12EmbeddingConstant d * Real.sqrt d)
      nlinarith only [this, hG1]
    nlinarith only [this]
  have hw2nn : 0 ≤ (Wn + 48 * ca2_gp d ((3 : ℝ) ^ m / 4) ℓ G1 G2) / (3 : ℝ) ^ m := by positivity
  have hP : ((Wn + 48 * ca2_gp d ((3 : ℝ) ^ m / 4) ℓ G1 G2) / (3 : ℝ) ^ m) ^ 2 ≤
      3 * (Wn / (3 : ℝ) ^ m) ^ 2 + 3 * (1 + 192 * cubeBesovW12EmbeddingConstant d * Real.sqrt d) ^ 2 * G1 ^ 2 +
        12 * cubeBesovW12EmbeddingConstant d ^ 2 * d * (ℓ ^ 2 * G2 ^ 2) := by
    refine (pow_le_pow_left₀ hw2nn hPle 2).trans ?_
    refine (ca2_sq3 _ _ _).trans (le_of_eq ?_)
    have : (Real.sqrt d) ^ 2 = d := Real.sq_sqrt (Nat.cast_nonneg d)
    have e : (2 * cubeBesovW12EmbeddingConstant d * Real.sqrt d * ℓ * G2) ^ 2 =
        4 * cubeBesovW12EmbeddingConstant d ^ 2 * d * (ℓ ^ 2 * G2 ^ 2) := by
      rw [show (2 * cubeBesovW12EmbeddingConstant d * Real.sqrt d * ℓ * G2) ^ 2 =
        4 * cubeBesovW12EmbeddingConstant d ^ 2 * (Real.sqrt d) ^ 2 * (ℓ ^ 2 * G2 ^ 2) by ring, this]
    rw [mul_pow, e]
    ring
  -- the final estimate
  have hc0 : 0 < ((125 / 729 : ℝ) ^ d) := by positivity
  have hCal : 0 ≤ ca2_Cal d Cα := by
    unfold ca2_Cal ca2_c8
    positivity
  have hfin2 : ν * G ^ 2 ≤ ca2_Cal d Cα * (3 + 4 * (1 + 192 * cubeBesovW12EmbeddingConstant d * Real.sqrt d) ^ 2 +
      16 * cubeBesovW12EmbeddingConstant d ^ 2 * d) * (S * (((3 : ℝ) ^ m)⁻¹) ^ 2 * Wn ^ 2 + S⁻¹ * ((3 : ℝ) ^ m) ^ 2 * Fn ^ 2 +
        S * G1 ^ 2 + S * ℓ ^ 2 * G2 ^ 2) := by
    refine hfin.trans ?_
    set M : ℝ := 3 + 4 * (1 + 192 * cubeBesovW12EmbeddingConstant d * Real.sqrt d) ^ 2 +
      16 * cubeBesovW12EmbeddingConstant d ^ 2 * d with hM
    have hSw := mul_le_mul_of_nonneg_left hP hSpos.le
    have e1 : S * (Wn / (3 : ℝ) ^ m) ^ 2 = S * (((3 : ℝ) ^ m)⁻¹) ^ 2 * Wn ^ 2 := by
      rw [div_eq_mul_inv, mul_pow]; ring
    have e2 : S⁻¹ * ((3 : ℝ) ^ m * Fn) ^ 2 = S⁻¹ * ((3 : ℝ) ^ m) ^ 2 * Fn ^ 2 := by ring
    rw [e2]
    have hQ1 : 0 ≤ S * (((3 : ℝ) ^ m)⁻¹) ^ 2 * Wn ^ 2 := by positivity
    have hQ2 : 0 ≤ S⁻¹ * ((3 : ℝ) ^ m) ^ 2 * Fn ^ 2 := by positivity
    have hQ3 : 0 ≤ S * G1 ^ 2 := by positivity
    have hQ4 : 0 ≤ S * ℓ ^ 2 * G2 ^ 2 := by positivity
    have h41 : 0 ≤ 4 * (1 + 192 * cubeBesovW12EmbeddingConstant d * Real.sqrt d) ^ 2 := by positivity
    have h42 : 0 ≤ cubeBesovW12EmbeddingConstant d ^ 2 * d := by positivity
    have h43 : 0 ≤ (1 + 192 * cubeBesovW12EmbeddingConstant d * Real.sqrt d) ^ 2 := by positivity
    have hk1 : (3 : ℝ) ≤ M := by rw [hM]; linarith only [h41, h42]
    have hk2 : 3 * (1 + 192 * cubeBesovW12EmbeddingConstant d * Real.sqrt d) ^ 2 ≤ M := by
      rw [hM]; linarith only [h43, h42]
    have hk3 : 12 * cubeBesovW12EmbeddingConstant d ^ 2 * d ≤ M := by
      rw [hM]; nlinarith only [h41, h42]
    have hk4 : (1 : ℝ) ≤ M := by linarith only [hk1]
    have hineq : S * ((Wn + 48 * ca2_gp d ((3 : ℝ) ^ m / 4) ℓ G1 G2) / (3 : ℝ) ^ m) ^ 2 +
        S⁻¹ * ((3 : ℝ) ^ m) ^ 2 * Fn ^ 2 ≤
        M * (S * (((3 : ℝ) ^ m)⁻¹) ^ 2 * Wn ^ 2 + S⁻¹ * ((3 : ℝ) ^ m) ^ 2 * Fn ^ 2 +
          S * G1 ^ 2 + S * ℓ ^ 2 * G2 ^ 2) := by
      have e3 : S * (3 * (Wn / (3 : ℝ) ^ m) ^ 2 + 3 * (1 + 192 * cubeBesovW12EmbeddingConstant d * Real.sqrt d) ^ 2 * G1 ^ 2 +
          12 * cubeBesovW12EmbeddingConstant d ^ 2 * d * (ℓ ^ 2 * G2 ^ 2)) =
          3 * (S * (Wn / (3 : ℝ) ^ m) ^ 2) + (3 * (1 + 192 * cubeBesovW12EmbeddingConstant d * Real.sqrt d) ^ 2) *
            (S * G1 ^ 2) + (12 * cubeBesovW12EmbeddingConstant d ^ 2 * d) * (S * ℓ ^ 2 * G2 ^ 2) := by ring
      rw [e3, e1] at hSw
      nlinarith only [hSw, mul_le_mul_of_nonneg_right hk1 hQ1, mul_le_mul_of_nonneg_right hk2 hQ3,
        mul_le_mul_of_nonneg_right hk3 hQ4, mul_le_mul_of_nonneg_right hk4 hQ2]
    calc ca2_Cal d Cα * (S * ((Wn + 48 * ca2_gp d ((3 : ℝ) ^ m / 4) ℓ G1 G2) / (3 : ℝ) ^ m) ^ 2 +
          S⁻¹ * ((3 : ℝ) ^ m) ^ 2 * Fn ^ 2)
        ≤ ca2_Cal d Cα * (M * (S * (((3 : ℝ) ^ m)⁻¹) ^ 2 * Wn ^ 2 + S⁻¹ * ((3 : ℝ) ^ m) ^ 2 * Fn ^ 2 +
          S * G1 ^ 2 + S * ℓ ^ 2 * G2 ^ 2)) := mul_le_mul_of_nonneg_left hineq hCal
      _ = _ := by ring
  rw [hWneq, hFneq]
  have h1 : ν * ∫ x in openCubeSet (originCube d (m - 1)) ∩ W, vecNormSq (u.grad x) ≤
      ν * ((((125 / 729 : ℝ) ^ d)⁻¹) ^ 2 * (cubeVolume (originCube d m) * G ^ 2)) :=
    mul_le_mul_of_nonneg_left hZg hν.le
  refine h1.trans ?_
  have h2 := mul_le_mul_of_nonneg_left hfin2 (by positivity : 0 ≤ (((125 / 729 : ℝ) ^ d)⁻¹) ^ 2 * cubeVolume (originCube d m))
  unfold ca2_Cdet
  nlinarith only [h2]

end SuperdiffusionCLT.Section7
