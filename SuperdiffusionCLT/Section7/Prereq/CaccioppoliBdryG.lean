/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.CaccioppoliBdryC
public import SuperdiffusionCLT.Section7.Prereq.CaccioppoliBdryF

/-!
# The weak test on a good grid cube with a smooth datum

On a grid cube `R` inside the domain, the pairing `avg_R (A∇u)·(Φ∇γ - (u - γ)∇Φ)` is bounded by the
two weak bounds of the right-hand-side lemma times `‖ξ‖ + 2Kℓ‖∇ξ‖`, with `ξ_i = Φ ∂_iγ - E_i (u - γ)`.
The `H¹(R)` field `ξ` is built from `C¹` functions and the Lipschitz multiplier `E_i`.
-/

@[expose] public section

open scoped ENNReal NNReal
open MeasureTheory Filter Topology Homogenization

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- A `C¹` function as an `H¹` function on a cube. -/
noncomputable def ca2_h1R (R : TriadicCube d) {f : Vec d → ℝ} (hf : ContDiff ℝ 1 f) :
    H1Function (openCubeSet R) :=
  H1Function.ofContDiffOnIsOpenBoundedConvexDomain (isOpenBoundedConvexDomain_openCubeSet R) hf

theorem ca2_h1R_toFun (R : TriadicCube d) {f : Vec d → ℝ} (hf : ContDiff ℝ 1 f) (x : Vec d) :
    (ca2_h1R R hf).toFun x = f x := rfl

theorem ca2_h1R_grad (R : TriadicCube d) {f : Vec d → ℝ} (hf : ContDiff ℝ 1 f) (x : Vec d) :
    (ca2_h1R R hf).grad x = p12_grad f x := rfl

/-- The `i`-th component of the gradient of `γ` is `C¹` when `γ` is `C²`. -/
theorem ca2_contDiff_partial {γ : Vec d → ℝ} (hγ : ContDiff ℝ 2 γ) (i : Fin d) :
    ContDiff ℝ 1 (fun x => p12_grad γ x i) := by
  have h : ContDiff ℝ 1 (fderiv ℝ γ) := hγ.fderiv_right (m := 1) (by norm_num)
  exact h.clm_apply contDiff_const

theorem ca2_contDiff_Phi (a : ℝ) : ContDiff ℝ 1 (ca1_Phi (d := d) a) :=
  ca1_Phi1_contDiff.comp (contDiff_const_smul a⁻¹)

theorem ca2_contDiff_E (a : ℝ) (i : Fin d) : ContDiff ℝ 1 (ca1_E (d := d) a i) :=
  contDiff_const.mul ((ca1_E1_contDiff i).comp (contDiff_const_smul a⁻¹))

/-- The `H¹(R)` field `ξ_i = Φ ∂_iγ - E_i (u - γ)`. -/
noncomputable def ca2_xi (R : TriadicCube d) {W : Set (Vec d)} (hRW : openCubeSet R ⊆ W)
    (u : H1Function W) {γ : Vec d → ℝ} (hγ : ContDiff ℝ 2 γ) {a : ℝ} (ha : 0 < a)
    {Kη : ℝ≥0} (hKη : ∀ i, LipschitzWith Kη (ca1_E (d := d) a i)) (i : Fin d) :
    H1Function (openCubeSet R) :=
  ca2_h1R R ((ca2_contDiff_Phi a).mul (ca2_contDiff_partial hγ i)) -
    mulLip (isOpen_openCubeSet R)
      (u.restrict (isOpen_openCubeSet R) hRW - ca2_h1R R (hγ.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)))
      (hKη i) (M := 12 * a⁻¹) (ca1_E_abs_le_const ha i)

theorem ca2_xi_toFun (R : TriadicCube d) {W : Set (Vec d)} (hRW : openCubeSet R ⊆ W)
    (u : H1Function W) {γ : Vec d → ℝ} (hγ : ContDiff ℝ 2 γ) {a : ℝ} (ha : 0 < a)
    {Kη : ℝ≥0} (hKη : ∀ i, LipschitzWith Kη (ca1_E (d := d) a i)) (i : Fin d) (x : Vec d) :
    (ca2_xi R hRW u hγ ha hKη i).toFun x =
      ca1_Phi a x * p12_grad γ x i - ca1_E a i x * (u.toFun x - γ x) := by
  simp [ca2_xi, H1Function.sub_toFun, mulLip, ca2_h1R_toFun, H1Function.restrict]

theorem ca2_xi_grad (R : TriadicCube d) {W : Set (Vec d)} (hRW : openCubeSet R ⊆ W)
    (u : H1Function W) {γ : Vec d → ℝ} (hγ : ContDiff ℝ 2 γ) {a : ℝ} (ha : 0 < a)
    {Kη : ℝ≥0} (hKη : ∀ i, LipschitzWith Kη (ca1_E (d := d) a i)) (i : Fin d) (x : Vec d) :
    (ca2_xi R hRW u hγ ha hKη i).grad x =
      p12_grad (fun y => ca1_Phi a y * p12_grad γ y i) x -
        (ca1_E a i x • (u.grad x - p12_grad γ x) +
          (u.toFun x - γ x) • lipGradient (ca1_E a i) x) := by
  simp [ca2_xi, H1Function.sub_grad, mulLip, ca2_h1R_grad, H1Function.sub_toFun, H1Function.restrict]
  rfl

theorem ca2_eucNorm_sub_le (v w : Vec d) : eucNorm (v - w) ≤ eucNorm v + eucNorm w := by
  have : v - w = v + (-1 : ℝ) • w := by funext j; simp [sub_eq_add_neg]
  rw [this]
  refine (r1_eucNorm_add_le _ _).trans ?_
  rw [ca1_eucNorm_smul]
  simp

theorem ca2_basis_norm (i : Fin d) : ‖basisVec (d := d) i‖ = 1 := by simp [basisVec, Pi.norm_single]

theorem ca2_abs_partial_le {γ : Vec d → ℝ} (x : Vec d) (i : Fin d) :
    |p12_grad γ x i| ≤ ‖fderiv ℝ γ x‖ := by
  have h := (fderiv ℝ γ x).le_opNorm (basisVec i)
  rw [ca2_basis_norm, mul_one] at h
  simpa [p12_grad, Real.norm_eq_abs] using h

theorem ca2_eucNorm_grad_le {γ : Vec d → ℝ} (x : Vec d) :
    eucNorm (p12_grad γ x) ≤ Real.sqrt d * ‖fderiv ℝ γ x‖ :=
  ca1_eucNorm_le_of_abs_le (norm_nonneg _) (fun i => ca2_abs_partial_le x i)

theorem ca2_abs_hess_le {γ : Vec d → ℝ} (hγ : ContDiff ℝ 2 γ) (x : Vec d) (i j : Fin d) :
    |p12_grad (fun y => p12_grad γ y i) x j| ≤ ‖fderiv ℝ (fderiv ℝ γ) x‖ := by
  have h1 : DifferentiableAt ℝ (fderiv ℝ γ) x :=
    ((hγ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
  have h2 : fderiv ℝ (fun y => p12_grad γ y i) x (basisVec j) =
      fderiv ℝ (fderiv ℝ γ) x (basisVec j) (basisVec i) := by
    have : (fun y => p12_grad γ y i) = fun y => (fderiv ℝ γ y) (basisVec i) := rfl
    rw [this, fderiv_clm_apply h1 (differentiableAt_const _)]
    simp
  have h3 : ‖fderiv ℝ (fderiv ℝ γ) x (basisVec j) (basisVec i)‖ ≤ ‖fderiv ℝ (fderiv ℝ γ) x‖ := by
    calc _ ≤ ‖fderiv ℝ (fderiv ℝ γ) x (basisVec j)‖ * ‖basisVec (d := d) i‖ :=
          (fderiv ℝ (fderiv ℝ γ) x (basisVec j)).le_opNorm _
      _ ≤ (‖fderiv ℝ (fderiv ℝ γ) x‖ * ‖basisVec (d := d) j‖) * ‖basisVec (d := d) i‖ :=
          mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ γ) x).le_opNorm _) (norm_nonneg _)
      _ = _ := by rw [ca2_basis_norm, ca2_basis_norm]; ring
  show |fderiv ℝ (fun y => p12_grad γ y i) x (basisVec j)| ≤ _
  rw [h2, ← Real.norm_eq_abs]
  exact h3

theorem ca2_eucNorm_hess_le {γ : Vec d → ℝ} (hγ : ContDiff ℝ 2 γ) (x : Vec d) (i : Fin d) :
    eucNorm (p12_grad (fun y => p12_grad γ y i) x) ≤ Real.sqrt d * ‖fderiv ℝ (fderiv ℝ γ) x‖ :=
  ca1_eucNorm_le_of_abs_le (norm_nonneg (fderiv ℝ (fderiv ℝ γ) x)) (fun j => ca2_abs_hess_le hγ x i j)

theorem ca2_grad_mul {Φ ψ : Vec d → ℝ} (hΦ : ContDiff ℝ 1 Φ) (hψ : ContDiff ℝ 1 ψ) (x : Vec d) :
    p12_grad (fun y => Φ y * ψ y) x = ψ x • p12_grad Φ x + Φ x • p12_grad ψ x := by
  funext i
  have hd1 : HasFDerivAt Φ (fderiv ℝ Φ x) x := ((hΦ.differentiable (by simp)) x).hasFDerivAt
  have hd2 : HasFDerivAt ψ (fderiv ℝ ψ x) x := ((hψ.differentiable (by simp)) x).hasFDerivAt
  have := hd1.mul hd2
  simp only [p12_grad, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [show (fun y => Φ y * ψ y) = Φ * ψ from rfl, this.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem ca2_phi_harnack_cube {a : ℝ} (ha : 0 < a) (R : TriadicCube d)
    (hint : ∀ k, |triadicCubeShift R k| + 3 / 2 * cubeScaleFactor R ≤ a) :
    ∀ x ∈ openCubeSet R, ca1_phi a x ≤ 64 ^ d * ca1_phi a (triadicCubeShift R) := by
  intro x hx
  have hℓ : 0 < cubeScaleFactor R := by simp [cubeScaleFactor]; positivity
  exact ca1_phi_harnack (a := a) (η := cubeScaleFactor R) ha hℓ.le (x := triadicCubeShift R) (y := x)
    (fun k => by linarith only [hint k, hℓ])
    (fun k => by
      have := (ca1_mem_openCube_iff R x).1 hx k
      exact this.le.trans (by linarith only [hℓ]))

theorem ca2_Phi_le_phi (a : ℝ) (x : Vec d) : ca1_Phi a x ≤ ca1_phi a x := by
  rw [ca1_Phi_eq]
  have h0 := ca1_phi_nonneg a x
  have h1 := ca1_phi_le_one a x
  nlinarith only [h0, h1]

/-- Pointwise bound of the field `ξ_i` on a good cube. -/
theorem ca2_xi_abs_le {a : ℝ} (ha : 0 < a) (R : TriadicCube d)
    (hint : ∀ k, |triadicCubeShift R k| + 3 / 2 * cubeScaleFactor R ≤ a) {γ : Vec d → ℝ} {G1 : ℝ}
    (hb1 : ∀ x ∈ openCubeSet R, ‖fderiv ℝ γ x‖ ≤ G1) {x : Vec d}
    (hx : x ∈ openCubeSet R) (i : Fin d) (w : ℝ) :
    |ca1_Phi a x * p12_grad γ x i - ca1_E a i x * w| ≤
      12 * 64 ^ d * a⁻¹ * ca1_phi a (triadicCubeShift R) * |w| +
        64 ^ d * ca1_phi a (triadicCubeShift R) * G1 := by
  have hφ := ca2_phi_harnack_cube ha R hint x hx
  have hE := ca1_harnack_cube ha R hint x hx i
  have hΦ0 : 0 ≤ ca1_Phi a x := by rw [ca1_Phi_eq]; exact sq_nonneg _
  have h1 : |ca1_Phi a x * p12_grad γ x i| ≤ 64 ^ d * ca1_phi a (triadicCubeShift R) * G1 := by
    rw [abs_mul, abs_of_nonneg hΦ0]
    have := ca2_abs_partial_le (γ := γ) x i
    calc ca1_Phi a x * |p12_grad γ x i| ≤ (64 ^ d * ca1_phi a (triadicCubeShift R)) * G1 :=
          mul_le_mul ((ca2_Phi_le_phi a x).trans hφ) (this.trans (hb1 x hx)) (abs_nonneg _)
            (by have := ca1_phi_nonneg a (triadicCubeShift R); positivity)
      _ = _ := by ring
  have h2 : |ca1_E a i x * w| ≤ 12 * 64 ^ d * a⁻¹ * ca1_phi a (triadicCubeShift R) * |w| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hE (abs_nonneg _)
  calc _ ≤ |ca1_Phi a x * p12_grad γ x i| + |ca1_E a i x * w| := abs_sub _ _
    _ ≤ _ := by linarith only [h1, h2]

/-- Pointwise bound of the gradient of `ξ_i` on a good cube. -/
theorem ca2_xi_grad_le [NeZero d] {a : ℝ} (ha : 0 < a) (R : TriadicCube d)
    (hint : ∀ k, |triadicCubeShift R k| + 3 / 2 * cubeScaleFactor R ≤ a) {γ : Vec d → ℝ}
    (hγ : ContDiff ℝ 2 γ) {G1 G2 : ℝ} (hG1 : 0 ≤ G1)
    (hb1 : ∀ x ∈ openCubeSet R, ‖fderiv ℝ γ x‖ ≤ G1)
    (hb2 : ∀ x ∈ openCubeSet R, ‖fderiv ℝ (fderiv ℝ γ) x‖ ≤ G2) {Kη : ℝ≥0}
    (hKη : ∀ i, LipschitzWith Kη (ca1_E (d := d) a i)) {x : Vec d} (hx : x ∈ openCubeSet R)
    (i : Fin d) (g : Vec d) (w : ℝ) :
    eucNorm (p12_grad (fun y => ca1_Phi a y * p12_grad γ y i) x -
        (ca1_E a i x • (g - p12_grad γ x) + w • lipGradient (ca1_E a i) x)) ≤
      12 * 64 ^ d * a⁻¹ * ca1_phi a (triadicCubeShift R) * eucNorm g + Real.sqrt d * Kη * |w| +
        ca1_phi a (triadicCubeShift R) * (64 ^ d * Real.sqrt d * (24 * a⁻¹ * G1 + G2)) := by
  have hφ := ca2_phi_harnack_cube ha R hint x hx
  have hE := ca1_harnack_cube ha R hint x hx i
  have hφ0 := ca1_phi_nonneg a (triadicCubeShift R)
  have hφx0 := ca1_phi_nonneg a x
  set φR := ca1_phi a (triadicCubeShift R) with hφR
  have hd0 : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hΦ0 : 0 ≤ ca1_Phi a x := by rw [ca1_Phi_eq]; exact sq_nonneg _
  have hP : ca1_Phi (d := d) a = fun y => ca1_phi a y ^ 2 := funext fun y => ca1_Phi_eq a y
  -- the pieces
  have hgrΦ : p12_grad (ca1_Phi (d := d) a) x = fun j => ca1_E a j x := by
    funext j; exact ca1_Phi_fderiv a j x
  have t1 : eucNorm (p12_grad γ x i • p12_grad (ca1_Phi (d := d) a) x) ≤
      G1 * (Real.sqrt d * (12 * a⁻¹ * (64 ^ d * φR))) := by
    rw [ca1_eucNorm_smul, hgrΦ]
    have h2 : eucNorm (fun j => ca1_E a j x) ≤ Real.sqrt d * (12 * a⁻¹ * (64 ^ d * φR)) := by
      refine ca1_eucNorm_le_of_abs_le (by positivity) fun j => ?_
      exact (ca1_E_abs_le ha j x).trans (by
        have h12 : 0 ≤ 12 * a⁻¹ := by positivity
        exact mul_le_mul_of_nonneg_left hφ h12)
    exact mul_le_mul ((ca2_abs_partial_le x i).trans (hb1 x hx)) h2 (ca1_eucNorm_nonneg _) hG1
  have t2 : eucNorm (ca1_Phi a x • p12_grad (fun y => p12_grad γ y i) x) ≤
      (64 ^ d * φR) * (Real.sqrt d * G2) := by
    rw [ca1_eucNorm_smul, abs_of_nonneg hΦ0]
    exact mul_le_mul ((ca2_Phi_le_phi a x).trans hφ)
      ((ca2_eucNorm_hess_le hγ x i).trans (mul_le_mul_of_nonneg_left (hb2 x hx) hd0))
      (ca1_eucNorm_nonneg _) (by positivity)
  have t3 : eucNorm (ca1_E a i x • (g - p12_grad γ x)) ≤
      12 * 64 ^ d * a⁻¹ * φR * (eucNorm g + Real.sqrt d * G1) := by
    rw [ca1_eucNorm_smul]
    have h1 : eucNorm (g - p12_grad γ x) ≤ eucNorm g + Real.sqrt d * G1 := by
      have : g - p12_grad γ x = g + (-1 : ℝ) • p12_grad γ x := by
        funext j; simp [sub_eq_add_neg]
      rw [this]
      refine (r1_eucNorm_add_le _ _).trans ?_
      rw [ca1_eucNorm_smul]
      simp only [abs_neg, abs_one, one_mul]
      exact add_le_add le_rfl ((ca2_eucNorm_grad_le x).trans (mul_le_mul_of_nonneg_left (hb1 x hx) hd0))
    exact mul_le_mul hE h1 (ca1_eucNorm_nonneg _) (by positivity)
  have t4 : eucNorm (w • lipGradient (ca1_E a i) x) ≤ Real.sqrt d * Kη * |w| := by
    rw [ca1_eucNorm_smul]
    have hlip : ∀ j, |lipGradient (ca1_E a i) x j| ≤ Kη := by
      intro j
      have h1 : ‖fderiv ℝ (ca1_E a i) x‖ ≤ Kη := norm_fderiv_le_of_lipschitz ℝ (hKη i)
      have h3 : ‖fderiv ℝ (ca1_E a i) x (basisVec j)‖ ≤ Kη := by
        calc ‖fderiv ℝ (ca1_E a i) x (basisVec j)‖ ≤ ‖fderiv ℝ (ca1_E a i) x‖ * ‖basisVec (d := d) j‖ :=
              (fderiv ℝ (ca1_E a i) x).le_opNorm _
          _ ≤ Kη := by rw [ca2_basis_norm, mul_one]; exact h1
      simpa [lipGradient] using h3
    have hl : eucNorm (lipGradient (ca1_E a i) x) ≤ Real.sqrt d * Kη :=
      ca1_eucNorm_le_of_abs_le (by positivity) hlip
    calc |w| * eucNorm (lipGradient (ca1_E a i) x) ≤ |w| * (Real.sqrt d * Kη) :=
          mul_le_mul_of_nonneg_left hl (abs_nonneg _)
      _ = _ := by ring
  have hgp : p12_grad (fun y => ca1_Phi a y * p12_grad γ y i) x =
      p12_grad γ x i • p12_grad (ca1_Phi (d := d) a) x +
        ca1_Phi a x • p12_grad (fun y => p12_grad γ y i) x :=
    ca2_grad_mul (ca2_contDiff_Phi a) (ca2_contDiff_partial hγ i) x
  rw [hgp]
  refine (ca2_eucNorm_sub_le _ _).trans ?_
  have h12 := (r1_eucNorm_add_le (p12_grad γ x i • p12_grad (ca1_Phi (d := d) a) x)
    (ca1_Phi a x • p12_grad (fun y => p12_grad γ y i) x))
  have h34 := (r1_eucNorm_add_le (ca1_E a i x • (g - p12_grad γ x)) (w • lipGradient (ca1_E a i) x))
  have e : G1 * (Real.sqrt d * (12 * a⁻¹ * (64 ^ d * φR))) + (64 ^ d * φR) * (Real.sqrt d * G2) +
      (12 * 64 ^ d * a⁻¹ * φR * (eucNorm g + Real.sqrt d * G1) + Real.sqrt d * Kη * |w|) =
      12 * 64 ^ d * a⁻¹ * φR * eucNorm g + Real.sqrt d * Kη * |w| +
        φR * (64 ^ d * Real.sqrt d * (24 * a⁻¹ * G1 + G2)) := by ring
  linarith only [h12, h34, t1, t2, t3, t4, e]

/-- The `L²` bound of `ξ_i` and of its gradient on a good cube. -/
theorem ca2_xi_L2 [NeZero d] {a : ℝ} (ha : 0 < a) (R : TriadicCube d) {W : Set (Vec d)}
    (hRW : openCubeSet R ⊆ W) (u : H1Function W)
    (hint : ∀ k, |triadicCubeShift R k| + 3 / 2 * cubeScaleFactor R ≤ a) {γ : Vec d → ℝ}
    (hγ : ContDiff ℝ 2 γ) {G1 G2 : ℝ} (hG1 : 0 ≤ G1) (hG2 : 0 ≤ G2)
    (hb1 : ∀ x ∈ openCubeSet R, ‖fderiv ℝ γ x‖ ≤ G1)
    (hb2 : ∀ x ∈ openCubeSet R, ‖fderiv ℝ (fderiv ℝ γ) x‖ ≤ G2) {Kη : ℝ≥0}
    (hKη : ∀ i, LipschitzWith Kη (ca1_E (d := d) a i)) (i : Fin d) :
    cubeLpNorm R (2 : ℝ≥0∞) (ca2_xi R hRW u hγ ha hKη i).toFun +
        2 * cubeBesovW12EmbeddingConstant d * cubeScaleFactor R *
          cubeLpNorm R (2 : ℝ≥0∞) (fun x => euclideanNorm ((ca2_xi R hRW u hγ ha hKη i).grad x)) ≤
      12 * 64 ^ d * a⁻¹ * ca1_phi a (triadicCubeShift R) *
          cubeLpNorm R (2 : ℝ≥0∞) (fun x => u.toFun x - γ x) +
        2 * cubeBesovW12EmbeddingConstant d * cubeScaleFactor R *
          (12 * 64 ^ d * a⁻¹ * ca1_phi a (triadicCubeShift R) *
              cubeLpNorm R (2 : ℝ≥0∞) (fun x => Real.sqrt (vecNormSq (u.grad x))) +
            Real.sqrt d * Kη * cubeLpNorm R (2 : ℝ≥0∞) (fun x => u.toFun x - γ x)) +
        ca1_phi a (triadicCubeShift R) *
          (64 ^ d * (G1 + 2 * cubeBesovW12EmbeddingConstant d * cubeScaleFactor R * Real.sqrt d *
            (24 * a⁻¹ * G1 + G2))) := by
  have hγ1 : ContDiff ℝ 1 γ := hγ.of_le (by norm_num)
  set φR := ca1_phi a (triadicCubeShift R) with hφR
  have hφ0 : 0 ≤ φR := ca1_phi_nonneg a _
  set M : ℝ := 12 * 64 ^ d * a⁻¹ * φR with hM
  have hM0 : 0 ≤ M := by positivity
  set K2 : ℝ := 2 * cubeBesovW12EmbeddingConstant d * cubeScaleFactor R with hK2
  have hK20 : 0 ≤ K2 := by
    have := cubeBesovW12EmbeddingConstant_nonneg d
    have := cubeScaleFactor_pos' R
    positivity
  have hd0 : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  let ur : H1Function (openCubeSet R) := u.restrict (isOpen_openCubeSet R) hRW
  have hγR : MemLp γ 2 (normalizedCubeMeasure R) := (ca2_h1R R hγ1).memL2_normalizedCubeMeasure
  have hwL : MemLp (fun x => u.toFun x - γ x) 2 (normalizedCubeMeasure R) :=
    ur.memL2_normalizedCubeMeasure.sub hγR
  have heL : MemLp (fun x => Real.sqrt (vecNormSq (u.grad x))) 2 (normalizedCubeMeasure R) :=
    r1_memLp_grad_eucNorm R ur
  have hnorm : cubeLpNorm R (2 : ℝ≥0∞) (fun x => |u.toFun x - γ x|) =
      cubeLpNorm R (2 : ℝ≥0∞) (fun x => u.toFun x - γ x) := by
    unfold cubeLpNorm
    simp only [← Real.norm_eq_abs]
    exact congrArg ENNReal.toReal (eLpNorm_norm (f := fun x => u.toFun x - γ x) hwL.aestronglyMeasurable)
  set Wn := cubeLpNorm R (2 : ℝ≥0∞) (fun x => u.toFun x - γ x) with hWn
  set en := cubeLpNorm R (2 : ℝ≥0∞) (fun x => Real.sqrt (vecNormSq (u.grad x))) with hen
  have hW0 : 0 ≤ Wn := cubeLpNorm_nonneg _ _ _
  have he0 : 0 ≤ en := cubeLpNorm_nonneg _ _ _
  set c0 : ℝ := 64 ^ d * φR * G1 with hc0
  have hc00 : 0 ≤ c0 := by
    have : 0 ≤ G1 := hG1
    positivity
  -- the function itself
  have hfun : cubeLpNorm R (2 : ℝ≥0∞) (ca2_xi R hRW u hγ ha hKη i).toFun ≤ M * Wn + c0 := by
    have hH : MemLp (fun x => M * |u.toFun x - γ x| + c0) 2 (normalizedCubeMeasure R) :=
      (hwL.norm.const_mul M).add (memLp_const c0)
    have h1 := ca1_cubeLpNorm_le R (ca2_xi R hRW u hγ ha hKη i).memL2_normalizedCubeMeasure.aestronglyMeasurable
      hH zero_le_one (ca1_ae_openR R fun x hx => by
        rw [one_mul, abs_of_nonneg (add_nonneg (mul_nonneg hM0 (abs_nonneg _)) hc00), ca2_xi_toFun]
        exact ca2_xi_abs_le ha R hint hb1 hx i _)
    have h2 := Homogenization.cubeLpNorm_add_le R (2 : ℝ≥0∞) (fun x => M * |u.toFun x - γ x|)
      (fun _ => c0) (hwL.norm.const_mul M) (memLp_const c0) (by norm_num)
    rw [cubeLpNorm_const_mul, cubeLpNorm_const R _ _ (by norm_num), hnorm,
      Real.norm_of_nonneg hM0, Real.norm_of_nonneg hc00] at h2
    linarith only [h1, h2]
  -- the gradient
  set c1 : ℝ := φR * (64 ^ d * Real.sqrt d * (24 * a⁻¹ * G1 + G2)) with hc1
  have hc10 : 0 ≤ c1 := by
    have : 0 ≤ G1 := hG1
    have : 0 ≤ G2 := hG2
    positivity
  have hKd0 : 0 ≤ Real.sqrt d * Kη := by positivity
  have hgrad : cubeLpNorm R (2 : ℝ≥0∞) (fun x => euclideanNorm ((ca2_xi R hRW u hγ ha hKη i).grad x)) ≤
      M * en + Real.sqrt d * Kη * Wn + c1 := by
    have hH : MemLp (fun x => M * Real.sqrt (vecNormSq (u.grad x)) +
        Real.sqrt d * Kη * |u.toFun x - γ x| + c1) 2 (normalizedCubeMeasure R) :=
      ((heL.const_mul M).add (hwL.norm.const_mul _)).add (memLp_const c1)
    have hξm : MemLp (fun x => euclideanNorm ((ca2_xi R hRW u hγ ha hKη i).grad x)) 2
        (normalizedCubeMeasure R) := r1_memLp_grad_eucNorm R (ca2_xi R hRW u hγ ha hKη i)
    have h1 := ca1_cubeLpNorm_le R hξm.aestronglyMeasurable hH zero_le_one
      (ca1_ae_openR R fun x hx => by
        have hpos : 0 ≤ M * Real.sqrt (vecNormSq (u.grad x)) +
            Real.sqrt d * Kη * |u.toFun x - γ x| + c1 := by positivity
        rw [one_mul, abs_of_nonneg hpos, abs_of_nonneg (show 0 ≤ euclideanNorm ((ca2_xi R hRW u hγ ha hKη i).grad x) from Real.sqrt_nonneg _), ca2_xi_grad]
        exact ca2_xi_grad_le ha R hint hγ hG1 hb1 hb2 hKη hx i (u.grad x) (u.toFun x - γ x))
    have h2 := Homogenization.cubeLpNorm_add_le R (2 : ℝ≥0∞)
      (fun x => M * Real.sqrt (vecNormSq (u.grad x)) + Real.sqrt d * Kη * |u.toFun x - γ x|)
      (fun _ => c1) ((heL.const_mul M).add (hwL.norm.const_mul _)) (memLp_const c1) (by norm_num)
    have h3 := Homogenization.cubeLpNorm_add_le R (2 : ℝ≥0∞)
      (fun x => M * Real.sqrt (vecNormSq (u.grad x))) (fun x => Real.sqrt d * Kη * |u.toFun x - γ x|)
      (heL.const_mul M) (hwL.norm.const_mul _) (by norm_num)
    rw [cubeLpNorm_const_mul, cubeLpNorm_const_mul, hnorm, Real.norm_of_nonneg hM0,
      Real.norm_of_nonneg hKd0] at h3
    rw [cubeLpNorm_const R _ _ (by norm_num), Real.norm_of_nonneg hc10] at h2
    linarith only [h1, h2, h3]
  have hKK := mul_le_mul_of_nonneg_left hgrad hK20
  have e : M * Wn + K2 * (M * en + Real.sqrt d * Kη * Wn) +
      φR * (64 ^ d * (G1 + K2 * Real.sqrt d * (24 * a⁻¹ * G1 + G2))) =
      (M * Wn + c0) + K2 * (M * en + Real.sqrt d * Kη * Wn + c1) := by
    rw [hc0, hc1]; ring
  rw [e]
  linarith only [hfun, hKK]

/-- **The pairing on a good grid cube** for the datum field `Φ ∇γ - (u - γ) ∇Φ`. -/
theorem ca2_x_good [NeZero d] (R : TriadicCube d) {W : Set (Vec d)} (hRW : openCubeSet R ⊆ W)
    {lam Lam : ℝ} {A : CoeffField d} (hEll : IsEllipticFieldOn lam Lam W A)
    {S α1 β1 α2 β2 : ℝ} (hS : 0 ≤ S) (hα1 : 0 ≤ α1) (hβ1 : 0 ≤ β1) (hα2 : 0 ≤ α2) (hβ2 : 0 ≤ β2)
    (u : H1Function W) {f : Vec d → ℝ} (hf2 : MemLp f 2 (normalizedCubeMeasure R))
    (hfin : SuperdiffusionCLT.Section2.Norms.cubeLpENorm R
      (ENNReal.ofReal (sobStar d)).conjExponent f ≠ ⊤)
    (hu : IsWeakSolutionOn A W u f (fun _ => 0))
    (hBB : ∀ (u' : H1Function (openCubeSet (originCube d R.scale))) (f' : Vec d → ℝ),
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
    {a : ℝ} (ha : 0 < a) (hint : ∀ k, |triadicCubeShift R k| + 3 / 2 * cubeScaleFactor R ≤ a)
    {γ : Vec d → ℝ} (hγ : ContDiff ℝ 2 γ) {G1 G2 : ℝ} (hG1 : 0 ≤ G1) (hG2 : 0 ≤ G2)
    (hb1 : ∀ x ∈ openCubeSet R, ‖fderiv ℝ γ x‖ ≤ G1)
    (hb2 : ∀ x ∈ openCubeSet R, ‖fderiv ℝ (fderiv ℝ γ) x‖ ≤ G2) {Kη : ℝ≥0}
    (hKη : ∀ i, LipschitzWith Kη (ca1_E (d := d) a i)) :
    |cubeAverage R (fun x => vecDot (matVecMul (A x) (u.grad x))
        (ca2_G (ca1_Phi a) γ (fun y => u.toFun y - γ y) x))| ≤
      (S * (α2 * cubeLpNorm R (2 : ℝ≥0∞) (fun x => Real.sqrt (vecNormSq (u.grad x))) +
            β2 * cubeLpNorm R (ENNReal.ofReal (sobStar d)).conjExponent f) +
          (α1 * cubeLpNorm R (2 : ℝ≥0∞) (fun x => Real.sqrt (vecNormSq (u.grad x))) +
            β1 * cubeLpNorm R (ENNReal.ofReal (sobStar d)).conjExponent f)) *
        (12 * 64 ^ d * a⁻¹ * ca1_phi a (triadicCubeShift R) *
            cubeLpNorm R (2 : ℝ≥0∞) (fun x => u.toFun x - γ x) +
          2 * cubeBesovW12EmbeddingConstant d * cubeScaleFactor R *
            (12 * 64 ^ d * a⁻¹ * ca1_phi a (triadicCubeShift R) *
                cubeLpNorm R (2 : ℝ≥0∞) (fun x => Real.sqrt (vecNormSq (u.grad x))) +
              Real.sqrt d * Kη * cubeLpNorm R (2 : ℝ≥0∞) (fun x => u.toFun x - γ x)) +
          ca1_phi a (triadicCubeShift R) *
            (64 ^ d * (G1 + 2 * cubeBesovW12EmbeddingConstant d * cubeScaleFactor R * Real.sqrt d *
              (24 * a⁻¹ * G1 + G2)))) := by
  have key := ca2_cube_pair R hRW hEll hS hα1 hβ1 hα2 hβ2 u hf2 hfin hu hBB
    (fun i => ca2_xi R hRW u hγ ha hKη i)
    (Λ := 12 * 64 ^ d * a⁻¹ * ca1_phi a (triadicCubeShift R) *
            cubeLpNorm R (2 : ℝ≥0∞) (fun x => u.toFun x - γ x) +
          2 * cubeBesovW12EmbeddingConstant d * cubeScaleFactor R *
            (12 * 64 ^ d * a⁻¹ * ca1_phi a (triadicCubeShift R) *
                cubeLpNorm R (2 : ℝ≥0∞) (fun x => Real.sqrt (vecNormSq (u.grad x))) +
              Real.sqrt d * Kη * cubeLpNorm R (2 : ℝ≥0∞) (fun x => u.toFun x - γ x)) +
          ca1_phi a (triadicCubeShift R) *
            (64 ^ d * (G1 + 2 * cubeBesovW12EmbeddingConstant d * cubeScaleFactor R * Real.sqrt d *
              (24 * a⁻¹ * G1 + G2))))
    (fun i => ca2_xi_L2 ha R hRW u hint hγ hG1 hG2 hb1 hb2 hKη i)
  have hfun : (fun x => vecDot (matVecMul (A x) (u.grad x))
        (fun i => (ca2_xi R hRW u hγ ha hKη i).toFun x)) =
      fun x => vecDot (matVecMul (A x) (u.grad x)) (ca2_G (ca1_Phi a) γ (fun y => u.toFun y - γ y) x) := by
    funext x
    congr 1
    funext i
    rw [ca2_xi_toFun]
    simp only [ca2_G, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [show p12_grad (ca1_Phi (d := d) a) x i = ca1_E a i x from ca1_Phi_fderiv a i x]
    ring
  rw [hfun] at key
  exact key

end SuperdiffusionCLT.Section7
