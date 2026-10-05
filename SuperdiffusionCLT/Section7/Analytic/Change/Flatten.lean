/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Change.LinearEquation
public import SuperdiffusionCLT.Section7.Analytic.Change.ShearEquationB
public import SuperdiffusionCLT.Section7.Analytic.Geometry.AtlasTransform

/-!
# The exact flattening chart map

At a point `x₀` of the graph `{⟨e,y⟩ = ψ(Py)}` of a `C^{1,1}` chart the chart map is
`Ψ y = L (Φ y - Φ x₀)`, where `Φ = shear e ψ` is the volume preserving shear (it maps the graph
to `e^⊥`), and `L = O (1 + e ⊗ g)` with `g = ∇(ψ ∘ P)(x₀) ⟂ e`. The linear shear `1 + e ⊗ g` makes
`L DΦ(x₀) = O`, and the Householder reflection `O` sends the unit normal `(e - g)/|e - g|` of the
tilted plane to the target unit vector `u` (a coordinate axis in the application). Hence
`Ψ x₀ = 0`, `|det Ψ| = 1`, `DΨ(x₀) = O` is orthogonal, and the transported Laplacian
coefficient `Ã = DΨ DΨᵀ ∘ Ψ⁻¹` satisfies `Ã(0) = 1`. A single Householder reflection replaces the
composite of the tilt reflection and the axis reflection.

## Main results

* `Section7.flattenHouseholder`, `Section7.flattenLin`, `Section7.flattenMap`,
  `Section7.flattenInv`, `Section7.flattenCoeff`
* `Section7.flattenMap_flattenInv`, `Section7.flattenInv_flattenMap`, `Section7.flattenMap_base`
* `Section7.flattenLin_mul_shearJac`: `L DΦ(y) = O (1 + e ⊗ (∇G(x₀) - ∇G(y)))`
* `Section7.vecDot_flattenMap`, `Section7.mem_iff_flattenMap`: the half-space description.
-/

@[expose] public section

open MeasureTheory Homogenization Matrix

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-! ### Householder reflections -/

/-- The Householder reflection taking the unit vector `n` to the unit vector `u`
(the identity when `n = u`). -/
noncomputable def flattenHouseholder (n u : Vec d) : Mat d :=
  if n = u then 1 else 1 - (2 / ((n - u) ⬝ᵥ (n - u))) • vecMulVec (n - u) (n - u)

theorem flattenHouseholder_transpose (n u : Vec d) :
    (flattenHouseholder n u)ᵀ = flattenHouseholder n u := by
  unfold flattenHouseholder
  split_ifs
  · exact Matrix.transpose_one
  · rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul,
      Matrix.transpose_vecMulVec]

theorem flatten_op_smul (c : ℝ) (v : Vec d) : MulOpposite.op c • v = c • v := by
  ext i
  simp [mul_comm]

theorem flatten_reflect_sq (V : Mat d) (s : ℝ) (hs : s ≠ 0) (hV : V * V = s • V) :
    (1 - (2 / s) • V) * (1 - (2 / s) • V) = 1 := by
  have hmain : (1 - (2 / s) • V) * (1 - (2 / s) • V) =
      1 - (2 * (2 / s) - (2 / s) * (2 / s) * s) • V := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, hV]
    module
  have h0 : 2 * (2 / s) - (2 / s) * (2 / s) * s = 0 := by
    field_simp
    ring
  rw [hmain, h0, zero_smul, sub_zero]

theorem flattenHouseholder_mul_self (n u : Vec d) :
    flattenHouseholder n u * flattenHouseholder n u = 1 := by
  unfold flattenHouseholder
  split_ifs with h
  · exact Matrix.one_mul _
  · have hs : (n - u) ⬝ᵥ (n - u) ≠ 0 := fun h0 =>
      h (sub_eq_zero.1 (vecNormSq_eq_zero (x := n - u) h0))
    refine flatten_reflect_sq _ _ hs ?_
    rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul]

theorem flattenHouseholder_mulVec {n u : Vec d} (hn : n ⬝ᵥ n = 1) (hu : u ⬝ᵥ u = 1) :
    flattenHouseholder n u *ᵥ n = u := by
  unfold flattenHouseholder
  split_ifs with h
  · rw [Matrix.one_mulVec]; exact h
  · have hsd : (n - u) ⬝ᵥ (n - u) = 2 - 2 * (n ⬝ᵥ u) := by
      rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, hn, hu, dotProduct_comm u n]
      ring
    have hvn : (n - u) ⬝ᵥ n = 1 - n ⬝ᵥ u := by
      rw [sub_dotProduct, hn, dotProduct_comm u n]
    have hs : (n - u) ⬝ᵥ (n - u) ≠ 0 := fun h0 =>
      h (sub_eq_zero.1 (vecNormSq_eq_zero (x := n - u) h0))
    have h1 : 1 - n ⬝ᵥ u ≠ 0 := by
      intro h0
      apply hs
      rw [hsd]
      linarith only [h0]
    have hc : (2 / ((n - u) ⬝ᵥ (n - u))) * (1 - n ⬝ᵥ u) = 1 := by
      rw [hsd]
      have : (2 : ℝ) - 2 * (n ⬝ᵥ u) = 2 * (1 - n ⬝ᵥ u) := by ring
      rw [this]
      field_simp
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
      flatten_op_smul, hvn, smul_smul, hc, one_smul, sub_sub_cancel]

theorem flattenHouseholder_mulVec_target {n u : Vec d} (hn : n ⬝ᵥ n = 1) (hu : u ⬝ᵥ u = 1) :
    flattenHouseholder n u *ᵥ u = n := by
  have h := flattenHouseholder_mulVec hn hu
  have h2 := congrArg (fun w => flattenHouseholder n u *ᵥ w) h
  simp only [Matrix.mulVec_mulVec, flattenHouseholder_mul_self _ _, Matrix.one_mulVec] at h2
  exact h2.symm

/-- The reflection is an isometry in the form `u ⬝ O w = n ⬝ w`. -/
theorem dotProduct_flattenHouseholder_mulVec {n u : Vec d} (hn : n ⬝ᵥ n = 1) (hu : u ⬝ᵥ u = 1)
    (w : Vec d) : u ⬝ᵥ (flattenHouseholder n u *ᵥ w) = n ⬝ᵥ w := by
  rw [Matrix.dotProduct_mulVec]
  have : u ᵥ* flattenHouseholder n u = flattenHouseholder n u *ᵥ u := by
    conv_lhs => rw [← flattenHouseholder_transpose n u]
    exact Matrix.vecMul_transpose _ _
  rw [this, flattenHouseholder_mulVec_target hn hu]

/-- `O Oᵀ = 1`. -/
theorem flattenHouseholder_mul_transpose (n u : Vec d) :
    flattenHouseholder n u * (flattenHouseholder n u)ᵀ = 1 := by
  rw [flattenHouseholder_transpose]
  exact flattenHouseholder_mul_self _ _

/-! ### The tilt and the linear part -/

/-- The unit normal `(e - g)/|e - g|` of the tilted plane. -/
noncomputable def flattenNormal (e g : Vec d) : Vec d :=
  (Real.sqrt (1 + g ⬝ᵥ g))⁻¹ • (e - g)

theorem flattenNormal_dot {e g : Vec d} (he : e ⬝ᵥ e = 1) (hg : e ⬝ᵥ g = 0) :
    flattenNormal e g ⬝ᵥ flattenNormal e g = 1 := by
  unfold flattenNormal
  have hpos : 0 < 1 + g ⬝ᵥ g := by
    have : 0 ≤ g ⬝ᵥ g := vecNormSq_nonneg g
    linarith only [this]
  have hsq := Real.sq_sqrt hpos.le
  have hne : Real.sqrt (1 + g ⬝ᵥ g) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  rw [smul_dotProduct, dotProduct_smul, sub_dotProduct, dotProduct_sub, dotProduct_sub, he, hg,
    dotProduct_comm g e, hg, smul_eq_mul, smul_eq_mul]
  have : (Real.sqrt (1 + g ⬝ᵥ g))⁻¹ * ((Real.sqrt (1 + g ⬝ᵥ g))⁻¹ * (1 - 0 - (0 - g ⬝ᵥ g))) = 1 := by
    rw [← mul_assoc, ← mul_inv, ← sq, hsq]
    field_simp
    ring
  exact this

/-- The linear shear `1 + e ⊗ g`. -/
noncomputable def flattenTilt (e g : Vec d) : Mat d := 1 + vecMulVec e g

/-- The inverse linear shear `1 - e ⊗ g`. -/
noncomputable def flattenTiltInv (e g : Vec d) : Mat d := 1 - vecMulVec e g

theorem flatten_rank1_sq {e g : Vec d} (hg : g ⬝ᵥ e = 0) :
    vecMulVec e g * vecMulVec e g = 0 := by
  rw [Matrix.vecMulVec_mul_vecMulVec, hg, zero_smul]
  ext i j
  simp [Matrix.vecMulVec_apply]

theorem flattenTilt_mul_inv {e g : Vec d} (hg : g ⬝ᵥ e = 0) :
    flattenTilt e g * flattenTiltInv e g = 1 := by
  unfold flattenTilt flattenTiltInv
  simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    flatten_rank1_sq hg]
  abel

theorem flattenTiltInv_mul {e g : Vec d} (hg : g ⬝ᵥ e = 0) :
    flattenTiltInv e g * flattenTilt e g = 1 := by
  unfold flattenTilt flattenTiltInv
  simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    flatten_rank1_sq hg]
  abel

/-- The linear part `L = O (1 + e ⊗ g)` of the chart map. -/
noncomputable def flattenLin (e g u : Vec d) : Mat d :=
  flattenHouseholder (flattenNormal e g) u * flattenTilt e g

/-- Its inverse `(1 - e ⊗ g) O`. -/
noncomputable def flattenLinInv (e g u : Vec d) : Mat d :=
  flattenTiltInv e g * flattenHouseholder (flattenNormal e g) u

theorem flattenLin_mul_inv {e g u : Vec d} (hg : e ⬝ᵥ g = 0) : flattenLin e g u * flattenLinInv e g u = 1 := by
  have hg' : g ⬝ᵥ e = 0 := by rw [dotProduct_comm]; exact hg
  unfold flattenLin flattenLinInv
  calc _ = flattenHouseholder (flattenNormal e g) u * (flattenTilt e g * flattenTiltInv e g) *
        flattenHouseholder (flattenNormal e g) u := by simp only [Matrix.mul_assoc]
    _ = 1 := by
      rw [flattenTilt_mul_inv hg', Matrix.mul_one, flattenHouseholder_mul_self _ _]

theorem flattenLinInv_mul {e g u : Vec d} (hg : e ⬝ᵥ g = 0) : flattenLinInv e g u * flattenLin e g u = 1 := by
  have hg' : g ⬝ᵥ e = 0 := by rw [dotProduct_comm]; exact hg
  unfold flattenLin flattenLinInv
  calc _ = flattenTiltInv e g * (flattenHouseholder (flattenNormal e g) u *
        flattenHouseholder (flattenNormal e g) u) * flattenTilt e g := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
      rw [flattenHouseholder_mul_self _ _, Matrix.mul_one, flattenTiltInv_mul hg']

theorem isUnit_flattenLin {e g u : Vec d} (hg : e ⬝ᵥ g = 0) : IsUnit (flattenLin e g u) :=
  (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 fun h0 => by
    have := congrArg Matrix.det (flattenLin_mul_inv (u := u) hg)
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this)

theorem flattenLin_inv_eq {e g u : Vec d} (hg : e ⬝ᵥ g = 0) : (flattenLin e g u)⁻¹ = flattenLinInv e g u :=
  Matrix.inv_eq_right_inv (flattenLin_mul_inv hg)

/-- `|det L| = 1`. -/
theorem abs_det_flattenLin {e g u : Vec d} (hg : e ⬝ᵥ g = 0) : |(flattenLin e g u).det| = 1 := by
  have hO := congrArg Matrix.det (flattenHouseholder_mul_self (flattenNormal e g) u)
  rw [Matrix.det_mul, Matrix.det_one] at hO
  have hT : (flattenTilt e g).det = 1 := by
    unfold flattenTilt
    rw [Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow]
    rw [dotProduct_comm, hg]
    simp
  unfold flattenLin
  rw [Matrix.det_mul, hT, mul_one]
  have : |(flattenHouseholder (flattenNormal e g) u).det| ^ 2 = 1 := by
    rw [sq_abs, sq]; exact hO
  nlinarith only [this, abs_nonneg (flattenHouseholder (flattenNormal e g) u).det]

/-- `L DΦ(y) = O (1 + e ⊗ (g - γ))` where `DΦ(y) = 1 - e ⊗ γ`. -/
theorem flattenLin_mul_jac {e g u : Vec d} (hg : e ⬝ᵥ g = 0) (γ : Vec d) :
    flattenLin e g u * (1 - vecMulVec e γ) =
      flattenHouseholder (flattenNormal e g) u * (1 + vecMulVec e (g - γ)) := by
  have hg' : g ⬝ᵥ e = 0 := by rw [dotProduct_comm]; exact hg
  unfold flattenLin flattenTilt
  rw [Matrix.mul_assoc]
  congr 1
  simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
  rw [Matrix.vecMulVec_mul_vecMulVec, hg', zero_smul]
  have h0 : vecMulVec e (0 : Vec d) = 0 := by ext i j; simp [Matrix.vecMulVec_apply]
  have h1 : vecMulVec e (g - γ) = vecMulVec e g - vecMulVec e γ := by
    ext i j; simp [Matrix.vecMulVec_apply, mul_sub]
  rw [h0, h1]
  abel

/-! ### The chart map and its inverse -/

theorem flatten_matVecMul_eq (A : Mat d) (x : Vec d) : matVecMul A x = A *ᵥ x := rfl

/-- The exact chart map `Ψ y = L (Φ y - Φ x₀)`, `Φ = shear e ψ`,
`L = O (1 + e ⊗ ∇(ψ ∘ P)(x₀))`, `O` the Householder reflection taking the unit normal of the
tilted plane to the target `u`. -/
noncomputable def flattenMap (e : Vec d) (ψ : Vec d → ℝ) (x₀ u : Vec d) (y : Vec d) : Vec d :=
  matVecMul (flattenLin e (projGradVec e ψ x₀) u) (shear e ψ y - shear e ψ x₀)

/-- The explicit inverse `Ψ⁻¹ z = Φ⁻¹ (L⁻¹ z + Φ x₀)`. -/
noncomputable def flattenInv (e : Vec d) (ψ : Vec d → ℝ) (x₀ u : Vec d) (z : Vec d) : Vec d :=
  shear e (-ψ) (matVecMul (flattenLinInv e (projGradVec e ψ x₀) u) z + shear e ψ x₀)

theorem flattenInv_flattenMap {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {u : Vec d} (x₀ y : Vec d) :
    flattenInv e ψ x₀ u (flattenMap e ψ x₀ u y) = y := by
  have hg := vecDot_self_projGradVec he hψ x₀
  unfold flattenInv flattenMap
  simp only [flatten_matVecMul_eq]
  rw [Matrix.mulVec_mulVec, flattenLinInv_mul hg, Matrix.one_mulVec, sub_add_cancel,
    shear_neg_shear he]

theorem flattenMap_flattenInv {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {u : Vec d} (x₀ z : Vec d) :
    flattenMap e ψ x₀ u (flattenInv e ψ x₀ u z) = z := by
  have hg := vecDot_self_projGradVec he hψ x₀
  unfold flattenInv flattenMap
  simp only [flatten_matVecMul_eq]
  rw [shear_shear_neg he, add_sub_cancel_right, Matrix.mulVec_mulVec,
    flattenLin_mul_inv hg, Matrix.one_mulVec]

theorem flattenMap_base (e : Vec d) (ψ : Vec d → ℝ) (x₀ u : Vec d) :
    flattenMap e ψ x₀ u x₀ = 0 := by
  unfold flattenMap
  rw [sub_self, flatten_matVecMul_eq, Matrix.mulVec_zero]

theorem flattenInv_zero {e : Vec d} (he : vecNormSq e = 1) (ψ : Vec d → ℝ) (x₀ u : Vec d) :
    flattenInv e ψ x₀ u 0 = x₀ := by
  unfold flattenInv
  rw [flatten_matVecMul_eq, Matrix.mulVec_zero, zero_add, shear_neg_shear he]

/-! ### The half-space description -/

theorem vecDot_flattenLin {e g u : Vec d} (he : e ⬝ᵥ e = 1) (hg : e ⬝ᵥ g = 0)
    (hu : u ⬝ᵥ u = 1) (z : Vec d) :
    u ⬝ᵥ (flattenLin e g u *ᵥ z) = (Real.sqrt (1 + g ⬝ᵥ g))⁻¹ * (e ⬝ᵥ z) := by
  have hg' : g ⬝ᵥ e = 0 := by rw [dotProduct_comm]; exact hg
  have hn := flattenNormal_dot he hg
  unfold flattenLin
  rw [← Matrix.mulVec_mulVec, dotProduct_flattenHouseholder_mulVec hn hu]
  unfold flattenNormal flattenTilt
  rw [smul_dotProduct, smul_eq_mul]
  congr 1
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec,
    flatten_op_smul, sub_dotProduct, dotProduct_add, dotProduct_add,
    dotProduct_smul, dotProduct_smul, he, hg', smul_eq_mul, smul_eq_mul]
  ring

theorem vecDot_shear {e : Vec d} (he : vecNormSq e = 1) (ψ : Vec d → ℝ) (y : Vec d) :
    vecDot e (shear e ψ y) = vecDot e y - ψ (y - vecDot e y • e) :=
  vecDot_sub_smul_self he y _

/-- The `u`-coordinate of the chart image is `(1 + |∇G(x₀)|²)^{-1/2}` times the height of `y`
above the graph. -/
theorem vecDot_flattenMap {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {u : Vec d} (hu : vecNormSq u = 1) {x₀ : Vec d}
    (hx₀ : vecDot e x₀ = ψ (x₀ - vecDot e x₀ • e)) (y : Vec d) :
    vecDot u (flattenMap e ψ x₀ u y) =
      (Real.sqrt (1 + projGradVec e ψ x₀ ⬝ᵥ projGradVec e ψ x₀))⁻¹ *
        (vecDot e y - ψ (y - vecDot e y • e)) := by
  have hg := vecDot_self_projGradVec he hψ x₀
  unfold flattenMap
  rw [flatten_matVecMul_eq]
  change u ⬝ᵥ _ = _
  rw [vecDot_flattenLin he hg hu, dotProduct_sub]
  have h1 := vecDot_shear he ψ y
  have h2 := vecDot_shear he ψ x₀
  change e ⬝ᵥ shear e ψ y = _ at h1
  change e ⬝ᵥ shear e ψ x₀ = _ at h2
  rw [h1, h2, ← hx₀]
  congr 1
  ring

/-- Inside a chart ball, membership in `U` is the sign of the `u`-coordinate of the chart image. -/
theorem mem_iff_flattenMap {U : Set (Vec d)} {e : Vec d} (he : vecNormSq e = 1)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {u : Vec d} (hu : vecNormSq u = 1)
    {x₀ : Vec d} (hx₀ : vecDot e x₀ = ψ (x₀ - vecDot e x₀ • e)) {r : ℝ}
    (hch : ∀ y ∈ Metric.ball x₀ r, (y ∈ U ↔ vecDot e y < ψ (y - vecDot e y • e)))
    {y : Vec d} (hy : y ∈ Metric.ball x₀ r) :
    y ∈ U ↔ vecDot u (flattenMap e ψ x₀ u y) < 0 := by
  have hpos : 0 < (Real.sqrt (1 + projGradVec e ψ x₀ ⬝ᵥ projGradVec e ψ x₀))⁻¹ := by
    have : 0 ≤ projGradVec e ψ x₀ ⬝ᵥ projGradVec e ψ x₀ := vecNormSq_nonneg _
    exact inv_pos.2 (Real.sqrt_pos.2 (by linarith only [this]))
  rw [vecDot_flattenMap he hψ hu hx₀, hch y hy]
  constructor
  · intro h
    exact mul_neg_of_pos_of_neg hpos (sub_neg.2 h)
  · intro h
    by_contra hge
    have : 0 ≤ vecDot e y - ψ (y - vecDot e y • e) := sub_nonneg.2 (not_lt.1 hge)
    exact absurd h (not_lt.2 (mul_nonneg hpos.le this))

/-! ### The transported coefficient -/

/-- The transported coefficient `Ã(z) = DΨ a DΨᵀ` evaluated at `Ψ⁻¹ z`, with
`DΨ(y) = L DΦ(y)`. -/
noncomputable def flattenCoeff (e : Vec d) (ψ : Vec d → ℝ) (x₀ u : Vec d) (a : CoeffField d)
    (z : Vec d) : Mat d :=
  flattenLin e (projGradVec e ψ x₀) u *
      (shearJac e ψ (flattenInv e ψ x₀ u z) * a (flattenInv e ψ x₀ u z) *
        matTranspose (shearJac e ψ (flattenInv e ψ x₀ u z))) *
    (flattenLin e (projGradVec e ψ x₀) u)ᵀ

theorem flattenLin_mul_shearJac (e : Vec d) {ψ : Vec d → ℝ} (u : Vec d) {x₀ : Vec d}
    (hg : vecDot e (projGradVec e ψ x₀) = 0) (y : Vec d) :
    flattenLin e (projGradVec e ψ x₀) u * shearJac e ψ y =
      flattenHouseholder (flattenNormal e (projGradVec e ψ x₀)) u *
        (1 + vecMulVec e (projGradVec e ψ x₀ - projGradVec e ψ y)) :=
  flattenLin_mul_jac hg _

theorem flattenCoeff_eq {e : Vec d} {ψ : Vec d → ℝ} {x₀ : Vec d}
    (hg : vecDot e (projGradVec e ψ x₀) = 0) (u : Vec d) (a : CoeffField d) (z : Vec d) :
    flattenCoeff e ψ x₀ u a z =
      (flattenHouseholder (flattenNormal e (projGradVec e ψ x₀)) u *
          (1 + vecMulVec e (projGradVec e ψ x₀ - projGradVec e ψ (flattenInv e ψ x₀ u z)))) *
        a (flattenInv e ψ x₀ u z) *
      (flattenHouseholder (flattenNormal e (projGradVec e ψ x₀)) u *
          (1 + vecMulVec e (projGradVec e ψ x₀ - projGradVec e ψ (flattenInv e ψ x₀ u z))))ᵀ := by
  rw [← flattenLin_mul_shearJac e u hg]
  unfold flattenCoeff matTranspose
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]

end SuperdiffusionCLT.Section7
