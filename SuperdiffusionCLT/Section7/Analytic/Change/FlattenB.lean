/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Change.Flatten

/-!
# Estimates and transport for the flattening chart map

* `Section7.flattenCoeff_one_sub_le`: for `a ≡ 1` (the Laplacian) every entry of `Ã - 1`
  is at most `flattenLipConst d M₁ M₂ * ‖z‖`, where `M₁` bounds `‖Dψ‖` and `M₂` is the Lipschitz
  constant of `Dψ` (sup norm on `Vec d`, so the constant carries `d`). The bound is global in
  `z`; the chart radius only enters through the half-space description
  `Section7.mem_iff_flattenMap`.
* `Section7.IsWeakSolutionOn.flatten`: transport of a weak solution under `L ∘ Φ`, the chart map
  up to the translation by `L Φ x₀`, with coefficient `Ã(· - L Φ x₀)`.
* `Section7.measurePreserving_flattenMap`.
-/

@[expose] public section

open MeasureTheory Homogenization Matrix

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-! ### Elementary bounds -/

theorem flatten_abs_dot_le (a b : Vec d) : |a ⬝ᵥ b| ≤ d * (‖a‖ * ‖b‖) := by
  unfold dotProduct
  calc |∑ i, a i * b i| ≤ ∑ i, |a i * b i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, ‖a‖ * ‖b‖ := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]
        exact mul_le_mul (by simpa using norm_le_pi_norm a i)
          (by simpa using norm_le_pi_norm b i) (abs_nonneg _) (norm_nonneg _)
    _ = d * (‖a‖ * ‖b‖) := by simp

theorem flatten_abs_entry_le_one {O : Mat d} (hO : O * Oᵀ = 1) (i k : Fin d) : |O i k| ≤ 1 := by
  have h := congrFun (congrFun hO i) i
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  simp only [Matrix.transpose_apply] at h
  have h1 : O i k * O i k ≤ 1 := by
    rw [← h]
    exact Finset.single_le_sum (f := fun j => O i j * O i j) (fun _ _ => mul_self_nonneg _)
      (Finset.mem_univ k)
  exact abs_le_one_iff_mul_self_le_one.2 h1

theorem flatten_abs_mulVec_le {A : Mat d} (hA : ∀ i k, |A i k| ≤ 1) (v : Vec d) (i : Fin d) :
    |(A *ᵥ v) i| ≤ d * ‖v‖ := by
  have h1 : ‖A i‖ ≤ 1 :=
    (pi_norm_le_iff_of_nonneg zero_le_one).2 fun k => by simpa using hA i k
  have h2 : |A i ⬝ᵥ v| ≤ d * (‖A i‖ * ‖v‖) := flatten_abs_dot_le (A i) v
  have h3 : ‖A i‖ * ‖v‖ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  have h4 : (d : ℝ) * (‖A i‖ * ‖v‖) ≤ d * (1 * ‖v‖) :=
    mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg d)
  calc |(A *ᵥ v) i| = |A i ⬝ᵥ v| := rfl
    _ ≤ d * ‖v‖ := by linarith only [h2, h4]

theorem flatten_norm_mulVec_le {A : Mat d} (hA : ∀ i k, |A i k| ≤ 1) (v : Vec d) :
    ‖A *ᵥ v‖ ≤ d * ‖v‖ :=
  (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => by
    simpa using flatten_abs_mulVec_le hA v i

/-- The gradient of `ψ ∘ P` as the derivative of `ψ` at the projection applied to `P eᵢ`. -/
theorem flatten_projGrad_eq {e : Vec d} {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (y : Vec d) (i : Fin d) :
    projGrad e ψ i y = fderiv ℝ ψ (y - vecDot e y • e) (Pi.single i 1 - e i • e) := by
  have hchain : fderiv ℝ (projComp e ψ) y = (fderiv ℝ ψ (projCLM e y)).comp (projCLM e) := by
    rw [projComp_eq]
    rw [fderiv_comp y ((hψ.differentiable (by simp)) _) (projCLM e).differentiableAt,
      ContinuousLinearMap.fderiv]
  have hdot : vecDot e (Pi.single i (1 : ℝ) : Vec d) = e i := by
    simp [vecDot, Pi.single_apply]
  unfold projGrad
  rw [hchain, ContinuousLinearMap.comp_apply, projCLM_apply, projCLM_apply, hdot]

theorem flatten_norm_projVec_le {e : Vec d} (he : vecNormSq e = 1) (i : Fin d) :
    ‖(Pi.single i (1 : ℝ) : Vec d) - e i • e‖ ≤ 2 := by
  refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun k => ?_
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs]
  have h1 : |(Pi.single i (1 : ℝ) : Vec d) k| ≤ 1 := by
    by_cases h : k = i <;> simp [h]
  have h2 : |e i * e k| ≤ 1 := by
    rw [abs_mul]
    calc |e i| * |e k| ≤ 1 * 1 :=
          mul_le_mul (abs_apply_le_one he i) (abs_apply_le_one he k) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul _
  calc |(Pi.single i (1 : ℝ) : Vec d) k - e i * e k|
      ≤ |(Pi.single i (1 : ℝ) : Vec d) k| + |e i * e k| := abs_sub _ _
    _ ≤ 1 + 1 := add_le_add h1 h2
    _ = 2 := by norm_num

theorem flatten_abs_projGrad_le {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {M₁ : ℝ} (hb1 : ∀ y, ‖fderiv ℝ ψ y‖ ≤ M₁) (y : Vec d)
    (i : Fin d) : |projGrad e ψ i y| ≤ 2 * M₁ := by
  have hM : 0 ≤ M₁ := (norm_nonneg _).trans (hb1 0)
  rw [flatten_projGrad_eq hψ]
  calc |fderiv ℝ ψ (y - vecDot e y • e) (Pi.single i 1 - e i • e)|
      = ‖fderiv ℝ ψ (y - vecDot e y • e) (Pi.single i 1 - e i • e)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖fderiv ℝ ψ (y - vecDot e y • e)‖ * ‖(Pi.single i (1 : ℝ) : Vec d) - e i • e‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ M₁ * 2 := mul_le_mul (hb1 _) (flatten_norm_projVec_le he i) (norm_nonneg _) hM
    _ = 2 * M₁ := mul_comm _ _

theorem flatten_abs_projGrad_sub_le {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {M₂ : ℝ} (hM₂ : 0 ≤ M₂)
    (hb2 : ∀ y z, ‖fderiv ℝ ψ y - fderiv ℝ ψ z‖ ≤ M₂ * ‖y - z‖) (x y : Vec d) (i : Fin d) :
    |projGrad e ψ i x - projGrad e ψ i y| ≤ 2 * M₂ * ((1 + d) * ‖x - y‖) := by
  rw [flatten_projGrad_eq hψ, flatten_projGrad_eq hψ, ← _root_.sub_apply]
  have h1 := hb2 (x - vecDot e x • e) (y - vecDot e y • e)
  have h2 := norm_proj_sub_le he x y
  have h3 : M₂ * ‖(x - vecDot e x • e) - (y - vecDot e y • e)‖ ≤ M₂ * ((1 + d) * ‖x - y‖) :=
    mul_le_mul_of_nonneg_left h2 hM₂
  calc |(fderiv ℝ ψ (x - vecDot e x • e) - fderiv ℝ ψ (y - vecDot e y • e))
          (Pi.single i 1 - e i • e)|
      = ‖(fderiv ℝ ψ (x - vecDot e x • e) - fderiv ℝ ψ (y - vecDot e y • e))
          (Pi.single i 1 - e i • e)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖fderiv ℝ ψ (x - vecDot e x • e) - fderiv ℝ ψ (y - vecDot e y • e)‖ *
          ‖(Pi.single i (1 : ℝ) : Vec d) - e i • e‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (M₂ * ((1 + d) * ‖x - y‖)) * 2 :=
        mul_le_mul (h1.trans h3) (flatten_norm_projVec_le he i) (norm_nonneg _)
          (mul_nonneg hM₂ (by positivity))
    _ = 2 * M₂ * ((1 + d) * ‖x - y‖) := by ring

theorem flatten_norm_projGradVec_sub_le {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {M₂ : ℝ} (hM₂ : 0 ≤ M₂)
    (hb2 : ∀ y z, ‖fderiv ℝ ψ y - fderiv ℝ ψ z‖ ≤ M₂ * ‖y - z‖) (x y : Vec d) :
    ‖projGradVec e ψ x - projGradVec e ψ y‖ ≤ 2 * M₂ * ((1 + d) * ‖x - y‖) :=
  (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => by
    simpa [projGradVec] using flatten_abs_projGrad_sub_le he hψ hM₂ hb2 x y i

theorem flatten_norm_projGradVec_le {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {M₁ : ℝ} (hb1 : ∀ y, ‖fderiv ℝ ψ y‖ ≤ M₁) (y : Vec d) :
    ‖projGradVec e ψ y‖ ≤ 2 * M₁ := by
  have hM : 0 ≤ M₁ := (norm_nonneg _).trans (hb1 0)
  exact (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => by
    simpa [projGradVec] using flatten_abs_projGrad_le he hψ hb1 y i

theorem flatten_nonneg_of_lipschitz {ψ : Vec d → ℝ} {M₂ : ℝ}
    (hb2 : ∀ y z, ‖fderiv ℝ ψ y - fderiv ℝ ψ z‖ ≤ M₂ * ‖y - z‖) (i : Fin d) : 0 ≤ M₂ := by
  have h := hb2 (Pi.single i 1) 0
  have hn : 0 < ‖(Pi.single i (1 : ℝ) : Vec d) - 0‖ := by
    rw [sub_zero, norm_pos_iff]
    intro h0
    have := congrFun h0 i
    simp at this
  nlinarith only [h, hn, norm_nonneg (fderiv ℝ ψ (Pi.single i 1) - fderiv ℝ ψ 0)]

/-! ### The Gram matrix of `L DΦ` -/

theorem flatten_gram {O : Mat d} (hO : O * Oᵀ = 1) (e δ : Vec d) :
    (O * (1 + vecMulVec e δ)) * 1 * (O * (1 + vecMulVec e δ))ᵀ =
      1 + vecMulVec (O *ᵥ δ) (O *ᵥ e) + vecMulVec (O *ᵥ e) (O *ᵥ δ) +
        (δ ⬝ᵥ δ) • vecMulVec (O *ᵥ e) (O *ᵥ e) := by
  have hP : O * (1 + vecMulVec e δ) = O + vecMulVec (O *ᵥ e) δ := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_vecMulVec]
  rw [hP, Matrix.mul_one, Matrix.transpose_add, Matrix.transpose_vecMulVec, Matrix.add_mul,
    Matrix.mul_add, Matrix.mul_add, hO, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
    Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul, Matrix.vecMul_transpose]
  abel

theorem flatten_entry_le {O : Mat d} (hO : O * Oᵀ = 1) {e : Vec d} (he : vecNormSq e = 1)
    (δ : Vec d) (i j : Fin d) :
    |((1 : Mat d) + vecMulVec (O *ᵥ δ) (O *ᵥ e) + vecMulVec (O *ᵥ e) (O *ᵥ δ) +
        (δ ⬝ᵥ δ) • vecMulVec (O *ᵥ e) (O *ᵥ e)) i j - (1 : Mat d) i j| ≤
      2 * d ^ 2 * ‖δ‖ + d ^ 3 * ‖δ‖ ^ 2 := by
  have hA := flatten_abs_entry_le_one hO
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hw : ∀ k, |(O *ᵥ e) k| ≤ d := fun k => by
    have := flatten_abs_mulVec_le hA e k
    have h1 : ‖e‖ ≤ 1 := norm_le_one_of_vecNormSq he
    nlinarith only [this, h1, hd]
  have hv : ∀ k, |(O *ᵥ δ) k| ≤ d * ‖δ‖ := flatten_abs_mulVec_le hA δ
  have hc : |δ ⬝ᵥ δ| ≤ d * (‖δ‖ * ‖δ‖) := flatten_abs_dot_le δ δ
  have hn := norm_nonneg δ
  have e1 : |(O *ᵥ δ) i| * |(O *ᵥ e) j| ≤ (d * ‖δ‖) * d :=
    mul_le_mul (hv i) (hw j) (abs_nonneg _) (by positivity)
  have e2 : |(O *ᵥ e) i| * |(O *ᵥ δ) j| ≤ d * (d * ‖δ‖) :=
    mul_le_mul (hw i) (hv j) (abs_nonneg _) hd
  have e3 : |δ ⬝ᵥ δ| * (|(O *ᵥ e) i| * |(O *ᵥ e) j|) ≤ (d * (‖δ‖ * ‖δ‖)) * (d * d) :=
    mul_le_mul hc (mul_le_mul (hw i) (hw j) (abs_nonneg _) hd) (by positivity) (by positivity)
  have hexp : ((1 : Mat d) + vecMulVec (O *ᵥ δ) (O *ᵥ e) + vecMulVec (O *ᵥ e) (O *ᵥ δ) +
        (δ ⬝ᵥ δ) • vecMulVec (O *ᵥ e) (O *ᵥ e)) i j - (1 : Mat d) i j =
      (O *ᵥ δ) i * (O *ᵥ e) j + (O *ᵥ e) i * (O *ᵥ δ) j +
        (δ ⬝ᵥ δ) * ((O *ᵥ e) i * (O *ᵥ e) j) := by
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
    ring
  rw [hexp]
  calc _ ≤ |(O *ᵥ δ) i * (O *ᵥ e) j + (O *ᵥ e) i * (O *ᵥ δ) j| +
        |(δ ⬝ᵥ δ) * ((O *ᵥ e) i * (O *ᵥ e) j)| := abs_add_le _ _
    _ ≤ (|(O *ᵥ δ) i * (O *ᵥ e) j| + |(O *ᵥ e) i * (O *ᵥ δ) j|) +
        |(δ ⬝ᵥ δ) * ((O *ᵥ e) i * (O *ᵥ e) j)| := by
        gcongr
        exact abs_add_le _ _
    _ ≤ 2 * d ^ 2 * ‖δ‖ + d ^ 3 * ‖δ‖ ^ 2 := by
        rw [abs_mul, abs_mul, abs_mul, abs_mul]
        nlinarith only [e1, e2, e3]

/-! ### The Lipschitz bound -/

/-- The explicit constant of the Lipschitz bound: it depends only on `d`, `M₁` and `M₂`. -/
noncomputable def flattenLipConst (d : ℕ) (M₁ M₂ : ℝ) : ℝ :=
  (2 * d ^ 2 + 4 * d ^ 3 * M₁) *
    (2 * M₂ * (1 + d) * ((1 + (1 + d) * M₁) * (d * (1 + 2 * d * M₁))))

theorem flatten_norm_linInv_le {e g u : Vec d} (he : vecNormSq e = 1)
    {G : ℝ} (hG : ‖g‖ ≤ G) (z : Vec d) :
    ‖flattenLinInv e g u *ᵥ z‖ ≤ d * (1 + d * G) * ‖z‖ := by
  have hOO := flattenHouseholder_mul_transpose (flattenNormal e g) u
  have hA := flatten_abs_entry_le_one hOO
  set w : Vec d := flattenHouseholder (flattenNormal e g) u *ᵥ z with hw
  have hwn : ‖w‖ ≤ d * ‖z‖ := flatten_norm_mulVec_le hA z
  have hrew : flattenLinInv e g u *ᵥ z = w - (g ⬝ᵥ w) • e := by
    unfold flattenLinInv flattenTiltInv
    rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec,
      flatten_op_smul]
  have hG0 : 0 ≤ G := (norm_nonneg g).trans hG
  have h1 : |g ⬝ᵥ w| ≤ d * (G * (d * ‖z‖)) :=
    (flatten_abs_dot_le g w).trans (mul_le_mul_of_nonneg_left
      (mul_le_mul hG hwn (norm_nonneg _) hG0) (Nat.cast_nonneg d))
  have h2 : ‖(g ⬝ᵥ w) • e‖ ≤ d * (G * (d * ‖z‖)) := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |g ⬝ᵥ w| * ‖e‖ ≤ (d * (G * (d * ‖z‖))) * 1 :=
          mul_le_mul h1 (norm_le_one_of_vecNormSq he) (norm_nonneg _) (by positivity)
      _ = _ := mul_one _
  rw [hrew]
  calc ‖w - (g ⬝ᵥ w) • e‖ ≤ ‖w‖ + ‖(g ⬝ᵥ w) • e‖ := norm_sub_le _ _
    _ ≤ d * ‖z‖ + d * (G * (d * ‖z‖)) := add_le_add hwn h2
    _ = d * (1 + d * G) * ‖z‖ := by ring

/-- **Lipschitz bound.** For the Laplacian (`a ≡ 1`) the transported coefficient satisfies
`|Ã(z)ᵢⱼ - δᵢⱼ| ≤ C(d, M₁, M₂) ‖z‖` for all `z`. -/
theorem flattenCoeff_one_sub_le {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {M₁ M₂ : ℝ} (hb1 : ∀ y, ‖fderiv ℝ ψ y‖ ≤ M₁)
    (hb2 : ∀ y z, ‖fderiv ℝ ψ y - fderiv ℝ ψ z‖ ≤ M₂ * ‖y - z‖) {u : Vec d}
    (x₀ z : Vec d) (i j : Fin d) :
    |flattenCoeff e ψ x₀ u (fun _ => (1 : Mat d)) z i j - (1 : Mat d) i j| ≤
      flattenLipConst d M₁ M₂ * ‖z‖ := by
  have hg := vecDot_self_projGradVec he hψ x₀
  have hOO := flattenHouseholder_mul_transpose (flattenNormal e (projGradVec e ψ x₀)) u
  have hM₁ : 0 ≤ M₁ := (norm_nonneg _).trans (hb1 0)
  have hM₂ : 0 ≤ M₂ := flatten_nonneg_of_lipschitz hb2 i
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  set y := flattenInv e ψ x₀ u z with hy
  set δ := projGradVec e ψ x₀ - projGradVec e ψ y with hδ
  -- entrywise formula
  have hform : flattenCoeff e ψ x₀ u (fun _ => (1 : Mat d)) z =
      1 + vecMulVec (flattenHouseholder (flattenNormal e (projGradVec e ψ x₀)) u *ᵥ δ)
          (flattenHouseholder (flattenNormal e (projGradVec e ψ x₀)) u *ᵥ e) +
        vecMulVec (flattenHouseholder (flattenNormal e (projGradVec e ψ x₀)) u *ᵥ e)
          (flattenHouseholder (flattenNormal e (projGradVec e ψ x₀)) u *ᵥ δ) +
        (δ ⬝ᵥ δ) • vecMulVec (flattenHouseholder (flattenNormal e (projGradVec e ψ x₀)) u *ᵥ e)
          (flattenHouseholder (flattenNormal e (projGradVec e ψ x₀)) u *ᵥ e) := by
    rw [flattenCoeff_eq hg, ← flatten_gram hOO e δ]
  rw [hform]
  have hent := flatten_entry_le hOO he δ i j
  -- sizes of `δ`
  have ht1 : ‖δ‖ ≤ 4 * M₁ := by
    have h1 := flatten_norm_projGradVec_le he hψ hb1 x₀
    have h2 := flatten_norm_projGradVec_le he hψ hb1 y
    calc ‖δ‖ ≤ ‖projGradVec e ψ x₀‖ + ‖projGradVec e ψ y‖ := norm_sub_le _ _
      _ ≤ 4 * M₁ := by linarith only [h1, h2]
  have ht2 : ‖δ‖ ≤ 2 * M₂ * ((1 + d) * ‖x₀ - y‖) :=
    flatten_norm_projGradVec_sub_le he hψ hM₂ hb2 x₀ y
  -- distance of `y` from `x₀`
  have hr : ‖x₀ - y‖ ≤ (1 + (1 + d) * M₁) * (d * (1 + 2 * d * M₁) * ‖z‖) := by
    have hK : ∀ a b : Vec d, |(-ψ) a - (-ψ) b| ≤ M₁ * ‖a - b‖ := fun a b => by
      have := abs_sub_le_of_fderiv_bound hψ hb1 a b
      have e1 : (-ψ) a - (-ψ) b = -(ψ a - ψ b) := by simp only [Pi.neg_apply]; ring
      rw [e1, abs_neg]
      exact this
    have hsh := norm_shear_sub_le he hM₁ hK
      (matVecMul (flattenLinInv e (projGradVec e ψ x₀) u) z + shear e ψ x₀) (shear e ψ x₀)
    have hx0 : shear e (-ψ) (shear e ψ x₀) = x₀ := shear_neg_shear he ψ x₀
    have hdiff : (matVecMul (flattenLinInv e (projGradVec e ψ x₀) u) z + shear e ψ x₀) -
        shear e ψ x₀ = flattenLinInv e (projGradVec e ψ x₀) u *ᵥ z := by
      rw [add_sub_cancel_right]; rfl
    rw [hx0, hdiff] at hsh
    have hlin := flatten_norm_linInv_le (u := u) he
      (flatten_norm_projGradVec_le he hψ hb1 x₀) z
    rw [norm_sub_rev]
    calc ‖y - x₀‖ ≤ (1 + (1 + d) * M₁) * ‖flattenLinInv e (projGradVec e ψ x₀) u *ᵥ z‖ := hsh
      _ ≤ (1 + (1 + d) * M₁) * (d * (1 + d * (2 * M₁)) * ‖z‖) :=
          mul_le_mul_of_nonneg_left hlin (by positivity)
      _ = (1 + (1 + d) * M₁) * (d * (1 + 2 * d * M₁) * ‖z‖) := by ring
  have ht : ‖δ‖ ≤ 2 * M₂ * ((1 + d) * ((1 + (1 + d) * M₁) *
      (d * (1 + 2 * d * M₁) * ‖z‖))) :=
    ht2.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr (by positivity))
      (by positivity))
  have hnn := norm_nonneg δ
  have hsq : 2 * (d : ℝ) ^ 2 * ‖δ‖ + (d : ℝ) ^ 3 * ‖δ‖ ^ 2 ≤
      (2 * d ^ 2 + 4 * d ^ 3 * M₁) * ‖δ‖ := by
    have h3 : (d : ℝ) ^ 3 * ‖δ‖ ^ 2 ≤ (d : ℝ) ^ 3 * (‖δ‖ * (4 * M₁)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [sq]
      exact mul_le_mul_of_nonneg_left ht1 hnn
    nlinarith only [h3]
  refine hent.trans (hsq.trans ?_)
  unfold flattenLipConst
  calc (2 * (d : ℝ) ^ 2 + 4 * d ^ 3 * M₁) * ‖δ‖
      ≤ (2 * d ^ 2 + 4 * d ^ 3 * M₁) * (2 * M₂ * ((1 + d) * ((1 + (1 + d) * M₁) *
          (d * (1 + 2 * d * M₁) * ‖z‖)))) :=
        mul_le_mul_of_nonneg_left ht (by positivity)
    _ = _ := by ring

/-! ### Transport of weak solutions -/

theorem flatten_hb {ψ : Vec d → ℝ} {M₁ : ℝ} (hb1 : ∀ y, ‖fderiv ℝ ψ y‖ ≤ M₁) :
    ∀ i, ∃ M, ∀ y, |fderiv ℝ ψ y (Pi.single i 1)| ≤ M := fun i => by
  refine ⟨M₁, fun y => ?_⟩
  have hs : ‖(Pi.single i (1 : ℝ) : Vec d)‖ ≤ 1 :=
    (pi_norm_le_iff_of_nonneg zero_le_one).2 fun k => by
      by_cases h : k = i <;> simp [h]
  calc |fderiv ℝ ψ y (Pi.single i 1)| = ‖fderiv ℝ ψ y (Pi.single i 1)‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ‖fderiv ℝ ψ y‖ * ‖(Pi.single i (1 : ℝ) : Vec d)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ M₁ * 1 := mul_le_mul (hb1 y) hs (norm_nonneg _) ((norm_nonneg _).trans (hb1 y))
    _ = M₁ := mul_one _

theorem IsWeakSolutionOn.congr {U : Set (Vec d)} {a a' : CoeffField d} {w : H1Function U}
    {f f' : Vec d → ℝ} {g g' : Vec d → Vec d} (ha : ∀ x, a x = a' x) (hf : ∀ x, f x = f' x)
    (hg : ∀ x, g x = g' x) (h : IsWeakSolutionOn a U w f g) : IsWeakSolutionOn a' U w f' g' := by
  obtain rfl : a = a' := funext ha
  obtain rfl : f = f' := funext hf
  obtain rfl : g = g' := funext hg
  exact h

/-- The linear map `L` of the chart map as a continuous linear equivalence. -/
noncomputable def flattenEquiv {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (u x₀ : Vec d) :
    Vec d ≃L[ℝ] Vec d :=
  matrixContinuousLinearEquiv (flattenLin e (projGradVec e ψ x₀) u)
    (isUnit_flattenLin (vecDot_self_projGradVec he hψ x₀))

/-- The translation `L Φ x₀` separating `L ∘ Φ` from the chart map. -/
noncomputable def flattenShift (e : Vec d) (ψ : Vec d → ℝ) (x₀ u : Vec d) : Vec d :=
  matVecMul (flattenLin e (projGradVec e ψ x₀) u) (shear e ψ x₀)

theorem flattenInv_sub_shift {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (u x₀ v : Vec d) :
    flattenInv e ψ x₀ u (v - flattenShift e ψ x₀ u) =
      shear e (-ψ) ((flattenEquiv he hψ u x₀).symm v) := by
  have hg := vecDot_self_projGradVec he hψ x₀
  unfold flattenInv flattenShift flattenEquiv
  rw [matrixContinuousLinearEquiv_symm_apply, flattenLin_inv_eq hg]
  simp only [flatten_matVecMul_eq, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
    flattenLinInv_mul hg, Matrix.one_mulVec, sub_add_cancel]

/-- **Transport.** A weak solution `w` in `U` of coefficient `a` gives a weak solution on
`(L ∘ Φ)(U)` with coefficient `Ã(· - L Φ x₀)`, where `Ã = flattenCoeff` is the transported
coefficient `DΨ a DΨᵀ ∘ Ψ⁻¹` and the data are `f ∘ Ψ⁻¹`, `DΨ (g ∘ Ψ⁻¹)` (no normalization:
`|det DΨ| = 1`). The remaining translation by `L Φ x₀` is a pure translation. -/
theorem IsWeakSolutionOn.flatten {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {M₁ : ℝ} (hb1 : ∀ y, ‖fderiv ℝ ψ y‖ ≤ M₁) (u x₀ : Vec d) {U : Set (Vec d)} {a : CoeffField d}
    {w : H1Function U} {f : Vec d → ℝ} {g : Vec d → Vec d}
    (hw : IsWeakSolutionOn a U w f g) :
    IsWeakSolutionOn
      (fun v => flattenCoeff e ψ x₀ u a (v - flattenShift e ψ x₀ u))
      (flattenEquiv he hψ u x₀ '' (shear e (-ψ) ⁻¹' U))
      ((H1Function.compShear (ψ := -ψ) he hψ.neg (exists_bound_neg (flatten_hb hb1)) w).compLinearEquiv
        (flattenEquiv he hψ u x₀))
      (fun v => f (flattenInv e ψ x₀ u (v - flattenShift e ψ x₀ u)))
      (fun v => matVecMul (flattenLin e (projGradVec e ψ x₀) u *
          shearJac e ψ (flattenInv e ψ x₀ u (v - flattenShift e ψ x₀ u)))
        (g (flattenInv e ψ x₀ u (v - flattenShift e ψ x₀ u)))) := by
  have hg := vecDot_self_projGradVec he hψ x₀
  have h := IsWeakSolutionOn.linearChange_normalized (flattenLin e (projGradVec e ψ x₀) u)
    (isUnit_flattenLin hg)
    (IsWeakSolutionOn.shearPush he hψ (flatten_hb hb1) hw)
  have hdet : |(flattenLin e (projGradVec e ψ x₀) u).det|⁻¹ = 1 := by
    rw [abs_det_flattenLin hg, inv_one]
  refine IsWeakSolutionOn.congr (fun v => ?_) (fun v => ?_) (fun v => ?_) h
  · have hk := flattenInv_sub_shift he hψ u x₀ v
    unfold flattenCoeff
    rw [hk, hdet, one_smul]
    rfl
  · have hk := flattenInv_sub_shift he hψ u x₀ v
    rw [hk, hdet, one_mul]
    rfl
  · have hk := flattenInv_sub_shift he hψ u x₀ v
    rw [hk, hdet, one_smul, flatten_matVecMul_eq, flatten_matVecMul_eq, flatten_matVecMul_eq,
      Matrix.mulVec_mulVec]
    rfl

/-! ### Volume preservation -/

theorem measurePreserving_flattenMap {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (u x₀ : Vec d) :
    MeasurePreserving (flattenMap e ψ x₀ u) volume volume := by
  have hg := vecDot_self_projGradVec he hψ x₀
  have h1 := measurePreserving_shear he (hψ.differentiable (by simp))
  have h2 := measurePreserving_sub_right (volume : Measure (Vec d)) (shear e ψ x₀)
  have h3 : MeasurePreserving (flattenEquiv he hψ u x₀) volume volume := by
    refine ⟨(flattenEquiv he hψ u x₀).continuous.measurable, ?_⟩
    rw [map_linearEquiv_volume]
    have hdet : LinearMap.det (flattenEquiv he hψ u x₀).toLinearMap =
        (flattenLin e (projGradVec e ψ x₀) u).det := by
      have : (flattenEquiv he hψ u x₀).toLinearMap =
          Matrix.toLin' (flattenLin e (projGradVec e ψ x₀) u) := LinearMap.ext fun x => rfl
      rw [this, LinearMap.det_toLin']
    rw [hdet, abs_inv, abs_det_flattenLin hg]
    simp
  exact h3.comp (h2.comp h1)

/-! ### Satisfiability: the Euclidean ball at a boundary point -/

end SuperdiffusionCLT.Section7
