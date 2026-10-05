/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Root.Rescaling
public import SuperdiffusionCLT.Section7.Analytic.OpenH10.LipschitzB

/-!
# The three terms of the first root under dilation

Triangle inequality and homogeneity of the dual seminorm, and the exact equality of the three
terms of the root estimate on `U` with the corresponding terms of the rescaled pair on `ε⁻¹ • U`,
together with the scaling of the two right-hand-side norms.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization MeasureTheory
open scoped ENNReal Pointwise

variable {d : ℕ}

/-- The products of the components of `F` with every `H¹₀(V)` function are integrable. -/
def s12_PairInt (V : Set (Vec d)) (F : Vec d → Vec d) : Prop :=
  ∀ (i : Fin d) (ψ : H10Function V),
    IntegrableOn (fun x => F x i * ψ.toH1Function.toFun x) V

theorem s12_pairInt_of_gradMemL2On {V : Set (Vec d)} {F : Vec d → Vec d}
    (hF : GradMemL2On V F) : s12_PairInt V F :=
  fun i ψ => integrableOn_mul_of_memL2On (hF i) ψ.toH1Function.memL2

theorem s12_pairInt_grad {V : Set (Vec d)} (w : H1Function V) : s12_PairInt V w.grad :=
  s12_pairInt_of_gradMemL2On w.gradMemL2

theorem s12_pairInt_add {V : Set (Vec d)} {F G : Vec d → Vec d} (hF : s12_PairInt V F)
    (hG : s12_PairInt V G) : s12_PairInt V (fun x => F x + G x) := fun i ψ => by
  have h : Integrable (fun x => F x i * ψ.toH1Function.toFun x +
      G x i * ψ.toH1Function.toFun x) (volume.restrict V) := Integrable.add (hF i ψ) (hG i ψ)
  show Integrable _ _
  simpa [add_mul] using h

theorem s12_pairInt_smul {V : Set (Vec d)} {F : Vec d → Vec d} (c : ℝ) (hF : s12_PairInt V F) :
    s12_PairInt V (fun x => c • F x) := fun i ψ => by
  have h : Integrable (fun x => c * (F x i * ψ.toH1Function.toFun x)) (volume.restrict V) :=
    Integrable.const_mul (hF i ψ) c
  show Integrable _ _
  simpa [mul_assoc] using h

/-- Triangle inequality for the normalized dual seminorm. -/
theorem s12_wMinusOneBar_add_le (V : Set (Vec d)) (p : ℝ≥0∞) {h₁ h₂ : Vec d → ℝ}
    (hi₁ : ∀ ψ : H10Function V, IntegrableOn (fun x => h₁ x * ψ.toH1Function.toFun x) V)
    (hi₂ : ∀ ψ : H10Function V, IntegrableOn (fun x => h₂ x * ψ.toH1Function.toFun x) V) :
    wMinusOneBar V p (fun x => h₁ x + h₂ x) ≤ wMinusOneBar V p h₁ + wMinusOneBar V p h₂ := by
  unfold wMinusOneBar
  refine iSup_le fun ψ => iSup_le fun hψ => ?_
  have hI : ∫ x in V, (h₁ x + h₂ x) * ψ.toH1Function.toFun x =
      (∫ x in V, h₁ x * ψ.toH1Function.toFun x) + ∫ x in V, h₂ x * ψ.toH1Function.toFun x := by
    rw [← integral_add (hi₁ ψ) (hi₂ ψ)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  rw [hI]
  have h1 : ENNReal.ofReal |((volume V).toReal)⁻¹ *
      ((∫ x in V, h₁ x * ψ.toH1Function.toFun x) +
        ∫ x in V, h₂ x * ψ.toH1Function.toFun x)| ≤
      ENNReal.ofReal |((volume V).toReal)⁻¹ * ∫ x in V, h₁ x * ψ.toH1Function.toFun x| +
        ENNReal.ofReal |((volume V).toReal)⁻¹ * ∫ x in V, h₂ x * ψ.toH1Function.toFun x| := by
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_add]
    exact abs_add_le _ _
  refine h1.trans (add_le_add ?_ ?_)
  · exact le_iSup₂ (f := fun (ψ : H10Function V)
      (_ : lpBar V p.conjExponent ψ.toH1Function.grad ≤ 1) =>
        ENNReal.ofReal |((volume V).toReal)⁻¹ * ∫ x in V, h₁ x * ψ.toH1Function.toFun x|) ψ hψ
  · exact le_iSup₂ (f := fun (ψ : H10Function V)
      (_ : lpBar V p.conjExponent ψ.toH1Function.grad ≤ 1) =>
        ENNReal.ofReal |((volume V).toReal)⁻¹ * ∫ x in V, h₂ x * ψ.toH1Function.toFun x|) ψ hψ

/-- Homogeneity of the `H^{-1}` seminorm of a vector field. -/
theorem s12_hMinusOneVec_smul (V : Set (Vec d)) (c : ℝ) (F : Vec d → Vec d) :
    s12_hMinusOneVec V (fun x => c • F x) = ENNReal.ofReal |c| * s12_hMinusOneVec V F := by
  unfold s12_hMinusOneVec
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (fun x => (c • F x) i) = fun x => c * F x i := by
    funext x
    simp
  rw [this, s12_wMinusOneBar_const_mul]

/-- Triangle inequality for the `H^{-1}` seminorm of vector fields. -/
theorem s12_hMinusOneVec_add_le (V : Set (Vec d)) {F G : Vec d → Vec d} (hF : s12_PairInt V F)
    (hG : s12_PairInt V G) :
    s12_hMinusOneVec V (fun x => F x + G x) ≤ s12_hMinusOneVec V F + s12_hMinusOneVec V G := by
  unfold s12_hMinusOneVec
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have := s12_wMinusOneBar_add_le V 2 (h₁ := fun x => F x i) (h₂ := fun x => G x i)
    (fun ψ => hF i ψ) (fun ψ => hG i ψ)
  simpa using this

/-! ### The three terms of the root estimate under dilation -/

/-- The first term: the `L^∞` distance is invariant. -/
theorem s12_term_one {U : Set (Vec d)} {ε : ℝ} (hε : ε ≠ 0) (u v : H1Function U) :
    eLpNorm (fun x => u.toFun x - v.toFun x) ⊤ (volume.restrict U) =
      eLpNorm (fun y => (u.dilateArg hε).toFun y - (v.dilateArg hε).toFun y) ⊤
        (volume.restrict (ε⁻¹ • U)) := by
  rw [← s12_eLpNorm_top_dilate hε U (fun x => u.toFun x - v.toFun x)]
  simp only [H1Function.dilateArg_toFun]

/-- The second term: the `H^{-1}` seminorm of the gradient difference is invariant. -/
theorem s12_term_two {U : Set (Vec d)} {ε : ℝ} (hε : 0 < ε) (u v : H1Function U) :
    s12_hMinusOneVec (ε⁻¹ • U) (fun y => (u.dilateArg hε.ne').grad y - (v.dilateArg hε.ne').grad y) =
      s12_hMinusOneVec U (fun x => u.grad x - v.grad x) := by
  refine s12_hMinusOneVec_dilate_grad hε U _ _ fun y => ?_
  simp only [H1Function.dilateArg_grad, smul_sub]

theorem s12_matVecMul_sub (A B : Mat d) (v : Vec d) :
    matVecMul (A - B) v = matVecMul A v - matVecMul B v := by
  funext i
  simp [matVecMul, sub_mul, Finset.sum_sub_distrib]

theorem s12_matVecMul_smul_left (c : ℝ) (A : Mat d) (v : Vec d) :
    matVecMul (c • A) v = c • matVecMul A v := by
  funext i
  simp [matVecMul, mul_assoc, Finset.mul_sum]

/-- The third term: the flux difference, with the field centered at the average of `k^ε` over
`U` on the left and at the average of `k` over `ε⁻¹ • U` on the right. -/
theorem s12_term_three (nu : ℝ) (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
    {U : Set (Vec d)} {ε : ℝ} (hε : 0 < ε) (S : ℝ) (u v : H1Function U) :
    s12_hMinusOneVec (ε⁻¹ • U) (fun y =>
      matVecMul (S⁻¹ • (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega y -
        Matrix.of fun i j => ⨍ w in ε⁻¹ • U,
          SuperdiffusionCLT.Section6.fullStreamRecentered omega w i j))
        ((u.dilateArg hε.ne').grad y) - (v.dilateArg hε.ne').grad y) =
      s12_hMinusOneVec U (fun x =>
        matVecMul (S⁻¹ • s12_epFieldCentered nu omega ε U x) (u.grad x) - v.grad x) := by
  refine s12_hMinusOneVec_dilate_grad hε U _ _ fun y => ?_
  simp only [H1Function.dilateArg_grad, s12_epFieldCentered_dilate nu omega hε.ne',
    matVecMul_smul, smul_sub]

/-- The datum `f` in the rescaled right-hand side `S ε² f(ε ·)`. -/
theorem s12_rhs_f {U : Set (Vec d)} {ε S : ℝ} (hε : ε ≠ 0) (hS : 0 ≤ S) (f : Vec d → ℝ) :
    eLpNorm (fun y => S * ε ^ 2 * f (ε • y)) ⊤ (volume.restrict (ε⁻¹ • U)) =
      ENNReal.ofReal (S * ε ^ 2) * eLpNorm f ⊤ (volume.restrict U) := by
  have h : (fun y => S * ε ^ 2 * f (ε • y)) = (S * ε ^ 2) • fun y => f (ε • y) := by
    funext y
    simp
  rw [h, eLpNorm_const_smul, s12_eLpNorm_top_dilate hε U f, Real.enorm_eq_ofReal_abs,
    abs_of_nonneg (mul_nonneg hS (sq_nonneg ε))]

/-- The gradient of the datum: the Euclidean length scales by `ε`. -/
theorem s12_rhs_g {U : Set (Vec d)} {ε : ℝ} (hε : 0 < ε) (g : H1Function U) :
    eLpNorm (fun y => eucNorm ((g.dilateArg hε.ne').grad y)) ⊤ (volume.restrict (ε⁻¹ • U)) =
      ENNReal.ofReal ε * eLpNorm (fun x => eucNorm (g.grad x)) ⊤ (volume.restrict U) := by
  have h : (fun y => eucNorm ((g.dilateArg hε.ne').grad y)) =
      ε • fun y => (fun x => eucNorm (g.grad x)) (ε • y) := by
    funext y
    simp only [H1Function.dilateArg_grad, eucNorm, vecNormSq_smul, Pi.smul_apply, smul_eq_mul]
    rw [Real.sqrt_mul (sq_nonneg ε), Real.sqrt_sq hε.le]
  rw [h, eLpNorm_const_smul, s12_eLpNorm_top_dilate hε.ne' U (fun x => eucNorm (g.grad x)),
    Real.enorm_eq_ofReal_abs, abs_of_pos hε]

/-! ### Triangle inequalities for the three terms -/

theorem s12_term_one_le {V : Set (Vec d)} (u v w : H1Function V) :
    eLpNorm (fun x => u.toFun x - w.toFun x) ⊤ (volume.restrict V) ≤
      eLpNorm (fun x => u.toFun x - v.toFun x) ⊤ (volume.restrict V) +
        eLpNorm (fun x => v.toFun x - w.toFun x) ⊤ (volume.restrict V) := by
  have h : (fun x => u.toFun x - w.toFun x) =
      (fun x => u.toFun x - v.toFun x) + fun x => v.toFun x - w.toFun x := by
    funext x
    simp
  rw [h]
  exact eLpNorm_add_le le_top

theorem s12_term_two_le {V : Set (Vec d)} (u v w : H1Function V) :
    s12_hMinusOneVec V (fun x => u.grad x - w.grad x) ≤
      s12_hMinusOneVec V (fun x => u.grad x - v.grad x) +
        s12_hMinusOneVec V (fun x => v.grad x - w.grad x) := by
  have h : (fun x => u.grad x - w.grad x) =
      fun x => (u.grad x - v.grad x) + (v.grad x - w.grad x) := by
    funext x
    abel
  rw [h]
  refine s12_hMinusOneVec_add_le V ?_ ?_
  · simpa using s12_pairInt_grad (u - v)
  · simpa using s12_pairInt_grad (v - w)

/-- Triangle inequality for a four-term decomposition of a flux. -/
theorem s12_flux_triangle (V : Set (Vec d)) {T X₁ X₂ X₃ X₄ : Vec d → Vec d}
    (hT : ∀ y, T y = X₁ y + X₂ y + X₃ y + X₄ y) (p₁ : s12_PairInt V X₁) (p₂ : s12_PairInt V X₂)
    (p₃ : s12_PairInt V X₃) (p₄ : s12_PairInt V X₄) :
    s12_hMinusOneVec V T ≤ s12_hMinusOneVec V X₁ + s12_hMinusOneVec V X₂ +
      s12_hMinusOneVec V X₃ + s12_hMinusOneVec V X₄ := by
  have e : T = fun y => (X₁ y + X₂ y + X₃ y) + X₄ y := funext hT
  rw [e]
  refine (s12_hMinusOneVec_add_le V (s12_pairInt_add (s12_pairInt_add p₁ p₂) p₃) p₄).trans ?_
  refine add_le_add ?_ le_rfl
  refine (s12_hMinusOneVec_add_le V (s12_pairInt_add p₁ p₂) p₃).trans ?_
  exact add_le_add (s12_hMinusOneVec_add_le V p₁ p₂) le_rfl

/-- The pointwise splitting of the flux with scalar `S⁻¹` and centering `M_V` into the black-box
flux (scalar `shom⁻¹`, centering `M_K`), the Laplace gradient difference, the change of centering
and the change of scalar. -/
theorem s12_flux_decomp (A MV MK : Mat d) (S sh : ℝ) (v ub uh : Vec d) :
    matVecMul (S⁻¹ • (A - MV)) v - uh =
      (matVecMul (sh⁻¹ • (A - MK)) v - ub) + (ub - uh) +
        (-(sh⁻¹) • matVecMul (MV - MK) v) + ((S⁻¹ - sh⁻¹) • matVecMul (A - MV) v) := by
  simp only [s12_matVecMul_smul_left, s12_matVecMul_sub]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-! ### The three terms of the root, through the rescaled pair -/

/-- The first two terms of the root estimate on `U` are at most the corresponding terms of the
rescaled pair `(u_R, ū_R)` (the black-box comparison) plus those of `(ū_R, u_{hom,R})` (the
Laplace comparison), on `ε⁻¹ • U`. -/
theorem s12_root_terms_one_two_le {U : Set (Vec d)} {ε : ℝ} (hε : 0 < ε)
    (u uhom : H1Function U) (ub : H1Function (ε⁻¹ • U)) :
    eLpNorm (fun x => u.toFun x - uhom.toFun x) ⊤ (volume.restrict U) +
        s12_hMinusOneVec U (fun x => u.grad x - uhom.grad x) ≤
      (eLpNorm (fun y => (u.dilateArg hε.ne').toFun y - ub.toFun y) ⊤
          (volume.restrict (ε⁻¹ • U)) +
        s12_hMinusOneVec (ε⁻¹ • U) (fun y => (u.dilateArg hε.ne').grad y - ub.grad y)) +
      (eLpNorm (fun y => ub.toFun y - (uhom.dilateArg hε.ne').toFun y) ⊤
          (volume.restrict (ε⁻¹ • U)) +
        s12_hMinusOneVec (ε⁻¹ • U) (fun y => ub.grad y - (uhom.dilateArg hε.ne').grad y)) := by
  rw [s12_term_one hε.ne' u uhom, ← s12_term_two hε u uhom]
  have h1 := s12_term_one_le (u.dilateArg hε.ne') ub (uhom.dilateArg hε.ne')
  have h2 := s12_term_two_le (u.dilateArg hε.ne') ub (uhom.dilateArg hε.ne')
  calc _ ≤ _ := add_le_add h1 h2
    _ = _ := by abel

/-- The third term of the root estimate on `U`, split into the black-box flux term, the Laplace
gradient difference, the change of centering and the change of scalar, on `ε⁻¹ • U`. -/
theorem s12_root_flux_le (nu : ℝ) (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
    {U : Set (Vec d)} {ε : ℝ} (hε : 0 < ε) (S sh : ℝ) (MK : Mat d) (u uhom : H1Function U)
    (ub : H1Function (ε⁻¹ • U))
    (p₁ : s12_PairInt (ε⁻¹ • U) (fun y =>
      matVecMul (sh⁻¹ • (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega y - MK))
        ((u.dilateArg hε.ne').grad y) - ub.grad y))
    (p₂ : s12_PairInt (ε⁻¹ • U) (fun y => ub.grad y - (uhom.dilateArg hε.ne').grad y))
    (p₃ : s12_PairInt (ε⁻¹ • U) (fun y => matVecMul ((Matrix.of fun i j => ⨍ w in ε⁻¹ • U,
        SuperdiffusionCLT.Section6.fullStreamRecentered omega w i j) - MK)
        ((u.dilateArg hε.ne').grad y)))
    (p₄ : s12_PairInt (ε⁻¹ • U) (fun y => matVecMul
        (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega y -
          Matrix.of fun i j => ⨍ w in ε⁻¹ • U,
            SuperdiffusionCLT.Section6.fullStreamRecentered omega w i j)
        ((u.dilateArg hε.ne').grad y))) :
    s12_hMinusOneVec U (fun x =>
        matVecMul (S⁻¹ • s12_epFieldCentered nu omega ε U x) (u.grad x) - uhom.grad x) ≤
      s12_hMinusOneVec (ε⁻¹ • U) (fun y =>
        matVecMul (sh⁻¹ • (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega y -
          MK)) ((u.dilateArg hε.ne').grad y) - ub.grad y) +
      s12_hMinusOneVec (ε⁻¹ • U) (fun y => ub.grad y - (uhom.dilateArg hε.ne').grad y) +
      ENNReal.ofReal |-(sh⁻¹)| * s12_hMinusOneVec (ε⁻¹ • U) (fun y => matVecMul
        ((Matrix.of fun i j => ⨍ w in ε⁻¹ • U,
          SuperdiffusionCLT.Section6.fullStreamRecentered omega w i j) - MK)
        ((u.dilateArg hε.ne').grad y)) +
      ENNReal.ofReal |S⁻¹ - sh⁻¹| * s12_hMinusOneVec (ε⁻¹ • U) (fun y => matVecMul
        (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega y -
          Matrix.of fun i j => ⨍ w in ε⁻¹ • U,
            SuperdiffusionCLT.Section6.fullStreamRecentered omega w i j)
        ((u.dilateArg hε.ne').grad y)) := by
  rw [← s12_term_three nu omega hε S u uhom]
  have h := s12_flux_triangle (ε⁻¹ • U)
    (T := fun y => matVecMul (S⁻¹ • (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu
      omega y - Matrix.of fun i j => ⨍ w in ε⁻¹ • U,
        SuperdiffusionCLT.Section6.fullStreamRecentered omega w i j))
      ((u.dilateArg hε.ne').grad y) - (uhom.dilateArg hε.ne').grad y)
    (X₁ := fun y => matVecMul (sh⁻¹ • (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu
      omega y - MK)) ((u.dilateArg hε.ne').grad y) - ub.grad y)
    (X₂ := fun y => ub.grad y - (uhom.dilateArg hε.ne').grad y)
    (X₃ := fun y => (-(sh⁻¹)) • matVecMul ((Matrix.of fun i j => ⨍ w in ε⁻¹ • U,
        SuperdiffusionCLT.Section6.fullStreamRecentered omega w i j) - MK)
        ((u.dilateArg hε.ne').grad y))
    (X₄ := fun y => (S⁻¹ - sh⁻¹) • matVecMul
        (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega y -
          Matrix.of fun i j => ⨍ w in ε⁻¹ • U,
            SuperdiffusionCLT.Section6.fullStreamRecentered omega w i j)
        ((u.dilateArg hε.ne').grad y))
    (fun y => s12_flux_decomp _ _ MK S sh _ _ _) p₁ p₂ (s12_pairInt_smul _ p₃)
    (s12_pairInt_smul _ p₄)
  rw [s12_hMinusOneVec_smul, s12_hMinusOneVec_smul] at h
  exact h

/-- Satisfiability of the integrability condition. -/
example (V : Set (Vec d)) : s12_PairInt V (fun _ => (0 : Vec d)) := fun i ψ => by
  simp

end SuperdiffusionCLT.Section7
