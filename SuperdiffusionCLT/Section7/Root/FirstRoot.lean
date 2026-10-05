/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Root.ScalarComparisonB
public import SuperdiffusionCLT.Section7.Prereq.RootCarriersApiC

/-!
# The first root: bridges, vector fields times matrices, and the flux splitting

* The root carriers (`IsDirichletSolution`, `hMinusOneVec`, `epField`, `epFieldCentered`) are
  definitionally the `s12_` copies used by the scalar comparison.
* Products of a bounded matrix field with an `L²` gradient field are `L²`.
* The `H^{-1}` seminorm of a constant matrix times a vector field.
* The splitting of the recentred flux used for the change of centring.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization MeasureTheory
open scoped ENNReal Pointwise

variable {d : ℕ}

/-! ### Bridges to the scalar-comparison copies -/

theorem s5_isDirichletSolution_iff {a : CoeffField d} {U : Set (Vec d)} {f : Vec d → ℝ}
    {g u : H1Function U} :
    IsDirichletSolution a U f g u ↔ s12_IsDirichletSolution a U f g u := Iff.rfl

/-! ### A bounded matrix field times an `L²` gradient field -/

theorem s5_gradMemL2On_matVecMul {V : Set (Vec d)} (hV : MeasurableSet V) {A : Vec d → Mat d}
    {F : Vec d → Vec d} {B : ℝ} (hA : Measurable A) (hB : ∀ x ∈ V, ∀ i j, |A x i j| ≤ B)
    (hF : GradMemL2On V F) : GradMemL2On V (fun x => matVecMul (A x) (F x)) := by
  intro i
  have h : (fun x => matVecMul (A x) (F x) i) = fun x => ∑ j : Fin d, A x i j * F x j := rfl
  show MemLp (fun x => matVecMul (A x) (F x) i) 2 (volume.restrict V)
  rw [h]
  refine memLp_finsetSum _ fun j _ => ?_
  have hAij : Measurable fun x => A x i j :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hA)
  refine (hF j).of_le_mul (c := B) (hAij.aestronglyMeasurable.mul (hF j).aestronglyMeasurable) ?_
  refine (ae_restrict_iff' hV).2 (Filter.Eventually.of_forall fun x hx => ?_)
  rw [norm_mul, Real.norm_eq_abs (A x i j)]
  exact mul_le_mul_of_nonneg_right (hB x hx i j) (norm_nonneg _)

theorem s5_pairInt_matVecMul {V : Set (Vec d)} (hV : MeasurableSet V) {A : Vec d → Mat d}
    {F : Vec d → Vec d} {B : ℝ} (hA : Measurable A) (hB : ∀ x ∈ V, ∀ i j, |A x i j| ≤ B)
    (hF : GradMemL2On V F) : s12_PairInt V (fun x => matVecMul (A x) (F x)) :=
  s12_pairInt_of_gradMemL2On (s5_gradMemL2On_matVecMul hV hA hB hF)

theorem s5_pairInt_sub {V : Set (Vec d)} {F G : Vec d → Vec d} (hF : s12_PairInt V F)
    (hG : s12_PairInt V G) : s12_PairInt V (fun x => F x - G x) := by
  have h := s12_pairInt_add hF (s12_pairInt_smul (-1) hG)
  simpa [sub_eq_add_neg] using h

/-! ### The `H^{-1}` seminorm of a constant matrix times a vector field -/

/-- A finite linear combination of functions. -/
theorem s5_wMinusOneBar_sum_le (V : Set (Vec d)) {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (h : ι → Vec d → ℝ)
    (hi : ∀ j ∈ s, ∀ ψ : H10Function V, IntegrableOn (fun x => h j x * ψ.toH1Function.toFun x) V) :
    wMinusOneBar V 2 (fun x => ∑ j ∈ s, c j * h j x) ≤
      ∑ j ∈ s, ENNReal.ofReal |c j| * wMinusOneBar V 2 (h j) := by
  unfold wMinusOneBar
  refine iSup_le fun ψ => iSup_le fun hψ => ?_
  have hI : ∫ x in V, (∑ j ∈ s, c j * h j x) * ψ.toH1Function.toFun x =
      ∑ j ∈ s, c j * ∫ x in V, h j x * ψ.toH1Function.toFun x := by
    have e : (fun x => (∑ j ∈ s, c j * h j x) * ψ.toH1Function.toFun x) =
        fun x => ∑ j ∈ s, c j * (h j x * ψ.toH1Function.toFun x) := by
      funext x
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e, integral_finsetSum _ fun j hj => (hi j hj ψ).const_mul (c j)]
    exact Finset.sum_congr rfl fun j _ => by rw [integral_const_mul]
  rw [hI]
  have e2 : ((volume V).toReal)⁻¹ * ∑ j ∈ s, c j * ∫ x in V, h j x * ψ.toH1Function.toFun x =
      ∑ j ∈ s, c j * (((volume V).toReal)⁻¹ * ∫ x in V, h j x * ψ.toH1Function.toFun x) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e2]
  refine (ENNReal.ofReal_le_ofReal (Finset.abs_sum_le_sum_abs _ _)).trans ?_
  rw [ENNReal.ofReal_sum_of_nonneg fun j _ => abs_nonneg _]
  refine Finset.sum_le_sum fun j hj => ?_
  rw [abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
  refine mul_le_mul' le_rfl ?_
  exact le_iSup₂ (f := fun (ψ : H10Function V)
    (_ : lpBar V (2 : ℝ≥0∞).conjExponent ψ.toH1Function.grad ≤ 1) =>
      ENNReal.ofReal |((volume V).toReal)⁻¹ * ∫ x in V, h j x * ψ.toH1Function.toFun x|) ψ hψ

/-- The `H^{-1}` seminorm of a constant matrix times a vector field. -/
theorem s5_hMinusOneVec_matVecMul_le (V : Set (Vec d)) (M : Mat d) {B : ℝ}
    (hB : ∀ i j, |M i j| ≤ B) {F : Vec d → Vec d} (hF : s12_PairInt V F) :
    s12_hMinusOneVec V (fun x => matVecMul M (F x)) ≤
      ENNReal.ofReal ((d : ℝ) * B) * s12_hMinusOneVec V F := by
  unfold s12_hMinusOneVec
  have h1 : ∀ i : Fin d, wMinusOneBar V 2 (fun x => matVecMul M (F x) i) ≤
      ∑ j : Fin d, ENNReal.ofReal B * wMinusOneBar V 2 (fun x => F x j) := by
    intro i
    have h := s5_wMinusOneBar_sum_le V Finset.univ (fun j => M i j) (fun j x => F x j)
      (fun j _ ψ => hF j ψ)
    refine h.trans (Finset.sum_le_sum fun j _ => ?_)
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hB i j)) le_rfl
  refine (Finset.sum_le_sum fun i _ => h1 i).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ENNReal.ofReal_mul (Nat.cast_nonneg d), ENNReal.ofReal_natCast, ← Finset.mul_sum, mul_assoc]

/-! ### The splitting of the flux for the change of centring -/

theorem s5_flux_centre_decomp (A MV MK : Mat d) (sh : ℝ) (v ub : Vec d) :
    matVecMul (sh⁻¹ • (A - MV)) v =
      (matVecMul (sh⁻¹ • (A - MK)) v - ub) + ub + (-(sh⁻¹)) • matVecMul (MV - MK) v := by
  simp only [s12_matVecMul_smul_left, s12_matVecMul_sub]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The `H^{-1}` seminorm of the flux centred at `M_V`, in terms of the flux centred at `M_K`,
the Laplace gradient, and the change of centring. -/
theorem s5_flux_centre_le (V : Set (Vec d)) (A : Vec d → Mat d) (MV MK : Mat d) (sh : ℝ)
    (v ub : Vec d → Vec d)
    (p₁ : s12_PairInt V (fun y => matVecMul (sh⁻¹ • (A y - MK)) (v y) - ub y))
    (p₂ : s12_PairInt V ub) (p₃ : s12_PairInt V (fun y => matVecMul (MV - MK) (v y))) :
    s12_hMinusOneVec V (fun y => matVecMul (sh⁻¹ • (A y - MV)) (v y)) ≤
      s12_hMinusOneVec V (fun y => matVecMul (sh⁻¹ • (A y - MK)) (v y) - ub y) +
        s12_hMinusOneVec V ub +
        ENNReal.ofReal |sh⁻¹| * s12_hMinusOneVec V (fun y => matVecMul (MV - MK) (v y)) := by
  have e : (fun y => matVecMul (sh⁻¹ • (A y - MV)) (v y)) = fun y =>
      ((matVecMul (sh⁻¹ • (A y - MK)) (v y) - ub y) + ub y) +
        (-(sh⁻¹)) • matVecMul (MV - MK) (v y) := funext fun y => s5_flux_centre_decomp _ _ _ _ _ _
  rw [e]
  have p₃' : s12_PairInt V (fun y => (-(sh⁻¹)) • matVecMul (MV - MK) (v y)) :=
    s12_pairInt_smul _ p₃
  refine (s12_hMinusOneVec_add_le V (s12_pairInt_add p₁ p₂) p₃').trans ?_
  rw [s12_hMinusOneVec_smul, abs_neg]
  exact add_le_add (s12_hMinusOneVec_add_le V p₁ p₂) le_rfl

end SuperdiffusionCLT.Section7
