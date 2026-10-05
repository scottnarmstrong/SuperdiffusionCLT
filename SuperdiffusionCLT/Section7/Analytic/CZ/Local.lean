/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.CZ.CubePerturb
public import SuperdiffusionCLT.Section7.Analytic.CZ.CubeScalarDataB
public import SuperdiffusionCLT.Section7.Analytic.Defs
public import Homogenization.Sobolev.H1.LocalizedZeroTrace
public import Homogenization.Sobolev.Foundations.Cutoff.Box
public import Homogenization.Sobolev.H1.Translation

/-!
# Local `W^{1,p}` estimates: translation and localization of weak solutions

* `IsWeakSolutionOn.translate`: translating a weak solution (and its test class) by `z`.
* `p12_grad_ae`: the gradient of `χ v` for a smooth compactly supported cutoff `χ`, almost
  everywhere, even when `χ v` is only known to lie in `H¹₀`.
* `p12_localize`: if `v` is a weak solution with data `(s, G)` and `w = χ v` lies in `H¹₀`,
  then `w` is a weak solution with data `(χ s + G·∇χ - (A∇v)·∇χ, χ G + v A ∇χ)`.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- **Translation of weak solutions.** -/
theorem IsWeakSolutionOn.translate {a : CoeffField d} {U : Set (Vec d)} {u : H1Function U}
    {f : Vec d → ℝ} {g : Vec d → Vec d} (z : Vec d) (hw : IsWeakSolutionOn a U u f g) :
    IsWeakSolutionOn (fun x => a (x - z)) (translateSet z U) (u.translate z)
      (fun x => f (x - z)) (fun x => g (x - z)) := by
  intro φ
  have h := hw (H10Function.untranslate z φ)
  have hmp := measurePreserving_subRight_restrict_translateSet z U
  have hme : MeasurableEmbedding (fun x : Vec d => x - z) := (Homeomorph.subRight z).measurableEmbedding
  have e1 := hmp.integral_comp hme
    (fun y => vecDot (matVecMul (a y) (u.grad y)) (φ.toH1Function.grad (y + z)))
  have e2 := hmp.integral_comp hme
    (fun y => f y * φ.toH1Function.toFun (y + z))
  have e3 := hmp.integral_comp hme
    (fun y => vecDot (g y) (φ.toH1Function.grad (y + z)))
  simp only [sub_add_cancel] at e1 e2 e3
  simp only [H10Function.untranslate_toH1Function, H1Function.untranslate_toFun,
    H1Function.untranslate_grad] at h
  simp only [H1Function.translate_grad]
  rw [e1, e2, e3]
  exact h



/-- The gradient of a scalar function as a vector field. -/
noncomputable def p12_grad (χ : Vec d → ℝ) (x : Vec d) : Vec d :=
  fun i => fderiv ℝ χ x (basisVec i)

theorem p12_locInt_of_memL2 {U : Set (Vec d)} {f : Vec d → ℝ} (h : MemL2On U f) :
    LocallyIntegrableOn f U volume :=
  locallyIntegrableOn_of_locallyIntegrable_restrict (h.locallyIntegrable (by norm_num))

/-- A: gradient of a product with a smooth compactly supported function, a.e. -/
theorem p12_grad_ae (Q : TriadicCube d) {χ : Vec d → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (v : H1Function (openCubeSet Q)) (w : H10Function (openCubeSet Q))
    (hw : ∀ x, w.toH1Function.toFun x = χ x * v.toFun x) :
    ∀ᵐ x ∂(volume.restrict (openCubeSet Q)),
      w.toH1Function.grad x = χ x • v.grad x + v.toFun x • p12_grad χ x := by
  set P := v.mulContDiffHasCompactSupport hχ hχc with hP
  have hfun : w.toH1Function.toFun = P.toFun := by
    funext x
    rw [hw x]
    simp [hP]
  have hall : ∀ i, (fun x => w.toH1Function.grad x i) =ᵐ[volume.restrict (openCubeSet Q)]
      (fun x => P.grad x i) := by
    intro i
    refine HasWeakPartialDerivOn.ae_eq (isOpen_openCubeSet Q)
      (p12_locInt_of_memL2 (w.toH1Function.gradMemL2 i))
      (p12_locInt_of_memL2 (P.gradMemL2 i)) ?_ (P.hasWeakGradient i)
    have := w.toH1Function.hasWeakGradient i
    rwa [hfun] at this
  have := ae_all_iff.2 hall
  filter_upwards [this] with x hx
  funext i
  have h1 := hx i
  rw [h1]
  simp [hP, p12_grad]


theorem p12_vecDot_smul_left (a : ℝ) (x y : Vec d) : vecDot (a • x) y = a * vecDot x y := by
  simp [vecDot, Finset.mul_sum, mul_assoc]

theorem p12_vecDot_add_left (x y z : Vec d) : vecDot (x + y) z = vecDot x z + vecDot y z := by
  simp [vecDot, add_mul, Finset.sum_add_distrib]

theorem p12_vecDot_add_right (x y z : Vec d) : vecDot x (y + z) = vecDot x y + vecDot x z := by
  simp [vecDot, mul_add, Finset.sum_add_distrib]

theorem p12_vecDot_smul_right (a : ℝ) (x y : Vec d) : vecDot x (a • y) = a * vecDot x y := by
  simp [vecDot, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

theorem p12_matVecMul_add_smul (M : Mat d) (a b : ℝ) (x y : Vec d) :
    matVecMul M (a • x + b • y) = a • matVecMul M x + b • matVecMul M y := by
  change M.mulVec (a • x + b • y) = a • M.mulVec x + b • M.mulVec y
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]

theorem p12_abs_vecDot_le (a b : Vec d) : |vecDot a b| ≤ d * (‖a‖ * ‖b‖) := by
  unfold vecDot
  calc |∑ i, a i * b i| ≤ ∑ i, |a i * b i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, ‖a‖ * ‖b‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        exact mul_le_mul (by simpa using norm_le_pi_norm a i) (by simpa using norm_le_pi_norm b i)
          (abs_nonneg _) (norm_nonneg _)
    _ = d * (‖a‖ * ‖b‖) := by simp

theorem p12_continuous_grad {χ : Vec d → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) :
    Continuous (p12_grad χ) := by
  refine continuous_pi fun i => ?_
  exact (hχ.continuous_fderiv (by simp)).clm_apply continuous_const

theorem p12_aesm_matVec (Q : TriadicCube d) {A : CoeffField d}
    (hA : ∀ i j, AEStronglyMeasurable (fun x => A x i j) (volume.restrict (openCubeSet Q)))
    {F : Vec d → Vec d} (hF : AEStronglyMeasurable F (normalizedCubeMeasure Q)) :
    AEStronglyMeasurable (fun x => matVecMul (A x) (F x)) (normalizedCubeMeasure Q) := by
  refine AEMeasurable.aestronglyMeasurable (aemeasurable_pi_iff.2 fun i => ?_)
  simp only [matVecMul]
  refine (Finset.univ.aestronglyMeasurable_fun_sum fun j _ => ?_).aemeasurable
  refine AEStronglyMeasurable.mul ?_ ?_
  · rw [normalizedCubeMeasure_eq_smul]
    exact (hA i j).smul_measure _
  · exact (continuous_apply j).comp_aestronglyMeasurable hF

theorem p12_memLp_matVec (Q : TriadicCube d) {A : CoeffField d} {K : ℝ}
    (hA : ∀ i j, AEStronglyMeasurable (fun x => A x i j) (volume.restrict (openCubeSet Q)))
    (hK : ∀ x ∈ openCubeSet Q, ∀ y : Vec d, ‖matVecMul (A x) y‖ ≤ K * ‖y‖)
    {F : Vec d → Vec d} (hF : MemLp F 2 (normalizedCubeMeasure Q)) :
    MemLp (fun x => matVecMul (A x) (F x)) 2 (normalizedCubeMeasure Q) := by
  refine hF.of_le_mul (c := K) (p12_aesm_matVec Q hA hF.aestronglyMeasurable) ?_
  filter_upwards [ae_mem_openCubeSet Q] with x hx
  exact hK x hx _

theorem p12_memLp_vecDot_bdd (Q : TriadicCube d) {F H : Vec d → Vec d} {Λ : ℝ}
    (hF : MemLp F 2 (normalizedCubeMeasure Q)) (hH : AEStronglyMeasurable H (normalizedCubeMeasure Q))
    (hΛ : ∀ x, ‖H x‖ ≤ Λ) :
    MemLp (fun x => vecDot (F x) (H x)) 2 (normalizedCubeMeasure Q) := by
  have hm : AEStronglyMeasurable (fun x => vecDot (F x) (H x)) (normalizedCubeMeasure Q) := by
    unfold vecDot
    refine Finset.univ.aestronglyMeasurable_fun_sum fun j _ => ?_
    exact ((continuous_apply j).comp_aestronglyMeasurable hF.aestronglyMeasurable).mul
      ((continuous_apply j).comp_aestronglyMeasurable hH)
  refine hF.of_le_mul (c := d * Λ) hm (Filter.Eventually.of_forall fun x => ?_)
  have := p12_abs_vecDot_le (F x) (H x)
  rw [Real.norm_eq_abs]
  have h2 : ‖F x‖ * ‖H x‖ ≤ ‖F x‖ * Λ := mul_le_mul_of_nonneg_left (hΛ x) (norm_nonneg _)
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  calc |vecDot (F x) (H x)| ≤ d * (‖F x‖ * ‖H x‖) := this
    _ ≤ d * (‖F x‖ * Λ) := mul_le_mul_of_nonneg_left h2 hd
    _ = d * Λ * ‖F x‖ := by ring


/-- B: localization of a weak equation. -/
theorem p12_localize (Q : TriadicCube d) {A : CoeffField d} {K : ℝ}
    (hA : ∀ i j, AEStronglyMeasurable (fun x => A x i j) (volume.restrict (openCubeSet Q)))
    (hK : ∀ x ∈ openCubeSet Q, ∀ y : Vec d, ‖matVecMul (A x) y‖ ≤ K * ‖y‖)
    {u : H1Function (openCubeSet Q)} {s : Vec d → ℝ} {G : Vec d → Vec d}
    (hs : MemLp s 2 (normalizedCubeMeasure Q)) (hG : MemLp G 2 (normalizedCubeMeasure Q))
    (hu : IsWeakSolutionOn A (openCubeSet Q) u s G)
    {χ : Vec d → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    {M Λ : ℝ} (hM : ∀ x, |χ x| ≤ M) (hΛ : ∀ x, ‖p12_grad χ x‖ ≤ Λ)
    (w : H10Function (openCubeSet Q)) (hw : ∀ x, w.toH1Function.toFun x = χ x * u.toFun x) :
    IsWeakSolutionOn A (openCubeSet Q) w.toH1Function
      (fun x => χ x * s x + vecDot (G x) (p12_grad χ x) -
        vecDot (matVecMul (A x) (u.grad x)) (p12_grad χ x))
      (fun x => χ x • G x + u.toFun x • matVecMul (A x) (p12_grad χ x)) := by
  intro ψ
  beta_reduce
  set ψ' : H10Function (openCubeSet Q) := ψ.mulContDiffHasCompactSupport hχ hχc with hψ'
  have hψ'f : ∀ x, ψ'.toH1Function.toFun x = χ x * ψ.toH1Function.toFun x := fun x => by
    simp [hψ']
  have hψ'g : ∀ x, ψ'.toH1Function.grad x =
      χ x • ψ.toH1Function.grad x + ψ.toH1Function.toFun x • p12_grad χ x := by
    intro x; funext i
    change (ψ.toH1Function.mulContDiffHasCompactSupport hχ hχc).grad x i = _
    simp [p12_grad]
  have hae := p12_grad_ae Q hχ hχc u w hw
  have hu2 : MemLp u.grad 2 (normalizedCubeMeasure Q) :=
    memLp_normalized_of_memVectorL2 Q u.grad_memVectorL2
  have huf : MemLp u.toFun 2 (normalizedCubeMeasure Q) := H1Function.memL2_normalizedCubeMeasure u
  have hgψ := memLp_two_grad Q ψ
  have hgψ' := memLp_two_grad Q ψ'
  have hψf : MemLp ψ.toH1Function.toFun 2 (normalizedCubeMeasure Q) :=
    H1Function.memL2_normalizedCubeMeasure ψ.toH1Function
  have hψ'f2 : MemLp ψ'.toH1Function.toFun 2 (normalizedCubeMeasure Q) :=
    H1Function.memL2_normalizedCubeMeasure ψ'.toH1Function
  have hgw := memLp_two_grad Q w
  have hAu := p12_memLp_matVec Q hA hK hu2
  have hAw := p12_memLp_matVec Q hA hK hgw
  have hgχ : AEStronglyMeasurable (p12_grad χ) (normalizedCubeMeasure Q) :=
    (p12_continuous_grad hχ).aestronglyMeasurable
  have hB : AEStronglyMeasurable (fun x => matVecMul (A x) (p12_grad χ x))
      (normalizedCubeMeasure Q) := p12_aesm_matVec Q hA hgχ
  have hχm : AEStronglyMeasurable χ (normalizedCubeMeasure Q) := hχ.continuous.aestronglyMeasurable
  have hs' : MemLp (fun x => χ x * s x + vecDot (G x) (p12_grad χ x) -
      vecDot (matVecMul (A x) (u.grad x)) (p12_grad χ x)) 2 (normalizedCubeMeasure Q) := by
    have h1 : MemLp (fun x => χ x * s x) 2 (normalizedCubeMeasure Q) := by
      refine hs.of_le_mul (c := M) (hχm.mul hs.aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)
    exact (h1.add (p12_memLp_vecDot_bdd Q hG hgχ hΛ)).sub (p12_memLp_vecDot_bdd Q hAu hgχ hΛ)
  have hG' : MemLp (fun x => χ x • G x + u.toFun x • matVecMul (A x) (p12_grad χ x)) 2
      (normalizedCubeMeasure Q) := by
    have h1 : MemLp (fun x => χ x • G x) 2 (normalizedCubeMeasure Q) := by
      refine hG.of_le_mul (c := M) (hχm.smul hG.aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)
    have h2 : MemLp (fun x => u.toFun x • matVecMul (A x) (p12_grad χ x)) 2
        (normalizedCubeMeasure Q) := by
      refine huf.of_le_mul (c := |K| * Λ) (huf.aestronglyMeasurable.smul hB) ?_
      filter_upwards [ae_mem_openCubeSet Q] with x hx
      rw [norm_smul]
      have h3 : ‖matVecMul (A x) (p12_grad χ x)‖ ≤ |K| * Λ :=
        (hK x hx (p12_grad χ x)).trans
          (mul_le_mul (le_abs_self K) (hΛ x) (norm_nonneg _) (abs_nonneg K))
      rw [mul_comm (|K| * Λ)]
      exact mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    exact h1.add h2
  -- integrability
  have hIL := integrable_vecDot_of_memLp Q hAw hgψ
  have hIX := integrable_vecDot_of_memLp Q hAu hgψ'
  have hIG := integrable_vecDot_of_memLp Q hG hgψ'
  have hIG' := integrable_vecDot_of_memLp Q hG' hgψ
  have hIs : Integrable (fun x => s x * ψ'.toH1Function.toFun x)
      (volume.restrict (openCubeSet Q)) :=
    (memLp_restrict_of_normalized Q hs).integrable_mul (memLp_restrict_of_normalized Q hψ'f2)
  have hIs' : Integrable (fun x => (χ x * s x + vecDot (G x) (p12_grad χ x) -
        vecDot (matVecMul (A x) (u.grad x)) (p12_grad χ x)) * ψ.toH1Function.toFun x)
      (volume.restrict (openCubeSet Q)) :=
    (memLp_restrict_of_normalized Q hs').integrable_mul (memLp_restrict_of_normalized Q hψf)
  -- the extra term
  set E : Vec d → ℝ := fun x =>
    -(ψ.toH1Function.toFun x * vecDot (matVecMul (A x) (u.grad x)) (p12_grad χ x)) +
      u.toFun x * vecDot (matVecMul (A x) (p12_grad χ x)) (ψ.toH1Function.grad x) with hE
  have hE1 : ∀ᵐ x ∂(volume.restrict (openCubeSet Q)),
      vecDot (matVecMul (A x) (w.toH1Function.grad x)) (ψ.toH1Function.grad x) =
        vecDot (matVecMul (A x) (u.grad x)) (ψ'.toH1Function.grad x) + E x := by
    filter_upwards [hae] with x hx
    rw [hx, hψ'g, p12_matVecMul_add_smul, p12_vecDot_add_left, p12_vecDot_smul_left,
      p12_vecDot_smul_left, p12_vecDot_add_right, p12_vecDot_smul_right, p12_vecDot_smul_right,
      hE]
    ring
  have hE2 : ∀ x, (χ x * s x + vecDot (G x) (p12_grad χ x) -
        vecDot (matVecMul (A x) (u.grad x)) (p12_grad χ x)) * ψ.toH1Function.toFun x +
      vecDot (χ x • G x + u.toFun x • matVecMul (A x) (p12_grad χ x)) (ψ.toH1Function.grad x) =
      (s x * ψ'.toH1Function.toFun x + vecDot (G x) (ψ'.toH1Function.grad x)) + E x := by
    intro x
    rw [hψ'g, hψ'f, p12_vecDot_add_left, p12_vecDot_smul_left, p12_vecDot_smul_left,
      p12_vecDot_add_right, p12_vecDot_smul_right, p12_vecDot_smul_right, hE]
    ring
  have hEint : Integrable E (volume.restrict (openCubeSet Q)) := by
    refine (hIL.sub hIX).congr ?_
    filter_upwards [hE1] with x hx
    simp only [Pi.sub_apply]
    rw [hx]; ring
  have hIsG : Integrable (fun x => s x * ψ'.toH1Function.toFun x +
      vecDot (G x) (ψ'.toH1Function.grad x)) (volume.restrict (openCubeSet Q)) := hIs.add hIG
  have h0 := hu ψ'
  calc ∫ x in openCubeSet Q, vecDot (matVecMul (A x) (w.toH1Function.grad x))
          (ψ.toH1Function.grad x)
      = ∫ x in openCubeSet Q, (vecDot (matVecMul (A x) (u.grad x)) (ψ'.toH1Function.grad x) + E x) :=
        integral_congr_ae hE1
    _ = (∫ x in openCubeSet Q, vecDot (matVecMul (A x) (u.grad x)) (ψ'.toH1Function.grad x)) +
          ∫ x in openCubeSet Q, E x := integral_add hIX hEint
    _ = ((∫ x in openCubeSet Q, s x * ψ'.toH1Function.toFun x) +
          ∫ x in openCubeSet Q, vecDot (G x) (ψ'.toH1Function.grad x)) +
          ∫ x in openCubeSet Q, E x := by rw [h0]
    _ = ∫ x in openCubeSet Q, ((s x * ψ'.toH1Function.toFun x +
          vecDot (G x) (ψ'.toH1Function.grad x)) + E x) := by
        rw [integral_add hIsG hEint, integral_add hIs hIG]
    _ = ∫ x in openCubeSet Q, ((χ x * s x + vecDot (G x) (p12_grad χ x) -
        vecDot (matVecMul (A x) (u.grad x)) (p12_grad χ x)) * ψ.toH1Function.toFun x +
      vecDot (χ x • G x + u.toFun x • matVecMul (A x) (p12_grad χ x)) (ψ.toH1Function.grad x)) :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => (hE2 x).symm)
    _ = _ := integral_add hIs' hIG'



theorem p12_isProb (Q : TriadicCube d) : IsProbabilityMeasure (normalizedCubeMeasure Q) :=
  ⟨normalizedCubeMeasure_apply_univ Q⟩

theorem p12_eLpNorm_mono_exp (Q : TriadicCube d) {E : Type*} [NormedAddCommGroup E]
    {F : Vec d → E} {p q : ℝ≥0∞} (h : p ≤ q) :
    eLpNorm F p (normalizedCubeMeasure Q) ≤ eLpNorm F q (normalizedCubeMeasure Q) := by
  have := p12_isProb Q
  exact eLpNorm_le_eLpNorm_of_exponent_le h

theorem p12_memLp_mono_exp (Q : TriadicCube d) {E : Type*} [NormedAddCommGroup E]
    {F : Vec d → E} {p q : ℝ≥0∞} (h : p ≤ q) (hF : MemLp F q (normalizedCubeMeasure Q)) :
    MemLp F p (normalizedCubeMeasure Q) := by
  have := p12_isProb Q
  exact hF.mono_exponent h

theorem p12_ofReal_mul_ofReal_div {ℓ : ℝ} (hℓ : 0 < ℓ) (x : ℝ) :
    ENNReal.ofReal ℓ * ENNReal.ofReal (x / ℓ) = ENNReal.ofReal x := by
  rw [← ENNReal.ofReal_mul hℓ.le]
  congr 1
  field_simp

theorem p12_comb {X x1 x2 x3 : ℝ≥0∞} {α β γ C : ℝ}
    (h : X ≤ ENNReal.ofReal α * x1 + ENNReal.ofReal β * x2 + ENNReal.ofReal γ * x3)
    (hα : α ≤ C) (hβ : β ≤ C) (hγ : γ ≤ C) :
    X ≤ ENNReal.ofReal C * (x1 + x2 + x3) := by
  refine h.trans ?_
  rw [mul_add, mul_add]
  gcongr

/-- A cutoff attaining the value `1` has zero gradient there. -/
theorem p12_grad_eq_zero_of_eq_one {χ : Vec d → ℝ}
    (h1 : ∀ x, χ x ≤ 1) {x : Vec d} (hx : χ x = 1) : p12_grad χ x = 0 := by
  have hmax : IsLocalMax χ x := Filter.Eventually.of_forall fun y => by rw [hx]; exact h1 y
  have := hmax.fderiv_eq_zero
  funext i
  simp [p12_grad, this]

/-- Away from the support the gradient vanishes. -/
theorem p12_grad_eq_zero_of_notMem {χ : Vec d → ℝ} {x : Vec d} (hx : x ∉ tsupport χ) :
    p12_grad χ x = 0 := by
  have h : χ =ᶠ[nhds x] 0 := notMem_tsupport_iff_eventuallyEq.1 hx
  have h2 : fderiv ℝ χ x = fderiv ℝ (0 : Vec d → ℝ) x := h.fderiv_eq (𝕜 := ℝ)
  funext i
  simp [p12_grad, h2]

theorem p12_matVecMul_zero (M : Mat d) : matVecMul M (0 : Vec d) = 0 := by
  funext i
  simp [matVecMul]

theorem p12_aesm_vecDot (Q : TriadicCube d) {F H : Vec d → Vec d}
    (hF : AEStronglyMeasurable F (normalizedCubeMeasure Q))
    (hH : AEStronglyMeasurable H (normalizedCubeMeasure Q)) :
    AEStronglyMeasurable (fun x => vecDot (F x) (H x)) (normalizedCubeMeasure Q) := by
  unfold vecDot
  refine Finset.univ.aestronglyMeasurable_fun_sum fun j _ => ?_
  have h1 : AEStronglyMeasurable (fun x => F x j) (normalizedCubeMeasure Q) :=
    (continuous_apply j).comp_aestronglyMeasurable hF
  have h2 : AEStronglyMeasurable (fun x => H x j) (normalizedCubeMeasure Q) :=
    (continuous_apply j).comp_aestronglyMeasurable hH
  exact h1.mul h2


theorem p12_eLpNorm_const_mul_norm {α E' : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E'] {p : ℝ≥0∞} {r : ℝ} (hr : 0 ≤ r) {W : α → E'} (hW : AEStronglyMeasurable W μ) :
    eLpNorm (fun x => r * ‖W x‖) p μ = ENNReal.ofReal r * eLpNorm W p μ := by
  have := eLpNorm_const_smul (μ := μ) r (fun x => ‖W x‖) p
  rw [show (fun x => r * ‖W x‖) = r • (fun x => ‖W x‖) from rfl, this, eLpNorm_norm W hW,
    Real.enorm_eq_ofReal hr]

theorem p12_bound3 {α E E1 E2 E3 : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedAddCommGroup E1] [NormedAddCommGroup E2]
    [NormedAddCommGroup E3] {p : ℝ≥0∞} (hp : 1 ≤ p) {F : α → E} {X : α → E1} {Y : α → E2}
    {Z : α → E3} {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hF : AEStronglyMeasurable F μ) (hX : MemLp X p μ) (hY : MemLp Y p μ) (hZ : MemLp Z p μ)
    (h : ∀ᵐ x ∂μ, ‖F x‖ ≤ a * ‖X x‖ + b * ‖Y x‖ + c * ‖Z x‖) :
    MemLp F p μ ∧ eLpNorm F p μ ≤ ENNReal.ofReal a * eLpNorm X p μ +
      ENNReal.ofReal b * eLpNorm Y p μ + ENNReal.ofReal c * eLpNorm Z p μ := by
  have hX' : MemLp (fun x => ‖X x‖) p μ := hX.norm
  have hY' : MemLp (fun x => ‖Y x‖) p μ := hY.norm
  have hZ' : MemLp (fun x => ‖Z x‖) p μ := hZ.norm
  have e1 : MemLp (fun x => a * ‖X x‖ + b * ‖Y x‖ + c * ‖Z x‖) p μ :=
    ((hX'.const_mul a).add (hY'.const_mul b)).add (hZ'.const_mul c)
  have hle : eLpNorm F p μ ≤ eLpNorm (fun x => a * ‖X x‖ + b * ‖Y x‖ + c * ‖Z x‖) p μ := by
    refine eLpNorm_mono_ae hF ?_
    filter_upwards [h] with x hx
    have h0 : 0 ≤ a * ‖X x‖ + b * ‖Y x‖ + c * ‖Z x‖ := by positivity
    rwa [Real.norm_of_nonneg h0]
  refine ⟨e1.of_le hF (by
    filter_upwards [h] with x hx
    have h0 : 0 ≤ a * ‖X x‖ + b * ‖Y x‖ + c * ‖Z x‖ := by positivity
    rwa [Real.norm_of_nonneg h0]), ?_⟩
  refine hle.trans ?_
  have t1 := eLpNorm_add_le (μ := μ) (p := p)
    (f := fun x => a * ‖X x‖ + b * ‖Y x‖) (g := fun x => c * ‖Z x‖) hp
  have t2 := eLpNorm_add_le (μ := μ) (p := p)
    (f := fun x => a * ‖X x‖) (g := fun x => b * ‖Y x‖) hp
  calc eLpNorm (fun x => a * ‖X x‖ + b * ‖Y x‖ + c * ‖Z x‖) p μ
      ≤ eLpNorm (fun x => a * ‖X x‖ + b * ‖Y x‖) p μ + eLpNorm (fun x => c * ‖Z x‖) p μ := t1
    _ ≤ (eLpNorm (fun x => a * ‖X x‖) p μ + eLpNorm (fun x => b * ‖Y x‖) p μ) +
          eLpNorm (fun x => c * ‖Z x‖) p μ := by gcongr; exact t2
    _ = _ := by
        rw [p12_eLpNorm_const_mul_norm ha hX.aestronglyMeasurable, p12_eLpNorm_const_mul_norm hb hY.aestronglyMeasurable,
          p12_eLpNorm_const_mul_norm hc hZ.aestronglyMeasurable]

end SuperdiffusionCLT.Section7
