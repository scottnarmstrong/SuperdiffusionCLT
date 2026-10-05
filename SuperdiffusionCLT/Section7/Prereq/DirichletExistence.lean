/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.DirichletExistenceB
public import SuperdiffusionCLT.Section6.Prereq.EuclidBall
public import Homogenization.Ambient.CoefficientFieldHilbert
public import Homogenization.Sobolev.PotentialSolenoidalL2

/-!
# Lax–Milgram for the `H¹₀` Dirichlet problem on a bounded open set

The closed graph of `u ↦ (u, ∇u)` over `H¹₀(U)` is a Hilbert space `H10HilbertSpace U` inside
the `ℓ²`-product `L²(U) × L²(U; ℝᵈ)`. For an elliptic, not necessarily symmetric, coefficient
field the form `(z, w) ↦ ⟪a ∇z, ∇w⟫` is bounded and coercive on it, so Mathlib's
`IsCoercive.continuousLinearEquivOfBilin` solves the weak problem
`-∇·(a∇u) = f + ∇·g`, `u ∈ H¹₀(U)`, for `f ∈ L²` and `g ∈ L²`.

## Main results

* `Section7.h10_dirichlet_wellPosed`: existence, uniqueness and the energy bound.
* `Section7.exists_h10_weak_solution`, `Section7.h10_weak_solution_unique`,
  `Section7.h10_energy_bound`: the three parts separately.
* `Section7.isEllipticFieldOn_one_euclidBall`, `Section7.isBoundedDomain_euclidBall`: a Euclidean
  ball with identity coefficients satisfies the hypotheses.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open scoped RealInnerProductSpace
open Homogenization

variable {d : ℕ} {U : Set (Vec d)}

/-- Hilbert ambient for the `H¹₀` graph. -/
noncomputable abbrev H10Ambient (U : Set (Vec d)) :=
  WithLp 2 (ScalarL2 U × HilbertVectorL2 U)

noncomputable abbrev h10AmbientEquiv (U : Set (Vec d)) :
    H10Ambient U ≃L[ℝ] ScalarL2 U × HilbertVectorL2 U :=
  WithLp.prodContinuousLinearEquiv 2 ℝ (ScalarL2 U) (HilbertVectorL2 U)

/-- The closed `H¹₀` graph inside the Hilbert ambient. -/
noncomputable def h10HilbertClosedSubmodule (U : Set (Vec d)) :
    ClosedSubmodule ℝ (H10Ambient U) :=
  (h10GraphClosedSubmodule U).comap (h10AmbientEquiv U).toContinuousLinearMap

/-- The Hilbert space `H¹₀(U)`, realised as the closed graph of `u ↦ (u, ∇u)`. -/
abbrev H10HilbertSpace (U : Set (Vec d)) :=
  ↥(h10HilbertClosedSubmodule U).toSubmodule

noncomputable instance : NormedAddCommGroup (H10HilbertSpace U) :=
  inferInstanceAs (NormedAddCommGroup (h10HilbertClosedSubmodule U).toSubmodule)

noncomputable instance : InnerProductSpace ℝ (H10HilbertSpace U) :=
  inferInstanceAs (InnerProductSpace ℝ (h10HilbertClosedSubmodule U).toSubmodule)

noncomputable instance : CompleteSpace (H10HilbertSpace U) :=
  (h10HilbertClosedSubmodule U).isClosed.completeSpace_coe

namespace H10HilbertSpace

/-- Value component. -/
abbrev value (z : H10HilbertSpace U) : ScalarL2 U := z.1.fst

/-- Gradient component. -/
abbrev gradient (z : H10HilbertSpace U) : HilbertVectorL2 U := z.1.snd

noncomputable def valueCLM : H10HilbertSpace U →L[ℝ] ScalarL2 U :=
  (WithLp.fstL (p := 2) (𝕜 := ℝ) (α := ScalarL2 U) (β := HilbertVectorL2 U)).comp
    (h10HilbertClosedSubmodule U).toSubmodule.subtypeL

noncomputable def gradientCLM : H10HilbertSpace U →L[ℝ] HilbertVectorL2 U :=
  (WithLp.sndL (p := 2) (𝕜 := ℝ) (α := ScalarL2 U) (β := HilbertVectorL2 U)).comp
    (h10HilbertClosedSubmodule U).toSubmodule.subtypeL

@[simp] theorem valueCLM_apply (z : H10HilbertSpace U) : valueCLM z = value z := rfl

@[simp] theorem gradientCLM_apply (z : H10HilbertSpace U) : gradientCLM z = gradient z := rfl

theorem norm_sq_eq (z : H10HilbertSpace U) :
    ‖z‖ ^ 2 = ‖value z‖ ^ 2 + ‖gradient z‖ ^ 2 := by
  change ‖(z.1 : H10Ambient U)‖ ^ 2 = _
  rw [WithLp.prod_norm_sq_eq_of_L2]

/-- The graph point of an `H¹₀` function. -/
theorem pair_mem (u : H10Function U) :
    (WithLp.toLp 2 (u.toH1Function.toScalarL2, u.toH1Function.gradToHilbertVectorL2) :
      H10Ambient U) ∈ (h10HilbertClosedSubmodule U).toSubmodule :=
  (Submodule.le_topologicalClosure _) (h10_pair_mem_h10GraphSubmodule u)

/-- The element of `H¹₀(U)` (Hilbert) attached to an `H¹₀` function. -/
noncomputable def ofH10Function (u : H10Function U) : H10HilbertSpace U :=
  ⟨_, pair_mem u⟩

@[simp] theorem value_ofH10Function (u : H10Function U) :
    value (ofH10Function u) = u.toH1Function.toScalarL2 := rfl

@[simp] theorem gradient_ofH10Function (u : H10Function U) :
    gradient (ofH10Function u) = u.toH1Function.gradToHilbertVectorL2 := rfl

/-- Every element of the Hilbert graph is realised by an `H¹₀` function on an open set. -/
theorem exists_h10Function (hUo : IsOpen U) (z : H10HilbertSpace U) :
    ∃ u : H10Function U, u.toH1Function.toScalarL2 = value z ∧
      u.toH1Function.gradToHilbertVectorL2 = gradient z :=
  exists_h10Function_of_mem_closedGraph hUo z.2

/-- Poincaré inequality on the Hilbert graph of a bounded open set. -/
theorem exists_norm_value_le [NeZero d] (hUo : IsOpen U) (hUb : IsBoundedDomain U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : H10HilbertSpace U, ‖value z‖ ≤ C * ‖gradient z‖ := by
  rcases h10Graph_norm_value_le_of_bounded hUo hUb with ⟨C, hC, h⟩
  exact ⟨C, hC, fun z => h _ z.2⟩

end H10HilbertSpace

/-- Every Hilbert-vector `L²` class is the class of its vector representative. -/
theorem eq_toHilbertVectorL2OfVecField (F : HilbertVectorL2 U) :
    F = toHilbertVectorL2OfVecField
      (MeasureTheory.Lp.memLp (hilbertVectorL2ToVectorL2 (U := U) F)) := by
  calc
    F = vectorL2ToHilbertVectorL2 (U := U) (hilbertVectorL2ToVectorL2 (U := U) F) :=
      (vectorL2ToHilbertVectorL2_hilbertVectorL2ToVectorL2 (U := U) F).symm
    _ = vectorL2ToHilbertVectorL2 (U := U)
          (toVectorL2 (MeasureTheory.Lp.memLp (hilbertVectorL2ToVectorL2 (U := U) F))) := by
        congr 1
        exact (MeasureTheory.Lp.toLp_coeFn _ _).symm
    _ = _ := rfl

/-- Coercivity of a (nonsymmetric) elliptic coefficient operator on `L²(U; ℝᵈ)`. -/
theorem coeffOperator_coercive {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam U a) (F : HilbertVectorL2 U) :
    lam * ‖F‖ ^ 2 ≤ inner ℝ (hilbertCoeffOperator hEll F) F := by
  set V : VectorL2 U := hilbertVectorL2ToVectorL2 (U := U) F with hV
  have hmem : MemVectorL2 U V := MeasureTheory.Lp.memLp V
  have hF : F = toHilbertVectorL2OfVecField hmem := eq_toHilbertVectorL2OfVecField F
  have hA : hilbertCoeffOperator hEll F = toHilbertVectorL2OfVecField
      (memVectorL2_matVecMul_of_isEllipticFieldOn hEll hmem) := by
    rw [hF]
    exact hilbertCoeffOperator_toHilbertVectorL2OfVecField hEll hmem
  have hsqInt : MeasureTheory.IntegrableOn (fun x => vecNormSq (V x)) U := by
    simpa [vecNormSq] using integrableOn_vecDot_of_memVectorL2 hmem hmem
  have henergyInt : MeasureTheory.IntegrableOn
      (fun x => vecDot (matVecMul (a x) (V x)) (V x)) U :=
    integrableOn_vecDot_of_memVectorL2
      (memVectorL2_matVecMul_of_isEllipticFieldOn hEll hmem) hmem
  have hUm : MeasurableSet U := measurableSet_of_isEllipticFieldOn hEll
  have hmemU : ∀ᵐ x ∂ volumeMeasureOn U, x ∈ U :=
    (MeasureTheory.ae_restrict_iff' hUm).2 (Filter.Eventually.of_forall fun x hx => hx)
  have hpoint : ∀ᵐ x ∂ volumeMeasureOn U,
      lam * vecNormSq (V x) ≤ vecDot (matVecMul (a x) (V x)) (V x) := by
    filter_upwards [hmemU] with x hx
    simpa [vecDot_comm] using (hEll.2 x hx).2.2.1 (V x)
  have hnormSq : ‖F‖ ^ 2 = ∫ x in U, vecNormSq (V x) ∂MeasureTheory.volume := by
    calc
      ‖F‖ ^ 2 = inner ℝ F F := by simp
      _ = inner ℝ (toHilbertVectorL2OfVecField hmem) (toHilbertVectorL2OfVecField hmem) := by
          rw [← hF]
      _ = ∫ x in U, vecDot (V x) (V x) ∂MeasureTheory.volume :=
          inner_toHilbertVectorL2OfVecField_eq_integral hmem hmem
      _ = _ := by simp [vecNormSq]
  calc
    lam * ‖F‖ ^ 2 = ∫ x in U, lam * vecNormSq (V x) ∂MeasureTheory.volume := by
        rw [hnormSq, MeasureTheory.integral_const_mul]
    _ ≤ ∫ x in U, vecDot (matVecMul (a x) (V x)) (V x) ∂MeasureTheory.volume :=
        MeasureTheory.integral_mono_ae (hsqInt.const_mul lam) henergyInt hpoint
    _ = inner ℝ (hilbertCoeffOperator hEll F) F := by
        rw [hA]
        conv_rhs => rw [hF]
        exact (inner_toHilbertVectorL2OfVecField_eq_integral
          (memVectorL2_matVecMul_of_isEllipticFieldOn hEll hmem) hmem).symm

/-- The (nonsymmetric) coefficient bilinear form on the Hilbert graph. -/
noncomputable def coeffBilin {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam U a) :
    H10HilbertSpace U →L[ℝ] H10HilbertSpace U →L[ℝ] ℝ :=
  ContinuousLinearMap.bilinearComp
    (isBoundedBilinearMap_inner (𝕜 := ℝ)).toContinuousLinearMap
    ((hilbertCoeffOperator hEll).comp H10HilbertSpace.gradientCLM) H10HilbertSpace.gradientCLM

theorem coeffBilin_apply {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam U a) (z w : H10HilbertSpace U) :
    coeffBilin hEll z w =
      inner ℝ (hilbertCoeffOperator hEll (H10HilbertSpace.gradient z))
        (H10HilbertSpace.gradient w) := by
  simp [coeffBilin, ContinuousLinearMap.bilinearComp_apply]

/-- The forcing functional `w ↦ ⟪f, w⟫ + ⟪g, ∇w⟫`. -/
noncomputable def forcingFunctional {f : Vec d → ℝ} {g : Vec d → Vec d}
    (hf : MemScalarL2 U f) (hg : MemVectorL2 U g) : H10HilbertSpace U →L[ℝ] ℝ :=
  (InnerProductSpace.toDual ℝ (ScalarL2 U) (toScalarL2 hf)).comp H10HilbertSpace.valueCLM +
  (InnerProductSpace.toDual ℝ (HilbertVectorL2 U) (toHilbertVectorL2OfVecField hg)).comp
    H10HilbertSpace.gradientCLM

theorem forcingFunctional_apply {f : Vec d → ℝ} {g : Vec d → Vec d}
    (hf : MemScalarL2 U f) (hg : MemVectorL2 U g) (w : H10HilbertSpace U) :
    forcingFunctional hf hg w =
      inner ℝ (toScalarL2 hf) (H10HilbertSpace.value w) +
        inner ℝ (toHilbertVectorL2OfVecField hg) (H10HilbertSpace.gradient w) := by
  simp [forcingFunctional]

/-- Coercivity of the coefficient form on the Hilbert graph of a bounded open set. -/
theorem isCoercive_coeffBilin [NeZero d] {lam Lam : ℝ} {a : CoeffField d}
    (hUo : IsOpen U) (hUb : IsBoundedDomain U) (hne : U.Nonempty)
    (hEll : IsEllipticFieldOn lam Lam U a) : IsCoercive (coeffBilin hEll) := by
  rcases hne with ⟨x0, hx0⟩
  have hlam : 0 < lam := (hEll.2 x0 hx0).1
  rcases H10HilbertSpace.exists_norm_value_le hUo hUb with ⟨C, hC0, hC⟩
  have hpos : 0 < C ^ 2 + 1 := by positivity
  refine ⟨lam / (C ^ 2 + 1), by positivity, fun z => ?_⟩
  rw [coeffBilin_apply]
  have h1 := coeffOperator_coercive hEll (H10HilbertSpace.gradient z)
  have h2 : ‖z‖ ^ 2 ≤ (C ^ 2 + 1) * ‖H10HilbertSpace.gradient z‖ ^ 2 := by
    rw [H10HilbertSpace.norm_sq_eq]
    have := hC z
    have h3 : ‖H10HilbertSpace.value z‖ ^ 2 ≤ (C * ‖H10HilbertSpace.gradient z‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) this 2
    nlinarith only [h3]
  have h4 : lam / (C ^ 2 + 1) * ‖z‖ * ‖z‖ ≤ lam * ‖H10HilbertSpace.gradient z‖ ^ 2 := by
    have : lam / (C ^ 2 + 1) * ‖z‖ * ‖z‖ = lam / (C ^ 2 + 1) * ‖z‖ ^ 2 := by ring
    rw [this, div_mul_eq_mul_div, div_le_iff₀ hpos]
    nlinarith only [h2, hlam]
  linarith only [h1, h4]

/-- Lax–Milgram on the Hilbert graph: a solution of the abstract weak problem. -/
theorem exists_graph_solution [NeZero d] {lam Lam : ℝ} {a : CoeffField d}
    {f : Vec d → ℝ} {g : Vec d → Vec d}
    (hUo : IsOpen U) (hUb : IsBoundedDomain U) (hne : U.Nonempty)
    (hEll : IsEllipticFieldOn lam Lam U a) (hf : MemScalarL2 U f) (hg : MemVectorL2 U g) :
    ∃ z : H10HilbertSpace U, ∀ w, coeffBilin hEll z w = forcingFunctional hf hg w := by
  have hB := isCoercive_coeffBilin hUo hUb hne hEll
  refine ⟨hB.continuousLinearEquivOfBilin.symm
    ((InnerProductSpace.toDual ℝ (H10HilbertSpace U)).symm (forcingFunctional hf hg)), fun w => ?_⟩
  rw [← hB.continuousLinearEquivOfBilin_apply, ContinuousLinearEquiv.apply_symm_apply]
  simp

theorem coeffBilin_ofH10Function {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam U a) (u φ : H10Function U) :
    coeffBilin hEll (H10HilbertSpace.ofH10Function u) (H10HilbertSpace.ofH10Function φ) =
      ∫ x in U, vecDot (matVecMul (a x) (u.toH1Function.grad x)) (φ.toH1Function.grad x)
        ∂MeasureTheory.volume := by
  rw [coeffBilin_apply, H10HilbertSpace.gradient_ofH10Function,
    H10HilbertSpace.gradient_ofH10Function]
  have hu : u.toH1Function.gradToHilbertVectorL2 =
      toHilbertVectorL2OfVecField u.toH1Function.grad_memVectorL2 := rfl
  have hφ : φ.toH1Function.gradToHilbertVectorL2 =
      toHilbertVectorL2OfVecField φ.toH1Function.grad_memVectorL2 := rfl
  rw [hu, hφ, hilbertCoeffOperator_toHilbertVectorL2OfVecField]
  exact inner_toHilbertVectorL2OfVecField_eq_integral _ _

theorem forcingFunctional_ofH10Function {f : Vec d → ℝ} {g : Vec d → Vec d}
    (hf : MemScalarL2 U f) (hg : MemVectorL2 U g) (φ : H10Function U) :
    forcingFunctional hf hg (H10HilbertSpace.ofH10Function φ) =
      (∫ x in U, f x * φ.toH1Function.toFun x ∂MeasureTheory.volume) +
        ∫ x in U, vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume := by
  rw [forcingFunctional_apply, H10HilbertSpace.value_ofH10Function,
    H10HilbertSpace.gradient_ofH10Function]
  congr 1
  · have hφ : φ.toH1Function.toScalarL2 = toScalarL2 φ.toH1Function.memL2 := rfl
    rw [hφ, MeasureTheory.L2.inner_def]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [coeFn_toScalarL2 hf, coeFn_toScalarL2 φ.toH1Function.memL2] with x h1 h2
    simp [h1, h2, mul_comm]
  · have hφ : φ.toH1Function.gradToHilbertVectorL2 =
        toHilbertVectorL2OfVecField φ.toH1Function.grad_memVectorL2 := rfl
    rw [hφ]
    exact inner_toHilbertVectorL2OfVecField_eq_integral _ _

theorem H10HilbertSpace.ofH10Function_eq {z : H10HilbertSpace U} {u : H10Function U}
    (hv : u.toH1Function.toScalarL2 = H10HilbertSpace.value z)
    (hg : u.toH1Function.gradToHilbertVectorL2 = H10HilbertSpace.gradient z) :
    H10HilbertSpace.ofH10Function u = z := by
  apply Subtype.ext
  apply WithLp.ofLp_injective
  exact Prod.ext hv hg

/-- **Existence** for the zero-trace Dirichlet problem `-∇·(a∇u) = f + ∇·g` on a bounded open
set, for bounded coercive, not necessarily symmetric, coefficients. -/
theorem exists_h10_weak_solution [NeZero d] {lam Lam : ℝ} {a : CoeffField d}
    {f : Vec d → ℝ} {g : Vec d → Vec d}
    (hUo : IsOpen U) (hUb : IsBoundedDomain U) (hne : U.Nonempty)
    (hEll : IsEllipticFieldOn lam Lam U a) (hf : MemScalarL2 U f) (hg : MemVectorL2 U g) :
    ∃ u : H10Function U, ∀ φ : H10Function U,
      ∫ x in U, vecDot (matVecMul (a x) (u.toH1Function.grad x)) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume =
        (∫ x in U, f x * φ.toH1Function.toFun x ∂MeasureTheory.volume) +
          ∫ x in U, vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume := by
  rcases exists_graph_solution hUo hUb hne hEll hf hg with ⟨z, hz⟩
  rcases H10HilbertSpace.exists_h10Function hUo z with ⟨u, hv, hgr⟩
  refine ⟨u, fun φ => ?_⟩
  rw [← coeffBilin_ofH10Function hEll, ← forcingFunctional_ofH10Function hf hg,
    H10HilbertSpace.ofH10Function_eq hv hgr]
  exact hz _

/-- Every weak solution tests against all of the Hilbert graph. -/
theorem coeffBilin_eq_forcing_of_weak [NeZero d] {lam Lam : ℝ} {a : CoeffField d}
    {f : Vec d → ℝ} {g : Vec d → Vec d} (hUo : IsOpen U)
    (hEll : IsEllipticFieldOn lam Lam U a) (hf : MemScalarL2 U f) (hg : MemVectorL2 U g)
    {u : H10Function U}
    (hu : ∀ φ : H10Function U,
      ∫ x in U, vecDot (matVecMul (a x) (u.toH1Function.grad x)) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume =
        (∫ x in U, f x * φ.toH1Function.toFun x ∂MeasureTheory.volume) +
          ∫ x in U, vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume)
    (w : H10HilbertSpace U) :
    coeffBilin hEll (H10HilbertSpace.ofH10Function u) w = forcingFunctional hf hg w := by
  rcases H10HilbertSpace.exists_h10Function hUo w with ⟨φ, hv, hgr⟩
  rw [← H10HilbertSpace.ofH10Function_eq hv hgr, coeffBilin_ofH10Function,
    forcingFunctional_ofH10Function]
  exact hu φ

/-- **Uniqueness** of the zero-trace weak solution (as an element of `L²` together with its
weak gradient). -/
theorem h10_weak_solution_unique [NeZero d] {lam Lam : ℝ} {a : CoeffField d}
    {f : Vec d → ℝ} {g : Vec d → Vec d}
    (hUo : IsOpen U) (hUb : IsBoundedDomain U) (hne : U.Nonempty)
    (hEll : IsEllipticFieldOn lam Lam U a) (hf : MemScalarL2 U f) (hg : MemVectorL2 U g)
    {u v : H10Function U}
    (hu : ∀ φ : H10Function U,
      ∫ x in U, vecDot (matVecMul (a x) (u.toH1Function.grad x)) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume =
        (∫ x in U, f x * φ.toH1Function.toFun x ∂MeasureTheory.volume) +
          ∫ x in U, vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume)
    (hv : ∀ φ : H10Function U,
      ∫ x in U, vecDot (matVecMul (a x) (v.toH1Function.grad x)) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume =
        (∫ x in U, f x * φ.toH1Function.toFun x ∂MeasureTheory.volume) +
          ∫ x in U, vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume) :
    u.toH1Function.toScalarL2 = v.toH1Function.toScalarL2 ∧
      u.toH1Function.gradToHilbertVectorL2 = v.toH1Function.gradToHilbertVectorL2 := by
  have hB := isCoercive_coeffBilin hUo hUb hne hEll
  set D : H10HilbertSpace U :=
    H10HilbertSpace.ofH10Function u - H10HilbertSpace.ofH10Function v with hD
  have hDw : ∀ w, coeffBilin hEll D w = 0 := fun w => by
    rw [hD, map_sub, sub_apply,
      coeffBilin_eq_forcing_of_weak hUo hEll hf hg hu,
      coeffBilin_eq_forcing_of_weak hUo hEll hf hg hv, sub_self]
  rcases hB with ⟨c, hc, hcoer⟩
  have h0 := hcoer D
  rw [hDw D] at h0
  have hDz : D = 0 := by
    have : ‖D‖ * ‖D‖ ≤ 0 := by
      by_contra hcon
      have hpos : 0 < ‖D‖ * ‖D‖ := lt_of_not_ge hcon
      nlinarith only [h0, hc, hpos, mul_pos hc hpos]
    have : ‖D‖ = 0 := by nlinarith only [this, norm_nonneg D]
    exact norm_eq_zero.mp this
  have hEq : H10HilbertSpace.ofH10Function u = H10HilbertSpace.ofH10Function v := sub_eq_zero.mp (hD ▸ hDz)
  exact ⟨congrArg H10HilbertSpace.value hEq, congrArg H10HilbertSpace.gradient hEq⟩

/-- Poincaré inequality for `H¹₀(U)` functions, in terms of the `L²` norms of the value and of the
weak gradient. -/
theorem exists_h10_norm_le [NeZero d] (hUo : IsOpen U) (hUb : IsBoundedDomain U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : H10Function U,
      ‖u.toH1Function.toScalarL2‖ ≤ C * ‖u.toH1Function.gradToHilbertVectorL2‖ := by
  rcases H10HilbertSpace.exists_norm_value_le hUo hUb with ⟨C, hC, h⟩
  exact ⟨C, hC, fun u => h (H10HilbertSpace.ofH10Function u)⟩

/-- Energy bound for a weak solution, given a Poincaré constant `C`. -/
theorem h10_energy_bound [NeZero d] {lam Lam : ℝ} {a : CoeffField d}
    {f : Vec d → ℝ} {g : Vec d → Vec d} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ u : H10Function U,
      ‖u.toH1Function.toScalarL2‖ ≤ C * ‖u.toH1Function.gradToHilbertVectorL2‖)
    (hUo : IsOpen U) (hEll : IsEllipticFieldOn lam Lam U a)
    (hf : MemScalarL2 U f) (hg : MemVectorL2 U g) {u : H10Function U}
    (hu : ∀ φ : H10Function U,
      ∫ x in U, vecDot (matVecMul (a x) (u.toH1Function.grad x)) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume =
        (∫ x in U, f x * φ.toH1Function.toFun x ∂MeasureTheory.volume) +
          ∫ x in U, vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume)
    :
    lam * ‖u.toH1Function.gradToHilbertVectorL2‖ ≤
      ‖toHilbertVectorL2OfVecField hg‖ + C * ‖toScalarL2 hf‖ := by
  set x : ℝ := ‖u.toH1Function.gradToHilbertVectorL2‖ with hx
  have hx0 : 0 ≤ x := norm_nonneg _
  have hK : 0 ≤ ‖toHilbertVectorL2OfVecField hg‖ + C * ‖toScalarL2 hf‖ := by positivity
  have h1 := coeffOperator_coercive hEll u.toH1Function.gradToHilbertVectorL2
  have h2 := coeffBilin_eq_forcing_of_weak hUo hEll hf hg hu (H10HilbertSpace.ofH10Function u)
  rw [coeffBilin_apply, forcingFunctional_apply, H10HilbertSpace.value_ofH10Function,
    H10HilbertSpace.gradient_ofH10Function] at h2
  have h3 : inner ℝ (toScalarL2 hf) u.toH1Function.toScalarL2 ≤
      ‖toScalarL2 hf‖ * (C * x) :=
    (real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (hC u) (norm_nonneg _))
  have h4 : inner ℝ (toHilbertVectorL2OfVecField hg) u.toH1Function.gradToHilbertVectorL2 ≤
      ‖toHilbertVectorL2OfVecField hg‖ * x := real_inner_le_norm _ _
  have h5 : lam * x ^ 2 ≤ (‖toHilbertVectorL2OfVecField hg‖ + C * ‖toScalarL2 hf‖) * x := by
    nlinarith only [h1, h2, h3, h4]
  by_cases hx00 : x = 0
  · rw [hx00, mul_zero]; exact hK
  · have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx00)
    have : lam * x * x ≤ (‖toHilbertVectorL2OfVecField hg‖ + C * ‖toScalarL2 hf‖) * x := by
      nlinarith only [h5]
    exact le_of_mul_le_mul_right this hxpos

/-- The weak zero-trace Dirichlet problem `-∇·(a∇u) = f + ∇·g` in `U`: `u ∈ H¹₀(U)` and
`∫_U ∇φ·a∇u = ∫_U f φ + ∫_U g·∇φ` for every `φ ∈ H¹₀(U)`. -/
def IsH10WeakSolution (a : CoeffField d) (U : Set (Vec d)) (f : Vec d → ℝ)
    (g : Vec d → Vec d) (u : H10Function U) : Prop :=
  ∀ φ : H10Function U,
    ∫ x in U, vecDot (matVecMul (a x) (u.toH1Function.grad x)) (φ.toH1Function.grad x)
        ∂MeasureTheory.volume =
      (∫ x in U, f x * φ.toH1Function.toFun x ∂MeasureTheory.volume) +
        ∫ x in U, vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume

/-- **Lax–Milgram well-posedness of the `H¹₀` Dirichlet problem** on a bounded open set, for
bounded coercive (not necessarily symmetric) coefficients: existence, uniqueness (of the
`L²` classes of the value and of the weak gradient) and the energy bound, with a constant `C`
depending only on `U` (the Poincaré constant). -/
theorem h10_dirichlet_wellPosed [NeZero d] (hUo : IsOpen U) (hUb : IsBoundedDomain U)
    (hne : U.Nonempty) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {lam Lam : ℝ} {a : CoeffField d}
      (_ : IsEllipticFieldOn lam Lam U a) {f : Vec d → ℝ} {g : Vec d → Vec d}
      (hf : MemScalarL2 U f) (hg : MemVectorL2 U g),
      (∃ u : H10Function U, IsH10WeakSolution a U f g u) ∧
      (∀ u v : H10Function U, IsH10WeakSolution a U f g u → IsH10WeakSolution a U f g v →
        u.toH1Function.toScalarL2 = v.toH1Function.toScalarL2 ∧
          u.toH1Function.gradToHilbertVectorL2 = v.toH1Function.gradToHilbertVectorL2) ∧
      (∀ u : H10Function U, IsH10WeakSolution a U f g u →
        lam * ‖u.toH1Function.gradToHilbertVectorL2‖ ≤
          ‖toHilbertVectorL2OfVecField hg‖ + C * ‖toScalarL2 hf‖) := by
  rcases exists_h10_norm_le hUo hUb with ⟨C, hC0, hC⟩
  refine ⟨C, hC0, ?_⟩
  intro lam Lam a hEll f g hf hg
  refine ⟨?_, fun u v hu hv => ?_, fun u hu => ?_⟩
  · exact exists_h10_weak_solution hUo hUb hne hEll hf hg
  · exact h10_weak_solution_unique hUo hUb hne hEll hf hg hu hv
  · exact h10_energy_bound hC0 hC hUo hEll hf hg hu

/-! ### Witness: the unit Euclidean ball with identity coefficients -/

theorem isEllipticMatrix_one : IsEllipticMatrix (d := d) 1 1 (1 : Mat d) := by
  have hmv : ∀ ξ : Vec d, matVecMul (1 : Mat d) ξ = ξ := fun ξ => by
    funext i
    simp [matVecMul, Matrix.one_apply]
  refine ⟨one_pos, le_refl _, fun ξ => ?_, fun ξ => ?_⟩
  · rw [hmv]
    simp [vecNormSq]
  · rw [Matrix.inv_eq_right_inv (Matrix.mul_one (1 : Mat d)), hmv]
    simp [vecNormSq]

theorem isEllipticFieldOn_one_euclidBall :
    IsEllipticFieldOn (d := d) 1 1 (Section6.euclidBall 1) (fun _ => (1 : Mat d)) := by
  classical
  refine ⟨?_, fun x _ => isEllipticMatrix_one⟩
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  exact Measurable.ite (Section6.measurableSet_euclidBall 1) measurable_const measurable_const

theorem isBoundedDomain_euclidBall {r : ℝ} (hr : 0 < r) :
    IsBoundedDomain (Section6.euclidBall (d := d) r) :=
  (Metric.isBounded_ball.subset (Section6.euclidBall_subset_ball hr)).isBoundedDomain

end SuperdiffusionCLT.Section7
