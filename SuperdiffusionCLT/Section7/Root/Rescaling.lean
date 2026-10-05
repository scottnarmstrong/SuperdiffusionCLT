/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Change.DilationB
public import SuperdiffusionCLT.Section6.Prereq.FullField

/-!
# Rescaling of the Dirichlet problem

The change of variables `y = x / ε` of the first root: the Dirichlet problem for
`S⁻¹ A(·/ε)` on `U` with right-hand side `f` becomes the Dirichlet problem for `A` on `ε⁻¹ • U`
with right-hand side `S ε² f(ε ·)` and datum `g(ε ·)`.

The two carriers below are copies of the statement carriers of the first root, under
`s12_`-prefixed names, to be replaced by the root carrier.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization MeasureTheory
open scoped ENNReal Pointwise

variable {d : ℕ}

/-- `u ∈ H¹(U)` solves `-∇·(a∇u) = f` in `U` with `u = g` on `∂U`
(to be replaced by the root carrier). -/
def s12_IsDirichletSolution (a : CoeffField d) (U : Set (Vec d)) (f : Vec d → ℝ)
    (g u : H1Function U) : Prop :=
  IsWeakSolutionOn a U u f (fun _ => 0) ∧ MemH10 U (fun x => u.toFun x - g.toFun x)

/-- The `H^{-1}(U)` seminorm of a vector field (to be replaced by the root carrier). -/
noncomputable def s12_hMinusOneVec (U : Set (Vec d)) (F : Vec d → Vec d) : ℝ≥0∞ :=
  ∑ i : Fin d, wMinusOneBar U 2 (fun x => F x i)

/-- Transfer of a weak solution along pointwise equal data. -/
theorem s12_transfer {U : Set (Vec d)} {a a' : CoeffField d} {u : H1Function U}
    {f f' : Vec d → ℝ} {g g' : Vec d → Vec d} (ha : ∀ x, a x = a' x) (hf : ∀ x, f x = f' x)
    (hg : ∀ x, g x = g' x) (hu : IsWeakSolutionOn a U u f g) : IsWeakSolutionOn a' U u f' g' := by
  have ha' : a = a' := funext ha
  have hf' : f = f' := funext hf
  have hg' : g = g' := funext hg
  subst ha' hf' hg'
  exact hu

/-- Dilation of membership in `H¹₀`. -/
theorem s12_memH10_dilate {U : Set (Vec d)} {s : ℝ} (hs : s ≠ 0) {h : Vec d → ℝ}
    (hh : MemH10 U h) : MemH10 (s⁻¹ • U) (fun y => h (s • y)) := by
  obtain ⟨v, hv⟩ := hh
  refine ⟨v.dilateArg hs, ?_⟩
  funext y
  rw [H10Function.dilateArg_toH1Function, H1Function.dilateArg_toFun, hv]

/-- **Rescaling of the Dirichlet problem.** -/
theorem s12_dirichlet_dilate {U : Set (Vec d)} {A : CoeffField d} {S ε : ℝ} (hS : S ≠ 0)
    (hε : ε ≠ 0) {f : Vec d → ℝ} {g u : H1Function U}
    (h : s12_IsDirichletSolution (fun x => S⁻¹ • A (ε⁻¹ • x)) U f g u) :
    s12_IsDirichletSolution A (ε⁻¹ • U) (fun y => S * ε ^ 2 * f (ε • y))
      (g.dilateArg hε) (u.dilateArg hε) := by
  refine ⟨?_, ?_⟩
  · have h1 := (IsWeakSolutionOn.dilate hε h.1).smul S
    refine s12_transfer (fun y => ?_) (fun y => ?_) (fun y => ?_) h1
    · simp only [smul_smul, inv_smul_smul₀ hε]
      rw [mul_inv_cancel₀ hS, one_smul]
    · ring
    · simp
  · have h2 := s12_memH10_dilate hε h.2
    convert h2 using 1
    funext y
    rw [H1Function.dilateArg_toFun, H1Function.dilateArg_toFun]

/-- The `L^∞` norm on the dilated set. -/
theorem s12_eLpNorm_top_dilate {E : Type*} [NormedAddCommGroup E] {ε : ℝ} (hε : ε ≠ 0)
    (U : Set (Vec d)) (F : Vec d → E) :
    eLpNorm (fun y => F (ε • y)) ⊤ (volume.restrict (ε⁻¹ • U)) =
      eLpNorm F ⊤ (volume.restrict U) := by
  have h := (a18_measurableEmbedding (d := d) hε).eLpNorm_map_measure (g := F) (p := ⊤)
    (μ := volume.restrict (ε⁻¹ • U))
  have hc : ENNReal.ofReal |(ε ^ d)⁻¹| ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact abs_pos.mpr (inv_ne_zero (pow_ne_zero d hε))
  rw [a18_map_restrict hε U, eLpNorm_smul_measure_of_ne_zero hc] at h
  have h0 : (1 / (⊤ : ℝ≥0∞)).toReal = 0 := by simp
  rw [h0, ENNReal.rpow_zero, one_smul] at h
  exact h.symm

/-- Averages over a dilated set. -/
theorem s12_setAverage_dilate {ε : ℝ} (hε : ε ≠ 0) (U : Set (Vec d)) (κ : Vec d → ℝ) :
    ⨍ y in ε⁻¹ • U, κ y = ⨍ x in U, κ (ε⁻¹ • x) := by
  have h := a18_setIntegral_dilate hε U (fun x => κ (ε⁻¹ • x))
  simp only [inv_smul_smul₀ hε] at h
  have hv := a18_toReal_volume hε U
  have hc : |(ε ^ d)⁻¹| ≠ 0 := abs_ne_zero.mpr (inv_ne_zero (pow_ne_zero d hε))
  rw [setAverage_eq, setAverage_eq, Measure.real, Measure.real, hv, h, smul_eq_mul, smul_eq_mul,
    mul_inv]
  have e : (|(ε ^ d)⁻¹|)⁻¹ * ((volume U).toReal)⁻¹ * (|(ε ^ d)⁻¹| * ∫ x in U, κ (ε⁻¹ • x)) =
      (|(ε ^ d)⁻¹|)⁻¹ * |(ε ^ d)⁻¹| * (((volume U).toReal)⁻¹ * ∫ x in U, κ (ε⁻¹ • x)) := by ring
  rw [e, inv_mul_cancel₀ hc, one_mul]

/-- The rescaled coefficient field `ν Id + (k - k(0))(·/ε)` (to be replaced by the root
carrier). -/
noncomputable def s12_epField (nu : ℝ) (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
    (ε : ℝ) : CoeffField d :=
  fun x => SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega (ε⁻¹ • x)

/-- The same field centered by the entrywise average of `k^ε` over `U` (to be replaced by the
root carrier). -/
noncomputable def s12_epFieldCentered (nu : ℝ)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (ε : ℝ) (U : Set (Vec d)) :
    CoeffField d :=
  fun x => s12_epField nu omega ε x -
    Matrix.of fun i j =>
      ⨍ y in U, SuperdiffusionCLT.Section6.fullStreamRecentered omega (ε⁻¹ • y) i j

/-- The centered field at `ε y` is the field `ν Id + k` centered by the average over the
dilated set. -/
theorem s12_epFieldCentered_dilate (nu : ℝ)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) {ε : ℝ} (hε : ε ≠ 0)
    (U : Set (Vec d)) (y : Vec d) :
    s12_epFieldCentered nu omega ε U (ε • y) =
      SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega y -
        Matrix.of fun i j =>
          ⨍ w in ε⁻¹ • U, SuperdiffusionCLT.Section6.fullStreamRecentered omega w i j := by
  unfold s12_epFieldCentered s12_epField
  simp only [inv_smul_smul₀ hε]
  congr 1
  ext i j
  simp only [Matrix.of_apply]
  rw [s12_setAverage_dilate hε U (fun w =>
    SuperdiffusionCLT.Section6.fullStreamRecentered omega w i j)]

/-- Homogeneity of the normalized dual seminorm. -/
theorem s12_wMinusOneBar_const_mul (V : Set (Vec d)) (p : ℝ≥0∞) (c : ℝ) (h : Vec d → ℝ) :
    wMinusOneBar V p (fun x => c * h x) = ENNReal.ofReal |c| * wMinusOneBar V p h := by
  unfold wMinusOneBar
  rw [ENNReal.mul_iSup]
  refine iSup_congr fun ψ => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_congr fun _ => ?_
  have hI : ∫ x in V, c * h x * ψ.toH1Function.toFun x =
      c * ∫ x in V, h x * ψ.toH1Function.toFun x := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  rw [hI, ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  have e : ((volume V).toReal)⁻¹ * (c * ∫ x in V, h x * ψ.toH1Function.toFun x) =
      c * (((volume V).toReal)⁻¹ * ∫ x in V, h x * ψ.toH1Function.toFun x) := by ring
  rw [e, abs_mul]

/-- **The `H^{-1}` seminorm of a gradient-scaled field under dilation.** If
`G(y) = ε F(ε y)` then the normalized seminorm of `G` on `ε⁻¹ • U` is that of `F` on `U`. -/
theorem s12_hMinusOneVec_dilate_grad {ε : ℝ} (hε : 0 < ε) (U : Set (Vec d))
    (F G : Vec d → Vec d) (hG : ∀ y, G y = ε • F (ε • y)) :
    s12_hMinusOneVec (ε⁻¹ • U) G = s12_hMinusOneVec U F := by
  unfold s12_hMinusOneVec
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : (fun y => G y i) = fun y => ε * (fun x => F x i) (ε • y) := by
    funext y
    rw [hG y]
    simp
  have h2 := wMinusOneBar_dilate hε U 2 (fun x => F x i)
  rw [h1, s12_wMinusOneBar_const_mul, h2, ← mul_assoc,
    ← ENNReal.ofReal_mul (abs_nonneg _), abs_of_pos hε, mul_inv_cancel₀ hε.ne']
  simp

/-- Satisfiability: the zero function solves the Dirichlet problem with zero datum for every
coefficient field, and the rescaling applies to it. -/
example (U : Set (Vec d)) (A : CoeffField d) {S ε : ℝ} (hS : S ≠ 0) (hε : ε ≠ 0) :
    s12_IsDirichletSolution A (ε⁻¹ • U) (fun y => S * ε ^ 2 * (fun _ : Vec d => (0 : ℝ)) (ε • y))
      ((0 : H10Function U).toH1Function.dilateArg hε)
      ((0 : H10Function U).toH1Function.dilateArg hε) := by
  have h0 : ∀ x, (0 : H10Function U).toH1Function.grad x = 0 := fun _ => rfl
  refine s12_dirichlet_dilate (U := U) (A := A) (S := S) (ε := ε) hS hε
    (f := fun _ => 0) ?_
  refine ⟨?_, ?_⟩
  · intro φ
    simp [vecDot, matVecMul, h0]
  · have h : (fun x => (0 : H10Function U).toH1Function.toFun x -
        (0 : H10Function U).toH1Function.toFun x) = (0 : Vec d → ℝ) := by
      funext x
      simp
    rw [h]
    exact memH10_zero

end SuperdiffusionCLT.Section7
