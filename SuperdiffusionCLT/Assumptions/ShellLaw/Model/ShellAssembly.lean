/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellField.SequenceLaw
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Scalar `C^2` fields and their operations

The scalar carrier `ScalarC2Field d` mirrors the shell carrier: a continuous value,
a continuous first derivative and a continuous second derivative, with exact
derivative compatibility. Its topology is the compact-open topology on the triple
and its measurable space is the Borel one. The operations are precomposition with a
continuous linear map of `Vec d` and multiplication by a constant; each is continuous.
-/

@[expose] public section

namespace SuperdiffusionCLT.Assumptions.ShellLaw.Model

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions

noncomputable section

/-- The ambient compact-open triple of the scalar carrier. -/
abbrev ScalarAmbient (d : ℕ) :=
  C(Vec d, ℝ) × (C(Vec d, Vec d →L[ℝ] ℝ) × C(Vec d, Vec d →L[ℝ] (Vec d →L[ℝ] ℝ)))

/-- A scalar `C^2` field with its stored first and second derivatives. -/
def ScalarC2Field (d : ℕ) :=
  { p : ScalarAmbient d //
    (∀ x, HasFDerivAt p.1 (p.2.1 x) x) ∧ ∀ x, HasFDerivAt p.2.1 (p.2.2 x) x }

instance (d : ℕ) : TopologicalSpace (ScalarC2Field d) :=
  inferInstanceAs (TopologicalSpace
    { p : ScalarAmbient d //
      (∀ x, HasFDerivAt p.1 (p.2.1 x) x) ∧ ∀ x, HasFDerivAt p.2.1 (p.2.2 x) x })

instance (d : ℕ) : SecondCountableTopology (ScalarC2Field d) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology

instance (d : ℕ) : MeasurableSpace (ScalarC2Field d) := borel _

instance (d : ℕ) : BorelSpace (ScalarC2Field d) := ⟨rfl⟩

namespace ScalarC2Field

variable {d : ℕ}

instance : CoeFun (ScalarC2Field d) (fun _ ↦ Vec d → ℝ) :=
  ⟨fun f ↦ f.1.1⟩

/-- The stored first derivative. -/
def deriv (f : ScalarC2Field d) : C(Vec d, Vec d →L[ℝ] ℝ) := f.1.2.1

/-- The stored second derivative. -/
def secondDeriv (f : ScalarC2Field d) :
    C(Vec d, Vec d →L[ℝ] (Vec d →L[ℝ] ℝ)) := f.1.2.2

theorem hasFDerivAt (f : ScalarC2Field d) (x : Vec d) :
    HasFDerivAt f (deriv f x) x :=
  f.2.1 x

theorem deriv_hasFDerivAt (f : ScalarC2Field d) (x : Vec d) :
    HasFDerivAt (deriv f) (secondDeriv f x) x :=
  f.2.2 x

theorem continuous_val_fst :
    Continuous (fun f : ScalarC2Field d ↦ f.1.1) :=
  continuous_subtype_val.fst

theorem continuous_val_snd_fst :
    Continuous (fun f : ScalarC2Field d ↦ f.1.2.1) :=
  continuous_subtype_val.snd.fst

theorem continuous_val_snd_snd :
    Continuous (fun f : ScalarC2Field d ↦ f.1.2.2) :=
  continuous_subtype_val.snd.snd

/-- Evaluation of the value at a point is continuous. -/
theorem continuous_eval (x : Vec d) :
    Continuous (fun f : ScalarC2Field d ↦ f x) :=
  (continuous_eval_const x).comp continuous_val_fst

/-- Evaluation of the first derivative at a point is continuous. -/
theorem continuous_eval_deriv (x : Vec d) :
    Continuous (fun f : ScalarC2Field d ↦ deriv f x) :=
  (continuous_eval_const x).comp continuous_val_snd_fst

/-- Evaluation of the second derivative at a point is continuous. -/
theorem continuous_eval_secondDeriv (x : Vec d) :
    Continuous (fun f : ScalarC2Field d ↦ secondDeriv f x) :=
  (continuous_eval_const x).comp continuous_val_snd_snd

theorem measurable_eval (x : Vec d) :
    Measurable (fun f : ScalarC2Field d ↦ f x) :=
  (continuous_eval x).measurable

/-- The entries of the first derivative along a direction are measurable. -/
theorem measurable_eval_deriv (x v : Vec d) :
    Measurable (fun f : ScalarC2Field d ↦ deriv f x v) :=
  ((ContinuousLinearMap.apply ℝ ℝ v).continuous.comp (continuous_eval_deriv x)).measurable

/-- The entries of the second derivative along two directions are measurable. -/
theorem measurable_eval_secondDeriv (x v w : Vec d) :
    Measurable (fun f : ScalarC2Field d ↦ secondDeriv f x v w) :=
  (((ContinuousLinearMap.apply ℝ ℝ w).continuous.comp
    ((ContinuousLinearMap.apply ℝ (Vec d →L[ℝ] ℝ) v).continuous.comp
      (continuous_eval_secondDeriv x)))).measurable

/-- Values determine the scalar field, including both stored derivatives. -/
@[ext]
theorem ext {f g : ScalarC2Field d} (h : ∀ x, f x = g x) : f = g := by
  have hval : f.1.1 = g.1.1 := ContinuousMap.ext h
  have hfirst : f.1.2.1 = g.1.2.1 := by
    apply ContinuousMap.ext
    intro x
    symm
    refine (g.hasFDerivAt x).unique ?_
    simpa only [hval, deriv] using f.hasFDerivAt x
  have hsecond : f.1.2.2 = g.1.2.2 := by
    apply ContinuousMap.ext
    intro x
    symm
    refine (g.deriv_hasFDerivAt x).unique ?_
    simpa only [deriv, secondDeriv, hfirst] using f.deriv_hasFDerivAt x
  apply Subtype.ext
  exact Prod.ext hval (Prod.ext hfirst hsecond)

/-! ## Multiplication by a constant -/

/-- Multiplication by a constant as a continuous self-map of a real topological module. -/
def nv_smulMap (E : Type*) [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
    [ContinuousConstSMul ℝ E] (c : ℝ) : C(E, E) :=
  ⟨fun t ↦ c • t, continuous_id.const_smul c⟩

def smulAmbient (c : ℝ) : ScalarAmbient d → ScalarAmbient d := fun p ↦
  ((nv_smulMap ℝ c).comp p.1,
    ((nv_smulMap (Vec d →L[ℝ] ℝ) c).comp p.2.1,
      (nv_smulMap (Vec d →L[ℝ] (Vec d →L[ℝ] ℝ)) c).comp p.2.2))

private theorem continuous_smulAmbient (c : ℝ) :
    Continuous (smulAmbient (d := d) c) :=
  ((ContinuousMap.continuous_postcomp _).comp continuous_fst).prodMk
    (((ContinuousMap.continuous_postcomp _).comp continuous_snd.fst).prodMk
      ((ContinuousMap.continuous_postcomp _).comp continuous_snd.snd))

/-- Multiplication of a scalar field by a constant. -/
def smulConst (c : ℝ) (f : ScalarC2Field d) : ScalarC2Field d :=
  ⟨smulAmbient c f.1, by
    refine ⟨?_, ?_⟩
    · intro x
      exact (f.hasFDerivAt x).const_smul c
    · intro x
      exact (f.deriv_hasFDerivAt x).const_smul c⟩

@[simp]
theorem smulConst_apply (c : ℝ) (f : ScalarC2Field d) (x : Vec d) :
    smulConst c f x = c * f x :=
  rfl

theorem continuous_smulConst (c : ℝ) : Continuous (smulConst (d := d) c) :=
  Continuous.subtype_mk
    ((continuous_smulAmbient c).comp continuous_subtype_val)
    (fun f ↦ (smulConst c f).2)

theorem measurable_smulConst (c : ℝ) : Measurable (smulConst (d := d) c) :=
  (continuous_smulConst c).measurable

/-! ## Precomposition with a continuous linear map -/

/-- Precomposition of first derivatives with `L`. -/
def nv_precompFirst (L : Vec d →L[ℝ] Vec d) :
    (Vec d →L[ℝ] ℝ) →L[ℝ] (Vec d →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ (Vec d) (Vec d) ℝ).flip L

@[simp]
theorem nv_precompFirst_apply (L : Vec d →L[ℝ] Vec d) (D : Vec d →L[ℝ] ℝ) :
    nv_precompFirst L D = D.comp L :=
  rfl

/-- Precomposition of second derivatives with `L` in both arguments. -/
def nv_precompSecond (L : Vec d →L[ℝ] Vec d) :
    (Vec d →L[ℝ] (Vec d →L[ℝ] ℝ)) →L[ℝ] (Vec d →L[ℝ] (Vec d →L[ℝ] ℝ)) :=
  (ContinuousLinearMap.compL ℝ (Vec d) (Vec d →L[ℝ] ℝ) (Vec d →L[ℝ] ℝ)
      (nv_precompFirst L)).comp
    ((ContinuousLinearMap.compL ℝ (Vec d) (Vec d) (Vec d →L[ℝ] ℝ)).flip L)

@[simp]
theorem nv_precompSecond_apply (L : Vec d →L[ℝ] Vec d)
    (H : Vec d →L[ℝ] (Vec d →L[ℝ] ℝ)) (v : Vec d) :
    nv_precompSecond L H v = (H (L v)).comp L :=
  rfl

def precompAmbient (L : Vec d →L[ℝ] Vec d) :
    ScalarAmbient d → ScalarAmbient d := fun p ↦
  (p.1.comp ⟨L, L.continuous⟩,
    (((⟨nv_precompFirst L, (nv_precompFirst L).continuous⟩ :
        C(Vec d →L[ℝ] ℝ, Vec d →L[ℝ] ℝ))).comp (p.2.1.comp ⟨L, L.continuous⟩),
      ((⟨nv_precompSecond L, (nv_precompSecond L).continuous⟩ :
        C(Vec d →L[ℝ] (Vec d →L[ℝ] ℝ), Vec d →L[ℝ] (Vec d →L[ℝ] ℝ))).comp
          (p.2.2.comp ⟨L, L.continuous⟩))))

private theorem continuous_precompAmbient (L : Vec d →L[ℝ] Vec d) :
    Continuous (precompAmbient L) :=
  ((ContinuousMap.continuous_precomp _).comp continuous_fst).prodMk
    (((ContinuousMap.continuous_postcomp _).comp
      ((ContinuousMap.continuous_precomp _).comp continuous_snd.fst)).prodMk
        ((ContinuousMap.continuous_postcomp _).comp
          ((ContinuousMap.continuous_precomp _).comp continuous_snd.snd)))

/-- Precomposition `f ↦ f ∘ L` by a continuous linear map, with the chain-rule
derivatives. -/
def precomp (L : Vec d →L[ℝ] Vec d) (f : ScalarC2Field d) : ScalarC2Field d :=
  ⟨precompAmbient L f.1, by
    refine ⟨?_, ?_⟩
    · intro x
      exact (f.hasFDerivAt (L x)).comp x L.hasFDerivAt
    · intro x
      exact (nv_precompFirst L).hasFDerivAt.comp x
        ((f.deriv_hasFDerivAt (L x)).comp x L.hasFDerivAt)⟩

@[simp]
theorem precomp_apply (L : Vec d →L[ℝ] Vec d) (f : ScalarC2Field d) (x : Vec d) :
    precomp L f x = f (L x) :=
  rfl

theorem continuous_precomp (L : Vec d →L[ℝ] Vec d) :
    Continuous (precomp (d := d) L) :=
  Continuous.subtype_mk
    ((continuous_precompAmbient L).comp continuous_subtype_val)
    (fun f ↦ (precomp L f).2)

theorem measurable_precomp (L : Vec d →L[ℝ] Vec d) :
    Measurable (precomp (d := d) L) :=
  (continuous_precomp L).measurable

/-! ## Scalar fields from `C^2` functions -/

/-- The scalar field of a `C^2` function, with the Fréchet derivatives as stored data. -/
def ofContDiff (f : Vec d → ℝ) (hf : ContDiff ℝ 2 f) : ScalarC2Field d :=
  ⟨(⟨f, hf.continuous⟩,
    (⟨fderiv ℝ f, hf.continuous_fderiv (by norm_num)⟩,
      ⟨fderiv ℝ (fderiv ℝ f),
        (hf.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)⟩)), by
    refine ⟨?_, ?_⟩
    · intro x
      exact (hf.differentiable (by norm_num) x).hasFDerivAt
    · intro x
      exact (((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x).hasFDerivAt⟩

@[simp]
theorem ofContDiff_apply (f : Vec d → ℝ) (hf : ContDiff ℝ 2 f) (x : Vec d) :
    ofContDiff f hf x = f x :=
  rfl

@[simp]
theorem deriv_ofContDiff (f : Vec d → ℝ) (hf : ContDiff ℝ 2 f) (x : Vec d) :
    deriv (ofContDiff f hf) x = fderiv ℝ f x :=
  rfl

@[simp]
theorem secondDeriv_ofContDiff (f : Vec d → ℝ) (hf : ContDiff ℝ 2 f) (x : Vec d) :
    secondDeriv (ofContDiff f hf) x = fderiv ℝ (fderiv ℝ f) x :=
  rfl

end ScalarC2Field

end

end SuperdiffusionCLT.Assumptions.ShellLaw.Model
