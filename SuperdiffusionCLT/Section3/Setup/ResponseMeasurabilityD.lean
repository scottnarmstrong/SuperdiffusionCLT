/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.ResponseMeasurabilityC
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2Measurability
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1Inputs

/-!
# The response gradient class on a sub-`σ`-algebra, and the field half of the
measurability sentence

The measurability sentence of the paper reads the response flux
`R = (a_{L'} − a_ℓ) ∇w` against the `σ`-field `F_> = σ(j_r : r > ℓ)`.  The
proxy half and the coefficient half of that sentence are proved in the
module `RHSTerm2Measurability`; the field half needs a record of how the
Dirichlet response depends on the sample.

`ResponseMeasurabilityB` provides exactly that, through the `1`-Lipschitz
cube Dirichlet solution operator.  Every step of its proof is generic in the
`σ`-algebra of the sample, so this module re-runs it for an arbitrary
measurable parameter (`measurable_toHilbertVectorL2OfVecField_of_measurable`,
`measurable_gradToHilbertVectorL2_dirichletResponse_comp`) and reads the cube
mean of `R` as an inner product of `L²(cu_m)` classes
(`volumeAverageVec_matVecMul_eq_inner`).  The scale ordering
`ℓ < ℓ' < m < L'` of `ScalesOrdering` then puts both factors in `F_>`: the
coefficient difference is the shell sum over `(ℓ, L']` and the flux of the
Dirichlet problem is the shell sum over `(ℓ', L']`.

The two remaining measurability statements of the `l.RHS.term1` reduction are
reduced, not proved, and the docstrings of
`aemeasurable_ofReal_abs_volumeAverage_vecDot_grad_of_pairing` and
`aemeasurable_vecCubeH1ENorm_grad_of_hessian` say what each still needs.

## Main results

* `measurable_toHilbertVectorL2OfVecField_of_measurable`: a jointly measurable
  family of square-integrable fields has a measurable `L²` class map, for an
  arbitrary `σ`-algebra on the parameter.
* `measurable_gradToHilbertVectorL2_dirichletResponse_comp`: the gradient class
  of the canonical Dirichlet response, through an arbitrary measurable
  parameter.
* `volumeAverageVec_matVecMul_eq_inner`,
  `measurable_volumeAverageVec_matVecMul_grad_dirichletResponse_comp`: the cube
  mean of `A ∇w` as an inner product, and its measurability.
* `measurable_volumeAverageVec_matVecMul_coefficientCutoff_sub_grad_highShellSigma`:
  the field half of the measurability sentence.
* `aemeasurable_ofReal_abs_volumeAverage_vecDot_grad_of_pairing`:
  measurability of the second-step observable of `l.RHS.term1` from the
  `L²(cu_m)` class of the pairing field alone, with the response eliminated.
* `aemeasurable_vecCubeH1ENorm_grad_of_hessian`: measurability of the `H̲¹(cu_m)`
  observable of `l.RHS.term1` reduced to its Hessian half.  Weak Hessians are a.e.
  unique and see the function only through its weak-gradient class, so the Hessian
  half is a definite function of the sample.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Setup

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream

noncomputable section

variable {d : ℕ}

/-! ## `L²` classes of a jointly measurable family of fields -/

section ClassMeasurability

variable {alpha : Type*} [MeasurableSpace alpha]

/-- **A jointly measurable family of square-integrable fields has a measurable
class map.**  The `σ`-algebra of the parameter is arbitrary: the class space is
second countable, so the distance criterion against a countable dense sequence
applies, and both the norm and the inner products against a fixed class are set
integrals of jointly measurable integrands. -/
theorem measurable_toHilbertVectorL2OfVecField_of_measurable {U : Set (Vec d)}
    {G : alpha → Vec d → Vec d}
    (hG : Measurable fun q : alpha × Vec d => G q.1 q.2)
    (hmem : ∀ a : alpha, MemVectorL2 U (G a)) :
    Measurable fun a : alpha => toHilbertVectorL2OfVecField (hmem a) := by
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  refine measurable_of_measurable_norm_inner_denseRange
    (TopologicalSpace.denseSeq (HilbertVectorL2 U))
    (TopologicalSpace.denseRange_denseSeq _) ?_ ?_
  · have hnormeq : (fun a : alpha => ‖toHilbertVectorL2OfVecField (hmem a)‖) =
        fun a : alpha => Real.sqrt
          (∫ x in U, vecDot (G a x) (G a x) ∂MeasureTheory.volume) := by
      funext a
      exact norm_toHilbertVectorL2OfVecField_eq_sqrt (hmem a)
    rw [hnormeq]
    exact Real.continuous_sqrt.measurable.comp
      (measurable_setIntegral_vecDot_prod U hG hG)
  · intro n
    have hinnereq : (fun a : alpha => inner ℝ
        (TopologicalSpace.denseSeq (HilbertVectorL2 U) n)
        (toHilbertVectorL2OfVecField (hmem a))) =
        fun a : alpha => ∫ x in U,
          vecDot (hilbertClassField
              (TopologicalSpace.denseSeq (HilbertVectorL2 U) n) x)
            (G a x) ∂MeasureTheory.volume := by
      funext a
      have h0 : TopologicalSpace.denseSeq (HilbertVectorL2 U) n =
          toHilbertVectorL2OfVecField (memVectorL2_hilbertClassField
            (TopologicalSpace.denseSeq (HilbertVectorL2 U) n)) :=
        (toHilbertVectorL2OfVecField_hilbertClassField _).symm
      conv_lhs => rw [h0]
      exact inner_toHilbertVectorL2OfVecField_eq_integral _ _
    rw [hinnereq]
    exact measurable_setIntegral_vecDot_prod U
      ((measurable_hilbertClassField _).comp measurable_snd) hG

end ClassMeasurability

/-! ## The response gradient class through an arbitrary measurable parameter -/

section Parameter

variable {alpha : Type*} [mAlpha : MeasurableSpace alpha]

/-- A matrix-valued map with measurable entries gives a measurable vector-valued
map after multiplication by a fixed vector. -/
theorem measurable_matVecMul_of_entries {M : alpha → Mat d}
    (hM : ∀ i j : Fin d, Measurable fun a : alpha => M a i j) (v : Vec d) :
    Measurable fun a : alpha => matVecMul (M a) v := by
  refine Measurable.of_eval fun i => ?_
  exact Finset.measurable_sum _ fun j _ => (hM i j).mul_const (v j)

/-- A Caratheodory family is jointly measurable, for an arbitrary `σ`-algebra
on the parameter. -/
theorem measurable_prod_of_continuous_of_measurable {G : alpha → Vec d → Vec d}
    (hcont : ∀ a : alpha, Continuous (G a))
    (hmeas : ∀ x : Vec d, Measurable fun a : alpha => G a x) :
    Measurable fun q : alpha × Vec d => G q.1 q.2 := by
  have h : Measurable (Function.uncurry (fun (x : Vec d) (a : alpha) => G a x)) :=
    measurable_uncurry_of_continuous_of_measurable hcont hmeas
  have hcomp : (fun q : alpha × Vec d => G q.1 q.2) =
      (Function.uncurry (fun (x : Vec d) (a : alpha) => G a x)) ∘ Prod.swap := rfl
  rw [hcomp]
  exact h.comp measurable_swap

/-- **The flux class of `e.def.w` read through an arbitrary measurable
parameter.**  Only the pointwise measurability of the flux field in the
parameter is used, so the `σ`-algebra is arbitrary. -/
theorem measurable_toHilbertVectorL2OfVecField_dirichletRhsField_comp
    (F : alpha → ShellSeq d) (LPrime ellPrime m : ℕ) (p : Vec d)
    (hF : ∀ x : Vec d, Measurable fun a : alpha =>
      dirichletRhsField (F a) LPrime ellPrime p x) :
    Measurable fun a : alpha => toHilbertVectorL2OfVecField
      (memVectorL2_dirichletRhsField (F a) LPrime ellPrime m p) :=
  measurable_toHilbertVectorL2OfVecField_of_measurable
    (measurable_prod_of_continuous_of_measurable
      (fun a => continuous_dirichletRhsField (F a) LPrime ellPrime p) hF)
    (fun a => memVectorL2_dirichletRhsField (F a) LPrime ellPrime m p)

/-- **The gradient class of the canonical Dirichlet response read through an
arbitrary measurable parameter.**  The solution operator is continuous and the
flux class is measurable. -/
theorem measurable_gradToHilbertVectorL2_dirichletResponse_comp [NeZero d]
    (F : alpha → ShellSeq d) (LPrime ellPrime m : ℕ) (p : Vec d)
    (hF : ∀ x : Vec d, Measurable fun a : alpha =>
      dirichletRhsField (F a) LPrime ellPrime p x) :
    Measurable fun a : alpha =>
      (dirichletResponse (F a) LPrime ellPrime m p).toH1Function.gradToHilbertVectorL2 := by
  have hfun : (fun a : alpha =>
      (dirichletResponse (F a) LPrime ellPrime m p).toH1Function.gradToHilbertVectorL2) =
      fun a : alpha => cubeDirichletGradClass (originCube d (m : ℤ))
        (toHilbertVectorL2OfVecField
          (memVectorL2_dirichletRhsField (F a) LPrime ellPrime m p)) := by
    funext a
    exact gradToHilbertVectorL2_eq_cubeDirichletGradClass_of_isDirichletResponse (F a)
      (isDirichletResponse_dirichletResponse (F a) LPrime ellPrime m p)
  rw [hfun]
  exact (continuous_cubeDirichletGradClass (originCube d (m : ℤ))).measurable.comp
    (measurable_toHilbertVectorL2OfVecField_dirichletRhsField_comp F LPrime ellPrime m p hF)

end Parameter

/-! ## The cube mean of a matrix flux as an inner product -/

section CubeMean

/-- **The cube mean of `A g` on a sub-cube is an inner product of `L²(U)`
classes**: the `i`-th coordinate pairs the class of the `i`-th row of `A`,
cut off outside the sub-cube, against the class of `g`. -/
theorem volumeAverageVec_matVecMul_eq_inner {U V : Set (Vec d)} (hVU : V ⊆ U)
    (hV : MeasurableSet V) (A : Vec d → Mat d) {g : Vec d → Vec d}
    (hg : MemVectorL2 U g) (i : Fin d)
    (hK : MemVectorL2 U (Set.indicator V (fun y => (fun j => A y i j : Vec d)))) :
    volumeAverageVec V (fun y => matVecMul (A y) (g y)) i =
      (MeasureTheory.volume V).toReal⁻¹ *
        inner ℝ (toHilbertVectorL2OfVecField hK) (toHilbertVectorL2OfVecField hg) := by
  rw [inner_toHilbertVectorL2OfVecField_eq_integral]
  have hind : (fun y : Vec d =>
        vecDot (Set.indicator V (fun y => (fun j => A y i j : Vec d)) y) (g y)) =
      Set.indicator V (fun y : Vec d => vecDot (fun j => A y i j) (g y)) := by
    funext y
    by_cases hy : y ∈ V
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, vecDot_zero_left]
  show volumeAverage V (fun y : Vec d => matVecMul (A y) (g y) i) = _
  rw [volumeAverage]
  congr 1
  rw [hind, MeasureTheory.setIntegral_indicator hV,
    Set.inter_eq_self_of_subset_right hVU]
  rfl

end CubeMean

/-! ## The cube mean of the response flux, through an arbitrary parameter -/

section CanonicalCubeMean

variable {alpha : Type*} [mAlpha : MeasurableSpace alpha] [NeZero d]

/-- **The cube mean of `A ∇w` at the canonical Dirichlet response is measurable
in the parameter.**  The coefficient field is Caratheodory, so each cut-off row
is a measurable family of `L²(cu_m)` classes; the response gradient class is a
measurable family too; and the cube mean is their inner product. -/
theorem measurable_volumeAverageVec_matVecMul_grad_dirichletResponse_comp
    (F : alpha → ShellSeq d) (A : alpha → Vec d → Mat d)
    (hAcont : ∀ (a : alpha) (i j : Fin d), Continuous fun y : Vec d => A a y i j)
    (hAmeas : ∀ (y : Vec d) (i j : Fin d), Measurable fun a : alpha => A a y i j)
    (LPrime ellPrime m : ℕ) (p : Vec d)
    {V : Set (Vec d)} (hVU : V ⊆ openCubeSet (originCube d (m : ℤ)))
    (hV : MeasurableSet V)
    (hflux : ∀ x : Vec d, Measurable fun a : alpha =>
      dirichletRhsField (F a) LPrime ellPrime p x) :
    Measurable fun a : alpha => volumeAverageVec V
      (fun y => matVecMul (A a y)
        ((dirichletResponse (F a) LPrime ellPrime m p).toH1Function.grad y)) := by
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  refine Measurable.of_eval fun i => ?_
  have hrowcont : ∀ a : alpha,
      Continuous fun y : Vec d => (fun j => A a y i j : Vec d) :=
    fun a => continuous_pi fun j => hAcont a i j
  have hrowjoint : Measurable fun q : alpha × Vec d => (fun j => A q.1 q.2 i j : Vec d) :=
    measurable_prod_of_continuous_of_measurable hrowcont
      (fun x => Measurable.of_eval fun j => hAmeas x i j)
  have hKmem : ∀ a : alpha, MemVectorL2 (openCubeSet (originCube d (m : ℤ)))
      (Set.indicator V (fun y => (fun j => A a y i j : Vec d))) :=
    fun a => (memVectorL2_of_continuous (m : ℤ) (hrowcont a)).indicator hV
  have hKjoint : Measurable fun q : alpha × Vec d =>
      Set.indicator V (fun y => (fun j => A q.1 y i j : Vec d)) q.2 := by
    have hrw : (fun q : alpha × Vec d =>
        Set.indicator V (fun y => (fun j => A q.1 y i j : Vec d)) q.2) =
        Set.indicator (Prod.snd ⁻¹' V)
          (fun q : alpha × Vec d => (fun j => A q.1 q.2 i j : Vec d)) := by
      funext q
      by_cases hq : q.2 ∈ V
      · rw [Set.indicator_of_mem hq,
          Set.indicator_of_mem (show q ∈ Prod.snd ⁻¹' V from hq)]
      · rw [Set.indicator_of_notMem hq,
          Set.indicator_of_notMem (show q ∉ Prod.snd ⁻¹' V from hq)]
    rw [hrw]
    exact hrowjoint.indicator (measurable_snd hV)
  have hKclass : Measurable fun a : alpha => toHilbertVectorL2OfVecField (hKmem a) :=
    measurable_toHilbertVectorL2OfVecField_of_measurable hKjoint hKmem
  have hg : ∀ a : alpha, MemVectorL2 (openCubeSet (originCube d (m : ℤ)))
      (dirichletResponse (F a) LPrime ellPrime m p).toH1Function.grad :=
    fun a => (dirichletResponse (F a) LPrime ellPrime m p).toH1Function.grad_memVectorL2
  have hGclass : Measurable fun a : alpha => toHilbertVectorL2OfVecField (hg a) :=
    measurable_gradToHilbertVectorL2_dirichletResponse_comp F LPrime ellPrime m p hflux
  have hfun : (fun a : alpha => volumeAverageVec V
      (fun y => matVecMul (A a y)
        ((dirichletResponse (F a) LPrime ellPrime m p).toH1Function.grad y)) i) =
      fun a : alpha => (MeasureTheory.volume V).toReal⁻¹ *
        inner ℝ (toHilbertVectorL2OfVecField (hKmem a))
          (toHilbertVectorL2OfVecField (hg a)) := by
    funext a
    exact volumeAverageVec_matVecMul_eq_inner hVU hV (A a) (hg a) i (hKmem a)
  rw [hfun]
  exact (continuous_inner.measurable.comp (hKclass.prodMk hGclass)).const_mul _

end CanonicalCubeMean

/-! ## The field half of the measurability sentence of `l.RHS.term2` -/

section Obligation7

/-- The finite shell increment over `(n, L]` reads only the shells `r > ℓ`
whenever `ℓ ≤ n`. -/
theorem measurable_finiteShellIncrement_highShellSigma_of_le {ell n L : ℕ}
    (h : ell ≤ n) :
    Measurable[Terms.highShellSigma d ell]
      (fun omega : ShellSeq d => finiteShellIncrement omega n L) := by
  unfold finiteShellIncrement
  refine Finset.measurable_sum _ fun k hk => ?_
  exact SuperdiffusionCLT.Section3.HighContrast.measurable_shellReg_indexSigma
    (Set.mem_Ioi.mpr (lt_of_le_of_lt h (Finset.mem_Ioc.mp hk).1))

/-- Entrywise form of `measurable_finiteShellIncrement_highShellSigma_of_le`. -/
theorem measurable_finiteShellIncrement_apply_entry_highShellSigma {ell n L : ℕ}
    (h : ell ≤ n) (y : Vec d) (i j : Fin d) :
    Measurable[Terms.highShellSigma d ell]
      (fun omega : ShellSeq d => finiteShellIncrement omega n L y i j) :=
  (measurable_apply_entry y i j).comp
    (measurable_finiteShellIncrement_highShellSigma_of_le h)

/-- **The cutoff-difference coefficient field reads only the shells `r > ℓ`.** -/
theorem measurable_coefficientCutoff_sub_entry_highShellSigma (nu : ℝ) {ell L : ℕ}
    (h : ell ≤ L) (y : Vec d) (i j : Fin d) :
    Measurable[Terms.highShellSigma d ell] (fun omega : ShellSeq d =>
      ((coefficientCutoff nu omega L).toCoeffField y -
        (coefficientCutoff nu omega ell).toCoeffField y) i j) := by
  have hfun : (fun omega : ShellSeq d =>
      ((coefficientCutoff nu omega L).toCoeffField y -
        (coefficientCutoff nu omega ell).toCoeffField y) i j) =
      fun omega : ShellSeq d => finiteShellIncrement omega ell L y i j := by
    funext omega
    rw [Terms.coefficientCutoff_toCoeffField_sub_eq_finiteShellIncrement nu omega h y]
  rw [hfun]
  exact measurable_finiteShellIncrement_apply_entry_highShellSigma le_rfl y i j

/-- **The flux field of `e.def.w` reads only the shells `r > ℓ`**, because it is
the shell increment over `(ℓ', L']` and `ℓ ≤ ℓ'`. -/
theorem measurable_dirichletRhsField_apply_highShellSigma {ell ellPrime LPrime : ℕ}
    (hell : ell ≤ ellPrime) (hlL : ellPrime ≤ LPrime) (p x : Vec d) :
    Measurable[Terms.highShellSigma d ell]
      (fun omega : ShellSeq d => dirichletRhsField omega LPrime ellPrime p x) := by
  have hfun : (fun omega : ShellSeq d => dirichletRhsField omega LPrime ellPrime p x) =
      fun omega : ShellSeq d =>
        matVecMul (finiteShellIncrement omega ellPrime LPrime x) p := by
    funext omega
    rw [dirichletRhsField, finiteShellIncrement_apply_eq_streamCutoff_sub omega hlL x]
  rw [hfun]
  exact measurable_matVecMul_of_entries (mAlpha := Terms.highShellSigma d ell)
    (fun i j => measurable_finiteShellIncrement_apply_entry_highShellSigma hell x i j) p

/-- **The field half of the measurability sentence.**  On every scale-`n` sub-cube of `cu_m` the
cube mean of the response flux `R = (a_{L'} − a_ℓ) ∇w` is measurable for
`F_> = σ(j_r : r > ℓ)`, for every selection `w` of the Dirichlet response of
`e.def.w`.

Choice independence (`measurable_volumeAverageVec_matVecMul_grad_of_canonical`)
moves the observable to the canonical response.  There the cube mean is the
inner product of the cut-off coefficient rows with the response gradient class;
the coefficient difference is the shell sum over `(ℓ, L']` and the flux of the
Dirichlet problem is the shell sum over `(ℓ', L']`, so both read only shells
`r > ℓ`, and the Dirichlet solution operator is continuous. -/
theorem measurable_volumeAverageVec_matVecMul_coefficientCutoff_sub_grad_highShellSigma
    [NeZero d] (nu : ℝ) {ell ellPrime LPrime m n : ℕ}
    (hell : ell ≤ ellPrime) (hlL : ellPrime ≤ LPrime) {p : Vec d}
    {w : ShellSeq d → H10Function (openCubeSet (originCube d (m : ℤ)))}
    (hw : ∀ omega : ShellSeq d, IsDirichletResponse omega LPrime ellPrime m p (w omega))
    {z : TriadicCube d} (hz : z ∈ largeCubeSubcubes d n m) :
    Measurable[Terms.highShellSigma d ell] (fun omega : ShellSeq d =>
      volumeAverageVec (openCubeSet z)
        (fun y => matVecMul ((coefficientCutoff nu omega LPrime).toCoeffField y -
            (coefficientCutoff nu omega ell).toCoeffField y)
          ((w omega).toH1Function.grad y))) := by
  have hVU : openCubeSet z ⊆ openCubeSet (originCube d (m : ℤ)) :=
    openCubeSet_subset_of_mem_descendantsAtDepth hz
  refine measurable_volumeAverageVec_matVecMul_grad_of_canonical hVU
    (fun omega y => (coefficientCutoff nu omega LPrime).toCoeffField y -
      (coefficientCutoff nu omega ell).toCoeffField y) hw ?_
  exact measurable_volumeAverageVec_matVecMul_grad_dirichletResponse_comp
    (mAlpha := Terms.highShellSigma d ell) (fun omega : ShellSeq d => omega)
    (fun omega y => (coefficientCutoff nu omega LPrime).toCoeffField y -
      (coefficientCutoff nu omega ell).toCoeffField y)
    (fun omega i j => continuous_coefficientCutoff_sub_entry nu omega LPrime ell i j)
    (fun y i j => measurable_coefficientCutoff_sub_entry_highShellSigma nu
      (le_trans hell hlL) y i j)
    LPrime ellPrime m p hVU (isOpen_openCubeSet z).measurableSet
    (fun x => measurable_dirichletRhsField_apply_highShellSigma hell hlL p x)

end Obligation7

/-! ## The second-step observable of `l.RHS.term1` -/

section Step2

variable [NeZero d]

omit [NeZero d] in
/-- The cube mean of a pairing of two `L²(U)` fields is their inner product. -/
theorem volumeAverage_vecDot_eq_inner {U : Set (Vec d)} {f g : Vec d → Vec d}
    (hf : MemVectorL2 U f) (hg : MemVectorL2 U g) :
    volumeAverage U (fun x => vecDot (f x) (g x)) =
      (MeasureTheory.volume U).toReal⁻¹ *
        inner ℝ (toHilbertVectorL2OfVecField hf) (toHilbertVectorL2OfVecField hg) := by
  rw [inner_toHilbertVectorL2OfVecField_eq_integral, volumeAverage]

/-- **The second-step observable from the pairing field alone.**  The response `w` is
eliminated: the second step's observable of `l.RHS.term1` is `AEMeasurable`
as soon as the `L²(cu_m)` class of the sample-dependent pairing field is.

This is the sharpest form available at the present carriers.  The pairing field
of the statement is `a_ℓ(ω) ∇ũ_n(ω) − q̃`, an observable of
`gluedGradientField`, whose sample dependence runs through the Chapter 2 cube
maximizer — a different choice point from the Dirichlet response, and one that
no available declaration makes measurable. -/
theorem aemeasurable_ofReal_abs_volumeAverage_vecDot_grad_of_pairing
    {LPrime ellPrime m : ℕ} {p : Vec d} {mu : MeasureTheory.Measure (ShellSeq d)}
    {w : ShellSeq d → H10Function (openCubeSet (originCube d (m : ℤ)))}
    (hw : ∀ omega : ShellSeq d, IsDirichletResponse omega LPrime ellPrime m p (w omega))
    {Vfield : ShellSeq d → Vec d → Vec d}
    (hVmem : ∀ omega : ShellSeq d,
      MemVectorL2 (openCubeSet (originCube d (m : ℤ))) (Vfield omega))
    (hVclass : AEMeasurable (fun omega : ShellSeq d =>
      toHilbertVectorL2OfVecField (hVmem omega)) mu) :
    AEMeasurable (fun omega : ShellSeq d =>
      ENNReal.ofReal |volumeAverage (openCubeSet (originCube d (m : ℤ)))
        (fun x => vecDot ((w omega).toH1Function.grad x) (Vfield omega x))|) mu := by
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  refine aemeasurable_ofReal_abs_volumeAverage_vecDot_grad_of_canonical
    Set.Subset.rfl Vfield hw ?_
  have hg : ∀ omega : ShellSeq d, MemVectorL2 (openCubeSet (originCube d (m : ℤ)))
      (dirichletResponse omega LPrime ellPrime m p).toH1Function.grad :=
    fun omega => (dirichletResponse omega LPrime ellPrime m p).toH1Function.grad_memVectorL2
  have hfun : (fun omega : ShellSeq d =>
      ENNReal.ofReal |volumeAverage (openCubeSet (originCube d (m : ℤ)))
        (fun x => vecDot ((dirichletResponse omega LPrime ellPrime m p).toH1Function.grad x)
          (Vfield omega x))|) =
      fun omega : ShellSeq d => ENNReal.ofReal
        |(MeasureTheory.volume (openCubeSet (originCube d (m : ℤ)))).toReal⁻¹ *
          inner ℝ (toHilbertVectorL2OfVecField (hg omega))
            (toHilbertVectorL2OfVecField (hVmem omega))| := by
    funext omega
    exact congrArg (fun t : ℝ => ENNReal.ofReal |t|)
      (volumeAverage_vecDot_eq_inner (hg omega) (hVmem omega))
  rw [hfun]
  have hinner : AEMeasurable (fun omega : ShellSeq d =>
      inner ℝ (toHilbertVectorL2OfVecField (hg omega))
        (toHilbertVectorL2OfVecField (hVmem omega))) mu :=
    continuous_inner.measurable.comp_aemeasurable
      ((measurable_gradToHilbertVectorL2_dirichletResponse
        (LPrime := LPrime) (ellPrime := ellPrime) (m := m) (p := p)).aemeasurable.prodMk hVclass)
  exact ENNReal.measurable_ofReal.comp_aemeasurable
    (continuous_abs.measurable.comp_aemeasurable (hinner.const_mul _))

end Step2

/-! ## The `H̲¹` observable of `l.RHS.term1` -/

section Hessian

variable [NeZero d]

/-- **Measurability of the `H̲¹` observable reduced to its Hessian
half.**  The `H̲¹(cu_m)` observable of the response splits as a fixed multiple
of the cube energy plus the cube `L²` norm of the Hessian carrier.  The first summand is discharged
(`aemeasurable_vecCubeLpENorm_grad`); the second is the whole content.

The second summand is a definite function of the sample (weak Hessians are a.e.
unique and see the function only through its weak-gradient class), but making it
measurable is the graph measurability of the (unbounded) weak-Hessian operator, which the
`1`-Lipschitz Dirichlet solution operator does not provide. -/
theorem aemeasurable_vecCubeH1ENorm_grad_of_hessian
    {LPrime ellPrime m : ℕ} {p : Vec d} {mu : MeasureTheory.Measure (ShellSeq d)}
    {w : ShellSeq d → H10Function (openCubeSet (originCube d (m : ℤ)))}
    (hw : ∀ omega : ShellSeq d, IsDirichletResponse omega LPrime ellPrime m p (w omega))
    (J : ShellSeq d → Vec d → Mat d)
    (hJ : AEMeasurable (fun omega : ShellSeq d =>
      Section2.Norms.cubeLpENorm (originCube d (m : ℤ)) 2
        (fun x => HilbertMat.ofMat (J omega x))) mu) :
    AEMeasurable (fun omega : ShellSeq d =>
      Terms.vecCubeH1ENorm (originCube d (m : ℤ)) (w omega).toH1Function.grad
        (J omega)) mu := by
  have hfun : (fun omega : ShellSeq d =>
      Terms.vecCubeH1ENorm (originCube d (m : ℤ)) (w omega).toH1Function.grad (J omega)) =
      fun omega : ShellSeq d =>
        ENNReal.ofReal ((3 : ℝ) ^ (-(((originCube d (m : ℤ)).scale : ℝ)))) *
            ResponseFields.vecCubeLpENorm (originCube d (m : ℤ)) 2
              (w omega).toH1Function.grad +
          Section2.Norms.cubeLpENorm (originCube d (m : ℤ)) 2
            (fun x => HilbertMat.ofMat (J omega x)) := by
    funext omega
    exact Terms.vecCubeH1ENorm_eq _ _ _
  rw [hfun]
  exact ((aemeasurable_vecCubeLpENorm_grad hw).const_mul _).add hJ

end Hessian

end

end SuperdiffusionCLT.Section3.Setup
