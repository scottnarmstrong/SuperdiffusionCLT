/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.ShellAssembly

/-!
# Assembling a skew shell field from scalar fields

From a family `φ` of scalar `C^2` fields indexed by pairs `i < j` the assembled shell
field has entries `k i j = φ (i,j)`, `k j i = -φ (i,j)` and `k i i = 0`; its stored
first and second derivatives are the entrywise derivatives of the scalar fields.
-/

@[expose] public section

namespace SuperdiffusionCLT.Assumptions.ShellLaw.Model

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-- The index pairs `i < j`. -/
abbrev SkewIdx (d : ℕ) := { p : Fin d × Fin d // p.1 < p.2 }

/-- The skew matrix unit `E_ij - E_ji` of the pair `p = (i,j)`. -/
def nv_skewUnit (p : SkewIdx d) : Mat d :=
  Matrix.single p.1.1 p.1.2 (1 : ℝ) - Matrix.single p.1.2 p.1.1 (1 : ℝ)

/-- The skew extension of a family of reals indexed by pairs `i < j`. -/
def nv_skewCoef (c : SkewIdx d → ℝ) (i j : Fin d) : ℝ :=
  if h : i < j then c ⟨(i, j), h⟩ else if h' : j < i then -c ⟨(j, i), h'⟩ else 0

theorem nv_skewCoef_of_lt (c : SkewIdx d → ℝ) {i j : Fin d} (h : i < j) :
    nv_skewCoef c i j = c ⟨(i, j), h⟩ := by
  simp [nv_skewCoef, h]

theorem nv_skewCoef_of_gt (c : SkewIdx d → ℝ) {i j : Fin d} (h : j < i) :
    nv_skewCoef c i j = -c ⟨(j, i), h⟩ := by
  simp [nv_skewCoef, h, not_lt.2 h.le]

theorem nv_skewCoef_diag (c : SkewIdx d → ℝ) (i : Fin d) :
    nv_skewCoef c i i = 0 := by
  simp [nv_skewCoef]

theorem nv_skewCoef_antisymm (c : SkewIdx d → ℝ) (i j : Fin d) :
    nv_skewCoef c j i = -nv_skewCoef c i j := by
  rcases lt_trichotomy i j with h | rfl | h
  · rw [nv_skewCoef_of_lt c h, nv_skewCoef_of_gt c h]
  · rw [nv_skewCoef_diag, neg_zero]
  · rw [nv_skewCoef_of_lt c h, nv_skewCoef_of_gt c h, neg_neg]

theorem nv_skewCoef_neg (c : SkewIdx d → ℝ) (i j : Fin d) :
    nv_skewCoef (fun p ↦ -c p) i j = -nv_skewCoef c i j := by
  rcases lt_trichotomy i j with h | rfl | h
  · rw [nv_skewCoef_of_lt _ h, nv_skewCoef_of_lt c h]
  · rw [nv_skewCoef_diag, nv_skewCoef_diag, neg_zero]
  · rw [nv_skewCoef_of_gt _ h, nv_skewCoef_of_gt c h]

theorem nv_skewUnit_apply (p : SkewIdx d) (i j : Fin d) :
    nv_skewUnit p i j =
      (if p.1.1 = i ∧ p.1.2 = j then 1 else 0) - (if p.1.2 = i ∧ p.1.1 = j then 1 else 0) := by
  simp [nv_skewUnit, Matrix.single_apply]

/-- Entries of a combination of skew units. -/
theorem nv_sum_skewUnit_apply (c : SkewIdx d → ℝ) (i j : Fin d) :
    (∑ p, c p • nv_skewUnit p) i j = nv_skewCoef c i j := by
  rw [Matrix.sum_apply]
  by_cases h : i < j
  · rw [nv_skewCoef_of_lt c h]
    rw [Finset.sum_eq_single ⟨(i, j), h⟩]
    · simp [nv_skewUnit_apply, h.ne, h.ne']
    · intro p _ hp
      rw [Matrix.smul_apply, nv_skewUnit_apply]
      have h1 : ¬ (p.1.1 = i ∧ p.1.2 = j) := by
        rintro ⟨h1, h2⟩
        exact hp (Subtype.ext (Prod.ext h1 h2))
      have h2 : ¬ (p.1.2 = i ∧ p.1.1 = j) := by
        rintro ⟨h1, h2⟩
        have := p.2
        rw [h1, h2] at this
        exact absurd (lt_trans this h) (lt_irrefl _)
      simp [h1, h2]
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · by_cases h' : j < i
    · rw [nv_skewCoef_of_gt c h']
      rw [Finset.sum_eq_single ⟨(j, i), h'⟩]
      · simp [nv_skewUnit_apply, h'.ne, h'.ne']
      · intro p _ hp
        rw [Matrix.smul_apply, nv_skewUnit_apply]
        have h1 : ¬ (p.1.2 = i ∧ p.1.1 = j) := by
          rintro ⟨h1, h2⟩
          exact hp (Subtype.ext (Prod.ext h2 h1))
        have h2 : ¬ (p.1.1 = i ∧ p.1.2 = j) := by
          rintro ⟨h1, h2⟩
          have := p.2
          rw [h1, h2] at this
          exact absurd (lt_trans this h') (lt_irrefl _)
        simp [h1, h2]
      · intro hn
        exact absurd (Finset.mem_univ _) hn
    · have hij : i = j := le_antisymm (not_lt.1 h') (not_lt.1 h)
      subst hij
      rw [nv_skewCoef_diag]
      refine Finset.sum_eq_zero fun p _ ↦ ?_
      rw [Matrix.smul_apply, nv_skewUnit_apply]
      have h1 : ¬ (p.1.1 = i ∧ p.1.2 = i) := by
        rintro ⟨h1, h2⟩
        have := p.2
        rw [h1, h2] at this
        exact lt_irrefl _ this
      simp only [h1, and_comm, ite_false, sub_self, smul_zero]

/-! ## The assembly map -/

/-- The unit-multiplication map `t ↦ t • E_p`. -/
def nv_unitCLM (p : SkewIdx d) : ℝ →L[ℝ] Mat d :=
  ContinuousLinearMap.toSpanSingleton ℝ (nv_skewUnit p)

/-- Postcomposition of first derivatives with `nv_unitCLM p`. -/
def nv_unitFirst (p : SkewIdx d) : (Vec d →L[ℝ] ℝ) →L[ℝ] (Vec d →L[ℝ] Mat d) :=
  ContinuousLinearMap.compL ℝ (Vec d) ℝ (Mat d) (nv_unitCLM p)

/-- Postcomposition of second derivatives with `nv_unitCLM p`. -/
def nv_unitSecond (p : SkewIdx d) :
    (Vec d →L[ℝ] (Vec d →L[ℝ] ℝ)) →L[ℝ] (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) :=
  ContinuousLinearMap.compL ℝ (Vec d) (Vec d →L[ℝ] ℝ) (Vec d →L[ℝ] Mat d) (nv_unitFirst p)

/-- A continuous linear map as a continuous map. -/
def nv_cm {E F : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
    [TopologicalSpace F] [AddCommMonoid F] [Module ℝ F] (T : E →L[ℝ] F) : C(E, F) :=
  ⟨T, T.continuous⟩

/-- The ambient triple of the assembled field. -/
def nv_assembleAmbient (φ : SkewIdx d → ScalarC2Field d) : ShellAmbient d :=
  (∑ p, (nv_cm (nv_unitCLM p)).comp (φ p).1.1,
    (∑ p, (nv_cm (nv_unitFirst p)).comp (φ p).1.2.1,
      ∑ p, (nv_cm (nv_unitSecond p)).comp (φ p).1.2.2))

theorem nv_assembleAmbient_fst_apply (φ : SkewIdx d → ScalarC2Field d) (x : Vec d) :
    (nv_assembleAmbient φ).1 x = ∑ p, φ p x • nv_skewUnit p := by
  simp [nv_assembleAmbient, nv_cm, nv_unitCLM, ContinuousMap.sum_apply]

theorem nv_assembleAmbient_deriv_apply (φ : SkewIdx d → ScalarC2Field d) (x : Vec d) :
    (nv_assembleAmbient φ).2.1 x = ∑ p, nv_unitFirst p (ScalarC2Field.deriv (φ p) x) := by
  simp [nv_assembleAmbient, nv_cm, ContinuousMap.sum_apply]
  rfl

theorem nv_assembleAmbient_secondDeriv_apply (φ : SkewIdx d → ScalarC2Field d) (x : Vec d) :
    (nv_assembleAmbient φ).2.2 x =
      ∑ p, nv_unitSecond p (ScalarC2Field.secondDeriv (φ p) x) := by
  simp [nv_assembleAmbient, nv_cm, ContinuousMap.sum_apply]
  rfl

theorem nv_assembleAmbient_prop (φ : SkewIdx d → ScalarC2Field d) :
    (∀ x, HasFDerivAt (nv_assembleAmbient φ).1 ((nv_assembleAmbient φ).2.1 x) x) ∧
    (∀ x, HasFDerivAt (nv_assembleAmbient φ).2.1 ((nv_assembleAmbient φ).2.2 x) x) ∧
    ∀ x i j, (nv_assembleAmbient φ).1 x i j = -(nv_assembleAmbient φ).1 x j i := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    have h := HasFDerivAt.fun_sum (u := Finset.univ) (x := x)
      (A := fun p y ↦ nv_unitCLM p (φ p y))
      (A' := fun p ↦ (nv_unitCLM p).comp (ScalarC2Field.deriv (φ p) x))
      (fun p _ ↦ (nv_unitCLM p).hasFDerivAt.comp x ((φ p).hasFDerivAt x))
    have hf : ⇑(nv_assembleAmbient φ).1 = fun y ↦ ∑ p, nv_unitCLM p (φ p y) := by
      funext y
      rw [nv_assembleAmbient_fst_apply]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      simp [nv_unitCLM]
    rw [hf, nv_assembleAmbient_deriv_apply]
    exact h
  · intro x
    have h := HasFDerivAt.fun_sum (u := Finset.univ) (x := x)
      (A := fun p y ↦ nv_unitFirst p (ScalarC2Field.deriv (φ p) y))
      (A' := fun p ↦ (nv_unitFirst p).comp (ScalarC2Field.secondDeriv (φ p) x))
      (fun p _ ↦ (nv_unitFirst p).hasFDerivAt.comp x ((φ p).deriv_hasFDerivAt x))
    have hf : ⇑(nv_assembleAmbient φ).2.1 =
        fun y ↦ ∑ p, nv_unitFirst p (ScalarC2Field.deriv (φ p) y) := by
      funext y
      rw [nv_assembleAmbient_deriv_apply]
    rw [hf, nv_assembleAmbient_secondDeriv_apply]
    exact h
  · intro x i j
    rw [nv_assembleAmbient_fst_apply, nv_sum_skewUnit_apply, nv_sum_skewUnit_apply,
      nv_skewCoef_antisymm]

/-- **The skew shell field assembled from scalar `C^2` fields indexed by pairs `i < j`.** -/
def assembleSkew (φ : SkewIdx d → ScalarC2Field d) : ShellField d :=
  ⟨nv_assembleAmbient φ, nv_assembleAmbient_prop φ⟩

/-- Entry formula for the value. -/
theorem assembleSkew_apply (φ : SkewIdx d → ScalarC2Field d) (x : Vec d) (i j : Fin d) :
    assembleSkew φ x i j = nv_skewCoef (fun p ↦ φ p x) i j := by
  change (nv_assembleAmbient φ).1 x i j = _
  rw [nv_assembleAmbient_fst_apply, nv_sum_skewUnit_apply]

theorem nv_unitFirst_apply (p : SkewIdx d) (D : Vec d →L[ℝ] ℝ) (v : Vec d) :
    nv_unitFirst p D v = D v • nv_skewUnit p :=
  rfl

theorem nv_unitSecond_apply (p : SkewIdx d) (H : Vec d →L[ℝ] (Vec d →L[ℝ] ℝ)) (v w : Vec d) :
    nv_unitSecond p H v w = H v w • nv_skewUnit p :=
  rfl

/-- Entry formula for the first derivative. -/
theorem assembleSkew_deriv_apply (φ : SkewIdx d → ScalarC2Field d) (x v : Vec d)
    (i j : Fin d) :
    ShellField.deriv (assembleSkew φ) x v i j =
      nv_skewCoef (fun p ↦ ScalarC2Field.deriv (φ p) x v) i j := by
  change (nv_assembleAmbient φ).2.1 x v i j = _
  rw [nv_assembleAmbient_deriv_apply, _root_.sum_apply, ← nv_sum_skewUnit_apply]
  simp only [nv_unitFirst_apply]

/-- Entry formula for the second derivative. -/
theorem assembleSkew_secondDeriv_apply (φ : SkewIdx d → ScalarC2Field d) (x v w : Vec d)
    (i j : Fin d) :
    ShellField.secondDeriv (assembleSkew φ) x v w i j =
      nv_skewCoef (fun p ↦ ScalarC2Field.secondDeriv (φ p) x v w) i j := by
  change (nv_assembleAmbient φ).2.2 x v w i j = _
  rw [nv_assembleAmbient_secondDeriv_apply, _root_.sum_apply, _root_.sum_apply,
    ← nv_sum_skewUnit_apply]
  simp only [nv_unitSecond_apply]

theorem assembleSkew_apply_lt (φ : SkewIdx d → ScalarC2Field d) (x : Vec d) {i j : Fin d}
    (h : i < j) : assembleSkew φ x i j = φ ⟨(i, j), h⟩ x := by
  rw [assembleSkew_apply]
  simp [nv_skewCoef, h]

/-! ## Measurability -/

theorem continuous_nv_assembleAmbient :
    Continuous (nv_assembleAmbient (d := d)) := by
  refine Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_)
  · exact continuous_finsetSum _ fun p _ ↦
      (ContinuousMap.continuous_postcomp (nv_cm (nv_unitCLM p))).comp
        (ScalarC2Field.continuous_val_fst.comp (continuous_apply p))
  · exact continuous_finsetSum _ fun p _ ↦
      (ContinuousMap.continuous_postcomp (nv_cm (nv_unitFirst p))).comp
        (ScalarC2Field.continuous_val_snd_fst.comp (continuous_apply p))
  · exact continuous_finsetSum _ fun p _ ↦
      (ContinuousMap.continuous_postcomp (nv_cm (nv_unitSecond p))).comp
        (ScalarC2Field.continuous_val_snd_snd.comp (continuous_apply p))

/-- The assembly map is continuous for the product of the compact-open topologies. -/
theorem continuous_assembleSkew : Continuous (assembleSkew (d := d)) :=
  Continuous.subtype_mk continuous_nv_assembleAmbient (fun φ ↦ (assembleSkew φ).2)

/-- **The assembly map is measurable** for the product (Borel) sigma-algebra on the family. -/
theorem measurable_assembleSkew : Measurable (assembleSkew (d := d)) :=
  continuous_assembleSkew.measurable

/-! ## Negation and signed-permutation conjugation -/

/-- Negation of the assembled field is the assembly of the negated family. -/
theorem negate_assembleSkew (φ : SkewIdx d → ScalarC2Field d) :
    ShellField.negate (assembleSkew φ) =
      assembleSkew (fun p ↦ ScalarC2Field.smulConst (-1) (φ p)) := by
  ext x i j
  rw [ShellField.negate_apply, Matrix.neg_apply, assembleSkew_apply, assembleSkew_apply]
  simp only [ScalarC2Field.smulConst_apply, neg_one_mul]
  rw [nv_skewCoef_neg]

/-- The pair-indexed family extended to ordered pairs `i ≠ j` by antisymmetry. -/
def nv_pairFamily (φ : SkewIdx d → ScalarC2Field d) (i j : Fin d) (h : i ≠ j) :
    ScalarC2Field d :=
  if hl : i < j then φ ⟨(i, j), hl⟩
  else ScalarC2Field.smulConst (-1) (φ ⟨(j, i), lt_of_le_of_ne (not_lt.1 hl) h.symm⟩)

theorem nv_pairFamily_apply (φ : SkewIdx d → ScalarC2Field d) (i j : Fin d) (h : i ≠ j)
    (x : Vec d) : nv_pairFamily φ i j h x = nv_skewCoef (fun p ↦ φ p x) i j := by
  by_cases hl : i < j
  · rw [nv_skewCoef_of_lt _ hl]
    simp only [nv_pairFamily, hl, ↓reduceDIte]
  · have h' : j < i := lt_of_le_of_ne (not_lt.1 hl) h.symm
    rw [nv_skewCoef_of_gt _ h']
    simp only [nv_pairFamily, hl, ↓reduceDIte, ScalarC2Field.smulConst_apply, neg_one_mul]

/-- The coordinate-wise map `x ↦ R x` as a continuous linear map. -/
def nv_matVecCLM (R : Mat d) : Vec d →L[ℝ] Vec d :=
  ⟨Matrix.toLin' R, (Matrix.toLin' R).continuous_of_finiteDimensional⟩

@[simp]
theorem nv_matVecCLM_apply (R : Mat d) (x : Vec d) : nv_matVecCLM R x = matVecMul R x :=
  rfl

/-- The scalar family describing the signed-permutation conjugate of an assembled field:
the pair `(a,b)` carries `s a * s b * φ_{σ a, σ b} (R ·)`. -/
def nv_rotFamily (σ : Equiv.Perm (Fin d)) (s : Fin d → ℝ) (L : Vec d →L[ℝ] Vec d)
    (φ : SkewIdx d → ScalarC2Field d) : SkewIdx d → ScalarC2Field d :=
  fun q ↦ ScalarC2Field.smulConst (s q.1.1 * s q.1.2)
    (ScalarC2Field.precomp L
      (nv_pairFamily φ (σ q.1.1) (σ q.1.2) (fun h ↦ (ne_of_lt q.2) (σ.injective h))))

theorem nv_rotate_entry (R M : Mat d) (σ : Equiv.Perm (Fin d)) (s : Fin d → ℝ)
    (hRσ : ∀ i j, R i j = if i = σ j then s j else 0) (a b : Fin d) :
    (matTranspose R * M * R) a b = s a * s b * M (σ a) (σ b) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ b)]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (σ a)]
    · have h1 : matTranspose R a (σ a) = s a := by
        simp [matTranspose, hRσ]
      have h2 : R (σ b) b = s b := by
        simp [hRσ]
      rw [h1, h2]
      ring
    · intro c _ hc
      have : matTranspose R a c = 0 := by
        simp [matTranspose, hRσ, hc]
      rw [this, zero_mul]
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · intro e _ he
    have : R e b = 0 := by
      simp [hRσ, he]
    rw [this, mul_zero]
  · intro hn
    exact absurd (Finset.mem_univ _) hn

/-- **Signed-permutation conjugation of an assembled field**: for `R = (s_j δ_{i,σ j})`
the conjugate `Rᵀ k(R ·) R` is the assembly of the family `nv_rotFamily`. -/
theorem rotate_assembleSkew (R : Mat d) (hR : IsSignedPermutationMatrix R)
    (σ : Equiv.Perm (Fin d)) (s : Fin d → ℝ)
    (hRσ : ∀ i j, R i j = if i = σ j then s j else 0) (φ : SkewIdx d → ScalarC2Field d) :
    ShellField.rotate R hR (assembleSkew φ) =
      assembleSkew (nv_rotFamily σ s (nv_matVecCLM R) φ) := by
  ext x a b
  rw [ShellField.rotate_apply, nv_rotate_entry R _ σ s hRσ, assembleSkew_apply,
    assembleSkew_apply]
  have key : ∀ q : SkewIdx d, nv_rotFamily σ s (nv_matVecCLM R) φ q x =
      s q.1.1 * s q.1.2 * nv_skewCoef (fun p ↦ φ p (matVecMul R x)) (σ q.1.1) (σ q.1.2) := by
    intro q
    simp only [nv_rotFamily, ScalarC2Field.smulConst_apply, ScalarC2Field.precomp_apply,
      nv_matVecCLM_apply, nv_pairFamily_apply]
  by_cases hab : a < b
  · rw [nv_skewCoef_of_lt _ hab, key]
  · by_cases hba : b < a
    · rw [nv_skewCoef_of_gt _ hba, key, nv_skewCoef_antisymm _ (σ a) (σ b)]
      ring
    · have : a = b := le_antisymm (not_lt.1 hba) (not_lt.1 hab)
      subst this
      rw [nv_skewCoef_diag, nv_skewCoef_diag]
      ring

/-- The hypotheses of `rotate_assembleSkew` are satisfiable: the identity matrix. -/
theorem nv_signedPermutation_one_witness :
    ∃ (σ : Equiv.Perm (Fin d)) (s : Fin d → ℝ),
      IsSignedPermutationMatrix (1 : Mat d) ∧
        ∀ i j, (1 : Mat d) i j = if i = σ j then s j else 0 := by
  have h : ∀ i j : Fin d, (1 : Mat d) i j = if i = (Equiv.refl (Fin d)) j then (fun _ ↦ (1 : ℝ)) j
      else 0 := by
    intro i j
    rw [Matrix.one_apply]
    rfl
  exact ⟨Equiv.refl _, fun _ ↦ 1,
    ⟨Equiv.refl _, fun _ ↦ 1, fun _ ↦ Or.inl rfl, h⟩, h⟩

end

end SuperdiffusionCLT.Assumptions.ShellLaw.Model
