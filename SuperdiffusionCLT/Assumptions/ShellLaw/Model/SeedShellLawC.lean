/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.SeedShellLawB

/-!
# Signed-permutation invariance of the seed shell law, and the dilated shell laws

The conjugate of an assembled field by a signed permutation is the assembly of a family obtained
from the original one by reindexing the strict upper pairs (`(a, b) ↦` the ordered pair of
`(σ a, σ b)`), a sign twist and precomposition with the matrix. The reindexing is a bijection of
the index set, so the product of scalar seeds is preserved.
-/

@[expose] public section

namespace SuperdiffusionCLT.Assumptions.ShellLaw.Model

open Homogenization MeasureTheory ProbabilityTheory
open SuperdiffusionCLT.Frozen.Assumptions

noncomputable section

variable {d : ℕ}

/-- The ordered pair `(σ a, σ b)` or `(σ b, σ a)`, whichever has the smaller entry first. -/
def nv_orderedPair (σ : Equiv.Perm (Fin d)) (q : SkewIdx d) : SkewIdx d :=
  if h : σ q.1.1 < σ q.1.2 then ⟨(σ q.1.1, σ q.1.2), h⟩
  else ⟨(σ q.1.2, σ q.1.1), lt_of_le_of_ne (not_lt.1 h) (fun e ↦ (ne_of_lt q.2) (σ.injective e.symm))⟩

/-- The sign picked up when reordering. -/
def nv_orderSign (σ : Equiv.Perm (Fin d)) (q : SkewIdx d) : ℝ :=
  if σ q.1.1 < σ q.1.2 then 1 else -1

theorem nv_orderedPair_injective (σ : Equiv.Perm (Fin d)) :
    Function.Injective (nv_orderedPair σ) := by
  intro q q' h
  have hq := q.2
  have hq' := q'.2
  obtain ⟨⟨a, b⟩, hab⟩ := q
  obtain ⟨⟨a', b'⟩, hab'⟩ := q'
  simp only [nv_orderedPair] at h hq hq'
  by_cases h1 : σ a < σ b <;> by_cases h2 : σ a' < σ b' <;> simp only [h1, h2, dite_true,
    dite_false, Subtype.mk.injEq, Prod.mk.injEq] at h
  · exact Subtype.ext (Prod.ext (σ.injective h.1) (σ.injective h.2))
  · have e1 := σ.injective h.1
    have e2 := σ.injective h.2
    subst e1
    subst e2
    exact absurd (lt_trans hab hab') (lt_irrefl _)
  · have e1 := σ.injective h.1
    have e2 := σ.injective h.2
    subst e1
    subst e2
    exact absurd (lt_trans hab hab') (lt_irrefl _)
  · exact Subtype.ext (Prod.ext (σ.injective h.2) (σ.injective h.1))

/-- The reindexing of the strict upper pairs as a permutation. -/
def nv_orderedPairEquiv (σ : Equiv.Perm (Fin d)) : Equiv.Perm (SkewIdx d) :=
  Equiv.ofBijective (nv_orderedPair σ) (Finite.injective_iff_bijective.1 (nv_orderedPair_injective σ))

/-- Reindexing coordinates by a permutation preserves the iid product. -/
theorem nv_seedProduct_map_reindex (ε : ℝ) (e : Equiv.Perm (SkewIdx d)) :
    (nv_seedProduct d ε).map (fun (φ : SkewIdx d → ScalarC2Field d) q ↦ φ (e q)) =
      nv_seedProduct d ε := by
  have h := Measure.pi_map_piCongrLeft (ι := SkewIdx d) (ι' := SkewIdx d) e.symm
    (β := fun _ ↦ ScalarC2Field d) (fun _ ↦ nv_seedLaw d ε)
  unfold nv_seedProduct
  rw [← h]
  congr 1
  funext φ q
  simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft']

/-- Invariance is stable under composition. -/
theorem nv_map_comp_eq_self {α : Type*} [MeasurableSpace α] (μ : Measure α) (f g : α → α)
    (hf : Measurable f) (hg : Measurable g) (h1 : μ.map f = μ) (h2 : μ.map g = μ) :
    μ.map (g ∘ f) = μ := by
  rw [← Measure.map_map hg hf, h1, h2]

theorem nv_smulConst_one (f : ScalarC2Field d) : ScalarC2Field.smulConst 1 f = f :=
  ScalarC2Field.ext fun x ↦ by simp

theorem nv_seedLaw_map_smulConst (ε c : ℝ) (hc : c = 1 ∨ c = -1) :
    (nv_seedLaw d ε).map (ScalarC2Field.smulConst c) = nv_seedLaw d ε := by
  rcases hc with rfl | rfl
  · have : ScalarC2Field.smulConst (d := d) 1 = id := funext nv_smulConst_one
    rw [this, Measure.map_id]
  · exact nv_seedLaw_map_neg ε

theorem nv_orderSign_cases (σ : Equiv.Perm (Fin d)) (q : SkewIdx d) :
    nv_orderSign σ q = 1 ∨ nv_orderSign σ q = -1 := by
  unfold nv_orderSign
  split_ifs <;> simp

/-- The coordinate map of the reindexed family. -/
def nv_rotCoord (σ : Equiv.Perm (Fin d)) (s : Fin d → ℝ) (L : Vec d →L[ℝ] Vec d)
    (q : SkewIdx d) (f : ScalarC2Field d) : ScalarC2Field d :=
  ScalarC2Field.smulConst (s q.1.1 * s q.1.2)
    (ScalarC2Field.precomp L (ScalarC2Field.smulConst (nv_orderSign σ q) f))

theorem nv_rotFamily_eq (σ : Equiv.Perm (Fin d)) (s : Fin d → ℝ) (L : Vec d →L[ℝ] Vec d)
    (φ : SkewIdx d → ScalarC2Field d) (q : SkewIdx d) :
    nv_rotFamily σ s L φ q = nv_rotCoord σ s L q (φ (nv_orderedPair σ q)) := by
  unfold nv_rotFamily nv_rotCoord nv_pairFamily nv_orderedPair nv_orderSign
  by_cases h : σ q.1.1 < σ q.1.2
  · simp only [h, dite_true, ite_true]
    rw [nv_smulConst_one]
  · simp only [h, dite_false, ite_false]

theorem measurable_nv_rotCoord (σ : Equiv.Perm (Fin d)) (s : Fin d → ℝ) (L : Vec d →L[ℝ] Vec d)
    (q : SkewIdx d) : Measurable (nv_rotCoord σ s L q) :=
  (ScalarC2Field.measurable_smulConst _).comp
    ((ScalarC2Field.measurable_precomp L).comp (ScalarC2Field.measurable_smulConst _))

theorem nv_seedLaw_map_rotCoord (ε : ℝ) (σ : Equiv.Perm (Fin d)) (s : Fin d → ℝ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) (L : Vec d →L[ℝ] Vec d)
    (hL : (nv_seedLaw d ε).map (ScalarC2Field.precomp L) = nv_seedLaw d ε) (q : SkewIdx d) :
    (nv_seedLaw d ε).map (nv_rotCoord σ s L q) = nv_seedLaw d ε := by
  have hss : s q.1.1 * s q.1.2 = 1 ∨ s q.1.1 * s q.1.2 = -1 := by
    rcases hs q.1.1 with h1 | h1 <;> rcases hs q.1.2 with h2 | h2 <;> simp [h1, h2]
  have h3 := nv_map_comp_eq_self (nv_seedLaw d ε) _ _
    (ScalarC2Field.measurable_smulConst (nv_orderSign σ q)) (ScalarC2Field.measurable_precomp L)
    (nv_seedLaw_map_smulConst ε _ (nv_orderSign_cases σ q)) hL
  exact nv_map_comp_eq_self (nv_seedLaw d ε) _ _
    ((ScalarC2Field.measurable_precomp L).comp (ScalarC2Field.measurable_smulConst _))
    (ScalarC2Field.measurable_smulConst _) h3 (nv_seedLaw_map_smulConst ε _ hss)

/-- The matrix action of a signed permutation matrix is a signed permutation of coordinates. -/
theorem nv_matVecCLM_eq (R : Mat d) (σ : Equiv.Perm (Fin d)) (s : Fin d → ℝ)
    (hRσ : ∀ i j, R i j = if i = σ j then s j else 0) :
    nv_matVecCLM R = nv_signedPermCLM σ.symm (fun i ↦ s (σ.symm i)) := by
  refine ContinuousLinearMap.ext fun x ↦ ?_
  funext i
  rw [nv_matVecCLM_apply, nv_signedPermCLM_apply]
  simp only [matVecMul, nv_signedPerm, hRσ]
  rw [Finset.sum_eq_single (σ.symm i)]
  · simp
  · intro j _ hj
    have : i ≠ σ j := fun h ↦ hj (by rw [h]; simp)
    simp [this]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **Signed-permutation invariance** of the seed shell law. -/
theorem nv_seedShellLaw_map_rotate (d : ℕ) (ε : ℝ) (R : Mat d)
    (hR : IsSignedPermutationMatrix R) :
    Measure.map (ShellField.rotate R hR) (nv_seedShellLaw d ε).toMeasure =
      (nv_seedShellLaw d ε).toMeasure := by
  obtain ⟨σ, s, hs, hRσ⟩ := hR
  have hL : (nv_seedLaw d ε).map (ScalarC2Field.precomp (nv_matVecCLM R)) = nv_seedLaw d ε := by
    rw [nv_matVecCLM_eq R σ s hRσ]
    exact nv_seedLaw_map_signedPerm ε σ.symm _ (fun i ↦ hs _)
  have hP : Measurable (fun (φ : SkewIdx d → ScalarC2Field d) q ↦
      φ (nv_orderedPairEquiv σ q)) :=
    Measurable.of_eval fun q ↦ measurable_pi_apply _
  have hΨ : Measurable (fun (ψ : SkewIdx d → ScalarC2Field d) q ↦
      nv_rotCoord σ s (nv_matVecCLM R) q (ψ q)) :=
    Measurable.of_eval fun q ↦ (measurable_nv_rotCoord σ s _ q).comp (measurable_pi_apply q)
  refine nv_seedShellLaw_map_of_comm ε _ (ShellField.measurable_rotate R ⟨σ, s, hs, hRσ⟩)
    (fun φ q ↦ nv_rotCoord σ s (nv_matVecCLM R) q (φ (nv_orderedPairEquiv σ q)))
    (hΨ.comp hP) (fun φ ↦ ?_) ?_
  · rw [rotate_assembleSkew R ⟨σ, s, hs, hRσ⟩ σ s hRσ]
    congr 1
    funext q
    exact nv_rotFamily_eq σ s _ φ q
  · have h1 := nv_seedProduct_map_coord ε (fun q ↦ nv_rotCoord σ s (nv_matVecCLM R) q)
      (fun q ↦ measurable_nv_rotCoord σ s _ q) (fun q ↦ nv_seedLaw_map_rotCoord ε σ s hs _ hL q)
    have h2 := nv_seedProduct_map_reindex ε (nv_orderedPairEquiv σ)
    exact nv_map_comp_eq_self (nv_seedProduct d ε) _ _ hP hΨ h2 h1

/-! ## Corollaries for the dilated shell laws -/

theorem nv_scaledSeedShellLaw_map_negate (d : ℕ) (ε : ℝ) (n : ℕ) :
    Measure.map ShellField.negate (scaledShellLaw (nv_seedShellLaw d ε) n).toMeasure =
      (scaledShellLaw (nv_seedShellLaw d ε) n).toMeasure :=
  map_negate_scaledShellLaw _ (nv_seedShellLaw_map_negate d ε) n

/-! ## Satisfiability witnesses (dimension two) -/

example : Measure.map (ShellField.rotate (1 : Mat 2) (nv_signedPermutation_one_witness.choose_spec.choose_spec.1))
    (nv_seedShellLaw 2 1).toMeasure = (nv_seedShellLaw 2 1).toMeasure :=
  nv_seedShellLaw_map_rotate 2 1 _ _

example : Measure.map ShellField.negate (scaledShellLaw (nv_seedShellLaw 2 1) 3).toMeasure =
    (scaledShellLaw (nv_seedShellLaw 2 1) 3).toMeasure :=
  nv_scaledSeedShellLaw_map_negate 2 1 3

end

end SuperdiffusionCLT.Assumptions.ShellLaw.Model
