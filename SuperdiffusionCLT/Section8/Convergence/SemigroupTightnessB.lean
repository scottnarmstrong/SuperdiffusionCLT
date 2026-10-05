/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Convergence.SemigroupTightness

/-!
# Grid chains of a path law

For a probability law on continuous paths with the finite-dimensional distributions of a
conservative semigroup, the coordinates at the uniform grid `g, 2g, …, Jg` form the `J`-step
chain of the time-`g` kernel; the first step of a chain can be peeled off.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.Convergence
open Filter Homogenization MeasureTheory ProbabilityTheory Topology
open MarkovProcess MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal NNReal ZeroAtInfty
noncomputable section

section Marginals

variable {α : Type*} [MetricSpace α] [MeasurableSpace α] [BorelSpace α]

/-- The marginal of a path law with the finite-dimensional distributions of `S` at an ordered
family of times is the finite-time kernel. -/
theorem sgConv_map_finiteEvaluation_ordered (S : SubMarkovKernelSemigroup α)
    (hSc : S.IsConservative) (x : α) {Q : Measure (ContinuousPath α)}
    (hfdd : ∀ I : Finset ℝ≥0, Q.map (ContinuousPath.finsetEvaluation I) =
      finiteSetKernel S I x) {n : ℕ} (times : FiniteOrderedTimes n) :
    Q.map (ContinuousPath.finiteEvaluation (fun i ↦ times i)) = finiteTimeKernel S times x := by
  classical
  have hmem : ∀ i : Fin n,
      times i ∈ Finset.image (fun j ↦ times j) (Finset.univ : Finset (Fin n)) :=
    fun i ↦ Finset.mem_image_of_mem _ (Finset.mem_univ i)
  let I : Finset ℝ≥0 := Finset.image (fun j ↦ times j) (Finset.univ : Finset (Fin n))
  let phi : Fin n ↪o I :=
    OrderEmbedding.ofStrictMono (fun i ↦ (⟨times i, hmem i⟩ : I))
      (fun _ _ hij ↦ times.strictMono hij)
  let emb : Fin n ↪o Fin I.card := phi.trans (I.orderIsoOfFin rfl).symm.toOrderEmbedding
  have hphi : ∀ i : Fin n, ((phi i : I) : ℝ≥0) = times i := fun _ ↦ rfl
  have hsel : Measurable (fun w : I → α ↦ w ∘ (phi : Fin n → I)) :=
    measurable_pi_iff.mpr fun i ↦ measurable_pi_apply (phi i)
  have hfinset : Measurable (ContinuousPath.finsetEvaluation (alpha := α) I) :=
    ContinuousPath.measurable_finiteEvaluation _
  have hcomp : ContinuousPath.finiteEvaluation (α := α) (fun i ↦ times i) =
      (fun w : I → α ↦ w ∘ (phi : Fin n → I)) ∘
        ContinuousPath.finsetEvaluation (alpha := α) I := rfl
  have hrestrict : (fun w : I → α ↦ w ∘ (phi : Fin n → I)) ∘
      orderedPathToFiniteSet (α := α) I = FiniteOrderedTimes.restrictPath emb := rfl
  have htimes : (finiteSetTimes I).restrict emb = times := by
    apply DFunLike.ext _ _
    intro i
    show finiteSetTimes I ((I.orderIsoOfFin rfl).symm (phi i)) = times i
    rw [finiteSetTimes_orderIsoOfFin_symm_apply, hphi i]
  have hker : (finiteSetKernel S I x).map (fun w : I → α ↦ w ∘ (phi : Fin n → I)) =
      finiteTimeKernel S times x := by
    rw [finiteSetKernel_eq_map, ← Kernel.map_apply _ hsel,
      ← Kernel.map_comp_right _ (measurable_orderedPathToFiniteSet I) hsel, hrestrict,
      hSc.finiteTimeKernel_map_restrictPath S (finiteSetTimes I) emb, htimes]
  rw [hcomp, ← Measure.map_map hsel hfinset, hfdd I, hker]

end Marginals

section Chain

variable {α : Type*} [MeasurableSpace α]

/-- The uniform grid `g, 2g, …, Jg`. -/
def sgConv_gridTimes (g : ℝ≥0) (hg : 0 < g) (J : ℕ) : FiniteOrderedTimes J :=
  OrderEmbedding.ofStrictMono (fun i ↦ ((i : ℕ) + 1 : ℝ≥0) * g) fun i j hij ↦ by
    have : ((i : ℕ) + 1 : ℝ≥0) < ((j : ℕ) + 1 : ℝ≥0) := by
      exact_mod_cast Nat.add_lt_add_right (Fin.lt_def.mp hij) 1
    exact mul_lt_mul_of_pos_right this hg

theorem sgConv_gridTimes_apply (g : ℝ≥0) (hg : 0 < g) (J : ℕ) (i : Fin J) :
    sgConv_gridTimes g hg J i = ((i : ℕ) + 1 : ℝ≥0) * g := rfl

theorem sgConv_gridTimes_relativeTail (g : ℝ≥0) (hg : 0 < g) (J : ℕ) :
    (sgConv_gridTimes g hg (J + 1)).relativeTail = sgConv_gridTimes g hg J := by
  apply DFunLike.ext _ _
  intro i
  rw [FiniteOrderedTimes.relativeTail_apply]
  show (((i.succ : Fin (J + 1)) : ℕ) + 1 : ℝ≥0) * g - (((0 : Fin (J + 1)) : ℕ) + 1 : ℝ≥0) * g =
    ((i : ℕ) + 1 : ℝ≥0) * g
  simp only [Fin.val_succ, Fin.val_zero]
  refine tsub_eq_of_eq_add ?_
  push_cast
  ring

theorem sgConv_gridTimes_zero (g : ℝ≥0) (hg : 0 < g) (J : ℕ) :
    sgConv_gridTimes g hg (J + 1) 0 = g := by
  rw [sgConv_gridTimes_apply]; simp

/-- The `J`-step chain of a transition kernel `p`: the law of `(X₁, …, X_J)` from the start. -/
noncomputable def sgConv_chain (p : Kernel α α) : (J : ℕ) → Kernel α (Fin J → α)
  | 0 => Kernel.const α (Measure.dirac (FiniteOrderedTimes.emptyPath α))
  | J + 1 => Kernel.mapOfMeasurable (p ⊗ₖ Kernel.prodMkLeft α (sgConv_chain p J))
      (fun z ↦ @Fin.cons J (fun _ : Fin (J + 1) ↦ α) z.1 z.2) measurable_finCons

/-- The finite-time kernel on the uniform grid is the chain of the time-`g` kernel. -/
theorem sgConv_finiteTimeKernel_grid (S : SubMarkovKernelSemigroup α) (g : ℝ≥0) (hg : 0 < g)
    (J : ℕ) : finiteTimeKernel S (sgConv_gridTimes g hg J) = sgConv_chain (S g) J := by
  induction J with
  | zero => rfl
  | succ J ih =>
    rw [finiteTimeKernel_succ, sgConv_gridTimes_relativeTail, ih, sgConv_gridTimes_zero]
    rfl

theorem sgConv_chain_succ (p : Kernel α α) (J : ℕ) :
    sgConv_chain p (J + 1) = Kernel.mapOfMeasurable
      (p ⊗ₖ Kernel.prodMkLeft α (sgConv_chain p J))
      (fun z ↦ @Fin.cons J (fun _ : Fin (J + 1) ↦ α) z.1 z.2) measurable_finCons := rfl

instance sgConv_chain_isMarkovKernel (p : Kernel α α) [IsMarkovKernel p] (J : ℕ) :
    IsMarkovKernel (sgConv_chain p J) := by
  induction J with
  | zero => unfold sgConv_chain; infer_instance
  | succ J ih =>
    rw [sgConv_chain_succ, Kernel.mapOfMeasurable_eq_map]
    exact Kernel.IsMarkovKernel.map _ measurable_finCons

/-- **Peeling the first step.**  The expectation of a functional of the `J+1`-step chain is the
expectation over the first step of the expectation of the functional of the remaining `J`-step
chain started there. -/
theorem sgConv_lintegral_chain_succ (p : Kernel α α) [IsMarkovKernel p] {J : ℕ}
    (F : (Fin (J + 1) → α) → ℝ≥0∞) (hF : Measurable F) (y : α) :
    ∫⁻ w, F w ∂sgConv_chain p (J + 1) y =
      ∫⁻ z, ∫⁻ v, F (Fin.cons z v) ∂sgConv_chain p J z ∂p y := by
  rw [sgConv_chain_succ, Kernel.mapOfMeasurable_eq_map, Kernel.map_apply _ measurable_finCons,
    lintegral_map hF measurable_finCons,
    Kernel.lintegral_compProd _ _ _ (f := fun a : α × (Fin J → α) ↦ F (Fin.cons a.1 a.2))
      (hF.comp measurable_finCons)]
  simp only [Kernel.prodMkLeft_apply]

end Chain

end
end SuperdiffusionCLT.Section8.Convergence
