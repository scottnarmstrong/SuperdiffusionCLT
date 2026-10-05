/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Convergence.SemigroupTightnessB

/-!
# Ottaviani's inequality for the killed grid chain

For a Markov kernel `p` and its `m`-step chain, the probability `sgConv_zeta` of reaching
distance `r` from an anchor within `m` steps while staying in a set `K` is controlled by the
displacement tails of the chain (`sgConv_ottaviani`), and the displacement tails of the grid
chain of a conservative semigroup are those of the semigroup kernels (`sgConv_kappa_eq`).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.Convergence
open Filter Homogenization MeasureTheory ProbabilityTheory Topology
open MarkovProcess MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal NNReal ZeroAtInfty
noncomputable section

section Hit

variable {α : Type*} [MetricSpace α] [MeasurableSpace α] [BorelSpace α]
  [SecondCountableTopology α]

open Classical in
/-- Indicator that the chain, killed outside `K`, reaches distance `r` from the anchor `a`
within `m` steps. -/
def sgConv_hit (K : Set α) (r : ℝ) : (m : ℕ) → α → (Fin m → α) → ℝ≥0∞
  | 0, _, _ => 0
  | m + 1, a, w => if w 0 ∈ K then
      (if r ≤ dist (w 0) a then 1 else sgConv_hit K r m a (Fin.tail w)) else 0

open Classical in
omit [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α] in
theorem sgConv_hit_succ (K : Set α) (r : ℝ) (m : ℕ) (a : α) (w : Fin (m + 1) → α) :
    sgConv_hit K r (m + 1) a w = if w 0 ∈ K then
      (if r ≤ dist (w 0) a then 1 else sgConv_hit K r m a (Fin.tail w)) else 0 := rfl

omit [MetricSpace α] [BorelSpace α] [SecondCountableTopology α] in
theorem sgConv_measurable_tail {m : ℕ} :
    Measurable (fun w : Fin (m + 1) → α ↦ Fin.tail w) :=
  measurable_pi_iff.mpr fun i ↦ measurable_pi_apply i.succ

open Classical in
theorem measurable_sgConv_hit {K : Set α} (hK : MeasurableSet K) (r : ℝ) (m : ℕ) :
    Measurable (fun q : α × (Fin m → α) ↦ sgConv_hit K r m q.1 q.2) := by
  induction m with
  | zero => exact measurable_const
  | succ m ih =>
    have h0 : Measurable (fun q : α × (Fin (m + 1) → α) ↦ q.2 0) :=
      (measurable_pi_apply 0).comp measurable_snd
    simp only [sgConv_hit_succ]
    refine Measurable.ite (hK.preimage h0) (Measurable.ite ?_ measurable_const ?_) measurable_const
    · exact measurableSet_le measurable_const (h0.dist measurable_fst)
    · exact ih.comp (measurable_fst.prodMk (sgConv_measurable_tail.comp measurable_snd))

/-- The probability, for the chain from `y`, of reaching distance `r` from `a` within `m` steps
while staying in `K`. -/
def sgConv_zeta (p : Kernel α α) (K : Set α) (r : ℝ) (m : ℕ) (y a : α) : ℝ≥0∞ :=
  ∫⁻ w, sgConv_hit K r m a w ∂sgConv_chain p m y

omit [BorelSpace α] [SecondCountableTopology α] in
theorem sgConv_zeta_zero (p : Kernel α α) (K : Set α) (r : ℝ) (y a : α) :
    sgConv_zeta p K r 0 y a = 0 := by
  simp [sgConv_zeta, sgConv_hit]

open Classical in
theorem sgConv_zeta_succ (p : Kernel α α) [IsMarkovKernel p] {K : Set α} (hK : MeasurableSet K)
    (r : ℝ) (m : ℕ) (y a : α) :
    sgConv_zeta p K r (m + 1) y a = ∫⁻ z, (if z ∈ K then
      (if r ≤ dist z a then 1 else sgConv_zeta p K r m z a) else 0) ∂p y := by
  unfold sgConv_zeta
  have hmeas : Measurable (fun w : Fin (m + 1) → α ↦ sgConv_hit K r (m + 1) a w) :=
    (measurable_sgConv_hit hK r (m + 1)).comp (measurable_const.prodMk measurable_id)
  rw [sgConv_lintegral_chain_succ p _ hmeas y]
  refine lintegral_congr fun z ↦ ?_
  simp only [sgConv_hit_succ, Fin.cons_zero, Fin.tail_cons]
  by_cases hz : z ∈ K
  · by_cases hd : r ≤ dist z a
    · simp [hz, hd]
    · simp [hz, hd]
  · simp [hz]

/-- The state of the chain after `m` steps (`y` itself after zero steps). -/
def sgConv_last : (m : ℕ) → α → (Fin m → α) → α
  | 0, y, _ => y
  | m + 1, _, w => w (Fin.last m)

omit [MetricSpace α] [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α] in
theorem sgConv_last_cons (m : ℕ) (y z : α) (v : Fin m → α) :
    sgConv_last (m + 1) y (Fin.cons z v : Fin (m + 1) → α) = sgConv_last m z v := by
  cases m with
  | zero => rfl
  | succ m =>
    simp only [sgConv_last]
    rw [← Fin.succ_last, Fin.cons_succ]

omit [MetricSpace α] [BorelSpace α] [SecondCountableTopology α] in
theorem measurable_sgConv_last (m : ℕ) (y : α) : Measurable (sgConv_last m y) := by
  cases m with
  | zero => exact measurable_const
  | succ m => exact measurable_pi_apply (Fin.last m)

/-- The probability that the chain from `y` is at distance at least `ρ` from `a` after `m`
steps. -/
def sgConv_kappa (p : Kernel α α) (ρ : ℝ) (m : ℕ) (y a : α) : ℝ≥0∞ :=
  ∫⁻ w, (if ρ ≤ dist (sgConv_last m y w) a then 1 else 0) ∂sgConv_chain p m y

omit [BorelSpace α] [SecondCountableTopology α] in
theorem sgConv_kappa_zero (p : Kernel α α) [IsMarkovKernel p] (ρ : ℝ) (y a : α) :
    sgConv_kappa p ρ 0 y a = if ρ ≤ dist y a then 1 else 0 := by
  show ∫⁻ _w : Fin 0 → α, (if ρ ≤ dist y a then (1 : ℝ≥0∞) else 0) ∂sgConv_chain p 0 y = _
  rw [lintegral_const, measure_univ, mul_one]

theorem sgConv_kappa_succ (p : Kernel α α) [IsMarkovKernel p] (ρ : ℝ) (m : ℕ) (y a : α) :
    sgConv_kappa p ρ (m + 1) y a = ∫⁻ z, sgConv_kappa p ρ m z a ∂p y := by
  unfold sgConv_kappa
  have hmeas : Measurable (fun w : Fin (m + 1) → α ↦
      (if ρ ≤ dist (sgConv_last (m + 1) y w) a then (1 : ℝ≥0∞) else 0)) :=
    Measurable.ite (measurableSet_le measurable_const
      ((measurable_sgConv_last (m + 1) y).dist measurable_const)) measurable_const
      measurable_const
  rw [sgConv_lintegral_chain_succ p _ hmeas y]
  refine lintegral_congr fun z ↦ ?_
  simp only [sgConv_last_cons]

/-- If the chain started at `z` is at distance `2ρ` from `a`, then with probability at least one
minus its displacement tail it stays at distance at least `ρ` from `a`. -/
theorem sgConv_one_sub_kappa_le (p : Kernel α α) [IsMarkovKernel p] {ρ : ℝ} (m : ℕ) {z a : α}
    (h : 2 * ρ ≤ dist z a) : 1 - sgConv_kappa p ρ m z z ≤ sgConv_kappa p ρ m z a := by
  rw [tsub_le_iff_right]
  have : (1 : ℝ≥0∞) = ∫⁻ _w, 1 ∂sgConv_chain p m z := by simp
  unfold sgConv_kappa
  have hm1 : Measurable (fun w : Fin m → α ↦
      (if ρ ≤ dist (sgConv_last m z w) z then (1 : ℝ≥0∞) else 0)) :=
    Measurable.ite (measurableSet_le measurable_const
      ((measurable_sgConv_last m z).dist measurable_const)) measurable_const measurable_const
  rw [← lintegral_add_right _ hm1]
  rw [this]
  refine lintegral_mono fun w ↦ ?_
  by_cases hw : ρ ≤ dist (sgConv_last m z w) z
  · simp [hw]
  · have : ρ ≤ dist (sgConv_last m z w) a := by
      have h1 := dist_triangle z (sgConv_last m z w) a
      rw [dist_comm z (sgConv_last m z w)] at h1
      have hw' := not_le.mp hw
      linarith only [h, h1, hw']
    simp [hw, this]

open Classical in
/-- **Ottaviani's inequality for the killed chain.** -/
theorem sgConv_ottaviani (p : Kernel α α) [IsMarkovKernel p] {K : Set α} (hK : MeasurableSet K)
    {ρ : ℝ} {β : ℝ≥0∞} (m : ℕ)
    (hβ : ∀ z ∈ K, ∀ j ≤ m, sgConv_kappa p ρ j z z ≤ β) (y a : α) :
    (1 - β) * sgConv_zeta p K (2 * ρ) m y a ≤ sgConv_kappa p ρ m y a := by
  induction m generalizing y a with
  | zero => simp [sgConv_zeta_zero]
  | succ m ih =>
    rw [sgConv_zeta_succ p hK, sgConv_kappa_succ,
      ← lintegral_const_mul' _ _ (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)]
    refine lintegral_mono fun z ↦ ?_
    by_cases hz : z ∈ K
    · by_cases hd : 2 * ρ ≤ dist z a
      · simp only [hz, hd, ↓reduceIte, mul_one]
        exact (tsub_le_tsub_left (hβ z hz m (Nat.le_succ m)) 1).trans
          (sgConv_one_sub_kappa_le p m hd)
      · simp only [hz, hd, ↓reduceIte]
        exact ih (fun z' hz' j hj ↦ hβ z' hz' j (hj.trans (Nat.le_succ m))) z a
    · simp [hz]

/-- For a start point in `K` and tail probabilities at most `β ≤ 1/2`, the probability of
reaching distance `2ρ` within `m` steps is at most `2β`. -/
theorem sgConv_zeta_le_two_mul (p : Kernel α α) [IsMarkovKernel p] {K : Set α}
    (hK : MeasurableSet K) {ρ : ℝ} {β : ℝ≥0∞} (hβ2 : β ≤ 2⁻¹) (m : ℕ)
    (hβ : ∀ z ∈ K, ∀ j ≤ m, sgConv_kappa p ρ j z z ≤ β) {a : α} (ha : a ∈ K) :
    sgConv_zeta p K (2 * ρ) m a a ≤ 2 * β := by
  have h1 := sgConv_ottaviani p hK m hβ a a
  have h2 : sgConv_kappa p ρ m a a ≤ β := hβ a ha m le_rfl
  have h3 : 2⁻¹ ≤ 1 - β := by
    rw [← ENNReal.one_sub_inv_two]
    exact tsub_le_tsub_left hβ2 1
  have h4 : 2⁻¹ * sgConv_zeta p K (2 * ρ) m a a ≤ β :=
    (mul_le_mul_left h3 _).trans (h1.trans h2)
  calc sgConv_zeta p K (2 * ρ) m a a = 2 * (2⁻¹ * sgConv_zeta p K (2 * ρ) m a a) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
    _ ≤ 2 * β := mul_le_mul_right h4 _

/-- The tail probability of the grid chain is the tail of the semigroup kernel at the grid time. -/
theorem sgConv_kappa_eq (S : SubMarkovKernelSemigroup α) (hSc : S.IsConservative) (g : ℝ≥0)
    (ρ : ℝ) (a : α) : ∀ (j : ℕ) (z : α),
    sgConv_kappa (S g) ρ j z a = S ((j : ℝ≥0) * g) z {w | ρ ≤ dist w a}
  | 0, z => by
    have : IsMarkovKernel (S g) := hSc.isMarkovKernel g
    have hA : MeasurableSet {w : α | ρ ≤ dist w a} :=
      measurableSet_le measurable_const (measurable_id.dist measurable_const)
    rw [sgConv_kappa_zero]
    simp only [Nat.cast_zero, zero_mul, SubMarkovKernelSemigroup.zero, Kernel.id_apply,
      Measure.dirac_apply' _ hA]
    by_cases h : ρ ≤ dist z a <;> simp [h]
  | j + 1, z => by
    have : IsMarkovKernel (S g) := hSc.isMarkovKernel g
    have hA : MeasurableSet {w : α | ρ ≤ dist w a} :=
      measurableSet_le measurable_const (measurable_id.dist measurable_const)
    rw [sgConv_kappa_succ]
    have hadd : ((j + 1 : ℕ) : ℝ≥0) * g = g + (j : ℝ≥0) * g := by push_cast; ring
    rw [hadd, S.add, Kernel.comp_apply' _ _ _ hA]
    exact lintegral_congr fun z' ↦ sgConv_kappa_eq S hSc g ρ a j z'

end Hit
end
end SuperdiffusionCLT.Section8.Convergence
