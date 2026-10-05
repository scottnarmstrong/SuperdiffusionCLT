/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Convergence.SemigroupTightnessC

/-!
# Short gaps between markers of a grid chain

Along a chain killed outside a set `K`, a *marker* is a step ending at distance at least `r`
from the current anchor, which is then reset to the endpoint of that step.  The probability that two
consecutive markers are at most `δ` steps apart is bounded by a first-passage recursion, in terms
of the Ottaviani bound of `SemigroupTightnessC` for the time to the first marker, by a geometric
sum (`sgConv_xi_le_pow`).  On the deterministic side (`sgConv_comb`), a tuple with no short gap
and no step of size `r` moves by less than `4r` over every window of `δ` steps.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.Convergence
open Filter Homogenization MeasureTheory ProbabilityTheory Topology
open MarkovProcess MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal NNReal ZeroAtInfty
noncomputable section

section Bad

variable {α : Type*} [MetricSpace α] [MeasurableSpace α] [BorelSpace α]
  [SecondCountableTopology α]

open Classical in
/-- Indicator of a short gap between consecutive `r`-markers of the chain killed outside `K`:
the anchor is `a`, and `e` steps have elapsed since it was set; a marker is a step that lands at
distance at least `r` from the anchor, and it is short if the elapsed time is at most `δ`. -/
def sgConv_bad (K : Set α) (r : ℝ) (δ : ℕ) : (J : ℕ) → ℕ → α → (Fin J → α) → ℝ≥0∞
  | 0, _, _, _ => 0
  | J + 1, e, a, w => if w 0 ∈ K then
      (if r ≤ dist (w 0) a then
        (if e + 1 ≤ δ then 1 else sgConv_bad K r δ J 0 (w 0) (Fin.tail w))
      else sgConv_bad K r δ J (e + 1) a (Fin.tail w)) else 0

open Classical in
omit [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α] in
theorem sgConv_bad_succ (K : Set α) (r : ℝ) (δ J e : ℕ) (a : α) (w : Fin (J + 1) → α) :
    sgConv_bad K r δ (J + 1) e a w = if w 0 ∈ K then
      (if r ≤ dist (w 0) a then
        (if e + 1 ≤ δ then 1 else sgConv_bad K r δ J 0 (w 0) (Fin.tail w))
      else sgConv_bad K r δ J (e + 1) a (Fin.tail w)) else 0 := rfl

open Classical in
theorem measurable_sgConv_bad {K : Set α} (hK : MeasurableSet K) (r : ℝ) (δ J : ℕ) :
    ∀ e : ℕ, Measurable (fun q : α × (Fin J → α) ↦ sgConv_bad K r δ J e q.1 q.2) := by
  induction J with
  | zero => intro e; exact measurable_const
  | succ J ih =>
    intro e
    have h0 : Measurable (fun q : α × (Fin (J + 1) → α) ↦ q.2 0) :=
      (measurable_pi_apply 0).comp measurable_snd
    simp only [sgConv_bad_succ]
    refine Measurable.ite (hK.preimage h0) (Measurable.ite ?_ (Measurable.ite
      (MeasurableSet.const _) measurable_const ?_) ?_) measurable_const
    · exact measurableSet_le measurable_const (h0.dist measurable_fst)
    · exact (ih 0).comp (h0.prodMk (sgConv_measurable_tail.comp measurable_snd))
    · exact (ih (e + 1)).comp (measurable_fst.prodMk (sgConv_measurable_tail.comp measurable_snd))

/-- The probability of a short gap for the chain from `y`. -/
def sgConv_xi (p : Kernel α α) (K : Set α) (r : ℝ) (δ J e : ℕ) (y a : α) : ℝ≥0∞ :=
  ∫⁻ w, sgConv_bad K r δ J e a w ∂sgConv_chain p J y

omit [BorelSpace α] [SecondCountableTopology α] in
theorem sgConv_xi_zero (p : Kernel α α) (K : Set α) (r : ℝ) (δ e : ℕ) (y a : α) :
    sgConv_xi p K r δ 0 e y a = 0 := by
  simp [sgConv_xi, sgConv_bad]

open Classical in
theorem sgConv_xi_succ (p : Kernel α α) [IsMarkovKernel p] {K : Set α} (hK : MeasurableSet K)
    (r : ℝ) (δ J e : ℕ) (y a : α) :
    sgConv_xi p K r δ (J + 1) e y a = ∫⁻ z, (if z ∈ K then
      (if r ≤ dist z a then (if e + 1 ≤ δ then 1 else sgConv_xi p K r δ J 0 z z)
        else sgConv_xi p K r δ J (e + 1) z a) else 0) ∂p y := by
  unfold sgConv_xi
  have hmeas : Measurable (fun w : Fin (J + 1) → α ↦ sgConv_bad K r δ (J + 1) e a w) :=
    (measurable_sgConv_bad hK r δ (J + 1) e).comp (measurable_const.prodMk measurable_id)
  rw [sgConv_lintegral_chain_succ p _ hmeas y]
  refine lintegral_congr fun z ↦ ?_
  simp only [sgConv_bad_succ, Fin.cons_zero, Fin.tail_cons]
  by_cases hz : z ∈ K
  · by_cases hd : r ≤ dist z a
    · by_cases he : e + 1 ≤ δ
      · simp [hz, hd, he]
      · simp [hz, hd, he]
    · simp [hz, hd]
  · simp [hz]

open Classical in
theorem sgConv_xi_mono (p : Kernel α α) [IsMarkovKernel p] {K : Set α} (hK : MeasurableSet K)
    (r : ℝ) (δ : ℕ) : ∀ (J e : ℕ) (y a : α),
    sgConv_xi p K r δ J e y a ≤ sgConv_xi p K r δ (J + 1) e y a := by
  intro J
  induction J with
  | zero => intro e y a; simp [sgConv_xi_zero]
  | succ J ih =>
    intro e y a
    rw [sgConv_xi_succ p hK, sgConv_xi_succ p hK]
    refine lintegral_mono fun z ↦ ?_
    by_cases hz : z ∈ K
    · by_cases hd : r ≤ dist z a
      · by_cases he : e + 1 ≤ δ
        · simp [hz, hd, he]
        · simp only [hz, hd, he, ↓reduceIte]
          exact ih 0 z z
      · simp only [hz, hd, ↓reduceIte]
        exact ih (e + 1) z a
    · simp [hz]

/-- The worst-case probability of a short gap, over starting points in `K`. -/
def sgConv_gbar (p : Kernel α α) (K : Set α) (r : ℝ) (δ J : ℕ) : ℝ≥0∞ :=
  ⨆ a ∈ K, sgConv_xi p K r δ J 0 a a

theorem sgConv_gbar_mono (p : Kernel α α) [IsMarkovKernel p] {K : Set α} (hK : MeasurableSet K)
    (r : ℝ) (δ : ℕ) : Monotone (sgConv_gbar p K r δ) := by
  refine monotone_nat_of_le_succ fun J ↦ ?_
  unfold sgConv_gbar
  exact iSup₂_mono fun a _ ↦ sgConv_xi_mono p hK r δ J 0 a a

omit [BorelSpace α] [SecondCountableTopology α] in
theorem sgConv_xi_le_gbar (p : Kernel α α) (K : Set α) (r : ℝ) (δ J : ℕ) {a : α} (ha : a ∈ K) :
    sgConv_xi p K r δ J 0 a a ≤ sgConv_gbar p K r δ J :=
  le_iSup₂ (f := fun a (_ : a ∈ K) ↦ sgConv_xi p K r δ J 0 a a) a ha

omit [BorelSpace α] [SecondCountableTopology α] in
theorem sgConv_gbar_zero (p : Kernel α α) (K : Set α) (r : ℝ) (δ : ℕ) :
    sgConv_gbar p K r δ 0 = 0 := by
  simp [sgConv_gbar, sgConv_xi_zero]

open Classical in
/-- The integrand of the hitting probability: one step, then continue. -/
def sgConv_zi (p : Kernel α α) (K : Set α) (r : ℝ) (m : ℕ) (a z : α) : ℝ≥0∞ :=
  if m = 0 then 0 else if z ∈ K then
    (if r ≤ dist z a then 1 else sgConv_zeta p K r (m - 1) z a) else 0

theorem measurable_sgConv_zeta_left (p : Kernel α α) [IsMarkovKernel p] {K : Set α}
    (hK : MeasurableSet K) (r : ℝ) (m : ℕ) (a : α) :
    Measurable (fun y ↦ sgConv_zeta p K r m y a) :=
  Measurable.lintegral_kernel (κ := sgConv_chain p m)
    ((measurable_sgConv_hit hK r m).comp (measurable_const.prodMk measurable_id))

open Classical in
theorem measurable_sgConv_zi (p : Kernel α α) [IsMarkovKernel p] {K : Set α}
    (hK : MeasurableSet K) (r : ℝ) (m : ℕ) (a : α) : Measurable (sgConv_zi p K r m a) := by
  unfold sgConv_zi
  by_cases hm : m = 0
  · simp only [hm, ↓reduceIte]; exact measurable_const
  · simp only [hm, ↓reduceIte]
    exact Measurable.ite hK (Measurable.ite (measurableSet_le measurable_const
      (measurable_id.dist measurable_const)) measurable_const
      (measurable_sgConv_zeta_left p hK r (m - 1) a)) measurable_const

open Classical in
theorem sgConv_zeta_eq_lintegral_zi (p : Kernel α α) [IsMarkovKernel p] {K : Set α}
    (hK : MeasurableSet K) (r : ℝ) (m : ℕ) (y a : α) :
    sgConv_zeta p K r m y a = ∫⁻ z, sgConv_zi p K r m a z ∂p y := by
  cases m with
  | zero => simp [sgConv_zeta_zero, sgConv_zi]
  | succ m =>
    rw [sgConv_zeta_succ p hK]
    refine lintegral_congr fun z ↦ ?_
    simp [sgConv_zi]

open Classical in
omit [BorelSpace α] [SecondCountableTopology α] in
theorem sgConv_zi_of_not_marker (p : Kernel α α) (K : Set α) (r : ℝ) (m : ℕ) {a z : α}
    (hz : z ∈ K) (hd : ¬ r ≤ dist z a) :
    sgConv_zi p K r m a z = sgConv_zeta p K r (m - 1) z a := by
  by_cases hm : m = 0
  · simp [sgConv_zi, hm, sgConv_zeta_zero]
  · simp [sgConv_zi, hm, hz, hd]

open Classical in
omit [BorelSpace α] [SecondCountableTopology α] in
theorem sgConv_zi_of_marker (p : Kernel α α) (K : Set α) (r : ℝ) {m : ℕ} (hm : m ≠ 0) {a z : α}
    (hz : z ∈ K) (hd : r ≤ dist z a) : sgConv_zi p K r m a z = 1 := by
  simp [sgConv_zi, hm, hz, hd]

open Classical in
/-- **The first-passage bound for the short-gap probability.**  For every state `(y, a, e)`: the
short-gap probability is at most the probability of a marker within `m₁` steps (when `m₁` covers
the remaining short budget `δ - e`), plus the probability of a marker within `m₂` steps times a
bound for what follows a marker, plus a bound for what follows a marker after more than `m₂`
steps. -/
theorem sgConv_xi_le_aux (p : Kernel α α) [IsMarkovKernel p] {K : Set α} (hK : MeasurableSet K)
    (r : ℝ) (δ : ℕ) : ∀ (J e m₁ m₂ : ℕ) (g₁ g₂ : ℝ≥0∞) (y a : α), δ ≤ e + m₁ →
      (1 ≤ m₂ → sgConv_gbar p K r δ (J - 1) ≤ g₁) → sgConv_gbar p K r δ (J - 1 - m₂) ≤ g₂ →
      sgConv_xi p K r δ J e y a ≤
        sgConv_zeta p K r m₁ y a + sgConv_zeta p K r m₂ y a * g₁ + g₂ := by
  intro J
  induction J with
  | zero => intro e m₁ m₂ g₁ g₂ y a _ _ _; simp [sgConv_xi_zero]
  | succ J ih =>
    intro e m₁ m₂ g₁ g₂ y a h1 h2a h2b
    have hmono := sgConv_gbar_mono p hK r δ
    rw [sgConv_xi_succ p hK, sgConv_zeta_eq_lintegral_zi p hK, sgConv_zeta_eq_lintegral_zi p hK]
    have hsum : ∫⁻ z, sgConv_zi p K r m₁ a z ∂p y + (∫⁻ z, sgConv_zi p K r m₂ a z ∂p y) * g₁ + g₂ =
        ∫⁻ z, (sgConv_zi p K r m₁ a z + sgConv_zi p K r m₂ a z * g₁ + g₂) ∂p y := by
      rw [lintegral_add_right _ measurable_const, lintegral_add_left (measurable_sgConv_zi p hK r m₁ a),
        lintegral_mul_const _ (measurable_sgConv_zi p hK r m₂ a), lintegral_const, measure_univ,
        mul_one]
    rw [hsum]
    refine lintegral_mono fun z ↦ ?_
    by_cases hz : z ∈ K
    · by_cases hd : r ≤ dist z a
      · by_cases he : e + 1 ≤ δ
        · simp only [hz, hd, he, ↓reduceIte]
          have hm1 : m₁ ≠ 0 := by omega
          rw [sgConv_zi_of_marker p K r hm1 hz hd]
          exact le_add_right (le_add_right le_rfl)
        · simp only [hz, hd, he, ↓reduceIte]
          have hx := sgConv_xi_le_gbar p K r δ J hz
          by_cases hm2 : m₂ = 0
          · have h3 : sgConv_gbar p K r δ J ≤ g₂ := by
              have := h2b; subst hm2; simpa using this
            exact (hx.trans h3).trans le_add_self
          · have h3 : sgConv_gbar p K r δ J ≤ g₁ := by
              have := h2a (Nat.one_le_iff_ne_zero.mpr hm2); simpa using this
            rw [sgConv_zi_of_marker p K r hm2 hz hd, one_mul]
            exact (hx.trans h3).trans ((le_add_self).trans (le_add_right le_rfl))
      · simp only [hz, hd, ↓reduceIte]
        rw [sgConv_zi_of_not_marker p K r m₁ hz hd, sgConv_zi_of_not_marker p K r m₂ hz hd]
        refine ih (e + 1) (m₁ - 1) (m₂ - 1) g₁ g₂ z a (by omega) (fun h ↦ ?_) ?_
        · have h' := h2a (by omega)
          exact (hmono (by omega : J - 1 ≤ J + 1 - 1)).trans h'
        · exact (hmono (by omega : J - 1 - (m₂ - 1) ≤ J + 1 - 1 - m₂)).trans h2b
    · simp [hz]

theorem sgConv_gbar_le_rec (p : Kernel α α) [IsMarkovKernel p] {K : Set α} (hK : MeasurableSet K)
    (r : ℝ) (δ H : ℕ) {A u : ℝ≥0∞} (hA : ∀ a ∈ K, sgConv_zeta p K r δ a a ≤ A)
    (hu : ∀ a ∈ K, sgConv_zeta p K r H a a ≤ u) (J : ℕ) :
    sgConv_gbar p K r δ J ≤
      A + u * sgConv_gbar p K r δ (J - 1) + sgConv_gbar p K r δ (J - 1 - H) := by
  unfold sgConv_gbar
  refine iSup₂_le fun a ha ↦ ?_
  have h := sgConv_xi_le_aux p hK r δ J 0 δ H (sgConv_gbar p K r δ (J - 1))
    (sgConv_gbar p K r δ (J - 1 - H)) a a (by omega) (fun _ ↦ le_rfl) le_rfl
  refine h.trans ?_
  exact add_le_add (add_le_add (hA a ha) (mul_le_mul_left (hu a ha) _)) le_rfl

/-- The recursion `b (k+1) = 2 (A + b k)`. -/
def sgConv_bseq (A : ℝ≥0∞) : ℕ → ℝ≥0∞
  | 0 => 0
  | k + 1 => 2 * (A + sgConv_bseq A k)

theorem sgConv_bseq_add (A : ℝ≥0∞) (k : ℕ) : sgConv_bseq A k + 2 * A = 2 ^ (k + 1) * A := by
  induction k with
  | zero => simp [sgConv_bseq]
  | succ k ih =>
    calc sgConv_bseq A (k + 1) + 2 * A = 2 * (sgConv_bseq A k + 2 * A) := by
          simp only [sgConv_bseq]; ring
      _ = 2 ^ (k + 1 + 1) * A := by rw [ih]; ring

theorem sgConv_gbar_le (p : Kernel α α) [IsMarkovKernel p] {K : Set α} (hK : MeasurableSet K)
    (r : ℝ) (δ H : ℕ) {A u : ℝ≥0∞} (hu2 : u ≤ 2⁻¹)
    (hA : ∀ a ∈ K, sgConv_zeta p K r δ a a ≤ A)
    (hu : ∀ a ∈ K, sgConv_zeta p K r H a a ≤ u) :
    ∀ k J : ℕ, J < k * H → sgConv_gbar p K r δ J ≤ sgConv_bseq A k := by
  intro k
  induction k with
  | zero => intro J hJ; omega
  | succ k ih =>
    intro J
    induction J using Nat.strong_induction_on with
    | _ J ihJ =>
      intro hJ
      have hJ' : J < k * H + H := by rw [Nat.succ_mul] at hJ; exact hJ
      rcases Nat.eq_zero_or_pos J with h0 | hpos
      · subst h0; simp [sgConv_gbar_zero]
      · have hrec := sgConv_gbar_le_rec p hK r δ H hA hu J
        have h1 : sgConv_gbar p K r δ (J - 1) ≤ sgConv_bseq A (k + 1) :=
          ihJ (J - 1) (by omega) (by rw [Nat.succ_mul]; omega)
        have h2 : sgConv_gbar p K r δ (J - 1 - H) ≤ sgConv_bseq A k := by
          rcases Nat.eq_zero_or_pos (J - 1 - H) with h | h
          · rw [h, sgConv_gbar_zero]; exact zero_le
          · exact ih (J - 1 - H) (by omega)
        refine hrec.trans ?_
        have h3 : A + u * sgConv_gbar p K r δ (J - 1) + sgConv_gbar p K r δ (J - 1 - H) ≤
            A + 2⁻¹ * sgConv_bseq A (k + 1) + sgConv_bseq A k :=
          add_le_add (add_le_add le_rfl (mul_le_mul' hu2 h1)) h2
        refine h3.trans (le_of_eq ?_)
        have h4 : 2⁻¹ * sgConv_bseq A (k + 1) = A + sgConv_bseq A k := by
          simp only [sgConv_bseq]
          rw [← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
        rw [h4]
        simp only [sgConv_bseq]
        ring

/-- **Bound for the short-gap probability.** -/
theorem sgConv_xi_le_pow (p : Kernel α α) [IsMarkovKernel p] {K : Set α} (hK : MeasurableSet K)
    (r : ℝ) (δ H : ℕ) {A u : ℝ≥0∞} (hu2 : u ≤ 2⁻¹)
    (hA : ∀ a ∈ K, sgConv_zeta p K r δ a a ≤ A)
    (hu : ∀ a ∈ K, sgConv_zeta p K r H a a ≤ u) (k J : ℕ) (hJ : J < k * H) {a : α} (ha : a ∈ K) :
    sgConv_xi p K r δ J 0 a a ≤ 2 ^ (k + 1) * A :=
  ((sgConv_xi_le_gbar p K r δ J ha).trans (sgConv_gbar_le p hK r δ H hu2 hA hu k J hJ)).trans
    (le_trans le_self_add (le_of_eq (sgConv_bseq_add A k)))

end Bad
section Pt
variable {α : Type*}

open Classical in
/-- The `j`-th point of the extended sequence `y, w 0, …, w (J-1)`. -/
def sgConv_pt {J : ℕ} (y : α) (w : Fin J → α) (j : ℕ) : α :=
  if j = 0 then y else if h' : j - 1 < J then w ⟨j - 1, h'⟩ else y

theorem sgConv_pt_zero {J : ℕ} (y : α) (w : Fin J → α) : sgConv_pt y w 0 = y := by
  simp [sgConv_pt]

theorem sgConv_pt_succ {J : ℕ} (y : α) (w : Fin (J + 1) → α) {j : ℕ} (hj : j ≤ J) :
    sgConv_pt y w (j + 1) = sgConv_pt (w 0) (Fin.tail w) j := by
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h
    simp [sgConv_pt]
  · have h1 : j ≠ 0 := by omega
    have h2 : j - 1 < J := by omega
    simp only [sgConv_pt, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false,
      Nat.add_sub_cancel, h1, h2, dite_true]
    have hlt : j < J + 1 := by omega
    simp only [hlt, dite_true, Fin.tail]
    congr 1
    refine Fin.ext ?_
    simp only [Fin.val_succ]
    omega

end Pt

section Comb

variable {α : Type*} [MetricSpace α] [MeasurableSpace α] [BorelSpace α]
  [SecondCountableTopology α]

omit [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α] in
theorem sgConv_comb_window {J L δ : ℕ} {r : ℝ} {a y : α} (w : Fin (J + 1) → α)
    (hya : dist y a < r)
    (hb : ∀ j ≤ L + 1, j ≤ δ → dist (sgConv_pt y w j) a < 3 * r)
    (hc : ∀ i j, i < j → j ≤ L → j - i ≤ δ →
      dist (sgConv_pt (w 0) (Fin.tail w) i) (sgConv_pt (w 0) (Fin.tail w) j) < 4 * r)
    (hLJ : L ≤ J) :
    ∀ i j, i < j → j ≤ L + 1 → j - i ≤ δ → dist (sgConv_pt y w i) (sgConv_pt y w j) < 4 * r := by
  intro i j hij hj hjd
  rcases i with _ | i
  · rw [sgConv_pt_zero]
    have h1 := hb j hj (by omega)
    have h2 := dist_triangle y a (sgConv_pt y w j)
    linarith only [hya, h1, h2, dist_comm a (sgConv_pt y w j)]
  · rcases j with _ | j
    · omega
    · rw [sgConv_pt_succ y w (by omega), sgConv_pt_succ y w (by omega)]
      exact hc i j (by omega) (by omega) (by omega)

open Classical in
omit [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α] in
/-- **Deterministic content of the marker construction.**  If the first `L` steps of a tuple stay
in `K`, take no step of size `r` or more, and the tuple has no short gap between consecutive
`r`-markers (`bad = 0`), then over every window of at most `δ` steps inside the first `L` steps it
moves by less than `4r`. -/
theorem sgConv_comb (K : Set α) {r : ℝ} (hr : 0 < r) (δ : ℕ) : ∀ (J L e : ℕ) (a y : α)
    (w : Fin J → α), L ≤ J → dist y a < r → (∀ j ≤ L, sgConv_pt y w j ∈ K) →
    (∀ j < L, dist (sgConv_pt y w (j + 1)) (sgConv_pt y w j) < r) →
    sgConv_bad K r δ J e a w = 0 →
    (∀ j ≤ L, j + e ≤ δ → dist (sgConv_pt y w j) a < r) ∧
    (∀ j ≤ L, j ≤ δ → dist (sgConv_pt y w j) a < 3 * r) ∧
    (∀ i j, i < j → j ≤ L → j - i ≤ δ → dist (sgConv_pt y w i) (sgConv_pt y w j) < 4 * r) := by
  intro J
  induction J with
  | zero =>
    intro L e a y w hL hya _ _ _
    refine ⟨fun j hj _ ↦ ?_, fun j hj _ ↦ ?_, fun i j hij hj _ ↦ by omega⟩
    · have : j = 0 := by omega
      subst this; rwa [sgConv_pt_zero]
    · have : j = 0 := by omega
      subst this; rw [sgConv_pt_zero]; linarith only [hya, hr]
  | succ J ih =>
    intro L e a y w hLJ hya hK hjump hbad
    rcases Nat.eq_zero_or_pos L with hL0 | hLpos
    · subst hL0
      refine ⟨fun j hj _ ↦ ?_, fun j hj _ ↦ ?_, fun i j hij hj _ ↦ by omega⟩
      · have : j = 0 := by omega
        subst this; rwa [sgConv_pt_zero]
      · have : j = 0 := by omega
        subst this; rw [sgConv_pt_zero]; linarith only [hya, hr]
    obtain ⟨L, rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
    have hpt1 : sgConv_pt y w 1 = w 0 := by
      rw [sgConv_pt_succ y w (Nat.zero_le J), sgConv_pt_zero]
    have hzK : w 0 ∈ K := hpt1 ▸ hK 1 (by omega)
    have hKv : ∀ j ≤ L, sgConv_pt (w 0) (Fin.tail w) j ∈ K := fun j hj ↦ by
      rw [← sgConv_pt_succ y w (by omega)]; exact hK (j + 1) (by omega)
    have hjv : ∀ j < L, dist (sgConv_pt (w 0) (Fin.tail w) (j + 1))
        (sgConv_pt (w 0) (Fin.tail w) j) < r := fun j hj ↦ by
      rw [← sgConv_pt_succ y w (by omega), ← sgConv_pt_succ y w (by omega)]
      exact hjump (j + 1) (by omega)
    have hjz : dist (w 0) y < r := by
      have := hjump 0 (by omega)
      rwa [hpt1, sgConv_pt_zero] at this
    rw [sgConv_bad_succ] at hbad
    simp only [hzK, ↓reduceIte] at hbad
    by_cases hd : r ≤ dist (w 0) a
    · simp only [hd, ↓reduceIte] at hbad
      by_cases he : e + 1 ≤ δ
      · simp [he] at hbad
      · simp only [he, ↓reduceIte] at hbad
        obtain ⟨Qa', -, Qc'⟩ := ih L 0 (w 0) (w 0) (Fin.tail w) (by omega) (by simp [hr]) hKv hjv
          hbad
        have hQa : ∀ j ≤ L + 1, j + e ≤ δ → dist (sgConv_pt y w j) a < r := by
          intro j hj hje
          rcases j with _ | j
          · rw [sgConv_pt_zero]; exact hya
          · omega
        have hQb : ∀ j ≤ L + 1, j ≤ δ → dist (sgConv_pt y w j) a < 3 * r := by
          intro j hj hjδ
          rcases j with _ | j
          · rw [sgConv_pt_zero]; linarith only [hya, hr]
          · rw [sgConv_pt_succ y w (by omega)]
            have h1 := Qa' j (by omega) (by omega)
            have h2 := dist_triangle (sgConv_pt (w 0) (Fin.tail w) j) (w 0) a
            have h3 := dist_triangle (w 0) y a
            linarith only [h1, h2, h3, hjz, hya]
        exact ⟨hQa, hQb, sgConv_comb_window w hya hQb Qc' (by omega)⟩
    · have hd' := not_le.mp hd
      simp only [hd, ↓reduceIte] at hbad
      obtain ⟨Qa', Qb', Qc'⟩ := ih L (e + 1) a (w 0) (Fin.tail w) (by omega) hd' hKv hjv hbad
      have hQa : ∀ j ≤ L + 1, j + e ≤ δ → dist (sgConv_pt y w j) a < r := by
        intro j hj hje
        rcases j with _ | j
        · rw [sgConv_pt_zero]; exact hya
        · rw [sgConv_pt_succ y w (by omega)]
          exact Qa' j (by omega) (by omega)
      have hQb : ∀ j ≤ L + 1, j ≤ δ → dist (sgConv_pt y w j) a < 3 * r := by
        intro j hj hjδ
        rcases j with _ | j
        · rw [sgConv_pt_zero]; linarith only [hya, hr]
        · rw [sgConv_pt_succ y w (by omega)]
          exact Qb' j (by omega) (by omega)
      exact ⟨hQa, hQb, sgConv_comb_window w hya hQb Qc' (by omega)⟩

end Comb

section GridBound

variable {α : Type*} [MetricSpace α] [MeasurableSpace α] [BorelSpace α]
  [SecondCountableTopology α]

open Classical in
omit [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α] in
theorem sgConv_bad_eq_zero_or_one (K : Set α) (r : ℝ) (δ : ℕ) :
    ∀ (J e : ℕ) (a : α) (w : Fin J → α), sgConv_bad K r δ J e a w = 0 ∨ sgConv_bad K r δ J e a w = 1
  | 0, _, _, _ => by simp [sgConv_bad]
  | J + 1, e, a, w => by
    rw [sgConv_bad_succ]
    split_ifs
    · exact Or.inr rfl
    · exact sgConv_bad_eq_zero_or_one K r δ J 0 _ _
    · exact sgConv_bad_eq_zero_or_one K r δ J (e + 1) a _
    · exact Or.inl rfl

/-- The coordinates of a path at the grid times `g, 2g, …, Jg`. -/
def sgConv_grid (g : ℝ≥0) (J : ℕ) (ω : ContinuousPath α) : Fin J → α :=
  fun i ↦ ω (((i : ℕ) + 1 : ℝ≥0) * g)

omit [SecondCountableTopology α] in
theorem measurable_sgConv_grid (g : ℝ≥0) (J : ℕ) :
    Measurable (sgConv_grid (α := α) g J) :=
  measurable_pi_iff.mpr fun _ ↦ ContinuousPath.measurable_coordinateProcess (alpha := α) _

omit [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α] in
theorem sgConv_pt_grid (g : ℝ≥0) (J : ℕ) (ω : ContinuousPath α) {l : ℕ} (hl : l ≤ J) :
    sgConv_pt (ω 0) (sgConv_grid g J ω) l = ω ((l : ℝ≥0) * g) := by
  rcases Nat.eq_zero_or_pos l with h | h
  · subst h; simp [sgConv_pt_zero]
  · have h1 : l ≠ 0 := by omega
    simp only [sgConv_pt, h1, ite_false, show l - 1 < J by omega, dite_true, sgConv_grid]
    congr 1
    have : ((l - 1 : ℕ) : ℝ≥0) + 1 = (l : ℝ≥0) := by
      have : ((l - 1 + 1 : ℕ) : ℝ≥0) = (l : ℝ≥0) := by rw [Nat.sub_add_cancel h]
      rw [← this]; push_cast; rfl
    rw [this]

/-- Almost surely the path starts at the starting point. -/
theorem sgConv_start_ae (S : SubMarkovKernelSemigroup α) (hSc : S.IsConservative) (x : α)
    {Q : Measure (ContinuousPath α)}
    (hfdd : ∀ I : Finset ℝ≥0, Q.map (ContinuousPath.finsetEvaluation I) =
      finiteSetKernel S I x) : Q {ω | ω 0 ≠ x} = 0 := by
  let times : FiniteOrderedTimes 1 := OrderEmbedding.ofStrictMono (fun _ ↦ (0 : ℝ≥0))
    (fun i j hij ↦ absurd hij (by simp [Subsingleton.elim i j]))
  have h1 := sgConv_map_finiteEvaluation_ordered S hSc x hfdd times
  have h2 : (Q.map (fun ω ↦ ω 0)) = S 0 x := by
    have hmeas : Measurable (fun ω : ContinuousPath α ↦ ω 0) :=
      ContinuousPath.measurable_coordinateProcess (alpha := α) 0
    have hev : (fun ω : ContinuousPath α ↦ ω 0) =
        (fun p : Fin 1 → α ↦ p 0) ∘ ContinuousPath.finiteEvaluation (fun i ↦ times i) := rfl
    rw [hev, ← Measure.map_map (measurable_pi_apply 0)
      (ContinuousPath.measurable_finiteEvaluation _), h1]
    have := finiteTimeKernel_one_map_eval S times
    rw [← Kernel.map_apply _ (measurable_pi_apply 0), this]
    rfl
  have hset : MeasurableSet {y : α | y ≠ x} := (measurableSet_singleton x).compl
  have hmeas : Measurable (fun ω : ContinuousPath α ↦ ω 0) :=
    ContinuousPath.measurable_coordinateProcess (alpha := α) 0
  have : {ω : ContinuousPath α | ω 0 ≠ x} = (fun ω : ContinuousPath α ↦ ω 0) ⁻¹' {y | y ≠ x} := rfl
  rw [this, ← Measure.map_apply hmeas hset, h2, SubMarkovKernelSemigroup.zero, Kernel.id_apply,
    Measure.dirac_apply' _ hset]
  simp

/-- **Short-gap bound for a path law.**  The probability that the grid chain of a path law with the
finite-dimensional distributions of `S` from `x ∈ K` has a short gap between consecutive
`r`-markers is at most `2^(k+1) A`, provided the displacement tails of `S` over the times up to
`δ` and `H` grid steps are small. -/
theorem sgConv_grid_bad_le (S : SubMarkovKernelSemigroup α) (hSc : S.IsConservative) {x : α}
    {Q : Measure (ContinuousPath α)}
    (hfdd : ∀ I : Finset ℝ≥0, Q.map (ContinuousPath.finsetEvaluation I) =
      finiteSetKernel S I x) {K : Set α} (hK : MeasurableSet K) (hx : x ∈ K) (g : ℝ≥0)
    (hg : 0 < g) (r : ℝ) (δ H k J : ℕ) {A u : ℝ≥0∞} (hu2 : u ≤ 2⁻¹)
    (hA : ∀ a ∈ K, sgConv_zeta (S g) K r δ a a ≤ A)
    (hu : ∀ a ∈ K, sgConv_zeta (S g) K r H a a ≤ u) (hJ : J < k * H) :
    Q {ω | sgConv_bad K r δ J 0 x (sgConv_grid g J ω) ≠ 0} ≤ 2 ^ (k + 1) * A := by
  have : IsMarkovKernel (S g) := hSc.isMarkovKernel g
  have hmapΦ : Q.map (sgConv_grid g J) = sgConv_chain (S g) J x := by
    have h1 := sgConv_map_finiteEvaluation_ordered S hSc x hfdd (sgConv_gridTimes g hg J)
    rw [sgConv_finiteTimeKernel_grid] at h1
    exact h1
  have hbm : Measurable (fun w : Fin J → α ↦ sgConv_bad K r δ J 0 x w) :=
    (measurable_sgConv_bad hK r δ J 0).comp (measurable_const.prodMk measurable_id)
  have hset : MeasurableSet {w : Fin J → α | sgConv_bad K r δ J 0 x w ≠ 0} :=
    (measurableSet_singleton (0 : ℝ≥0∞)).compl.preimage hbm
  have hpre : {ω : ContinuousPath α | sgConv_bad K r δ J 0 x (sgConv_grid g J ω) ≠ 0} =
      sgConv_grid g J ⁻¹' {w | sgConv_bad K r δ J 0 x w ≠ 0} := rfl
  rw [hpre, ← Measure.map_apply (measurable_sgConv_grid g J) hset, hmapΦ]
  calc sgConv_chain (S g) J x {w | sgConv_bad K r δ J 0 x w ≠ 0}
      = ∫⁻ w, Set.indicator {w | sgConv_bad K r δ J 0 x w ≠ 0} 1 w ∂sgConv_chain (S g) J x := by
        rw [lintegral_indicator_one hset]
    _ ≤ ∫⁻ w, sgConv_bad K r δ J 0 x w ∂sgConv_chain (S g) J x := by
        refine lintegral_mono fun w ↦ ?_
        by_cases hw : sgConv_bad K r δ J 0 x w ≠ 0
        · rw [Set.indicator_of_mem (show w ∈ {w | sgConv_bad K r δ J 0 x w ≠ 0} from hw)]
          rcases sgConv_bad_eq_zero_or_one K r δ J 0 x w with h | h
          · exact absurd h hw
          · simp [h]
        · rw [Set.indicator_of_notMem (show w ∉ {w | sgConv_bad K r δ J 0 x w ≠ 0} from hw)]
          exact zero_le
    _ = sgConv_xi (S g) K r δ J 0 x x := rfl
    _ ≤ 2 ^ (k + 1) * A := sgConv_xi_le_pow (S g) hK r δ H hu2 hA hu k J hJ hx

end GridBound

end
end SuperdiffusionCLT.Section8.Convergence
