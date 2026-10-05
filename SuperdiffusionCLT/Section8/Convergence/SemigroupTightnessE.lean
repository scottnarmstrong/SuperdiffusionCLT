/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Convergence.SemigroupTightnessD

/-!
# Uniform bound for the oscillation event along convergent semigroups

The concrete grids `1/(m+1)` and the floor/ceiling bookkeeping used to apply
`sgConv_modEvent_le` to a convergent sequence of semigroups.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.Convergence
open Filter Homogenization MeasureTheory ProbabilityTheory Topology
open MarkovProcess MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal NNReal ZeroAtInfty
noncomputable section

section Params

/-- The grid meshes `1/(m+1)`. -/
def sgConv_mesh (m : ℕ) : ℝ≥0 := ((m : ℝ≥0) + 1)⁻¹

theorem sgConv_mesh_pos (m : ℕ) : 0 < sgConv_mesh m := by
  unfold sgConv_mesh
  exact pos_iff_ne_zero.mpr (inv_ne_zero (Nat.cast_add_one_ne_zero m))

theorem sgConv_mesh_tendsto : Tendsto sgConv_mesh atTop (nhds 0) := by
  unfold sgConv_mesh
  have : Tendsto (fun m : ℕ ↦ ((m : ℝ≥0) + 1)) atTop atTop :=
    tendsto_atTop_mono (fun m ↦ le_self_add) (tendsto_natCast_atTop_atTop (R := ℝ≥0))
  exact this.inv_tendsto_atTop

theorem sgConv_mesh_le (m : ℕ) (δ : ℝ≥0) (hδ : 0 < δ) (M : ℕ) (hM : δ⁻¹ ≤ M) (hm : M ≤ m) :
    sgConv_mesh m ≤ δ := by
  unfold sgConv_mesh
  have h1 : δ⁻¹ ≤ (m : ℝ≥0) + 1 := hM.trans (by exact_mod_cast hm) |>.trans le_self_add
  exact (inv_le_comm₀ hδ (pos_iff_ne_zero.mpr (Nat.cast_add_one_ne_zero m))).mp h1

/-- The number of grid steps in `[0, T]` is smaller than `k` times the number of grid steps in
`[0, h]`, for `k > T / h + 1` and fine enough grids. -/
theorem sgConv_steps_lt (T h : ℝ≥0) (hh : 0 < h) :
    ∃ M : ℕ, ∀ m ≥ M, ⌊T / sgConv_mesh m⌋₊ < (⌈T / h⌉₊ + 2) * ⌊h / sgConv_mesh m⌋₊ := by
  set k : ℕ := ⌈T / h⌉₊ + 2 with hk
  have hkpos : (0 : ℝ≥0) < k := by positivity
  have hkT : T / h + 2 ≤ (k : ℝ≥0) := by
    have := Nat.le_ceil (T / h)
    rw [hk]; push_cast
    exact add_le_add this le_rfl
  obtain ⟨M, hM⟩ := exists_nat_ge ((h / k)⁻¹)
  refine ⟨M, fun m hm ↦ ?_⟩
  have hg := sgConv_mesh_pos m
  have hgle : sgConv_mesh m ≤ h / k := sgConv_mesh_le m (h / k) (by positivity) M hM hm
  set g := sgConv_mesh m with hgdef
  have h1 : h / g < (⌊h / g⌋₊ : ℝ≥0) + 1 := Nat.lt_floor_add_one (h / g)
  have h2 : (k : ℝ≥0) ≤ h / g := by
    rw [le_div_iff₀ hg]
    have := mul_le_mul_of_nonneg_left hgle (zero_le : 0 ≤ (k : ℝ≥0))
    calc (k : ℝ≥0) * g ≤ k * (h / k) := this
      _ = h := by field_simp
  have h3 : T / g + (k : ℝ≥0) < (k : ℝ≥0) * ⌊h / g⌋₊ + k := by
    calc T / g + k ≤ T / g + 2 * (h / g) :=
          add_le_add le_rfl (h2.trans (le_mul_of_one_le_left zero_le one_le_two))
      _ = (T / h + 2) * (h / g) := by field_simp
      _ ≤ k * (h / g) := mul_le_mul_of_nonneg_right hkT zero_le
      _ < k * ((⌊h / g⌋₊ : ℝ≥0) + 1) := by gcongr
      _ = k * ⌊h / g⌋₊ + k := by ring
  have h4 : T / g < (k : ℝ≥0) * ⌊h / g⌋₊ := (add_lt_add_iff_right _).mp h3
  have h5 : (⌊T / g⌋₊ : ℝ≥0) ≤ T / g := Nat.floor_le zero_le
  have h6 : (⌊T / g⌋₊ : ℝ≥0) < ((k * ⌊h / g⌋₊ : ℕ) : ℝ≥0) := by push_cast; exact h5.trans_lt h4
  exact_mod_cast h6

end Params
section Concrete

variable {α : Type*} [MetricSpace α] [ProperSpace α] [MeasurableSpace α] [BorelSpace α]
  [SecondCountableTopology α]

theorem sgConv_two_mul_ofReal_quarter : 2 * ENNReal.ofReal (1 / 4) ≤ 2⁻¹ := by
  have : (2 : ℝ≥0∞) * ENNReal.ofReal (1 / 4) = ENNReal.ofReal (1 / 2) := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  rw [this, one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
  simp

theorem sgConv_pow_mul_ofReal (k : ℕ) (η : ℝ) (hη : 0 ≤ η) :
    2 ^ (k + 1) * (2 * ENNReal.ofReal (η / 2 ^ (k + 3))) ≤ ENNReal.ofReal η := by
  have h1 : (2 : ℝ≥0∞) ^ (k + 1) * (2 * ENNReal.ofReal (η / 2 ^ (k + 3))) =
      ENNReal.ofReal (2 ^ (k + 1) * (2 * (η / 2 ^ (k + 3)))) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num)]
    simp
  rw [h1]
  refine ENNReal.ofReal_le_ofReal ?_
  have : (2 : ℝ) ^ (k + 1) * (2 * (η / 2 ^ (k + 3))) = η / 2 := by
    have h2 : (2 : ℝ) ^ (k + 3) = 2 ^ (k + 1) * 4 := by ring
    rw [h2]
    field_simp
    ring
  rw [this]; linarith only [hη]

theorem sgConv_ofReal_half : ENNReal.ofReal (1 / 2) = 2⁻¹ := by
  rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
  simp

omit [ProperSpace α] [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α] in
theorem sgConv_floor_mul_le (T g : ℝ≥0) (hg : 0 < g) : (⌊T / g⌋₊ : ℝ≥0) * g ≤ T := by
  have := Nat.floor_le (zero_le : 0 ≤ T / g)
  rwa [le_div_iff₀ hg] at this

omit [ProperSpace α] [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α] in
theorem sgConv_lt_floor_succ_mul (T g : ℝ≥0) (hg : 0 < g) :
    T < ((⌊T / g⌋₊ : ℝ≥0) + 1) * g := by
  have := Nat.lt_floor_add_one (T / g)
  rwa [div_lt_iff₀ hg] at this

omit [ProperSpace α] [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α] in
theorem sgConv_le_ceil_succ_mul (δ g : ℝ≥0) (hg : 0 < g) :
    δ + g ≤ ((⌈δ / g⌉₊ : ℝ≥0) + 1) * g := by
  have := Nat.le_ceil (δ / g)
  rw [div_le_iff₀ hg] at this
  rw [add_one_mul]
  exact add_le_add this le_rfl |>.trans' le_rfl

omit [ProperSpace α] [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α] in
theorem sgConv_ceil_mul_lt (δ g : ℝ≥0) (hg : 0 < g) :
    (⌈δ / g⌉₊ : ℝ≥0) * g < δ + g := by
  have := Nat.ceil_lt_add_one (zero_le : 0 ≤ δ / g)
  have h2 := mul_lt_mul_of_pos_right this hg
  rwa [add_one_mul, div_mul_cancel₀ _ hg.ne'] at h2

/-- **Uniform oscillation bound along convergent semigroups.**  For path laws `Q n` with the
finite-dimensional distributions of `S n` from starting points `x n` in a compact set `K`, and
strongly convergent semigroups, the mass of the event of an oscillation larger than `4r` at some
small scale `δ` before time `T`, while staying in `K`, is at most `η` for all large `n`. -/
theorem sgConv_modEvent_le_semigroup
    {S : ℕ → SubMarkovKernelSemigroup α} {T₀ : SubMarkovKernelSemigroup α}
    (hS : ∀ n, (S n).IsFellerKernelSemigroup) (hSc : ∀ n, (S n).IsConservative)
    (hT : T₀.IsFellerKernelSemigroup)
    (hconv : ∀ (t : ℝ≥0) (f : C₀(α, ℝ)),
      Tendsto (fun n ↦ (hS n).c0Semigroup t f) atTop (nhds (hT.c0Semigroup t f)))
    {Q : ℕ → Measure (ContinuousPath α)} [∀ n, IsFiniteMeasure (Q n)] {x : ℕ → α}
    (hfdd : ∀ n (I : Finset ℝ≥0), (Q n).map (ContinuousPath.finsetEvaluation I) =
      finiteSetKernel (S n) I (x n))
    {K : Set α} (hK : IsCompact K) (hx : ∀ n, x n ∈ K) {r : ℝ} (hr : 0 < r) (T : ℝ≥0)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
      Q n (sgConv_modEvent K T δ (4 * r)) ≤ ENNReal.ofReal η := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  set η' : ℝ := min η 1 with hη'def
  have hη' : 0 < η' := lt_min hη one_pos
  obtain ⟨h₁, hh₁, n₁, hn₁⟩ := sgConv_small_time hS hSc hT hconv hK (r := r / 2) (ε := 1 / 4)
    (by positivity) (by norm_num)
  set k : ℕ := ⌈T / h₁⌉₊ + 2 with hk
  set ε₂ : ℝ := η' / 2 ^ (k + 3) with hε₂def
  have hε₂ : 0 < ε₂ := by positivity
  have hε₂half : ε₂ ≤ 1 / 2 := by
    have h8 : (8 : ℝ) ≤ 2 ^ (k + 3) := by
      calc (8 : ℝ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (k + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h1 : η' ≤ 1 := min_le_right _ _
    rw [hε₂def, div_le_iff₀ (by positivity)]
    linarith only [h8, h1]
  obtain ⟨h₂, hh₂, n₂, hn₂⟩ := sgConv_small_time hS hSc hT hconv hK (r := r / 2) (ε := ε₂)
    (by positivity) hε₂
  obtain ⟨M₁, hM₁⟩ := sgConv_steps_lt T h₁ hh₁
  set δ : ℝ≥0 := h₂ / 2 with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨M₂, hM₂⟩ := exists_nat_ge (δ⁻¹)
  refine ⟨δ, hδ, max n₁ n₂, fun n hn ↦ ?_⟩
  have hn1 : n₁ ≤ n := (le_max_left _ _).trans hn
  have hn2 : n₂ ≤ n := (le_max_right _ _).trans hn
  refine sgConv_modEvent_le (Q n) (sgConv_start_ae (S n) (hSc n) (x n) (hfdd n)) hr T δ
    sgConv_mesh_pos sgConv_mesh_tendsto (J := fun m ↦ ⌊T / sgConv_mesh m⌋₊)
    (δs := fun m ↦ ⌈δ / sgConv_mesh m⌉₊)
    (fun m ↦ sgConv_floor_mul_le T _ (sgConv_mesh_pos m))
    (fun m ↦ sgConv_lt_floor_succ_mul T _ (sgConv_mesh_pos m))
    (fun m ↦ sgConv_le_ceil_succ_mul δ _ (sgConv_mesh_pos m)) (P := ENNReal.ofReal η) ?_
  refine Filter.eventually_atTop.mpr ⟨max M₁ M₂, fun m hm ↦ ?_⟩
  have hm1 : M₁ ≤ m := (le_max_left _ _).trans hm
  have hm2 : M₂ ≤ m := (le_max_right _ _).trans hm
  have hg := sgConv_mesh_pos m
  have hgδ : sgConv_mesh m ≤ δ := sgConv_mesh_le m δ hδ M₂ hM₂ hm2
  have : IsMarkovKernel (S n (sgConv_mesh m)) := (hSc n).isMarkovKernel _
  have hJk := hM₁ m hm1
  have hHg : (⌊h₁ / sgConv_mesh m⌋₊ : ℝ≥0) * sgConv_mesh m ≤ h₁ := sgConv_floor_mul_le h₁ _ hg
  have hδg : (⌈δ / sgConv_mesh m⌉₊ : ℝ≥0) * sgConv_mesh m ≤ h₂ := by
    have := (sgConv_ceil_mul_lt δ _ hg).le
    refine this.trans ?_
    calc δ + sgConv_mesh m ≤ δ + δ := add_le_add le_rfl hgδ
      _ = h₂ := by rw [hδdef]; exact add_halves h₂
  have hA : ∀ a ∈ K, sgConv_zeta (S n (sgConv_mesh m)) K r ⌈δ / sgConv_mesh m⌉₊ a a ≤
      2 * ENNReal.ofReal ε₂ := by
    intro a ha
    have h := sgConv_zeta_le_two_mul (S n (sgConv_mesh m)) hKm (ρ := r / 2)
      (β := ENNReal.ofReal ε₂) ((ENNReal.ofReal_le_ofReal hε₂half).trans_eq sgConv_ofReal_half)
      ⌈δ / sgConv_mesh m⌉₊ (fun z hz j hj ↦ ?_) ha
    · have e : (2 : ℝ) * (r / 2) = r := by ring
      rwa [e] at h
    · rw [sgConv_kappa_eq (S n) (hSc n) _ (r / 2) z j z]
      refine hn₂ n hn2 _ ?_ z hz
      exact le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hj) zero_le) hδg
  have hu : ∀ a ∈ K, sgConv_zeta (S n (sgConv_mesh m)) K r ⌊h₁ / sgConv_mesh m⌋₊ a a ≤ 2⁻¹ := by
    intro a ha
    have h := sgConv_zeta_le_two_mul (S n (sgConv_mesh m)) hKm (ρ := r / 2)
      (β := ENNReal.ofReal (1 / 4)) (le_trans (ENNReal.ofReal_le_ofReal (by norm_num))
        sgConv_ofReal_half.le) ⌊h₁ / sgConv_mesh m⌋₊ (fun z hz j hj ↦ ?_) ha
    · have e : (2 : ℝ) * (r / 2) = r := by ring
      rw [e] at h
      exact h.trans sgConv_two_mul_ofReal_quarter
    · rw [sgConv_kappa_eq (S n) (hSc n) _ (r / 2) z j z]
      refine hn₁ n hn1 _ ?_ z hz
      exact le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hj) zero_le) hHg
  have hI := sgConv_grid_bad_le (S n) (hSc n) (hfdd n) hKm (hx n) (sgConv_mesh m) hg r
    ⌈δ / sgConv_mesh m⌉₊ ⌊h₁ / sgConv_mesh m⌋₊ k ⌊T / sgConv_mesh m⌋₊ le_rfl hA hu hJk
  refine hI.trans ?_
  refine (sgConv_pow_mul_ofReal k η' hη'.le).trans (ENNReal.ofReal_le_ofReal (min_le_left _ _))

end Concrete

end
end SuperdiffusionCLT.Section8.Convergence
