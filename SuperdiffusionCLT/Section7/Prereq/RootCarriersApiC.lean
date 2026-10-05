/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.RootCarriersApi
public import SuperdiffusionCLT.Section7.Prereq.WellPosed
public import SuperdiffusionCLT.Section7.Prereq.WellPosedB
public import SuperdiffusionCLT.Section7.Prereq.DomainInvariance
public import SuperdiffusionCLT.Section7.Prereq.FieldBridge
public import SuperdiffusionCLT.Section7.MinimalScale.GridMaxCount

/-!
# Almost-sure well-posedness of the Dirichlet problem, and witnesses on the carriers

* `rc_ae_dirichlet_wellPosed`: almost surely, for the rescaled field and for constant multiples
  of the identity, the Dirichlet problem on every bounded open set has a solution for every
  `L²` right-hand side and every `H¹` datum, unique up to almost everywhere equality.
* `rc_whitney_hypothesis_witness`: the Poincaré hypothesis of the Whitney lemma, read on
  `whitneyInterior`, holds on dilates of the ball of radius `1/2`.
* `rc_interior_window_nonempty`: the scale window of the interior estimate is nonempty.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Assumptions
open scoped ENNReal Pointwise

variable {d : ℕ}

/-- A constant multiple of the identity is elliptic on every measurable set. -/
theorem rc_isEllipticFieldOn_smul_one {s : ℝ} (hs : 0 < s) {U : Set (Vec d)}
    (hU : MeasurableSet U) : IsEllipticFieldOn s s U (fun _ => s • (1 : Mat d)) := by
  classical
  refine ⟨?_, fun x _ => ?_⟩
  · refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
    exact Measurable.ite hU measurable_const measurable_const
  · have hmv : ∀ ξ : Vec d, matVecMul (s • (1 : Mat d)) ξ = s • ξ := fun ξ => by
      funext i
      simp [matVecMul, Matrix.smul_apply, Matrix.one_apply]
    have hinv : (s • (1 : Mat d))⁻¹ = s⁻¹ • (1 : Mat d) := by
      refine Matrix.inv_eq_right_inv ?_
      rw [smul_mul_assoc, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
    have hmv' : ∀ ξ : Vec d, matVecMul (s⁻¹ • (1 : Mat d)) ξ = s⁻¹ • ξ := fun ξ => by
      funext i
      simp [matVecMul, Matrix.smul_apply, Matrix.one_apply]
    refine ⟨hs, le_refl _, fun ξ => ?_, fun ξ => ?_⟩
    · rw [hmv]
      simp only [vecDot, vecNormSq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact le_of_eq (Finset.sum_congr rfl fun i _ => by ring)
    · rw [hinv, hmv']
      simp only [vecDot, vecNormSq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact le_of_eq (Finset.sum_congr rfl fun i _ => by ring)

/-- Existence and almost everywhere uniqueness for an elliptic field, in the form used for the
carrier `IsDirichletSolution`. -/
theorem rc_dirichlet_wellPosed_of_elliptic [NeZero d] {U : Set (Vec d)} (hUo : IsOpen U)
    (hUb : Bornology.IsBounded U) {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam U a) {f : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict U)) (g : H1Function U) :
    (∃ u : H1Function U, IsDirichletSolution a U f g u) ∧
      ∀ u₁ u₂ : H1Function U, IsDirichletSolution a U f g u₁ → IsDirichletSolution a U f g u₂ →
        u₁.toFun =ᵐ[volume.restrict U] u₂.toFun ∧ u₁.grad =ᵐ[volume.restrict U] u₂.grad := by
  have hb := hUb.isBoundedDomain
  refine ⟨?_, fun u₁ u₂ h₁ h₂ => ?_⟩
  · obtain ⟨u, hu, hm⟩ := w0_dirichlet_exists hUo hb hEll hf g
    exact ⟨u, hu, hm⟩
  · exact w0_dirichlet_unique hUo hb hEll hf g h₁.1 h₁.2 h₂.1 h₂.2

/-- **Almost-sure well-posedness of the Dirichlet problem.** Under `J3` and `ν > 0`, almost
surely: for every bounded open set `U`, every `L²` right-hand side `f`, every `H¹` datum `g`,
(1) for every `ε > 0` the Dirichlet problem for the rescaled field `ν Id + (k - k(0))(·/ε)` has
a solution, and any two solutions agree almost everywhere (values and gradients); (2) the same
for `-s Δ`, every `s > 0` (the constant field `s Id`). -/
theorem rc_ae_dirichlet_wellPosed [NeZero d] {P : ProbabilityMeasure (ShellSeq d)}
    (hJ3 : ShellLawJ3 d P) {nu : ℝ} (hnu : 0 < nu) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure, ∀ U : Set (Vec d), IsOpen U → Bornology.IsBounded U →
      ∀ f : Vec d → ℝ, MemLp f 2 (volume.restrict U) → ∀ g : H1Function U,
        (∀ ε : ℝ, 0 < ε →
          (∃ u : H1Function U, IsDirichletSolution (epField nu omega ε) U f g u) ∧
            ∀ u₁ u₂ : H1Function U, IsDirichletSolution (epField nu omega ε) U f g u₁ →
              IsDirichletSolution (epField nu omega ε) U f g u₂ →
              u₁.toFun =ᵐ[volume.restrict U] u₂.toFun ∧
                u₁.grad =ᵐ[volume.restrict U] u₂.grad) ∧
        (∀ s : ℝ, 0 < s →
          (∃ u : H1Function U, IsDirichletSolution (fun _ => s • (1 : Mat d)) U f g u) ∧
            ∀ u₁ u₂ : H1Function U,
              IsDirichletSolution (fun _ => s • (1 : Mat d)) U f g u₁ →
              IsDirichletSolution (fun _ => s • (1 : Mat d)) U f g u₂ →
              u₁.toFun =ᵐ[volume.restrict U] u₂.toFun ∧
                u₁.grad =ᵐ[volume.restrict U] u₂.grad) := by
  filter_upwards [w0_ae_isElliptic_rescaled hJ3 hnu] with omega hω U hUo hUb f hf g
  refine ⟨fun ε hε => ?_, fun s hs => ?_⟩
  · obtain ⟨Lam, hLam⟩ := hω ε hε.ne' U hUb hUo.measurableSet
    exact rc_dirichlet_wellPosed_of_elliptic hUo hUb hLam hf g
  · exact rc_dirichlet_wellPosed_of_elliptic hUo hUb (rc_isEllipticFieldOn_smul_one hs
      hUo.measurableSet) hf g

/-- Witness for the hypotheses of `rc_ae_dirichlet_wellPosed`: the Dirac zero law, the unit ball,
the right-hand side `1` and the datum `0`; the conclusion yields a sample and a solution. -/
example [NeZero d] :
    ∃ (omega : ShellSeq d) (u : H1Function (SuperdiffusionCLT.Section6.euclidBall (d := d) 1)),
      IsDirichletSolution (epField 1 omega 1)
        (SuperdiffusionCLT.Section6.euclidBall (d := d) 1) (fun _ => 1) 0 u := by
  have hae := rc_ae_dirichlet_wellPosed (d := d)
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ3_diracZeroLaw (nu := 1) one_pos
  have hone : MemLp (fun _ : Vec d => (1 : ℝ)) 2
      (volume.restrict (SuperdiffusionCLT.Section6.euclidBall (d := d) 1)) := by
    have : IsFiniteMeasure
        (volume.restrict (SuperdiffusionCLT.Section6.euclidBall (d := d) 1)) :=
      ⟨by simpa [Measure.restrict_apply_univ] using
        SuperdiffusionCLT.Section6.volume_euclidBall_lt_top (d := d) one_pos⟩
    exact memLp_const 1
  obtain ⟨omega, hom⟩ := hae.exists
  obtain ⟨u, hu⟩ := ((hom _ (SuperdiffusionCLT.Section6.isOpen_euclidBall (d := d) 1)
    (Metric.isBounded_ball.subset
      (SuperdiffusionCLT.Section6.euclidBall_subset_ball one_pos)) _ hone 0).1 1 one_pos).1
  exact ⟨omega, u, hu⟩

/-- **The Poincaré hypothesis of the Whitney lemma on the ball of radius `1/2`, read on the
carriers.** For `U = B_{1/2}` (a smooth bounded domain inside the unit cube) there are `D₀ ≥ 1`
and `T ≥ 1`, depending only on `d`, such that for every `D ≥ D₀`, `M ≥ 1`, every `t ≥ T` and
`m` with `3^{m-1} < t ≤ 3^m`, every `φ ∈ H¹(t U)` satisfies the scaled Poincaré inequality on
`whitneyInterior (t U) (m - ⌈M log m⌉)` with constant `D 3^m`. -/
theorem rc_whitney_hypothesis_witness [NeZero d] :
    IsSmoothBoundedDomain (SuperdiffusionCLT.Section6.euclidBall (d := d) (1 / 2)) ∧
    SuperdiffusionCLT.Section6.euclidBall (d := d) (1 / 2) ⊆
      openCubeSet (originCube d 0) ∧
    ∃ D₀ T : ℝ, 1 ≤ D₀ ∧ 1 ≤ T ∧ ∀ D M : ℝ, D₀ ≤ D → 1 ≤ M →
      ∀ (t : ℝ) (m : ℕ), T ≤ t → (3 : ℝ) ^ m < 3 * t → t ≤ (3 : ℝ) ^ m →
        ∀ φ : H1Function (t • SuperdiffusionCLT.Section6.euclidBall (d := d) (1 / 2)),
          eLpNorm (fun x => φ.toFun x -
              ⨍ z in whitneyInterior
                  (t • SuperdiffusionCLT.Section6.euclidBall (d := d) (1 / 2))
                  ((m : ℤ) - ⌈M * Real.log (m : ℝ)⌉), φ.toFun z) 2
            (volume.restrict (whitneyInterior
              (t • SuperdiffusionCLT.Section6.euclidBall (d := d) (1 / 2))
              ((m : ℤ) - ⌈M * Real.log (m : ℝ)⌉))) ≤
          ENNReal.ofReal (D * (3 : ℝ) ^ m) *
            eLpNorm (fun x => eucNorm (φ.grad x)) 2
              (volume.restrict (whitneyInterior
                (t • SuperdiffusionCLT.Section6.euclidBall (d := d) (1 / 2))
                ((m : ℤ) - ⌈M * Real.log (m : ℝ)⌉))) := by
  obtain ⟨hsm, hsub, D₀, T, hD₀, hT, hW⟩ := wpd_whitney_poincare_witness (d := d)
  exact ⟨hsm, hsub, D₀, T, hD₀, hT, fun D M hD hM t m ht h1 h2 φ =>
    hW D M hD hM t m ht h1 h2 φ⟩

/-- Witness: the thresholds of `rc_whitney_hypothesis_witness` can be met by a dilate and a scale
(`d = 2`): `t = 3^m` with `m` large. -/
example : ∃ (t : ℝ) (m : ℕ), (3 : ℝ) ^ m < 3 * t ∧ t ≤ (3 : ℝ) ^ m ∧ 1 ≤ t :=
  ⟨3, 1, by norm_num, by norm_num, by norm_num⟩

/-- The window of `interior_pointwise` is nonempty for every value of the constants and of the
random scale: there are `n < m` with `(m - n) δ_m ≤ c`, `L̂ ≤ nK N n` and `X ≤ 3^{nK N n}`. -/
theorem rc_interior_window_nonempty {c N ε ρ Lhat Xω : ℝ} (hc : 0 < c) (hN : 0 ≤ N) (hε : 0 < ε)
    (hρ : ρ < 1) :
    ∃ m n : ℕ, n < m ∧
      ((m : ℝ) - (n : ℝ)) * (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)) ≤ c ∧
      Lhat ≤ (nK N n : ℝ) ∧ Xω ≤ (3 : ℝ) ^ nK N n := by
  have ha : 0 < (1 - ρ) / 2 := by linarith only [hρ]
  have h1 : ∀ᶠ x : ℝ in Filter.atTop, ε * x ^ (-((1 - ρ) / 2)) * Real.log x ≤ c := by
    have ho := (isLittleO_log_rpow_atTop ha).def (div_pos hc hε)
    filter_upwards [ho, Filter.eventually_gt_atTop (1 : ℝ)] with x hx hx1
    have hx0 : 0 < x := by linarith only [hx1]
    have hp : 0 < x ^ ((1 - ρ) / 2) := Real.rpow_pos_of_pos hx0 _
    rw [Real.norm_of_nonneg (Real.log_nonneg hx1.le), Real.norm_of_nonneg hp.le] at hx
    rw [Real.rpow_neg hx0.le]
    calc ε * (x ^ ((1 - ρ) / 2))⁻¹ * Real.log x
        ≤ ε * (x ^ ((1 - ρ) / 2))⁻¹ * (c / ε * x ^ ((1 - ρ) / 2)) :=
          mul_le_mul_of_nonneg_left hx (by positivity)
      _ = c := by field_simp
  have h2 : ∀ᶠ n : ℕ in Filter.atTop,
      ε * ((n + 1 : ℕ) : ℝ) ^ (-((1 - ρ) / 2)) * Real.log ((n + 1 : ℕ) : ℝ) ≤ c :=
    ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (Filter.tendsto_add_atTop_nat 1)).eventually h1
  set j : ℕ := ⌈max Lhat Xω⌉₊ with hj
  have h3 : ∀ᶠ n : ℕ in Filter.atTop, ⌈(4 * N + 2) ^ 2⌉₊ + 2 * j ≤ n :=
    Filter.eventually_ge_atTop _
  obtain ⟨n, hn2, hn3⟩ := (h2.and h3).exists
  have hK : (4 * N + 2) ^ 2 ≤ (n : ℝ) := by
    have : ((⌈(4 * N + 2) ^ 2⌉₊ : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : ⌈(4 * N + 2) ^ 2⌉₊ ≤ n)
    exact (Nat.le_ceil _).trans this
  have hhalf := ceil_le_half hN hK
  have hjn : j ≤ nK N n := by
    have hh : 2 * ⌈N * Real.log (n : ℝ)⌉₊ ≤ n := by exact_mod_cast hhalf
    unfold nK
    omega
  have hjR : max Lhat Xω ≤ (j : ℝ) := Nat.le_ceil _
  refine ⟨n + 1, n, Nat.lt_succ_self n, ?_, ?_, ?_⟩
  · have : ((n + 1 : ℕ) : ℝ) - (n : ℝ) = 1 := by push_cast; ring
    rw [this, one_mul]
    exact hn2
  · exact (le_max_left _ _).trans (hjR.trans (by exact_mod_cast hjn))
  · have h3j : (j : ℝ) ≤ (3 : ℝ) ^ j := by
      exact_mod_cast (Nat.lt_pow_self (by norm_num : 1 < 3)).le
    calc Xω ≤ (j : ℝ) := (le_max_right _ _).trans hjR
      _ ≤ (3 : ℝ) ^ j := h3j
      _ ≤ (3 : ℝ) ^ nK N n := pow_le_pow_right₀ (by norm_num) hjn


/-- Witness: the window is nonempty for all constants equal to `1` and `ρ = 0`. -/
example : ∃ m n : ℕ, n < m ∧
    ((m : ℝ) - (n : ℝ)) * (1 * (m : ℝ) ^ (-((1 - (0 : ℝ)) / 2)) * Real.log (m : ℝ)) ≤ 1 ∧
    (1 : ℝ) ≤ (nK 1 n : ℝ) ∧ (1 : ℝ) ≤ (3 : ℝ) ^ nK 1 n :=
  rc_interior_window_nonempty one_pos zero_le_one one_pos zero_lt_one

end SuperdiffusionCLT.Section7
